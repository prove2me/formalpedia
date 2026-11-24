-- Prove2me | solution 1 for ProphetBipartite.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T08:12:17.831458+00:00
-- url     : https://prove2.me/submissions/da3a264f-7e5e-408a-bea4-337a3dd89c8d

import Mathlib
import Definitions.Def_ProphetBipartite_optValue
import Definitions.Def_ProphetBipartite_IsOrder
import Definitions.Def_ProphetBipartite_vaddRun
import Definitions.Def_ProphetBipartite_IsOptSelector
import Definitions.Def_ProphetBipartite_Mmat
import Definitions.Def_ProphetBipartite_IsSolution17
import Theorems.Thm_ProphetBipartite_eq_11_lower_bound
import Theorems.Thm_ProphetBipartite_eq_12_opt
import Theorems.Thm_ProphetBipartite_fact_3_2
import Theorems.Thm_ProphetBipartite_eq_14_ge_third_opt
import Theorems.Thm_ProphetBipartite_eq_17_solution_exists

open MeasureTheory
open scoped NNReal ENNReal

namespace ProphetBipartite.Sol31

open ProphetBipartite

private lemma measurable_coe_nnreal : Measurable (fun x : ℝ≥0 => (x : ℝ≥0∞)) := by
  fun_prop

private lemma measurable_finset_sup_nnreal {Ω α : Type*} [MeasurableSpace Ω]
    (s : Finset α) (f : α → Ω → ℝ≥0) (hf : ∀ a ∈ s, Measurable (f a)) :
    Measurable (fun ω => s.sup (fun a => f a ω)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sup_empty]
      exact measurable_const
  | @insert a s _ ih =>
      simp only [Finset.sup_insert]
      exact (hf a (Finset.mem_insert_self a s)).sup
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

private lemma measurable_optValue {L R E : Type*} [Fintype E] [DecidableEq E]
    (left : E → L) (right : E → R) :
    Measurable (optValue left right) := by
  unfold optValue
  refine measurable_finset_sup_nnreal _ _ ?_
  intro S _
  exact Finset.measurable_sum S (fun e _ => measurable_pi_apply e)

private noncomputable def selectFrom {E : Type*} (t : (E → ℝ≥0) → ℝ≥0) :
    List (Finset E) → (E → ℝ≥0) → Finset E
  | [], _ => ∅
  | S :: tl, v =>
      if ∑ e ∈ S, v e = t v then S else selectFrom t tl v

private lemma measurableSet_selectFrom_eq {E : Type*} {t : (E → ℝ≥0) → ℝ≥0}
    (ht : Measurable t) :
    ∀ (L : List (Finset E)) (T : Finset E),
      MeasurableSet {v : E → ℝ≥0 | selectFrom t L v = T}
  | [], T => MeasurableSet.const (∅ = T)
  | S :: tl, T => by
      let A : Set (E → ℝ≥0) := {v | ∑ e ∈ S, v e = t v}
      have hsum : Measurable (fun v : E → ℝ≥0 => ∑ e ∈ S, v e) :=
        Finset.measurable_sum S (fun e _ => measurable_pi_apply e)
      have hA : MeasurableSet A := measurableSet_eq_fun hsum ht
      have hset : {v : E → ℝ≥0 | selectFrom t (S :: tl) v = T} =
          (A ∩ {v | S = T}) ∪ (Aᶜ ∩ {v | selectFrom t tl v = T}) := by
        ext v
        simp only [selectFrom, A, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
          Set.mem_compl_iff]
        split_ifs with h <;> simp [h]
      rw [hset]
      exact (hA.inter (MeasurableSet.const _)).union
        (hA.compl.inter (measurableSet_selectFrom_eq ht tl T))

private lemma selectFrom_mem_and_eq {E : Type*} (t : (E → ℝ≥0) → ℝ≥0) :
    ∀ (L : List (Finset E)) (v : E → ℝ≥0),
      (∃ S ∈ L, ∑ e ∈ S, v e = t v) →
        selectFrom t L v ∈ L ∧ ∑ e ∈ selectFrom t L v, v e = t v
  | [], _, ⟨_, hmem, _⟩ => nomatch hmem
  | S₀ :: tl, v, ⟨S, hmem, heq⟩ => by
      simp only [selectFrom]
      split_ifs with h
      · exact ⟨List.mem_cons_self .., h⟩
      · rcases List.mem_cons.mp hmem with rfl | htl
        · exact absurd heq h
        · rcases selectFrom_mem_and_eq t tl v ⟨S, htl, heq⟩ with ⟨hm, hs⟩
          exact ⟨List.mem_cons_of_mem _ hm, hs⟩

private lemma exists_isOptSelector {L R E : Type*} [Fintype E] [DecidableEq E]
    (left : E → L) (right : E → R) :
    ∃ opt : (E → ℝ≥0) → Finset E, IsOptSelector left right opt := by
  classical
  let matchings : Finset (Finset E) :=
    Finset.univ.filter (fun S : Finset E => IsMatching left right S)
  have hempty : (∅ : Finset E) ∈ matchings := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simp [IsMatching]⟩
  let opt : (E → ℝ≥0) → Finset E := selectFrom (optValue left right) matchings.toList
  refine ⟨opt, ⟨fun v => ?_, fun T => ?_⟩⟩
  · have hopt_eq : optValue left right v = matchings.sup (fun S => ∑ e ∈ S, v e) := by
      unfold optValue
      dsimp only [matchings]
    obtain ⟨S, hS, hsup⟩ :=
      Finset.exists_mem_eq_sup matchings ⟨∅, hempty⟩ (fun S => ∑ e ∈ S, v e)
    have hex : ∃ S ∈ matchings.toList, ∑ e ∈ S, v e = optValue left right v :=
      ⟨S, Finset.mem_toList.mpr hS, (hopt_eq.trans hsup).symm⟩
    rcases selectFrom_mem_and_eq (optValue left right) matchings.toList v hex with ⟨hmem, hsum⟩
    have hmatch : IsMatching left right (opt v) :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hmem)).2
    exact ⟨hmatch, hsum⟩
  · exact measurableSet_selectFrom_eq (measurable_optValue left right) matchings.toList T

private lemma measurable_foldl_vaddStep {L R E : Type*}
    [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0)
    (f : RunState L R E → (E → ℝ≥0) → ℝ≥0) (hf : ∀ s, Measurable (f s)) :
    ∀ (σ : List E) (s : RunState L R E),
      Measurable (fun v => f (σ.foldl (vaddStep left right l r v) s) v)
  | [], s => hf s
  | e :: tl, s => by
      let p : (E → ℝ≥0) → Prop := fun v =>
        left e ∉ s.coveredL ∧ right e ∉ s.coveredR ∧ l (left e) + r (right e) ≤ v e
      let s_yes : RunState L R E :=
        { coveredL := insert (left e) s.coveredL
          coveredR := insert (right e) s.coveredR
          accepted := insert e s.accepted }
      have hp : MeasurableSet {v | p v} :=
        (MeasurableSet.const _).inter
          ((MeasurableSet.const _).inter (measurable_pi_apply e measurableSet_Ici))
      have heq : (fun v => f ((e :: tl).foldl (vaddStep left right l r v) s) v) =
          fun v => @ite _ (p v) (Classical.propDecidable _)
            (f (tl.foldl (vaddStep left right l r v) s_yes) v)
            (f (tl.foldl (vaddStep left right l r v) s) v) := by
        ext v
        simp only [List.foldl_cons, vaddStep, p, s_yes]
        split_ifs <;> rfl
      rw [heq]
      exact Measurable.ite hp
        (measurable_foldl_vaddStep left right l r f hf tl s_yes)
        (measurable_foldl_vaddStep left right l r f hf tl s)

private lemma measurable_vaddValue {L R E : Type*}
    [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) :
    Measurable (vaddValue left right l r σ) := by
  refine measurable_foldl_vaddStep left right l r
    (fun s v => ∑ e ∈ s.accepted, v e) ?_ σ ⟨∅, ∅, ∅⟩
  intro s
  exact Finset.measurable_sum s.accepted (fun e _ => measurable_pi_apply e)

private lemma lintegral_optValue_ne_top {L R E : Type*} [Fintype E] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤) :
    ∫⁻ v, (optValue left right v : ℝ≥0∞) ∂(Measure.pi μ) ≠ ⊤ := by
  have hle : ∀ v : E → ℝ≥0,
      (optValue left right v : ℝ≥0∞) ≤ ∑ e : E, (v e : ℝ≥0∞) := by
    intro v
    have hnn : optValue left right v ≤ ∑ e : E, v e := by
      unfold optValue
      refine Finset.sup_le ?_
      intro S _
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    exact (ENNReal.coe_le_coe.mpr hnn).trans_eq (ENNReal.ofNNReal_finsetSum _ _)
  have hlt : ∫⁻ v, (optValue left right v : ℝ≥0∞) ∂(Measure.pi μ) < ⊤ := by
    refine (lintegral_mono hle).trans_lt ?_
    rw [lintegral_finsetSum _ (fun e _ =>
      show Measurable (fun v : E → ℝ≥0 => (v e : ℝ≥0∞)) from
        measurable_coe_nnreal.comp (measurable_pi_apply e))]
    refine ENNReal.sum_lt_top.mpr ?_
    intro e _
    have heval : ∫⁻ v : E → ℝ≥0, (v e : ℝ≥0∞) ∂(Measure.pi μ) = ∫⁻ x : ℝ≥0, (x : ℝ≥0∞) ∂(μ e) :=
      (MeasureTheory.measurePreserving_eval μ e).lintegral_comp measurable_coe_nnreal
    exact heval.trans_lt (hμ e).lt_top
  exact hlt.ne

end ProphetBipartite.Sol31

open ProphetBipartite ProphetBipartite.Sol31

theorem solution {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤) :
    ∃ (l : L → ℝ≥0) (r : R → ℝ≥0), ∀ σ : List E, IsOrder σ →
      ∫⁻ v, (optValue left right v : ℝ≥0∞) ∂(Measure.pi μ) ≤
        3 * ∫⁻ v, (vaddValue left right l r σ v : ℝ≥0∞) ∂(Measure.pi μ) := by
  obtain ⟨opt, hopt⟩ := exists_isOptSelector left right
  let M := Mmat left right opt μ
  let Q := Qmat left right opt μ
  have hM : ∀ i j, 0 ≤ M i j := by
    intro i j
    exact integral_nonneg (fun v => Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _))
  have hQ : ∀ i j, 0 ≤ Q i j := fun _ _ => measureReal_nonneg
  obtain ⟨hrow, hcol⟩ := fact_3_2 left right μ opt hopt
  obtain ⟨l_real, r_real, _, hsol17⟩ := eq_17_solution_exists M Q hM hQ hrow hcol 0 0
  obtain ⟨hl_nn, hr_nn, hbound14⟩ := eq_14_ge_third_opt M Q hM hQ hrow hcol l_real r_real hsol17
  let l : L → ℝ≥0 := fun i => ⟨l_real i, hl_nn i⟩
  let r : R → ℝ≥0 := fun j => ⟨r_real j, hr_nn j⟩
  refine ⟨l, r, fun σ hσ => ?_⟩
  have h11 := eq_11_lower_bound left right μ hμ opt hopt l r σ hσ
  obtain ⟨⟨SL, SR⟩, _, hinf_eq⟩ :=
    Finset.exists_mem_eq_inf'
      (Finset.univ_nonempty : (Finset.univ : Finset (Finset L × Finset R)).Nonempty)
      (fun S => ∑ i ∈ S.1, (l i : ℝ) + ∑ j ∈ S.2, (r j : ℝ) +
        ∑ i ∈ S.1ᶜ, ∑ j ∈ S.2ᶜ, max (M i j - ((l i : ℝ) + r j) * Q i j) 0)
  have h12 := eq_12_opt left right μ hμ opt hopt
  have h_real : ∫ v, (optValue left right v : ℝ) ∂(Measure.pi μ) ≤
      3 * ∫ v, (vaddValue left right l r σ v : ℝ) ∂(Measure.pi μ) := by
    calc ∫ v, (optValue left right v : ℝ) ∂(Measure.pi μ)
        = ∑ i, ∑ j, M i j := h12
      _ ≤ 3 * (∑ i ∈ SL, l_real i + ∑ j ∈ SR, r_real j +
            ∑ i ∈ SLᶜ, ∑ j ∈ SRᶜ, max (M i j - (l_real i + r_real j) * Q i j) 0) :=
          hbound14 SL SR
      _ ≤ 3 * ∫ v, (vaddValue left right l r σ v : ℝ) ∂(Measure.pi μ) := by
          have hstep : ∑ i ∈ SL, l_real i + ∑ j ∈ SR, r_real j +
              ∑ i ∈ SLᶜ, ∑ j ∈ SRᶜ, max (M i j - (l_real i + r_real j) * Q i j) 0 ≤
              ∫ v, (vaddValue left right l r σ v : ℝ) ∂(Measure.pi μ) :=
            hinf_eq.symm.trans_le h11
          linarith
  have h_opt_toReal :
      ∫ v, (optValue left right v : ℝ) ∂(Measure.pi μ) =
        (∫⁻ v, (optValue left right v : ℝ≥0∞) ∂(Measure.pi μ)).toReal := by
    have hm : Measurable (fun v : E → ℝ≥0 => (optValue left right v : ℝ≥0∞)) :=
      measurable_coe_nnreal.comp (measurable_optValue left right)
    simpa only [ENNReal.coe_toReal] using
      integral_toReal hm.aemeasurable (ae_of_all _ (fun _ => ENNReal.coe_lt_top))
  have h_vadd_toReal :
      ∫ v, (vaddValue left right l r σ v : ℝ) ∂(Measure.pi μ) =
        (∫⁻ v, (vaddValue left right l r σ v : ℝ≥0∞) ∂(Measure.pi μ)).toReal := by
    have hm : Measurable (fun v : E → ℝ≥0 => (vaddValue left right l r σ v : ℝ≥0∞)) :=
      measurable_coe_nnreal.comp (measurable_vaddValue left right l r σ)
    simpa only [ENNReal.coe_toReal] using
      integral_toReal hm.aemeasurable (ae_of_all _ (fun _ => ENNReal.coe_lt_top))
  rw [h_opt_toReal, h_vadd_toReal] at h_real
  have hI_opt := lintegral_optValue_ne_top left right μ hμ
  calc ∫⁻ v, (optValue left right v : ℝ≥0∞) ∂(Measure.pi μ)
      = ENNReal.ofReal (∫⁻ v, (optValue left right v : ℝ≥0∞) ∂(Measure.pi μ)).toReal :=
        (ENNReal.ofReal_toReal hI_opt).symm
    _ ≤ ENNReal.ofReal
          (3 * (∫⁻ v, (vaddValue left right l r σ v : ℝ≥0∞) ∂(Measure.pi μ)).toReal) :=
        ENNReal.ofReal_le_ofReal h_real
    _ = 3 * ENNReal.ofReal
          (∫⁻ v, (vaddValue left right l r σ v : ℝ≥0∞) ∂(Measure.pi μ)).toReal := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
    _ ≤ 3 * ∫⁻ v, (vaddValue left right l r σ v : ℝ≥0∞) ∂(Measure.pi μ) := by
        gcongr
        exact ENNReal.ofReal_toReal_le
