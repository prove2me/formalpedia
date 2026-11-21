-- Prove2me | solution 1 for ProphetBipartite.eq_11_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T00:32:44.177137+00:00
-- url     : https://prove2.me/submissions/2bf9843b-2ae2-440f-9757-81b8e3e5b05a

import Mathlib
import Definitions.Def_ProphetBipartite_IsOrder
import Definitions.Def_ProphetBipartite_vaddRun
import Definitions.Def_ProphetBipartite_IsOptSelector
import Definitions.Def_ProphetBipartite_Mmat

open MeasureTheory
open scoped NNReal ENNReal

namespace Aux_PB31
open ProphetBipartite

section run
variable {L R E : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq E]
  (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0)

theorem step_mono (v : E → ℝ≥0) (s : RunState L R E) (e : E) :
    s.coveredL ⊆ (vaddStep left right l r v s e).coveredL ∧
    s.coveredR ⊆ (vaddStep left right l r v s e).coveredR ∧
    s.accepted ⊆ (vaddStep left right l r v s e).accepted := by
  unfold vaddStep
  split_ifs
  · exact ⟨Finset.subset_insert _ _, Finset.subset_insert _ _, Finset.subset_insert _ _⟩
  · exact ⟨subset_refl _, subset_refl _, subset_refl _⟩

theorem fold_mono (v : E → ℝ≥0) (σ : List E) : ∀ s : RunState L R E,
    s.coveredL ⊆ (σ.foldl (vaddStep left right l r v) s).coveredL ∧
    s.coveredR ⊆ (σ.foldl (vaddStep left right l r v) s).coveredR ∧
    s.accepted ⊆ (σ.foldl (vaddStep left right l r v) s).accepted := by
  induction σ with
  | nil => intro s; exact ⟨subset_refl _, subset_refl _, subset_refl _⟩
  | cons e σ ih =>
    intro s
    obtain ⟨h1, h2, h3⟩ := step_mono left right l r v s e
    obtain ⟨g1, g2, g3⟩ := ih (vaddStep left right l r v s e)
    exact ⟨h1.trans g1, h2.trans g2, h3.trans g3⟩

theorem step_update (v : E → ℝ≥0) (e : E) (x : ℝ≥0) (s : RunState L R E) (e' : E)
    (hne : e' ≠ e) :
    vaddStep left right l r (Function.update v e x) s e' = vaddStep left right l r v s e' := by
  unfold vaddStep
  rw [Function.update_of_ne hne]

theorem fold_update (v : E → ℝ≥0) (e : E) (x : ℝ≥0) (σ : List E) (he : e ∉ σ) :
    ∀ s : RunState L R E, σ.foldl (vaddStep left right l r (Function.update v e x)) s =
      σ.foldl (vaddStep left right l r v) s := by
  induction σ with
  | nil => intro s; rfl
  | cons e' σ ih =>
    intro s
    have hne : e' ≠ e := fun h => he (by rw [← h]; exact List.mem_cons.mpr (Or.inl rfl))
    have he' : e ∉ σ := fun h => he (List.mem_cons_of_mem _ h)
    simp only [List.foldl_cons]
    rw [step_update left right l r v e x s e' hne]
    exact ih he' _

theorem accept_lemma (v : E → ℝ≥0) (σ : List E) (hσ : σ.Nodup) (e : E) (he : e ∈ σ)
    (x : ℝ≥0) (hx : l (left e) + r (right e) ≤ x)
    (hL : left e ∉ (vaddRun left right l r σ v).coveredL)
    (hR : right e ∉ (vaddRun left right l r σ v).coveredR) :
    e ∈ (vaddRun left right l r σ (Function.update v e x)).accepted := by
  obtain ⟨σ1, σ2, rfl⟩ := List.append_of_mem he
  have he1 : e ∉ σ1 := fun h =>
    List.disjoint_of_nodup_append hσ h (List.mem_cons.mpr (Or.inl rfl))
  unfold vaddRun at hL hR ⊢
  rw [List.foldl_append, List.foldl_cons] at hL hR ⊢
  rw [fold_update left right l r v e x σ1 he1]
  obtain ⟨s, hs⟩ : ∃ s, s = σ1.foldl (vaddStep left right l r v) ⟨∅, ∅, ∅⟩ := ⟨_, rfl⟩
  rw [← hs] at hL hR ⊢
  have hm := fold_mono left right l r v σ2 (vaddStep left right l r v s e)
  have hm' := step_mono left right l r v s e
  have hsL : left e ∉ s.coveredL := fun h => hL (hm.1 (hm'.1 h))
  have hsR : right e ∉ s.coveredR := fun h => hR (hm.2.1 (hm'.2.1 h))
  have hstep : e ∈ (vaddStep left right l r (Function.update v e x) s e).accepted := by
    unfold vaddStep
    rw [if_pos ⟨hsL, hsR, by rw [Function.update_self]; exact hx⟩]
    exact Finset.mem_insert_self _ _
  exact (fold_mono left right l r (Function.update v e x) σ2 _).2.2 hstep

theorem meas_fold (P : RunState L R E → Prop) (σ : List E) :
    ∀ s0 : RunState L R E,
      MeasurableSet {v : E → ℝ≥0 | P (σ.foldl (vaddStep left right l r v) s0)} := by
  induction σ with
  | nil =>
    intro s0
    show MeasurableSet {v : E → ℝ≥0 | P s0}
    exact MeasurableSet.const _
  | cons e σ ih =>
    intro s0
    have hc : MeasurableSet {v : E → ℝ≥0 | left e ∉ s0.coveredL ∧ right e ∉ s0.coveredR ∧
        l (left e) + r (right e) ≤ v e} := by
      have h3 : MeasurableSet {v : E → ℝ≥0 | l (left e) + r (right e) ≤ v e} :=
        measurableSet_le measurable_const (measurable_pi_apply e)
      have h4 : {v : E → ℝ≥0 | left e ∉ s0.coveredL ∧ right e ∉ s0.coveredR ∧
          l (left e) + r (right e) ≤ v e} = {v : E → ℝ≥0 | left e ∉ s0.coveredL} ∩
          ({v : E → ℝ≥0 | right e ∉ s0.coveredR} ∩
            {v : E → ℝ≥0 | l (left e) + r (right e) ≤ v e}) := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      rw [h4]
      exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter h3)
    have heq : {v : E → ℝ≥0 | P ((e :: σ).foldl (vaddStep left right l r v) s0)} =
        ({v : E → ℝ≥0 | left e ∉ s0.coveredL ∧ right e ∉ s0.coveredR ∧
            l (left e) + r (right e) ≤ v e} ∩
          {v | P (σ.foldl (vaddStep left right l r v)
            ⟨insert (left e) s0.coveredL, insert (right e) s0.coveredR, insert e s0.accepted⟩)}) ∪
        ({v : E → ℝ≥0 | left e ∉ s0.coveredL ∧ right e ∉ s0.coveredR ∧
            l (left e) + r (right e) ≤ v e}ᶜ ∩
          {v | P (σ.foldl (vaddStep left right l r v) s0)}) := by
      ext v
      simp only [List.foldl_cons, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff]
      by_cases h : left e ∉ s0.coveredL ∧ right e ∉ s0.coveredR ∧ l (left e) + r (right e) ≤ v e
      · have hs : vaddStep left right l r v s0 e =
            ⟨insert (left e) s0.coveredL, insert (right e) s0.coveredR, insert e s0.accepted⟩ := by
          unfold vaddStep
          rw [if_pos h]
        rw [hs]
        tauto
      · have hs : vaddStep left right l r v s0 e = s0 := by
          unfold vaddStep
          rw [if_neg h]
        rw [hs]
        tauto
    rw [heq]
    exact (hc.inter (ih _)).union (hc.compl.inter (ih _))

theorem meas_acc (σ : List E) (e : E) :
    MeasurableSet {v : E → ℝ≥0 | e ∈ vaddAccepted left right l r σ v} :=
  meas_fold left right l r (fun s => e ∈ s.accepted) σ _

theorem meas_covL (σ : List E) (i : L) :
    MeasurableSet {v : E → ℝ≥0 | i ∈ vaddCoveredL left right l r σ v} :=
  meas_fold left right l r (fun s => i ∈ s.coveredL) σ _

theorem meas_covR (σ : List E) (j : R) :
    MeasurableSet {v : E → ℝ≥0 | j ∈ vaddCoveredR left right l r σ v} :=
  meas_fold left right l r (fun s => j ∈ s.coveredR) σ _

end run

section main
variable {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
  [DecidableEq L] [DecidableEq R] [DecidableEq E]

theorem integ_coord (μ : E → Measure ℝ≥0) (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤) (e : E) :
    Integrable (fun x : ℝ≥0 => (x : ℝ)) (μ e) := by
  have h0 := integrable_toReal_of_lintegral_ne_top (μ := μ e) (f := fun x : ℝ≥0 => (x : ℝ≥0∞))
    (by fun_prop) (hμ e)
  simpa using h0

theorem integ_pp (μ : E → Measure ℝ≥0) (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤) (e : E)
    (a b : ℝ≥0) :
    Integrable (fun x : ℝ≥0 => max ((x : ℝ) - a - b) 0) (μ e) := by
  refine (integ_coord μ hμ e).mono'
    (by fun_prop : Measurable fun x : ℝ≥0 => max ((x : ℝ) - a - b) 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have ha : (0 : ℝ) ≤ a := NNReal.coe_nonneg a
  have hb : (0 : ℝ) ≤ b := NNReal.coe_nonneg b
  have hx : (0 : ℝ) ≤ x := NNReal.coe_nonneg x
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith) hx

theorem MQ_bound (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0)
    [∀ e, IsProbabilityMeasure (μ e)] (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤)
    (opt : (E → ℝ≥0) → Finset E) (hopt : IsOptSelector left right opt)
    (l : L → ℝ≥0) (r : R → ℝ≥0) (i : L) (j : R) :
    Mmat left right opt μ i j - ((l i : ℝ) + r j) * Qmat left right opt μ i j ≤
      ∑ e ∈ Finset.univ.filter (fun e => left e = i ∧ right e = j),
        ∫ x, max ((x : ℝ) - l (left e) - r (right e)) 0 ∂(μ e) := by
  have hmemS : ∀ e, MeasurableSet {v : E → ℝ≥0 | e ∈ opt v} := by
    intro e
    have h : {v : E → ℝ≥0 | e ∈ opt v} =
        ⋃ S ∈ Finset.univ.filter (fun S : Finset E => e ∈ S), {v | opt v = S} := by
      ext v
      simp
    rw [h]
    exact Finset.measurableSet_biUnion _ (fun S _ => hopt.2 S)
  have hQS : MeasurableSet {v : E → ℝ≥0 | ∃ e ∈ opt v, left e = i ∧ right e = j} := by
    have h : {v : E → ℝ≥0 | ∃ e ∈ opt v, left e = i ∧ right e = j} =
        ⋃ e ∈ Finset.univ.filter (fun e => left e = i ∧ right e = j), {v | e ∈ opt v} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        exists_prop]
      constructor
      · rintro ⟨e, h1, h2⟩
        exact ⟨e, h2, h1⟩
      · rintro ⟨e, h1, h2⟩
        exact ⟨e, h2, h1⟩
    rw [h]
    exact Finset.measurableSet_biUnion _ (fun e _ => hmemS e)
  have hfM : ∀ v : E → ℝ≥0,
      ∑ e ∈ (opt v).filter (fun e => left e = i ∧ right e = j), (v e : ℝ) =
      ∑ e ∈ Finset.univ.filter (fun e => left e = i ∧ right e = j),
        Set.indicator {v : E → ℝ≥0 | e ∈ opt v} (fun v => (v e : ℝ)) v := by
    intro v
    have h1 : (opt v).filter (fun e => left e = i ∧ right e = j) =
        (Finset.univ.filter (fun e => left e = i ∧ right e = j)).filter (fun e => e ∈ opt v) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [h1, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e ∈ opt v
    · rw [if_pos he, Set.indicator_of_mem (show v ∈ {v : E → ℝ≥0 | e ∈ opt v} from he)]
    · rw [if_neg he, Set.indicator_of_notMem (show v ∉ {v : E → ℝ≥0 | e ∈ opt v} from he)]
  have hintM : Integrable (fun v : E → ℝ≥0 =>
      ∑ e ∈ (opt v).filter (fun e => left e = i ∧ right e = j), (v e : ℝ)) (Measure.pi μ) := by
    have h : Integrable (fun v : E → ℝ≥0 =>
        ∑ e ∈ Finset.univ.filter (fun e => left e = i ∧ right e = j),
          Set.indicator {v : E → ℝ≥0 | e ∈ opt v} (fun v => (v e : ℝ)) v) (Measure.pi μ) :=
      integrable_finsetSum _ (fun e _ =>
        (integrable_comp_eval (μ := μ) (i := e) (f := fun x : ℝ≥0 => (x : ℝ)) (integ_coord μ hμ e)).indicator
          (hmemS e))
    exact h.congr (Filter.Eventually.of_forall fun v => (hfM v).symm)
  have hintQ : Integrable (Set.indicator {v : E → ℝ≥0 | ∃ e ∈ opt v, left e = i ∧ right e = j}
      (1 : (E → ℝ≥0) → ℝ)) (Measure.pi μ) :=
    (integrable_const (1 : ℝ)).indicator hQS
  have hintP : ∀ e, Integrable (fun v : E → ℝ≥0 =>
      max ((v e : ℝ) - l (left e) - r (right e)) 0) (Measure.pi μ) := fun e =>
    integrable_comp_eval (μ := μ) (i := e) (f := fun x : ℝ≥0 => max ((x : ℝ) - l (left e) - r (right e)) 0)
      (integ_pp μ hμ e (l (left e)) (r (right e)))
  have hpt : ∀ v : E → ℝ≥0,
      ∑ e ∈ (opt v).filter (fun e => left e = i ∧ right e = j), (v e : ℝ) -
        ((l i : ℝ) + r j) *
          Set.indicator {v : E → ℝ≥0 | ∃ e ∈ opt v, left e = i ∧ right e = j} 1 v ≤
      ∑ e ∈ Finset.univ.filter (fun e => left e = i ∧ right e = j),
        max ((v e : ℝ) - l (left e) - r (right e)) 0 := by
    intro v
    have hnn : ∀ e ∈ Finset.univ.filter (fun e => left e = i ∧ right e = j),
        0 ≤ max ((v e : ℝ) - l (left e) - r (right e)) 0 := fun e _ => le_max_right _ _
    by_cases hex : ∃ e ∈ opt v, left e = i ∧ right e = j
    · obtain ⟨e0, he0, hp0⟩ := hex
      have hF : (opt v).filter (fun e => left e = i ∧ right e = j) = {e0} := by
        rw [Finset.eq_singleton_iff_unique_mem]
        refine ⟨Finset.mem_filter.mpr ⟨he0, hp0⟩, fun b hb => ?_⟩
        rw [Finset.mem_filter] at hb
        by_contra hbe
        exact ((hopt.1 v).1 b hb.1 e0 he0 hbe).1 (hb.2.1.trans hp0.1.symm)
      rw [hF, Finset.sum_singleton,
        Set.indicator_of_mem (show v ∈ {v : E → ℝ≥0 | ∃ e ∈ opt v, left e = i ∧ right e = j} from
          ⟨e0, he0, hp0⟩)]
      have hmem : e0 ∈ Finset.univ.filter (fun e => left e = i ∧ right e = j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0⟩
      have h1 := Finset.single_le_sum hnn hmem
      have h2 : (v e0 : ℝ) - l (left e0) - r (right e0) ≤
          max ((v e0 : ℝ) - l (left e0) - r (right e0)) 0 := le_max_left _ _
      rw [hp0.1, hp0.2] at h1 h2
      simp only [Pi.one_apply, mul_one]
      linarith
    · have hF : (opt v).filter (fun e => left e = i ∧ right e = j) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro e he hp
        exact hex ⟨e, he, hp⟩
      rw [hF, Finset.sum_empty,
        Set.indicator_of_notMem (show v ∉ {v : E → ℝ≥0 | ∃ e ∈ opt v, left e = i ∧ right e = j}
          from hex), mul_zero, sub_zero]
      exact Finset.sum_nonneg hnn
  have hQ : Qmat left right opt μ i j = ∫ v, Set.indicator
      {v : E → ℝ≥0 | ∃ e ∈ opt v, left e = i ∧ right e = j} (1 : (E → ℝ≥0) → ℝ) v
      ∂(Measure.pi μ) := (integral_indicator_one hQS).symm
  have hM : Mmat left right opt μ i j = ∫ v,
      ∑ e ∈ (opt v).filter (fun e => left e = i ∧ right e = j), (v e : ℝ) ∂(Measure.pi μ) := rfl
  rw [hM, hQ, ← integral_const_mul, ← integral_sub hintM (hintQ.const_mul _)]
  calc ∫ v, (∑ e ∈ (opt v).filter (fun e => left e = i ∧ right e = j), (v e : ℝ) -
          ((l i : ℝ) + r j) *
            Set.indicator {v : E → ℝ≥0 | ∃ e ∈ opt v, left e = i ∧ right e = j} 1 v)
          ∂(Measure.pi μ)
      ≤ ∫ v, ∑ e ∈ Finset.univ.filter (fun e => left e = i ∧ right e = j),
          max ((v e : ℝ) - l (left e) - r (right e)) 0 ∂(Measure.pi μ) :=
        integral_mono (hintM.sub (hintQ.const_mul _))
          (integrable_finsetSum _ (fun e _ => hintP e)) hpt
    _ = ∑ e ∈ Finset.univ.filter (fun e => left e = i ∧ right e = j),
          ∫ v, max ((v e : ℝ) - l (left e) - r (right e)) 0 ∂(Measure.pi μ) :=
        integral_finsetSum _ (fun e _ => hintP e)
    _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        exact integral_comp_eval (μ := μ) (i := e)
          (f := fun x : ℝ≥0 => max ((x : ℝ) - l (left e) - r (right e)) 0)
          (integ_pp μ hμ e _ _).aestronglyMeasurable

end main

section final
variable {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
  [DecidableEq L] [DecidableEq R] [DecidableEq E]

noncomputable def cM (left : E → L) (right : E → R) (opt : (E → ℝ≥0) → Finset E)
    (μ : E → Measure ℝ≥0) (l : L → ℝ≥0) (r : R → ℝ≥0) (i : L) (j : R) : ℝ :=
  max (Mmat left right opt μ i j - ((l i : ℝ) + r j) * Qmat left right opt μ i j) 0

noncomputable def kap (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0)
    (l : L → ℝ≥0) (r : R → ℝ≥0) (e : E) : ℝ :=
  ∫ x, max ((x : ℝ) - l (left e) - r (right e)) 0 ∂(μ e)

noncomputable def Gf (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E)
    (e : E) (u : E → ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (if e ∈ vaddAccepted left right l r σ u then
    max ((u e : ℝ) - l (left e) - r (right e)) 0 else 0)

theorem Gf_meas (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E)
    (e : E) : Measurable (Gf left right l r σ e) := by
  unfold Gf
  refine ENNReal.measurable_ofReal.comp (Measurable.ite (meas_acc left right l r σ e) ?_
    measurable_const)
  fun_prop

theorem marg_int (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (G : (E → ℝ≥0) → ℝ≥0∞) (hG : Measurable G) (e : E) :
    ∫⁻ v, lmarginal μ {e} G v ∂(Measure.pi μ) = ∫⁻ v, G v ∂(Measure.pi μ) := by
  apply lintegral_eq_of_lmarginal_eq (μ := μ) (s := {e}) (Measurable.lmarginal (μ := μ) hG) hG
  ext x
  rw [lmarginal_singleton (μ := μ) (lmarginal μ {e} G) e]
  beta_reduce
  have h : ∀ y : ℝ≥0, lmarginal μ {e} G (Function.update x e y) = lmarginal μ {e} G x :=
    fun y => lmarginal_update_of_mem (μ := μ) (Finset.mem_singleton_self e) G x y
  simp_rw [h]
  rw [lintegral_const, measure_univ, mul_one]

theorem lemma31 (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0)
    [∀ e, IsProbabilityMeasure (μ e)] (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤)
    (opt : (E → ℝ≥0) → Finset E) (hopt : IsOptSelector left right opt)
    (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) (hσ : IsOrder σ) :
    ∫ v, ∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ, ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ,
        max (Mmat left right opt μ i j - ((l i : ℝ) + r j) * Qmat left right opt μ i j) 0
        ∂(Measure.pi μ) ≤
      ∫ v, ∑ e ∈ vaddAccepted left right l r σ v,
        max ((v e : ℝ) - l (left e) - r (right e)) 0 ∂(Measure.pi μ) := by
  obtain ⟨hnd, hall⟩ := hσ
  show ∫ v, ∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ, ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ,
      cM left right opt μ l r i j ∂(Measure.pi μ) ≤ _
  have hκ0 : ∀ e, 0 ≤ kap left right μ l r e := fun e =>
    integral_nonneg (fun x => le_max_right _ _)
  have hc0 : ∀ i j, 0 ≤ cM left right opt μ l r i j := fun i j => le_max_right _ _
  -- pointwise bound by the uncovered edges
  have step1 : ∀ v, ∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ,
      ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ, cM left right opt μ l r i j ≤
      ∑ e, (if left e ∉ vaddCoveredL left right l r σ v ∧ right e ∉ vaddCoveredR left right l r σ v
        then kap left right μ l r e else 0) := by
    intro v
    obtain ⟨A, hA⟩ : ∃ A, A = (vaddCoveredL left right l r σ v)ᶜ := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, B = (vaddCoveredR left right l r σ v)ᶜ := ⟨_, rfl⟩
    have hunc : ∀ e, (left e ∉ vaddCoveredL left right l r σ v ∧
        right e ∉ vaddCoveredR left right l r σ v) ↔ (left e ∈ A ∧ right e ∈ B) := by
      intro e
      rw [hA, hB, Finset.mem_compl, Finset.mem_compl]
    rw [← hA, ← hB]
    have hsum : ∑ e, (if left e ∉ vaddCoveredL left right l r σ v ∧
        right e ∉ vaddCoveredR left right l r σ v then kap left right μ l r e else 0) =
        ∑ e ∈ Finset.univ.filter (fun e => left e ∈ A ∧ right e ∈ B), kap left right μ l r e := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : left e ∈ A ∧ right e ∈ B
      · rw [if_pos ((hunc e).mpr h), if_pos h]
      · rw [if_neg (fun h' => h ((hunc e).mp h')), if_neg h]
    rw [hsum]
    calc ∑ i ∈ A, ∑ j ∈ B, cM left right opt μ l r i j
        ≤ ∑ i ∈ A, ∑ j ∈ B, ∑ e ∈ Finset.univ.filter (fun e => left e = i ∧ right e = j),
            kap left right μ l r e := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact max_le (MQ_bound left right μ hμ opt hopt l r i j)
            (Finset.sum_nonneg (fun e _ => hκ0 e))
      _ = ∑ i ∈ A, ∑ j ∈ B, ∑ e ∈ ((Finset.univ.filter (fun e => left e ∈ A ∧ right e ∈ B)).filter
            (fun e => left e = i)).filter (fun e => right e = j), kap left right μ l r e := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          congr 1
          ext e
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨⟨⟨by rw [h1]; exact hi, by rw [h2]; exact hj⟩, h1⟩, h2⟩
          · rintro ⟨⟨_, h1⟩, h2⟩
            exact ⟨h1, h2⟩
      _ = ∑ i ∈ A, ∑ e ∈ (Finset.univ.filter (fun e => left e ∈ A ∧ right e ∈ B)).filter
            (fun e => left e = i), kap left right μ l r e := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_fiberwise_of_maps_to
          intro e he
          rw [Finset.mem_filter, Finset.mem_filter] at he
          exact he.1.2.2
      _ = ∑ e ∈ Finset.univ.filter (fun e => left e ∈ A ∧ right e ∈ B), kap left right μ l r e := by
          apply Finset.sum_fiberwise_of_maps_to
          intro e he
          rw [Finset.mem_filter] at he
          exact he.2.1
  -- each uncovered edge is paid by the marginal of the modified run
  have step2 : ∀ v e, (if left e ∉ vaddCoveredL left right l r σ v ∧
      right e ∉ vaddCoveredR left right l r σ v then ENNReal.ofReal (kap left right μ l r e)
        else 0) ≤ lmarginal μ {e} (Gf left right l r σ e) v := by
    intro v e
    by_cases h : left e ∉ vaddCoveredL left right l r σ v ∧
        right e ∉ vaddCoveredR left right l r σ v
    · rw [if_pos h, lmarginal_singleton (μ := μ) (Gf left right l r σ e) e]
      beta_reduce
      unfold kap
      rw [ofReal_integral_eq_lintegral_ofReal (integ_pp μ hμ e _ _)
        (Filter.Eventually.of_forall (fun x => le_max_right _ _))]
      apply lintegral_mono
      intro x
      unfold Gf
      beta_reduce
      by_cases hx : l (left e) + r (right e) ≤ x
      · have hacc : e ∈ vaddAccepted left right l r σ (Function.update v e x) :=
          accept_lemma left right l r v σ hnd e (hall e) x hx h.1 h.2
        rw [if_pos hacc, Function.update_self] <;> exact le_rfl
      · have hlt : (x : ℝ) < (l (left e) : ℝ) + (r (right e) : ℝ) := by
          rw [not_le] at hx
          exact_mod_cast hx
        have h0 : max ((x : ℝ) - l (left e) - r (right e)) 0 = 0 := max_eq_right (by linarith)
        rw [h0, ENNReal.ofReal_zero]
        exact zero_le
    · rw [if_neg h]
      exact zero_le
  -- measurability and integrability
  have hSm : ∀ i j, MeasurableSet {v : E → ℝ≥0 | i ∉ vaddCoveredL left right l r σ v ∧
      j ∉ vaddCoveredR left right l r σ v} := fun i j =>
    (meas_covL left right l r σ i).compl.inter (meas_covR left right l r σ j).compl
  have hAeq : ∀ v, ∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ,
      ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ, cM left right opt μ l r i j =
      ∑ i, ∑ j, Set.indicator {v : E → ℝ≥0 | i ∉ vaddCoveredL left right l r σ v ∧
        j ∉ vaddCoveredR left right l r σ v} (fun _ => cM left right opt μ l r i j) v := by
    intro v
    rw [← Finset.sum_compl_add_sum (vaddCoveredL left right l r σ v)]
    have h1 : ∑ i ∈ vaddCoveredL left right l r σ v, ∑ j,
        Set.indicator {v : E → ℝ≥0 | i ∉ vaddCoveredL left right l r σ v ∧
          j ∉ vaddCoveredR left right l r σ v} (fun _ => cM left right opt μ l r i j) v = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j _
      exact Set.indicator_of_notMem (fun h => h.1 hi) _
    rw [h1, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_compl_add_sum (vaddCoveredR left right l r σ v)]
    have h2 : ∑ j ∈ vaddCoveredR left right l r σ v,
        Set.indicator {v : E → ℝ≥0 | i ∉ vaddCoveredL left right l r σ v ∧
          j ∉ vaddCoveredR left right l r σ v} (fun _ => cM left right opt μ l r i j) v = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact Set.indicator_of_notMem (fun h => h.2 hj) _
    rw [h2, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_compl] at hi hj
    rw [Set.indicator_of_mem (show v ∈ {v : E → ℝ≥0 | i ∉ vaddCoveredL left right l r σ v ∧
      j ∉ vaddCoveredR left right l r σ v} from ⟨hi, hj⟩)]
  have hBeq : ∀ v : E → ℝ≥0, ∑ e ∈ vaddAccepted left right l r σ v,
      max ((v e : ℝ) - l (left e) - r (right e)) 0 =
      ∑ e, Set.indicator {v : E → ℝ≥0 | e ∈ vaddAccepted left right l r σ v}
        (fun v => max ((v e : ℝ) - l (left e) - r (right e)) 0) v := by
    intro v
    rw [← Finset.sum_compl_add_sum (vaddAccepted left right l r σ v)]
    have h1 : ∑ e ∈ (vaddAccepted left right l r σ v)ᶜ,
        Set.indicator {v : E → ℝ≥0 | e ∈ vaddAccepted left right l r σ v}
          (fun v => max ((v e : ℝ) - l (left e) - r (right e)) 0) v = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [Finset.mem_compl] at he
      exact Set.indicator_of_notMem
        (show v ∉ {v : E → ℝ≥0 | e ∈ vaddAccepted left right l r σ v} from he) _
    rw [h1, zero_add]
    apply Finset.sum_congr rfl
    intro e he
    rw [Set.indicator_of_mem (show v ∈ {v : E → ℝ≥0 | e ∈ vaddAccepted left right l r σ v}
      from he)]
  have hAint : Integrable (fun v => ∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ,
      ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ, cM left right opt μ l r i j) (Measure.pi μ) := by
    have h : Integrable (fun v => ∑ i, ∑ j, Set.indicator {v : E → ℝ≥0 |
        i ∉ vaddCoveredL left right l r σ v ∧ j ∉ vaddCoveredR left right l r σ v}
        (fun _ => cM left right opt μ l r i j) v) (Measure.pi μ) :=
      integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
        (integrable_const _).indicator (hSm i j)))
    exact h.congr (Filter.Eventually.of_forall (fun v => (hAeq v).symm))
  have hBint : Integrable (fun v : E → ℝ≥0 => ∑ e ∈ vaddAccepted left right l r σ v,
      max ((v e : ℝ) - l (left e) - r (right e)) 0) (Measure.pi μ) := by
    have h : Integrable (fun v : E → ℝ≥0 => ∑ e, Set.indicator
        {v : E → ℝ≥0 | e ∈ vaddAccepted left right l r σ v}
        (fun v => max ((v e : ℝ) - l (left e) - r (right e)) 0) v) (Measure.pi μ) :=
      integrable_finsetSum _ (fun e _ =>
        (integrable_comp_eval (μ := μ) (i := e)
          (f := fun x : ℝ≥0 => max ((x : ℝ) - l (left e) - r (right e)) 0)
          (integ_pp μ hμ e (l (left e)) (r (right e)))).indicator
          (meas_acc left right l r σ e))
    exact h.congr (Filter.Eventually.of_forall (fun v => (hBeq v).symm))
  have hA0 : ∀ v, 0 ≤ ∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ,
      ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ, cM left right opt μ l r i j := fun v =>
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hc0 i j))
  have hB0 : ∀ v : E → ℝ≥0, 0 ≤ ∑ e ∈ vaddAccepted left right l r σ v,
      max ((v e : ℝ) - l (left e) - r (right e)) 0 := fun v =>
    Finset.sum_nonneg (fun e _ => le_max_right _ _)
  -- lintegral comparison
  have hlin : ∫⁻ v, ENNReal.ofReal (∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ,
      ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ, cM left right opt μ l r i j) ∂(Measure.pi μ) ≤
      ∫⁻ v, ENNReal.ofReal (∑ e ∈ vaddAccepted left right l r σ v,
        max ((v e : ℝ) - l (left e) - r (right e)) 0) ∂(Measure.pi μ) := by
    calc ∫⁻ v, ENNReal.ofReal (∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ,
          ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ, cM left right opt μ l r i j) ∂(Measure.pi μ)
        ≤ ∫⁻ v, ∑ e, lmarginal μ {e} (Gf left right l r σ e) v ∂(Measure.pi μ) := by
          apply lintegral_mono
          intro v
          calc ENNReal.ofReal (∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ,
                ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ, cM left right opt μ l r i j)
              ≤ ENNReal.ofReal (∑ e, (if left e ∉ vaddCoveredL left right l r σ v ∧
                  right e ∉ vaddCoveredR left right l r σ v
                  then kap left right μ l r e else 0)) := ENNReal.ofReal_le_ofReal (step1 v)
            _ = ∑ e, ENNReal.ofReal (if left e ∉ vaddCoveredL left right l r σ v ∧
                  right e ∉ vaddCoveredR left right l r σ v
                  then kap left right μ l r e else 0) := by
                rw [ENNReal.ofReal_sum_of_nonneg]
                intro e _
                split_ifs
                · exact hκ0 e
                · exact le_refl _
            _ ≤ ∑ e, lmarginal μ {e} (Gf left right l r σ e) v := by
                apply Finset.sum_le_sum
                intro e _
                refine le_trans ?_ (step2 v e)
                split_ifs
                · exact le_refl _
                · rw [ENNReal.ofReal_zero]
      _ = ∑ e, ∫⁻ v, lmarginal μ {e} (Gf left right l r σ e) v ∂(Measure.pi μ) :=
          lintegral_finsetSum _ (fun e _ => Measurable.lmarginal (μ := μ) (Gf_meas left right l r σ e))
      _ = ∑ e, ∫⁻ v, Gf left right l r σ e v ∂(Measure.pi μ) := by
          apply Finset.sum_congr rfl
          intro e _
          exact marg_int μ _ (Gf_meas left right l r σ e) e
      _ = ∫⁻ v, ∑ e, Gf left right l r σ e v ∂(Measure.pi μ) :=
          (lintegral_finsetSum _ (fun e _ => Gf_meas left right l r σ e)).symm
      _ = ∫⁻ v, ENNReal.ofReal (∑ e ∈ vaddAccepted left right l r σ v,
            max ((v e : ℝ) - l (left e) - r (right e)) 0) ∂(Measure.pi μ) := by
          apply lintegral_congr
          intro v
          unfold Gf
          rw [← ENNReal.ofReal_sum_of_nonneg (fun e _ => by split_ifs <;> simp)]
          congr 1
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext e
          simp
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg hB0),
    ofReal_integral_eq_lintegral_ofReal hAint (Filter.Eventually.of_forall hA0),
    ofReal_integral_eq_lintegral_ofReal hBint (Filter.Eventually.of_forall hB0)]
  exact hlin

end final

section extra
variable {L R E : Type*} [DecidableEq L] [DecidableEq R] [DecidableEq E]

def Inv (left : E → L) (l : L → ℝ≥0) (right : E → R) (r : R → ℝ≥0)
    (s : RunState L R E) : Prop :=
  (∑ e ∈ s.accepted, (l (left e) + r (right e)) =
    ∑ i ∈ s.coveredL, l i + ∑ j ∈ s.coveredR, r j) ∧ ∀ e ∈ s.accepted, left e ∈ s.coveredL

theorem inv_step (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (v : E → ℝ≥0)
    (s : RunState L R E) (e : E) (hs : Inv left l right r s) :
    Inv left l right r (vaddStep left right l r v s e) := by
  unfold vaddStep
  split_ifs with h
  · obtain ⟨hL, hR, _⟩ := h
    have he : e ∉ s.accepted := fun he => hL (hs.2 e he)
    refine ⟨?_, ?_⟩
    · show ∑ x ∈ insert e s.accepted, (l (left x) + r (right x)) =
        ∑ i ∈ insert (left e) s.coveredL, l i + ∑ j ∈ insert (right e) s.coveredR, r j
      rw [Finset.sum_insert he, Finset.sum_insert hL, Finset.sum_insert hR, hs.1]
      ring
    · intro e' he'
      show left e' ∈ insert (left e) s.coveredL
      rcases Finset.mem_insert.mp he' with rfl | h'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hs.2 e' h')
  · exact hs

theorem inv_fold (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (v : E → ℝ≥0)
    (σ : List E) : ∀ s : RunState L R E, Inv left l right r s →
      Inv left l right r (σ.foldl (vaddStep left right l r v) s) := by
  induction σ with
  | nil => intro s hs; exact hs
  | cons e σ ih => intro s hs; exact ih _ (inv_step left right l r v s e hs)

theorem accInv (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (v : E → ℝ≥0)
    (σ : List E) : ∀ s : RunState L R E,
      (∀ e ∈ s.accepted, l (left e) + r (right e) ≤ v e) →
      ∀ e ∈ (σ.foldl (vaddStep left right l r v) s).accepted, l (left e) + r (right e) ≤ v e := by
  induction σ with
  | nil => intro s hs; exact hs
  | cons e σ ih =>
    intro s hs
    apply ih
    intro e' he'
    unfold vaddStep at he'
    split_ifs at he' with h
    · rcases Finset.mem_insert.mp he' with rfl | h'
      · exact h.2.2
      · exact hs e' h'
    · exact hs e' he'

theorem decomp (left : E → L) (right : E → R) (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E)
    (v : E → ℝ≥0) :
    (vaddValue left right l r σ v : ℝ) =
      (∑ i ∈ vaddCoveredL left right l r σ v, (l i : ℝ) +
        ∑ j ∈ vaddCoveredR left right l r σ v, (r j : ℝ)) +
      ∑ e ∈ vaddAccepted left right l r σ v, max ((v e : ℝ) - l (left e) - r (right e)) 0 := by
  have h0 : Inv left l right r (⟨∅, ∅, ∅⟩ : RunState L R E) := by
    refine ⟨?_, ?_⟩
    · simp
    · intro e he
      simp at he
  have hI := (inv_fold left right l r v σ _ h0).1
  have hA := accInv left right l r v σ ⟨∅, ∅, ∅⟩ (by intro e he; simp at he)
  have hI' : ∑ e ∈ vaddAccepted left right l r σ v, ((l (left e) : ℝ) + (r (right e) : ℝ)) =
      ∑ i ∈ vaddCoveredL left right l r σ v, (l i : ℝ) +
        ∑ j ∈ vaddCoveredR left right l r σ v, (r j : ℝ) := by
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) hI
    simp only [NNReal.coe_sum, NNReal.coe_add] at this
    exact this
  rw [← hI']
  unfold vaddValue
  rw [NNReal.coe_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hle : (l (left e) : ℝ) + (r (right e) : ℝ) ≤ (v e : ℝ) := by
    have := hA e he
    exact_mod_cast this
  rw [max_eq_left (by linarith)]
  ring

end extra

section ints
variable {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
  [DecidableEq L] [DecidableEq R] [DecidableEq E]

theorem sum_ind {α : Type*} [Fintype α] [DecidableEq α] (S : (E → ℝ≥0) → Finset α)
    (c : α → (E → ℝ≥0) → ℝ) (v : E → ℝ≥0) :
    ∑ i ∈ S v, c i v = ∑ i, Set.indicator {v : E → ℝ≥0 | i ∈ S v} (c i) v := by
  rw [← Finset.sum_compl_add_sum (S v)]
  have h1 : ∑ i ∈ (S v)ᶜ, Set.indicator {v : E → ℝ≥0 | i ∈ S v} (c i) v = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_compl] at hi
    exact Set.indicator_of_notMem (show v ∉ {v : E → ℝ≥0 | i ∈ S v} from hi) _
  rw [h1, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Set.indicator_of_mem (show v ∈ {v : E → ℝ≥0 | i ∈ S v} from hi)]

theorem intK (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0)
    [∀ e, IsProbabilityMeasure (μ e)] (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) :
    Integrable (fun v : E → ℝ≥0 => ∑ i ∈ vaddCoveredL left right l r σ v, (l i : ℝ) +
      ∑ j ∈ vaddCoveredR left right l r σ v, (r j : ℝ)) (Measure.pi μ) := by
  have h1 : Integrable (fun v : E → ℝ≥0 => ∑ i, Set.indicator
      {v : E → ℝ≥0 | i ∈ vaddCoveredL left right l r σ v} (fun _ => (l i : ℝ)) v)
      (Measure.pi μ) :=
    integrable_finsetSum _ (fun i _ => (integrable_const _).indicator (meas_covL left right l r σ i))
  have h2 : Integrable (fun v : E → ℝ≥0 => ∑ j, Set.indicator
      {v : E → ℝ≥0 | j ∈ vaddCoveredR left right l r σ v} (fun _ => (r j : ℝ)) v)
      (Measure.pi μ) :=
    integrable_finsetSum _ (fun j _ => (integrable_const _).indicator (meas_covR left right l r σ j))
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun v => ?_)
  show (∑ i, Set.indicator {v : E → ℝ≥0 | i ∈ vaddCoveredL left right l r σ v}
      (fun _ => (l i : ℝ)) v) + (∑ j, Set.indicator
      {v : E → ℝ≥0 | j ∈ vaddCoveredR left right l r σ v} (fun _ => (r j : ℝ)) v) = _
  rw [← sum_ind (fun v => vaddCoveredL left right l r σ v) (fun i _ => (l i : ℝ)) v,
    ← sum_ind (fun v => vaddCoveredR left right l r σ v) (fun j _ => (r j : ℝ)) v]

end ints


section intab
variable {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
  [DecidableEq L] [DecidableEq R] [DecidableEq E]

theorem intAB (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0)
    [∀ e, IsProbabilityMeasure (μ e)] (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤)
    (opt : (E → ℝ≥0) → Finset E)
    (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) :
    Integrable (fun v => ∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ,
      ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ,
        max (Mmat left right opt μ i j - ((l i : ℝ) + r j) * Qmat left right opt μ i j) 0)
      (Measure.pi μ) ∧
    Integrable (fun v : E → ℝ≥0 => ∑ e ∈ vaddAccepted left right l r σ v,
      max ((v e : ℝ) - l (left e) - r (right e)) 0) (Measure.pi μ) := by
  have hSm : ∀ i j, MeasurableSet {v : E → ℝ≥0 | i ∉ vaddCoveredL left right l r σ v ∧
      j ∉ vaddCoveredR left right l r σ v} := fun i j =>
    (meas_covL left right l r σ i).compl.inter (meas_covR left right l r σ j).compl
  have hAeq : ∀ v, ∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ,
      ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ, cM left right opt μ l r i j =
      ∑ i, ∑ j, Set.indicator {v : E → ℝ≥0 | i ∉ vaddCoveredL left right l r σ v ∧
        j ∉ vaddCoveredR left right l r σ v} (fun _ => cM left right opt μ l r i j) v := by
    intro v
    rw [← Finset.sum_compl_add_sum (vaddCoveredL left right l r σ v)]
    have h1 : ∑ i ∈ vaddCoveredL left right l r σ v, ∑ j,
        Set.indicator {v : E → ℝ≥0 | i ∉ vaddCoveredL left right l r σ v ∧
          j ∉ vaddCoveredR left right l r σ v} (fun _ => cM left right opt μ l r i j) v = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j _
      exact Set.indicator_of_notMem (fun h => h.1 hi) _
    rw [h1, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_compl_add_sum (vaddCoveredR left right l r σ v)]
    have h2 : ∑ j ∈ vaddCoveredR left right l r σ v,
        Set.indicator {v : E → ℝ≥0 | i ∉ vaddCoveredL left right l r σ v ∧
          j ∉ vaddCoveredR left right l r σ v} (fun _ => cM left right opt μ l r i j) v = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact Set.indicator_of_notMem (fun h => h.2 hj) _
    rw [h2, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_compl] at hi hj
    rw [Set.indicator_of_mem (show v ∈ {v : E → ℝ≥0 | i ∉ vaddCoveredL left right l r σ v ∧
      j ∉ vaddCoveredR left right l r σ v} from ⟨hi, hj⟩)]
  have hBeq : ∀ v : E → ℝ≥0, ∑ e ∈ vaddAccepted left right l r σ v,
      max ((v e : ℝ) - l (left e) - r (right e)) 0 =
      ∑ e, Set.indicator {v : E → ℝ≥0 | e ∈ vaddAccepted left right l r σ v}
        (fun v => max ((v e : ℝ) - l (left e) - r (right e)) 0) v := by
    intro v
    rw [← Finset.sum_compl_add_sum (vaddAccepted left right l r σ v)]
    have h1 : ∑ e ∈ (vaddAccepted left right l r σ v)ᶜ,
        Set.indicator {v : E → ℝ≥0 | e ∈ vaddAccepted left right l r σ v}
          (fun v => max ((v e : ℝ) - l (left e) - r (right e)) 0) v = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [Finset.mem_compl] at he
      exact Set.indicator_of_notMem
        (show v ∉ {v : E → ℝ≥0 | e ∈ vaddAccepted left right l r σ v} from he) _
    rw [h1, zero_add]
    apply Finset.sum_congr rfl
    intro e he
    rw [Set.indicator_of_mem (show v ∈ {v : E → ℝ≥0 | e ∈ vaddAccepted left right l r σ v}
      from he)]
  have hAint : Integrable (fun v => ∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ,
      ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ, cM left right opt μ l r i j) (Measure.pi μ) := by
    have h : Integrable (fun v => ∑ i, ∑ j, Set.indicator {v : E → ℝ≥0 |
        i ∉ vaddCoveredL left right l r σ v ∧ j ∉ vaddCoveredR left right l r σ v}
        (fun _ => cM left right opt μ l r i j) v) (Measure.pi μ) :=
      integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
        (integrable_const _).indicator (hSm i j)))
    exact h.congr (Filter.Eventually.of_forall (fun v => (hAeq v).symm))
  have hBint : Integrable (fun v : E → ℝ≥0 => ∑ e ∈ vaddAccepted left right l r σ v,
      max ((v e : ℝ) - l (left e) - r (right e)) 0) (Measure.pi μ) := by
    have h : Integrable (fun v : E → ℝ≥0 => ∑ e, Set.indicator
        {v : E → ℝ≥0 | e ∈ vaddAccepted left right l r σ v}
        (fun v => max ((v e : ℝ) - l (left e) - r (right e)) 0) v) (Measure.pi μ) :=
      integrable_finsetSum _ (fun e _ =>
        (integrable_comp_eval (μ := μ) (i := e)
          (f := fun x : ℝ≥0 => max ((x : ℝ) - l (left e) - r (right e)) 0)
          (integ_pp μ hμ e (l (left e)) (r (right e)))).indicator
          (meas_acc left right l r σ e))
    exact h.congr (Filter.Eventually.of_forall (fun v => (hBeq v).symm))
  exact ⟨hAint, hBint⟩

noncomputable def Ffun (left : E → L) (right : E → R) (opt : (E → ℝ≥0) → Finset E)
    (μ : E → Measure ℝ≥0) (l : L → ℝ≥0) (r : R → ℝ≥0) (S : Finset L × Finset R) : ℝ :=
  ∑ i ∈ S.1, (l i : ℝ) + ∑ j ∈ S.2, (r j : ℝ) +
    ∑ i ∈ S.1ᶜ, ∑ j ∈ S.2ᶜ,
      max (Mmat left right opt μ i j - ((l i : ℝ) + r j) * Qmat left right opt μ i j) 0

end intab

end Aux_PB31

open ProphetBipartite in
theorem solution {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤)
    (opt : (E → ℝ≥0) → Finset E) (hopt : IsOptSelector left right opt)
    (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) (hσ : IsOrder σ) :
    (Finset.univ : Finset (Finset L × Finset R)).inf' Finset.univ_nonempty
        (fun S => ∑ i ∈ S.1, (l i : ℝ) + ∑ j ∈ S.2, (r j : ℝ) +
          ∑ i ∈ S.1ᶜ, ∑ j ∈ S.2ᶜ,
            max (Mmat left right opt μ i j - ((l i : ℝ) + r j) * Qmat left right opt μ i j) 0) ≤
      ∫ v, (vaddValue left right l r σ v : ℝ) ∂(Measure.pi μ) := by
  show (Finset.univ : Finset (Finset L × Finset R)).inf' Finset.univ_nonempty
    (Aux_PB31.Ffun left right opt μ l r) ≤ _
  obtain ⟨hA, hB⟩ := Aux_PB31.intAB left right μ hμ opt l r σ
  have hK := Aux_PB31.intK left right μ l r σ
  have h31 := Aux_PB31.lemma31 left right μ hμ opt hopt l r σ hσ
  have hconst : ∀ c : ℝ, ∫ _v : E → ℝ≥0, c ∂(Measure.pi μ) = c := fun c => by simp
  have hFint : Integrable (fun v => Aux_PB31.Ffun left right opt μ l r
      (vaddCoveredL left right l r σ v, vaddCoveredR left right l r σ v)) (Measure.pi μ) :=
    hK.add hA
  calc (Finset.univ : Finset (Finset L × Finset R)).inf' Finset.univ_nonempty
        (Aux_PB31.Ffun left right opt μ l r)
      = ∫ _v : E → ℝ≥0, (Finset.univ : Finset (Finset L × Finset R)).inf' Finset.univ_nonempty
          (Aux_PB31.Ffun left right opt μ l r) ∂(Measure.pi μ) := (hconst _).symm
    _ ≤ ∫ v, Aux_PB31.Ffun left right opt μ l r
          (vaddCoveredL left right l r σ v, vaddCoveredR left right l r σ v) ∂(Measure.pi μ) :=
        integral_mono (integrable_const _) hFint
          (fun v => Finset.inf'_le _ (Finset.mem_univ _))
    _ = ∫ v, (∑ i ∈ vaddCoveredL left right l r σ v, (l i : ℝ) +
            ∑ j ∈ vaddCoveredR left right l r σ v, (r j : ℝ)) ∂(Measure.pi μ) +
        ∫ v, ∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ, ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ,
          max (Mmat left right opt μ i j - ((l i : ℝ) + r j) * Qmat left right opt μ i j) 0
          ∂(Measure.pi μ) := integral_add hK hA
    _ ≤ ∫ v, (∑ i ∈ vaddCoveredL left right l r σ v, (l i : ℝ) +
            ∑ j ∈ vaddCoveredR left right l r σ v, (r j : ℝ)) ∂(Measure.pi μ) +
        ∫ v, ∑ e ∈ vaddAccepted left right l r σ v,
          max ((v e : ℝ) - l (left e) - r (right e)) 0 ∂(Measure.pi μ) := by linarith
    _ = ∫ v, ((∑ i ∈ vaddCoveredL left right l r σ v, (l i : ℝ) +
            ∑ j ∈ vaddCoveredR left right l r σ v, (r j : ℝ)) +
          ∑ e ∈ vaddAccepted left right l r σ v,
            max ((v e : ℝ) - l (left e) - r (right e)) 0) ∂(Measure.pi μ) :=
        (integral_add hK hB).symm
    _ = ∫ v, (vaddValue left right l r σ v : ℝ) ∂(Measure.pi μ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun v =>
          (Aux_PB31.decomp left right l r σ v).symm)
