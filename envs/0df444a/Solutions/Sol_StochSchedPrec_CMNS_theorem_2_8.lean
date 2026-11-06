-- Prove2me | solution 1 for StochSchedPrec.CMNS.theorem_2_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T17:34:18.329438+00:00
-- url     : https://prove2.me/submissions/baf74dca-60fe-48f2-98f9-8615af1f33fd

import Mathlib
import Definitions.Def_StochSchedPrec_CMNS_Model
import Definitions.Def_StochSchedPrec_CMNS_Algorithm
import Theorems.Thm_StochSchedPrec_CMNS_lemma_2_5
import Theorems.Thm_StochSchedPrec_CMNS_lemma_2_6
import Theorems.Thm_StochSchedPrec_CMNS_lemma_2_7

open MeasureTheory ProbabilityTheory

open StochSchedPrec.CMNS in
theorem SSP28aux_chain_meas {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop) (r : V → ℝ)
    (tb : V ≃ Fin (Fintype.card V)) :
    ∀ n j, Measurable (fun x : (V → ℝ) × (V → ℝ) => chainLengthAux A r tb x.1 x.2 n j) := by
  classical
  have hlt : ∀ f g : (V → ℝ) × (V → ℝ) → ℝ, Measurable f → Measurable g →
      Measurable fun x => f x < g x :=
    fun f g hf hg => measurableSet_setOfPred.1 (measurableSet_lt hf hg)
  have hle : ∀ f g : (V → ℝ) × (V → ℝ) → ℝ, Measurable f → Measurable g →
      Measurable fun x => f x ≤ g x :=
    fun f g hf hg => measurableSet_setOfPred.1 (measurableSet_le hf hg)
  have hc : ∀ i, Measurable (fun x : (V → ℝ) × (V → ℝ) => x.2 i + x.1 i) := fun i =>
    ((measurable_pi_apply i).comp measurable_snd).add ((measurable_pi_apply i).comp measurable_fst)
  intro n
  induction n with
  | zero =>
    intro j
    exact measurable_const.add ((measurable_pi_apply j).comp measurable_fst)
  | succ n ih =>
    intro j
    let Mf : (V → ℝ) × (V → ℝ) → Finset V := fun x => Finset.univ.filter fun i =>
      Relation.TransGen A i j ∧ r j < x.2 i + x.1 i ∧
        ∀ i', Relation.TransGen A i' j → x.2 i' + x.1 i' ≤ x.2 i + x.1 i
    let Φ : Finset V → Option V := fun T =>
      if h : T.Nonempty then some (tb.symm ((T.image tb).min' (h.image tb))) else none
    let Ψ : Finset V → (V → ℝ) × (V → ℝ) → ℝ := fun T x =>
      match Φ T with
      | none => r j + x.1 j
      | some i => x.1 j + chainLengthAux A r tb x.1 x.2 n i
    have hcp : ∀ x : (V → ℝ) × (V → ℝ), critPred A r tb x.1 x.2 j = Φ (Mf x) := by
      intro x
      unfold critPred
      simp only [Φ, Mf]
    have heq : (fun x : (V → ℝ) × (V → ℝ) => chainLengthAux A r tb x.1 x.2 (n + 1) j)
        = fun x => ∑ T : Finset V, if Mf x = T then Ψ T x else 0 := by
      funext x
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true, chainLengthAux, hcp x, Ψ]
      rfl
    rw [heq]
    refine Finset.measurable_fun_sum _ (fun T _ => ?_)
    refine Measurable.ite ?_ ?_ measurable_const
    · have : {x : (V → ℝ) × (V → ℝ) | Mf x = T} = {x | ∀ i, (Relation.TransGen A i j ∧
          r j < x.2 i + x.1 i ∧ ∀ i', Relation.TransGen A i' j → x.2 i' + x.1 i' ≤ x.2 i + x.1 i)
            ↔ i ∈ T} := by
        ext x
        simp only [Set.mem_setOf_eq, Finset.ext_iff, Mf, Finset.mem_filter, Finset.mem_univ,
          true_and]
      rw [this]
      refine measurableSet_setOfPred.2 (Measurable.forall fun i => Measurable.iff ?_ measurable_const)
      refine Measurable.and measurable_const (Measurable.and (hlt _ _ measurable_const (hc i)) ?_)
      exact Measurable.forall fun i' => Measurable.imp measurable_const (hle _ _ (hc i') (hc i))
    · simp only [Ψ]
      cases Φ T with
      | none => exact measurable_const.add ((measurable_pi_apply j).comp measurable_fst)
      | some i => exact ((measurable_pi_apply j).comp measurable_fst).add (ih i)

open StochSchedPrec.CMNS in
theorem SSP28aux_chain_bound {V : Type*} [Fintype V] [DecidableEq V] (A : V → V → Prop)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (tb : V ≃ Fin (Fintype.card V)) (p S : V → ℝ)
    (hp : ∀ j, 0 ≤ p j) :
    ∀ n j, 0 ≤ chainLengthAux A r tb p S n j ∧
      chainLengthAux A r tb p S n j ≤ ∑ k, r k + (n + 1) * ∑ k, p k := by
  have hrs : ∀ j, r j ≤ ∑ k, r k := fun j =>
    Finset.single_le_sum (fun k _ => hr k) (Finset.mem_univ j)
  have hps : ∀ j, p j ≤ ∑ k, p k := fun j =>
    Finset.single_le_sum (fun k _ => hp k) (Finset.mem_univ j)
  have hP0 : 0 ≤ ∑ k, p k := Finset.sum_nonneg (fun k _ => hp k)
  intro n
  induction n with
  | zero =>
    intro j
    simp only [chainLengthAux]
    refine ⟨add_nonneg (hr j) (hp j), ?_⟩
    simp only [Nat.cast_zero, zero_add, one_mul]
    linarith [hrs j, hps j]
  | succ n ih =>
    intro j
    simp only [chainLengthAux]
    split
    · refine ⟨add_nonneg (hr j) (hp j), ?_⟩
      push_cast
      nlinarith [hrs j, hps j]
    · rename_i i _
      obtain ⟨h1, h2⟩ := ih i
      refine ⟨add_nonneg (hp j) h1, ?_⟩
      push_cast
      nlinarith [hps j]

open StochSchedPrec.CMNS in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : ∀ j, ¬ Relation.TransGen A j j)
    (r : V → ℝ) (hr : ∀ j, 0 ≤ r j) (hAss : ∀ i j, Relation.TransGen A i j → r i ≤ r j)
    (P : V → Ω → ℝ) (hP : IsStochModel Pr P)
    (L : Fin (Fintype.card V) ≃ V) (hLE : IsLinearExtension A L) (β : ℝ) (hβ : 0 < β)
    (tb : V ≃ Fin (Fintype.card V))
    (σ : (V → ℝ) → V → ℝ) (hσ : IsCMNSPolicy m A r L β (fun j => ∫ ω, P j ω ∂Pr) σ)
    (hσna : IsNonanticipatory σ)
    (hσm : AEMeasurable σ (Pr.map (fun ω k => P k ω))) (j : V) :
    Integrable (fun ω => σ (fun k => P k ω) j + P j ω) Pr ∧
    ∫ ω, (σ (fun k => P k ω) j + P j ω) ∂Pr
      ≤ (((m : ℝ) - 1) / m + 1 / β)
          * ∫ ω, chainLength A r tb (fun k => P k ω) (σ (fun k => P k ω)) j ∂Pr
        + (1 + β) / m * ∑ i ∈ before L j, ∫ ω, P i ω ∂Pr + 1 / (m : ℝ) * r j := by
  set μ : V → ℝ := fun j => ∫ ω, P j ω ∂Pr with hμdef
  have hμnn : ∀ j, 0 ≤ μ j := fun j => integral_nonneg (fun ω => hP.2.1 j ω)
  have hXm : Measurable (fun ω k => P k ω) := measurable_pi_lambda _ (fun k => hP.1 k)
  have hσm' : AEMeasurable (fun ω => σ (fun k => P k ω)) Pr :=
    hσm.comp_aemeasurable hXm.aemeasurable
  have hY : AEMeasurable (fun ω => ((fun k => P k ω), σ (fun k => P k ω))) Pr :=
    hXm.aemeasurable.prodMk hσm'
  have hpnn : ∀ ω, ∀ k, 0 ≤ (fun k => P k ω) k := fun ω k => hP.2.1 k ω
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- the three random quantities
  set fC : Ω → ℝ := fun ω => σ (fun k => P k ω) j + P j ω with hfC
  set fl : Ω → ℝ := fun ω => chainLength A r tb (fun k => P k ω) (σ (fun k => P k ω)) j with hfl
  set fO : Ω → ℝ := fun ω => ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, P i ω with hfO
  set fOμ : Ω → ℝ := fun ω => ∑ i ∈ outOfOrder L (σ (fun k => P k ω)) j, μ i with hfOμ
  have hsumP : Integrable (fun ω => ∑ k, P k ω) Pr := integrable_finsetSum _ (fun k _ => hP.2.2.1 k)
  -- measurability
  have hflm : AEStronglyMeasurable fl Pr :=
    ((SSP28aux_chain_meas A r tb (Fintype.card V) j).comp_aemeasurable hY).aestronglyMeasurable
  have hOmeas : ∀ c : V → (V → ℝ) × (V → ℝ) → ℝ, (∀ i, Measurable (c i)) →
      Measurable (fun x : (V → ℝ) × (V → ℝ) => ∑ i ∈ outOfOrder L x.2 j, c i x) := by
    intro c hc
    have : (fun x : (V → ℝ) × (V → ℝ) => ∑ i ∈ outOfOrder L x.2 j, c i x)
        = fun x => ∑ i ∈ after L j, if x.2 i < x.2 j then c i x else 0 := by
      funext x
      rw [outOfOrder, Finset.sum_filter]
    rw [this]
    refine Finset.measurable_fun_sum _ (fun i _ => Measurable.ite ?_ (hc i) measurable_const)
    exact measurableSet_lt ((measurable_pi_apply i).comp measurable_snd)
      ((measurable_pi_apply j).comp measurable_snd)
  have hfOm : AEStronglyMeasurable fO Pr :=
    ((hOmeas (fun i x => x.1 i) (fun i => (measurable_pi_apply i).comp measurable_fst)).comp_aemeasurable
      hY).aestronglyMeasurable
  have hfOμm : AEStronglyMeasurable fOμ Pr :=
    ((hOmeas (fun i _ => μ i) (fun i => measurable_const)).comp_aemeasurable hY).aestronglyMeasurable
  have hfCm : AEStronglyMeasurable fC Pr :=
    (((measurable_pi_apply j).comp_aemeasurable hσm').add (hP.1 j).aemeasurable).aestronglyMeasurable
  -- integrability
  have hOsub : ∀ ω, 0 ≤ fO ω ∧ fO ω ≤ ∑ k, P k ω := by
    intro ω
    refine ⟨Finset.sum_nonneg (fun i _ => hP.2.1 i ω), ?_⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hP.2.1 i ω)
  have hfOi : Integrable fO Pr := by
    refine hsumP.mono' hfOm (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hOsub ω).1]
    exact (hOsub ω).2
  have hfOμi : Integrable fOμ Pr := by
    refine (integrable_const (∑ k, μ k)).mono' hfOμm (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => hμnn i))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hμnn i)
  have hlb : ∀ ω, 0 ≤ fl ω ∧ fl ω ≤ ∑ k, r k + ((Fintype.card V : ℕ) + 1) * ∑ k, P k ω := by
    intro ω
    have := SSP28aux_chain_bound A r hr tb (fun k => P k ω) (σ (fun k => P k ω)) (hpnn ω)
      (Fintype.card V) j
    exact this
  have hfli : Integrable fl Pr := by
    refine ((integrable_const (∑ k, r k)).add (hsumP.const_mul ((Fintype.card V : ℕ) + 1 : ℝ))).mono'
      hflm (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hlb ω).1]
    exact (hlb ω).2
  -- the pointwise bound of Lemma 2.5
  set g : Ω → ℝ := fun ω => ((m : ℝ) - 1) / m * fl ω + 1 / (m : ℝ) * r j
      + 1 / (m : ℝ) * (∑ i ∈ before L j, (P i ω + β * μ i) + fO ω) with hg
  have h25 : ∀ ω, fC ω ≤ g ω := fun ω =>
    lemma_2_5 m hm A hacyc r hr hAss L hLE β hβ.le μ hμnn tb (fun k => P k ω) (hpnn ω)
      (σ (fun k => P k ω)) (hσ _ (hpnn ω)) j
  have hBi : Integrable (fun ω => ∑ i ∈ before L j, (P i ω + β * μ i)) Pr :=
    integrable_finsetSum _ (fun i _ => (hP.2.2.1 i).add (integrable_const _))
  have hgi : Integrable g Pr :=
    ((hfli.const_mul _).add (integrable_const _)).add ((hBi.add hfOi).const_mul _)
  have hC0 : ∀ ω, 0 ≤ fC ω := by
    intro ω
    have h1 := ((hσ _ (hpnn ω)).1.1 j)
    have h2 := hr j
    have h3 := hP.2.1 j ω
    simp only [hfC]
    linarith
  have hfCi : Integrable fC Pr := by
    refine hgi.mono' hfCm (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hC0 ω)]
    exact h25 ω
  refine ⟨hfCi, ?_⟩
  have hE1 : ∫ ω, fC ω ∂Pr ≤ ∫ ω, g ω ∂Pr := integral_mono hfCi hgi h25
  have hEg : ∫ ω, g ω ∂Pr = ((m : ℝ) - 1) / m * ∫ ω, fl ω ∂Pr + 1 / (m : ℝ) * r j
      + 1 / (m : ℝ) * (∑ i ∈ before L j, (μ i + β * μ i) + ∫ ω, fO ω ∂Pr) := by
    have I0 : Integrable (fun ω => ((m : ℝ) - 1) / m * fl ω) Pr := hfli.const_mul _
    have I1 : Integrable (fun ω => ((m : ℝ) - 1) / m * fl ω + 1 / (m : ℝ) * r j) Pr :=
      I0.add (integrable_const _)
    have I3 : Integrable (fun ω => ∑ i ∈ before L j, (P i ω + β * μ i) + fO ω) Pr := hBi.add hfOi
    have I2 : Integrable (fun ω => 1 / (m : ℝ) * (∑ i ∈ before L j, (P i ω + β * μ i) + fO ω)) Pr :=
      I3.const_mul _
    simp only [hg]
    rw [integral_add I1 I2, integral_add I0 (integrable_const _), integral_const_mul,
      integral_const_mul, integral_const, integral_const_mul, integral_add hBi hfOi,
      integral_finsetSum (f := fun i ω => P i ω + β * μ i) _
        (fun i _ => (hP.2.2.1 i).add (integrable_const (β * μ i)))]
    have hB : ∀ i, ∫ ω, (P i ω + β * μ i) ∂Pr = μ i + β * μ i := by
      intro i
      rw [integral_add (hP.2.2.1 i) (integrable_const _), integral_const]
      simp [μ]
    simp only [hB, probReal_univ, one_smul]
  have h26 : ∫ ω, fO ω ∂Pr = ∫ ω, fOμ ω ∂Pr :=
    lemma_2_6 m hm A hacyc r hr hAss P hP L hLE β hβ.le σ hσ hσna hσm j
  have h27 : 1 / (m : ℝ) * ∫ ω, fOμ ω ∂Pr ≤ 1 / β * ∫ ω, fl ω ∂Pr :=
    lemma_2_7 m hm A hacyc r hr hAss P hP L hLE β hβ tb σ hσ hσm' j
  have hsplit : ∑ i ∈ before L j, (μ i + β * μ i) = (1 + β) * ∑ i ∈ before L j, μ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have : (1 + β) / m * ∑ i ∈ before L j, μ i = 1 / (m : ℝ) * ((1 + β) * ∑ i ∈ before L j, μ i) := by
    ring
  show ∫ ω, fC ω ∂Pr ≤ _
  rw [this]
  rw [hEg, hsplit, h26] at hE1
  have : 1 / (m : ℝ) * ((1 + β) * ∑ i ∈ before L j, μ i + ∫ ω, fOμ ω ∂Pr)
      = 1 / (m : ℝ) * ((1 + β) * ∑ i ∈ before L j, μ i) + 1 / (m : ℝ) * ∫ ω, fOμ ω ∂Pr := by ring
  rw [this] at hE1
  have : (((m : ℝ) - 1) / m + 1 / β) * ∫ ω, fl ω ∂Pr
      = ((m : ℝ) - 1) / m * ∫ ω, fl ω ∂Pr + 1 / β * ∫ ω, fl ω ∂Pr := by ring
  rw [this]
  linarith
