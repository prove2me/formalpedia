-- Prove2me | solution 1 for StochSchedPrec.InForest.theorem_4_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:51:48.585204+00:00
-- url     : https://prove2.me/submissions/90b37dab-5617-4c52-b95a-90c255c7766c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model
import Definitions.Def_StochSchedPrec_InForest_LP
import Definitions.Def_StochSchedPrec_InForest_Graham
import Theorems.Thm_StochSchedPrec_InForest_lemma_4_4
import Theorems.Thm_StochSchedPrec_InForest_chain_lower_bound
import Theorems.Thm_StochSchedPrec_InForest_lemma_3_3
import Theorems.Thm_StochSchedPrec_InForest_lp_relaxation
open MeasureTheory ProbabilityTheory

namespace StochSchedPrec.InForest.T45Aux

open Classical

variable {V : Type*} [Fintype V]

/-- The set of candidate critical predecessors of `j`. -/
noncomputable def candSet (A : V → V → Prop) (p S : V → ℝ) (j : V) : Finset V :=
  Finset.univ.filter fun i => Relation.TransGen A i j ∧ 0 < S i + p i ∧
    ∀ i', Relation.TransGen A i' j → S i' + p i' ≤ S i + p i

/-- Choose an element of a finset, if any. -/
noncomputable def pick (s : Finset V) : Option V :=
  if h : s.Nonempty then some h.choose else none

noncomputable def critSel (A : V → V → Prop) (p S : V → ℝ) (j : V) : Option V :=
  pick (candSet A p S j)

lemma critSel_spec (A : V → V → Prop) (p S : V → ℝ) :
    IsCritSelector A p S (critSel A p S) := by
  intro j
  constructor
  · intro i hi
    unfold critSel pick at hi
    split_ifs at hi with h
    · cases hi
      have := h.choose_spec
      simpa [candSet] using this
  · intro hn ⟨i, hi⟩
    unfold critSel pick at hn
    split_ifs at hn with h
    exact h ⟨i, by simpa [candSet] using hi⟩

lemma measurable_candSet_eq (A : V → V → Prop) (j : V) (s : Finset V) :
    MeasurableSet {x : (V → ℝ) × (V → ℝ) | candSet A x.1 x.2 j = s} := by
  have hpr : ∀ k : V, Measurable fun x : (V → ℝ) × (V → ℝ) =>
      Relation.TransGen A k j ∧ 0 < x.2 k + x.1 k ∧
        ∀ i', Relation.TransGen A i' j → x.2 i' + x.1 i' ≤ x.2 k + x.1 k := by
    intro k
    have hc : ∀ i : V, Measurable fun x : (V → ℝ) × (V → ℝ) => x.2 i + x.1 i := fun i =>
      ((measurable_pi_apply i).comp measurable_snd).add ((measurable_pi_apply i).comp measurable_fst)
    refine measurable_const.and (Measurable.and ?_ ?_)
    · exact measurableSet_setOf.mp (measurableSet_lt measurable_const (hc k))
    · refine Measurable.forall fun i' => measurable_const.imp ?_
      exact measurableSet_setOf.mp (measurableSet_le (hc i') (hc k))
  have : {x : (V → ℝ) × (V → ℝ) | candSet A x.1 x.2 j = s} =
      {x | ∀ k, (Relation.TransGen A k j ∧ 0 < x.2 k + x.1 k ∧
        ∀ i', Relation.TransGen A i' j → x.2 i' + x.1 i' ≤ x.2 k + x.1 k) ↔ k ∈ s} := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.ext_iff, candSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
  rw [this]
  exact measurableSet_setOf.mpr (Measurable.forall fun k => (hpr k).iff measurable_const)

lemma measurable_critSel_eq (A : V → V → Prop) (j : V) (o : Option V) :
    MeasurableSet {x : (V → ℝ) × (V → ℝ) | critSel A x.1 x.2 j = o} := by
  have : {x : (V → ℝ) × (V → ℝ) | critSel A x.1 x.2 j = o} =
      ⋃ s ∈ (Finset.univ.filter fun s : Finset V => pick s = o),
        {x : (V → ℝ) × (V → ℝ) | candSet A x.1 x.2 j = s} := by
    ext x
    simp [critSel]
  rw [this]
  exact Finset.measurableSet_biUnion _ fun s _ => measurable_candSet_eq A j s

lemma chainLenAux_eq (crit : V → Option V) (p : V → ℝ) (n : ℕ) (j : V) :
    chainLenAux crit p (n + 1) j =
      p j + ∑ i, (if crit j = some i then chainLenAux crit p n i else 0) := by
  cases h : crit j with
  | none => simp [chainLenAux, h]
  | some i => simp [chainLenAux, h]

lemma measurable_chainLenAux (A : V → V → Prop) (n : ℕ) :
    ∀ j, Measurable fun x : (V → ℝ) × (V → ℝ) =>
      chainLenAux (critSel A x.1 x.2) x.1 n j := by
  induction n with
  | zero =>
    intro j
    show Measurable fun x : (V → ℝ) × (V → ℝ) => x.1 j
    exact (measurable_pi_apply j).comp measurable_fst
  | succ n ih =>
    intro j
    simp only [chainLenAux_eq]
    refine ((measurable_pi_apply j).comp measurable_fst).add ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact Measurable.ite (measurable_critSel_eq A j (some i)) (ih i) measurable_const

/-- `∫ ∑ w_j f_j ≤ ∑ w_j ∫ f_j` for nonnegative weights and nonnegative a.e.-measurable `f_j`. -/
lemma integral_wsum_le {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    (w : V → ℝ) (hw : ∀ j, 0 ≤ w j) (g : V → Ω → ℝ) (hg : ∀ j, AEMeasurable (g j) Pr)
    (hg0 : ∀ j ω, 0 ≤ g j ω) :
    ∫ ω, (∑ j, w j * g j ω) ∂Pr ≤ ∑ j, w j * ∫ ω, g j ω ∂Pr := by
  by_cases h : ∀ j, Integrable (fun ω => w j * g j ω) Pr
  · rw [integral_finset_sum _ (fun j _ => h j)]
    exact le_of_eq (Finset.sum_congr rfl fun j _ => integral_const_mul _ _)
  · push_neg at h
    obtain ⟨j, hj⟩ := h
    have hni : ¬ Integrable (fun ω => ∑ j, w j * g j ω) Pr := by
      intro hint
      apply hj
      refine hint.mono' (((hg j).const_mul (w j)).aestronglyMeasurable) ?_
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw j) (hg0 j ω))]
      exact Finset.single_le_sum (f := fun k => w k * g k ω)
        (fun k _ => mul_nonneg (hw k) (hg0 k ω)) (Finset.mem_univ j)
    rw [integral_undef hni]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (hw k) (integral_nonneg fun ω => hg0 k ω)

end StochSchedPrec.InForest.T45Aux

open StochSchedPrec.InForest StochSchedPrec.InForest.T45Aux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A) (hforest : IsInForest A)
    (w : V → ℝ) (hw : ∀ j, 0 ≤ w j)
    (P : V → Ω → ℝ) (hP : IsStochProcTimes P Pr) (Δ : ℝ) (hCV : CVBound P Pr Δ)
    (C : V → ℝ) (hC : IsLPOptimal (fun j => ∫ ω, P j ω ∂Pr) A m Δ w C)
    (L : Fin (Fintype.card V) ≃ V) (hL : StochSchedPrec.CMNS.IsSortedBy L C)
    (γ : (V → ℝ) → (V → ℝ)) (hγ : ∀ p, IsNonneg p → IsGraham A m L p (γ p))
    (hγmeas : ∀ j, AEMeasurable (fun ω => γ (fun k => P k ω) j) Pr) :
    ∀ pol : (V → ℝ) → (V → ℝ), IsComparator A m P Pr pol →
      ∫ ω, (∑ j, w j * (γ (fun k => P k ω) j + P j ω)) ∂Pr ≤
        (2 - 1 / (m : ℝ) + max 1 (((m : ℝ) - 1) / m * Δ)) *
          ∫ ω, (∑ j, w j * (pol (fun k => P k ω) j + P j ω)) ∂Pr := by
  intro pol hpol
  set μ : V → ℝ := fun j => ∫ ω, P j ω ∂Pr with hμ
  have hμpos : ∀ j, 0 < μ j := hCV.2.2.1
  -- integrability of processing times
  have hPint : ∀ j, Integrable (P j) Pr := fun j =>
    (hCV.2.1 j).integrable (by norm_num)
  -- the LP-sorted list is a linear extension
  have hlt : ∀ i j, Relation.TransGen A i j → C i < C j := by
    intro i j h
    induction h with
    | single hab => exact lt_of_lt_of_le (lt_add_of_pos_right _ (hμpos _)) (hC.1.2.1 _ _ hab)
    | tail _ hbc ih =>
      exact lt_trans ih (lt_of_lt_of_le (lt_add_of_pos_right _ (hμpos _)) (hC.1.2.1 _ _ hbc))
  have hLin : StochSchedPrec.CMNS.IsLinearExtension A L := by
    intro i j h
    by_contra hcon
    have := hL _ _ (not_lt.mp hcon)
    simp only [Equiv.apply_symm_apply] at this
    exact absurd (hlt i j h) (not_lt.mpr this)
  -- critical-predecessor selector and measurability of chain lengths
  let crit : (V → ℝ) → V → Option V := fun p => critSel A p (γ p)
  have hcrit : ∀ p, IsNonneg p → IsCritSelector A p (γ p) (crit p) :=
    fun p _ => critSel_spec A p (γ p)
  have hpair : AEMeasurable (fun ω => ((fun k => P k ω), γ (fun k => P k ω))) Pr :=
    (measurable_pi_lambda _ fun k => hP.1 k).aemeasurable.prodMk
      (aemeasurable_pi_iff.mpr hγmeas)
  have hℓmeas : ∀ j, AEMeasurable
      (fun ω => chainLen (crit (fun k => P k ω)) (fun k => P k ω) j) Pr := by
    intro j
    have hG := measurable_chainLenAux A (Fintype.card V) j
    have h2 := hG.comp_aemeasurable hpair
    exact h2
  -- the four ingredients
  have h44 := fun j => lemma_4_4 m hm A hacyc hforest P hP hPint L hLin γ hγ hγmeas crit hcrit
    hℓmeas j
  have hclb := (chain_lower_bound m hm A hacyc P hP hPint γ (fun p hp => (hγ p hp).1) crit
    hcrit hℓmeas).2 pol hpol
  have h33 := fun j => lemma_3_3 m hm Δ hCV.1 μ hμpos C hC.1.1 hC.1.2.2 L hL j
  have hlp := lp_relaxation m hm A hacyc w hw P hP Δ hCV pol hpol
  have hopt := hC.2 _ hlp.1
  rw [← hlp.2]
  -- notation
  set E : V → ℝ := fun j => ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr with hE
  set M : ℝ := max 1 (((m : ℝ) - 1) / m * Δ) with hM
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hcoef : 0 ≤ ((m : ℝ) - 1) / m := div_nonneg (by linarith) hmpos.le
  have hM0 : 0 ≤ 1 + M := by have := le_max_left 1 (((m : ℝ) - 1) / m * Δ); linarith
  -- Graham completion times are nonnegative
  have hg0 : ∀ j ω, 0 ≤ γ (fun k => P k ω) j + P j ω := fun j ω =>
    add_nonneg ((hγ _ (fun k => hP.2.1 k ω)).1.1 j) (hP.2.1 j ω)
  have hgm : ∀ j, AEMeasurable (fun ω => γ (fun k => P k ω) j + P j ω) Pr := fun j =>
    (hγmeas j).add (hP.1 j).aemeasurable
  have step1 := integral_wsum_le w hw (fun j ω => γ (fun k => P k ω) j + P j ω) hgm hg0
  have hj : ∀ j, ∫ ω, (γ (fun k => P k ω) j + P j ω) ∂Pr ≤
      ((m : ℝ) - 1) / m * E j + (1 + M) * C j := by
    intro j
    have a := h44 j
    have b := mul_le_mul_of_nonneg_left (hclb j) hcoef
    have c := h33 j
    linarith
  calc ∫ ω, (∑ j, w j * (γ (fun k => P k ω) j + P j ω)) ∂Pr
      ≤ ∑ j, w j * ∫ ω, (γ (fun k => P k ω) j + P j ω) ∂Pr := step1
    _ ≤ ∑ j, w j * (((m : ℝ) - 1) / m * E j + (1 + M) * C j) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hj j) (hw j)
    _ = ((m : ℝ) - 1) / m * ∑ j, w j * E j + (1 + M) * ∑ j, w j * C j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ((m : ℝ) - 1) / m * ∑ j, w j * E j + (1 + M) * ∑ j, w j * E j := by
        have := mul_le_mul_of_nonneg_left hopt hM0
        linarith
    _ = (2 - 1 / (m : ℝ) + M) * ∑ j, w j * E j := by
        field_simp
        ring
