-- Prove2me | solution 1 for WassTwoStage.Copositive.theorem_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:59:09.701058+00:00
-- url     : https://prove2.me/submissions/6d62eb7b-c459-4940-9f28-814717a04217
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_ConicPrograms
import Theorems.Thm_WassTwoStage_Copositive_theorem_2
import Theorems.Thm_WassTwoStage_Copositive_theorem_3
import Theorems.Thm_WassTwoStage_Copositive_theorem_4
import Theorems.Thm_WassTwoStage_Copositive_proposition_2

open Filter Topology Matrix

namespace WassTwoStage.Copositive.T5Aux

open WassTwoStage.Copositive

variable {K J M N₁ N₂ I : ℕ}

lemma coe_add_iInf (a : ℝ) {ι : Sort*} (f : ι → EReal) :
    (a : EReal) + ⨅ i, f i = ⨅ i, ((a : EReal) + f i) := by
  apply le_antisymm
  · exact le_iInf fun i => add_le_add le_rfl (iInf_le f i)
  · have h1 : ((-a : ℝ) : EReal) + ⨅ i, ((a : EReal) + f i) ≤ ⨅ i, f i := by
      refine le_iInf fun i => ?_
      calc ((-a : ℝ) : EReal) + ⨅ i, ((a : EReal) + f i)
          ≤ ((-a : ℝ) : EReal) + ((a : EReal) + f i) := add_le_add le_rfl (iInf_le _ i)
        _ = f i := by rw [← add_assoc, ← EReal.coe_add]; simp
    calc ⨅ i, ((a : EReal) + f i)
        = (a : EReal) + (((-a : ℝ) : EReal) + ⨅ i, ((a : EReal) + f i)) := by
          rw [← add_assoc, ← EReal.coe_add]; simp
      _ ≤ _ := add_le_add le_rfl h1

lemma coe_add_iSup (a : ℝ) {ι : Sort*} (f : ι → EReal) :
    (a : EReal) + ⨆ i, f i = ⨆ i, ((a : EReal) + f i) := by
  apply le_antisymm
  · have h1 : ⨆ i, f i ≤ ((-a : ℝ) : EReal) + ⨆ i, ((a : EReal) + f i) := by
      refine iSup_le fun i => ?_
      calc f i = ((-a : ℝ) : EReal) + ((a : EReal) + f i) := by
            rw [← add_assoc, ← EReal.coe_add]; simp
        _ ≤ ((-a : ℝ) : EReal) + ⨆ i, ((a : EReal) + f i) :=
            add_le_add le_rfl (le_iSup (fun i => (a : EReal) + f i) i)
    calc (a : EReal) + ⨆ i, f i
        ≤ (a : EReal) + (((-a : ℝ) : EReal) + ⨆ i, ((a : EReal) + f i)) := add_le_add le_rfl h1
      _ = _ := by rw [← add_assoc, ← EReal.coe_add]; simp
  · exact iSup_le fun i => add_le_add le_rfl (le_iSup f i)

lemma val28_eq (d : Data K J M N₁ N₂ I) (c : Fin N₁ → ℝ) (X : Set (Fin N₁ → ℝ)) (δ : ℝ) :
    d.val28 c X δ = ⨅ (x : Fin N₁ → ℝ) (_ : x ∈ X), ((c ⬝ᵥ x : ℝ) : EReal) + d.upperValue δ x := by
  unfold Data.val28 Data.upperValue
  refine iInf_congr fun x => iInf_congr fun _ => ?_
  simp only [coe_add_iInf, EReal.coe_add]

lemma lowerValue_anti (d : Data K J M N₁ N₂ I) (x : Fin N₁ → ℝ) {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) :
    d.lowerValue δ₂ x ≤ d.lowerValue δ₁ x := by
  unfold Data.lowerValue
  refine iSup_mono fun γ => iSup_mono fun μ => iSup_mono fun Γ => iSup_mono fun Ω =>
    iSup_mono fun Y => iSup_mono fun hF => ?_
  rw [EReal.coe_le_coe_iff]
  unfold Data.cpObjective
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  have ht : 0 ≤ trace (Γ i) := (hF.1 i).2.2.1.trace_nonneg
  nlinarith [mul_le_mul_of_nonneg_right h ht]

lemma cpObjective_continuous (d : Data K J M N₁ N₂ I) (δ : ℝ)
    (γ : Fin I → Fin M ⊕ Fin J → ℝ) (Γ : Fin I → Matrix (Fin M ⊕ Fin J) (Fin M ⊕ Fin J) ℝ)
    (Y : Fin I → Matrix (Fin K) (Fin M ⊕ Fin J) ℝ) :
    Continuous fun x => d.cpObjective x δ γ Γ Y := by
  have hT : Continuous d.T := by
    rw [← AffineMap.continuous_linear_iff]; exact LinearMap.continuous_of_finiteDimensional _
  have hh : Continuous d.h := by
    rw [← AffineMap.continuous_linear_iff]; exact LinearMap.continuous_of_finiteDimensional _
  have hbT : Continuous fun x => d.bT x := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i
    · simp only [Data.bT, Matrix.fromRows_apply_inl]
      exact (continuous_apply j).comp ((continuous_apply i).comp hT)
    · simp only [Data.bT, Matrix.fromRows_apply_inr]
      exact continuous_const
  have hbh : Continuous fun x => d.bh x := by
    unfold Data.bh
    refine continuous_pi fun k => ?_
    rcases k with k | k
    · exact (continuous_apply k).comp hh
    · exact continuous_const
  unfold Data.cpObjective
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
  refine Continuous.sub (Continuous.add ?_ ?_) continuous_const
  · exact (hbT.matrix_mul continuous_const).matrix_trace
  · exact hbh.dotProduct continuous_const

lemma isClosed_sublevel (d : Data K J M N₁ N₂ I) (c : Fin N₁ → ℝ) (δ : ℝ) (B : EReal) :
    IsClosed {x : Fin N₁ → ℝ | ((c ⬝ᵥ x : ℝ) : EReal) + d.lowerValue δ x ≤ B} := by
  have : (fun x : Fin N₁ → ℝ => ((c ⬝ᵥ x : ℝ) : EReal) + d.lowerValue δ x) =
      fun x => ⨆ (γ : Fin I → Fin M ⊕ Fin J → ℝ) (μ : Fin I → Fin K → ℝ)
        (Γ : Fin I → Matrix (Fin M ⊕ Fin J) (Fin M ⊕ Fin J) ℝ)
        (Ω : Fin I → Matrix (Fin K) (Fin K) ℝ) (Y : Fin I → Matrix (Fin K) (Fin M ⊕ Fin J) ℝ)
        (_ : d.CPFeasible γ μ Γ Ω Y), ((c ⬝ᵥ x + d.cpObjective x δ γ Γ Y : ℝ) : EReal) := by
    funext x
    unfold Data.lowerValue
    simp only [coe_add_iSup, EReal.coe_add]
  have hl : LowerSemicontinuous
      (fun x : Fin N₁ → ℝ => ((c ⬝ᵥ x : ℝ) : EReal) + d.lowerValue δ x) := by
    rw [this]
    refine lowerSemicontinuous_iSup fun γ => lowerSemicontinuous_iSup fun μ =>
      lowerSemicontinuous_iSup fun Γ => lowerSemicontinuous_iSup fun Ω =>
      lowerSemicontinuous_iSup fun Y => lowerSemicontinuous_iSup fun _ => ?_
    refine Continuous.lowerSemicontinuous ?_
    refine continuous_coe_real_ereal.comp ?_
    exact (continuous_const.dotProduct continuous_id).add (cpObjective_continuous d δ γ Γ Y)
  exact hl.isClosed_preimage B

lemma mem_of_cluster {α : Type*} [TopologicalSpace α] {C : Set α} (hC : IsClosed C)
    {xs : ℕ → α} {xstar : α} (hcl : MapClusterPt xstar atTop xs)
    (hev : ∀ᶠ n in atTop, xs n ∈ C) : xstar ∈ C := by
  by_contra hx
  have hfr := (mapClusterPt_iff_frequently.1 hcl) Cᶜ (hC.isOpen_compl.mem_nhds hx)
  obtain ⟨n, h1, h2⟩ := (hfr.and_eventually hev).exists
  exact h1 h2

section main

variable (d : Data K J M N₁ N₂ I) (hI : 0 < I) (hXi : d.Xi.Nonempty)
  (hSER : d.SufficientlyExpensiveRecourse) (hξ : ∀ i, d.ξhat i ∈ d.Xi) (hε : 0 ≤ d.ε)
include hI hXi hSER hξ hε

/-- Passing to the limit `δ ↓ 0` in a sublevel bound, via Proposition 2. -/
lemma limit_bound (c : Fin N₁ → ℝ) (x : Fin N₁ → ℝ) (B : EReal)
    (h : ∀ δ : ℝ, 0 < δ → ((c ⬝ᵥ x : ℝ) : EReal) + d.lowerValue δ x ≤ B) :
    ((c ⬝ᵥ x : ℝ) : EReal) + d.worstCase x ≤ B := by
  have hP := proposition_2 d hI hXi hSER hξ hε x
  have hcont : ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
      (((c ⬝ᵥ x : ℝ) : EReal), d.worstCase x) :=
    EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))
  have ht : Tendsto (fun δ => ((c ⬝ᵥ x : ℝ) : EReal) + d.upperValue δ x) (𝓝[>] 0)
      (𝓝 (((c ⬝ᵥ x : ℝ) : EReal) + d.worstCase x)) :=
    hcont.tendsto.comp (tendsto_const_nhds.prodMk_nhds hP.2)
  refine le_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [(hP.1 δ hδ).1]
  exact h δ hδ

/-- Key epi-convergence step: a cluster point of points with bounded `(28)`-objective along
`δ_n ↓ 0` has `(1)`-objective bounded by the same constant. -/
lemma cluster_bound (c : Fin N₁ → ℝ) (δs : ℕ → ℝ) (xs : ℕ → Fin N₁ → ℝ) (xstar : Fin N₁ → ℝ)
    (hδ : Tendsto δs atTop (𝓝[>] 0)) (hcl : MapClusterPt xstar atTop xs) (B : EReal)
    (hB : ∀ᶠ n in atTop, ((c ⬝ᵥ xs n : ℝ) : EReal) + d.upperValue (δs n) (xs n) ≤ B) :
    ((c ⬝ᵥ xstar : ℝ) : EReal) + d.worstCase xstar ≤ B := by
  refine limit_bound d hI hXi hSER hξ hε c xstar B fun δ' hδ' => ?_
  refine mem_of_cluster (C := {x | ((c ⬝ᵥ x : ℝ) : EReal) + d.lowerValue δ' x ≤ B})
    (isClosed_sublevel d c δ' B) hcl ?_
  have hmem : ∀ᶠ n in atTop, δs n ∈ Set.Ioo (0 : ℝ) δ' := hδ (Ioo_mem_nhdsGT hδ')
  filter_upwards [hB, hmem] with n hn hn'
  show ((c ⬝ᵥ xs n : ℝ) : EReal) + d.lowerValue δ' (xs n) ≤ B
  have hP := proposition_2 d hI hXi hSER hξ hε (xs n)
  rw [(hP.1 (δs n) hn'.1).1] at hn
  exact le_trans (add_le_add le_rfl (lowerValue_anti d (xs n) hn'.2.le)) hn

end main

end WassTwoStage.Copositive.T5Aux

open WassTwoStage.Copositive WassTwoStage.Copositive.T5Aux

theorem solution {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) (c : Fin N₁ → ℝ)
    (X : Set (Fin N₁ → ℝ)) (hI : 0 < I) (hXi : d.Xi.Nonempty)
    (hSER : d.SufficientlyExpensiveRecourse) (hξ : ∀ i, d.ξhat i ∈ d.Xi) (hε : 0 ≤ d.ε) :
    (d.CompleteRecourse →
      d.val28 c X 0 = d.val1 c X ∧
      ∀ x, d.IsMinimizer28 c X 0 x ↔ d.IsMinimizer1 c X x) ∧
    d.val1 c X ≤ d.val28 c X 0 ∧
    (∀ δ : ℝ, 0 < δ → d.val28 c X δ ≤ d.val1 c X) ∧
    (IsCompact X →
      Tendsto (fun δ => d.val28 c X δ) (𝓝[>] 0) (𝓝 (d.val1 c X)) ∧
      ∀ (δs : ℕ → ℝ) (xs : ℕ → Fin N₁ → ℝ),
        Tendsto δs atTop (𝓝[>] 0) →
        (∀ n, d.IsMinimizer28 c X (δs n) (xs n)) →
        ∀ xstar : Fin N₁ → ℝ, MapClusterPt xstar atTop xs → d.IsMinimizer1 c X xstar) := by
  -- `𝒵̄_δ(x) ≤ 𝒵(x)` for `δ > 0` (Proposition 2, relaxation, Theorem 3)
  have hup_le : ∀ δ : ℝ, 0 < δ → ∀ x, d.upperValue δ x ≤ d.worstCase x := by
    intro δ hδ x
    rw [((proposition_2 d hI hXi hSER hξ hε x).1 δ hδ).1, theorem_3 d hI hXi hSER hξ hε x]
    exact lowerValue_anti d x hδ.le
  have hiii : ∀ δ : ℝ, 0 < δ → d.val28 c X δ ≤ d.val1 c X := by
    intro δ hδ
    rw [val28_eq]
    unfold Data.val1
    exact iInf_mono fun x => iInf_mono fun _ => add_le_add le_rfl (hup_le δ hδ x)
  refine ⟨?_, ?_, hiii, ?_⟩
  · -- (i): Theorem 4
    intro hCR
    have h4 : ∀ x, d.upperValue 0 x = d.worstCase x := fun x => by
      obtain ⟨a, b⟩ := theorem_4 d hI hXi hSER hξ hε hCR x
      rw [← b, ← a]
    refine ⟨?_, fun x => ?_⟩
    · rw [val28_eq]; unfold Data.val1; simp only [h4]
    · unfold Data.IsMinimizer28 Data.IsMinimizer1; simp only [h4]
  · -- (ii): Theorem 2
    rw [val28_eq]
    unfold Data.val1
    exact iInf_mono fun x => iInf_mono fun _ =>
      add_le_add le_rfl (theorem_2 d hI hXi hSER hξ hε x)
  · intro hX
    refine ⟨?_, ?_⟩
    · -- convergence of optimal values
      refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
      · by_contra hne
        have hfr : ∃ᶠ δ in 𝓝[>] (0 : ℝ), d.val28 c X δ ≤ a := by
          rw [not_eventually] at hne
          exact hne.mono fun δ h => not_lt.1 h
        obtain ⟨a', ha1, ha2⟩ := exists_between ha
        have hseq : ∀ n : ℕ, ∃ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)) ∧
            d.val28 c X δ ≤ a := by
          intro n
          have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          obtain ⟨δ, h1, h2⟩ := (hfr.and_eventually (Ioo_mem_nhdsGT hpos)).exists
          exact ⟨δ, h2, h1⟩
        choose δs hδs hval using hseq
        have hδt : Tendsto δs atTop (𝓝[>] 0) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (hδs n).1⟩
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
            tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hδs n).1.le)
            (fun n => (hδs n).2.le)
        have hx : ∀ n, ∃ x ∈ X, ((c ⬝ᵥ x : ℝ) : EReal) + d.upperValue (δs n) x < a' := by
          intro n
          have h := lt_of_le_of_lt (hval n) ha1
          rw [val28_eq] at h
          obtain ⟨x, hx⟩ := iInf_lt_iff.1 h
          obtain ⟨hxX, hx'⟩ := iInf_lt_iff.1 hx
          exact ⟨x, hxX, hx'⟩
        choose xs hxsX hxs using hx
        obtain ⟨xstar, hxstarX, hcl⟩ := hX.exists_mapClusterPt (f := atTop) (u := xs)
          (by rw [le_principal_iff, mem_map]; exact univ_mem' hxsX)
        have hb := cluster_bound d hI hXi hSER hξ hε c δs xs xstar hδt hcl a'
          (Eventually.of_forall fun n => (hxs n).le)
        have : d.val1 c X ≤ a' := by
          unfold Data.val1
          exact le_trans (iInf_le_of_le xstar (iInf_le _ hxstarX)) hb
        exact absurd (lt_of_le_of_lt this ha2) (lt_irrefl _)
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact lt_of_le_of_lt (hiii δ hδ) ha
    · -- cluster points of minimizers are minimizers
      intro δs xs hδ hmin xstar hcl
      have hxstarX : xstar ∈ X :=
        mem_of_cluster hX.isClosed hcl (Eventually.of_forall fun n => (hmin n).1)
      refine ⟨hxstarX, fun x' hx' => ?_⟩
      refine cluster_bound d hI hXi hSER hξ hε c δs xs xstar hδ hcl _ ?_
      have hpos : ∀ᶠ n in atTop, 0 < δs n := (tendsto_nhdsWithin_iff.1 hδ).2
      filter_upwards [hpos] with n hn
      exact le_trans ((hmin n).2 x' hx') (add_le_add le_rfl (hup_le _ hn x'))
