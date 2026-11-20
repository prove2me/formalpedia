-- Prove2me | solution 1 for ProbabilityTheory.measureReal_exists_abs_lt_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:10:55.344849+00:00
-- url     : https://prove2.me/submissions/e16550b1-b3d6-416e-bfc2-e5edfad47639

import Definitions.Def_BrownianMotion_Auxiliary_Filtration_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_Basic_F000
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F001

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran, Rémy Degenne
-/

/-! # Maximal inequality for real quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section Bridge

variable {F : Finset ι} {t : ι} {k l : ℕ}

end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

end UpcrossingBound

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

variable [TopologicalSpace ι] [OrderTopology ι]

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

end Selection

/-! ### Maximal inequality along finite time sets -/

section Maximal

variable {t : ι} {F : Finset ι} {lam : ℝ}

-- todo name
theorem AuxMX.mx [IsFiniteMeasure μ]
    {g : ι → Ω → ℝ} (hg : StronglyAdapted 𝓕 g) (hgint : ∀ s, Integrable (g s) μ)
    {n : ℕ} {idx : ℕ → ι} (hidx : Monotone idx) {K : ℝ}
    (hK : ∀ W : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) →
      ∫ ω, (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ ≤ K) :
    lam * μ.real {ω | ∃ k ≤ n, lam < g (idx k) ω}
      ≤ K + ∫ ω, |g (idx 0) ω| ∂μ + ∫ ω, |g (idx n) ω| ∂μ := by
  classical
  have hgm : ∀ s, Measurable (g s) := fun s => ((hg s).measurable).mono (𝓕.le s) le_rfl
  set A := {ω | ∃ k ≤ n, lam < g (idx k) ω} with hA
  let σ : Ω → ℕ := fun ω => if h : ∃ k ≤ n, lam < g (idx k) ω then Nat.find h else n
  have hσle : ∀ ω, σ ω ≤ n := by
    intro ω
    simp only [σ]
    split_ifs with h
    · exact (Nat.find_spec h).1
    · exact le_rfl
  have hWσ : ∀ k ω, k < n → (k < σ ω ↔ ∀ j ≤ k, g (idx j) ω ≤ lam) := by
    intro k ω hk
    simp only [σ]
    split_ifs with h
    · rw [Nat.lt_find_iff]
      constructor
      · intro H j hj
        have := H j hj
        push_neg at this
        exact this (hj.trans hk.le)
      · intro H j hj hcon
        linarith [H j hj, hcon.2]
    · push_neg at h
      simp only [hk, true_iff]
      intro j hj
      exact h j (hj.trans hk.le)
  set W : ℕ → Ω → ℝ := fun k ω => if k < σ ω then 1 else 0 with hW
  have hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1 := by
    intro k _ ω
    simp only [W]
    split_ifs <;> simp
  have hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k) := by
    intro k hk
    have hset : MeasurableSet[𝓕 (idx k)] {ω | k < σ ω} := by
      have : {ω | k < σ ω} = ⋂ j ∈ Finset.range (k + 1), {ω | g (idx j) ω ≤ lam} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, hWσ k ω hk]
        constructor
        · intro H j hj; exact H j (Nat.lt_succ_iff.1 hj)
        · intro H j hj; exact H j (Nat.lt_succ_iff.2 hj)
      rw [this]
      refine Finset.measurableSet_biInter _ fun j hj => ?_
      have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      exact 𝓕.mono (hidx hj') _ ((hg (idx j)).measurable measurableSet_Iic)
    exact Measurable.ite hset measurable_const measurable_const
  have hWm' : ∀ k, k < n → Measurable (W k) := fun k hk => (hWmeas k hk).mono (𝓕.le _) le_rfl
  have hKW := hK W hW01 hWmeas
  set gs : Ω → ℝ := fun ω => g (idx (σ ω)) ω with hgs_def
  have htel : ∀ ω, ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)
      = gs ω - g (idx 0) ω := by
    intro ω
    have : ∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)
        = ∑ k ∈ range (σ ω), (g (idx (k + 1)) ω - g (idx k) ω) := by
      rw [← Finset.sum_range_add_sum_Ico _ (hσle ω)]
      have h1 : ∑ k ∈ range (σ ω), W k ω * (g (idx (k + 1)) ω - g (idx k) ω)
          = ∑ k ∈ range (σ ω), (g (idx (k + 1)) ω - g (idx k) ω) :=
        Finset.sum_congr rfl fun k hk => by simp [W, Finset.mem_range.1 hk]
      have h2 : ∑ k ∈ Ico (σ ω) n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω) = 0 :=
        Finset.sum_eq_zero fun k hk => by simp [W, not_lt.2 (Finset.mem_Ico.1 hk).1]
      rw [h1, h2, add_zero]
    rw [this, Finset.sum_range_sub (fun k => g (idx k) ω)]
  have hint_sum : Integrable (fun ω => ∑ k ∈ range n,
      W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) μ :=
    integrable_finset_sum _ fun k hk => ((hgint _).sub (hgint _)).bdd_mul (c := 1)
      (hWm' k (Finset.mem_range.1 hk)).aestronglyMeasurable
      (ae_of_all _ fun ω => by simp only [W]; split_ifs <;> simp)
  have hgs : Integrable gs μ := by
    have : gs = fun ω => (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω))
        + g (idx 0) ω := funext fun ω => by rw [htel]; ring
    rw [this]; exact hint_sum.add (hgint _)
  have hAm : MeasurableSet A := by
    have : A = ⋃ k ∈ Finset.range (n + 1), {ω | lam < g (idx k) ω} := by
      ext ω
      simp only [hA, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop,
        Nat.lt_succ_iff]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun k _ => measurableSet_lt measurable_const (hgm _)
  have hpt : ∀ ω, lam * A.indicator 1 ω ≤ gs ω + |g (idx n) ω| := by
    intro ω
    by_cases h : ∃ k ≤ n, lam < g (idx k) ω
    · have hmem : ω ∈ A := h
      rw [Set.indicator_of_mem hmem]
      have hσ : σ ω = Nat.find h := by simp only [σ, dif_pos h]
      have := (Nat.find_spec h).2
      simp only [gs, hσ, Pi.one_apply, mul_one]
      linarith [abs_nonneg (g (idx n) ω)]
    · have hmem : ω ∉ A := h
      rw [Set.indicator_of_notMem hmem]
      have hσ : σ ω = n := by simp only [σ, dif_neg h]
      simp only [gs, hσ, mul_zero]
      linarith [neg_abs_le (g (idx n) ω)]
  have hE : ∫ ω, gs ω ∂μ ≤ K + ∫ ω, |g (idx 0) ω| ∂μ := by
    have : ∫ ω, gs ω ∂μ = ∫ ω, (∑ k ∈ range n, W k ω * (g (idx (k + 1)) ω - g (idx k) ω)) ∂μ
        + ∫ ω, g (idx 0) ω ∂μ := by
      rw [← integral_add hint_sum (hgint _)]
      congr 1; funext ω; rw [htel]; ring
    rw [this]
    have := integral_mono (hgint (idx 0)) (hgint (idx 0)).abs fun ω => le_abs_self (g (idx 0) ω)
    linarith
  calc lam * μ.real A = ∫ ω, lam * A.indicator 1 ω ∂μ := by
        rw [integral_const_mul, integral_indicator_one hAm]
    _ ≤ ∫ ω, (gs ω + |g (idx n) ω|) ∂μ :=
        integral_mono (((integrable_const (1 : ℝ)).indicator hAm).const_mul lam)
          (hgs.add (hgint _).abs) hpt
    _ = ∫ ω, gs ω ∂μ + ∫ ω, |g (idx n) ω| ∂μ := integral_add hgs (hgint _).abs
    _ ≤ K + ∫ ω, |g (idx 0) ω| ∂μ + ∫ ω, |g (idx n) ω| ∂μ := by linarith


theorem AuxE.eps [OrderBot ι] {t : ι} (n : ℕ) {idx : ℕ → ι}
    (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t) {W : ℕ → Ω → ℝ}
    (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) (ω : Ω) :
    ((elemPredSetOfSeq hidx n hWmeas).indicator (1 : ℝ) ● X) t ω =
      ∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω) := by
  classical
  have hst : ∀ s, s ≤ t → stoppedProcess X (fun _ ↦ (t : WithTop ι)) s ω = X s ω := fun s hs =>
    stoppedProcess_eq_of_le (WithTop.coe_le_coe.2 hs)
  set K : Finset ℕ := {k ∈ range n | idx k < idx (k + 1)} with hK
  have hinj : ∀ x ∈ K, ∀ y ∈ K, (idx x, idx (x + 1)) = (idx y, idx (y + 1)) → x = y := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.1 hx).2
    have hy' := (Finset.mem_filter.1 hy).2
    have h1 : idx x = idx y := (Prod.ext_iff.1 hxy).1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hidx (Nat.succ_le_of_lt h)
      rw [← h1] at this
      exact absurd hx' (not_lt.2 this)
    · have := hidx (Nat.succ_le_of_lt h)
      rw [h1] at this
      exact absurd hy' (not_lt.2 this)
  rw [ElementaryPredictableSet.integral_indicator_apply]
  simp only [elemPredSetOfSeq]
  rw [Finset.sum_image hinj]
  have hne : ∀ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω) ≠ 0 →
      idx k < idx (k + 1) := by
    intro k _ hne
    by_contra hlt
    have heq : idx k = idx (k + 1) := le_antisymm (hidx (Nat.le_succ k)) (not_lt.1 hlt)
    apply hne
    rw [heq, sub_self, mul_zero]
  rw [← Finset.sum_filter_of_ne hne]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hex : ∃ k' ∈ K, (idx k', idx (k' + 1)) = (idx k, idx (k + 1)) := ⟨k, hk, rfl⟩
  rw [dif_pos hex]
  have hch : hex.choose = k := hinj _ hex.choose_spec.1 _ hk hex.choose_spec.2
  rw [hch]
  have hkn : k < n := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
  rcases hW01 k hkn ω with h | h
  · simp [Set.indicator, h]
  · simp [Set.indicator, h, hst _ (hidxt _)]


theorem AuxSW.swi [OrderBot ι]
    (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    {n : ℕ} {idx : ℕ → ι} (hidx : Monotone idx) (hidxt : ∀ k, idx k ≤ t)
    {W : ℕ → Ω → ℝ} (hW01 : ∀ k, k < n → ∀ ω, W k ω = 0 ∨ W k ω = 1)
    (hWmeas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W k)) :
    ∫ ω, (∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ
        ∈ Set.Icc (-(C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)) C := by
  have key : ∀ V : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (V k)) →
      ∫ ω, (∑ k ∈ range n, V k ω * (X (idx (k + 1)) ω - X (idx k) ω)) ∂μ ≤ C := by
    intro V hV01 hVmeas
    have h := hC (elemPredSetOfSeq hidx n hVmeas)
    have heq : (fun ω => ((elemPredSetOfSeq hidx n hVmeas).indicator (1 : ℝ) ● X) t ω)
        = fun ω => ∑ k ∈ range n, V k ω * (X (idx (k + 1)) ω - X (idx k) ω) :=
      funext fun ω => AuxE.eps n hidx hidxt hV01 hVmeas ω
    rw [heq] at h
    exact h
  have hint : ∀ V : ℕ → Ω → ℝ, (∀ k, k < n → ∀ ω, V k ω = 0 ∨ V k ω = 1) →
      (∀ k, k < n → Measurable[𝓕 (idx k)] (V k)) →
      Integrable (fun ω => ∑ k ∈ range n, V k ω * (X (idx (k + 1)) ω - X (idx k) ω)) μ := by
    intro V hV01 hVmeas
    refine integrable_sum_weight_increments hXint
      (fun k hk => ((hVmeas k hk).mono (𝓕.le _) le_rfl).aestronglyMeasurable) ?_
    intro k hk ω
    rcases hV01 k hk ω with h | h <;> simp [h]
  refine ⟨?_, key W hW01 hWmeas⟩
  set W' : ℕ → Ω → ℝ := fun k ω => 1 - W k ω with hW'
  have hW'01 : ∀ k, k < n → ∀ ω, W' k ω = 0 ∨ W' k ω = 1 := by
    intro k hk ω
    rcases hW01 k hk ω with h | h <;> simp [W', h]
  have hW'meas : ∀ k, k < n → Measurable[𝓕 (idx k)] (W' k) := fun k hk =>
    measurable_const.sub (hWmeas k hk)
  have h1 := key W' hW'01 hW'meas
  have hsum : ∀ ω, ∑ k ∈ range n, W' k ω * (X (idx (k + 1)) ω - X (idx k) ω)
      = (X (idx n) ω - X (idx 0) ω)
        - ∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω) := by
    intro ω
    simp only [W', sub_mul, one_mul, Finset.sum_sub_distrib]
    have := Finset.sum_range_sub (fun k => X (idx k) ω) n
    simp only [Finset.sum_sub_distrib] at this
    linarith
  simp_rw [hsum] at h1
  rw [integral_sub (f := fun ω => X (idx n) ω - X (idx 0) ω) ((hXint _).sub (hXint _)) (hint W hW01 hWmeas)] at h1
  have h2' : -∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ ≤ ∫ ω, (X (idx n) ω - X (idx 0) ω) ∂μ := by
    rw [← integral_neg]
    exact integral_mono ((hXint _).sub (hXint _)).abs.neg ((hXint _).sub (hXint _))
      fun ω => neg_abs_le (X (idx n) ω - X (idx 0) ω)
  linarith


theorem _root_.solution [OrderBot ι] [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hlam : 0 < lam) (hF : ∀ s ∈ F, s ≤ t) :
    μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ 2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ + ∫ ω, |X t ω| ∂μ) / lam := by
  classical
  set G := insert ⊥ F with hG
  have hGt : ∀ s ∈ G, s ≤ t := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact bot_le
    · exact hF s hs
  set n := #G
  set idx := finIdx G t
  have hidx : Monotone idx := finIdx_monotone hGt
  have hidxt : ∀ k, idx k ≤ t := finIdx_le hGt
  have h0 : idx 0 = ⊥ := finIdx_zero_eq_bot (Finset.mem_insert_self _ _)
  have hn : idx n = t := finIdx_eq_of_card_le le_rfl
  -- positive part
  have h1 := AuxMX.mx (lam := lam) (μ := μ) hX hXint hidx (n := n) (K := C)
    (fun W hW01 hWmeas => (AuxSW.swi hXint hC hidx hidxt hW01 hWmeas).2)
  -- negative part
  have hXn : StronglyAdapted 𝓕 (fun s ω => -X s ω) := fun s => (hX s).neg
  have h2 := AuxMX.mx (lam := lam) (μ := μ) (g := fun s ω => -X s ω) hXn
    (fun s => (hXint s).neg) hidx (n := n) (K := C + ∫ ω, |X (idx n) ω - X (idx 0) ω| ∂μ)
    (fun W hW01 hWmeas => by
      have := (AuxSW.swi hXint hC hidx hidxt hW01 hWmeas).1
      have heq : (fun ω => ∑ k ∈ range n, W k ω * (-X (idx (k + 1)) ω - -X (idx k) ω))
          = fun ω => -∑ k ∈ range n, W k ω * (X (idx (k + 1)) ω - X (idx k) ω) := by
        funext ω
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [heq, integral_neg]
      linarith)
  rw [h0, hn] at h1 h2
  simp only [abs_neg] at h2
  have hsub : {ω | ∃ s ∈ F, lam < |X s ω|} ⊆ {ω | ∃ k ≤ n, lam < X (idx k) ω}
      ∪ {ω | ∃ k ≤ n, lam < -X (idx k) ω} := by
    intro ω ⟨s, hs, hlt⟩
    obtain ⟨k, hk, hks⟩ := exists_finIdx_eq (t := t) (Finset.mem_insert_of_mem hs : s ∈ G)
    rcases lt_abs.1 hlt with h | h
    · exact Or.inl ⟨k, hk.le, by rw [show idx k = s from hks]; exact h⟩
    · exact Or.inr ⟨k, hk.le, by rw [show idx k = s from hks]; exact h⟩
  have hP : μ.real {ω | ∃ s ∈ F, lam < |X s ω|} ≤ μ.real {ω | ∃ k ≤ n, lam < X (idx k) ω}
      + μ.real {ω | ∃ k ≤ n, lam < -X (idx k) ω} :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have i1 : 0 ≤ ∫ ω, |X t ω - X ⊥ ω| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have i2 : 0 ≤ ∫ ω, |X ⊥ ω| ∂μ := integral_nonneg fun _ => abs_nonneg _
  have i3 : 0 ≤ ∫ ω, |X t ω| ∂μ := integral_nonneg fun _ => abs_nonneg _
  rw [le_div_iff₀ hlam]
  nlinarith [h1, h2, hP, hlam]

end Maximal

end ProbabilityTheory
