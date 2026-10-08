-- Prove2me | solution 1 for ProjSchedTW.Cumulative.inventoryFeasible_iff_resolves_minimal_sets
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:14:42.571411+00:00
-- url     : https://prove2.me/submissions/aebe6602-292e-46b9-96c3-a4dda5a9ea92

import Mathlib
import Definitions.Def_ProjSchedTW_Cumulative_Model

set_option autoImplicit false

open ProjSchedTW.Cumulative in
theorem afbb6247_mem_active {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (S : Fin (n + 2) → ℝ) (k : K) (t : ℝ) (i : Fin (n + 2)) :
    i ∈ activeSet P S k t ↔
      (P.r i k < 0 ∧ S i ≤ t) ∨ (0 < P.r i k ∧ S i + (P.p i : ℝ) ≤ t) := by
  simp [activeSet]

open ProjSchedTW.Cumulative in
theorem afbb6247_sum_eq_ite {n : ℕ} {K : Type} (P : CumulativeProject n K) (k : K)
    (s : Finset (Fin (n + 2))) :
    ∑ i ∈ s, P.r i k = ∑ i, if i ∈ s then P.r i k else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

open ProjSchedTW.Cumulative in
theorem afbb6247_fwd_surplus {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (hRem : BoundsStraddleZero P) (S : Fin (n + 2) → ℝ) (hS : IsSchedule S)
    (hF : InventoryFeasible P S) : ResolvesSurplusSets P S := by
  classical
  intro k F hFmin
  obtain ⟨⟨_, hsum⟩, -, -⟩ := hFmin
  by_contra hcon
  push Not at hcon
  have hFp : (F.filter (fun j => 0 < P.r j k)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : ∑ i ∈ F, P.r i k ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      by_contra h'
      push Not at h'
      have : i ∈ F.filter (fun j => 0 < P.r j k) := Finset.mem_filter.2 ⟨hi, h'⟩
      simp [h] at this
    linarith [(hRem k).2]
  obtain ⟨j0, hj0, hmax⟩ := (F.filter (fun j => 0 < P.r j k)).exists_max_image
    (fun j => S j + (P.p j : ℝ)) hFp
  rw [Finset.mem_filter] at hj0
  have ht : 0 ≤ S j0 + (P.p j0 : ℝ) := by have := hS.2 j0; positivity
  have hinv := (hF k _ ht).2
  have hle : ∑ i ∈ F, P.r i k ≤ inventory P S k (S j0 + (P.p j0 : ℝ)) := by
    unfold inventory
    rw [afbb6247_sum_eq_ite, afbb6247_sum_eq_ite]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h1 h2 h2
    · exact le_rfl
    · by_contra h3
      push Not at h3
      exact h2 ((afbb6247_mem_active P S k _ i).2
        (Or.inr ⟨h3, hmax i (Finset.mem_filter.2 ⟨h1, h3⟩)⟩))
    · rcases (afbb6247_mem_active P S k _ i).1 h2 with ⟨h3, h4⟩ | ⟨h3, _⟩
      · have := hcon j0 hj0.1 i h1 hj0.2 h3
        linarith
      · exact h3.le
    · exact le_rfl
  linarith

open ProjSchedTW.Cumulative in
theorem afbb6247_fwd_shortage {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (hRem : BoundsStraddleZero P) (S : Fin (n + 2) → ℝ) (hS : IsSchedule S)
    (hF : InventoryFeasible P S) : ResolvesShortageSets P S := by
  classical
  intro k F hFmin
  obtain ⟨⟨_, hsum⟩, -, -⟩ := hFmin
  by_contra hcon
  push Not at hcon
  have hFn : (F.filter (fun j => P.r j k < 0)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : 0 ≤ ∑ i ∈ F, P.r i k := by
      apply Finset.sum_nonneg
      intro i hi
      by_contra h'
      push Not at h'
      have : i ∈ F.filter (fun j => P.r j k < 0) := Finset.mem_filter.2 ⟨hi, h'⟩
      simp [h] at this
    linarith [(hRem k).1]
  obtain ⟨j0, hj0, hmax⟩ := (F.filter (fun j => P.r j k < 0)).exists_max_image S hFn
  rw [Finset.mem_filter] at hj0
  have ht : 0 ≤ S j0 := hS.2 j0
  have hinv := (hF k _ ht).1
  have hle : inventory P S k (S j0) ≤ ∑ i ∈ F, P.r i k := by
    unfold inventory
    rw [afbb6247_sum_eq_ite, afbb6247_sum_eq_ite]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h1 h2 h2
    · exact le_rfl
    · rcases (afbb6247_mem_active P S k _ i).1 h1 with ⟨h3, _⟩ | ⟨h3, h4⟩
      · exact h3.le
      · have := hcon j0 hj0.1 i h2 hj0.2 h3
        linarith
    · by_contra h3
      push Not at h3
      exact h1 ((afbb6247_mem_active P S k _ i).2
        (Or.inl ⟨h3, hmax i (Finset.mem_filter.2 ⟨h2, h3⟩)⟩))
    · exact le_rfl
  linarith

open ProjSchedTW.Cumulative in
theorem afbb6247_bwd_upper {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (hRem : BoundsStraddleZero P) (S : Fin (n + 2) → ℝ)
    (hR : ResolvesSurplusSets P S) (k : K) (t : ℝ) :
    inventory P S k t ≤ P.Rup k := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hA⟩ : ∃ A, A = activeSet P S k t := ⟨_, rfl⟩
  have hmem : ∀ i, i ∈ A ↔ (P.r i k < 0 ∧ S i ≤ t) ∨ (0 < P.r i k ∧ S i + (P.p i : ℝ) ≤ t) :=
    fun i => hA ▸ afbb6247_mem_active P S k t i
  have hlt' : P.Rup k < ∑ i ∈ A, P.r i k := by rw [hA]; exact hlt
  let w : Fin (n + 2) → ℤ := fun i => if 0 < P.r i k then 1 else if P.r i k < 0 then -1 else 0
  let G := (Finset.univ : Finset (Finset (Fin (n + 2)))).filter (fun F =>
    IsSurplusSet P k F ∧ (∀ j ∈ F, 0 < P.r j k → j ∈ A) ∧ (∀ i ∈ A, P.r i k < 0 → i ∈ F))
  have hAG : A ∈ G := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨?_, hlt'⟩, fun j hj _ => hj, fun i hi _ => hi⟩
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hlt'
    linarith [(hRem k).2]
  obtain ⟨F, hFG, hFmin⟩ := G.exists_min_image (fun F => ∑ i ∈ F, w i) ⟨A, hAG⟩
  obtain ⟨-, hFs, hFA, hAF⟩ := Finset.mem_filter.1 hFG
  have hmin : IsMinimalSurplusSet P k F := by
    refine ⟨hFs, ?_, ?_⟩
    · rintro ⟨F', hss, hF's, hpos⟩
      have hF'G : F' ∈ G := Finset.mem_filter.2 ⟨Finset.mem_univ _, hF's,
        fun j hj hr => hFA j (hss.subset hj) hr, fun i hi hr => by
          by_contra hni
          have := hpos i (Finset.mem_sdiff.2 ⟨hAF i hi hr, hni⟩)
          linarith⟩
      have h1 := hFmin F' hF'G
      have h2 : 0 < ∑ i ∈ F \ F', w i := by
        apply Finset.sum_pos
        · intro i hi; simp [w, hpos i hi]
        · exact Finset.sdiff_nonempty.2 (not_subset_of_ssubset hss)
      have h3 := Finset.sum_sdiff (f := w) hss.subset
      linarith
    · rintro ⟨F'', hss, hF''s, hneg⟩
      have hF''G : F'' ∈ G := Finset.mem_filter.2 ⟨Finset.mem_univ _, hF''s,
        fun j hj hr => by
          by_cases hjF : j ∈ F
          · exact hFA j hjF hr
          · have := hneg j (Finset.mem_sdiff.2 ⟨hj, hjF⟩)
            linarith,
        fun i hi hr => hss.subset (hAF i hi hr)⟩
      have h1 := hFmin F'' hF''G
      have h2 : ∑ i ∈ F'' \ F, w i < 0 := by
        apply Finset.sum_neg
        · intro i hi
          have := hneg i hi
          simp [w, this, not_lt.2 this.le]
        · exact Finset.sdiff_nonempty.2 (not_subset_of_ssubset hss)
      have h3 := Finset.sum_sdiff (f := w) hss.subset
      linarith
  obtain ⟨j, hjF, i, hiF, hj, hi, hSij⟩ := hR k F hmin
  have hjt : S j + (P.p j : ℝ) ≤ t := by
    rcases (hmem j).1 (hFA j hjF hj) with ⟨h, _⟩ | ⟨_, h⟩
    · omega
    · exact h
  have hit : t < S i := by
    by_contra hc
    push Not at hc
    exact hiF (hAF i ((hmem i).2 (Or.inl ⟨hi, hc⟩)) hi)
  linarith

open ProjSchedTW.Cumulative in
theorem afbb6247_bwd_lower {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (hRem : BoundsStraddleZero P) (S : Fin (n + 2) → ℝ)
    (hR : ResolvesShortageSets P S) (k : K) (t : ℝ) :
    P.Rlow k ≤ inventory P S k t := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hA⟩ : ∃ A, A = activeSet P S k t := ⟨_, rfl⟩
  have hmem : ∀ i, i ∈ A ↔ (P.r i k < 0 ∧ S i ≤ t) ∨ (0 < P.r i k ∧ S i + (P.p i : ℝ) ≤ t) :=
    fun i => hA ▸ afbb6247_mem_active P S k t i
  have hlt' : ∑ i ∈ A, P.r i k < P.Rlow k := by rw [hA]; exact hlt
  let w : Fin (n + 2) → ℤ := fun i => if 0 < P.r i k then 1 else if P.r i k < 0 then -1 else 0
  let G := (Finset.univ : Finset (Finset (Fin (n + 2)))).filter (fun F =>
    IsShortageSet P k F ∧ (∀ j ∈ F, P.r j k < 0 → j ∈ A) ∧ (∀ i ∈ A, 0 < P.r i k → i ∈ F))
  have hAG : A ∈ G := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨?_, hlt'⟩, fun j hj _ => hj, fun i hi _ => hi⟩
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hlt'
    linarith [(hRem k).1]
  obtain ⟨F, hFG, hFmax⟩ := G.exists_max_image (fun F => ∑ i ∈ F, w i) ⟨A, hAG⟩
  obtain ⟨-, hFs, hFA, hAF⟩ := Finset.mem_filter.1 hFG
  have hmin : IsMinimalShortageSet P k F := by
    refine ⟨hFs, ?_, ?_⟩
    · rintro ⟨F', hss, hF's, hneg⟩
      have hF'G : F' ∈ G := Finset.mem_filter.2 ⟨Finset.mem_univ _, hF's,
        fun j hj hr => hFA j (hss.subset hj) hr, fun i hi hr => by
          by_contra hni
          have := hneg i (Finset.mem_sdiff.2 ⟨hAF i hi hr, hni⟩)
          linarith⟩
      have h1 := hFmax F' hF'G
      have h2 : ∑ i ∈ F \ F', w i < 0 := by
        apply Finset.sum_neg
        · intro i hi
          have := hneg i hi
          simp [w, this, not_lt.2 this.le]
        · exact Finset.sdiff_nonempty.2 (not_subset_of_ssubset hss)
      have h3 := Finset.sum_sdiff (f := w) hss.subset
      linarith
    · rintro ⟨F'', hss, hF''s, hpos⟩
      have hF''G : F'' ∈ G := Finset.mem_filter.2 ⟨Finset.mem_univ _, hF''s,
        fun j hj hr => by
          by_cases hjF : j ∈ F
          · exact hFA j hjF hr
          · have := hpos j (Finset.mem_sdiff.2 ⟨hj, hjF⟩)
            linarith,
        fun i hi hr => hss.subset (hAF i hi hr)⟩
      have h1 := hFmax F'' hF''G
      have h2 : 0 < ∑ i ∈ F'' \ F, w i := by
        apply Finset.sum_pos
        · intro i hi; simp [w, hpos i hi]
        · exact Finset.sdiff_nonempty.2 (not_subset_of_ssubset hss)
      have h3 := Finset.sum_sdiff (f := w) hss.subset
      linarith
  obtain ⟨j, hjF, i, hiF, hj, hi, hSij⟩ := hR k F hmin
  have hjt : S j ≤ t := by
    rcases (hmem j).1 (hFA j hjF hj) with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · omega
  have hit : t < S i + (P.p i : ℝ) := by
    by_contra hc
    push Not at hc
    exact hiF (hAF i ((hmem i).2 (Or.inr ⟨hi, hc⟩)) hi)
  linarith

open ProjSchedTW.Cumulative in
theorem solution {n : ℕ} {K : Type}
    (P : CumulativeProject n K)
    (h2121 : TotalDemandWithinBounds P) (hRem : BoundsStraddleZero P)
    (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) :
    InventoryFeasible P S ↔ ResolvesSurplusSets P S ∧ ResolvesShortageSets P S := by
  constructor
  · intro hF
    exact ⟨afbb6247_fwd_surplus P hRem S hS hF, afbb6247_fwd_shortage P hRem S hS hF⟩
  · rintro ⟨h1, h2⟩ k t _
    exact ⟨afbb6247_bwd_lower P hRem S h2 k t, afbb6247_bwd_upper P hRem S h1 k t⟩
