-- Prove2me | solution 1 for SPFacilityGraph.lemma_I_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:15:46.736431+00:00
-- url     : https://prove2.me/submissions/59e70f3e-5a68-4a90-b5c8-08da9932a199

import Mathlib

set_option autoImplicit false

namespace SPFGLemmaI1

/-- Sorting a finite set of breakpoints containing `0` and `1` inside `[0,1]`. -/
lemma partition_of_finset (B : Finset ℝ) (h0 : (0:ℝ) ∈ B) (h1 : (1:ℝ) ∈ B)
    (hB : ∀ b ∈ B, b ∈ Set.Icc (0:ℝ) 1) (Good : ℝ → ℝ → Prop)
    (hgood : ∀ c ∈ B, ∀ d ∈ B, c < d → (∀ b ∈ B, ¬ (c < b ∧ b < d)) → Good c d) :
    ∃ (m : ℕ) (s : Fin (m + 1) → ℝ), StrictMono s ∧ s 0 = 0 ∧ s (Fin.last m) = 1 ∧
      ∀ j : Fin m, Good (s j.castSucc) (s j.succ) := by
  have hpos : 0 < B.card := Finset.card_pos.2 ⟨0, h0⟩
  set m := B.card - 1 with hm
  have hcard : B.card = m + 1 := by omega
  let s := B.orderEmbOfFin hcard
  refine ⟨m, s, s.strictMono, ?_, ?_, ?_⟩
  · have := Finset.orderEmbOfFin_zero hcard (Nat.succ_pos m)
    refine (show s 0 = s ⟨0, Nat.succ_pos m⟩ from rfl).trans (this.trans ?_)
    apply le_antisymm (Finset.min'_le _ _ h0)
    exact (hB _ (Finset.min'_mem _ _)).1
  · have := Finset.orderEmbOfFin_last hcard (Nat.succ_pos m)
    refine (show s (Fin.last m) = s ⟨m + 1 - 1, by omega⟩ from by congr 1).trans (this.trans ?_)
    apply le_antisymm _ (Finset.le_max' _ _ h1)
    exact (hB _ (Finset.max'_mem _ _)).2
  · intro j
    refine hgood _ (Finset.orderEmbOfFin_mem _ _ _) _ (Finset.orderEmbOfFin_mem _ _ _)
      (s.strictMono (Fin.castSucc_lt_succ)) ?_
    rintro b hb ⟨hb1, hb2⟩
    have : b ∈ Set.range s := by rw [Finset.range_orderEmbOfFin]; exact hb
    obtain ⟨l, rfl⟩ := this
    have h1 := s.lt_iff_lt.1 hb1
    have h2 := s.lt_iff_lt.1 hb2
    rw [Fin.lt_def] at h1 h2
    simp at h1 h2
    omega

end SPFGLemmaI1

open SPFGLemmaI1

theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (𝒰 : Finset (Finset V)) (γ : ℝ → V)
    (hcover : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ ⋃ P ∈ 𝒰, convexHull ℝ (P : Set V))
    (hcont : ContinuousOn γ (Set.Icc 0 1))
    (hpw : ∃ (p : ℕ) (r : Fin (p + 1) → ℝ), StrictMono r ∧ r 0 = 0 ∧ r (Fin.last p) = 1 ∧
      ∀ j : Fin p, ∃ a b : V, ∀ s ∈ Set.Icc (r j.castSucc) (r j.succ), γ s = a + s • b) :
    ∃ (m : ℕ) (s : Fin (m + 1) → ℝ), StrictMono s ∧ s 0 = 0 ∧ s (Fin.last m) = 1 ∧
      ∀ j : Fin m, ∃ P ∈ 𝒰, γ '' Set.Icc (s j.castSucc) (s j.succ) ⊆ convexHull ℝ (P : Set V) := by
  classical
  obtain ⟨p, r, hr, hr0, hr1, hpiece⟩ := hpw
  choose a b hab using hpiece
  -- the pieces of the preimages
  let I : Fin p → Finset V → Set ℝ := fun j P =>
    Set.Icc (r j.castSucc) (r j.succ) ∩ {s | γ s ∈ convexHull ℝ (P : Set V)}
  have hI_eq : ∀ j P, I j P = Set.Icc (r j.castSucc) (r j.succ) ∩
      (AffineMap.lineMap (a j) (a j + b j) : ℝ →ᵃ[ℝ] V) ⁻¹' convexHull ℝ (P : Set V) := by
    intro j P
    ext s
    simp only [I, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, and_congr_right_iff]
    intro hs
    rw [hab j s hs, AffineMap.lineMap_apply]
    simp [add_comm]
  have hIconv : ∀ j P, Convex ℝ (I j P) := by
    intro j P; rw [hI_eq]
    exact (convex_Icc _ _).inter ((convex_convexHull ℝ _).affine_preimage _)
  have hIclosed : ∀ j P, IsClosed (I j P) := by
    intro j P; rw [hI_eq]
    exact isClosed_Icc.inter ((P.finite_toSet.isCompact_convexHull ℝ).isClosed.preimage
      (AffineMap.lineMap_continuous))
  have hIbdd : ∀ j P, BddBelow (I j P) ∧ BddAbove (I j P) := fun j P =>
    ⟨bddBelow_Icc.mono Set.inter_subset_left, bddAbove_Icc.mono Set.inter_subset_left⟩
  have hrI : ∀ l, r l ∈ Set.Icc (0:ℝ) 1 := fun l =>
    ⟨hr0 ▸ hr.monotone (Fin.zero_le _), hr1 ▸ hr.monotone (Fin.le_last _)⟩
  -- the breakpoints
  let B0 : Finset ℝ := insert 0 (insert 1 (Finset.univ.image r ∪
    (Finset.univ ×ˢ 𝒰).image (fun jP => sInf (I jP.1 jP.2)) ∪
    (Finset.univ ×ˢ 𝒰).image (fun jP => sSup (I jP.1 jP.2))))
  let B := B0.filter (fun b => b ∈ Set.Icc (0:ℝ) 1)
  have hB0 : (0:ℝ) ∈ B := Finset.mem_filter.2 ⟨by simp [B0], by simp⟩
  have hB1 : (1:ℝ) ∈ B := Finset.mem_filter.2 ⟨by simp [B0], by simp⟩
  have hBr : ∀ l, r l ∈ B := fun l => Finset.mem_filter.2 ⟨by simp [B0], hrI l⟩
  have hBlo : ∀ j, ∀ P ∈ 𝒰, (I j P).Nonempty → sInf (I j P) ∈ B ∧ sSup (I j P) ∈ B ∧
      sInf (I j P) ∈ I j P ∧ sSup (I j P) ∈ I j P := by
    intro j P hP hne
    have hinf := (hIclosed j P).csInf_mem hne (hIbdd j P).1
    have hsup := (hIclosed j P).csSup_mem hne (hIbdd j P).2
    have hsub : ∀ s ∈ I j P, s ∈ Set.Icc (0:ℝ) 1 := fun s hs =>
      ⟨(hrI _).1.trans hs.1.1, hs.1.2.trans (hrI _).2⟩
    refine ⟨Finset.mem_filter.2 ⟨?_, hsub _ hinf⟩, Finset.mem_filter.2 ⟨?_, hsub _ hsup⟩, hinf, hsup⟩
    · simp only [B0, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      right; right; left; right; exact ⟨(j, P), Finset.mem_product.2 ⟨Finset.mem_univ _, hP⟩, rfl⟩
    · simp only [B0, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      right; right; right; exact ⟨(j, P), Finset.mem_product.2 ⟨Finset.mem_univ _, hP⟩, rfl⟩
  refine partition_of_finset B hB0 hB1 (fun b hb => (Finset.mem_filter.1 hb).2)
    (fun c d => ∃ P ∈ 𝒰, γ '' Set.Icc c d ⊆ convexHull ℝ (P : Set V)) ?_
  intro c hc d hd hcd hgap
  have hcI := (Finset.mem_filter.1 hc).2
  have hdI := (Finset.mem_filter.1 hd).2
  -- find the affine piece containing `[c, d]`
  obtain ⟨j, hjc, hjd⟩ : ∃ j : Fin p, r j.castSucc ≤ c ∧ d ≤ r j.succ := by
    let S := Finset.univ.filter (fun l : Fin (p+1) => c < r l)
    have hSne : S.Nonempty := ⟨Fin.last p, by simp [S, hr1]; linarith [hdI.2]⟩
    set l := S.min' hSne with hl
    have hlS : c < r l := (Finset.mem_filter.1 (S.min'_mem hSne)).2
    have hl0 : l ≠ 0 := by
      intro h; rw [h, hr0] at hlS; linarith [hcI.1]
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq.2 hl0
    refine ⟨j, ?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      have : l ≤ j.castSucc := S.min'_le _ (by simp [S, hlt])
      rw [← hj] at this
      exact absurd this (not_le.2 Fin.castSucc_lt_succ)
    · rw [hj]
      by_contra hlt
      push Not at hlt
      exact hgap _ (hBr l) ⟨hlS, hlt⟩
  -- the midpoint lies in some cell
  set mid := (c + d) / 2 with hmd
  have hmidI : mid ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [hcI.1], by linarith [hdI.2]⟩
  obtain ⟨P, hP, hγP⟩ := Set.mem_iUnion₂.1 (hcover mid hmidI)
  have hmid : mid ∈ I j P := ⟨⟨by rw [hmd]; linarith, by rw [hmd]; linarith⟩, hγP⟩
  obtain ⟨hloB, hhiB, hloI, hhiI⟩ := hBlo j P hP ⟨mid, hmid⟩
  have hlo : sInf (I j P) ≤ c := by
    by_contra h; push Not at h
    have : sInf (I j P) ≤ mid := csInf_le (hIbdd j P).1 hmid
    exact hgap _ hloB ⟨h, by rw [hmd] at this; linarith⟩
  have hhi : d ≤ sSup (I j P) := by
    by_contra h; push Not at h
    have : mid ≤ sSup (I j P) := le_csSup (hIbdd j P).2 hmid
    exact hgap _ hhiB ⟨by rw [hmd] at this; linarith, h⟩
  refine ⟨P, hP, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have : s ∈ I j P := (hIconv j P).ordConnected.out hloI hhiI ⟨hlo.trans hs.1, hs.2.trans hhi⟩
  exact this.2
