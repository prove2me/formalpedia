-- Prove2me | solution 1 for WilliamsonShmoys.triangular_plane_map_edge_card
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:51:50.133734+00:00
-- url     : https://prove2.me/submissions/3f224480-e689-4fc5-abd9-29be2db60026

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hFaces : ∃ (F : Type) (faceInst : Fintype F)
      (boundary : F → Finset (Sym2 V)),
      (∀ f, (boundary f).card = 3) ∧
      (∀ f, ∀ e ∈ boundary f, e ∈ L.edgeSet) ∧
      (∀ e ∈ L.edgeSet,
        ((@Finset.univ F faceInst).filter (fun f => e ∈ boundary f)).card = 2) ∧
      Fintype.card V + @Fintype.card F faceInst = L.edgeSet.ncard + 2) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  classical
  obtain ⟨F, inst, boundary, h3, hsub, h2, hE⟩ := hFaces
  letI := inst
  -- double count pairs (f, e) with e ∈ boundary f
  have hfin : L.edgeSet.Finite := Set.toFinite _
  set Es : Finset (Sym2 V) := hfin.toFinset with hEs
  have hEcard : L.edgeSet.ncard = Es.card := Set.ncard_eq_toFinset_card L.edgeSet hfin
  have hsum1 : ∑ f : F, (boundary f).card = 3 * Fintype.card F := by
    simp [h3, mul_comm]
  have hsum2 : ∑ f : F, (boundary f).card = 2 * Es.card := by
    have : ∑ f : F, (boundary f).card = ∑ f : F, ∑ e ∈ Es, if e ∈ boundary f then 1 else 0 := by
      refine Finset.sum_congr rfl (fun f _ => ?_)
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      ext e
      simp only [Finset.mem_filter, hEs, Set.Finite.mem_toFinset]
      constructor
      · intro he; exact ⟨hsub f e he, he⟩
      · intro he; exact he.2
    rw [this, Finset.sum_comm]
    have : ∀ e ∈ Es, (∑ f : F, if e ∈ boundary f then 1 else 0) = 2 := by
      intro e he
      have he' : e ∈ L.edgeSet := by simpa [hEs] using he
      have := h2 e he'
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      exact this
    rw [Finset.sum_congr rfl this]
    simp [mul_comm]
  have hF : 3 * Fintype.card F = 2 * Es.card := by omega
  rw [hEcard] at hE ⊢
  omega
