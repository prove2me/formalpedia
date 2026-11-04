-- Prove2me | solution 1 for QuantumMaxCutEnergy.laminar_internal_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:22:40.957211+00:00
-- url     : https://prove2.me/submissions/90785228-cde0-4e21-84f2-54ea4f8d6647

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- If two distinct vertices of `P` lie together in no proper member of a laminar family, and `P` is
cardinality-maximal among the members with a nonzero coefficient, then that coefficient vanishes. -/
theorem laminar_coeff_zero_of_edge {n : ℕ} (L : Finset (Finset (Fin n)))
    (hlam : ∀ S ∈ L, ∀ T ∈ L, S ≠ T → S ⊆ T ∨ T ⊆ S ∨ Disjoint S T)
    (c : Finset (Fin n) → ℝ)
    (hc : ∀ e : Edge n, ∑ S ∈ L, (if e.val.1 ∈ S ∧ e.val.2 ∈ S then c S else 0) = 0)
    (P : Finset (Fin n)) (hPL : P ∈ L)
    (hbig : ∀ T ∈ L, c T ≠ 0 → T.card ≤ P.card)
    (u v : Fin n) (hu : u ∈ P) (hv : v ∈ P) (huv : u ≠ v)
    (hno : ∀ T ∈ L, T ⊂ P → ¬ (u ∈ T ∧ v ∈ T)) : c P = 0 := by
  classical
  -- the edge spanned by `u` and `v`
  have hex : ∃ e : Edge n, (e.val.1 = u ∧ e.val.2 = v) ∨ (e.val.1 = v ∧ e.val.2 = u) := by
    rcases lt_or_gt_of_ne huv with h | h
    · exact ⟨⟨(u, v), h⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨⟨(v, u), h⟩, Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨e, hee⟩ := hex
  have hsum := hc e
  -- every member other than `P` contributes nothing
  have hzero : ∀ T ∈ L, T ≠ P →
      (if e.val.1 ∈ T ∧ e.val.2 ∈ T then c T else 0) = 0 := by
    intro T hTL hTP
    rcases hee with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hgoal : (if u ∈ T ∧ v ∈ T then c T else 0) = 0 := by
        rcases hlam P hPL T hTL (Ne.symm hTP) with hsub | hsub | hdisj
        · have hcT : c T = 0 := by
            by_contra hne
            have h1' := hbig T hTL hne
            have h2' : P.card < T.card :=
              Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hTP h.symm⟩)
            omega
          rw [if_pos ⟨hsub hu, hsub hv⟩, hcT]
        · rw [if_neg (hno T hTL (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hTP⟩))]
        · rw [if_neg (by rintro ⟨huT, -⟩; exact (Finset.disjoint_left.mp hdisj hu) huT)]
      rw [h1, h2]; exact hgoal
    · have hgoal : (if v ∈ T ∧ u ∈ T then c T else 0) = 0 := by
        rcases hlam P hPL T hTL (Ne.symm hTP) with hsub | hsub | hdisj
        · have hcT : c T = 0 := by
            by_contra hne
            have h1' := hbig T hTL hne
            have h2' : P.card < T.card :=
              Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hTP h.symm⟩)
            omega
          rw [if_pos ⟨hsub hv, hsub hu⟩, hcT]
        · rw [if_neg (fun h => hno T hTL (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hTP⟩) ⟨h.2, h.1⟩)]
        · rw [if_neg (by rintro ⟨hvT, -⟩; exact (Finset.disjoint_left.mp hdisj hv) hvT)]
      rw [h1, h2]; exact hgoal
  have hmain : ∑ S ∈ L, (if e.val.1 ∈ S ∧ e.val.2 ∈ S then c S else 0)
      = (if e.val.1 ∈ P ∧ e.val.2 ∈ P then c P else 0) := by
    refine Finset.sum_eq_single_of_mem P hPL (fun T hTL hTP => hzero T hTL hTP)
  rw [hmain] at hsum
  rcases hee with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, if_pos ⟨hu, hv⟩] at hsum; exact hsum
  · rw [h1, h2, if_pos ⟨hv, hu⟩] at hsum; exact hsum

/-- **Laminar independence.** For a laminar family of sets of size at least three, the incidence vectors of
their internal edge sets are linearly independent. -/
theorem solution {n : ℕ} (L : Finset (Finset (Fin n)))
    (hL3 : ∀ S ∈ L, 3 ≤ S.card)
    (hlam : ∀ S ∈ L, ∀ T ∈ L, S ≠ T → S ⊆ T ∨ T ⊆ S ∨ Disjoint S T) :
    ∀ c : Finset (Fin n) → ℝ,
      (∀ e : Edge n, ∑ S ∈ L, (if e.val.1 ∈ S ∧ e.val.2 ∈ S then c S else 0) = 0) →
      ∀ S ∈ L, c S = 0 := by
  classical
  intro c hc S₀ hS₀
  by_contra hS₀c
  set K : Finset (Finset (Fin n)) := L.filter (fun S => c S ≠ 0) with hK
  have hS₀K : S₀ ∈ K := Finset.mem_filter.mpr ⟨hS₀, hS₀c⟩
  obtain ⟨P, hPK, hPmax⟩ :=
    Finset.exists_max_image K (fun S : Finset (Fin n) => S.card) ⟨S₀, hS₀K⟩
  have hPL : P ∈ L := (Finset.mem_filter.mp hPK).1
  have hPc : c P ≠ 0 := (Finset.mem_filter.mp hPK).2
  have hbig : ∀ T ∈ L, c T ≠ 0 → T.card ≤ P.card := by
    intro T hTL hcT
    exact hPmax T (Finset.mem_filter.mpr ⟨hTL, hcT⟩)
  set M : Finset (Finset (Fin n)) := L.filter (fun T => T ⊂ P) with hM
  set W : Finset (Fin n) := M.biUnion (fun T => T) with hW
  have hWmem : ∀ u : Fin n, u ∈ W ↔ ∃ T ∈ M, u ∈ T := by
    intro u; rw [hW, Finset.mem_biUnion]
  have hP3 : 3 ≤ P.card := hL3 P hPL
  have hPcard2 : 1 < P.card := by omega
  by_cases hcase : ∃ u ∈ P, u ∉ W
  · obtain ⟨u, huP, huW⟩ := hcase
    obtain ⟨a, haP, b, hbP, hab⟩ := Finset.one_lt_card.mp hPcard2
    have hex : ∃ v ∈ P, v ≠ u := by
      by_cases hau : a = u
      · exact ⟨b, hbP, fun h => hab (by rw [hau, h])⟩
      · exact ⟨a, haP, hau⟩
    obtain ⟨v, hvP, hvu⟩ := hex
    refine hPc (laminar_coeff_zero_of_edge L hlam c hc P hPL hbig u v huP hvP (Ne.symm hvu) ?_)
    intro T hTL hTP hmem
    exact huW (hWmem u |>.mpr ⟨T, Finset.mem_filter.mpr ⟨hTL, hTP⟩, hmem.1⟩)
  · push_neg at hcase
    have hMne : M.Nonempty := by
      obtain ⟨a, haP, b, hbP, hab⟩ := Finset.one_lt_card.mp hPcard2
      obtain ⟨T, hT, haT⟩ := (hWmem a).mp (hcase a haP)
      exact ⟨T, hT⟩
    obtain ⟨T₁, hT₁M, hT₁max⟩ :=
      Finset.exists_max_image M (fun T : Finset (Fin n) => T.card) hMne
    have hT₁L : T₁ ∈ L := (Finset.mem_filter.mp hT₁M).1
    have hT₁P : T₁ ⊂ P := (Finset.mem_filter.mp hT₁M).2
    have hex : ∃ v ∈ P, v ∉ T₁ := by
      by_contra hcon
      push_neg at hcon
      exact hT₁P.2 (fun v hv => hcon v hv)
    obtain ⟨v, hvP, hvT₁⟩ := hex
    have hT₁3 : 3 ≤ T₁.card := hL3 T₁ hT₁L
    obtain ⟨u, huT₁⟩ := Finset.card_pos.mp (by omega : 0 < T₁.card)
    have huP : u ∈ P := hT₁P.1 huT₁
    have huv : u ≠ v := by rintro rfl; exact hvT₁ huT₁
    refine hPc (laminar_coeff_zero_of_edge L hlam c hc P hPL hbig u v huP hvP huv ?_)
    intro T hTL hTP hmem
    rcases hlam T hTL T₁ hT₁L (by intro h; rw [h] at hmem; exact hvT₁ hmem.2) with hsub | hsub | hdisj
    · exact hvT₁ (hsub hmem.2)
    · have hne : T₁ ≠ T := by intro h; rw [← h] at hmem; exact hvT₁ hmem.2
      have hlt : T₁ ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
      have hTM : T ∈ M := Finset.mem_filter.mpr ⟨hTL, hTP⟩
      have := hT₁max T hTM
      have := Finset.card_lt_card hlt
      omega
    · exact absurd huT₁ (Finset.disjoint_left.mp hdisj hmem.1)



#print axioms solution
