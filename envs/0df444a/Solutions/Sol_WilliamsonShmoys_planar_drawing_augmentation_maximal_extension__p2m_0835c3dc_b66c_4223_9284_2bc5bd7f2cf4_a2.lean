-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_augmentation_maximal_extension__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:47:54.938771+00:00
-- url     : https://prove2.me/submissions/a7efc9c7-b890-47ad-bcae-7b9c07cb0acf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L := by
  classical
  let E : SimpleGraph V → Finset (V × V) := fun G =>
    Finset.univ.filter (fun e => G.Adj e.1 e.2)
  let A : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun G => K ≤ G ∧ HasPlanarDrawingOn G)
  have hA : A.Nonempty := by
    refine ⟨K, ?_⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_rfl, hK⟩
  obtain ⟨L, hL, hmax⟩ := Finset.exists_max_image A (fun G => (E G).card) hA
  have hLprops : K ≤ L ∧ HasPlanarDrawingOn L := by
    simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hL
  refine ⟨L, hLprops.1, hLprops.2, ?_⟩
  intro M hLM hM
  by_contra hML
  change (¬ ∀ ⦃a b : V⦄, M.Adj a b → L.Adj a b) at hML
  push_neg at hML
  rcases hML with ⟨a, b, habM, habL⟩
  have hMA : M ∈ A := by
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hLprops.1.trans hLM, hM⟩
  have hsub : E L ⊆ E M := by
    intro e he
    change e ∈ (Finset.univ.filter (fun p => L.Adj p.1 p.2)) at he
    change e ∈ (Finset.univ.filter (fun p => M.Adj p.1 p.2)
    )
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact hLM he
  have hMmem : (a, b) ∈ E M := by
    simp [E, habM]
  have hnLmem : (a, b) ∉ E L := by
    simp [E, habL]
  have hne : E L ≠ E M := by
    intro heq
    apply hnLmem
    rw [heq]
    exact hMmem
  have hss : E L ⊂ E M := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  have hcard : (E L).card < (E M).card := Finset.card_lt_card hss
  have hmaxM := hmax M hMA
  omega
