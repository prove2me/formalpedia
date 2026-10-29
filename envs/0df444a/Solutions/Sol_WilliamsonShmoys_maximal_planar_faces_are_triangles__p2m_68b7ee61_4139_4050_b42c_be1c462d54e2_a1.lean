-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_faces_are_triangles__p2m_68b7ee61_4139_4050_b42c_be1c462d54e2_a1
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:37:08.304215+00:00
-- url     : https://prove2.me/submissions/c5c60c55-b946-46ed-be6a-530b8d9467f9

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

namespace DisTriHelp

def px : Fin 4 → ℝ := ![0, 3, 0, 1]
def py : Fin 4 → ℝ := ![0, 0, 3, 1]

noncomputable def pt (v : Fin 4) : ℝ × ℝ := (px v, py v)

noncomputable def arc (u v : Fin 4) (t : ℝ) : ℝ × ℝ :=
  ((1 - t) * px u + t * px v, (1 - t) * py u + t * py v)

lemma drawK4 : WilliamsonShmoys.HasPlanarDrawingOn (⊤ : SimpleGraph (Fin 4)) := by
  refine ⟨pt, arc, ?_, ?_, ?_⟩
  · intro a b h
    simp only [pt, Prod.ext_iff] at h
    fin_cases a <;> fin_cases b <;> simp_all [px, py] <;> norm_num at h
  · intro u v huv _
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · unfold arc; fun_prop
    · intro t _ s _ h
      simp only [arc, Prod.ext_iff] at h
      obtain ⟨h1, h2⟩ := h
      fin_cases u <;> fin_cases v <;> simp [px, py] at h1 h2 huv ⊢ <;> nlinarith
    · simp [arc, pt]
    · simp [arc, pt]
    · intro t ht w h
      simp only [arc, pt, Prod.ext_iff] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨ht0, ht1⟩ := ht
      fin_cases u <;> fin_cases v <;> fin_cases w <;> simp [px, py] at h1 h2 huv <;> linarith
  · intro u v x y huv hxy _ _ hne t ht s hs h
    simp only [arc, Prod.ext_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ht0, ht1⟩ := ht
    obtain ⟨hs0, hs1⟩ := hs
    fin_cases u <;> fin_cases v <;> fin_cases x <;> fin_cases y <;>
      simp [px, py] at h1 h2 huv hxy hne ⊢ <;>
      first
        | (exfalso; linarith)
        | (refine ⟨Or.inl ?_, Or.inl ?_⟩ <;> linarith)
        | (refine ⟨Or.inl ?_, Or.inr ?_⟩ <;> linarith)
        | (refine ⟨Or.inr ?_, Or.inl ?_⟩ <;> linarith)
        | (refine ⟨Or.inr ?_, Or.inr ?_⟩ <;> linarith)

def bd : Fin 3 → Finset (Sym2 (Fin 4)) :=
  ![{s(0,1), s(1,2), s(2,3), s(0,3)},
    {s(0,1), s(1,3), s(2,3), s(0,2)},
    {s(0,2), s(1,2), s(1,3), s(0,3)}]

end DisTriHelp

open DisTriHelp in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      Set.Subset M.edgeSet L.edgeSet)
    (F : Type) (faceInst : Fintype F)
    (boundary : F → Finset (Sym2 V))
    (hsize : ∀ f, 3 ≤ (boundary f).card)
    (hmem : ∀ f, ∀ e ∈ boundary f, e ∈ L.edgeSet)
    (hinc : ∀ e ∈ L.edgeSet,
      ((@Finset.univ F faceInst).filter (fun f => e ∈ boundary f)).card = 2)
    (hCard : 3 ≤ Fintype.card V),
    ∀ f, (boundary f).card = 3) := by
  intro h
  have := h (V := Fin 4) ⊤ drawK4
    (by
      intro M _ _ e he
      rw [SimpleGraph.edgeSet_top]
      exact M.not_isDiag_of_mem_edgeSet he)
    (Fin 3) inferInstance bd (by decide)
    (by intro f e he; rw [SimpleGraph.edgeSet_top]; revert e; revert f; decide)
    (by rw [SimpleGraph.edgeSet_top]; decide) (by decide) 0
  revert this; decide
