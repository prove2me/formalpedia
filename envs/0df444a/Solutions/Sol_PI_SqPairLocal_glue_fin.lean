-- Prove2me | solution 1 for PI.SqPairLocal.glue_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:12.68897+00:00
-- url     : https://prove2.me/submissions/c1284200-5872-432e-b52f-68faa8e61f76

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Theorems.Thm_PI_SqPairLocal_pres_zero
import Theorems.Thm_PI_SqPairLocal_comap_cj_comap
import Theorems.Thm_PI_SqPairLocal_isMaximal_comap_cj
import Theorems.Thm_PI_SqPairLocal_glue_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution (hP : PowLoc) (hO : OnePlace) (hE : PI.IsCMUnram E)
    {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hN : Even N) (h' : IsSDG E N L') (h'' : IsSDG E N L'')
    {c : 𝓞 E} (hc : c ≠ 0) (T : Finset (Ideal (𝓞 E))) (hT : ∀ P ∈ T, P.IsMaximal) :
    ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧
      ∀ P ∈ T, Good P c L' L'' e ∧ Good (P.comap (cj E)) c L' L'' e := by
  classical
  revert hT
  refine Finset.induction_on T ?_ ?_
  · intro _
    exact ⟨0, pres_zero, pres_zero, fun P h => by simp at h⟩
  · intro Q T' _ ih hT
    obtain ⟨e₁, p₁', p₁'', g₁⟩ := ih (fun P hP' => hT P (Finset.mem_insert_of_mem hP'))
    have hQm : Q.IsMaximal := hT Q (Finset.mem_insert_self Q T')
    obtain ⟨e₂, p₂', p₂'', gQ, gQc⟩ := hO E hE N L' L'' hN h' h'' Q hQm c hc
    have hAm : ∀ P ∈ T' ∪ T'.image (fun P => P.comap (cj E)), P.IsMaximal := by
      intro P hP'
      rcases Finset.mem_union.mp hP' with h | h
      · exact hT P (Finset.mem_insert_of_mem h)
      · obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp h
        exact isMaximal_comap_cj (hT P0 (Finset.mem_insert_of_mem hP0))
    have hBm : ∀ P ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E))), P.IsMaximal := by
      intro P hP'
      rcases Finset.mem_insert.mp hP' with h | h
      · rw [h]; exact hQm
      · rw [Finset.mem_singleton.mp h]; exact isMaximal_comap_cj hQm
    have hA : ∀ P ∈ T' ∪ T'.image (fun P => P.comap (cj E)),
        P.comap (cj E) ∈ T' ∪ T'.image (fun P => P.comap (cj E)) := by
      intro P hP'
      rcases Finset.mem_union.mp hP' with h | h
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
      · obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp h
        simp only [comap_cj_comap]
        exact Finset.mem_union_left _ hP0
    have hB : ∀ P ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E))),
        P.comap (cj E) ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E))) := by
      intro P hP'
      rcases Finset.mem_insert.mp hP' with h | h
      · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · rw [Finset.mem_singleton.mp h, comap_cj_comap]
        exact Finset.mem_insert_self _ _
    have hg₁ : ∀ P ∈ T' ∪ T'.image (fun P => P.comap (cj E)), Good P c L' L'' e₁ := by
      intro P hP'
      rcases Finset.mem_union.mp hP' with h | h
      · exact (g₁ P h).1
      · obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp h
        exact (g₁ P0 hP0).2
    have hg₂ : ∀ P ∈ ({Q, Q.comap (cj E)} : Finset (Ideal (𝓞 E))), Good P c L' L'' e₂ := by
      intro P hP'
      rcases Finset.mem_insert.mp hP' with h | h
      · rw [h]; exact gQ
      · rw [Finset.mem_singleton.mp h]; exact gQc
    obtain ⟨e, q', q'', g⟩ :=
      glue_two hP h' h'' hc _ _ hAm hBm hA hB p₁' p₁'' p₂' p₂'' hg₁ hg₂
    refine ⟨e, q', q'', fun P hP' => ?_⟩
    rcases Finset.mem_insert.mp hP' with h | hPT
    · rw [h]
      exact ⟨g _ (Finset.mem_union_right _ (Finset.mem_insert_self _ _)),
        g _ (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))⟩
    · exact ⟨g _ (Finset.mem_union_left _ (Finset.mem_union_left _ hPT)),
        g _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPT)))⟩
end PI.SqPairLocal
