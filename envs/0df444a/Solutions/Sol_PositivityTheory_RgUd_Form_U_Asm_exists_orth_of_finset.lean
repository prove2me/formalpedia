-- Prove2me | solution 1 for PositivityTheory.RgUd.Form.U.Asm.exists_orth_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:55:30.374915+00:00
-- url     : https://prove2.me/submissions/3f519158-7638-44f4-82e6-2ff8d157ec77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_HermitianForms_UnitaryLattices_UnitaryHypotheses_ExistsOrthOfFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd.Form.U.Asm
namespace PositivityTheory.RgUd.Form.U.Asm
theorem _root_.solution {D : Type} [AddCommGroup D] [Module ℂ D] (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re) (s : Finset D) :
    ∀ u : D, ∃ w ∈ Submodule.span ℂ (s : Set D), ∀ m ∈ Submodule.span ℂ (s : Set D), B (u - w) m = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro u
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    intro m hm
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hm
    simp [hm]
  | insert a s ha ih =>
    intro u
    obtain ⟨wa, hwa, hwa'⟩ := ih a
    obtain ⟨wu, hwu, hwu'⟩ := ih u
    obtain ⟨a', ha'⟩ : ∃ a' : D, a' = a - wa := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = B (u - wu) a' / B a' a' := ⟨_, rfl⟩
    have hsub : Submodule.span ℂ (s : Set D) ≤ Submodule.span ℂ ((insert a s : Finset D) : Set D) :=
      Submodule.span_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    have hamem : a ∈ Submodule.span ℂ ((insert a s : Finset D) : Set D) :=
      Submodule.subset_span (by simp)
    refine ⟨wu + c • a', ?_, ?_⟩
    · rw [ha']
      exact Submodule.add_mem _ (hsub hwu) (Submodule.smul_mem _ _ (Submodule.sub_mem _ hamem (hsub hwa)))
    · have hexp : ∀ m, B (u - (wu + c • a')) m = B (u - wu) m - c * B a' m := by
        intro m
        rw [show u - (wu + c • a') = (u - wu) - c • a' by abel, map_sub, map_smul,
          LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      have hs : ∀ m ∈ Submodule.span ℂ (s : Set D), B (u - (wu + c • a')) m = 0 := by
        intro m hm
        rw [hexp, hwu' m hm, ha', hwa' m hm, mul_zero, sub_zero]
      have key : ∀ m ∈ ((insert a s : Finset D) : Set D), B (u - (wu + c • a')) m = 0 := by
        intro m hm
        rw [Finset.coe_insert, Set.mem_insert_iff] at hm
        rcases hm with hm | hm
        · have hsplit : m = a' + wa := by rw [hm, ha']; abel
          rw [hsplit, map_add, hs wa hwa, add_zero, hexp]
          by_cases h0 : B a' a' = 0
          · have h0' : a' = 0 := by
              by_contra hne
              have := hBp a' hne
              rw [h0] at this
              simp at this
            simp [h0']
          · rw [hc, div_mul_cancel₀ _ h0, sub_self]
        · exact hs m (Submodule.subset_span hm)
      intro m hm
      have hle : Submodule.span ℂ ((insert a s : Finset D) : Set D) ≤ LinearMap.ker (B (u - (wu + c • a'))) :=
        Submodule.span_le.2 (fun m hm => LinearMap.mem_ker.2 (key m hm))
      exact LinearMap.mem_ker.1 (hle hm)
end PositivityTheory.RgUd.Form.U.Asm
