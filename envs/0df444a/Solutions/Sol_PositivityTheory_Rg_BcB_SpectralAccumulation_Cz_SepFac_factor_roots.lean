-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.factor_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:10.766115+00:00
-- url     : https://prove2.me/submissions/2280b2ac-bd9c-45a4-af91-3b516c036bd4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFac
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PSepFacB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
variable {B : Type} [CommRing B] [Algebra ℂ B]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
theorem _root_.solution (e : B) (P : B[X]) (J : Finset ℂ) (h : ∀ α ∈ J, e * P.eval (algebraMap ℂ B α) = 0) :
    ∃ Rm : B[X], C e * P = (∏ α ∈ J, (X - C (algebraMap ℂ B α))) * Rm := by
  classical
  induction J using Finset.induction_on with
  | empty => exact ⟨C e * P, by simp⟩
  | insert β J hβ ih =>
    obtain ⟨Rm, hRm⟩ := ih fun α hα => h α (Finset.mem_insert_of_mem hα)
    have hu : IsUnit (∏ α ∈ J, (algebraMap ℂ B β - algebraMap ℂ B α)) := by
      have e0 : ∏ α ∈ J, (algebraMap ℂ B β - algebraMap ℂ B α) = algebraMap ℂ B (∏ α ∈ J, (β - α)) := by
        simp [map_prod, map_sub]
      rw [e0]
      refine (IsUnit.mk0 _ ?_).map (algebraMap ℂ B)
      exact Finset.prod_ne_zero_iff.2 fun α hα => sub_ne_zero.2 fun h' => hβ (h' ▸ hα)
    have h0 : Rm.eval (algebraMap ℂ B β) = 0 := by
      have e1 := congrArg (eval (algebraMap ℂ B β)) hRm
      rw [eval_mul, eval_C, h β (Finset.mem_insert_self _ _), eval_mul, eval_prod] at e1
      simp only [eval_sub, eval_X, eval_C] at e1
      exact hu.mul_right_eq_zero.1 e1.symm
    refine ⟨Rm /ₘ (X - C (algebraMap ℂ B β)), ?_⟩
    rw [hRm, Finset.prod_insert hβ]
    conv_lhs => rw [← (mul_divByMonic_eq_iff_isRoot).2 h0]
    ring
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
