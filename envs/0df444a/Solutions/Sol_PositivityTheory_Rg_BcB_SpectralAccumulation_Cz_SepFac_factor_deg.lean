-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac.factor_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:29:07.991617+00:00
-- url     : https://prove2.me/submissions/582cd081-12b9-493a-969d-986fd5b269de

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
omit [Algebra ℂ B]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
theorem _root_.solution {e : B} {P Pi Rm : B[X]} (hP : P.Monic) (hPi : Pi.Monic) (h : C e * P = Pi * Rm) :
    (Pi.natDegree ≤ P.natDegree ∨ e = 0) ∧ (Pi.natDegree = P.natDegree → ∀ k, e * P.coeff k = Pi.coeff k * e) := by
  by_cases hR : Rm = 0
  · have h0 : C e * P = 0 := by rw [h, hR, mul_zero]
    have he : e = 0 := by
      have := congrArg (fun F : B[X] => F.coeff P.natDegree) h0
      simpa [coeff_C_mul, hP.coeff_natDegree] using this
    exact ⟨Or.inr he, fun _ k => by simp [he]⟩
  · have hdeg : (Pi * Rm).natDegree = Pi.natDegree + Rm.natDegree := hPi.natDegree_mul' hR
    have hle : (C e * P).natDegree ≤ P.natDegree := natDegree_C_mul_le e P
    rw [h, hdeg] at hle
    refine ⟨Or.inl (by omega), fun hm k => ?_⟩
    have hRC : Rm = C (Rm.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
    have h2 : C e * P = Pi * C (Rm.coeff 0) := by
      rw [h]
      conv_lhs => rw [hRC]
    have hb : e = Rm.coeff 0 := by
      have := congrArg (fun F : B[X] => F.coeff P.natDegree) h2
      simp only [coeff_C_mul, coeff_mul_C, hP.coeff_natDegree, mul_one] at this
      rw [this, ← hm, hPi.coeff_natDegree, one_mul]
    have := congrArg (fun F : B[X] => F.coeff k) h2
    simp only [coeff_C_mul, coeff_mul_C] at this
    rw [this, ← hb]
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.SepFac
