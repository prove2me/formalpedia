-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_gaussNormOf_eq_b0903c48cd28
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:45.013025+00:00
-- url     : https://prove2.me/submissions/aaab8e39-ac17-4174-aba0-4961b2ead9b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_def_6cd6aa89eff0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {f : MvPolynomial ι R} (hf : f ≠ 0) :
    ∃ m ∈ f.support, gaussNormOf w f = w (f.coeff m) := by
  obtain ⟨m, hm, h⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
    (fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal))
  refine ⟨m, hm, ?_⟩
  rw [gaussNormOf_def]
  exact congrArg Subtype.val h
end GroundTheory.Heights₂.Heights
