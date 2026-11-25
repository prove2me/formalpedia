-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_constantCoeff_eq_zero_of_isHomogIdeal_ccff6c17f035
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:26:05.128257+00:00
-- url     : https://prove2.me/submissions/d5c0f2c8-f009-4025-94ba-4ae57ca8314e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PConeDimOfChowForm

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsHomogIdeal P) (htop : P ≠ ⊤)
    {g : MvPolynomial (Fin n) F} (hg : g ∈ P) : constantCoeff g = 0 := by
  by_contra h
  have h0 := hP g hg 0
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h0
  exact htop (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))
end GroundTheory.Heights₂.Heights
