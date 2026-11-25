-- Prove2me | solution 1 for P2M_GlobalTheory_DetPowPairing_coeff_pderiv__dbf7971f6bc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:31.360063+00:00
-- url     : https://prove2.me/submissions/3eaa65ce-6737-4ca1-974f-b237e0a77346

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.DetPowPairing
open MvPolynomial
variable {σ : Type} {C : Type} [CommRing C]
namespace GlobalTheory.DetPowPairing
theorem _root_.solution (j : σ) (A : σ →₀ ℕ) (Q : MvPolynomial σ C) :
    coeff A (pderiv j Q) = coeff (A + Finsupp.single j 1) Q * ((A j : C) + 1) :=
  coeff_pderiv Q A
end GlobalTheory.DetPowPairing
