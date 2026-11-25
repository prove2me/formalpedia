-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_QuasiRefl_hform_smul_right__8972bbbb794c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:29:42.190735+00:00
-- url     : https://prove2.me/submissions/45fd4711-ff93-4a36-8edd-ea3efb18325f

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermConstantsEqAlongAffineSpaceSquare

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuasiRefl
open HeckeCharacterZeroLocus.SiegelWeilU
variable {A : Type} [CommRing A] {n : Type} [Fintype n] {σ : A →+* A} {J : Matrix n n A}
namespace GlobalTheory.CompanionTheory.SW.QuasiRefl
theorem _root_.solution (d y : n → A) (c : A) :
    hform σ J y (c • d) = c * hform σ J y d := by
  simp [hform, Finset.mul_sum, mul_left_comm]
end GlobalTheory.CompanionTheory.SW.QuasiRefl
