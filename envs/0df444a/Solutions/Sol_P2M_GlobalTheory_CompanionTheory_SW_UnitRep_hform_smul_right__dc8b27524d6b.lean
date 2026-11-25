-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_UnitRep_hform_smul_right__dc8b27524d6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:29:46.881849+00:00
-- url     : https://prove2.me/submissions/57f99e2c-2c17-4b19-9779-094df5ef00e5

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitRep
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CompanionTheory.SW.UnitRep
theorem _root_.solution (σ : A →+* A) (J : Matrix n n A) (a : A) (x y : n → A) :
    hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.CompanionTheory.SW.UnitRep
