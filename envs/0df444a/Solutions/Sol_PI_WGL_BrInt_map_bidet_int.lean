-- Prove2me | solution 1 for PI.WGL.BrInt.map_bidet_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:55.336568+00:00
-- url     : https://prove2.me/submissions/0fe72e22-a793-438e-a16a-f41e3c390d14

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionBrInt
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace BrInt
open Formalism.REAL Formalism.GradedWeylDivisibility
section fock
variable {σ : Type}
end fock
private theorem map_initMinor {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    MvPolynomial.map φ (initMinor R I hs) = initMinor S I hs := by
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]
end BrInt
end PI.WGL
end
end

set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
open PI.WGL.BrInt
open Formalism.REAL Formalism.GradedWeylDivisibility
namespace PI.WGL.BrInt
theorem _root_.solution (R : Type) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    MvPolynomial.map (Int.castRingHom R) (bideterminant ℤ sz hsz I) = bideterminant R sz hsz I := by
  unfold bideterminant
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => map_initMinor _ (I k) (hsz k)
end PI.WGL.BrInt
