-- Prove2me | solution 1 for P2M_UpperTheory_V_Alg_WPres_origin___2faba994ee10
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:55.674576+00:00
-- url     : https://prove2.me/submissions/45f283c6-8743-4fb9-b8f9-9b00b804ce28

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebra_ResMapBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open UpperTheory UpperTheory.V UpperTheory.V.Alg
attribute [instance] IsCO.complete IsCO.isLocalHom
attribute [instance] WPres.fin
open UpperTheory.V.Alg.WPres
variable {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
namespace UpperTheory.V.Alg.WPres
theorem _root_.solution (h : W.HasOrigin) (f : MvPowerSeries W.σ O) : W.origin h (W.π f) = constantCoeff f := by
  have : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π f) = Ideal.Quotient.mk _ f := by
    rw [AlgEquiv.symm_apply_eq]; rfl
  simp only [origin, AlgHom.comp_apply, AlgEquiv.coe_algHom]
  erw [this]
  rfl
end UpperTheory.V.Alg.WPres
