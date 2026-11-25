-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.finrank_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:58.66606+00:00
-- url     : https://prove2.me/submissions/f3f0879c-e4b4-4ef3-9c94-2f44c59560e0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.JLatOf
open PositivityTheory.Rg.Rs
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.Rg.Rs.JLatOf
theorem _root_.solution (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    finrank k (gmap g M) = finrank k M := by
  have hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin N) (Fin N) k)) := by
    intro x y hxy
    have h2 := congrArg (fun v => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ v) hxy
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h2
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj M)).symm
end PositivityTheory.Rg.Rs.JLatOf
