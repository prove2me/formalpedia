-- Prove2me | solution 1 for UpperTheory.V.Alg.coeff_wcomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:02:30.963549+00:00
-- url     : https://prove2.me/submissions/af4c5c23-4e41-494d-9bb4-7db631cc30f3

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
variable (O : Type) [CommRing O] {σ X : Type} [AddCommGroup X] (wt : σ → X)
open Classical
namespace UpperTheory.V.Alg
theorem _root_.solution (j : X) (f : MvPowerSeries σ O) (n : σ →₀ ℕ) :
    coeff n (wcomp O wt j f) = if Finsupp.weight wt n = j then coeff n f else 0 := rfl
end UpperTheory.V.Alg
