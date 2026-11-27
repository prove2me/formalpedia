-- Prove2me | solution 2 for UpperTheory.V.Hi.Frame.ra_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:35:22.03034+00:00
-- url     : https://prove2.me/submissions/1c464f2d-1959-4004-9918-0a70597ba683

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FixedSubgroup
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_ContinuousTorusCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing Matrix
open UpperTheory UpperTheory.V UpperTheory.V.Hi
attribute [instance] IsCNL.complete IsCNL.finite
open UpperTheory.V.Hi.Frame
variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp)
variable {A : Type} [CommRing A] {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ)
namespace UpperTheory.V.Hi.Frame
theorem _root_.solution (u : X.Ub) (f : X.Fn A m) (g : Ga × Gp) :
    X.ra τ u f g = (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * ((u : Ga), 1)) := rfl
end UpperTheory.V.Hi.Frame
