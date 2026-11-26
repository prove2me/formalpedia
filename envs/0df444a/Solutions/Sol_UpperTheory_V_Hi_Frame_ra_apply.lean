-- Prove2me | solution 1 for UpperTheory.V.Hi.Frame.ra_apply
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:40:25.627346+00:00
-- url     : https://prove2.me/submissions/ee02f5bc-edc0-46e0-b81a-24d2efa1a617

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_ContinuousTorusCharacter
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FixedSubgroup
import Mathlib



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
theorem _root_.solution (u : X.Ub) (f : X.Fn A m) (g : Ga × Gp) :
    X.ra τ u f g = (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * ((u : Ga), 1)) := by
  first
    | (intros; rfl)
    | exact Iff.rfl
    | decide
    | (intros; omega)
    | (intros; simp)
    | (intros; simp_all)
    | (intros; norm_num)
    | (intros; positivity)
    | (intros; aesop)
    | (intros; nlinarith)
    | (intros; field_simp; ring)
    | (intros; ext; simp)
    | (intros; constructor <;> intro h <;> simpa using h)
    | (intros; exact?)
  trace "HIT_36_0"

end 
