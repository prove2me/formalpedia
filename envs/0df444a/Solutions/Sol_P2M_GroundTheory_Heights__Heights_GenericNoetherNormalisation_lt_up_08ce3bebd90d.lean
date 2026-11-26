-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_lt_up_08ce3bebd90d
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:08:09.203515+00:00
-- url     : https://prove2.me/submissions/dba12109-f86b-443b-b401-46aece5493ca

import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProofSimp
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Mathlib
import Mathlib.Tactic





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
open Polynomial MvPolynomial Ideal Nat RingHom List
open GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) A)
variable (v w : Fin (n + 1) →₀ ℕ)
local notation3 "up" => 2 + f.totalDegree
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1
omit [IsDomain A]
variable {f v}
theorem _root_.solution (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  first
    | (intros; rfl)
    | (intros; ext; rfl)
    | (intros; exact LinearMap.ext fun _ => rfl)
    | (intros; apply Subtype.ext; rfl)
    | (intros; infer_instance)
    | (refine ⟨?_, ?_⟩ <;> infer_instance)
    | (intros; ext; simp; done)
    | (intros; assumption)
    | (intros; omega)
    | (intros; simp []; done)
    | (intros; grind)
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_2_1"



