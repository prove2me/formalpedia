-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_coordRing_eq_cd809ea45753
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:01:05.133247+00:00
-- url     : https://prove2.me/submissions/51df9d7f-3ccc-4b6b-b68a-07b0b3a9be87

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω]
variable {N : ℕ} (x : Fin (N + 1) → Ω)
theorem _root_.solution : coordRing (S := S) x = (cone (S := S) x).range := by
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
    | (intros; simp [cone, coordRing]; done)
    | (intros; grind)
    | (intros; grind [cone, coordRing])
    | (intros; unfold cone coordRing; grind)
    | (intros; simp only [cone, coordRing] at * <;> grind)
    | (intros; simp_all [cone, coordRing] <;> grind)
    | (intros; ext <;> grind [cone, coordRing])
    | (intros; constructor <;> intro _ <;> grind [cone, coordRing])
    | (intro x; cases x <;> grind [cone, coordRing])
    | (intro x; induction x <;> simp_all [cone, coordRing])
    | (intro x y; induction x <;> grind [cone, coordRing])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [cone, coordRing])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [cone, coordRing])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_23_2"



end 
