-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_points_eq_conePoints_8ae422774d28
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:06:17.735169+00:00
-- url     : https://prove2.me/submissions/b9b81c95-8750-4002-8493-0bb32b872d36

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_DenseChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
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
open MvPolynomial NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]
theorem _root_.solution (P : ArithVariety n) (F : Type*) [CommRing F] :
    P.points F = conePoints P.ideal F := by
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
    | (intros; simp [conePoints]; done)
    | (intros; grind)
    | (intros; grind [conePoints])
    | (intros; unfold conePoints; grind)
    | (intros; simp only [conePoints] at * <;> grind)
    | (intros; simp_all [conePoints] <;> grind)
    | (intros; ext <;> grind [conePoints])
    | (intros; constructor <;> intro _ <;> grind [conePoints])
    | (intro x; cases x <;> grind [conePoints])
    | (intro x; induction x <;> simp_all [conePoints])
    | (intro x y; induction x <;> grind [conePoints])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [conePoints])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [conePoints])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_53_0"



end 
