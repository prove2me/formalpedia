-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_whole_c3c64e80bbe7
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:06:17.000768+00:00
-- url     : https://prove2.me/submissions/fabf65bd-bde1-4fed-98dc-1ba88b18ec29

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
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
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.ArithVariety
omit [Fintype ι]
theorem _root_.solution {F : Type*} [CommRing F] {z : Cone n F} (hz : BlockNonzero z) :
    z ∈ (whole n).points F := by
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
    | (intros; simp [Cone, BlockNonzero, points, whole]; done)
    | (intros; grind)
    | (intros; grind [Cone, BlockNonzero, points, whole])
    | (intros; unfold Cone BlockNonzero points whole; grind)
    | (intros; simp only [Cone, BlockNonzero, points, whole] at * <;> grind)
    | (intros; simp_all [Cone, BlockNonzero, points, whole] <;> grind)
    | (intros; ext <;> grind [Cone, BlockNonzero, points, whole])
    | (intros; constructor <;> intro _ <;> grind [Cone, BlockNonzero, points, whole])
    | (intro x; cases x <;> grind [Cone, BlockNonzero, points, whole])
    | (intro x; induction x <;> simp_all [Cone, BlockNonzero, points, whole])
    | (intro x y; induction x <;> grind [Cone, BlockNonzero, points, whole])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [Cone, BlockNonzero, points, whole])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [Cone, BlockNonzero, points, whole])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_50_0"



end 
