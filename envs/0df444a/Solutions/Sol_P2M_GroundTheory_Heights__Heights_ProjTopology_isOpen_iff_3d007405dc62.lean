-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjTopology_isOpen_iff_3d007405dc62
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:08:10.571803+00:00
-- url     : https://prove2.me/submissions/6ef8f8b6-3cff-4949-84d8-f5c054f3797b

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ProjTopology
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
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
open GroundTheory.Heights₂.Heights.ProjTopology
theorem _root_.solution {s : Set (ℙ K V)} :
    IsOpen s ↔ IsOpen ((Projectivization.mk' K) ⁻¹' s : Set {v : V // v ≠ 0}) := by
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
  trace "HIT_5_1"



