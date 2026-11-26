-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradientAtPoint_eval_linPart_0d7a1dbc4716
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:08:11.348794+00:00
-- url     : https://prove2.me/submissions/7ea64bf8-fa69-41aa-8e14-c4b3d5d46686

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.GradientAtPoint
variable {σ : Type*} (w : σ → ℂ)
theorem _root_.solution [Fintype σ] (c : σ → ℂ) : eval w (linPart w c) = 0 := by
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
    | (intros; simp [linPart]; done)
    | (intros; grind)
    | (intros; grind [linPart])
    | (intros; unfold linPart; grind)
    | (intros; simp only [linPart] at * <;> grind)
    | (intros; simp_all [linPart] <;> grind)
    | (intros; ext <;> grind [linPart])
    | (intros; constructor <;> intro _ <;> grind [linPart])
    | (intro x; cases x <;> grind [linPart])
    | (intro x; induction x <;> simp_all [linPart])
    | (intro x y; induction x <;> grind [linPart])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [linPart])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [linPart])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_8_1"



end 
