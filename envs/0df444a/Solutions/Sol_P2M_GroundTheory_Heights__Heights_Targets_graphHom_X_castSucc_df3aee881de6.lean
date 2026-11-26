-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_graphHom_X_castSucc_df3aee881de6
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:08:09.749917+00:00
-- url     : https://prove2.me/submissions/228fa5e1-a78e-4844-89a6-5510f08424ce

import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_GraphIdeal
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
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
variable {n : ℕ}
theorem _root_.solution (p : MvPolynomial (Fin n) ℂ) (i : Fin n) :
    graphHom p (X (Fin.castSucc i)) = X i := by
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
    | (intros; simp [graphHom]; done)
    | (intros; grind)
    | (intros; grind [graphHom])
    | (intros; unfold graphHom; grind)
    | (intros; simp only [graphHom] at * <;> grind)
    | (intros; simp_all [graphHom] <;> grind)
    | (intros; ext <;> grind [graphHom])
    | (intros; constructor <;> intro _ <;> grind [graphHom])
    | (intro x; cases x <;> grind [graphHom])
    | (intro x; induction x <;> simp_all [graphHom])
    | (intro x y; induction x <;> grind [graphHom])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [graphHom])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [graphHom])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_4_2"



end 
