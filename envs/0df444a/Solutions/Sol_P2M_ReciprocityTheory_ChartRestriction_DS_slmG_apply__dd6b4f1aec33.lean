-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_slmG_apply__dd6b4f1aec33
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:08:49.159644+00:00
-- url     : https://prove2.me/submissions/53467461-ea98-44f9-a8d9-f049eec39a13

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_ContDiffOnZeroOfContinuousOn
import Mathlib.Tactic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
theorem _root_.solution (C : ι → Y →L[ℝ] ℝ) (fd : X →L[ℝ] Y) (w : ι → E) (W : X) (κ : ι → ℝ)
    (hκ : ∀ i, C i (fd W) = κ i) : slmG C fd w W = ∑ i, κ i • w i := by
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
    | (intros; simp [slmG]; done)
    | (intros; grind)
    | (intros; grind [slmG])
    | (intros; unfold slmG; grind)
    | (intros; simp only [slmG] at * <;> grind)
    | (intros; simp_all [slmG] <;> grind)
    | (intros; ext <;> grind [slmG])
    | (intros; constructor <;> intro _ <;> grind [slmG])
    | (intro x; cases x <;> grind [slmG])
    | (intro x; induction x <;> simp_all [slmG])
    | (intro x y; induction x <;> grind [slmG])
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> intros <;> grind [slmG])
    | (intros; refine ⟨?_, ?_⟩ <;> intros <;> grind [slmG])
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_1_0"



end 
