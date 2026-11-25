-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_adjoin_of_mem_blockFnField_0a47ea1c92ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:45.669971+00:00
-- url     : https://prove2.me/submissions/57483eb5-3cf6-4f1a-9a62-99f3111344cd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.CurveAffineCharts
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.CurveAffineCharts
theorem _root_.solution [NumberField K'] (t : T) (ht : y ⟨(), t⟩ ≠ 0) {x : K'}
    (hx : x ∈ blockFnField y) :
    x ∈ Algebra.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) := by
  rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)]
  have hle : blockFnField y ≤
      IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, -, rfl⟩
    have hp : y p / y ⟨(), t⟩ ∈
        IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) :=
      IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨(), t⟩ ∈
        IntermediateField.adjoin ℚ (Set.range fun p : Σ _ : Unit, T => y p / y ⟨p.1, t⟩) :=
      IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    rw [← div_div_div_cancel_right₀ ht]
    exact div_mem hp hq
  exact hle hx
end GroundTheory.Heights₂.Heights.CurveAffineCharts
