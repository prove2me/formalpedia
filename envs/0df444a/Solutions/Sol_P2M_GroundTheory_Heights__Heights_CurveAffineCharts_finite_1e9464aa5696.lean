-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finite_1e9464aa5696
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:02.930977+00:00
-- url     : https://prove2.me/submissions/b8481d15-0ded-4d82-ae53-53e8d6e2e4b1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_mem_integralClosure_of_mem_curveRing_b6c172556c3d

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
namespace GroundTheory.Heights₂.Heights.CurveAffineCharts
theorem _root_.solution [NumberField K'] (hy : IsArithVar (mCoordIdeal y) 1) : Module.Finite ℤ (curveRing y) := by
  have : Module.Finite ℤ (integralClosure ℤ K') := inferInstanceAs (Module.Finite ℤ (𝓞 K'))
  let f : curveRing y →ₗ[ℤ] integralClosure ℤ K' :=
    { toFun := fun b => ⟨b, mem_integralClosure_of_mem_curveRing y hy b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun a b h => Subtype.ext (congrArg (fun z : integralClosure ℤ K' => (z : K')) h)
end GroundTheory.Heights₂.Heights.CurveAffineCharts
