-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multiConeMap_eq_f5c45a24f8f1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:43.774741+00:00
-- url     : https://prove2.me/submissions/7c66f58c-58e8-4116-9ee6-4078e7aebd13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOrdOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
omit [Fintype ι] [Fintype ν] [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (b : Fin 2 → Φ) :
    T.multiConeMap (T.wwCoord x δ e φ (b 0) (b 1)) =
      (MvPolynomial.map (aeval b : MvPolynomial (Fin 2) Ω →ₐ[Ω] Φ).toRingHom).comp (polyConeMap x δ e φ) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
  · simp [T.multiConeMap, polyConeMap]
  · rcases p with ⟨_ | _ | _ | _, i⟩ <;>
      simp [T.multiConeMap, polyConeMap, polyCoord, T.wwCoord, T.lineVal, mul_comm]
end GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
