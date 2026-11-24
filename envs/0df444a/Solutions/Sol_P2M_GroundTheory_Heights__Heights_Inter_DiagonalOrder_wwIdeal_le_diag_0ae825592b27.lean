-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_wwIdeal_le_diag_0ae825592b27
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:03.289734+00:00
-- url     : https://prove2.me/submissions/d88ff0d0-3b01-4032-a132-4a33f077214a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOrdOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOrd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_multiConeMap_eq_f5c45a24f8f1

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
    (a : Fin 2 → Φ) (ha : AlgebraicIndependent Ω a) :
    T.wwIdeal x δ e φ (a 0) (a 1) ≤ T.wwIdeal x δ e φ (a 0) (a 0) := by
  intro s hs
  rw [T.wwIdeal, RingHom.mem_ker, multiConeMap_eq x δ e φ a, RingHom.comp_apply] at hs
  have hinj : Function.Injective (aeval a : MvPolynomial (Fin 2) Ω →ₐ[Ω] Φ).toRingHom :=
    algebraicIndependent_iff_injective_aeval.mp ha
  have hz : polyConeMap x δ e φ s = 0 := MvPolynomial.map_injective _ hinj (hs.trans (map_zero _).symm)
  rw [T.wwIdeal, RingHom.mem_ker, multiConeMap_eq x δ e φ (fun _ => a 0), RingHom.comp_apply, hz, map_zero]
end GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
