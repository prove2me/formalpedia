-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalOrder_aeval_diag_eq_5d1249f546d0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:43.690954+00:00
-- url     : https://prove2.me/submissions/70cf5853-322f-4362-9b1a-3cf160d3d71a

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
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) {m : ℕ} {h : MRing (T.wwIdx ι ν κ)} (hh : IsMultiHomog h (T.wwDeg m 0)) :
    aeval (T.wwCoord x δ e φ a₀ a₀) h = aeval (T.wwCoord x δ e φ a₀ a₁) h := by
  rw [aeval_def, aeval_def]
  apply eval₂_congr
  intro p c hp hc
  rcases p with ⟨_ | _ | _ | _, i⟩
  · rfl
  · rfl
  · rfl
  · exfalso
    have hs := hh c (mem_support_iff.mpr hc) .line1
    simp only [T.wwDeg] at hs
    exact (Finsupp.mem_support_iff.mp hp) ((Finset.sum_eq_zero_iff.mp hs) i (Finset.mem_univ _))
end GroundTheory.Heights₂.Heights.Inter.DiagonalOrder
