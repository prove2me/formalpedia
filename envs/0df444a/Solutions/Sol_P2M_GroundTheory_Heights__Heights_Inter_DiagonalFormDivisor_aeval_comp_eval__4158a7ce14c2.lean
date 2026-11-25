-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_aeval_comp_eval__4158a7ce14c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:36.216071+00:00
-- url     : https://prove2.me/submissions/3c3d2852-88bc-4798-8d9d-cdaa27c9a541

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv

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
open GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
set_option linter.unusedSectionVars false
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
  [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
theorem _root_.solution {σ n R : Type} [CommRing R] (f : R →+* Φ) (w : n → Φ) (g : σ → MvPolynomial n R)
    (s : MvPolynomial σ ℤ) : aeval (fun p => eval₂ f w (g p)) s = eval₂ f w (aeval g s) := by
  have h : (eval₂Hom f w).comp (aeval g : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial n R).toRingHom =
      (aeval (fun p => eval₂ f w (g p)) : MvPolynomial σ ℤ →ₐ[ℤ] Φ).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun p => by simp)
  exact (RingHom.congr_fun h s).symm
end GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
