-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_aeval_scale_d6b95e793f4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:38.833875+00:00
-- url     : https://prove2.me/submissions/11a1b7d8-82ce-42aa-b798-1e8b576ea3d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_multiConeMap_of_homog_3655d6d60990


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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
theorem _root_.solution (u : K → Φ) (c : (Σ k, ι k) → Φ) (s : MRing ι) (β : K → ℕ) (hs : IsMultiHomog s β) :
    aeval (fun p => u p.1 * c p) s = (∏ k, u k ^ β k) * aeval c s := by
  have h1 := congrArg (MvPolynomial.eval u) (DiagRAux.multiConeMap_of_homog c s β hs)
  have h2 : (MvPolynomial.eval u).comp (T.multiConeMap c) =
      (aeval (fun p => u p.1 * c p) : MRing ι →ₐ[ℤ] Φ).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp [T.multiConeMap]) (fun p => by simp [T.multiConeMap, mul_comm])
  rw [← RingHom.comp_apply, h2, map_mul, eval_C, map_prod] at h1
  simp only [map_pow, eval_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
  rw [h1, mul_comm]
end GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
