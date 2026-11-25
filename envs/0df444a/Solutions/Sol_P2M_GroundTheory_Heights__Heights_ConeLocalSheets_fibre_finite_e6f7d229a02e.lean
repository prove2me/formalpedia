-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_fibre_finite_e6f7d229a02e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:28.21691+00:00
-- url     : https://prove2.me/submissions/8318b25c-5be5-49d0-8315-8ad73422e290

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_segre_lift_bc08ad365c4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_of_mem_fibre_91ae637f4033
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix
open GroundTheory.Heights₂.Heights.ConeLocalSheets
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ConeLocalSheets
theorem _root_.solution {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hP : IsArithVar P (e + 1))
    (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y).Finite := by
  have hinj : Function.Injective fun z : Fin n → ℂ => segre (lift z) := by
    intro a b h
    funext i
    simpa [segre_lift] using congrFun h (fun _ => i)
  refine ((ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite Unit (PBlk n) P e Ψ hP hΨ y).preimage hinj.injOn).subset ?_
  intro z hz
  have h := of_mem_fibre hz
  exact ⟨lift z, h.1, rfl, h.2⟩
end GroundTheory.Heights₂.Heights.ConeLocalSheets
