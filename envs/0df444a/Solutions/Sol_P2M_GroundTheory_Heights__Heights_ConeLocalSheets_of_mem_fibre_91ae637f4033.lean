-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_of_mem_fibre_91ae637f4033
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:01.640412+00:00
-- url     : https://prove2.me/submissions/e765cf3b-cc20-4c26-97a0-675fb7b96f0f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_mat_mulVec_b5e90605ff3e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_mem_zeroSet_chartIdeal_0963b45b1ca9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_eq_cons_b295b14b7ef8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_tailMat_mulVec_c4c1d9585b97

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
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ} {z : Fin n → ℂ}
    (hz : z ∈ ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y) :
    lift z ∈ mcPts P ∧ Ψ (segre (lift z)) = Fin.cons 1 y := by
  obtain ⟨hZ, hA⟩ := hz
  obtain ⟨hP, h0⟩ := mem_zeroSet_chartIdeal.mp hZ
  refine ⟨⟨fun k => ?_, hP⟩, eq_cons h0 fun i => by rw [← tailMat_mulVec, hA]⟩
  by_contra hne
  push Not at hne
  have hz0 : z = 0 := funext fun i => hne i
  rw [hz0, ← mat_mulVec, Matrix.mulVec_zero] at h0
  exact zero_ne_one h0
end GroundTheory.Heights₂.Heights.ConeLocalSheets
