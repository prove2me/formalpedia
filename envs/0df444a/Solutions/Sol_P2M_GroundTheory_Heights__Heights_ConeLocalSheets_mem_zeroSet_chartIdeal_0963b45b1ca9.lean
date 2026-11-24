-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_mem_zeroSet_chartIdeal_0963b45b1ca9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:38.904618+00:00
-- url     : https://prove2.me/submissions/5caf0d3e-c769-40ad-8f87-b8678308851a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_mat_mulVec_b5e90605ff3e

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
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {z : Fin n → ℂ} :
    z ∈ ComplexSets.zeroSet (chartIdeal P Ψ) ↔
      (∀ f ∈ P, eval (lift z) (map (Int.castRingHom ℂ) f) = 0) ∧ Ψ (segre (lift z)) 0 = 1 := by
  have key : ∀ J : Ideal (MvPolynomial (Fin n) ℂ),
      z ∈ ComplexSets.zeroSet J ↔ J ≤ RingHom.ker (eval z) := fun J => by
    simp [ComplexSets.zeroSet, SetLike.le_def, RingHom.mem_ker]
  rw [key, chartIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff,
    ← mat_mulVec]
  refine and_congr ?_ ?_
  · simp only [SetLike.le_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename]
    rfl
  · simp [RingHom.mem_ker, Matrix.mulVec, dotProduct, sub_eq_zero]
end GroundTheory.Heights₂.Heights.ConeLocalSheets
