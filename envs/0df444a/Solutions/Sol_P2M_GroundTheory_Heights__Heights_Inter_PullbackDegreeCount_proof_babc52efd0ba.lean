-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_proof_babc52efd0ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:58:39.835206+00:00
-- url     : https://prove2.me/submissions/0a1bcea1-3c78-4fac-8d70-f5dd89ed93bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOver
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NormSegreSameOrbit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_ncard_pullW_eq_558ce03dd39e
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
open PullbackDegreeCount
namespace GroundTheory.Heights₂.Heights.Inter
namespace PullbackDegreeCount
theorem _root_.solution (hDim : FibreDimStatement) (hRank : ChartRankAdjoin.Statement)
    (hCount : GenericPointsCount.Statement) (hB : PullbackVanishingOfNullCycle.Statement) (hBad : pullbackBadImage_holds.Statement) :
    PullbackDegreeCount.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n G J R Ψ hv hP' hP hJ hΨ
  classical
  have hfib : IsProjVarF (fibreIdeal κ G) 0 := hDim K ι K' ι' κ v P' (n + 1) 0 G hv hP' hP
  choose i hi using hfib.1.2.2
  have hz : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0 := by
    intro k h0
    apply hi k
    rw [fibreIdeal, RingHom.mem_ker, aeval_X]
    exact h0
  have he : J (fibreIdeal κ G) 0 Fin.elim0 = (Module.finrank G.Φ (IntermediateField.adjoin G.Φ
      (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩)) : ℤ) := by
    rw [hJ.1 _ Fin.elim0 i hfib hi]
    exact congrArg _ (hRank (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) i hz hfib.1.2.1)
  have hN := measure_union_null (hB K ι K' ι' κ v P' J' n Ψ hv hP' hP hΨ R.homog R.nondeg)
    (hBad K ι K' ι' κ v P' J' n R Ψ hv hP' hP hΨ)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN, hCount K ι K' ι' κ v P' n G i Ψ hv hP' hP hΨ hz]
    with y hy hc
  intro w hw
  obtain ⟨-, -, -, hΨw⟩ := id hw
  have hset : ({x | pullQ R v Ψ x = y ∧ pullW R v Ψ x = w} \ pullBad R v Ψ) = {x | pullW R v Ψ x = w} := by
    ext x
    refine ⟨fun h => h.1.2, fun hx => ?_⟩
    have hx' : pullW R v Ψ x = w := hx
    have h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0 := by
      intro h0
      have h1 := congrFun hΨw 0
      rw [← hx', pullW, h0, inv_zero, zero_smul, map_zero] at h1
      simp at h1
    have hq : pullQ R v Ψ x = y := by
      funext m
      have h1 := congrFun hΨw m.succ
      rw [← hx', pullW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at h1
      rw [pullQ, ← h1, div_eq_inv_mul]
    exact ⟨⟨hq, hx'⟩, fun hbad => hy (Or.inr ⟨x, ⟨hbad, h0⟩, hq⟩)⟩
  rw [hset, ncard_pullW_eq hv R Ψ w fun z' hz' hJ' hzw => hy (Or.inl ⟨z', hz', hJ', hzw ▸ hw⟩), hc w hw, he]
end PullbackDegreeCount
end GroundTheory.Heights₂.Heights.Inter
