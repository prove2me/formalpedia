-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionNorm_proof_feadc2837ee9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:58.36042+00:00
-- url     : https://prove2.me/submissions/6de25e7d-c3f5-428f-9d80-81c730b9794d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionNorm_evalCone_liftOld_79e2f292e4c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionNorm_chartMonomial_ne_zero_33456487209d

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace SectionNorm
theorem _root_.solution (hP : ConePoints.Statement) (hM : ChartMetric.Statement) :
    SectionNorm.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG c j _ w hw hgz
  obtain ⟨hz, la, hla, hform⟩ := (hP ι n P D d g hg).2 w hw
  have hm := SectionNorm.chartMonomial_ne_zero D hg hz c j hgz
  have hmet := (hM ι n P D N hN d g hg r G δ hG).2 w hw c la hm (hform c hm)
  have hNpos : 0 < N.metric (D.basePart₂ w) := N.metric_pos _ hz.1
  have heval : evalCone w (X (D.newCoord j) * D.liftOld (chartMonomial c d)) =
      D.newPart w j * evalCone (D.basePart₂ w) (chartMonomial c d) := by
    rw [show evalCone w (X (D.newCoord j) * D.liftOld (chartMonomial c d)) =
        evalCone w (X (D.newCoord j)) * evalCone w (D.liftOld (chartMonomial c d)) by
      simp [evalCone, eval₂_mul], SectionNorm.evalCone_liftOld]
    simp [evalCone, eval₂_X, AddBlockData.newCoord, AddBlockData.newPart]
  rw [heval, SectionNorm.evalCone_liftOld, hmet, hform c hm j, div_mul_cancel₀ _ hm,
    mul_div_assoc, div_self hNpos.ne', mul_one, norm_mul]
  have h1 : ‖la‖ ≠ 0 := norm_ne_zero_iff.mpr hla
  have h2 : ‖evalCone (D.basePart₂ w) (g c j)‖ ≠ 0 := norm_ne_zero_iff.mpr hgz
  field_simp
end SectionNorm
end GroundTheory.Heights₂.Heights
