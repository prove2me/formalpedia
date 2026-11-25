-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_ret_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:47:54.382034+00:00
-- url     : https://prove2.me/submissions/25b6b6e5-767a-4ad0-afbc-cd31cdcc7f20

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cd_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_X_cd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
local notation "JJ" => Formalism.REAL.Jm
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) (g0 : Matrix (Fin n) (Fin n) ℂ) :
    ContDiffOn ℝ ∞ (slmRet ε g0) (slmV ε g0) := by
  have hX : ContDiffOn ℝ ∞ (slmX ε g0) (slmV ε g0) := (slm_X_cd ε g0).mono fun g hg => hg.1
  have hM : ContDiffOn ℝ ∞ (fun g => 1 - slmX ε g0 g) (slmV ε g0) := contDiffOn_const.sub hX
  have hP : ContDiffOn ℝ ∞ (fun g => 1 + slmX ε g0 g) (slmV ε g0) := contDiffOn_const.add hX
  have hI := slm_cd_inv hM fun g hg => hg.2
  exact slm_cd_mul contDiffOn_const (slm_cd_mul hP hI)
end ReciprocityTheory.ChartRestriction.DS
