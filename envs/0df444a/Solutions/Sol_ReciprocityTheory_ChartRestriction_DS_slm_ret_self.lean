-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.slm_ret_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:34:21.317847+00:00
-- url     : https://prove2.me/submissions/b0a019c8-ec7a-4314-9da7-f121d75b720f

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CayleyChartDomainIsOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_inUJ_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_mul_Ji
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_Ji_inUJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_skewAdjointPart_eq_self_of_isSkewAdjoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_Y_inG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slm_cay_left

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
theorem _root_.solution {g0 : Matrix (Fin n) (Fin n) ℂ} (hg0 : Formalism.REAL.inUJ ε g0) :
    ∀ g ∈ slmV ε g0, Formalism.REAL.inUJ ε g → slmRet ε g0 g = g := by
  intro g hg hgU
  have hh : Formalism.REAL.inUJ ε (slmJi ε g0 * g) := slm_inUJ_mul (slm_Ji_inUJ hg0) hgU
  have hd : (slmJi ε g0 * g + 1).det ≠ 0 := hg.1
  have hXY : slmX ε g0 g = (slmJi ε g0 * g - 1) * (slmJi ε g0 * g + 1)⁻¹ :=
    skewAdjointPart_eq_self_of_isSkewAdjoint (slm_Y_inG hh hd)
  have hd2 : (1 - slmX ε g0 g).det ≠ 0 := hg.2
  rw [hXY] at hd2
  show g0 * ((1 + slmX ε g0 g) * (1 - slmX ε g0 g)⁻¹) = g
  rw [hXY, slm_cay_left hd hd2, ← Matrix.mul_assoc, slm_mul_Ji hg0, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.DS
