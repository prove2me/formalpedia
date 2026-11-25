-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.ktint_inK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:59.794941+00:00
-- url     : https://prove2.me/submissions/f1026e26-3d23-40f6-99fa-ac7a40914579

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KtintExpApplyOfEig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (a : Fin n) :
    inK ε (Complex.I • Matrix.single a a (1 : ℂ)) := by
  have hc : Commute (Complex.I • Matrix.single a a (1 : ℂ)) (Jm ε) := by
    apply Commute.smul_left
    ext i j
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    by_cases h : a = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp [h]
  refine ⟨?_, hc.eq⟩
  unfold inG
  have hs : (Complex.I • Matrix.single a a (1 : ℂ))ᴴ = -(Complex.I • Matrix.single a a (1 : ℂ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_single, star_one, Complex.star_def,
      Complex.conj_I, neg_smul]
  rw [hs, Matrix.neg_mul, hc.eq, neg_add_cancel]
end ReciprocityTheory.ChartRestriction.DS.HW
