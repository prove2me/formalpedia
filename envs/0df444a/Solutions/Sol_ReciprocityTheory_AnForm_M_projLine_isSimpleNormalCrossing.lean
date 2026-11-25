-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_isSimpleNormalCrossing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:33:55.026257+00:00
-- url     : https://prove2.me/submissions/ba1c7016-45c3-43ae-8708-32d816d04479

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_U_infty
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_U_coe
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLineSection_infty
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLineSection_coe
import Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_const
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isCompatibleChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : IsSNC p1 fsPot projectiveLinePairSection ![1] ![{∞}] := by
  intro x
  induction x with
  | infty =>
    refine ⟨projectiveLineChartAtInfinity, projLine_isCompatibleChart 1, OnePoint.infty_ne_coe 0, fun y hy => by rw [fsPot_U_infty]; exact hy,
      fun _ => Option.some 0, ?_, ?_, fun _ => 1, holoOn_const _ 1, fun _ _ => one_ne_zero, ?_⟩
    · intro k k' i _ _
      exact Subsingleton.elim k k'
    · intro k
      obtain rfl : k = 0 := Subsingleton.elim _ _
      ext y
      constructor
      · rintro ⟨hy1, hy2⟩
        have hy : y = ∞ := hy1
        subst hy
        exact ⟨hy2, 0, rfl, rfl⟩
      · rintro ⟨hy1, i, _, hi⟩
        refine ⟨?_, hy1⟩
        induction y with
        | infty => exact Set.mem_singleton _
        | coe z =>
          have hz : z⁻¹ = 0 := hi
          exact absurd (show (z : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) by rw [inv_eq_zero.1 hz]) hy1
    · intro y _
      rw [projLineSection_infty, Fin.prod_univ_one]
      show crd1 y = 1 * crd1 y ^ 1
      ring
  | coe z =>
    refine ⟨projectiveLineChartAtZero, projLine_isCompatibleChart 0, ⟨z, rfl⟩, fun y hy => by rw [fsPot_U_coe]; exact hy,
      fun _ => Option.none, ?_, ?_, fun _ => 1, holoOn_const _ 1, fun _ _ => one_ne_zero, ?_⟩
    · intro k k' i hk _
      cases hk
    · intro k
      obtain rfl : k = 0 := Subsingleton.elim _ _
      ext y
      constructor
      · rintro ⟨hy1, ⟨w, rfl⟩⟩
        exact absurd (hy1 : (w : OnePoint ℂ) = ∞) (OnePoint.coe_ne_infty w)
      · rintro ⟨_, i, hi, _⟩
        cases hi
    · intro y _
      rw [projLineSection_coe, Fin.prod_univ_one]
      show (1 : ℂ) = 1 * 1
      ring
end ReciprocityTheory.AnForm.M
