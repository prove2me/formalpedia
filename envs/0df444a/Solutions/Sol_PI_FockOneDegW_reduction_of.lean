-- Prove2me | solution 1 for PI.FockOneDegW.reduction_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:29.12979+00:00
-- url     : https://prove2.me/submissions/c0ed2e61-a26a-4d2a-ac0e-8bf15463ebee

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_SameBlockOfPosC
import Theorems.Thm_PI_FockOneDegW_key_of
import Theorems.Thm_FockRaiseLowGrade_eq_zero_of_hc
import Theorems.Thm_FockRaiseLowGrade_hc_hc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW
namespace PI.FockOneDegW
theorem _root_.solution (hI : InnerFacts) (hKc : KHc) (hKh : KHarm) (hHc : HcHarm) (hS : HarmSub)
    (hA : KAdj) (hE : HwExist) : Reduction := by
  intro hT p q r s μ P hP0 hOT hH
  obtain ⟨W, hWfd, hPW, hWK, hWhw⟩ := hOT
  have key := fun e he => key_of hI hKc hKh hHc hS hA hE hT μ W hWK hWhw P hPW hH e he
  obtain ⟨e, he⟩ : ∃ e, homogeneousComponent e P ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP0 (FockRaiseLowGrade.eq_zero_of_hc P h)
  refine ⟨e, key e he, ?_⟩
  have hother : ∀ e', e' ≠ e → homogeneousComponent e' P = 0 := by
    intro e' hne
    by_contra h
    have h1 := key e' h
    rw [← key e he] at h1
    exact hne (by exact_mod_cast h1)
  have hPe : P = homogeneousComponent e P := by
    have : P - homogeneousComponent e P = 0 := by
      apply FockRaiseLowGrade.eq_zero_of_hc
      intro e'
      rw [map_sub, FockRaiseLowGrade.hc_hc]
      by_cases h : e' = e
      · subst h; simp
      · rw [if_neg h, hother e' h, sub_zero]
    exact sub_eq_zero.mp this
  rw [hPe]
  exact (mem_homogeneousSubmodule _ _).mpr (homogeneousComponent_isHomogeneous e P)
end PI.FockOneDegW
