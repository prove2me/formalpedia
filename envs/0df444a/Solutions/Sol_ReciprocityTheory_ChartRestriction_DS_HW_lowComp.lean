-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.lowComp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:15.965329+00:00
-- url     : https://prove2.me/submissions/65f47d46-10f6-4898-ac14-febfe9f6625e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_LowComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowComp_tensAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowComp_lin_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution : LowCompStatement := by
  intro V _ _ n ε A ι _ _ M γ hM hd ν x hx hhw
  classical
  obtain ⟨hwt, hup⟩ := hhw
  set S : Finset ι := Finset.univ.filter (fun i => x i ≠ 0) with hS
  have hSne : S.Nonempty := by
    by_contra h
    apply hx
    ext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using hi⟩⟩
  obtain ⟨i0, hi0, hmax⟩ := S.exists_max_image (fun i => lowCompLin (γ i)) hSne
  refine ⟨γ i0, ⟨i0, rfl, (Finset.mem_filter.1 hi0).2⟩, ?_⟩
  intro j hj
  constructor
  · intro c
    have h := congrArg (fun y : PiLp 2 (fun _ : ι => V) => y j) (hwt c)
    simp only [lowComp_tensAct_apply, hd c, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, PiLp.smul_apply] at h
    rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h, hj]
    abel
  · intro a b hab he
    have h := congrArg (fun y : PiLp 2 (fun _ : ι => V) => y j) (hup a b hab he)
    simp only [lowComp_tensAct_apply, PiLp.zero_apply] at h
    have hsum : ∑ k, M a b j k • x k = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hne : M a b j k = 0
      · simp [hne]
      · have hxk : x k = 0 := by
          by_contra hxk
          have hle := hmax k (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxk⟩)
          have hl := lowComp_lin_entry hM hd hab he hne
          rw [hj] at hl
          have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
          linarith
        simp [hxk]
    rw [hsum, add_zero] at h
    exact h
end ReciprocityTheory.ChartRestriction.DS.HW
