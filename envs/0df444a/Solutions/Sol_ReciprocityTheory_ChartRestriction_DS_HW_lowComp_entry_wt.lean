-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.lowComp_entry_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:11:46.711321+00:00
-- url     : https://prove2.me/submissions/252ea776-0925-46a8-8f34-267a244a2b5f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_LowComp

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
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ε : Fin n → Bool}
    {M : Fin n → Fin n → Matrix ι ι ℂ} {γ : ι → Fin n → ℝ}
    (hM : Formalism.REAL.KRel ε M) (hd : ∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ))
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) {j k : ι} (hne : M a b j k ≠ 0) (c : Fin n) :
    γ k c = γ j c + ((if c = b then 1 else 0) - (if c = a then 1 else 0)) := by
  have h := congrFun (congrFun (hM a b c c he rfl) j) k
  rw [hd c] at h
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hba : b ≠ a := ne_of_gt hab
  have key : ((γ k c : ℝ) : ℂ) - ((γ j c : ℝ) : ℂ) =
      (((if c = b then 1 else 0) - (if c = a then 1 else 0) : ℝ) : ℂ) := by
    by_cases hcb : c = b
    · subst hcb
      have hca : ¬ c = a := hba
      simp only [if_neg hca, ite_true, Matrix.zero_apply, sub_zero] at h
      simp only [if_neg hca]
      apply mul_left_cancel₀ hne
      push_cast
      linear_combination h
    · by_cases hca : c = a
      · subst hca
        simp only [if_neg (Ne.symm hcb), ite_true, Matrix.zero_apply, zero_sub] at h
        simp only [if_neg hcb]
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination h
      · simp only [if_neg (Ne.symm hcb), if_neg hca, Matrix.zero_apply, sub_zero] at h
        simp only [if_neg hcb, if_neg hca]
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination h
  have key' : ((γ k c - γ j c : ℝ) : ℂ) =
      (((if c = b then 1 else 0) - (if c = a then 1 else 0) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub (γ k c)]; exact key
  have := Complex.ofReal_injective key'
  linarith
end ReciprocityTheory.ChartRestriction.DS.HW
