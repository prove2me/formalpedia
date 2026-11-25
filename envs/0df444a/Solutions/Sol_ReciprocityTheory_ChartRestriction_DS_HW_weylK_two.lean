-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylK_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:27:02.058248+00:00
-- url     : https://prove2.me/submissions/ee0bc429-228a-4f26-9b2b-063a362285b9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylRatio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylK_shift_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylRatio_prod_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylK_shift

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ) (hΛ : KDom ε Λ) {i j : Fin n}
    (hij : ε i ≠ ε j) :
    weylK ε (Λ + (Pi.single i 1 - Pi.single j 1)) =
      weylK ε Λ *
        (∏ b ∈ univ.filter (fun b => b ≠ i ∧ ε b = ε i),
          (((Λ + rhoC ε) i - (Λ + rhoC ε) b + 1) / ((Λ + rhoC ε) i - (Λ + rhoC ε) b))) *
        ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
          (((Λ + rhoC ε) j - (Λ + rhoC ε) b - 1) / ((Λ + rhoC ε) j - (Λ + rhoC ε) b)) := by
  have hji : j ≠ i := fun h => hij (by rw [h])
  have hF : ∀ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
      (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b =
        (Λ + rhoC ε) j - (Λ + rhoC ε) b := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hbi : b ≠ i := fun h => hij (by rw [← h, hb.2])
    simp only [Pi.add_apply, Pi.single_apply, hji, hbi, ↓reduceIte]
    ring
  have hP0 : ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
      ((Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b) =
        ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j), ((Λ + rhoC ε) j - (Λ + rhoC ε) b) :=
    Finset.prod_congr rfl hF
  have hP1 : ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j),
      ((Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) j - (Λ + Pi.single i (1 : ℝ) + rhoC ε : Fin n → ℝ) b + -1) =
        ∏ b ∈ univ.filter (fun b => b ≠ j ∧ ε b = ε j), ((Λ + rhoC ε) j - (Λ + rhoC ε) b - 1) :=
    Finset.prod_congr rfl fun b hb => by rw [hF b hb]; ring
  have hmul := weylK_shift_mul ε (Λ + Pi.single i 1) j (-1)
  rw [hP0, hP1, weylK_shift ε Λ hΛ i 1] at hmul
  have hΛe : Λ + (Pi.single i 1 - Pi.single j 1) = Λ + Pi.single i 1 + Pi.single j (-1) := by
    rw [sub_eq_add_neg, ← Pi.single_neg, add_assoc]
  rw [hΛe, Finset.prod_div_distrib (s := univ.filter (fun b => b ≠ j ∧ ε b = ε j)), ← mul_div_assoc, eq_div_iff (weylRatio_prod_ne ε Λ hΛ j), hmul]
end ReciprocityTheory.ChartRestriction.DS.HW
