-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.vogan_num
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:54.581564+00:00
-- url     : https://prove2.me/submissions/a255beba-ba6f-42d6-926c-b91fbedf6694

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gap_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_abs_dot_root_rhoC_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casValK_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Num
variable {ε : Fin n → Bool}
private theorem dot_add_l (u v w : Fin n → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, sum_add_distrib]
private theorem dot_add_r (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, sum_add_distrib]
private theorem dot_comm' (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp only [dot, mul_comm]
private theorem dot_sum_r {k : ℕ} (u : Fin n → ℝ) (f : Fin k → Fin n → ℝ) :
    dot u (∑ i, f i) = ∑ i, dot u (f i) := by
  simp only [dot, Finset.sum_apply, mul_sum]
  exact Finset.sum_comm
private theorem nsq_add'' (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  simp only [nsq, dot_add_l, dot_add_r, dot_comm' v u]; ring
end Num
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {Λ ν : Fin n → ℝ} {j : ℕ} (hj : 1 ≤ j) (hν : IsNCSum ε j ν) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hc : casValK ε Λ + 2 * (j : ℝ) * (h - n + 1) ≤ casValK ε (Λ + ν)) :
    nsq (Λ + (2 : ℝ) • rhoC ε) ≤ nsq (Λ + ν + (2 : ℝ) • rhoC ε) := by
  obtain ⟨γ, hγ, rfl⟩ := hν
  obtain ⟨hg1, hg2⟩ := gap_gt (hγ ⟨0, hj⟩) hbig
  have hρ : -((j : ℝ) * (((n : ℝ) - 2) / 2)) ≤ dot (rhoC ε) (∑ i, root (γ i).1 (γ i).2) := by
    rw [dot_sum_r]
    have : ∑ _i : Fin j, -(((n : ℝ) - 2) / 2) ≤ ∑ i, dot (rhoC ε) (root (γ i).1 (γ i).2) := by
      apply Finset.sum_le_sum
      intro i _
      have := abs_dot_root_rhoC_le (ε := ε) (hγ i)
      rw [dot_comm'] at this
      linarith [neg_abs_le (dot (rhoC ε) (root (γ i).1 (γ i).2))]
    simpa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg] using this
  rw [casValK_add] at hc
  have e2 : Λ + (2 : ℝ) • rhoC ε = (Λ + rhoC ε) + rhoC ε := by rw [two_smul]; abel
  have e3 : Λ + (∑ i, root (γ i).1 (γ i).2) + (2 : ℝ) • rhoC ε =
      ((Λ + rhoC ε) + rhoC ε) + ∑ i, root (γ i).1 (γ i).2 := by rw [two_smul]; abel
  rw [e2, e3, nsq_add'' ((Λ + rhoC ε) + rhoC ε), dot_add_l]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hpos : 0 ≤ 2 * h - 3 * (n : ℝ) + 4 := by linarith
  nlinarith [mul_nonneg hj0 hpos]
end ReciprocityTheory.ChartRestriction.DS
