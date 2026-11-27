-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.G2.vogan_num
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:24:33.892955+00:00
-- url     : https://prove2.me/submissions/34e264a8-55d2-4b3c-b486-1061f955321d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_StdGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_Numerics
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
namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}
section Num
variable {ε : Fin n → Bool}
private theorem dot_add_l (u v w : Fin n → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private theorem dot_add_r (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem dot_comm' (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp only [dot, mul_comm]
private theorem dot_sum_r {k : ℕ} (u : Fin n → ℝ) (f : Fin k → Fin n → ℝ) :
    dot u (∑ i, f i) = ∑ i, dot u (f i) := by
  simp only [dot, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm
private theorem dot_root_r (u : Fin n → ℝ) (a b : Fin n) : dot u (root a b) = u a - u b := by
  simp [dot, root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
private theorem nsq_add'' (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  unfold nsq
  rw [dot_add_l, dot_add_r, dot_add_r, dot_comm' v u]
  ring
end Num
end ReciprocityTheory.ChartRestriction.DS.G2
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}
variable {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS.G2
theorem _root_.solution {Λ ν : Fin n → ℝ} {j : ℕ} (hj : 1 ≤ j) (hν : IsNCSum ε j ν) {h : ℝ}
    (hbig : 2 * (n : ℝ) < h)
    (hc : casValK ε Λ + 2 * (j : ℝ) * (h - n + 1) ≤ casValK ε (Λ + ν)) :
    nsq (Λ + (2 : ℝ) • rhoC ε) ≤ nsq (Λ + ν + (2 : ℝ) • rhoC ε) := by
  obtain ⟨γ, -, hνeq⟩ := hν
  have hcard : ∀ s : Finset (Fin n), (s.card : ℝ) ≤ n := fun s => by
    have := Finset.card_le_univ s
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have hbound : ∀ a, -(n : ℝ) / 2 ≤ rhoC ε a ∧ rhoC ε a ≤ (n : ℝ) / 2 := by
    intro a
    have h1 := hcard (univ.filter fun b => a < b ∧ ε b = ε a)
    have h2 := hcard (univ.filter fun b => b < a ∧ ε b = ε a)
    have h3 := (Nat.cast_nonneg (univ.filter fun b => a < b ∧ ε b = ε a).card : (0 : ℝ) ≤ _)
    have h4 := (Nat.cast_nonneg (univ.filter fun b => b < a ∧ ε b = ε a).card : (0 : ℝ) ≤ _)
    simp only [rhoC]
    constructor <;> linarith
  have hdot : -((j : ℝ) * n) ≤ dot (rhoC ε) ν := by
    rw [hνeq, dot_sum_r]
    simp only [dot_root_r]
    have hle : ∀ i ∈ (univ : Finset (Fin j)), -(n : ℝ) ≤ rhoC ε (γ i).1 - rhoC ε (γ i).2 :=
      fun i _ => by
        have := hbound (γ i).1
        have := hbound (γ i).2
        linarith
    have := Finset.sum_le_sum hle
    simpa using this
  have hjn : (j : ℝ) * n ≤ j * (h - n + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg j)
  unfold casValK at hc
  have e1 : Λ + (2 : ℝ) • rhoC ε = (Λ + rhoC ε) + rhoC ε := by rw [two_smul]; abel
  have e2 : Λ + ν + (2 : ℝ) • rhoC ε = ((Λ + rhoC ε) + rhoC ε) + ν := by rw [two_smul]; abel
  have e3 : Λ + ν + rhoC ε = (Λ + rhoC ε) + ν := by abel
  rw [e3, nsq_add'' (Λ + rhoC ε) ν] at hc
  rw [e1, e2, nsq_add'' ((Λ + rhoC ε) + rhoC ε) ν, dot_add_l (Λ + rhoC ε) (rhoC ε) ν]
  linarith
end ReciprocityTheory.ChartRestriction.DS.G2
