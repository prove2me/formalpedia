-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.degree_num
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:14.724038+00:00
-- url     : https://prove2.me/submissions/19ea31eb-bf2a-4458-9975-db5e707ba514

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_nsq_root

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
private theorem nsq_nonneg'' (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact sum_nonneg fun i _ => mul_self_nonneg (u i)
private theorem nsq_add'' (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  simp only [nsq, dot_add_l, dot_add_r, dot_comm' v u]; ring
private theorem dot_le_sqrt (u v : Fin n → ℝ) : dot u v ≤ √(nsq u) * √(nsq v) := by
  rw [← Real.sqrt_mul (nsq_nonneg'' u)]
  refine le_trans (le_abs_self _) ?_
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  simpa [dot, nsq, sq] using Finset.sum_mul_sq_le_sq_mul_sq univ u v
private theorem sqrt_nsq_add_le (u v : Fin n → ℝ) : √(nsq (u + v)) ≤ √(nsq u) + √(nsq v) := by
  have h1 : nsq (u + v) ≤ (√(nsq u) + √(nsq v)) ^ 2 := by
    rw [nsq_add'', add_sq, Real.sq_sqrt (nsq_nonneg'' u), Real.sq_sqrt (nsq_nonneg'' v)]
    nlinarith [dot_le_sqrt u v]
  calc √(nsq (u + v)) ≤ √((√(nsq u) + √(nsq v)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := Real.sqrt_sq (by positivity)
private theorem sqrt_nsq_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    √(nsq (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, √(nsq (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nsq, dot]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (sqrt_nsq_add_le _ _).trans (by linarith)
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
theorem _root_.solution {Λ ν : Fin n → ℝ} {j k : ℕ} (hjk : j ≤ k) (hν : IsNCSum ε j ν) :
    casValK ε (Λ + ν) ≤ (√(nsq (Λ + rhoC ε)) + √2 * k) ^ 2 - nsq (rhoC ε) := by
  obtain ⟨γ, hγ, rfl⟩ := hν
  have hs : √(nsq (∑ i, root (γ i).1 (γ i).2)) ≤ √2 * k := by
    refine (sqrt_nsq_sum_le _ _).trans ?_
    have : ∀ i, √(nsq (root (γ i).1 (γ i).2)) = √2 := fun i => by
      rw [nsq_root (fun e => hγ i (by rw [e]))]
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjk) (Real.sqrt_nonneg 2)
  unfold casValK
  have e : Λ + (∑ i, root (γ i).1 (γ i).2) + rhoC ε = (Λ + rhoC ε) + ∑ i, root (γ i).1 (γ i).2 := by
    abel
  rw [e]
  have h1 := (sqrt_nsq_add_le (Λ + rhoC ε) (∑ i, root (γ i).1 (γ i).2)).trans (by linarith [hs] :
    √(nsq (Λ + rhoC ε)) + √(nsq (∑ i, root (γ i).1 (γ i).2)) ≤ √(nsq (Λ + rhoC ε)) + √2 * k)
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [Real.sq_sqrt (nsq_nonneg'' _)] at h2
  linarith
end ReciprocityTheory.ChartRestriction.DS
