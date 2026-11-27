-- Prove2me | solution 1 for SharedVehicleApprox.Pricing.Supplement.theorem_29_refuted
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:38.005185+00:00
-- url     : https://prove2.me/submissions/881502f2-f076-4d68-87af-b8ddaf552bae

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_PointPricing
import Definitions.Def_SharedVehicleApprox_Pricing_Supplement_DiscretePointPricing

open Finset QueueingFundamentals.Networks

open SharedVehicleApprox
open SharedVehicleApprox.Pricing
open SharedVehicleApprox.Pricing.Supplement

/-- Refutation of Theorem 29, p. 37: one station, one unit, uniform values, revenue,
grid `(3/5, 1/10)` and `α = 1`. The printed adjacent-grid condition holds, but
Algorithm 7 rounds the unrestricted optimum `1/2` to `1/10`, earning `9/100`
instead of the discrete optimum `6/25` at `3/5`. -/
theorem solution :
    let φ : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
    let I : Fin 1 → Fin 1 → ℝ → ℝ := fun _ _ q => 1 - q
    let grid : Fin 1 → Finset ℝ := fun _ => {3 / 5, 1 / 10}
    let levels : Fin 2 → ℝ := ![3 / 5, 1 / 10]
    let q' : Fin 1 → ℝ := fun _ => 1 / 2
    let qt : Fin 1 → ℝ := fun _ => 1 / 10
    let qc : Fin 1 → ℝ := fun _ => 3 / 5
    let π : (Fin 1 → ℕ) → ℝ := fun x => if x ∈ states 1 1 then 1 else 0
    (∀ i j, 0 ≤ φ i j) ∧ SupportConnected φ (fun _ _ => 1) ∧
    (∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (rewardCurve I i j)) ∧
    (∀ i, ∀ v ∈ grid i, 0 ≤ v ∧ v ≤ 1) ∧
    Antitone levels ∧ (1 : ℝ) * levels 0 ≥ levels 1 ∧
    IsAlg6Optimal φ I q' ∧ IsAlg7Output grid q' qt ∧
    IsDiscretePointPolicy 1 1 grid (fun x i => toPolicy (pointQuantile qc) x i 0) ∧
    IsStationary 1 1 φ (toPolicy (pointQuantile qt)) π ∧
    IsStationary 1 1 φ (toPolicy (pointQuantile qc)) π ∧
    obj 1 1 φ I (toPolicy (pointQuantile qt)) π = 9 / 100 ∧
    obj 1 1 φ I (toPolicy (pointQuantile qc)) π = 6 / 25 ∧
    (∀ (q : (Fin 1 → ℕ) → Fin 1 → ℝ) (πc : (Fin 1 → ℕ) → ℝ),
      IsDiscretePointPolicy 1 1 grid q → IsStationary 1 1 φ (pointPolicy q) πc →
        obj 1 1 φ I (pointPolicy q) πc ≤ 6 / 25) ∧
    ¬ ((1 : ℝ) * obj 1 1 φ I (toPolicy (pointQuantile qt)) π ≥
      (1 : ℝ) / (1 + 1 - 1) * (6 / 25)) := by
        intro φ I grid levels q' qt qc π
        have hS : states 1 1 = {fun _ => 1} := by
          ext x
          simp only [states, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
            Finset.mem_singleton, Fin.sum_univ_one]
          constructor
          · rintro ⟨-, h⟩
            funext i
            rw [Subsingleton.elim i 0]; exact h
          · rintro rfl
            exact ⟨fun _ => by norm_num, rfl⟩
        have hπ : ∀ x ∈ states 1 1, π x = 1 := fun x hx => by simp only [π, if_pos hx]
        have hx0 : ∀ x ∈ states 1 1, ∀ i : Fin 1, x i = 1 := by
          intro x hx i; rw [hS, Finset.mem_singleton] at hx; rw [hx]
        have hstat : ∀ c : ℝ, IsStationary 1 1 φ (toPolicy (pointQuantile (fun _ => c))) π := by
          intro c
          refine ⟨fun x => ?_, fun x hx => ?_, ?_, fun x hx => ?_⟩
          · simp only [π]; split_ifs <;> norm_num
          · simp only [π, if_neg hx]
          · rw [hS, Finset.sum_singleton]; exact hπ _ (by rw [hS]; exact Finset.mem_singleton_self _)
          · simp [inflowTerm]; ring
        have hobj : ∀ c : ℝ, obj 1 1 φ I (toPolicy (pointQuantile (fun _ => c))) π = c * (1 - c) := by
          intro c
          rw [obj, hS, Finset.sum_singleton]
          rw [hπ _ (by rw [hS]; exact Finset.mem_singleton_self _)]
          simp [φ, I, rewardCurve, toPolicy, pointQuantile]
        refine ⟨fun _ _ => zero_le_one, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hstat _, hstat _, ?_, ?_, ?_, ?_⟩
        · intro i j
          rw [Subsingleton.elim i j]
        · intro i j
          refine ⟨convex_Icc 0 1, ?_⟩
          intro x _ y _ a b ha hb hab
          simp only [rewardCurve, I, smul_eq_mul]
          have hb' : b = 1 - a := by linarith
          subst hb'
          nlinarith [mul_nonneg ha hb, sq_nonneg (x - y), mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))]
        · intro i v hv
          simp only [grid, Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl <;> norm_num
        · intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all [levels] <;> norm_num
        · simp [levels]; norm_num
        · refine ⟨⟨fun i j => ?_, fun i => ?_⟩, fun q hq => ?_⟩
          · simp [pointQuantile, q']; norm_num
          · rw [Subsingleton.elim i 0]; simp [pointQuantile]
          · simp only [elevObj, Fin.sum_univ_one, φ, one_mul, rewardCurve, I, pointQuantile, q']
            nlinarith [sq_nonneg (q 0 - 1/2)]
        · intro i
          refine ⟨⟨by simp [grid, qt], by simp [q', qt]; norm_num⟩, ?_⟩
          rintro v ⟨hv, hle⟩
          simp only [grid, Finset.mem_insert, Finset.mem_singleton] at hv
          simp only [q'] at hle
          rcases hv with rfl | rfl
          · norm_num at hle
          · exact le_refl _
        · refine ⟨fun x hx i j => ?_, fun x hx i hi => ?_⟩
          · simp only [pointPolicy, toPolicy, pointQuantile, qc]
            split_ifs with h
            · exact ⟨by norm_num, by norm_num, fun h0 => absurd h0 (Nat.pos_iff_ne_zero.mp h)⟩
            · refine ⟨le_refl _, by norm_num, fun _ => rfl⟩
          · simp only [toPolicy, pointQuantile, qc, if_pos hi, grid]
            simp
        · rw [hobj]; norm_num
        · rw [hobj]; norm_num
        · intro q πc hq hst
          obtain ⟨hpol, hgrid⟩ := hq
          obtain ⟨hnn, hoff, hsum, -⟩ := hst
          have hmem : (fun _ : Fin 1 => (1:ℕ)) ∈ states 1 1 := by rw [hS]; exact Finset.mem_singleton_self _
          have hg := hgrid _ hmem 0 (by norm_num)
          rw [hS, Finset.sum_singleton] at hsum
          rw [obj, hS, Finset.sum_singleton, hsum]
          simp only [Fin.sum_univ_one, φ, one_mul, rewardCurve, I, pointPolicy]
          simp only [grid, Finset.mem_insert, Finset.mem_singleton] at hg
          rcases hg with h | h <;> rw [h] <;> norm_num
        · rw [hobj]; norm_num
