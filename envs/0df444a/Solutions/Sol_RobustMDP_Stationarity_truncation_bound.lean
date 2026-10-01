-- Prove2me | solution 1 for RobustMDP.Stationarity.truncation_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:04:58.562302+00:00
-- url     : https://prove2.me/submissions/43e8f4b3-84c1-433f-ad1a-311464ded453

import Definitions.Def_RobustMDP_Stationarity_gameValues
import Mathlib.Order.ConditionallyCompleteLattice.Group
import Mathlib.Tactic
open RobustMDP.Stationarity Filter Topology
namespace CStationary

theorem state_simplex {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n)
    (π : Policy n A) (τ : M.NaturePolicy) : ∀ t, M.stateDist i₀ π τ t∈stdSimplex ℝ (Fin n) := by
  intro t
  induction t with
  | zero => simpa [Model.stateDist,eq_comm] using ite_eq_mem_stdSimplex ℝ i₀
  | succ t ih =>
    have hp : ∀ i, (τ t).1 (π t i) i∈stdSimplex ℝ (Fin n) :=
      fun i => M.rows_subset_simplex _ _ ((τ t).2 _ _)
    constructor
    · intro j
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (ih.1 i) ((hp i).1 j))
    · simp only [Model.stateDist]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum,(hp _).2,mul_one]
      exact ih.2

theorem cost_le_cmax {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (i : Fin n) (a : A) :
    M.cost i a ≤ M.cmax :=
  (le_ciSup (Set.finite_range (M.cost i)).bddAbove a).trans
    (le_ciSup (Set.finite_range (fun i => ⨆ a, M.cost i a)).bddAbove i)

theorem stage_bounds {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ)
    (hν : 0 ≤ ν) (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) (t : ℕ) :
    0 ≤ M.stageCost ν i₀ π τ t ∧ M.stageCost ν i₀ π τ t ≤ ν^t*M.cmax := by
  have hp := state_simplex M i₀ π τ t
  constructor
  · exact mul_nonneg (pow_nonneg hν _) (Finset.sum_nonneg (fun i _ => mul_nonneg (hp.1 i) (M.cost_nonneg _ _)))
  · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hν _)
    calc
      _ ≤ ∑ i, M.stateDist i₀ π τ t i*M.cmax := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (cost_le_cmax M i (π t i)) (hp.1 i))
      _ = _ := by rw [← Finset.sum_mul,hp.2,one_mul]

theorem series_tail (f : ℕ → ℝ) (ν C : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1)
    (hf0 : ∀ t, 0 ≤ f t) (hbound : ∀ t, f t ≤ ν^t*C) (N : ℕ) :
    (∑ t∈Finset.range N, f t) ≤ ∑' t, f t ∧
      (∑' t, f t) ≤ (∑ t∈Finset.range N, f t)+ν^N*C/(1-ν) := by
  have hg := (hasSum_geometric_of_lt_one hν0 hν1).mul_right C
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hbound hg.summable
  refine ⟨hf.sum_le_tsum _ (fun t _ => hf0 t),?_⟩
  have htail := Summable.tsum_le_tsum (fun t => hbound (t+N))
    ((summable_nat_add_iff N).mpr hf) ((summable_nat_add_iff N).mpr hg.summable)
  have hts : (∑' t : ℕ, ν^(t+N)*C)=ν^N*C/(1-ν) := by
    have hh := (hasSum_geometric_of_lt_one hν0 hν1).mul_right (ν^N*C)
    convert! hh.tsum_eq using 1
    · congr 1
      ext t
      rw [pow_add]
      ring
    · ring
  rw [hts] at htail
  have hdecomp := hf.sum_add_tsum_nat_add N
  linarith

theorem truncation {n : ℕ} {A : Type} [Fintype A] (M : Model n A) (ν : ℝ)
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) (i₀ : Fin n) (π : Policy n A) (τ : M.NaturePolicy) (N : ℕ) :
    M.finiteCost ν i₀ N π τ ≤ M.infCost ν i₀ π τ ∧
      M.infCost ν i₀ π τ ≤ M.finiteCost ν i₀ N π τ+M.epsN ν N :=
  series_tail (M.stageCost ν i₀ π τ) ν M.cmax hν0 hν1
    (fun t => (stage_bounds M ν hν0 i₀ π τ t).1) (fun t => (stage_bounds M ν hν0 i₀ π τ t).2) N
end CStationary

theorem solution {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A)
    (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n)
    (π : Policy n A) (τ : M.NaturePolicy) (N : ℕ) :
    M.finiteCost ν i₀ N π τ ≤ M.infCost ν i₀ π τ ∧
      M.infCost ν i₀ π τ ≤ M.finiteCost ν i₀ N π τ+M.epsN ν N :=
  CStationary.truncation M ν hν₀.le hν₁ i₀ π τ N
