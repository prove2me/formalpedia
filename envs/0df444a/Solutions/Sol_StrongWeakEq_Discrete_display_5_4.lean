-- Prove2me | solution 1 for StrongWeakEq.Discrete.display_5_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:28:11.062003+00:00
-- url     : https://prove2.me/submissions/db8d40e3-e85d-4d7f-9289-d563dd78a2a0

import Mathlib
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel

open StrongWeakEq.Discrete in
theorem solution {N : ℕ} {A : Fin N → Set (Fin N → ℝ)} {κ : ℕ → Fin N → (Fin N → ℝ) → ℝ}
    (hS : DStanding A κ) {u us : Matrix (Fin N) (Fin N) ℝ}
    (hu : u ∈ DControls A) (hus : us ∈ DControls A) (i : Fin N) :
    dConcatValue κ u us i = κ 0 i (u i) + ∑ j, dH κ us j * u i j := by
  have hstoch : us ∈ Matrix.rowStochastic ℝ (Fin N) :=
    Matrix.mem_rowStochastic_iff_sum.mpr
      ⟨fun j k => (hS.rows j (hus j)).1 k, fun j => (hS.rows j (hus j)).2⟩
  have hpow : ∀ t : ℕ, us ^ t ∈ Matrix.rowStochastic ℝ (Fin N) :=
    fun t => Submonoid.pow_mem _ hstoch t
  obtain ⟨b, hb, hbd⟩ := hS.summ
  have hg : ∀ j, Summable (fun t : ℕ => ∑ k, (us ^ t) j k * κ (t + 1) k (us k)) := by
    intro j
    apply Summable.of_norm_bounded (g := fun t : ℕ => (N : ℝ) * b (t + 1))
      (((summable_nat_add_iff 1).mpr hb).mul_left (N : ℝ))
    intro t
    rw [Real.norm_eq_abs]
    calc |∑ k, (us ^ t) j k * κ (t + 1) k (us k)|
        ≤ ∑ k, |(us ^ t) j k * κ (t + 1) k (us k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin N, b (t + 1) := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          have h0 : 0 ≤ (us ^ t) j k := Matrix.nonneg_of_mem_rowStochastic (hpow t)
          have h1 : (us ^ t) j k ≤ 1 := Matrix.le_one_of_mem_rowStochastic (hpow t)
          have h2 := hbd (t + 1) k (us k) (hS.rows k (hus k))
          rw [abs_of_nonneg h0]
          nlinarith [abs_nonneg (κ (t + 1) k (us k))]
      _ = (N : ℝ) * b (t + 1) := by simp
  unfold dConcatValue dH
  congr 1
  have e : ∀ t : ℕ, ∑ k, (u * us ^ t) i k * κ (t + 1) k (us k) =
      ∑ j, u i j * ∑ k, (us ^ t) j k * κ (t + 1) k (us k) := by
    intro t
    simp_rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [e]
  rw [Summable.tsum_finsetSum (fun j _ => (hg j).mul_left (u i j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [tsum_mul_left]
  ring
