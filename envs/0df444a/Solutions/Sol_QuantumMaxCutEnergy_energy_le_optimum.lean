-- Prove2me | solution 1 for QuantumMaxCutEnergy.energy_le_optimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T16:58:53.519401+00:00
-- url     : https://prove2.me/submissions/06f870f2-51c2-43ff-a0ca-930cd2beafc9

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

lemma normSq_sub_le_two (z w : ℂ) :
    Complex.normSq (z - w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h2 : ‖z - w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 := by
    nlinarith [norm_sub_le z w, norm_nonneg (z - w)]
  nlinarith [h2, sq_nonneg (‖z‖ - ‖w‖), norm_nonneg z, norm_nonneg w]

def reindexPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Basis n ≃ Basis n where
  toFun x := x ∘ σ
  invFun x := x ∘ σ.symm
  left_inv x := by funext k; simp
  right_inv x := by funext k; simp

lemma sum_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Basis n → ℝ) :
    (∑ x, f (x ∘ σ)) = ∑ x, f x :=
  Equiv.sum_comp (reindexPerm σ) f

theorem edge_sum_le_four {n : ℕ} (ψ : Wave n) (hψ : squaredNorm ψ = 1) (e : Edge n) :
    (∑ x, Complex.normSq (ψ x - ψ (x ∘ Equiv.swap e.val.1 e.val.2))) ≤ 4 := by
  have h1 : (∑ x, Complex.normSq (ψ x - ψ (x ∘ Equiv.swap e.val.1 e.val.2))) ≤
      ∑ x, (2 * Complex.normSq (ψ x) + 2 * Complex.normSq (ψ (x ∘ Equiv.swap e.val.1 e.val.2))) :=
    Finset.sum_le_sum (fun x _ => normSq_sub_le_two _ _)
  have h3 : (∑ x, Complex.normSq (ψ (x ∘ Equiv.swap e.val.1 e.val.2)))
      = ∑ x, Complex.normSq (ψ x) :=
    sum_comp_perm (Equiv.swap e.val.1 e.val.2) (fun x => Complex.normSq (ψ x))
  have h2 : (∑ x, (2 * Complex.normSq (ψ x) +
        2 * Complex.normSq (ψ (x ∘ Equiv.swap e.val.1 e.val.2))))
      = 2 * squaredNorm ψ + 2 * squaredNorm ψ := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h3, squaredNorm]
  rw [h2, hψ] at h1
  linarith

theorem energy_le_two_mul_sum {n : ℕ} (w : Weights n) (ψ : Wave n) (hψ : squaredNorm ψ = 1) :
    energy w ψ ≤ 2 * ∑ e, (w e : ℝ) := by
  calc energy w ψ = ∑ e, (w e : ℝ) / 2 *
        (∑ x, Complex.normSq (ψ x - ψ (x ∘ Equiv.swap e.val.1 e.val.2))) := rfl
    _ ≤ ∑ e, (w e : ℝ) / 2 * 4 := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        have h4 := edge_sum_le_four ψ hψ e
        have hw : (0:ℝ) ≤ (w e : ℝ) / 2 := by
          have h0 : (0:ℝ) ≤ (w e : ℝ) := by positivity
          linarith
        nlinarith
    _ = 2 * ∑ e, (w e : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun e _ => by ring)

lemma exists_normalized (n : ℕ) : ∃ ψ : Wave n, squaredNorm ψ = 1 := by
  classical
  refine ⟨fun x => if x = (fun _ => false) then 1 else 0, ?_⟩
  unfold squaredNorm
  rw [Finset.sum_eq_single (fun _ => false)]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem energy_le_optimum {n : ℕ} (w : Weights n) (ψ : Wave n) (hψ : squaredNorm ψ = 1) :
    energy w ψ ≤ optimum ⟨n, w⟩ := by
  refine le_csSup ?_ ⟨ψ, hψ, rfl⟩
  refine ⟨2 * ∑ e, (w e : ℝ), ?_⟩
  rintro v ⟨φ, hφ, rfl⟩
  exact energy_le_two_mul_sum w φ hφ

end QuantumMaxCutEnergy

theorem solution {n : ℕ} (w : QuantumMaxCutEnergy.Weights n) (ψ : QuantumMaxCutEnergy.Wave n)
    (hψ : QuantumMaxCutEnergy.squaredNorm ψ = 1) :
    QuantumMaxCutEnergy.energy w ψ ≤ QuantumMaxCutEnergy.optimum ⟨n, w⟩ :=
  QuantumMaxCutEnergy.energy_le_optimum w ψ hψ
