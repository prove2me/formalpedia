-- Prove2me | solution 1 for QuantumMaxCutEnergy.energy_eq_sum_overlap
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-02T12:20:33.579864+00:00
-- url     : https://prove2.me/submissions/88702113-d230-401b-a61e-37035f00d335

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem solution {n : ℕ} (w : QuantumMaxCutEnergy.Weights n) (ψ : QuantumMaxCutEnergy.Wave n)
    (hψ : QuantumMaxCutEnergy.squaredNorm ψ = 1) :
    QuantumMaxCutEnergy.energy w ψ = ∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) *
      (1 - (∑ x, star (ψ x) * ψ (x ∘ Equiv.swap e.val.1 e.val.2)).re) := by
  classical
  unfold QuantumMaxCutEnergy.energy
  apply Finset.sum_congr rfl
  intro e he
  let τ : Equiv.Perm (QuantumMaxCutEnergy.Basis n) :=
    { toFun := fun x => x ∘ Equiv.swap e.val.1 e.val.2
      invFun := fun x => x ∘ Equiv.swap e.val.1 e.val.2
      left_inv := by intro x; funext i; simp
      right_inv := by intro x; funext i; simp }
  have hsum : ∑ x, Complex.normSq (ψ (x ∘ Equiv.swap e.val.1 e.val.2)) = 1 := by
    change ∑ x, Complex.normSq (ψ (τ x)) = 1
    calc
      _ = ∑ x, Complex.normSq (ψ x) := Fintype.sum_equiv τ _ _ (fun x => rfl)
      _ = 1 := hψ
  have hterm (x : QuantumMaxCutEnergy.Basis n) :
      Complex.normSq (ψ x - ψ (x ∘ Equiv.swap e.val.1 e.val.2)) =
        Complex.normSq (ψ x) + Complex.normSq (ψ (x ∘ Equiv.swap e.val.1 e.val.2)) -
          2 * (star (ψ x) * ψ (x ∘ Equiv.swap e.val.1 e.val.2)).re := by
    rw [Complex.normSq_sub]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.star_def]
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum, ← Finset.mul_sum, ← Complex.re_sum]
  change (w e : ℝ) / 2 *
    ((QuantumMaxCutEnergy.squaredNorm ψ + 1) -
      2 * (∑ x, star (ψ x) * ψ (x ∘ Equiv.swap e.val.1 e.val.2)).re) = _
  rw [hψ]
  ring

#print axioms solution
