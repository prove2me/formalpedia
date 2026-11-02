-- Prove2me | solution 2 for QuantumMaxCutEnergy.optimum_le_two_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T17:01:50.262775+00:00
-- url     : https://prove2.me/submissions/9c366506-b992-4ade-9b8b-917ec09f3fb8

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib
open scoped BigOperators

set_option autoImplicit false

namespace QMCExtra
open QuantumMaxCutEnergy

/-- Reindexing a sum over all basis states along a permutation of the qubits. -/
lemma sum_comp_perm {n : ℕ} (f : Wave n) (e : Equiv.Perm (Fin n)) :
    (∑ x : Basis n, Complex.normSq (f (x ∘ ⇑e))) = ∑ x : Basis n, Complex.normSq (f x) := by
  let φ : Basis n ≃ Basis n :=
    { toFun := fun x => x ∘ ⇑e
      invFun := fun x => x ∘ ⇑e.symm
      left_inv := by intro x; funext i; simp
      right_inv := by intro x; funext i; simp }
  simpa [φ] using Equiv.sum_comp φ (fun y => Complex.normSq (f y))

lemma normSq_sub_le (z z' : ℂ) :
    Complex.normSq (z - z') ≤ 2 * Complex.normSq z + 2 * Complex.normSq z' := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h := norm_sub_le z z'
  have h2 : ‖z - z'‖ ^ 2 ≤ (‖z‖ + ‖z'‖) ^ 2 := by
    nlinarith [h, norm_nonneg (z - z'), norm_nonneg z, norm_nonneg z']
  nlinarith [h2, sq_nonneg (‖z‖ - ‖z'‖)]

/-- Along one edge the squared differences of a normalized state sum to at most `4`. -/
lemma edge_bound {n : ℕ} (f : Wave n) (hf : squaredNorm f = 1) (i j : Fin n) :
    (∑ x : Basis n, Complex.normSq (f x - f (x ∘ ⇑(Equiv.swap i j)))) ≤ 4 := by
  have hf' : (∑ x : Basis n, Complex.normSq (f x)) = 1 := hf
  have hsum2 : (∑ x : Basis n, Complex.normSq (f (x ∘ ⇑(Equiv.swap i j)))) =
      ∑ x : Basis n, Complex.normSq (f x) := sum_comp_perm f (Equiv.swap i j)
  calc (∑ x : Basis n, Complex.normSq (f x - f (x ∘ ⇑(Equiv.swap i j))))
      ≤ ∑ x : Basis n,
          (2 * Complex.normSq (f x) + 2 * Complex.normSq (f (x ∘ ⇑(Equiv.swap i j)))) :=
        Finset.sum_le_sum (fun x _ => normSq_sub_le (f x) (f (x ∘ ⇑(Equiv.swap i j))))
    _ = 2 * (∑ x : Basis n, Complex.normSq (f x)) +
          2 * (∑ x : Basis n, Complex.normSq (f (x ∘ ⇑(Equiv.swap i j)))) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = 4 := by rw [hsum2, hf']; ring

/-- The energy of any normalized state is at most twice the total weight. -/
theorem energy_le_two_mul {n : ℕ} (w : Weights n) (f : Wave n) (hf : squaredNorm f = 1) :
    energy w f ≤ 2 * ∑ e, (w e : ℝ) := by
  have hterm : ∀ e : Edge n,
      (∑ x : Basis n, Complex.normSq (f x - f (x ∘ ⇑(Equiv.swap e.val.1 e.val.2)))) ≤ 4 :=
    fun e => edge_bound f hf e.val.1 e.val.2
  calc energy w f
      = ∑ e : Edge n, (w e : ℝ) / 2 *
          (∑ x : Basis n, Complex.normSq (f x - f (x ∘ ⇑(Equiv.swap e.val.1 e.val.2)))) := rfl
    _ ≤ ∑ e : Edge n, (w e : ℝ) / 2 * 4 := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        have hw : (0:ℝ) ≤ (w e : ℝ) := by positivity
        have := hterm e
        nlinarith
    _ = 2 * ∑ e : Edge n, (w e : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun e _ => by ring)

end QMCExtra

theorem solution (G : QuantumMaxCutEnergy.Input) :
    QuantumMaxCutEnergy.optimum G ≤ 2 * ∑ e, (G.weights e : ℝ) := by
  change sSup {v : ℝ | ∃ f : QuantumMaxCutEnergy.Wave G.n,
      QuantumMaxCutEnergy.squaredNorm f = 1 ∧ v = QuantumMaxCutEnergy.energy G.weights f}
    ≤ 2 * ∑ e, (G.weights e : ℝ)
  have hne : {v : ℝ | ∃ f : QuantumMaxCutEnergy.Wave G.n,
      QuantumMaxCutEnergy.squaredNorm f = 1 ∧ v = QuantumMaxCutEnergy.energy G.weights f}.Nonempty := by
    set x0 : QuantumMaxCutEnergy.Basis G.n := fun _ => false with hx0
    refine ⟨QuantumMaxCutEnergy.energy G.weights (fun x => if x = x0 then (1:ℂ) else 0),
      ⟨fun x => if x = x0 then (1:ℂ) else 0, ?_, rfl⟩⟩
    simp only [QuantumMaxCutEnergy.squaredNorm, Complex.normSq_eq_norm_sq]
    have h1 : ∀ x : QuantumMaxCutEnergy.Basis G.n,
        ‖(if x = x0 then (1:ℂ) else 0)‖ ^ 2 = if x = x0 then (1:ℝ) else 0 := by
      intro x; by_cases h : x = x0 <;> simp [h]
    simp only [h1]
    rw [Finset.sum_eq_single x0]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine csSup_le hne ?_
  rintro v ⟨f, hf, rfl⟩
  exact QMCExtra.energy_le_two_mul G.weights f hf
