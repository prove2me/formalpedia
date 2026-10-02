-- Prove2me | solution 1 for ThornStringBits.cycLaplacian_hasEigenvalue_fourier
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T12:30:14.914063+00:00
-- url     : https://prove2.me/submissions/7000e955-33be-4a0d-8f34-6e97d6215cec

import Definitions.Def_ThornStringBits_Defs
import Mathlib

set_option autoImplicit false

open Real Matrix

namespace ThornStringBits

open ZMod in
lemma p2m6_cos (N : ℕ) [NeZero N] (k : ℕ) :
    (stdAddChar (k : ZMod N) : ℂ) + stdAddChar (-(k : ZMod N))
      = ((2 * Real.cos (2 * π * (k : ℝ) / (N : ℝ)) : ℝ) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, stdAddChar_apply, toCircle_natCast]
  have e : (2 * ↑π * Complex.I * ↑k / ↑N : ℂ)
      = ((2 * π * (k : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos]
  ring_nf

lemma p2m6_mulVec (n : ℕ) (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (cycLaplacian (n + 1) *ᵥ x) i = 2 * x i - x (i + 1) - x (i - 1) := by
  have h1 : ∀ j : Fin (n + 1), (j.val = (i.val + 1) % (n + 1)) ↔ j = i + 1 := by
    intro j
    rw [Fin.ext_iff, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have h2 : ∀ j : Fin (n + 1), (i.val = (j.val + 1) % (n + 1)) ↔ j = i - 1 := by
    intro j
    rw [eq_sub_iff_add_eq, Fin.ext_iff, Fin.val_add, Fin.val_one', Nat.add_mod_mod, eq_comm]
  simp only [mulVec, dotProduct, cycLaplacian, h1, h2, sub_mul, ite_mul, zero_mul, one_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open ZMod in
theorem p2m6_main (M : ℕ) (hM : 1 ≤ M) (k : ℕ) :
    Module.End.HasEigenvalue (Matrix.toLin' (cycLaplacian M))
      (4 * Real.sin (π * k / M) ^ 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  set c : ℝ := 2 * Real.cos (2 * π * (k : ℝ) / ((n + 1 : ℕ) : ℝ)) with hcdef
  have hc := p2m6_cos (n + 1) k
  have hval : 4 * Real.sin (π * k / ((n + 1 : ℕ) : ℝ)) ^ 2 = 2 - c := by
    rw [hcdef]
    have : 2 * π * (k : ℝ) / ((n + 1 : ℕ) : ℝ) = 2 * (π * k / ((n + 1 : ℕ) : ℝ)) := by ring
    rw [this, Real.cos_two_mul, Real.cos_sq']
    ring
  rw [hval]
  let g : ZMod (n + 1) → ℝ := fun z => (stdAddChar (N := n + 1) (z * (k : ZMod (n + 1)))).re
  have key : ∀ z : ZMod (n + 1), g (z + 1) + g (z + -1) = g z * c := by
    intro z
    simp only [g]
    rw [add_mul, add_mul, one_mul, neg_one_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      ← Complex.add_re, ← mul_add, hc, Complex.re_mul_ofReal]
  let v : Fin (n + 1) → ℝ := fun j => g j
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    funext i
    rw [p2m6_mulVec]
    have hsum : v (i + 1) + v (i - 1) = v i * c := by
      rw [sub_eq_add_neg]
      exact key i
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith
  · intro h0
    have h1 : g 0 = 1 := by simp [g, AddChar.map_zero_eq_one]
    have h2 : v 0 = 0 := congrFun h0 0
    exact one_ne_zero (h1.symm.trans h2)

end ThornStringBits

open Real Matrix ThornStringBits in
theorem solution (M : ℕ) (hM : 1 ≤ M) (k : ℕ) :
    Module.End.HasEigenvalue (Matrix.toLin' (cycLaplacian M))
      (4 * Real.sin (π * k / M) ^ 2) := by
  exact ThornStringBits.p2m6_main M hM k
