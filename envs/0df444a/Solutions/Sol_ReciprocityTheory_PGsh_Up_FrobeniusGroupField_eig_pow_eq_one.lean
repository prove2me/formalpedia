-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.eig_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:00:01.059668+00:00
-- url     : https://prove2.me/submissions/e53de846-2448-4ec7-b77d-435214bba63b

import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem
import Definitions.Def_ReciprocityTheory_DualLattices_EigPowEqOne
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_smul_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (hv : v.Integers R) {p : ℕ} [Fact p.Prime] {n : Type} [Fintype n] [DecidableEq n]
    [Algebra ℤ_[p] R] (N : Matrix n n ℤ_[p]) (e : Matrix n n R) (he : e ≠ 0) (x : R)
    (h : N.map (algebraMap ℤ_[p] R) * e = x • e) {m : ℕ} (hN : N ^ m = 1) : x ^ m = 1 := by
  have hpow : ∀ k : ℕ, (N.map (algebraMap ℤ_[p] R)) ^ k * e = x ^ k • e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, h, Matrix.mul_smul, ih, smul_smul, ← pow_succ']
  have hN' : (N.map (algebraMap ℤ_[p] R)) ^ m = 1 := by
    have := congrArg (algebraMap ℤ_[p] R).mapMatrix hN
    rwa [map_pow, map_one, RingHom.mapMatrix_apply] at this
  have h1 := hpow m
  rw [hN', one_mul] at h1
  exact (smul_cancel hv he (by rw [one_smul]; exact h1)).symm
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
