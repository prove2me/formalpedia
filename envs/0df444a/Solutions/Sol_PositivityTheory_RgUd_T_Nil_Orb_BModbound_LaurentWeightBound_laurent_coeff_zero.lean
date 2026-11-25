-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound.laurent_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:36.497952+00:00
-- url     : https://prove2.me/submissions/81a8bc5a-450f-4521-afc0-18c86b29652c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_OrbitIntegrals_ModulusBounds_LaurentCoeffZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module Polynomial
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BModbound
open PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
variable {k : Type} [Field k] {n : ℕ}
namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
theorem _root_.solution [Infinite k] (M : Finset ℤ) (c : ℤ → k)
    (h : ∀ t : kˣ, ∑ m ∈ M, ((t ^ m : kˣ) : k) * c m = 0) : ∀ m ∈ M, c m = 0 := by
  classical
  set N : ℕ := ∑ m ∈ M, m.natAbs with hN
  have hle : ∀ m ∈ M, 0 ≤ m + N := by
    intro m hm
    have h1 : m.natAbs ≤ N := Finset.single_le_sum (f := fun m : ℤ => m.natAbs) (fun _ _ => Nat.zero_le _) hm
    have h2 : -(m.natAbs : ℤ) ≤ m := by
      rcases Int.natAbs_eq m with h | h <;> omega
    omega
  let e : ℤ → ℕ := fun m => (m + N).toNat
  let p : k[X] := ∑ m ∈ M, C (c m) * X ^ (e m)
  have heval : ∀ t : kˣ, p.eval (t : k) = 0 := by
    intro t
    have hx : ∀ m ∈ M, (t : k) ^ (e m) = (t : k) ^ N * ((t ^ m : kˣ) : k) := by
      intro m hm
      have h3 : ((e m : ℕ) : ℤ) = m + N := Int.toNat_of_nonneg (hle m hm)
      have h4 : (t ^ ((e m : ℕ) : ℤ) : kˣ) = t ^ (N : ℤ) * t ^ m := by
        rw [h3, ← _root_.zpow_add, add_comm]
      have h5 := congrArg (fun u : kˣ => (u : k)) h4
      simpa [zpow_natCast] using h5
    simp only [p, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.sum_congr rfl (fun m hm => by rw [hx m hm])]
    rw [show (∑ m ∈ M, c m * ((t : k) ^ N * ((t ^ m : kˣ) : k))) =
      (t : k) ^ N * ∑ m ∈ M, ((t ^ m : kˣ) : k) * c m by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun m _ => by ring)]
    rw [h t, mul_zero]
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinf : Set.Infinite ({0}ᶜ : Set k) := (Set.finite_singleton (0 : k)).infinite_compl
    refine hinf.mono ?_
    intro x hx
    have hx' : x ≠ 0 := hx
    exact heval (Units.mk0 x hx')
  intro m hm
  have hc := congrArg (fun q : k[X] => q.coeff (e m)) hp
  simp only [p, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single m] at hc
  · simpa using hc
  · intro b hb hbm
    have : e m ≠ e b := by
      intro heq
      have h3 : ((e m : ℕ) : ℤ) = m + N := Int.toNat_of_nonneg (hle m hm)
      have h4 : ((e b : ℕ) : ℤ) = b + N := Int.toNat_of_nonneg (hle b hb)
      apply hbm
      have : ((e m : ℕ) : ℤ) = ((e b : ℕ) : ℤ) := by rw [heq]
      omega
    simp [this]
  · intro h; exact absurd hm h
end PositivityTheory.RgUd.T.Nil.Orb.BModbound.LaurentWeightBound
