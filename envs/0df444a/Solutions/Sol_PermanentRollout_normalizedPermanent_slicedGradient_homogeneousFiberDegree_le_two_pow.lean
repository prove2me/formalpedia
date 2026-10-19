-- Prove2me | solution 1 for PermanentRollout.normalizedPermanent_slicedGradient_homogeneousFiberDegree_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/767d846a-dad1-4ca0-b203-7ab9f9eaf467

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_exists_normalized_permanent_slicedGradient_circuit
import Theorems.Thm_PermanentRollout_freeAffineCircuit_homogeneousFiberDegree_le_two_pow

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n m k : ℕ}
    (circuit : ArithmeticCircuit (Fin n × Fin n))
    (hpermanent : circuit.polynomial = permanent n)
    (substitution : (Fin n × Fin n) → FreeAffineInput (Fin m))
    (P : MvPolynomial (Fin m) ℂ)
    (c : ℂ) (hc : c ≠ 0)
    (hspecialization :
      MvPolynomial.aeval (fun ij => (substitution ij).polynomial)
          (permanent n) = MvPolynomial.C c * P)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (slicedGradientPolynomial P W A i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point
        (slicedGradientPolynomial P W A i) = 0) ↔ point = 0) :
    e ^ k ≤ 2 ^ (3 * circuit.size) := by
  obtain ⟨D, hcount, hpolynomials⟩ :=
    exists_normalized_permanent_slicedGradient_circuit
      circuit hpermanent substitution P c hc hspecialization W A
  have hexists (i : Fin k) :
      ∃ form : FreeAffineForm (Fin k),
        form.eval D.values = slicedGradientPolynomial P W A i := by
    have hmem : slicedGradientPolynomial P W A i ∈ D.polynomials := by
      rw [hpolynomials]
      exact List.mem_map.mpr ⟨i, by simp, rfl⟩
    change slicedGradientPolynomial P W A i ∈
      D.outputs.map (fun form => form.eval D.values) at hmem
    obtain ⟨form, _, hform⟩ := List.mem_map.mp hmem
    exact ⟨form, hform⟩
  choose forms hforms using hexists
  calc
    e ^ k ≤ 2 ^ D.multiplicationCount :=
      freeAffineCircuit_homogeneousFiberDegree_le_two_pow
        D forms (slicedGradientPolynomial P W A)
        e he hF hzero (fun _ => 0) hforms
    _ ≤ 2 ^ (3 * circuit.size) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hcount
end PermanentRollout
