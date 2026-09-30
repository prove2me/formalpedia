-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_nilpotent_evaluation_kernel
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T01:26:14.475084+00:00
-- url     : https://prove2.me/submissions/03a2c587-eb52-44f8-951b-32f5882d6408

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_WeierstrassEllipticZeta_polynomial_nilpotent_root_order



theorem solution
    (K A : Type*) [Field K] [CommRing A]
    (φ : K →+* A) (x : A) (z : K) (d : ℕ) (hx : (x - φ z) ^ d = 0) :
    let n := nilpotencyClass (x - φ z)
    n ≤ d ∧
      (∀ q : Polynomial K, q.eval₂ φ x = 0 ↔
        (Polynomial.X - Polynomial.C z) ^ n ∣ q) ∧
      RingHom.ker (Polynomial.eval₂RingHom φ x) =
        Ideal.span ({(Polynomial.X - Polynomial.C z) ^ n} : Set (Polynomial K)) ∧
      ∃ f : (Polynomial K ⧸ Ideal.span {(Polynomial.X - Polynomial.C z) ^ n}) →+* A,
        Function.Injective f ∧ ∀ q : Polynomial K,
          f (Ideal.Quotient.mk (Ideal.span {(Polynomial.X - Polynomial.C z) ^ n}) q) =
            q.eval₂ φ x := by
  let n := nilpotencyClass (x - φ z)
  have hn : ∀ k : ℕ, (x - φ z) ^ k = 0 ↔ n ≤ k := by
    intro k
    exact ⟨fun h => Nat.sInf_le h,
      fun h => pow_eq_zero_of_le h (pow_nilpotencyClass ⟨d, hx⟩)⟩
  have hpoly : ∀ q : Polynomial K, q.eval₂ φ x = 0 ↔
      (Polynomial.X - Polynomial.C z) ^ n ∣ q := by
    intro q
    by_cases hq : q = 0
    · simp [hq]
    obtain ⟨u, hu, hpower, hbound⟩ :=
      WeierstrassEllipticZeta.polynomial_nilpotent_root_order K A φ x z d hx q hq
    calc
      q.eval₂ φ x = 0 ↔ (x - φ z) ^ q.rootMultiplicity z = 0 := by
        simpa only [pow_one, Nat.mul_one] using hpower 1
      _ ↔ n ≤ q.rootMultiplicity z := hn _
      _ ↔ (Polynomial.X - Polynomial.C z) ^ n ∣ q := Polynomial.le_rootMultiplicity_iff hq
  have hker : RingHom.ker (Polynomial.eval₂RingHom φ x) =
      Ideal.span ({(Polynomial.X - Polynomial.C z) ^ n} : Set (Polynomial K)) := by
    ext q
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    exact hpoly q
  refine ⟨(hn d).mp hx, hpoly, hker, ?_⟩
  let J : Ideal (Polynomial K) := Ideal.span {(Polynomial.X - Polynomial.C z) ^ n}
  have hJ : ∀ q : Polynomial K, q ∈ J → (Polynomial.eval₂RingHom φ x) q = 0 := by
    intro q hq
    exact (hpoly q).mpr (Ideal.mem_span_singleton.mp hq)
  refine ⟨Ideal.Quotient.lift J (Polynomial.eval₂RingHom φ x) hJ,
    RingHom.lift_injective_of_ker_le_ideal J hJ (le_of_eq hker), ?_⟩
  intro q
  rfl

