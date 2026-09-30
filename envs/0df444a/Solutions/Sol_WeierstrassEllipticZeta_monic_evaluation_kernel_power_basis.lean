-- Prove2me | solution 1 for WeierstrassEllipticZeta.monic_evaluation_kernel_power_basis
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T14:55:53.442223+00:00
-- url     : https://prove2.me/submissions/775a37d2-165d-49da-81fc-a3051f4f0e2c

import Mathlib.RingTheory.Adjoin.PowerBasis



theorem solution
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (x : A) (m : Polynomial K) (hm : m.Monic)
    (hker : ∀ q : Polynomial K, q.eval₂ (algebraMap K A) x = 0 ↔ m ∣ q) :
    minpoly K x = m ∧
      (∃ b : PowerBasis K (Algebra.adjoin K ({x} : Set A)),
        (b.gen : A) = x ∧ b.dim = m.natDegree) ∧
      FiniteDimensional K (Algebra.adjoin K ({x} : Set A)) ∧
      Module.finrank K (Algebra.adjoin K ({x} : Set A)) = m.natDegree ∧
      LinearIndependent K (fun i : Fin m.natDegree => x ^ (i : ℕ)) := by
  have hroot : Polynomial.aeval x m = 0 := by
    simpa only [Polynomial.aeval_def] using (hker m).mpr dvd_rfl
  have hx : IsIntegral K x := ⟨m, hm, hroot⟩
  have hmin : minpoly K x = m := by
    symm
    apply minpoly.unique K x hm hroot
    intro q hq hrootq
    apply Polynomial.degree_le_of_dvd _ hq.ne_zero
    exact (hker q).mp (by simpa only [Polynomial.aeval_def] using hrootq)
  let b := Algebra.adjoin.powerBasis hx
  have hdim : b.dim = m.natDegree := by
    simpa only [b, Algebra.adjoin.powerBasis_dim] using congrArg Polynomial.natDegree hmin
  refine ⟨hmin, ⟨b, rfl, hdim⟩, b.finite, b.finrank.trans hdim, ?_⟩
  rw [← hmin]
  exact linearIndependent_pow x

