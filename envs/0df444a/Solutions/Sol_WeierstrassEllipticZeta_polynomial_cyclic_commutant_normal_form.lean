-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_cyclic_commutant_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T22:27:11.588116+00:00
-- url     : https://prove2.me/submissions/1214775e-1ff0-44d6-9296-b2a63a77f5e2

import Theorems.Thm_WeierstrassEllipticZeta_polynomial_cyclic_commutant
import Theorems.Thm_WeierstrassEllipticZeta_polynomial_monic_evaluation_normal_form



theorem solution
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (x : A) (m : Polynomial K) (hm : m.Monic)
    (hker : ∀ q : Polynomial K, q.eval₂ (algebraMap K A) x = 0 ↔ m ∣ q)
    (hx : Function.Surjective (fun q : Polynomial K => q.eval₂ (algebraMap K A) x))
    (T : A →ₗ[K] A) :
    (∀ a : A, T (x * a) = x * T a) ↔
      ∃! q : Polynomial K, q.degree < m.degree ∧
        T = Algebra.lmul K A (q.eval₂ (algebraMap K A) x) := by
  have hcomm := WeierstrassEllipticZeta.polynomial_cyclic_commutant K A x hx T
  have hnormal := (WeierstrassEllipticZeta.polynomial_monic_evaluation_normal_form K A
    (algebraMap K A) x m hm hker).1
  constructor
  · intro hT
    obtain ⟨b, hb, _⟩ := hcomm.mp hT
    obtain ⟨q, hq⟩ := hx b
    change q.eval₂ (algebraMap K A) x = b at hq
    refine ⟨q %ₘ m, ⟨(hnormal q).1, ?_⟩, ?_⟩
    · rw [(hnormal q).2.1, hq]
      exact hb
    · intro r hr
      apply (hnormal q).2.2 r hr.1
      have hval := Algebra.lmul_injective (hr.2.symm.trans hb)
      exact hval.trans hq.symm
  · rintro ⟨q, ⟨_, hq⟩, _⟩
    apply hcomm.mpr
    refine ⟨q.eval₂ (algebraMap K A) x, hq, ?_⟩
    intro b hb
    exact Algebra.lmul_injective (hb.symm.trans hq)

