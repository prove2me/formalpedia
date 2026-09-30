-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_time_polynomial_factorization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T18:20:33.729722+00:00
-- url     : https://prove2.me/submissions/61818e93-4ff3-416a-b79b-5b2c3fcde1aa

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_ideal_structure
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_contact_quotient_dimension
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div

noncomputable section
open WeierstrassEllipticZeta

theorem solution (g₂ g₃ : ℂ) (c : Fin 2)
    (V : Finset (Fin 4 → ℂ)) (n : V → ℕ) (g : Polynomial ℂ) (hg : g.Monic)
    (htime : ∀ q : Polynomial ℂ,
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) q ∈
        (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ↔ g ∣ q)
    (hdegree : g.natDegree = Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v))) :
    g = (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ n v) ∧
      ∀ z : ℂ, g.eval z = 0 ↔ ∃ v : V, 0 < n v ∧ z = v.val 0 := by
  classical
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  let P : Polynomial ℂ := ∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ n v
  have hPmonic : P.Monic := Polynomial.monic_prod_of_monic _ _ fun v _ =>
    (Polynomial.monic_X_sub_C (v.val 0)).pow (n v)
  have hPdegree : P.natDegree = ∑ v : V, n v := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    simp [P, Polynomial.degree_prod, Polynomial.degree_pow]
  have hPmem : E P ∈ (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) := by
    apply (Submodule.mem_iInf _).mpr
    intro v
    have hker : MvPolynomial.X (0 : Fin 4) - MvPolynomial.C (v.val 0) ∈
        RingHom.ker (MvPolynomial.eval v.val) := by simp
    have hpower := (elliptic_extension_contact_ideal_structure g₂ g₃).2.2.1 c v.val (n v)
      (Ideal.pow_mem_pow hker (n v))
    have hfactor : E ((Polynomial.X - Polynomial.C (v.val 0)) ^ n v) ∈
        extensionChartContactIdeal g₂ g₃ c v.val (n v) := by
      simpa [E] using hpower
    have hdiv : (Polynomial.X - Polynomial.C (v.val 0)) ^ n v ∣ P :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ v)
    obtain ⟨q, hq⟩ := hdiv
    rw [hq, map_mul]
    exact Ideal.mul_mem_right _ _ hfactor
  have hdiv : g ∣ P := (htime P).mp hPmem
  have hsame : P.natDegree = g.natDegree := by
    rw [hPdegree, hdegree,
      (elliptic_extension_contact_quotient_dimension g₂ g₃ c V n).2.1]
  have heq : g = P :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hg hPmonic hdiv hsame.le).symm
  refine ⟨heq, ?_⟩
  intro z
  rw [heq]
  simp [P, Polynomial.eval_prod, Finset.prod_eq_zero_iff,
    sub_eq_zero, Nat.pos_iff_ne_zero, and_comm]

