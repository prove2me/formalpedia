-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_residual_quotient_length
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T02:44:27.678573+00:00
-- url     : https://prove2.me/submissions/aed9af6e-4bdc-41f4-b97c-7ecf3afdca84

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Colon

noncomputable section


private lemma residual_divisibility (M q f : Polynomial ℂ) (hM : M ≠ 0) :
    M ∣ f * q ↔ M / gcd M q ∣ f := by
  have hg : gcd M q ≠ 0 := by
    simp only [ne_eq, gcd_eq_zero_iff]
    exact fun h => hM h.1
  have hfactor : M / gcd M q * gcd M q = M := by
    rw [mul_comm]
    exact EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left M q)
  constructor
  · intro h
    have hmul : M ∣ f * gcd M q := by
      obtain ⟨a, b, hab⟩ := exists_gcd_eq_mul_add_mul M q
      rw [hab, mul_add]
      apply dvd_add
      · exact dvd_mul_of_dvd_right (dvd_mul_right M a) f
      · simpa only [mul_assoc] using dvd_mul_of_dvd_left h b
    apply (mul_dvd_mul_iff_right hg).mp
    rwa [hfactor]
  · intro h
    have hmul := mul_dvd_mul h (gcd_dvd_right M q)
    rwa [hfactor] at hmul

theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M ≠ 0)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) :
    ∀ p : MvPolynomial (Fin 4) ℂ,
      let q := MvPolynomial.aeval (Fin.cons Polynomial.X r) p
      let G := M / gcd M q
      let J := I.colon {p}
      (∀ f : MvPolynomial (Fin 4) ℂ,
        f ∈ J ↔ G ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
      Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
        (Polynomial ℂ ⧸ Ideal.span {G})) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = G.natDegree ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) + (gcd M q).natDegree = M.natDegree := by
  classical
  intro p
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hE : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  have hsurj : Function.Surjective φ := fun q => ⟨E q, AlgHom.congr_fun hE q⟩
  let J := I.colon {p}
  let G := M / gcd M (φ p)
  have hg : gcd M (φ p) ≠ 0 := by
    simp only [ne_eq, gcd_eq_zero_iff]
    exact fun h => hM h.1
  have hfactor : G * gcd M (φ p) = M := by
    rw [mul_comm]
    exact EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left M (φ p))
  have hG : G ≠ 0 := by
    intro h
    apply hM
    rw [← hfactor, h, zero_mul]
  have hJ : ∀ f : MvPolynomial (Fin 4) ℂ, f ∈ J ↔ G ∣ φ f := by
    intro f
    rw [Submodule.mem_colon_singleton, smul_eq_mul, hI, map_mul]
    exact residual_divisibility M (φ p) (φ f) hM
  let ψ := (Ideal.Quotient.mkₐ ℂ (Ideal.span {G})).comp φ
  have hsurjψ : Function.Surjective ψ := (Ideal.Quotient.mkₐ_surjective ℂ _).comp hsurj
  have hkerψ : RingHom.ker ψ.toRingHom = J := by
    ext f
    change Ideal.Quotient.mk (Ideal.span {G}) (φ f) = 0 ↔ f ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact (hJ f).symm
  let e : (MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ] (Polynomial ℂ ⧸ Ideal.span {G}) :=
    (Ideal.quotientEquivAlgOfEq ℂ hkerψ.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurjψ)
  have : FiniteDimensional ℂ (Polynomial ℂ ⧸ Ideal.span {G}) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hG).basis
  have hfin : FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  have hdim : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = G.natDegree := by
    rw [e.toLinearEquiv.finrank_eq, finrank_quotient_span_eq_natDegree]
  refine ⟨hJ, ⟨e⟩, hfin, hdim, ?_⟩
  change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) + (gcd M (φ p)).natDegree = M.natDegree
  rw [hdim, ← Polynomial.natDegree_mul hG hg, hfactor]

