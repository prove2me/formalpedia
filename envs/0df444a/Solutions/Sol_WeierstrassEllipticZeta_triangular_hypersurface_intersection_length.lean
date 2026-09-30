-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_hypersurface_intersection_length
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T22:56:07.928501+00:00
-- url     : https://prove2.me/submissions/0d7c96b6-ad3b-42c9-954a-acd2e3a14b02

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section


theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M ≠ 0)
    (hI : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p) :
    ∀ p : MvPolynomial (Fin 4) ℂ,
      let q := MvPolynomial.aeval (Fin.cons Polynomial.X r) p
      let J := I ⊔ Ideal.span {p}
      Nonempty ((MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ]
        (Polynomial ℂ ⧸ Ideal.span {gcd M q})) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = (gcd M q).natDegree ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ M.natDegree ∧
      (q ≠ 0 → Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ≤ q.natDegree) := by
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
  have hcomap : I = Ideal.comap φ.toRingHom (Ideal.span {M}) := by
    ext q
    simpa only [Ideal.mem_comap, Ideal.mem_span_singleton, φ] using! hI q
  have hmap : Ideal.map φ.toRingHom I = Ideal.span {M} := by
    rw [hcomap]
    exact Ideal.map_comap_of_surjective _ hsurj _
  have hker : RingHom.ker φ.toRingHom ≤ I := by
    rw [hcomap]
    exact Ideal.ker_le_comap _
  let J := I ⊔ Ideal.span {p}
  let G := gcd M (φ p)
  have hG : G ≠ 0 := by
    simp only [G, ne_eq, gcd_eq_zero_iff]
    exact fun h => hM h.1
  have hmapJ : Ideal.map φ.toRingHom J = Ideal.span {G} := by
    rw [Ideal.map_sup, hmap, Ideal.map_span, Set.image_singleton]
    rw [← Ideal.span_insert, ← span_gcd]
    rfl
  let ψ := (Ideal.Quotient.mkₐ ℂ (Ideal.span {G})).comp φ
  have hsurjψ : Function.Surjective ψ := (Ideal.Quotient.mkₐ_surjective ℂ _).comp hsurj
  have hkerψ : RingHom.ker ψ.toRingHom = J := by
    have heq : RingHom.ker ψ.toRingHom = Ideal.comap φ.toRingHom (Ideal.span {G}) := by
      ext q
      change Ideal.Quotient.mk (Ideal.span {G}) (φ q) = 0 ↔ φ q ∈ Ideal.span {G}
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [heq, ← hmapJ]
    exact (Ideal.comap_map_of_surjective' φ.toRingHom hsurj J).trans
      (sup_of_le_left (hker.trans le_sup_left))
  let e : (MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ] (Polynomial ℂ ⧸ Ideal.span {G}) :=
    (Ideal.quotientEquivAlgOfEq ℂ hkerψ.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurjψ)
  have : FiniteDimensional ℂ (Polynomial ℂ ⧸ Ideal.span {G}) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hG).basis
  have hfin : FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  have hdim : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = G.natDegree := by
    rw [e.toLinearEquiv.finrank_eq, finrank_quotient_span_eq_natDegree]
  refine ⟨⟨e⟩, hfin, hdim, ?_, ?_⟩
  · rw [hdim]
    exact Polynomial.natDegree_le_of_dvd (gcd_dvd_left M (φ p)) hM
  · intro hq
    rw [hdim]
    exact Polynomial.natDegree_le_of_dvd (gcd_dvd_right M (φ p)) hq

