-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_residual_duality
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T11:59:58.921978+00:00
-- url     : https://prove2.me/submissions/249a592c-918b-4fcd-96c1-5a44cac70f9e

import Theorems.Thm_WeierstrassEllipticZeta_triangular_residual_quotient_length
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.Tactic.Ring

noncomputable section
open WeierstrassEllipticZeta

theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M ≠ 0)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) :
    ∀ p : MvPolynomial (Fin 4) ℂ,
      let J := I ⊔ Ideal.span {p}
      let R := I.colon {p}
      I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
      I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) = R := by
  classical
  intro p
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hsection : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  have hE (q : Polynomial ℂ) : φ (E q) = q := AlgHom.congr_fun hsection q
  let J := I ⊔ Ideal.span {p}
  let R := I.colon {p}
  have hIJ : I ≤ J := le_sup_left
  have hpJ : Ideal.span {p} ≤ J := le_sup_right
  let g := gcd M (φ p)
  let G := M / g
  have hg : g ≠ 0 := by
    simp only [g, ne_eq, gcd_eq_zero_iff]
    exact fun h => hM h.1
  have hfactor : G * g = M := by
    rw [mul_comm]
    exact EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left M (φ p))
  have hG : G ≠ 0 := by
    intro h
    apply hM
    rw [← hfactor, h, zero_mul]
  have hR : ∀ f : MvPolynomial (Fin 4) ℂ, f ∈ R ↔ G ∣ φ f :=
    (triangular_residual_quotient_length I M r hM hI p).1
  have hJ : ∀ f : MvPolynomial (Fin 4) ℂ, g ∣ φ f → f ∈ J := by
    intro f ⟨s, hs⟩
    obtain ⟨a, b, hab⟩ := exists_gcd_eq_mul_add_mul M (φ p)
    have hrem : f - p * E (b * s) ∈ I := by
      apply (hI _).mpr
      refine ⟨a * s, ?_⟩
      change φ (f - p * E (b * s)) = M * (a * s)
      rw [map_sub, map_mul, hE, hs]
      change gcd M (φ p) * s - φ p * (b * s) = M * (a * s)
      rw [hab]
      ring
    have hp : p * E (b * s) ∈ J :=
      hpJ (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton p)))
    simpa only [sub_add_cancel] using J.add_mem (hIJ hrem) hp
  constructor
  · apply le_antisymm
    · intro f hf
      have hEG : E G ∈ R := (hR _).mpr (by rw [hE])
      have hdiv : M ∣ φ f * G := by
        have hprod := (Submodule.mem_colon.mp hf) (E G) hEG
        have := (hI _).mp hprod
        change M ∣ φ (f * E G) at this
        simpa only [smul_eq_mul, map_mul, hE] using this
      apply hJ
      apply (mul_dvd_mul_iff_right hG).mp
      simpa only [mul_comm g G, hfactor] using hdiv
    · apply sup_le Ideal.le_colon
      apply Ideal.span_le.mpr
      intro q hq
      obtain rfl := Set.mem_singleton_iff.mp hq
      apply Submodule.mem_colon.mpr
      intro f hf
      simpa only [smul_eq_mul, mul_comm] using Submodule.mem_colon_singleton.mp hf
  · apply le_antisymm
    · intro f hf
      apply Submodule.mem_colon_singleton.mpr
      exact (Submodule.mem_colon.mp hf) p
        (hpJ (Ideal.subset_span (Set.mem_singleton p)))
    · intro f hf
      apply Submodule.mem_colon.mpr
      intro q hq
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hq
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hb
      rw [smul_eq_mul, mul_add, ← mul_assoc]
      apply I.add_mem (I.mul_mem_left f ha)
      exact I.mul_mem_right s (Submodule.mem_colon_singleton.mp hf)

