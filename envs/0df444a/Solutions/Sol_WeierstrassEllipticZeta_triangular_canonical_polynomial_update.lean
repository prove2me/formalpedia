-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_canonical_polynomial_update
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T19:40:31.469631+00:00
-- url     : https://prove2.me/submissions/b8e4edbd-35ba-4b68-ae24-0667eff4f421

import Theorems.Thm_WeierstrassEllipticZeta_triangular_hypersurface_intersection_length
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section

open WeierstrassEllipticZeta

theorem solution
    (J : Ideal (MvPolynomial (Fin 4) ℂ)) (g : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hg : g.Monic)
    (hJ : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ J ↔ g ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) :
    ∀ p : MvPolynomial (Fin 4) ℂ,
      let h := gcd g (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
      let K := J ⊔ Ideal.span {p}
      h.Monic ∧ h ∣ g ∧
      (∀ f : MvPolynomial (Fin 4) ℂ,
        f ∈ K ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) = h.natDegree ∧
      h.natDegree ≤ g.natDegree ∧
      (h = g ↔ p ∈ J) ∧
      (h.natDegree < g.natDegree ↔ p ∉ J) ∧
      (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ K) <
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ↔ p ∉ J) ∧
      (∀ q : Polynomial ℂ, q.Monic →
        (∀ f : MvPolynomial (Fin 4) ℂ,
          f ∈ K ↔ q ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → q = h) := by
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
  have hsurj : Function.Surjective φ := fun q => ⟨E q, hE q⟩
  let h := gcd g (φ p)
  let K := J ⊔ Ideal.span {p}
  have hne : h ≠ 0 := by
    simp only [h, ne_eq, gcd_eq_zero_iff]
    exact fun heq => hg.ne_zero heq.1
  have hmonic : h.Monic := by
    rw [← Polynomial.normalize_eq_self_iff_monic hne]
    exact normalize_gcd g (φ p)
  have hdiv : h ∣ g := gcd_dvd_left g (φ p)
  have hcomapJ : J = Ideal.comap φ.toRingHom (Ideal.span {g}) := by
    ext f
    simpa only [Ideal.mem_comap, Ideal.mem_span_singleton, φ] using! hJ f
  have hmapJ : Ideal.map φ.toRingHom J = Ideal.span {g} := by
    rw [hcomapJ]
    exact Ideal.map_comap_of_surjective _ hsurj _
  have hker : RingHom.ker φ.toRingHom ≤ J := by
    rw [hcomapJ]
    exact Ideal.ker_le_comap _
  have hmapK : Ideal.map φ.toRingHom K = Ideal.span {h} := by
    rw [Ideal.map_sup, hmapJ, Ideal.map_span, Set.image_singleton]
    rw [← Ideal.span_insert, ← span_gcd]
    rfl
  have hcomapK : K = Ideal.comap φ.toRingHom (Ideal.span {h}) := by
    rw [← hmapK]
    exact ((Ideal.comap_map_of_surjective' φ.toRingHom hsurj K).trans
      (sup_of_le_left (hker.trans le_sup_left))).symm
  have hmem (f : MvPolynomial (Fin 4) ℂ) : f ∈ K ↔ h ∣ φ f := by
    rw [hcomapK, Ideal.mem_comap, Ideal.mem_span_singleton]
    rfl
  obtain ⟨_, hfinite, hlength, _, _⟩ :=
    triangular_hypersurface_intersection_length J g r hg.ne_zero hJ p
  have hdegree : h.natDegree ≤ g.natDegree :=
    Polynomial.natDegree_le_of_dvd hdiv hg.ne_zero
  have hlengthJ : Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = g.natDegree := by
    have hzero := (triangular_hypersurface_intersection_length J g r hg.ne_zero hJ 0).2.2.1
    change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J ⊔ Ideal.span {0}) =
      (gcd g (φ 0)).natDegree at hzero
    rw [Ideal.span_singleton_zero, sup_bot_eq] at hzero
    simpa only [map_zero, gcd_zero_right,
      hg.normalize_eq_self] using hzero
  have hsame : h = g ↔ p ∈ J :=
    (gcd_eq_left_iff g (φ p) hg.normalize_eq_self).trans (hJ p).symm
  have hstrict : h.natDegree < g.natDegree ↔ p ∉ J := by
    constructor
    · intro hlt hp
      rw [hsame.mpr hp] at hlt
      exact (lt_irrefl _ hlt)
    · intro hp
      by_contra hnot
      have heq : g = h := Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        hmonic hg hdiv (Nat.le_of_not_gt hnot)
      exact hp (hsame.mp heq.symm)
  refine ⟨hmonic, hdiv, hmem, hfinite, hlength, hdegree, hsame, hstrict, ?_, ?_⟩
  · rw [hlength, hlengthJ]
    exact hstrict
  · intro q hq hother
    have hqh : q ∣ h := by
      have := (hother (E h)).mp ((hmem _).mpr (by rw [hE]))
      change q ∣ φ (E h) at this
      simpa only [hE] using this
    have hhq : h ∣ q := by
      have := (hmem (E q)).mp ((hother _).mpr (by change q ∣ φ (E q); rw [hE]))
      simpa only [hE] using this
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic hq hhq
      (Polynomial.natDegree_le_of_dvd hqh hne)

