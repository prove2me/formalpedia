-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_contact_bounded_inverse
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T21:52:42.637113+00:00
-- url     : https://prove2.me/submissions/d6eeaefc-8d36-4552-a150-7765f4b4996e

import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_finite_contact_bezout_certificate
import Theorems.Thm_WeierstrassEllipticZeta_bounded_time_bezout_coefficients
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic.Ring

noncomputable section
open WeierstrassEllipticZeta

theorem solution
    (g₂ g₃ : ℂ) (c : Fin 2) (V : Finset (Fin 4 → ℂ)) (n : V → ℕ)
    (hpower : ∀ v : V, RingHom.ker (MvPolynomial.eval v.val) ^ n v ≤
      extensionChartContactIdeal g₂ g₃ c v.val (n v))
    (hcrt : ∀ p : V → MvPolynomial (Fin 4) ℂ,
      ∃ q : MvPolynomial (Fin 4) ℂ, ∀ v : V,
        q - p v ∈ extensionChartContactIdeal g₂ g₃ c v.val (n v))
    (M : Polynomial ℂ) (hM : M.Monic) (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ↔
        M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f)
    (q : MvPolynomial (Fin 4) ℂ)
    (hq : ∀ v : V, 0 < n v → MvPolynomial.eval v.val q ≠ 0) :
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    ∃ b : Polynomial ℂ,
      b.degree < (M.natDegree : ℕ) ∧
      (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) b).totalDegree ≤
        M.natDegree - 1 ∧
      1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I ∧
      (1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q).totalDegree ≤
        M.natDegree - 1 + q.totalDegree ∧
      (∀ b' : Polynomial ℂ, b'.degree < (M.natDegree : ℕ) →
        1 - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b' * q ∈ I → b' = b) ∧
      (∀ f : MvPolynomial (Fin 4) ℂ, f * q ∈ I ↔ f ∈ I) ∧
      I ⊔ Ideal.span {q} = ⊤ := by
  classical
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hE : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  have hEapp (p : Polynomial ℂ) : φ (E p) = p := AlgHom.congr_fun hE p
  obtain ⟨a, ha, htop⟩ := elliptic_extension_finite_contact_bezout_certificate
    g₂ g₃ c V n hpower hcrt 1 (fun _ => q) (fun v hn => ⟨0, hq v hn⟩)
  obtain ⟨b, hb, hcert, hdegree⟩ := bounded_time_bezout_coefficients
    I M.natDegree M hM (Polynomial.degree_eq_natDegree hM.ne_zero) r hmem
    1 (fun _ => q) a ha
  have hc : 1 - E (b 0) * q ∈ I := by
    simpa only [Fin.sum_univ_one] using hcert
  have hcancel (f : MvPolynomial (Fin 4) ℂ) : f * q ∈ I ↔ f ∈ I := by
    refine ⟨fun hf => ?_, fun hf => Ideal.mul_mem_right _ _ hf⟩
    have heq : f = f * (1 - E (b 0) * q) + E (b 0) * (f * q) := by ring
    rw [heq]
    exact I.add_mem (Ideal.mul_mem_left _ _ hc) (Ideal.mul_mem_left _ _ hf)
  refine ⟨b 0, (hb 0).1, (hb 0).2.1, hc, ?_, ?_, hcancel, ?_⟩
  · simpa only [Fin.sum_univ_one] using hdegree q.totalDegree (fun _ => le_rfl)
  · intro b' hb' hc'
    have hdiff : (E b' - E (b 0)) * q ∈ I := by
      convert I.sub_mem hc hc' using 1
      ring
    have hdvd : M ∣ b' - b 0 := by
      have h := (hmem _).mp ((hcancel _).mp hdiff)
      change M ∣ φ (E b' - E (b 0)) at h
      simpa only [map_sub, hEapp] using h
    have hsmall : (b' - b 0).degree < M.degree := by
      rw [Polynomial.degree_eq_natDegree hM.ne_zero]
      exact (Polynomial.degree_sub_le _ _).trans_lt (max_lt hb' (hb 0).1)
    exact sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hsmall)
  · simpa only [Set.range_const] using htop

