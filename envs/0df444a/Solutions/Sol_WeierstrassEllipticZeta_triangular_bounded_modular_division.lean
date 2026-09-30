-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_bounded_modular_division
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T22:09:51.925049+00:00
-- url     : https://prove2.me/submissions/e256c2f7-3cf5-4380-8785-7406bd61def2

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

noncomputable section


private lemma modular_division_time_totalDegree (p : Polynomial ℂ) :
    (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) p).totalDegree ≤ p.natDegree := by
  classical
  rw [Polynomial.aeval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  rw [MvPolynomial.totalDegree_X_pow]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)

theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (hM : M.Monic) (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
    (q a : MvPolynomial (Fin 4) ℂ) (ha : 1 - a * q ∈ I) :
    ∃ T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
      (∀ p : MvPolynomial (Fin 4) ℂ,
        T p = (MvPolynomial.aeval (Fin.cons Polynomial.X r) (p * a)) %ₘ M ∧
        (T p).degree < (M.natDegree : ℕ) ∧
        (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (T p)).totalDegree ≤
          M.natDegree - 1 ∧
        p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q ∈ I ∧
        (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q).totalDegree ≤
          max p.totalDegree (M.natDegree - 1 + q.totalDegree) ∧
        (∀ b : Polynomial ℂ, b.degree < (M.natDegree : ℕ) →
          (p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I ↔ b = T p))) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ, T p = 0 ↔ p ∈ I) ∧
      (∀ T' : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ,
        (∀ p : MvPolynomial (Fin 4) ℂ, (T' p).degree < (M.natDegree : ℕ) ∧
          p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T' p) * q ∈ I) → T' = T) := by
  classical
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hE : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  have hEapp (b : Polynomial ℂ) : φ (E b) = b := AlgHom.congr_fun hE b
  let T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ :=
    { toFun := fun p => φ (p * a) %ₘ M
      map_add' := by
        intro p p'
        simp only [add_mul, map_add, Polynomial.add_modByMonic]
      map_smul' := by
        intro z p
        simp only [smul_mul_assoc, map_smul, Polynomial.smul_modByMonic, RingHom.id_apply] }
  have hsmall (p : MvPolynomial (Fin 4) ℂ) :
      (T p).degree < (M.natDegree : ℕ) ∧ (E (T p)).totalDegree ≤ M.natDegree - 1 := by
    have hd : (T p).degree < (M.natDegree : ℕ) := by
      change (φ (p * a) %ₘ M).degree < (M.natDegree : ℕ)
      simpa only [Polynomial.degree_eq_natDegree hM.ne_zero] using
        Polynomial.degree_modByMonic_lt (φ (p * a)) hM
    refine ⟨hd, (modular_division_time_totalDegree (T p)).trans ?_⟩
    by_cases hp : T p = 0
    · simp [hp]
    · exact Nat.le_sub_one_of_lt ((Polynomial.natDegree_lt_iff_degree_lt hp).mpr hd)
  have hcongr (p : MvPolynomial (Fin 4) ℂ) : p - E (T p) * q ∈ I := by
    have hrem : p * a - E (T p) ∈ I := by
      apply (hmem _).mpr
      change M ∣ φ (p * a - E (T p))
      rw [map_sub, hEapp]
      change M ∣ φ (p * a) - φ (p * a) %ₘ M
      rw [Polynomial.modByMonic_eq_sub_mul_div, sub_sub_cancel]
      exact dvd_mul_right _ _
    have heq : p - E (T p) * q = p * (1 - a * q) + (p * a - E (T p)) * q := by ring
    rw [heq]
    exact I.add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_right _ _ hrem)
  have hcancel (f : MvPolynomial (Fin 4) ℂ) (hf : f * q ∈ I) : f ∈ I := by
    have heq : f = f * (1 - a * q) + a * (f * q) := by ring
    rw [heq]
    exact I.add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hf)
  have hunique (p : MvPolynomial (Fin 4) ℂ) (b : Polynomial ℂ)
      (hb : b.degree < (M.natDegree : ℕ)) (hp : p - E b * q ∈ I) : b = T p := by
    have hdiff : (E b - E (T p)) * q ∈ I := by
      convert I.sub_mem (hcongr p) hp using 1
      ring
    have hdvd : M ∣ b - T p := by
      have h := (hmem _).mp (hcancel _ hdiff)
      change M ∣ φ (E b - E (T p)) at h
      simpa only [map_sub, hEapp] using h
    apply sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd ?_)
    rw [Polynomial.degree_eq_natDegree hM.ne_zero]
    exact (Polynomial.degree_sub_le _ _).trans_lt (max_lt hb (hsmall p).1)
  refine ⟨T, ?_, ?_, ?_⟩
  · intro p
    refine ⟨rfl, (hsmall p).1, (hsmall p).2, hcongr p, ?_, ?_⟩
    · change (p - E (T p) * q).totalDegree ≤ _
      rw [sub_eq_add_neg]
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le_max le_rfl
      simpa only [neg_one_smul] using
        (MvPolynomial.totalDegree_smul_le (-1 : ℂ) (E (T p) * q)).trans
          ((MvPolynomial.totalDegree_mul _ _).trans
            (Nat.add_le_add (hsmall p).2 le_rfl))
    · intro b hb
      exact ⟨hunique p b hb, fun h => h ▸ hcongr p⟩
  · intro p
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · simpa only [hp, map_zero, zero_mul, sub_zero] using hcongr p
    · exact (hunique p 0 (by simp) (by simpa only [map_zero, zero_mul, sub_zero] using hp)).symm
  · intro T' hT'
    apply LinearMap.ext
    intro p
    exact hunique p (T' p) (hT' p).1 (hT' p).2

