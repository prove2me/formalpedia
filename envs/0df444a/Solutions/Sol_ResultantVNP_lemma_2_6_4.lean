-- Prove2me | solution 1 for ResultantVNP.lemma_2_6_4
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T09:35:58.484193+00:00
-- url     : https://prove2.me/submissions/e5177225-d9f6-49b7-b93d-fe6f855161bc

import Mathlib
import Definitions.Def_ResultantVNP_resOf

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ResultantPermutation

open MvPolynomial ResultantVNP

private lemma scalar_of_zeros {ι : Type} [Finite ι]
    {P Q : MvPolynomial ι ℂ} (hP : Irreducible P) (hQ : Irreducible Q)
    (hz : ∀ x : ι → ℂ, eval x P = 0 → eval x Q = 0) :
    ∃ a : ℂ, Q = C a * P := by
  let I : Ideal (MvPolynomial ι ℂ) := Ideal.span {P}
  letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hP.prime
  have hmem : Q ∈ vanishingIdeal ℂ (zeroLocus ℂ I) := by
    intro x hx
    rw [aeval_eq_eval]
    apply hz
    have hp := hx P (Ideal.subset_span (by simp : P ∈ ({P} : Set _)))
    simpa only [aeval_eq_eval] using hp
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hmem
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hmem
  have huunit : IsUnit u := (hQ.isUnit_or_isUnit hu).resolve_left hP.not_isUnit
  obtain ⟨a, _, ha⟩ := isUnit_iff_eq_C_of_isReduced.mp huunit
  exact ⟨a, by rw [hu, ha, mul_comm]⟩

private lemma normalized_unique {ι : Type} [Finite ι]
    {P Q : MvPolynomial ι ℂ} (hP : Irreducible P) (hQ : Irreducible Q)
    (hz : ∀ x : ι → ℂ, eval x P = 0 → eval x Q = 0)
    (x₀ : ι → ℂ) (h₀ : eval x₀ P = 1) (h₁ : eval x₀ Q = 1) : Q = P := by
  obtain ⟨a, ha⟩ := scalar_of_zeros hP hQ hz
  have h : a = 1 := by simpa [ha, h₀] using h₁
  simp [ha, h]

private noncomputable def expEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (Fin n →₀ ℕ) ≃ (Fin n →₀ ℕ) where
  toFun := Finsupp.equivMapDomain σ
  invFun := Finsupp.equivMapDomain σ.symm
  left_inv := by intro v; ext i; simp
  right_inv := by intro v; ext i; simp

private lemma expEquiv_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n →₀ ℕ)
    (i : Fin n) : expEquiv σ v i = v (σ.symm i) := by
  simp [expEquiv]

private lemma expEquiv_sum {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n →₀ ℕ) :
    ∑ i, expEquiv σ v i = ∑ i, v i := by
  simp only [expEquiv_apply]
  exact Equiv.sum_comp σ.symm (fun i => v i)

private noncomputable def blockEquiv {n : ℕ} (e : ℕ) (σ : Equiv.Perm (Fin n)) :
    {v : Fin n →₀ ℕ // ∑ i, v i = e} ≃ {v : Fin n →₀ ℕ // ∑ i, v i = e} :=
  (expEquiv σ).subtypeEquiv (by intro v; rw [expEquiv_sum])

private noncomputable def coeffEquiv {n : ℕ} (e : ℕ) (σ : Equiv.Perm (Fin n)) :
    CoeffVar (fun _ : Fin n => e) ≃ CoeffVar (fun _ : Fin n => e) where
  toFun v := ⟨σ v.1, blockEquiv e σ v.2⟩
  invFun v := ⟨σ.symm v.1, (blockEquiv e σ).symm v.2⟩
  left_inv := by intro v; simp
  right_inv := by intro v; simp

private noncomputable def equationEquiv {n : ℕ} (e : ℕ) (σ : Equiv.Perm (Fin n)) :
    CoeffVar (fun _ : Fin n => e) ≃ CoeffVar (fun _ : Fin n => e) where
  toFun v := ⟨σ v.1, v.2⟩
  invFun v := ⟨σ.symm v.1, v.2⟩
  left_inv := by intro v; simp
  right_inv := by intro v; simp

private lemma equation_form {n : ℕ} (e : ℕ) (σ : Equiv.Perm (Fin n))
    (c : CoeffVar (fun _ : Fin n => e) → ℂ) (i : Fin n) :
    form (fun _ => e) (c ∘ equationEquiv e σ) i = form (fun _ => e) c (σ i) := by
  rfl

private lemma equiv_form {n : ℕ} (e : ℕ) (σ : Equiv.Perm (Fin n))
    (c : CoeffVar (fun _ : Fin n => e) → ℂ) (i : Fin n) :
    rename σ (form (fun _ => e) (c ∘ coeffEquiv e σ) i) =
      form (fun _ => e) c (σ i) := by
  classical
  unfold form
  rw [map_sum]
  apply Fintype.sum_equiv (blockEquiv e σ)
  intro v
  rw [rename_monomial]
  congr 1
  simp [blockEquiv, expEquiv, Finsupp.equivMapDomain_eq_mapDomain]

private noncomputable def diagonal {n : ℕ} (e : ℕ)
    (v : CoeffVar (fun _ : Fin n => e)) : ℤ :=
  if v.2.1 = Finsupp.single v.1 e then 1 else 0

private lemma expEquiv_single {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) (e : ℕ) :
    expEquiv σ (Finsupp.single i e) = Finsupp.single (σ i) e := by
  classical
  ext j
  simp [expEquiv, Finsupp.single_apply, Equiv.eq_symm_apply]

private lemma diagonal_coeffEquiv {n : ℕ} (e : ℕ) (σ : Equiv.Perm (Fin n))
    (v : CoeffVar (fun _ : Fin n => e)) :
    diagonal e (coeffEquiv e σ v) = diagonal e v := by
  classical
  have heq : expEquiv σ v.2.1 = Finsupp.single (σ v.1) e ↔
      v.2.1 = Finsupp.single v.1 e := by
    rw [← expEquiv_single]
    exact (expEquiv σ).injective.eq_iff
  by_cases h : v.2.1 = Finsupp.single v.1 e
  · have h' := heq.mpr h
    simp [diagonal, coeffEquiv, blockEquiv, h, expEquiv_single]
  · have h' := heq.not.mpr h
    simp [diagonal, coeffEquiv, blockEquiv, h, h']

private lemma eval_cast {ι : Type} (p : MvPolynomial ι ℤ) (c : ι → ℤ) :
    eval (fun i => (c i : ℂ)) (map (Int.castRingHom ℂ) p) = (eval c p : ℂ) := by
  simpa only [Function.comp_def, Int.coe_castRingHom] using
    (map_eval (Int.castRingHom ℂ) c p).symm

private lemma resultant_conjugate {n : ℕ} (𝓡 : ResultantSystem)
    (hn : 1 ≤ n) (e : ℕ) (he : 0 < e) (σ : Equiv.Perm (Fin n)) :
    rename (coeffEquiv e σ)
      (map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => e))) =
      map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => e)) := by
  classical
  let P := map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => e))
  obtain ⟨hzero, hnorm, hirr⟩ := 𝓡.spec (fun _ : Fin n => e) hn (fun _ => he)
  have hQ : Irreducible (rename (coeffEquiv e σ) P) :=
    hirr.map (renameEquiv ℂ (coeffEquiv e σ)).toMulEquiv
  have hdiag : eval (fun v => (diagonal e v : ℂ)) P = 1 := by
    rw [eval_cast]
    have h : eval (diagonal e) (𝓡.res (fun _ : Fin n => e)) = 1 := by
      convert hnorm using 1
      congr 2
    exact_mod_cast h
  apply normalized_unique hirr hQ ?_ (fun v => (diagonal e v : ℂ)) hdiag ?_
  · intro c hc
    rw [eval_rename]
    apply (hzero _).mpr
    obtain ⟨x, hx, hforms⟩ := (hzero c).mp hc
    refine ⟨x ∘ σ, ?_, ?_⟩
    · intro hz
      apply hx
      funext i
      have h := congrFun hz (σ.symm i)
      simpa [Function.comp_def] using h
    · intro i
      have h := congrArg (eval x) (equiv_form e σ c i)
      rw [eval_rename] at h
      exact h.trans (hforms (σ i))
  · rw [eval_rename]
    have hfun : (fun v => (diagonal e v : ℂ)) ∘ coeffEquiv e σ =
        (fun v => (diagonal e v : ℂ)) := by
      funext v
      simp [Function.comp_def, diagonal_coeffEquiv]
    rw [hfun]
    exact hdiag

private lemma integer_scalar {ι : Type} [Finite ι]
    (R : MvPolynomial ι ℤ) (ρ : Equiv.Perm ι)
    (hirr : Irreducible (map (Int.castRingHom ℂ) R))
    (c₀ : ι → ℤ) (hnorm : eval c₀ R = 1)
    (hz : ∀ c : ι → ℂ, eval c (map (Int.castRingHom ℂ) R) = 0 →
      eval (c ∘ ρ) (map (Int.castRingHom ℂ) R) = 0) :
    ∃ a : ℤ, rename ρ (map (Int.castRingHom ℂ) R) =
      C (a : ℂ) * map (Int.castRingHom ℂ) R := by
  have hQ : Irreducible (rename ρ (map (Int.castRingHom ℂ) R)) :=
    hirr.map (renameEquiv ℂ ρ).toMulEquiv
  obtain ⟨a, ha⟩ := scalar_of_zeros hirr hQ
    (by intro c hc; rw [eval_rename]; exact hz c hc)
  let b : ℤ := eval (c₀ ∘ ρ) R
  have hb : (b : ℂ) = a := by
    have h := congrArg (eval (fun v => (c₀ v : ℂ))) ha
    rw [eval_rename, map_mul, eval_C] at h
    simp only [Function.comp_def] at h
    rw [eval_cast, eval_cast, hnorm, Int.cast_one, mul_one] at h
    exact h
  exact ⟨b, by rw [hb]; exact ha⟩

private lemma equation_scalar {n : ℕ} (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (e : ℕ) (he : 0 < e) (σ : Equiv.Perm (Fin n)) :
    ∃ a : ℤ, rename (equationEquiv e σ)
      (map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => e))) =
      C (a : ℂ) * map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => e)) := by
  obtain ⟨hzero, hnorm, hirr⟩ := 𝓡.spec (fun _ : Fin n => e) hn (fun _ => he)
  apply integer_scalar _ (equationEquiv e σ) hirr (diagonal e) ?_ ?_
  · convert hnorm using 1
    congr 2
  · intro c hc
    obtain ⟨x, hx, hf⟩ := (hzero c).mp hc
    apply (hzero _).mpr
    exact ⟨x, hx, fun i => by rw [equation_form]; exact hf (σ i)⟩

private lemma equation_square {n : ℕ} (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (e : ℕ) (he : 0 < e) (σ : Equiv.Perm (Fin n)) :
    rename (equationEquiv e σ) (rename (equationEquiv e σ)
      (map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => e)))) =
      map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => e)) := by
  let P := map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => e))
  obtain ⟨a, ha⟩ := equation_scalar 𝓡 hn e he σ
  obtain ⟨b, hb⟩ := equation_scalar 𝓡 hn e he σ.symm
  have hcomp : rename (equationEquiv e σ) (rename (equationEquiv e σ.symm) P) = P := by
    rw [rename_rename]
    have hfun : (equationEquiv e σ) ∘ (equationEquiv e σ.symm) = id := by
      funext v
      simp [Function.comp_def, equationEquiv]
    rw [hfun, rename_id]
    rfl
  rw [hb, map_mul, rename_C, ha] at hcomp
  have hab : b * a = 1 := by
    have hnorm := (𝓡.spec (fun _ : Fin n => e) hn (fun _ => he)).2.1
    have hd : eval (diagonal e) (𝓡.res (fun _ : Fin n => e)) = 1 := by
      convert hnorm using 1
      congr 2
    have h := congrArg (eval (fun v => (diagonal e v : ℂ))) hcomp
    change eval _ (C (b : ℂ) * (C (a : ℂ) * P)) = eval _ P at h
    simp only [map_mul, eval_C] at h
    dsimp only [P] at h
    rw [eval_cast, hd] at h
    norm_cast at h
    simpa only [mul_one] using h
  have hua : IsUnit a := isUnit_of_dvd_one ⟨b, by simpa [mul_comm] using hab.symm⟩
  have haa : (a : ℂ) * (a : ℂ) = 1 := by
    rcases Int.isUnit_iff.mp hua with h | h <;> simp [h]
  rw [ha, map_mul, rename_C, ha, ← mul_assoc, ← map_mul, haa, map_one, one_mul]

private lemma resOf_conjugation {n : ℕ} (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (e : ℕ) (he : 0 < e) (σ : Equiv.Perm (Fin n))
    (f : Fin n → MvPolynomial (Fin n) ℂ) :
    resOf 𝓡 (fun _ => e) (fun i => rename σ (f (σ.symm i))) =
      resOf 𝓡 (fun _ => e) f := by
  unfold resOf
  conv_lhs => rw [← resultant_conjugate 𝓡 hn e he σ, eval_rename]
  congr 2
  funext v
  change (rename σ (f (σ.symm (σ v.1)))).coeff (expEquiv σ v.2.1) = _
  simp only [Equiv.symm_apply_apply]
  change (rename σ (f v.1)).coeff (Finsupp.equivMapDomain σ v.2.1) = _
  rw [Finsupp.equivMapDomain_eq_mapDomain]
  exact coeff_rename_mapDomain σ σ.injective (f v.1) v.2.1

private lemma resOf_equation_square {n : ℕ} (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (e : ℕ) (he : 0 < e) (σ : Equiv.Perm (Fin n))
    (f : Fin n → MvPolynomial (Fin n) ℂ) :
    resOf 𝓡 (fun _ => e) (fun i => f (σ (σ i))) = resOf 𝓡 (fun _ => e) f := by
  unfold resOf
  conv_rhs => rw [← equation_square 𝓡 hn e he σ, eval_rename, eval_rename]
  rfl

theorem simultaneous_permutation {n : ℕ} (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (e : ℕ) (he : 0 < e) (f : Fin n → MvPolynomial (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) :
    resOf 𝓡 (fun _ => e) (fun i => rename σ (f (σ i))) = resOf 𝓡 (fun _ => e) f := by
  have h := resOf_conjugation 𝓡 hn e he σ (fun i => f (σ (σ i)))
  simp only [Equiv.apply_symm_apply] at h
  exact h.trans (resOf_equation_square 𝓡 hn e he σ f)

end ResultantPermutation

theorem solution (𝓡 : ResultantVNP.ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (e : ℕ) (he : 0 < e) (f : Fin n → MvPolynomial (Fin n) ℂ)
    (_hf : ∀ i, (f i).IsHomogeneous e) (σ : Equiv.Perm (Fin n)) :
    ResultantVNP.resOf 𝓡 (fun _ => e) (fun i => MvPolynomial.rename σ (f (σ i))) =
      ResultantVNP.resOf 𝓡 (fun _ => e) f :=
  ResultantPermutation.simultaneous_permutation 𝓡 hn e he f σ

#print axioms solution
