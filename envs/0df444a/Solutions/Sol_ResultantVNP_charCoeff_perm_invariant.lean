-- Prove2me | solution 1 for ResultantVNP.charCoeff_perm_invariant
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T09:43:56.278923+00:00
-- url     : https://prove2.me/submissions/19657bf5-32ad-40cf-bb9d-96e77dea80a7

import Mathlib
import Definitions.Def_ResultantVNP_resOf
import Definitions.Def_ResultantVNP_charCoeff

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CharCoeffProof

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


private def tripleMap (n : ℕ) (t : Fin n × Fin n × Fin n) : Sym (Fin n) 3 :=
  t.1 ::ₛ t.2.1 ::ₛ t.2.2 ::ₛ Sym.nil

private noncomputable def symForm (n : ℕ) (i : Fin n) :
    MvPolynomial (Fin n) (MvPolynomial (Sym (Fin n) 3) ℤ) :=
  ∑ j : Fin n, ∑ k : Fin n,
    C (X (tripleMap n (i, j, k))) * X j * X k

private noncomputable def symCoeff (n : ℕ) (v : CoeffVar (fun _ : Fin n => 2)) :
    MvPolynomial (Sym (Fin n) 3) ℤ := (symForm n v.1).coeff v.2.1

private lemma symForm_map (n : ℕ) (i : Fin n) :
    map (rename (tripleMap n)).toRingHom (tensorForm n i) = symForm n i := by
  simp [tensorForm, symForm, tripleMap, map_sum, map_mul]

private lemma symDet_aeval (𝓡 : ResultantSystem) (n : ℕ) :
    symTensorDet 𝓡 n = aeval (symCoeff n) (quadRes 𝓡 n) := by
  change rename (tripleMap n)
    (aeval (fun v : CoeffVar (fun _ : Fin n => 2) => (tensorForm n v.1).coeff v.2.1)
      (quadRes 𝓡 n)) = _
  rw [comp_aeval_apply]
  apply congrArg (fun f : CoeffVar (fun _ : Fin n => 2) →
    MvPolynomial (Sym (Fin n) 3) ℤ => aeval f (quadRes 𝓡 n))
  funext v
  change (rename (tripleMap n)) ((tensorForm n v.1).coeff v.2.1) =
    (symForm n v.1).coeff v.2.1
  have h := coeff_map (rename (tripleMap n)).toRingHom (tensorForm n v.1) v.2.1
  rw [symForm_map] at h
  exact h.symm

private lemma symForm_equiv (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    rename σ (map (rename (Sym.map σ)).toRingHom (symForm n i)) =
      symForm n (σ i) := by
  classical
  unfold symForm
  simp only [map_sum, map_mul, map_C, map_X, rename_C, rename_X]
  apply Fintype.sum_equiv σ
  intro j
  apply Fintype.sum_equiv σ
  intro k
  simp [tripleMap, Sym.map_cons,
    show Sym.map σ (Sym.nil : Sym (Fin n) 0) = Sym.nil from Subsingleton.elim _ _]

private lemma symCoeff_equiv (n : ℕ) (σ : Equiv.Perm (Fin n))
    (v : CoeffVar (fun _ : Fin n => 2)) :
    rename (Sym.map σ) (symCoeff n v) = symCoeff n (coeffEquiv 2 σ v) := by
  change rename (Sym.map σ) ((symForm n v.1).coeff v.2.1) =
    (symForm n (σ v.1)).coeff (expEquiv σ v.2.1)
  have h := congrArg (fun p : MvPolynomial (Fin n) (MvPolynomial (Sym (Fin n) 3) ℤ) =>
    p.coeff (Finsupp.mapDomain σ v.2.1)) (symForm_equiv n σ v.1)
  rw [coeff_rename_mapDomain σ σ.injective, coeff_map] at h
  change _ = (symForm n (σ v.1)).coeff (Finsupp.equivMapDomain σ v.2.1)
  rw [Finsupp.equivMapDomain_eq_mapDomain]
  exact h

private lemma resultant_conjugate_int {n : ℕ} (𝓡 : ResultantSystem)
    (hn : 1 ≤ n) (e : ℕ) (he : 0 < e) (σ : Equiv.Perm (Fin n)) :
    rename (coeffEquiv e σ) (𝓡.res (fun _ : Fin n => e)) =
      𝓡.res (fun _ : Fin n => e) := by
  apply map_injective (Int.castRingHom ℂ) (by
    intro a b h
    have hc : (a : ℂ) = (b : ℂ) := by simpa only [Int.coe_castRingHom] using h
    exact_mod_cast hc)
  rw [map_rename]
  exact resultant_conjugate 𝓡 hn e he σ

private lemma symDet_invariant (𝓡 : ResultantSystem) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) : rename (Sym.map σ) (symTensorDet 𝓡 n) = symTensorDet 𝓡 n := by
  classical
  by_cases hn : 1 ≤ n
  · rw [symDet_aeval, comp_aeval_apply]
    have hfun : (fun v => rename (Sym.map σ) (symCoeff n v)) =
        symCoeff n ∘ coeffEquiv 2 σ := by
      funext v
      exact symCoeff_equiv n σ v
    rw [hfun, ← aeval_rename, quadRes, resultant_conjugate_int 𝓡 hn 2 (by omega) σ]
  · have hz : n = 0 := by omega
    subst n
    have hs : σ = Equiv.refl (Fin 0) := Subsingleton.elim _ _
    subst σ
    have hfun : Sym.map (Equiv.refl (Fin 0)) = (id : Sym (Fin 0) 3 → _) := by
      funext T
      simp
    rw [hfun, rename_id]
    rfl

private lemma sym_map_replicate {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    Sym.map σ (Sym.replicate 3 i) = Sym.replicate 3 (σ i) := by
  apply Sym.coe_injective
  simp [Sym.replicate]

private noncomputable def diagonalTriple (n : ℕ) (T : Sym (Fin n) 3) :
    MvPolynomial (Sym (Fin n) 3) ℤ :=
  if ∃ i, T = Sym.replicate 3 i then 1 else 0

private lemma diagonalTriple_equiv (n : ℕ) (σ : Equiv.Perm (Fin n))
    (T : Sym (Fin n) 3) :
    rename (Sym.map σ) (diagonalTriple n T) = diagonalTriple n (Sym.map σ T) := by
  classical
  have heq : (∃ i, Sym.map σ T = Sym.replicate 3 i) ↔
      ∃ i, T = Sym.replicate 3 i := by
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨σ.symm i, ?_⟩
      apply Sym.map_injective σ.injective 3
      rw [hi, sym_map_replicate, Equiv.apply_symm_apply]
    · rintro ⟨i, rfl⟩
      exact ⟨σ i, sym_map_replicate σ i⟩
  by_cases h : ∃ i, T = Sym.replicate 3 i <;> simp [diagonalTriple, heq, h]

private noncomputable def affine (n : ℕ) (T : Sym (Fin n) 3) :
    Polynomial (MvPolynomial (Sym (Fin n) 3) ℤ) :=
  Polynomial.C (diagonalTriple n T) + Polynomial.X * Polynomial.C (X T)

theorem charCoeff_invariant (𝓡 : ResultantSystem) (n s : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    rename (Sym.map σ) (charCoeff 𝓡 n s) = charCoeff 𝓡 n s := by
  let φ := Polynomial.mapAlgHom (rename (Sym.map σ) :
    MvPolynomial (Sym (Fin n) 3) ℤ →ₐ[ℤ] MvPolynomial (Sym (Fin n) 3) ℤ)
  have hF (T : Sym (Fin n) 3) : φ (affine n T) = affine n (Sym.map σ T) := by
    simp only [φ, Polynomial.coe_mapAlgHom, affine, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    change Polynomial.C (rename (Sym.map σ) (diagonalTriple n T)) +
      Polynomial.X * Polynomial.C (rename (Sym.map σ) (X T)) = _
    rw [diagonalTriple_equiv, rename_X]
  have hpoly : φ (aeval (affine n) (symTensorDet 𝓡 n)) =
      aeval (affine n) (symTensorDet 𝓡 n) := by
    rw [comp_aeval_apply]
    have hfun : (fun T => φ (affine n T)) = affine n ∘ Sym.map σ := by
      funext T
      exact hF T
    rw [hfun, ← aeval_rename, symDet_invariant]
  have hcoeff := congrArg (fun p => p.coeff s) hpoly
  rw [Polynomial.coeff_mapAlgHom_apply] at hcoeff
  exact hcoeff

end CharCoeffProof

theorem solution (𝓡 : ResultantVNP.ResultantSystem) (n s : ℕ)
    (π : Equiv.Perm (Fin n)) :
    MvPolynomial.rename (Sym.map π) (ResultantVNP.charCoeff 𝓡 n s) =
      ResultantVNP.charCoeff 𝓡 n s := CharCoeffProof.charCoeff_invariant 𝓡 n s π

#print axioms solution
