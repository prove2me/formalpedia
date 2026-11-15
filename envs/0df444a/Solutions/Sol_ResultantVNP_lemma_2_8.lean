-- Prove2me | solution 1 for ResultantVNP.lemma_2_8
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T12:39:45.71827+00:00
-- url     : https://prove2.me/submissions/fbfee15f-a3a2-461c-a9d2-d497d2544ebf

import Definitions.Def_ResultantVNP_tensorDet
import Definitions.Def_ResultantVNP_resOf
import Theorems.Thm_ResultantVNP_lemma_2_2
import Theorems.Thm_ResultantVNP_lemma_2_6_3

set_option maxHeartbeats 400000
open MvPolynomial ResultantVNP Finset

namespace TensorDetProperties

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



noncomputable def tensorCoeff (n : ℕ) (v : CoeffVar (fun _ : Fin n => 2)) :
    MvPolynomial (Fin n × Fin n × Fin n) ℤ := (tensorForm n v.1).coeff v.2.1

lemma tensorCoeff_formula (n : ℕ) (v : CoeffVar (fun _ : Fin n => 2)) :
    tensorCoeff n v = ∑ j : Fin n, ∑ k : Fin n,
      if Finsupp.single j 1 + Finsupp.single k 1 = v.2.1 then X (v.1,j,k) else 0 := by
  classical
  simp only [tensorCoeff,tensorForm,coeff_sum]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro k hk
  rw [mul_assoc,coeff_C_mul]
  have hx : (X j * X k : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n × Fin n) ℤ)).coeff v.2.1 =
      if Finsupp.single j 1 + Finsupp.single k 1 = v.2.1 then 1 else 0 := by
    simp only [X,monomial_mul,one_mul,coeff_monomial]
  rw [hx]
  split_ifs <;> simp

lemma homogeneous (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) :
    (tensorDet 𝓡 n).IsHomogeneous (n * 2 ^ (n-1)) := by
  classical
  have hcoeff (v : CoeffVar (fun _ : Fin n => 2)) : (tensorCoeff n v).IsHomogeneous 1 := by
    rw [tensorCoeff_formula]
    apply IsHomogeneous.sum
    intro j hj
    apply IsHomogeneous.sum
    intro k hk
    split_ifs
    · exact isHomogeneous_X ℤ _
    · exact isHomogeneous_zero _ _ _
  change (aeval (tensorCoeff n) (quadRes 𝓡 n)).IsHomogeneous _
  simpa only [one_mul] using
    ((lemma_2_2 𝓡 hn (fun _ : Fin n => 2) (by omega)).2.2.2).aeval (tensorCoeff n) hcoeff

def triplePerm {n : ℕ} (π : Equiv.Perm (Fin n)) (t : Fin n × Fin n × Fin n) :=
  (π t.1,π t.2.1,π t.2.2)

lemma tensorForm_equiv {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    rename π (map (rename (triplePerm π)).toRingHom (tensorForm n i)) = tensorForm n (π i) := by
  classical
  unfold tensorForm
  simp only [map_sum,map_mul,map_C,map_X,rename_C,rename_X]
  apply Fintype.sum_equiv π
  intro j
  apply Fintype.sum_equiv π
  intro k
  simp [triplePerm]

lemma tensorCoeff_equiv {n : ℕ} (π : Equiv.Perm (Fin n)) (v : CoeffVar (fun _ : Fin n => 2)) :
    rename (triplePerm π) (tensorCoeff n v) = tensorCoeff n (coeffEquiv 2 π v) := by
  change rename (triplePerm π) ((tensorForm n v.1).coeff v.2.1) =
    (tensorForm n (π v.1)).coeff (expEquiv π v.2.1)
  have h := congrArg (fun p : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n × Fin n) ℤ) =>
    p.coeff (Finsupp.mapDomain π v.2.1)) (tensorForm_equiv π v.1)
  rw [coeff_rename_mapDomain π π.injective,coeff_map] at h
  change _ = (tensorForm n (π v.1)).coeff (Finsupp.equivMapDomain π v.2.1)
  rw [Finsupp.equivMapDomain_eq_mapDomain]
  exact h

lemma invariant (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (π : Equiv.Perm (Fin n)) :
    rename (triplePerm π) (tensorDet 𝓡 n) = tensorDet 𝓡 n := by
  have hR : rename (coeffEquiv 2 π) (quadRes 𝓡 n) = quadRes 𝓡 n := by
    apply map_injective (Int.castRingHom ℂ) (by
      intro a b h
      have hc : (a : ℂ) = (b : ℂ) := by simpa only [Int.coe_castRingHom] using h
      exact_mod_cast hc)
    rw [map_rename]
    exact resultant_conjugate 𝓡 hn 2 (by omega) π
  change rename (triplePerm π) (aeval (tensorCoeff n) (quadRes 𝓡 n)) = _
  rw [comp_aeval_apply]
  have hfun : (fun v => rename (triplePerm π) (tensorCoeff n v)) = tensorCoeff n ∘ coeffEquiv 2 π :=
    funext (tensorCoeff_equiv π)
  rw [hfun,← aeval_rename,hR]
  rfl

noncomputable def evaluatedForm {n : ℕ} (A : Fin n × Fin n × Fin n → ℂ) (i : Fin n) :
    MvPolynomial (Fin n) ℂ := ∑ j,∑ k,C (A (i,j,k)) * X j * X k

lemma evaluatedForm_hom {n : ℕ} (A : Fin n × Fin n × Fin n → ℂ) (i : Fin n) :
    (evaluatedForm A i).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro j hj
  apply IsHomogeneous.sum
  intro k hk
  exact ((isHomogeneous_X ℂ j).C_mul _).mul (isHomogeneous_X ℂ k)

lemma eval_tensorDet (𝓡 : ResultantSystem) {n : ℕ} (A : Fin n × Fin n × Fin n → ℂ) :
    eval A (map (Int.castRingHom ℂ) (tensorDet 𝓡 n)) =
      resOf 𝓡 (fun _ : Fin n => 2) (evaluatedForm A) := by
  have hmap : map (Int.castRingHom ℂ) (tensorDet 𝓡 n) =
      aeval (fun v => map (Int.castRingHom ℂ) (tensorCoeff n v))
        (map (Int.castRingHom ℂ) (quadRes 𝓡 n)) :=
    map_bind₁ (Int.castRingHom ℂ) (tensorCoeff n) (quadRes 𝓡 n)
  rw [hmap]
  change aeval A (aeval _ _) = aeval _ _
  rw [comp_aeval_apply]
  congr 2
  funext v
  change eval A (map (Int.castRingHom ℂ) ((tensorForm n v.1).coeff v.2.1)) = _
  rw [← coeff_map,← coeff_map]
  congr 1
  simp [tensorForm,evaluatedForm,map_sum,map_mul]

lemma row_scaling (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (l : Fin n → ℂ)
    (f : Fin n → MvPolynomial (Fin n) ℂ) :
    resOf 𝓡 (fun _ : Fin n => 2) (fun i => C (l i) * f i) =
      (∏ i,l i ^ (2 ^ (n-1))) * resOf 𝓡 (fun _ : Fin n => 2) f := by
  classical
  let P := map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => 2))
  have hs (S : Finset (Fin n)) (c : CoeffVar (fun _ : Fin n => 2) → ℂ) :
      eval (fun v => if v.1 ∈ S then l v.1 * c v else c v) P =
        (∏ i ∈ S,l i ^ (2 ^ (n-1))) * eval c P := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      let cS : CoeffVar (fun _ : Fin n => 2) → ℂ := fun v => if v.1 ∈ S then l v.1 * c v else c v
      have hfun : (fun v : CoeffVar (fun _ : Fin n => 2) =>
          if v.1 ∈ insert i S then l v.1 * c v else c v) =
          fun v => if v.1 = i then l i * cS v else cS v := by
        funext v
        by_cases hv : v.1 = i <;> simp [cS,hv,hi]
      rw [hfun,(lemma_2_2 𝓡 hn (fun _ => 2) (by omega)).2.1 i (l i) cS]
      have hq : (∏ j ∈ univ.erase i, (2 : ℕ)) = 2 ^ (n-1) := by simp
      rw [hq,show eval cS P = _ from ih,prod_insert hi]
      ring
  simpa only [resOf,coeff_C_mul,mem_univ,ite_true,P] using
    hs univ (fun v => (f v.1).coeff v.2.1)

lemma scaling (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (l : Fin n → ℂ) (A : Fin n × Fin n × Fin n → ℂ) :
    eval (fun t => l t.1 * l t.2.1 * l t.2.2 * A t)
        (map (Int.castRingHom ℂ) (tensorDet 𝓡 n)) =
      (∏ i, l i ^ (3 * 2 ^ (n-1))) * eval A (map (Int.castRingHom ℂ) (tensorDet 𝓡 n)) := by
  classical
  let sub : Fin n → MvPolynomial (Fin n) ℂ := fun j => C (l j) * X j
  have hform : evaluatedForm (fun t => l t.1 * l t.2.1 * l t.2.2 * A t) =
      fun i => C (l i) * aeval sub (evaluatedForm A i) := by
    funext i
    unfold evaluatedForm
    simp only [map_sum,map_mul,aeval_C,aeval_X,mul_sum]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro k hk
    simp only [sub,map_mul,MvPolynomial.algebraMap_eq]
    ring
  have hdiag : (fun k : Fin n => ∑ j,C ((Matrix.diagonal l) k j) * X j) = sub := by
    funext k
    simp [Matrix.diagonal,sub,ite_mul,apply_ite]
  have hchange := lemma_2_6_3 𝓡 hn (fun _ : Fin n => 2) (by omega)
    (evaluatedForm A) (evaluatedForm_hom A) (Matrix.diagonal l)
  rw [hdiag,Matrix.det_diagonal] at hchange
  simp only [prod_const,card_univ,Fintype.card_fin] at hchange
  rw [eval_tensorDet,eval_tensorDet,hform,row_scaling 𝓡 hn l,hchange,← mul_assoc]
  congr 1
  rw [← prod_pow,← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  rw [← pow_add]
  congr 1
  have hn' : n = (n-1)+1 := by omega
  conv_lhs => rhs; rw [hn',pow_succ]
  omega

end TensorDetProperties

theorem solution (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) :
    (tensorDet 𝓡 n).IsHomogeneous (n * 2 ^ (n - 1)) ∧
    (∀ π : Equiv.Perm (Fin n),
        MvPolynomial.rename (fun t : Fin n × Fin n × Fin n => (π t.1, π t.2.1, π t.2.2))
          (tensorDet 𝓡 n) = tensorDet 𝓡 n) ∧
    (∀ (l : Fin n → ℂ) (A : Fin n × Fin n × Fin n → ℂ),
        MvPolynomial.eval (fun t => l t.1 * l t.2.1 * l t.2.2 * A t)
            (MvPolynomial.map (Int.castRingHom ℂ) (tensorDet 𝓡 n)) =
          (∏ i, l i ^ (3 * 2 ^ (n - 1))) *
            MvPolynomial.eval A (MvPolynomial.map (Int.castRingHom ℂ) (tensorDet 𝓡 n))) := by
  exact ⟨TensorDetProperties.homogeneous 𝓡 hn,TensorDetProperties.invariant 𝓡 hn,
    TensorDetProperties.scaling 𝓡 hn⟩

#print axioms solution
