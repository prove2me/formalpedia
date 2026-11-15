-- Prove2me | solution 1 for ResultantVNP.lemma_2_6_2
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T10:02:39.22968+00:00
-- url     : https://prove2.me/submissions/b92a70c5-fe75-4871-8c13-ed0fdba82141

import Mathlib
import Definitions.Def_ResultantVNP_resOf

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LinearResultant

open MvPolynomial ResultantVNP
open scoped Matrix

private noncomputable def linearVar (n : ℕ) (i j : Fin n) : CoeffVar (fun _ : Fin n => 1) :=
  ⟨i, ⟨Finsupp.single j 1, by simp⟩⟩

private lemma single_injective {n : ℕ} {i j : Fin n}
    (h : (Finsupp.single i 1 : Fin n →₀ ℕ) = Finsupp.single j 1) : i = j := by
  classical
  by_contra hne
  have hh := congrArg (fun e => e i) h
  simp [Finsupp.single_apply, hne, Ne.symm hne] at hh

private lemma single_eq_iff {n : ℕ} (i j : Fin n) :
    (Finsupp.single i 1 : Fin n →₀ ℕ) = Finsupp.single j 1 ↔ i = j :=
  ⟨single_injective, fun h => by rw [h]⟩

private lemma linearVar_eq {n : ℕ} (i j k l : Fin n) :
    linearVar n i j = linearVar n k l ↔ i = k ∧ j = l := by
  constructor
  · intro h
    refine ⟨congrArg Sigma.fst h, ?_⟩
    exact single_injective (congrArg
      (fun v : CoeffVar (fun _ : Fin n => 1) => v.2.1) h)
  · rintro ⟨rfl, rfl⟩
    rfl

private lemma exists_single {n : ℕ} (v : Fin n →₀ ℕ) (hv : ∑ j, v j = 1) :
    ∃ j, v = Finsupp.single j 1 := by
  apply (Finsupp.sum_eq_one_iff v).mp
  change v.degree = 1
  rw [Finsupp.degree_eq_sum]
  exact hv

private noncomputable def exponentEquiv (n : ℕ) :
    Fin n ≃ {v : Fin n →₀ ℕ // ∑ j, v j = 1} :=
  Equiv.ofBijective (fun j => ⟨Finsupp.single j 1, by simp⟩) ⟨by
    intro i j h
    exact single_injective (congrArg Subtype.val h), by
    intro v
    obtain ⟨j, hj⟩ := exists_single v.1 v.2
    exact ⟨j, Subtype.ext hj.symm⟩⟩

private lemma form_linear {n : ℕ} (c : CoeffVar (fun _ : Fin n => 1) → ℂ) (i : Fin n) :
    form (fun _ => 1) c i = ∑ j : Fin n, C (c (linearVar n i j)) * X j := by
  classical
  unfold form
  symm
  apply Fintype.sum_equiv (exponentEquiv n)
  intro j
  change C (c (linearVar n i j)) * X j =
    monomial (Finsupp.single j 1) (c (linearVar n i j))
  simp [X, C_mul_monomial]

private noncomputable def genericMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (CoeffVar (fun _ : Fin n => 1)) ℂ) :=
  fun i j => X (linearVar n i j)

private noncomputable def detPoly (n : ℕ) :
    MvPolynomial (CoeffVar (fun _ : Fin n => 1)) ℂ := (genericMatrix n).det

private lemma eval_detPoly (n : ℕ) (c : CoeffVar (fun _ : Fin n => 1) → ℂ) :
    eval c (detPoly n) = Matrix.det (fun i j : Fin n => c (linearVar n i j)) := by
  rw [detPoly, Matrix.det_apply' (genericMatrix n),
    Matrix.det_apply' (fun i j : Fin n => c (linearVar n i j))]
  simp [genericMatrix, map_sum, map_prod]

private lemma form_mulVec (n : ℕ) (c : CoeffVar (fun _ : Fin n => 1) → ℂ)
    (x : Fin n → ℂ) (i : Fin n) :
    eval x (form (fun _ => 1) c i) =
      ((fun k j : Fin n => c (linearVar n k j)) *ᵥ x) i := by
  rw [form_linear]
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

private lemma det_degree (n : ℕ) (v : CoeffVar (fun _ : Fin n => 1)) :
    (detPoly n).degreeOf v ≤ 1 := by
  classical
  unfold detPoly
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply (degreeOf_sum_le v _ _).trans
  apply Finset.sup_le
  intro σ _
  apply (degreeOf_mul_le v _ _).trans
  have hc : degreeOf v ((Equiv.Perm.sign σ : ℤ) :
      MvPolynomial (CoeffVar (fun _ : Fin n => 1)) ℂ) = 0 := by
    rw [← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (CoeffVar (fun _ : Fin n => 1)) ℂ)]
    exact degreeOf_C _ _
  rw [hc, zero_add]
  apply (degreeOf_prod_le v _ _).trans
  calc
    (∑ k : Fin n, degreeOf v ((genericMatrix n).transpose (σ k) k)) ≤
        ∑ k : Fin n, if k = v.1 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases h : k = v.1
      · simp only [h, ite_true]
        simp [genericMatrix, Matrix.transpose_apply, degreeOf_X]
        split_ifs <;> omega
      · have hne : linearVar n k (σ k) ≠ v := by
          intro heq
          exact h (congrArg Sigma.fst heq)
        simp [genericMatrix, Matrix.transpose_apply, degreeOf_X, h, hne, Ne.symm hne]
    _ = 1 := by simp

private lemma dvd_of_zeros {ι : Type} [Finite ι]
    {P Q : MvPolynomial ι ℂ} (hP : Irreducible P)
    (hz : ∀ x : ι → ℂ, eval x P = 0 → eval x Q = 0) : P ∣ Q := by
  let I : Ideal (MvPolynomial ι ℂ) := Ideal.span {P}
  letI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hP.prime
  have hmem : Q ∈ vanishingIdeal ℂ (zeroLocus ℂ I) := by
    intro x hx
    rw [aeval_eq_eval]
    apply hz
    have hp := hx P (Ideal.subset_span (by simp : P ∈ ({P} : Set _)))
    simpa only [aeval_eq_eval] using hp
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hmem
  exact Ideal.mem_span_singleton.mp hmem

private lemma resultant_dvd_det (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) :
    map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => 1)) ∣ detPoly n := by
  obtain ⟨hzero, _, hirr⟩ := 𝓡.spec (fun _ : Fin n => 1) hn (by omega)
  apply dvd_of_zeros hirr
  intro c hc
  obtain ⟨x, hx, hf⟩ := (hzero c).mp hc
  rw [eval_detPoly]
  have hker : (fun k j : Fin n => c (linearVar n k j)) *ᵥ x = 0 := by
    funext i
    exact (form_mulVec n c x i).symm.trans (hf i)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hker
  simpa using hi

private noncomputable def permutationPoint (n : ℕ) (σ : Equiv.Perm (Fin n))
    (v : CoeffVar (fun _ : Fin n => 1)) : ℂ :=
  if v.2.1 = Finsupp.single (σ v.1) 1 then 1 else 0

private lemma permutation_coeff (n : ℕ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permutationPoint n σ (linearVar n i j) = if j = σ i then 1 else 0 := by
  classical
  simp [permutationPoint, linearVar, single_eq_iff]

private lemma permutation_form (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    form (fun _ => 1) (permutationPoint n σ) i = X (σ i) := by
  classical
  rw [form_linear]
  simp [permutation_coeff, apply_ite]

private lemma permutation_nonzero (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin n)) :
    eval (permutationPoint n σ)
      (map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => 1))) ≠ 0 := by
  intro hc
  obtain ⟨x, hx, hf⟩ := ((𝓡.spec (fun _ : Fin n => 1) hn (by omega)).1 _).mp hc
  apply hx
  funext j
  have h := hf (σ.symm j)
  rw [permutation_form, eval_X, Equiv.apply_symm_apply] at h
  exact h

private lemma resultant_degree_positive (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (i j : Fin n) :
    0 < (map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => 1))).degreeOf (linearVar n i j) := by
  classical
  let P := map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => 1))
  let σ := Equiv.swap i j
  let c₁ := permutationPoint n σ
  let c₀ : CoeffVar (fun _ : Fin n => 1) → ℂ :=
    fun v => if v = linearVar n i j then 0 else c₁ v
  have hσi : σ i = j := Equiv.swap_apply_left i j
  have hcoeff (k l : Fin n) :
      c₀ (linearVar n k l) = if k = i then 0 else if l = σ k then 1 else 0 := by
    dsimp only [c₀, c₁]
    simp only [linearVar_eq]
    by_cases hk : k = i
    · subst k
      by_cases hl : l = j <;> simp [hl, permutation_coeff, hσi]
    · simp [hk, permutation_coeff]
  have hform (k : Fin n) :
      form (fun _ => 1) c₀ k = if k = i then 0 else X (σ k) := by
    rw [form_linear]
    by_cases hk : k = i <;> simp [hcoeff, hk, apply_ite]
  have hzero : eval c₀ P = 0 := by
    apply ((𝓡.spec (fun _ : Fin n => 1) hn (by omega)).1 _).mpr
    refine ⟨Pi.single j 1, ?_, ?_⟩
    · intro h
      have hh := congrFun h j
      simpa using hh
    · intro k
      rw [hform]
      by_cases hk : k = i
      · simp [hk]
      · have hkj : σ k ≠ j := by
          intro heq
          exact hk (σ.injective (heq.trans hσi.symm))
        simp [hk, Pi.single_apply, hkj, Ne.symm hkj]
  have hnonzero : eval c₁ P ≠ 0 := permutation_nonzero 𝓡 hn σ
  by_contra hpos
  change ¬0 < P.degreeOf (linearVar n i j) at hpos
  have hdegree : P.degreeOf (linearVar n i j) = 0 := by omega
  have hnot : linearVar n i j ∉ P.vars := by
    rw [mem_vars_iff_degreeOf_ne_zero]
    simp [hdegree]
  have heval : eval c₁ P = eval c₀ P := by
    apply eval₂Hom_congr' rfl ?_ rfl
    intro v hv _
    have hvne : v ≠ linearVar n i j := by intro h; subst v; exact hnot hv
    simp [c₀, hvne]
  exact hnonzero (heval.trans hzero)

private lemma det_normalization (n : ℕ) :
    eval (permutationPoint n (Equiv.refl (Fin n))) (detPoly n) = 1 := by
  classical
  rw [eval_detPoly]
  have hM : (fun i j : Fin n => permutationPoint n (Equiv.refl (Fin n)) (linearVar n i j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    simp [permutation_coeff, Matrix.one_apply, eq_comm]
  rw [hM, Matrix.det_one]

private lemma resultant_normalization (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) :
    eval (permutationPoint n (Equiv.refl (Fin n)))
      (map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => 1))) = 1 := by
  classical
  have h := congrArg (Int.castRingHom ℂ)
    (𝓡.spec (fun _ : Fin n => 1) hn (by omega)).2.1
  rw [map_eval] at h
  simp only [map_one] at h
  convert h using 1
  congr 2
  funext v
  by_cases hv : v.2.1 = Finsupp.single v.1 1 <;>
    simp [permutationPoint, Function.comp_def, hv]

theorem polynomial_eq_det (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) :
    map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => 1)) = detPoly n := by
  classical
  let P := map (Int.castRingHom ℂ) (𝓡.res (fun _ : Fin n => 1))
  have hP : P ≠ 0 := (𝓡.spec (fun _ : Fin n => 1) hn (by omega)).2.2.ne_zero
  have hD : detPoly n ≠ 0 := by
    intro h
    have hh := congrArg (eval (permutationPoint n (Equiv.refl (Fin n)))) h
    rw [det_normalization, map_zero] at hh
    exact one_ne_zero hh
  obtain ⟨U, hU⟩ := resultant_dvd_det 𝓡 hn
  have hUne : U ≠ 0 := by intro h; rw [h, mul_zero] at hU; exact hD hU
  have hdegree (v : CoeffVar (fun _ : Fin n => 1)) : U.degreeOf v = 0 := by
    obtain ⟨i, v, hv⟩ := v
    obtain ⟨j, hj⟩ := exists_single v hv
    subst v
    have hp := resultant_degree_positive 𝓡 hn i j
    change 0 < P.degreeOf (linearVar n i j) at hp
    have hd := det_degree n (linearVar n i j)
    rw [hU, degreeOf_mul_eq hP hUne] at hd
    change P.degreeOf (linearVar n i j) + U.degreeOf (linearVar n i j) ≤ 1 at hd
    change U.degreeOf (linearVar n i j) = 0
    omega
  have hvars : U.vars = ∅ := by
    ext v
    simp [mem_vars_iff_degreeOf_ne_zero, hdegree]
  have hC := vars_eq_empty_iff_eq_C.mp hvars
  rw [hC] at hU
  have ha : U.coeff 0 = 1 := by
    have hh := congrArg (eval (permutationPoint n (Equiv.refl (Fin n)))) hU
    rw [det_normalization, map_mul, resultant_normalization 𝓡 hn, eval_C, one_mul] at hh
    exact hh.symm
  rw [ha, map_one, mul_one] at hU
  exact hU.symm

private lemma coeff_linear (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (∑ k : Fin n, C (A i k) * X k).coeff (Finsupp.single j 1) = A i j := by
  classical
  simp only [coeff_sum, coeff_C_mul, coeff_X, single_eq_iff]
  simp

theorem linear_resultant (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    resOf 𝓡 (fun _ => 1) (fun i => ∑ j, C (A i j) * X j) = A.det := by
  unfold resOf
  rw [polynomial_eq_det 𝓡 hn, eval_detPoly]
  congr 1
  ext i j
  exact coeff_linear n A i j

end LinearResultant

theorem solution (𝓡 : ResultantVNP.ResultantSystem) {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ResultantVNP.resOf 𝓡 (fun _ => 1)
      (fun i => ∑ j, MvPolynomial.C (A i j) * MvPolynomial.X j) = A.det :=
  LinearResultant.linear_resultant 𝓡 hn A

#print axioms solution
