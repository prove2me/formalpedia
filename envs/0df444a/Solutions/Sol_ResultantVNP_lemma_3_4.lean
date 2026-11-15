-- Prove2me | solution 1 for ResultantVNP.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T09:56:13.146199+00:00
-- url     : https://prove2.me/submissions/c8c2680f-d2d9-45c4-884e-2829c2bfa515

import Mathlib
import Definitions.Def_ResultantVNP_charCoeff

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace IndexHomogeneity

open MvPolynomial

private noncomputable def affine {σ : Type} (δ : σ → ℤ) (v : σ) :
    Polynomial (MvPolynomial σ ℤ) :=
  Polynomial.C (C (δ v)) + Polynomial.X * Polynomial.C (X v)

theorem coefficient_homogeneous {σ : Type} (δ : σ → ℤ) (p : MvPolynomial σ ℤ) :
    ∀ s, ((aeval (affine δ) p).coeff s).IsHomogeneous s := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    intro s
    have hc : aeval (affine δ) (C a) = (Polynomial.C (C a) : Polynomial (MvPolynomial σ ℤ)) := by
      simp
    rw [hc]
    cases s with
    | zero => simpa using isHomogeneous_C σ a
    | succ s =>
      rw [Polynomial.coeff_C]
      simp only [Nat.succ_ne_zero, ite_false]
      exact isHomogeneous_zero σ ℤ (s + 1)
  | add p q hp hq =>
    intro s
    rw [map_add, Polynomial.coeff_add]
    exact (hp s).add (hq s)
  | mul_X p v hp =>
    intro s
    rw [map_mul, aeval_X]
    change ((aeval (affine δ) p * (Polynomial.C (C (δ v)) +
      Polynomial.X * Polynomial.C (X v))).coeff s).IsHomogeneous s
    rw [mul_add, Polynomial.coeff_add, ← mul_assoc, Polynomial.coeff_mul_C,
      Polynomial.coeff_mul_C]
    apply IsHomogeneous.add
    · simpa only [add_zero] using (hp s).mul (isHomogeneous_C σ (δ v))
    · cases s with
      | zero => simp only [Polynomial.coeff_mul_X_zero, zero_mul]; exact isHomogeneous_zero σ ℤ 0
      | succ s =>
        rw [Polynomial.coeff_mul_X]
        exact (hp s).mul (isHomogeneous_X ℤ v)

theorem charCoeff_homogeneous (𝓡 : ResultantVNP.ResultantSystem) (n s : ℕ) :
    (ResultantVNP.charCoeff 𝓡 n s).IsHomogeneous s := by
  classical
  let δ : Sym (Fin n) 3 → ℤ := fun T => if ∃ i, T = Sym.replicate 3 i then 1 else 0
  have h := coefficient_homogeneous δ (ResultantVNP.symTensorDet 𝓡 n) s
  convert h using 2
  unfold ResultantVNP.charCoeff
  apply congrArg (fun f : Sym (Fin n) 3 → Polynomial (MvPolynomial (Sym (Fin n) 3) ℤ) =>
    (aeval f (ResultantVNP.symTensorDet 𝓡 n)).coeff s)
  funext T
  simp [affine, δ, apply_ite]

end IndexHomogeneity


namespace IndexOccurrences

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


private noncomputable def diagonal {n : ℕ} (e : ℕ)
    (v : CoeffVar (fun _ : Fin n => e)) : ℤ :=
  if v.2.1 = Finsupp.single v.1 e then 1 else 0


private lemma eval_cast {ι : Type} (p : MvPolynomial ι ℤ) (c : ι → ℤ) :
    eval (fun i => (c i : ℂ)) (map (Int.castRingHom ℂ) p) = (eval c p : ℂ) := by
  simpa only [Function.comp_def, Int.coe_castRingHom] using
    (map_eval (Int.castRingHom ℂ) c p).symm


private def weight {ι : Type} (w : ι → ℕ) (μ : ι →₀ ℕ) : ℕ :=
  μ.sum (fun i k => k * w i)

private noncomputable def scale {ι : Type} (ζ : ℂ) (w : ι → ℕ) :
    MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial ι ℂ :=
  aeval (fun i => C (ζ ^ w i) * X i)

private lemma scale_monomial {ι : Type} (ζ : ℂ) (w : ι → ℕ)
    (μ : ι →₀ ℕ) (a : ℂ) :
    scale ζ w (monomial μ a) = monomial μ (ζ ^ weight w μ * a) := by
  classical
  rw [scale, monomial_eq, map_mul, aeval_C]
  simp only [Finsupp.prod, map_prod, map_pow, aeval_X, mul_pow]
  rw [Finset.prod_mul_distrib]
  simp only [← map_pow, ← map_prod, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [monomial_eq]
  simp only [weight, Finsupp.sum, Finsupp.prod]
  have he : ∑ i ∈ μ.support, w i * μ i = ∑ i ∈ μ.support, μ i * w i := by
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.mul_comm _ _
  rw [he, map_mul]
  simp only [MvPolynomial.algebraMap_eq]
  ring

private lemma scale_coeff {ι : Type} (ζ : ℂ) (w : ι → ℕ)
    (p : MvPolynomial ι ℂ) (μ : ι →₀ ℕ) :
    (scale ζ w p).coeff μ = ζ ^ weight w μ * p.coeff μ := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, coeff_sum, scale_monomial, coeff_monomial]
  by_cases h : μ ∈ p.support
  · rw [Finset.sum_eq_single μ]
    · simp
    · intro ν _ hν
      simp [hν]
    · exact fun h' => (h' h).elim
  · simp only [mem_support_iff, not_not] at h
    rw [h, mul_zero]
    apply Finset.sum_eq_zero
    intro ν hν
    have hne : ν ≠ μ := by
      intro heq
      subst ν
      simpa [mem_support_iff, h] using hν
    simp [hne]

private lemma scale_comp {ι : Type} (ζ η : ℂ) (w : ι → ℕ) :
    (scale ζ w).comp (scale η w) = scale (η * ζ) w := by
  ext i
  simp [scale, mul_pow, mul_assoc, mul_left_comm, mul_comm]

private lemma scale_one {ι : Type} (w : ι → ℕ) :
    scale 1 w = AlgHom.id ℂ (MvPolynomial ι ℂ) := by
  ext i
  simp [scale]

private lemma scale_cube {ι : Type} (ζ : ℂ) (hz : ζ ^ 3 = 1) (w : ι → ℕ)
    (p : MvPolynomial ι ℂ) : scale ζ w (scale ζ w (scale ζ w p)) = p := by
  have hh : (scale ζ w).comp ((scale ζ w).comp (scale ζ w)) = AlgHom.id ℂ _ := by
    rw [scale_comp, scale_comp]
    have h : (ζ * ζ) * ζ = 1 := by
      calc
        (ζ * ζ) * ζ = ζ ^ 3 := by ring
        _ = 1 := hz
    rw [h, scale_one]
  exact AlgHom.congr_fun hh p

private noncomputable def scaleEquiv {ι : Type} (ζ : ℂ) (hz : ζ ^ 3 = 1)
    (w : ι → ℕ) : MvPolynomial ι ℂ ≃ₐ[ℂ] MvPolynomial ι ℂ :=
  AlgEquiv.ofBijective (scale ζ w) ⟨by
    intro p q h
    have hh := congrArg (fun r => scale ζ w (scale ζ w r)) h
    simpa only [scale_cube ζ hz] using hh,
    fun p => ⟨scale ζ w (scale ζ w p), scale_cube ζ hz w p⟩⟩

private lemma eval_scale {ι : Type} (ζ : ℂ) (w : ι → ℕ)
    (x : ι → ℂ) (p : MvPolynomial ι ℂ) :
    eval x (scale ζ w p) = eval (fun i => ζ ^ w i * x i) p := by
  change aeval x (scale ζ w p) = aeval _ p
  rw [scale, comp_aeval_apply]
  congr 2
  funext i
  simp

private def varWeight {n : ℕ} (i j : Fin n) : ℕ := if j = i then 1 else 0

private lemma weight_var {n : ℕ} (i : Fin n) (μ : Fin n →₀ ℕ) :
    weight (varWeight i) μ = μ i := by
  classical
  simp only [weight, varWeight, Finsupp.sum, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm

private def coeffWeight {n : ℕ} (i : Fin n) (v : CoeffVar (fun _ : Fin n => 2)) : ℕ :=
  varWeight i v.1 + v.2.1 i

private lemma form_scale {n : ℕ} (ζ : ℂ) (i k : Fin n)
    (c : CoeffVar (fun _ : Fin n => 2) → ℂ) :
    form (fun _ => 2) (fun v => ζ ^ coeffWeight i v * c v) k =
      C (ζ ^ varWeight i k) * scale ζ (varWeight i) (form (fun _ => 2) c k) := by
  classical
  unfold form
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [scale_monomial, C_mul_monomial, weight_var]
  simp [coeffWeight, pow_add, mul_assoc]

private lemma resultant_scale {n : ℕ} (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (ζ : ℂ) (hz : ζ ^ 3 = 1) (i : Fin n) :
    scale ζ (coeffWeight i) (map (Int.castRingHom ℂ) (quadRes 𝓡 n)) =
      map (Int.castRingHom ℂ) (quadRes 𝓡 n) := by
  classical
  let P := map (Int.castRingHom ℂ) (quadRes 𝓡 n)
  obtain ⟨hzero, hnorm, hirr⟩ := 𝓡.spec (fun _ : Fin n => 2) hn (by omega)
  have hz₀ : ζ ≠ 0 := by intro h; simp [h] at hz
  have hQ : Irreducible (scale ζ (coeffWeight i) P) :=
    hirr.map (scaleEquiv ζ hz (coeffWeight i)).toMulEquiv
  have hdiag : eval (fun v => (diagonal 2 v : ℂ)) P = 1 := by
    rw [eval_cast]
    have h : eval (diagonal 2) (𝓡.res (fun _ : Fin n => 2)) = 1 := by
      convert hnorm using 1
      congr 2
    exact_mod_cast h
  apply normalized_unique hirr hQ ?_ (fun v => (diagonal 2 v : ℂ)) hdiag ?_
  · intro c hc
    rw [eval_scale]
    obtain ⟨x, hx, hf⟩ := (hzero c).mp hc
    apply (hzero _).mpr
    let x' : Fin n → ℂ := fun j => ζ ^ (2 * varWeight i j) * x j
    have hpoint : (fun j => ζ ^ varWeight i j * x' j) = x := by
      funext j
      dsimp only [x']
      rw [← mul_assoc, ← pow_add]
      have hpower : ζ ^ (varWeight i j + 2 * varWeight i j) = 1 := by
        rw [show varWeight i j + 2 * varWeight i j = 3 * varWeight i j by omega,
          pow_mul, hz, one_pow]
      rw [hpower, one_mul]
    refine ⟨x', ?_, ?_⟩
    · intro hx'
      apply hx
      funext j
      have h := congrFun hx' j
      change ζ ^ (2 * varWeight i j) * x j = 0 at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hz₀)
    · intro k
      rw [form_scale, map_mul, eval_C, eval_scale, hpoint, hf k, mul_zero]
  · rw [eval_scale]
    have hfun : (fun v => ζ ^ coeffWeight i v * (diagonal 2 v : ℂ)) =
        (fun v => (diagonal 2 v : ℂ)) := by
      funext v
      by_cases hv : v.2.1 = Finsupp.single v.1 2
      · have hw : coeffWeight i v = 3 * varWeight i v.1 := by
          simp only [coeffWeight, hv, Finsupp.single_apply, varWeight]
          split_ifs <;> omega
        simp [diagonal, hv, hw, pow_mul, hz]
      · simp [diagonal, hv]
    rw [hfun]
    exact hdiag

private def tripleMap (n : ℕ) (t : Fin n × Fin n × Fin n) : Sym (Fin n) 3 :=
  t.1 ::ₛ t.2.1 ::ₛ t.2.2 ::ₛ Sym.nil

private noncomputable def symForm (n : ℕ) (i : Fin n) :
    MvPolynomial (Fin n) (MvPolynomial (Sym (Fin n) 3) ℤ) :=
  ∑ j : Fin n, ∑ k : Fin n,
    C (X (tripleMap n (i, j, k))) * X j * X k

private noncomputable def integerSymCoeff (n : ℕ) (v : CoeffVar (fun _ : Fin n => 2)) :
    MvPolynomial (Sym (Fin n) 3) ℤ := (symForm n v.1).coeff v.2.1

private lemma symForm_map (n : ℕ) (i : Fin n) :
    map (rename (tripleMap n)).toRingHom (tensorForm n i) = symForm n i := by
  simp [tensorForm, symForm, tripleMap, map_sum, map_mul]

private lemma symDet_aeval (𝓡 : ResultantSystem) (n : ℕ) :
    symTensorDet 𝓡 n = aeval (integerSymCoeff n) (quadRes 𝓡 n) := by
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


private noncomputable def symCoeff (n : ℕ) (v : CoeffVar (fun _ : Fin n => 2)) :
    MvPolynomial (Sym (Fin n) 3) ℂ := map (Int.castRingHom ℂ) (integerSymCoeff n v)

private lemma symDet_complex (𝓡 : ResultantSystem) (n : ℕ) :
    map (Int.castRingHom ℂ) (symTensorDet 𝓡 n) =
      aeval (symCoeff n) (map (Int.castRingHom ℂ) (quadRes 𝓡 n)) := by
  rw [symDet_aeval]
  exact map_bind₁ (Int.castRingHom ℂ) (integerSymCoeff n) (quadRes 𝓡 n)

private def tensorWeight {n : ℕ} (i : Fin n) (T : Sym (Fin n) 3) : ℕ :=
  Multiset.count i (T : Multiset (Fin n))

private lemma symCoeff_formula (n : ℕ) (v : CoeffVar (fun _ : Fin n => 2)) :
    symCoeff n v = ∑ j : Fin n, ∑ k : Fin n,
      if Finsupp.single j 1 + Finsupp.single k 1 = v.2.1 then
        X (tripleMap n (v.1, j, k)) else 0 := by
  classical
  simp only [symCoeff, integerSymCoeff, symForm, coeff_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_assoc, coeff_C_mul]
  have hx : (X j * X k : MvPolynomial (Fin n) (MvPolynomial (Sym (Fin n) 3) ℤ)).coeff v.2.1 =
      if Finsupp.single j 1 + Finsupp.single k 1 = v.2.1 then 1 else 0 := by
    simp only [X, monomial_mul, one_mul, coeff_monomial]
  rw [hx]
  by_cases h : Finsupp.single j 1 + Finsupp.single k 1 = v.2.1 <;> simp [h]

private lemma weight_triple {n : ℕ} (i : Fin n) (v : CoeffVar (fun _ : Fin n => 2))
    (j k : Fin n) (he : Finsupp.single j 1 + Finsupp.single k 1 = v.2.1) :
    tensorWeight i (tripleMap n (v.1, j, k)) = coeffWeight i v := by
  classical
  rw [tensorWeight, tripleMap, coeffWeight, ← he]
  simp only [Sym.coe_cons, Sym.coe_nil, Multiset.count_cons, Multiset.count_zero,
    Finsupp.add_apply, Finsupp.single_apply, varWeight]
  split_ifs <;> omega

private lemma scale_symCoeff (n : ℕ) (ζ : ℂ) (i : Fin n)
    (v : CoeffVar (fun _ : Fin n => 2)) :
    scale ζ (tensorWeight i) (symCoeff n v) = C (ζ ^ coeffWeight i v) * symCoeff n v := by
  classical
  rw [symCoeff_formula]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : Finsupp.single j 1 + Finsupp.single k 1 = v.2.1
  · simp only [if_pos h]
    simp only [scale, aeval_X]
    rw [weight_triple i v j k h]
  · simp [h]

private lemma symDet_scale {n : ℕ} (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (ζ : ℂ) (hz : ζ ^ 3 = 1) (i : Fin n) :
    scale ζ (tensorWeight i) (map (Int.castRingHom ℂ) (symTensorDet 𝓡 n)) =
      map (Int.castRingHom ℂ) (symTensorDet 𝓡 n) := by
  rw [symDet_complex, comp_aeval_apply]
  have hfun : (fun v => scale ζ (tensorWeight i) (symCoeff n v)) =
      (fun v => C (ζ ^ coeffWeight i v) * symCoeff n v) := by
    funext v
    exact scale_symCoeff n ζ i v
  rw [hfun]
  have hbind : aeval (symCoeff n)
      (scale ζ (coeffWeight i) (map (Int.castRingHom ℂ) (quadRes 𝓡 n))) =
      aeval (fun v => C (ζ ^ coeffWeight i v) * symCoeff n v)
        (map (Int.castRingHom ℂ) (quadRes 𝓡 n)) := by
    rw [scale, comp_aeval_apply]
    congr 2
    funext v
    simp
  rw [← hbind, resultant_scale 𝓡 hn ζ hz i]

private noncomputable def delta (n : ℕ) (T : Sym (Fin n) 3) : ℤ :=
  if ∃ j, T = Sym.replicate 3 j then 1 else 0

private noncomputable def affine {σ R : Type} [CommRing R] (δ : σ → ℤ) (T : σ) :
    Polynomial (MvPolynomial σ R) :=
  Polynomial.C (C (δ T : R)) + Polynomial.X * Polynomial.C (X T)

private lemma lift_charPoly {σ : Type} (δ : σ → ℤ) (p : MvPolynomial σ ℤ) :
    Polynomial.map (map (Int.castRingHom ℂ)) (aeval (affine (R := ℤ) δ) p) =
      aeval (affine (R := ℂ) δ) (map (Int.castRingHom ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [affine]
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | mul_X p i hp => simp [affine, hp]

private lemma charCoeff_complex (𝓡 : ResultantSystem) (n s : ℕ) :
    map (Int.castRingHom ℂ) (charCoeff 𝓡 n s) =
      (aeval (affine (R := ℂ) (delta n))
        (map (Int.castRingHom ℂ) (symTensorDet 𝓡 n))).coeff s := by
  classical
  have h := lift_charPoly (delta n) (symTensorDet 𝓡 n)
  have hfun : affine (R := ℤ) (delta n) =
      (fun T : Sym (Fin n) 3 =>
        Polynomial.C (if ∃ j, T = Sym.replicate 3 j then (1 : MvPolynomial (Sym (Fin n) 3) ℤ) else 0) +
          Polynomial.X * Polynomial.C (X T)) := by
    funext T
    by_cases hT : ∃ j, T = Sym.replicate 3 j <;> simp [affine, delta, hT]
  rw [hfun] at h
  have hc := congrArg (fun p => p.coeff s) h
  simpa only [Polynomial.coeff_map, charCoeff] using hc

private lemma delta_weight {n : ℕ} (ζ : ℂ) (hz : ζ ^ 3 = 1) (i : Fin n)
    (T : Sym (Fin n) 3) : ζ ^ tensorWeight i T * (delta n T : ℂ) = (delta n T : ℂ) := by
  classical
  by_cases hT : ∃ j, T = Sym.replicate 3 j
  · obtain ⟨j, rfl⟩ := hT
    have hw : tensorWeight i (Sym.replicate 3 j) = if j = i then 3 else 0 :=
      Multiset.count_replicate i j 3
    rw [hw]
    by_cases hji : j = i <;> simp [delta, hji, hz]
  · simp [delta, hT]

private lemma charCoeff_scale {n : ℕ} (𝓡 : ResultantSystem) (hn : 1 ≤ n)
    (s : ℕ) (ζ : ℂ) (hz : ζ ^ 3 = 1) (i : Fin n) :
    scale ζ (tensorWeight i) (map (Int.castRingHom ℂ) (charCoeff 𝓡 n s)) =
      map (Int.castRingHom ℂ) (charCoeff 𝓡 n s) := by
  let φ := Polynomial.mapAlgHom (scale ζ (tensorWeight i))
  have hF (T : Sym (Fin n) 3) :
      φ (affine (R := ℂ) (delta n) T) =
        Polynomial.C (C (ζ ^ tensorWeight i T)) * affine (R := ℂ) (delta n) T := by
    simp only [φ, Polynomial.coe_mapAlgHom, affine, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    change Polynomial.C (scale ζ (tensorWeight i) (C (delta n T : ℂ))) +
      Polynomial.X * Polynomial.C (scale ζ (tensorWeight i) (X T)) = _
    simp only [scale, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
    have hd := congrArg (fun c : ℂ => (Polynomial.C (C c) :
      Polynomial (MvPolynomial (Sym (Fin n) 3) ℂ))) (delta_weight ζ hz i T)
    simp only [map_mul] at hd
    rw [Polynomial.C_mul]
    linear_combination -hd
  have hpoly : φ (aeval (affine (R := ℂ) (delta n))
      (map (Int.castRingHom ℂ) (symTensorDet 𝓡 n))) =
      aeval (affine (R := ℂ) (delta n))
        (map (Int.castRingHom ℂ) (symTensorDet 𝓡 n)) := by
    rw [comp_aeval_apply]
    have hfun : (fun T => φ (affine (R := ℂ) (delta n) T)) =
        (fun T => Polynomial.C (C (ζ ^ tensorWeight i T)) * affine (R := ℂ) (delta n) T) := by
      funext T
      exact hF T
    rw [hfun]
    have hb : aeval (affine (R := ℂ) (delta n))
        (scale ζ (tensorWeight i) (map (Int.castRingHom ℂ) (symTensorDet 𝓡 n))) =
        aeval (fun T => Polynomial.C (C (ζ ^ tensorWeight i T)) *
          affine (R := ℂ) (delta n) T) (map (Int.castRingHom ℂ) (symTensorDet 𝓡 n)) := by
      rw [scale, comp_aeval_apply]
      congr 2
      funext T
      simp [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    rw [← hb, symDet_scale 𝓡 hn ζ hz i]
  rw [charCoeff_complex]
  have hc := congrArg (fun p => p.coeff s) hpoly
  rw [Polynomial.coeff_mapAlgHom_apply] at hc
  exact hc

theorem index_divisible (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (s : ℕ)
    (μ : Sym (Fin n) 3 →₀ ℕ) (hμ : μ ∈ (charCoeff 𝓡 n s).support) (i : Fin n) :
    3 ∣ μ.sum (fun T k => k * Multiset.count i (T : Multiset (Fin n))) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ 3
  have hz : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hc := congrArg (fun p : MvPolynomial (Sym (Fin n) 3) ℂ => p.coeff μ)
    (charCoeff_scale 𝓡 hn s ζ hz i)
  rw [scale_coeff] at hc
  have hne : (map (Int.castRingHom ℂ) (charCoeff 𝓡 n s)).coeff μ ≠ 0 := by
    rw [coeff_map]
    have hμ' := mem_support_iff.mp hμ
    simpa only [Int.coe_castRingHom, Int.cast_ne_zero] using hμ'
  have hp : ζ ^ weight (tensorWeight i) μ = 1 := by
    exact (mul_right_cancel₀ hne (by simpa only [one_mul] using hc))
  exact (hζ.pow_eq_one_iff_dvd _).mp hp

private lemma sum_count {n : ℕ} (M : Multiset (Fin n)) :
    ∑ i : Fin n, Multiset.count i M = M.card := by
  classical
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    simp only [Multiset.count_cons, Finset.sum_add_distrib, ih, Multiset.card_cons]
    simp

private lemma total_occurrences {n : ℕ} (μ : Sym (Fin n) 3 →₀ ℕ) :
    (∑ i : Fin n, μ.sum (fun T k => k * Multiset.count i (T : Multiset (Fin n)))) =
      3 * ∑ T ∈ μ.support, μ T := by
  classical
  simp only [Finsupp.sum]
  rw [Finset.sum_comm]
  calc
    (∑ T ∈ μ.support, ∑ i : Fin n, μ T * Multiset.count i (T : Multiset (Fin n))) =
        ∑ T ∈ μ.support, μ T * 3 := by
      apply Finset.sum_congr rfl
      intro T _
      rw [← Finset.mul_sum, sum_count, Sym.card_coe]
    _ = 3 * ∑ T ∈ μ.support, μ T := by rw [← Finset.sum_mul, Nat.mul_comm]

theorem occurrences_bound (𝓡 : ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (s : ℕ)
    (μ : Sym (Fin n) 3 →₀ ℕ) (hμ : μ ∈ (charCoeff 𝓡 n s).support) :
    (Finset.univ.filter
      (fun i : Fin n => 0 < μ.sum (fun T k => k * Multiset.count i (T : Multiset (Fin n))))).card ≤ s := by
  classical
  let occ : Fin n → ℕ := fun i => μ.sum (fun T k => k * Multiset.count i (T : Multiset (Fin n)))
  let used := Finset.univ.filter (fun i : Fin n => 0 < occ i)
  have hdegree := (IndexHomogeneity.charCoeff_homogeneous 𝓡 n s).degree_eq_sum_deg_support hμ
  have htotal : ∑ i : Fin n, occ i = 3 * s := by
    change (∑ i : Fin n, μ.sum _) = 3 * s
    rw [total_occurrences, ← hdegree]
  have hthree (i : Fin n) (hi : i ∈ used) : 3 ≤ occ i := by
    have hpos : 0 < occ i := (Finset.mem_filter.mp hi).2
    obtain ⟨k, hk⟩ := index_divisible 𝓡 hn s μ hμ i
    change occ i = 3 * k at hk
    omega
  have hcard : 3 * used.card ≤ ∑ i ∈ used, occ i := by
    calc
      3 * used.card = ∑ _i ∈ used, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ used, occ i := Finset.sum_le_sum hthree
  have hsum : ∑ i ∈ used, occ i ≤ ∑ i : Fin n, occ i :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  change used.card ≤ s
  omega

end IndexOccurrences

theorem solution (𝓡 : ResultantVNP.ResultantSystem) {n : ℕ} (hn : 1 ≤ n) (s : ℕ)
    (μ : Sym (Fin n) 3 →₀ ℕ) (hμ : μ ∈ (ResultantVNP.charCoeff 𝓡 n s).support) :
    (∀ i : Fin n, 3 ∣ μ.sum (fun T k => k * Multiset.count i (T : Multiset (Fin n)))) ∧
    (Finset.univ.filter
      (fun i : Fin n => 0 < μ.sum (fun T k => k * Multiset.count i (T : Multiset (Fin n))))).card ≤ s :=
  ⟨IndexOccurrences.index_divisible 𝓡 hn s μ hμ, IndexOccurrences.occurrences_bound 𝓡 hn s μ hμ⟩

#print axioms solution
