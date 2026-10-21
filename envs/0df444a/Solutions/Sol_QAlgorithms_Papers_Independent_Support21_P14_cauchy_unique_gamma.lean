-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P14.cauchy_unique_gamma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:43:41.702973+00:00
-- url     : https://prove2.me/submissions/c2c88eaf-9527-4799-881a-3f888c2004c3

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14
noncomputable section

open scoped BigOperators Classical

open Polynomial QAlgorithms.Papers.Independent.Support21.P14

theorem g66l2_lag {F : Type*} [Field F] {r : ℕ} (u : Fin r → F) (hu : Function.Injective u)
    (hzero : ∀ j, u j ≠ 0) (hprod : ∀ i j, u i * u j ≠ 1) (p : F[X]) (hp : p.degree < r)
    (i : Fin r) :
    ∑ j, (1 - u i * u j)⁻¹ * (p.eval (u j)⁻¹ * ∏ k ∈ Finset.univ.erase j, (u j / (u j - u k)))
      * ∏ k, (1 - u i * u k) = p.eval (u i) := by
  have hinj : Set.InjOn (fun j => (u j)⁻¹) (Finset.univ : Finset (Fin r)) := by
    intro a _ b _ h; exact hu (inv_injective h)
  have hp' : p.degree < (Finset.univ : Finset (Fin r)).card := by simpa using hp
  conv_rhs => rw [Lagrange.eq_interpolate hinj hp']
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [eval_mul, eval_C, Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_sub, eval_X]
  rw [← Finset.mul_prod_erase Finset.univ (fun k => 1 - u i * u k) (Finset.mem_univ j)]
  have h1 : 1 - u i * u j ≠ 0 := sub_ne_zero.mpr (hprod i j).symm
  rw [mul_assoc, mul_assoc]
  have : (1 - u i * u j)⁻¹ * (eval (u j)⁻¹ p * ((∏ k ∈ Finset.univ.erase j, u j / (u j - u k)) *
      ((1 - u i * u j) * ∏ k ∈ Finset.univ.erase j, (1 - u i * u k)))) =
      eval (u j)⁻¹ p * ∏ k ∈ Finset.univ.erase j, (u j / (u j - u k) * (1 - u i * u k)) := by
    rw [Finset.prod_mul_distrib]; field_simp
  rw [this]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  have hjk : j ≠ k := (Finset.ne_of_mem_erase hk).symm
  have h2 : u j - u k ≠ 0 := sub_ne_zero.mpr (hu.ne hjk)
  have h3 : (u j)⁻¹ - (u k)⁻¹ ≠ 0 := sub_ne_zero.mpr (fun h => hjk (hu (inv_injective h)))
  have hj := hzero j; have hk := hzero k
  rw [eq_comm, inv_mul_eq_iff_eq_mul₀ h3]
  field_simp
  ring

theorem g66l2_Q_ne {F : Type*} [Field F] {r : ℕ} (u : Fin r → F)
    (hprod : ∀ i j, u i * u j ≠ 1) (i : Fin r) : ∏ k, (1 - u i * u k) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => sub_ne_zero.mpr (hprod i k).symm

theorem g66l2_solve {F : Type*} [Field F] {r : ℕ} (u : Fin r → F) (hu : Function.Injective u)
    (hzero : ∀ j, u j ≠ 0) (hprod : ∀ i j, u i * u j ≠ 1) (p : F[X]) (hp : p.degree < r)
    (b : Fin r → F) (hb : ∀ i, p.eval (u i) = b i * ∏ k, (1 - u i * u k))
    (γ : Fin r → F) (hγ : ∀ j, γ j = p.eval (u j)⁻¹ * ∏ k ∈ Finset.univ.erase j, (u j / (u j - u k)))
    (i : Fin r) : ∑ j, cauchyMatrix u i j * γ j = b i := by
  have h := g66l2_lag u hu hzero hprod p hp i
  rw [hb i, ← Finset.sum_mul] at h
  have h' := mul_right_cancel₀ (g66l2_Q_ne u hprod i) h
  rw [← h']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hγ j]; rfl

theorem g66l2_isUnit {F : Type*} [Field F] {r : ℕ} (u : Fin r → F) (hu : Function.Injective u)
    (hzero : ∀ j, u j ≠ 0) (hprod : ∀ i j, u i * u j ≠ 1) : IsUnit (cauchyMatrix u) := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  intro b
  have hinj : Set.InjOn u (Finset.univ : Finset (Fin r)) := fun a _ b _ h => hu h
  set p := Lagrange.interpolate Finset.univ u (fun i => b i * ∏ k, (1 - u i * u k))
  have hp : p.degree < r := by
    have := Lagrange.degree_interpolate_lt (fun i => b i * ∏ k, (1 - u i * u k)) hinj
    rwa [Finset.card_univ, Fintype.card_fin] at this
  refine ⟨fun j => p.eval (u j)⁻¹ * ∏ k ∈ Finset.univ.erase j, (u j / (u j - u k)), ?_⟩
  funext i
  exact g66l2_solve u hu hzero hprod p hp b
    (fun i => Lagrange.eval_interpolate_at_node _ hinj (Finset.mem_univ i)) _ (fun _ => rfl) i

theorem g66l2_unique {F : Type*} [Field F] {r : ℕ} (u : Fin r → F) (hu : Function.Injective u)
    (hzero : ∀ j, u j ≠ 0) (hprod : ∀ i j, u i * u j ≠ 1) (b g0 : Fin r → F)
    (h0 : ∀ i, ∑ j, cauchyMatrix u i j * g0 j = b i) (gamma : Fin r → F) :
    (∀ i, ∑ j, cauchyMatrix u i j * gamma j = b i) ↔ gamma = g0 := by
  constructor
  · intro h
    have hinj := (Matrix.mulVec_injective_iff_isUnit (A := cauchyMatrix u)).mpr
      (g66l2_isUnit u hu hzero hprod)
    apply hinj
    funext i
    simp only [Matrix.mulVec, dotProduct]
    rw [h i, h0 i]
  · rintro rfl; exact h0

theorem g66l2_first {F : Type*} [Field F] {r : ℕ} (u : Fin r → F) (hu : Function.Injective u)
    (hzero : ∀ j, u j ≠ 0) (hprod : ∀ i j, u i * u j ≠ 1) (i : Fin r) :
    ∑ j, cauchyMatrix u i j * cauchyFirstVector u j = 1 := by
  set c : F := ∏ k, (-u k)
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => neg_ne_zero.mpr (hzero k)
  set p : F[X] := C c * (∏ k, (X - C (u k)⁻¹) - ∏ k, (X - C (u k)))
  have hm1 : (∏ k, (X - C (u k)⁻¹) : F[X]).Monic :=
    monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _
  have hm2 : (∏ k, (X - C (u k)) : F[X]).Monic :=
    monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _
  have hd1 : (∏ k, (X - C (u k)⁻¹) : F[X]).degree = r := by
    rw [degree_eq_natDegree hm1.ne_zero, natDegree_finsetProd_X_sub_C_eq_card]; simp
  have hd2 : (∏ k, (X - C (u k)) : F[X]).degree = r := by
    rw [degree_eq_natDegree hm2.ne_zero, natDegree_finsetProd_X_sub_C_eq_card]; simp
  have hp : p.degree < r := by
    rw [degree_C_mul hc, ← hd1]
    exact degree_sub_lt_left (hd1.trans hd2.symm) hm1.ne_zero (hm1.leadingCoeff.trans hm2.leadingCoeff.symm)
  refine g66l2_solve u hu hzero hprod p hp (fun _ => 1) ?_ _ ?_ i
  · intro i
    simp only [p, eval_mul, eval_C, eval_sub, eval_prod, eval_X]
    rw [Finset.prod_eq_zero (f := fun k => u i - u k) (Finset.mem_univ i) (sub_self _), sub_zero,
      one_mul]
    simp only [c]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have := hzero k
    field_simp; ring
  · intro j
    simp only [p, eval_mul, eval_C, eval_sub, eval_prod, eval_X]
    rw [Finset.prod_eq_zero (f := fun k => (u j)⁻¹ - (u k)⁻¹) (Finset.mem_univ j) (sub_self _),
      zero_sub, cauchyFirstVector, cauchyProduct]
    simp only [c]
    rw [← Finset.mul_prod_erase _ (fun k => -u k) (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ (fun x => (u j)⁻¹ - u x) (Finset.mem_univ j)]
    have hj := hzero j
    have key : (∏ l ∈ Finset.univ.erase j, u l) *
        ∏ l ∈ Finset.univ.erase j, (u l * u j - 1) / (u j - u l) =
        (∏ k ∈ Finset.univ.erase j, -u k) * (∏ x ∈ Finset.univ.erase j, ((u j)⁻¹ - u x)) *
        ∏ k ∈ Finset.univ.erase j, u j / (u j - u k) := by
      simp only [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k hk => ?_
      have hjk : j ≠ k := (Finset.ne_of_mem_erase hk).symm
      have h2 : u j - u k ≠ 0 := sub_ne_zero.mpr (hu.ne hjk)
      field_simp; ring
    have e : u j * ((u j)⁻¹ - u j) = 1 - u j ^ 2 := by field_simp
    linear_combination (1 - u j ^ 2) * key - ((∏ k ∈ Finset.univ.erase j, -u k) *
      (∏ x ∈ Finset.univ.erase j, ((u j)⁻¹ - u x)) * ∏ k ∈ Finset.univ.erase j, u j / (u j - u k)) * e

theorem g66l2_div {F : Type*} [Field F] {r : ℕ} (u : Fin r → F) (S : Finset (Fin r)) :
    ∃ D : F[X], (X ^ 2 - C 1) * D = (if Even S.card then 1 else X) * ∏ k ∈ S, (X - C (u k)) -
      ∏ k ∈ S, (1 - C (u k) * X) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a S ha ih =>
    obtain ⟨D, hD⟩ := ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    by_cases he : Even S.card
    · have hne : ¬ Even (S.card + 1) := by rw [Nat.even_add_one]; exact not_not.mpr he
      rw [if_pos he] at hD; rw [if_neg hne]
      refine ⟨D * (1 - C (u a) * X) + ∏ k ∈ S, (X - C (u k)), ?_⟩
      simp only [map_one] at hD ⊢
      linear_combination (1 - C (u a) * X) * hD
    · have hne : Even (S.card + 1) := by rw [Nat.even_add_one]; exact he
      rw [if_neg he] at hD; rw [if_pos hne]
      refine ⟨D * (1 - C (u a) * X) + C (u a) * ∏ k ∈ S, (X - C (u k)), ?_⟩
      simp only [map_one] at hD ⊢
      linear_combination (1 - C (u a) * X) * hD

theorem g66l2_second {F : Type*} [Field F] {r : ℕ} (hr : 0 < r) (u : Fin r → F)
    (hu : Function.Injective u)
    (hzero : ∀ j, u j ≠ 0) (hprod : ∀ i j, u i * u j ≠ 1) (i : Fin r) :
    ∑ j, cauchyMatrix u i j * cauchySecondVector u j = (1 - u i ^ 2)⁻¹ := by
  obtain ⟨D, hD⟩ := g66l2_div u Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hD
  have hdeg : D.degree < r := by
    rcases eq_or_ne D 0 with h0 | h0
    · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
    have hm : (X ^ 2 - C (1 : F)).Monic := monic_X_pow_sub_C _ (by norm_num)
    have h1 := hm.natDegree_mul' h0
    rw [natDegree_X_pow_sub_C, hD] at h1
    have h2 : ((if Even r then 1 else X) * ∏ k : Fin r, (X - C (u k)) -
        ∏ k : Fin r, (1 - C (u k) * X)).natDegree ≤ r + 1 := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_mul_le).trans ?_
        rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin]
        have : (if Even r then (1 : F[X]) else X).natDegree ≤ 1 := by
          split_ifs <;> simp
        omega
      · refine (natDegree_prod_le _ _).trans ?_
        refine (Finset.sum_le_sum (g := fun _ => 1) fun k _ => ?_).trans ?_
        · compute_degree
        · simp
    have h3 : D.natDegree < r := by omega
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast h3)
  refine g66l2_solve u hu hzero hprod D hdeg (fun i => (1 - u i ^ 2)⁻¹) ?_ _ ?_ i
  · intro i
    have h := congrArg (eval (u i)) hD
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_prod, eval_one] at h
    rw [Finset.prod_eq_zero (f := fun k => u i - u k) (Finset.mem_univ i) (sub_self _),
      mul_zero, zero_sub] at h
    have hi : 1 - u i ^ 2 ≠ 0 := by
      have := hprod i i; intro h'; apply this; linear_combination -h'
    rw [eq_inv_mul_iff_mul_eq₀ hi]
    have : ∏ k, (1 - u k * u i) = ∏ k, (1 - u i * u k) :=
      Finset.prod_congr rfl fun k _ => by ring
    rw [← this]; linear_combination -h
  · intro j
    have h := congrArg (eval (u j)⁻¹) hD
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C, eval_prod, eval_one] at h
    have hj := hzero j
    rw [Finset.prod_eq_zero (f := fun k => 1 - u k * (u j)⁻¹) (Finset.mem_univ j)
      (by field_simp; ring), sub_zero] at h
    rw [← Finset.mul_prod_erase _ (fun k => (u j)⁻¹ - u k) (Finset.mem_univ j)] at h
    have hj1 : (u j)⁻¹ ^ 2 - 1 ≠ 0 := by
      have := hprod j j; intro h'; apply this; field_simp at h'; linear_combination -h'
    rw [← eq_inv_mul_iff_mul_eq₀ hj1] at h
    have key : (∏ k ∈ Finset.univ.erase j, ((u j)⁻¹ - u k)) *
        ∏ k ∈ Finset.univ.erase j, u j / (u j - u k) =
        (-1) ^ (r - 1) * ∏ l ∈ Finset.univ.erase j, (u l * u j - 1) / (u j - u l) := by
      have hc : (Finset.univ.erase j).card = r - 1 := by simp
      rw [← hc, ← Finset.prod_neg, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k hk => ?_
      have hjk : j ≠ k := (Finset.ne_of_mem_erase hk).symm
      have h2 : u j - u k ≠ 0 := sub_ne_zero.mpr (hu.ne hjk)
      field_simp; ring
    have hj2 : 1 - u j ^ 2 ≠ 0 := by
      have := hprod j j; intro h'; apply this; linear_combination -h'
    by_cases he : Even r
    · have ho : ¬ Odd r := Nat.not_odd_iff_even.mpr he
      have hs : (-1 : F) ^ (r - 1) = -1 := by
        apply Odd.neg_one_pow; obtain ⟨m, hm⟩ := he; exact ⟨m - 1, by omega⟩
      rw [if_pos he, eval_one] at h
      rw [hs] at key
      rw [h, cauchySecondVector, cauchyProduct, if_neg ho]
      have sc : ((u j)⁻¹ ^ 2 - 1)⁻¹ * 1 * ((u j)⁻¹ - u j) * (-1) = -u j := by
        field_simp
      linear_combination (-(((u j)⁻¹ ^ 2 - 1)⁻¹ * 1 * ((u j)⁻¹ - u j))) * key -
        (∏ l ∈ Finset.univ.erase j, (u l * u j - 1) / (u j - u l)) * sc
    · have ho : Odd r := Nat.not_even_iff_odd.mp he
      have hs : (-1 : F) ^ (r - 1) = 1 := by
        apply Even.neg_one_pow; obtain ⟨m, hm⟩ := ho; exact ⟨m, by omega⟩
      rw [if_neg he, eval_X] at h
      rw [hs] at key
      rw [h, cauchySecondVector, cauchyProduct, if_pos ho]
      have sc : ((u j)⁻¹ ^ 2 - 1)⁻¹ * (u j)⁻¹ * ((u j)⁻¹ - u j) * 1 = 1 := by
        field_simp
      linear_combination (-(((u j)⁻¹ ^ 2 - 1)⁻¹ * (u j)⁻¹ * ((u j)⁻¹ - u j))) * key -
        (∏ l ∈ Finset.univ.erase j, (u l * u j - 1) / (u j - u l)) * sc

/-- Lemma 3.9, PDF p.19. The formula is a solution and the only solution.
No ground-ring relation involving rho,q,delta is required. -/
theorem solution {F : Type*} [Field F] (r : ℕ) (hr : 0 < r)
    (u : Fin r → F) (hu : Function.Injective u) (hzero : ∀ j, u j ≠ 0)
    (hprod : ∀ i j, u i * u j ≠ 1) (rho q : F)
    (hrho : rho ≠ 0) (hq : q ≠ 0) (hsquare : q^2 ≠ 1) :
    ∀ gamma : Fin r → F,
      (∀ i, ∑ j : Fin r, cauchyMatrix u i j * gamma j =
        (1-u i^2)⁻¹ + (rho*(q⁻¹-q))⁻¹) ↔ gamma = gammaVector u rho q := by
  intro gamma
  refine g66l2_unique u hu hzero hprod (fun i => (1-u i^2)⁻¹ + (rho*(q⁻¹-q))⁻¹) _ ?_ gamma
  intro i
  have h1 := g66l2_first u hu hzero hprod i
  have h2 := g66l2_second hr u hu hzero hprod i
  have e : ∀ j, gammaVector u rho q j =
      (rho*(q⁻¹-q))⁻¹ * cauchyFirstVector u j + cauchySecondVector u j := by
    intro j; simp only [gammaVector, cauchyFirstVector, cauchySecondVector]; rw [div_eq_mul_inv]; ring
  simp only [e, mul_add, Finset.sum_add_distrib, h2]
  have : ∑ j, cauchyMatrix u i j * ((rho*(q⁻¹-q))⁻¹ * cauchyFirstVector u j) =
      (rho*(q⁻¹-q))⁻¹ * ∑ j, cauchyMatrix u i j * cauchyFirstVector u j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, h1]; ring

end
