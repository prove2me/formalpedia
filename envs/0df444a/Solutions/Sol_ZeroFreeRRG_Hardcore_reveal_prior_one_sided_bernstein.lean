-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.reveal_prior_one_sided_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:45:05.393213+00:00
-- url     : https://prove2.me/submissions/cdd92de1-a146-4bd9-ab47-ba72181de50d

import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

private theorem exp_sharp (x : ℝ) (hx : |x| ≤ 1/3) : Real.exp x ≤ 1+x+(3/4)*x^2 := by
  have hx1 : |x| ≤ 1 := by linarith
  have hh := Real.exp_bound (n := 3) hx1 (by norm_num)
  norm_num [Finset.sum_range_succ] at hh
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hx2 : 0 ≤ x^2 := sq_nonneg x
  have h3 : |x|^3 ≤ (1/3)*x^2 := by
    have hsq : |x|^2 = x^2 := sq_abs x
    have hh := mul_le_mul_of_nonneg_right hx hx2
    nlinarith [sq_abs x, sq_nonneg (|x|)]
  have he := le_abs_self (Real.exp x - (1 + x + x^2/2))
  nlinarith

theorem solution {A : Type} [Fintype A] (n : ℕ) (s η : ℝ) (ν z : A → ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (hν : ∀ a, 0 ≤ ν a) (hνsum : (∑ a, ν a) = 1)
    (hz : ∀ a, |z a| ≤ 1) (hcenter : (∑ a, ν a * z a) = 0) :
    (∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
      (∏ v, ν (y v)) * (if s*η*n/2 ≤ ∑ v, z (y v) then 1 else 0)) ≤
        Real.exp (-(s*η^2/12)*n) := by
  classical
  let θ := η/3
  let a := s*η*n/2
  let K := (3/4:ℝ)*θ^2
  let A₀ := ∑ a, ν a * Real.exp (θ*z a)
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith
  have hθ1 : θ ≤ 1/3 := by dsimp [θ]; linarith
  have hA0 : 0 ≤ A₀ := Finset.sum_nonneg fun a ha => mul_nonneg (hν a) (Real.exp_pos _).le
  have hA : A₀ ≤ 1+K := by
    have hbound (a : A) : Real.exp (θ*z a) ≤ 1+θ*z a+K := by
      have ha0 : 0 ≤ |z a| := abs_nonneg _
      have ha2 : (z a)^2 ≤ 1 := by nlinarith [hz a,sq_abs (z a),sq_nonneg (|z a|)]
      have habs : |θ*z a| ≤ 1/3 := by rw [abs_mul,abs_of_nonneg hθ]; nlinarith [hz a]
      have he := exp_sharp (θ*z a) habs
      have he2 : (θ*z a)^2 ≤ θ^2 := by
        nlinarith [sq_nonneg θ,mul_nonneg (sq_nonneg θ) (sub_nonneg.mpr ha2)]
      dsimp [K]
      nlinarith
    have hh : (∑ a, ν a * Real.exp (θ*z a)) ≤ ∑ a, ν a * (1+θ*z a+K) := by
      exact Finset.sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hbound a) (hν a))
    have heq : (∑ a, ν a * (1+θ*z a+K)) = 1+K := by
      simp only [mul_add,Finset.sum_add_distrib, mul_one,← Finset.sum_mul] 
      have hh' : (∑ a, ν a * (θ*z a)) = θ * ∑ a, ν a * z a := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        ring
      rw [hh',hcenter,hνsum]
      ring
    exact hh.trans_eq heq
  have hbase0 : 0 ≤ 1-s+s*A₀ := by nlinarith
  have hbase : 1-s+s*A₀ ≤ Real.exp (s*K) := by
    have hh := mul_le_mul_of_nonneg_left hA hs
    have he := Real.add_one_le_exp (s*K)
    linarith
  have hmoment (U : Finset (Fin n)) :
      (∑ y : ({v : Fin n // v ∈ U} → A), (∏ v, ν (y v)) * Real.exp (θ*(∑ v, z (y v)))) = A₀^U.card := by
    have hprod := Fintype.prod_sum (fun (_ : {v : Fin n // v ∈ U}) (a : A) => ν a * Real.exp (θ*z a))
    simp only [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum] at hprod
    rw [← hprod]
    simp [A₀]
  have hmix : (∑ U : Finset (Fin n), revealProb s U * A₀^U.card) = (1-s+s*A₀)^n := by
    have hh := Finset.prod_add (fun _ : Fin n => s*A₀) (fun _ : Fin n => 1-s) Finset.univ
    simp only [Finset.powerset_univ,Finset.prod_const,Finset.card_sdiff,Finset.inter_univ,
      Finset.card_univ,Fintype.card_fin] at hh
    have hp : s*A₀+(1-s) = 1-s+s*A₀ := by ring
    rw [hp] at hh
    symm
    calc
      _ = ∑ U : Finset (Fin n), (s*A₀)^U.card*(1-s)^(n-U.card) := hh
      _ = ∑ U : Finset (Fin n), revealProb s U * A₀^U.card := by
        apply Finset.sum_congr rfl
        intro U hU
        unfold revealProb
        rw [mul_pow]
        ring
  have hmgf : (∑ U : Finset (Fin n), revealProb s U *
      ∑ y : ({v : Fin n // v ∈ U} → A), (∏ v, ν (y v)) * Real.exp (θ*(∑ v, z (y v)))) ≤
        Real.exp (s*K*n) := by
    simp_rw [hmoment]
    rw [hmix]
    calc
      _ ≤ (Real.exp (s*K))^n := pow_le_pow_left₀ hbase0 hbase _
      _ = Real.exp (s*K*n) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hpoint (U : Finset (Fin n)) (y : {v : Fin n // v ∈ U} → A) :
      (∏ v, ν (y v)) * (if a ≤ ∑ v, z (y v) then 1 else 0) ≤
        (∏ v, ν (y v)) * Real.exp (θ*((∑ v, z (y v))-a)) := by
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun v hv => hν (y v))
    split_ifs with hy
    · have hh := Real.add_one_le_exp (θ*((∑ v, z (y v))-a))
      have hm := mul_nonneg hθ (sub_nonneg.mpr hy)
      linarith
    · exact (Real.exp_pos _).le
  have hbound : (∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
      (∏ v, ν (y v)) * (if a ≤ ∑ v, z (y v) then 1 else 0)) ≤
      ∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
        (∏ v, ν (y v)) * Real.exp (θ*((∑ v, z (y v))-a)) := by
    apply Finset.sum_le_sum
    intro U hU
    apply mul_le_mul_of_nonneg_left _
    · unfold revealProb
      exact mul_nonneg (pow_nonneg hs _) (pow_nonneg (sub_nonneg.mpr hs1) _)
    · exact Finset.sum_le_sum (fun y hy => hpoint U y)
  have hfactor : (∑ U : Finset (Fin n), revealProb s U * ∑ y : ({v : Fin n // v ∈ U} → A),
        (∏ v, ν (y v)) * Real.exp (θ*((∑ v, z (y v))-a))) =
      Real.exp (-θ*a) * (∑ U : Finset (Fin n), revealProb s U *
        ∑ y : ({v : Fin n // v ∈ U} → A), (∏ v, ν (y v)) * Real.exp (θ*(∑ v, z (y v)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    have he : Real.exp (θ*((∑ v, z (y v))-a)) = Real.exp (-θ*a)*Real.exp (θ*(∑ v, z (y v))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    rw [← Finset.mul_sum]
    ring
  rw [hfactor] at hbound
  have hh := mul_le_mul_of_nonneg_left hmgf (Real.exp_pos (-θ*a)).le
  have heq : Real.exp (-θ*a)*Real.exp (s*K*n) = Real.exp (-(s*η^2/12)*n) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [θ,a,K]
    ring
  rw [heq] at hh
  exact hbound.trans hh
