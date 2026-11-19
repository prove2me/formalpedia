-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.interior_integer_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:44:27.904837+00:00
-- url     : https://prove2.me/submissions/5ee8530c-3ebc-4b78-8ac2-095b2bba0f7c

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
/-
Adapted portions copyright (c) 2026 Saint Wesonga.
Licensed under the Apache License, Version 2.0,
https://www.apache.org/licenses/LICENSE-2.0

The symmetric finite-difference stencil below is adapted from
Saint Wesonga, formalcs/circuit-complexity release/0.2.0,
Majority/ApproximateDegree/LowerBoundGrid.lean (Apache 2.0).
The mesh is changed from four to sixteen. The fractional interpolation
estimate following the stencil is developed for the present mission.
-/
namespace QuantumBipartiteTesting.Bipartiteness.GridProof
open Polynomial
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

/-- The central binomial coefficient normalizes the middle weight to one. -/
noncomputable def centralGridWeight (m j : ℕ) : ℝ :=
  (-1) ^ (j + m) * ((2 * m).choose j : ℝ) / (2 * m).choose m

theorem centralGridWeight_center (m : ℕ) : centralGridWeight m m = 1 := by
  have hpos : (0 : ℝ) < (2 * m).choose m := by
    exact_mod_cast Nat.choose_pos (by omega : m ≤ 2 * m)
  simp [centralGridWeight, ← two_mul, pow_mul, ne_of_gt hpos]

theorem abs_centralGridWeight_le_one (m j : ℕ) : |centralGridWeight m j| ≤ 1 := by
  have hpos : (0 : ℝ) < (2 * m).choose m := by
    exact_mod_cast Nat.choose_pos (by omega : m ≤ 2 * m)
  rw [centralGridWeight, abs_div, abs_mul, abs_neg_one_pow, one_mul,
    abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hpos, div_le_one hpos]
  exact_mod_cast Nat.choose_le_centralBinom j m

theorem centralGridWeight_reflect (m j : ℕ) (hj : j ≤ 2 * m) :
    centralGridWeight m (2 * m - j) = centralGridWeight m j := by
  unfold centralGridWeight
  rw [Nat.choose_symm hj]
  have hpow : (-1 : ℝ) ^ (2 * m - j + m) = (-1 : ℝ) ^ (j + m) := by
    calc
      _ = (-1 : ℝ) ^ ((2 * m - j + m) % 2) := neg_one_pow_eq_pow_mod_two _
      _ = (-1 : ℝ) ^ ((j + m) % 2) := by congr 1; omega
      _ = _ := (neg_one_pow_eq_pow_mod_two _).symm
  rw [hpow]

/-- Alternating binomial weights annihilate polynomials below their order. -/
theorem sum_alternating_choose_eval_eq_zero {n : ℕ} {p : ℝ[X]}
    (hp : p.natDegree < n) :
    ∑ j ∈ Finset.range (n + 1), (-1 : ℝ) ^ (n - j) * n.choose j * p.eval (j : ℝ) = 0 := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hp) 0
  rw [fwdDiff_iter_eq_sum_shift] at h
  simpa only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, nsmul_eq_mul, mul_one, zero_add, Pi.zero_apply] using h

/-- The order `2m` difference stencil with mesh four, centered at zero. -/
theorem sum_alternating_choose_grid_eval_eq_zero {m : ℕ} {p : ℝ[X]}
    (hp : p.natDegree < 2 * m) :
    ∑ j ∈ Finset.range (2 * m + 1),
      (-1 : ℝ) ^ j * (2 * m).choose j * p.eval (16 * ((j : ℝ) - m)) = 0 := by
  let q : ℝ[X] := p.comp (C (16 : ℝ) * (X - C (m : ℝ)))
  have hq : q.natDegree < 2 * m := by
    apply lt_of_le_of_lt ?_ hp
    calc q.natDegree ≤ p.natDegree * (C (16 : ℝ) * (X - C (m : ℝ))).natDegree := natDegree_comp_le
      _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ (by compute_degree)
      _ = p.natDegree := Nat.mul_one _
  have h := sum_alternating_choose_eval_eq_zero hq
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  have hpar : (-1 : ℝ) ^ (2 * m - j) = (-1 : ℝ) ^ j := by
    have hj' := Finset.mem_range.mp hj
    calc
      _ = (-1 : ℝ) ^ ((2 * m - j) % 2) := neg_one_pow_eq_pow_mod_two _
      _ = (-1 : ℝ) ^ (j % 2) := by congr 1; omega
      _ = _ := (neg_one_pow_eq_pow_mod_two _).symm
  simp [q, eval_comp, hpar]

/-- The normalized symmetric grid weights retain the full annihilation order. -/
theorem sum_centralGridWeight_eval_eq_zero {m : ℕ} {p : ℝ[X]}
    (hp : p.natDegree < 2 * m) :
    ∑ j ∈ Finset.range (2 * m + 1),
      centralGridWeight m j * p.eval (16 * ((j : ℝ) - m)) = 0 := by
  have h := congrArg (fun z : ℝ => (-1) ^ m / ((2 * m).choose m : ℝ) * z)
    (sum_alternating_choose_grid_eval_eq_zero hp)
  rw [Finset.mul_sum, mul_zero] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp [centralGridWeight]
  rw [pow_add]
  ring

noncomputable def pairedGridWeight (m j : ℕ) : ℝ := centralGridWeight m (m + j)

theorem abs_pairedGridWeight_le_one (m j : ℕ) : |pairedGridWeight m j| ≤ 1 :=
  abs_centralGridWeight_le_one _ _

private theorem sum_range_center (f : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m + 1), f j =
      f m + ∑ j ∈ Finset.range m, (f (m + (j + 1)) + f (m - (j + 1))) := by
  rw [show 2 * m + 1 = m + (m + 1) by omega, Finset.sum_range_add,
    Finset.sum_range_succ']
  have hleft : ∑ j ∈ Finset.range m, f j =
      ∑ j ∈ Finset.range m, f (m - (j + 1)) := by
    rw [← Finset.sum_range_reflect f m]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega
  rw [hleft, Finset.sum_add_distrib]
  simp only [Nat.add_zero]
  ring

/-- Paired form of the symmetric stencil: the central evaluation has
coefficient one and every pair has a coefficient of absolute value at most one. -/
theorem sum_pairedGridWeight_eval_eq_zero {m : ℕ} {p : ℝ[X]}
    (hp : p.natDegree < 2 * m) :
    p.eval 0 + ∑ j ∈ Finset.Icc 1 m,
      pairedGridWeight m j * (p.eval (16 * (j : ℝ)) + p.eval (-16 * (j : ℝ))) = 0 := by
  have h := sum_centralGridWeight_eval_eq_zero hp
  rw [sum_range_center, centralGridWeight_center] at h
  simp only [sub_self, mul_zero, one_mul] at h
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j + 1 ≤ m := by have := Finset.mem_range.mp hj; omega
  have href : centralGridWeight m (m - (j + 1)) =
      centralGridWeight m (m + (j + 1)) := by
    simpa only [show 2 * m - (m + (j + 1)) = m - (j + 1) by omega] using
      centralGridWeight_reflect m (m + (j + 1)) (by omega)
  rw [href]
  simp only [pairedGridWeight, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj']
  ring_nf


private def DD (p : ℝ[X]) (a : ℝ) : ℝ[X] := p /ₘ (X-C a)

private lemma dd_degree (p : ℝ[X]) (a : ℝ) :
    (DD p a).natDegree = p.natDegree-1 := by
  simp [DD, natDegree_divByMonic p (monic_X_sub_C a)]

private lemma dd_eval (p : ℝ[X]) (a x : ℝ) (hx : x ≠ a) :
    (DD p a).eval x = (p.eval x-p.eval a)/(x-a) := by
  have hh := congrArg (fun q : ℝ[X] => q.eval x) (modByMonic_add_div p (X-C a))
  rw [modByMonic_X_sub_C_eq_C_eval] at hh
  simp only [eval_add,eval_C,eval_mul,eval_sub,eval_X] at hh
  apply (eq_div_iff (sub_ne_zero.mpr hx)).mpr
  change (p /ₘ (X-C a)).eval x * (x-a) = _
  linarith

private def NeighborWeight (m : ℕ) : ℝ :=
  1 - ∑ j ∈ Finset.Icc 1 m, pairedGridWeight m j *
    (1/(16*(j:ℝ)-1) + 1/(-16*(j:ℝ)-1))

private lemma extended_identity {m : ℕ} (hm : 0 < m) {p : ℝ[X]}
    (hp : p.natDegree < 2*m+1) :
    -p.eval 0 + NeighborWeight m * p.eval 1 +
      ∑ j ∈ Finset.Icc 1 m, pairedGridWeight m j *
        (p.eval (16*(j:ℝ))/(16*(j:ℝ)-1) + p.eval (-16*(j:ℝ))/(-16*(j:ℝ)-1)) = 0 := by
  have hd : (DD p 1).natDegree < 2*m := by rw [dd_degree]; omega
  have hh := sum_pairedGridWeight_eval_eq_zero hd
  rw [dd_eval p 1 0 (by norm_num)] at hh
  simp only [zero_sub, div_neg, div_one, neg_sub] at hh
  have heq : (∑ j ∈ Finset.Icc 1 m, pairedGridWeight m j *
      ((DD p 1).eval (16*(j:ℝ)) + (DD p 1).eval (-16*(j:ℝ)))) =
      (∑ j ∈ Finset.Icc 1 m, pairedGridWeight m j *
        (p.eval (16*(j:ℝ))/(16*(j:ℝ)-1) + p.eval (-16*(j:ℝ))/(-16*(j:ℝ)-1))) -
      (∑ j ∈ Finset.Icc 1 m, pairedGridWeight m j *
        (1/(16*(j:ℝ)-1) + 1/(-16*(j:ℝ)-1))) * p.eval 1 := by
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : (1:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    rw [dd_eval p 1 _ (by linarith),dd_eval p 1 _ (by linarith)]
    ring
  rw [heq] at hh
  unfold NeighborWeight
  linarith

private lemma reciprocal_square_sum (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, 1/(j:ℝ)^2 ≤ 2 := by
  have htel : (∑ j ∈ Finset.Icc 1 m, (1/(j:ℝ)-1/((j:ℝ)+1))) = 1-1/((m:ℝ)+1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega),ih]
      push_cast
      ring
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 m, 2*(1/(j:ℝ)-1/((j:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : (1:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      have h0 : (j:ℝ) ≠ 0 := by linarith
      have h1 : (j:ℝ)+1 ≠ 0 := by linarith
      field_simp
      nlinarith
    _ = 2*(1-1/((m:ℝ)+1)) := by rw [← Finset.mul_sum,htel]
    _ ≤ 2 := by
      have h : 0 ≤ 1/((m:ℝ)+1) := by positivity
      linarith

private lemma neighbor_weight_nonneg (m : ℕ) : 0 ≤ NeighborWeight m := by
  have heq : (∑ j ∈ Finset.Icc 1 m, pairedGridWeight m j *
      (1/(16*(j:ℝ)-1)+1/(-16*(j:ℝ)-1))) =
      ∑ j ∈ Finset.Icc 1 m, pairedGridWeight m j * (2/(256*(j:ℝ)^2-1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : (1:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have h1 : 16*(j:ℝ)-1 ≠ 0 := by linarith
    have h2 : -16*(j:ℝ)-1 ≠ 0 := by linarith
    have h3 : 256*(j:ℝ)^2-1 ≠ 0 := by nlinarith
    congr 1
    rw [div_add_div 1 1 h1 h2]
    calc
      _ = (-2:ℝ)/(-(256*(j:ℝ)^2-1)) := by congr 1 <;> ring
      _ = _ := neg_div_neg_eq _ _
  have hsum : |∑ j ∈ Finset.Icc 1 m, pairedGridWeight m j * (2/(256*(j:ℝ)^2-1))| ≤ 1/32 := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 m, |pairedGridWeight m j * (2/(256*(j:ℝ)^2-1))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 m, (1/64:ℝ)*(1/(j:ℝ)^2) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : (1:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
        have hden : 0 < 256*(j:ℝ)^2-1 := by nlinarith
        rw [abs_mul,abs_of_pos (div_pos (by norm_num) hden)]
        apply le_trans (mul_le_of_le_one_left (le_of_lt (div_pos (by norm_num) hden))
          (abs_pairedGridWeight_le_one m j))
        have hj0 : (0:ℝ) < j := by linarith
        apply (div_le_iff₀ hden).mpr
        field_simp
        nlinarith
      _ ≤ (1/64:ℝ)*2 := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (reciprocal_square_sum m) (by norm_num)
      _ = 1/32 := by norm_num
  unfold NeighborWeight
  rw [heq]
  have hh := (abs_le.mp hsum).2
  linarith

private def Tail (m : ℕ) (z : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 m, pairedGridWeight m j *
    (f (16*(j:ℝ))/((16*(j:ℝ)-1)*(16*(j:ℝ)-z)) +
     f (-16*(j:ℝ))/((-16*(j:ℝ)-1)*(-16*(j:ℝ)-z)))

private lemma tail_bound (m : ℕ) (z : ℝ) (hz : z ∈ Set.Icc (0:ℝ) 1)
    (f : ℝ → ℝ) (hf : ∀ j ∈ Finset.Icc 1 m,
      |f (16*(j:ℝ))| ≤ 1 ∧ |f (-16*(j:ℝ))| ≤ 1) : |Tail m z f| ≤ 1/16 := by
  unfold Tail
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 m, |pairedGridWeight m j *
      (f (16*(j:ℝ))/((16*(j:ℝ)-1)*(16*(j:ℝ)-z)) +
       f (-16*(j:ℝ))/((-16*(j:ℝ)-1)*(-16*(j:ℝ)-z)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 m, (1/32:ℝ)*(1/(j:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : (1:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
      have hj0 : (0:ℝ) < j := by linarith
      have hpos : 64*(j:ℝ)^2 ≤ (16*(j:ℝ)-1)*(16*(j:ℝ)-z) := by
        have hh := mul_le_mul (show 8*(j:ℝ) ≤ 16*(j:ℝ)-1 by linarith)
          (show 8*(j:ℝ) ≤ 16*(j:ℝ)-z by linarith [hz.2]) (by positivity)
          (by linarith : 0 ≤ 16*(j:ℝ)-1)
        nlinarith
      have hneg : 64*(j:ℝ)^2 ≤ (-16*(j:ℝ)-1)*(-16*(j:ℝ)-z) := by
        nlinarith [hz.1]
      have hbpos : |f (16*(j:ℝ))/((16*(j:ℝ)-1)*(16*(j:ℝ)-z))| ≤ 1/(64*(j:ℝ)^2) := by
        rw [abs_div,abs_of_pos (lt_of_lt_of_le (by positivity) hpos)]
        exact (div_le_div_of_nonneg_right (hf j hj).1 (by nlinarith [sq_nonneg (j:ℝ)])).trans
          (one_div_le_one_div_of_le (by positivity) hpos)
      have hbneg : |f (-16*(j:ℝ))/((-16*(j:ℝ)-1)*(-16*(j:ℝ)-z))| ≤ 1/(64*(j:ℝ)^2) := by
        rw [abs_div,abs_of_pos (lt_of_lt_of_le (by positivity) hneg)]
        exact (div_le_div_of_nonneg_right (hf j hj).2 (by nlinarith [sq_nonneg (j:ℝ)])).trans
          (one_div_le_one_div_of_le (by positivity) hneg)
      rw [abs_mul]
      apply le_trans (mul_le_of_le_one_left (abs_nonneg _) (abs_pairedGridWeight_le_one m j))
      have hab := (abs_add_le _ _).trans (add_le_add hbpos hbneg)
      convert hab using 1 <;> ring
    _ ≤ (1/32:ℝ)*2 := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (reciprocal_square_sum m) (by norm_num)
    _ = 1/16 := by norm_num

private lemma fractional_identity {m : ℕ} (hm : 0 < m) {p : ℝ[X]}
    (hp : p.natDegree < 2*m+2) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    (1/z + NeighborWeight m/(1-z) + Tail m z (fun _ => 1)) * p.eval z =
      p.eval 0/z + NeighborWeight m*p.eval 1/(1-z) + Tail m z p.eval := by
  have hd : (DD p z).natDegree < 2*m+1 := by rw [dd_degree]; omega
  have hh := extended_identity hm hd
  rw [dd_eval p z 0 (by linarith),dd_eval p z 1 (by linarith)] at hh
  have heq : (∑ j ∈ Finset.Icc 1 m, pairedGridWeight m j *
      ((DD p z).eval (16*(j:ℝ))/(16*(j:ℝ)-1) +
       (DD p z).eval (-16*(j:ℝ))/(-16*(j:ℝ)-1))) =
      Tail m z p.eval - Tail m z (fun _ => 1)*p.eval z := by
    unfold Tail
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : (1:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    rw [dd_eval p z _ (by linarith),dd_eval p z _ (by linarith)]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [heq] at hh
  have heq' : -((p.eval 0-p.eval z)/(0-z)) = p.eval 0/z-p.eval z/z := by ring
  rw [heq'] at hh
  linear_combination -hh

private lemma interior_bound {m : ℕ} (hm : 0 < m) {p : ℝ[X]}
    (hp : p.natDegree < 2*m+2) (h0 : |p.eval 0| ≤ 1) (h1 : |p.eval 1| ≤ 1)
    (hb : ∀ j ∈ Finset.Icc 1 m, |p.eval (16*(j:ℝ))| ≤ 1 ∧ |p.eval (-16*(j:ℝ))| ≤ 1)
    {z : ℝ} (hz : z ∈ Set.Icc (0:ℝ) 1) : |p.eval z| ≤ 4/3 := by
  by_cases hz0 : z = 0
  · subst z; linarith
  by_cases hz1 : z = 1
  · subst z; linarith
  have hz' : 0 < z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
  have hz1' : z < 1 := lt_of_le_of_ne hz.2 hz1
  let A := 1/z + NeighborWeight m/(1-z)
  let t := Tail m z (fun _ => 1)
  have hA : 1 ≤ A := by
    have hrec : 1 ≤ 1/z := (le_div_iff₀ hz').mpr (by simpa using hz.2)
    have hnon : 0 ≤ NeighborWeight m/(1-z) := div_nonneg (neighbor_weight_nonneg m) (by linarith)
    dsimp [A]
    linarith
  have ht : |t| ≤ 1/16 := tail_bound m z hz (fun _ => 1) (by intros; norm_num)
  have hS : 0 < A+t := by have h := (abs_le.mp ht).1; linarith
  have heq := fractional_identity hm hp hz' hz1'
  have hrhs : |p.eval 0/z + NeighborWeight m*p.eval 1/(1-z) + Tail m z p.eval| ≤ A+1/16 := by
    calc
      _ ≤ |p.eval 0/z| + |NeighborWeight m*p.eval 1/(1-z)| + |Tail m z p.eval| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ 1/z + NeighborWeight m/(1-z) + 1/16 := by
        apply add_le_add
        · apply add_le_add
          · rw [abs_div,abs_of_pos hz']
            exact div_le_div_of_nonneg_right h0 hz'.le
          · rw [abs_div,abs_mul,abs_of_nonneg (neighbor_weight_nonneg m),abs_of_pos (by linarith : 0 < 1-z)]
            exact div_le_div_of_nonneg_right
              (mul_le_of_le_one_right (neighbor_weight_nonneg m) h1) (by linarith)
        · exact tail_bound m z hz p.eval hb
      _ = _ := rfl
  rw [← heq,abs_mul,abs_of_pos hS] at hrhs
  have htailnon : 0 ≤ (t+1/16)*|p.eval z| :=
    mul_nonneg (by have h := (abs_le.mp ht).1; linarith) (abs_nonneg _)
  have hbound : (A-1/16)*|p.eval z| ≤ A+1/16 := by dsimp [A,t] at *; nlinarith
  by_contra hn
  have hlarge : 4/3 < |p.eval z| := lt_of_not_ge hn
  have hprod := mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hlarge.le)
  nlinarith

end
end QuantumBipartiteTesting.Bipartiteness.GridProof

open QuantumBipartiteTesting.Bipartiteness.GridProof

theorem solution (m : ℕ) (hm : 0 < m) (p : Polynomial ℝ)
    (hp : p.natDegree < 2*m+2)
    (hb : ∀ x : ℤ, -(16*(m:ℤ)) ≤ x → x ≤ 16*(m:ℤ)+1 → |p.eval (x:ℝ)| ≤ 1) :
    ∀ z : ℝ, 0 ≤ z → z ≤ 1 → |p.eval z| ≤ 4/3 := by
  intro z hz hz1
  apply interior_bound hm hp
  · simpa using hb 0 (by omega) (by omega)
  · simpa using hb 1 (by omega) (by omega)
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    constructor
    · simpa using hb (16*(j:ℤ)) (by omega) (by omega)
    · simpa using hb (-16*(j:ℤ)) (by omega) (by omega)
  · exact ⟨hz,hz1⟩
