-- Prove2me | solution 1 for PowerSeries.dvd_of_forall_taylorShift_order_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bce9c8df-1619-5fb5-a98a-85ae84a4ee96

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open PowerSeries Polynomial Filter Topology

namespace CuspDisc

section Defs

variable {L : Type*} [NormedField L]

def Small (ρ C : ℝ) (m : ℕ) (P : L⟦X⟧) : Prop := ∀ k, ‖coeff k P‖ ≤ C * ρ ^ (m - k)

def Bdd (C : ℝ) (P : L⟦X⟧) : Prop := ∀ k, ‖coeff k P‖ ≤ C

theorem small_zero_iff {ρ C : ℝ} {P : L⟦X⟧} : Small ρ C 0 P ↔ Bdd C P := by
  simp [Small, Bdd]

theorem Small.bdd {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (h : Small ρ C m P) : Bdd C P := fun k =>
  (h k).trans (mul_le_of_le_one_right hC (pow_le_one₀ hρ0 hρ1))

theorem Small.anti {ρ C : ℝ} {m m' : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hm : m' ≤ m) (h : Small ρ C m P) : Small ρ C m' P := fun k =>
  (h k).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1 (by omega)) hC)

theorem small_of_coeff_eq_zero {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hC : 0 ≤ C)
    (hb : Bdd C P) (hz : ∀ k < m, coeff k P = 0) : Small ρ C m P := by
  intro k
  by_cases hk : k < m
  · rw [hz k hk, norm_zero]; exact mul_nonneg hC (pow_nonneg hρ0 _)
  · have : m - k = 0 := by omega
    simpa [this] using hb k

theorem Small.neg {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hP : Small ρ C m P) : Small ρ C m (-P) := fun k => by
  simpa using hP k

theorem Small.mono_C {ρ C C' : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hCC' : C ≤ C')
    (hP : Small ρ C m P) : Small ρ C' m P := fun k =>
  (hP k).trans (mul_le_mul_of_nonneg_right hCC' (pow_nonneg hρ0 _))

variable (r : L)

def tcoeff (P : L⟦X⟧) (n : ℕ) : L := ∑' k : ℕ, coeff (n + k) P * ((n + k).choose n : L) * r ^ k

private def _root_.CuspDisc.T (P : L⟦X⟧) : L⟦X⟧ := PowerSeries.mk (tcoeff r P)

p2m_export "CuspDisc" "T"
@[scoped simp] theorem coeff_T (P : L⟦X⟧) (n : ℕ) : coeff n (T r P) = tcoeff r P n := by
  simp [T]

variable {r}

theorem T_neg (P : L⟦X⟧) : T r (-P) = -T r P := by
  ext n
  simp only [coeff_T, map_neg, tcoeff]
  rw [← tsum_neg]; congr 1; ext k; ring

@[scoped simp] theorem T_zero' : T r (0 : L⟦X⟧) = 0 := by
  ext n; simp [tcoeff]

theorem T_coe (p : L[X]) : T r (p : L⟦X⟧) = ((taylor r p : L[X]) : L⟦X⟧) := by
  ext n
  rw [coeff_T, Polynomial.coeff_coe, taylor_coeff, tcoeff]
  have hM : (hasseDeriv n p).natDegree < p.natDegree + 1 :=
    Nat.lt_succ_of_le ((natDegree_hasseDeriv_le p n).trans (Nat.sub_le _ _))
  rw [eval_eq_sum_range' hM, tsum_eq_sum (s := Finset.range (p.natDegree + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hasseDeriv_coeff, Polynomial.coeff_coe, Nat.add_comm k n]
    ring
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

theorem T_X : T r (PowerSeries.X : L⟦X⟧) = PowerSeries.X + PowerSeries.C r := by
  have := T_coe (r := r) (Polynomial.X : L[X])
  simpa [taylor_X] using this

theorem T_C (a : L) : T r (PowerSeries.C a : L⟦X⟧) = PowerSeries.C a := by
  have := T_coe (r := r) (Polynomial.C a : L[X])
  simpa [taylor_C] using this

@[scoped simp] theorem T_one : T r (1 : L⟦X⟧) = 1 := by
  simpa using T_C (r := r) (1 : L)

theorem constantCoeff_T (P : L⟦X⟧) : constantCoeff (T r P) = ∑' k : ℕ, coeff k P * r ^ k := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_T, tcoeff]
  congr 1; ext k; simp

end Defs

section Ultra

variable {L : Type*} [NormedField L] [IsUltrametricDist L]

theorem Small.add {ρ C : ℝ} {m : ℕ} {P Q : L⟦X⟧} (hP : Small ρ C m P) (hQ : Small ρ C m Q) :
    Small ρ C m (P + Q) := fun k => by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hP k) (hQ k))

theorem Small.sub {ρ C : ℝ} {m : ℕ} {P Q : L⟦X⟧} (hP : Small ρ C m P) (hQ : Small ρ C m Q) :
    Small ρ C m (P - Q) := by
  simpa [sub_eq_add_neg] using hP.add hQ.neg

theorem Bdd.add {C : ℝ} {P Q : L⟦X⟧} (hP : Bdd C P) (hQ : Bdd C Q) : Bdd C (P + Q) :=
  small_zero_iff.mp ((small_zero_iff (ρ := 1)).mpr hP |>.add (small_zero_iff.mpr hQ))

theorem Bdd.sub {C : ℝ} {P Q : L⟦X⟧} (hP : Bdd C P) (hQ : Bdd C Q) : Bdd C (P - Q) :=
  small_zero_iff.mp ((small_zero_iff (ρ := 1)).mpr hP |>.sub (small_zero_iff.mpr hQ))

theorem Small.mul {ρ C C' : ℝ} {m : ℕ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hC' : 0 ≤ C') (hP : Small ρ C m P) (hQ : Bdd C' Q) : Small ρ (C * C') m (P * Q) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (mul_nonneg hC hC') (pow_nonneg hρ0 _)) fun ij hij => ?_
  have hi : ij.1 ≤ n := Finset.HasAntidiagonal.antidiagonal.fst_le hij
  calc ‖coeff ij.1 P * coeff ij.2 Q‖ = ‖coeff ij.1 P‖ * ‖coeff ij.2 Q‖ := norm_mul _ _
    _ ≤ (C * ρ ^ (m - ij.1)) * C' :=
        mul_le_mul (hP _) (hQ _) (norm_nonneg _) (mul_nonneg hC (pow_nonneg hρ0 _))
    _ = (C * C') * ρ ^ (m - ij.1) := by ring
    _ ≤ (C * C') * ρ ^ (m - n) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0 hρ1 (by omega)) (mul_nonneg hC hC')

theorem Bdd.mul_small {ρ C C' : ℝ} {m : ℕ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hC' : 0 ≤ C') (hP : Bdd C P) (hQ : Small ρ C' m Q) : Small ρ (C * C') m (P * Q) := by
  rw [mul_comm P Q, mul_comm C C']
  exact hQ.mul hρ0 hρ1 hC' hC hP

theorem Bdd.mul {C C' : ℝ} {P Q : L⟦X⟧} (hC : 0 ≤ C) (hC' : 0 ≤ C') (hP : Bdd C P) (hQ : Bdd C' Q) :
    Bdd (C * C') (P * Q) := by
  rw [← small_zero_iff (ρ := (1/2 : ℝ))] at hP ⊢
  exact hP.mul (by norm_num) (by norm_num) hC hC' hQ

theorem eq_zero_of_forall_small {ρ C : ℝ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ m, Small ρ C m P) : P = 0 := by
  ext k
  rw [map_zero]
  have hlim : Tendsto (fun j : ℕ => C * ρ ^ j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C
  have hle : ∀ j, ‖coeff k P‖ ≤ C * ρ ^ j := fun j => by
    simpa using h (k + j) k
  have : ‖coeff k P‖ ≤ 0 := ge_of_tendsto' hlim hle
  exact norm_le_zero_iff.mp this

variable {r : L}

theorem norm_term_le {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Small ρ C m P) (n k : ℕ) :
    ‖coeff (n + k) P * ((n + k).choose n : L) * r ^ k‖ ≤ C * ρ ^ (m - n) := by
  have h1 : ‖((n + k).choose n : L)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one L _
  calc ‖coeff (n + k) P * ((n + k).choose n : L) * r ^ k‖
      = ‖coeff (n + k) P‖ * ‖((n + k).choose n : L)‖ * ‖r‖ ^ k := by
        rw [norm_mul, norm_mul, norm_pow]
    _ ≤ (C * ρ ^ (m - (n + k))) * 1 * ρ ^ k :=
        mul_le_mul (mul_le_mul (hP _) h1 (norm_nonneg _) (mul_nonneg hC (pow_nonneg hρ0 _)))
          (pow_le_pow_left₀ (norm_nonneg _) hr k) (pow_nonneg (norm_nonneg _) _)
          (mul_nonneg (mul_nonneg hC (pow_nonneg hρ0 _)) zero_le_one)
    _ = C * (ρ ^ (m - (n + k)) * ρ ^ k) := by ring
    _ ≤ C * ρ ^ (m - n) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        rw [← _root_.pow_add]
        exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)

theorem norm_tcoeff_le {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Small ρ C m P) (n : ℕ) : ‖tcoeff r P n‖ ≤ C * ρ ^ (m - n) :=
  IsUltrametricDist.norm_tsum_le_of_forall_le fun k => norm_term_le hρ0 hρ1 hC hr hP n k

theorem Small.T {ρ C : ℝ} {m : ℕ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Small ρ C m P) : Small ρ C m (T r P) := fun n => by
  rw [coeff_T]; exact norm_tcoeff_le hρ0 hρ1 hC hr hP n

theorem Bdd.T {ρ C : ℝ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) : Bdd C (T r P) :=
  small_zero_iff.mp ((small_zero_iff.mpr hP).T hρ0 hρ1 hC hr)

end Ultra

section Complete

variable {L : Type*} [NormedField L] [CompleteSpace L] [IsUltrametricDist L] {r : L}

theorem summable_term {ρ C : ℝ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) (n : ℕ) :
    Summable fun k : ℕ => coeff (n + k) P * ((n + k).choose n : L) * r ^ k := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_left C) fun k => ?_
  have h1 : ‖((n + k).choose n : L)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one L _
  calc ‖coeff (n + k) P * ((n + k).choose n : L) * r ^ k‖
      = ‖coeff (n + k) P‖ * ‖((n + k).choose n : L)‖ * ‖r‖ ^ k := by
        rw [norm_mul, norm_mul, norm_pow]
    _ ≤ C * 1 * ρ ^ k :=
        mul_le_mul (mul_le_mul (hP _) h1 (norm_nonneg _) hC)
          (pow_le_pow_left₀ (norm_nonneg _) hr k) (pow_nonneg (norm_nonneg _) _)
          (mul_nonneg hC zero_le_one)
    _ = C * ρ ^ k := by ring

theorem T_add {ρ C C' : ℝ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) (hQ : Bdd C' Q) : T r (P + Q) = T r P + T r Q := by
  ext n
  simp only [coeff_T, map_add, tcoeff]
  rw [← (summable_term hρ0 hρ1 hC hr hP n).tsum_add (summable_term hρ0 hρ1 hC' hr hQ n)]
  congr 1; ext k; ring

theorem T_sub {ρ C C' : ℝ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) (hQ : Bdd C' Q) : T r (P - Q) = T r P - T r Q := by
  rw [sub_eq_add_neg, T_add hρ0 hρ1 hC hC' hr hP (by simpa [Bdd] using hQ), T_neg, sub_eq_add_neg]

theorem T_mul {ρ C C' : ℝ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) (hQ : Bdd C' Q) : T r (P * Q) = T r P * T r Q := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_small (ρ := ρ) (C := C * C') hρ0 hρ1 fun m => ?_
  have hρ1' := hρ1.le

  obtain ⟨p, hp⟩ : ∃ p : L⟦X⟧, p = ((trunc m P : L[X]) : L⟦X⟧) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : L⟦X⟧, q = ((trunc m Q : L[X]) : L⟦X⟧) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := hC
  have hpB : Bdd C p := fun k => by
    rw [hp, Polynomial.coeff_coe, coeff_trunc]
    split_ifs
    · exact hP k
    · rw [norm_zero]; exact hC
  have hqB : Bdd C' q := fun k => by
    rw [hq, Polynomial.coeff_coe, coeff_trunc]
    split_ifs
    · exact hQ k
    · rw [norm_zero]; exact hC'
  have hP'S : Small ρ C m (P - p) := by
    refine small_of_coeff_eq_zero hρ0 hC (hP.sub hpB) fun k hk => ?_
    rw [map_sub, hp, Polynomial.coeff_coe, coeff_trunc, if_pos hk, sub_self]
  have hQ'S : Small ρ C' m (Q - q) := by
    refine small_of_coeff_eq_zero hρ0 hC' (hQ.sub hqB) fun k hk => ?_
    rw [map_sub, hq, Polynomial.coeff_coe, coeff_trunc, if_pos hk, sub_self]
  have hP'B : Bdd C (P - p) := hP'S.bdd hρ0 hρ1' hC
  have hQ'B : Bdd C' (Q - q) := hQ'S.bdd hρ0 hρ1' hC'

  have hpq : T r (p * q) = T r p * T r q := by
    rw [hp, hq, ← Polynomial.coe_mul, T_coe, T_coe, T_coe, taylor_mul, Polynomial.coe_mul]

  have hE : P * Q = p * q + ((P - p) * Q + p * (Q - q)) := by ring
  have hES : Small ρ (C * C') m ((P - p) * Q + p * (Q - q)) :=
    (hP'S.mul hρ0 hρ1' hC hC' hQ).add (hpB.mul_small hρ0 hρ1' hC hC' hQ'S)
  have hEB : Bdd (C * C') ((P - p) * Q + p * (Q - q)) := hES.bdd hρ0 hρ1' (mul_nonneg hC hC')
  have h1 : T r (P * Q) = T r p * T r q + T r ((P - p) * Q + p * (Q - q)) := by
    rw [hE, T_add hρ0 hρ1 (mul_nonneg hC hC') (mul_nonneg hC hC') hr (hpB.mul hC hC' hqB) hEB, hpq]
  have h2 : T r P = T r p + T r (P - p) := by
    conv_lhs => rw [show P = p + (P - p) by ring]
    exact T_add hρ0 hρ1 hC hC hr hpB hP'B
  have h3 : T r Q = T r q + T r (Q - q) := by
    conv_lhs => rw [show Q = q + (Q - q) by ring]
    exact T_add hρ0 hρ1 hC' hC' hr hqB hQ'B
  have h4 : T r (P * Q) - T r P * T r Q
      = T r ((P - p) * Q + p * (Q - q))
        - (T r p * T r (Q - q) + T r (P - p) * T r q + T r (P - p) * T r (Q - q)) := by
    rw [h1, h2, h3]; ring
  rw [h4]
  refine (hES.T hρ0 hρ1' (mul_nonneg hC hC') hr).sub ?_
  refine ((hpB.T hρ0 hρ1' hC hr).mul_small hρ0 hρ1' hC hC' (hQ'S.T hρ0 hρ1' hC' hr)).add
    ((hP'S.T hρ0 hρ1' hC hr).mul hρ0 hρ1' hC hC' (hqB.T hρ0 hρ1' hC' hr)) |>.add ?_
  exact (hP'S.T hρ0 hρ1' hC hr).mul hρ0 hρ1' hC hC' (hQ'B.T hρ0 hρ1' hC' hr)

theorem T_T {ρ C : ℝ} {P : L⟦X⟧} {s : L} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hs : ‖s‖ ≤ ρ) (hP : Bdd C P) : T s (T r P) = T (s + r) P := by
  have hρ1' := hρ1.le
  have hsr : ‖s + r‖ ≤ ρ := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hs hr)
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_small (ρ := ρ) (C := C) hρ0 hρ1 fun m => ?_
  obtain ⟨p, hp⟩ : ∃ p : L⟦X⟧, p = ((trunc m P : L[X]) : L⟦X⟧) := ⟨_, rfl⟩
  have hpB : Bdd C p := fun k => by
    rw [hp, Polynomial.coeff_coe, coeff_trunc]
    split_ifs
    · exact hP k
    · rw [norm_zero]; exact hC
  have hP'S : Small ρ C m (P - p) := by
    refine small_of_coeff_eq_zero hρ0 hC (hP.sub hpB) fun k hk => ?_
    rw [map_sub, hp, Polynomial.coeff_coe, coeff_trunc, if_pos hk, sub_self]
  have hP'B : Bdd C (P - p) := hP'S.bdd hρ0 hρ1' hC
  have hpp : T s (T r p) = T (s + r) p := by
    rw [hp, T_coe, T_coe, T_coe, taylor_taylor]
  have h2 : T r P = T r p + T r (P - p) := by
    conv_lhs => rw [show P = p + (P - p) by ring]
    exact T_add hρ0 hρ1 hC hC hr hpB hP'B
  have h3 : T (s + r) P = T (s + r) p + T (s + r) (P - p) := by
    conv_lhs => rw [show P = p + (P - p) by ring]
    exact T_add hρ0 hρ1 hC hC hsr hpB hP'B
  have h4 : T s (T r P) - T (s + r) P = T s (T r (P - p)) - T (s + r) (P - p) := by
    rw [h2, T_add hρ0 hρ1 hC hC hs (hpB.T hρ0 hρ1' hC hr) (hP'B.T hρ0 hρ1' hC hr), hpp, h3]
    ring
  rw [h4]
  exact ((hP'S.T hρ0 hρ1' hC hr).T hρ0 hρ1' hC hs).sub (hP'S.T hρ0 hρ1' hC hsr)

omit [CompleteSpace L] [IsUltrametricDist L] in
theorem T_zero_left (P : L⟦X⟧) : T (0 : L) P = P := by
  ext n
  rw [coeff_T, tcoeff, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

theorem T_injective {ρ C : ℝ} {P Q : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) (hQ : Bdd C Q) (h : T r P = T r Q) : P = Q := by
  have hnr : ‖-r‖ ≤ ρ := by rwa [norm_neg]
  have := congrArg (T (-r)) h
  rwa [T_T hρ0 hρ1 hC hr hnr hP, T_T hρ0 hρ1 hC hr hnr hQ, neg_add_cancel,
    T_zero_left, T_zero_left] at this

theorem T_eq_zero_iff {ρ C : ℝ} {P : L⟦X⟧} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hC : 0 ≤ C)
    (hr : ‖r‖ ≤ ρ) (hP : Bdd C P) : T r P = 0 ↔ P = 0 := by
  refine ⟨fun h => T_injective hρ0 hρ1 hC hr hP (fun k => by simpa using hC) ?_, fun h => by simp [h]⟩
  rw [h, T_zero']

theorem constantCoeff_T_ne_zero {u : L⟦X⟧} (hu : Bdd 1 u) (hu0 : ‖constantCoeff u‖ = 1)
    (hr : ‖r‖ < 1) : constantCoeff (T r u) ≠ 0 := by
  intro h0
  rw [constantCoeff_T] at h0
  have hsum : Summable fun k : ℕ => coeff k u * r ^ k := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hr) fun k => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) (hu k)
  have hsplit := hsum.tsum_eq_zero_add
  rw [h0] at hsplit
  simp only [pow_zero, mul_one, coeff_zero_eq_constantCoeff] at hsplit
  have htail : ‖∑' k : ℕ, coeff (k + 1) u * r ^ (k + 1)‖ ≤ ‖r‖ := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le fun k => ?_
    rw [norm_mul, norm_pow]
    calc ‖coeff (k + 1) u‖ * ‖r‖ ^ (k + 1) ≤ 1 * ‖r‖ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (hu _) (pow_nonneg (norm_nonneg _) _)
      _ ≤ ‖r‖ := by
          rw [one_mul, pow_succ]
          exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hr.le)
  have : ‖constantCoeff u‖ ≤ ‖r‖ := by
    have h' : constantCoeff u = -∑' k : ℕ, coeff (k + 1) u * r ^ (k + 1) := by
      linear_combination -hsplit
    rw [h', norm_neg]; exact htail
  linarith

end Complete

end CuspDisc
p2m_reactivate "P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le.CuspDisc"

namespace CuspDisc

section Weier

open Polynomial IsLocalRing

variable {O : Type*} [CommRing O]
variable {L : Type*} [NontriviallyNormedField L]

theorem bdd_map (ι : O →+* L) (hι1 : ∀ x, ‖ι x‖ ≤ 1) (P : PowerSeries O) : Bdd 1 (P.map ι) := fun k => by
  rw [PowerSeries.coeff_map]; exact hι1 _

theorem norm_root_lt_one [IsLocalRing O] [IsUltrametricDist L] (ι : O →+* L)
    (hιm : ∀ x ∈ maximalIdeal O, ‖ι x‖ < 1) {ω : O[X]} (hω : ω.IsDistinguishedAt (maximalIdeal O)) {r : L}
    (hr : (ω.map ι).IsRoot r) : ‖r‖ < 1 := by
  by_contra h
  have h' : 1 ≤ ‖r‖ := not_lt.mp h
  have hr1 : 0 < ‖r‖ := lt_of_lt_of_le one_pos h'
  have hmonic : (ω.map ι).Monic := hω.monic.map ι
  have hdeg : (ω.map ι).natDegree = ω.natDegree := hω.monic.natDegree_map ι
  have heval : (ω.map ι).eval r = 0 := hr
  rw [eval_eq_sum_range, Finset.sum_range_succ, hmonic.coeff_natDegree, one_mul,
    add_eq_zero_iff_neg_eq] at heval

  have hlow : ‖∑ i ∈ Finset.range (ω.map ι).natDegree, (ω.map ι).coeff i * r ^ i‖
      < ‖r‖ ^ (ω.map ι).natDegree := by
    rcases Nat.eq_zero_or_pos (ω.map ι).natDegree with hd0 | hd0
    · rw [hd0]; simp
    have hne : (Finset.range (ω.map ι).natDegree).Nonempty := ⟨0, Finset.mem_range.mpr hd0⟩
    obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun i => (ω.map ι).coeff i * r ^ i)
    refine lt_of_le_of_lt hle ?_
    rw [norm_mul, norm_pow]
    have hid : i < (ω.map ι).natDegree := Finset.mem_range.mp hi
    have hci : ‖(ω.map ι).coeff i‖ < 1 := by
      rw [Polynomial.coeff_map]
      exact hιm _ (hω.mem (by rwa [hdeg] at hid))
    calc ‖(ω.map ι).coeff i‖ * ‖r‖ ^ i < 1 * ‖r‖ ^ i :=
          mul_lt_mul_of_pos_right hci (pow_pos hr1 _)
      _ ≤ ‖r‖ ^ (ω.map ι).natDegree := by rw [one_mul]; exact pow_le_pow_right₀ h' hid.le
  have hlt : ‖r ^ (ω.map ι).natDegree‖ < ‖r‖ ^ (ω.map ι).natDegree := by
    rw [← heval, norm_neg]; exact hlow
  rw [norm_pow] at hlt
  exact lt_irrefl _ hlt

theorem le_rootMultiplicity_of_le_order {p : L[X]} (hp : p ≠ 0) {r : L} {m : ℕ}
    (h : (m : ℕ∞) ≤ (T r (p : L⟦X⟧)).order) : m ≤ p.rootMultiplicity r := by
  rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
  rw [T_coe] at h
  have hne : taylor r p ≠ 0 := fun h0 => hp (by
    have := congrArg (taylor (-r)) h0
    rwa [taylor_taylor, neg_add_cancel, taylor_zero', LinearMap.map_zero] at this)
  refine le_natTrailingDegree hne fun i hi => ?_
  have := PowerSeries.coeff_of_lt_order i (lt_of_lt_of_le (by exact_mod_cast hi) h)
  rwa [Polynomial.coeff_coe] at this

variable [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
variable [CompleteSpace L] [IsUltrametricDist L] [IsAlgClosed L]

theorem dvd_of_forall_order_le (ι : O →+* L) (hι : Function.Injective ι) (hι1 : ∀ x, ‖ι x‖ ≤ 1)
    (hιm : ∀ x ∈ maximalIdeal O, ‖ι x‖ < 1)
    (P Q : PowerSeries O) (hQ : Q.map (residue O) ≠ 0)
    (hgood : ∀ r : L, ‖r‖ < 1 → (T r (Q.map ι)).order ≤ (T r (P.map ι)).order) :
    ∃ G : PowerSeries O, P = Q * G := by
  classical
  obtain ⟨ω, u, hfac⟩ := PowerSeries.exists_isWeierstrassFactorization hQ
  obtain ⟨G, R, hdiv⟩ := PowerSeries.exists_isWeierstrassDivision P hQ
  have hdeg : R.degree < (ω.natDegree : WithBot ℕ) := by
    rw [hfac.natDegree_eq_toNat_order_map]; exact hdiv.degree_lt
  refine ⟨G, ?_⟩
  suffices hR : R = 0 by rw [hdiv.eq_mul_add, hR, Polynomial.coe_zero, add_zero]
  by_contra hR0
  have hRL0 : R.map ι ≠ 0 := fun h => hR0 ((Polynomial.map_eq_zero_iff hι).mp h)
  have hωL0 : ω.map ι ≠ 0 := (hfac.isDistinguishedAt.monic.map ι).ne_zero

  have hmult : ∀ r : L, (ω.map ι).rootMultiplicity r ≤ (R.map ι).rootMultiplicity r := by
    intro r
    by_cases hroot : (ω.map ι).IsRoot r
    swap
    · rw [rootMultiplicity_eq_zero hroot]; exact Nat.zero_le _
    have hr : ‖r‖ < 1 := norm_root_lt_one ι hιm hfac.isDistinguishedAt hroot
    apply le_rootMultiplicity_of_le_order hRL0
    have hρ0 : (0 : ℝ) ≤ ‖r‖ := norm_nonneg _
    have h01 : (0 : ℝ) ≤ 1 := zero_le_one
    have hPB := bdd_map ι hι1 P
    have hQB := bdd_map ι hι1 Q
    have hGB := bdd_map ι hι1 G
    have huB := bdd_map ι hι1 u
    have hωB : Bdd 1 ((ω.map ι : L[X]) : L⟦X⟧) := by
      have := bdd_map ι hι1 (ω : PowerSeries O)
      rwa [← Polynomial.polynomial_map_coe] at this
    have hRB : Bdd 1 ((R.map ι : L[X]) : L⟦X⟧) := by
      have := bdd_map ι hι1 (R : PowerSeries O)
      rwa [← Polynomial.polynomial_map_coe] at this
    have hPL : P.map ι = Q.map ι * G.map ι + ((R.map ι : L[X]) : L⟦X⟧) := by
      rw [hdiv.eq_mul_add, map_add, map_mul, ← Polynomial.polynomial_map_coe]
    have hQL : Q.map ι = ((ω.map ι : L[X]) : L⟦X⟧) * u.map ι := by
      rw [hfac.eq_mul, map_mul, ← Polynomial.polynomial_map_coe]
    have hQGB : Bdd (1 * 1) (Q.map ι * G.map ι) := hQB.mul h01 h01 hGB
    have hTR : T r ((R.map ι : L[X]) : L⟦X⟧) = T r (P.map ι) - T r (Q.map ι) * T r (G.map ι) := by
      rw [hPL, T_add hρ0 hr (mul_nonneg h01 h01) h01 le_rfl hQGB hRB,
        T_mul hρ0 hr h01 h01 le_rfl hQB hGB]
      ring
    have hTQ : T r (Q.map ι) = T r ((ω.map ι : L[X]) : L⟦X⟧) * T r (u.map ι) := by
      rw [hQL, T_mul hρ0 hr h01 h01 le_rfl hωB huB]
    have hordω : ((ω.map ι).rootMultiplicity r : ℕ∞) ≤ (T r ((ω.map ι : L[X]) : L⟦X⟧)).order := by
      rw [T_coe, rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
      refine PowerSeries.nat_le_order _ _ fun i hi => ?_
      rw [Polynomial.coeff_coe]
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi
    have h1 : ((ω.map ι).rootMultiplicity r : ℕ∞) ≤ (T r (Q.map ι)).order := by
      rw [hTQ]
      exact hordω.trans (by rw [PowerSeries.order_mul]; exact le_self_add)
    have h2 : ((ω.map ι).rootMultiplicity r : ℕ∞) ≤ (T r (P.map ι)).order := h1.trans (hgood r hr)
    rw [hTR, sub_eq_add_neg]
    refine le_trans ?_ (PowerSeries.min_order_le_order_add _ _)
    rw [le_min_iff, PowerSeries.order_neg, PowerSeries.order_mul]
    exact ⟨h2, h1.trans le_self_add⟩

  have hdvd : ω.map ι ∣ R.map ι := by
    rw [IsAlgClosed.dvd_iff_roots_le_roots hωL0 hRL0, Multiset.le_iff_count]
    intro a
    rw [count_roots, count_roots]
    exact hmult a
  have h1 := Polynomial.natDegree_le_of_dvd hdvd hRL0
  have h2 : (R.map ι).natDegree ≤ R.natDegree := natDegree_map_le
  have h3 : (ω.map ι).natDegree = ω.natDegree := (hfac.isDistinguishedAt.monic).natDegree_map ι
  have h4 : R.natDegree < ω.natDegree := (natDegree_lt_iff_degree_lt hR0).mpr hdeg
  omega

end Weier
p2m_reactivate "P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le.CuspDisc"

theorem solution
    {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [IsAlgClosed L]
    (ι : O →+* L) (hι : Function.Injective ι) (hι1 : ∀ x, ‖ι x‖ ≤ 1)
    (hιm : ∀ x ∈ IsLocalRing.maximalIdeal O, ‖ι x‖ < 1)
    (P Q : PowerSeries O) (hQ : Q.map (IsLocalRing.residue O) ≠ 0)
    (h : ∀ r : L, ‖r‖ < 1 →
      (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (Q.map ι) * ((n + k).choose n : L) * r ^ k).order
        ≤ (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (P.map ι) * ((n + k).choose n : L) * r ^ k).order) :
    Q ∣ P :=
  CuspDisc.dvd_of_forall_order_le ι hι hι1 hιm P Q hQ h

end
end S_PowerSeries_dvd_of_forall_taylorShift_order_le
end P2MW
export P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le (solution)
