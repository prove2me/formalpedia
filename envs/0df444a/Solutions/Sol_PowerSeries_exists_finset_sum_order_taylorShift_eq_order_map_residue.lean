-- Prove2me | solution 1 for PowerSeries.exists_finset_sum_order_taylorShift_eq_order_map_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1d55ecf8-419d-5411-a4ad-0cee8f2fd5b2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_exists_finset_sum_order_taylorShift_eq_order_map_residue

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
        rw [← pow_add]
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
p2m_reactivate "P2MW.S_PowerSeries_exists_finset_sum_order_taylorShift_eq_order_map_residue.CuspDisc"

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

variable [IsDomain O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
variable [CompleteSpace L] [IsUltrametricDist L] [IsAlgClosed L]

theorem order_coe_eq_natTrailingDegree {p : L[X]} (hp : p ≠ 0) :
    ((p : L⟦X⟧)).order = p.natTrailingDegree := by
  refine PowerSeries.order_eq_nat.mpr ⟨?_, fun i hi => ?_⟩
  · rw [Polynomial.coeff_coe]
    exact mt Polynomial.trailingCoeff_eq_zero.mp hp
  · rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi

theorem order_T_coe (p : L[X]) (hp : p ≠ 0) (r : L) :
    (T r (p : L⟦X⟧)).order = p.rootMultiplicity r := by
  rw [T_coe, rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
  have hne : taylor r p ≠ 0 := fun h0 => hp (by
    have := congrArg (taylor (-r)) h0
    rwa [taylor_taylor, neg_add_cancel, taylor_zero', LinearMap.map_zero] at this)
  exact order_coe_eq_natTrailingDegree hne

theorem norm_map_unit (ι : O →+* L) (hι1 : ∀ x, ‖ι x‖ ≤ 1) {a : O} (ha : IsUnit a) : ‖ι a‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have h1 : ‖ι (u : O)‖ * ‖ι (↑u⁻¹ : O)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have ha := hι1 (u : O)
  have hb := hι1 (↑u⁻¹ : O)
  by_contra hne
  have hlt : ‖ι (u : O)‖ < 1 := lt_of_le_of_ne ha hne
  have : ‖ι (u : O)‖ * ‖ι (↑u⁻¹ : O)‖ < 1 := by
    calc ‖ι (u : O)‖ * ‖ι (↑u⁻¹ : O)‖ ≤ ‖ι (u : O)‖ * 1 :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hlt
  exact absurd h1 this.ne

theorem exists_finset_sum_order_T_eq (ι : O →+* L) (hι : Function.Injective ι) (hι1 : ∀ x, ‖ι x‖ ≤ 1)
    (hιm : ∀ x ∈ maximalIdeal O, ‖ι x‖ < 1)
    (F : PowerSeries O) (hF : F.map (residue O) ≠ 0) :
    ∃ S : Finset L, (∀ r, r ∈ S ↔ ‖r‖ < 1 ∧ 0 < (T r (F.map ι)).order) ∧
      ∑ r ∈ S, (T r (F.map ι)).order = (F.map (residue O)).order := by
  classical
  obtain ⟨ω, u, hfac⟩ := PowerSeries.exists_isWeierstrassFactorization hF
  have hω0 : ω.map ι ≠ 0 := (hfac.isDistinguishedAt.monic.map ι).ne_zero
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have hωB : Bdd 1 ((ω.map ι : L[X]) : L⟦X⟧) := by
    have := bdd_map ι hι1 (ω : PowerSeries O)
    rwa [← Polynomial.polynomial_map_coe] at this
  have huB : Bdd 1 (u.map ι) := bdd_map ι hι1 _
  have hFL : F.map ι = ((ω.map ι : L[X]) : L⟦X⟧) * u.map ι := by
    rw [hfac.eq_mul, map_mul, ← Polynomial.polynomial_map_coe]

  have hu0 : ‖constantCoeff (u.map ι)‖ = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact norm_map_unit ι hι1 (PowerSeries.isUnit_constantCoeff _ hfac.isUnit)
  have horder : ∀ r : L, ‖r‖ < 1 → (T r (F.map ι)).order = (ω.map ι).rootMultiplicity r := by
    intro r hr
    have hρ0 : (0 : ℝ) ≤ ‖r‖ := norm_nonneg _
    rw [hFL, T_mul hρ0 hr h01 h01 le_rfl hωB huB, PowerSeries.order_mul, order_T_coe _ hω0]
    have hc : constantCoeff (T r (u.map ι)) ≠ 0 :=
      constantCoeff_T_ne_zero huB hu0 hr
    have : (T r (u.map ι)).order = 0 := by
      rw [← ENat.coe_zero, PowerSeries.order_eq_nat]
      refine ⟨by simp at hc ⊢; exact hc, fun i hi => (Nat.not_lt_zero i hi).elim⟩
    rw [this, add_zero]
  refine ⟨(ω.map ι).roots.toFinset, fun r => ?_, ?_⟩
  · rw [Multiset.mem_toFinset, mem_roots hω0]
    constructor
    · intro hroot
      have hr : ‖r‖ < 1 := norm_root_lt_one ι hιm hfac.isDistinguishedAt hroot
      refine ⟨hr, ?_⟩
      rw [horder r hr, Nat.cast_pos]
      exact (rootMultiplicity_pos hω0).mpr hroot
    · rintro ⟨hr, hpos⟩
      rw [horder r hr, Nat.cast_pos] at hpos
      exact (rootMultiplicity_pos hω0).mp hpos
  · have hsum : ∑ r ∈ (ω.map ι).roots.toFinset, (T r (F.map ι)).order
        = ∑ r ∈ (ω.map ι).roots.toFinset, ((ω.map ι).rootMultiplicity r : ℕ∞) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Multiset.mem_toFinset, mem_roots hω0] at hr
      exact horder r (norm_root_lt_one ι hιm hfac.isDistinguishedAt hr)
    rw [hsum, ← Nat.cast_sum]
    have hcount : ∑ r ∈ (ω.map ι).roots.toFinset, (ω.map ι).rootMultiplicity r = (ω.map ι).natDegree := by
      simp_rw [← count_roots]
      rw [Multiset.toFinset_sum_count_eq, ← (IsAlgClosed.splits _).natDegree_eq_card_roots]
    rw [hcount, (hfac.isDistinguishedAt.monic).natDegree_map, hfac.natDegree_eq_toNat_order_map,
      ENat.coe_toNat]
    exact PowerSeries.order_finite_iff_ne_zero.mpr hF |>.ne

end Weier
p2m_reactivate "P2MW.S_PowerSeries_exists_finset_sum_order_taylorShift_eq_order_map_residue.CuspDisc"

end CuspDisc
p2m_reactivate "P2MW.S_PowerSeries_exists_finset_sum_order_taylorShift_eq_order_map_residue.CuspDisc"

theorem solution
    {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [IsAlgClosed L]
    (ι : O →+* L) (hι : Function.Injective ι) (hι1 : ∀ x, ‖ι x‖ ≤ 1)
    (hιm : ∀ x ∈ IsLocalRing.maximalIdeal O, ‖ι x‖ < 1)
    (F : PowerSeries O) (hF : F.map (IsLocalRing.residue O) ≠ 0) :
    ∃ S : Finset L, (∀ r, r ∈ S ↔ ‖r‖ < 1 ∧
        0 < (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (F.map ι) * ((n + k).choose n : L) * r ^ k).order) ∧
      ∑ r ∈ S, (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) (F.map ι) * ((n + k).choose n : L) * r ^ k).order
        = (F.map (IsLocalRing.residue O)).order :=
  CuspDisc.exists_finset_sum_order_T_eq ι hι hι1 hιm F hF

end
end S_PowerSeries_exists_finset_sum_order_taylorShift_eq_order_map_residue
end P2MW
export P2MW.S_PowerSeries_exists_finset_sum_order_taylorShift_eq_order_map_residue (solution)
