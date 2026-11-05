-- Prove2me | solution 2 for ToddKK14.Diameter.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:24:42.848205+00:00
-- url     : https://prove2.me/submissions/b6cc6ec5-fd84-48aa-9a10-d79745bbe767

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_ToddKK14_Diameter_Bound
import Theorems.Thm_ToddKK14_Diameter_log_swap
import Theorems.Thm_KalaiKleitman92_Diameter_recursion
import Theorems.Thm_ToddKK14_Diameter_base_eq
import Theorems.Thm_ToddKK14_Diameter_base_dim_one
import Theorems.Thm_Hirsch_plane_bound_general
import Theorems.Thm_ToddKK14_Diameter_facet_step
import Theorems.Thm_ToddKK14_Diameter_small_cases
import Theorems.Thm_ToddKK14_Diameter_general_step

open scoped RealInnerProductSpace

namespace ToddD3

open ToddKK14.Diameter

theorem le_rpow_of_pow_le {x c : ℝ} (hx : 0 < x) (hc : 0 ≤ c) (p q : ℕ) (hq : 0 < q)
    (h : c ^ q ≤ x ^ p) : c ≤ x ^ ((p : ℝ) / q) := by
  by_contra hlt
  push Not at hlt
  have h1 : (x ^ ((p : ℝ) / q)) ^ q < c ^ q :=
    pow_lt_pow_left₀ hlt (Real.rpow_nonneg hx.le _) hq.ne'
  rw [← Real.rpow_natCast (x ^ ((p : ℝ) / q)), ← Real.rpow_mul hx.le,
    div_mul_cancel₀ _ (by exact_mod_cast hq.ne'), Real.rpow_natCast] at h1
  linarith

theorem rpow_le_of_pow_le {x c : ℝ} (hx : 0 < x) (hc : 0 ≤ c) (p q : ℕ) (hq : 0 < q)
    (h : x ^ p ≤ c ^ q) : x ^ ((p : ℝ) / q) ≤ c := by
  by_contra hlt
  push Not at hlt
  have h1 : c ^ q < (x ^ ((p : ℝ) / q)) ^ q := pow_lt_pow_left₀ hlt hc hq.ne'
  rw [← Real.rpow_natCast (x ^ ((p : ℝ) / q)), ← Real.rpow_mul hx.le,
    div_mul_cancel₀ _ (by exact_mod_cast hq.ne'), Real.rpow_natCast] at h1
  linarith

theorem two_rpow_L : (2 : ℝ) ^ Real.logb 2 3 = 3 := Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

theorem pow_two_rpow_L (j : ℕ) : ((2 : ℝ) ^ j) ^ Real.logb 2 3 = 3 ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    two_rpow_L, Real.rpow_natCast]

theorem L_ge : (3 : ℝ) / 2 ≤ Real.logb 2 3 := by
  rw [Real.le_logb_iff_rpow_le one_lt_two (by norm_num)]
  have := rpow_le_of_pow_le (x := 2) (c := 3) (by norm_num) (by norm_num) 3 2 (by norm_num)
    (by norm_num)
  simpa using this

/-- `m ^ (L - 1)` lower bounds. -/
theorem s_ge_of_pow2 (m : ℝ) (j : ℕ) (hm : (2 : ℝ) ^ j ≤ m) :
    (3 / 2 : ℝ) ^ j ≤ m ^ (Real.logb 2 3 - 1) := by
  have hL : 0 ≤ Real.logb 2 3 - 1 := by linarith [L_ge]
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  calc (3 / 2 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ (Real.logb 2 3 - 1) := by
        rw [Real.rpow_sub h2, Real.rpow_one, pow_two_rpow_L, div_pow]
    _ ≤ m ^ (Real.logb 2 3 - 1) := Real.rpow_le_rpow h2.le hm hL

theorem toddBound_three (k : ℕ) (hk : 6 ≤ k + 1) :
    toddBound 2 k + 2 * toddBound 3 ((k + 1) / 2) + 2 ≤ toddBound 3 (k + 1) := by
  set L := Real.logb 2 3 with hLdef
  have hL1 : 0 ≤ L - 1 := by linarith [L_ge]
  have hb1 : toddBound 2 k = k - 2 := by
    unfold toddBound
    have : ((k : ℝ) - ((2 : ℕ) : ℝ)) = ((k - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
    rw [this]
    simp
  rw [hb1]
  set m : ℝ := ((k + 1 : ℕ) : ℝ) - 3 with hm
  have hm3 : (3 : ℝ) ≤ m := by
    have : (6 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hk
    linarith
  have hmpos : 0 < m := by linarith
  set s := m ^ (L - 1) with hs
  have hsnn : 0 ≤ s := Real.rpow_nonneg hmpos.le _
  -- second term
  have hb2 : (toddBound 3 ((k + 1) / 2) : ℝ) ≤ (m - 3) * s / 3 := by
    unfold toddBound
    have hge : 3 ≤ (k + 1) / 2 := by omega
    have hnn : (0 : ℝ) ≤ (((k + 1) / 2 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) := by
      have : ((3 : ℕ) : ℝ) ≤ (((k + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hge
      linarith
    have hhalf : (((k + 1) / 2 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) ≤ (m - 3) / 2 := by
      have : (((k + 1) / 2 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / 2 := Nat.cast_div_le
      have hm' : m = (k : ℝ) + 1 - 3 := by rw [hm]; push_cast; ring
      push_cast at this ⊢
      linarith
    have hm3' : 0 ≤ m - 3 := by linarith
    calc (⌊((((k + 1) / 2 : ℕ) : ℝ) - ((3 : ℕ) : ℝ)) ^ Real.logb 2 ((3 : ℕ) : ℝ)⌋₊ : ℝ)
        ≤ ((((k + 1) / 2 : ℕ) : ℝ) - ((3 : ℕ) : ℝ)) ^ Real.logb 2 ((3 : ℕ) : ℝ) :=
          Nat.floor_le (Real.rpow_nonneg hnn _)
      _ ≤ ((m - 3) / 2) ^ L := by
          rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]
          exact Real.rpow_le_rpow hnn hhalf (by linarith [L_ge])
      _ = (m - 3) ^ L / 3 := by
          rw [Real.div_rpow hm3' (by norm_num), hLdef, two_rpow_L]
      _ ≤ (m - 3) * s / 3 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          rw [show L = 1 + (L - 1) by ring, Real.rpow_add' hm3' (by linarith [L_ge]),
            Real.rpow_one]
          apply mul_le_mul_of_nonneg_left _ hm3'
          exact Real.rpow_le_rpow hm3' (by linarith) hL1
  have hmL : m ^ L = m * s := by
    rw [show L = 1 + (L - 1) by ring, Real.rpow_add hmpos, Real.rpow_one]
  -- key inequality 3m + 6 ≤ s (m + 6)
  have key : 3 * m + 6 ≤ s * (m + 6) := by
    rcases lt_or_ge m 4 with h4 | h4
    · -- m = 3
      have hm3e : m = 3 := by
        have : ((k + 1 : ℕ) : ℝ) < 7 := by linarith
        have hk7 : k + 1 < 7 := by exact_mod_cast this
        have : k + 1 = 6 := by omega
        rw [hm, this]; norm_num
      have hsq : (5 / 3 : ℝ) ≤ 3 ^ ((1 : ℕ) / (2 : ℕ) : ℝ) :=
        le_rpow_of_pow_le (by norm_num) (by norm_num) 1 2 (by norm_num) (by norm_num)
      have hs' : (3 : ℝ) ^ ((1 : ℕ) / (2 : ℕ) : ℝ) ≤ s := by
        rw [hs, hm3e]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        push_cast
        linarith [L_ge]
      rw [hm3e]
      nlinarith
    · rcases lt_or_ge m 8 with h8 | h8
      · have := s_ge_of_pow2 m 2 (by norm_num; linarith)
        nlinarith
      · have := s_ge_of_pow2 m 3 (by norm_num; linarith)
        nlinarith
  unfold toddBound
  apply Nat.le_floor
  have hk2 : ((k - 2 : ℕ) : ℝ) = m := by
    rw [Nat.cast_sub (by omega), hm]; push_cast; ring
  have hcast : (((k + 1 : ℕ) : ℝ) - ((3 : ℕ) : ℝ)) ^ Real.logb 2 ((3 : ℕ) : ℝ) = m * s := by
    rw [← hmL, hm, hLdef]; norm_num
  rw [hcast]
  push_cast
  rw [hk2]
  unfold toddBound at hb2
  nlinarith

end ToddD3

namespace ToddThm1Aux

open Hirsch ToddKK14.Diameter

/-- `DiamLE` is monotone in the bound (pad with stationary steps). -/
theorem diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E} {B B' : ℕ}
    (h : DiamLE P B) (hB : B ≤ B') : DiamLE P B' := by
  intro u hu v hv
  obtain ⟨w, h0, hBv, hs⟩ := h u hu v hv
  refine ⟨fun i => w (min i B), by simp [h0], by simp [min_eq_right hB, hBv], ?_⟩
  intro i _
  by_cases hi : i < B
  · have h1 : min i B = i := min_eq_left hi.le
    have h2 : min (i + 1) B = i + 1 := min_eq_left hi
    simp only [h1, h2]
    exact hs i hi
  · have h1 : min i B = B := min_eq_right (by omega)
    have h2 : min (i + 1) B = B := min_eq_right (by omega)
    left
    simp only [h1, h2]

theorem diamLE_of_extremePoints_empty {E : Type*} [AddCommGroup E] [Module ℝ E] {P : Set E}
    (h : Set.extremePoints ℝ P = ∅) (B : ℕ) : DiamLE P B := by
  intro u hu
  rw [h] at hu
  exact absurd hu (Set.notMem_empty u)

/-- A polyhedron with a nonzero direction orthogonal to all rows has no vertex. -/
theorem extremePoints_empty_of_kernel {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (z : EuclideanSpace ℝ (Fin d)) (hz : z ≠ 0) (h : ∀ i, ⟪a i, z⟫ = 0) :
    Set.extremePoints ℝ (Hpoly a b) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  rw [mem_extremePoints] at hx
  obtain ⟨hxP, hext⟩ := hx
  have hm : x - z ∈ Hpoly a b := by
    intro i
    rw [inner_sub_right, h i, sub_zero]
    exact hxP i
  have hp : x + z ∈ Hpoly a b := by
    intro i
    rw [inner_add_right, h i, add_zero]
    exact hxP i
  have hseg : x ∈ openSegment ℝ (x - z) (x + z) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have := (hext (x - z) hm (x + z) hp hseg).1
  apply hz
  have h2 : x - z - x = 0 := by rw [this, sub_self]
  simpa using h2

/-- Fewer than `d` rows: no vertex. -/
theorem extremePoints_empty_of_lt {d n : ℕ} (hnd : n < d) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) : Set.extremePoints ℝ (Hpoly a b) = ∅ := by
  let f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i => ((innerSL ℝ (a i) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ))
  have hker : LinearMap.ker f ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp [hnd]
  obtain ⟨z, hzk, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  apply extremePoints_empty_of_kernel a b z hz
  intro i
  have := congrFun (LinearMap.mem_ker.mp hzk) i
  simpa [f] using this

theorem toddBound_mono {d m m' : ℕ} (hd : 1 ≤ d) (hdm : d ≤ m) (hm : m ≤ m') :
    toddBound d m ≤ toddBound d m' := by
  unfold toddBound
  apply Nat.floor_mono
  apply Real.rpow_le_rpow
  · have : (d : ℝ) ≤ m := by exact_mod_cast hdm
    linarith
  · have : (m : ℝ) ≤ m' := by exact_mod_cast hm
    linarith
  · apply Real.logb_nonneg one_lt_two
    exact_mod_cast hd

/-- Statement with only nonzero rows. -/
def NZ (d c : ℕ) : Prop :=
  ∀ (a : Fin c → EuclideanSpace ℝ (Fin d)) (b : Fin c → ℝ), (∀ i, a i ≠ 0) →
    DiamLE (Hpoly a b) (toddBound d c)

/-- Statement allowing zero rows, counted by the number of nonzero rows. -/
def TT (d m : ℕ) : Prop :=
  ∀ (n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    (Finset.univ.filter (fun i => a i ≠ 0)).card ≤ m → DiamLE (Hpoly a b) (toddBound d m)

theorem reduce_zero_rows (d m : ℕ) (hd : 1 ≤ d) (hN : ∀ c, c ≤ m → d ≤ c → NZ d c) :
    TT d m := by
  intro n a b hcard
  by_cases hneg : ∃ i, a i = 0 ∧ b i < 0
  · obtain ⟨i, hi, hb⟩ := hneg
    apply diamLE_of_extremePoints_empty
    have : Hpoly a b = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      have := hx i
      rw [hi, inner_zero_left] at this
      linarith
    rw [this]
    simp
  · push Not at hneg
    let S := {i : Fin n // a i ≠ 0}
    let c := Fintype.card S
    have hc : c = (Finset.univ.filter (fun i => a i ≠ 0)).card := by
      simp only [c, S, Fintype.card_subtype]
    let e : Fin c ≃ S := (Fintype.equivFin S).symm
    let a' : Fin c → EuclideanSpace ℝ (Fin d) := fun j => a (e j).1
    let b' : Fin c → ℝ := fun j => b (e j).1
    have hset : Hpoly a b = Hpoly a' b' := by
      ext x
      constructor
      · intro hx j
        exact hx _
      · intro hx i
        by_cases hi : a i = 0
        · rw [hi, inner_zero_left]
          exact hneg i hi
        · have := hx (e.symm ⟨i, hi⟩)
          simpa [a', b'] using this
    rw [hset]
    by_cases hcd : c < d
    · exact diamLE_of_extremePoints_empty (extremePoints_empty_of_lt hcd a' b') _
    · push Not at hcd
      have hcm : c ≤ m := hc ▸ hcard
      have h1 := hN c hcm hcd a' b' (fun j => (e j).2)
      exact diamLE_mono h1 (toddBound_mono hd hcd hcm)

theorem toddBound_one (c : ℕ) : toddBound 1 c = 1 := by
  unfold toddBound
  simp

theorem toddBound_two (c : ℕ) (hc : 2 ≤ c) : toddBound 2 c = c - 2 := by
  unfold toddBound
  have : ((c : ℝ) - ((2 : ℕ) : ℝ)) = ((c - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hc]
  rw [this]
  simp

theorem toddBound_facet (d k : ℕ) (hd : 3 ≤ d) (hdk : d ≤ k + 1) :
    toddBound (d - 1) k ≤ toddBound d (k + 1) := by
  unfold toddBound
  have hx : ((k : ℝ) - ((d - 1 : ℕ) : ℝ)) = ((k + 1 - d : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hdk]
    push_cast
    ring
  have hx' : (((k + 1 : ℕ) : ℝ) - (d : ℝ)) = ((k + 1 - d : ℕ) : ℝ) := by
    rw [Nat.cast_sub hdk]
  rw [hx, hx']
  have hl1 : 0 < Real.logb 2 ((d - 1 : ℕ) : ℝ) := by
    apply Real.logb_pos one_lt_two
    have : 2 ≤ d - 1 := by omega
    exact_mod_cast (by omega : 1 < d - 1)
  have hl2 : Real.logb 2 ((d - 1 : ℕ) : ℝ) ≤ Real.logb 2 (d : ℝ) := by
    apply Real.logb_le_logb_of_le one_lt_two
    · exact_mod_cast (by omega : 0 < d - 1)
    · exact_mod_cast (by omega : d - 1 ≤ d)
  rcases Nat.eq_zero_or_pos (k + 1 - d) with h0 | hpos
  · rw [h0]
    simp only [Nat.cast_zero]
    rw [Real.zero_rpow hl1.ne']
    simp
  · apply Nat.floor_mono
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast hpos
    · exact hl2

theorem toddBound_general (d k : ℕ) (hd : 4 ≤ d) (hnd : d + 8 ≤ k + 1) (h2d : 2 * d ≤ k + 1) :
    toddBound (d - 1) k + 2 * toddBound d ((k + 1) / 2) + 2 ≤ toddBound d (k + 1) := by
  have key := general_step d (k + 1) hd hnd h2d
  have hs1 := log_swap (d - 1) k (by omega) (by omega)
  have hs2 := log_swap d (k + 1) (by omega) (by omega)
  have hd1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hk : ((k : ℝ) - ((d - 1 : ℕ) : ℝ)) = ((k + 1 : ℕ) : ℝ) - d := by
    rw [hd1]; push_cast; ring
  rw [hk, hd1] at hs1
  -- bound on the first term
  have hb1 : (toddBound (d - 1) k : ℝ) ≤ ((d : ℝ) - 1) ^ Real.logb 2 (((k + 1 : ℕ) : ℝ) - d) := by
    unfold toddBound
    rw [hk, hd1, ← hs1]
    apply Nat.floor_le
    apply Real.rpow_nonneg
    have : (d : ℝ) + 8 ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hnd
    linarith
  -- bound on the second term
  have hb2 : (toddBound d ((k + 1) / 2) : ℝ) ≤
      (((k + 1 : ℕ) : ℝ) / 2 - d) ^ Real.logb 2 d := by
    unfold toddBound
    have hge : d ≤ (k + 1) / 2 := by omega
    have hnn : (0 : ℝ) ≤ (((k + 1) / 2 : ℕ) : ℝ) - d := by
      have : (d : ℝ) ≤ (((k + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hge
      linarith
    calc (⌊((((k + 1) / 2 : ℕ) : ℝ) - d) ^ Real.logb 2 d⌋₊ : ℝ)
        ≤ ((((k + 1) / 2 : ℕ) : ℝ) - d) ^ Real.logb 2 d :=
          Nat.floor_le (Real.rpow_nonneg hnn _)
      _ ≤ _ := by
        apply Real.rpow_le_rpow hnn
        · have : (((k + 1) / 2 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / 2 := Nat.cast_div_le
          linarith
        · apply Real.logb_nonneg one_lt_two
          exact_mod_cast (by omega : 1 ≤ d)
  unfold toddBound at *
  apply Nat.le_floor
  rw [hs2]
  push_cast at hb1 hb2 key ⊢
  linarith

theorem toddBound_small (d k : ℕ) (hd : 4 ≤ d) (hnd : k + 1 < d + 8) (h2d : 2 * d ≤ k + 1) :
    toddBound (d - 1) k + 2 * toddBound d ((k + 1) / 2) + 2 ≤ toddBound d (k + 1) := by
  have h := small_cases d (k + 1) (by omega)
  simpa using h

theorem main (s : ℕ) : ∀ d m, d + m = s → 1 ≤ d → TT d m := by
  induction s using Nat.strong_induction_on with
  | _ s IH =>
  intro d m hs hd
  apply reduce_zero_rows d m hd
  intro c hcm hdc a b hane
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  by_cases hd1 : d = 1
  · subst hd1
    rw [toddBound_one]
    exact base_dim_one (k + 1) a b
  by_cases hd2 : d = 2
  · subst hd2
    rw [toddBound_two (k + 1) hdc]
    exact plane_bound_general (k + 1) a b hane
  have hd3 : 3 ≤ d := by omega
  -- the induction hypothesis in dimension d - 1 with k rows
  have IH1 : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      DiamLE (Hpoly a' b') (toddBound (d - 1) k) := by
    intro a' b'
    apply IH (d - 1 + k) (by omega) (d - 1) k rfl (by omega) k a' b'
    exact (Finset.card_filter_le _ _).trans (by simp)
  by_cases hsmall : k + 1 < 2 * d
  · exact diamLE_mono (facet_step d k hsmall a b hane _ IH1) (toddBound_facet d k hd3 hdc)
  push Not at hsmall
  have IH2 : ∀ F : Finset (Fin (k + 1)), F.card ≤ (k + 1) / 2 →
      DiamLE (Hpoly (fun i => if i ∈ F then a i else 0)
        (fun i => if i ∈ F then b i else 1)) (toddBound d ((k + 1) / 2)) := by
    intro F hF
    apply IH (d + (k + 1) / 2) (by omega) d ((k + 1) / 2) rfl hd (k + 1)
    refine le_trans (Finset.card_le_card ?_) hF
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_contra hiF
    exact hi (by simp [hiF])
  have hrec := KalaiKleitman92.Diameter.recursion d k a b hane _ _ IH1 IH2
  refine diamLE_mono hrec ?_
  by_cases hd3' : d = 3
  · subst hd3'
    exact ToddD3.toddBound_three k (by omega)
  have hd4 : 4 ≤ d := by omega
  by_cases hgen : d + 8 ≤ k + 1
  · exact toddBound_general d k hd4 hgen hsmall
  · exact toddBound_small d k hd4 (by omega) hsmall

end ToddThm1Aux

open Hirsch in
theorem solution (d n : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    DiamLE (Hpoly a b) ⌊((n : ℝ) - d) ^ Real.logb 2 d⌋₊ ∧
      (d = 1 → n = 1 → DiamLE (Hpoly a b) 0) := by
  refine ⟨?_, ?_⟩
  · have h := ToddThm1Aux.main (d + n) d n rfl hd n a b
      ((Finset.card_filter_le _ _).trans (by simp))
    exact h
  · intro h1 h2
    subst h1 h2
    exact ToddKK14.Diameter.base_eq 1 a b
