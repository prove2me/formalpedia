-- Prove2me | solution 1 for SurelyBetter.CLB.theorem2_violation
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:12:44.355991+00:00
-- url     : https://prove2.me/submissions/ee741285-7ac9-4f76-bd32-d6b854f9365a

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_SurelyBetter_CLB_Model
import Theorems.Thm_SurelyBetter_CLB_theorem2_interior_optimum

open SurelyBetter.CLB

namespace ViolationAux

theorem violation_of_interior {S : Type*} [Fintype S] (U : Set ℝ) (hU : Convex ℝ U)
    (hU2 : ∃ a ∈ U, ∃ b ∈ U, a ≠ b) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ)
    (hV : IsCLinBisep U V ρ) (E : Set S) (hρ : ρ E + ρ Eᶜ < 1)
    (hopt : ∀ (x y w z : ℝ), x ∈ U → y ∈ U → w ∈ U → z ∈ U →
      y < x → w < z → w < x → y < z →
      ρ E * (x - w) < (1 - ρ E) * (z - y) →
      ρ Eᶜ * (z - y) < (1 - ρ Eᶜ) * (x - w) →
      optMix V (binProf E x y) (binProf E w z) = {1 / (1 + (x - y) / (z - w))}) :
    ¬ MOMOn V (measE U E) := by
  classical
  have huv : ∃ u ∈ U, ∃ v ∈ U, u < v := by
    obtain ⟨u, hu, v, hv, huv⟩ := hU2
    rcases lt_or_gt_of_ne huv with hlt | hgt
    · exact ⟨u, hu, v, hv, hlt⟩
    · exact ⟨v, hv, u, hu, hgt⟩
  obtain ⟨u, hu, v, hv, huv⟩ := huv
  have hp0 : 0 ≤ ρ E := by
    rw [← hV.capacity.1]
    exact hV.capacity.2.2 ∅ E (Set.empty_subset E)
  have hq0 : 0 ≤ ρ Eᶜ := by
    rw [← hV.capacity.1]
    exact hV.capacity.2.2 ∅ Eᶜ (Set.empty_subset Eᶜ)
  have hp1 : ρ E ≤ 1 := by linarith
  have hq1 : ρ Eᶜ < 1 := by linarith
  let δ := 1 - ρ E - ρ Eᶜ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let A := ρ Eᶜ + δ / 3
  let A' := ρ Eᶜ + 2 * δ / 3
  let B := 1 - A
  have hA0 : 0 < A := by dsimp [A]; linarith
  have hAA' : A < A' := by dsimp [A, A']; linarith
  have hA'1 : A' < 1 := by dsimp [A', δ]; linarith
  have hA1 : A < 1 := hAA'.trans hA'1
  have hB0 : 0 < B := sub_pos.mpr hA1
  have hB1 : B < 1 := by dsimp [B]; linarith
  have hsum : A + B = 1 := by dsimp [B]; ring
  have hlo : ρ E * A < (1 - ρ E) * B := by
    dsimp [A, B, δ]
    nlinarith
  have hlo' : ρ E * A' < (1 - ρ E) * B := by
    have hn := mul_nonneg (sub_nonneg.mpr hp1) hδ.le
    dsimp [A, A', B, δ] at *
    nlinarith
  have hhi : ρ Eᶜ * B < (1 - ρ Eᶜ) * A := by
    dsimp [A, B, δ]
    nlinarith
  have hhi' : ρ Eᶜ * B < (1 - ρ Eᶜ) * A' :=
    hhi.trans (mul_lt_mul_of_pos_left hAA' (sub_pos.mpr hq1))
  have mem (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : u + r * (v - u) ∈ U := by
    convert hU hu hv (sub_nonneg.mpr hr1) hr0 (by ring) using 1
    dsimp
    ring
  let x := u + A * (v - u)
  let x' := u + A' * (v - u)
  let z := u + B * (v - u)
  have hx : x ∈ U := mem A hA0.le hA1.le
  have hx' : x' ∈ U := mem A' (hA0.trans hAA').le hA'1.le
  have hz : z ∈ U := mem B hB0.le hB1.le
  have hD : 0 < v - u := sub_pos.mpr huv
  have hux : u < x := by dsimp [x]; nlinarith [mul_pos hA0 hD]
  have hxx' : x < x' := by
    have hm := mul_lt_mul_of_pos_right hAA' hD
    dsimp [x, x']
    linarith
  have hux' : u < x' := hux.trans hxx'
  have huz : u < z := by dsimp [z]; nlinarith [mul_pos hB0 hD]
  have lift_lo (r : ℝ) (hr : ρ E * r < (1 - ρ E) * B) :
      ρ E * ((u + r * (v - u)) - u) < (1 - ρ E) * (z - u) := by
    dsimp [z]
    nlinarith [mul_lt_mul_of_pos_right hr hD]
  have lift_hi (r : ℝ) (hr : ρ Eᶜ * B < (1 - ρ Eᶜ) * r) :
      ρ Eᶜ * (z - u) < (1 - ρ Eᶜ) * ((u + r * (v - u)) - u) := by
    dsimp [z]
    nlinarith [mul_lt_mul_of_pos_right hr hD]
  have opt := hopt x u u z hx hu hu hz hux huz hux huz (lift_lo A hlo) (lift_hi A hhi)
  have opt' := hopt x' u u z hx' hu hu hz hux' huz hux' huz (lift_lo A' hlo') (lift_hi A' hhi')
  let a := 1 / (1 + (x - u) / (z - u))
  let b := 1 / (1 + (x' - u) / (z - u))
  have hba : b < a := by
    apply one_div_lt_one_div_of_lt
    · have hd := div_pos (sub_pos.mpr hux) (sub_pos.mpr huz)
      linarith
    · simpa only [add_comm] using add_lt_add_left
        (div_lt_div_of_pos_right (sub_lt_sub_right hxx' u) (sub_pos.mpr huz)) 1
  intro hM
  have hfg : ∀ s, binProf E x u s ≤ binProf E x' u s := by
    intro s
    by_cases hs : s ∈ E <;> simp [binProf, hs, hxx'.le]
  have ha : a ∈ optMix V (binProf E x u) (binProf E u z) := by rw [opt]; exact rfl
  have hb : b ∈ optMix V (binProf E x' u) (binProf E u z) := by rw [opt']; exact rfl
  have hord := hM (binProf E x u) ⟨x, hx, u, hu, rfl⟩
    (binProf E x' u) ⟨x', hx', u, hu, rfl⟩ (binProf E u z) ⟨u, hu, z, hz, rfl⟩ hfg ha hb
  have hbad : b = a := by
    have hmin := hord.1
    rw [inf_eq_right.mpr hba.le, opt] at hmin
    exact hmin
  exact (ne_of_lt hba) hbad

end ViolationAux

theorem solution {S : Type*} [Fintype S] (U : Set ℝ) (hU : Convex ℝ U)
    (hU2 : ∃ a ∈ U, ∃ b ∈ U, a ≠ b) (V : (S → ℝ) → ℝ) (ρ : Set S → ℝ)
    (hV : IsCLinBisep U V ρ) (E : Set S) :
    ρ E + ρ Eᶜ < 1 → ¬ MOMOn V (measE U E) := by
  intro hρ
  apply ViolationAux.violation_of_interior U hU hU2 V ρ hV E hρ
  exact SurelyBetter.CLB.theorem2_interior_optimum U hU hU2 V ρ hV E hρ
