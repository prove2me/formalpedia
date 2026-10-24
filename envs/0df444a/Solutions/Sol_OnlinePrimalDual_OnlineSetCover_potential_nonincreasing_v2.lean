-- Prove2me | solution 1 for OnlinePrimalDual.OnlineSetCover.potential_nonincreasing_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:58:20.756023+00:00
-- url     : https://prove2.me/submissions/9e52c185-768b-470d-8112-bd32c919d7b7

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_potential

namespace SC88
open Real

lemma core (x y : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1/2) (hy : 0 ≤ y) :
    (1 - exp (-y)) * exp x * exp (-(3/2*x*y)) + exp (-y) * exp (-(3/2*x*y)) ≤ 1 := by
  have h1 : exp x - 1 ≤ 3/2 * x := by
    have := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_le]; constructor <;> linarith)
    have := (abs_le.mp this).2
    nlinarith
  have h2 : 1 - exp (-y) ≤ y := by linarith [add_one_le_exp (-y)]
  have h3 : 0 ≤ 1 - exp (-y) := by
    have : exp (-y) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    linarith
  have h4 : 0 ≤ exp x - 1 := by linarith [add_one_le_exp x]
  have h5 : 1 + 3/2*x*y ≤ exp (3/2*x*y) := by linarith [add_one_le_exp (3/2*x*y)]
  have h6 : exp (3/2*x*y) * exp (-(3/2*x*y)) = 1 := by rw [← exp_add]; simp
  have hE : 0 < exp (-(3/2*x*y)) := exp_pos _
  have h7 : (1 - exp (-y)) * (exp x - 1) ≤ 3/2*x*y := by
    calc (1 - exp (-y)) * (exp x - 1) ≤ y * (3/2*x) := mul_le_mul h2 h1 h4 hy
      _ = 3/2*x*y := by ring
  have : (1 - exp (-y)) * exp x * exp (-(3/2*x*y)) + exp (-y) * exp (-(3/2*x*y))
      = (1 + (1 - exp (-y)) * (exp x - 1)) * exp (-(3/2*x*y)) := by ring
  rw [this]
  calc (1 + (1 - exp (-y)) * (exp x - 1)) * exp (-(3/2*x*y))
      ≤ exp (3/2*x*y) * exp (-(3/2*x*y)) := by
        apply mul_le_mul_of_nonneg_right _ hE.le; linarith
    _ = 1 := h6

end SC88

open OnlinePrimalDual.OnlineSetCover in
theorem solution {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (hα_pos : 0 < α)
    (w w' : T → ℝ) (C : Finset T) (s : T) (hcs : inst.c s ≤ α)
    (hw'_off : ∀ t, t ≠ s → w' t = w t) (hw'_ge : w s ≤ w' s)
    (hE : 1 ≤ Fintype.card E) :
    let n : ℝ := (Fintype.card E : ℝ)
    let p : ℝ := 1 - n ^ (-2 * (w' s - w s))
    p * potential inst w' (insert s C) α + (1 - p) * potential inst w' C α ≤
      potential inst w C α := by
  classical
  intro n p
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hE
  have hn : 0 < n := by linarith
  set L := Real.log n with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hn1
  set δ := w' s - w s with hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hq : 1 - p = Real.exp (-(2*δ*L)) := by
    have h0 : 1 - p = n ^ (-2 * δ) := by simp only [p, δ]; ring
    rw [h0, Real.rpow_def_of_pos hn]; congr 1; ring
  -- element part
  have hrp : ∀ z : ℝ, n ^ z = Real.exp (L * z) := fun z => Real.rpow_def_of_pos hn z
  have hcov : ∀ e, coveredBy inst (insert s C) e ↔ coveredBy inst C e ∨ s ∈ inst.elemSets e := by
    intro e; unfold coveredBy; constructor
    · rintro ⟨t, ht, htC⟩
      rcases Finset.mem_insert.mp htC with h | h
      · subst h; exact Or.inr ht
      · exact Or.inl ⟨t, ht, h⟩
    · rintro (⟨t, ht, htC⟩ | h)
      · exact ⟨t, ht, Finset.mem_insert_of_mem htC⟩
      · exact ⟨s, h, Finset.mem_insert_self _ _⟩
  have hW_out : ∀ e, s ∉ inst.elemSets e → elementWeight inst w' e = elementWeight inst w e := by
    intro e he; unfold elementWeight
    apply Finset.sum_congr rfl; intro t ht
    exact hw'_off t (fun h => he (h ▸ ht))
  have hW_in : ∀ e, s ∈ inst.elemSets e → elementWeight inst w' e = elementWeight inst w e + δ := by
    intro e he; unfold elementWeight
    rw [← Finset.add_sum_erase _ _ he, ← Finset.add_sum_erase _ _ he]
    have : ∑ t ∈ (inst.elemSets e).erase s, w' t = ∑ t ∈ (inst.elemSets e).erase s, w t := by
      apply Finset.sum_congr rfl; intro t ht
      exact hw'_off t (Finset.ne_of_mem_erase ht)
    rw [this, hδ]; ring
  have hA : p * (∑ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst (insert s C) e),
        n ^ (2 * elementWeight inst w' e)) +
      (1 - p) * (∑ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e),
        n ^ (2 * elementWeight inst w' e)) =
      ∑ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e),
        n ^ (2 * elementWeight inst w e) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hC : coveredBy inst C e
    · have : coveredBy inst (insert s C) e := (hcov e).mpr (Or.inl hC)
      simp [hC, this]
    · by_cases hs : s ∈ inst.elemSets e
      · have : coveredBy inst (insert s C) e := (hcov e).mpr (Or.inr hs)
        simp only [hC, this, not_true_eq_false, not_false_eq_true, if_true, if_false, mul_zero,
          zero_add]
        rw [hW_in e hs, hq, hrp, hrp, ← Real.exp_add]; ring_nf
      · have : ¬ coveredBy inst (insert s C) e := by
          rw [hcov]; tauto
        simp only [hC, this, not_false_eq_true, if_true]
        rw [hW_out e hs]; ring
  -- exponential part
  set a := 1 / (2 * α) with ha
  have ha0 : 0 < a := by positivity
  set c := inst.c s with hc
  have hc0 : 0 < c := inst.hc_pos s
  set R := ∑ t ∈ Finset.univ.erase s,
      (inst.c t * (if t ∈ C then (1 : ℝ) else 0) - 3 * w t * inst.c t * L) with hR
  have hsplit : ∀ (v : T → ℝ) (D : Finset T),
      ∑ t : T, (inst.c t * (if t ∈ D then (1 : ℝ) else 0) - 3 * v t * inst.c t * L) =
        (c * (if s ∈ D then (1 : ℝ) else 0) - 3 * v s * c * L) +
        ∑ t ∈ Finset.univ.erase s,
          (inst.c t * (if t ∈ D then (1 : ℝ) else 0) - 3 * v t * inst.c t * L) :=
    fun v D => (Finset.add_sum_erase _ _ (Finset.mem_univ s)).symm
  have hR1 : ∑ t ∈ Finset.univ.erase s,
      (inst.c t * (if t ∈ C then (1 : ℝ) else 0) - 3 * w' t * inst.c t * L) = R := by
    apply Finset.sum_congr rfl; intro t ht
    rw [hw'_off t (Finset.ne_of_mem_erase ht)]
  have hR2 : ∑ t ∈ Finset.univ.erase s,
      (inst.c t * (if t ∈ insert s C then (1 : ℝ) else 0) - 3 * w' t * inst.c t * L) = R := by
    apply Finset.sum_congr rfl; intro t ht
    have hts := Finset.ne_of_mem_erase ht
    rw [hw'_off t hts]
    simp [Finset.mem_insert, hts]
  set χ : ℝ := if s ∈ C then (1 : ℝ) else 0 with hχ
  have hχ0 : 0 ≤ χ := by simp only [χ]; split_ifs <;> norm_num
  have hS0 := hsplit w C
  have hS1 := hsplit w' C
  have hS2 := hsplit w' (insert s C)
  rw [hR1] at hS1
  rw [hR2] at hS2
  simp only [Finset.mem_insert_self, if_true] at hS2
  set B := a * (c * χ - 3 * w s * c * L + R) with hB
  set x := a * c with hx
  set y := 2 * δ * L with hy
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1/2 := by
    simp only [x, a]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
  have hy0 : 0 ≤ y := by positivity
  have hcore := SC88.core x y hx0 hx1 hy0
  have hp0 : 0 ≤ p := by
    have : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have e1 : a * ((c * 1 - 3 * w' s * c * L) + R) ≤ B + x + (-(3/2*x*y)) := by
    simp only [B, x, y, δ]
    have : a * c * χ ≥ 0 := by positivity
    nlinarith
  have e2 : a * ((c * χ - 3 * w' s * c * L) + R) = B + (-(3/2*x*y)) := by
    simp only [B, x, y, δ, a]; field_simp; ring
  have hX : p * Real.exp (a * ((c * 1 - 3 * w' s * c * L) + R)) +
      (1 - p) * Real.exp (a * ((c * χ - 3 * w' s * c * L) + R)) ≤ Real.exp B := by
    rw [e2, hq]
    calc p * Real.exp (a * ((c * 1 - 3 * w' s * c * L) + R)) +
          Real.exp (-y) * Real.exp (B + -(3 / 2 * x * y))
        ≤ p * Real.exp (B + x + (-(3/2*x*y))) + Real.exp (-y) * Real.exp (B + -(3 / 2 * x * y)) := by
          gcongr
      _ = Real.exp B * ((1 - Real.exp (-y)) * Real.exp x * Real.exp (-(3/2*x*y)) +
            Real.exp (-y) * Real.exp (-(3/2*x*y))) := by
          rw [show p = 1 - Real.exp (-y) by linarith [hq]]
          simp only [Real.exp_add]; ring
      _ ≤ Real.exp B * 1 := by gcongr
      _ = Real.exp B := mul_one _
  unfold potential
  simp only []
  rw [← hR] at hS0
  have hn' : (Fintype.card E : ℝ) = n := rfl
  rw [hS0, hS1, hS2, ← ha, ← hχ, hn']
  calc _ = (p * (∑ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst (insert s C) e),
        n ^ (2 * elementWeight inst w' e)) +
      (1 - p) * (∑ e ∈ Finset.univ.filter (fun e => ¬ coveredBy inst C e),
        n ^ (2 * elementWeight inst w' e))) +
      n * (p * Real.exp (a * ((c * 1 - 3 * w' s * c * L) + R)) +
      (1 - p) * Real.exp (a * ((c * χ - 3 * w' s * c * L) + R))) := by ring
    _ ≤ _ := by rw [hA]; gcongr
