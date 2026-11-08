-- Prove2me | solution 1 for PolarizedLearning.piMinus_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:03:15.029264+00:00
-- url     : https://prove2.me/submissions/1af41ff9-17f2-42f5-b6c9-0482880b1f8d

import Mathlib
import Definitions.Def_PolarizedLearning_Model

namespace PolarizedLearning

namespace Aux_PL

theorem hmono {x a b : ℝ} (hx0 : 0 ≤ x) (ha : x ≤ a) (hab : a < b) (hb : b < 1) (ha0 : 0 < a) :
    x * Real.log b + (1 - x) * Real.log (1 - b) < x * Real.log a + (1 - x) * Real.log (1 - a) := by
  have hx1 : x < 1 := by linarith
  have hb0 : 0 < b := by linarith
  have h1 : 1 - (a / b)⁻¹ ≤ Real.log (a / b) := Real.one_sub_inv_le_log_of_pos (div_pos ha0 hb0)
  have e1 : Real.log (a / b) = Real.log a - Real.log b := Real.log_div (ne_of_gt ha0) (ne_of_gt hb0)
  have t : 0 < (1 - b) / (1 - a) := div_pos (by linarith) (by linarith)
  have hne : (1 - b) / (1 - a) ≠ 1 := by
    intro h
    rw [div_eq_one_iff_eq (by linarith)] at h
    linarith
  have h2 : Real.log ((1 - b) / (1 - a)) < (1 - b) / (1 - a) - 1 := Real.log_lt_sub_one_of_pos t hne
  have e2 : Real.log ((1 - b) / (1 - a)) = Real.log (1 - b) - Real.log (1 - a) :=
    Real.log_div (by linarith) (by linarith)
  rw [inv_div, e1] at h1
  rw [e2] at h2
  have k1 : x * (1 - b / a) ≤ x * (Real.log a - Real.log b) := mul_le_mul_of_nonneg_left h1 hx0
  have k2 : (1 - x) * (Real.log (1 - b) - Real.log (1 - a)) < (1 - x) * ((1 - b) / (1 - a) - 1) :=
    mul_lt_mul_of_pos_left h2 (by linarith)
  have k3 : -(x * (1 - b / a)) + (1 - x) * ((1 - b) / (1 - a) - 1) ≤ 0 := by
    have ha1 : (1 - a) ≠ 0 := by linarith
    have e : -(x * (1 - b / a)) + (1 - x) * ((1 - b) / (1 - a) - 1)
        = (b - a) * (x - a) / (a * (1 - a)) := by
      field_simp <;> ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [mul_nonneg (sub_nonneg.2 hab.le) (sub_nonneg.2 ha)]
    · exact (mul_pos ha0 (by linarith)).le
  linarith

theorem theta_bounds (P : Params) {π v : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) (v0 : 0 ≤ v) (v1 : v ≤ 1) :
    0 < theta P π v ∧ theta P π v < 1 := by
  have hHL := P.hLH
  have hp := P.hp
  have hLp := P.hLp
  have hHp := P.hHp
  unfold theta
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hHL.le) h0, mul_nonneg hp.le v0]
  · nlinarith [mul_nonneg (sub_nonneg.2 hHL.le) (sub_nonneg.2 h1), mul_nonneg hp.le (sub_nonneg.2 v1)]

theorem B0_iff (P : Params) (b : ℝ × ℝ) :
    b ∈ B0 P ↔ (0 ≤ b.1 ∧ b.1 ≤ 1) ∧ (P.u - P.eps ≤ b.2 ∧ b.2 ≤ P.u + P.eps) := by
  simp only [B0, Set.mem_prod, Set.mem_Icc]

theorem mem_Pi (P : Params) (x : ℝ) (b : ℝ × ℝ) (h1 : b ∈ B0 P)
    (h2 : ∀ b' ∈ B0 P, normLoglik P x b'.1 b'.2 ≤ normLoglik P x b.1 b.2) : b.1 ∈ Pi P x := by
  have : b ∈ mlSet P x := by
    simp only [mlSet, Set.mem_setOf_eq]
    exact ⟨h1, h2⟩
  simp only [Pi]
  exact Set.mem_image_of_mem _ this

theorem Pi_bounds (P : Params) (x : ℝ) {z : ℝ} (hz : z ∈ Pi P x) : 0 ≤ z ∧ z ≤ 1 := by
  simp only [Pi, Set.mem_image] at hz
  obtain ⟨b, hb, rfl⟩ := hz
  have h := hb
  simp only [mlSet, Set.mem_setOf_eq] at h
  exact ((B0_iff P b).1 h.1).1

theorem exists_max (P : Params) (x : ℝ) :
    ∃ b ∈ B0 P, ∀ b' ∈ B0 P, normLoglik P x b'.1 b'.2 ≤ normLoglik P x b.1 b.2 := by
  have hK : IsCompact (B0 P) := by
    unfold B0
    exact isCompact_Icc.prod isCompact_Icc
  have hne : (B0 P).Nonempty := ⟨(0, P.u), by
    rw [B0_iff]
    have := P.heps
    refine ⟨⟨le_refl _, zero_le_one⟩, by linarith, by linarith⟩⟩
  have hc : ContinuousOn (fun b : ℝ × ℝ => normLoglik P x b.1 b.2) (B0 P) := by
    have hpos : ∀ b ∈ B0 P, 0 < theta P b.1 b.2 ∧ theta P b.1 b.2 < 1 := by
      intro b hb
      rw [B0_iff] at hb
      have := P.hlo
      have := P.hhi
      exact theta_bounds P hb.1.1 hb.1.2 (by linarith [hb.2.1]) (by linarith [hb.2.2])
    have hθc : Continuous (fun b : ℝ × ℝ => theta P b.1 b.2) := by
      unfold theta
      fun_prop
    unfold normLoglik
    apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.log hθc.continuousOn (fun b hb => ne_of_gt (hpos b hb).1)
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.log (by fun_prop)
      intro b hb
      have := (hpos b hb).2
      exact ne_of_gt (by linarith)
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne hc
  exact ⟨b, hb, fun b' hb' => (isMaxOn_iff.mp hmax) b' hb'⟩

end Aux_PL

end PolarizedLearning

open PolarizedLearning PolarizedLearning.Aux_PL in
theorem solution (P : Params) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (x ≤ P.H + P.p * (2 * P.u - 1) → piMinus P x < 1) ∧
    (P.L + P.p * (2 * P.u - 1) ≤ x → 0 < piPlus P x) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hHL := P.hLH
  have hp := P.hp
  have hLp := P.hLp
  have hHp := P.hHp
  have heps := P.heps
  have hlo := P.hlo
  have hhi := P.hhi
  have hu0 := P.hu0
  have hu1 := P.hu1
  obtain ⟨⟨π0, u0⟩, hb, hmax⟩ := exists_max P x
  have hb' := (B0_iff P _).1 hb
  simp only at hb'
  obtain ⟨⟨hπa, hπb⟩, hua, hub⟩ := hb'
  have hbdd_below : BddBelow (Pi P x) := ⟨0, fun z hz => (Pi_bounds P x hz).1⟩
  have hbdd_above : BddAbove (Pi P x) := ⟨1, fun z hz => (Pi_bounds P x hz).2⟩
  constructor
  · intro hxle
    have key : ∃ q ∈ Pi P x, q < 1 := by
      rcases lt_or_ge π0 1 with h | h
      · exact ⟨π0, mem_Pi P x (π0, u0) hb hmax, h⟩
      · have hπ1 : π0 = 1 := le_antisymm hπb h
        rcases lt_or_ge u0 (P.u + P.eps) with hu | hu
        · set δ := min 1 (2 * P.p * (P.u + P.eps - u0) / (P.H - P.L)) with hδ
          have hδ0 : 0 < δ := lt_min one_pos (div_pos (by nlinarith) (by linarith))
          have hδ1 : δ ≤ 1 := min_le_left _ _
          have hδ2 : δ ≤ 2 * P.p * (P.u + P.eps - u0) / (P.H - P.L) := min_le_right _ _
          have hδ3 : δ * (P.H - P.L) / (2 * P.p) ≤ P.u + P.eps - u0 := by
            rw [div_le_iff₀ (by linarith)]
            rw [le_div_iff₀ (by linarith)] at hδ2
            linarith
          have hδ4 : 0 ≤ δ * (P.H - P.L) / (2 * P.p) :=
            div_nonneg (mul_nonneg hδ0.le (by linarith)) (by linarith)
          refine ⟨1 - δ, mem_Pi P x (1 - δ, u0 + δ * (P.H - P.L) / (2 * P.p)) ?_ ?_, by linarith⟩
          · rw [B0_iff]
            exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
          · intro b' hb''
            have hm := hmax b' hb''
            have e : theta P (1 - δ) (u0 + δ * (P.H - P.L) / (2 * P.p)) = theta P π0 u0 := by
              rw [hπ1]
              unfold theta
              field_simp <;> ring
            simp only at hm ⊢
            unfold normLoglik at hm ⊢
            rw [e]
            exact hm
        · exfalso
          have hm := hmax (1, P.u) (by
            rw [B0_iff]
            exact ⟨⟨zero_le_one, le_refl _⟩, by linarith, by linarith⟩)
          simp only at hm
          unfold normLoglik at hm
          have hθa : theta P 1 P.u = P.H + P.p * (2 * P.u - 1) := by unfold theta; ring
          have hθb : theta P π0 u0 = P.H + P.p * (2 * u0 - 1) := by rw [hπ1]; unfold theta; ring
          have hlt := hmono hx0 (a := theta P 1 P.u) (b := theta P π0 u0)
            (by rw [hθa]; exact hxle) (by rw [hθa, hθb]; nlinarith)
            (by rw [hθb]; nlinarith) (by rw [hθa]; nlinarith)
          linarith
    obtain ⟨q, hq, hq1⟩ := key
    exact lt_of_le_of_lt (csInf_le hbdd_below hq) hq1
  · intro hxge
    have key : ∃ q ∈ Pi P x, 0 < q := by
      rcases lt_or_ge 0 π0 with h | h
      · exact ⟨π0, mem_Pi P x (π0, u0) hb hmax, h⟩
      · have hπ0 : π0 = 0 := le_antisymm h hπa
        rcases lt_or_ge (P.u - P.eps) u0 with hu | hu
        · set δ := min 1 (2 * P.p * (u0 - (P.u - P.eps)) / (P.H - P.L)) with hδ
          have hδ0 : 0 < δ := lt_min one_pos (div_pos (by nlinarith) (by linarith))
          have hδ1 : δ ≤ 1 := min_le_left _ _
          have hδ2 : δ ≤ 2 * P.p * (u0 - (P.u - P.eps)) / (P.H - P.L) := min_le_right _ _
          have hδ3 : δ * (P.H - P.L) / (2 * P.p) ≤ u0 - (P.u - P.eps) := by
            rw [div_le_iff₀ (by linarith)]
            rw [le_div_iff₀ (by linarith)] at hδ2
            linarith
          have hδ4 : 0 ≤ δ * (P.H - P.L) / (2 * P.p) :=
            div_nonneg (mul_nonneg hδ0.le (by linarith)) (by linarith)
          refine ⟨δ, mem_Pi P x (δ, u0 - δ * (P.H - P.L) / (2 * P.p)) ?_ ?_, hδ0⟩
          · rw [B0_iff]
            exact ⟨⟨hδ0.le, hδ1⟩, by linarith, by linarith⟩
          · intro b' hb''
            have hm := hmax b' hb''
            have e : theta P δ (u0 - δ * (P.H - P.L) / (2 * P.p)) = theta P π0 u0 := by
              rw [hπ0]
              unfold theta
              field_simp <;> ring
            simp only at hm ⊢
            unfold normLoglik at hm ⊢
            rw [e]
            exact hm
        · exfalso
          have hm := hmax (0, P.u) (by
            rw [B0_iff]
            exact ⟨⟨le_refl _, zero_le_one⟩, by linarith, by linarith⟩)
          simp only at hm
          unfold normLoglik at hm
          have hθa : theta P 0 P.u = P.L + P.p * (2 * P.u - 1) := by unfold theta; ring
          have hθb : theta P π0 u0 = P.L + P.p * (2 * u0 - 1) := by rw [hπ0]; unfold theta; ring
          have hlt := hmono (x := 1 - x) (a := 1 - theta P 0 P.u) (b := 1 - theta P π0 u0)
            (by linarith) (by rw [hθa]; linarith) (by rw [hθa, hθb]; nlinarith)
            (by rw [hθb]; nlinarith) (by rw [hθa]; nlinarith)
          simp only [sub_sub_cancel] at hlt
          linarith
    obtain ⟨q, hq, hq1⟩ := key
    exact lt_of_lt_of_le hq1 (le_csSup hbdd_above hq)
