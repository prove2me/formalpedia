-- Prove2me | solution 1 for PeriodicDividend.FixedPoint.theorem_3_3_D
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:42:51.208347+00:00
-- url     : https://prove2.me/submissions/bbd006e9-1fb0-46b3-8400-3d3138e6aac4

import Mathlib
import Definitions.Def_PeriodicDividend_FixedPoint_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace PDSol33D
open PeriodicDividend.FixedPoint

lemma D_bdd (φ : ℝ≥0 → ℝ) (A : ℝ) (hb : ∀ y, φ y ≤ (y : ℝ) + A) (x : ℝ≥0) :
    BddAbove {y : ℝ | ∃ d : ℝ≥0, d ≤ x ∧ y = φ (x - d) + (d : ℝ)} := by
  refine ⟨(x : ℝ) + A, ?_⟩
  rintro y ⟨d, hd, rfl⟩
  have h1 := hb (x - d)
  rw [NNReal.coe_sub hd] at h1
  linarith

lemma le_D (φ : ℝ≥0 → ℝ) (A : ℝ) (hb : ∀ y, φ y ≤ (y : ℝ) + A) (x y : ℝ≥0)
    (hy : y ≤ x) : φ y + ((x : ℝ) - y) ≤ Dop φ x := by
  apply le_csSup (D_bdd φ A hb x)
  refine ⟨x - y, tsub_le_self, ?_⟩
  rw [tsub_tsub_cancel_of_le hy, NNReal.coe_sub hy]

lemma D_le (φ : ℝ≥0 → ℝ) (x : ℝ≥0) (c : ℝ)
    (h : ∀ y : ℝ≥0, y ≤ x → φ y + ((x : ℝ) - y) ≤ c) : Dop φ x ≤ c := by
  refine csSup_le ⟨_, 0, zero_le, rfl⟩ ?_
  rintro w ⟨d, hd, rfl⟩
  have := h (x - d) tsub_le_self
  rw [NNReal.coe_sub hd] at this
  linarith

lemma Iop_bdd (p : Params) (hS : p.Standing) (ψ : ℝ≥0 → ℝ) (A : ℝ)
    (hb : ∀ y, ψ y ≤ (y : ℝ) + A) (x : ℝ≥0) :
    BddAbove {y : ℝ | ∃ z : ℝ≥0, 0 < z ∧ y = ψ (x + z) - issueCost p z} := by
  obtain ⟨_, _, _, hF, hP, _⟩ := hS
  refine ⟨(x : ℝ) + A, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have h1 := hb (x + z)
  have hz' : (0 : ℝ) < z := hz
  simp only [issueCost, hz', if_true]
  push_cast at h1
  nlinarith

lemma Iop_nonempty (p : Params) (ψ : ℝ≥0 → ℝ) (x : ℝ≥0) :
    ({y : ℝ | ∃ z : ℝ≥0, 0 < z ∧ y = ψ (x + z) - issueCost p z}).Nonempty :=
  ⟨_, 1, one_pos, rfl⟩

lemma le_Iop (p : Params) (hS : p.Standing) (ψ : ℝ≥0 → ℝ) (A : ℝ)
    (hb : ∀ y, ψ y ≤ (y : ℝ) + A) (x z : ℝ≥0) (hz : 0 < z) :
    ψ (x + z) - issueCost p z ≤ Iop p ψ x :=
  le_csSup (Iop_bdd p hS ψ A hb x) ⟨z, hz, rfl⟩

end PDSol33D

open PDSol33D in
theorem solution (p : PeriodicDividend.FixedPoint.Params) (hS : p.Standing) (A : ℝ) (hA : 0 ≤ A)
    (φ : ℝ≥0 → ℝ) (hφ : PeriodicDividend.FixedPoint.ChatA p A φ) :
    PeriodicDividend.FixedPoint.CA p A (PeriodicDividend.FixedPoint.Dop φ) := by
  open PeriodicDividend.FixedPoint in
  obtain ⟨hcont, hmono, hpt, h0⟩ := hφ
  have hb : ∀ y, φ y ≤ (y : ℝ) + A := fun y => (hpt y).2.2
  have hnn : ∀ y, 0 ≤ φ y := fun y => (hpt y).1
  have hI : ∀ y, Iop p φ y ≤ φ y := fun y => le_trans (le_max_left _ _) (hpt y).2.1
  obtain ⟨hρ, hμ, hσ, hF, hP, hT⟩ := hS
  have hS' : p.Standing := ⟨hρ, hμ, hσ, hF, hP, hT⟩
  set D := Dop φ with hDdef
  have le_D' : ∀ x y : ℝ≥0, y ≤ x → φ y + ((x : ℝ) - y) ≤ D x := le_D φ A hb
  have D_le' : ∀ (x : ℝ≥0) (c : ℝ), (∀ y : ℝ≥0, y ≤ x → φ y + ((x : ℝ) - y) ≤ c) → D x ≤ c :=
    D_le φ
  -- basic facts
  have hφD : ∀ x, φ x ≤ D x := fun x => by
    have := le_D' x x le_rfl; simpa using this
  have hDA : ∀ x, D x ≤ (x : ℝ) + A := fun x =>
    D_le' x _ (fun y _ => by have := hb y; linarith)
  have hDb : ∀ y, D y ≤ (y : ℝ) + A := hDA
  -- monotonicity of D x - x
  have hmonoM : Monotone (fun x => D x - (x : ℝ)) := by
    intro x x' hxx'
    have : D x ≤ D x' - x' + x := D_le' x _ (fun y hy => by
      have := le_D' x' y (le_trans hy hxx'); linarith)
    simp only; linarith
  have hmonoD : Monotone D := by
    intro x x' h
    have := hmonoM h
    have h' : (x : ℝ) ≤ x' := h
    simp only at this; linarith
  -- local Lipschitz-type bound
  have hlip : ∀ x x' : ℝ≥0, x ≤ x' → D x' ≤ D x + (φ x' - φ x) + ((x' : ℝ) - x) := by
    intro x x' h
    apply D_le' x' _
    intro y hy
    rcases le_total y x with hyx | hxy
    · have := le_D' x y hyx
      have := hmono h
      linarith
    · have h1 : φ y ≤ φ x' := hmono hy
      have h2 := hφD x
      have h3 : (x : ℝ) ≤ y := hxy
      linarith
  have hcontD : Continuous D := by
    rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.continuous_iff.mp hcont b (ε / 2) (by linarith)
    refine ⟨min δ1 (ε / 2), lt_min hδ1 (by linarith), fun a ha => ?_⟩
    have ha1 : dist a b < δ1 := lt_of_lt_of_le ha (min_le_left _ _)
    have ha2 : dist a b < ε / 2 := lt_of_lt_of_le ha (min_le_right _ _)
    have hφab := hδ1' a ha1
    rw [Real.dist_eq] at hφab ⊢
    rw [NNReal.dist_eq] at ha2
    rcases le_total a b with hab | hab
    · have h1 := hlip a b hab
      have h2 := hmonoD hab
      have h3 : φ a ≤ φ b := hmono hab
      rw [abs_lt] at hφab ha2 ⊢
      constructor <;> linarith
    · have h1 := hlip b a hab
      have h2 := hmonoD hab
      have h3 : φ b ≤ φ a := hmono hab
      rw [abs_lt] at hφab ha2 ⊢
      constructor <;> linarith
  -- Iop condition for D
  have hID : ∀ x, Iop p D x ≤ D x := by
    intro x
    apply csSup_le (Iop_nonempty p D x)
    rintro w ⟨z, hz, rfl⟩
    have hz' : (0 : ℝ) < z := hz
    have hc : issueCost p z = p.lamF + (1 + p.lamP) * z := by simp [issueCost, hz']
    rw [hc]
    have : D (x + z) ≤ D x + p.lamF + (1 + p.lamP) * z := by
      apply D_le' (x + z) _
      intro y hy
      have hy' : (y : ℝ) ≤ x + z := by exact_mod_cast hy
      rcases le_total y x with hyx | hxy
      · have := le_D' x y hyx
        push_cast
        nlinarith
      · rcases eq_or_lt_of_le hxy with heq | hlt
        · subst heq
          have := hφD x
          push_cast; nlinarith
        · -- y = x + z' with 0 < z' ≤ z
          have hz'pos : 0 < y - x := tsub_pos_of_lt hlt
          have hy_eq : x + (y - x) = y := add_tsub_cancel_of_le hxy
          have h1 := le_Iop p hS' φ A hb x (y - x) hz'pos
          rw [hy_eq] at h1
          have hc' : issueCost p ((y - x : ℝ≥0) : ℝ) = p.lamF + (1 + p.lamP) * ((y : ℝ) - x) := by
            have : (0 : ℝ) < ((y - x : ℝ≥0) : ℝ) := hz'pos
            rw [issueCost, if_pos this, NNReal.coe_sub hxy]
          rw [hc'] at h1
          have h2 := hI x
          have h3 := hφD x
          have hxy' : (x : ℝ) ≤ y := hxy
          push_cast
          nlinarith
    linarith
  refine ⟨⟨hcontD, hmonoD, fun x => ⟨le_trans (hnn x) (hφD x), max_le (hID x)
    (le_trans (hnn x) (hφD x)), hDA x⟩, ?_⟩, hmonoM, fun x => ?_⟩
  · -- value at 0
    have hD0 : D 0 = φ 0 := by
      apply le_antisymm _ (hφD 0)
      apply D_le' 0 _
      intro y hy
      have : y = 0 := le_antisymm hy (zero_le)
      subst this; simp
    apply le_antisymm
    · rw [hD0, h0]
      apply max_le_max _ le_rfl
      apply csSup_le (Iop_nonempty p φ 0)
      rintro w ⟨z, hz, rfl⟩
      have := le_Iop p hS' D A hDb 0 z hz
      have := hφD (0 + z)
      linarith
    · exact max_le (hID 0) (le_trans (hnn 0) (hφD 0))
  · rw [abs_le]
    have h1 := le_D' x 0 (zero_le)
    have h2 := hnn 0
    have h3 := hDA x
    simp at h1
    constructor <;> linarith
