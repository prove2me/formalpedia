-- Prove2me | solution 1 for PELiquidity.Secondary.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:38:37.172692+00:00
-- url     : https://prove2.me/submissions/c259972a-682f-432b-9d53-7512b54ee731

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

set_option autoImplicit false
open PELiquidity.Primary

lemma CC_gdiff (lam δ D1 D2 : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (h1 : 1 - δ ≤ D1) (h12 : D1 < D2) (h2 : D2 < 1) :
    (1 + lam * δ * D1 / (1 - D1) * (1 / (1 - lam * (1 - δ))) - 1 / (1 - lam * D1)) <
    (1 + lam * δ * D2 / (1 - D2) * (1 / (1 - lam * (1 - δ))) - 1 / (1 - lam * D2)) := by
  set c : ℝ := 1 - lam * (1 - δ) with hc
  have hcpos : 0 < c := by rw [hc]; nlinarith
  have hcδ : δ < c := by rw [hc]; nlinarith
  have hB1 : 0 < 1 - D1 := by linarith
  have hB2 : 0 < 1 - D2 := by linarith
  have hA1 : 0 < 1 - lam * D1 := by nlinarith
  have hA2 : 0 < 1 - lam * D2 := by nlinarith
  set e1 : ℝ := δ * (1 - lam * D1) - c * (1 - D1) with he1
  set e2 : ℝ := δ * (1 - lam * D2) - c * (1 - D2) with he2
  have he1' : e1 = (1 - lam) * (D1 - (1 - δ)) := by rw [he1, hc]; ring
  have he2' : e2 = (1 - lam) * (D2 - (1 - δ)) := by rw [he2, hc]; ring
  have he1n : 0 ≤ e1 := by rw [he1']; apply mul_nonneg <;> linarith
  have he2n : 0 ≤ e2 := by rw [he2']; apply mul_nonneg <;> linarith
  set N : ℝ := δ * (1 - lam * D1) * (1 - lam * D2) - c * ((1 - D1) * (1 - D2)) with hN
  have hδN : δ * N = c * (c - δ) * ((1 - D1) * (1 - D2)) + c * ((1 - D1) * e2 + (1 - D2) * e1) + e1 * e2 := by
    rw [hN, he1, he2]; ring
  have hNpos : 0 < N := by
    have : 0 < δ * N := by
      rw [hδN]
      have t1 : 0 < c * (c - δ) * ((1 - D1) * (1 - D2)) :=
        mul_pos (mul_pos hcpos (sub_pos.2 hcδ)) (mul_pos hB1 hB2)
      have t2 : 0 ≤ c * ((1 - D1) * e2 + (1 - D2) * e1) :=
        mul_nonneg hcpos.le (add_nonneg (mul_nonneg hB1.le he2n) (mul_nonneg hB2.le he1n))
      have t3 : 0 ≤ e1 * e2 := mul_nonneg he1n he2n
      linarith
    exact (pos_iff_pos_of_mul_pos this).1 hδ0
  have hdiff : (1 + lam * δ * D2 / (1 - D2) * (1 / c) - 1 / (1 - lam * D2)) -
      (1 + lam * δ * D1 / (1 - D1) * (1 / c) - 1 / (1 - lam * D1)) =
      (D2 - D1) * lam * N / (c * (1 - D1) * (1 - D2) * (1 - lam * D1) * (1 - lam * D2)) := by
    rw [hN]
    field_simp
    ring
  have : 0 < (D2 - D1) * lam * N / (c * (1 - D1) * (1 - D2) * (1 - lam * D1) * (1 - lam * D2)) := by
    apply div_pos
    · exact mul_pos (mul_pos (sub_pos.2 h12) hl0) hNpos
    · positivity
  linarith

theorem solution (P : PELiquidity.Primary.Params) :
    let RminH : ℝ → ℝ := fun D =>
      1 + P.lam * P.δH * D / (1 - D) * PELiquidity.Primary.grossReturn P.lam P.δH
    let RminL : ℝ → ℝ := fun D => 1 / (1 - P.lam * D)
    RminH (1 - P.δH) = RminL (1 - P.δH) ∧
    StrictMonoOn (fun D => RminH D - RminL D)
      (Set.Icc (1 - P.δH) (1 - P.δL)) ∧
    ∀ D ∈ Set.Ioc (1 - P.δH) (1 - P.δL),
      0 < RminH D - RminL D := by
  intro RminH RminL
  have hl0 := P.hlam0
  have hl1 := P.hlam1
  have hδ0 := P.hδH0
  have hδ1 := P.hδH1
  have hL0 := P.hδL0
  have hL1 := P.hδL1
  have hgr : PELiquidity.Primary.grossReturn P.lam P.δH = 1 / (1 - P.lam * (1 - P.δH)) := rfl
  have hc : 0 < 1 - P.lam * (1 - P.δH) := by nlinarith
  have hH : ∀ D, RminH D = 1 + P.lam * P.δH * D / (1 - D) * (1 / (1 - P.lam * (1 - P.δH))) := by
    intro D; simp only [RminH, hgr]
  have hmono : StrictMonoOn (fun D => RminH D - RminL D) (Set.Icc (1 - P.δH) (1 - P.δL)) := by
    intro D1 hD1 D2 hD2 h12
    simp only [hH]
    exact CC_gdiff P.lam P.δH D1 D2 hl0 hl1 hδ0 hδ1 hD1.1 h12 (by linarith [hD2.2])
  have hzero : RminH (1 - P.δH) = RminL (1 - P.δH) := by
    simp only [hH, RminL]
    have : (1 - (1 - P.δH)) = P.δH := by ring
    rw [this]
    field_simp
    ring
  refine ⟨hzero, hmono, ?_⟩
  intro D hD
  have hδLH : 1 - P.δH ≤ 1 - P.δL := by
    have := hD.1; have := hD.2; linarith
  have hlt := hmono (a := 1 - P.δH) (b := D) ⟨le_rfl, hδLH⟩ ⟨hD.1.le, hD.2⟩ hD.1
  simp only [hzero, sub_self] at hlt
  exact hlt
