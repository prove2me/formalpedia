-- Prove2me | solution 1 for PELiquidity.Secondary.mu2_welldefined
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T19:07:37.468182+00:00
-- url     : https://prove2.me/submissions/227c05cc-d6df-4946-af20-2884d962562a

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

/-- Appendix C.6: the middle threshold is well defined. Top-level `solution`
    matching platform target 0e37aaaa-511d-47f3-b65c-99e74d9e620a. -/
theorem solution (P : PELiquidity.Primary.Params) :
    let g : ℝ → ℝ := fun D => (1 - P.lam) * D / (1 - P.lam * D)
    StrictMonoOn g (Set.Icc (1 - P.δH) (1 - P.δL)) ∧
    g (1 - P.δH) < PELiquidity.Primary.xBar P.p P.q ∧
    PELiquidity.Primary.xBar P.p P.q < g (1 - P.δL) ∧
    (∀ δ : ℝ, 0 < δ → δ < 1 → g (1 - δ) = PELiquidity.Primary.xHat P.lam δ) := by
  have hLH : P.δL < P.δH := lt_trans P.hA6a P.hA6b
  have hRange : 1 - P.δH ≤ 1 - P.δL := by linarith
  have hpq : (0 : ℝ) < P.p + P.q := by
    have hpp : (0 : ℝ) < P.p := lt_trans P.hq P.hqp
    linarith [P.hq]
  have hpqne : (P.p + P.q : ℝ) ≠ 0 := ne_of_gt hpq
  have hsh : (0 : ℝ) < 1 - P.lam := by linarith [P.hlam1]
  have hlq : (0 : ℝ) < (1 - P.lam) * P.q := mul_pos hsh P.hq
  have hs : (0 : ℝ) < P.p + (1 - P.lam) * P.q := by linarith [hlq, P.hq, P.hqp]
  have hsne : (P.p + (1 - P.lam) * P.q : ℝ) ≠ 0 := ne_of_gt hs
  have hΔ0 : (0 : ℝ) < PELiquidity.Primary.deltaHat P.p P.q P.lam :=
    lt_trans P.hδL0 P.hA6a
  have hΔHlt : PELiquidity.Primary.deltaHat P.p P.q P.lam < P.δH := P.hA6b
  have hΔgtL : P.δL < PELiquidity.Primary.deltaHat P.p P.q P.lam := P.hA6a
  have hLtH : 1 - P.δH < 1 - PELiquidity.Primary.deltaHat P.p P.q P.lam := by
    linarith [hΔHlt]
  have hMidMem : 1 - PELiquidity.Primary.deltaHat P.p P.q P.lam ∈
      Set.Icc (1 - P.δH) (1 - P.δL) := ⟨by linarith [hΔHlt], by linarith [hΔgtL]⟩
  have hΔden : (0 : ℝ) < 1 - P.lam * (1 - PELiquidity.Primary.deltaHat P.p P.q P.lam) := by
    have h5 : (1 : ℝ) - PELiquidity.Primary.deltaHat P.p P.q P.lam < 1 := by
      linarith
    have h6 : P.lam * (1 - PELiquidity.Primary.deltaHat P.p P.q P.lam) < P.lam :=
      by linarith [mul_lt_mul_of_pos_left h5 P.hlam0]
    linarith [h6, P.hlam1]
  have hΔx : PELiquidity.Primary.deltaHat P.p P.q P.lam *
      (P.p + (1 - P.lam) * P.q) = (1 - P.lam) * P.q := by
    have hΔu : PELiquidity.Primary.deltaHat P.p P.q P.lam =
        1 - P.p / (P.p + (1 - P.lam) * P.q) := rfl
    rw [hΔu]
    field_simp [hsne]
    ring
  have hgen : ∀ δ : ℝ, (1 - P.lam) * (1 - δ) * (P.p + P.q) =
      P.p * (1 - P.lam * (1 - δ)) ↔
      δ * (P.p + (1 - P.lam) * P.q) = (1 - P.lam) * P.q := by
    intro δ
    constructor <;> intro h <;> linarith
  have hxB : (1 - P.lam) * (1 - PELiquidity.Primary.deltaHat P.p P.q P.lam) /
      (1 - P.lam * (1 - PELiquidity.Primary.deltaHat P.p P.q P.lam)) = P.p / (P.p + P.q) := by
    have hΔcross : (1 - P.lam) * (1 - PELiquidity.Primary.deltaHat P.p P.q P.lam) *
        (P.p + P.q) =
        P.p * (1 - P.lam * (1 - PELiquidity.Primary.deltaHat P.p P.q P.lam)) :=
      (hgen _).mpr hΔx
    rw [div_eq_div_iff (ne_of_gt hΔden) hpqne]
    exact hΔcross
  have hmono : StrictMonoOn (fun D => (1 - P.lam) * D / (1 - P.lam * D))
      (Set.Icc (1 - P.δH) (1 - P.δL)) := by
    intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
    obtain ⟨hy1, hy2⟩ := Set.mem_Icc.mp hy
    have hxlt : x < 1 := by linarith [hx2, P.hδL0]
    have hylt : y < 1 := by linarith [hy2, P.hδL0]
    have hdx : (0 : ℝ) < 1 - P.lam * x := by
      have h3 : P.lam * x < P.lam := by linarith [mul_lt_mul_of_pos_left hxlt P.hlam0]
      linarith [h3, P.hlam1]
    have hdy : (0 : ℝ) < 1 - P.lam * y := by
      have h3 : P.lam * y < P.lam := by linarith [mul_lt_mul_of_pos_left hylt P.hlam0]
      linarith [h3, P.hlam1]
    rw [div_lt_div_iff₀ hdx hdy]
    nlinarith [sub_pos.mpr P.hlam1, hxy]
  refine ⟨hmono, ?_, ?_, ?_⟩
  · -- g (1 - δH) < xBar p q
    calc (1 - P.lam) * (1 - P.δH) / (1 - P.lam * (1 - P.δH))
        < (1 - P.lam) * (1 - PELiquidity.Primary.deltaHat P.p P.q P.lam) /
          (1 - P.lam * (1 - PELiquidity.Primary.deltaHat P.p P.q P.lam)) :=
          hmono (Set.mem_Icc.mpr ⟨le_refl _, hRange⟩) hMidMem hLtH
      _ = P.p / (P.p + P.q) := hxB
  · -- xBar p q < g (1 - δL)
    calc P.p / (P.p + P.q)
        = (1 - P.lam) * (1 - PELiquidity.Primary.deltaHat P.p P.q P.lam) /
          (1 - P.lam * (1 - PELiquidity.Primary.deltaHat P.p P.q P.lam)) := hxB.symm
      _ < (1 - P.lam) * (1 - P.δL) / (1 - P.lam * (1 - P.δL)) :=
          hmono hMidMem (Set.mem_Icc.mpr ⟨hRange, le_refl _⟩) (by linarith [hΔgtL])
  · intro δ h0 h1
    show (1 - P.lam) * (1 - δ) / (1 - P.lam * (1 - δ)) = PELiquidity.Primary.xHat P.lam δ
    rw [show PELiquidity.Primary.xHat P.lam δ = 1 - δ / (1 - P.lam * (1 - δ)) from rfl]
    have hden : (1 - P.lam * (1 - δ) : ℝ) ≠ 0 := by
      have h4 : P.lam * (1 - δ) < P.lam := by
        have h01 : (1 : ℝ) - δ < 1 := by linarith
        linarith [mul_lt_mul_of_pos_left h01 P.hlam0]
      exact ne_of_gt (by linarith [h4, P.hlam1])
    field_simp [hden]
    ring
