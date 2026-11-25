-- Prove2me | solution 1 for SteklovTriangles.X_eq_rho_Y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:50:31.730068+00:00
-- url     : https://prove2.me/submissions/27f922a9-d9b7-40ba-9530-a2f4236ac46c

import Mathlib
import Definitions.Def_SteklovTriangles_Reformulation

set_option autoImplicit false
open SteklovTriangles
namespace SteklovTriangles
theorem _root_.solution (σ ρ a b d1 d2 g0 g1 g2 m0x m1x m2x m0y m1y m2y Q11 Q12 Q21 Q22 : ℝ)
    (hd : 1 + ρ * b ≠ 0) (hL : 3 + ρ * d1 + ρ * d2 ≠ 0)
    (hmx : m0x + m1x + m2x = 0) (hmy : m0y + m1y + m2y = 0)
    (heig : Q11 + Q22 = σ * (g0 + g1 + g2)) :
    let d := 1 + ρ * b
    let s1 := 1 + ρ * d1
    let s2 := 1 + ρ * d2
    let L := 1 + s1 + s2
    let G11 := 1 + ρ ^ 2 * a ^ 2 / d ^ 2
    let G12 := -(ρ * a) / d ^ 2
    let G22 := 1 / d ^ 2
    let DA := (g0 + s1 * g1 + s2 * g2) - (m0x + s1 * m1x + s2 * m2x) * (m0y + s1 * m1y + s2 * m2y) / L
    let NA := d * (G11 * Q11 + G12 * Q12 + G12 * Q21 + G22 * Q22)
    let X := σ * (3 / L) * DA - NA
    let c0 := -(d1 + d2) / L
    let c1 := (2 * d1 - d2) / L
    let c2 := (2 * d2 - d1) / L
    let vx := d1 * m1x + d2 * m2x
    let vy := d1 * m1y + d2 * m2y
    let H11 := b + ρ * a ^ 2 / d
    let H12 := -a / d
    let H22 := -b / d
    let Y := σ * (c0 * g0 + c1 * g1 + c2 * g2 - 3 * ρ * vx * vy / L ^ 2)
              - (H11 * Q11 + H12 * Q12 + H12 * Q21 + H22 * Q22)
    X = ρ * Y := by
  intro d s1 s2 L G11 G12 G22 DA NA X c0 c1 c2 vx vy H11 H12 H22 Y
  have hd' : d ≠ 0 := hd
  have hL' : L ≠ 0 := by
    show 1 + (1 + ρ * d1) + (1 + ρ * d2) ≠ 0
    have : 1 + (1 + ρ * d1) + (1 + ρ * d2) = 3 + ρ * d1 + ρ * d2 := by ring
    rw [this]; exact hL
  -- the means: Σ s_e m_e = ρ v  (uses Σ m_e = 0)
  have hsx : m0x + s1 * m1x + s2 * m2x = ρ * vx := by
    simp only [s1, s2, vx]; linear_combination hmx
  have hsy : m0y + s1 * m1y + s2 * m2y = ρ * vy := by
    simp only [s1, s2, vy]; linear_combination hmy
  have hQ : Q22 = σ * (g0 + g1 + g2) - Q11 := by linarith
  simp only [X, DA, NA, Y]
  rw [hsx, hsy]
  simp only [G11, G12, G22, H11, H12, H22, c0, c1, c2]
  rw [hQ]
  simp only [L, s1, s2] at hL' ⊢
  field_simp
  ring
end SteklovTriangles
