-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA.cross_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:20.746679+00:00
-- url     : https://prove2.me/submissions/d29e5483-31df-40f4-90e1-20591fbfde86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetMonoDetOneAdd
import Definitions.Def_Lemmata_PosDefOfRealQuadratic_QuadFormRealSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA
open Matrix
open scoped ComplexOrder Matrix
variable {p q : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA
theorem _root_.solution (Z W : Matrix (Fin p) (Fin q) ℂ) (hW : (1 - W * Wᴴ).PosDef) :
    ((1 - Z * Wᴴ) * (1 - W * Wᴴ)⁻¹ * (1 - Z * Wᴴ)ᴴ - (1 - Z * Zᴴ)).PosSemidef := by
  set B := 1 - W * Wᴴ with hBdef
  set C := 1 - Z * Wᴴ with hCdef
  set S := B⁻¹ with hSdef
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 hW.det_pos.ne'
  have hSB : S * B = 1 := Matrix.nonsing_inv_mul B hBu
  have hBS : B * S = 1 := Matrix.mul_nonsing_inv B hBu
  have hBh : Bᴴ = B := hW.1
  have hS : Sᴴ = S := by rw [hSdef, Matrix.conjTranspose_nonsing_inv, hBh]
  have h1 : (C * S - 1) * B * (C * S - 1)ᴴ = C * S * Cᴴ - C - Cᴴ + B := by
    have e : (C * S - 1) * B = C - B := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hSB, Matrix.mul_one, Matrix.one_mul]
    rw [e, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hS, Matrix.conjTranspose_one,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_one,
      ← Matrix.mul_assoc B S, hBS, Matrix.one_mul, Matrix.mul_assoc C S]
    abel
  have h2 : C + Cᴴ - B = (1 - Z * Zᴴ) + (W - Z) * (W - Z)ᴴ := by
    rw [hCdef, hBdef]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
      Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have e : C * S * Cᴴ - (1 - Z * Zᴴ) = (C * S - 1) * B * (C * S - 1)ᴴ + (W - Z) * (W - Z)ᴴ := by
    have hA : (1 - Z * Zᴴ) = C + Cᴴ - B - (W - Z) * (W - Z)ᴴ := by rw [h2]; abel
    rw [h1, hA]; abel
  rw [e]
  exact (hW.posSemidef.mul_mul_conjTranspose_same _).add (posSemidef_self_mul_conjTranspose _)
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA
