-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction.det_Am_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:44.236619+00:00
-- url     : https://prove2.me/submissions/1fb8e46e-9733-4294-bf4d-99ed090df54f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_IntegralBasisReduction_Bm_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
open Matrix NumberField Complex Module QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
theorem _root_.solution {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    (Am X y g).det ≤ |(Bm X g).det| := by
  have hSS : Sg X * Sg X = 1 := by
    refine LinearMap.ext fun u => funext fun τ => funext fun a => ?_
    show ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * (((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * u τ a) = u τ a
    rw [← mul_assoc, ← Complex.ofReal_mul]
    unfold sgn
    split_ifs <;> simp
  have hM : LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) *
      LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) = 1 := by
    rw [← LinearMap.toMatrix_mul, hSS, LinearMap.toMatrix_one]
  have h2 : |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| *
      |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| = 1 := by
    rw [← abs_mul, ← Matrix.det_mul, hM, Matrix.det_one, abs_one]
  have hd : |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| = 1 := by
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · linarith [abs_nonneg (LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det]
  rw [Bm_eq X hy g, Matrix.det_mul, abs_mul, hd, mul_one]
  exact le_abs_self _
end ReciprocityTheory.ChartRestriction.G.FD.IntegralBasisReduction
