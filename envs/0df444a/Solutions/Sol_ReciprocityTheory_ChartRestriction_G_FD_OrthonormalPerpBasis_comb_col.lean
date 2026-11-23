-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.comb_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:10.804803+00:00
-- url     : https://prove2.me/submissions/da7986e1-04e3-4032-9150-900cd1122a10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OnbPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosCoordNe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HCSumRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable {r : ℕ} (X : Data E r)
private theorem hermC_add_left_eq_add (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u u' w : Fin r → ℂ) :
    hermC τ G (u + u') w = hermC τ G u w + hermC τ G u' w := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private theorem hermC_smul_left_eq_smul_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u w : Fin r → ℂ) : hermC τ G (c • u) w = c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
private theorem hermC_finset_sum_smul_left (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (v : ι → Fin r → ℂ) (w : Fin r → ℂ) :
    hermC τ G (∑ k ∈ s, c k • v k) w = ∑ k ∈ s, c k * hermC τ G (v k) w := by
  classical
  induction s using Finset.induction_on
  · simp [hermC]
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hermC_add_left_eq_add, hermC_smul_left_eq_smul_mul, ih]
end
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
theorem _root_.solution {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c : Fin r → ℂ) (b : Fin r) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (col (mat x0 τ) b) = c b * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) := by
  rw [hermC_finset_sum_smul_left]
  have hab : ∀ a, hermC τ.1 X.Gm (col (mat x0 τ) a) (col (mat x0 τ) b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
    intro a
    have h := congrFun (congrFun (ho τ) a) b
    rw [Matrix.diagonal_apply] at h
    exact h
  simp [hab, mul_ite]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
