-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.comb_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:04:03.425831+00:00
-- url     : https://prove2.me/submissions/e6516f62-5605-4de2-a5a8-44c09f4249ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OnbPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosCoordNe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HCSumRight
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_hC_sum_right__1bac482c7394
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_comb_col
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
private theorem hermC_smul_right_eq_conj_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ)
    (u v : Fin r → ℂ) : hermC τ G u (c • v) = conj c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
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
theorem _root_.solution {x0 : Frame X.Ψ r} (ho : X.IsOrtho x0) (τ : X.Ψ) (c d : Fin r → ℂ) :
    hermC τ.1 X.Gm (∑ a, c a • col (mat x0 τ) a) (∑ b, d b • col (mat x0 τ) b) =
      ∑ a, c a * conj (d a) * ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  rw [hC_sum_right']
  simp only [hermC_smul_right_eq_conj_mul, comb_col X ho τ c]
  exact Finset.sum_congr rfl fun a _ => by ring
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
