-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift.maj_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:59:41.297181+00:00
-- url     : https://prove2.me/submissions/96d2f83c-684b-45a3-a16d-091c19139e02

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_UnipotentCoefficientShift_Hf_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift
open NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift
theorem _root_.solution {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v e : Fin r → ℂ)
    (he : X.Hf z τ e e ≠ 0) :
    X.maj z τ v = X.maj z τ (v - (X.Hf z τ v e / X.Hf z τ e e) • e) +
      ‖X.Hf z τ v e / X.Hf z τ e e‖ ^ 2 * X.maj z τ e := by
  set K := X.Hf z τ v e / X.Hf z τ e e with hKdef
  have hK : K * X.Hf z τ e e = X.Hf z τ v e := div_mul_cancel₀ _ he
  have h1 : X.Hf z τ (v - K • e) e = 0 := by
    rw [Hf_sub_left, Hf_smul_left, hK, sub_self]
  have h2 : X.Hf z τ e (v - K • e) = 0 := by
    rw [← Hf_conj hz τ (v - K • e) e, h1, map_zero]
  have hv : v = (v - K • e) + K • e := (sub_add_cancel v (K • e)).symm
  have hexp : X.Hf z τ v v = X.Hf z τ (v - K • e) (v - K • e) + K * conj K * X.Hf z τ e e := by
    conv_lhs => rw [hv]
    rw [Hf_add_left, Hf_add_right, Hf_add_right, Hf_smul_left, Hf_smul_left, Hf_smul_right,
      Hf_smul_right, h1, h2]
    ring
  rw [X.Hf_self hz, X.Hf_self hz, X.Hf_self hz, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hexp
  exact_mod_cast hexp
end ReciprocityTheory.ChartRestriction.G.FD.UnipotentCoefficientShift
