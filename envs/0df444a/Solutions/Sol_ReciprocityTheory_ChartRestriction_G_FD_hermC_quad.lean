-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.hermC_quad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:04.810794+00:00
-- url     : https://prove2.me/submissions/0c8f109a-d21a-4bf6-b969-9662234204fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (γ : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) :
    hermC τ G (∑ a, γ a • f a) (∑ b, γ b • f b) =
      ∑ a, ∑ b, γ a * hermC τ G (f a) (f b) * conj (γ b) := by
  rw [hermC_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hermC_smul_right]
  ring
end ReciprocityTheory.ChartRestriction.G.FD
