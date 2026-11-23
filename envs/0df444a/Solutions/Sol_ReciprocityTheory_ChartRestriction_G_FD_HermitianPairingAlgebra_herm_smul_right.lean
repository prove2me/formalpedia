-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.herm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:47.554792+00:00
-- url     : https://prove2.me/submissions/618a7aed-5e0d-4c65-8150-3b86ea9f78e3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_cc_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra
theorem _root_.solution {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (a : E) (x y : Fin r → E) :
    herm G x (a • y) = cc a * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, cc_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra
