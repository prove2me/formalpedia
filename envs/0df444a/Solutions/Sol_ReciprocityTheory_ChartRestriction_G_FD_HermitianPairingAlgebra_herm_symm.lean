-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra.herm_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:04:58.029354+00:00
-- url     : https://prove2.me/submissions/4a4665ad-8eb1-49db-a4b8-551cb26782f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_cc_sum

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
theorem _root_.solution {r : ℕ} {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, cc (G a b) = G b a)
    (x y : Fin r → E) : cc (herm G x y) = herm G y x := by
  simp only [herm, cc_sum, cc_mul, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra
