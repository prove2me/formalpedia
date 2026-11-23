-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_HermitianPairingAlgebra_smul_mem__5cba0dccb7e4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:06.608122+00:00
-- url     : https://prove2.me/submissions/4e769f0e-6464-4755-aa09-2ff07d09d6c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra

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
theorem _root_.solution {r : ℕ} {M : Submodule (𝓞 E) (Fin r → E)} {a : E} (ha : IsIntegral ℤ a)
    {y : Fin r → E} (hy : y ∈ M) : a • y ∈ M := by
  convert M.smul_mem (⟨a, ha⟩ : 𝓞 E) hy using 1
  rw [← algebraMap_smul E]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.HermitianPairingAlgebra
