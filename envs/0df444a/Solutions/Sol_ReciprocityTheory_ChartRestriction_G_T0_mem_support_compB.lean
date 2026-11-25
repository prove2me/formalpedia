-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.mem_support_compB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:03:37.965273+00:00
-- url     : https://prove2.me/submissions/e8227266-77d2-43b9-ad5e-02fbc741bc8a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SupportFreeOfBlockSubstInvariant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_coeff_compB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K : Type} [Field K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {b : Fin (D + 1)} {k : ℕ} {p : MvPolynomial (TVar D N) K}
    {t : TVar D N →₀ ℕ} (ht : t ∈ (compB b k p).support) : t ∈ p.support ∧ degB b t = k := by
  rw [mem_support_iff, coeff_compB] at ht
  by_cases h : degB b t = k
  · rw [if_pos h] at ht
    exact ⟨mem_support_iff.mpr ht, h⟩
  · rw [if_neg h] at ht
    exact absurd rfl ht
end ReciprocityTheory.ChartRestriction.G.T0
