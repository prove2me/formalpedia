-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.rename_swap_mem_ker_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:03:31.541812+00:00
-- url     : https://prove2.me/submissions/39f4e325-8750-4a58-81b6-79b4cff502f7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZMultiHomogeneousDegreeSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_chiP_rename_swap

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
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (j₀ : Fin (N + 1)) (x : Fin N → Ω) (g : MvPolynomial (TVar D N) K)
    (hg : g ∈ kerP (K := K) (D := D) j₀ x) : rename swapT g ∈ kerP (K := K) (D := D) j₀ x := by
  rw [kerP, RingHom.mem_ker] at hg ⊢
  have hg' : chiP (K := K) j₀ x g = 0 := hg
  show chiP (K := K) j₀ x (rename swapT g) = 0
  rw [chiP_rename_swap, hg', map_zero]
end ReciprocityTheory.ChartRestriction.G.T0
