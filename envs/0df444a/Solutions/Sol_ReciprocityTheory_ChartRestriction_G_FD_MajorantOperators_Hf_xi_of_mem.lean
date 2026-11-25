-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.Hf_xi_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:02:35.631906+00:00
-- url     : https://prove2.me/submissions/3d6c79da-0f25-4085-9f88-8bb209e35b55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_mem_Uz_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_eq_jp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
theorem _root_.solution {z : Frame X.Ψ r} {ξ : Fin r → E} {u : X.Ψ → Fin r → ℂ}
    (hu : u ∈ X.Uz z ξ) (τ : X.Ψ) : X.Hf z τ (u τ) (Data.emb τ.1 ξ) = 0 := by
  rw [Data.Hf_eq_jp]
  exact ((mem_Uz_iff z ξ u).mp hu τ).2
end ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
