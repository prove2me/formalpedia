-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators.jp_fam_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:12:11.866653+00:00
-- url     : https://prove2.me/submissions/82926734-f21e-4e20-bf2f-431aa47be3b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_mem_Uz_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_jp_jp


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
theorem _root_.solution {z : Frame X.Ψ r} (hz : z ∈ X.dom) {ξ : Fin r → E} {u : X.Ψ → Fin r → ℂ}
    (hu : u ∈ X.Uz z ξ) : (fun τ => X.jp z τ (u τ)) ∈ X.Uz z ξ := by
  rw [mem_Uz_iff] at hu ⊢
  intro τ
  exact ⟨(hu τ).2, by rw [X.jp_jp hz]; exact (hu τ).1⟩
end ReciprocityTheory.ChartRestriction.G.FD.MajorantOperators
