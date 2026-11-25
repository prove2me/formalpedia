-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.sec_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:22.124897+00:00
-- url     : https://prove2.me/submissions/156fd2fc-69a1-4c96-9355-f96b341b9200

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (n : ℕ) : sec ℤ (x ∘ e) n ≤ sec ℤ x n := by
  rintro z ⟨p, hp, rfl⟩
  refine ⟨MvPolynomial.rename e p, hp.rename_isHomogeneous, ?_⟩
  simp [MvPolynomial.aeval_rename]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
