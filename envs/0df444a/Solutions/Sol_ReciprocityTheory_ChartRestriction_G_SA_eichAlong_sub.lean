-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.SA.eichAlong_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:49:59.4741+00:00
-- url     : https://prove2.me/submissions/d1a7b027-25d2-4807-881d-3408c9b008e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_preserves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_mem_SU_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] {σ : R →+* R}
  {J : Matrix ι ι R}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ
namespace ReciprocityTheory.ChartRestriction.G.SA
theorem _root_.solution {e f : ι → R} (he : hf σ J e e = 0) : eichAlong σ J e f ⊆ SU σ J := by
  intro M hM
  obtain ⟨u, c, hue, -, hc, rfl⟩ := hM
  rw [mem_SU_iff]
  exact ⟨eich_det (hσ := hσ) (hJ := hJ) he hue, eich_preserves (hσ := hσ) (hJ := hJ) he hue hc⟩
end ReciprocityTheory.ChartRestriction.G.SA
