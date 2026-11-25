-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_finrank_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:26:46.470806+00:00
-- url     : https://prove2.me/submissions/69aa00ef-f693-4138-b7e6-9967a43d2967

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_alpha_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_finrank_fin_pi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_IsProjFrame_isRatProjFrame
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_indep_sections
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_finrank_sec_free


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Module Filter Asymptotics
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e) :
    ∃ k : ℕ, ∀ n, projDeg x e * (n + D).choose D ≤ finrank ℤ (sec ℤ x (n + k)) := by
  obtain ⟨k, ε, hε, hli⟩ := exists_indep_sections x e h.isRatProjFrame
  refine ⟨k, fun n => ?_⟩
  have hinj : Function.Injective (alphaMap x e ε hε n) := by
    refine (injective_iff_map_eq_zero _).2 fun P hP => ?_
    have h0 : ∑ l, (P l : Ω) * ε l = 0 := congrArg Subtype.val hP
    have h1 := alpha_injective x e h.isRatProjFrame ε hli (fun l => (P l : Ω)) (fun l => (P l).2) h0
    funext l
    exact Subtype.ext (congrFun h1 l)
  have h2 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_fin_pi, finrank_sec_free (x ∘ e) h.isRatProjFrame.free n] at h2
  exact h2
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
