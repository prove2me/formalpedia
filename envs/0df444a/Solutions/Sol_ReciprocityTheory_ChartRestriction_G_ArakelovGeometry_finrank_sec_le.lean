-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.finrank_sec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:53.380512+00:00
-- url     : https://prove2.me/submissions/8e33eff4-bf78-46bc-ad5e-1fd9415ac185

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqZeroOfSecTraceMulEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsNatMulMemConeRingIntFin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_finrank_fin_pi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_IsProjFrame_isRatProjFrame
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eq_zero_of_secTrace_mul_eq_zero
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
    ∃ k : ℕ, ∀ n, finrank ℤ (sec ℤ x n) ≤ projDeg x e * (n + k + D).choose D := by
  obtain ⟨k, ε, hε, hli⟩ := exists_indep_sections x e h.isRatProjFrame
  refine ⟨k, fun n => ?_⟩
  have hinj : Function.Injective (betaMap x e h ε hε n).toIntLinearMap := by
    refine (injective_iff_map_eq_zero _).2 fun s hs => ?_
    have h0 : ∀ l, secTrace x e (n + k) ((s : Ω) * ε l) = 0 := fun l =>
      congrArg Subtype.val (congrFun hs l)
    exact Subtype.ext (eq_zero_of_secTrace_mul_eq_zero x e h.isRatProjFrame ε hε hli n s.2 h0)
  have h2 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_fin_pi, finrank_sec_free (x ∘ e) h.isRatProjFrame.free (n + k)] at h2
  exact h2
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
