-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.orthonormalFlagTranslate_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:50:51.628194+00:00
-- url     : https://prove2.me/submissions/373cb112-281d-411a-af7a-662fe5eb4ec4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_pnorm_rmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ppos_sameFlag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_Hf_sameFlag
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_bOf_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_ortho_bOf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : OrthonormalFlagTranslate (E := E) := by
  intro r X
  refine ⟨fun x hx => ⟨FrameDegreeData.bOf X x, FrameDegreeData.bOf_mem X hx, FrameDegreeData.ortho_bOf X hx⟩,
    fun la P hP x hx b hb => FrameDegreeData.pnorm_rmul X la P hP x hx b hb, fun x hx x' hx' h => ?_⟩
  have hpp := FrameDegreeData.ppos_sameFlag X hx hx' h
  have hJ : X.Jz x = X.Jz x' := by
    funext u τ
    simp only [Data.Jz, hpp]
  refine ⟨fun ξ => ⟨hJ, ?_, ?_⟩, ?_⟩
  · simp only [Data.Uz, hJ]
  · unfold Data.aproj
    rw [FrameDegreeData.Hf_sameFlag X hx hx' h]
  · funext τ v
    have e : ∀ y : Frame X.Ψ r, X.posPart y τ v = (hermC τ.1 X.Gm (X.ppos y τ v) v).re := by
      intro y
      rw [X.hermC_ppos_self]
      rfl
    simp only [Data.maj, e, hpp]
end ReciprocityTheory.ChartRestriction.G.FD
