-- Prove2me | solution 1 for UnipMove.sFlagMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:31.177416+00:00
-- url     : https://prove2.me/submissions/ae2dfb03-d192-460d-86ef-ed7699ed2f35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoNormRelationTamePrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace UnipMove
theorem _root_.solution : SFlagMap E := by
  intro r X x y n h τ
  have hcol : ∀ (z : Frame X.Ψ r) (a : Fin r),
      col (mat (X.lmulC n z) τ) a = (n τ).mulVec (col (mat z τ) a) := by
    intro z a
    funext k
    simp [col, mat, Data.lmulC, Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  simp only [hcol]
  have hr : ∀ z : Frame X.Ψ r, (Set.range fun a : Fin X.p0 =>
      (n τ).mulVec (col (mat z τ) (Fin.castLE X.p0_le a))) =
      (Matrix.mulVecLin (n τ)) '' Set.range (fun a : Fin X.p0 => col (mat z τ) (Fin.castLE X.p0_le a)) :=
    fun z => by rw [← Set.range_comp]; rfl
  rw [hr, hr, Submodule.span_image, Submodule.span_image, h τ]
end UnipMove
