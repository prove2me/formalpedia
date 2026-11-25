-- Prove2me | solution 1 for UnipMove.sGraph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:50:49.918619+00:00
-- url     : https://prove2.me/submissions/fea75a7b-a25a-4adf-b25f-bf418cddeb00

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Theorems.Thm_UnipMove_GraphH_graph_tau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
namespace UnipMove
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] : SGraph E := by
  unfold SGraph
  intro r X x0 hx0 ho n Z1 η z hη hz hZ1 hs hn
  have hg := fun τ => GraphH.graph_tau X hx0 ho τ (n τ) Z1 hη hz hZ1 hs (hn τ)
  choose W hW1 hW2 using hg
  refine ⟨(fun τ => W τ : X.Coord), ?_, ?_⟩
  · intro τ
    exact hW2 τ (fun τ => W τ) rfl
  · unfold Data.zN
    apply Real.iSup_le
    · intro τ
      exact hW1 τ
    · have h1 : 0 ≤ η * (1 + z) := mul_nonneg hη (by linarith)
      apply div_nonneg
      · linarith
      · linarith
end UnipMove
