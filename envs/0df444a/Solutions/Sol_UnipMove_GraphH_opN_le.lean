-- Prove2me | solution 1 for UnipMove.GraphH.opN_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:00:26.462654+00:00
-- url     : https://prove2.me/submissions/24c734ca-9915-4007-852e-e04f30f36692

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Theorems.Thm_UnipMove_GraphH_en_eq_sqrt
import Theorems.Thm_UnipMove_GraphH_en_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
namespace UnipMove.GraphH
theorem _root_.solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, en (A *ᵥ v) ≤ c * en v) : Data.opN A ≤ c := by
  unfold Data.opN
  apply Real.sSup_le _ hc
  rintro t ⟨v, hv, rfl⟩
  have h1 := h v
  rw [en_eq_sqrt, en_eq_sqrt] at h1
  have hpos : 0 < Real.sqrt (nsq v) := by
    have := en_pos hv
    rwa [en_eq_sqrt] at this
  change Real.sqrt (nsq (A *ᵥ v)) / Real.sqrt (nsq v) ≤ c
  rw [div_le_iff₀ hpos]
  exact h1
end UnipMove.GraphH
