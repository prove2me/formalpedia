-- Prove2me | solution 1 for UnipMove.AffineProjectionSplitting.ucomp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:09:21.55045+00:00
-- url     : https://prove2.me/submissions/67f9f380-027b-46eb-8c55-559c1cb756f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_AprojEqZeroOfUz
import Theorems.Thm_UnipMove_AffineProjectionSplitting_aproj_smul

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
open UnipMove.AffineProjectionSplitting
variable {r : ℕ} (X : Data E r) (ξ : Fin r → E)
namespace UnipMove.AffineProjectionSplitting
theorem _root_.solution (x : Frame X.Ψ r) (c : ℂ) (u : X.Ψ → Fin r → ℂ) :
    X.ucomp x ξ (c • u) = c • X.ucomp x ξ u := by
  simp only [Data.ucomp, aproj_smul, smul_sub]
end UnipMove.AffineProjectionSplitting
