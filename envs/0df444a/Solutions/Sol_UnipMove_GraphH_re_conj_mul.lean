-- Prove2me | solution 1 for UnipMove.GraphH.re_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:22:22.908005+00:00
-- url     : https://prove2.me/submissions/75b622a7-d528-4c11-b2d6-f350dc2b8d89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt

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
theorem _root_.solution (w : ℂ) (s : ℝ) : (conj w * (w * (s : ℂ))).re = s * ‖w‖ ^ 2 := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  first
    | (rw [Complex.sq_norm, Complex.normSq_apply]; ring)
    | (rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring)
    | (simp [Complex.sq_abs, Complex.normSq_apply]; ring)
end UnipMove.GraphH
