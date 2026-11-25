-- Prove2me | solution 1 for UnipMove.MajH.mulVec_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:12.186748+00:00
-- url     : https://prove2.me/submissions/a811454c-4d6e-4a79-b1f2-c1a082f317dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_DotAddRight
import Theorems.Thm_UnipMove_MajH_sum_splitC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.MajH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds UnipMove.GraphH NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace UnipMove.MajH
theorem _root_.solution (P : Matrix (Fin r) (Fin r) ℂ) (d : Fin X.p0 → ℂ) :
    P *ᵥ ext X d = ∑ a, d a • col P (Fin.castLE X.p0_le a) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
  rw [sum_splitC X]
  have h2 : ∑ m : Fin (r - X.p0), P i (nI X m) * ext X d (nI X m) = 0 := by
    refine Finset.sum_eq_zero fun m _ => ?_
    have hm : ¬ (((nI X m : Fin r) : ℕ) < X.p0) := by
      show ¬ (X.p0 + (m : ℕ) < X.p0)
      omega
    rw [show ext X d (nI X m) = 0 from dif_neg hm, mul_zero]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show ext X d (Fin.castLE X.p0_le a) = d a from dif_pos a.isLt]
  try ring
end UnipMove.MajH
