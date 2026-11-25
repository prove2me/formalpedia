-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_upDeg_cast_eb6ec3376b64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:57:39.933786+00:00
-- url     : https://prove2.me/submissions/843506af-6694-441f-834e-7c7fee07d63b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ThmIExists
theorem _root_.solution (A : HermLine ι) (k : K) : ((upDeg A k : ℕ) : ℤ) = A.a k + shift A := by
  rw [upDeg, Int.toNat_of_nonneg]
  have h1 : (A.a k).natAbs ≤ shift A :=
    Finset.single_le_sum (f := fun k => (A.a k).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have h2 : -((A.a k).natAbs : ℤ) ≤ A.a k := by
    rw [Int.natCast_natAbs]; exact neg_abs_le _
  omega
end GroundTheory.Heights₂.Heights.Inter.ThmIExists
