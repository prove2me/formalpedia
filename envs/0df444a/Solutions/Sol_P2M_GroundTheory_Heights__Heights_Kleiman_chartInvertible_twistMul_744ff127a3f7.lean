-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_chartInvertible_twistMul_744ff127a3f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:52.881204+00:00
-- url     : https://prove2.me/submissions/d4afeaf8-1a43-4e2a-a810-1de40be10339

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_sub_eq_mul_066a67fa7155
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ChartInvertible_mul_6cd6215982f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_chartInvertible_twistSys_c135df1c8a47

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (M : LineBundle S x) (p : ℕ) (m : ℤ) (I : Chart x) :
    ChartInvertible ((twistMul M.toSubSystem p m).sub I) := by
  have hpow : ∀ n : ℕ, ChartInvertible ((M.toSubSystem.pow n).sub I) := by
    intro n
    induction n with
    | zero => exact chartInvertible_twistSys 0 I
    | succ n ih =>
      change ChartInvertible (((M.toSubSystem.pow n).twist M.toSubSystem).sub I)
      rw [twist_sub_eq_mul]
      exact ChartInvertible.mul (M.invertible I) ih
  rw [twistMul, twist_sub_eq_mul]
  exact ChartInvertible.mul (chartInvertible_twistSys m I) (hpow p)
end GroundTheory.Heights₂.Heights.Kleiman
