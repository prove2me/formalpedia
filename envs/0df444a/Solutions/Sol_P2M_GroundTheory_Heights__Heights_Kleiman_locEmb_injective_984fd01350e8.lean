-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locEmb_injective_984fd01350e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:01:03.670102+00:00
-- url     : https://prove2.me/submissions/40012161-7cf5-4219-9265-5d8e02072585

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_xyHom_mul_locEmb_mk_c65ae6a1d680

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
open MvPolynomial Pointwise AddMonoidAlgebra
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I : Finset (Fin (N + 1))} (hI : I ⊆ support x) :
    Function.Injective (locEmb η M₀ I hI) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  induction w using LocalizedModule.induction_on with
  | h m s =>
    have key := xyHom_mul_locEmb_mk η M₀ hI m s
    rw [hw] at key
    have hm : m = 0 := TwM.val_injective (by rw [← key, TwM.val_zero]; exact mul_zero _)
    rw [hm, LocalizedModule.zero_mk]
    rfl
end GroundTheory.Heights₂.Heights.Kleiman
