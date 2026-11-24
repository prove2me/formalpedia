-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_pow_3db7e9c92ffa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:06.028336+00:00
-- url     : https://prove2.me/submissions/08bfdddc-1cbe-4f85-8ebe-2908cb05533f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsAmple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleCover_sub_twist_fad4ee8c76b1

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
namespace AmpleCover
theorem _root_.solution (Q : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero =>
    obtain ⟨i, hi⟩ := I.2.1
    rw [pow_zero]
    change twistMod S x 0 I = 1
    rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]
  | succ n ih =>
    change ((Q.pow n).twist Q).sub I = _
    rw [AmpleCover.sub_twist, ih, pow_succ]
end AmpleCover
end GroundTheory.Heights₂.Heights.Kleiman
