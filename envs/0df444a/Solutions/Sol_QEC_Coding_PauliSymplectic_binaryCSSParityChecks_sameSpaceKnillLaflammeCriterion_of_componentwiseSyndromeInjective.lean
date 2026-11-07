-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryCSSParityChecks_sameSpaceKnillLaflammeCriterion_of_componentwiseSyndromeInjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:43:10.488181+00:00
-- url     : https://prove2.me/submissions/754c5c5a-d5e1-4713-a328-6444c76e631c

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_CSS_Correctability
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSParityChecks_pairProductCriterion_on_activeSupport_of_componentwiseSyndromeInjective
import Theorems.Thm_QEC_Coding_StabilizerCode_binaryPauliKrausFamily_sameSpaceKnillLaflammeCriterion_iff_pairProductCriterion_on_support


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe u v
variable {iota kappaP kappaQ : Type u} [Fintype iota] [DecidableEq iota]
  [Fintype kappaP] [Fintype kappaQ]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    {alpha : Type v} [Fintype alpha]
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (tX tZ : Nat)
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    (E : alpha → Binary iota) (amp : alpha → Complex)
    (hbound : ∀ a, amp a ≠ 0 →
      HammingWeight (E a).vector.xPart ≤ tX ∧
      HammingWeight (E a).vector.zPart ≤ tZ) :
    (binaryPauliKrausFamily E amp).sameSpaceKnillLaflammeCriterion
      (binaryCSSStabilizerCodeOfParityChecks P Q horth).code := by
  apply
    (StabilizerCode.binaryPauliKrausFamily_sameSpaceKnillLaflammeCriterion_iff_pairProductCriterion_on_support
      (binaryCSSSourceValidStabilizerOfParityChecks P Q horth) E amp).2
  exact
    binaryCSSParityChecks_pairProductCriterion_on_activeSupport_of_componentwiseSyndromeInjective
      P Q horth tX tZ hP hQ E amp hbound
end QEC.Coding.PauliSymplectic
