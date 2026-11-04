-- Prove2me | solution 1 for ThreeSum.LightMomentZeroDetector.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:31.596196+00:00
-- url     : https://prove2.me/submissions/20054718-276e-4d7c-afe2-ca129ece69a5

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightMomentDeterminant_wordBound_polynomial
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector
namespace ThreeSum.LightMomentZeroDetector
theorem _root_.solution (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {t : ℕ}
    (v w : Fin t → ℤ) (hv : Function.Injective v) (hweights : ∀ s, w s≠0)
    (ht : t≤H) {lim : Limits} {depth : ℕ}
    (hspace : base+(2*H+1)≤lim.space) (hspaceWord : (lim.space : ℤ)≤lim.word)
    (U : ℤ) (hU : 0≤U) (ha : |a|≤U)
    (hword : wordCoefficient H*(U+1)^wordDegree H≤lim.word)
    (hmabs : ∀ k≤2*H, |μ (base+k)|≤U)
    (hm : ∀ k≤2*H, μ (base+k)=moment v w k) :
    Meets lim (program H) 0 depth [base,a] μ (time (atoms H) H)
      (fun r ν => r=(if ∃ s, v s=a then 1 else 0 : ℤ) ∧ ν=μ) := by
  exact meets H base a μ v w hv hweights ht rfl hspace hspaceWord U hU ha
    ((wordBound_polynomial H hU).trans hword) hmabs hm
end ThreeSum.LightMomentZeroDetector
