-- Prove2me | solution 1 for ThreeSum.LightMomentZeroDetector.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:46:55.612341+00:00
-- url     : https://prove2.me/submissions/58a7ead6-6ebe-4b0e-bad9-c8688609e23d

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_safe
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_abs
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_leading_memory
import Theorems.Thm_ThreeSum_LightMomentZeroDetector_modified_memory
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_ThreeSum_LightMomentDeterminant_body_ends


set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector
namespace ThreeSum.LightMomentZeroDetector
theorem _root_.solution (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {t : ℕ}
    (v w : Fin t → ℤ) (hv : Function.Injective v) (hweights : ∀ s, w s≠0)
    (ht : t≤H) {lim : Limits} {P : Program} {p depth : ℕ}
    (hp : P[p]?=some (body (atoms H) H))
    (hspace : base+(2*H+1)≤lim.space) (hspaceWord : (lim.space : ℤ)≤lim.word)
    (U : ℤ) (hU : 0≤U) (ha : |a|≤U)
    (hword : wordBound U H≤lim.word)
    (hmabs : ∀ k≤2*H, |μ (base+k)|≤U)
    (hm : ∀ k≤2*H, μ (base+k)=moment v w k) :
    Meets lim P p depth [base,a] μ (time (atoms H) H)
      (fun r ν => r=(if ∃ s, v s=a then 1 else 0 : ℤ) ∧ ν=μ) := by
  apply Meets.of_body hp
  exact body_ends H v w a hv hweights ht (atoms H) _ U hU
    (atoms_safe H base a μ hspace hspaceWord)
    (atoms_abs H base a μ U hU ha hmabs) hword
    (leading_memory H base a μ v w hm) (modified_memory H base a μ v w hm)
end ThreeSum.LightMomentZeroDetector
