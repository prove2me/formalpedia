-- Prove2me | solution 1 for ThreeSum.TernaryWeightChannels.fourth_pair_channel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:50.232498+00:00
-- url     : https://prove2.me/submissions/3e59076f-2db2-402b-b0db-770b76ef36bf

import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWeightChannels
open Finset LightFixedArithmetic TernaryJointType TernaryWeightedPhysicalSources
open scoped BigOperators
variable {ι κ I : Type*}
namespace ThreeSum.TernaryWeightChannels
theorem _root_.solution {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (L : ι→I→ℤ) (R : κ→I→ℤ) (a b c d : I) (Q : TritWord N) :
    pairWeight S T left right (productWeight L a b) (productWeight R c d) Q=
      ∑ i∈S, ∑ j∈T, if TernaryConvolution.Adds (left i) (right j) Q then
        L i a*L i b*R j c*R j d else 0 := by
  classical
  unfold pairWeight productWeight
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  split <;> ring
end ThreeSum.TernaryWeightChannels
