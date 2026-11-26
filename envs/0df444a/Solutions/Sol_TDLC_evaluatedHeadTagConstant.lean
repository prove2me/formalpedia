-- Prove2me | solution 1 for TDLC.evaluatedHeadTagConstant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:25:09.126326+00:00
-- url     : https://prove2.me/submissions/b33e60cd-622b-4b27-a6d4-0bafaef7bf07


import Definitions.Def_TDLC_Solution

set_option autoImplicit true
open TDLC
universe u
namespace TDLC
theorem _root_.solution {A B : Type u} {f g : A → B}
    (e : HomotopyStepI f g) (x y : A) :
    Step.headTag ((evalHomotopyStepI e).family x) =
      Step.headTag ((evalHomotopyStepI e).family y) := by
  induction e <;> rfl
end TDLC
