-- Prove2me | solution 1 for actuarial_f_member_two_tranche_calendar_payment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:03:20.682994+00:00
-- url     : https://prove2.me/submissions/78607b49-5e98-44f2-8dbc-a9864f7c9334

import Mathlib
import Definitions.Def_actuarial_f_memberDue
import Definitions.Def_actuarial_f_spouseInstalment
import Definitions.Def_actuarial_f_estateInstalment
import Definitions.Def_actuarial_f_linkedSpouseBasis
import Definitions.Def_actuarial_f_linkedFirstTranche
import Definitions.Def_actuarial_f_monthlyLinkedInstalment
open ActuarialUnderpinsF

theorem solution
    (h r g z i j t : ℕ) (a b c : ℕ → ℝ)
    (sa sb : ℕ → ℕ → ℝ) (estate ga gb gc : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) :
    monthlyLinkedInstalment h r g z i j t
        a b c sa sb estate ga gb gc gs ge =
      linkedFirstTranche r z i t a b ga gb +
      c z * gc t * memberDue r i t +
      spouseInstalment h z i j t (linkedSpouseBasis a b sa sb) gs +
      estateInstalment h r g z i t estate ge := by
  rfl
