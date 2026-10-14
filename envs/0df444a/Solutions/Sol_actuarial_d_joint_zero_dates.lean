-- Prove2me | solution 1 for actuarial_d_joint_zero_dates
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:38.267506+00:00
-- url     : https://prove2.me/submissions/caf24bbb-1166-41c1-8edb-b74ccd9e9082

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_annValue
import Definitions.Def_actuarial_d_annPath
import Definitions.Def_actuarial_d_annX
import Definitions.Def_actuarial_d_annY
import Definitions.Def_actuarial_d_annJoint
import Definitions.Def_actuarial_d_annLast
import Definitions.Def_actuarial_d_annRev
import Definitions.Def_actuarial_d_annMemberSpouse

open ActuarialJointD

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : annJoint h 0 p d b = 0 := by
  simp [annMemberSpouse, annValue, annPath, expect, onlyY, dead, alive, annRev, annLast, last, onlyX, both, annJoint, annY, annX]
