-- Prove2me | solution 1 for actuarial_d_member_spouse_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:38.673616+00:00
-- url     : https://prove2.me/submissions/a66d27fa-3922-4986-b9d1-1a8e0138f025

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

theorem solution (h n : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) : annMemberSpouse h n p d b 0 = annX h n p d b := by
  simp [annMemberSpouse, annValue, annPath, expect, onlyY, dead, alive, annRev, annLast, last, onlyX, both, annJoint, annY, annX]
