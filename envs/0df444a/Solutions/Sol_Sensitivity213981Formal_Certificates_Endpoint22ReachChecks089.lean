-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks089
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:34:43.883125+00:00
-- url     : https://prove2.me/submissions/71c9394f-aafb-49d1-8ee9-be989a3cd79d

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks089
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks089
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RelaxedReachableSearch
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/- Shared suffix bitsets retain every degree completion. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 200000
namespace ThreeBoundRelaxedReachable
open ThreeBoundQ3 ThreeBoundRelaxed ThreeBoundRelaxedCompiled
open ThreeBoundRelaxedPacked (Tree fastKey)





















theorem valid_step (cs : List State) (bits : ℕ) (tail : Plan) (ht : tail.Valid)
    (h : localCheck cs bits tail.bits=true) : (Plan.step cs bits tail).Valid := by
  refine ⟨ht,?_⟩
  intro s hs
  have hh := List.all_eq_true.mp h s hs
  have hh' : decide (0≤ point s)=true ∧
      decide (((tail.bits <<< (point s).toNat) &&& bits)=tail.bits <<< (point s).toNat)=true := by
    simpa only [Bool.and_eq_true] using hh
  exact ⟨of_decide_eq_true hh'.1,of_decide_eq_true hh'.2⟩























theorem frontier_check (tree : Tree) (d : ℕ) (j : Job) :
    (j.frontier d).all (Job.check tree)=j.check tree := by
  induction d generalizing j with
  | zero => simp [Job.frontier]
  | succ d ih =>
      cases j with
      | mk p pre previous remaining =>
          cases p with
          | done => simp [Job.frontier]
          | step cs bits tail =>
              simp only [Job.frontier,Job.check,Plan.run]
              split_ifs with h
              · rw [List.all_flatMap]
                apply congrArg (fun f=>cs.all f)
                funext s
                split_ifs with hp
                · exact ih _
                · rfl
              · rfl

theorem check_of_frontier (tree : Tree) (d : ℕ) (j : Job) (jobs : List Job)
    (he : j.frontier d=jobs) (h : jobs.all (Job.check tree)=true) : j.check tree=true := by
  rw [← he,frontier_check] at h
  exact h















end ThreeBoundRelaxedReachable


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)

theorem valid0 : plan0.Valid := by trivial










































































































































































































































































































































end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)









































































theorem valid133 : plan133.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid134 : plan134.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid135 : plan135.Valid := valid_step _ _ _ valid0 (by decide +kernel)


















































































































end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)

theorem valid577 : plan577.Valid := valid_step _ _ _ valid135 (by decide +kernel)

theorem valid578 : plan578.Valid := valid_step _ _ _ valid134 (by decide +kernel)

theorem valid579 : plan579.Valid := valid_step _ _ _ valid134 (by decide +kernel)

theorem valid580 : plan580.Valid := valid_step _ _ _ valid135 (by decide +kernel)
























































































































































































end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)





























































































































































































theorem valid575 : plan575.Valid := valid_step _ _ _ valid133 (by decide +kernel)

theorem valid576 : plan576.Valid := valid_step _ _ _ valid134 (by decide +kernel)
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)

















































































































theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)









theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1606 : plan1606.Valid := valid_step _ _ _ valid580 (by decide +kernel)




















































end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)





































theorem valid3475 : plan3475.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3477 : plan3477.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

















































theorem valid3507 : plan3507.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3508 : plan3508.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3509 : plan3509.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3510 : plan3510.Valid := valid_step _ _ _ valid1606 (by decide +kernel)




















































































end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)













































theorem valid5879 : plan5879.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5880 : plan5880.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5881 : plan5881.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5882 : plan5882.Valid := valid_step _ _ _ valid3510 (by decide +kernel)

theorem valid5883 : plan5883.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5884 : plan5884.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5885 : plan5885.Valid := valid_step _ _ _ valid3477 (by decide +kernel)

theorem valid5886 : plan5886.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5887 : plan5887.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5888 : plan5888.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5889 : plan5889.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5890 : plan5890.Valid := valid_step _ _ _ valid3482 (by decide +kernel)




























































































































end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)































































































































theorem valid7360 : plan7360.Valid := valid_step _ _ _ valid5879 (by decide +kernel)

theorem valid7361 : plan7361.Valid := valid_step _ _ _ valid5880 (by decide +kernel)

theorem valid7362 : plan7362.Valid := valid_step _ _ _ valid5881 (by decide +kernel)

theorem valid7363 : plan7363.Valid := valid_step _ _ _ valid5882 (by decide +kernel)

theorem valid7364 : plan7364.Valid := valid_step _ _ _ valid5883 (by decide +kernel)

theorem valid7365 : plan7365.Valid := valid_step _ _ _ valid5884 (by decide +kernel)

theorem valid7366 : plan7366.Valid := valid_step _ _ _ valid5885 (by decide +kernel)

theorem valid7367 : plan7367.Valid := valid_step _ _ _ valid5886 (by decide +kernel)

theorem valid7368 : plan7368.Valid := valid_step _ _ _ valid5887 (by decide +kernel)

theorem valid7369 : plan7369.Valid := valid_step _ _ _ valid5888 (by decide +kernel)

theorem valid7370 : plan7370.Valid := valid_step _ _ _ valid5889 (by decide +kernel)

theorem valid7371 : plan7371.Valid := valid_step _ _ _ valid5890 (by decide +kernel)










































end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)
open ThreeBoundEndpoint22Packed (tree)
theorem t6_749choices : plan7360.choices=[2,5,10,7,7,7].map (options 6 5) := by rfl


theorem t6_749part0 : t6_749jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_749part1 : t6_749jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_749part2 : t6_749jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_749frontier : t6_749root.frontier 2=t6_749jobs := by rfl
theorem t6_749all : t6_749jobs.all (Job.check tree)=true := by
  simp only [t6_749jobs,List.all_append,List.all_nil,t6_749part0,t6_749part1,t6_749part2,Bool.and_self]
theorem t6_749checked : Checked tree [2,5,10,7,7,7] := by
  refine ⟨plan7360,valid7360,t6_749choices,?_⟩
  exact check_of_frontier tree 2 t6_749root t6_749jobs t6_749frontier t6_749all
theorem t6_750choices : plan7361.choices=[2,5,10,10,7,7].map (options 6 5) := by rfl


theorem t6_750part0 : t6_750jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_750part1 : t6_750jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_750frontier : t6_750root.frontier 2=t6_750jobs := by rfl
theorem t6_750all : t6_750jobs.all (Job.check tree)=true := by
  simp only [t6_750jobs,List.all_append,List.all_nil,t6_750part0,t6_750part1,Bool.and_self]
theorem t6_750checked : Checked tree [2,5,10,10,7,7] := by
  refine ⟨plan7361,valid7361,t6_750choices,?_⟩
  exact check_of_frontier tree 2 t6_750root t6_750jobs t6_750frontier t6_750all
theorem t6_751choices : plan7362.choices=[2,5,10,10,10,7].map (options 6 5) := by rfl


theorem t6_751part0 : t6_751jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_751frontier : t6_751root.frontier 0=t6_751jobs := by rfl
theorem t6_751all : t6_751jobs.all (Job.check tree)=true := by
  simp only [t6_751jobs,List.all_append,List.all_nil,t6_751part0,Bool.and_self]
theorem t6_751checked : Checked tree [2,5,10,10,10,7] := by
  refine ⟨plan7362,valid7362,t6_751choices,?_⟩
  exact check_of_frontier tree 0 t6_751root t6_751jobs t6_751frontier t6_751all
theorem t6_752choices : plan7363.choices=[2,5,10,10,10,10].map (options 6 5) := by rfl


theorem t6_752part0 : t6_752jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_752frontier : t6_752root.frontier 0=t6_752jobs := by rfl
theorem t6_752all : t6_752jobs.all (Job.check tree)=true := by
  simp only [t6_752jobs,List.all_append,List.all_nil,t6_752part0,Bool.and_self]
theorem t6_752checked : Checked tree [2,5,10,10,10,10] := by
  refine ⟨plan7363,valid7363,t6_752choices,?_⟩
  exact check_of_frontier tree 0 t6_752root t6_752jobs t6_752frontier t6_752all
theorem t6_753choices : plan7364.choices=[2,6,6,6,6,6].map (options 6 5) := by rfl


theorem t6_753part0 : t6_753jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_753frontier : t6_753root.frontier 0=t6_753jobs := by rfl
theorem t6_753all : t6_753jobs.all (Job.check tree)=true := by
  simp only [t6_753jobs,List.all_append,List.all_nil,t6_753part0,Bool.and_self]
theorem t6_753checked : Checked tree [2,6,6,6,6,6] := by
  refine ⟨plan7364,valid7364,t6_753choices,?_⟩
  exact check_of_frontier tree 0 t6_753root t6_753jobs t6_753frontier t6_753all
theorem t6_754choices : plan7365.choices=[2,6,6,6,6,7].map (options 6 5) := by rfl


theorem t6_754part0 : t6_754jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_754frontier : t6_754root.frontier 0=t6_754jobs := by rfl
theorem t6_754all : t6_754jobs.all (Job.check tree)=true := by
  simp only [t6_754jobs,List.all_append,List.all_nil,t6_754part0,Bool.and_self]
theorem t6_754checked : Checked tree [2,6,6,6,6,7] := by
  refine ⟨plan7365,valid7365,t6_754choices,?_⟩
  exact check_of_frontier tree 0 t6_754root t6_754jobs t6_754frontier t6_754all
theorem t6_755choices : plan7366.choices=[2,6,6,6,6,10].map (options 6 5) := by rfl


theorem t6_755part0 : t6_755jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_755frontier : t6_755root.frontier 0=t6_755jobs := by rfl
theorem t6_755all : t6_755jobs.all (Job.check tree)=true := by
  simp only [t6_755jobs,List.all_append,List.all_nil,t6_755part0,Bool.and_self]
theorem t6_755checked : Checked tree [2,6,6,6,6,10] := by
  refine ⟨plan7366,valid7366,t6_755choices,?_⟩
  exact check_of_frontier tree 0 t6_755root t6_755jobs t6_755frontier t6_755all
theorem t6_756choices : plan7367.choices=[2,6,6,6,7,7].map (options 6 5) := by rfl


theorem t6_756part0 : t6_756jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_756part1 : t6_756jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_756frontier : t6_756root.frontier 1=t6_756jobs := by rfl
theorem t6_756all : t6_756jobs.all (Job.check tree)=true := by
  simp only [t6_756jobs,List.all_append,List.all_nil,t6_756part0,t6_756part1,Bool.and_self]
theorem t6_756checked : Checked tree [2,6,6,6,7,7] := by
  refine ⟨plan7367,valid7367,t6_756choices,?_⟩
  exact check_of_frontier tree 1 t6_756root t6_756jobs t6_756frontier t6_756all
theorem t6_757choices : plan7368.choices=[2,6,6,6,10,7].map (options 6 5) := by rfl


theorem t6_757part0 : t6_757jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_757part1 : t6_757jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_757frontier : t6_757root.frontier 2=t6_757jobs := by rfl
theorem t6_757all : t6_757jobs.all (Job.check tree)=true := by
  simp only [t6_757jobs,List.all_append,List.all_nil,t6_757part0,t6_757part1,Bool.and_self]
theorem t6_757checked : Checked tree [2,6,6,6,10,7] := by
  refine ⟨plan7368,valid7368,t6_757choices,?_⟩
  exact check_of_frontier tree 2 t6_757root t6_757jobs t6_757frontier t6_757all
theorem t6_758choices : plan7369.choices=[2,6,6,6,10,10].map (options 6 5) := by rfl


theorem t6_758part0 : t6_758jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_758frontier : t6_758root.frontier 0=t6_758jobs := by rfl
theorem t6_758all : t6_758jobs.all (Job.check tree)=true := by
  simp only [t6_758jobs,List.all_append,List.all_nil,t6_758part0,Bool.and_self]
theorem t6_758checked : Checked tree [2,6,6,6,10,10] := by
  refine ⟨plan7369,valid7369,t6_758choices,?_⟩
  exact check_of_frontier tree 0 t6_758root t6_758jobs t6_758frontier t6_758all
theorem t6_759choices : plan7370.choices=[2,6,6,7,7,7].map (options 6 5) := by rfl


theorem t6_759part0 : t6_759jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_759part1 : t6_759jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_759part2 : t6_759jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_759frontier : t6_759root.frontier 2=t6_759jobs := by rfl
theorem t6_759all : t6_759jobs.all (Job.check tree)=true := by
  simp only [t6_759jobs,List.all_append,List.all_nil,t6_759part0,t6_759part1,t6_759part2,Bool.and_self]
theorem t6_759checked : Checked tree [2,6,6,7,7,7] := by
  refine ⟨plan7370,valid7370,t6_759choices,?_⟩
  exact check_of_frontier tree 2 t6_759root t6_759jobs t6_759frontier t6_759all
theorem t6_760choices : plan7371.choices=[2,6,6,10,7,7].map (options 6 5) := by rfl


theorem t6_760part0 : t6_760jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_760part1 : t6_760jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_760part2 : t6_760jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_760part3 : t6_760jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_760frontier : t6_760root.frontier 2=t6_760jobs := by rfl
theorem t6_760all : t6_760jobs.all (Job.check tree)=true := by
  simp only [t6_760jobs,List.all_append,List.all_nil,t6_760part0,t6_760part1,t6_760part2,t6_760part3,Bool.and_self]
theorem t6_760checked : Checked tree [2,6,6,10,7,7] := by
  refine ⟨plan7371,valid7371,t6_760choices,?_⟩
  exact check_of_frontier tree 2 t6_760root t6_760jobs t6_760frontier t6_760all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks089 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_757checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_758checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_759checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_760checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_749checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_750checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_751checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_752checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_753checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_754checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_755checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_756checked⟩
