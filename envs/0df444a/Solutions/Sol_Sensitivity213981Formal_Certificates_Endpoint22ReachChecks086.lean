-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks086
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:31:33.158987+00:00
-- url     : https://prove2.me/submissions/85fc916f-02bf-42cf-89a5-36873bb1ea8f

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks086
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks086
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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





































































theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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











































































































































































theorem valid566 : plan566.Valid := valid_step _ _ _ valid131 (by decide +kernel)





theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)

theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid573 : plan573.Valid := valid_step _ _ _ valid132 (by decide +kernel)



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















































theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1561 : plan1561.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1564 : plan1564.Valid := valid_step _ _ _ valid573 (by decide +kernel)

theorem valid1565 : plan1565.Valid := valid_step _ _ _ valid566 (by decide +kernel)





















theorem valid1576 : plan1576.Valid := valid_step _ _ _ valid566 (by decide +kernel)



























theorem valid1590 : plan1590.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1591 : plan1591.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1592 : plan1592.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)



theorem valid1601 : plan1601.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1602 : plan1602.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1603 : plan1603.Valid := valid_step _ _ _ valid579 (by decide +kernel)

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





























theorem valid3375 : plan3375.Valid := valid_step _ _ _ valid1560 (by decide +kernel)

theorem valid3376 : plan3376.Valid := valid_step _ _ _ valid1561 (by decide +kernel)

theorem valid3377 : plan3377.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3378 : plan3378.Valid := valid_step _ _ _ valid1563 (by decide +kernel)

theorem valid3379 : plan3379.Valid := valid_step _ _ _ valid1564 (by decide +kernel)

theorem valid3380 : plan3380.Valid := valid_step _ _ _ valid1565 (by decide +kernel)





















theorem valid3391 : plan3391.Valid := valid_step _ _ _ valid1576 (by decide +kernel)


































































































































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



theorem valid3458 : plan3458.Valid := valid_step _ _ _ valid1590 (by decide +kernel)

theorem valid3459 : plan3459.Valid := valid_step _ _ _ valid1591 (by decide +kernel)

theorem valid3460 : plan3460.Valid := valid_step _ _ _ valid1592 (by decide +kernel)

theorem valid3461 : plan3461.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3462 : plan3462.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3463 : plan3463.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3464 : plan3464.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3465 : plan3465.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3466 : plan3466.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3467 : plan3467.Valid := valid_step _ _ _ valid1599 (by decide +kernel)



theorem valid3469 : plan3469.Valid := valid_step _ _ _ valid1601 (by decide +kernel)

theorem valid3470 : plan3470.Valid := valid_step _ _ _ valid1602 (by decide +kernel)

theorem valid3471 : plan3471.Valid := valid_step _ _ _ valid1603 (by decide +kernel)

theorem valid3472 : plan3472.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3473 : plan3473.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3474 : plan3474.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3475 : plan3475.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3477 : plan3477.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)


















































































































































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



































theorem valid5682 : plan5682.Valid := valid_step _ _ _ valid3375 (by decide +kernel)

theorem valid5683 : plan5683.Valid := valid_step _ _ _ valid3376 (by decide +kernel)

theorem valid5684 : plan5684.Valid := valid_step _ _ _ valid3377 (by decide +kernel)

theorem valid5685 : plan5685.Valid := valid_step _ _ _ valid3378 (by decide +kernel)

theorem valid5686 : plan5686.Valid := valid_step _ _ _ valid3379 (by decide +kernel)

theorem valid5687 : plan5687.Valid := valid_step _ _ _ valid3380 (by decide +kernel)

theorem valid5688 : plan5688.Valid := valid_step _ _ _ valid3391 (by decide +kernel)
















































































































































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













































































































































theorem valid5831 : plan5831.Valid := valid_step _ _ _ valid3458 (by decide +kernel)

theorem valid5832 : plan5832.Valid := valid_step _ _ _ valid3459 (by decide +kernel)

theorem valid5833 : plan5833.Valid := valid_step _ _ _ valid3460 (by decide +kernel)

theorem valid5834 : plan5834.Valid := valid_step _ _ _ valid3461 (by decide +kernel)

theorem valid5835 : plan5835.Valid := valid_step _ _ _ valid3462 (by decide +kernel)

theorem valid5836 : plan5836.Valid := valid_step _ _ _ valid3463 (by decide +kernel)

theorem valid5837 : plan5837.Valid := valid_step _ _ _ valid3464 (by decide +kernel)

theorem valid5838 : plan5838.Valid := valid_step _ _ _ valid3465 (by decide +kernel)

theorem valid5839 : plan5839.Valid := valid_step _ _ _ valid3466 (by decide +kernel)

theorem valid5840 : plan5840.Valid := valid_step _ _ _ valid3467 (by decide +kernel)



theorem valid5842 : plan5842.Valid := valid_step _ _ _ valid3469 (by decide +kernel)

theorem valid5843 : plan5843.Valid := valid_step _ _ _ valid3470 (by decide +kernel)

theorem valid5844 : plan5844.Valid := valid_step _ _ _ valid3471 (by decide +kernel)

theorem valid5845 : plan5845.Valid := valid_step _ _ _ valid3472 (by decide +kernel)

theorem valid5846 : plan5846.Valid := valid_step _ _ _ valid3473 (by decide +kernel)

theorem valid5847 : plan5847.Valid := valid_step _ _ _ valid3474 (by decide +kernel)

theorem valid5848 : plan5848.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5849 : plan5849.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5850 : plan5850.Valid := valid_step _ _ _ valid3477 (by decide +kernel)

theorem valid5851 : plan5851.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5852 : plan5852.Valid := valid_step _ _ _ valid3479 (by decide +kernel)








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















































theorem valid7320 : plan7320.Valid := valid_step _ _ _ valid5831 (by decide +kernel)

theorem valid7321 : plan7321.Valid := valid_step _ _ _ valid5832 (by decide +kernel)

theorem valid7322 : plan7322.Valid := valid_step _ _ _ valid5833 (by decide +kernel)

theorem valid7323 : plan7323.Valid := valid_step _ _ _ valid5834 (by decide +kernel)

theorem valid7324 : plan7324.Valid := valid_step _ _ _ valid5835 (by decide +kernel)

theorem valid7325 : plan7325.Valid := valid_step _ _ _ valid5836 (by decide +kernel)

theorem valid7326 : plan7326.Valid := valid_step _ _ _ valid5837 (by decide +kernel)

theorem valid7327 : plan7327.Valid := valid_step _ _ _ valid5838 (by decide +kernel)

theorem valid7328 : plan7328.Valid := valid_step _ _ _ valid5839 (by decide +kernel)

theorem valid7329 : plan7329.Valid := valid_step _ _ _ valid5840 (by decide +kernel)

theorem valid7330 : plan7330.Valid := valid_step _ _ _ valid5842 (by decide +kernel)

theorem valid7331 : plan7331.Valid := valid_step _ _ _ valid5843 (by decide +kernel)

theorem valid7332 : plan7332.Valid := valid_step _ _ _ valid5844 (by decide +kernel)

theorem valid7333 : plan7333.Valid := valid_step _ _ _ valid5845 (by decide +kernel)

theorem valid7334 : plan7334.Valid := valid_step _ _ _ valid5846 (by decide +kernel)

theorem valid7335 : plan7335.Valid := valid_step _ _ _ valid5847 (by decide +kernel)

theorem valid7336 : plan7336.Valid := valid_step _ _ _ valid5848 (by decide +kernel)

theorem valid7337 : plan7337.Valid := valid_step _ _ _ valid5849 (by decide +kernel)

theorem valid7338 : plan7338.Valid := valid_step _ _ _ valid5850 (by decide +kernel)

theorem valid7339 : plan7339.Valid := valid_step _ _ _ valid5851 (by decide +kernel)

theorem valid7340 : plan7340.Valid := valid_step _ _ _ valid5852 (by decide +kernel)








































































































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























































theorem valid6940 : plan6940.Valid := valid_step _ _ _ valid5682 (by decide +kernel)

theorem valid6941 : plan6941.Valid := valid_step _ _ _ valid5683 (by decide +kernel)

theorem valid6942 : plan6942.Valid := valid_step _ _ _ valid5684 (by decide +kernel)

theorem valid6943 : plan6943.Valid := valid_step _ _ _ valid5685 (by decide +kernel)

theorem valid6944 : plan6944.Valid := valid_step _ _ _ valid5686 (by decide +kernel)

theorem valid6945 : plan6945.Valid := valid_step _ _ _ valid5687 (by decide +kernel)

theorem valid6946 : plan6946.Valid := valid_step _ _ _ valid5688 (by decide +kernel)




























































































































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
theorem t6_691choices : plan6940.choices=[2,5,5,3,6,7].map (options 6 4) := by rfl


theorem t6_691part0 : t6_691jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_691part1 : t6_691jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_691part2 : t6_691jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_691frontier : t6_691root.frontier 1=t6_691jobs := by rfl
theorem t6_691all : t6_691jobs.all (Job.check tree)=true := by
  simp only [t6_691jobs,List.all_append,List.all_nil,t6_691part0,t6_691part1,t6_691part2,Bool.and_self]
theorem t6_691checked : Checked tree [2,5,5,3,6,7] := by
  refine ⟨plan6940,valid6940,t6_691choices,?_⟩
  exact check_of_frontier tree 1 t6_691root t6_691jobs t6_691frontier t6_691all
theorem t6_692choices : plan6941.choices=[2,5,5,3,6,10].map (options 6 4) := by rfl


theorem t6_692part0 : t6_692jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_692frontier : t6_692root.frontier 0=t6_692jobs := by rfl
theorem t6_692all : t6_692jobs.all (Job.check tree)=true := by
  simp only [t6_692jobs,List.all_append,List.all_nil,t6_692part0,Bool.and_self]
theorem t6_692checked : Checked tree [2,5,5,3,6,10] := by
  refine ⟨plan6941,valid6941,t6_692choices,?_⟩
  exact check_of_frontier tree 0 t6_692root t6_692jobs t6_692frontier t6_692all
theorem t6_693choices : plan6942.choices=[2,5,5,3,7,7].map (options 6 4) := by rfl


theorem t6_693part0 : t6_693jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_693part1 : t6_693jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_693part2 : t6_693jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_693frontier : t6_693root.frontier 1=t6_693jobs := by rfl
theorem t6_693all : t6_693jobs.all (Job.check tree)=true := by
  simp only [t6_693jobs,List.all_append,List.all_nil,t6_693part0,t6_693part1,t6_693part2,Bool.and_self]
theorem t6_693checked : Checked tree [2,5,5,3,7,7] := by
  refine ⟨plan6942,valid6942,t6_693choices,?_⟩
  exact check_of_frontier tree 1 t6_693root t6_693jobs t6_693frontier t6_693all
theorem t6_694choices : plan6943.choices=[2,5,5,3,10,7].map (options 6 4) := by rfl


theorem t6_694part0 : t6_694jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_694part1 : t6_694jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_694part2 : t6_694jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_694frontier : t6_694root.frontier 1=t6_694jobs := by rfl
theorem t6_694all : t6_694jobs.all (Job.check tree)=true := by
  simp only [t6_694jobs,List.all_append,List.all_nil,t6_694part0,t6_694part1,t6_694part2,Bool.and_self]
theorem t6_694checked : Checked tree [2,5,5,3,10,7] := by
  refine ⟨plan6943,valid6943,t6_694choices,?_⟩
  exact check_of_frontier tree 1 t6_694root t6_694jobs t6_694frontier t6_694all
theorem t6_695choices : plan6944.choices=[2,5,5,3,10,10].map (options 6 4) := by rfl


theorem t6_695part0 : t6_695jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_695frontier : t6_695root.frontier 0=t6_695jobs := by rfl
theorem t6_695all : t6_695jobs.all (Job.check tree)=true := by
  simp only [t6_695jobs,List.all_append,List.all_nil,t6_695part0,Bool.and_self]
theorem t6_695checked : Checked tree [2,5,5,3,10,10] := by
  refine ⟨plan6944,valid6944,t6_695choices,?_⟩
  exact check_of_frontier tree 0 t6_695root t6_695jobs t6_695frontier t6_695all
theorem t6_696choices : plan6945.choices=[2,5,5,5,3,7].map (options 6 4) := by rfl


theorem t6_696part0 : t6_696jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_696frontier : t6_696root.frontier 0=t6_696jobs := by rfl
theorem t6_696all : t6_696jobs.all (Job.check tree)=true := by
  simp only [t6_696jobs,List.all_append,List.all_nil,t6_696part0,Bool.and_self]
theorem t6_696checked : Checked tree [2,5,5,5,3,7] := by
  refine ⟨plan6945,valid6945,t6_696choices,?_⟩
  exact check_of_frontier tree 0 t6_696root t6_696jobs t6_696frontier t6_696all
theorem t6_697choices : plan7320.choices=[2,5,5,5,6,7].map (options 6 5) := by rfl


theorem t6_697part0 : t6_697jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_697frontier : t6_697root.frontier 0=t6_697jobs := by rfl
theorem t6_697all : t6_697jobs.all (Job.check tree)=true := by
  simp only [t6_697jobs,List.all_append,List.all_nil,t6_697part0,Bool.and_self]
theorem t6_697checked : Checked tree [2,5,5,5,6,7] := by
  refine ⟨plan7320,valid7320,t6_697choices,?_⟩
  exact check_of_frontier tree 0 t6_697root t6_697jobs t6_697frontier t6_697all
theorem t6_698choices : plan7321.choices=[2,5,5,5,7,7].map (options 6 5) := by rfl


theorem t6_698part0 : t6_698jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_698frontier : t6_698root.frontier 0=t6_698jobs := by rfl
theorem t6_698all : t6_698jobs.all (Job.check tree)=true := by
  simp only [t6_698jobs,List.all_append,List.all_nil,t6_698part0,Bool.and_self]
theorem t6_698checked : Checked tree [2,5,5,5,7,7] := by
  refine ⟨plan7321,valid7321,t6_698choices,?_⟩
  exact check_of_frontier tree 0 t6_698root t6_698jobs t6_698frontier t6_698all
theorem t6_699choices : plan7322.choices=[2,5,5,5,10,7].map (options 6 5) := by rfl


theorem t6_699part0 : t6_699jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_699frontier : t6_699root.frontier 0=t6_699jobs := by rfl
theorem t6_699all : t6_699jobs.all (Job.check tree)=true := by
  simp only [t6_699jobs,List.all_append,List.all_nil,t6_699part0,Bool.and_self]
theorem t6_699checked : Checked tree [2,5,5,5,10,7] := by
  refine ⟨plan7322,valid7322,t6_699choices,?_⟩
  exact check_of_frontier tree 0 t6_699root t6_699jobs t6_699frontier t6_699all
theorem t6_700choices : plan7323.choices=[2,5,5,6,6,6].map (options 6 5) := by rfl


theorem t6_700part0 : t6_700jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_700frontier : t6_700root.frontier 0=t6_700jobs := by rfl
theorem t6_700all : t6_700jobs.all (Job.check tree)=true := by
  simp only [t6_700jobs,List.all_append,List.all_nil,t6_700part0,Bool.and_self]
theorem t6_700checked : Checked tree [2,5,5,6,6,6] := by
  refine ⟨plan7323,valid7323,t6_700choices,?_⟩
  exact check_of_frontier tree 0 t6_700root t6_700jobs t6_700frontier t6_700all
theorem t6_701choices : plan7324.choices=[2,5,5,6,6,7].map (options 6 5) := by rfl


theorem t6_701part0 : t6_701jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_701frontier : t6_701root.frontier 0=t6_701jobs := by rfl
theorem t6_701all : t6_701jobs.all (Job.check tree)=true := by
  simp only [t6_701jobs,List.all_append,List.all_nil,t6_701part0,Bool.and_self]
theorem t6_701checked : Checked tree [2,5,5,6,6,7] := by
  refine ⟨plan7324,valid7324,t6_701choices,?_⟩
  exact check_of_frontier tree 0 t6_701root t6_701jobs t6_701frontier t6_701all
theorem t6_702choices : plan7325.choices=[2,5,5,6,6,10].map (options 6 5) := by rfl


theorem t6_702part0 : t6_702jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_702frontier : t6_702root.frontier 0=t6_702jobs := by rfl
theorem t6_702all : t6_702jobs.all (Job.check tree)=true := by
  simp only [t6_702jobs,List.all_append,List.all_nil,t6_702part0,Bool.and_self]
theorem t6_702checked : Checked tree [2,5,5,6,6,10] := by
  refine ⟨plan7325,valid7325,t6_702choices,?_⟩
  exact check_of_frontier tree 0 t6_702root t6_702jobs t6_702frontier t6_702all
theorem t6_703choices : plan7326.choices=[2,5,5,6,7,7].map (options 6 5) := by rfl


theorem t6_703part0 : t6_703jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_703frontier : t6_703root.frontier 0=t6_703jobs := by rfl
theorem t6_703all : t6_703jobs.all (Job.check tree)=true := by
  simp only [t6_703jobs,List.all_append,List.all_nil,t6_703part0,Bool.and_self]
theorem t6_703checked : Checked tree [2,5,5,6,7,7] := by
  refine ⟨plan7326,valid7326,t6_703choices,?_⟩
  exact check_of_frontier tree 0 t6_703root t6_703jobs t6_703frontier t6_703all
theorem t6_704choices : plan7327.choices=[2,5,5,6,10,7].map (options 6 5) := by rfl


theorem t6_704part0 : t6_704jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_704frontier : t6_704root.frontier 0=t6_704jobs := by rfl
theorem t6_704all : t6_704jobs.all (Job.check tree)=true := by
  simp only [t6_704jobs,List.all_append,List.all_nil,t6_704part0,Bool.and_self]
theorem t6_704checked : Checked tree [2,5,5,6,10,7] := by
  refine ⟨plan7327,valid7327,t6_704choices,?_⟩
  exact check_of_frontier tree 0 t6_704root t6_704jobs t6_704frontier t6_704all
theorem t6_705choices : plan7328.choices=[2,5,5,6,10,10].map (options 6 5) := by rfl


theorem t6_705part0 : t6_705jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_705frontier : t6_705root.frontier 0=t6_705jobs := by rfl
theorem t6_705all : t6_705jobs.all (Job.check tree)=true := by
  simp only [t6_705jobs,List.all_append,List.all_nil,t6_705part0,Bool.and_self]
theorem t6_705checked : Checked tree [2,5,5,6,10,10] := by
  refine ⟨plan7328,valid7328,t6_705choices,?_⟩
  exact check_of_frontier tree 0 t6_705root t6_705jobs t6_705frontier t6_705all
theorem t6_706choices : plan7329.choices=[2,5,5,7,7,7].map (options 6 5) := by rfl


theorem t6_706part0 : t6_706jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_706frontier : t6_706root.frontier 0=t6_706jobs := by rfl
theorem t6_706all : t6_706jobs.all (Job.check tree)=true := by
  simp only [t6_706jobs,List.all_append,List.all_nil,t6_706part0,Bool.and_self]
theorem t6_706checked : Checked tree [2,5,5,7,7,7] := by
  refine ⟨plan7329,valid7329,t6_706choices,?_⟩
  exact check_of_frontier tree 0 t6_706root t6_706jobs t6_706frontier t6_706all
theorem t6_707choices : plan6946.choices=[2,5,5,9,3,7].map (options 6 4) := by rfl


theorem t6_707part0 : t6_707jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_707frontier : t6_707root.frontier 0=t6_707jobs := by rfl
theorem t6_707all : t6_707jobs.all (Job.check tree)=true := by
  simp only [t6_707jobs,List.all_append,List.all_nil,t6_707part0,Bool.and_self]
theorem t6_707checked : Checked tree [2,5,5,9,3,7] := by
  refine ⟨plan6946,valid6946,t6_707choices,?_⟩
  exact check_of_frontier tree 0 t6_707root t6_707jobs t6_707frontier t6_707all
theorem t6_708choices : plan7330.choices=[2,5,5,9,6,7].map (options 6 5) := by rfl


theorem t6_708part0 : t6_708jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_708frontier : t6_708root.frontier 0=t6_708jobs := by rfl
theorem t6_708all : t6_708jobs.all (Job.check tree)=true := by
  simp only [t6_708jobs,List.all_append,List.all_nil,t6_708part0,Bool.and_self]
theorem t6_708checked : Checked tree [2,5,5,9,6,7] := by
  refine ⟨plan7330,valid7330,t6_708choices,?_⟩
  exact check_of_frontier tree 0 t6_708root t6_708jobs t6_708frontier t6_708all
theorem t6_709choices : plan7331.choices=[2,5,5,9,7,7].map (options 6 5) := by rfl


theorem t6_709part0 : t6_709jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_709frontier : t6_709root.frontier 0=t6_709jobs := by rfl
theorem t6_709all : t6_709jobs.all (Job.check tree)=true := by
  simp only [t6_709jobs,List.all_append,List.all_nil,t6_709part0,Bool.and_self]
theorem t6_709checked : Checked tree [2,5,5,9,7,7] := by
  refine ⟨plan7331,valid7331,t6_709choices,?_⟩
  exact check_of_frontier tree 0 t6_709root t6_709jobs t6_709frontier t6_709all
theorem t6_710choices : plan7332.choices=[2,5,5,9,10,7].map (options 6 5) := by rfl


theorem t6_710part0 : t6_710jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_710frontier : t6_710root.frontier 0=t6_710jobs := by rfl
theorem t6_710all : t6_710jobs.all (Job.check tree)=true := by
  simp only [t6_710jobs,List.all_append,List.all_nil,t6_710part0,Bool.and_self]
theorem t6_710checked : Checked tree [2,5,5,9,10,7] := by
  refine ⟨plan7332,valid7332,t6_710choices,?_⟩
  exact check_of_frontier tree 0 t6_710root t6_710jobs t6_710frontier t6_710all
theorem t6_711choices : plan7333.choices=[2,5,5,10,7,7].map (options 6 5) := by rfl


theorem t6_711part0 : t6_711jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_711frontier : t6_711root.frontier 0=t6_711jobs := by rfl
theorem t6_711all : t6_711jobs.all (Job.check tree)=true := by
  simp only [t6_711jobs,List.all_append,List.all_nil,t6_711part0,Bool.and_self]
theorem t6_711checked : Checked tree [2,5,5,10,7,7] := by
  refine ⟨plan7333,valid7333,t6_711choices,?_⟩
  exact check_of_frontier tree 0 t6_711root t6_711jobs t6_711frontier t6_711all
theorem t6_712choices : plan7334.choices=[2,5,5,10,10,7].map (options 6 5) := by rfl


theorem t6_712part0 : t6_712jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_712frontier : t6_712root.frontier 0=t6_712jobs := by rfl
theorem t6_712all : t6_712jobs.all (Job.check tree)=true := by
  simp only [t6_712jobs,List.all_append,List.all_nil,t6_712part0,Bool.and_self]
theorem t6_712checked : Checked tree [2,5,5,10,10,7] := by
  refine ⟨plan7334,valid7334,t6_712choices,?_⟩
  exact check_of_frontier tree 0 t6_712root t6_712jobs t6_712frontier t6_712all
theorem t6_713choices : plan7335.choices=[2,5,5,10,10,10].map (options 6 5) := by rfl


theorem t6_713part0 : t6_713jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_713frontier : t6_713root.frontier 0=t6_713jobs := by rfl
theorem t6_713all : t6_713jobs.all (Job.check tree)=true := by
  simp only [t6_713jobs,List.all_append,List.all_nil,t6_713part0,Bool.and_self]
theorem t6_713checked : Checked tree [2,5,5,10,10,10] := by
  refine ⟨plan7335,valid7335,t6_713choices,?_⟩
  exact check_of_frontier tree 0 t6_713root t6_713jobs t6_713frontier t6_713all
theorem t6_714choices : plan7336.choices=[2,5,6,6,6,6].map (options 6 5) := by rfl


theorem t6_714part0 : t6_714jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_714frontier : t6_714root.frontier 0=t6_714jobs := by rfl
theorem t6_714all : t6_714jobs.all (Job.check tree)=true := by
  simp only [t6_714jobs,List.all_append,List.all_nil,t6_714part0,Bool.and_self]
theorem t6_714checked : Checked tree [2,5,6,6,6,6] := by
  refine ⟨plan7336,valid7336,t6_714choices,?_⟩
  exact check_of_frontier tree 0 t6_714root t6_714jobs t6_714frontier t6_714all
theorem t6_715choices : plan7337.choices=[2,5,6,6,6,7].map (options 6 5) := by rfl


theorem t6_715part0 : t6_715jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_715frontier : t6_715root.frontier 0=t6_715jobs := by rfl
theorem t6_715all : t6_715jobs.all (Job.check tree)=true := by
  simp only [t6_715jobs,List.all_append,List.all_nil,t6_715part0,Bool.and_self]
theorem t6_715checked : Checked tree [2,5,6,6,6,7] := by
  refine ⟨plan7337,valid7337,t6_715choices,?_⟩
  exact check_of_frontier tree 0 t6_715root t6_715jobs t6_715frontier t6_715all
theorem t6_716choices : plan7338.choices=[2,5,6,6,6,10].map (options 6 5) := by rfl


theorem t6_716part0 : t6_716jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_716frontier : t6_716root.frontier 0=t6_716jobs := by rfl
theorem t6_716all : t6_716jobs.all (Job.check tree)=true := by
  simp only [t6_716jobs,List.all_append,List.all_nil,t6_716part0,Bool.and_self]
theorem t6_716checked : Checked tree [2,5,6,6,6,10] := by
  refine ⟨plan7338,valid7338,t6_716choices,?_⟩
  exact check_of_frontier tree 0 t6_716root t6_716jobs t6_716frontier t6_716all
theorem t6_717choices : plan7339.choices=[2,5,6,6,7,7].map (options 6 5) := by rfl


theorem t6_717part0 : t6_717jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_717part1 : t6_717jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_717frontier : t6_717root.frontier 2=t6_717jobs := by rfl
theorem t6_717all : t6_717jobs.all (Job.check tree)=true := by
  simp only [t6_717jobs,List.all_append,List.all_nil,t6_717part0,t6_717part1,Bool.and_self]
theorem t6_717checked : Checked tree [2,5,6,6,7,7] := by
  refine ⟨plan7339,valid7339,t6_717choices,?_⟩
  exact check_of_frontier tree 2 t6_717root t6_717jobs t6_717frontier t6_717all
theorem t6_718choices : plan7340.choices=[2,5,6,6,10,7].map (options 6 5) := by rfl


theorem t6_718part0 : t6_718jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_718part1 : t6_718jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_718frontier : t6_718root.frontier 2=t6_718jobs := by rfl
theorem t6_718all : t6_718jobs.all (Job.check tree)=true := by
  simp only [t6_718jobs,List.all_append,List.all_nil,t6_718part0,t6_718part1,Bool.and_self]
theorem t6_718checked : Checked tree [2,5,6,6,10,7] := by
  refine ⟨plan7340,valid7340,t6_718choices,?_⟩
  exact check_of_frontier tree 2 t6_718root t6_718jobs t6_718frontier t6_718all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks086 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_702checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_703checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_704checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_705checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_706checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_707checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_691checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_708checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_709checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_710checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_711checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_712checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_713checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_714checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_715checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_716checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_692checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_717checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_718checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_693checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_694checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_695checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_696checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_697checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_698checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_699checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_700checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_701checked⟩
