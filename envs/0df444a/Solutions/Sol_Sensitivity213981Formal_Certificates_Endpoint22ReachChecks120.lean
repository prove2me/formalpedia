-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks120
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:44:23.544989+00:00
-- url     : https://prove2.me/submissions/86bee8e0-3c6c-450a-90c7-a51091b92175

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks120
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks120
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
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































































theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)





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

























































































































































theorem valid557 : plan557.Valid := valid_step _ _ _ valid128 (by decide +kernel)























theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)



theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)







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



















































































































































































theorem valid1530 : plan1530.Valid := valid_step _ _ _ valid557 (by decide +kernel)












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



theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)





























































theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)



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















































































theorem valid3304 : plan3304.Valid := valid_step _ _ _ valid1530 (by decide +kernel)

















































































theorem valid3345 : plan3345.Valid := valid_step _ _ _ valid1562 (by decide +kernel)



















theorem valid3355 : plan3355.Valid := valid_step _ _ _ valid1560 (by decide +kernel)



theorem valid3357 : plan3357.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3358 : plan3358.Valid := valid_step _ _ _ valid1563 (by decide +kernel)




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

























































































































































theorem valid3437 : plan3437.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3438 : plan3438.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3439 : plan3439.Valid := valid_step _ _ _ valid1604 (by decide +kernel)



theorem valid3441 : plan3441.Valid := valid_step _ _ _ valid1594 (by decide +kernel)



theorem valid3443 : plan3443.Valid := valid_step _ _ _ valid1596 (by decide +kernel)


























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

















































theorem valid5497 : plan5497.Valid := valid_step _ _ _ valid3304 (by decide +kernel)














































































































































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





























































































































































theorem valid5647 : plan5647.Valid := valid_step _ _ _ valid3345 (by decide +kernel)







theorem valid5651 : plan5651.Valid := valid_step _ _ _ valid3355 (by decide +kernel)

theorem valid5652 : plan5652.Valid := valid_step _ _ _ valid3357 (by decide +kernel)

theorem valid5653 : plan5653.Valid := valid_step _ _ _ valid3358 (by decide +kernel)






















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























theorem valid6636 : plan6636.Valid := valid_step _ _ _ valid5497 (by decide +kernel)








































































































































































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













































theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)











































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



























theorem valid5774 : plan5774.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5775 : plan5775.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5776 : plan5776.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5777 : plan5777.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5778 : plan5778.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5779 : plan5779.Valid := valid_step _ _ _ valid3484 (by decide +kernel)

theorem valid5780 : plan5780.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5781 : plan5781.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5782 : plan5782.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5783 : plan5783.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5784 : plan5784.Valid := valid_step _ _ _ valid3510 (by decide +kernel)

theorem valid5785 : plan5785.Valid := valid_step _ _ _ valid3437 (by decide +kernel)

theorem valid5786 : plan5786.Valid := valid_step _ _ _ valid3438 (by decide +kernel)

theorem valid5787 : plan5787.Valid := valid_step _ _ _ valid3439 (by decide +kernel)

theorem valid5788 : plan5788.Valid := valid_step _ _ _ valid3441 (by decide +kernel)

theorem valid5789 : plan5789.Valid := valid_step _ _ _ valid3443 (by decide +kernel)






































































































































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























































































































































theorem valid7468 : plan7468.Valid := valid_step _ _ _ valid5774 (by decide +kernel)

theorem valid7469 : plan7469.Valid := valid_step _ _ _ valid5775 (by decide +kernel)

theorem valid7470 : plan7470.Valid := valid_step _ _ _ valid5776 (by decide +kernel)

theorem valid7471 : plan7471.Valid := valid_step _ _ _ valid5777 (by decide +kernel)

theorem valid7472 : plan7472.Valid := valid_step _ _ _ valid5778 (by decide +kernel)

theorem valid7473 : plan7473.Valid := valid_step _ _ _ valid5779 (by decide +kernel)

theorem valid7474 : plan7474.Valid := valid_step _ _ _ valid5780 (by decide +kernel)

theorem valid7475 : plan7475.Valid := valid_step _ _ _ valid5781 (by decide +kernel)

theorem valid7476 : plan7476.Valid := valid_step _ _ _ valid5782 (by decide +kernel)

theorem valid7477 : plan7477.Valid := valid_step _ _ _ valid5783 (by decide +kernel)

theorem valid7478 : plan7478.Valid := valid_step _ _ _ valid5784 (by decide +kernel)

theorem valid7479 : plan7479.Valid := valid_step _ _ _ valid5785 (by decide +kernel)

theorem valid7480 : plan7480.Valid := valid_step _ _ _ valid5786 (by decide +kernel)

theorem valid7481 : plan7481.Valid := valid_step _ _ _ valid5787 (by decide +kernel)

theorem valid7482 : plan7482.Valid := valid_step _ _ _ valid5788 (by decide +kernel)

theorem valid7483 : plan7483.Valid := valid_step _ _ _ valid5789 (by decide +kernel)










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























theorem valid7020 : plan7020.Valid := valid_step _ _ _ valid5647 (by decide +kernel)

theorem valid7021 : plan7021.Valid := valid_step _ _ _ valid5651 (by decide +kernel)

theorem valid7022 : plan7022.Valid := valid_step _ _ _ valid5652 (by decide +kernel)

theorem valid7023 : plan7023.Valid := valid_step _ _ _ valid5653 (by decide +kernel)


































































































































































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
theorem t6_984choices : plan7468.choices=[4,3,6,6,10,7].map (options 6 5) := by rfl


theorem t6_984part0 : t6_984jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_984part1 : t6_984jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_984frontier : t6_984root.frontier 1=t6_984jobs := by rfl
theorem t6_984all : t6_984jobs.all (Job.check tree)=true := by
  simp only [t6_984jobs,List.all_append,List.all_nil,t6_984part0,t6_984part1,Bool.and_self]
theorem t6_984checked : Checked tree [4,3,6,6,10,7] := by
  refine ⟨plan7468,valid7468,t6_984choices,?_⟩
  exact check_of_frontier tree 1 t6_984root t6_984jobs t6_984frontier t6_984all
theorem t6_985choices : plan7469.choices=[4,3,6,6,10,10].map (options 6 5) := by rfl


theorem t6_985part0 : t6_985jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_985frontier : t6_985root.frontier 0=t6_985jobs := by rfl
theorem t6_985all : t6_985jobs.all (Job.check tree)=true := by
  simp only [t6_985jobs,List.all_append,List.all_nil,t6_985part0,Bool.and_self]
theorem t6_985checked : Checked tree [4,3,6,6,10,10] := by
  refine ⟨plan7469,valid7469,t6_985choices,?_⟩
  exact check_of_frontier tree 0 t6_985root t6_985jobs t6_985frontier t6_985all
theorem t6_986choices : plan7470.choices=[4,3,6,7,7,7].map (options 6 5) := by rfl


theorem t6_986part0 : t6_986jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_986part1 : t6_986jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_986part2 : t6_986jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_986frontier : t6_986root.frontier 1=t6_986jobs := by rfl
theorem t6_986all : t6_986jobs.all (Job.check tree)=true := by
  simp only [t6_986jobs,List.all_append,List.all_nil,t6_986part0,t6_986part1,t6_986part2,Bool.and_self]
theorem t6_986checked : Checked tree [4,3,6,7,7,7] := by
  refine ⟨plan7470,valid7470,t6_986choices,?_⟩
  exact check_of_frontier tree 1 t6_986root t6_986jobs t6_986frontier t6_986all
theorem t6_987choices : plan7471.choices=[4,3,6,10,7,7].map (options 6 5) := by rfl


theorem t6_987part0 : t6_987jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_987part1 : t6_987jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_987part2 : t6_987jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_987frontier : t6_987root.frontier 2=t6_987jobs := by rfl
theorem t6_987all : t6_987jobs.all (Job.check tree)=true := by
  simp only [t6_987jobs,List.all_append,List.all_nil,t6_987part0,t6_987part1,t6_987part2,Bool.and_self]
theorem t6_987checked : Checked tree [4,3,6,10,7,7] := by
  refine ⟨plan7471,valid7471,t6_987choices,?_⟩
  exact check_of_frontier tree 2 t6_987root t6_987jobs t6_987frontier t6_987all
theorem t6_988choices : plan7472.choices=[4,3,6,10,10,7].map (options 6 5) := by rfl


theorem t6_988part0 : t6_988jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_988part1 : t6_988jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_988frontier : t6_988root.frontier 1=t6_988jobs := by rfl
theorem t6_988all : t6_988jobs.all (Job.check tree)=true := by
  simp only [t6_988jobs,List.all_append,List.all_nil,t6_988part0,t6_988part1,Bool.and_self]
theorem t6_988checked : Checked tree [4,3,6,10,10,7] := by
  refine ⟨plan7472,valid7472,t6_988choices,?_⟩
  exact check_of_frontier tree 1 t6_988root t6_988jobs t6_988frontier t6_988all
theorem t6_989choices : plan7473.choices=[4,3,6,10,10,10].map (options 6 5) := by rfl


theorem t6_989part0 : t6_989jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_989frontier : t6_989root.frontier 0=t6_989jobs := by rfl
theorem t6_989all : t6_989jobs.all (Job.check tree)=true := by
  simp only [t6_989jobs,List.all_append,List.all_nil,t6_989part0,Bool.and_self]
theorem t6_989checked : Checked tree [4,3,6,10,10,10] := by
  refine ⟨plan7473,valid7473,t6_989choices,?_⟩
  exact check_of_frontier tree 0 t6_989root t6_989jobs t6_989frontier t6_989all
theorem t6_990choices : plan7474.choices=[4,3,7,7,7,7].map (options 6 5) := by rfl


theorem t6_990part0 : t6_990jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_990part1 : t6_990jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_990frontier : t6_990root.frontier 1=t6_990jobs := by rfl
theorem t6_990all : t6_990jobs.all (Job.check tree)=true := by
  simp only [t6_990jobs,List.all_append,List.all_nil,t6_990part0,t6_990part1,Bool.and_self]
theorem t6_990checked : Checked tree [4,3,7,7,7,7] := by
  refine ⟨plan7474,valid7474,t6_990choices,?_⟩
  exact check_of_frontier tree 1 t6_990root t6_990jobs t6_990frontier t6_990all
theorem t6_991choices : plan7475.choices=[4,3,10,7,7,7].map (options 6 5) := by rfl


theorem t6_991part0 : t6_991jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_991part1 : t6_991jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_991part2 : t6_991jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_991frontier : t6_991root.frontier 1=t6_991jobs := by rfl
theorem t6_991all : t6_991jobs.all (Job.check tree)=true := by
  simp only [t6_991jobs,List.all_append,List.all_nil,t6_991part0,t6_991part1,t6_991part2,Bool.and_self]
theorem t6_991checked : Checked tree [4,3,10,7,7,7] := by
  refine ⟨plan7475,valid7475,t6_991choices,?_⟩
  exact check_of_frontier tree 1 t6_991root t6_991jobs t6_991frontier t6_991all
theorem t6_992choices : plan7476.choices=[4,3,10,10,7,7].map (options 6 5) := by rfl


theorem t6_992part0 : t6_992jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_992part1 : t6_992jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_992frontier : t6_992root.frontier 1=t6_992jobs := by rfl
theorem t6_992all : t6_992jobs.all (Job.check tree)=true := by
  simp only [t6_992jobs,List.all_append,List.all_nil,t6_992part0,t6_992part1,Bool.and_self]
theorem t6_992checked : Checked tree [4,3,10,10,7,7] := by
  refine ⟨plan7476,valid7476,t6_992choices,?_⟩
  exact check_of_frontier tree 1 t6_992root t6_992jobs t6_992frontier t6_992all
theorem t6_993choices : plan7477.choices=[4,3,10,10,10,7].map (options 6 5) := by rfl


theorem t6_993part0 : t6_993jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_993frontier : t6_993root.frontier 0=t6_993jobs := by rfl
theorem t6_993all : t6_993jobs.all (Job.check tree)=true := by
  simp only [t6_993jobs,List.all_append,List.all_nil,t6_993part0,Bool.and_self]
theorem t6_993checked : Checked tree [4,3,10,10,10,7] := by
  refine ⟨plan7477,valid7477,t6_993choices,?_⟩
  exact check_of_frontier tree 0 t6_993root t6_993jobs t6_993frontier t6_993all
theorem t6_994choices : plan7478.choices=[4,3,10,10,10,10].map (options 6 5) := by rfl


theorem t6_994part0 : t6_994jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_994frontier : t6_994root.frontier 0=t6_994jobs := by rfl
theorem t6_994all : t6_994jobs.all (Job.check tree)=true := by
  simp only [t6_994jobs,List.all_append,List.all_nil,t6_994part0,Bool.and_self]
theorem t6_994checked : Checked tree [4,3,10,10,10,10] := by
  refine ⟨plan7478,valid7478,t6_994choices,?_⟩
  exact check_of_frontier tree 0 t6_994root t6_994jobs t6_994frontier t6_994all
theorem t6_995choices : plan7020.choices=[4,4,2,3,7,7].map (options 6 4) := by rfl


theorem t6_995part0 : t6_995jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_995frontier : t6_995root.frontier 0=t6_995jobs := by rfl
theorem t6_995all : t6_995jobs.all (Job.check tree)=true := by
  simp only [t6_995jobs,List.all_append,List.all_nil,t6_995part0,Bool.and_self]
theorem t6_995checked : Checked tree [4,4,2,3,7,7] := by
  refine ⟨plan7020,valid7020,t6_995choices,?_⟩
  exact check_of_frontier tree 0 t6_995root t6_995jobs t6_995frontier t6_995all
theorem t6_996choices : plan7479.choices=[4,4,2,6,7,7].map (options 6 5) := by rfl


theorem t6_996part0 : t6_996jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_996frontier : t6_996root.frontier 0=t6_996jobs := by rfl
theorem t6_996all : t6_996jobs.all (Job.check tree)=true := by
  simp only [t6_996jobs,List.all_append,List.all_nil,t6_996part0,Bool.and_self]
theorem t6_996checked : Checked tree [4,4,2,6,7,7] := by
  refine ⟨plan7479,valid7479,t6_996choices,?_⟩
  exact check_of_frontier tree 0 t6_996root t6_996jobs t6_996frontier t6_996all
theorem t6_997choices : plan7480.choices=[4,4,2,7,7,7].map (options 6 5) := by rfl


theorem t6_997part0 : t6_997jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_997frontier : t6_997root.frontier 0=t6_997jobs := by rfl
theorem t6_997all : t6_997jobs.all (Job.check tree)=true := by
  simp only [t6_997jobs,List.all_append,List.all_nil,t6_997part0,Bool.and_self]
theorem t6_997checked : Checked tree [4,4,2,7,7,7] := by
  refine ⟨plan7480,valid7480,t6_997choices,?_⟩
  exact check_of_frontier tree 0 t6_997root t6_997jobs t6_997frontier t6_997all
theorem t6_998choices : plan7481.choices=[4,4,2,10,7,7].map (options 6 5) := by rfl


theorem t6_998part0 : t6_998jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_998frontier : t6_998root.frontier 0=t6_998jobs := by rfl
theorem t6_998all : t6_998jobs.all (Job.check tree)=true := by
  simp only [t6_998jobs,List.all_append,List.all_nil,t6_998part0,Bool.and_self]
theorem t6_998checked : Checked tree [4,4,2,10,7,7] := by
  refine ⟨plan7481,valid7481,t6_998choices,?_⟩
  exact check_of_frontier tree 0 t6_998root t6_998jobs t6_998frontier t6_998all
theorem t6_999choices : plan6636.choices=[4,4,3,3,3,7].map (options 6 3) := by rfl


theorem t6_999part0 : t6_999jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_999frontier : t6_999root.frontier 0=t6_999jobs := by rfl
theorem t6_999all : t6_999jobs.all (Job.check tree)=true := by
  simp only [t6_999jobs,List.all_append,List.all_nil,t6_999part0,Bool.and_self]
theorem t6_999checked : Checked tree [4,4,3,3,3,7] := by
  refine ⟨plan6636,valid6636,t6_999choices,?_⟩
  exact check_of_frontier tree 0 t6_999root t6_999jobs t6_999frontier t6_999all
theorem t6_1000choices : plan7021.choices=[4,4,3,3,6,7].map (options 6 4) := by rfl


theorem t6_1000part0 : t6_1000jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1000frontier : t6_1000root.frontier 0=t6_1000jobs := by rfl
theorem t6_1000all : t6_1000jobs.all (Job.check tree)=true := by
  simp only [t6_1000jobs,List.all_append,List.all_nil,t6_1000part0,Bool.and_self]
theorem t6_1000checked : Checked tree [4,4,3,3,6,7] := by
  refine ⟨plan7021,valid7021,t6_1000choices,?_⟩
  exact check_of_frontier tree 0 t6_1000root t6_1000jobs t6_1000frontier t6_1000all
theorem t6_1001choices : plan7022.choices=[4,4,3,3,7,7].map (options 6 4) := by rfl


theorem t6_1001part0 : t6_1001jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1001frontier : t6_1001root.frontier 0=t6_1001jobs := by rfl
theorem t6_1001all : t6_1001jobs.all (Job.check tree)=true := by
  simp only [t6_1001jobs,List.all_append,List.all_nil,t6_1001part0,Bool.and_self]
theorem t6_1001checked : Checked tree [4,4,3,3,7,7] := by
  refine ⟨plan7022,valid7022,t6_1001choices,?_⟩
  exact check_of_frontier tree 0 t6_1001root t6_1001jobs t6_1001frontier t6_1001all
theorem t6_1002choices : plan7023.choices=[4,4,3,3,10,7].map (options 6 4) := by rfl


theorem t6_1002part0 : t6_1002jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1002frontier : t6_1002root.frontier 0=t6_1002jobs := by rfl
theorem t6_1002all : t6_1002jobs.all (Job.check tree)=true := by
  simp only [t6_1002jobs,List.all_append,List.all_nil,t6_1002part0,Bool.and_self]
theorem t6_1002checked : Checked tree [4,4,3,3,10,7] := by
  refine ⟨plan7023,valid7023,t6_1002choices,?_⟩
  exact check_of_frontier tree 0 t6_1002root t6_1002jobs t6_1002frontier t6_1002all
theorem t6_1003choices : plan7482.choices=[4,4,3,6,6,7].map (options 6 5) := by rfl


theorem t6_1003part0 : t6_1003jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1003frontier : t6_1003root.frontier 0=t6_1003jobs := by rfl
theorem t6_1003all : t6_1003jobs.all (Job.check tree)=true := by
  simp only [t6_1003jobs,List.all_append,List.all_nil,t6_1003part0,Bool.and_self]
theorem t6_1003checked : Checked tree [4,4,3,6,6,7] := by
  refine ⟨plan7482,valid7482,t6_1003choices,?_⟩
  exact check_of_frontier tree 0 t6_1003root t6_1003jobs t6_1003frontier t6_1003all
theorem t6_1004choices : plan7483.choices=[4,4,3,6,7,7].map (options 6 5) := by rfl


theorem t6_1004part0 : t6_1004jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1004frontier : t6_1004root.frontier 0=t6_1004jobs := by rfl
theorem t6_1004all : t6_1004jobs.all (Job.check tree)=true := by
  simp only [t6_1004jobs,List.all_append,List.all_nil,t6_1004part0,Bool.and_self]
theorem t6_1004checked : Checked tree [4,4,3,6,7,7] := by
  refine ⟨plan7483,valid7483,t6_1004choices,?_⟩
  exact check_of_frontier tree 0 t6_1004root t6_1004jobs t6_1004frontier t6_1004all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks120 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_992checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_993checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_994checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_995checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_984checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_996checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_997checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_998checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_999checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1000checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1001checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1002checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1003checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1004checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_985checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_986checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_987checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_988checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_989checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_990checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_991checked⟩
