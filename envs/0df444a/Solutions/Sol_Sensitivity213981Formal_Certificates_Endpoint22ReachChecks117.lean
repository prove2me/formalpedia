-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks117
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:54:33.925392+00:00
-- url     : https://prove2.me/submissions/59796b84-a324-486d-8c20-5056a4540efa

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks117
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks117
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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

























































































































































theorem valid557 : plan557.Valid := valid_step _ _ _ valid128 (by decide +kernel)























theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)



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

































theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1582 : plan1582.Valid := valid_step _ _ _ valid573 (by decide +kernel)

















theorem valid1591 : plan1591.Valid := valid_step _ _ _ valid578 (by decide +kernel)



theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)





theorem valid1602 : plan1602.Valid := valid_step _ _ _ valid578 (by decide +kernel)



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























































































































theorem valid3324 : plan3324.Valid := valid_step _ _ _ valid1530 (by decide +kernel)























theorem valid3336 : plan3336.Valid := valid_step _ _ _ valid1530 (by decide +kernel)
















































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













































































































































































theorem valid5463 : plan5463.Valid := valid_step _ _ _ valid3324 (by decide +kernel)

















theorem valid5472 : plan5472.Valid := valid_step _ _ _ valid3336 (by decide +kernel)
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













theorem valid3367 : plan3367.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3368 : plan3368.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3369 : plan3369.Valid := valid_step _ _ _ valid1582 (by decide +kernel)











theorem valid3375 : plan3375.Valid := valid_step _ _ _ valid1560 (by decide +kernel)



theorem valid3377 : plan3377.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3378 : plan3378.Valid := valid_step _ _ _ valid1563 (by decide +kernel)







































































theorem valid3414 : plan3414.Valid := valid_step _ _ _ valid1560 (by decide +kernel)



theorem valid3416 : plan3416.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3417 : plan3417.Valid := valid_step _ _ _ valid1563 (by decide +kernel)














































































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

theorem valid5569 : plan5569.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5570 : plan5570.Valid := valid_step _ _ _ valid3368 (by decide +kernel)

theorem valid5571 : plan5571.Valid := valid_step _ _ _ valid3369 (by decide +kernel)

theorem valid5572 : plan5572.Valid := valid_step _ _ _ valid3375 (by decide +kernel)

theorem valid5573 : plan5573.Valid := valid_step _ _ _ valid3377 (by decide +kernel)

theorem valid5574 : plan5574.Valid := valid_step _ _ _ valid3378 (by decide +kernel)























































theorem valid5602 : plan5602.Valid := valid_step _ _ _ valid3414 (by decide +kernel)

theorem valid5603 : plan5603.Valid := valid_step _ _ _ valid3416 (by decide +kernel)

theorem valid5604 : plan5604.Valid := valid_step _ _ _ valid3417 (by decide +kernel)
























































































































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







theorem valid6628 : plan6628.Valid := valid_step _ _ _ valid5463 (by decide +kernel)

theorem valid6629 : plan6629.Valid := valid_step _ _ _ valid5472 (by decide +kernel)






















































































































































































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





theorem valid3459 : plan3459.Valid := valid_step _ _ _ valid1591 (by decide +kernel)





theorem valid3462 : plan3462.Valid := valid_step _ _ _ valid1594 (by decide +kernel)



theorem valid3464 : plan3464.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3465 : plan3465.Valid := valid_step _ _ _ valid1597 (by decide +kernel)



theorem valid3467 : plan3467.Valid := valid_step _ _ _ valid1599 (by decide +kernel)





theorem valid3470 : plan3470.Valid := valid_step _ _ _ valid1602 (by decide +kernel)



theorem valid3472 : plan3472.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3473 : plan3473.Valid := valid_step _ _ _ valid1605 (by decide +kernel)



theorem valid3475 : plan3475.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3477 : plan3477.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

















theorem valid3494 : plan3494.Valid := valid_step _ _ _ valid1594 (by decide +kernel)



theorem valid3496 : plan3496.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3497 : plan3497.Valid := valid_step _ _ _ valid1597 (by decide +kernel)














































































































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























































































































































theorem valid5740 : plan5740.Valid := valid_step _ _ _ valid3459 (by decide +kernel)

theorem valid5741 : plan5741.Valid := valid_step _ _ _ valid3462 (by decide +kernel)

theorem valid5742 : plan5742.Valid := valid_step _ _ _ valid3464 (by decide +kernel)

theorem valid5743 : plan5743.Valid := valid_step _ _ _ valid3465 (by decide +kernel)

theorem valid5744 : plan5744.Valid := valid_step _ _ _ valid3467 (by decide +kernel)

theorem valid5745 : plan5745.Valid := valid_step _ _ _ valid3470 (by decide +kernel)

theorem valid5746 : plan5746.Valid := valid_step _ _ _ valid3472 (by decide +kernel)

theorem valid5747 : plan5747.Valid := valid_step _ _ _ valid3473 (by decide +kernel)

theorem valid5748 : plan5748.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5749 : plan5749.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5750 : plan5750.Valid := valid_step _ _ _ valid3477 (by decide +kernel)

theorem valid5751 : plan5751.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5752 : plan5752.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5753 : plan5753.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5754 : plan5754.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5755 : plan5755.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5756 : plan5756.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5757 : plan5757.Valid := valid_step _ _ _ valid3484 (by decide +kernel)

theorem valid5758 : plan5758.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5759 : plan5759.Valid := valid_step _ _ _ valid3494 (by decide +kernel)

theorem valid5760 : plan5760.Valid := valid_step _ _ _ valid3496 (by decide +kernel)
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

theorem valid5761 : plan5761.Valid := valid_step _ _ _ valid3497 (by decide +kernel)






























































































































































































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

















































































































































































theorem valid7001 : plan7001.Valid := valid_step _ _ _ valid5569 (by decide +kernel)

theorem valid7002 : plan7002.Valid := valid_step _ _ _ valid5570 (by decide +kernel)

theorem valid7003 : plan7003.Valid := valid_step _ _ _ valid5571 (by decide +kernel)

theorem valid7004 : plan7004.Valid := valid_step _ _ _ valid5572 (by decide +kernel)

theorem valid7005 : plan7005.Valid := valid_step _ _ _ valid5573 (by decide +kernel)

theorem valid7006 : plan7006.Valid := valid_step _ _ _ valid5574 (by decide +kernel)

theorem valid7007 : plan7007.Valid := valid_step _ _ _ valid5602 (by decide +kernel)

theorem valid7008 : plan7008.Valid := valid_step _ _ _ valid5603 (by decide +kernel)
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



















































































theorem valid7434 : plan7434.Valid := valid_step _ _ _ valid5740 (by decide +kernel)

theorem valid7435 : plan7435.Valid := valid_step _ _ _ valid5741 (by decide +kernel)

theorem valid7436 : plan7436.Valid := valid_step _ _ _ valid5742 (by decide +kernel)

theorem valid7437 : plan7437.Valid := valid_step _ _ _ valid5743 (by decide +kernel)

theorem valid7438 : plan7438.Valid := valid_step _ _ _ valid5744 (by decide +kernel)

theorem valid7439 : plan7439.Valid := valid_step _ _ _ valid5745 (by decide +kernel)

theorem valid7440 : plan7440.Valid := valid_step _ _ _ valid5746 (by decide +kernel)

theorem valid7441 : plan7441.Valid := valid_step _ _ _ valid5747 (by decide +kernel)

theorem valid7442 : plan7442.Valid := valid_step _ _ _ valid5748 (by decide +kernel)

theorem valid7443 : plan7443.Valid := valid_step _ _ _ valid5749 (by decide +kernel)

theorem valid7444 : plan7444.Valid := valid_step _ _ _ valid5750 (by decide +kernel)

theorem valid7445 : plan7445.Valid := valid_step _ _ _ valid5751 (by decide +kernel)

theorem valid7446 : plan7446.Valid := valid_step _ _ _ valid5752 (by decide +kernel)

theorem valid7447 : plan7447.Valid := valid_step _ _ _ valid5753 (by decide +kernel)

theorem valid7448 : plan7448.Valid := valid_step _ _ _ valid5754 (by decide +kernel)

theorem valid7449 : plan7449.Valid := valid_step _ _ _ valid5755 (by decide +kernel)

theorem valid7450 : plan7450.Valid := valid_step _ _ _ valid5756 (by decide +kernel)

theorem valid7451 : plan7451.Valid := valid_step _ _ _ valid5757 (by decide +kernel)

theorem valid7452 : plan7452.Valid := valid_step _ _ _ valid5758 (by decide +kernel)

theorem valid7453 : plan7453.Valid := valid_step _ _ _ valid5759 (by decide +kernel)

theorem valid7454 : plan7454.Valid := valid_step _ _ _ valid5760 (by decide +kernel)

theorem valid7455 : plan7455.Valid := valid_step _ _ _ valid5761 (by decide +kernel)


































































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

theorem valid7009 : plan7009.Valid := valid_step _ _ _ valid5604 (by decide +kernel)






























































































































































































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
theorem t6_919choices : plan7001.choices=[4,2,3,10,7,7].map (options 6 4) := by rfl


theorem t6_919part0 : t6_919jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_919part1 : t6_919jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_919part2 : t6_919jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_919frontier : t6_919root.frontier 2=t6_919jobs := by rfl
theorem t6_919all : t6_919jobs.all (Job.check tree)=true := by
  simp only [t6_919jobs,List.all_append,List.all_nil,t6_919part0,t6_919part1,t6_919part2,Bool.and_self]
theorem t6_919checked : Checked tree [4,2,3,10,7,7] := by
  refine ⟨plan7001,valid7001,t6_919choices,?_⟩
  exact check_of_frontier tree 2 t6_919root t6_919jobs t6_919frontier t6_919all
theorem t6_920choices : plan7002.choices=[4,2,3,10,10,7].map (options 6 4) := by rfl


theorem t6_920part0 : t6_920jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_920part1 : t6_920jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_920frontier : t6_920root.frontier 1=t6_920jobs := by rfl
theorem t6_920all : t6_920jobs.all (Job.check tree)=true := by
  simp only [t6_920jobs,List.all_append,List.all_nil,t6_920part0,t6_920part1,Bool.and_self]
theorem t6_920checked : Checked tree [4,2,3,10,10,7] := by
  refine ⟨plan7002,valid7002,t6_920choices,?_⟩
  exact check_of_frontier tree 1 t6_920root t6_920jobs t6_920frontier t6_920all
theorem t6_921choices : plan7003.choices=[4,2,3,10,10,10].map (options 6 4) := by rfl


theorem t6_921part0 : t6_921jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_921frontier : t6_921root.frontier 0=t6_921jobs := by rfl
theorem t6_921all : t6_921jobs.all (Job.check tree)=true := by
  simp only [t6_921jobs,List.all_append,List.all_nil,t6_921part0,Bool.and_self]
theorem t6_921checked : Checked tree [4,2,3,10,10,10] := by
  refine ⟨plan7003,valid7003,t6_921choices,?_⟩
  exact check_of_frontier tree 0 t6_921root t6_921jobs t6_921frontier t6_921all
theorem t6_922choices : plan6628.choices=[4,2,5,3,3,7].map (options 6 3) := by rfl


theorem t6_922part0 : t6_922jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_922frontier : t6_922root.frontier 0=t6_922jobs := by rfl
theorem t6_922all : t6_922jobs.all (Job.check tree)=true := by
  simp only [t6_922jobs,List.all_append,List.all_nil,t6_922part0,Bool.and_self]
theorem t6_922checked : Checked tree [4,2,5,3,3,7] := by
  refine ⟨plan6628,valid6628,t6_922choices,?_⟩
  exact check_of_frontier tree 0 t6_922root t6_922jobs t6_922frontier t6_922all
theorem t6_923choices : plan7004.choices=[4,2,5,3,6,7].map (options 6 4) := by rfl


theorem t6_923part0 : t6_923jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_923frontier : t6_923root.frontier 0=t6_923jobs := by rfl
theorem t6_923all : t6_923jobs.all (Job.check tree)=true := by
  simp only [t6_923jobs,List.all_append,List.all_nil,t6_923part0,Bool.and_self]
theorem t6_923checked : Checked tree [4,2,5,3,6,7] := by
  refine ⟨plan7004,valid7004,t6_923choices,?_⟩
  exact check_of_frontier tree 0 t6_923root t6_923jobs t6_923frontier t6_923all
theorem t6_924choices : plan7005.choices=[4,2,5,3,7,7].map (options 6 4) := by rfl


theorem t6_924part0 : t6_924jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_924part1 : t6_924jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_924frontier : t6_924root.frontier 1=t6_924jobs := by rfl
theorem t6_924all : t6_924jobs.all (Job.check tree)=true := by
  simp only [t6_924jobs,List.all_append,List.all_nil,t6_924part0,t6_924part1,Bool.and_self]
theorem t6_924checked : Checked tree [4,2,5,3,7,7] := by
  refine ⟨plan7005,valid7005,t6_924choices,?_⟩
  exact check_of_frontier tree 1 t6_924root t6_924jobs t6_924frontier t6_924all
theorem t6_925choices : plan7006.choices=[4,2,5,3,10,7].map (options 6 4) := by rfl


theorem t6_925part0 : t6_925jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_925frontier : t6_925root.frontier 0=t6_925jobs := by rfl
theorem t6_925all : t6_925jobs.all (Job.check tree)=true := by
  simp only [t6_925jobs,List.all_append,List.all_nil,t6_925part0,Bool.and_self]
theorem t6_925checked : Checked tree [4,2,5,3,10,7] := by
  refine ⟨plan7006,valid7006,t6_925choices,?_⟩
  exact check_of_frontier tree 0 t6_925root t6_925jobs t6_925frontier t6_925all
theorem t6_926choices : plan7434.choices=[4,2,5,5,7,7].map (options 6 5) := by rfl


theorem t6_926part0 : t6_926jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_926frontier : t6_926root.frontier 0=t6_926jobs := by rfl
theorem t6_926all : t6_926jobs.all (Job.check tree)=true := by
  simp only [t6_926jobs,List.all_append,List.all_nil,t6_926part0,Bool.and_self]
theorem t6_926checked : Checked tree [4,2,5,5,7,7] := by
  refine ⟨plan7434,valid7434,t6_926choices,?_⟩
  exact check_of_frontier tree 0 t6_926root t6_926jobs t6_926frontier t6_926all
theorem t6_927choices : plan7435.choices=[4,2,5,6,6,7].map (options 6 5) := by rfl


theorem t6_927part0 : t6_927jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_927frontier : t6_927root.frontier 0=t6_927jobs := by rfl
theorem t6_927all : t6_927jobs.all (Job.check tree)=true := by
  simp only [t6_927jobs,List.all_append,List.all_nil,t6_927part0,Bool.and_self]
theorem t6_927checked : Checked tree [4,2,5,6,6,7] := by
  refine ⟨plan7435,valid7435,t6_927choices,?_⟩
  exact check_of_frontier tree 0 t6_927root t6_927jobs t6_927frontier t6_927all
theorem t6_928choices : plan7436.choices=[4,2,5,6,7,7].map (options 6 5) := by rfl


theorem t6_928part0 : t6_928jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_928frontier : t6_928root.frontier 0=t6_928jobs := by rfl
theorem t6_928all : t6_928jobs.all (Job.check tree)=true := by
  simp only [t6_928jobs,List.all_append,List.all_nil,t6_928part0,Bool.and_self]
theorem t6_928checked : Checked tree [4,2,5,6,7,7] := by
  refine ⟨plan7436,valid7436,t6_928choices,?_⟩
  exact check_of_frontier tree 0 t6_928root t6_928jobs t6_928frontier t6_928all
theorem t6_929choices : plan7437.choices=[4,2,5,6,10,7].map (options 6 5) := by rfl


theorem t6_929part0 : t6_929jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_929frontier : t6_929root.frontier 0=t6_929jobs := by rfl
theorem t6_929all : t6_929jobs.all (Job.check tree)=true := by
  simp only [t6_929jobs,List.all_append,List.all_nil,t6_929part0,Bool.and_self]
theorem t6_929checked : Checked tree [4,2,5,6,10,7] := by
  refine ⟨plan7437,valid7437,t6_929choices,?_⟩
  exact check_of_frontier tree 0 t6_929root t6_929jobs t6_929frontier t6_929all
theorem t6_930choices : plan7438.choices=[4,2,5,7,7,7].map (options 6 5) := by rfl


theorem t6_930part0 : t6_930jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_930frontier : t6_930root.frontier 0=t6_930jobs := by rfl
theorem t6_930all : t6_930jobs.all (Job.check tree)=true := by
  simp only [t6_930jobs,List.all_append,List.all_nil,t6_930part0,Bool.and_self]
theorem t6_930checked : Checked tree [4,2,5,7,7,7] := by
  refine ⟨plan7438,valid7438,t6_930choices,?_⟩
  exact check_of_frontier tree 0 t6_930root t6_930jobs t6_930frontier t6_930all
theorem t6_931choices : plan7439.choices=[4,2,5,9,7,7].map (options 6 5) := by rfl


theorem t6_931part0 : t6_931jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_931frontier : t6_931root.frontier 0=t6_931jobs := by rfl
theorem t6_931all : t6_931jobs.all (Job.check tree)=true := by
  simp only [t6_931jobs,List.all_append,List.all_nil,t6_931part0,Bool.and_self]
theorem t6_931checked : Checked tree [4,2,5,9,7,7] := by
  refine ⟨plan7439,valid7439,t6_931choices,?_⟩
  exact check_of_frontier tree 0 t6_931root t6_931jobs t6_931frontier t6_931all
theorem t6_932choices : plan7440.choices=[4,2,5,10,7,7].map (options 6 5) := by rfl


theorem t6_932part0 : t6_932jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_932frontier : t6_932root.frontier 0=t6_932jobs := by rfl
theorem t6_932all : t6_932jobs.all (Job.check tree)=true := by
  simp only [t6_932jobs,List.all_append,List.all_nil,t6_932part0,Bool.and_self]
theorem t6_932checked : Checked tree [4,2,5,10,7,7] := by
  refine ⟨plan7440,valid7440,t6_932choices,?_⟩
  exact check_of_frontier tree 0 t6_932root t6_932jobs t6_932frontier t6_932all
theorem t6_933choices : plan7441.choices=[4,2,5,10,10,7].map (options 6 5) := by rfl


theorem t6_933part0 : t6_933jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_933frontier : t6_933root.frontier 0=t6_933jobs := by rfl
theorem t6_933all : t6_933jobs.all (Job.check tree)=true := by
  simp only [t6_933jobs,List.all_append,List.all_nil,t6_933part0,Bool.and_self]
theorem t6_933checked : Checked tree [4,2,5,10,10,7] := by
  refine ⟨plan7441,valid7441,t6_933choices,?_⟩
  exact check_of_frontier tree 0 t6_933root t6_933jobs t6_933frontier t6_933all
theorem t6_934choices : plan7442.choices=[4,2,6,6,6,6].map (options 6 5) := by rfl


theorem t6_934part0 : t6_934jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_934frontier : t6_934root.frontier 0=t6_934jobs := by rfl
theorem t6_934all : t6_934jobs.all (Job.check tree)=true := by
  simp only [t6_934jobs,List.all_append,List.all_nil,t6_934part0,Bool.and_self]
theorem t6_934checked : Checked tree [4,2,6,6,6,6] := by
  refine ⟨plan7442,valid7442,t6_934choices,?_⟩
  exact check_of_frontier tree 0 t6_934root t6_934jobs t6_934frontier t6_934all
theorem t6_935choices : plan7443.choices=[4,2,6,6,6,7].map (options 6 5) := by rfl


theorem t6_935part0 : t6_935jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_935frontier : t6_935root.frontier 0=t6_935jobs := by rfl
theorem t6_935all : t6_935jobs.all (Job.check tree)=true := by
  simp only [t6_935jobs,List.all_append,List.all_nil,t6_935part0,Bool.and_self]
theorem t6_935checked : Checked tree [4,2,6,6,6,7] := by
  refine ⟨plan7443,valid7443,t6_935choices,?_⟩
  exact check_of_frontier tree 0 t6_935root t6_935jobs t6_935frontier t6_935all
theorem t6_936choices : plan7444.choices=[4,2,6,6,6,10].map (options 6 5) := by rfl


theorem t6_936part0 : t6_936jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_936frontier : t6_936root.frontier 0=t6_936jobs := by rfl
theorem t6_936all : t6_936jobs.all (Job.check tree)=true := by
  simp only [t6_936jobs,List.all_append,List.all_nil,t6_936part0,Bool.and_self]
theorem t6_936checked : Checked tree [4,2,6,6,6,10] := by
  refine ⟨plan7444,valid7444,t6_936choices,?_⟩
  exact check_of_frontier tree 0 t6_936root t6_936jobs t6_936frontier t6_936all
theorem t6_937choices : plan7445.choices=[4,2,6,6,7,7].map (options 6 5) := by rfl


theorem t6_937part0 : t6_937jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_937frontier : t6_937root.frontier 0=t6_937jobs := by rfl
theorem t6_937all : t6_937jobs.all (Job.check tree)=true := by
  simp only [t6_937jobs,List.all_append,List.all_nil,t6_937part0,Bool.and_self]
theorem t6_937checked : Checked tree [4,2,6,6,7,7] := by
  refine ⟨plan7445,valid7445,t6_937choices,?_⟩
  exact check_of_frontier tree 0 t6_937root t6_937jobs t6_937frontier t6_937all
theorem t6_938choices : plan7446.choices=[4,2,6,6,10,7].map (options 6 5) := by rfl


theorem t6_938part0 : t6_938jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_938frontier : t6_938root.frontier 0=t6_938jobs := by rfl
theorem t6_938all : t6_938jobs.all (Job.check tree)=true := by
  simp only [t6_938jobs,List.all_append,List.all_nil,t6_938part0,Bool.and_self]
theorem t6_938checked : Checked tree [4,2,6,6,10,7] := by
  refine ⟨plan7446,valid7446,t6_938choices,?_⟩
  exact check_of_frontier tree 0 t6_938root t6_938jobs t6_938frontier t6_938all
theorem t6_939choices : plan7447.choices=[4,2,6,6,10,10].map (options 6 5) := by rfl


theorem t6_939part0 : t6_939jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_939frontier : t6_939root.frontier 0=t6_939jobs := by rfl
theorem t6_939all : t6_939jobs.all (Job.check tree)=true := by
  simp only [t6_939jobs,List.all_append,List.all_nil,t6_939part0,Bool.and_self]
theorem t6_939checked : Checked tree [4,2,6,6,10,10] := by
  refine ⟨plan7447,valid7447,t6_939choices,?_⟩
  exact check_of_frontier tree 0 t6_939root t6_939jobs t6_939frontier t6_939all
theorem t6_940choices : plan7448.choices=[4,2,6,7,7,7].map (options 6 5) := by rfl


theorem t6_940part0 : t6_940jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_940frontier : t6_940root.frontier 0=t6_940jobs := by rfl
theorem t6_940all : t6_940jobs.all (Job.check tree)=true := by
  simp only [t6_940jobs,List.all_append,List.all_nil,t6_940part0,Bool.and_self]
theorem t6_940checked : Checked tree [4,2,6,7,7,7] := by
  refine ⟨plan7448,valid7448,t6_940choices,?_⟩
  exact check_of_frontier tree 0 t6_940root t6_940jobs t6_940frontier t6_940all
theorem t6_941choices : plan7449.choices=[4,2,6,10,7,7].map (options 6 5) := by rfl


theorem t6_941part0 : t6_941jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_941part1 : t6_941jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_941frontier : t6_941root.frontier 1=t6_941jobs := by rfl
theorem t6_941all : t6_941jobs.all (Job.check tree)=true := by
  simp only [t6_941jobs,List.all_append,List.all_nil,t6_941part0,t6_941part1,Bool.and_self]
theorem t6_941checked : Checked tree [4,2,6,10,7,7] := by
  refine ⟨plan7449,valid7449,t6_941choices,?_⟩
  exact check_of_frontier tree 1 t6_941root t6_941jobs t6_941frontier t6_941all
theorem t6_942choices : plan7450.choices=[4,2,6,10,10,7].map (options 6 5) := by rfl


theorem t6_942part0 : t6_942jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_942frontier : t6_942root.frontier 0=t6_942jobs := by rfl
theorem t6_942all : t6_942jobs.all (Job.check tree)=true := by
  simp only [t6_942jobs,List.all_append,List.all_nil,t6_942part0,Bool.and_self]
theorem t6_942checked : Checked tree [4,2,6,10,10,7] := by
  refine ⟨plan7450,valid7450,t6_942choices,?_⟩
  exact check_of_frontier tree 0 t6_942root t6_942jobs t6_942frontier t6_942all
theorem t6_943choices : plan7451.choices=[4,2,6,10,10,10].map (options 6 5) := by rfl


theorem t6_943part0 : t6_943jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_943frontier : t6_943root.frontier 0=t6_943jobs := by rfl
theorem t6_943all : t6_943jobs.all (Job.check tree)=true := by
  simp only [t6_943jobs,List.all_append,List.all_nil,t6_943part0,Bool.and_self]
theorem t6_943checked : Checked tree [4,2,6,10,10,10] := by
  refine ⟨plan7451,valid7451,t6_943choices,?_⟩
  exact check_of_frontier tree 0 t6_943root t6_943jobs t6_943frontier t6_943all
theorem t6_944choices : plan7452.choices=[4,2,7,7,7,7].map (options 6 5) := by rfl


theorem t6_944part0 : t6_944jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_944frontier : t6_944root.frontier 0=t6_944jobs := by rfl
theorem t6_944all : t6_944jobs.all (Job.check tree)=true := by
  simp only [t6_944jobs,List.all_append,List.all_nil,t6_944part0,Bool.and_self]
theorem t6_944checked : Checked tree [4,2,7,7,7,7] := by
  refine ⟨plan7452,valid7452,t6_944choices,?_⟩
  exact check_of_frontier tree 0 t6_944root t6_944jobs t6_944frontier t6_944all
theorem t6_945choices : plan6629.choices=[4,2,9,3,3,7].map (options 6 3) := by rfl


theorem t6_945part0 : t6_945jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_945frontier : t6_945root.frontier 0=t6_945jobs := by rfl
theorem t6_945all : t6_945jobs.all (Job.check tree)=true := by
  simp only [t6_945jobs,List.all_append,List.all_nil,t6_945part0,Bool.and_self]
theorem t6_945checked : Checked tree [4,2,9,3,3,7] := by
  refine ⟨plan6629,valid6629,t6_945choices,?_⟩
  exact check_of_frontier tree 0 t6_945root t6_945jobs t6_945frontier t6_945all
theorem t6_946choices : plan7007.choices=[4,2,9,3,6,7].map (options 6 4) := by rfl


theorem t6_946part0 : t6_946jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_946frontier : t6_946root.frontier 0=t6_946jobs := by rfl
theorem t6_946all : t6_946jobs.all (Job.check tree)=true := by
  simp only [t6_946jobs,List.all_append,List.all_nil,t6_946part0,Bool.and_self]
theorem t6_946checked : Checked tree [4,2,9,3,6,7] := by
  refine ⟨plan7007,valid7007,t6_946choices,?_⟩
  exact check_of_frontier tree 0 t6_946root t6_946jobs t6_946frontier t6_946all
theorem t6_947choices : plan7008.choices=[4,2,9,3,7,7].map (options 6 4) := by rfl


theorem t6_947part0 : t6_947jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_947part1 : t6_947jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_947frontier : t6_947root.frontier 1=t6_947jobs := by rfl
theorem t6_947all : t6_947jobs.all (Job.check tree)=true := by
  simp only [t6_947jobs,List.all_append,List.all_nil,t6_947part0,t6_947part1,Bool.and_self]
theorem t6_947checked : Checked tree [4,2,9,3,7,7] := by
  refine ⟨plan7008,valid7008,t6_947choices,?_⟩
  exact check_of_frontier tree 1 t6_947root t6_947jobs t6_947frontier t6_947all
theorem t6_948choices : plan7009.choices=[4,2,9,3,10,7].map (options 6 4) := by rfl


theorem t6_948part0 : t6_948jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_948frontier : t6_948root.frontier 0=t6_948jobs := by rfl
theorem t6_948all : t6_948jobs.all (Job.check tree)=true := by
  simp only [t6_948jobs,List.all_append,List.all_nil,t6_948part0,Bool.and_self]
theorem t6_948checked : Checked tree [4,2,9,3,10,7] := by
  refine ⟨plan7009,valid7009,t6_948choices,?_⟩
  exact check_of_frontier tree 0 t6_948root t6_948jobs t6_948frontier t6_948all
theorem t6_949choices : plan7453.choices=[4,2,9,6,6,7].map (options 6 5) := by rfl


theorem t6_949part0 : t6_949jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_949frontier : t6_949root.frontier 0=t6_949jobs := by rfl
theorem t6_949all : t6_949jobs.all (Job.check tree)=true := by
  simp only [t6_949jobs,List.all_append,List.all_nil,t6_949part0,Bool.and_self]
theorem t6_949checked : Checked tree [4,2,9,6,6,7] := by
  refine ⟨plan7453,valid7453,t6_949choices,?_⟩
  exact check_of_frontier tree 0 t6_949root t6_949jobs t6_949frontier t6_949all
theorem t6_950choices : plan7454.choices=[4,2,9,6,7,7].map (options 6 5) := by rfl


theorem t6_950part0 : t6_950jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_950frontier : t6_950root.frontier 0=t6_950jobs := by rfl
theorem t6_950all : t6_950jobs.all (Job.check tree)=true := by
  simp only [t6_950jobs,List.all_append,List.all_nil,t6_950part0,Bool.and_self]
theorem t6_950checked : Checked tree [4,2,9,6,7,7] := by
  refine ⟨plan7454,valid7454,t6_950choices,?_⟩
  exact check_of_frontier tree 0 t6_950root t6_950jobs t6_950frontier t6_950all
theorem t6_951choices : plan7455.choices=[4,2,9,6,10,7].map (options 6 5) := by rfl


theorem t6_951part0 : t6_951jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_951frontier : t6_951root.frontier 0=t6_951jobs := by rfl
theorem t6_951all : t6_951jobs.all (Job.check tree)=true := by
  simp only [t6_951jobs,List.all_append,List.all_nil,t6_951part0,Bool.and_self]
theorem t6_951checked : Checked tree [4,2,9,6,10,7] := by
  refine ⟨plan7455,valid7455,t6_951choices,?_⟩
  exact check_of_frontier tree 0 t6_951root t6_951jobs t6_951frontier t6_951all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks117 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_929checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_930checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_931checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_932checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_933checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_934checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_935checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_936checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_937checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_938checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_939checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_940checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_941checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_942checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_943checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_944checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_945checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_946checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_919checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_947checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_948checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_949checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_950checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_951checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_920checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_921checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_922checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_923checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_924checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_925checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_926checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_927checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_928checked⟩
