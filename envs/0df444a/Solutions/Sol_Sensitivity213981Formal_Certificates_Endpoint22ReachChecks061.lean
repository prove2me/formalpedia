-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks061
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:11:57.935807+00:00
-- url     : https://prove2.me/submissions/8ac7eb95-15c7-49b6-b321-07900caf71e4

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
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









































theorem valid117 : plan117.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid119 : plan119.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid120 : plan120.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid121 : plan121.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid123 : plan123.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid125 : plan125.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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























































































































theorem valid540 : plan540.Valid := valid_step _ _ _ valid117 (by decide +kernel)



theorem valid542 : plan542.Valid := valid_step _ _ _ valid119 (by decide +kernel)

theorem valid543 : plan543.Valid := valid_step _ _ _ valid120 (by decide +kernel)

theorem valid544 : plan544.Valid := valid_step _ _ _ valid121 (by decide +kernel)





theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)



theorem valid549 : plan549.Valid := valid_step _ _ _ valid123 (by decide +kernel)

theorem valid550 : plan550.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid551 : plan551.Valid := valid_step _ _ _ valid125 (by decide +kernel)

theorem valid552 : plan552.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid553 : plan553.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid554 : plan554.Valid := valid_step _ _ _ valid125 (by decide +kernel)





theorem valid557 : plan557.Valid := valid_step _ _ _ valid128 (by decide +kernel)



theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)

theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)









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



































































































































theorem valid1506 : plan1506.Valid := valid_step _ _ _ valid540 (by decide +kernel)

theorem valid1507 : plan1507.Valid := valid_step _ _ _ valid543 (by decide +kernel)



theorem valid1509 : plan1509.Valid := valid_step _ _ _ valid542 (by decide +kernel)

theorem valid1510 : plan1510.Valid := valid_step _ _ _ valid543 (by decide +kernel)

theorem valid1511 : plan1511.Valid := valid_step _ _ _ valid544 (by decide +kernel)

theorem valid1512 : plan1512.Valid := valid_step _ _ _ valid550 (by decide +kernel)

theorem valid1513 : plan1513.Valid := valid_step _ _ _ valid552 (by decide +kernel)

theorem valid1514 : plan1514.Valid := valid_step _ _ _ valid553 (by decide +kernel)









theorem valid1519 : plan1519.Valid := valid_step _ _ _ valid549 (by decide +kernel)

theorem valid1520 : plan1520.Valid := valid_step _ _ _ valid550 (by decide +kernel)

theorem valid1521 : plan1521.Valid := valid_step _ _ _ valid551 (by decide +kernel)

theorem valid1522 : plan1522.Valid := valid_step _ _ _ valid552 (by decide +kernel)

theorem valid1523 : plan1523.Valid := valid_step _ _ _ valid553 (by decide +kernel)

theorem valid1524 : plan1524.Valid := valid_step _ _ _ valid554 (by decide +kernel)

theorem valid1525 : plan1525.Valid := valid_step _ _ _ valid547 (by decide +kernel)

theorem valid1526 : plan1526.Valid := valid_step _ _ _ valid547 (by decide +kernel)







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















































































































































theorem valid3240 : plan3240.Valid := valid_step _ _ _ valid1506 (by decide +kernel)



theorem valid3242 : plan3242.Valid := valid_step _ _ _ valid1507 (by decide +kernel)

theorem valid3243 : plan3243.Valid := valid_step _ _ _ valid1509 (by decide +kernel)

theorem valid3244 : plan3244.Valid := valid_step _ _ _ valid1510 (by decide +kernel)

theorem valid3245 : plan3245.Valid := valid_step _ _ _ valid1511 (by decide +kernel)













theorem valid3252 : plan3252.Valid := valid_step _ _ _ valid1512 (by decide +kernel)

theorem valid3253 : plan3253.Valid := valid_step _ _ _ valid1513 (by decide +kernel)

theorem valid3254 : plan3254.Valid := valid_step _ _ _ valid1514 (by decide +kernel)



theorem valid3256 : plan3256.Valid := valid_step _ _ _ valid1519 (by decide +kernel)

theorem valid3257 : plan3257.Valid := valid_step _ _ _ valid1520 (by decide +kernel)

theorem valid3258 : plan3258.Valid := valid_step _ _ _ valid1521 (by decide +kernel)

theorem valid3259 : plan3259.Valid := valid_step _ _ _ valid1522 (by decide +kernel)

theorem valid3260 : plan3260.Valid := valid_step _ _ _ valid1523 (by decide +kernel)

theorem valid3261 : plan3261.Valid := valid_step _ _ _ valid1524 (by decide +kernel)

theorem valid3262 : plan3262.Valid := valid_step _ _ _ valid1525 (by decide +kernel)

theorem valid3263 : plan3263.Valid := valid_step _ _ _ valid1526 (by decide +kernel)


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





theorem valid1539 : plan1539.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1540 : plan1540.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1541 : plan1541.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1542 : plan1542.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1543 : plan1543.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1544 : plan1544.Valid := valid_step _ _ _ valid561 (by decide +kernel)

theorem valid1545 : plan1545.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1546 : plan1546.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1547 : plan1547.Valid := valid_step _ _ _ valid564 (by decide +kernel)

theorem valid1548 : plan1548.Valid := valid_step _ _ _ valid562 (by decide +kernel)



theorem valid1550 : plan1550.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1551 : plan1551.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1552 : plan1552.Valid := valid_step _ _ _ valid563 (by decide +kernel)















theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)



theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)





























































theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)



theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)



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













































theorem valid3287 : plan3287.Valid := valid_step _ _ _ valid1539 (by decide +kernel)

theorem valid3288 : plan3288.Valid := valid_step _ _ _ valid1540 (by decide +kernel)

theorem valid3289 : plan3289.Valid := valid_step _ _ _ valid1541 (by decide +kernel)

theorem valid3290 : plan3290.Valid := valid_step _ _ _ valid1542 (by decide +kernel)

theorem valid3291 : plan3291.Valid := valid_step _ _ _ valid1543 (by decide +kernel)

theorem valid3292 : plan3292.Valid := valid_step _ _ _ valid1544 (by decide +kernel)

theorem valid3293 : plan3293.Valid := valid_step _ _ _ valid1545 (by decide +kernel)

theorem valid3294 : plan3294.Valid := valid_step _ _ _ valid1546 (by decide +kernel)

theorem valid3295 : plan3295.Valid := valid_step _ _ _ valid1547 (by decide +kernel)

theorem valid3296 : plan3296.Valid := valid_step _ _ _ valid1548 (by decide +kernel)

theorem valid3297 : plan3297.Valid := valid_step _ _ _ valid1550 (by decide +kernel)

theorem valid3298 : plan3298.Valid := valid_step _ _ _ valid1551 (by decide +kernel)

theorem valid3299 : plan3299.Valid := valid_step _ _ _ valid1552 (by decide +kernel)









































































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



























































































































theorem valid5342 : plan5342.Valid := valid_step _ _ _ valid3240 (by decide +kernel)







theorem valid5346 : plan5346.Valid := valid_step _ _ _ valid3242 (by decide +kernel)

theorem valid5347 : plan5347.Valid := valid_step _ _ _ valid3243 (by decide +kernel)

theorem valid5348 : plan5348.Valid := valid_step _ _ _ valid3244 (by decide +kernel)

theorem valid5349 : plan5349.Valid := valid_step _ _ _ valid3245 (by decide +kernel)

































theorem valid5366 : plan5366.Valid := valid_step _ _ _ valid3252 (by decide +kernel)

theorem valid5367 : plan5367.Valid := valid_step _ _ _ valid3253 (by decide +kernel)

theorem valid5368 : plan5368.Valid := valid_step _ _ _ valid3254 (by decide +kernel)



theorem valid5370 : plan5370.Valid := valid_step _ _ _ valid3256 (by decide +kernel)

theorem valid5371 : plan5371.Valid := valid_step _ _ _ valid3257 (by decide +kernel)

theorem valid5372 : plan5372.Valid := valid_step _ _ _ valid3258 (by decide +kernel)

theorem valid5373 : plan5373.Valid := valid_step _ _ _ valid3259 (by decide +kernel)

theorem valid5374 : plan5374.Valid := valid_step _ _ _ valid3260 (by decide +kernel)

theorem valid5375 : plan5375.Valid := valid_step _ _ _ valid3261 (by decide +kernel)

theorem valid5376 : plan5376.Valid := valid_step _ _ _ valid3262 (by decide +kernel)
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

theorem valid5377 : plan5377.Valid := valid_step _ _ _ valid3263 (by decide +kernel)











































































































theorem valid5431 : plan5431.Valid := valid_step _ _ _ valid3287 (by decide +kernel)

theorem valid5432 : plan5432.Valid := valid_step _ _ _ valid3288 (by decide +kernel)

theorem valid5433 : plan5433.Valid := valid_step _ _ _ valid3289 (by decide +kernel)

theorem valid5434 : plan5434.Valid := valid_step _ _ _ valid3290 (by decide +kernel)

theorem valid5435 : plan5435.Valid := valid_step _ _ _ valid3291 (by decide +kernel)

theorem valid5436 : plan5436.Valid := valid_step _ _ _ valid3292 (by decide +kernel)

theorem valid5437 : plan5437.Valid := valid_step _ _ _ valid3293 (by decide +kernel)

theorem valid5438 : plan5438.Valid := valid_step _ _ _ valid3294 (by decide +kernel)

theorem valid5439 : plan5439.Valid := valid_step _ _ _ valid3295 (by decide +kernel)

theorem valid5440 : plan5440.Valid := valid_step _ _ _ valid3296 (by decide +kernel)

theorem valid5441 : plan5441.Valid := valid_step _ _ _ valid3297 (by decide +kernel)

theorem valid5442 : plan5442.Valid := valid_step _ _ _ valid3298 (by decide +kernel)

theorem valid5443 : plan5443.Valid := valid_step _ _ _ valid3299 (by decide +kernel)


























































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













































































theorem valid6279 : plan6279.Valid := valid_step _ _ _ valid5342 (by decide +kernel)



































theorem valid6297 : plan6297.Valid := valid_step _ _ _ valid5346 (by decide +kernel)

theorem valid6298 : plan6298.Valid := valid_step _ _ _ valid5347 (by decide +kernel)

theorem valid6299 : plan6299.Valid := valid_step _ _ _ valid5348 (by decide +kernel)

theorem valid6300 : plan6300.Valid := valid_step _ _ _ valid5349 (by decide +kernel)








































































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



























































































































theorem valid5534 : plan5534.Valid := valid_step _ _ _ valid3336 (by decide +kernel)




































































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

















































theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

















theorem valid3494 : plan3494.Valid := valid_step _ _ _ valid1594 (by decide +kernel)



theorem valid3496 : plan3496.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3497 : plan3497.Valid := valid_step _ _ _ valid1597 (by decide +kernel)



theorem valid3499 : plan3499.Valid := valid_step _ _ _ valid1599 (by decide +kernel)





theorem valid3502 : plan3502.Valid := valid_step _ _ _ valid1602 (by decide +kernel)



theorem valid3504 : plan3504.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3505 : plan3505.Valid := valid_step _ _ _ valid1605 (by decide +kernel)



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











































































































































theorem valid5734 : plan5734.Valid := valid_step _ _ _ valid3414 (by decide +kernel)



theorem valid5736 : plan5736.Valid := valid_step _ _ _ valid3416 (by decide +kernel)

theorem valid5737 : plan5737.Valid := valid_step _ _ _ valid3417 (by decide +kernel)














































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













































































































































































theorem valid5943 : plan5943.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5944 : plan5944.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5945 : plan5945.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5946 : plan5946.Valid := valid_step _ _ _ valid3484 (by decide +kernel)

theorem valid5947 : plan5947.Valid := valid_step _ _ _ valid3485 (by decide +kernel)










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





















































theorem valid6363 : plan6363.Valid := valid_step _ _ _ valid5366 (by decide +kernel)

theorem valid6364 : plan6364.Valid := valid_step _ _ _ valid5367 (by decide +kernel)

theorem valid6365 : plan6365.Valid := valid_step _ _ _ valid5368 (by decide +kernel)

theorem valid6366 : plan6366.Valid := valid_step _ _ _ valid5370 (by decide +kernel)

theorem valid6367 : plan6367.Valid := valid_step _ _ _ valid5371 (by decide +kernel)

theorem valid6368 : plan6368.Valid := valid_step _ _ _ valid5372 (by decide +kernel)

theorem valid6369 : plan6369.Valid := valid_step _ _ _ valid5373 (by decide +kernel)

theorem valid6370 : plan6370.Valid := valid_step _ _ _ valid5374 (by decide +kernel)

theorem valid6371 : plan6371.Valid := valid_step _ _ _ valid5375 (by decide +kernel)

theorem valid6372 : plan6372.Valid := valid_step _ _ _ valid5376 (by decide +kernel)

theorem valid6373 : plan6373.Valid := valid_step _ _ _ valid5377 (by decide +kernel)






















































































































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





theorem valid5955 : plan5955.Valid := valid_step _ _ _ valid3494 (by decide +kernel)



theorem valid5957 : plan5957.Valid := valid_step _ _ _ valid3496 (by decide +kernel)

theorem valid5958 : plan5958.Valid := valid_step _ _ _ valid3497 (by decide +kernel)



theorem valid5960 : plan5960.Valid := valid_step _ _ _ valid3499 (by decide +kernel)





theorem valid5963 : plan5963.Valid := valid_step _ _ _ valid3502 (by decide +kernel)



theorem valid5965 : plan5965.Valid := valid_step _ _ _ valid3504 (by decide +kernel)

theorem valid5966 : plan5966.Valid := valid_step _ _ _ valid3505 (by decide +kernel)



theorem valid5968 : plan5968.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5969 : plan5969.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5970 : plan5970.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5971 : plan5971.Valid := valid_step _ _ _ valid3510 (by decide +kernel)

theorem valid5972 : plan5972.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5973 : plan5973.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5974 : plan5974.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5975 : plan5975.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5976 : plan5976.Valid := valid_step _ _ _ valid3510 (by decide +kernel)
















































































































































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





































































































theorem valid6867 : plan6867.Valid := valid_step _ _ _ valid5734 (by decide +kernel)

theorem valid6868 : plan6868.Valid := valid_step _ _ _ valid5736 (by decide +kernel)

theorem valid6869 : plan6869.Valid := valid_step _ _ _ valid5737 (by decide +kernel)






















































































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













theorem valid6535 : plan6535.Valid := valid_step _ _ _ valid5534 (by decide +kernel)

theorem valid6536 : plan6536.Valid := valid_step _ _ _ valid5431 (by decide +kernel)

theorem valid6537 : plan6537.Valid := valid_step _ _ _ valid5432 (by decide +kernel)

theorem valid6538 : plan6538.Valid := valid_step _ _ _ valid5433 (by decide +kernel)

theorem valid6539 : plan6539.Valid := valid_step _ _ _ valid5434 (by decide +kernel)

theorem valid6540 : plan6540.Valid := valid_step _ _ _ valid5435 (by decide +kernel)

theorem valid6541 : plan6541.Valid := valid_step _ _ _ valid5436 (by decide +kernel)

theorem valid6542 : plan6542.Valid := valid_step _ _ _ valid5437 (by decide +kernel)

theorem valid6543 : plan6543.Valid := valid_step _ _ _ valid5438 (by decide +kernel)

theorem valid6544 : plan6544.Valid := valid_step _ _ _ valid5439 (by decide +kernel)

theorem valid6545 : plan6545.Valid := valid_step _ _ _ valid5440 (by decide +kernel)

theorem valid6546 : plan6546.Valid := valid_step _ _ _ valid5441 (by decide +kernel)

theorem valid6547 : plan6547.Valid := valid_step _ _ _ valid5442 (by decide +kernel)

theorem valid6548 : plan6548.Valid := valid_step _ _ _ valid5443 (by decide +kernel)
























































































































































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





theorem valid7299 : plan7299.Valid := valid_step _ _ _ valid5943 (by decide +kernel)

theorem valid7300 : plan7300.Valid := valid_step _ _ _ valid5944 (by decide +kernel)

theorem valid7301 : plan7301.Valid := valid_step _ _ _ valid5945 (by decide +kernel)

theorem valid7302 : plan7302.Valid := valid_step _ _ _ valid5946 (by decide +kernel)

theorem valid7303 : plan7303.Valid := valid_step _ _ _ valid5947 (by decide +kernel)

theorem valid7304 : plan7304.Valid := valid_step _ _ _ valid5955 (by decide +kernel)

theorem valid7305 : plan7305.Valid := valid_step _ _ _ valid5957 (by decide +kernel)

theorem valid7306 : plan7306.Valid := valid_step _ _ _ valid5958 (by decide +kernel)

theorem valid7307 : plan7307.Valid := valid_step _ _ _ valid5960 (by decide +kernel)

theorem valid7308 : plan7308.Valid := valid_step _ _ _ valid5963 (by decide +kernel)

theorem valid7309 : plan7309.Valid := valid_step _ _ _ valid5965 (by decide +kernel)

theorem valid7310 : plan7310.Valid := valid_step _ _ _ valid5966 (by decide +kernel)

theorem valid7311 : plan7311.Valid := valid_step _ _ _ valid5968 (by decide +kernel)

theorem valid7312 : plan7312.Valid := valid_step _ _ _ valid5969 (by decide +kernel)

theorem valid7313 : plan7313.Valid := valid_step _ _ _ valid5970 (by decide +kernel)

theorem valid7314 : plan7314.Valid := valid_step _ _ _ valid5971 (by decide +kernel)

theorem valid7315 : plan7315.Valid := valid_step _ _ _ valid5972 (by decide +kernel)

theorem valid7316 : plan7316.Valid := valid_step _ _ _ valid5973 (by decide +kernel)

theorem valid7317 : plan7317.Valid := valid_step _ _ _ valid5974 (by decide +kernel)

theorem valid7318 : plan7318.Valid := valid_step _ _ _ valid5975 (by decide +kernel)

theorem valid7319 : plan7319.Valid := valid_step _ _ _ valid5976 (by decide +kernel)


















































































































































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
theorem t6_487choices : plan7299.choices=[1,9,6,7,7,7].map (options 6 5) := by rfl


theorem t6_487part0 : t6_487jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_487frontier : t6_487root.frontier 0=t6_487jobs := by rfl
theorem t6_487all : t6_487jobs.all (Job.check tree)=true := by
  simp only [t6_487jobs,List.all_append,List.all_nil,t6_487part0,Bool.and_self]
theorem t6_487checked : Checked tree [1,9,6,7,7,7] := by
  refine ⟨plan7299,valid7299,t6_487choices,?_⟩
  exact check_of_frontier tree 0 t6_487root t6_487jobs t6_487frontier t6_487all
theorem t6_488choices : plan7300.choices=[1,9,6,10,7,7].map (options 6 5) := by rfl


theorem t6_488part0 : t6_488jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_488frontier : t6_488root.frontier 0=t6_488jobs := by rfl
theorem t6_488all : t6_488jobs.all (Job.check tree)=true := by
  simp only [t6_488jobs,List.all_append,List.all_nil,t6_488part0,Bool.and_self]
theorem t6_488checked : Checked tree [1,9,6,10,7,7] := by
  refine ⟨plan7300,valid7300,t6_488choices,?_⟩
  exact check_of_frontier tree 0 t6_488root t6_488jobs t6_488frontier t6_488all
theorem t6_489choices : plan7301.choices=[1,9,6,10,10,7].map (options 6 5) := by rfl


theorem t6_489part0 : t6_489jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_489frontier : t6_489root.frontier 0=t6_489jobs := by rfl
theorem t6_489all : t6_489jobs.all (Job.check tree)=true := by
  simp only [t6_489jobs,List.all_append,List.all_nil,t6_489part0,Bool.and_self]
theorem t6_489checked : Checked tree [1,9,6,10,10,7] := by
  refine ⟨plan7301,valid7301,t6_489choices,?_⟩
  exact check_of_frontier tree 0 t6_489root t6_489jobs t6_489frontier t6_489all
theorem t6_490choices : plan7302.choices=[1,9,6,10,10,10].map (options 6 5) := by rfl


theorem t6_490part0 : t6_490jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_490frontier : t6_490root.frontier 0=t6_490jobs := by rfl
theorem t6_490all : t6_490jobs.all (Job.check tree)=true := by
  simp only [t6_490jobs,List.all_append,List.all_nil,t6_490part0,Bool.and_self]
theorem t6_490checked : Checked tree [1,9,6,10,10,10] := by
  refine ⟨plan7302,valid7302,t6_490choices,?_⟩
  exact check_of_frontier tree 0 t6_490root t6_490jobs t6_490frontier t6_490all
theorem t6_491choices : plan7303.choices=[1,9,7,7,7,7].map (options 6 5) := by rfl


theorem t6_491part0 : t6_491jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_491frontier : t6_491root.frontier 0=t6_491jobs := by rfl
theorem t6_491all : t6_491jobs.all (Job.check tree)=true := by
  simp only [t6_491jobs,List.all_append,List.all_nil,t6_491part0,Bool.and_self]
theorem t6_491checked : Checked tree [1,9,7,7,7,7] := by
  refine ⟨plan7303,valid7303,t6_491choices,?_⟩
  exact check_of_frontier tree 0 t6_491root t6_491jobs t6_491frontier t6_491all
theorem t6_492choices : plan6535.choices=[1,9,9,3,3,7].map (options 6 3) := by rfl


theorem t6_492part0 : t6_492jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_492frontier : t6_492root.frontier 0=t6_492jobs := by rfl
theorem t6_492all : t6_492jobs.all (Job.check tree)=true := by
  simp only [t6_492jobs,List.all_append,List.all_nil,t6_492part0,Bool.and_self]
theorem t6_492checked : Checked tree [1,9,9,3,3,7] := by
  refine ⟨plan6535,valid6535,t6_492choices,?_⟩
  exact check_of_frontier tree 0 t6_492root t6_492jobs t6_492frontier t6_492all
theorem t6_493choices : plan6867.choices=[1,9,9,3,6,7].map (options 6 4) := by rfl


theorem t6_493part0 : t6_493jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_493frontier : t6_493root.frontier 0=t6_493jobs := by rfl
theorem t6_493all : t6_493jobs.all (Job.check tree)=true := by
  simp only [t6_493jobs,List.all_append,List.all_nil,t6_493part0,Bool.and_self]
theorem t6_493checked : Checked tree [1,9,9,3,6,7] := by
  refine ⟨plan6867,valid6867,t6_493choices,?_⟩
  exact check_of_frontier tree 0 t6_493root t6_493jobs t6_493frontier t6_493all
theorem t6_494choices : plan6868.choices=[1,9,9,3,7,7].map (options 6 4) := by rfl


theorem t6_494part0 : t6_494jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_494frontier : t6_494root.frontier 0=t6_494jobs := by rfl
theorem t6_494all : t6_494jobs.all (Job.check tree)=true := by
  simp only [t6_494jobs,List.all_append,List.all_nil,t6_494part0,Bool.and_self]
theorem t6_494checked : Checked tree [1,9,9,3,7,7] := by
  refine ⟨plan6868,valid6868,t6_494choices,?_⟩
  exact check_of_frontier tree 0 t6_494root t6_494jobs t6_494frontier t6_494all
theorem t6_495choices : plan6869.choices=[1,9,9,3,10,7].map (options 6 4) := by rfl


theorem t6_495part0 : t6_495jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_495frontier : t6_495root.frontier 0=t6_495jobs := by rfl
theorem t6_495all : t6_495jobs.all (Job.check tree)=true := by
  simp only [t6_495jobs,List.all_append,List.all_nil,t6_495part0,Bool.and_self]
theorem t6_495checked : Checked tree [1,9,9,3,10,7] := by
  refine ⟨plan6869,valid6869,t6_495choices,?_⟩
  exact check_of_frontier tree 0 t6_495root t6_495jobs t6_495frontier t6_495all
theorem t6_496choices : plan7304.choices=[1,9,9,6,6,7].map (options 6 5) := by rfl


theorem t6_496part0 : t6_496jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_496frontier : t6_496root.frontier 0=t6_496jobs := by rfl
theorem t6_496all : t6_496jobs.all (Job.check tree)=true := by
  simp only [t6_496jobs,List.all_append,List.all_nil,t6_496part0,Bool.and_self]
theorem t6_496checked : Checked tree [1,9,9,6,6,7] := by
  refine ⟨plan7304,valid7304,t6_496choices,?_⟩
  exact check_of_frontier tree 0 t6_496root t6_496jobs t6_496frontier t6_496all
theorem t6_497choices : plan7305.choices=[1,9,9,6,7,7].map (options 6 5) := by rfl


theorem t6_497part0 : t6_497jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_497frontier : t6_497root.frontier 0=t6_497jobs := by rfl
theorem t6_497all : t6_497jobs.all (Job.check tree)=true := by
  simp only [t6_497jobs,List.all_append,List.all_nil,t6_497part0,Bool.and_self]
theorem t6_497checked : Checked tree [1,9,9,6,7,7] := by
  refine ⟨plan7305,valid7305,t6_497choices,?_⟩
  exact check_of_frontier tree 0 t6_497root t6_497jobs t6_497frontier t6_497all
theorem t6_498choices : plan7306.choices=[1,9,9,6,10,7].map (options 6 5) := by rfl


theorem t6_498part0 : t6_498jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_498frontier : t6_498root.frontier 0=t6_498jobs := by rfl
theorem t6_498all : t6_498jobs.all (Job.check tree)=true := by
  simp only [t6_498jobs,List.all_append,List.all_nil,t6_498part0,Bool.and_self]
theorem t6_498checked : Checked tree [1,9,9,6,10,7] := by
  refine ⟨plan7306,valid7306,t6_498choices,?_⟩
  exact check_of_frontier tree 0 t6_498root t6_498jobs t6_498frontier t6_498all
theorem t6_499choices : plan7307.choices=[1,9,9,7,7,7].map (options 6 5) := by rfl


theorem t6_499part0 : t6_499jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_499frontier : t6_499root.frontier 0=t6_499jobs := by rfl
theorem t6_499all : t6_499jobs.all (Job.check tree)=true := by
  simp only [t6_499jobs,List.all_append,List.all_nil,t6_499part0,Bool.and_self]
theorem t6_499checked : Checked tree [1,9,9,7,7,7] := by
  refine ⟨plan7307,valid7307,t6_499choices,?_⟩
  exact check_of_frontier tree 0 t6_499root t6_499jobs t6_499frontier t6_499all
theorem t6_500choices : plan7308.choices=[1,9,9,9,7,7].map (options 6 5) := by rfl


theorem t6_500part0 : t6_500jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_500frontier : t6_500root.frontier 0=t6_500jobs := by rfl
theorem t6_500all : t6_500jobs.all (Job.check tree)=true := by
  simp only [t6_500jobs,List.all_append,List.all_nil,t6_500part0,Bool.and_self]
theorem t6_500checked : Checked tree [1,9,9,9,7,7] := by
  refine ⟨plan7308,valid7308,t6_500choices,?_⟩
  exact check_of_frontier tree 0 t6_500root t6_500jobs t6_500frontier t6_500all
theorem t6_501choices : plan7309.choices=[1,9,9,10,7,7].map (options 6 5) := by rfl


theorem t6_501part0 : t6_501jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_501frontier : t6_501root.frontier 0=t6_501jobs := by rfl
theorem t6_501all : t6_501jobs.all (Job.check tree)=true := by
  simp only [t6_501jobs,List.all_append,List.all_nil,t6_501part0,Bool.and_self]
theorem t6_501checked : Checked tree [1,9,9,10,7,7] := by
  refine ⟨plan7309,valid7309,t6_501choices,?_⟩
  exact check_of_frontier tree 0 t6_501root t6_501jobs t6_501frontier t6_501all
theorem t6_502choices : plan7310.choices=[1,9,9,10,10,7].map (options 6 5) := by rfl


theorem t6_502part0 : t6_502jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_502frontier : t6_502root.frontier 0=t6_502jobs := by rfl
theorem t6_502all : t6_502jobs.all (Job.check tree)=true := by
  simp only [t6_502jobs,List.all_append,List.all_nil,t6_502part0,Bool.and_self]
theorem t6_502checked : Checked tree [1,9,9,10,10,7] := by
  refine ⟨plan7310,valid7310,t6_502choices,?_⟩
  exact check_of_frontier tree 0 t6_502root t6_502jobs t6_502frontier t6_502all
theorem t6_503choices : plan7311.choices=[1,9,10,7,7,7].map (options 6 5) := by rfl


theorem t6_503part0 : t6_503jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_503frontier : t6_503root.frontier 0=t6_503jobs := by rfl
theorem t6_503all : t6_503jobs.all (Job.check tree)=true := by
  simp only [t6_503jobs,List.all_append,List.all_nil,t6_503part0,Bool.and_self]
theorem t6_503checked : Checked tree [1,9,10,7,7,7] := by
  refine ⟨plan7311,valid7311,t6_503choices,?_⟩
  exact check_of_frontier tree 0 t6_503root t6_503jobs t6_503frontier t6_503all
theorem t6_504choices : plan7312.choices=[1,9,10,10,7,7].map (options 6 5) := by rfl


theorem t6_504part0 : t6_504jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_504frontier : t6_504root.frontier 0=t6_504jobs := by rfl
theorem t6_504all : t6_504jobs.all (Job.check tree)=true := by
  simp only [t6_504jobs,List.all_append,List.all_nil,t6_504part0,Bool.and_self]
theorem t6_504checked : Checked tree [1,9,10,10,7,7] := by
  refine ⟨plan7312,valid7312,t6_504choices,?_⟩
  exact check_of_frontier tree 0 t6_504root t6_504jobs t6_504frontier t6_504all
theorem t6_505choices : plan7313.choices=[1,9,10,10,10,7].map (options 6 5) := by rfl


theorem t6_505part0 : t6_505jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_505frontier : t6_505root.frontier 0=t6_505jobs := by rfl
theorem t6_505all : t6_505jobs.all (Job.check tree)=true := by
  simp only [t6_505jobs,List.all_append,List.all_nil,t6_505part0,Bool.and_self]
theorem t6_505checked : Checked tree [1,9,10,10,10,7] := by
  refine ⟨plan7313,valid7313,t6_505choices,?_⟩
  exact check_of_frontier tree 0 t6_505root t6_505jobs t6_505frontier t6_505all
theorem t6_506choices : plan7314.choices=[1,9,10,10,10,10].map (options 6 5) := by rfl


theorem t6_506part0 : t6_506jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_506frontier : t6_506root.frontier 0=t6_506jobs := by rfl
theorem t6_506all : t6_506jobs.all (Job.check tree)=true := by
  simp only [t6_506jobs,List.all_append,List.all_nil,t6_506part0,Bool.and_self]
theorem t6_506checked : Checked tree [1,9,10,10,10,10] := by
  refine ⟨plan7314,valid7314,t6_506choices,?_⟩
  exact check_of_frontier tree 0 t6_506root t6_506jobs t6_506frontier t6_506all
theorem t6_507choices : plan7315.choices=[1,10,7,7,7,7].map (options 6 5) := by rfl


theorem t6_507part0 : t6_507jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_507frontier : t6_507root.frontier 0=t6_507jobs := by rfl
theorem t6_507all : t6_507jobs.all (Job.check tree)=true := by
  simp only [t6_507jobs,List.all_append,List.all_nil,t6_507part0,Bool.and_self]
theorem t6_507checked : Checked tree [1,10,7,7,7,7] := by
  refine ⟨plan7315,valid7315,t6_507choices,?_⟩
  exact check_of_frontier tree 0 t6_507root t6_507jobs t6_507frontier t6_507all
theorem t6_508choices : plan7316.choices=[1,10,10,7,7,7].map (options 6 5) := by rfl


theorem t6_508part0 : t6_508jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_508frontier : t6_508root.frontier 0=t6_508jobs := by rfl
theorem t6_508all : t6_508jobs.all (Job.check tree)=true := by
  simp only [t6_508jobs,List.all_append,List.all_nil,t6_508part0,Bool.and_self]
theorem t6_508checked : Checked tree [1,10,10,7,7,7] := by
  refine ⟨plan7316,valid7316,t6_508choices,?_⟩
  exact check_of_frontier tree 0 t6_508root t6_508jobs t6_508frontier t6_508all
theorem t6_509choices : plan7317.choices=[1,10,10,10,7,7].map (options 6 5) := by rfl


theorem t6_509part0 : t6_509jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_509frontier : t6_509root.frontier 0=t6_509jobs := by rfl
theorem t6_509all : t6_509jobs.all (Job.check tree)=true := by
  simp only [t6_509jobs,List.all_append,List.all_nil,t6_509part0,Bool.and_self]
theorem t6_509checked : Checked tree [1,10,10,10,7,7] := by
  refine ⟨plan7317,valid7317,t6_509choices,?_⟩
  exact check_of_frontier tree 0 t6_509root t6_509jobs t6_509frontier t6_509all
theorem t6_510choices : plan7318.choices=[1,10,10,10,10,7].map (options 6 5) := by rfl


theorem t6_510part0 : t6_510jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_510frontier : t6_510root.frontier 0=t6_510jobs := by rfl
theorem t6_510all : t6_510jobs.all (Job.check tree)=true := by
  simp only [t6_510jobs,List.all_append,List.all_nil,t6_510part0,Bool.and_self]
theorem t6_510checked : Checked tree [1,10,10,10,10,7] := by
  refine ⟨plan7318,valid7318,t6_510choices,?_⟩
  exact check_of_frontier tree 0 t6_510root t6_510jobs t6_510frontier t6_510all
theorem t6_511choices : plan7319.choices=[1,10,10,10,10,10].map (options 6 5) := by rfl


theorem t6_511part0 : t6_511jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_511frontier : t6_511root.frontier 0=t6_511jobs := by rfl
theorem t6_511all : t6_511jobs.all (Job.check tree)=true := by
  simp only [t6_511jobs,List.all_append,List.all_nil,t6_511part0,Bool.and_self]
theorem t6_511checked : Checked tree [1,10,10,10,10,10] := by
  refine ⟨plan7319,valid7319,t6_511choices,?_⟩
  exact check_of_frontier tree 0 t6_511root t6_511jobs t6_511frontier t6_511all
theorem t6_512choices : plan6297.choices=[2,2,2,2,3,7].map (options 6 1) := by rfl


theorem t6_512part0 : t6_512jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_512frontier : t6_512root.frontier 0=t6_512jobs := by rfl
theorem t6_512all : t6_512jobs.all (Job.check tree)=true := by
  simp only [t6_512jobs,List.all_append,List.all_nil,t6_512part0,Bool.and_self]
theorem t6_512checked : Checked tree [2,2,2,2,3,7] := by
  refine ⟨plan6297,valid6297,t6_512choices,?_⟩
  exact check_of_frontier tree 0 t6_512root t6_512jobs t6_512frontier t6_512all
theorem t6_513choices : plan6363.choices=[2,2,2,2,6,7].map (options 6 2) := by rfl


theorem t6_513part0 : t6_513jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_513frontier : t6_513root.frontier 0=t6_513jobs := by rfl
theorem t6_513all : t6_513jobs.all (Job.check tree)=true := by
  simp only [t6_513jobs,List.all_append,List.all_nil,t6_513part0,Bool.and_self]
theorem t6_513checked : Checked tree [2,2,2,2,6,7] := by
  refine ⟨plan6363,valid6363,t6_513choices,?_⟩
  exact check_of_frontier tree 0 t6_513root t6_513jobs t6_513frontier t6_513all
theorem t6_514choices : plan6364.choices=[2,2,2,2,7,7].map (options 6 2) := by rfl


theorem t6_514part0 : t6_514jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_514frontier : t6_514root.frontier 0=t6_514jobs := by rfl
theorem t6_514all : t6_514jobs.all (Job.check tree)=true := by
  simp only [t6_514jobs,List.all_append,List.all_nil,t6_514part0,Bool.and_self]
theorem t6_514checked : Checked tree [2,2,2,2,7,7] := by
  refine ⟨plan6364,valid6364,t6_514choices,?_⟩
  exact check_of_frontier tree 0 t6_514root t6_514jobs t6_514frontier t6_514all
theorem t6_515choices : plan6365.choices=[2,2,2,2,10,7].map (options 6 2) := by rfl


theorem t6_515part0 : t6_515jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_515frontier : t6_515root.frontier 0=t6_515jobs := by rfl
theorem t6_515all : t6_515jobs.all (Job.check tree)=true := by
  simp only [t6_515jobs,List.all_append,List.all_nil,t6_515part0,Bool.and_self]
theorem t6_515checked : Checked tree [2,2,2,2,10,7] := by
  refine ⟨plan6365,valid6365,t6_515choices,?_⟩
  exact check_of_frontier tree 0 t6_515root t6_515jobs t6_515frontier t6_515all
theorem t6_516choices : plan6279.choices=[2,2,2,3,3,3].map (options 6 0) := by rfl


theorem t6_516part0 : t6_516jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_516frontier : t6_516root.frontier 0=t6_516jobs := by rfl
theorem t6_516all : t6_516jobs.all (Job.check tree)=true := by
  simp only [t6_516jobs,List.all_append,List.all_nil,t6_516part0,Bool.and_self]
theorem t6_516checked : Checked tree [2,2,2,3,3,3] := by
  refine ⟨plan6279,valid6279,t6_516choices,?_⟩
  exact check_of_frontier tree 0 t6_516root t6_516jobs t6_516frontier t6_516all
theorem t6_517choices : plan6298.choices=[2,2,2,3,3,6].map (options 6 1) := by rfl


theorem t6_517part0 : t6_517jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_517frontier : t6_517root.frontier 0=t6_517jobs := by rfl
theorem t6_517all : t6_517jobs.all (Job.check tree)=true := by
  simp only [t6_517jobs,List.all_append,List.all_nil,t6_517part0,Bool.and_self]
theorem t6_517checked : Checked tree [2,2,2,3,3,6] := by
  refine ⟨plan6298,valid6298,t6_517choices,?_⟩
  exact check_of_frontier tree 0 t6_517root t6_517jobs t6_517frontier t6_517all
theorem t6_518choices : plan6299.choices=[2,2,2,3,3,7].map (options 6 1) := by rfl


theorem t6_518part0 : t6_518jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_518frontier : t6_518root.frontier 0=t6_518jobs := by rfl
theorem t6_518all : t6_518jobs.all (Job.check tree)=true := by
  simp only [t6_518jobs,List.all_append,List.all_nil,t6_518part0,Bool.and_self]
theorem t6_518checked : Checked tree [2,2,2,3,3,7] := by
  refine ⟨plan6299,valid6299,t6_518choices,?_⟩
  exact check_of_frontier tree 0 t6_518root t6_518jobs t6_518frontier t6_518all
theorem t6_519choices : plan6300.choices=[2,2,2,3,3,10].map (options 6 1) := by rfl


theorem t6_519part0 : t6_519jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_519frontier : t6_519root.frontier 0=t6_519jobs := by rfl
theorem t6_519all : t6_519jobs.all (Job.check tree)=true := by
  simp only [t6_519jobs,List.all_append,List.all_nil,t6_519part0,Bool.and_self]
theorem t6_519checked : Checked tree [2,2,2,3,3,10] := by
  refine ⟨plan6300,valid6300,t6_519choices,?_⟩
  exact check_of_frontier tree 0 t6_519root t6_519jobs t6_519frontier t6_519all
theorem t6_520choices : plan6366.choices=[2,2,2,3,6,6].map (options 6 2) := by rfl


theorem t6_520part0 : t6_520jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_520frontier : t6_520root.frontier 0=t6_520jobs := by rfl
theorem t6_520all : t6_520jobs.all (Job.check tree)=true := by
  simp only [t6_520jobs,List.all_append,List.all_nil,t6_520part0,Bool.and_self]
theorem t6_520checked : Checked tree [2,2,2,3,6,6] := by
  refine ⟨plan6366,valid6366,t6_520choices,?_⟩
  exact check_of_frontier tree 0 t6_520root t6_520jobs t6_520frontier t6_520all
theorem t6_521choices : plan6367.choices=[2,2,2,3,6,7].map (options 6 2) := by rfl


theorem t6_521part0 : t6_521jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_521frontier : t6_521root.frontier 0=t6_521jobs := by rfl
theorem t6_521all : t6_521jobs.all (Job.check tree)=true := by
  simp only [t6_521jobs,List.all_append,List.all_nil,t6_521part0,Bool.and_self]
theorem t6_521checked : Checked tree [2,2,2,3,6,7] := by
  refine ⟨plan6367,valid6367,t6_521choices,?_⟩
  exact check_of_frontier tree 0 t6_521root t6_521jobs t6_521frontier t6_521all
theorem t6_522choices : plan6368.choices=[2,2,2,3,6,10].map (options 6 2) := by rfl


theorem t6_522part0 : t6_522jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_522frontier : t6_522root.frontier 0=t6_522jobs := by rfl
theorem t6_522all : t6_522jobs.all (Job.check tree)=true := by
  simp only [t6_522jobs,List.all_append,List.all_nil,t6_522part0,Bool.and_self]
theorem t6_522checked : Checked tree [2,2,2,3,6,10] := by
  refine ⟨plan6368,valid6368,t6_522choices,?_⟩
  exact check_of_frontier tree 0 t6_522root t6_522jobs t6_522frontier t6_522all
theorem t6_523choices : plan6369.choices=[2,2,2,3,7,7].map (options 6 2) := by rfl


theorem t6_523part0 : t6_523jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_523frontier : t6_523root.frontier 0=t6_523jobs := by rfl
theorem t6_523all : t6_523jobs.all (Job.check tree)=true := by
  simp only [t6_523jobs,List.all_append,List.all_nil,t6_523part0,Bool.and_self]
theorem t6_523checked : Checked tree [2,2,2,3,7,7] := by
  refine ⟨plan6369,valid6369,t6_523choices,?_⟩
  exact check_of_frontier tree 0 t6_523root t6_523jobs t6_523frontier t6_523all
theorem t6_524choices : plan6370.choices=[2,2,2,3,10,7].map (options 6 2) := by rfl


theorem t6_524part0 : t6_524jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_524frontier : t6_524root.frontier 0=t6_524jobs := by rfl
theorem t6_524all : t6_524jobs.all (Job.check tree)=true := by
  simp only [t6_524jobs,List.all_append,List.all_nil,t6_524part0,Bool.and_self]
theorem t6_524checked : Checked tree [2,2,2,3,10,7] := by
  refine ⟨plan6370,valid6370,t6_524choices,?_⟩
  exact check_of_frontier tree 0 t6_524root t6_524jobs t6_524frontier t6_524all
theorem t6_525choices : plan6371.choices=[2,2,2,3,10,10].map (options 6 2) := by rfl


theorem t6_525part0 : t6_525jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_525frontier : t6_525root.frontier 0=t6_525jobs := by rfl
theorem t6_525all : t6_525jobs.all (Job.check tree)=true := by
  simp only [t6_525jobs,List.all_append,List.all_nil,t6_525part0,Bool.and_self]
theorem t6_525checked : Checked tree [2,2,2,3,10,10] := by
  refine ⟨plan6371,valid6371,t6_525choices,?_⟩
  exact check_of_frontier tree 0 t6_525root t6_525jobs t6_525frontier t6_525all
theorem t6_526choices : plan6372.choices=[2,2,2,5,3,7].map (options 6 2) := by rfl


theorem t6_526part0 : t6_526jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_526frontier : t6_526root.frontier 0=t6_526jobs := by rfl
theorem t6_526all : t6_526jobs.all (Job.check tree)=true := by
  simp only [t6_526jobs,List.all_append,List.all_nil,t6_526part0,Bool.and_self]
theorem t6_526checked : Checked tree [2,2,2,5,3,7] := by
  refine ⟨plan6372,valid6372,t6_526choices,?_⟩
  exact check_of_frontier tree 0 t6_526root t6_526jobs t6_526frontier t6_526all
theorem t6_527choices : plan6536.choices=[2,2,2,5,6,7].map (options 6 3) := by rfl


theorem t6_527part0 : t6_527jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_527frontier : t6_527root.frontier 0=t6_527jobs := by rfl
theorem t6_527all : t6_527jobs.all (Job.check tree)=true := by
  simp only [t6_527jobs,List.all_append,List.all_nil,t6_527part0,Bool.and_self]
theorem t6_527checked : Checked tree [2,2,2,5,6,7] := by
  refine ⟨plan6536,valid6536,t6_527choices,?_⟩
  exact check_of_frontier tree 0 t6_527root t6_527jobs t6_527frontier t6_527all
theorem t6_528choices : plan6537.choices=[2,2,2,5,7,7].map (options 6 3) := by rfl


theorem t6_528part0 : t6_528jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_528frontier : t6_528root.frontier 0=t6_528jobs := by rfl
theorem t6_528all : t6_528jobs.all (Job.check tree)=true := by
  simp only [t6_528jobs,List.all_append,List.all_nil,t6_528part0,Bool.and_self]
theorem t6_528checked : Checked tree [2,2,2,5,7,7] := by
  refine ⟨plan6537,valid6537,t6_528choices,?_⟩
  exact check_of_frontier tree 0 t6_528root t6_528jobs t6_528frontier t6_528all
theorem t6_529choices : plan6538.choices=[2,2,2,5,10,7].map (options 6 3) := by rfl


theorem t6_529part0 : t6_529jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_529frontier : t6_529root.frontier 0=t6_529jobs := by rfl
theorem t6_529all : t6_529jobs.all (Job.check tree)=true := by
  simp only [t6_529jobs,List.all_append,List.all_nil,t6_529part0,Bool.and_self]
theorem t6_529checked : Checked tree [2,2,2,5,10,7] := by
  refine ⟨plan6538,valid6538,t6_529choices,?_⟩
  exact check_of_frontier tree 0 t6_529root t6_529jobs t6_529frontier t6_529all
theorem t6_530choices : plan6539.choices=[2,2,2,6,6,6].map (options 6 3) := by rfl


theorem t6_530part0 : t6_530jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_530frontier : t6_530root.frontier 0=t6_530jobs := by rfl
theorem t6_530all : t6_530jobs.all (Job.check tree)=true := by
  simp only [t6_530jobs,List.all_append,List.all_nil,t6_530part0,Bool.and_self]
theorem t6_530checked : Checked tree [2,2,2,6,6,6] := by
  refine ⟨plan6539,valid6539,t6_530choices,?_⟩
  exact check_of_frontier tree 0 t6_530root t6_530jobs t6_530frontier t6_530all
theorem t6_531choices : plan6540.choices=[2,2,2,6,6,7].map (options 6 3) := by rfl


theorem t6_531part0 : t6_531jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_531frontier : t6_531root.frontier 0=t6_531jobs := by rfl
theorem t6_531all : t6_531jobs.all (Job.check tree)=true := by
  simp only [t6_531jobs,List.all_append,List.all_nil,t6_531part0,Bool.and_self]
theorem t6_531checked : Checked tree [2,2,2,6,6,7] := by
  refine ⟨plan6540,valid6540,t6_531choices,?_⟩
  exact check_of_frontier tree 0 t6_531root t6_531jobs t6_531frontier t6_531all
theorem t6_532choices : plan6541.choices=[2,2,2,6,6,10].map (options 6 3) := by rfl


theorem t6_532part0 : t6_532jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_532frontier : t6_532root.frontier 0=t6_532jobs := by rfl
theorem t6_532all : t6_532jobs.all (Job.check tree)=true := by
  simp only [t6_532jobs,List.all_append,List.all_nil,t6_532part0,Bool.and_self]
theorem t6_532checked : Checked tree [2,2,2,6,6,10] := by
  refine ⟨plan6541,valid6541,t6_532choices,?_⟩
  exact check_of_frontier tree 0 t6_532root t6_532jobs t6_532frontier t6_532all
theorem t6_533choices : plan6542.choices=[2,2,2,6,7,7].map (options 6 3) := by rfl


theorem t6_533part0 : t6_533jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_533frontier : t6_533root.frontier 0=t6_533jobs := by rfl
theorem t6_533all : t6_533jobs.all (Job.check tree)=true := by
  simp only [t6_533jobs,List.all_append,List.all_nil,t6_533part0,Bool.and_self]
theorem t6_533checked : Checked tree [2,2,2,6,7,7] := by
  refine ⟨plan6542,valid6542,t6_533choices,?_⟩
  exact check_of_frontier tree 0 t6_533root t6_533jobs t6_533frontier t6_533all
theorem t6_534choices : plan6543.choices=[2,2,2,6,10,7].map (options 6 3) := by rfl


theorem t6_534part0 : t6_534jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_534frontier : t6_534root.frontier 0=t6_534jobs := by rfl
theorem t6_534all : t6_534jobs.all (Job.check tree)=true := by
  simp only [t6_534jobs,List.all_append,List.all_nil,t6_534part0,Bool.and_self]
theorem t6_534checked : Checked tree [2,2,2,6,10,7] := by
  refine ⟨plan6543,valid6543,t6_534choices,?_⟩
  exact check_of_frontier tree 0 t6_534root t6_534jobs t6_534frontier t6_534all
theorem t6_535choices : plan6544.choices=[2,2,2,6,10,10].map (options 6 3) := by rfl


theorem t6_535part0 : t6_535jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_535frontier : t6_535root.frontier 0=t6_535jobs := by rfl
theorem t6_535all : t6_535jobs.all (Job.check tree)=true := by
  simp only [t6_535jobs,List.all_append,List.all_nil,t6_535part0,Bool.and_self]
theorem t6_535checked : Checked tree [2,2,2,6,10,10] := by
  refine ⟨plan6544,valid6544,t6_535choices,?_⟩
  exact check_of_frontier tree 0 t6_535root t6_535jobs t6_535frontier t6_535all
theorem t6_536choices : plan6545.choices=[2,2,2,7,7,7].map (options 6 3) := by rfl


theorem t6_536part0 : t6_536jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_536frontier : t6_536root.frontier 0=t6_536jobs := by rfl
theorem t6_536all : t6_536jobs.all (Job.check tree)=true := by
  simp only [t6_536jobs,List.all_append,List.all_nil,t6_536part0,Bool.and_self]
theorem t6_536checked : Checked tree [2,2,2,7,7,7] := by
  refine ⟨plan6545,valid6545,t6_536choices,?_⟩
  exact check_of_frontier tree 0 t6_536root t6_536jobs t6_536frontier t6_536all
theorem t6_537choices : plan6373.choices=[2,2,2,9,3,7].map (options 6 2) := by rfl


theorem t6_537part0 : t6_537jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_537frontier : t6_537root.frontier 0=t6_537jobs := by rfl
theorem t6_537all : t6_537jobs.all (Job.check tree)=true := by
  simp only [t6_537jobs,List.all_append,List.all_nil,t6_537part0,Bool.and_self]
theorem t6_537checked : Checked tree [2,2,2,9,3,7] := by
  refine ⟨plan6373,valid6373,t6_537choices,?_⟩
  exact check_of_frontier tree 0 t6_537root t6_537jobs t6_537frontier t6_537all
theorem t6_538choices : plan6546.choices=[2,2,2,9,6,7].map (options 6 3) := by rfl


theorem t6_538part0 : t6_538jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_538frontier : t6_538root.frontier 0=t6_538jobs := by rfl
theorem t6_538all : t6_538jobs.all (Job.check tree)=true := by
  simp only [t6_538jobs,List.all_append,List.all_nil,t6_538part0,Bool.and_self]
theorem t6_538checked : Checked tree [2,2,2,9,6,7] := by
  refine ⟨plan6546,valid6546,t6_538choices,?_⟩
  exact check_of_frontier tree 0 t6_538root t6_538jobs t6_538frontier t6_538all
theorem t6_539choices : plan6547.choices=[2,2,2,9,7,7].map (options 6 3) := by rfl


theorem t6_539part0 : t6_539jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_539frontier : t6_539root.frontier 0=t6_539jobs := by rfl
theorem t6_539all : t6_539jobs.all (Job.check tree)=true := by
  simp only [t6_539jobs,List.all_append,List.all_nil,t6_539part0,Bool.and_self]
theorem t6_539checked : Checked tree [2,2,2,9,7,7] := by
  refine ⟨plan6547,valid6547,t6_539choices,?_⟩
  exact check_of_frontier tree 0 t6_539root t6_539jobs t6_539frontier t6_539all
theorem t6_540choices : plan6548.choices=[2,2,2,9,10,7].map (options 6 3) := by rfl


theorem t6_540part0 : t6_540jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_540frontier : t6_540root.frontier 0=t6_540jobs := by rfl
theorem t6_540all : t6_540jobs.all (Job.check tree)=true := by
  simp only [t6_540jobs,List.all_append,List.all_nil,t6_540part0,Bool.and_self]
theorem t6_540checked : Checked tree [2,2,2,9,10,7] := by
  refine ⟨plan6548,valid6548,t6_540choices,?_⟩
  exact check_of_frontier tree 0 t6_540root t6_540jobs t6_540frontier t6_540all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks061 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_487checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_500checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_501checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_502checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_503checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_504checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_505checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_506checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_507checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_508checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_509checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_488checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_510checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_511checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_512checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_513checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_514checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_515checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_516checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_517checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_518checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_519checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_489checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_520checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_521checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_522checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_523checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_524checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_525checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_526checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_527checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_528checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_529checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_490checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_530checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_531checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_532checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_533checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_534checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_535checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_536checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_537checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_538checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_539checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_491checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_540checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_492checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_493checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_494checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_495checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_496checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_497checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_498checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_499checked⟩
