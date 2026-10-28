-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks006
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:15:51.535088+00:00
-- url     : https://prove2.me/submissions/a595993f-cbae-46dc-8bdd-fb0c5e3a2dfe

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans042
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans047
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













































































































































































theorem valid87 : plan87.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid88 : plan88.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid90 : plan90.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid91 : plan91.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid93 : plan93.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid94 : plan94.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid96 : plan96.Valid := valid_step _ _ _ valid0 (by decide +kernel)
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

theorem valid97 : plan97.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid99 : plan99.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid102 : plan102.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid105 : plan105.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid108 : plan108.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid109 : plan109.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid111 : plan111.Valid := valid_step _ _ _ valid0 (by decide +kernel)


































































































































































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



























































































































theorem valid446 : plan446.Valid := valid_step _ _ _ valid87 (by decide +kernel)













theorem valid453 : plan453.Valid := valid_step _ _ _ valid88 (by decide +kernel)

theorem valid454 : plan454.Valid := valid_step _ _ _ valid90 (by decide +kernel)

theorem valid455 : plan455.Valid := valid_step _ _ _ valid91 (by decide +kernel)

theorem valid456 : plan456.Valid := valid_step _ _ _ valid93 (by decide +kernel)











theorem valid462 : plan462.Valid := valid_step _ _ _ valid94 (by decide +kernel)

theorem valid463 : plan463.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid464 : plan464.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid465 : plan465.Valid := valid_step _ _ _ valid99 (by decide +kernel)













theorem valid472 : plan472.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid473 : plan473.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid474 : plan474.Valid := valid_step _ _ _ valid99 (by decide +kernel)

theorem valid475 : plan475.Valid := valid_step _ _ _ valid97 (by decide +kernel)










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

theorem valid481 : plan481.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid482 : plan482.Valid := valid_step _ _ _ valid99 (by decide +kernel)





theorem valid485 : plan485.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid486 : plan486.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid487 : plan487.Valid := valid_step _ _ _ valid105 (by decide +kernel)







theorem valid491 : plan491.Valid := valid_step _ _ _ valid103 (by decide +kernel)





theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)





theorem valid500 : plan500.Valid := valid_step _ _ _ valid103 (by decide +kernel)





theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)













theorem valid511 : plan511.Valid := valid_step _ _ _ valid109 (by decide +kernel)





theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)





theorem valid520 : plan520.Valid := valid_step _ _ _ valid109 (by decide +kernel)





theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid524 : plan524.Valid := valid_step _ _ _ valid111 (by decide +kernel)








































































































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



theorem valid1250 : plan1250.Valid := valid_step _ _ _ valid446 (by decide +kernel)



























theorem valid1264 : plan1264.Valid := valid_step _ _ _ valid453 (by decide +kernel)

theorem valid1265 : plan1265.Valid := valid_step _ _ _ valid454 (by decide +kernel)

theorem valid1266 : plan1266.Valid := valid_step _ _ _ valid455 (by decide +kernel)

theorem valid1267 : plan1267.Valid := valid_step _ _ _ valid456 (by decide +kernel)

theorem valid1268 : plan1268.Valid := valid_step _ _ _ valid453 (by decide +kernel)

theorem valid1269 : plan1269.Valid := valid_step _ _ _ valid453 (by decide +kernel)

















theorem valid1278 : plan1278.Valid := valid_step _ _ _ valid464 (by decide +kernel)







































theorem valid1298 : plan1298.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1299 : plan1299.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1300 : plan1300.Valid := valid_step _ _ _ valid465 (by decide +kernel)

theorem valid1301 : plan1301.Valid := valid_step _ _ _ valid472 (by decide +kernel)

theorem valid1302 : plan1302.Valid := valid_step _ _ _ valid473 (by decide +kernel)

theorem valid1303 : plan1303.Valid := valid_step _ _ _ valid474 (by decide +kernel)

theorem valid1304 : plan1304.Valid := valid_step _ _ _ valid475 (by decide +kernel)

theorem valid1305 : plan1305.Valid := valid_step _ _ _ valid481 (by decide +kernel)

theorem valid1306 : plan1306.Valid := valid_step _ _ _ valid482 (by decide +kernel)



theorem valid1308 : plan1308.Valid := valid_step _ _ _ valid462 (by decide +kernel)

theorem valid1309 : plan1309.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1310 : plan1310.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1311 : plan1311.Valid := valid_step _ _ _ valid465 (by decide +kernel)







theorem valid1315 : plan1315.Valid := valid_step _ _ _ valid462 (by decide +kernel)

theorem valid1316 : plan1316.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1317 : plan1317.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1318 : plan1318.Valid := valid_step _ _ _ valid465 (by decide +kernel)



















theorem valid1328 : plan1328.Valid := valid_step _ _ _ valid495 (by decide +kernel)



theorem valid1330 : plan1330.Valid := valid_step _ _ _ valid497 (by decide +kernel)







theorem valid1334 : plan1334.Valid := valid_step _ _ _ valid503 (by decide +kernel)









theorem valid1339 : plan1339.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1340 : plan1340.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1341 : plan1341.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1342 : plan1342.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1343 : plan1343.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1344 : plan1344.Valid := valid_step _ _ _ valid504 (by decide +kernel)
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















































theorem valid2520 : plan2520.Valid := valid_step _ _ _ valid1250 (by decide +kernel)





















































theorem valid2547 : plan2547.Valid := valid_step _ _ _ valid1268 (by decide +kernel)

theorem valid2548 : plan2548.Valid := valid_step _ _ _ valid1269 (by decide +kernel)



theorem valid2550 : plan2550.Valid := valid_step _ _ _ valid1265 (by decide +kernel)

theorem valid2551 : plan2551.Valid := valid_step _ _ _ valid1266 (by decide +kernel)

theorem valid2552 : plan2552.Valid := valid_step _ _ _ valid1267 (by decide +kernel)



theorem valid2554 : plan2554.Valid := valid_step _ _ _ valid1264 (by decide +kernel)

theorem valid2555 : plan2555.Valid := valid_step _ _ _ valid1264 (by decide +kernel)



theorem valid2557 : plan2557.Valid := valid_step _ _ _ valid1264 (by decide +kernel)

theorem valid2558 : plan2558.Valid := valid_step _ _ _ valid1264 (by decide +kernel)




































































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

























theorem valid3661 : plan3661.Valid := valid_step _ _ _ valid2520 (by decide +kernel)















































theorem valid3685 : plan3685.Valid := valid_step _ _ _ valid2547 (by decide +kernel)

theorem valid3686 : plan3686.Valid := valid_step _ _ _ valid2548 (by decide +kernel)

theorem valid3687 : plan3687.Valid := valid_step _ _ _ valid2550 (by decide +kernel)

theorem valid3688 : plan3688.Valid := valid_step _ _ _ valid2551 (by decide +kernel)

theorem valid3689 : plan3689.Valid := valid_step _ _ _ valid2552 (by decide +kernel)

theorem valid3690 : plan3690.Valid := valid_step _ _ _ valid2554 (by decide +kernel)

theorem valid3691 : plan3691.Valid := valid_step _ _ _ valid2555 (by decide +kernel)

theorem valid3692 : plan3692.Valid := valid_step _ _ _ valid2557 (by decide +kernel)

theorem valid3693 : plan3693.Valid := valid_step _ _ _ valid2558 (by decide +kernel)






































































































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











theorem valid1350 : plan1350.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1351 : plan1351.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1352 : plan1352.Valid := valid_step _ _ _ valid487 (by decide +kernel)







theorem valid1356 : plan1356.Valid := valid_step _ _ _ valid491 (by decide +kernel)





theorem valid1359 : plan1359.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1360 : plan1360.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1361 : plan1361.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1362 : plan1362.Valid := valid_step _ _ _ valid497 (by decide +kernel)





theorem valid1365 : plan1365.Valid := valid_step _ _ _ valid500 (by decide +kernel)





theorem valid1368 : plan1368.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1369 : plan1369.Valid := valid_step _ _ _ valid504 (by decide +kernel)

theorem valid1370 : plan1370.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1371 : plan1371.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1372 : plan1372.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1373 : plan1373.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1374 : plan1374.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1375 : plan1375.Valid := valid_step _ _ _ valid504 (by decide +kernel)

theorem valid1376 : plan1376.Valid := valid_step _ _ _ valid497 (by decide +kernel)











theorem valid1382 : plan1382.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1383 : plan1383.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1384 : plan1384.Valid := valid_step _ _ _ valid487 (by decide +kernel)

theorem valid1385 : plan1385.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1386 : plan1386.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1387 : plan1387.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1388 : plan1388.Valid := valid_step _ _ _ valid497 (by decide +kernel)





theorem valid1391 : plan1391.Valid := valid_step _ _ _ valid500 (by decide +kernel)





theorem valid1394 : plan1394.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1395 : plan1395.Valid := valid_step _ _ _ valid504 (by decide +kernel)

theorem valid1396 : plan1396.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1397 : plan1397.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1398 : plan1398.Valid := valid_step _ _ _ valid504 (by decide +kernel)

















































theorem valid1423 : plan1423.Valid := valid_step _ _ _ valid511 (by decide +kernel)





theorem valid1426 : plan1426.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1427 : plan1427.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1428 : plan1428.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1429 : plan1429.Valid := valid_step _ _ _ valid517 (by decide +kernel)





theorem valid1432 : plan1432.Valid := valid_step _ _ _ valid520 (by decide +kernel)





theorem valid1435 : plan1435.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1436 : plan1436.Valid := valid_step _ _ _ valid524 (by decide +kernel)

theorem valid1437 : plan1437.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1438 : plan1438.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1439 : plan1439.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1440 : plan1440.Valid := valid_step _ _ _ valid517 (by decide +kernel)
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









































theorem valid2613 : plan2613.Valid := valid_step _ _ _ valid1304 (by decide +kernel)

theorem valid2614 : plan2614.Valid := valid_step _ _ _ valid1305 (by decide +kernel)

theorem valid2615 : plan2615.Valid := valid_step _ _ _ valid1306 (by decide +kernel)



theorem valid2617 : plan2617.Valid := valid_step _ _ _ valid1309 (by decide +kernel)

theorem valid2618 : plan2618.Valid := valid_step _ _ _ valid1310 (by decide +kernel)

theorem valid2619 : plan2619.Valid := valid_step _ _ _ valid1311 (by decide +kernel)







theorem valid2623 : plan2623.Valid := valid_step _ _ _ valid1316 (by decide +kernel)

theorem valid2624 : plan2624.Valid := valid_step _ _ _ valid1317 (by decide +kernel)

theorem valid2625 : plan2625.Valid := valid_step _ _ _ valid1318 (by decide +kernel)









theorem valid2630 : plan2630.Valid := valid_step _ _ _ valid1301 (by decide +kernel)

theorem valid2631 : plan2631.Valid := valid_step _ _ _ valid1302 (by decide +kernel)

theorem valid2632 : plan2632.Valid := valid_step _ _ _ valid1303 (by decide +kernel)

theorem valid2633 : plan2633.Valid := valid_step _ _ _ valid1304 (by decide +kernel)

theorem valid2634 : plan2634.Valid := valid_step _ _ _ valid1305 (by decide +kernel)

theorem valid2635 : plan2635.Valid := valid_step _ _ _ valid1306 (by decide +kernel)







theorem valid2639 : plan2639.Valid := valid_step _ _ _ valid1278 (by decide +kernel)





theorem valid2642 : plan2642.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2643 : plan2643.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2644 : plan2644.Valid := valid_step _ _ _ valid1300 (by decide +kernel)







theorem valid2648 : plan2648.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2649 : plan2649.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2650 : plan2650.Valid := valid_step _ _ _ valid1300 (by decide +kernel)

theorem valid2651 : plan2651.Valid := valid_step _ _ _ valid1308 (by decide +kernel)

theorem valid2652 : plan2652.Valid := valid_step _ _ _ valid1315 (by decide +kernel)







theorem valid2656 : plan2656.Valid := valid_step _ _ _ valid1278 (by decide +kernel)





theorem valid2659 : plan2659.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2660 : plan2660.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2661 : plan2661.Valid := valid_step _ _ _ valid1300 (by decide +kernel)







theorem valid2665 : plan2665.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2666 : plan2666.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2667 : plan2667.Valid := valid_step _ _ _ valid1300 (by decide +kernel)










































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









































































theorem valid3781 : plan3781.Valid := valid_step _ _ _ valid2613 (by decide +kernel)

theorem valid3782 : plan3782.Valid := valid_step _ _ _ valid2614 (by decide +kernel)

theorem valid3783 : plan3783.Valid := valid_step _ _ _ valid2615 (by decide +kernel)

theorem valid3784 : plan3784.Valid := valid_step _ _ _ valid2617 (by decide +kernel)

theorem valid3785 : plan3785.Valid := valid_step _ _ _ valid2618 (by decide +kernel)

theorem valid3786 : plan3786.Valid := valid_step _ _ _ valid2619 (by decide +kernel)

theorem valid3787 : plan3787.Valid := valid_step _ _ _ valid2623 (by decide +kernel)

theorem valid3788 : plan3788.Valid := valid_step _ _ _ valid2624 (by decide +kernel)

theorem valid3789 : plan3789.Valid := valid_step _ _ _ valid2625 (by decide +kernel)

theorem valid3790 : plan3790.Valid := valid_step _ _ _ valid2630 (by decide +kernel)

theorem valid3791 : plan3791.Valid := valid_step _ _ _ valid2631 (by decide +kernel)

theorem valid3792 : plan3792.Valid := valid_step _ _ _ valid2632 (by decide +kernel)

theorem valid3793 : plan3793.Valid := valid_step _ _ _ valid2633 (by decide +kernel)

theorem valid3794 : plan3794.Valid := valid_step _ _ _ valid2634 (by decide +kernel)

theorem valid3795 : plan3795.Valid := valid_step _ _ _ valid2635 (by decide +kernel)

theorem valid3796 : plan3796.Valid := valid_step _ _ _ valid2639 (by decide +kernel)

theorem valid3797 : plan3797.Valid := valid_step _ _ _ valid2642 (by decide +kernel)

theorem valid3798 : plan3798.Valid := valid_step _ _ _ valid2643 (by decide +kernel)

theorem valid3799 : plan3799.Valid := valid_step _ _ _ valid2644 (by decide +kernel)

theorem valid3800 : plan3800.Valid := valid_step _ _ _ valid2648 (by decide +kernel)

theorem valid3801 : plan3801.Valid := valid_step _ _ _ valid2649 (by decide +kernel)

theorem valid3802 : plan3802.Valid := valid_step _ _ _ valid2650 (by decide +kernel)

theorem valid3803 : plan3803.Valid := valid_step _ _ _ valid2651 (by decide +kernel)

theorem valid3804 : plan3804.Valid := valid_step _ _ _ valid2652 (by decide +kernel)

theorem valid3805 : plan3805.Valid := valid_step _ _ _ valid2656 (by decide +kernel)

theorem valid3806 : plan3806.Valid := valid_step _ _ _ valid2659 (by decide +kernel)

theorem valid3807 : plan3807.Valid := valid_step _ _ _ valid2660 (by decide +kernel)

theorem valid3808 : plan3808.Valid := valid_step _ _ _ valid2661 (by decide +kernel)

theorem valid3809 : plan3809.Valid := valid_step _ _ _ valid2665 (by decide +kernel)

theorem valid3810 : plan3810.Valid := valid_step _ _ _ valid2666 (by decide +kernel)

theorem valid3811 : plan3811.Valid := valid_step _ _ _ valid2667 (by decide +kernel)


























































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







































































theorem valid2724 : plan2724.Valid := valid_step _ _ _ valid1356 (by decide +kernel)





theorem valid2727 : plan2727.Valid := valid_step _ _ _ valid1359 (by decide +kernel)

theorem valid2728 : plan2728.Valid := valid_step _ _ _ valid1360 (by decide +kernel)

theorem valid2729 : plan2729.Valid := valid_step _ _ _ valid1361 (by decide +kernel)

theorem valid2730 : plan2730.Valid := valid_step _ _ _ valid1362 (by decide +kernel)





theorem valid2733 : plan2733.Valid := valid_step _ _ _ valid1365 (by decide +kernel)





theorem valid2736 : plan2736.Valid := valid_step _ _ _ valid1368 (by decide +kernel)

theorem valid2737 : plan2737.Valid := valid_step _ _ _ valid1369 (by decide +kernel)

theorem valid2738 : plan2738.Valid := valid_step _ _ _ valid1370 (by decide +kernel)

theorem valid2739 : plan2739.Valid := valid_step _ _ _ valid1371 (by decide +kernel)

theorem valid2740 : plan2740.Valid := valid_step _ _ _ valid1372 (by decide +kernel)

theorem valid2741 : plan2741.Valid := valid_step _ _ _ valid1373 (by decide +kernel)

theorem valid2742 : plan2742.Valid := valid_step _ _ _ valid1374 (by decide +kernel)

theorem valid2743 : plan2743.Valid := valid_step _ _ _ valid1375 (by decide +kernel)

theorem valid2744 : plan2744.Valid := valid_step _ _ _ valid1376 (by decide +kernel)







theorem valid2748 : plan2748.Valid := valid_step _ _ _ valid1385 (by decide +kernel)

theorem valid2749 : plan2749.Valid := valid_step _ _ _ valid1386 (by decide +kernel)

theorem valid2750 : plan2750.Valid := valid_step _ _ _ valid1387 (by decide +kernel)

theorem valid2751 : plan2751.Valid := valid_step _ _ _ valid1388 (by decide +kernel)





theorem valid2754 : plan2754.Valid := valid_step _ _ _ valid1391 (by decide +kernel)





theorem valid2757 : plan2757.Valid := valid_step _ _ _ valid1394 (by decide +kernel)

theorem valid2758 : plan2758.Valid := valid_step _ _ _ valid1395 (by decide +kernel)

theorem valid2759 : plan2759.Valid := valid_step _ _ _ valid1396 (by decide +kernel)

theorem valid2760 : plan2760.Valid := valid_step _ _ _ valid1397 (by decide +kernel)

theorem valid2761 : plan2761.Valid := valid_step _ _ _ valid1398 (by decide +kernel)













theorem valid2768 : plan2768.Valid := valid_step _ _ _ valid1370 (by decide +kernel)

theorem valid2769 : plan2769.Valid := valid_step _ _ _ valid1371 (by decide +kernel)

theorem valid2770 : plan2770.Valid := valid_step _ _ _ valid1372 (by decide +kernel)

theorem valid2771 : plan2771.Valid := valid_step _ _ _ valid1373 (by decide +kernel)

theorem valid2772 : plan2772.Valid := valid_step _ _ _ valid1374 (by decide +kernel)

theorem valid2773 : plan2773.Valid := valid_step _ _ _ valid1375 (by decide +kernel)

theorem valid2774 : plan2774.Valid := valid_step _ _ _ valid1376 (by decide +kernel)

theorem valid2775 : plan2775.Valid := valid_step _ _ _ valid1396 (by decide +kernel)

theorem valid2776 : plan2776.Valid := valid_step _ _ _ valid1397 (by decide +kernel)

theorem valid2777 : plan2777.Valid := valid_step _ _ _ valid1398 (by decide +kernel)













theorem valid2784 : plan2784.Valid := valid_step _ _ _ valid1328 (by decide +kernel)
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































































































































































theorem valid4016 : plan4016.Valid := valid_step _ _ _ valid2724 (by decide +kernel)

theorem valid4017 : plan4017.Valid := valid_step _ _ _ valid2727 (by decide +kernel)

theorem valid4018 : plan4018.Valid := valid_step _ _ _ valid2728 (by decide +kernel)

theorem valid4019 : plan4019.Valid := valid_step _ _ _ valid2729 (by decide +kernel)

theorem valid4020 : plan4020.Valid := valid_step _ _ _ valid2730 (by decide +kernel)

theorem valid4021 : plan4021.Valid := valid_step _ _ _ valid2733 (by decide +kernel)

theorem valid4022 : plan4022.Valid := valid_step _ _ _ valid2736 (by decide +kernel)

theorem valid4023 : plan4023.Valid := valid_step _ _ _ valid2737 (by decide +kernel)

theorem valid4024 : plan4024.Valid := valid_step _ _ _ valid2738 (by decide +kernel)

theorem valid4025 : plan4025.Valid := valid_step _ _ _ valid2739 (by decide +kernel)

theorem valid4026 : plan4026.Valid := valid_step _ _ _ valid2740 (by decide +kernel)

theorem valid4027 : plan4027.Valid := valid_step _ _ _ valid2741 (by decide +kernel)

theorem valid4028 : plan4028.Valid := valid_step _ _ _ valid2742 (by decide +kernel)

theorem valid4029 : plan4029.Valid := valid_step _ _ _ valid2743 (by decide +kernel)

theorem valid4030 : plan4030.Valid := valid_step _ _ _ valid2744 (by decide +kernel)

theorem valid4031 : plan4031.Valid := valid_step _ _ _ valid2748 (by decide +kernel)

theorem valid4032 : plan4032.Valid := valid_step _ _ _ valid2749 (by decide +kernel)
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



theorem valid2786 : plan2786.Valid := valid_step _ _ _ valid1330 (by decide +kernel)



theorem valid2788 : plan2788.Valid := valid_step _ _ _ valid1334 (by decide +kernel)









theorem valid2793 : plan2793.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2794 : plan2794.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2795 : plan2795.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2796 : plan2796.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2797 : plan2797.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2798 : plan2798.Valid := valid_step _ _ _ valid1344 (by decide +kernel)







theorem valid2802 : plan2802.Valid := valid_step _ _ _ valid1351 (by decide +kernel)









theorem valid2807 : plan2807.Valid := valid_step _ _ _ valid1383 (by decide +kernel)









theorem valid2812 : plan2812.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2813 : plan2813.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2814 : plan2814.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2815 : plan2815.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2816 : plan2816.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2817 : plan2817.Valid := valid_step _ _ _ valid1344 (by decide +kernel)



theorem valid2819 : plan2819.Valid := valid_step _ _ _ valid1350 (by decide +kernel)

theorem valid2820 : plan2820.Valid := valid_step _ _ _ valid1351 (by decide +kernel)

theorem valid2821 : plan2821.Valid := valid_step _ _ _ valid1352 (by decide +kernel)







theorem valid2825 : plan2825.Valid := valid_step _ _ _ valid1382 (by decide +kernel)

theorem valid2826 : plan2826.Valid := valid_step _ _ _ valid1383 (by decide +kernel)

theorem valid2827 : plan2827.Valid := valid_step _ _ _ valid1384 (by decide +kernel)















theorem valid2835 : plan2835.Valid := valid_step _ _ _ valid1328 (by decide +kernel)



theorem valid2837 : plan2837.Valid := valid_step _ _ _ valid1330 (by decide +kernel)



theorem valid2839 : plan2839.Valid := valid_step _ _ _ valid1334 (by decide +kernel)









theorem valid2844 : plan2844.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2845 : plan2845.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2846 : plan2846.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2847 : plan2847.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2848 : plan2848.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2849 : plan2849.Valid := valid_step _ _ _ valid1344 (by decide +kernel)





theorem valid2852 : plan2852.Valid := valid_step _ _ _ valid1351 (by decide +kernel)









theorem valid2857 : plan2857.Valid := valid_step _ _ _ valid1383 (by decide +kernel)









theorem valid2862 : plan2862.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2863 : plan2863.Valid := valid_step _ _ _ valid1340 (by decide +kernel)


































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

theorem valid4033 : plan4033.Valid := valid_step _ _ _ valid2750 (by decide +kernel)

theorem valid4034 : plan4034.Valid := valid_step _ _ _ valid2751 (by decide +kernel)

theorem valid4035 : plan4035.Valid := valid_step _ _ _ valid2754 (by decide +kernel)

theorem valid4036 : plan4036.Valid := valid_step _ _ _ valid2757 (by decide +kernel)

theorem valid4037 : plan4037.Valid := valid_step _ _ _ valid2758 (by decide +kernel)

theorem valid4038 : plan4038.Valid := valid_step _ _ _ valid2759 (by decide +kernel)

theorem valid4039 : plan4039.Valid := valid_step _ _ _ valid2760 (by decide +kernel)

theorem valid4040 : plan4040.Valid := valid_step _ _ _ valid2761 (by decide +kernel)

theorem valid4041 : plan4041.Valid := valid_step _ _ _ valid2768 (by decide +kernel)

theorem valid4042 : plan4042.Valid := valid_step _ _ _ valid2769 (by decide +kernel)

theorem valid4043 : plan4043.Valid := valid_step _ _ _ valid2770 (by decide +kernel)

theorem valid4044 : plan4044.Valid := valid_step _ _ _ valid2771 (by decide +kernel)

theorem valid4045 : plan4045.Valid := valid_step _ _ _ valid2772 (by decide +kernel)

theorem valid4046 : plan4046.Valid := valid_step _ _ _ valid2773 (by decide +kernel)

theorem valid4047 : plan4047.Valid := valid_step _ _ _ valid2774 (by decide +kernel)

theorem valid4048 : plan4048.Valid := valid_step _ _ _ valid2775 (by decide +kernel)

theorem valid4049 : plan4049.Valid := valid_step _ _ _ valid2776 (by decide +kernel)

theorem valid4050 : plan4050.Valid := valid_step _ _ _ valid2777 (by decide +kernel)

theorem valid4051 : plan4051.Valid := valid_step _ _ _ valid2784 (by decide +kernel)

theorem valid4052 : plan4052.Valid := valid_step _ _ _ valid2786 (by decide +kernel)

theorem valid4053 : plan4053.Valid := valid_step _ _ _ valid2788 (by decide +kernel)

theorem valid4054 : plan4054.Valid := valid_step _ _ _ valid2793 (by decide +kernel)

theorem valid4055 : plan4055.Valid := valid_step _ _ _ valid2794 (by decide +kernel)

theorem valid4056 : plan4056.Valid := valid_step _ _ _ valid2795 (by decide +kernel)

theorem valid4057 : plan4057.Valid := valid_step _ _ _ valid2796 (by decide +kernel)

theorem valid4058 : plan4058.Valid := valid_step _ _ _ valid2797 (by decide +kernel)

theorem valid4059 : plan4059.Valid := valid_step _ _ _ valid2798 (by decide +kernel)

theorem valid4060 : plan4060.Valid := valid_step _ _ _ valid2802 (by decide +kernel)

theorem valid4061 : plan4061.Valid := valid_step _ _ _ valid2807 (by decide +kernel)

theorem valid4062 : plan4062.Valid := valid_step _ _ _ valid2812 (by decide +kernel)

theorem valid4063 : plan4063.Valid := valid_step _ _ _ valid2813 (by decide +kernel)

theorem valid4064 : plan4064.Valid := valid_step _ _ _ valid2814 (by decide +kernel)

theorem valid4065 : plan4065.Valid := valid_step _ _ _ valid2815 (by decide +kernel)

theorem valid4066 : plan4066.Valid := valid_step _ _ _ valid2816 (by decide +kernel)

theorem valid4067 : plan4067.Valid := valid_step _ _ _ valid2817 (by decide +kernel)

theorem valid4068 : plan4068.Valid := valid_step _ _ _ valid2819 (by decide +kernel)

theorem valid4069 : plan4069.Valid := valid_step _ _ _ valid2820 (by decide +kernel)

theorem valid4070 : plan4070.Valid := valid_step _ _ _ valid2821 (by decide +kernel)

theorem valid4071 : plan4071.Valid := valid_step _ _ _ valid2825 (by decide +kernel)

theorem valid4072 : plan4072.Valid := valid_step _ _ _ valid2826 (by decide +kernel)

theorem valid4073 : plan4073.Valid := valid_step _ _ _ valid2827 (by decide +kernel)

theorem valid4074 : plan4074.Valid := valid_step _ _ _ valid2835 (by decide +kernel)

theorem valid4075 : plan4075.Valid := valid_step _ _ _ valid2837 (by decide +kernel)

theorem valid4076 : plan4076.Valid := valid_step _ _ _ valid2839 (by decide +kernel)

theorem valid4077 : plan4077.Valid := valid_step _ _ _ valid2844 (by decide +kernel)

theorem valid4078 : plan4078.Valid := valid_step _ _ _ valid2845 (by decide +kernel)

theorem valid4079 : plan4079.Valid := valid_step _ _ _ valid2846 (by decide +kernel)

theorem valid4080 : plan4080.Valid := valid_step _ _ _ valid2847 (by decide +kernel)

theorem valid4081 : plan4081.Valid := valid_step _ _ _ valid2848 (by decide +kernel)

theorem valid4082 : plan4082.Valid := valid_step _ _ _ valid2849 (by decide +kernel)

theorem valid4083 : plan4083.Valid := valid_step _ _ _ valid2852 (by decide +kernel)

theorem valid4084 : plan4084.Valid := valid_step _ _ _ valid2857 (by decide +kernel)

theorem valid4085 : plan4085.Valid := valid_step _ _ _ valid2862 (by decide +kernel)

theorem valid4086 : plan4086.Valid := valid_step _ _ _ valid2863 (by decide +kernel)




















































































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

theorem valid1441 : plan1441.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1442 : plan1442.Valid := valid_step _ _ _ valid524 (by decide +kernel)

theorem valid1443 : plan1443.Valid := valid_step _ _ _ valid517 (by decide +kernel)















theorem valid1451 : plan1451.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1452 : plan1452.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1453 : plan1453.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1454 : plan1454.Valid := valid_step _ _ _ valid517 (by decide +kernel)





theorem valid1457 : plan1457.Valid := valid_step _ _ _ valid520 (by decide +kernel)





theorem valid1460 : plan1460.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1461 : plan1461.Valid := valid_step _ _ _ valid524 (by decide +kernel)

theorem valid1462 : plan1462.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1463 : plan1463.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1464 : plan1464.Valid := valid_step _ _ _ valid524 (by decide +kernel)
















































































































































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

















































































































theorem valid2937 : plan2937.Valid := valid_step _ _ _ valid1427 (by decide +kernel)



theorem valid2939 : plan2939.Valid := valid_step _ _ _ valid1429 (by decide +kernel)



theorem valid2941 : plan2941.Valid := valid_step _ _ _ valid1435 (by decide +kernel)



theorem valid2943 : plan2943.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid2944 : plan2944.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid2945 : plan2945.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid2946 : plan2946.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid2947 : plan2947.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid2948 : plan2948.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid2949 : plan2949.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

















theorem valid2958 : plan2958.Valid := valid_step _ _ _ valid1452 (by decide +kernel)



theorem valid2960 : plan2960.Valid := valid_step _ _ _ valid1454 (by decide +kernel)



theorem valid2962 : plan2962.Valid := valid_step _ _ _ valid1460 (by decide +kernel)



theorem valid2964 : plan2964.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid2965 : plan2965.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid2966 : plan2966.Valid := valid_step _ _ _ valid1464 (by decide +kernel)




















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





theorem valid2979 : plan2979.Valid := valid_step _ _ _ valid1423 (by decide +kernel)





theorem valid2982 : plan2982.Valid := valid_step _ _ _ valid1426 (by decide +kernel)

theorem valid2983 : plan2983.Valid := valid_step _ _ _ valid1427 (by decide +kernel)

theorem valid2984 : plan2984.Valid := valid_step _ _ _ valid1428 (by decide +kernel)

theorem valid2985 : plan2985.Valid := valid_step _ _ _ valid1429 (by decide +kernel)





theorem valid2988 : plan2988.Valid := valid_step _ _ _ valid1432 (by decide +kernel)





theorem valid2991 : plan2991.Valid := valid_step _ _ _ valid1435 (by decide +kernel)

theorem valid2992 : plan2992.Valid := valid_step _ _ _ valid1436 (by decide +kernel)

theorem valid2993 : plan2993.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid2994 : plan2994.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid2995 : plan2995.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid2996 : plan2996.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid2997 : plan2997.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid2998 : plan2998.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid2999 : plan2999.Valid := valid_step _ _ _ valid1443 (by decide +kernel)







theorem valid3003 : plan3003.Valid := valid_step _ _ _ valid1451 (by decide +kernel)

theorem valid3004 : plan3004.Valid := valid_step _ _ _ valid1452 (by decide +kernel)

theorem valid3005 : plan3005.Valid := valid_step _ _ _ valid1453 (by decide +kernel)

theorem valid3006 : plan3006.Valid := valid_step _ _ _ valid1454 (by decide +kernel)





theorem valid3009 : plan3009.Valid := valid_step _ _ _ valid1457 (by decide +kernel)





theorem valid3012 : plan3012.Valid := valid_step _ _ _ valid1460 (by decide +kernel)

theorem valid3013 : plan3013.Valid := valid_step _ _ _ valid1461 (by decide +kernel)

theorem valid3014 : plan3014.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3015 : plan3015.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid3016 : plan3016.Valid := valid_step _ _ _ valid1464 (by decide +kernel)

theorem valid3017 : plan3017.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid3018 : plan3018.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid3019 : plan3019.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid3020 : plan3020.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid3021 : plan3021.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid3022 : plan3022.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid3023 : plan3023.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

theorem valid3024 : plan3024.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3025 : plan3025.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid3026 : plan3026.Valid := valid_step _ _ _ valid1464 (by decide +kernel)

theorem valid3027 : plan3027.Valid := valid_step _ _ _ valid1443 (by decide +kernel)







































theorem valid3047 : plan3047.Valid := valid_step _ _ _ valid1427 (by decide +kernel)



theorem valid3049 : plan3049.Valid := valid_step _ _ _ valid1429 (by decide +kernel)



theorem valid3051 : plan3051.Valid := valid_step _ _ _ valid1435 (by decide +kernel)



theorem valid3053 : plan3053.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid3054 : plan3054.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid3055 : plan3055.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid3056 : plan3056.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid3057 : plan3057.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid3058 : plan3058.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid3059 : plan3059.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

















theorem valid3068 : plan3068.Valid := valid_step _ _ _ valid1452 (by decide +kernel)



theorem valid3070 : plan3070.Valid := valid_step _ _ _ valid1454 (by decide +kernel)



theorem valid3072 : plan3072.Valid := valid_step _ _ _ valid1460 (by decide +kernel)
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



































































theorem valid4450 : plan4450.Valid := valid_step _ _ _ valid2937 (by decide +kernel)

theorem valid4451 : plan4451.Valid := valid_step _ _ _ valid2939 (by decide +kernel)

theorem valid4452 : plan4452.Valid := valid_step _ _ _ valid2941 (by decide +kernel)

theorem valid4453 : plan4453.Valid := valid_step _ _ _ valid2943 (by decide +kernel)

theorem valid4454 : plan4454.Valid := valid_step _ _ _ valid2944 (by decide +kernel)

theorem valid4455 : plan4455.Valid := valid_step _ _ _ valid2945 (by decide +kernel)

theorem valid4456 : plan4456.Valid := valid_step _ _ _ valid2946 (by decide +kernel)

theorem valid4457 : plan4457.Valid := valid_step _ _ _ valid2947 (by decide +kernel)

theorem valid4458 : plan4458.Valid := valid_step _ _ _ valid2948 (by decide +kernel)

theorem valid4459 : plan4459.Valid := valid_step _ _ _ valid2949 (by decide +kernel)

theorem valid4460 : plan4460.Valid := valid_step _ _ _ valid2958 (by decide +kernel)

theorem valid4461 : plan4461.Valid := valid_step _ _ _ valid2960 (by decide +kernel)

theorem valid4462 : plan4462.Valid := valid_step _ _ _ valid2962 (by decide +kernel)

theorem valid4463 : plan4463.Valid := valid_step _ _ _ valid2964 (by decide +kernel)

theorem valid4464 : plan4464.Valid := valid_step _ _ _ valid2965 (by decide +kernel)

theorem valid4465 : plan4465.Valid := valid_step _ _ _ valid2966 (by decide +kernel)

theorem valid4466 : plan4466.Valid := valid_step _ _ _ valid2979 (by decide +kernel)

theorem valid4467 : plan4467.Valid := valid_step _ _ _ valid2982 (by decide +kernel)

theorem valid4468 : plan4468.Valid := valid_step _ _ _ valid2983 (by decide +kernel)

theorem valid4469 : plan4469.Valid := valid_step _ _ _ valid2984 (by decide +kernel)

theorem valid4470 : plan4470.Valid := valid_step _ _ _ valid2985 (by decide +kernel)

theorem valid4471 : plan4471.Valid := valid_step _ _ _ valid2988 (by decide +kernel)

theorem valid4472 : plan4472.Valid := valid_step _ _ _ valid2991 (by decide +kernel)

theorem valid4473 : plan4473.Valid := valid_step _ _ _ valid2992 (by decide +kernel)

theorem valid4474 : plan4474.Valid := valid_step _ _ _ valid2993 (by decide +kernel)

theorem valid4475 : plan4475.Valid := valid_step _ _ _ valid2994 (by decide +kernel)

theorem valid4476 : plan4476.Valid := valid_step _ _ _ valid2995 (by decide +kernel)

theorem valid4477 : plan4477.Valid := valid_step _ _ _ valid2996 (by decide +kernel)

theorem valid4478 : plan4478.Valid := valid_step _ _ _ valid2997 (by decide +kernel)

theorem valid4479 : plan4479.Valid := valid_step _ _ _ valid2998 (by decide +kernel)

theorem valid4480 : plan4480.Valid := valid_step _ _ _ valid2999 (by decide +kernel)

theorem valid4481 : plan4481.Valid := valid_step _ _ _ valid3003 (by decide +kernel)

theorem valid4482 : plan4482.Valid := valid_step _ _ _ valid3004 (by decide +kernel)

theorem valid4483 : plan4483.Valid := valid_step _ _ _ valid3005 (by decide +kernel)

theorem valid4484 : plan4484.Valid := valid_step _ _ _ valid3006 (by decide +kernel)

theorem valid4485 : plan4485.Valid := valid_step _ _ _ valid3009 (by decide +kernel)

theorem valid4486 : plan4486.Valid := valid_step _ _ _ valid3012 (by decide +kernel)

theorem valid4487 : plan4487.Valid := valid_step _ _ _ valid3013 (by decide +kernel)

theorem valid4488 : plan4488.Valid := valid_step _ _ _ valid3014 (by decide +kernel)

theorem valid4489 : plan4489.Valid := valid_step _ _ _ valid3015 (by decide +kernel)

theorem valid4490 : plan4490.Valid := valid_step _ _ _ valid3016 (by decide +kernel)

theorem valid4491 : plan4491.Valid := valid_step _ _ _ valid3017 (by decide +kernel)

theorem valid4492 : plan4492.Valid := valid_step _ _ _ valid3018 (by decide +kernel)

theorem valid4493 : plan4493.Valid := valid_step _ _ _ valid3019 (by decide +kernel)

theorem valid4494 : plan4494.Valid := valid_step _ _ _ valid3020 (by decide +kernel)

theorem valid4495 : plan4495.Valid := valid_step _ _ _ valid3021 (by decide +kernel)

theorem valid4496 : plan4496.Valid := valid_step _ _ _ valid3022 (by decide +kernel)

theorem valid4497 : plan4497.Valid := valid_step _ _ _ valid3023 (by decide +kernel)

theorem valid4498 : plan4498.Valid := valid_step _ _ _ valid3024 (by decide +kernel)

theorem valid4499 : plan4499.Valid := valid_step _ _ _ valid3025 (by decide +kernel)

theorem valid4500 : plan4500.Valid := valid_step _ _ _ valid3026 (by decide +kernel)

theorem valid4501 : plan4501.Valid := valid_step _ _ _ valid3027 (by decide +kernel)

theorem valid4502 : plan4502.Valid := valid_step _ _ _ valid3047 (by decide +kernel)

theorem valid4503 : plan4503.Valid := valid_step _ _ _ valid3049 (by decide +kernel)

theorem valid4504 : plan4504.Valid := valid_step _ _ _ valid3051 (by decide +kernel)

theorem valid4505 : plan4505.Valid := valid_step _ _ _ valid3053 (by decide +kernel)

theorem valid4506 : plan4506.Valid := valid_step _ _ _ valid3054 (by decide +kernel)

theorem valid4507 : plan4507.Valid := valid_step _ _ _ valid3055 (by decide +kernel)

theorem valid4508 : plan4508.Valid := valid_step _ _ _ valid3056 (by decide +kernel)

theorem valid4509 : plan4509.Valid := valid_step _ _ _ valid3057 (by decide +kernel)

theorem valid4510 : plan4510.Valid := valid_step _ _ _ valid3058 (by decide +kernel)

theorem valid4511 : plan4511.Valid := valid_step _ _ _ valid3059 (by decide +kernel)

theorem valid4512 : plan4512.Valid := valid_step _ _ _ valid3068 (by decide +kernel)
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



theorem valid3074 : plan3074.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3075 : plan3075.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid3076 : plan3076.Valid := valid_step _ _ _ valid1464 (by decide +kernel)
























































































































































































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

theorem valid4513 : plan4513.Valid := valid_step _ _ _ valid3070 (by decide +kernel)

theorem valid4514 : plan4514.Valid := valid_step _ _ _ valid3072 (by decide +kernel)

theorem valid4515 : plan4515.Valid := valid_step _ _ _ valid3074 (by decide +kernel)

theorem valid4516 : plan4516.Valid := valid_step _ _ _ valid3075 (by decide +kernel)

theorem valid4517 : plan4517.Valid := valid_step _ _ _ valid3076 (by decide +kernel)






















































































































































































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
theorem t5_52choices : plan3781.choices=[0,2,3,7,7].map (options 5 2) := by rfl


theorem t5_52part0 : t5_52jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_52frontier : t5_52root.frontier 0=t5_52jobs := by rfl
theorem t5_52all : t5_52jobs.all (Job.check tree)=true := by
  simp only [t5_52jobs,List.all_append,List.all_nil,t5_52part0,Bool.and_self]
theorem t5_52checked : Checked tree [0,2,3,7,7] := by
  refine ⟨plan3781,valid3781,t5_52choices,?_⟩
  exact check_of_frontier tree 0 t5_52root t5_52jobs t5_52frontier t5_52all
theorem t5_53choices : plan3782.choices=[0,2,3,10,7].map (options 5 2) := by rfl


theorem t5_53part0 : t5_53jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_53frontier : t5_53root.frontier 0=t5_53jobs := by rfl
theorem t5_53all : t5_53jobs.all (Job.check tree)=true := by
  simp only [t5_53jobs,List.all_append,List.all_nil,t5_53part0,Bool.and_self]
theorem t5_53checked : Checked tree [0,2,3,10,7] := by
  refine ⟨plan3782,valid3782,t5_53choices,?_⟩
  exact check_of_frontier tree 0 t5_53root t5_53jobs t5_53frontier t5_53all
theorem t5_54choices : plan3783.choices=[0,2,3,10,10].map (options 5 2) := by rfl


theorem t5_54part0 : t5_54jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_54frontier : t5_54root.frontier 0=t5_54jobs := by rfl
theorem t5_54all : t5_54jobs.all (Job.check tree)=true := by
  simp only [t5_54jobs,List.all_append,List.all_nil,t5_54part0,Bool.and_self]
theorem t5_54checked : Checked tree [0,2,3,10,10] := by
  refine ⟨plan3783,valid3783,t5_54choices,?_⟩
  exact check_of_frontier tree 0 t5_54root t5_54jobs t5_54frontier t5_54all
theorem t5_55choices : plan3685.choices=[0,2,5,3,3].map (options 5 1) := by rfl


theorem t5_55part0 : t5_55jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_55frontier : t5_55root.frontier 0=t5_55jobs := by rfl
theorem t5_55all : t5_55jobs.all (Job.check tree)=true := by
  simp only [t5_55jobs,List.all_append,List.all_nil,t5_55part0,Bool.and_self]
theorem t5_55checked : Checked tree [0,2,5,3,3] := by
  refine ⟨plan3685,valid3685,t5_55choices,?_⟩
  exact check_of_frontier tree 0 t5_55root t5_55jobs t5_55frontier t5_55all
theorem t5_56choices : plan3784.choices=[0,2,5,3,6].map (options 5 2) := by rfl


theorem t5_56part0 : t5_56jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_56frontier : t5_56root.frontier 0=t5_56jobs := by rfl
theorem t5_56all : t5_56jobs.all (Job.check tree)=true := by
  simp only [t5_56jobs,List.all_append,List.all_nil,t5_56part0,Bool.and_self]
theorem t5_56checked : Checked tree [0,2,5,3,6] := by
  refine ⟨plan3784,valid3784,t5_56choices,?_⟩
  exact check_of_frontier tree 0 t5_56root t5_56jobs t5_56frontier t5_56all
theorem t5_57choices : plan3785.choices=[0,2,5,3,7].map (options 5 2) := by rfl


theorem t5_57part0 : t5_57jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_57frontier : t5_57root.frontier 0=t5_57jobs := by rfl
theorem t5_57all : t5_57jobs.all (Job.check tree)=true := by
  simp only [t5_57jobs,List.all_append,List.all_nil,t5_57part0,Bool.and_self]
theorem t5_57checked : Checked tree [0,2,5,3,7] := by
  refine ⟨plan3785,valid3785,t5_57choices,?_⟩
  exact check_of_frontier tree 0 t5_57root t5_57jobs t5_57frontier t5_57all
theorem t5_58choices : plan3786.choices=[0,2,5,3,10].map (options 5 2) := by rfl


theorem t5_58part0 : t5_58jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_58frontier : t5_58root.frontier 0=t5_58jobs := by rfl
theorem t5_58all : t5_58jobs.all (Job.check tree)=true := by
  simp only [t5_58jobs,List.all_append,List.all_nil,t5_58part0,Bool.and_self]
theorem t5_58checked : Checked tree [0,2,5,3,10] := by
  refine ⟨plan3786,valid3786,t5_58choices,?_⟩
  exact check_of_frontier tree 0 t5_58root t5_58jobs t5_58frontier t5_58all
theorem t5_59choices : plan4016.choices=[0,2,5,5,7].map (options 5 3) := by rfl


theorem t5_59part0 : t5_59jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_59frontier : t5_59root.frontier 0=t5_59jobs := by rfl
theorem t5_59all : t5_59jobs.all (Job.check tree)=true := by
  simp only [t5_59jobs,List.all_append,List.all_nil,t5_59part0,Bool.and_self]
theorem t5_59checked : Checked tree [0,2,5,5,7] := by
  refine ⟨plan4016,valid4016,t5_59choices,?_⟩
  exact check_of_frontier tree 0 t5_59root t5_59jobs t5_59frontier t5_59all
theorem t5_60choices : plan4017.choices=[0,2,5,6,6].map (options 5 3) := by rfl


theorem t5_60part0 : t5_60jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_60frontier : t5_60root.frontier 0=t5_60jobs := by rfl
theorem t5_60all : t5_60jobs.all (Job.check tree)=true := by
  simp only [t5_60jobs,List.all_append,List.all_nil,t5_60part0,Bool.and_self]
theorem t5_60checked : Checked tree [0,2,5,6,6] := by
  refine ⟨plan4017,valid4017,t5_60choices,?_⟩
  exact check_of_frontier tree 0 t5_60root t5_60jobs t5_60frontier t5_60all
theorem t5_61choices : plan4018.choices=[0,2,5,6,7].map (options 5 3) := by rfl


theorem t5_61part0 : t5_61jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_61frontier : t5_61root.frontier 0=t5_61jobs := by rfl
theorem t5_61all : t5_61jobs.all (Job.check tree)=true := by
  simp only [t5_61jobs,List.all_append,List.all_nil,t5_61part0,Bool.and_self]
theorem t5_61checked : Checked tree [0,2,5,6,7] := by
  refine ⟨plan4018,valid4018,t5_61choices,?_⟩
  exact check_of_frontier tree 0 t5_61root t5_61jobs t5_61frontier t5_61all
theorem t5_62choices : plan4019.choices=[0,2,5,6,10].map (options 5 3) := by rfl


theorem t5_62part0 : t5_62jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_62frontier : t5_62root.frontier 0=t5_62jobs := by rfl
theorem t5_62all : t5_62jobs.all (Job.check tree)=true := by
  simp only [t5_62jobs,List.all_append,List.all_nil,t5_62part0,Bool.and_self]
theorem t5_62checked : Checked tree [0,2,5,6,10] := by
  refine ⟨plan4019,valid4019,t5_62choices,?_⟩
  exact check_of_frontier tree 0 t5_62root t5_62jobs t5_62frontier t5_62all
theorem t5_63choices : plan4020.choices=[0,2,5,7,7].map (options 5 3) := by rfl


theorem t5_63part0 : t5_63jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_63frontier : t5_63root.frontier 0=t5_63jobs := by rfl
theorem t5_63all : t5_63jobs.all (Job.check tree)=true := by
  simp only [t5_63jobs,List.all_append,List.all_nil,t5_63part0,Bool.and_self]
theorem t5_63checked : Checked tree [0,2,5,7,7] := by
  refine ⟨plan4020,valid4020,t5_63choices,?_⟩
  exact check_of_frontier tree 0 t5_63root t5_63jobs t5_63frontier t5_63all
theorem t5_64choices : plan4021.choices=[0,2,5,9,7].map (options 5 3) := by rfl


theorem t5_64part0 : t5_64jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_64frontier : t5_64root.frontier 0=t5_64jobs := by rfl
theorem t5_64all : t5_64jobs.all (Job.check tree)=true := by
  simp only [t5_64jobs,List.all_append,List.all_nil,t5_64part0,Bool.and_self]
theorem t5_64checked : Checked tree [0,2,5,9,7] := by
  refine ⟨plan4021,valid4021,t5_64choices,?_⟩
  exact check_of_frontier tree 0 t5_64root t5_64jobs t5_64frontier t5_64all
theorem t5_65choices : plan4022.choices=[0,2,5,10,7].map (options 5 3) := by rfl


theorem t5_65part0 : t5_65jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_65frontier : t5_65root.frontier 0=t5_65jobs := by rfl
theorem t5_65all : t5_65jobs.all (Job.check tree)=true := by
  simp only [t5_65jobs,List.all_append,List.all_nil,t5_65part0,Bool.and_self]
theorem t5_65checked : Checked tree [0,2,5,10,7] := by
  refine ⟨plan4022,valid4022,t5_65choices,?_⟩
  exact check_of_frontier tree 0 t5_65root t5_65jobs t5_65frontier t5_65all
theorem t5_66choices : plan4023.choices=[0,2,5,10,10].map (options 5 3) := by rfl


theorem t5_66part0 : t5_66jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_66frontier : t5_66root.frontier 0=t5_66jobs := by rfl
theorem t5_66all : t5_66jobs.all (Job.check tree)=true := by
  simp only [t5_66jobs,List.all_append,List.all_nil,t5_66part0,Bool.and_self]
theorem t5_66checked : Checked tree [0,2,5,10,10] := by
  refine ⟨plan4023,valid4023,t5_66choices,?_⟩
  exact check_of_frontier tree 0 t5_66root t5_66jobs t5_66frontier t5_66all
theorem t5_67choices : plan4024.choices=[0,2,6,6,6].map (options 5 3) := by rfl


theorem t5_67part0 : t5_67jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_67frontier : t5_67root.frontier 0=t5_67jobs := by rfl
theorem t5_67all : t5_67jobs.all (Job.check tree)=true := by
  simp only [t5_67jobs,List.all_append,List.all_nil,t5_67part0,Bool.and_self]
theorem t5_67checked : Checked tree [0,2,6,6,6] := by
  refine ⟨plan4024,valid4024,t5_67choices,?_⟩
  exact check_of_frontier tree 0 t5_67root t5_67jobs t5_67frontier t5_67all
theorem t5_68choices : plan4025.choices=[0,2,6,6,7].map (options 5 3) := by rfl


theorem t5_68part0 : t5_68jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_68frontier : t5_68root.frontier 0=t5_68jobs := by rfl
theorem t5_68all : t5_68jobs.all (Job.check tree)=true := by
  simp only [t5_68jobs,List.all_append,List.all_nil,t5_68part0,Bool.and_self]
theorem t5_68checked : Checked tree [0,2,6,6,7] := by
  refine ⟨plan4025,valid4025,t5_68choices,?_⟩
  exact check_of_frontier tree 0 t5_68root t5_68jobs t5_68frontier t5_68all
theorem t5_69choices : plan4026.choices=[0,2,6,6,10].map (options 5 3) := by rfl


theorem t5_69part0 : t5_69jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_69frontier : t5_69root.frontier 0=t5_69jobs := by rfl
theorem t5_69all : t5_69jobs.all (Job.check tree)=true := by
  simp only [t5_69jobs,List.all_append,List.all_nil,t5_69part0,Bool.and_self]
theorem t5_69checked : Checked tree [0,2,6,6,10] := by
  refine ⟨plan4026,valid4026,t5_69choices,?_⟩
  exact check_of_frontier tree 0 t5_69root t5_69jobs t5_69frontier t5_69all
theorem t5_70choices : plan4027.choices=[0,2,6,7,7].map (options 5 3) := by rfl


theorem t5_70part0 : t5_70jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_70frontier : t5_70root.frontier 0=t5_70jobs := by rfl
theorem t5_70all : t5_70jobs.all (Job.check tree)=true := by
  simp only [t5_70jobs,List.all_append,List.all_nil,t5_70part0,Bool.and_self]
theorem t5_70checked : Checked tree [0,2,6,7,7] := by
  refine ⟨plan4027,valid4027,t5_70choices,?_⟩
  exact check_of_frontier tree 0 t5_70root t5_70jobs t5_70frontier t5_70all
theorem t5_71choices : plan4028.choices=[0,2,6,10,7].map (options 5 3) := by rfl


theorem t5_71part0 : t5_71jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_71frontier : t5_71root.frontier 0=t5_71jobs := by rfl
theorem t5_71all : t5_71jobs.all (Job.check tree)=true := by
  simp only [t5_71jobs,List.all_append,List.all_nil,t5_71part0,Bool.and_self]
theorem t5_71checked : Checked tree [0,2,6,10,7] := by
  refine ⟨plan4028,valid4028,t5_71choices,?_⟩
  exact check_of_frontier tree 0 t5_71root t5_71jobs t5_71frontier t5_71all
theorem t5_72choices : plan4029.choices=[0,2,6,10,10].map (options 5 3) := by rfl


theorem t5_72part0 : t5_72jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_72frontier : t5_72root.frontier 0=t5_72jobs := by rfl
theorem t5_72all : t5_72jobs.all (Job.check tree)=true := by
  simp only [t5_72jobs,List.all_append,List.all_nil,t5_72part0,Bool.and_self]
theorem t5_72checked : Checked tree [0,2,6,10,10] := by
  refine ⟨plan4029,valid4029,t5_72choices,?_⟩
  exact check_of_frontier tree 0 t5_72root t5_72jobs t5_72frontier t5_72all
theorem t5_73choices : plan4030.choices=[0,2,7,7,7].map (options 5 3) := by rfl


theorem t5_73part0 : t5_73jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_73frontier : t5_73root.frontier 0=t5_73jobs := by rfl
theorem t5_73all : t5_73jobs.all (Job.check tree)=true := by
  simp only [t5_73jobs,List.all_append,List.all_nil,t5_73part0,Bool.and_self]
theorem t5_73checked : Checked tree [0,2,7,7,7] := by
  refine ⟨plan4030,valid4030,t5_73choices,?_⟩
  exact check_of_frontier tree 0 t5_73root t5_73jobs t5_73frontier t5_73all
theorem t5_74choices : plan3686.choices=[0,2,9,3,3].map (options 5 1) := by rfl


theorem t5_74part0 : t5_74jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_74frontier : t5_74root.frontier 0=t5_74jobs := by rfl
theorem t5_74all : t5_74jobs.all (Job.check tree)=true := by
  simp only [t5_74jobs,List.all_append,List.all_nil,t5_74part0,Bool.and_self]
theorem t5_74checked : Checked tree [0,2,9,3,3] := by
  refine ⟨plan3686,valid3686,t5_74choices,?_⟩
  exact check_of_frontier tree 0 t5_74root t5_74jobs t5_74frontier t5_74all
theorem t5_75choices : plan3787.choices=[0,2,9,3,6].map (options 5 2) := by rfl


theorem t5_75part0 : t5_75jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_75frontier : t5_75root.frontier 0=t5_75jobs := by rfl
theorem t5_75all : t5_75jobs.all (Job.check tree)=true := by
  simp only [t5_75jobs,List.all_append,List.all_nil,t5_75part0,Bool.and_self]
theorem t5_75checked : Checked tree [0,2,9,3,6] := by
  refine ⟨plan3787,valid3787,t5_75choices,?_⟩
  exact check_of_frontier tree 0 t5_75root t5_75jobs t5_75frontier t5_75all
theorem t5_76choices : plan3788.choices=[0,2,9,3,7].map (options 5 2) := by rfl


theorem t5_76part0 : t5_76jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_76frontier : t5_76root.frontier 0=t5_76jobs := by rfl
theorem t5_76all : t5_76jobs.all (Job.check tree)=true := by
  simp only [t5_76jobs,List.all_append,List.all_nil,t5_76part0,Bool.and_self]
theorem t5_76checked : Checked tree [0,2,9,3,7] := by
  refine ⟨plan3788,valid3788,t5_76choices,?_⟩
  exact check_of_frontier tree 0 t5_76root t5_76jobs t5_76frontier t5_76all
theorem t5_77choices : plan3789.choices=[0,2,9,3,10].map (options 5 2) := by rfl


theorem t5_77part0 : t5_77jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_77frontier : t5_77root.frontier 0=t5_77jobs := by rfl
theorem t5_77all : t5_77jobs.all (Job.check tree)=true := by
  simp only [t5_77jobs,List.all_append,List.all_nil,t5_77part0,Bool.and_self]
theorem t5_77checked : Checked tree [0,2,9,3,10] := by
  refine ⟨plan3789,valid3789,t5_77choices,?_⟩
  exact check_of_frontier tree 0 t5_77root t5_77jobs t5_77frontier t5_77all
theorem t5_78choices : plan4031.choices=[0,2,9,6,6].map (options 5 3) := by rfl


theorem t5_78part0 : t5_78jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_78frontier : t5_78root.frontier 0=t5_78jobs := by rfl
theorem t5_78all : t5_78jobs.all (Job.check tree)=true := by
  simp only [t5_78jobs,List.all_append,List.all_nil,t5_78part0,Bool.and_self]
theorem t5_78checked : Checked tree [0,2,9,6,6] := by
  refine ⟨plan4031,valid4031,t5_78choices,?_⟩
  exact check_of_frontier tree 0 t5_78root t5_78jobs t5_78frontier t5_78all
theorem t5_79choices : plan4032.choices=[0,2,9,6,7].map (options 5 3) := by rfl


theorem t5_79part0 : t5_79jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_79frontier : t5_79root.frontier 0=t5_79jobs := by rfl
theorem t5_79all : t5_79jobs.all (Job.check tree)=true := by
  simp only [t5_79jobs,List.all_append,List.all_nil,t5_79part0,Bool.and_self]
theorem t5_79checked : Checked tree [0,2,9,6,7] := by
  refine ⟨plan4032,valid4032,t5_79choices,?_⟩
  exact check_of_frontier tree 0 t5_79root t5_79jobs t5_79frontier t5_79all
theorem t5_80choices : plan4033.choices=[0,2,9,6,10].map (options 5 3) := by rfl


theorem t5_80part0 : t5_80jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_80frontier : t5_80root.frontier 0=t5_80jobs := by rfl
theorem t5_80all : t5_80jobs.all (Job.check tree)=true := by
  simp only [t5_80jobs,List.all_append,List.all_nil,t5_80part0,Bool.and_self]
theorem t5_80checked : Checked tree [0,2,9,6,10] := by
  refine ⟨plan4033,valid4033,t5_80choices,?_⟩
  exact check_of_frontier tree 0 t5_80root t5_80jobs t5_80frontier t5_80all
theorem t5_81choices : plan4034.choices=[0,2,9,7,7].map (options 5 3) := by rfl


theorem t5_81part0 : t5_81jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_81frontier : t5_81root.frontier 0=t5_81jobs := by rfl
theorem t5_81all : t5_81jobs.all (Job.check tree)=true := by
  simp only [t5_81jobs,List.all_append,List.all_nil,t5_81part0,Bool.and_self]
theorem t5_81checked : Checked tree [0,2,9,7,7] := by
  refine ⟨plan4034,valid4034,t5_81choices,?_⟩
  exact check_of_frontier tree 0 t5_81root t5_81jobs t5_81frontier t5_81all
theorem t5_82choices : plan4035.choices=[0,2,9,9,7].map (options 5 3) := by rfl


theorem t5_82part0 : t5_82jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_82frontier : t5_82root.frontier 0=t5_82jobs := by rfl
theorem t5_82all : t5_82jobs.all (Job.check tree)=true := by
  simp only [t5_82jobs,List.all_append,List.all_nil,t5_82part0,Bool.and_self]
theorem t5_82checked : Checked tree [0,2,9,9,7] := by
  refine ⟨plan4035,valid4035,t5_82choices,?_⟩
  exact check_of_frontier tree 0 t5_82root t5_82jobs t5_82frontier t5_82all
theorem t5_83choices : plan4036.choices=[0,2,9,10,7].map (options 5 3) := by rfl


theorem t5_83part0 : t5_83jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_83frontier : t5_83root.frontier 0=t5_83jobs := by rfl
theorem t5_83all : t5_83jobs.all (Job.check tree)=true := by
  simp only [t5_83jobs,List.all_append,List.all_nil,t5_83part0,Bool.and_self]
theorem t5_83checked : Checked tree [0,2,9,10,7] := by
  refine ⟨plan4036,valid4036,t5_83choices,?_⟩
  exact check_of_frontier tree 0 t5_83root t5_83jobs t5_83frontier t5_83all
theorem t5_84choices : plan4037.choices=[0,2,9,10,10].map (options 5 3) := by rfl


theorem t5_84part0 : t5_84jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_84frontier : t5_84root.frontier 0=t5_84jobs := by rfl
theorem t5_84all : t5_84jobs.all (Job.check tree)=true := by
  simp only [t5_84jobs,List.all_append,List.all_nil,t5_84part0,Bool.and_self]
theorem t5_84checked : Checked tree [0,2,9,10,10] := by
  refine ⟨plan4037,valid4037,t5_84choices,?_⟩
  exact check_of_frontier tree 0 t5_84root t5_84jobs t5_84frontier t5_84all
theorem t5_85choices : plan4038.choices=[0,2,10,7,7].map (options 5 3) := by rfl


theorem t5_85part0 : t5_85jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_85frontier : t5_85root.frontier 0=t5_85jobs := by rfl
theorem t5_85all : t5_85jobs.all (Job.check tree)=true := by
  simp only [t5_85jobs,List.all_append,List.all_nil,t5_85part0,Bool.and_self]
theorem t5_85checked : Checked tree [0,2,10,7,7] := by
  refine ⟨plan4038,valid4038,t5_85choices,?_⟩
  exact check_of_frontier tree 0 t5_85root t5_85jobs t5_85frontier t5_85all
theorem t5_86choices : plan4039.choices=[0,2,10,10,7].map (options 5 3) := by rfl


theorem t5_86part0 : t5_86jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_86frontier : t5_86root.frontier 0=t5_86jobs := by rfl
theorem t5_86all : t5_86jobs.all (Job.check tree)=true := by
  simp only [t5_86jobs,List.all_append,List.all_nil,t5_86part0,Bool.and_self]
theorem t5_86checked : Checked tree [0,2,10,10,7] := by
  refine ⟨plan4039,valid4039,t5_86choices,?_⟩
  exact check_of_frontier tree 0 t5_86root t5_86jobs t5_86frontier t5_86all
theorem t5_87choices : plan4040.choices=[0,2,10,10,10].map (options 5 3) := by rfl


theorem t5_87part0 : t5_87jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_87frontier : t5_87root.frontier 0=t5_87jobs := by rfl
theorem t5_87all : t5_87jobs.all (Job.check tree)=true := by
  simp only [t5_87jobs,List.all_append,List.all_nil,t5_87part0,Bool.and_self]
theorem t5_87checked : Checked tree [0,2,10,10,10] := by
  refine ⟨plan4040,valid4040,t5_87choices,?_⟩
  exact check_of_frontier tree 0 t5_87root t5_87jobs t5_87frontier t5_87all
theorem t5_88choices : plan3661.choices=[0,3,3,3,3].map (options 5 0) := by rfl


theorem t5_88part0 : t5_88jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_88frontier : t5_88root.frontier 0=t5_88jobs := by rfl
theorem t5_88all : t5_88jobs.all (Job.check tree)=true := by
  simp only [t5_88jobs,List.all_append,List.all_nil,t5_88part0,Bool.and_self]
theorem t5_88checked : Checked tree [0,3,3,3,3] := by
  refine ⟨plan3661,valid3661,t5_88choices,?_⟩
  exact check_of_frontier tree 0 t5_88root t5_88jobs t5_88frontier t5_88all
theorem t5_89choices : plan3687.choices=[0,3,3,3,6].map (options 5 1) := by rfl


theorem t5_89part0 : t5_89jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_89frontier : t5_89root.frontier 0=t5_89jobs := by rfl
theorem t5_89all : t5_89jobs.all (Job.check tree)=true := by
  simp only [t5_89jobs,List.all_append,List.all_nil,t5_89part0,Bool.and_self]
theorem t5_89checked : Checked tree [0,3,3,3,6] := by
  refine ⟨plan3687,valid3687,t5_89choices,?_⟩
  exact check_of_frontier tree 0 t5_89root t5_89jobs t5_89frontier t5_89all
theorem t5_90choices : plan3688.choices=[0,3,3,3,7].map (options 5 1) := by rfl


theorem t5_90part0 : t5_90jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_90frontier : t5_90root.frontier 0=t5_90jobs := by rfl
theorem t5_90all : t5_90jobs.all (Job.check tree)=true := by
  simp only [t5_90jobs,List.all_append,List.all_nil,t5_90part0,Bool.and_self]
theorem t5_90checked : Checked tree [0,3,3,3,7] := by
  refine ⟨plan3688,valid3688,t5_90choices,?_⟩
  exact check_of_frontier tree 0 t5_90root t5_90jobs t5_90frontier t5_90all
theorem t5_91choices : plan3689.choices=[0,3,3,3,10].map (options 5 1) := by rfl


theorem t5_91part0 : t5_91jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_91frontier : t5_91root.frontier 0=t5_91jobs := by rfl
theorem t5_91all : t5_91jobs.all (Job.check tree)=true := by
  simp only [t5_91jobs,List.all_append,List.all_nil,t5_91part0,Bool.and_self]
theorem t5_91checked : Checked tree [0,3,3,3,10] := by
  refine ⟨plan3689,valid3689,t5_91choices,?_⟩
  exact check_of_frontier tree 0 t5_91root t5_91jobs t5_91frontier t5_91all
theorem t5_92choices : plan3790.choices=[0,3,3,6,6].map (options 5 2) := by rfl


theorem t5_92part0 : t5_92jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_92frontier : t5_92root.frontier 0=t5_92jobs := by rfl
theorem t5_92all : t5_92jobs.all (Job.check tree)=true := by
  simp only [t5_92jobs,List.all_append,List.all_nil,t5_92part0,Bool.and_self]
theorem t5_92checked : Checked tree [0,3,3,6,6] := by
  refine ⟨plan3790,valid3790,t5_92choices,?_⟩
  exact check_of_frontier tree 0 t5_92root t5_92jobs t5_92frontier t5_92all
theorem t5_93choices : plan3791.choices=[0,3,3,6,7].map (options 5 2) := by rfl


theorem t5_93part0 : t5_93jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_93frontier : t5_93root.frontier 0=t5_93jobs := by rfl
theorem t5_93all : t5_93jobs.all (Job.check tree)=true := by
  simp only [t5_93jobs,List.all_append,List.all_nil,t5_93part0,Bool.and_self]
theorem t5_93checked : Checked tree [0,3,3,6,7] := by
  refine ⟨plan3791,valid3791,t5_93choices,?_⟩
  exact check_of_frontier tree 0 t5_93root t5_93jobs t5_93frontier t5_93all
theorem t5_94choices : plan3792.choices=[0,3,3,6,10].map (options 5 2) := by rfl


theorem t5_94part0 : t5_94jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_94frontier : t5_94root.frontier 0=t5_94jobs := by rfl
theorem t5_94all : t5_94jobs.all (Job.check tree)=true := by
  simp only [t5_94jobs,List.all_append,List.all_nil,t5_94part0,Bool.and_self]
theorem t5_94checked : Checked tree [0,3,3,6,10] := by
  refine ⟨plan3792,valid3792,t5_94choices,?_⟩
  exact check_of_frontier tree 0 t5_94root t5_94jobs t5_94frontier t5_94all
theorem t5_95choices : plan3793.choices=[0,3,3,7,7].map (options 5 2) := by rfl


theorem t5_95part0 : t5_95jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_95frontier : t5_95root.frontier 0=t5_95jobs := by rfl
theorem t5_95all : t5_95jobs.all (Job.check tree)=true := by
  simp only [t5_95jobs,List.all_append,List.all_nil,t5_95part0,Bool.and_self]
theorem t5_95checked : Checked tree [0,3,3,7,7] := by
  refine ⟨plan3793,valid3793,t5_95choices,?_⟩
  exact check_of_frontier tree 0 t5_95root t5_95jobs t5_95frontier t5_95all
theorem t5_96choices : plan3794.choices=[0,3,3,10,7].map (options 5 2) := by rfl


theorem t5_96part0 : t5_96jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_96frontier : t5_96root.frontier 0=t5_96jobs := by rfl
theorem t5_96all : t5_96jobs.all (Job.check tree)=true := by
  simp only [t5_96jobs,List.all_append,List.all_nil,t5_96part0,Bool.and_self]
theorem t5_96checked : Checked tree [0,3,3,10,7] := by
  refine ⟨plan3794,valid3794,t5_96choices,?_⟩
  exact check_of_frontier tree 0 t5_96root t5_96jobs t5_96frontier t5_96all
theorem t5_97choices : plan3795.choices=[0,3,3,10,10].map (options 5 2) := by rfl


theorem t5_97part0 : t5_97jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_97frontier : t5_97root.frontier 0=t5_97jobs := by rfl
theorem t5_97all : t5_97jobs.all (Job.check tree)=true := by
  simp only [t5_97jobs,List.all_append,List.all_nil,t5_97part0,Bool.and_self]
theorem t5_97checked : Checked tree [0,3,3,10,10] := by
  refine ⟨plan3795,valid3795,t5_97choices,?_⟩
  exact check_of_frontier tree 0 t5_97root t5_97jobs t5_97frontier t5_97all
theorem t5_98choices : plan4041.choices=[0,3,6,6,6].map (options 5 3) := by rfl


theorem t5_98part0 : t5_98jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_98frontier : t5_98root.frontier 0=t5_98jobs := by rfl
theorem t5_98all : t5_98jobs.all (Job.check tree)=true := by
  simp only [t5_98jobs,List.all_append,List.all_nil,t5_98part0,Bool.and_self]
theorem t5_98checked : Checked tree [0,3,6,6,6] := by
  refine ⟨plan4041,valid4041,t5_98choices,?_⟩
  exact check_of_frontier tree 0 t5_98root t5_98jobs t5_98frontier t5_98all
theorem t5_99choices : plan4042.choices=[0,3,6,6,7].map (options 5 3) := by rfl


theorem t5_99part0 : t5_99jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_99frontier : t5_99root.frontier 0=t5_99jobs := by rfl
theorem t5_99all : t5_99jobs.all (Job.check tree)=true := by
  simp only [t5_99jobs,List.all_append,List.all_nil,t5_99part0,Bool.and_self]
theorem t5_99checked : Checked tree [0,3,6,6,7] := by
  refine ⟨plan4042,valid4042,t5_99choices,?_⟩
  exact check_of_frontier tree 0 t5_99root t5_99jobs t5_99frontier t5_99all
theorem t5_100choices : plan4043.choices=[0,3,6,6,10].map (options 5 3) := by rfl


theorem t5_100part0 : t5_100jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_100frontier : t5_100root.frontier 0=t5_100jobs := by rfl
theorem t5_100all : t5_100jobs.all (Job.check tree)=true := by
  simp only [t5_100jobs,List.all_append,List.all_nil,t5_100part0,Bool.and_self]
theorem t5_100checked : Checked tree [0,3,6,6,10] := by
  refine ⟨plan4043,valid4043,t5_100choices,?_⟩
  exact check_of_frontier tree 0 t5_100root t5_100jobs t5_100frontier t5_100all
theorem t5_101choices : plan4044.choices=[0,3,6,7,7].map (options 5 3) := by rfl


theorem t5_101part0 : t5_101jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_101frontier : t5_101root.frontier 0=t5_101jobs := by rfl
theorem t5_101all : t5_101jobs.all (Job.check tree)=true := by
  simp only [t5_101jobs,List.all_append,List.all_nil,t5_101part0,Bool.and_self]
theorem t5_101checked : Checked tree [0,3,6,7,7] := by
  refine ⟨plan4044,valid4044,t5_101choices,?_⟩
  exact check_of_frontier tree 0 t5_101root t5_101jobs t5_101frontier t5_101all
theorem t5_102choices : plan4045.choices=[0,3,6,10,7].map (options 5 3) := by rfl


theorem t5_102part0 : t5_102jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_102frontier : t5_102root.frontier 0=t5_102jobs := by rfl
theorem t5_102all : t5_102jobs.all (Job.check tree)=true := by
  simp only [t5_102jobs,List.all_append,List.all_nil,t5_102part0,Bool.and_self]
theorem t5_102checked : Checked tree [0,3,6,10,7] := by
  refine ⟨plan4045,valid4045,t5_102choices,?_⟩
  exact check_of_frontier tree 0 t5_102root t5_102jobs t5_102frontier t5_102all
theorem t5_103choices : plan4046.choices=[0,3,6,10,10].map (options 5 3) := by rfl


theorem t5_103part0 : t5_103jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_103frontier : t5_103root.frontier 0=t5_103jobs := by rfl
theorem t5_103all : t5_103jobs.all (Job.check tree)=true := by
  simp only [t5_103jobs,List.all_append,List.all_nil,t5_103part0,Bool.and_self]
theorem t5_103checked : Checked tree [0,3,6,10,10] := by
  refine ⟨plan4046,valid4046,t5_103choices,?_⟩
  exact check_of_frontier tree 0 t5_103root t5_103jobs t5_103frontier t5_103all
theorem t5_104choices : plan4047.choices=[0,3,7,7,7].map (options 5 3) := by rfl


theorem t5_104part0 : t5_104jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_104frontier : t5_104root.frontier 0=t5_104jobs := by rfl
theorem t5_104all : t5_104jobs.all (Job.check tree)=true := by
  simp only [t5_104jobs,List.all_append,List.all_nil,t5_104part0,Bool.and_self]
theorem t5_104checked : Checked tree [0,3,7,7,7] := by
  refine ⟨plan4047,valid4047,t5_104choices,?_⟩
  exact check_of_frontier tree 0 t5_104root t5_104jobs t5_104frontier t5_104all
theorem t5_105choices : plan4048.choices=[0,3,10,7,7].map (options 5 3) := by rfl


theorem t5_105part0 : t5_105jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_105frontier : t5_105root.frontier 0=t5_105jobs := by rfl
theorem t5_105all : t5_105jobs.all (Job.check tree)=true := by
  simp only [t5_105jobs,List.all_append,List.all_nil,t5_105part0,Bool.and_self]
theorem t5_105checked : Checked tree [0,3,10,7,7] := by
  refine ⟨plan4048,valid4048,t5_105choices,?_⟩
  exact check_of_frontier tree 0 t5_105root t5_105jobs t5_105frontier t5_105all
theorem t5_106choices : plan4049.choices=[0,3,10,10,7].map (options 5 3) := by rfl


theorem t5_106part0 : t5_106jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_106frontier : t5_106root.frontier 0=t5_106jobs := by rfl
theorem t5_106all : t5_106jobs.all (Job.check tree)=true := by
  simp only [t5_106jobs,List.all_append,List.all_nil,t5_106part0,Bool.and_self]
theorem t5_106checked : Checked tree [0,3,10,10,7] := by
  refine ⟨plan4049,valid4049,t5_106choices,?_⟩
  exact check_of_frontier tree 0 t5_106root t5_106jobs t5_106frontier t5_106all
theorem t5_107choices : plan4050.choices=[0,3,10,10,10].map (options 5 3) := by rfl


theorem t5_107part0 : t5_107jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_107frontier : t5_107root.frontier 0=t5_107jobs := by rfl
theorem t5_107all : t5_107jobs.all (Job.check tree)=true := by
  simp only [t5_107jobs,List.all_append,List.all_nil,t5_107part0,Bool.and_self]
theorem t5_107checked : Checked tree [0,3,10,10,10] := by
  refine ⟨plan4050,valid4050,t5_107choices,?_⟩
  exact check_of_frontier tree 0 t5_107root t5_107jobs t5_107frontier t5_107all
theorem t5_108choices : plan3796.choices=[0,4,2,3,7].map (options 5 2) := by rfl


theorem t5_108part0 : t5_108jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_108frontier : t5_108root.frontier 0=t5_108jobs := by rfl
theorem t5_108all : t5_108jobs.all (Job.check tree)=true := by
  simp only [t5_108jobs,List.all_append,List.all_nil,t5_108part0,Bool.and_self]
theorem t5_108checked : Checked tree [0,4,2,3,7] := by
  refine ⟨plan3796,valid3796,t5_108choices,?_⟩
  exact check_of_frontier tree 0 t5_108root t5_108jobs t5_108frontier t5_108all
theorem t5_109choices : plan4051.choices=[0,4,2,6,7].map (options 5 3) := by rfl


theorem t5_109part0 : t5_109jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_109frontier : t5_109root.frontier 0=t5_109jobs := by rfl
theorem t5_109all : t5_109jobs.all (Job.check tree)=true := by
  simp only [t5_109jobs,List.all_append,List.all_nil,t5_109part0,Bool.and_self]
theorem t5_109checked : Checked tree [0,4,2,6,7] := by
  refine ⟨plan4051,valid4051,t5_109choices,?_⟩
  exact check_of_frontier tree 0 t5_109root t5_109jobs t5_109frontier t5_109all
theorem t5_110choices : plan4052.choices=[0,4,2,7,7].map (options 5 3) := by rfl


theorem t5_110part0 : t5_110jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_110frontier : t5_110root.frontier 0=t5_110jobs := by rfl
theorem t5_110all : t5_110jobs.all (Job.check tree)=true := by
  simp only [t5_110jobs,List.all_append,List.all_nil,t5_110part0,Bool.and_self]
theorem t5_110checked : Checked tree [0,4,2,7,7] := by
  refine ⟨plan4052,valid4052,t5_110choices,?_⟩
  exact check_of_frontier tree 0 t5_110root t5_110jobs t5_110frontier t5_110all
theorem t5_111choices : plan4053.choices=[0,4,2,10,7].map (options 5 3) := by rfl


theorem t5_111part0 : t5_111jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_111frontier : t5_111root.frontier 0=t5_111jobs := by rfl
theorem t5_111all : t5_111jobs.all (Job.check tree)=true := by
  simp only [t5_111jobs,List.all_append,List.all_nil,t5_111part0,Bool.and_self]
theorem t5_111checked : Checked tree [0,4,2,10,7] := by
  refine ⟨plan4053,valid4053,t5_111choices,?_⟩
  exact check_of_frontier tree 0 t5_111root t5_111jobs t5_111frontier t5_111all
theorem t5_112choices : plan3690.choices=[0,4,3,3,3].map (options 5 1) := by rfl


theorem t5_112part0 : t5_112jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_112frontier : t5_112root.frontier 0=t5_112jobs := by rfl
theorem t5_112all : t5_112jobs.all (Job.check tree)=true := by
  simp only [t5_112jobs,List.all_append,List.all_nil,t5_112part0,Bool.and_self]
theorem t5_112checked : Checked tree [0,4,3,3,3] := by
  refine ⟨plan3690,valid3690,t5_112choices,?_⟩
  exact check_of_frontier tree 0 t5_112root t5_112jobs t5_112frontier t5_112all
theorem t5_113choices : plan3797.choices=[0,4,3,3,6].map (options 5 2) := by rfl


theorem t5_113part0 : t5_113jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_113frontier : t5_113root.frontier 0=t5_113jobs := by rfl
theorem t5_113all : t5_113jobs.all (Job.check tree)=true := by
  simp only [t5_113jobs,List.all_append,List.all_nil,t5_113part0,Bool.and_self]
theorem t5_113checked : Checked tree [0,4,3,3,6] := by
  refine ⟨plan3797,valid3797,t5_113choices,?_⟩
  exact check_of_frontier tree 0 t5_113root t5_113jobs t5_113frontier t5_113all
theorem t5_114choices : plan3798.choices=[0,4,3,3,7].map (options 5 2) := by rfl


theorem t5_114part0 : t5_114jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_114frontier : t5_114root.frontier 0=t5_114jobs := by rfl
theorem t5_114all : t5_114jobs.all (Job.check tree)=true := by
  simp only [t5_114jobs,List.all_append,List.all_nil,t5_114part0,Bool.and_self]
theorem t5_114checked : Checked tree [0,4,3,3,7] := by
  refine ⟨plan3798,valid3798,t5_114choices,?_⟩
  exact check_of_frontier tree 0 t5_114root t5_114jobs t5_114frontier t5_114all
theorem t5_115choices : plan3799.choices=[0,4,3,3,10].map (options 5 2) := by rfl


theorem t5_115part0 : t5_115jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_115frontier : t5_115root.frontier 0=t5_115jobs := by rfl
theorem t5_115all : t5_115jobs.all (Job.check tree)=true := by
  simp only [t5_115jobs,List.all_append,List.all_nil,t5_115part0,Bool.and_self]
theorem t5_115checked : Checked tree [0,4,3,3,10] := by
  refine ⟨plan3799,valid3799,t5_115choices,?_⟩
  exact check_of_frontier tree 0 t5_115root t5_115jobs t5_115frontier t5_115all
theorem t5_116choices : plan4054.choices=[0,4,3,6,6].map (options 5 3) := by rfl


theorem t5_116part0 : t5_116jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_116frontier : t5_116root.frontier 0=t5_116jobs := by rfl
theorem t5_116all : t5_116jobs.all (Job.check tree)=true := by
  simp only [t5_116jobs,List.all_append,List.all_nil,t5_116part0,Bool.and_self]
theorem t5_116checked : Checked tree [0,4,3,6,6] := by
  refine ⟨plan4054,valid4054,t5_116choices,?_⟩
  exact check_of_frontier tree 0 t5_116root t5_116jobs t5_116frontier t5_116all
theorem t5_117choices : plan4055.choices=[0,4,3,6,7].map (options 5 3) := by rfl


theorem t5_117part0 : t5_117jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_117frontier : t5_117root.frontier 0=t5_117jobs := by rfl
theorem t5_117all : t5_117jobs.all (Job.check tree)=true := by
  simp only [t5_117jobs,List.all_append,List.all_nil,t5_117part0,Bool.and_self]
theorem t5_117checked : Checked tree [0,4,3,6,7] := by
  refine ⟨plan4055,valid4055,t5_117choices,?_⟩
  exact check_of_frontier tree 0 t5_117root t5_117jobs t5_117frontier t5_117all
theorem t5_118choices : plan4056.choices=[0,4,3,6,10].map (options 5 3) := by rfl


theorem t5_118part0 : t5_118jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_118frontier : t5_118root.frontier 0=t5_118jobs := by rfl
theorem t5_118all : t5_118jobs.all (Job.check tree)=true := by
  simp only [t5_118jobs,List.all_append,List.all_nil,t5_118part0,Bool.and_self]
theorem t5_118checked : Checked tree [0,4,3,6,10] := by
  refine ⟨plan4056,valid4056,t5_118choices,?_⟩
  exact check_of_frontier tree 0 t5_118root t5_118jobs t5_118frontier t5_118all
theorem t5_119choices : plan4057.choices=[0,4,3,7,7].map (options 5 3) := by rfl


theorem t5_119part0 : t5_119jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_119frontier : t5_119root.frontier 0=t5_119jobs := by rfl
theorem t5_119all : t5_119jobs.all (Job.check tree)=true := by
  simp only [t5_119jobs,List.all_append,List.all_nil,t5_119part0,Bool.and_self]
theorem t5_119checked : Checked tree [0,4,3,7,7] := by
  refine ⟨plan4057,valid4057,t5_119choices,?_⟩
  exact check_of_frontier tree 0 t5_119root t5_119jobs t5_119frontier t5_119all
theorem t5_120choices : plan4058.choices=[0,4,3,10,7].map (options 5 3) := by rfl


theorem t5_120part0 : t5_120jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_120frontier : t5_120root.frontier 0=t5_120jobs := by rfl
theorem t5_120all : t5_120jobs.all (Job.check tree)=true := by
  simp only [t5_120jobs,List.all_append,List.all_nil,t5_120part0,Bool.and_self]
theorem t5_120checked : Checked tree [0,4,3,10,7] := by
  refine ⟨plan4058,valid4058,t5_120choices,?_⟩
  exact check_of_frontier tree 0 t5_120root t5_120jobs t5_120frontier t5_120all
theorem t5_121choices : plan4059.choices=[0,4,3,10,10].map (options 5 3) := by rfl


theorem t5_121part0 : t5_121jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_121frontier : t5_121root.frontier 0=t5_121jobs := by rfl
theorem t5_121all : t5_121jobs.all (Job.check tree)=true := by
  simp only [t5_121jobs,List.all_append,List.all_nil,t5_121part0,Bool.and_self]
theorem t5_121checked : Checked tree [0,4,3,10,10] := by
  refine ⟨plan4059,valid4059,t5_121choices,?_⟩
  exact check_of_frontier tree 0 t5_121root t5_121jobs t5_121frontier t5_121all
theorem t5_122choices : plan4060.choices=[0,4,5,3,7].map (options 5 3) := by rfl


theorem t5_122part0 : t5_122jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_122frontier : t5_122root.frontier 0=t5_122jobs := by rfl
theorem t5_122all : t5_122jobs.all (Job.check tree)=true := by
  simp only [t5_122jobs,List.all_append,List.all_nil,t5_122part0,Bool.and_self]
theorem t5_122checked : Checked tree [0,4,5,3,7] := by
  refine ⟨plan4060,valid4060,t5_122choices,?_⟩
  exact check_of_frontier tree 0 t5_122root t5_122jobs t5_122frontier t5_122all
theorem t5_123choices : plan4450.choices=[0,4,5,6,7].map (options 5 4) := by rfl


theorem t5_123part0 : t5_123jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_123frontier : t5_123root.frontier 0=t5_123jobs := by rfl
theorem t5_123all : t5_123jobs.all (Job.check tree)=true := by
  simp only [t5_123jobs,List.all_append,List.all_nil,t5_123part0,Bool.and_self]
theorem t5_123checked : Checked tree [0,4,5,6,7] := by
  refine ⟨plan4450,valid4450,t5_123choices,?_⟩
  exact check_of_frontier tree 0 t5_123root t5_123jobs t5_123frontier t5_123all
theorem t5_124choices : plan4451.choices=[0,4,5,7,7].map (options 5 4) := by rfl


theorem t5_124part0 : t5_124jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_124frontier : t5_124root.frontier 0=t5_124jobs := by rfl
theorem t5_124all : t5_124jobs.all (Job.check tree)=true := by
  simp only [t5_124jobs,List.all_append,List.all_nil,t5_124part0,Bool.and_self]
theorem t5_124checked : Checked tree [0,4,5,7,7] := by
  refine ⟨plan4451,valid4451,t5_124choices,?_⟩
  exact check_of_frontier tree 0 t5_124root t5_124jobs t5_124frontier t5_124all
theorem t5_125choices : plan4452.choices=[0,4,5,10,7].map (options 5 4) := by rfl


theorem t5_125part0 : t5_125jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_125frontier : t5_125root.frontier 0=t5_125jobs := by rfl
theorem t5_125all : t5_125jobs.all (Job.check tree)=true := by
  simp only [t5_125jobs,List.all_append,List.all_nil,t5_125part0,Bool.and_self]
theorem t5_125checked : Checked tree [0,4,5,10,7] := by
  refine ⟨plan4452,valid4452,t5_125choices,?_⟩
  exact check_of_frontier tree 0 t5_125root t5_125jobs t5_125frontier t5_125all
theorem t5_126choices : plan4453.choices=[0,4,6,6,6].map (options 5 4) := by rfl


theorem t5_126part0 : t5_126jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_126frontier : t5_126root.frontier 0=t5_126jobs := by rfl
theorem t5_126all : t5_126jobs.all (Job.check tree)=true := by
  simp only [t5_126jobs,List.all_append,List.all_nil,t5_126part0,Bool.and_self]
theorem t5_126checked : Checked tree [0,4,6,6,6] := by
  refine ⟨plan4453,valid4453,t5_126choices,?_⟩
  exact check_of_frontier tree 0 t5_126root t5_126jobs t5_126frontier t5_126all
theorem t5_127choices : plan4454.choices=[0,4,6,6,7].map (options 5 4) := by rfl


theorem t5_127part0 : t5_127jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_127frontier : t5_127root.frontier 0=t5_127jobs := by rfl
theorem t5_127all : t5_127jobs.all (Job.check tree)=true := by
  simp only [t5_127jobs,List.all_append,List.all_nil,t5_127part0,Bool.and_self]
theorem t5_127checked : Checked tree [0,4,6,6,7] := by
  refine ⟨plan4454,valid4454,t5_127choices,?_⟩
  exact check_of_frontier tree 0 t5_127root t5_127jobs t5_127frontier t5_127all
theorem t5_128choices : plan4455.choices=[0,4,6,6,10].map (options 5 4) := by rfl


theorem t5_128part0 : t5_128jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_128frontier : t5_128root.frontier 0=t5_128jobs := by rfl
theorem t5_128all : t5_128jobs.all (Job.check tree)=true := by
  simp only [t5_128jobs,List.all_append,List.all_nil,t5_128part0,Bool.and_self]
theorem t5_128checked : Checked tree [0,4,6,6,10] := by
  refine ⟨plan4455,valid4455,t5_128choices,?_⟩
  exact check_of_frontier tree 0 t5_128root t5_128jobs t5_128frontier t5_128all
theorem t5_129choices : plan4456.choices=[0,4,6,7,7].map (options 5 4) := by rfl


theorem t5_129part0 : t5_129jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_129frontier : t5_129root.frontier 0=t5_129jobs := by rfl
theorem t5_129all : t5_129jobs.all (Job.check tree)=true := by
  simp only [t5_129jobs,List.all_append,List.all_nil,t5_129part0,Bool.and_self]
theorem t5_129checked : Checked tree [0,4,6,7,7] := by
  refine ⟨plan4456,valid4456,t5_129choices,?_⟩
  exact check_of_frontier tree 0 t5_129root t5_129jobs t5_129frontier t5_129all
theorem t5_130choices : plan4457.choices=[0,4,6,10,7].map (options 5 4) := by rfl


theorem t5_130part0 : t5_130jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_130frontier : t5_130root.frontier 0=t5_130jobs := by rfl
theorem t5_130all : t5_130jobs.all (Job.check tree)=true := by
  simp only [t5_130jobs,List.all_append,List.all_nil,t5_130part0,Bool.and_self]
theorem t5_130checked : Checked tree [0,4,6,10,7] := by
  refine ⟨plan4457,valid4457,t5_130choices,?_⟩
  exact check_of_frontier tree 0 t5_130root t5_130jobs t5_130frontier t5_130all
theorem t5_131choices : plan4458.choices=[0,4,6,10,10].map (options 5 4) := by rfl


theorem t5_131part0 : t5_131jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_131frontier : t5_131root.frontier 0=t5_131jobs := by rfl
theorem t5_131all : t5_131jobs.all (Job.check tree)=true := by
  simp only [t5_131jobs,List.all_append,List.all_nil,t5_131part0,Bool.and_self]
theorem t5_131checked : Checked tree [0,4,6,10,10] := by
  refine ⟨plan4458,valid4458,t5_131choices,?_⟩
  exact check_of_frontier tree 0 t5_131root t5_131jobs t5_131frontier t5_131all
theorem t5_132choices : plan4459.choices=[0,4,7,7,7].map (options 5 4) := by rfl


theorem t5_132part0 : t5_132jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_132frontier : t5_132root.frontier 0=t5_132jobs := by rfl
theorem t5_132all : t5_132jobs.all (Job.check tree)=true := by
  simp only [t5_132jobs,List.all_append,List.all_nil,t5_132part0,Bool.and_self]
theorem t5_132checked : Checked tree [0,4,7,7,7] := by
  refine ⟨plan4459,valid4459,t5_132choices,?_⟩
  exact check_of_frontier tree 0 t5_132root t5_132jobs t5_132frontier t5_132all
theorem t5_133choices : plan4061.choices=[0,4,9,3,7].map (options 5 3) := by rfl


theorem t5_133part0 : t5_133jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_133frontier : t5_133root.frontier 0=t5_133jobs := by rfl
theorem t5_133all : t5_133jobs.all (Job.check tree)=true := by
  simp only [t5_133jobs,List.all_append,List.all_nil,t5_133part0,Bool.and_self]
theorem t5_133checked : Checked tree [0,4,9,3,7] := by
  refine ⟨plan4061,valid4061,t5_133choices,?_⟩
  exact check_of_frontier tree 0 t5_133root t5_133jobs t5_133frontier t5_133all
theorem t5_134choices : plan4460.choices=[0,4,9,6,7].map (options 5 4) := by rfl


theorem t5_134part0 : t5_134jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_134frontier : t5_134root.frontier 0=t5_134jobs := by rfl
theorem t5_134all : t5_134jobs.all (Job.check tree)=true := by
  simp only [t5_134jobs,List.all_append,List.all_nil,t5_134part0,Bool.and_self]
theorem t5_134checked : Checked tree [0,4,9,6,7] := by
  refine ⟨plan4460,valid4460,t5_134choices,?_⟩
  exact check_of_frontier tree 0 t5_134root t5_134jobs t5_134frontier t5_134all
theorem t5_135choices : plan4461.choices=[0,4,9,7,7].map (options 5 4) := by rfl


theorem t5_135part0 : t5_135jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_135frontier : t5_135root.frontier 0=t5_135jobs := by rfl
theorem t5_135all : t5_135jobs.all (Job.check tree)=true := by
  simp only [t5_135jobs,List.all_append,List.all_nil,t5_135part0,Bool.and_self]
theorem t5_135checked : Checked tree [0,4,9,7,7] := by
  refine ⟨plan4461,valid4461,t5_135choices,?_⟩
  exact check_of_frontier tree 0 t5_135root t5_135jobs t5_135frontier t5_135all
theorem t5_136choices : plan4462.choices=[0,4,9,10,7].map (options 5 4) := by rfl


theorem t5_136part0 : t5_136jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_136frontier : t5_136root.frontier 0=t5_136jobs := by rfl
theorem t5_136all : t5_136jobs.all (Job.check tree)=true := by
  simp only [t5_136jobs,List.all_append,List.all_nil,t5_136part0,Bool.and_self]
theorem t5_136checked : Checked tree [0,4,9,10,7] := by
  refine ⟨plan4462,valid4462,t5_136choices,?_⟩
  exact check_of_frontier tree 0 t5_136root t5_136jobs t5_136frontier t5_136all
theorem t5_137choices : plan4463.choices=[0,4,10,7,7].map (options 5 4) := by rfl


theorem t5_137part0 : t5_137jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_137frontier : t5_137root.frontier 0=t5_137jobs := by rfl
theorem t5_137all : t5_137jobs.all (Job.check tree)=true := by
  simp only [t5_137jobs,List.all_append,List.all_nil,t5_137part0,Bool.and_self]
theorem t5_137checked : Checked tree [0,4,10,7,7] := by
  refine ⟨plan4463,valid4463,t5_137choices,?_⟩
  exact check_of_frontier tree 0 t5_137root t5_137jobs t5_137frontier t5_137all
theorem t5_138choices : plan4464.choices=[0,4,10,10,7].map (options 5 4) := by rfl


theorem t5_138part0 : t5_138jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_138frontier : t5_138root.frontier 0=t5_138jobs := by rfl
theorem t5_138all : t5_138jobs.all (Job.check tree)=true := by
  simp only [t5_138jobs,List.all_append,List.all_nil,t5_138part0,Bool.and_self]
theorem t5_138checked : Checked tree [0,4,10,10,7] := by
  refine ⟨plan4464,valid4464,t5_138choices,?_⟩
  exact check_of_frontier tree 0 t5_138root t5_138jobs t5_138frontier t5_138all
theorem t5_139choices : plan4465.choices=[0,4,10,10,10].map (options 5 4) := by rfl


theorem t5_139part0 : t5_139jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_139frontier : t5_139root.frontier 0=t5_139jobs := by rfl
theorem t5_139all : t5_139jobs.all (Job.check tree)=true := by
  simp only [t5_139jobs,List.all_append,List.all_nil,t5_139part0,Bool.and_self]
theorem t5_139checked : Checked tree [0,4,10,10,10] := by
  refine ⟨plan4465,valid4465,t5_139choices,?_⟩
  exact check_of_frontier tree 0 t5_139root t5_139jobs t5_139frontier t5_139all
theorem t5_140choices : plan3691.choices=[0,5,3,3,3].map (options 5 1) := by rfl


theorem t5_140part0 : t5_140jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_140frontier : t5_140root.frontier 0=t5_140jobs := by rfl
theorem t5_140all : t5_140jobs.all (Job.check tree)=true := by
  simp only [t5_140jobs,List.all_append,List.all_nil,t5_140part0,Bool.and_self]
theorem t5_140checked : Checked tree [0,5,3,3,3] := by
  refine ⟨plan3691,valid3691,t5_140choices,?_⟩
  exact check_of_frontier tree 0 t5_140root t5_140jobs t5_140frontier t5_140all
theorem t5_141choices : plan3800.choices=[0,5,3,3,6].map (options 5 2) := by rfl


theorem t5_141part0 : t5_141jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_141frontier : t5_141root.frontier 0=t5_141jobs := by rfl
theorem t5_141all : t5_141jobs.all (Job.check tree)=true := by
  simp only [t5_141jobs,List.all_append,List.all_nil,t5_141part0,Bool.and_self]
theorem t5_141checked : Checked tree [0,5,3,3,6] := by
  refine ⟨plan3800,valid3800,t5_141choices,?_⟩
  exact check_of_frontier tree 0 t5_141root t5_141jobs t5_141frontier t5_141all
theorem t5_142choices : plan3801.choices=[0,5,3,3,7].map (options 5 2) := by rfl


theorem t5_142part0 : t5_142jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_142frontier : t5_142root.frontier 0=t5_142jobs := by rfl
theorem t5_142all : t5_142jobs.all (Job.check tree)=true := by
  simp only [t5_142jobs,List.all_append,List.all_nil,t5_142part0,Bool.and_self]
theorem t5_142checked : Checked tree [0,5,3,3,7] := by
  refine ⟨plan3801,valid3801,t5_142choices,?_⟩
  exact check_of_frontier tree 0 t5_142root t5_142jobs t5_142frontier t5_142all
theorem t5_143choices : plan3802.choices=[0,5,3,3,10].map (options 5 2) := by rfl


theorem t5_143part0 : t5_143jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_143frontier : t5_143root.frontier 0=t5_143jobs := by rfl
theorem t5_143all : t5_143jobs.all (Job.check tree)=true := by
  simp only [t5_143jobs,List.all_append,List.all_nil,t5_143part0,Bool.and_self]
theorem t5_143checked : Checked tree [0,5,3,3,10] := by
  refine ⟨plan3802,valid3802,t5_143choices,?_⟩
  exact check_of_frontier tree 0 t5_143root t5_143jobs t5_143frontier t5_143all
theorem t5_144choices : plan4062.choices=[0,5,3,6,6].map (options 5 3) := by rfl


theorem t5_144part0 : t5_144jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_144frontier : t5_144root.frontier 0=t5_144jobs := by rfl
theorem t5_144all : t5_144jobs.all (Job.check tree)=true := by
  simp only [t5_144jobs,List.all_append,List.all_nil,t5_144part0,Bool.and_self]
theorem t5_144checked : Checked tree [0,5,3,6,6] := by
  refine ⟨plan4062,valid4062,t5_144choices,?_⟩
  exact check_of_frontier tree 0 t5_144root t5_144jobs t5_144frontier t5_144all
theorem t5_145choices : plan4063.choices=[0,5,3,6,7].map (options 5 3) := by rfl


theorem t5_145part0 : t5_145jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_145frontier : t5_145root.frontier 0=t5_145jobs := by rfl
theorem t5_145all : t5_145jobs.all (Job.check tree)=true := by
  simp only [t5_145jobs,List.all_append,List.all_nil,t5_145part0,Bool.and_self]
theorem t5_145checked : Checked tree [0,5,3,6,7] := by
  refine ⟨plan4063,valid4063,t5_145choices,?_⟩
  exact check_of_frontier tree 0 t5_145root t5_145jobs t5_145frontier t5_145all
theorem t5_146choices : plan4064.choices=[0,5,3,6,10].map (options 5 3) := by rfl


theorem t5_146part0 : t5_146jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_146frontier : t5_146root.frontier 0=t5_146jobs := by rfl
theorem t5_146all : t5_146jobs.all (Job.check tree)=true := by
  simp only [t5_146jobs,List.all_append,List.all_nil,t5_146part0,Bool.and_self]
theorem t5_146checked : Checked tree [0,5,3,6,10] := by
  refine ⟨plan4064,valid4064,t5_146choices,?_⟩
  exact check_of_frontier tree 0 t5_146root t5_146jobs t5_146frontier t5_146all
theorem t5_147choices : plan4065.choices=[0,5,3,7,7].map (options 5 3) := by rfl


theorem t5_147part0 : t5_147jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_147frontier : t5_147root.frontier 0=t5_147jobs := by rfl
theorem t5_147all : t5_147jobs.all (Job.check tree)=true := by
  simp only [t5_147jobs,List.all_append,List.all_nil,t5_147part0,Bool.and_self]
theorem t5_147checked : Checked tree [0,5,3,7,7] := by
  refine ⟨plan4065,valid4065,t5_147choices,?_⟩
  exact check_of_frontier tree 0 t5_147root t5_147jobs t5_147frontier t5_147all
theorem t5_148choices : plan4066.choices=[0,5,3,10,7].map (options 5 3) := by rfl


theorem t5_148part0 : t5_148jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_148frontier : t5_148root.frontier 0=t5_148jobs := by rfl
theorem t5_148all : t5_148jobs.all (Job.check tree)=true := by
  simp only [t5_148jobs,List.all_append,List.all_nil,t5_148part0,Bool.and_self]
theorem t5_148checked : Checked tree [0,5,3,10,7] := by
  refine ⟨plan4066,valid4066,t5_148choices,?_⟩
  exact check_of_frontier tree 0 t5_148root t5_148jobs t5_148frontier t5_148all
theorem t5_149choices : plan4067.choices=[0,5,3,10,10].map (options 5 3) := by rfl


theorem t5_149part0 : t5_149jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_149frontier : t5_149root.frontier 0=t5_149jobs := by rfl
theorem t5_149all : t5_149jobs.all (Job.check tree)=true := by
  simp only [t5_149jobs,List.all_append,List.all_nil,t5_149part0,Bool.and_self]
theorem t5_149checked : Checked tree [0,5,3,10,10] := by
  refine ⟨plan4067,valid4067,t5_149choices,?_⟩
  exact check_of_frontier tree 0 t5_149root t5_149jobs t5_149frontier t5_149all
theorem t5_150choices : plan3803.choices=[0,5,5,3,3].map (options 5 2) := by rfl


theorem t5_150part0 : t5_150jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_150frontier : t5_150root.frontier 0=t5_150jobs := by rfl
theorem t5_150all : t5_150jobs.all (Job.check tree)=true := by
  simp only [t5_150jobs,List.all_append,List.all_nil,t5_150part0,Bool.and_self]
theorem t5_150checked : Checked tree [0,5,5,3,3] := by
  refine ⟨plan3803,valid3803,t5_150choices,?_⟩
  exact check_of_frontier tree 0 t5_150root t5_150jobs t5_150frontier t5_150all
theorem t5_151choices : plan4068.choices=[0,5,5,3,6].map (options 5 3) := by rfl


theorem t5_151part0 : t5_151jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_151frontier : t5_151root.frontier 0=t5_151jobs := by rfl
theorem t5_151all : t5_151jobs.all (Job.check tree)=true := by
  simp only [t5_151jobs,List.all_append,List.all_nil,t5_151part0,Bool.and_self]
theorem t5_151checked : Checked tree [0,5,5,3,6] := by
  refine ⟨plan4068,valid4068,t5_151choices,?_⟩
  exact check_of_frontier tree 0 t5_151root t5_151jobs t5_151frontier t5_151all
theorem t5_152choices : plan4069.choices=[0,5,5,3,7].map (options 5 3) := by rfl


theorem t5_152part0 : t5_152jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_152frontier : t5_152root.frontier 0=t5_152jobs := by rfl
theorem t5_152all : t5_152jobs.all (Job.check tree)=true := by
  simp only [t5_152jobs,List.all_append,List.all_nil,t5_152part0,Bool.and_self]
theorem t5_152checked : Checked tree [0,5,5,3,7] := by
  refine ⟨plan4069,valid4069,t5_152choices,?_⟩
  exact check_of_frontier tree 0 t5_152root t5_152jobs t5_152frontier t5_152all
theorem t5_153choices : plan4070.choices=[0,5,5,3,10].map (options 5 3) := by rfl


theorem t5_153part0 : t5_153jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_153frontier : t5_153root.frontier 0=t5_153jobs := by rfl
theorem t5_153all : t5_153jobs.all (Job.check tree)=true := by
  simp only [t5_153jobs,List.all_append,List.all_nil,t5_153part0,Bool.and_self]
theorem t5_153checked : Checked tree [0,5,5,3,10] := by
  refine ⟨plan4070,valid4070,t5_153choices,?_⟩
  exact check_of_frontier tree 0 t5_153root t5_153jobs t5_153frontier t5_153all
theorem t5_154choices : plan4466.choices=[0,5,5,5,7].map (options 5 4) := by rfl


theorem t5_154part0 : t5_154jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_154frontier : t5_154root.frontier 0=t5_154jobs := by rfl
theorem t5_154all : t5_154jobs.all (Job.check tree)=true := by
  simp only [t5_154jobs,List.all_append,List.all_nil,t5_154part0,Bool.and_self]
theorem t5_154checked : Checked tree [0,5,5,5,7] := by
  refine ⟨plan4466,valid4466,t5_154choices,?_⟩
  exact check_of_frontier tree 0 t5_154root t5_154jobs t5_154frontier t5_154all
theorem t5_155choices : plan4467.choices=[0,5,5,6,6].map (options 5 4) := by rfl


theorem t5_155part0 : t5_155jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_155frontier : t5_155root.frontier 0=t5_155jobs := by rfl
theorem t5_155all : t5_155jobs.all (Job.check tree)=true := by
  simp only [t5_155jobs,List.all_append,List.all_nil,t5_155part0,Bool.and_self]
theorem t5_155checked : Checked tree [0,5,5,6,6] := by
  refine ⟨plan4467,valid4467,t5_155choices,?_⟩
  exact check_of_frontier tree 0 t5_155root t5_155jobs t5_155frontier t5_155all
theorem t5_156choices : plan4468.choices=[0,5,5,6,7].map (options 5 4) := by rfl


theorem t5_156part0 : t5_156jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_156frontier : t5_156root.frontier 0=t5_156jobs := by rfl
theorem t5_156all : t5_156jobs.all (Job.check tree)=true := by
  simp only [t5_156jobs,List.all_append,List.all_nil,t5_156part0,Bool.and_self]
theorem t5_156checked : Checked tree [0,5,5,6,7] := by
  refine ⟨plan4468,valid4468,t5_156choices,?_⟩
  exact check_of_frontier tree 0 t5_156root t5_156jobs t5_156frontier t5_156all
theorem t5_157choices : plan4469.choices=[0,5,5,6,10].map (options 5 4) := by rfl


theorem t5_157part0 : t5_157jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_157frontier : t5_157root.frontier 0=t5_157jobs := by rfl
theorem t5_157all : t5_157jobs.all (Job.check tree)=true := by
  simp only [t5_157jobs,List.all_append,List.all_nil,t5_157part0,Bool.and_self]
theorem t5_157checked : Checked tree [0,5,5,6,10] := by
  refine ⟨plan4469,valid4469,t5_157choices,?_⟩
  exact check_of_frontier tree 0 t5_157root t5_157jobs t5_157frontier t5_157all
theorem t5_158choices : plan4470.choices=[0,5,5,7,7].map (options 5 4) := by rfl


theorem t5_158part0 : t5_158jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_158frontier : t5_158root.frontier 0=t5_158jobs := by rfl
theorem t5_158all : t5_158jobs.all (Job.check tree)=true := by
  simp only [t5_158jobs,List.all_append,List.all_nil,t5_158part0,Bool.and_self]
theorem t5_158checked : Checked tree [0,5,5,7,7] := by
  refine ⟨plan4470,valid4470,t5_158choices,?_⟩
  exact check_of_frontier tree 0 t5_158root t5_158jobs t5_158frontier t5_158all
theorem t5_159choices : plan4471.choices=[0,5,5,9,7].map (options 5 4) := by rfl


theorem t5_159part0 : t5_159jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_159frontier : t5_159root.frontier 0=t5_159jobs := by rfl
theorem t5_159all : t5_159jobs.all (Job.check tree)=true := by
  simp only [t5_159jobs,List.all_append,List.all_nil,t5_159part0,Bool.and_self]
theorem t5_159checked : Checked tree [0,5,5,9,7] := by
  refine ⟨plan4471,valid4471,t5_159choices,?_⟩
  exact check_of_frontier tree 0 t5_159root t5_159jobs t5_159frontier t5_159all
theorem t5_160choices : plan4472.choices=[0,5,5,10,7].map (options 5 4) := by rfl


theorem t5_160part0 : t5_160jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_160frontier : t5_160root.frontier 0=t5_160jobs := by rfl
theorem t5_160all : t5_160jobs.all (Job.check tree)=true := by
  simp only [t5_160jobs,List.all_append,List.all_nil,t5_160part0,Bool.and_self]
theorem t5_160checked : Checked tree [0,5,5,10,7] := by
  refine ⟨plan4472,valid4472,t5_160choices,?_⟩
  exact check_of_frontier tree 0 t5_160root t5_160jobs t5_160frontier t5_160all
theorem t5_161choices : plan4473.choices=[0,5,5,10,10].map (options 5 4) := by rfl


theorem t5_161part0 : t5_161jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_161frontier : t5_161root.frontier 0=t5_161jobs := by rfl
theorem t5_161all : t5_161jobs.all (Job.check tree)=true := by
  simp only [t5_161jobs,List.all_append,List.all_nil,t5_161part0,Bool.and_self]
theorem t5_161checked : Checked tree [0,5,5,10,10] := by
  refine ⟨plan4473,valid4473,t5_161choices,?_⟩
  exact check_of_frontier tree 0 t5_161root t5_161jobs t5_161frontier t5_161all
theorem t5_162choices : plan4474.choices=[0,5,6,6,6].map (options 5 4) := by rfl


theorem t5_162part0 : t5_162jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_162frontier : t5_162root.frontier 0=t5_162jobs := by rfl
theorem t5_162all : t5_162jobs.all (Job.check tree)=true := by
  simp only [t5_162jobs,List.all_append,List.all_nil,t5_162part0,Bool.and_self]
theorem t5_162checked : Checked tree [0,5,6,6,6] := by
  refine ⟨plan4474,valid4474,t5_162choices,?_⟩
  exact check_of_frontier tree 0 t5_162root t5_162jobs t5_162frontier t5_162all
theorem t5_163choices : plan4475.choices=[0,5,6,6,7].map (options 5 4) := by rfl


theorem t5_163part0 : t5_163jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_163frontier : t5_163root.frontier 0=t5_163jobs := by rfl
theorem t5_163all : t5_163jobs.all (Job.check tree)=true := by
  simp only [t5_163jobs,List.all_append,List.all_nil,t5_163part0,Bool.and_self]
theorem t5_163checked : Checked tree [0,5,6,6,7] := by
  refine ⟨plan4475,valid4475,t5_163choices,?_⟩
  exact check_of_frontier tree 0 t5_163root t5_163jobs t5_163frontier t5_163all
theorem t5_164choices : plan4476.choices=[0,5,6,6,10].map (options 5 4) := by rfl


theorem t5_164part0 : t5_164jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_164frontier : t5_164root.frontier 0=t5_164jobs := by rfl
theorem t5_164all : t5_164jobs.all (Job.check tree)=true := by
  simp only [t5_164jobs,List.all_append,List.all_nil,t5_164part0,Bool.and_self]
theorem t5_164checked : Checked tree [0,5,6,6,10] := by
  refine ⟨plan4476,valid4476,t5_164choices,?_⟩
  exact check_of_frontier tree 0 t5_164root t5_164jobs t5_164frontier t5_164all
theorem t5_165choices : plan4477.choices=[0,5,6,7,7].map (options 5 4) := by rfl


theorem t5_165part0 : t5_165jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_165frontier : t5_165root.frontier 0=t5_165jobs := by rfl
theorem t5_165all : t5_165jobs.all (Job.check tree)=true := by
  simp only [t5_165jobs,List.all_append,List.all_nil,t5_165part0,Bool.and_self]
theorem t5_165checked : Checked tree [0,5,6,7,7] := by
  refine ⟨plan4477,valid4477,t5_165choices,?_⟩
  exact check_of_frontier tree 0 t5_165root t5_165jobs t5_165frontier t5_165all
theorem t5_166choices : plan4478.choices=[0,5,6,10,7].map (options 5 4) := by rfl


theorem t5_166part0 : t5_166jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_166frontier : t5_166root.frontier 0=t5_166jobs := by rfl
theorem t5_166all : t5_166jobs.all (Job.check tree)=true := by
  simp only [t5_166jobs,List.all_append,List.all_nil,t5_166part0,Bool.and_self]
theorem t5_166checked : Checked tree [0,5,6,10,7] := by
  refine ⟨plan4478,valid4478,t5_166choices,?_⟩
  exact check_of_frontier tree 0 t5_166root t5_166jobs t5_166frontier t5_166all
theorem t5_167choices : plan4479.choices=[0,5,6,10,10].map (options 5 4) := by rfl


theorem t5_167part0 : t5_167jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_167frontier : t5_167root.frontier 0=t5_167jobs := by rfl
theorem t5_167all : t5_167jobs.all (Job.check tree)=true := by
  simp only [t5_167jobs,List.all_append,List.all_nil,t5_167part0,Bool.and_self]
theorem t5_167checked : Checked tree [0,5,6,10,10] := by
  refine ⟨plan4479,valid4479,t5_167choices,?_⟩
  exact check_of_frontier tree 0 t5_167root t5_167jobs t5_167frontier t5_167all
theorem t5_168choices : plan4480.choices=[0,5,7,7,7].map (options 5 4) := by rfl


theorem t5_168part0 : t5_168jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_168frontier : t5_168root.frontier 0=t5_168jobs := by rfl
theorem t5_168all : t5_168jobs.all (Job.check tree)=true := by
  simp only [t5_168jobs,List.all_append,List.all_nil,t5_168part0,Bool.and_self]
theorem t5_168checked : Checked tree [0,5,7,7,7] := by
  refine ⟨plan4480,valid4480,t5_168choices,?_⟩
  exact check_of_frontier tree 0 t5_168root t5_168jobs t5_168frontier t5_168all
theorem t5_169choices : plan3804.choices=[0,5,9,3,3].map (options 5 2) := by rfl


theorem t5_169part0 : t5_169jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_169frontier : t5_169root.frontier 0=t5_169jobs := by rfl
theorem t5_169all : t5_169jobs.all (Job.check tree)=true := by
  simp only [t5_169jobs,List.all_append,List.all_nil,t5_169part0,Bool.and_self]
theorem t5_169checked : Checked tree [0,5,9,3,3] := by
  refine ⟨plan3804,valid3804,t5_169choices,?_⟩
  exact check_of_frontier tree 0 t5_169root t5_169jobs t5_169frontier t5_169all
theorem t5_170choices : plan4071.choices=[0,5,9,3,6].map (options 5 3) := by rfl


theorem t5_170part0 : t5_170jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_170frontier : t5_170root.frontier 0=t5_170jobs := by rfl
theorem t5_170all : t5_170jobs.all (Job.check tree)=true := by
  simp only [t5_170jobs,List.all_append,List.all_nil,t5_170part0,Bool.and_self]
theorem t5_170checked : Checked tree [0,5,9,3,6] := by
  refine ⟨plan4071,valid4071,t5_170choices,?_⟩
  exact check_of_frontier tree 0 t5_170root t5_170jobs t5_170frontier t5_170all
theorem t5_171choices : plan4072.choices=[0,5,9,3,7].map (options 5 3) := by rfl


theorem t5_171part0 : t5_171jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_171frontier : t5_171root.frontier 0=t5_171jobs := by rfl
theorem t5_171all : t5_171jobs.all (Job.check tree)=true := by
  simp only [t5_171jobs,List.all_append,List.all_nil,t5_171part0,Bool.and_self]
theorem t5_171checked : Checked tree [0,5,9,3,7] := by
  refine ⟨plan4072,valid4072,t5_171choices,?_⟩
  exact check_of_frontier tree 0 t5_171root t5_171jobs t5_171frontier t5_171all
theorem t5_172choices : plan4073.choices=[0,5,9,3,10].map (options 5 3) := by rfl


theorem t5_172part0 : t5_172jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_172frontier : t5_172root.frontier 0=t5_172jobs := by rfl
theorem t5_172all : t5_172jobs.all (Job.check tree)=true := by
  simp only [t5_172jobs,List.all_append,List.all_nil,t5_172part0,Bool.and_self]
theorem t5_172checked : Checked tree [0,5,9,3,10] := by
  refine ⟨plan4073,valid4073,t5_172choices,?_⟩
  exact check_of_frontier tree 0 t5_172root t5_172jobs t5_172frontier t5_172all
theorem t5_173choices : plan4481.choices=[0,5,9,6,6].map (options 5 4) := by rfl


theorem t5_173part0 : t5_173jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_173frontier : t5_173root.frontier 0=t5_173jobs := by rfl
theorem t5_173all : t5_173jobs.all (Job.check tree)=true := by
  simp only [t5_173jobs,List.all_append,List.all_nil,t5_173part0,Bool.and_self]
theorem t5_173checked : Checked tree [0,5,9,6,6] := by
  refine ⟨plan4481,valid4481,t5_173choices,?_⟩
  exact check_of_frontier tree 0 t5_173root t5_173jobs t5_173frontier t5_173all
theorem t5_174choices : plan4482.choices=[0,5,9,6,7].map (options 5 4) := by rfl


theorem t5_174part0 : t5_174jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_174frontier : t5_174root.frontier 0=t5_174jobs := by rfl
theorem t5_174all : t5_174jobs.all (Job.check tree)=true := by
  simp only [t5_174jobs,List.all_append,List.all_nil,t5_174part0,Bool.and_self]
theorem t5_174checked : Checked tree [0,5,9,6,7] := by
  refine ⟨plan4482,valid4482,t5_174choices,?_⟩
  exact check_of_frontier tree 0 t5_174root t5_174jobs t5_174frontier t5_174all
theorem t5_175choices : plan4483.choices=[0,5,9,6,10].map (options 5 4) := by rfl


theorem t5_175part0 : t5_175jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_175frontier : t5_175root.frontier 0=t5_175jobs := by rfl
theorem t5_175all : t5_175jobs.all (Job.check tree)=true := by
  simp only [t5_175jobs,List.all_append,List.all_nil,t5_175part0,Bool.and_self]
theorem t5_175checked : Checked tree [0,5,9,6,10] := by
  refine ⟨plan4483,valid4483,t5_175choices,?_⟩
  exact check_of_frontier tree 0 t5_175root t5_175jobs t5_175frontier t5_175all
theorem t5_176choices : plan4484.choices=[0,5,9,7,7].map (options 5 4) := by rfl


theorem t5_176part0 : t5_176jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_176frontier : t5_176root.frontier 0=t5_176jobs := by rfl
theorem t5_176all : t5_176jobs.all (Job.check tree)=true := by
  simp only [t5_176jobs,List.all_append,List.all_nil,t5_176part0,Bool.and_self]
theorem t5_176checked : Checked tree [0,5,9,7,7] := by
  refine ⟨plan4484,valid4484,t5_176choices,?_⟩
  exact check_of_frontier tree 0 t5_176root t5_176jobs t5_176frontier t5_176all
theorem t5_177choices : plan4485.choices=[0,5,9,9,7].map (options 5 4) := by rfl


theorem t5_177part0 : t5_177jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_177frontier : t5_177root.frontier 0=t5_177jobs := by rfl
theorem t5_177all : t5_177jobs.all (Job.check tree)=true := by
  simp only [t5_177jobs,List.all_append,List.all_nil,t5_177part0,Bool.and_self]
theorem t5_177checked : Checked tree [0,5,9,9,7] := by
  refine ⟨plan4485,valid4485,t5_177choices,?_⟩
  exact check_of_frontier tree 0 t5_177root t5_177jobs t5_177frontier t5_177all
theorem t5_178choices : plan4486.choices=[0,5,9,10,7].map (options 5 4) := by rfl


theorem t5_178part0 : t5_178jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_178frontier : t5_178root.frontier 0=t5_178jobs := by rfl
theorem t5_178all : t5_178jobs.all (Job.check tree)=true := by
  simp only [t5_178jobs,List.all_append,List.all_nil,t5_178part0,Bool.and_self]
theorem t5_178checked : Checked tree [0,5,9,10,7] := by
  refine ⟨plan4486,valid4486,t5_178choices,?_⟩
  exact check_of_frontier tree 0 t5_178root t5_178jobs t5_178frontier t5_178all
theorem t5_179choices : plan4487.choices=[0,5,9,10,10].map (options 5 4) := by rfl


theorem t5_179part0 : t5_179jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_179frontier : t5_179root.frontier 0=t5_179jobs := by rfl
theorem t5_179all : t5_179jobs.all (Job.check tree)=true := by
  simp only [t5_179jobs,List.all_append,List.all_nil,t5_179part0,Bool.and_self]
theorem t5_179checked : Checked tree [0,5,9,10,10] := by
  refine ⟨plan4487,valid4487,t5_179choices,?_⟩
  exact check_of_frontier tree 0 t5_179root t5_179jobs t5_179frontier t5_179all
theorem t5_180choices : plan4488.choices=[0,5,10,7,7].map (options 5 4) := by rfl


theorem t5_180part0 : t5_180jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_180frontier : t5_180root.frontier 0=t5_180jobs := by rfl
theorem t5_180all : t5_180jobs.all (Job.check tree)=true := by
  simp only [t5_180jobs,List.all_append,List.all_nil,t5_180part0,Bool.and_self]
theorem t5_180checked : Checked tree [0,5,10,7,7] := by
  refine ⟨plan4488,valid4488,t5_180choices,?_⟩
  exact check_of_frontier tree 0 t5_180root t5_180jobs t5_180frontier t5_180all
theorem t5_181choices : plan4489.choices=[0,5,10,10,7].map (options 5 4) := by rfl


theorem t5_181part0 : t5_181jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_181frontier : t5_181root.frontier 0=t5_181jobs := by rfl
theorem t5_181all : t5_181jobs.all (Job.check tree)=true := by
  simp only [t5_181jobs,List.all_append,List.all_nil,t5_181part0,Bool.and_self]
theorem t5_181checked : Checked tree [0,5,10,10,7] := by
  refine ⟨plan4489,valid4489,t5_181choices,?_⟩
  exact check_of_frontier tree 0 t5_181root t5_181jobs t5_181frontier t5_181all
theorem t5_182choices : plan4490.choices=[0,5,10,10,10].map (options 5 4) := by rfl


theorem t5_182part0 : t5_182jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_182frontier : t5_182root.frontier 0=t5_182jobs := by rfl
theorem t5_182all : t5_182jobs.all (Job.check tree)=true := by
  simp only [t5_182jobs,List.all_append,List.all_nil,t5_182part0,Bool.and_self]
theorem t5_182checked : Checked tree [0,5,10,10,10] := by
  refine ⟨plan4490,valid4490,t5_182choices,?_⟩
  exact check_of_frontier tree 0 t5_182root t5_182jobs t5_182frontier t5_182all
theorem t5_183choices : plan4491.choices=[0,6,6,6,6].map (options 5 4) := by rfl


theorem t5_183part0 : t5_183jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_183frontier : t5_183root.frontier 0=t5_183jobs := by rfl
theorem t5_183all : t5_183jobs.all (Job.check tree)=true := by
  simp only [t5_183jobs,List.all_append,List.all_nil,t5_183part0,Bool.and_self]
theorem t5_183checked : Checked tree [0,6,6,6,6] := by
  refine ⟨plan4491,valid4491,t5_183choices,?_⟩
  exact check_of_frontier tree 0 t5_183root t5_183jobs t5_183frontier t5_183all
theorem t5_184choices : plan4492.choices=[0,6,6,6,7].map (options 5 4) := by rfl


theorem t5_184part0 : t5_184jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_184frontier : t5_184root.frontier 0=t5_184jobs := by rfl
theorem t5_184all : t5_184jobs.all (Job.check tree)=true := by
  simp only [t5_184jobs,List.all_append,List.all_nil,t5_184part0,Bool.and_self]
theorem t5_184checked : Checked tree [0,6,6,6,7] := by
  refine ⟨plan4492,valid4492,t5_184choices,?_⟩
  exact check_of_frontier tree 0 t5_184root t5_184jobs t5_184frontier t5_184all
theorem t5_185choices : plan4493.choices=[0,6,6,6,10].map (options 5 4) := by rfl


theorem t5_185part0 : t5_185jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_185frontier : t5_185root.frontier 0=t5_185jobs := by rfl
theorem t5_185all : t5_185jobs.all (Job.check tree)=true := by
  simp only [t5_185jobs,List.all_append,List.all_nil,t5_185part0,Bool.and_self]
theorem t5_185checked : Checked tree [0,6,6,6,10] := by
  refine ⟨plan4493,valid4493,t5_185choices,?_⟩
  exact check_of_frontier tree 0 t5_185root t5_185jobs t5_185frontier t5_185all
theorem t5_186choices : plan4494.choices=[0,6,6,7,7].map (options 5 4) := by rfl


theorem t5_186part0 : t5_186jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_186frontier : t5_186root.frontier 0=t5_186jobs := by rfl
theorem t5_186all : t5_186jobs.all (Job.check tree)=true := by
  simp only [t5_186jobs,List.all_append,List.all_nil,t5_186part0,Bool.and_self]
theorem t5_186checked : Checked tree [0,6,6,7,7] := by
  refine ⟨plan4494,valid4494,t5_186choices,?_⟩
  exact check_of_frontier tree 0 t5_186root t5_186jobs t5_186frontier t5_186all
theorem t5_187choices : plan4495.choices=[0,6,6,10,7].map (options 5 4) := by rfl


theorem t5_187part0 : t5_187jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_187frontier : t5_187root.frontier 0=t5_187jobs := by rfl
theorem t5_187all : t5_187jobs.all (Job.check tree)=true := by
  simp only [t5_187jobs,List.all_append,List.all_nil,t5_187part0,Bool.and_self]
theorem t5_187checked : Checked tree [0,6,6,10,7] := by
  refine ⟨plan4495,valid4495,t5_187choices,?_⟩
  exact check_of_frontier tree 0 t5_187root t5_187jobs t5_187frontier t5_187all
theorem t5_188choices : plan4496.choices=[0,6,6,10,10].map (options 5 4) := by rfl


theorem t5_188part0 : t5_188jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_188frontier : t5_188root.frontier 0=t5_188jobs := by rfl
theorem t5_188all : t5_188jobs.all (Job.check tree)=true := by
  simp only [t5_188jobs,List.all_append,List.all_nil,t5_188part0,Bool.and_self]
theorem t5_188checked : Checked tree [0,6,6,10,10] := by
  refine ⟨plan4496,valid4496,t5_188choices,?_⟩
  exact check_of_frontier tree 0 t5_188root t5_188jobs t5_188frontier t5_188all
theorem t5_189choices : plan4497.choices=[0,6,7,7,7].map (options 5 4) := by rfl


theorem t5_189part0 : t5_189jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_189frontier : t5_189root.frontier 0=t5_189jobs := by rfl
theorem t5_189all : t5_189jobs.all (Job.check tree)=true := by
  simp only [t5_189jobs,List.all_append,List.all_nil,t5_189part0,Bool.and_self]
theorem t5_189checked : Checked tree [0,6,7,7,7] := by
  refine ⟨plan4497,valid4497,t5_189choices,?_⟩
  exact check_of_frontier tree 0 t5_189root t5_189jobs t5_189frontier t5_189all
theorem t5_190choices : plan4498.choices=[0,6,10,7,7].map (options 5 4) := by rfl


theorem t5_190part0 : t5_190jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_190frontier : t5_190root.frontier 0=t5_190jobs := by rfl
theorem t5_190all : t5_190jobs.all (Job.check tree)=true := by
  simp only [t5_190jobs,List.all_append,List.all_nil,t5_190part0,Bool.and_self]
theorem t5_190checked : Checked tree [0,6,10,7,7] := by
  refine ⟨plan4498,valid4498,t5_190choices,?_⟩
  exact check_of_frontier tree 0 t5_190root t5_190jobs t5_190frontier t5_190all
theorem t5_191choices : plan4499.choices=[0,6,10,10,7].map (options 5 4) := by rfl


theorem t5_191part0 : t5_191jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_191frontier : t5_191root.frontier 0=t5_191jobs := by rfl
theorem t5_191all : t5_191jobs.all (Job.check tree)=true := by
  simp only [t5_191jobs,List.all_append,List.all_nil,t5_191part0,Bool.and_self]
theorem t5_191checked : Checked tree [0,6,10,10,7] := by
  refine ⟨plan4499,valid4499,t5_191choices,?_⟩
  exact check_of_frontier tree 0 t5_191root t5_191jobs t5_191frontier t5_191all
theorem t5_192choices : plan4500.choices=[0,6,10,10,10].map (options 5 4) := by rfl


theorem t5_192part0 : t5_192jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_192frontier : t5_192root.frontier 0=t5_192jobs := by rfl
theorem t5_192all : t5_192jobs.all (Job.check tree)=true := by
  simp only [t5_192jobs,List.all_append,List.all_nil,t5_192part0,Bool.and_self]
theorem t5_192checked : Checked tree [0,6,10,10,10] := by
  refine ⟨plan4500,valid4500,t5_192choices,?_⟩
  exact check_of_frontier tree 0 t5_192root t5_192jobs t5_192frontier t5_192all
theorem t5_193choices : plan4501.choices=[0,7,7,7,7].map (options 5 4) := by rfl


theorem t5_193part0 : t5_193jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_193frontier : t5_193root.frontier 0=t5_193jobs := by rfl
theorem t5_193all : t5_193jobs.all (Job.check tree)=true := by
  simp only [t5_193jobs,List.all_append,List.all_nil,t5_193part0,Bool.and_self]
theorem t5_193checked : Checked tree [0,7,7,7,7] := by
  refine ⟨plan4501,valid4501,t5_193choices,?_⟩
  exact check_of_frontier tree 0 t5_193root t5_193jobs t5_193frontier t5_193all
theorem t5_194choices : plan3805.choices=[0,8,2,3,7].map (options 5 2) := by rfl


theorem t5_194part0 : t5_194jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_194frontier : t5_194root.frontier 0=t5_194jobs := by rfl
theorem t5_194all : t5_194jobs.all (Job.check tree)=true := by
  simp only [t5_194jobs,List.all_append,List.all_nil,t5_194part0,Bool.and_self]
theorem t5_194checked : Checked tree [0,8,2,3,7] := by
  refine ⟨plan3805,valid3805,t5_194choices,?_⟩
  exact check_of_frontier tree 0 t5_194root t5_194jobs t5_194frontier t5_194all
theorem t5_195choices : plan4074.choices=[0,8,2,6,7].map (options 5 3) := by rfl


theorem t5_195part0 : t5_195jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_195frontier : t5_195root.frontier 0=t5_195jobs := by rfl
theorem t5_195all : t5_195jobs.all (Job.check tree)=true := by
  simp only [t5_195jobs,List.all_append,List.all_nil,t5_195part0,Bool.and_self]
theorem t5_195checked : Checked tree [0,8,2,6,7] := by
  refine ⟨plan4074,valid4074,t5_195choices,?_⟩
  exact check_of_frontier tree 0 t5_195root t5_195jobs t5_195frontier t5_195all
theorem t5_196choices : plan4075.choices=[0,8,2,7,7].map (options 5 3) := by rfl


theorem t5_196part0 : t5_196jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_196frontier : t5_196root.frontier 0=t5_196jobs := by rfl
theorem t5_196all : t5_196jobs.all (Job.check tree)=true := by
  simp only [t5_196jobs,List.all_append,List.all_nil,t5_196part0,Bool.and_self]
theorem t5_196checked : Checked tree [0,8,2,7,7] := by
  refine ⟨plan4075,valid4075,t5_196choices,?_⟩
  exact check_of_frontier tree 0 t5_196root t5_196jobs t5_196frontier t5_196all
theorem t5_197choices : plan4076.choices=[0,8,2,10,7].map (options 5 3) := by rfl


theorem t5_197part0 : t5_197jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_197frontier : t5_197root.frontier 0=t5_197jobs := by rfl
theorem t5_197all : t5_197jobs.all (Job.check tree)=true := by
  simp only [t5_197jobs,List.all_append,List.all_nil,t5_197part0,Bool.and_self]
theorem t5_197checked : Checked tree [0,8,2,10,7] := by
  refine ⟨plan4076,valid4076,t5_197choices,?_⟩
  exact check_of_frontier tree 0 t5_197root t5_197jobs t5_197frontier t5_197all
theorem t5_198choices : plan3692.choices=[0,8,3,3,3].map (options 5 1) := by rfl


theorem t5_198part0 : t5_198jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_198frontier : t5_198root.frontier 0=t5_198jobs := by rfl
theorem t5_198all : t5_198jobs.all (Job.check tree)=true := by
  simp only [t5_198jobs,List.all_append,List.all_nil,t5_198part0,Bool.and_self]
theorem t5_198checked : Checked tree [0,8,3,3,3] := by
  refine ⟨plan3692,valid3692,t5_198choices,?_⟩
  exact check_of_frontier tree 0 t5_198root t5_198jobs t5_198frontier t5_198all
theorem t5_199choices : plan3806.choices=[0,8,3,3,6].map (options 5 2) := by rfl


theorem t5_199part0 : t5_199jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_199frontier : t5_199root.frontier 0=t5_199jobs := by rfl
theorem t5_199all : t5_199jobs.all (Job.check tree)=true := by
  simp only [t5_199jobs,List.all_append,List.all_nil,t5_199part0,Bool.and_self]
theorem t5_199checked : Checked tree [0,8,3,3,6] := by
  refine ⟨plan3806,valid3806,t5_199choices,?_⟩
  exact check_of_frontier tree 0 t5_199root t5_199jobs t5_199frontier t5_199all
theorem t5_200choices : plan3807.choices=[0,8,3,3,7].map (options 5 2) := by rfl


theorem t5_200part0 : t5_200jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_200frontier : t5_200root.frontier 0=t5_200jobs := by rfl
theorem t5_200all : t5_200jobs.all (Job.check tree)=true := by
  simp only [t5_200jobs,List.all_append,List.all_nil,t5_200part0,Bool.and_self]
theorem t5_200checked : Checked tree [0,8,3,3,7] := by
  refine ⟨plan3807,valid3807,t5_200choices,?_⟩
  exact check_of_frontier tree 0 t5_200root t5_200jobs t5_200frontier t5_200all
theorem t5_201choices : plan3808.choices=[0,8,3,3,10].map (options 5 2) := by rfl


theorem t5_201part0 : t5_201jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_201frontier : t5_201root.frontier 0=t5_201jobs := by rfl
theorem t5_201all : t5_201jobs.all (Job.check tree)=true := by
  simp only [t5_201jobs,List.all_append,List.all_nil,t5_201part0,Bool.and_self]
theorem t5_201checked : Checked tree [0,8,3,3,10] := by
  refine ⟨plan3808,valid3808,t5_201choices,?_⟩
  exact check_of_frontier tree 0 t5_201root t5_201jobs t5_201frontier t5_201all
theorem t5_202choices : plan4077.choices=[0,8,3,6,6].map (options 5 3) := by rfl


theorem t5_202part0 : t5_202jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_202frontier : t5_202root.frontier 0=t5_202jobs := by rfl
theorem t5_202all : t5_202jobs.all (Job.check tree)=true := by
  simp only [t5_202jobs,List.all_append,List.all_nil,t5_202part0,Bool.and_self]
theorem t5_202checked : Checked tree [0,8,3,6,6] := by
  refine ⟨plan4077,valid4077,t5_202choices,?_⟩
  exact check_of_frontier tree 0 t5_202root t5_202jobs t5_202frontier t5_202all
theorem t5_203choices : plan4078.choices=[0,8,3,6,7].map (options 5 3) := by rfl


theorem t5_203part0 : t5_203jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_203frontier : t5_203root.frontier 0=t5_203jobs := by rfl
theorem t5_203all : t5_203jobs.all (Job.check tree)=true := by
  simp only [t5_203jobs,List.all_append,List.all_nil,t5_203part0,Bool.and_self]
theorem t5_203checked : Checked tree [0,8,3,6,7] := by
  refine ⟨plan4078,valid4078,t5_203choices,?_⟩
  exact check_of_frontier tree 0 t5_203root t5_203jobs t5_203frontier t5_203all
theorem t5_204choices : plan4079.choices=[0,8,3,6,10].map (options 5 3) := by rfl


theorem t5_204part0 : t5_204jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_204frontier : t5_204root.frontier 0=t5_204jobs := by rfl
theorem t5_204all : t5_204jobs.all (Job.check tree)=true := by
  simp only [t5_204jobs,List.all_append,List.all_nil,t5_204part0,Bool.and_self]
theorem t5_204checked : Checked tree [0,8,3,6,10] := by
  refine ⟨plan4079,valid4079,t5_204choices,?_⟩
  exact check_of_frontier tree 0 t5_204root t5_204jobs t5_204frontier t5_204all
theorem t5_205choices : plan4080.choices=[0,8,3,7,7].map (options 5 3) := by rfl


theorem t5_205part0 : t5_205jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_205frontier : t5_205root.frontier 0=t5_205jobs := by rfl
theorem t5_205all : t5_205jobs.all (Job.check tree)=true := by
  simp only [t5_205jobs,List.all_append,List.all_nil,t5_205part0,Bool.and_self]
theorem t5_205checked : Checked tree [0,8,3,7,7] := by
  refine ⟨plan4080,valid4080,t5_205choices,?_⟩
  exact check_of_frontier tree 0 t5_205root t5_205jobs t5_205frontier t5_205all
theorem t5_206choices : plan4081.choices=[0,8,3,10,7].map (options 5 3) := by rfl


theorem t5_206part0 : t5_206jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_206frontier : t5_206root.frontier 0=t5_206jobs := by rfl
theorem t5_206all : t5_206jobs.all (Job.check tree)=true := by
  simp only [t5_206jobs,List.all_append,List.all_nil,t5_206part0,Bool.and_self]
theorem t5_206checked : Checked tree [0,8,3,10,7] := by
  refine ⟨plan4081,valid4081,t5_206choices,?_⟩
  exact check_of_frontier tree 0 t5_206root t5_206jobs t5_206frontier t5_206all
theorem t5_207choices : plan4082.choices=[0,8,3,10,10].map (options 5 3) := by rfl


theorem t5_207part0 : t5_207jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_207frontier : t5_207root.frontier 0=t5_207jobs := by rfl
theorem t5_207all : t5_207jobs.all (Job.check tree)=true := by
  simp only [t5_207jobs,List.all_append,List.all_nil,t5_207part0,Bool.and_self]
theorem t5_207checked : Checked tree [0,8,3,10,10] := by
  refine ⟨plan4082,valid4082,t5_207choices,?_⟩
  exact check_of_frontier tree 0 t5_207root t5_207jobs t5_207frontier t5_207all
theorem t5_208choices : plan4083.choices=[0,8,5,3,7].map (options 5 3) := by rfl


theorem t5_208part0 : t5_208jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_208frontier : t5_208root.frontier 0=t5_208jobs := by rfl
theorem t5_208all : t5_208jobs.all (Job.check tree)=true := by
  simp only [t5_208jobs,List.all_append,List.all_nil,t5_208part0,Bool.and_self]
theorem t5_208checked : Checked tree [0,8,5,3,7] := by
  refine ⟨plan4083,valid4083,t5_208choices,?_⟩
  exact check_of_frontier tree 0 t5_208root t5_208jobs t5_208frontier t5_208all
theorem t5_209choices : plan4502.choices=[0,8,5,6,7].map (options 5 4) := by rfl


theorem t5_209part0 : t5_209jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_209frontier : t5_209root.frontier 0=t5_209jobs := by rfl
theorem t5_209all : t5_209jobs.all (Job.check tree)=true := by
  simp only [t5_209jobs,List.all_append,List.all_nil,t5_209part0,Bool.and_self]
theorem t5_209checked : Checked tree [0,8,5,6,7] := by
  refine ⟨plan4502,valid4502,t5_209choices,?_⟩
  exact check_of_frontier tree 0 t5_209root t5_209jobs t5_209frontier t5_209all
theorem t5_210choices : plan4503.choices=[0,8,5,7,7].map (options 5 4) := by rfl


theorem t5_210part0 : t5_210jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_210frontier : t5_210root.frontier 0=t5_210jobs := by rfl
theorem t5_210all : t5_210jobs.all (Job.check tree)=true := by
  simp only [t5_210jobs,List.all_append,List.all_nil,t5_210part0,Bool.and_self]
theorem t5_210checked : Checked tree [0,8,5,7,7] := by
  refine ⟨plan4503,valid4503,t5_210choices,?_⟩
  exact check_of_frontier tree 0 t5_210root t5_210jobs t5_210frontier t5_210all
theorem t5_211choices : plan4504.choices=[0,8,5,10,7].map (options 5 4) := by rfl


theorem t5_211part0 : t5_211jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_211frontier : t5_211root.frontier 0=t5_211jobs := by rfl
theorem t5_211all : t5_211jobs.all (Job.check tree)=true := by
  simp only [t5_211jobs,List.all_append,List.all_nil,t5_211part0,Bool.and_self]
theorem t5_211checked : Checked tree [0,8,5,10,7] := by
  refine ⟨plan4504,valid4504,t5_211choices,?_⟩
  exact check_of_frontier tree 0 t5_211root t5_211jobs t5_211frontier t5_211all
theorem t5_212choices : plan4505.choices=[0,8,6,6,6].map (options 5 4) := by rfl


theorem t5_212part0 : t5_212jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_212frontier : t5_212root.frontier 0=t5_212jobs := by rfl
theorem t5_212all : t5_212jobs.all (Job.check tree)=true := by
  simp only [t5_212jobs,List.all_append,List.all_nil,t5_212part0,Bool.and_self]
theorem t5_212checked : Checked tree [0,8,6,6,6] := by
  refine ⟨plan4505,valid4505,t5_212choices,?_⟩
  exact check_of_frontier tree 0 t5_212root t5_212jobs t5_212frontier t5_212all
theorem t5_213choices : plan4506.choices=[0,8,6,6,7].map (options 5 4) := by rfl


theorem t5_213part0 : t5_213jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_213frontier : t5_213root.frontier 0=t5_213jobs := by rfl
theorem t5_213all : t5_213jobs.all (Job.check tree)=true := by
  simp only [t5_213jobs,List.all_append,List.all_nil,t5_213part0,Bool.and_self]
theorem t5_213checked : Checked tree [0,8,6,6,7] := by
  refine ⟨plan4506,valid4506,t5_213choices,?_⟩
  exact check_of_frontier tree 0 t5_213root t5_213jobs t5_213frontier t5_213all
theorem t5_214choices : plan4507.choices=[0,8,6,6,10].map (options 5 4) := by rfl


theorem t5_214part0 : t5_214jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_214frontier : t5_214root.frontier 0=t5_214jobs := by rfl
theorem t5_214all : t5_214jobs.all (Job.check tree)=true := by
  simp only [t5_214jobs,List.all_append,List.all_nil,t5_214part0,Bool.and_self]
theorem t5_214checked : Checked tree [0,8,6,6,10] := by
  refine ⟨plan4507,valid4507,t5_214choices,?_⟩
  exact check_of_frontier tree 0 t5_214root t5_214jobs t5_214frontier t5_214all
theorem t5_215choices : plan4508.choices=[0,8,6,7,7].map (options 5 4) := by rfl


theorem t5_215part0 : t5_215jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_215frontier : t5_215root.frontier 0=t5_215jobs := by rfl
theorem t5_215all : t5_215jobs.all (Job.check tree)=true := by
  simp only [t5_215jobs,List.all_append,List.all_nil,t5_215part0,Bool.and_self]
theorem t5_215checked : Checked tree [0,8,6,7,7] := by
  refine ⟨plan4508,valid4508,t5_215choices,?_⟩
  exact check_of_frontier tree 0 t5_215root t5_215jobs t5_215frontier t5_215all
theorem t5_216choices : plan4509.choices=[0,8,6,10,7].map (options 5 4) := by rfl


theorem t5_216part0 : t5_216jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_216frontier : t5_216root.frontier 0=t5_216jobs := by rfl
theorem t5_216all : t5_216jobs.all (Job.check tree)=true := by
  simp only [t5_216jobs,List.all_append,List.all_nil,t5_216part0,Bool.and_self]
theorem t5_216checked : Checked tree [0,8,6,10,7] := by
  refine ⟨plan4509,valid4509,t5_216choices,?_⟩
  exact check_of_frontier tree 0 t5_216root t5_216jobs t5_216frontier t5_216all
theorem t5_217choices : plan4510.choices=[0,8,6,10,10].map (options 5 4) := by rfl


theorem t5_217part0 : t5_217jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_217frontier : t5_217root.frontier 0=t5_217jobs := by rfl
theorem t5_217all : t5_217jobs.all (Job.check tree)=true := by
  simp only [t5_217jobs,List.all_append,List.all_nil,t5_217part0,Bool.and_self]
theorem t5_217checked : Checked tree [0,8,6,10,10] := by
  refine ⟨plan4510,valid4510,t5_217choices,?_⟩
  exact check_of_frontier tree 0 t5_217root t5_217jobs t5_217frontier t5_217all
theorem t5_218choices : plan4511.choices=[0,8,7,7,7].map (options 5 4) := by rfl


theorem t5_218part0 : t5_218jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_218frontier : t5_218root.frontier 0=t5_218jobs := by rfl
theorem t5_218all : t5_218jobs.all (Job.check tree)=true := by
  simp only [t5_218jobs,List.all_append,List.all_nil,t5_218part0,Bool.and_self]
theorem t5_218checked : Checked tree [0,8,7,7,7] := by
  refine ⟨plan4511,valid4511,t5_218choices,?_⟩
  exact check_of_frontier tree 0 t5_218root t5_218jobs t5_218frontier t5_218all
theorem t5_219choices : plan4084.choices=[0,8,9,3,7].map (options 5 3) := by rfl


theorem t5_219part0 : t5_219jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_219frontier : t5_219root.frontier 0=t5_219jobs := by rfl
theorem t5_219all : t5_219jobs.all (Job.check tree)=true := by
  simp only [t5_219jobs,List.all_append,List.all_nil,t5_219part0,Bool.and_self]
theorem t5_219checked : Checked tree [0,8,9,3,7] := by
  refine ⟨plan4084,valid4084,t5_219choices,?_⟩
  exact check_of_frontier tree 0 t5_219root t5_219jobs t5_219frontier t5_219all
theorem t5_220choices : plan4512.choices=[0,8,9,6,7].map (options 5 4) := by rfl


theorem t5_220part0 : t5_220jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_220frontier : t5_220root.frontier 0=t5_220jobs := by rfl
theorem t5_220all : t5_220jobs.all (Job.check tree)=true := by
  simp only [t5_220jobs,List.all_append,List.all_nil,t5_220part0,Bool.and_self]
theorem t5_220checked : Checked tree [0,8,9,6,7] := by
  refine ⟨plan4512,valid4512,t5_220choices,?_⟩
  exact check_of_frontier tree 0 t5_220root t5_220jobs t5_220frontier t5_220all
theorem t5_221choices : plan4513.choices=[0,8,9,7,7].map (options 5 4) := by rfl


theorem t5_221part0 : t5_221jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_221frontier : t5_221root.frontier 0=t5_221jobs := by rfl
theorem t5_221all : t5_221jobs.all (Job.check tree)=true := by
  simp only [t5_221jobs,List.all_append,List.all_nil,t5_221part0,Bool.and_self]
theorem t5_221checked : Checked tree [0,8,9,7,7] := by
  refine ⟨plan4513,valid4513,t5_221choices,?_⟩
  exact check_of_frontier tree 0 t5_221root t5_221jobs t5_221frontier t5_221all
theorem t5_222choices : plan4514.choices=[0,8,9,10,7].map (options 5 4) := by rfl


theorem t5_222part0 : t5_222jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_222frontier : t5_222root.frontier 0=t5_222jobs := by rfl
theorem t5_222all : t5_222jobs.all (Job.check tree)=true := by
  simp only [t5_222jobs,List.all_append,List.all_nil,t5_222part0,Bool.and_self]
theorem t5_222checked : Checked tree [0,8,9,10,7] := by
  refine ⟨plan4514,valid4514,t5_222choices,?_⟩
  exact check_of_frontier tree 0 t5_222root t5_222jobs t5_222frontier t5_222all
theorem t5_223choices : plan4515.choices=[0,8,10,7,7].map (options 5 4) := by rfl


theorem t5_223part0 : t5_223jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_223frontier : t5_223root.frontier 0=t5_223jobs := by rfl
theorem t5_223all : t5_223jobs.all (Job.check tree)=true := by
  simp only [t5_223jobs,List.all_append,List.all_nil,t5_223part0,Bool.and_self]
theorem t5_223checked : Checked tree [0,8,10,7,7] := by
  refine ⟨plan4515,valid4515,t5_223choices,?_⟩
  exact check_of_frontier tree 0 t5_223root t5_223jobs t5_223frontier t5_223all
theorem t5_224choices : plan4516.choices=[0,8,10,10,7].map (options 5 4) := by rfl


theorem t5_224part0 : t5_224jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_224frontier : t5_224root.frontier 0=t5_224jobs := by rfl
theorem t5_224all : t5_224jobs.all (Job.check tree)=true := by
  simp only [t5_224jobs,List.all_append,List.all_nil,t5_224part0,Bool.and_self]
theorem t5_224checked : Checked tree [0,8,10,10,7] := by
  refine ⟨plan4516,valid4516,t5_224choices,?_⟩
  exact check_of_frontier tree 0 t5_224root t5_224jobs t5_224frontier t5_224all
theorem t5_225choices : plan4517.choices=[0,8,10,10,10].map (options 5 4) := by rfl


theorem t5_225part0 : t5_225jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_225frontier : t5_225root.frontier 0=t5_225jobs := by rfl
theorem t5_225all : t5_225jobs.all (Job.check tree)=true := by
  simp only [t5_225jobs,List.all_append,List.all_nil,t5_225part0,Bool.and_self]
theorem t5_225checked : Checked tree [0,8,10,10,10] := by
  refine ⟨plan4517,valid4517,t5_225choices,?_⟩
  exact check_of_frontier tree 0 t5_225root t5_225jobs t5_225frontier t5_225all
theorem t5_226choices : plan3693.choices=[0,9,3,3,3].map (options 5 1) := by rfl


theorem t5_226part0 : t5_226jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_226frontier : t5_226root.frontier 0=t5_226jobs := by rfl
theorem t5_226all : t5_226jobs.all (Job.check tree)=true := by
  simp only [t5_226jobs,List.all_append,List.all_nil,t5_226part0,Bool.and_self]
theorem t5_226checked : Checked tree [0,9,3,3,3] := by
  refine ⟨plan3693,valid3693,t5_226choices,?_⟩
  exact check_of_frontier tree 0 t5_226root t5_226jobs t5_226frontier t5_226all
theorem t5_227choices : plan3809.choices=[0,9,3,3,6].map (options 5 2) := by rfl


theorem t5_227part0 : t5_227jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_227frontier : t5_227root.frontier 0=t5_227jobs := by rfl
theorem t5_227all : t5_227jobs.all (Job.check tree)=true := by
  simp only [t5_227jobs,List.all_append,List.all_nil,t5_227part0,Bool.and_self]
theorem t5_227checked : Checked tree [0,9,3,3,6] := by
  refine ⟨plan3809,valid3809,t5_227choices,?_⟩
  exact check_of_frontier tree 0 t5_227root t5_227jobs t5_227frontier t5_227all
theorem t5_228choices : plan3810.choices=[0,9,3,3,7].map (options 5 2) := by rfl


theorem t5_228part0 : t5_228jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_228frontier : t5_228root.frontier 0=t5_228jobs := by rfl
theorem t5_228all : t5_228jobs.all (Job.check tree)=true := by
  simp only [t5_228jobs,List.all_append,List.all_nil,t5_228part0,Bool.and_self]
theorem t5_228checked : Checked tree [0,9,3,3,7] := by
  refine ⟨plan3810,valid3810,t5_228choices,?_⟩
  exact check_of_frontier tree 0 t5_228root t5_228jobs t5_228frontier t5_228all
theorem t5_229choices : plan3811.choices=[0,9,3,3,10].map (options 5 2) := by rfl


theorem t5_229part0 : t5_229jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_229frontier : t5_229root.frontier 0=t5_229jobs := by rfl
theorem t5_229all : t5_229jobs.all (Job.check tree)=true := by
  simp only [t5_229jobs,List.all_append,List.all_nil,t5_229part0,Bool.and_self]
theorem t5_229checked : Checked tree [0,9,3,3,10] := by
  refine ⟨plan3811,valid3811,t5_229choices,?_⟩
  exact check_of_frontier tree 0 t5_229root t5_229jobs t5_229frontier t5_229all
theorem t5_230choices : plan4085.choices=[0,9,3,6,6].map (options 5 3) := by rfl


theorem t5_230part0 : t5_230jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_230frontier : t5_230root.frontier 0=t5_230jobs := by rfl
theorem t5_230all : t5_230jobs.all (Job.check tree)=true := by
  simp only [t5_230jobs,List.all_append,List.all_nil,t5_230part0,Bool.and_self]
theorem t5_230checked : Checked tree [0,9,3,6,6] := by
  refine ⟨plan4085,valid4085,t5_230choices,?_⟩
  exact check_of_frontier tree 0 t5_230root t5_230jobs t5_230frontier t5_230all
theorem t5_231choices : plan4086.choices=[0,9,3,6,7].map (options 5 3) := by rfl


theorem t5_231part0 : t5_231jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_231frontier : t5_231root.frontier 0=t5_231jobs := by rfl
theorem t5_231all : t5_231jobs.all (Job.check tree)=true := by
  simp only [t5_231jobs,List.all_append,List.all_nil,t5_231part0,Bool.and_self]
theorem t5_231checked : Checked tree [0,9,3,6,7] := by
  refine ⟨plan4086,valid4086,t5_231choices,?_⟩
  exact check_of_frontier tree 0 t5_231root t5_231jobs t5_231frontier t5_231all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks006 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_190checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_191checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_192checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_65checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_193checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_52checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_194checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_195checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_196checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_197checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_198checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_199checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_200checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_201checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_202checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_66checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_203checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_204checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_205checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_206checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_207checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_208checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_209checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_210checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_211checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_67checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_212checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_213checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_214checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_215checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_216checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_217checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_218checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_219checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_220checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_221checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_68checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_222checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_223checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_224checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_225checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_226checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_227checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_228checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_229checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_230checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_231checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_69checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_70checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_71checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_72checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_73checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_74checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_75checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_53checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_76checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_77checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_78checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_79checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_80checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_81checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_82checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_83checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_84checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_85checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_54checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_86checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_87checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_88checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_89checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_90checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_91checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_92checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_93checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_94checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_95checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_55checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_96checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_97checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_98checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_99checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_100checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_101checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_102checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_103checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_104checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_56checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_105checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_106checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_107checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_108checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_109checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_110checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_111checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_112checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_113checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_114checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_57checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_115checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_116checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_117checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_118checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_119checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_120checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_121checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_122checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_123checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_124checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_58checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_125checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_126checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_127checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_128checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_129checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_130checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_131checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_132checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_133checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_134checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_59checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_135checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_136checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_137checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_138checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_139checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_140checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_141checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_142checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_143checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_60checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_144checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_145checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_146checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_147checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_148checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_149checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_150checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_151checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_152checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_153checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_61checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_154checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_155checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_156checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_157checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_158checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_159checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_160checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_161checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_162checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_163checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_62checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_164checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_165checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_166checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_167checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_168checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_169checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_170checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_171checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_172checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_63checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_173checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_174checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_175checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_176checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_177checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_178checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_179checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_180checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_181checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_182checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_64checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_183checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_184checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_185checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_186checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_187checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_188checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_189checked⟩
