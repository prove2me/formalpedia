-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks011
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:47:09.691707+00:00
-- url     : https://prove2.me/submissions/7d5d68af-0db5-4924-b656-2adeeb1e8ee5

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks011
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
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















































































































































































theorem valid88 : plan88.Valid := valid_step _ _ _ valid0 (by decide +kernel)











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

theorem valid100 : plan100.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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









































































































































theorem valid453 : plan453.Valid := valid_step _ _ _ valid88 (by decide +kernel)

















theorem valid462 : plan462.Valid := valid_step _ _ _ valid94 (by decide +kernel)

theorem valid463 : plan463.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid464 : plan464.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid465 : plan465.Valid := valid_step _ _ _ valid99 (by decide +kernel)






























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









theorem valid485 : plan485.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid486 : plan486.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid487 : plan487.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid488 : plan488.Valid := valid_step _ _ _ valid100 (by decide +kernel)











theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid498 : plan498.Valid := valid_step _ _ _ valid100 (by decide +kernel)









theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)











theorem valid510 : plan510.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid511 : plan511.Valid := valid_step _ _ _ valid109 (by decide +kernel)



theorem valid513 : plan513.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)



theorem valid519 : plan519.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid520 : plan520.Valid := valid_step _ _ _ valid109 (by decide +kernel)



theorem valid522 : plan522.Valid := valid_step _ _ _ valid111 (by decide +kernel)

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































theorem valid1264 : plan1264.Valid := valid_step _ _ _ valid453 (by decide +kernel)



































































theorem valid1298 : plan1298.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1299 : plan1299.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1300 : plan1300.Valid := valid_step _ _ _ valid465 (by decide +kernel)















theorem valid1308 : plan1308.Valid := valid_step _ _ _ valid462 (by decide +kernel)













theorem valid1315 : plan1315.Valid := valid_step _ _ _ valid462 (by decide +kernel)















































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





















































































































theorem valid2555 : plan2555.Valid := valid_step _ _ _ valid1264 (by decide +kernel)










































































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



















































































































































theorem valid3722 : plan3722.Valid := valid_step _ _ _ valid2555 (by decide +kernel)












































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

theorem valid1353 : plan1353.Valid := valid_step _ _ _ valid488 (by decide +kernel)



















theorem valid1363 : plan1363.Valid := valid_step _ _ _ valid498 (by decide +kernel)



























theorem valid1377 : plan1377.Valid := valid_step _ _ _ valid486 (by decide +kernel)









theorem valid1382 : plan1382.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1383 : plan1383.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1384 : plan1384.Valid := valid_step _ _ _ valid487 (by decide +kernel)











































































theorem valid1422 : plan1422.Valid := valid_step _ _ _ valid510 (by decide +kernel)

theorem valid1423 : plan1423.Valid := valid_step _ _ _ valid511 (by decide +kernel)



theorem valid1425 : plan1425.Valid := valid_step _ _ _ valid513 (by decide +kernel)

theorem valid1426 : plan1426.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1427 : plan1427.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1428 : plan1428.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1429 : plan1429.Valid := valid_step _ _ _ valid517 (by decide +kernel)



theorem valid1431 : plan1431.Valid := valid_step _ _ _ valid519 (by decide +kernel)

theorem valid1432 : plan1432.Valid := valid_step _ _ _ valid520 (by decide +kernel)



theorem valid1434 : plan1434.Valid := valid_step _ _ _ valid522 (by decide +kernel)

theorem valid1435 : plan1435.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1436 : plan1436.Valid := valid_step _ _ _ valid524 (by decide +kernel)

theorem valid1437 : plan1437.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1438 : plan1438.Valid := valid_step _ _ _ valid515 (by decide +kernel)




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











































































































theorem valid2646 : plan2646.Valid := valid_step _ _ _ valid1315 (by decide +kernel)



theorem valid2648 : plan2648.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2649 : plan2649.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2650 : plan2650.Valid := valid_step _ _ _ valid1300 (by decide +kernel)

theorem valid2651 : plan2651.Valid := valid_step _ _ _ valid1308 (by decide +kernel)










































































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







































theorem valid2804 : plan2804.Valid := valid_step _ _ _ valid1377 (by decide +kernel)



theorem valid2806 : plan2806.Valid := valid_step _ _ _ valid1382 (by decide +kernel)

theorem valid2807 : plan2807.Valid := valid_step _ _ _ valid1383 (by decide +kernel)

theorem valid2808 : plan2808.Valid := valid_step _ _ _ valid1384 (by decide +kernel)







theorem valid2812 : plan2812.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2813 : plan2813.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2814 : plan2814.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2815 : plan2815.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2816 : plan2816.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2817 : plan2817.Valid := valid_step _ _ _ valid1344 (by decide +kernel)



theorem valid2819 : plan2819.Valid := valid_step _ _ _ valid1350 (by decide +kernel)

theorem valid2820 : plan2820.Valid := valid_step _ _ _ valid1351 (by decide +kernel)

theorem valid2821 : plan2821.Valid := valid_step _ _ _ valid1352 (by decide +kernel)

theorem valid2822 : plan2822.Valid := valid_step _ _ _ valid1353 (by decide +kernel)

theorem valid2823 : plan2823.Valid := valid_step _ _ _ valid1363 (by decide +kernel)


















































































































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



theorem valid1445 : plan1445.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1446 : plan1446.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1447 : plan1447.Valid := valid_step _ _ _ valid523 (by decide +kernel)







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





































































































































theorem valid2947 : plan2947.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid2948 : plan2948.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid2949 : plan2949.Valid := valid_step _ _ _ valid1443 (by decide +kernel)



theorem valid2951 : plan2951.Valid := valid_step _ _ _ valid1445 (by decide +kernel)

theorem valid2952 : plan2952.Valid := valid_step _ _ _ valid1446 (by decide +kernel)

theorem valid2953 : plan2953.Valid := valid_step _ _ _ valid1447 (by decide +kernel)







theorem valid2957 : plan2957.Valid := valid_step _ _ _ valid1451 (by decide +kernel)

theorem valid2958 : plan2958.Valid := valid_step _ _ _ valid1452 (by decide +kernel)

theorem valid2959 : plan2959.Valid := valid_step _ _ _ valid1453 (by decide +kernel)

theorem valid2960 : plan2960.Valid := valid_step _ _ _ valid1454 (by decide +kernel)

theorem valid2961 : plan2961.Valid := valid_step _ _ _ valid1457 (by decide +kernel)

theorem valid2962 : plan2962.Valid := valid_step _ _ _ valid1460 (by decide +kernel)

theorem valid2963 : plan2963.Valid := valid_step _ _ _ valid1461 (by decide +kernel)

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



theorem valid2978 : plan2978.Valid := valid_step _ _ _ valid1422 (by decide +kernel)

theorem valid2979 : plan2979.Valid := valid_step _ _ _ valid1423 (by decide +kernel)



theorem valid2981 : plan2981.Valid := valid_step _ _ _ valid1425 (by decide +kernel)

theorem valid2982 : plan2982.Valid := valid_step _ _ _ valid1426 (by decide +kernel)

theorem valid2983 : plan2983.Valid := valid_step _ _ _ valid1427 (by decide +kernel)

theorem valid2984 : plan2984.Valid := valid_step _ _ _ valid1428 (by decide +kernel)

theorem valid2985 : plan2985.Valid := valid_step _ _ _ valid1429 (by decide +kernel)



theorem valid2987 : plan2987.Valid := valid_step _ _ _ valid1431 (by decide +kernel)

theorem valid2988 : plan2988.Valid := valid_step _ _ _ valid1432 (by decide +kernel)



theorem valid2990 : plan2990.Valid := valid_step _ _ _ valid1434 (by decide +kernel)

theorem valid2991 : plan2991.Valid := valid_step _ _ _ valid1435 (by decide +kernel)

theorem valid2992 : plan2992.Valid := valid_step _ _ _ valid1436 (by decide +kernel)

theorem valid2993 : plan2993.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid2994 : plan2994.Valid := valid_step _ _ _ valid1438 (by decide +kernel)




























































































































































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



















































































theorem valid4554 : plan4554.Valid := valid_step _ _ _ valid2947 (by decide +kernel)

theorem valid4555 : plan4555.Valid := valid_step _ _ _ valid2948 (by decide +kernel)

theorem valid4556 : plan4556.Valid := valid_step _ _ _ valid2949 (by decide +kernel)

theorem valid4557 : plan4557.Valid := valid_step _ _ _ valid2951 (by decide +kernel)

theorem valid4558 : plan4558.Valid := valid_step _ _ _ valid2952 (by decide +kernel)

theorem valid4559 : plan4559.Valid := valid_step _ _ _ valid2953 (by decide +kernel)

theorem valid4560 : plan4560.Valid := valid_step _ _ _ valid2957 (by decide +kernel)

theorem valid4561 : plan4561.Valid := valid_step _ _ _ valid2958 (by decide +kernel)

theorem valid4562 : plan4562.Valid := valid_step _ _ _ valid2959 (by decide +kernel)

theorem valid4563 : plan4563.Valid := valid_step _ _ _ valid2960 (by decide +kernel)

theorem valid4564 : plan4564.Valid := valid_step _ _ _ valid2961 (by decide +kernel)

theorem valid4565 : plan4565.Valid := valid_step _ _ _ valid2962 (by decide +kernel)

theorem valid4566 : plan4566.Valid := valid_step _ _ _ valid2963 (by decide +kernel)

theorem valid4567 : plan4567.Valid := valid_step _ _ _ valid2964 (by decide +kernel)

theorem valid4568 : plan4568.Valid := valid_step _ _ _ valid2965 (by decide +kernel)

theorem valid4569 : plan4569.Valid := valid_step _ _ _ valid2966 (by decide +kernel)

theorem valid4570 : plan4570.Valid := valid_step _ _ _ valid2978 (by decide +kernel)

theorem valid4571 : plan4571.Valid := valid_step _ _ _ valid2979 (by decide +kernel)

theorem valid4572 : plan4572.Valid := valid_step _ _ _ valid2981 (by decide +kernel)

theorem valid4573 : plan4573.Valid := valid_step _ _ _ valid2982 (by decide +kernel)

theorem valid4574 : plan4574.Valid := valid_step _ _ _ valid2983 (by decide +kernel)

theorem valid4575 : plan4575.Valid := valid_step _ _ _ valid2984 (by decide +kernel)

theorem valid4576 : plan4576.Valid := valid_step _ _ _ valid2985 (by decide +kernel)

theorem valid4577 : plan4577.Valid := valid_step _ _ _ valid2987 (by decide +kernel)

theorem valid4578 : plan4578.Valid := valid_step _ _ _ valid2988 (by decide +kernel)

theorem valid4579 : plan4579.Valid := valid_step _ _ _ valid2990 (by decide +kernel)

theorem valid4580 : plan4580.Valid := valid_step _ _ _ valid2991 (by decide +kernel)

theorem valid4581 : plan4581.Valid := valid_step _ _ _ valid2992 (by decide +kernel)

theorem valid4582 : plan4582.Valid := valid_step _ _ _ valid2993 (by decide +kernel)

theorem valid4583 : plan4583.Valid := valid_step _ _ _ valid2994 (by decide +kernel)


















































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













































































theorem valid3879 : plan3879.Valid := valid_step _ _ _ valid2646 (by decide +kernel)

theorem valid3880 : plan3880.Valid := valid_step _ _ _ valid2648 (by decide +kernel)

theorem valid3881 : plan3881.Valid := valid_step _ _ _ valid2649 (by decide +kernel)

theorem valid3882 : plan3882.Valid := valid_step _ _ _ valid2650 (by decide +kernel)

theorem valid3883 : plan3883.Valid := valid_step _ _ _ valid2651 (by decide +kernel)










































































































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















































































































theorem valid4184 : plan4184.Valid := valid_step _ _ _ valid2804 (by decide +kernel)

theorem valid4185 : plan4185.Valid := valid_step _ _ _ valid2806 (by decide +kernel)

theorem valid4186 : plan4186.Valid := valid_step _ _ _ valid2807 (by decide +kernel)

theorem valid4187 : plan4187.Valid := valid_step _ _ _ valid2808 (by decide +kernel)

theorem valid4188 : plan4188.Valid := valid_step _ _ _ valid2812 (by decide +kernel)

theorem valid4189 : plan4189.Valid := valid_step _ _ _ valid2813 (by decide +kernel)

theorem valid4190 : plan4190.Valid := valid_step _ _ _ valid2814 (by decide +kernel)

theorem valid4191 : plan4191.Valid := valid_step _ _ _ valid2815 (by decide +kernel)

theorem valid4192 : plan4192.Valid := valid_step _ _ _ valid2816 (by decide +kernel)

theorem valid4193 : plan4193.Valid := valid_step _ _ _ valid2817 (by decide +kernel)

theorem valid4194 : plan4194.Valid := valid_step _ _ _ valid2819 (by decide +kernel)

theorem valid4195 : plan4195.Valid := valid_step _ _ _ valid2820 (by decide +kernel)

theorem valid4196 : plan4196.Valid := valid_step _ _ _ valid2821 (by decide +kernel)

theorem valid4197 : plan4197.Valid := valid_step _ _ _ valid2822 (by decide +kernel)

theorem valid4198 : plan4198.Valid := valid_step _ _ _ valid2823 (by decide +kernel)




















































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
theorem t5_466choices : plan4554.choices=[1,4,6,10,7].map (options 5 4) := by rfl


theorem t5_466part0 : t5_466jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_466frontier : t5_466root.frontier 0=t5_466jobs := by rfl
theorem t5_466all : t5_466jobs.all (Job.check tree)=true := by
  simp only [t5_466jobs,List.all_append,List.all_nil,t5_466part0,Bool.and_self]
theorem t5_466checked : Checked tree [1,4,6,10,7] := by
  refine ⟨plan4554,valid4554,t5_466choices,?_⟩
  exact check_of_frontier tree 0 t5_466root t5_466jobs t5_466frontier t5_466all
theorem t5_467choices : plan4555.choices=[1,4,6,10,10].map (options 5 4) := by rfl


theorem t5_467part0 : t5_467jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_467frontier : t5_467root.frontier 0=t5_467jobs := by rfl
theorem t5_467all : t5_467jobs.all (Job.check tree)=true := by
  simp only [t5_467jobs,List.all_append,List.all_nil,t5_467part0,Bool.and_self]
theorem t5_467checked : Checked tree [1,4,6,10,10] := by
  refine ⟨plan4555,valid4555,t5_467choices,?_⟩
  exact check_of_frontier tree 0 t5_467root t5_467jobs t5_467frontier t5_467all
theorem t5_468choices : plan4556.choices=[1,4,7,7,7].map (options 5 4) := by rfl


theorem t5_468part0 : t5_468jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_468frontier : t5_468root.frontier 0=t5_468jobs := by rfl
theorem t5_468all : t5_468jobs.all (Job.check tree)=true := by
  simp only [t5_468jobs,List.all_append,List.all_nil,t5_468part0,Bool.and_self]
theorem t5_468checked : Checked tree [1,4,7,7,7] := by
  refine ⟨plan4556,valid4556,t5_468choices,?_⟩
  exact check_of_frontier tree 0 t5_468root t5_468jobs t5_468frontier t5_468all
theorem t5_469choices : plan4184.choices=[1,4,8,3,7].map (options 5 3) := by rfl


theorem t5_469part0 : t5_469jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_469frontier : t5_469root.frontier 0=t5_469jobs := by rfl
theorem t5_469all : t5_469jobs.all (Job.check tree)=true := by
  simp only [t5_469jobs,List.all_append,List.all_nil,t5_469part0,Bool.and_self]
theorem t5_469checked : Checked tree [1,4,8,3,7] := by
  refine ⟨plan4184,valid4184,t5_469choices,?_⟩
  exact check_of_frontier tree 0 t5_469root t5_469jobs t5_469frontier t5_469all
theorem t5_470choices : plan4557.choices=[1,4,8,6,7].map (options 5 4) := by rfl


theorem t5_470part0 : t5_470jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_470frontier : t5_470root.frontier 0=t5_470jobs := by rfl
theorem t5_470all : t5_470jobs.all (Job.check tree)=true := by
  simp only [t5_470jobs,List.all_append,List.all_nil,t5_470part0,Bool.and_self]
theorem t5_470checked : Checked tree [1,4,8,6,7] := by
  refine ⟨plan4557,valid4557,t5_470choices,?_⟩
  exact check_of_frontier tree 0 t5_470root t5_470jobs t5_470frontier t5_470all
theorem t5_471choices : plan4558.choices=[1,4,8,7,7].map (options 5 4) := by rfl


theorem t5_471part0 : t5_471jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_471frontier : t5_471root.frontier 0=t5_471jobs := by rfl
theorem t5_471all : t5_471jobs.all (Job.check tree)=true := by
  simp only [t5_471jobs,List.all_append,List.all_nil,t5_471part0,Bool.and_self]
theorem t5_471checked : Checked tree [1,4,8,7,7] := by
  refine ⟨plan4558,valid4558,t5_471choices,?_⟩
  exact check_of_frontier tree 0 t5_471root t5_471jobs t5_471frontier t5_471all
theorem t5_472choices : plan4559.choices=[1,4,8,10,7].map (options 5 4) := by rfl


theorem t5_472part0 : t5_472jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_472frontier : t5_472root.frontier 0=t5_472jobs := by rfl
theorem t5_472all : t5_472jobs.all (Job.check tree)=true := by
  simp only [t5_472jobs,List.all_append,List.all_nil,t5_472part0,Bool.and_self]
theorem t5_472checked : Checked tree [1,4,8,10,7] := by
  refine ⟨plan4559,valid4559,t5_472choices,?_⟩
  exact check_of_frontier tree 0 t5_472root t5_472jobs t5_472frontier t5_472all
theorem t5_473choices : plan3879.choices=[1,4,9,3,3].map (options 5 2) := by rfl


theorem t5_473part0 : t5_473jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_473frontier : t5_473root.frontier 0=t5_473jobs := by rfl
theorem t5_473all : t5_473jobs.all (Job.check tree)=true := by
  simp only [t5_473jobs,List.all_append,List.all_nil,t5_473part0,Bool.and_self]
theorem t5_473checked : Checked tree [1,4,9,3,3] := by
  refine ⟨plan3879,valid3879,t5_473choices,?_⟩
  exact check_of_frontier tree 0 t5_473root t5_473jobs t5_473frontier t5_473all
theorem t5_474choices : plan4185.choices=[1,4,9,3,6].map (options 5 3) := by rfl


theorem t5_474part0 : t5_474jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_474frontier : t5_474root.frontier 0=t5_474jobs := by rfl
theorem t5_474all : t5_474jobs.all (Job.check tree)=true := by
  simp only [t5_474jobs,List.all_append,List.all_nil,t5_474part0,Bool.and_self]
theorem t5_474checked : Checked tree [1,4,9,3,6] := by
  refine ⟨plan4185,valid4185,t5_474choices,?_⟩
  exact check_of_frontier tree 0 t5_474root t5_474jobs t5_474frontier t5_474all
theorem t5_475choices : plan4186.choices=[1,4,9,3,7].map (options 5 3) := by rfl


theorem t5_475part0 : t5_475jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_475frontier : t5_475root.frontier 0=t5_475jobs := by rfl
theorem t5_475all : t5_475jobs.all (Job.check tree)=true := by
  simp only [t5_475jobs,List.all_append,List.all_nil,t5_475part0,Bool.and_self]
theorem t5_475checked : Checked tree [1,4,9,3,7] := by
  refine ⟨plan4186,valid4186,t5_475choices,?_⟩
  exact check_of_frontier tree 0 t5_475root t5_475jobs t5_475frontier t5_475all
theorem t5_476choices : plan4187.choices=[1,4,9,3,10].map (options 5 3) := by rfl


theorem t5_476part0 : t5_476jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_476frontier : t5_476root.frontier 0=t5_476jobs := by rfl
theorem t5_476all : t5_476jobs.all (Job.check tree)=true := by
  simp only [t5_476jobs,List.all_append,List.all_nil,t5_476part0,Bool.and_self]
theorem t5_476checked : Checked tree [1,4,9,3,10] := by
  refine ⟨plan4187,valid4187,t5_476choices,?_⟩
  exact check_of_frontier tree 0 t5_476root t5_476jobs t5_476frontier t5_476all
theorem t5_477choices : plan4560.choices=[1,4,9,6,6].map (options 5 4) := by rfl


theorem t5_477part0 : t5_477jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_477frontier : t5_477root.frontier 0=t5_477jobs := by rfl
theorem t5_477all : t5_477jobs.all (Job.check tree)=true := by
  simp only [t5_477jobs,List.all_append,List.all_nil,t5_477part0,Bool.and_self]
theorem t5_477checked : Checked tree [1,4,9,6,6] := by
  refine ⟨plan4560,valid4560,t5_477choices,?_⟩
  exact check_of_frontier tree 0 t5_477root t5_477jobs t5_477frontier t5_477all
theorem t5_478choices : plan4561.choices=[1,4,9,6,7].map (options 5 4) := by rfl


theorem t5_478part0 : t5_478jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_478frontier : t5_478root.frontier 0=t5_478jobs := by rfl
theorem t5_478all : t5_478jobs.all (Job.check tree)=true := by
  simp only [t5_478jobs,List.all_append,List.all_nil,t5_478part0,Bool.and_self]
theorem t5_478checked : Checked tree [1,4,9,6,7] := by
  refine ⟨plan4561,valid4561,t5_478choices,?_⟩
  exact check_of_frontier tree 0 t5_478root t5_478jobs t5_478frontier t5_478all
theorem t5_479choices : plan4562.choices=[1,4,9,6,10].map (options 5 4) := by rfl


theorem t5_479part0 : t5_479jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_479frontier : t5_479root.frontier 0=t5_479jobs := by rfl
theorem t5_479all : t5_479jobs.all (Job.check tree)=true := by
  simp only [t5_479jobs,List.all_append,List.all_nil,t5_479part0,Bool.and_self]
theorem t5_479checked : Checked tree [1,4,9,6,10] := by
  refine ⟨plan4562,valid4562,t5_479choices,?_⟩
  exact check_of_frontier tree 0 t5_479root t5_479jobs t5_479frontier t5_479all
theorem t5_480choices : plan4563.choices=[1,4,9,7,7].map (options 5 4) := by rfl


theorem t5_480part0 : t5_480jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_480frontier : t5_480root.frontier 0=t5_480jobs := by rfl
theorem t5_480all : t5_480jobs.all (Job.check tree)=true := by
  simp only [t5_480jobs,List.all_append,List.all_nil,t5_480part0,Bool.and_self]
theorem t5_480checked : Checked tree [1,4,9,7,7] := by
  refine ⟨plan4563,valid4563,t5_480choices,?_⟩
  exact check_of_frontier tree 0 t5_480root t5_480jobs t5_480frontier t5_480all
theorem t5_481choices : plan4564.choices=[1,4,9,9,7].map (options 5 4) := by rfl


theorem t5_481part0 : t5_481jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_481frontier : t5_481root.frontier 0=t5_481jobs := by rfl
theorem t5_481all : t5_481jobs.all (Job.check tree)=true := by
  simp only [t5_481jobs,List.all_append,List.all_nil,t5_481part0,Bool.and_self]
theorem t5_481checked : Checked tree [1,4,9,9,7] := by
  refine ⟨plan4564,valid4564,t5_481choices,?_⟩
  exact check_of_frontier tree 0 t5_481root t5_481jobs t5_481frontier t5_481all
theorem t5_482choices : plan4565.choices=[1,4,9,10,7].map (options 5 4) := by rfl


theorem t5_482part0 : t5_482jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_482frontier : t5_482root.frontier 0=t5_482jobs := by rfl
theorem t5_482all : t5_482jobs.all (Job.check tree)=true := by
  simp only [t5_482jobs,List.all_append,List.all_nil,t5_482part0,Bool.and_self]
theorem t5_482checked : Checked tree [1,4,9,10,7] := by
  refine ⟨plan4565,valid4565,t5_482choices,?_⟩
  exact check_of_frontier tree 0 t5_482root t5_482jobs t5_482frontier t5_482all
theorem t5_483choices : plan4566.choices=[1,4,9,10,10].map (options 5 4) := by rfl


theorem t5_483part0 : t5_483jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_483frontier : t5_483root.frontier 0=t5_483jobs := by rfl
theorem t5_483all : t5_483jobs.all (Job.check tree)=true := by
  simp only [t5_483jobs,List.all_append,List.all_nil,t5_483part0,Bool.and_self]
theorem t5_483checked : Checked tree [1,4,9,10,10] := by
  refine ⟨plan4566,valid4566,t5_483choices,?_⟩
  exact check_of_frontier tree 0 t5_483root t5_483jobs t5_483frontier t5_483all
theorem t5_484choices : plan4567.choices=[1,4,10,7,7].map (options 5 4) := by rfl


theorem t5_484part0 : t5_484jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_484frontier : t5_484root.frontier 0=t5_484jobs := by rfl
theorem t5_484all : t5_484jobs.all (Job.check tree)=true := by
  simp only [t5_484jobs,List.all_append,List.all_nil,t5_484part0,Bool.and_self]
theorem t5_484checked : Checked tree [1,4,10,7,7] := by
  refine ⟨plan4567,valid4567,t5_484choices,?_⟩
  exact check_of_frontier tree 0 t5_484root t5_484jobs t5_484frontier t5_484all
theorem t5_485choices : plan4568.choices=[1,4,10,10,7].map (options 5 4) := by rfl


theorem t5_485part0 : t5_485jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_485frontier : t5_485root.frontier 0=t5_485jobs := by rfl
theorem t5_485all : t5_485jobs.all (Job.check tree)=true := by
  simp only [t5_485jobs,List.all_append,List.all_nil,t5_485part0,Bool.and_self]
theorem t5_485checked : Checked tree [1,4,10,10,7] := by
  refine ⟨plan4568,valid4568,t5_485choices,?_⟩
  exact check_of_frontier tree 0 t5_485root t5_485jobs t5_485frontier t5_485all
theorem t5_486choices : plan4569.choices=[1,4,10,10,10].map (options 5 4) := by rfl


theorem t5_486part0 : t5_486jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_486frontier : t5_486root.frontier 0=t5_486jobs := by rfl
theorem t5_486all : t5_486jobs.all (Job.check tree)=true := by
  simp only [t5_486jobs,List.all_append,List.all_nil,t5_486part0,Bool.and_self]
theorem t5_486checked : Checked tree [1,4,10,10,10] := by
  refine ⟨plan4569,valid4569,t5_486choices,?_⟩
  exact check_of_frontier tree 0 t5_486root t5_486jobs t5_486frontier t5_486all
theorem t5_487choices : plan3722.choices=[1,5,3,3,3].map (options 5 1) := by rfl


theorem t5_487part0 : t5_487jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_487frontier : t5_487root.frontier 0=t5_487jobs := by rfl
theorem t5_487all : t5_487jobs.all (Job.check tree)=true := by
  simp only [t5_487jobs,List.all_append,List.all_nil,t5_487part0,Bool.and_self]
theorem t5_487checked : Checked tree [1,5,3,3,3] := by
  refine ⟨plan3722,valid3722,t5_487choices,?_⟩
  exact check_of_frontier tree 0 t5_487root t5_487jobs t5_487frontier t5_487all
theorem t5_488choices : plan3880.choices=[1,5,3,3,6].map (options 5 2) := by rfl


theorem t5_488part0 : t5_488jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_488frontier : t5_488root.frontier 0=t5_488jobs := by rfl
theorem t5_488all : t5_488jobs.all (Job.check tree)=true := by
  simp only [t5_488jobs,List.all_append,List.all_nil,t5_488part0,Bool.and_self]
theorem t5_488checked : Checked tree [1,5,3,3,6] := by
  refine ⟨plan3880,valid3880,t5_488choices,?_⟩
  exact check_of_frontier tree 0 t5_488root t5_488jobs t5_488frontier t5_488all
theorem t5_489choices : plan3881.choices=[1,5,3,3,7].map (options 5 2) := by rfl


theorem t5_489part0 : t5_489jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_489frontier : t5_489root.frontier 0=t5_489jobs := by rfl
theorem t5_489all : t5_489jobs.all (Job.check tree)=true := by
  simp only [t5_489jobs,List.all_append,List.all_nil,t5_489part0,Bool.and_self]
theorem t5_489checked : Checked tree [1,5,3,3,7] := by
  refine ⟨plan3881,valid3881,t5_489choices,?_⟩
  exact check_of_frontier tree 0 t5_489root t5_489jobs t5_489frontier t5_489all
theorem t5_490choices : plan3882.choices=[1,5,3,3,10].map (options 5 2) := by rfl


theorem t5_490part0 : t5_490jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_490frontier : t5_490root.frontier 0=t5_490jobs := by rfl
theorem t5_490all : t5_490jobs.all (Job.check tree)=true := by
  simp only [t5_490jobs,List.all_append,List.all_nil,t5_490part0,Bool.and_self]
theorem t5_490checked : Checked tree [1,5,3,3,10] := by
  refine ⟨plan3882,valid3882,t5_490choices,?_⟩
  exact check_of_frontier tree 0 t5_490root t5_490jobs t5_490frontier t5_490all
theorem t5_491choices : plan4188.choices=[1,5,3,6,6].map (options 5 3) := by rfl


theorem t5_491part0 : t5_491jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_491frontier : t5_491root.frontier 0=t5_491jobs := by rfl
theorem t5_491all : t5_491jobs.all (Job.check tree)=true := by
  simp only [t5_491jobs,List.all_append,List.all_nil,t5_491part0,Bool.and_self]
theorem t5_491checked : Checked tree [1,5,3,6,6] := by
  refine ⟨plan4188,valid4188,t5_491choices,?_⟩
  exact check_of_frontier tree 0 t5_491root t5_491jobs t5_491frontier t5_491all
theorem t5_492choices : plan4189.choices=[1,5,3,6,7].map (options 5 3) := by rfl


theorem t5_492part0 : t5_492jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_492part1 : t5_492jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_492frontier : t5_492root.frontier 1=t5_492jobs := by rfl
theorem t5_492all : t5_492jobs.all (Job.check tree)=true := by
  simp only [t5_492jobs,List.all_append,List.all_nil,t5_492part0,t5_492part1,Bool.and_self]
theorem t5_492checked : Checked tree [1,5,3,6,7] := by
  refine ⟨plan4189,valid4189,t5_492choices,?_⟩
  exact check_of_frontier tree 1 t5_492root t5_492jobs t5_492frontier t5_492all
theorem t5_493choices : plan4190.choices=[1,5,3,6,10].map (options 5 3) := by rfl


theorem t5_493part0 : t5_493jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_493part1 : t5_493jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_493frontier : t5_493root.frontier 1=t5_493jobs := by rfl
theorem t5_493all : t5_493jobs.all (Job.check tree)=true := by
  simp only [t5_493jobs,List.all_append,List.all_nil,t5_493part0,t5_493part1,Bool.and_self]
theorem t5_493checked : Checked tree [1,5,3,6,10] := by
  refine ⟨plan4190,valid4190,t5_493choices,?_⟩
  exact check_of_frontier tree 1 t5_493root t5_493jobs t5_493frontier t5_493all
theorem t5_494choices : plan4191.choices=[1,5,3,7,7].map (options 5 3) := by rfl


theorem t5_494part0 : t5_494jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_494part1 : t5_494jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_494frontier : t5_494root.frontier 1=t5_494jobs := by rfl
theorem t5_494all : t5_494jobs.all (Job.check tree)=true := by
  simp only [t5_494jobs,List.all_append,List.all_nil,t5_494part0,t5_494part1,Bool.and_self]
theorem t5_494checked : Checked tree [1,5,3,7,7] := by
  refine ⟨plan4191,valid4191,t5_494choices,?_⟩
  exact check_of_frontier tree 1 t5_494root t5_494jobs t5_494frontier t5_494all
theorem t5_495choices : plan4192.choices=[1,5,3,10,7].map (options 5 3) := by rfl


theorem t5_495part0 : t5_495jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_495part1 : t5_495jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_495frontier : t5_495root.frontier 1=t5_495jobs := by rfl
theorem t5_495all : t5_495jobs.all (Job.check tree)=true := by
  simp only [t5_495jobs,List.all_append,List.all_nil,t5_495part0,t5_495part1,Bool.and_self]
theorem t5_495checked : Checked tree [1,5,3,10,7] := by
  refine ⟨plan4192,valid4192,t5_495choices,?_⟩
  exact check_of_frontier tree 1 t5_495root t5_495jobs t5_495frontier t5_495all
theorem t5_496choices : plan4193.choices=[1,5,3,10,10].map (options 5 3) := by rfl


theorem t5_496part0 : t5_496jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_496frontier : t5_496root.frontier 0=t5_496jobs := by rfl
theorem t5_496all : t5_496jobs.all (Job.check tree)=true := by
  simp only [t5_496jobs,List.all_append,List.all_nil,t5_496part0,Bool.and_self]
theorem t5_496checked : Checked tree [1,5,3,10,10] := by
  refine ⟨plan4193,valid4193,t5_496choices,?_⟩
  exact check_of_frontier tree 0 t5_496root t5_496jobs t5_496frontier t5_496all
theorem t5_497choices : plan3883.choices=[1,5,5,3,3].map (options 5 2) := by rfl


theorem t5_497part0 : t5_497jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_497frontier : t5_497root.frontier 0=t5_497jobs := by rfl
theorem t5_497all : t5_497jobs.all (Job.check tree)=true := by
  simp only [t5_497jobs,List.all_append,List.all_nil,t5_497part0,Bool.and_self]
theorem t5_497checked : Checked tree [1,5,5,3,3] := by
  refine ⟨plan3883,valid3883,t5_497choices,?_⟩
  exact check_of_frontier tree 0 t5_497root t5_497jobs t5_497frontier t5_497all
theorem t5_498choices : plan4194.choices=[1,5,5,3,6].map (options 5 3) := by rfl


theorem t5_498part0 : t5_498jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_498frontier : t5_498root.frontier 0=t5_498jobs := by rfl
theorem t5_498all : t5_498jobs.all (Job.check tree)=true := by
  simp only [t5_498jobs,List.all_append,List.all_nil,t5_498part0,Bool.and_self]
theorem t5_498checked : Checked tree [1,5,5,3,6] := by
  refine ⟨plan4194,valid4194,t5_498choices,?_⟩
  exact check_of_frontier tree 0 t5_498root t5_498jobs t5_498frontier t5_498all
theorem t5_499choices : plan4195.choices=[1,5,5,3,7].map (options 5 3) := by rfl


theorem t5_499part0 : t5_499jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_499frontier : t5_499root.frontier 0=t5_499jobs := by rfl
theorem t5_499all : t5_499jobs.all (Job.check tree)=true := by
  simp only [t5_499jobs,List.all_append,List.all_nil,t5_499part0,Bool.and_self]
theorem t5_499checked : Checked tree [1,5,5,3,7] := by
  refine ⟨plan4195,valid4195,t5_499choices,?_⟩
  exact check_of_frontier tree 0 t5_499root t5_499jobs t5_499frontier t5_499all
theorem t5_500choices : plan4196.choices=[1,5,5,3,10].map (options 5 3) := by rfl


theorem t5_500part0 : t5_500jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_500frontier : t5_500root.frontier 0=t5_500jobs := by rfl
theorem t5_500all : t5_500jobs.all (Job.check tree)=true := by
  simp only [t5_500jobs,List.all_append,List.all_nil,t5_500part0,Bool.and_self]
theorem t5_500checked : Checked tree [1,5,5,3,10] := by
  refine ⟨plan4196,valid4196,t5_500choices,?_⟩
  exact check_of_frontier tree 0 t5_500root t5_500jobs t5_500frontier t5_500all
theorem t5_501choices : plan4197.choices=[1,5,5,5,3].map (options 5 3) := by rfl


theorem t5_501part0 : t5_501jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_501frontier : t5_501root.frontier 0=t5_501jobs := by rfl
theorem t5_501all : t5_501jobs.all (Job.check tree)=true := by
  simp only [t5_501jobs,List.all_append,List.all_nil,t5_501part0,Bool.and_self]
theorem t5_501checked : Checked tree [1,5,5,5,3] := by
  refine ⟨plan4197,valid4197,t5_501choices,?_⟩
  exact check_of_frontier tree 0 t5_501root t5_501jobs t5_501frontier t5_501all
theorem t5_502choices : plan4570.choices=[1,5,5,5,6].map (options 5 4) := by rfl


theorem t5_502part0 : t5_502jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_502frontier : t5_502root.frontier 0=t5_502jobs := by rfl
theorem t5_502all : t5_502jobs.all (Job.check tree)=true := by
  simp only [t5_502jobs,List.all_append,List.all_nil,t5_502part0,Bool.and_self]
theorem t5_502checked : Checked tree [1,5,5,5,6] := by
  refine ⟨plan4570,valid4570,t5_502choices,?_⟩
  exact check_of_frontier tree 0 t5_502root t5_502jobs t5_502frontier t5_502all
theorem t5_503choices : plan4571.choices=[1,5,5,5,7].map (options 5 4) := by rfl


theorem t5_503part0 : t5_503jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_503frontier : t5_503root.frontier 0=t5_503jobs := by rfl
theorem t5_503all : t5_503jobs.all (Job.check tree)=true := by
  simp only [t5_503jobs,List.all_append,List.all_nil,t5_503part0,Bool.and_self]
theorem t5_503checked : Checked tree [1,5,5,5,7] := by
  refine ⟨plan4571,valid4571,t5_503choices,?_⟩
  exact check_of_frontier tree 0 t5_503root t5_503jobs t5_503frontier t5_503all
theorem t5_504choices : plan4572.choices=[1,5,5,5,10].map (options 5 4) := by rfl


theorem t5_504part0 : t5_504jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_504frontier : t5_504root.frontier 0=t5_504jobs := by rfl
theorem t5_504all : t5_504jobs.all (Job.check tree)=true := by
  simp only [t5_504jobs,List.all_append,List.all_nil,t5_504part0,Bool.and_self]
theorem t5_504checked : Checked tree [1,5,5,5,10] := by
  refine ⟨plan4572,valid4572,t5_504choices,?_⟩
  exact check_of_frontier tree 0 t5_504root t5_504jobs t5_504frontier t5_504all
theorem t5_505choices : plan4573.choices=[1,5,5,6,6].map (options 5 4) := by rfl


theorem t5_505part0 : t5_505jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_505frontier : t5_505root.frontier 0=t5_505jobs := by rfl
theorem t5_505all : t5_505jobs.all (Job.check tree)=true := by
  simp only [t5_505jobs,List.all_append,List.all_nil,t5_505part0,Bool.and_self]
theorem t5_505checked : Checked tree [1,5,5,6,6] := by
  refine ⟨plan4573,valid4573,t5_505choices,?_⟩
  exact check_of_frontier tree 0 t5_505root t5_505jobs t5_505frontier t5_505all
theorem t5_506choices : plan4574.choices=[1,5,5,6,7].map (options 5 4) := by rfl


theorem t5_506part0 : t5_506jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_506frontier : t5_506root.frontier 0=t5_506jobs := by rfl
theorem t5_506all : t5_506jobs.all (Job.check tree)=true := by
  simp only [t5_506jobs,List.all_append,List.all_nil,t5_506part0,Bool.and_self]
theorem t5_506checked : Checked tree [1,5,5,6,7] := by
  refine ⟨plan4574,valid4574,t5_506choices,?_⟩
  exact check_of_frontier tree 0 t5_506root t5_506jobs t5_506frontier t5_506all
theorem t5_507choices : plan4575.choices=[1,5,5,6,10].map (options 5 4) := by rfl


theorem t5_507part0 : t5_507jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_507frontier : t5_507root.frontier 0=t5_507jobs := by rfl
theorem t5_507all : t5_507jobs.all (Job.check tree)=true := by
  simp only [t5_507jobs,List.all_append,List.all_nil,t5_507part0,Bool.and_self]
theorem t5_507checked : Checked tree [1,5,5,6,10] := by
  refine ⟨plan4575,valid4575,t5_507choices,?_⟩
  exact check_of_frontier tree 0 t5_507root t5_507jobs t5_507frontier t5_507all
theorem t5_508choices : plan4576.choices=[1,5,5,7,7].map (options 5 4) := by rfl


theorem t5_508part0 : t5_508jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_508frontier : t5_508root.frontier 0=t5_508jobs := by rfl
theorem t5_508all : t5_508jobs.all (Job.check tree)=true := by
  simp only [t5_508jobs,List.all_append,List.all_nil,t5_508part0,Bool.and_self]
theorem t5_508checked : Checked tree [1,5,5,7,7] := by
  refine ⟨plan4576,valid4576,t5_508choices,?_⟩
  exact check_of_frontier tree 0 t5_508root t5_508jobs t5_508frontier t5_508all
theorem t5_509choices : plan4198.choices=[1,5,5,9,3].map (options 5 3) := by rfl


theorem t5_509part0 : t5_509jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_509frontier : t5_509root.frontier 0=t5_509jobs := by rfl
theorem t5_509all : t5_509jobs.all (Job.check tree)=true := by
  simp only [t5_509jobs,List.all_append,List.all_nil,t5_509part0,Bool.and_self]
theorem t5_509checked : Checked tree [1,5,5,9,3] := by
  refine ⟨plan4198,valid4198,t5_509choices,?_⟩
  exact check_of_frontier tree 0 t5_509root t5_509jobs t5_509frontier t5_509all
theorem t5_510choices : plan4577.choices=[1,5,5,9,6].map (options 5 4) := by rfl


theorem t5_510part0 : t5_510jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_510frontier : t5_510root.frontier 0=t5_510jobs := by rfl
theorem t5_510all : t5_510jobs.all (Job.check tree)=true := by
  simp only [t5_510jobs,List.all_append,List.all_nil,t5_510part0,Bool.and_self]
theorem t5_510checked : Checked tree [1,5,5,9,6] := by
  refine ⟨plan4577,valid4577,t5_510choices,?_⟩
  exact check_of_frontier tree 0 t5_510root t5_510jobs t5_510frontier t5_510all
theorem t5_511choices : plan4578.choices=[1,5,5,9,7].map (options 5 4) := by rfl


theorem t5_511part0 : t5_511jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_511frontier : t5_511root.frontier 0=t5_511jobs := by rfl
theorem t5_511all : t5_511jobs.all (Job.check tree)=true := by
  simp only [t5_511jobs,List.all_append,List.all_nil,t5_511part0,Bool.and_self]
theorem t5_511checked : Checked tree [1,5,5,9,7] := by
  refine ⟨plan4578,valid4578,t5_511choices,?_⟩
  exact check_of_frontier tree 0 t5_511root t5_511jobs t5_511frontier t5_511all
theorem t5_512choices : plan4579.choices=[1,5,5,9,10].map (options 5 4) := by rfl


theorem t5_512part0 : t5_512jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_512frontier : t5_512root.frontier 0=t5_512jobs := by rfl
theorem t5_512all : t5_512jobs.all (Job.check tree)=true := by
  simp only [t5_512jobs,List.all_append,List.all_nil,t5_512part0,Bool.and_self]
theorem t5_512checked : Checked tree [1,5,5,9,10] := by
  refine ⟨plan4579,valid4579,t5_512choices,?_⟩
  exact check_of_frontier tree 0 t5_512root t5_512jobs t5_512frontier t5_512all
theorem t5_513choices : plan4580.choices=[1,5,5,10,7].map (options 5 4) := by rfl


theorem t5_513part0 : t5_513jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_513frontier : t5_513root.frontier 0=t5_513jobs := by rfl
theorem t5_513all : t5_513jobs.all (Job.check tree)=true := by
  simp only [t5_513jobs,List.all_append,List.all_nil,t5_513part0,Bool.and_self]
theorem t5_513checked : Checked tree [1,5,5,10,7] := by
  refine ⟨plan4580,valid4580,t5_513choices,?_⟩
  exact check_of_frontier tree 0 t5_513root t5_513jobs t5_513frontier t5_513all
theorem t5_514choices : plan4581.choices=[1,5,5,10,10].map (options 5 4) := by rfl


theorem t5_514part0 : t5_514jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_514frontier : t5_514root.frontier 0=t5_514jobs := by rfl
theorem t5_514all : t5_514jobs.all (Job.check tree)=true := by
  simp only [t5_514jobs,List.all_append,List.all_nil,t5_514part0,Bool.and_self]
theorem t5_514checked : Checked tree [1,5,5,10,10] := by
  refine ⟨plan4581,valid4581,t5_514choices,?_⟩
  exact check_of_frontier tree 0 t5_514root t5_514jobs t5_514frontier t5_514all
theorem t5_515choices : plan4582.choices=[1,5,6,6,6].map (options 5 4) := by rfl


theorem t5_515part0 : t5_515jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_515frontier : t5_515root.frontier 0=t5_515jobs := by rfl
theorem t5_515all : t5_515jobs.all (Job.check tree)=true := by
  simp only [t5_515jobs,List.all_append,List.all_nil,t5_515part0,Bool.and_self]
theorem t5_515checked : Checked tree [1,5,6,6,6] := by
  refine ⟨plan4582,valid4582,t5_515choices,?_⟩
  exact check_of_frontier tree 0 t5_515root t5_515jobs t5_515frontier t5_515all
theorem t5_516choices : plan4583.choices=[1,5,6,6,7].map (options 5 4) := by rfl


theorem t5_516part0 : t5_516jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_516frontier : t5_516root.frontier 0=t5_516jobs := by rfl
theorem t5_516all : t5_516jobs.all (Job.check tree)=true := by
  simp only [t5_516jobs,List.all_append,List.all_nil,t5_516part0,Bool.and_self]
theorem t5_516checked : Checked tree [1,5,6,6,7] := by
  refine ⟨plan4583,valid4583,t5_516choices,?_⟩
  exact check_of_frontier tree 0 t5_516root t5_516jobs t5_516frontier t5_516all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks011 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_479checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_480checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_481checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_482checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_483checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_484checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_485checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_486checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_487checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_488checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_467checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_489checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_490checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_491checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_492checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_493checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_494checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_495checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_496checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_468checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_497checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_498checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_499checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_500checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_501checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_502checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_503checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_504checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_505checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_506checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_469checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_507checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_508checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_509checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_510checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_511checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_512checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_513checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_514checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_515checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_516checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_470checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_471checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_472checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_473checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_474checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_475checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_476checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_477checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_478checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_466checked⟩
