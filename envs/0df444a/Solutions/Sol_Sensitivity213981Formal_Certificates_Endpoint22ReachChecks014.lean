-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks014
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:18.601376+00:00
-- url     : https://prove2.me/submissions/61e7f259-53bf-4f36-85c9-31f8ea9a728f

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans048
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











































































































































































theorem valid86 : plan86.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid87 : plan87.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid88 : plan88.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid89 : plan89.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid90 : plan90.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid91 : plan91.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid92 : plan92.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid93 : plan93.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid94 : plan94.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid95 : plan95.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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

theorem valid98 : plan98.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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























































































































theorem valid444 : plan444.Valid := valid_step _ _ _ valid86 (by decide +kernel)

theorem valid445 : plan445.Valid := valid_step _ _ _ valid87 (by decide +kernel)

theorem valid446 : plan446.Valid := valid_step _ _ _ valid87 (by decide +kernel)



theorem valid448 : plan448.Valid := valid_step _ _ _ valid89 (by decide +kernel)

theorem valid449 : plan449.Valid := valid_step _ _ _ valid90 (by decide +kernel)

theorem valid450 : plan450.Valid := valid_step _ _ _ valid91 (by decide +kernel)

theorem valid451 : plan451.Valid := valid_step _ _ _ valid92 (by decide +kernel)

theorem valid452 : plan452.Valid := valid_step _ _ _ valid93 (by decide +kernel)



theorem valid454 : plan454.Valid := valid_step _ _ _ valid90 (by decide +kernel)

theorem valid455 : plan455.Valid := valid_step _ _ _ valid91 (by decide +kernel)

theorem valid456 : plan456.Valid := valid_step _ _ _ valid93 (by decide +kernel)

theorem valid457 : plan457.Valid := valid_step _ _ _ valid88 (by decide +kernel)

theorem valid458 : plan458.Valid := valid_step _ _ _ valid88 (by decide +kernel)







theorem valid462 : plan462.Valid := valid_step _ _ _ valid94 (by decide +kernel)









theorem valid467 : plan467.Valid := valid_step _ _ _ valid95 (by decide +kernel)

theorem valid468 : plan468.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid469 : plan469.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid470 : plan470.Valid := valid_step _ _ _ valid98 (by decide +kernel)

theorem valid471 : plan471.Valid := valid_step _ _ _ valid99 (by decide +kernel)

theorem valid472 : plan472.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid473 : plan473.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid474 : plan474.Valid := valid_step _ _ _ valid99 (by decide +kernel)

theorem valid475 : plan475.Valid := valid_step _ _ _ valid97 (by decide +kernel)



theorem valid477 : plan477.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid478 : plan478.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid479 : plan479.Valid := valid_step _ _ _ valid98 (by decide +kernel)

theorem valid480 : plan480.Valid := valid_step _ _ _ valid99 (by decide +kernel)
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





























































































































































































theorem valid1247 : plan1247.Valid := valid_step _ _ _ valid444 (by decide +kernel)

theorem valid1248 : plan1248.Valid := valid_step _ _ _ valid445 (by decide +kernel)
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





















theorem valid498 : plan498.Valid := valid_step _ _ _ valid100 (by decide +kernel)









theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)



















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

theorem valid1249 : plan1249.Valid := valid_step _ _ _ valid446 (by decide +kernel)

theorem valid1250 : plan1250.Valid := valid_step _ _ _ valid446 (by decide +kernel)





theorem valid1253 : plan1253.Valid := valid_step _ _ _ valid448 (by decide +kernel)

theorem valid1254 : plan1254.Valid := valid_step _ _ _ valid449 (by decide +kernel)

theorem valid1255 : plan1255.Valid := valid_step _ _ _ valid450 (by decide +kernel)

theorem valid1256 : plan1256.Valid := valid_step _ _ _ valid451 (by decide +kernel)

theorem valid1257 : plan1257.Valid := valid_step _ _ _ valid452 (by decide +kernel)



theorem valid1259 : plan1259.Valid := valid_step _ _ _ valid454 (by decide +kernel)

theorem valid1260 : plan1260.Valid := valid_step _ _ _ valid455 (by decide +kernel)

theorem valid1261 : plan1261.Valid := valid_step _ _ _ valid456 (by decide +kernel)

theorem valid1262 : plan1262.Valid := valid_step _ _ _ valid457 (by decide +kernel)

theorem valid1263 : plan1263.Valid := valid_step _ _ _ valid458 (by decide +kernel)



theorem valid1265 : plan1265.Valid := valid_step _ _ _ valid454 (by decide +kernel)































theorem valid1281 : plan1281.Valid := valid_step _ _ _ valid467 (by decide +kernel)

theorem valid1282 : plan1282.Valid := valid_step _ _ _ valid468 (by decide +kernel)

theorem valid1283 : plan1283.Valid := valid_step _ _ _ valid469 (by decide +kernel)

theorem valid1284 : plan1284.Valid := valid_step _ _ _ valid470 (by decide +kernel)

theorem valid1285 : plan1285.Valid := valid_step _ _ _ valid471 (by decide +kernel)

theorem valid1286 : plan1286.Valid := valid_step _ _ _ valid472 (by decide +kernel)

theorem valid1287 : plan1287.Valid := valid_step _ _ _ valid473 (by decide +kernel)

theorem valid1288 : plan1288.Valid := valid_step _ _ _ valid474 (by decide +kernel)

theorem valid1289 : plan1289.Valid := valid_step _ _ _ valid475 (by decide +kernel)



theorem valid1291 : plan1291.Valid := valid_step _ _ _ valid477 (by decide +kernel)

theorem valid1292 : plan1292.Valid := valid_step _ _ _ valid478 (by decide +kernel)

theorem valid1293 : plan1293.Valid := valid_step _ _ _ valid479 (by decide +kernel)

theorem valid1294 : plan1294.Valid := valid_step _ _ _ valid480 (by decide +kernel)

theorem valid1295 : plan1295.Valid := valid_step _ _ _ valid481 (by decide +kernel)

theorem valid1296 : plan1296.Valid := valid_step _ _ _ valid482 (by decide +kernel)





































theorem valid1315 : plan1315.Valid := valid_step _ _ _ valid462 (by decide +kernel)























































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







































theorem valid2516 : plan2516.Valid := valid_step _ _ _ valid1247 (by decide +kernel)

theorem valid2517 : plan2517.Valid := valid_step _ _ _ valid1248 (by decide +kernel)

theorem valid2518 : plan2518.Valid := valid_step _ _ _ valid1249 (by decide +kernel)

theorem valid2519 : plan2519.Valid := valid_step _ _ _ valid1250 (by decide +kernel)

























theorem valid2532 : plan2532.Valid := valid_step _ _ _ valid1253 (by decide +kernel)

theorem valid2533 : plan2533.Valid := valid_step _ _ _ valid1254 (by decide +kernel)

theorem valid2534 : plan2534.Valid := valid_step _ _ _ valid1255 (by decide +kernel)

theorem valid2535 : plan2535.Valid := valid_step _ _ _ valid1256 (by decide +kernel)

theorem valid2536 : plan2536.Valid := valid_step _ _ _ valid1257 (by decide +kernel)



theorem valid2538 : plan2538.Valid := valid_step _ _ _ valid1259 (by decide +kernel)

theorem valid2539 : plan2539.Valid := valid_step _ _ _ valid1260 (by decide +kernel)

theorem valid2540 : plan2540.Valid := valid_step _ _ _ valid1261 (by decide +kernel)

theorem valid2541 : plan2541.Valid := valid_step _ _ _ valid1262 (by decide +kernel)

theorem valid2542 : plan2542.Valid := valid_step _ _ _ valid1263 (by decide +kernel)



theorem valid2544 : plan2544.Valid := valid_step _ _ _ valid1265 (by decide +kernel)





























































































theorem valid2591 : plan2591.Valid := valid_step _ _ _ valid1281 (by decide +kernel)

theorem valid2592 : plan2592.Valid := valid_step _ _ _ valid1282 (by decide +kernel)
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







































theorem valid3668 : plan3668.Valid := valid_step _ _ _ valid2516 (by decide +kernel)

theorem valid3669 : plan3669.Valid := valid_step _ _ _ valid2517 (by decide +kernel)

theorem valid3670 : plan3670.Valid := valid_step _ _ _ valid2518 (by decide +kernel)

theorem valid3671 : plan3671.Valid := valid_step _ _ _ valid2519 (by decide +kernel)













































































































theorem valid3726 : plan3726.Valid := valid_step _ _ _ valid2532 (by decide +kernel)

theorem valid3727 : plan3727.Valid := valid_step _ _ _ valid2533 (by decide +kernel)

theorem valid3728 : plan3728.Valid := valid_step _ _ _ valid2534 (by decide +kernel)

theorem valid3729 : plan3729.Valid := valid_step _ _ _ valid2535 (by decide +kernel)

theorem valid3730 : plan3730.Valid := valid_step _ _ _ valid2536 (by decide +kernel)

theorem valid3731 : plan3731.Valid := valid_step _ _ _ valid2538 (by decide +kernel)

theorem valid3732 : plan3732.Valid := valid_step _ _ _ valid2539 (by decide +kernel)

theorem valid3733 : plan3733.Valid := valid_step _ _ _ valid2540 (by decide +kernel)

theorem valid3734 : plan3734.Valid := valid_step _ _ _ valid2541 (by decide +kernel)

theorem valid3735 : plan3735.Valid := valid_step _ _ _ valid2542 (by decide +kernel)

theorem valid3736 : plan3736.Valid := valid_step _ _ _ valid2544 (by decide +kernel)
















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











































































theorem valid1382 : plan1382.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1383 : plan1383.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1384 : plan1384.Valid := valid_step _ _ _ valid487 (by decide +kernel)









theorem valid1389 : plan1389.Valid := valid_step _ _ _ valid498 (by decide +kernel)































































































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

theorem valid2593 : plan2593.Valid := valid_step _ _ _ valid1283 (by decide +kernel)

theorem valid2594 : plan2594.Valid := valid_step _ _ _ valid1284 (by decide +kernel)

theorem valid2595 : plan2595.Valid := valid_step _ _ _ valid1285 (by decide +kernel)

theorem valid2596 : plan2596.Valid := valid_step _ _ _ valid1286 (by decide +kernel)

theorem valid2597 : plan2597.Valid := valid_step _ _ _ valid1287 (by decide +kernel)

theorem valid2598 : plan2598.Valid := valid_step _ _ _ valid1288 (by decide +kernel)

theorem valid2599 : plan2599.Valid := valid_step _ _ _ valid1289 (by decide +kernel)



theorem valid2601 : plan2601.Valid := valid_step _ _ _ valid1291 (by decide +kernel)

theorem valid2602 : plan2602.Valid := valid_step _ _ _ valid1292 (by decide +kernel)

theorem valid2603 : plan2603.Valid := valid_step _ _ _ valid1293 (by decide +kernel)

theorem valid2604 : plan2604.Valid := valid_step _ _ _ valid1294 (by decide +kernel)

theorem valid2605 : plan2605.Valid := valid_step _ _ _ valid1295 (by decide +kernel)

theorem valid2606 : plan2606.Valid := valid_step _ _ _ valid1296 (by decide +kernel)



























































































































theorem valid2668 : plan2668.Valid := valid_step _ _ _ valid1315 (by decide +kernel)








































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



































































































































































theorem valid2866 : plan2866.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2867 : plan2867.Valid := valid_step _ _ _ valid1344 (by decide +kernel)



theorem valid2869 : plan2869.Valid := valid_step _ _ _ valid1382 (by decide +kernel)

theorem valid2870 : plan2870.Valid := valid_step _ _ _ valid1383 (by decide +kernel)

theorem valid2871 : plan2871.Valid := valid_step _ _ _ valid1384 (by decide +kernel)

theorem valid2872 : plan2872.Valid := valid_step _ _ _ valid1389 (by decide +kernel)
















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



theorem valid1456 : plan1456.Valid := valid_step _ _ _ valid519 (by decide +kernel)

theorem valid1457 : plan1457.Valid := valid_step _ _ _ valid520 (by decide +kernel)



theorem valid1459 : plan1459.Valid := valid_step _ _ _ valid522 (by decide +kernel)

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





















theorem valid3083 : plan3083.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid3084 : plan3084.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid3085 : plan3085.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid3086 : plan3086.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid3087 : plan3087.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid3088 : plan3088.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid3089 : plan3089.Valid := valid_step _ _ _ valid1443 (by decide +kernel)







theorem valid3093 : plan3093.Valid := valid_step _ _ _ valid1451 (by decide +kernel)

theorem valid3094 : plan3094.Valid := valid_step _ _ _ valid1452 (by decide +kernel)

theorem valid3095 : plan3095.Valid := valid_step _ _ _ valid1453 (by decide +kernel)

theorem valid3096 : plan3096.Valid := valid_step _ _ _ valid1454 (by decide +kernel)



theorem valid3098 : plan3098.Valid := valid_step _ _ _ valid1456 (by decide +kernel)

theorem valid3099 : plan3099.Valid := valid_step _ _ _ valid1457 (by decide +kernel)



theorem valid3101 : plan3101.Valid := valid_step _ _ _ valid1459 (by decide +kernel)

theorem valid3102 : plan3102.Valid := valid_step _ _ _ valid1460 (by decide +kernel)

theorem valid3103 : plan3103.Valid := valid_step _ _ _ valid1461 (by decide +kernel)

theorem valid3104 : plan3104.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3105 : plan3105.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid3106 : plan3106.Valid := valid_step _ _ _ valid1464 (by decide +kernel)

theorem valid3107 : plan3107.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

theorem valid3108 : plan3108.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3109 : plan3109.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid3110 : plan3110.Valid := valid_step _ _ _ valid1464 (by decide +kernel)




















































































































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

















































































































theorem valid3897 : plan3897.Valid := valid_step _ _ _ valid2668 (by decide +kernel)

theorem valid3898 : plan3898.Valid := valid_step _ _ _ valid2591 (by decide +kernel)

theorem valid3899 : plan3899.Valid := valid_step _ _ _ valid2592 (by decide +kernel)

theorem valid3900 : plan3900.Valid := valid_step _ _ _ valid2593 (by decide +kernel)

theorem valid3901 : plan3901.Valid := valid_step _ _ _ valid2594 (by decide +kernel)

theorem valid3902 : plan3902.Valid := valid_step _ _ _ valid2595 (by decide +kernel)

theorem valid3903 : plan3903.Valid := valid_step _ _ _ valid2596 (by decide +kernel)

theorem valid3904 : plan3904.Valid := valid_step _ _ _ valid2597 (by decide +kernel)

theorem valid3905 : plan3905.Valid := valid_step _ _ _ valid2598 (by decide +kernel)

theorem valid3906 : plan3906.Valid := valid_step _ _ _ valid2599 (by decide +kernel)

theorem valid3907 : plan3907.Valid := valid_step _ _ _ valid2601 (by decide +kernel)

theorem valid3908 : plan3908.Valid := valid_step _ _ _ valid2602 (by decide +kernel)

theorem valid3909 : plan3909.Valid := valid_step _ _ _ valid2603 (by decide +kernel)

theorem valid3910 : plan3910.Valid := valid_step _ _ _ valid2604 (by decide +kernel)

theorem valid3911 : plan3911.Valid := valid_step _ _ _ valid2605 (by decide +kernel)

theorem valid3912 : plan3912.Valid := valid_step _ _ _ valid2606 (by decide +kernel)
















































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































































theorem valid4640 : plan4640.Valid := valid_step _ _ _ valid3083 (by decide +kernel)

theorem valid4641 : plan4641.Valid := valid_step _ _ _ valid3084 (by decide +kernel)

theorem valid4642 : plan4642.Valid := valid_step _ _ _ valid3085 (by decide +kernel)

theorem valid4643 : plan4643.Valid := valid_step _ _ _ valid3086 (by decide +kernel)

theorem valid4644 : plan4644.Valid := valid_step _ _ _ valid3087 (by decide +kernel)

theorem valid4645 : plan4645.Valid := valid_step _ _ _ valid3088 (by decide +kernel)

theorem valid4646 : plan4646.Valid := valid_step _ _ _ valid3089 (by decide +kernel)

theorem valid4647 : plan4647.Valid := valid_step _ _ _ valid3093 (by decide +kernel)

theorem valid4648 : plan4648.Valid := valid_step _ _ _ valid3094 (by decide +kernel)

theorem valid4649 : plan4649.Valid := valid_step _ _ _ valid3095 (by decide +kernel)

theorem valid4650 : plan4650.Valid := valid_step _ _ _ valid3096 (by decide +kernel)

theorem valid4651 : plan4651.Valid := valid_step _ _ _ valid3098 (by decide +kernel)

theorem valid4652 : plan4652.Valid := valid_step _ _ _ valid3099 (by decide +kernel)

theorem valid4653 : plan4653.Valid := valid_step _ _ _ valid3101 (by decide +kernel)

theorem valid4654 : plan4654.Valid := valid_step _ _ _ valid3102 (by decide +kernel)

theorem valid4655 : plan4655.Valid := valid_step _ _ _ valid3103 (by decide +kernel)

theorem valid4656 : plan4656.Valid := valid_step _ _ _ valid3104 (by decide +kernel)

theorem valid4657 : plan4657.Valid := valid_step _ _ _ valid3105 (by decide +kernel)

theorem valid4658 : plan4658.Valid := valid_step _ _ _ valid3106 (by decide +kernel)

theorem valid4659 : plan4659.Valid := valid_step _ _ _ valid3107 (by decide +kernel)

theorem valid4660 : plan4660.Valid := valid_step _ _ _ valid3108 (by decide +kernel)

theorem valid4661 : plan4661.Valid := valid_step _ _ _ valid3109 (by decide +kernel)

theorem valid4662 : plan4662.Valid := valid_step _ _ _ valid3110 (by decide +kernel)




















































































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







theorem valid4228 : plan4228.Valid := valid_step _ _ _ valid2866 (by decide +kernel)

theorem valid4229 : plan4229.Valid := valid_step _ _ _ valid2867 (by decide +kernel)

theorem valid4230 : plan4230.Valid := valid_step _ _ _ valid2869 (by decide +kernel)

theorem valid4231 : plan4231.Valid := valid_step _ _ _ valid2870 (by decide +kernel)

theorem valid4232 : plan4232.Valid := valid_step _ _ _ valid2871 (by decide +kernel)

theorem valid4233 : plan4233.Valid := valid_step _ _ _ valid2872 (by decide +kernel)














































































































































































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
theorem t5_618choices : plan4228.choices=[1,9,3,10,7].map (options 5 3) := by rfl


theorem t5_618part0 : t5_618jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_618part1 : t5_618jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_618frontier : t5_618root.frontier 1=t5_618jobs := by rfl
theorem t5_618all : t5_618jobs.all (Job.check tree)=true := by
  simp only [t5_618jobs,List.all_append,List.all_nil,t5_618part0,t5_618part1,Bool.and_self]
theorem t5_618checked : Checked tree [1,9,3,10,7] := by
  refine ⟨plan4228,valid4228,t5_618choices,?_⟩
  exact check_of_frontier tree 1 t5_618root t5_618jobs t5_618frontier t5_618all
theorem t5_619choices : plan4229.choices=[1,9,3,10,10].map (options 5 3) := by rfl


theorem t5_619part0 : t5_619jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_619frontier : t5_619root.frontier 0=t5_619jobs := by rfl
theorem t5_619all : t5_619jobs.all (Job.check tree)=true := by
  simp only [t5_619jobs,List.all_append,List.all_nil,t5_619part0,Bool.and_self]
theorem t5_619checked : Checked tree [1,9,3,10,10] := by
  refine ⟨plan4229,valid4229,t5_619choices,?_⟩
  exact check_of_frontier tree 0 t5_619root t5_619jobs t5_619frontier t5_619all
theorem t5_620choices : plan4640.choices=[1,9,6,6,6].map (options 5 4) := by rfl


theorem t5_620part0 : t5_620jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_620frontier : t5_620root.frontier 0=t5_620jobs := by rfl
theorem t5_620all : t5_620jobs.all (Job.check tree)=true := by
  simp only [t5_620jobs,List.all_append,List.all_nil,t5_620part0,Bool.and_self]
theorem t5_620checked : Checked tree [1,9,6,6,6] := by
  refine ⟨plan4640,valid4640,t5_620choices,?_⟩
  exact check_of_frontier tree 0 t5_620root t5_620jobs t5_620frontier t5_620all
theorem t5_621choices : plan4641.choices=[1,9,6,6,7].map (options 5 4) := by rfl


theorem t5_621part0 : t5_621jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_621frontier : t5_621root.frontier 0=t5_621jobs := by rfl
theorem t5_621all : t5_621jobs.all (Job.check tree)=true := by
  simp only [t5_621jobs,List.all_append,List.all_nil,t5_621part0,Bool.and_self]
theorem t5_621checked : Checked tree [1,9,6,6,7] := by
  refine ⟨plan4641,valid4641,t5_621choices,?_⟩
  exact check_of_frontier tree 0 t5_621root t5_621jobs t5_621frontier t5_621all
theorem t5_622choices : plan4642.choices=[1,9,6,6,10].map (options 5 4) := by rfl


theorem t5_622part0 : t5_622jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_622frontier : t5_622root.frontier 0=t5_622jobs := by rfl
theorem t5_622all : t5_622jobs.all (Job.check tree)=true := by
  simp only [t5_622jobs,List.all_append,List.all_nil,t5_622part0,Bool.and_self]
theorem t5_622checked : Checked tree [1,9,6,6,10] := by
  refine ⟨plan4642,valid4642,t5_622choices,?_⟩
  exact check_of_frontier tree 0 t5_622root t5_622jobs t5_622frontier t5_622all
theorem t5_623choices : plan4643.choices=[1,9,6,7,7].map (options 5 4) := by rfl


theorem t5_623part0 : t5_623jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_623frontier : t5_623root.frontier 0=t5_623jobs := by rfl
theorem t5_623all : t5_623jobs.all (Job.check tree)=true := by
  simp only [t5_623jobs,List.all_append,List.all_nil,t5_623part0,Bool.and_self]
theorem t5_623checked : Checked tree [1,9,6,7,7] := by
  refine ⟨plan4643,valid4643,t5_623choices,?_⟩
  exact check_of_frontier tree 0 t5_623root t5_623jobs t5_623frontier t5_623all
theorem t5_624choices : plan4644.choices=[1,9,6,10,7].map (options 5 4) := by rfl


theorem t5_624part0 : t5_624jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_624frontier : t5_624root.frontier 0=t5_624jobs := by rfl
theorem t5_624all : t5_624jobs.all (Job.check tree)=true := by
  simp only [t5_624jobs,List.all_append,List.all_nil,t5_624part0,Bool.and_self]
theorem t5_624checked : Checked tree [1,9,6,10,7] := by
  refine ⟨plan4644,valid4644,t5_624choices,?_⟩
  exact check_of_frontier tree 0 t5_624root t5_624jobs t5_624frontier t5_624all
theorem t5_625choices : plan4645.choices=[1,9,6,10,10].map (options 5 4) := by rfl


theorem t5_625part0 : t5_625jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_625frontier : t5_625root.frontier 0=t5_625jobs := by rfl
theorem t5_625all : t5_625jobs.all (Job.check tree)=true := by
  simp only [t5_625jobs,List.all_append,List.all_nil,t5_625part0,Bool.and_self]
theorem t5_625checked : Checked tree [1,9,6,10,10] := by
  refine ⟨plan4645,valid4645,t5_625choices,?_⟩
  exact check_of_frontier tree 0 t5_625root t5_625jobs t5_625frontier t5_625all
theorem t5_626choices : plan4646.choices=[1,9,7,7,7].map (options 5 4) := by rfl


theorem t5_626part0 : t5_626jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_626frontier : t5_626root.frontier 0=t5_626jobs := by rfl
theorem t5_626all : t5_626jobs.all (Job.check tree)=true := by
  simp only [t5_626jobs,List.all_append,List.all_nil,t5_626part0,Bool.and_self]
theorem t5_626checked : Checked tree [1,9,7,7,7] := by
  refine ⟨plan4646,valid4646,t5_626choices,?_⟩
  exact check_of_frontier tree 0 t5_626root t5_626jobs t5_626frontier t5_626all
theorem t5_627choices : plan3897.choices=[1,9,9,3,3].map (options 5 2) := by rfl


theorem t5_627part0 : t5_627jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_627frontier : t5_627root.frontier 0=t5_627jobs := by rfl
theorem t5_627all : t5_627jobs.all (Job.check tree)=true := by
  simp only [t5_627jobs,List.all_append,List.all_nil,t5_627part0,Bool.and_self]
theorem t5_627checked : Checked tree [1,9,9,3,3] := by
  refine ⟨plan3897,valid3897,t5_627choices,?_⟩
  exact check_of_frontier tree 0 t5_627root t5_627jobs t5_627frontier t5_627all
theorem t5_628choices : plan4230.choices=[1,9,9,3,6].map (options 5 3) := by rfl


theorem t5_628part0 : t5_628jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_628frontier : t5_628root.frontier 0=t5_628jobs := by rfl
theorem t5_628all : t5_628jobs.all (Job.check tree)=true := by
  simp only [t5_628jobs,List.all_append,List.all_nil,t5_628part0,Bool.and_self]
theorem t5_628checked : Checked tree [1,9,9,3,6] := by
  refine ⟨plan4230,valid4230,t5_628choices,?_⟩
  exact check_of_frontier tree 0 t5_628root t5_628jobs t5_628frontier t5_628all
theorem t5_629choices : plan4231.choices=[1,9,9,3,7].map (options 5 3) := by rfl


theorem t5_629part0 : t5_629jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_629frontier : t5_629root.frontier 0=t5_629jobs := by rfl
theorem t5_629all : t5_629jobs.all (Job.check tree)=true := by
  simp only [t5_629jobs,List.all_append,List.all_nil,t5_629part0,Bool.and_self]
theorem t5_629checked : Checked tree [1,9,9,3,7] := by
  refine ⟨plan4231,valid4231,t5_629choices,?_⟩
  exact check_of_frontier tree 0 t5_629root t5_629jobs t5_629frontier t5_629all
theorem t5_630choices : plan4232.choices=[1,9,9,3,10].map (options 5 3) := by rfl


theorem t5_630part0 : t5_630jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_630frontier : t5_630root.frontier 0=t5_630jobs := by rfl
theorem t5_630all : t5_630jobs.all (Job.check tree)=true := by
  simp only [t5_630jobs,List.all_append,List.all_nil,t5_630part0,Bool.and_self]
theorem t5_630checked : Checked tree [1,9,9,3,10] := by
  refine ⟨plan4232,valid4232,t5_630choices,?_⟩
  exact check_of_frontier tree 0 t5_630root t5_630jobs t5_630frontier t5_630all
theorem t5_631choices : plan4647.choices=[1,9,9,6,6].map (options 5 4) := by rfl


theorem t5_631part0 : t5_631jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_631frontier : t5_631root.frontier 0=t5_631jobs := by rfl
theorem t5_631all : t5_631jobs.all (Job.check tree)=true := by
  simp only [t5_631jobs,List.all_append,List.all_nil,t5_631part0,Bool.and_self]
theorem t5_631checked : Checked tree [1,9,9,6,6] := by
  refine ⟨plan4647,valid4647,t5_631choices,?_⟩
  exact check_of_frontier tree 0 t5_631root t5_631jobs t5_631frontier t5_631all
theorem t5_632choices : plan4648.choices=[1,9,9,6,7].map (options 5 4) := by rfl


theorem t5_632part0 : t5_632jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_632frontier : t5_632root.frontier 0=t5_632jobs := by rfl
theorem t5_632all : t5_632jobs.all (Job.check tree)=true := by
  simp only [t5_632jobs,List.all_append,List.all_nil,t5_632part0,Bool.and_self]
theorem t5_632checked : Checked tree [1,9,9,6,7] := by
  refine ⟨plan4648,valid4648,t5_632choices,?_⟩
  exact check_of_frontier tree 0 t5_632root t5_632jobs t5_632frontier t5_632all
theorem t5_633choices : plan4649.choices=[1,9,9,6,10].map (options 5 4) := by rfl


theorem t5_633part0 : t5_633jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_633frontier : t5_633root.frontier 0=t5_633jobs := by rfl
theorem t5_633all : t5_633jobs.all (Job.check tree)=true := by
  simp only [t5_633jobs,List.all_append,List.all_nil,t5_633part0,Bool.and_self]
theorem t5_633checked : Checked tree [1,9,9,6,10] := by
  refine ⟨plan4649,valid4649,t5_633choices,?_⟩
  exact check_of_frontier tree 0 t5_633root t5_633jobs t5_633frontier t5_633all
theorem t5_634choices : plan4650.choices=[1,9,9,7,7].map (options 5 4) := by rfl


theorem t5_634part0 : t5_634jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_634frontier : t5_634root.frontier 0=t5_634jobs := by rfl
theorem t5_634all : t5_634jobs.all (Job.check tree)=true := by
  simp only [t5_634jobs,List.all_append,List.all_nil,t5_634part0,Bool.and_self]
theorem t5_634checked : Checked tree [1,9,9,7,7] := by
  refine ⟨plan4650,valid4650,t5_634choices,?_⟩
  exact check_of_frontier tree 0 t5_634root t5_634jobs t5_634frontier t5_634all
theorem t5_635choices : plan4233.choices=[1,9,9,9,3].map (options 5 3) := by rfl


theorem t5_635part0 : t5_635jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_635frontier : t5_635root.frontier 0=t5_635jobs := by rfl
theorem t5_635all : t5_635jobs.all (Job.check tree)=true := by
  simp only [t5_635jobs,List.all_append,List.all_nil,t5_635part0,Bool.and_self]
theorem t5_635checked : Checked tree [1,9,9,9,3] := by
  refine ⟨plan4233,valid4233,t5_635choices,?_⟩
  exact check_of_frontier tree 0 t5_635root t5_635jobs t5_635frontier t5_635all
theorem t5_636choices : plan4651.choices=[1,9,9,9,6].map (options 5 4) := by rfl


theorem t5_636part0 : t5_636jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_636frontier : t5_636root.frontier 0=t5_636jobs := by rfl
theorem t5_636all : t5_636jobs.all (Job.check tree)=true := by
  simp only [t5_636jobs,List.all_append,List.all_nil,t5_636part0,Bool.and_self]
theorem t5_636checked : Checked tree [1,9,9,9,6] := by
  refine ⟨plan4651,valid4651,t5_636choices,?_⟩
  exact check_of_frontier tree 0 t5_636root t5_636jobs t5_636frontier t5_636all
theorem t5_637choices : plan4652.choices=[1,9,9,9,7].map (options 5 4) := by rfl


theorem t5_637part0 : t5_637jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_637frontier : t5_637root.frontier 0=t5_637jobs := by rfl
theorem t5_637all : t5_637jobs.all (Job.check tree)=true := by
  simp only [t5_637jobs,List.all_append,List.all_nil,t5_637part0,Bool.and_self]
theorem t5_637checked : Checked tree [1,9,9,9,7] := by
  refine ⟨plan4652,valid4652,t5_637choices,?_⟩
  exact check_of_frontier tree 0 t5_637root t5_637jobs t5_637frontier t5_637all
theorem t5_638choices : plan4653.choices=[1,9,9,9,10].map (options 5 4) := by rfl


theorem t5_638part0 : t5_638jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_638frontier : t5_638root.frontier 0=t5_638jobs := by rfl
theorem t5_638all : t5_638jobs.all (Job.check tree)=true := by
  simp only [t5_638jobs,List.all_append,List.all_nil,t5_638part0,Bool.and_self]
theorem t5_638checked : Checked tree [1,9,9,9,10] := by
  refine ⟨plan4653,valid4653,t5_638choices,?_⟩
  exact check_of_frontier tree 0 t5_638root t5_638jobs t5_638frontier t5_638all
theorem t5_639choices : plan4654.choices=[1,9,9,10,7].map (options 5 4) := by rfl


theorem t5_639part0 : t5_639jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_639frontier : t5_639root.frontier 0=t5_639jobs := by rfl
theorem t5_639all : t5_639jobs.all (Job.check tree)=true := by
  simp only [t5_639jobs,List.all_append,List.all_nil,t5_639part0,Bool.and_self]
theorem t5_639checked : Checked tree [1,9,9,10,7] := by
  refine ⟨plan4654,valid4654,t5_639choices,?_⟩
  exact check_of_frontier tree 0 t5_639root t5_639jobs t5_639frontier t5_639all
theorem t5_640choices : plan4655.choices=[1,9,9,10,10].map (options 5 4) := by rfl


theorem t5_640part0 : t5_640jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_640frontier : t5_640root.frontier 0=t5_640jobs := by rfl
theorem t5_640all : t5_640jobs.all (Job.check tree)=true := by
  simp only [t5_640jobs,List.all_append,List.all_nil,t5_640part0,Bool.and_self]
theorem t5_640checked : Checked tree [1,9,9,10,10] := by
  refine ⟨plan4655,valid4655,t5_640choices,?_⟩
  exact check_of_frontier tree 0 t5_640root t5_640jobs t5_640frontier t5_640all
theorem t5_641choices : plan4656.choices=[1,9,10,7,7].map (options 5 4) := by rfl


theorem t5_641part0 : t5_641jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_641frontier : t5_641root.frontier 0=t5_641jobs := by rfl
theorem t5_641all : t5_641jobs.all (Job.check tree)=true := by
  simp only [t5_641jobs,List.all_append,List.all_nil,t5_641part0,Bool.and_self]
theorem t5_641checked : Checked tree [1,9,10,7,7] := by
  refine ⟨plan4656,valid4656,t5_641choices,?_⟩
  exact check_of_frontier tree 0 t5_641root t5_641jobs t5_641frontier t5_641all
theorem t5_642choices : plan4657.choices=[1,9,10,10,7].map (options 5 4) := by rfl


theorem t5_642part0 : t5_642jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_642frontier : t5_642root.frontier 0=t5_642jobs := by rfl
theorem t5_642all : t5_642jobs.all (Job.check tree)=true := by
  simp only [t5_642jobs,List.all_append,List.all_nil,t5_642part0,Bool.and_self]
theorem t5_642checked : Checked tree [1,9,10,10,7] := by
  refine ⟨plan4657,valid4657,t5_642choices,?_⟩
  exact check_of_frontier tree 0 t5_642root t5_642jobs t5_642frontier t5_642all
theorem t5_643choices : plan4658.choices=[1,9,10,10,10].map (options 5 4) := by rfl


theorem t5_643part0 : t5_643jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_643frontier : t5_643root.frontier 0=t5_643jobs := by rfl
theorem t5_643all : t5_643jobs.all (Job.check tree)=true := by
  simp only [t5_643jobs,List.all_append,List.all_nil,t5_643part0,Bool.and_self]
theorem t5_643checked : Checked tree [1,9,10,10,10] := by
  refine ⟨plan4658,valid4658,t5_643choices,?_⟩
  exact check_of_frontier tree 0 t5_643root t5_643jobs t5_643frontier t5_643all
theorem t5_644choices : plan4659.choices=[1,10,7,7,7].map (options 5 4) := by rfl


theorem t5_644part0 : t5_644jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_644frontier : t5_644root.frontier 0=t5_644jobs := by rfl
theorem t5_644all : t5_644jobs.all (Job.check tree)=true := by
  simp only [t5_644jobs,List.all_append,List.all_nil,t5_644part0,Bool.and_self]
theorem t5_644checked : Checked tree [1,10,7,7,7] := by
  refine ⟨plan4659,valid4659,t5_644choices,?_⟩
  exact check_of_frontier tree 0 t5_644root t5_644jobs t5_644frontier t5_644all
theorem t5_645choices : plan4660.choices=[1,10,10,7,7].map (options 5 4) := by rfl


theorem t5_645part0 : t5_645jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_645frontier : t5_645root.frontier 0=t5_645jobs := by rfl
theorem t5_645all : t5_645jobs.all (Job.check tree)=true := by
  simp only [t5_645jobs,List.all_append,List.all_nil,t5_645part0,Bool.and_self]
theorem t5_645checked : Checked tree [1,10,10,7,7] := by
  refine ⟨plan4660,valid4660,t5_645choices,?_⟩
  exact check_of_frontier tree 0 t5_645root t5_645jobs t5_645frontier t5_645all
theorem t5_646choices : plan4661.choices=[1,10,10,10,7].map (options 5 4) := by rfl


theorem t5_646part0 : t5_646jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_646frontier : t5_646root.frontier 0=t5_646jobs := by rfl
theorem t5_646all : t5_646jobs.all (Job.check tree)=true := by
  simp only [t5_646jobs,List.all_append,List.all_nil,t5_646part0,Bool.and_self]
theorem t5_646checked : Checked tree [1,10,10,10,7] := by
  refine ⟨plan4661,valid4661,t5_646choices,?_⟩
  exact check_of_frontier tree 0 t5_646root t5_646jobs t5_646frontier t5_646all
theorem t5_647choices : plan4662.choices=[1,10,10,10,10].map (options 5 4) := by rfl


theorem t5_647part0 : t5_647jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_647frontier : t5_647root.frontier 0=t5_647jobs := by rfl
theorem t5_647all : t5_647jobs.all (Job.check tree)=true := by
  simp only [t5_647jobs,List.all_append,List.all_nil,t5_647part0,Bool.and_self]
theorem t5_647checked : Checked tree [1,10,10,10,10] := by
  refine ⟨plan4662,valid4662,t5_647choices,?_⟩
  exact check_of_frontier tree 0 t5_647root t5_647jobs t5_647frontier t5_647all
theorem t5_648choices : plan3668.choices=[2,2,2,2,2].map (options 5 0) := by rfl


theorem t5_648part0 : t5_648jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_648frontier : t5_648root.frontier 0=t5_648jobs := by rfl
theorem t5_648all : t5_648jobs.all (Job.check tree)=true := by
  simp only [t5_648jobs,List.all_append,List.all_nil,t5_648part0,Bool.and_self]
theorem t5_648checked : Checked tree [2,2,2,2,2] := by
  refine ⟨plan3668,valid3668,t5_648choices,?_⟩
  exact check_of_frontier tree 0 t5_648root t5_648jobs t5_648frontier t5_648all
theorem t5_649choices : plan3669.choices=[2,2,2,2,3].map (options 5 0) := by rfl


theorem t5_649part0 : t5_649jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_649frontier : t5_649root.frontier 0=t5_649jobs := by rfl
theorem t5_649all : t5_649jobs.all (Job.check tree)=true := by
  simp only [t5_649jobs,List.all_append,List.all_nil,t5_649part0,Bool.and_self]
theorem t5_649checked : Checked tree [2,2,2,2,3] := by
  refine ⟨plan3669,valid3669,t5_649choices,?_⟩
  exact check_of_frontier tree 0 t5_649root t5_649jobs t5_649frontier t5_649all
theorem t5_650choices : plan3726.choices=[2,2,2,2,5].map (options 5 1) := by rfl


theorem t5_650part0 : t5_650jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_650frontier : t5_650root.frontier 0=t5_650jobs := by rfl
theorem t5_650all : t5_650jobs.all (Job.check tree)=true := by
  simp only [t5_650jobs,List.all_append,List.all_nil,t5_650part0,Bool.and_self]
theorem t5_650checked : Checked tree [2,2,2,2,5] := by
  refine ⟨plan3726,valid3726,t5_650choices,?_⟩
  exact check_of_frontier tree 0 t5_650root t5_650jobs t5_650frontier t5_650all
theorem t5_651choices : plan3727.choices=[2,2,2,2,6].map (options 5 1) := by rfl


theorem t5_651part0 : t5_651jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_651frontier : t5_651root.frontier 0=t5_651jobs := by rfl
theorem t5_651all : t5_651jobs.all (Job.check tree)=true := by
  simp only [t5_651jobs,List.all_append,List.all_nil,t5_651part0,Bool.and_self]
theorem t5_651checked : Checked tree [2,2,2,2,6] := by
  refine ⟨plan3727,valid3727,t5_651choices,?_⟩
  exact check_of_frontier tree 0 t5_651root t5_651jobs t5_651frontier t5_651all
theorem t5_652choices : plan3728.choices=[2,2,2,2,7].map (options 5 1) := by rfl


theorem t5_652part0 : t5_652jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_652frontier : t5_652root.frontier 0=t5_652jobs := by rfl
theorem t5_652all : t5_652jobs.all (Job.check tree)=true := by
  simp only [t5_652jobs,List.all_append,List.all_nil,t5_652part0,Bool.and_self]
theorem t5_652checked : Checked tree [2,2,2,2,7] := by
  refine ⟨plan3728,valid3728,t5_652choices,?_⟩
  exact check_of_frontier tree 0 t5_652root t5_652jobs t5_652frontier t5_652all
theorem t5_653choices : plan3729.choices=[2,2,2,2,9].map (options 5 1) := by rfl


theorem t5_653part0 : t5_653jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_653frontier : t5_653root.frontier 0=t5_653jobs := by rfl
theorem t5_653all : t5_653jobs.all (Job.check tree)=true := by
  simp only [t5_653jobs,List.all_append,List.all_nil,t5_653part0,Bool.and_self]
theorem t5_653checked : Checked tree [2,2,2,2,9] := by
  refine ⟨plan3729,valid3729,t5_653choices,?_⟩
  exact check_of_frontier tree 0 t5_653root t5_653jobs t5_653frontier t5_653all
theorem t5_654choices : plan3730.choices=[2,2,2,2,10].map (options 5 1) := by rfl


theorem t5_654part0 : t5_654jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_654frontier : t5_654root.frontier 0=t5_654jobs := by rfl
theorem t5_654all : t5_654jobs.all (Job.check tree)=true := by
  simp only [t5_654jobs,List.all_append,List.all_nil,t5_654part0,Bool.and_self]
theorem t5_654checked : Checked tree [2,2,2,2,10] := by
  refine ⟨plan3730,valid3730,t5_654choices,?_⟩
  exact check_of_frontier tree 0 t5_654root t5_654jobs t5_654frontier t5_654all
theorem t5_655choices : plan3670.choices=[2,2,2,3,3].map (options 5 0) := by rfl


theorem t5_655part0 : t5_655jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_655frontier : t5_655root.frontier 0=t5_655jobs := by rfl
theorem t5_655all : t5_655jobs.all (Job.check tree)=true := by
  simp only [t5_655jobs,List.all_append,List.all_nil,t5_655part0,Bool.and_self]
theorem t5_655checked : Checked tree [2,2,2,3,3] := by
  refine ⟨plan3670,valid3670,t5_655choices,?_⟩
  exact check_of_frontier tree 0 t5_655root t5_655jobs t5_655frontier t5_655all
theorem t5_656choices : plan3731.choices=[2,2,2,3,6].map (options 5 1) := by rfl


theorem t5_656part0 : t5_656jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_656frontier : t5_656root.frontier 0=t5_656jobs := by rfl
theorem t5_656all : t5_656jobs.all (Job.check tree)=true := by
  simp only [t5_656jobs,List.all_append,List.all_nil,t5_656part0,Bool.and_self]
theorem t5_656checked : Checked tree [2,2,2,3,6] := by
  refine ⟨plan3731,valid3731,t5_656choices,?_⟩
  exact check_of_frontier tree 0 t5_656root t5_656jobs t5_656frontier t5_656all
theorem t5_657choices : plan3732.choices=[2,2,2,3,7].map (options 5 1) := by rfl


theorem t5_657part0 : t5_657jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_657frontier : t5_657root.frontier 0=t5_657jobs := by rfl
theorem t5_657all : t5_657jobs.all (Job.check tree)=true := by
  simp only [t5_657jobs,List.all_append,List.all_nil,t5_657part0,Bool.and_self]
theorem t5_657checked : Checked tree [2,2,2,3,7] := by
  refine ⟨plan3732,valid3732,t5_657choices,?_⟩
  exact check_of_frontier tree 0 t5_657root t5_657jobs t5_657frontier t5_657all
theorem t5_658choices : plan3733.choices=[2,2,2,3,10].map (options 5 1) := by rfl


theorem t5_658part0 : t5_658jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_658frontier : t5_658root.frontier 0=t5_658jobs := by rfl
theorem t5_658all : t5_658jobs.all (Job.check tree)=true := by
  simp only [t5_658jobs,List.all_append,List.all_nil,t5_658part0,Bool.and_self]
theorem t5_658checked : Checked tree [2,2,2,3,10] := by
  refine ⟨plan3733,valid3733,t5_658choices,?_⟩
  exact check_of_frontier tree 0 t5_658root t5_658jobs t5_658frontier t5_658all
theorem t5_659choices : plan3734.choices=[2,2,2,5,3].map (options 5 1) := by rfl


theorem t5_659part0 : t5_659jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_659frontier : t5_659root.frontier 0=t5_659jobs := by rfl
theorem t5_659all : t5_659jobs.all (Job.check tree)=true := by
  simp only [t5_659jobs,List.all_append,List.all_nil,t5_659part0,Bool.and_self]
theorem t5_659checked : Checked tree [2,2,2,5,3] := by
  refine ⟨plan3734,valid3734,t5_659choices,?_⟩
  exact check_of_frontier tree 0 t5_659root t5_659jobs t5_659frontier t5_659all
theorem t5_660choices : plan3898.choices=[2,2,2,5,5].map (options 5 2) := by rfl


theorem t5_660part0 : t5_660jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_660frontier : t5_660root.frontier 0=t5_660jobs := by rfl
theorem t5_660all : t5_660jobs.all (Job.check tree)=true := by
  simp only [t5_660jobs,List.all_append,List.all_nil,t5_660part0,Bool.and_self]
theorem t5_660checked : Checked tree [2,2,2,5,5] := by
  refine ⟨plan3898,valid3898,t5_660choices,?_⟩
  exact check_of_frontier tree 0 t5_660root t5_660jobs t5_660frontier t5_660all
theorem t5_661choices : plan3899.choices=[2,2,2,5,6].map (options 5 2) := by rfl


theorem t5_661part0 : t5_661jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_661frontier : t5_661root.frontier 0=t5_661jobs := by rfl
theorem t5_661all : t5_661jobs.all (Job.check tree)=true := by
  simp only [t5_661jobs,List.all_append,List.all_nil,t5_661part0,Bool.and_self]
theorem t5_661checked : Checked tree [2,2,2,5,6] := by
  refine ⟨plan3899,valid3899,t5_661choices,?_⟩
  exact check_of_frontier tree 0 t5_661root t5_661jobs t5_661frontier t5_661all
theorem t5_662choices : plan3900.choices=[2,2,2,5,7].map (options 5 2) := by rfl


theorem t5_662part0 : t5_662jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_662frontier : t5_662root.frontier 0=t5_662jobs := by rfl
theorem t5_662all : t5_662jobs.all (Job.check tree)=true := by
  simp only [t5_662jobs,List.all_append,List.all_nil,t5_662part0,Bool.and_self]
theorem t5_662checked : Checked tree [2,2,2,5,7] := by
  refine ⟨plan3900,valid3900,t5_662choices,?_⟩
  exact check_of_frontier tree 0 t5_662root t5_662jobs t5_662frontier t5_662all
theorem t5_663choices : plan3901.choices=[2,2,2,5,9].map (options 5 2) := by rfl


theorem t5_663part0 : t5_663jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_663frontier : t5_663root.frontier 0=t5_663jobs := by rfl
theorem t5_663all : t5_663jobs.all (Job.check tree)=true := by
  simp only [t5_663jobs,List.all_append,List.all_nil,t5_663part0,Bool.and_self]
theorem t5_663checked : Checked tree [2,2,2,5,9] := by
  refine ⟨plan3901,valid3901,t5_663choices,?_⟩
  exact check_of_frontier tree 0 t5_663root t5_663jobs t5_663frontier t5_663all
theorem t5_664choices : plan3902.choices=[2,2,2,5,10].map (options 5 2) := by rfl


theorem t5_664part0 : t5_664jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_664frontier : t5_664root.frontier 0=t5_664jobs := by rfl
theorem t5_664all : t5_664jobs.all (Job.check tree)=true := by
  simp only [t5_664jobs,List.all_append,List.all_nil,t5_664part0,Bool.and_self]
theorem t5_664checked : Checked tree [2,2,2,5,10] := by
  refine ⟨plan3902,valid3902,t5_664choices,?_⟩
  exact check_of_frontier tree 0 t5_664root t5_664jobs t5_664frontier t5_664all
theorem t5_665choices : plan3903.choices=[2,2,2,6,6].map (options 5 2) := by rfl


theorem t5_665part0 : t5_665jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_665frontier : t5_665root.frontier 0=t5_665jobs := by rfl
theorem t5_665all : t5_665jobs.all (Job.check tree)=true := by
  simp only [t5_665jobs,List.all_append,List.all_nil,t5_665part0,Bool.and_self]
theorem t5_665checked : Checked tree [2,2,2,6,6] := by
  refine ⟨plan3903,valid3903,t5_665choices,?_⟩
  exact check_of_frontier tree 0 t5_665root t5_665jobs t5_665frontier t5_665all
theorem t5_666choices : plan3904.choices=[2,2,2,6,7].map (options 5 2) := by rfl


theorem t5_666part0 : t5_666jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_666frontier : t5_666root.frontier 0=t5_666jobs := by rfl
theorem t5_666all : t5_666jobs.all (Job.check tree)=true := by
  simp only [t5_666jobs,List.all_append,List.all_nil,t5_666part0,Bool.and_self]
theorem t5_666checked : Checked tree [2,2,2,6,7] := by
  refine ⟨plan3904,valid3904,t5_666choices,?_⟩
  exact check_of_frontier tree 0 t5_666root t5_666jobs t5_666frontier t5_666all
theorem t5_667choices : plan3905.choices=[2,2,2,6,10].map (options 5 2) := by rfl


theorem t5_667part0 : t5_667jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_667frontier : t5_667root.frontier 0=t5_667jobs := by rfl
theorem t5_667all : t5_667jobs.all (Job.check tree)=true := by
  simp only [t5_667jobs,List.all_append,List.all_nil,t5_667part0,Bool.and_self]
theorem t5_667checked : Checked tree [2,2,2,6,10] := by
  refine ⟨plan3905,valid3905,t5_667choices,?_⟩
  exact check_of_frontier tree 0 t5_667root t5_667jobs t5_667frontier t5_667all
theorem t5_668choices : plan3906.choices=[2,2,2,7,7].map (options 5 2) := by rfl


theorem t5_668part0 : t5_668jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_668frontier : t5_668root.frontier 0=t5_668jobs := by rfl
theorem t5_668all : t5_668jobs.all (Job.check tree)=true := by
  simp only [t5_668jobs,List.all_append,List.all_nil,t5_668part0,Bool.and_self]
theorem t5_668checked : Checked tree [2,2,2,7,7] := by
  refine ⟨plan3906,valid3906,t5_668choices,?_⟩
  exact check_of_frontier tree 0 t5_668root t5_668jobs t5_668frontier t5_668all
theorem t5_669choices : plan3735.choices=[2,2,2,9,3].map (options 5 1) := by rfl


theorem t5_669part0 : t5_669jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_669frontier : t5_669root.frontier 0=t5_669jobs := by rfl
theorem t5_669all : t5_669jobs.all (Job.check tree)=true := by
  simp only [t5_669jobs,List.all_append,List.all_nil,t5_669part0,Bool.and_self]
theorem t5_669checked : Checked tree [2,2,2,9,3] := by
  refine ⟨plan3735,valid3735,t5_669choices,?_⟩
  exact check_of_frontier tree 0 t5_669root t5_669jobs t5_669frontier t5_669all
theorem t5_670choices : plan3907.choices=[2,2,2,9,6].map (options 5 2) := by rfl


theorem t5_670part0 : t5_670jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_670frontier : t5_670root.frontier 0=t5_670jobs := by rfl
theorem t5_670all : t5_670jobs.all (Job.check tree)=true := by
  simp only [t5_670jobs,List.all_append,List.all_nil,t5_670part0,Bool.and_self]
theorem t5_670checked : Checked tree [2,2,2,9,6] := by
  refine ⟨plan3907,valid3907,t5_670choices,?_⟩
  exact check_of_frontier tree 0 t5_670root t5_670jobs t5_670frontier t5_670all
theorem t5_671choices : plan3908.choices=[2,2,2,9,7].map (options 5 2) := by rfl


theorem t5_671part0 : t5_671jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_671frontier : t5_671root.frontier 0=t5_671jobs := by rfl
theorem t5_671all : t5_671jobs.all (Job.check tree)=true := by
  simp only [t5_671jobs,List.all_append,List.all_nil,t5_671part0,Bool.and_self]
theorem t5_671checked : Checked tree [2,2,2,9,7] := by
  refine ⟨plan3908,valid3908,t5_671choices,?_⟩
  exact check_of_frontier tree 0 t5_671root t5_671jobs t5_671frontier t5_671all
theorem t5_672choices : plan3909.choices=[2,2,2,9,9].map (options 5 2) := by rfl


theorem t5_672part0 : t5_672jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_672frontier : t5_672root.frontier 0=t5_672jobs := by rfl
theorem t5_672all : t5_672jobs.all (Job.check tree)=true := by
  simp only [t5_672jobs,List.all_append,List.all_nil,t5_672part0,Bool.and_self]
theorem t5_672checked : Checked tree [2,2,2,9,9] := by
  refine ⟨plan3909,valid3909,t5_672choices,?_⟩
  exact check_of_frontier tree 0 t5_672root t5_672jobs t5_672frontier t5_672all
theorem t5_673choices : plan3910.choices=[2,2,2,9,10].map (options 5 2) := by rfl


theorem t5_673part0 : t5_673jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_673frontier : t5_673root.frontier 0=t5_673jobs := by rfl
theorem t5_673all : t5_673jobs.all (Job.check tree)=true := by
  simp only [t5_673jobs,List.all_append,List.all_nil,t5_673part0,Bool.and_self]
theorem t5_673checked : Checked tree [2,2,2,9,10] := by
  refine ⟨plan3910,valid3910,t5_673choices,?_⟩
  exact check_of_frontier tree 0 t5_673root t5_673jobs t5_673frontier t5_673all
theorem t5_674choices : plan3911.choices=[2,2,2,10,7].map (options 5 2) := by rfl


theorem t5_674part0 : t5_674jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_674frontier : t5_674root.frontier 0=t5_674jobs := by rfl
theorem t5_674all : t5_674jobs.all (Job.check tree)=true := by
  simp only [t5_674jobs,List.all_append,List.all_nil,t5_674part0,Bool.and_self]
theorem t5_674checked : Checked tree [2,2,2,10,7] := by
  refine ⟨plan3911,valid3911,t5_674choices,?_⟩
  exact check_of_frontier tree 0 t5_674root t5_674jobs t5_674frontier t5_674all
theorem t5_675choices : plan3912.choices=[2,2,2,10,10].map (options 5 2) := by rfl


theorem t5_675part0 : t5_675jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_675frontier : t5_675root.frontier 0=t5_675jobs := by rfl
theorem t5_675all : t5_675jobs.all (Job.check tree)=true := by
  simp only [t5_675jobs,List.all_append,List.all_nil,t5_675part0,Bool.and_self]
theorem t5_675checked : Checked tree [2,2,2,10,10] := by
  refine ⟨plan3912,valid3912,t5_675choices,?_⟩
  exact check_of_frontier tree 0 t5_675root t5_675jobs t5_675frontier t5_675all
theorem t5_676choices : plan3671.choices=[2,2,3,3,3].map (options 5 0) := by rfl


theorem t5_676part0 : t5_676jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_676frontier : t5_676root.frontier 0=t5_676jobs := by rfl
theorem t5_676all : t5_676jobs.all (Job.check tree)=true := by
  simp only [t5_676jobs,List.all_append,List.all_nil,t5_676part0,Bool.and_self]
theorem t5_676checked : Checked tree [2,2,3,3,3] := by
  refine ⟨plan3671,valid3671,t5_676choices,?_⟩
  exact check_of_frontier tree 0 t5_676root t5_676jobs t5_676frontier t5_676all
theorem t5_677choices : plan3736.choices=[2,2,3,3,6].map (options 5 1) := by rfl


theorem t5_677part0 : t5_677jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_677frontier : t5_677root.frontier 0=t5_677jobs := by rfl
theorem t5_677all : t5_677jobs.all (Job.check tree)=true := by
  simp only [t5_677jobs,List.all_append,List.all_nil,t5_677part0,Bool.and_self]
theorem t5_677checked : Checked tree [2,2,3,3,6] := by
  refine ⟨plan3736,valid3736,t5_677choices,?_⟩
  exact check_of_frontier tree 0 t5_677root t5_677jobs t5_677frontier t5_677all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks014 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_630checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_631checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_632checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_633checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_618checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_634checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_635checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_636checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_637checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_638checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_639checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_640checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_641checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_642checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_643checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_619checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_644checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_645checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_646checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_647checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_648checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_649checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_650checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_651checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_652checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_653checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_620checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_654checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_655checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_656checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_657checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_658checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_659checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_660checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_661checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_662checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_663checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_621checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_664checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_665checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_666checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_667checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_668checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_669checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_670checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_671checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_672checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_673checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_622checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_674checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_675checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_676checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_677checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_623checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_624checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_625checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_626checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_627checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_628checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_629checked⟩
