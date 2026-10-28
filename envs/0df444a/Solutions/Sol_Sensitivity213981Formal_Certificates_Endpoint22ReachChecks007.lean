-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks007
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:07:01.634634+00:00
-- url     : https://prove2.me/submissions/761b5cbc-7c43-4a50-b7ab-45930f38713b

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks007
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans042
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

























































































































theorem valid445 : plan445.Valid := valid_step _ _ _ valid87 (by decide +kernel)

theorem valid446 : plan446.Valid := valid_step _ _ _ valid87 (by decide +kernel)





theorem valid449 : plan449.Valid := valid_step _ _ _ valid90 (by decide +kernel)

theorem valid450 : plan450.Valid := valid_step _ _ _ valid91 (by decide +kernel)



theorem valid452 : plan452.Valid := valid_step _ _ _ valid93 (by decide +kernel)

theorem valid453 : plan453.Valid := valid_step _ _ _ valid88 (by decide +kernel)

theorem valid454 : plan454.Valid := valid_step _ _ _ valid90 (by decide +kernel)

theorem valid455 : plan455.Valid := valid_step _ _ _ valid91 (by decide +kernel)

theorem valid456 : plan456.Valid := valid_step _ _ _ valid93 (by decide +kernel)

theorem valid457 : plan457.Valid := valid_step _ _ _ valid88 (by decide +kernel)

theorem valid458 : plan458.Valid := valid_step _ _ _ valid88 (by decide +kernel)







theorem valid462 : plan462.Valid := valid_step _ _ _ valid94 (by decide +kernel)

theorem valid463 : plan463.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid464 : plan464.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid465 : plan465.Valid := valid_step _ _ _ valid99 (by decide +kernel)





theorem valid468 : plan468.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid469 : plan469.Valid := valid_step _ _ _ valid97 (by decide +kernel)



theorem valid471 : plan471.Valid := valid_step _ _ _ valid99 (by decide +kernel)

theorem valid472 : plan472.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid473 : plan473.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid474 : plan474.Valid := valid_step _ _ _ valid99 (by decide +kernel)

theorem valid475 : plan475.Valid := valid_step _ _ _ valid97 (by decide +kernel)



theorem valid477 : plan477.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid478 : plan478.Valid := valid_step _ _ _ valid97 (by decide +kernel)



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







theorem valid491 : plan491.Valid := valid_step _ _ _ valid103 (by decide +kernel)





theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)





theorem valid500 : plan500.Valid := valid_step _ _ _ valid103 (by decide +kernel)





theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)



















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

theorem valid1249 : plan1249.Valid := valid_step _ _ _ valid446 (by decide +kernel)

theorem valid1250 : plan1250.Valid := valid_step _ _ _ valid446 (by decide +kernel)

theorem valid1251 : plan1251.Valid := valid_step _ _ _ valid455 (by decide +kernel)





theorem valid1254 : plan1254.Valid := valid_step _ _ _ valid449 (by decide +kernel)

theorem valid1255 : plan1255.Valid := valid_step _ _ _ valid450 (by decide +kernel)



theorem valid1257 : plan1257.Valid := valid_step _ _ _ valid452 (by decide +kernel)



theorem valid1259 : plan1259.Valid := valid_step _ _ _ valid454 (by decide +kernel)

theorem valid1260 : plan1260.Valid := valid_step _ _ _ valid455 (by decide +kernel)

theorem valid1261 : plan1261.Valid := valid_step _ _ _ valid456 (by decide +kernel)

theorem valid1262 : plan1262.Valid := valid_step _ _ _ valid457 (by decide +kernel)

theorem valid1263 : plan1263.Valid := valid_step _ _ _ valid458 (by decide +kernel)



theorem valid1265 : plan1265.Valid := valid_step _ _ _ valid454 (by decide +kernel)

theorem valid1266 : plan1266.Valid := valid_step _ _ _ valid455 (by decide +kernel)

theorem valid1267 : plan1267.Valid := valid_step _ _ _ valid456 (by decide +kernel)

theorem valid1268 : plan1268.Valid := valid_step _ _ _ valid453 (by decide +kernel)

theorem valid1269 : plan1269.Valid := valid_step _ _ _ valid453 (by decide +kernel)

theorem valid1270 : plan1270.Valid := valid_step _ _ _ valid473 (by decide +kernel)

theorem valid1271 : plan1271.Valid := valid_step _ _ _ valid475 (by decide +kernel)

theorem valid1272 : plan1272.Valid := valid_step _ _ _ valid481 (by decide +kernel)



















theorem valid1282 : plan1282.Valid := valid_step _ _ _ valid468 (by decide +kernel)

theorem valid1283 : plan1283.Valid := valid_step _ _ _ valid469 (by decide +kernel)



theorem valid1285 : plan1285.Valid := valid_step _ _ _ valid471 (by decide +kernel)

theorem valid1286 : plan1286.Valid := valid_step _ _ _ valid472 (by decide +kernel)

theorem valid1287 : plan1287.Valid := valid_step _ _ _ valid473 (by decide +kernel)

theorem valid1288 : plan1288.Valid := valid_step _ _ _ valid474 (by decide +kernel)

theorem valid1289 : plan1289.Valid := valid_step _ _ _ valid475 (by decide +kernel)



theorem valid1291 : plan1291.Valid := valid_step _ _ _ valid477 (by decide +kernel)

theorem valid1292 : plan1292.Valid := valid_step _ _ _ valid478 (by decide +kernel)



theorem valid1294 : plan1294.Valid := valid_step _ _ _ valid480 (by decide +kernel)

theorem valid1295 : plan1295.Valid := valid_step _ _ _ valid481 (by decide +kernel)

theorem valid1296 : plan1296.Valid := valid_step _ _ _ valid482 (by decide +kernel)









theorem valid1301 : plan1301.Valid := valid_step _ _ _ valid472 (by decide +kernel)

theorem valid1302 : plan1302.Valid := valid_step _ _ _ valid473 (by decide +kernel)

theorem valid1303 : plan1303.Valid := valid_step _ _ _ valid474 (by decide +kernel)

theorem valid1304 : plan1304.Valid := valid_step _ _ _ valid475 (by decide +kernel)

theorem valid1305 : plan1305.Valid := valid_step _ _ _ valid481 (by decide +kernel)

theorem valid1306 : plan1306.Valid := valid_step _ _ _ valid482 (by decide +kernel)

theorem valid1307 : plan1307.Valid := valid_step _ _ _ valid464 (by decide +kernel)



theorem valid1309 : plan1309.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1310 : plan1310.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1311 : plan1311.Valid := valid_step _ _ _ valid465 (by decide +kernel)





theorem valid1314 : plan1314.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1315 : plan1315.Valid := valid_step _ _ _ valid462 (by decide +kernel)

theorem valid1316 : plan1316.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1317 : plan1317.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1318 : plan1318.Valid := valid_step _ _ _ valid465 (by decide +kernel)













































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



































theorem valid2514 : plan2514.Valid := valid_step _ _ _ valid1249 (by decide +kernel)

theorem valid2515 : plan2515.Valid := valid_step _ _ _ valid1250 (by decide +kernel)



theorem valid2517 : plan2517.Valid := valid_step _ _ _ valid1248 (by decide +kernel)

theorem valid2518 : plan2518.Valid := valid_step _ _ _ valid1249 (by decide +kernel)

theorem valid2519 : plan2519.Valid := valid_step _ _ _ valid1250 (by decide +kernel)



theorem valid2521 : plan2521.Valid := valid_step _ _ _ valid1251 (by decide +kernel)

theorem valid2522 : plan2522.Valid := valid_step _ _ _ valid1255 (by decide +kernel)

theorem valid2523 : plan2523.Valid := valid_step _ _ _ valid1259 (by decide +kernel)

theorem valid2524 : plan2524.Valid := valid_step _ _ _ valid1260 (by decide +kernel)

theorem valid2525 : plan2525.Valid := valid_step _ _ _ valid1261 (by decide +kernel)

theorem valid2526 : plan2526.Valid := valid_step _ _ _ valid1265 (by decide +kernel)

theorem valid2527 : plan2527.Valid := valid_step _ _ _ valid1266 (by decide +kernel)

theorem valid2528 : plan2528.Valid := valid_step _ _ _ valid1267 (by decide +kernel)

theorem valid2529 : plan2529.Valid := valid_step _ _ _ valid1268 (by decide +kernel)

theorem valid2530 : plan2530.Valid := valid_step _ _ _ valid1269 (by decide +kernel)





theorem valid2533 : plan2533.Valid := valid_step _ _ _ valid1254 (by decide +kernel)

theorem valid2534 : plan2534.Valid := valid_step _ _ _ valid1255 (by decide +kernel)



theorem valid2536 : plan2536.Valid := valid_step _ _ _ valid1257 (by decide +kernel)



theorem valid2538 : plan2538.Valid := valid_step _ _ _ valid1259 (by decide +kernel)

theorem valid2539 : plan2539.Valid := valid_step _ _ _ valid1260 (by decide +kernel)

theorem valid2540 : plan2540.Valid := valid_step _ _ _ valid1261 (by decide +kernel)

theorem valid2541 : plan2541.Valid := valid_step _ _ _ valid1262 (by decide +kernel)

theorem valid2542 : plan2542.Valid := valid_step _ _ _ valid1263 (by decide +kernel)



theorem valid2544 : plan2544.Valid := valid_step _ _ _ valid1265 (by decide +kernel)

theorem valid2545 : plan2545.Valid := valid_step _ _ _ valid1266 (by decide +kernel)

theorem valid2546 : plan2546.Valid := valid_step _ _ _ valid1267 (by decide +kernel)

























theorem valid2559 : plan2559.Valid := valid_step _ _ _ valid1270 (by decide +kernel)

theorem valid2560 : plan2560.Valid := valid_step _ _ _ valid1271 (by decide +kernel)

theorem valid2561 : plan2561.Valid := valid_step _ _ _ valid1272 (by decide +kernel)

theorem valid2562 : plan2562.Valid := valid_step _ _ _ valid1283 (by decide +kernel)

theorem valid2563 : plan2563.Valid := valid_step _ _ _ valid1286 (by decide +kernel)

theorem valid2564 : plan2564.Valid := valid_step _ _ _ valid1287 (by decide +kernel)

theorem valid2565 : plan2565.Valid := valid_step _ _ _ valid1288 (by decide +kernel)

theorem valid2566 : plan2566.Valid := valid_step _ _ _ valid1289 (by decide +kernel)

theorem valid2567 : plan2567.Valid := valid_step _ _ _ valid1292 (by decide +kernel)

theorem valid2568 : plan2568.Valid := valid_step _ _ _ valid1295 (by decide +kernel)

theorem valid2569 : plan2569.Valid := valid_step _ _ _ valid1296 (by decide +kernel)

theorem valid2570 : plan2570.Valid := valid_step _ _ _ valid1301 (by decide +kernel)

theorem valid2571 : plan2571.Valid := valid_step _ _ _ valid1302 (by decide +kernel)

theorem valid2572 : plan2572.Valid := valid_step _ _ _ valid1303 (by decide +kernel)

theorem valid2573 : plan2573.Valid := valid_step _ _ _ valid1304 (by decide +kernel)

theorem valid2574 : plan2574.Valid := valid_step _ _ _ valid1305 (by decide +kernel)

theorem valid2575 : plan2575.Valid := valid_step _ _ _ valid1306 (by decide +kernel)

theorem valid2576 : plan2576.Valid := valid_step _ _ _ valid1307 (by decide +kernel)

theorem valid2577 : plan2577.Valid := valid_step _ _ _ valid1309 (by decide +kernel)

theorem valid2578 : plan2578.Valid := valid_step _ _ _ valid1310 (by decide +kernel)

theorem valid2579 : plan2579.Valid := valid_step _ _ _ valid1311 (by decide +kernel)

theorem valid2580 : plan2580.Valid := valid_step _ _ _ valid1314 (by decide +kernel)

theorem valid2581 : plan2581.Valid := valid_step _ _ _ valid1316 (by decide +kernel)

theorem valid2582 : plan2582.Valid := valid_step _ _ _ valid1317 (by decide +kernel)

theorem valid2583 : plan2583.Valid := valid_step _ _ _ valid1318 (by decide +kernel)

















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



























theorem valid3662 : plan3662.Valid := valid_step _ _ _ valid2514 (by decide +kernel)

theorem valid3663 : plan3663.Valid := valid_step _ _ _ valid2515 (by decide +kernel)

theorem valid3664 : plan3664.Valid := valid_step _ _ _ valid2517 (by decide +kernel)

theorem valid3665 : plan3665.Valid := valid_step _ _ _ valid2518 (by decide +kernel)

theorem valid3666 : plan3666.Valid := valid_step _ _ _ valid2519 (by decide +kernel)























































theorem valid3694 : plan3694.Valid := valid_step _ _ _ valid2521 (by decide +kernel)

theorem valid3695 : plan3695.Valid := valid_step _ _ _ valid2522 (by decide +kernel)

theorem valid3696 : plan3696.Valid := valid_step _ _ _ valid2523 (by decide +kernel)

theorem valid3697 : plan3697.Valid := valid_step _ _ _ valid2524 (by decide +kernel)

theorem valid3698 : plan3698.Valid := valid_step _ _ _ valid2525 (by decide +kernel)

theorem valid3699 : plan3699.Valid := valid_step _ _ _ valid2526 (by decide +kernel)

theorem valid3700 : plan3700.Valid := valid_step _ _ _ valid2527 (by decide +kernel)

theorem valid3701 : plan3701.Valid := valid_step _ _ _ valid2528 (by decide +kernel)

theorem valid3702 : plan3702.Valid := valid_step _ _ _ valid2529 (by decide +kernel)

theorem valid3703 : plan3703.Valid := valid_step _ _ _ valid2530 (by decide +kernel)

theorem valid3704 : plan3704.Valid := valid_step _ _ _ valid2533 (by decide +kernel)

theorem valid3705 : plan3705.Valid := valid_step _ _ _ valid2534 (by decide +kernel)

theorem valid3706 : plan3706.Valid := valid_step _ _ _ valid2536 (by decide +kernel)

theorem valid3707 : plan3707.Valid := valid_step _ _ _ valid2538 (by decide +kernel)

theorem valid3708 : plan3708.Valid := valid_step _ _ _ valid2539 (by decide +kernel)

theorem valid3709 : plan3709.Valid := valid_step _ _ _ valid2540 (by decide +kernel)

theorem valid3710 : plan3710.Valid := valid_step _ _ _ valid2541 (by decide +kernel)

theorem valid3711 : plan3711.Valid := valid_step _ _ _ valid2542 (by decide +kernel)

theorem valid3712 : plan3712.Valid := valid_step _ _ _ valid2544 (by decide +kernel)

theorem valid3713 : plan3713.Valid := valid_step _ _ _ valid2545 (by decide +kernel)

theorem valid3714 : plan3714.Valid := valid_step _ _ _ valid2546 (by decide +kernel)




























































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



theorem valid1346 : plan1346.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1347 : plan1347.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1348 : plan1348.Valid := valid_step _ _ _ valid503 (by decide +kernel)















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



theorem valid1378 : plan1378.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1379 : plan1379.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1380 : plan1380.Valid := valid_step _ _ _ valid503 (by decide +kernel)



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



theorem valid2595 : plan2595.Valid := valid_step _ _ _ valid1285 (by decide +kernel)

theorem valid2596 : plan2596.Valid := valid_step _ _ _ valid1286 (by decide +kernel)

theorem valid2597 : plan2597.Valid := valid_step _ _ _ valid1287 (by decide +kernel)

theorem valid2598 : plan2598.Valid := valid_step _ _ _ valid1288 (by decide +kernel)

theorem valid2599 : plan2599.Valid := valid_step _ _ _ valid1289 (by decide +kernel)



theorem valid2601 : plan2601.Valid := valid_step _ _ _ valid1291 (by decide +kernel)

theorem valid2602 : plan2602.Valid := valid_step _ _ _ valid1292 (by decide +kernel)



theorem valid2604 : plan2604.Valid := valid_step _ _ _ valid1294 (by decide +kernel)

theorem valid2605 : plan2605.Valid := valid_step _ _ _ valid1295 (by decide +kernel)

theorem valid2606 : plan2606.Valid := valid_step _ _ _ valid1296 (by decide +kernel)







theorem valid2610 : plan2610.Valid := valid_step _ _ _ valid1301 (by decide +kernel)

theorem valid2611 : plan2611.Valid := valid_step _ _ _ valid1302 (by decide +kernel)

theorem valid2612 : plan2612.Valid := valid_step _ _ _ valid1303 (by decide +kernel)

theorem valid2613 : plan2613.Valid := valid_step _ _ _ valid1304 (by decide +kernel)













































































































theorem valid2668 : plan2668.Valid := valid_step _ _ _ valid1315 (by decide +kernel)

theorem valid2669 : plan2669.Valid := valid_step _ _ _ valid1346 (by decide +kernel)

theorem valid2670 : plan2670.Valid := valid_step _ _ _ valid1347 (by decide +kernel)

theorem valid2671 : plan2671.Valid := valid_step _ _ _ valid1348 (by decide +kernel)

theorem valid2672 : plan2672.Valid := valid_step _ _ _ valid1356 (by decide +kernel)

theorem valid2673 : plan2673.Valid := valid_step _ _ _ valid1359 (by decide +kernel)

theorem valid2674 : plan2674.Valid := valid_step _ _ _ valid1360 (by decide +kernel)

theorem valid2675 : plan2675.Valid := valid_step _ _ _ valid1361 (by decide +kernel)

theorem valid2676 : plan2676.Valid := valid_step _ _ _ valid1362 (by decide +kernel)

theorem valid2677 : plan2677.Valid := valid_step _ _ _ valid1365 (by decide +kernel)

theorem valid2678 : plan2678.Valid := valid_step _ _ _ valid1368 (by decide +kernel)

theorem valid2679 : plan2679.Valid := valid_step _ _ _ valid1369 (by decide +kernel)

theorem valid2680 : plan2680.Valid := valid_step _ _ _ valid1370 (by decide +kernel)

theorem valid2681 : plan2681.Valid := valid_step _ _ _ valid1371 (by decide +kernel)

theorem valid2682 : plan2682.Valid := valid_step _ _ _ valid1372 (by decide +kernel)

theorem valid2683 : plan2683.Valid := valid_step _ _ _ valid1373 (by decide +kernel)

theorem valid2684 : plan2684.Valid := valid_step _ _ _ valid1374 (by decide +kernel)

theorem valid2685 : plan2685.Valid := valid_step _ _ _ valid1375 (by decide +kernel)

theorem valid2686 : plan2686.Valid := valid_step _ _ _ valid1376 (by decide +kernel)

theorem valid2687 : plan2687.Valid := valid_step _ _ _ valid1378 (by decide +kernel)

theorem valid2688 : plan2688.Valid := valid_step _ _ _ valid1379 (by decide +kernel)
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







































































































































theorem valid3812 : plan3812.Valid := valid_step _ _ _ valid2668 (by decide +kernel)

theorem valid3813 : plan3813.Valid := valid_step _ _ _ valid2559 (by decide +kernel)

theorem valid3814 : plan3814.Valid := valid_step _ _ _ valid2560 (by decide +kernel)

theorem valid3815 : plan3815.Valid := valid_step _ _ _ valid2561 (by decide +kernel)

theorem valid3816 : plan3816.Valid := valid_step _ _ _ valid2562 (by decide +kernel)

theorem valid3817 : plan3817.Valid := valid_step _ _ _ valid2563 (by decide +kernel)

theorem valid3818 : plan3818.Valid := valid_step _ _ _ valid2564 (by decide +kernel)

theorem valid3819 : plan3819.Valid := valid_step _ _ _ valid2565 (by decide +kernel)

theorem valid3820 : plan3820.Valid := valid_step _ _ _ valid2566 (by decide +kernel)

theorem valid3821 : plan3821.Valid := valid_step _ _ _ valid2567 (by decide +kernel)

theorem valid3822 : plan3822.Valid := valid_step _ _ _ valid2568 (by decide +kernel)

theorem valid3823 : plan3823.Valid := valid_step _ _ _ valid2569 (by decide +kernel)

theorem valid3824 : plan3824.Valid := valid_step _ _ _ valid2570 (by decide +kernel)

theorem valid3825 : plan3825.Valid := valid_step _ _ _ valid2571 (by decide +kernel)

theorem valid3826 : plan3826.Valid := valid_step _ _ _ valid2572 (by decide +kernel)

theorem valid3827 : plan3827.Valid := valid_step _ _ _ valid2573 (by decide +kernel)

theorem valid3828 : plan3828.Valid := valid_step _ _ _ valid2574 (by decide +kernel)

theorem valid3829 : plan3829.Valid := valid_step _ _ _ valid2575 (by decide +kernel)

theorem valid3830 : plan3830.Valid := valid_step _ _ _ valid2576 (by decide +kernel)

theorem valid3831 : plan3831.Valid := valid_step _ _ _ valid2577 (by decide +kernel)

theorem valid3832 : plan3832.Valid := valid_step _ _ _ valid2578 (by decide +kernel)

theorem valid3833 : plan3833.Valid := valid_step _ _ _ valid2579 (by decide +kernel)

theorem valid3834 : plan3834.Valid := valid_step _ _ _ valid2580 (by decide +kernel)

theorem valid3835 : plan3835.Valid := valid_step _ _ _ valid2581 (by decide +kernel)

theorem valid3836 : plan3836.Valid := valid_step _ _ _ valid2582 (by decide +kernel)

theorem valid3837 : plan3837.Valid := valid_step _ _ _ valid2583 (by decide +kernel)

theorem valid3838 : plan3838.Valid := valid_step _ _ _ valid2592 (by decide +kernel)

theorem valid3839 : plan3839.Valid := valid_step _ _ _ valid2593 (by decide +kernel)

theorem valid3840 : plan3840.Valid := valid_step _ _ _ valid2595 (by decide +kernel)
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

theorem valid2689 : plan2689.Valid := valid_step _ _ _ valid1380 (by decide +kernel)

theorem valid2690 : plan2690.Valid := valid_step _ _ _ valid1385 (by decide +kernel)

theorem valid2691 : plan2691.Valid := valid_step _ _ _ valid1386 (by decide +kernel)

theorem valid2692 : plan2692.Valid := valid_step _ _ _ valid1387 (by decide +kernel)

theorem valid2693 : plan2693.Valid := valid_step _ _ _ valid1388 (by decide +kernel)

theorem valid2694 : plan2694.Valid := valid_step _ _ _ valid1391 (by decide +kernel)

theorem valid2695 : plan2695.Valid := valid_step _ _ _ valid1394 (by decide +kernel)

theorem valid2696 : plan2696.Valid := valid_step _ _ _ valid1395 (by decide +kernel)

theorem valid2697 : plan2697.Valid := valid_step _ _ _ valid1396 (by decide +kernel)

theorem valid2698 : plan2698.Valid := valid_step _ _ _ valid1397 (by decide +kernel)

theorem valid2699 : plan2699.Valid := valid_step _ _ _ valid1398 (by decide +kernel)










































































































































































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































































































































































theorem valid2864 : plan2864.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2865 : plan2865.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2866 : plan2866.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2867 : plan2867.Valid := valid_step _ _ _ valid1344 (by decide +kernel)



theorem valid2869 : plan2869.Valid := valid_step _ _ _ valid1382 (by decide +kernel)

theorem valid2870 : plan2870.Valid := valid_step _ _ _ valid1383 (by decide +kernel)

theorem valid2871 : plan2871.Valid := valid_step _ _ _ valid1384 (by decide +kernel)


















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













































































































theorem valid4087 : plan4087.Valid := valid_step _ _ _ valid2864 (by decide +kernel)

theorem valid4088 : plan4088.Valid := valid_step _ _ _ valid2865 (by decide +kernel)

theorem valid4089 : plan4089.Valid := valid_step _ _ _ valid2866 (by decide +kernel)

theorem valid4090 : plan4090.Valid := valid_step _ _ _ valid2867 (by decide +kernel)

theorem valid4091 : plan4091.Valid := valid_step _ _ _ valid2869 (by decide +kernel)

theorem valid4092 : plan4092.Valid := valid_step _ _ _ valid2870 (by decide +kernel)

theorem valid4093 : plan4093.Valid := valid_step _ _ _ valid2871 (by decide +kernel)

theorem valid4094 : plan4094.Valid := valid_step _ _ _ valid2669 (by decide +kernel)

theorem valid4095 : plan4095.Valid := valid_step _ _ _ valid2670 (by decide +kernel)

theorem valid4096 : plan4096.Valid := valid_step _ _ _ valid2671 (by decide +kernel)

theorem valid4097 : plan4097.Valid := valid_step _ _ _ valid2672 (by decide +kernel)

theorem valid4098 : plan4098.Valid := valid_step _ _ _ valid2673 (by decide +kernel)

theorem valid4099 : plan4099.Valid := valid_step _ _ _ valid2674 (by decide +kernel)

theorem valid4100 : plan4100.Valid := valid_step _ _ _ valid2675 (by decide +kernel)

theorem valid4101 : plan4101.Valid := valid_step _ _ _ valid2676 (by decide +kernel)

theorem valid4102 : plan4102.Valid := valid_step _ _ _ valid2677 (by decide +kernel)

theorem valid4103 : plan4103.Valid := valid_step _ _ _ valid2678 (by decide +kernel)

theorem valid4104 : plan4104.Valid := valid_step _ _ _ valid2679 (by decide +kernel)

theorem valid4105 : plan4105.Valid := valid_step _ _ _ valid2680 (by decide +kernel)

theorem valid4106 : plan4106.Valid := valid_step _ _ _ valid2681 (by decide +kernel)

theorem valid4107 : plan4107.Valid := valid_step _ _ _ valid2682 (by decide +kernel)

theorem valid4108 : plan4108.Valid := valid_step _ _ _ valid2683 (by decide +kernel)

theorem valid4109 : plan4109.Valid := valid_step _ _ _ valid2684 (by decide +kernel)

theorem valid4110 : plan4110.Valid := valid_step _ _ _ valid2685 (by decide +kernel)

theorem valid4111 : plan4111.Valid := valid_step _ _ _ valid2686 (by decide +kernel)

theorem valid4112 : plan4112.Valid := valid_step _ _ _ valid2687 (by decide +kernel)

theorem valid4113 : plan4113.Valid := valid_step _ _ _ valid2688 (by decide +kernel)

theorem valid4114 : plan4114.Valid := valid_step _ _ _ valid2689 (by decide +kernel)

theorem valid4115 : plan4115.Valid := valid_step _ _ _ valid2690 (by decide +kernel)

theorem valid4116 : plan4116.Valid := valid_step _ _ _ valid2691 (by decide +kernel)

theorem valid4117 : plan4117.Valid := valid_step _ _ _ valid2692 (by decide +kernel)

theorem valid4118 : plan4118.Valid := valid_step _ _ _ valid2693 (by decide +kernel)

theorem valid4119 : plan4119.Valid := valid_step _ _ _ valid2694 (by decide +kernel)

theorem valid4120 : plan4120.Valid := valid_step _ _ _ valid2695 (by decide +kernel)

theorem valid4121 : plan4121.Valid := valid_step _ _ _ valid2696 (by decide +kernel)

theorem valid4122 : plan4122.Valid := valid_step _ _ _ valid2697 (by decide +kernel)

theorem valid4123 : plan4123.Valid := valid_step _ _ _ valid2698 (by decide +kernel)

theorem valid4124 : plan4124.Valid := valid_step _ _ _ valid2699 (by decide +kernel)








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





theorem valid3099 : plan3099.Valid := valid_step _ _ _ valid1457 (by decide +kernel)





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











theorem valid4518 : plan4518.Valid := valid_step _ _ _ valid3083 (by decide +kernel)

theorem valid4519 : plan4519.Valid := valid_step _ _ _ valid3084 (by decide +kernel)

theorem valid4520 : plan4520.Valid := valid_step _ _ _ valid3085 (by decide +kernel)

theorem valid4521 : plan4521.Valid := valid_step _ _ _ valid3086 (by decide +kernel)

theorem valid4522 : plan4522.Valid := valid_step _ _ _ valid3087 (by decide +kernel)

theorem valid4523 : plan4523.Valid := valid_step _ _ _ valid3088 (by decide +kernel)

theorem valid4524 : plan4524.Valid := valid_step _ _ _ valid3089 (by decide +kernel)

theorem valid4525 : plan4525.Valid := valid_step _ _ _ valid3093 (by decide +kernel)

theorem valid4526 : plan4526.Valid := valid_step _ _ _ valid3094 (by decide +kernel)

theorem valid4527 : plan4527.Valid := valid_step _ _ _ valid3095 (by decide +kernel)

theorem valid4528 : plan4528.Valid := valid_step _ _ _ valid3096 (by decide +kernel)

theorem valid4529 : plan4529.Valid := valid_step _ _ _ valid3099 (by decide +kernel)

theorem valid4530 : plan4530.Valid := valid_step _ _ _ valid3102 (by decide +kernel)

theorem valid4531 : plan4531.Valid := valid_step _ _ _ valid3103 (by decide +kernel)

theorem valid4532 : plan4532.Valid := valid_step _ _ _ valid3104 (by decide +kernel)

theorem valid4533 : plan4533.Valid := valid_step _ _ _ valid3105 (by decide +kernel)

theorem valid4534 : plan4534.Valid := valid_step _ _ _ valid3106 (by decide +kernel)

theorem valid4535 : plan4535.Valid := valid_step _ _ _ valid3107 (by decide +kernel)

theorem valid4536 : plan4536.Valid := valid_step _ _ _ valid3108 (by decide +kernel)

theorem valid4537 : plan4537.Valid := valid_step _ _ _ valid3109 (by decide +kernel)

theorem valid4538 : plan4538.Valid := valid_step _ _ _ valid3110 (by decide +kernel)












































































































































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

theorem valid3841 : plan3841.Valid := valid_step _ _ _ valid2596 (by decide +kernel)

theorem valid3842 : plan3842.Valid := valid_step _ _ _ valid2597 (by decide +kernel)

theorem valid3843 : plan3843.Valid := valid_step _ _ _ valid2598 (by decide +kernel)

theorem valid3844 : plan3844.Valid := valid_step _ _ _ valid2599 (by decide +kernel)

theorem valid3845 : plan3845.Valid := valid_step _ _ _ valid2601 (by decide +kernel)

theorem valid3846 : plan3846.Valid := valid_step _ _ _ valid2602 (by decide +kernel)

theorem valid3847 : plan3847.Valid := valid_step _ _ _ valid2604 (by decide +kernel)

theorem valid3848 : plan3848.Valid := valid_step _ _ _ valid2605 (by decide +kernel)

theorem valid3849 : plan3849.Valid := valid_step _ _ _ valid2606 (by decide +kernel)

theorem valid3850 : plan3850.Valid := valid_step _ _ _ valid2610 (by decide +kernel)

theorem valid3851 : plan3851.Valid := valid_step _ _ _ valid2611 (by decide +kernel)

theorem valid3852 : plan3852.Valid := valid_step _ _ _ valid2612 (by decide +kernel)

theorem valid3853 : plan3853.Valid := valid_step _ _ _ valid2613 (by decide +kernel)






































































































































































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
theorem t5_232choices : plan4087.choices=[0,9,3,6,10].map (options 5 3) := by rfl


theorem t5_232part0 : t5_232jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_232frontier : t5_232root.frontier 0=t5_232jobs := by rfl
theorem t5_232all : t5_232jobs.all (Job.check tree)=true := by
  simp only [t5_232jobs,List.all_append,List.all_nil,t5_232part0,Bool.and_self]
theorem t5_232checked : Checked tree [0,9,3,6,10] := by
  refine ⟨plan4087,valid4087,t5_232choices,?_⟩
  exact check_of_frontier tree 0 t5_232root t5_232jobs t5_232frontier t5_232all
theorem t5_233choices : plan4088.choices=[0,9,3,7,7].map (options 5 3) := by rfl


theorem t5_233part0 : t5_233jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_233frontier : t5_233root.frontier 0=t5_233jobs := by rfl
theorem t5_233all : t5_233jobs.all (Job.check tree)=true := by
  simp only [t5_233jobs,List.all_append,List.all_nil,t5_233part0,Bool.and_self]
theorem t5_233checked : Checked tree [0,9,3,7,7] := by
  refine ⟨plan4088,valid4088,t5_233choices,?_⟩
  exact check_of_frontier tree 0 t5_233root t5_233jobs t5_233frontier t5_233all
theorem t5_234choices : plan4089.choices=[0,9,3,10,7].map (options 5 3) := by rfl


theorem t5_234part0 : t5_234jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_234frontier : t5_234root.frontier 0=t5_234jobs := by rfl
theorem t5_234all : t5_234jobs.all (Job.check tree)=true := by
  simp only [t5_234jobs,List.all_append,List.all_nil,t5_234part0,Bool.and_self]
theorem t5_234checked : Checked tree [0,9,3,10,7] := by
  refine ⟨plan4089,valid4089,t5_234choices,?_⟩
  exact check_of_frontier tree 0 t5_234root t5_234jobs t5_234frontier t5_234all
theorem t5_235choices : plan4090.choices=[0,9,3,10,10].map (options 5 3) := by rfl


theorem t5_235part0 : t5_235jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_235frontier : t5_235root.frontier 0=t5_235jobs := by rfl
theorem t5_235all : t5_235jobs.all (Job.check tree)=true := by
  simp only [t5_235jobs,List.all_append,List.all_nil,t5_235part0,Bool.and_self]
theorem t5_235checked : Checked tree [0,9,3,10,10] := by
  refine ⟨plan4090,valid4090,t5_235choices,?_⟩
  exact check_of_frontier tree 0 t5_235root t5_235jobs t5_235frontier t5_235all
theorem t5_236choices : plan4518.choices=[0,9,6,6,6].map (options 5 4) := by rfl


theorem t5_236part0 : t5_236jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_236frontier : t5_236root.frontier 0=t5_236jobs := by rfl
theorem t5_236all : t5_236jobs.all (Job.check tree)=true := by
  simp only [t5_236jobs,List.all_append,List.all_nil,t5_236part0,Bool.and_self]
theorem t5_236checked : Checked tree [0,9,6,6,6] := by
  refine ⟨plan4518,valid4518,t5_236choices,?_⟩
  exact check_of_frontier tree 0 t5_236root t5_236jobs t5_236frontier t5_236all
theorem t5_237choices : plan4519.choices=[0,9,6,6,7].map (options 5 4) := by rfl


theorem t5_237part0 : t5_237jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_237frontier : t5_237root.frontier 0=t5_237jobs := by rfl
theorem t5_237all : t5_237jobs.all (Job.check tree)=true := by
  simp only [t5_237jobs,List.all_append,List.all_nil,t5_237part0,Bool.and_self]
theorem t5_237checked : Checked tree [0,9,6,6,7] := by
  refine ⟨plan4519,valid4519,t5_237choices,?_⟩
  exact check_of_frontier tree 0 t5_237root t5_237jobs t5_237frontier t5_237all
theorem t5_238choices : plan4520.choices=[0,9,6,6,10].map (options 5 4) := by rfl


theorem t5_238part0 : t5_238jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_238frontier : t5_238root.frontier 0=t5_238jobs := by rfl
theorem t5_238all : t5_238jobs.all (Job.check tree)=true := by
  simp only [t5_238jobs,List.all_append,List.all_nil,t5_238part0,Bool.and_self]
theorem t5_238checked : Checked tree [0,9,6,6,10] := by
  refine ⟨plan4520,valid4520,t5_238choices,?_⟩
  exact check_of_frontier tree 0 t5_238root t5_238jobs t5_238frontier t5_238all
theorem t5_239choices : plan4521.choices=[0,9,6,7,7].map (options 5 4) := by rfl


theorem t5_239part0 : t5_239jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_239frontier : t5_239root.frontier 0=t5_239jobs := by rfl
theorem t5_239all : t5_239jobs.all (Job.check tree)=true := by
  simp only [t5_239jobs,List.all_append,List.all_nil,t5_239part0,Bool.and_self]
theorem t5_239checked : Checked tree [0,9,6,7,7] := by
  refine ⟨plan4521,valid4521,t5_239choices,?_⟩
  exact check_of_frontier tree 0 t5_239root t5_239jobs t5_239frontier t5_239all
theorem t5_240choices : plan4522.choices=[0,9,6,10,7].map (options 5 4) := by rfl


theorem t5_240part0 : t5_240jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_240frontier : t5_240root.frontier 0=t5_240jobs := by rfl
theorem t5_240all : t5_240jobs.all (Job.check tree)=true := by
  simp only [t5_240jobs,List.all_append,List.all_nil,t5_240part0,Bool.and_self]
theorem t5_240checked : Checked tree [0,9,6,10,7] := by
  refine ⟨plan4522,valid4522,t5_240choices,?_⟩
  exact check_of_frontier tree 0 t5_240root t5_240jobs t5_240frontier t5_240all
theorem t5_241choices : plan4523.choices=[0,9,6,10,10].map (options 5 4) := by rfl


theorem t5_241part0 : t5_241jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_241frontier : t5_241root.frontier 0=t5_241jobs := by rfl
theorem t5_241all : t5_241jobs.all (Job.check tree)=true := by
  simp only [t5_241jobs,List.all_append,List.all_nil,t5_241part0,Bool.and_self]
theorem t5_241checked : Checked tree [0,9,6,10,10] := by
  refine ⟨plan4523,valid4523,t5_241choices,?_⟩
  exact check_of_frontier tree 0 t5_241root t5_241jobs t5_241frontier t5_241all
theorem t5_242choices : plan4524.choices=[0,9,7,7,7].map (options 5 4) := by rfl


theorem t5_242part0 : t5_242jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_242frontier : t5_242root.frontier 0=t5_242jobs := by rfl
theorem t5_242all : t5_242jobs.all (Job.check tree)=true := by
  simp only [t5_242jobs,List.all_append,List.all_nil,t5_242part0,Bool.and_self]
theorem t5_242checked : Checked tree [0,9,7,7,7] := by
  refine ⟨plan4524,valid4524,t5_242choices,?_⟩
  exact check_of_frontier tree 0 t5_242root t5_242jobs t5_242frontier t5_242all
theorem t5_243choices : plan3812.choices=[0,9,9,3,3].map (options 5 2) := by rfl


theorem t5_243part0 : t5_243jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_243frontier : t5_243root.frontier 0=t5_243jobs := by rfl
theorem t5_243all : t5_243jobs.all (Job.check tree)=true := by
  simp only [t5_243jobs,List.all_append,List.all_nil,t5_243part0,Bool.and_self]
theorem t5_243checked : Checked tree [0,9,9,3,3] := by
  refine ⟨plan3812,valid3812,t5_243choices,?_⟩
  exact check_of_frontier tree 0 t5_243root t5_243jobs t5_243frontier t5_243all
theorem t5_244choices : plan4091.choices=[0,9,9,3,6].map (options 5 3) := by rfl


theorem t5_244part0 : t5_244jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_244frontier : t5_244root.frontier 0=t5_244jobs := by rfl
theorem t5_244all : t5_244jobs.all (Job.check tree)=true := by
  simp only [t5_244jobs,List.all_append,List.all_nil,t5_244part0,Bool.and_self]
theorem t5_244checked : Checked tree [0,9,9,3,6] := by
  refine ⟨plan4091,valid4091,t5_244choices,?_⟩
  exact check_of_frontier tree 0 t5_244root t5_244jobs t5_244frontier t5_244all
theorem t5_245choices : plan4092.choices=[0,9,9,3,7].map (options 5 3) := by rfl


theorem t5_245part0 : t5_245jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_245frontier : t5_245root.frontier 0=t5_245jobs := by rfl
theorem t5_245all : t5_245jobs.all (Job.check tree)=true := by
  simp only [t5_245jobs,List.all_append,List.all_nil,t5_245part0,Bool.and_self]
theorem t5_245checked : Checked tree [0,9,9,3,7] := by
  refine ⟨plan4092,valid4092,t5_245choices,?_⟩
  exact check_of_frontier tree 0 t5_245root t5_245jobs t5_245frontier t5_245all
theorem t5_246choices : plan4093.choices=[0,9,9,3,10].map (options 5 3) := by rfl


theorem t5_246part0 : t5_246jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_246frontier : t5_246root.frontier 0=t5_246jobs := by rfl
theorem t5_246all : t5_246jobs.all (Job.check tree)=true := by
  simp only [t5_246jobs,List.all_append,List.all_nil,t5_246part0,Bool.and_self]
theorem t5_246checked : Checked tree [0,9,9,3,10] := by
  refine ⟨plan4093,valid4093,t5_246choices,?_⟩
  exact check_of_frontier tree 0 t5_246root t5_246jobs t5_246frontier t5_246all
theorem t5_247choices : plan4525.choices=[0,9,9,6,6].map (options 5 4) := by rfl


theorem t5_247part0 : t5_247jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_247frontier : t5_247root.frontier 0=t5_247jobs := by rfl
theorem t5_247all : t5_247jobs.all (Job.check tree)=true := by
  simp only [t5_247jobs,List.all_append,List.all_nil,t5_247part0,Bool.and_self]
theorem t5_247checked : Checked tree [0,9,9,6,6] := by
  refine ⟨plan4525,valid4525,t5_247choices,?_⟩
  exact check_of_frontier tree 0 t5_247root t5_247jobs t5_247frontier t5_247all
theorem t5_248choices : plan4526.choices=[0,9,9,6,7].map (options 5 4) := by rfl


theorem t5_248part0 : t5_248jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_248frontier : t5_248root.frontier 0=t5_248jobs := by rfl
theorem t5_248all : t5_248jobs.all (Job.check tree)=true := by
  simp only [t5_248jobs,List.all_append,List.all_nil,t5_248part0,Bool.and_self]
theorem t5_248checked : Checked tree [0,9,9,6,7] := by
  refine ⟨plan4526,valid4526,t5_248choices,?_⟩
  exact check_of_frontier tree 0 t5_248root t5_248jobs t5_248frontier t5_248all
theorem t5_249choices : plan4527.choices=[0,9,9,6,10].map (options 5 4) := by rfl


theorem t5_249part0 : t5_249jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_249frontier : t5_249root.frontier 0=t5_249jobs := by rfl
theorem t5_249all : t5_249jobs.all (Job.check tree)=true := by
  simp only [t5_249jobs,List.all_append,List.all_nil,t5_249part0,Bool.and_self]
theorem t5_249checked : Checked tree [0,9,9,6,10] := by
  refine ⟨plan4527,valid4527,t5_249choices,?_⟩
  exact check_of_frontier tree 0 t5_249root t5_249jobs t5_249frontier t5_249all
theorem t5_250choices : plan4528.choices=[0,9,9,7,7].map (options 5 4) := by rfl


theorem t5_250part0 : t5_250jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_250frontier : t5_250root.frontier 0=t5_250jobs := by rfl
theorem t5_250all : t5_250jobs.all (Job.check tree)=true := by
  simp only [t5_250jobs,List.all_append,List.all_nil,t5_250part0,Bool.and_self]
theorem t5_250checked : Checked tree [0,9,9,7,7] := by
  refine ⟨plan4528,valid4528,t5_250choices,?_⟩
  exact check_of_frontier tree 0 t5_250root t5_250jobs t5_250frontier t5_250all
theorem t5_251choices : plan4529.choices=[0,9,9,9,7].map (options 5 4) := by rfl


theorem t5_251part0 : t5_251jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_251frontier : t5_251root.frontier 0=t5_251jobs := by rfl
theorem t5_251all : t5_251jobs.all (Job.check tree)=true := by
  simp only [t5_251jobs,List.all_append,List.all_nil,t5_251part0,Bool.and_self]
theorem t5_251checked : Checked tree [0,9,9,9,7] := by
  refine ⟨plan4529,valid4529,t5_251choices,?_⟩
  exact check_of_frontier tree 0 t5_251root t5_251jobs t5_251frontier t5_251all
theorem t5_252choices : plan4530.choices=[0,9,9,10,7].map (options 5 4) := by rfl


theorem t5_252part0 : t5_252jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_252frontier : t5_252root.frontier 0=t5_252jobs := by rfl
theorem t5_252all : t5_252jobs.all (Job.check tree)=true := by
  simp only [t5_252jobs,List.all_append,List.all_nil,t5_252part0,Bool.and_self]
theorem t5_252checked : Checked tree [0,9,9,10,7] := by
  refine ⟨plan4530,valid4530,t5_252choices,?_⟩
  exact check_of_frontier tree 0 t5_252root t5_252jobs t5_252frontier t5_252all
theorem t5_253choices : plan4531.choices=[0,9,9,10,10].map (options 5 4) := by rfl


theorem t5_253part0 : t5_253jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_253frontier : t5_253root.frontier 0=t5_253jobs := by rfl
theorem t5_253all : t5_253jobs.all (Job.check tree)=true := by
  simp only [t5_253jobs,List.all_append,List.all_nil,t5_253part0,Bool.and_self]
theorem t5_253checked : Checked tree [0,9,9,10,10] := by
  refine ⟨plan4531,valid4531,t5_253choices,?_⟩
  exact check_of_frontier tree 0 t5_253root t5_253jobs t5_253frontier t5_253all
theorem t5_254choices : plan4532.choices=[0,9,10,7,7].map (options 5 4) := by rfl


theorem t5_254part0 : t5_254jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_254frontier : t5_254root.frontier 0=t5_254jobs := by rfl
theorem t5_254all : t5_254jobs.all (Job.check tree)=true := by
  simp only [t5_254jobs,List.all_append,List.all_nil,t5_254part0,Bool.and_self]
theorem t5_254checked : Checked tree [0,9,10,7,7] := by
  refine ⟨plan4532,valid4532,t5_254choices,?_⟩
  exact check_of_frontier tree 0 t5_254root t5_254jobs t5_254frontier t5_254all
theorem t5_255choices : plan4533.choices=[0,9,10,10,7].map (options 5 4) := by rfl


theorem t5_255part0 : t5_255jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_255frontier : t5_255root.frontier 0=t5_255jobs := by rfl
theorem t5_255all : t5_255jobs.all (Job.check tree)=true := by
  simp only [t5_255jobs,List.all_append,List.all_nil,t5_255part0,Bool.and_self]
theorem t5_255checked : Checked tree [0,9,10,10,7] := by
  refine ⟨plan4533,valid4533,t5_255choices,?_⟩
  exact check_of_frontier tree 0 t5_255root t5_255jobs t5_255frontier t5_255all
theorem t5_256choices : plan4534.choices=[0,9,10,10,10].map (options 5 4) := by rfl


theorem t5_256part0 : t5_256jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_256frontier : t5_256root.frontier 0=t5_256jobs := by rfl
theorem t5_256all : t5_256jobs.all (Job.check tree)=true := by
  simp only [t5_256jobs,List.all_append,List.all_nil,t5_256part0,Bool.and_self]
theorem t5_256checked : Checked tree [0,9,10,10,10] := by
  refine ⟨plan4534,valid4534,t5_256choices,?_⟩
  exact check_of_frontier tree 0 t5_256root t5_256jobs t5_256frontier t5_256all
theorem t5_257choices : plan4535.choices=[0,10,7,7,7].map (options 5 4) := by rfl


theorem t5_257part0 : t5_257jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_257frontier : t5_257root.frontier 0=t5_257jobs := by rfl
theorem t5_257all : t5_257jobs.all (Job.check tree)=true := by
  simp only [t5_257jobs,List.all_append,List.all_nil,t5_257part0,Bool.and_self]
theorem t5_257checked : Checked tree [0,10,7,7,7] := by
  refine ⟨plan4535,valid4535,t5_257choices,?_⟩
  exact check_of_frontier tree 0 t5_257root t5_257jobs t5_257frontier t5_257all
theorem t5_258choices : plan4536.choices=[0,10,10,7,7].map (options 5 4) := by rfl


theorem t5_258part0 : t5_258jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_258frontier : t5_258root.frontier 0=t5_258jobs := by rfl
theorem t5_258all : t5_258jobs.all (Job.check tree)=true := by
  simp only [t5_258jobs,List.all_append,List.all_nil,t5_258part0,Bool.and_self]
theorem t5_258checked : Checked tree [0,10,10,7,7] := by
  refine ⟨plan4536,valid4536,t5_258choices,?_⟩
  exact check_of_frontier tree 0 t5_258root t5_258jobs t5_258frontier t5_258all
theorem t5_259choices : plan4537.choices=[0,10,10,10,7].map (options 5 4) := by rfl


theorem t5_259part0 : t5_259jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_259frontier : t5_259root.frontier 0=t5_259jobs := by rfl
theorem t5_259all : t5_259jobs.all (Job.check tree)=true := by
  simp only [t5_259jobs,List.all_append,List.all_nil,t5_259part0,Bool.and_self]
theorem t5_259checked : Checked tree [0,10,10,10,7] := by
  refine ⟨plan4537,valid4537,t5_259choices,?_⟩
  exact check_of_frontier tree 0 t5_259root t5_259jobs t5_259frontier t5_259all
theorem t5_260choices : plan4538.choices=[0,10,10,10,10].map (options 5 4) := by rfl


theorem t5_260part0 : t5_260jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_260frontier : t5_260root.frontier 0=t5_260jobs := by rfl
theorem t5_260all : t5_260jobs.all (Job.check tree)=true := by
  simp only [t5_260jobs,List.all_append,List.all_nil,t5_260part0,Bool.and_self]
theorem t5_260checked : Checked tree [0,10,10,10,10] := by
  refine ⟨plan4538,valid4538,t5_260choices,?_⟩
  exact check_of_frontier tree 0 t5_260root t5_260jobs t5_260frontier t5_260all
theorem t5_261choices : plan3694.choices=[1,1,1,3,7].map (options 5 1) := by rfl


theorem t5_261part0 : t5_261jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_261frontier : t5_261root.frontier 0=t5_261jobs := by rfl
theorem t5_261all : t5_261jobs.all (Job.check tree)=true := by
  simp only [t5_261jobs,List.all_append,List.all_nil,t5_261part0,Bool.and_self]
theorem t5_261checked : Checked tree [1,1,1,3,7] := by
  refine ⟨plan3694,valid3694,t5_261choices,?_⟩
  exact check_of_frontier tree 0 t5_261root t5_261jobs t5_261frontier t5_261all
theorem t5_262choices : plan3813.choices=[1,1,1,6,7].map (options 5 2) := by rfl


theorem t5_262part0 : t5_262jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_262frontier : t5_262root.frontier 0=t5_262jobs := by rfl
theorem t5_262all : t5_262jobs.all (Job.check tree)=true := by
  simp only [t5_262jobs,List.all_append,List.all_nil,t5_262part0,Bool.and_self]
theorem t5_262checked : Checked tree [1,1,1,6,7] := by
  refine ⟨plan3813,valid3813,t5_262choices,?_⟩
  exact check_of_frontier tree 0 t5_262root t5_262jobs t5_262frontier t5_262all
theorem t5_263choices : plan3814.choices=[1,1,1,7,7].map (options 5 2) := by rfl


theorem t5_263part0 : t5_263jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_263frontier : t5_263root.frontier 0=t5_263jobs := by rfl
theorem t5_263all : t5_263jobs.all (Job.check tree)=true := by
  simp only [t5_263jobs,List.all_append,List.all_nil,t5_263part0,Bool.and_self]
theorem t5_263checked : Checked tree [1,1,1,7,7] := by
  refine ⟨plan3814,valid3814,t5_263choices,?_⟩
  exact check_of_frontier tree 0 t5_263root t5_263jobs t5_263frontier t5_263all
theorem t5_264choices : plan3815.choices=[1,1,1,10,7].map (options 5 2) := by rfl


theorem t5_264part0 : t5_264jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_264frontier : t5_264root.frontier 0=t5_264jobs := by rfl
theorem t5_264all : t5_264jobs.all (Job.check tree)=true := by
  simp only [t5_264jobs,List.all_append,List.all_nil,t5_264part0,Bool.and_self]
theorem t5_264checked : Checked tree [1,1,1,10,7] := by
  refine ⟨plan3815,valid3815,t5_264choices,?_⟩
  exact check_of_frontier tree 0 t5_264root t5_264jobs t5_264frontier t5_264all
theorem t5_265choices : plan3695.choices=[1,1,2,2,7].map (options 5 1) := by rfl


theorem t5_265part0 : t5_265jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_265frontier : t5_265root.frontier 0=t5_265jobs := by rfl
theorem t5_265all : t5_265jobs.all (Job.check tree)=true := by
  simp only [t5_265jobs,List.all_append,List.all_nil,t5_265part0,Bool.and_self]
theorem t5_265checked : Checked tree [1,1,2,2,7] := by
  refine ⟨plan3695,valid3695,t5_265choices,?_⟩
  exact check_of_frontier tree 0 t5_265root t5_265jobs t5_265frontier t5_265all
theorem t5_266choices : plan3662.choices=[1,1,2,3,3].map (options 5 0) := by rfl


theorem t5_266part0 : t5_266jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_266frontier : t5_266root.frontier 0=t5_266jobs := by rfl
theorem t5_266all : t5_266jobs.all (Job.check tree)=true := by
  simp only [t5_266jobs,List.all_append,List.all_nil,t5_266part0,Bool.and_self]
theorem t5_266checked : Checked tree [1,1,2,3,3] := by
  refine ⟨plan3662,valid3662,t5_266choices,?_⟩
  exact check_of_frontier tree 0 t5_266root t5_266jobs t5_266frontier t5_266all
theorem t5_267choices : plan3696.choices=[1,1,2,3,6].map (options 5 1) := by rfl


theorem t5_267part0 : t5_267jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_267frontier : t5_267root.frontier 0=t5_267jobs := by rfl
theorem t5_267all : t5_267jobs.all (Job.check tree)=true := by
  simp only [t5_267jobs,List.all_append,List.all_nil,t5_267part0,Bool.and_self]
theorem t5_267checked : Checked tree [1,1,2,3,6] := by
  refine ⟨plan3696,valid3696,t5_267choices,?_⟩
  exact check_of_frontier tree 0 t5_267root t5_267jobs t5_267frontier t5_267all
theorem t5_268choices : plan3697.choices=[1,1,2,3,7].map (options 5 1) := by rfl


theorem t5_268part0 : t5_268jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_268frontier : t5_268root.frontier 0=t5_268jobs := by rfl
theorem t5_268all : t5_268jobs.all (Job.check tree)=true := by
  simp only [t5_268jobs,List.all_append,List.all_nil,t5_268part0,Bool.and_self]
theorem t5_268checked : Checked tree [1,1,2,3,7] := by
  refine ⟨plan3697,valid3697,t5_268choices,?_⟩
  exact check_of_frontier tree 0 t5_268root t5_268jobs t5_268frontier t5_268all
theorem t5_269choices : plan3698.choices=[1,1,2,3,10].map (options 5 1) := by rfl


theorem t5_269part0 : t5_269jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_269frontier : t5_269root.frontier 0=t5_269jobs := by rfl
theorem t5_269all : t5_269jobs.all (Job.check tree)=true := by
  simp only [t5_269jobs,List.all_append,List.all_nil,t5_269part0,Bool.and_self]
theorem t5_269checked : Checked tree [1,1,2,3,10] := by
  refine ⟨plan3698,valid3698,t5_269choices,?_⟩
  exact check_of_frontier tree 0 t5_269root t5_269jobs t5_269frontier t5_269all
theorem t5_270choices : plan3816.choices=[1,1,2,5,7].map (options 5 2) := by rfl


theorem t5_270part0 : t5_270jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_270frontier : t5_270root.frontier 0=t5_270jobs := by rfl
theorem t5_270all : t5_270jobs.all (Job.check tree)=true := by
  simp only [t5_270jobs,List.all_append,List.all_nil,t5_270part0,Bool.and_self]
theorem t5_270checked : Checked tree [1,1,2,5,7] := by
  refine ⟨plan3816,valid3816,t5_270choices,?_⟩
  exact check_of_frontier tree 0 t5_270root t5_270jobs t5_270frontier t5_270all
theorem t5_271choices : plan3817.choices=[1,1,2,6,6].map (options 5 2) := by rfl


theorem t5_271part0 : t5_271jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_271frontier : t5_271root.frontier 0=t5_271jobs := by rfl
theorem t5_271all : t5_271jobs.all (Job.check tree)=true := by
  simp only [t5_271jobs,List.all_append,List.all_nil,t5_271part0,Bool.and_self]
theorem t5_271checked : Checked tree [1,1,2,6,6] := by
  refine ⟨plan3817,valid3817,t5_271choices,?_⟩
  exact check_of_frontier tree 0 t5_271root t5_271jobs t5_271frontier t5_271all
theorem t5_272choices : plan3818.choices=[1,1,2,6,7].map (options 5 2) := by rfl


theorem t5_272part0 : t5_272jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_272frontier : t5_272root.frontier 0=t5_272jobs := by rfl
theorem t5_272all : t5_272jobs.all (Job.check tree)=true := by
  simp only [t5_272jobs,List.all_append,List.all_nil,t5_272part0,Bool.and_self]
theorem t5_272checked : Checked tree [1,1,2,6,7] := by
  refine ⟨plan3818,valid3818,t5_272choices,?_⟩
  exact check_of_frontier tree 0 t5_272root t5_272jobs t5_272frontier t5_272all
theorem t5_273choices : plan3819.choices=[1,1,2,6,10].map (options 5 2) := by rfl


theorem t5_273part0 : t5_273jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_273frontier : t5_273root.frontier 0=t5_273jobs := by rfl
theorem t5_273all : t5_273jobs.all (Job.check tree)=true := by
  simp only [t5_273jobs,List.all_append,List.all_nil,t5_273part0,Bool.and_self]
theorem t5_273checked : Checked tree [1,1,2,6,10] := by
  refine ⟨plan3819,valid3819,t5_273choices,?_⟩
  exact check_of_frontier tree 0 t5_273root t5_273jobs t5_273frontier t5_273all
theorem t5_274choices : plan3820.choices=[1,1,2,7,7].map (options 5 2) := by rfl


theorem t5_274part0 : t5_274jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_274frontier : t5_274root.frontier 0=t5_274jobs := by rfl
theorem t5_274all : t5_274jobs.all (Job.check tree)=true := by
  simp only [t5_274jobs,List.all_append,List.all_nil,t5_274part0,Bool.and_self]
theorem t5_274checked : Checked tree [1,1,2,7,7] := by
  refine ⟨plan3820,valid3820,t5_274choices,?_⟩
  exact check_of_frontier tree 0 t5_274root t5_274jobs t5_274frontier t5_274all
theorem t5_275choices : plan3821.choices=[1,1,2,9,7].map (options 5 2) := by rfl


theorem t5_275part0 : t5_275jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_275frontier : t5_275root.frontier 0=t5_275jobs := by rfl
theorem t5_275all : t5_275jobs.all (Job.check tree)=true := by
  simp only [t5_275jobs,List.all_append,List.all_nil,t5_275part0,Bool.and_self]
theorem t5_275checked : Checked tree [1,1,2,9,7] := by
  refine ⟨plan3821,valid3821,t5_275choices,?_⟩
  exact check_of_frontier tree 0 t5_275root t5_275jobs t5_275frontier t5_275all
theorem t5_276choices : plan3822.choices=[1,1,2,10,7].map (options 5 2) := by rfl


theorem t5_276part0 : t5_276jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_276frontier : t5_276root.frontier 0=t5_276jobs := by rfl
theorem t5_276all : t5_276jobs.all (Job.check tree)=true := by
  simp only [t5_276jobs,List.all_append,List.all_nil,t5_276part0,Bool.and_self]
theorem t5_276checked : Checked tree [1,1,2,10,7] := by
  refine ⟨plan3822,valid3822,t5_276choices,?_⟩
  exact check_of_frontier tree 0 t5_276root t5_276jobs t5_276frontier t5_276all
theorem t5_277choices : plan3823.choices=[1,1,2,10,10].map (options 5 2) := by rfl


theorem t5_277part0 : t5_277jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_277frontier : t5_277root.frontier 0=t5_277jobs := by rfl
theorem t5_277all : t5_277jobs.all (Job.check tree)=true := by
  simp only [t5_277jobs,List.all_append,List.all_nil,t5_277part0,Bool.and_self]
theorem t5_277checked : Checked tree [1,1,2,10,10] := by
  refine ⟨plan3823,valid3823,t5_277choices,?_⟩
  exact check_of_frontier tree 0 t5_277root t5_277jobs t5_277frontier t5_277all
theorem t5_278choices : plan3663.choices=[1,1,3,3,3].map (options 5 0) := by rfl


theorem t5_278part0 : t5_278jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_278frontier : t5_278root.frontier 0=t5_278jobs := by rfl
theorem t5_278all : t5_278jobs.all (Job.check tree)=true := by
  simp only [t5_278jobs,List.all_append,List.all_nil,t5_278part0,Bool.and_self]
theorem t5_278checked : Checked tree [1,1,3,3,3] := by
  refine ⟨plan3663,valid3663,t5_278choices,?_⟩
  exact check_of_frontier tree 0 t5_278root t5_278jobs t5_278frontier t5_278all
theorem t5_279choices : plan3699.choices=[1,1,3,3,6].map (options 5 1) := by rfl


theorem t5_279part0 : t5_279jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_279frontier : t5_279root.frontier 0=t5_279jobs := by rfl
theorem t5_279all : t5_279jobs.all (Job.check tree)=true := by
  simp only [t5_279jobs,List.all_append,List.all_nil,t5_279part0,Bool.and_self]
theorem t5_279checked : Checked tree [1,1,3,3,6] := by
  refine ⟨plan3699,valid3699,t5_279choices,?_⟩
  exact check_of_frontier tree 0 t5_279root t5_279jobs t5_279frontier t5_279all
theorem t5_280choices : plan3700.choices=[1,1,3,3,7].map (options 5 1) := by rfl


theorem t5_280part0 : t5_280jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_280frontier : t5_280root.frontier 0=t5_280jobs := by rfl
theorem t5_280all : t5_280jobs.all (Job.check tree)=true := by
  simp only [t5_280jobs,List.all_append,List.all_nil,t5_280part0,Bool.and_self]
theorem t5_280checked : Checked tree [1,1,3,3,7] := by
  refine ⟨plan3700,valid3700,t5_280choices,?_⟩
  exact check_of_frontier tree 0 t5_280root t5_280jobs t5_280frontier t5_280all
theorem t5_281choices : plan3701.choices=[1,1,3,3,10].map (options 5 1) := by rfl


theorem t5_281part0 : t5_281jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_281frontier : t5_281root.frontier 0=t5_281jobs := by rfl
theorem t5_281all : t5_281jobs.all (Job.check tree)=true := by
  simp only [t5_281jobs,List.all_append,List.all_nil,t5_281part0,Bool.and_self]
theorem t5_281checked : Checked tree [1,1,3,3,10] := by
  refine ⟨plan3701,valid3701,t5_281choices,?_⟩
  exact check_of_frontier tree 0 t5_281root t5_281jobs t5_281frontier t5_281all
theorem t5_282choices : plan3824.choices=[1,1,3,6,6].map (options 5 2) := by rfl


theorem t5_282part0 : t5_282jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_282frontier : t5_282root.frontier 0=t5_282jobs := by rfl
theorem t5_282all : t5_282jobs.all (Job.check tree)=true := by
  simp only [t5_282jobs,List.all_append,List.all_nil,t5_282part0,Bool.and_self]
theorem t5_282checked : Checked tree [1,1,3,6,6] := by
  refine ⟨plan3824,valid3824,t5_282choices,?_⟩
  exact check_of_frontier tree 0 t5_282root t5_282jobs t5_282frontier t5_282all
theorem t5_283choices : plan3825.choices=[1,1,3,6,7].map (options 5 2) := by rfl


theorem t5_283part0 : t5_283jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_283frontier : t5_283root.frontier 0=t5_283jobs := by rfl
theorem t5_283all : t5_283jobs.all (Job.check tree)=true := by
  simp only [t5_283jobs,List.all_append,List.all_nil,t5_283part0,Bool.and_self]
theorem t5_283checked : Checked tree [1,1,3,6,7] := by
  refine ⟨plan3825,valid3825,t5_283choices,?_⟩
  exact check_of_frontier tree 0 t5_283root t5_283jobs t5_283frontier t5_283all
theorem t5_284choices : plan3826.choices=[1,1,3,6,10].map (options 5 2) := by rfl


theorem t5_284part0 : t5_284jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_284frontier : t5_284root.frontier 0=t5_284jobs := by rfl
theorem t5_284all : t5_284jobs.all (Job.check tree)=true := by
  simp only [t5_284jobs,List.all_append,List.all_nil,t5_284part0,Bool.and_self]
theorem t5_284checked : Checked tree [1,1,3,6,10] := by
  refine ⟨plan3826,valid3826,t5_284choices,?_⟩
  exact check_of_frontier tree 0 t5_284root t5_284jobs t5_284frontier t5_284all
theorem t5_285choices : plan3827.choices=[1,1,3,7,7].map (options 5 2) := by rfl


theorem t5_285part0 : t5_285jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_285frontier : t5_285root.frontier 0=t5_285jobs := by rfl
theorem t5_285all : t5_285jobs.all (Job.check tree)=true := by
  simp only [t5_285jobs,List.all_append,List.all_nil,t5_285part0,Bool.and_self]
theorem t5_285checked : Checked tree [1,1,3,7,7] := by
  refine ⟨plan3827,valid3827,t5_285choices,?_⟩
  exact check_of_frontier tree 0 t5_285root t5_285jobs t5_285frontier t5_285all
theorem t5_286choices : plan3828.choices=[1,1,3,10,7].map (options 5 2) := by rfl


theorem t5_286part0 : t5_286jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_286frontier : t5_286root.frontier 0=t5_286jobs := by rfl
theorem t5_286all : t5_286jobs.all (Job.check tree)=true := by
  simp only [t5_286jobs,List.all_append,List.all_nil,t5_286part0,Bool.and_self]
theorem t5_286checked : Checked tree [1,1,3,10,7] := by
  refine ⟨plan3828,valid3828,t5_286choices,?_⟩
  exact check_of_frontier tree 0 t5_286root t5_286jobs t5_286frontier t5_286all
theorem t5_287choices : plan3829.choices=[1,1,3,10,10].map (options 5 2) := by rfl


theorem t5_287part0 : t5_287jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_287frontier : t5_287root.frontier 0=t5_287jobs := by rfl
theorem t5_287all : t5_287jobs.all (Job.check tree)=true := by
  simp only [t5_287jobs,List.all_append,List.all_nil,t5_287part0,Bool.and_self]
theorem t5_287checked : Checked tree [1,1,3,10,10] := by
  refine ⟨plan3829,valid3829,t5_287choices,?_⟩
  exact check_of_frontier tree 0 t5_287root t5_287jobs t5_287frontier t5_287all
theorem t5_288choices : plan3830.choices=[1,1,4,3,7].map (options 5 2) := by rfl


theorem t5_288part0 : t5_288jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_288frontier : t5_288root.frontier 0=t5_288jobs := by rfl
theorem t5_288all : t5_288jobs.all (Job.check tree)=true := by
  simp only [t5_288jobs,List.all_append,List.all_nil,t5_288part0,Bool.and_self]
theorem t5_288checked : Checked tree [1,1,4,3,7] := by
  refine ⟨plan3830,valid3830,t5_288choices,?_⟩
  exact check_of_frontier tree 0 t5_288root t5_288jobs t5_288frontier t5_288all
theorem t5_289choices : plan4094.choices=[1,1,4,6,7].map (options 5 3) := by rfl


theorem t5_289part0 : t5_289jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_289frontier : t5_289root.frontier 0=t5_289jobs := by rfl
theorem t5_289all : t5_289jobs.all (Job.check tree)=true := by
  simp only [t5_289jobs,List.all_append,List.all_nil,t5_289part0,Bool.and_self]
theorem t5_289checked : Checked tree [1,1,4,6,7] := by
  refine ⟨plan4094,valid4094,t5_289choices,?_⟩
  exact check_of_frontier tree 0 t5_289root t5_289jobs t5_289frontier t5_289all
theorem t5_290choices : plan4095.choices=[1,1,4,7,7].map (options 5 3) := by rfl


theorem t5_290part0 : t5_290jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_290frontier : t5_290root.frontier 0=t5_290jobs := by rfl
theorem t5_290all : t5_290jobs.all (Job.check tree)=true := by
  simp only [t5_290jobs,List.all_append,List.all_nil,t5_290part0,Bool.and_self]
theorem t5_290checked : Checked tree [1,1,4,7,7] := by
  refine ⟨plan4095,valid4095,t5_290choices,?_⟩
  exact check_of_frontier tree 0 t5_290root t5_290jobs t5_290frontier t5_290all
theorem t5_291choices : plan4096.choices=[1,1,4,10,7].map (options 5 3) := by rfl


theorem t5_291part0 : t5_291jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_291frontier : t5_291root.frontier 0=t5_291jobs := by rfl
theorem t5_291all : t5_291jobs.all (Job.check tree)=true := by
  simp only [t5_291jobs,List.all_append,List.all_nil,t5_291part0,Bool.and_self]
theorem t5_291checked : Checked tree [1,1,4,10,7] := by
  refine ⟨plan4096,valid4096,t5_291choices,?_⟩
  exact check_of_frontier tree 0 t5_291root t5_291jobs t5_291frontier t5_291all
theorem t5_292choices : plan3702.choices=[1,1,5,3,3].map (options 5 1) := by rfl


theorem t5_292part0 : t5_292jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_292frontier : t5_292root.frontier 0=t5_292jobs := by rfl
theorem t5_292all : t5_292jobs.all (Job.check tree)=true := by
  simp only [t5_292jobs,List.all_append,List.all_nil,t5_292part0,Bool.and_self]
theorem t5_292checked : Checked tree [1,1,5,3,3] := by
  refine ⟨plan3702,valid3702,t5_292choices,?_⟩
  exact check_of_frontier tree 0 t5_292root t5_292jobs t5_292frontier t5_292all
theorem t5_293choices : plan3831.choices=[1,1,5,3,6].map (options 5 2) := by rfl


theorem t5_293part0 : t5_293jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_293frontier : t5_293root.frontier 0=t5_293jobs := by rfl
theorem t5_293all : t5_293jobs.all (Job.check tree)=true := by
  simp only [t5_293jobs,List.all_append,List.all_nil,t5_293part0,Bool.and_self]
theorem t5_293checked : Checked tree [1,1,5,3,6] := by
  refine ⟨plan3831,valid3831,t5_293choices,?_⟩
  exact check_of_frontier tree 0 t5_293root t5_293jobs t5_293frontier t5_293all
theorem t5_294choices : plan3832.choices=[1,1,5,3,7].map (options 5 2) := by rfl


theorem t5_294part0 : t5_294jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_294frontier : t5_294root.frontier 0=t5_294jobs := by rfl
theorem t5_294all : t5_294jobs.all (Job.check tree)=true := by
  simp only [t5_294jobs,List.all_append,List.all_nil,t5_294part0,Bool.and_self]
theorem t5_294checked : Checked tree [1,1,5,3,7] := by
  refine ⟨plan3832,valid3832,t5_294choices,?_⟩
  exact check_of_frontier tree 0 t5_294root t5_294jobs t5_294frontier t5_294all
theorem t5_295choices : plan3833.choices=[1,1,5,3,10].map (options 5 2) := by rfl


theorem t5_295part0 : t5_295jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_295frontier : t5_295root.frontier 0=t5_295jobs := by rfl
theorem t5_295all : t5_295jobs.all (Job.check tree)=true := by
  simp only [t5_295jobs,List.all_append,List.all_nil,t5_295part0,Bool.and_self]
theorem t5_295checked : Checked tree [1,1,5,3,10] := by
  refine ⟨plan3833,valid3833,t5_295choices,?_⟩
  exact check_of_frontier tree 0 t5_295root t5_295jobs t5_295frontier t5_295all
theorem t5_296choices : plan4097.choices=[1,1,5,5,7].map (options 5 3) := by rfl


theorem t5_296part0 : t5_296jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_296frontier : t5_296root.frontier 0=t5_296jobs := by rfl
theorem t5_296all : t5_296jobs.all (Job.check tree)=true := by
  simp only [t5_296jobs,List.all_append,List.all_nil,t5_296part0,Bool.and_self]
theorem t5_296checked : Checked tree [1,1,5,5,7] := by
  refine ⟨plan4097,valid4097,t5_296choices,?_⟩
  exact check_of_frontier tree 0 t5_296root t5_296jobs t5_296frontier t5_296all
theorem t5_297choices : plan4098.choices=[1,1,5,6,6].map (options 5 3) := by rfl


theorem t5_297part0 : t5_297jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_297frontier : t5_297root.frontier 0=t5_297jobs := by rfl
theorem t5_297all : t5_297jobs.all (Job.check tree)=true := by
  simp only [t5_297jobs,List.all_append,List.all_nil,t5_297part0,Bool.and_self]
theorem t5_297checked : Checked tree [1,1,5,6,6] := by
  refine ⟨plan4098,valid4098,t5_297choices,?_⟩
  exact check_of_frontier tree 0 t5_297root t5_297jobs t5_297frontier t5_297all
theorem t5_298choices : plan4099.choices=[1,1,5,6,7].map (options 5 3) := by rfl


theorem t5_298part0 : t5_298jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_298frontier : t5_298root.frontier 0=t5_298jobs := by rfl
theorem t5_298all : t5_298jobs.all (Job.check tree)=true := by
  simp only [t5_298jobs,List.all_append,List.all_nil,t5_298part0,Bool.and_self]
theorem t5_298checked : Checked tree [1,1,5,6,7] := by
  refine ⟨plan4099,valid4099,t5_298choices,?_⟩
  exact check_of_frontier tree 0 t5_298root t5_298jobs t5_298frontier t5_298all
theorem t5_299choices : plan4100.choices=[1,1,5,6,10].map (options 5 3) := by rfl


theorem t5_299part0 : t5_299jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_299frontier : t5_299root.frontier 0=t5_299jobs := by rfl
theorem t5_299all : t5_299jobs.all (Job.check tree)=true := by
  simp only [t5_299jobs,List.all_append,List.all_nil,t5_299part0,Bool.and_self]
theorem t5_299checked : Checked tree [1,1,5,6,10] := by
  refine ⟨plan4100,valid4100,t5_299choices,?_⟩
  exact check_of_frontier tree 0 t5_299root t5_299jobs t5_299frontier t5_299all
theorem t5_300choices : plan4101.choices=[1,1,5,7,7].map (options 5 3) := by rfl


theorem t5_300part0 : t5_300jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_300frontier : t5_300root.frontier 0=t5_300jobs := by rfl
theorem t5_300all : t5_300jobs.all (Job.check tree)=true := by
  simp only [t5_300jobs,List.all_append,List.all_nil,t5_300part0,Bool.and_self]
theorem t5_300checked : Checked tree [1,1,5,7,7] := by
  refine ⟨plan4101,valid4101,t5_300choices,?_⟩
  exact check_of_frontier tree 0 t5_300root t5_300jobs t5_300frontier t5_300all
theorem t5_301choices : plan4102.choices=[1,1,5,9,7].map (options 5 3) := by rfl


theorem t5_301part0 : t5_301jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_301frontier : t5_301root.frontier 0=t5_301jobs := by rfl
theorem t5_301all : t5_301jobs.all (Job.check tree)=true := by
  simp only [t5_301jobs,List.all_append,List.all_nil,t5_301part0,Bool.and_self]
theorem t5_301checked : Checked tree [1,1,5,9,7] := by
  refine ⟨plan4102,valid4102,t5_301choices,?_⟩
  exact check_of_frontier tree 0 t5_301root t5_301jobs t5_301frontier t5_301all
theorem t5_302choices : plan4103.choices=[1,1,5,10,7].map (options 5 3) := by rfl


theorem t5_302part0 : t5_302jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_302frontier : t5_302root.frontier 0=t5_302jobs := by rfl
theorem t5_302all : t5_302jobs.all (Job.check tree)=true := by
  simp only [t5_302jobs,List.all_append,List.all_nil,t5_302part0,Bool.and_self]
theorem t5_302checked : Checked tree [1,1,5,10,7] := by
  refine ⟨plan4103,valid4103,t5_302choices,?_⟩
  exact check_of_frontier tree 0 t5_302root t5_302jobs t5_302frontier t5_302all
theorem t5_303choices : plan4104.choices=[1,1,5,10,10].map (options 5 3) := by rfl


theorem t5_303part0 : t5_303jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_303frontier : t5_303root.frontier 0=t5_303jobs := by rfl
theorem t5_303all : t5_303jobs.all (Job.check tree)=true := by
  simp only [t5_303jobs,List.all_append,List.all_nil,t5_303part0,Bool.and_self]
theorem t5_303checked : Checked tree [1,1,5,10,10] := by
  refine ⟨plan4104,valid4104,t5_303choices,?_⟩
  exact check_of_frontier tree 0 t5_303root t5_303jobs t5_303frontier t5_303all
theorem t5_304choices : plan4105.choices=[1,1,6,6,6].map (options 5 3) := by rfl


theorem t5_304part0 : t5_304jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_304frontier : t5_304root.frontier 0=t5_304jobs := by rfl
theorem t5_304all : t5_304jobs.all (Job.check tree)=true := by
  simp only [t5_304jobs,List.all_append,List.all_nil,t5_304part0,Bool.and_self]
theorem t5_304checked : Checked tree [1,1,6,6,6] := by
  refine ⟨plan4105,valid4105,t5_304choices,?_⟩
  exact check_of_frontier tree 0 t5_304root t5_304jobs t5_304frontier t5_304all
theorem t5_305choices : plan4106.choices=[1,1,6,6,7].map (options 5 3) := by rfl


theorem t5_305part0 : t5_305jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_305frontier : t5_305root.frontier 0=t5_305jobs := by rfl
theorem t5_305all : t5_305jobs.all (Job.check tree)=true := by
  simp only [t5_305jobs,List.all_append,List.all_nil,t5_305part0,Bool.and_self]
theorem t5_305checked : Checked tree [1,1,6,6,7] := by
  refine ⟨plan4106,valid4106,t5_305choices,?_⟩
  exact check_of_frontier tree 0 t5_305root t5_305jobs t5_305frontier t5_305all
theorem t5_306choices : plan4107.choices=[1,1,6,6,10].map (options 5 3) := by rfl


theorem t5_306part0 : t5_306jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_306frontier : t5_306root.frontier 0=t5_306jobs := by rfl
theorem t5_306all : t5_306jobs.all (Job.check tree)=true := by
  simp only [t5_306jobs,List.all_append,List.all_nil,t5_306part0,Bool.and_self]
theorem t5_306checked : Checked tree [1,1,6,6,10] := by
  refine ⟨plan4107,valid4107,t5_306choices,?_⟩
  exact check_of_frontier tree 0 t5_306root t5_306jobs t5_306frontier t5_306all
theorem t5_307choices : plan4108.choices=[1,1,6,7,7].map (options 5 3) := by rfl


theorem t5_307part0 : t5_307jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_307frontier : t5_307root.frontier 0=t5_307jobs := by rfl
theorem t5_307all : t5_307jobs.all (Job.check tree)=true := by
  simp only [t5_307jobs,List.all_append,List.all_nil,t5_307part0,Bool.and_self]
theorem t5_307checked : Checked tree [1,1,6,7,7] := by
  refine ⟨plan4108,valid4108,t5_307choices,?_⟩
  exact check_of_frontier tree 0 t5_307root t5_307jobs t5_307frontier t5_307all
theorem t5_308choices : plan4109.choices=[1,1,6,10,7].map (options 5 3) := by rfl


theorem t5_308part0 : t5_308jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_308frontier : t5_308root.frontier 0=t5_308jobs := by rfl
theorem t5_308all : t5_308jobs.all (Job.check tree)=true := by
  simp only [t5_308jobs,List.all_append,List.all_nil,t5_308part0,Bool.and_self]
theorem t5_308checked : Checked tree [1,1,6,10,7] := by
  refine ⟨plan4109,valid4109,t5_308choices,?_⟩
  exact check_of_frontier tree 0 t5_308root t5_308jobs t5_308frontier t5_308all
theorem t5_309choices : plan4110.choices=[1,1,6,10,10].map (options 5 3) := by rfl


theorem t5_309part0 : t5_309jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_309frontier : t5_309root.frontier 0=t5_309jobs := by rfl
theorem t5_309all : t5_309jobs.all (Job.check tree)=true := by
  simp only [t5_309jobs,List.all_append,List.all_nil,t5_309part0,Bool.and_self]
theorem t5_309checked : Checked tree [1,1,6,10,10] := by
  refine ⟨plan4110,valid4110,t5_309choices,?_⟩
  exact check_of_frontier tree 0 t5_309root t5_309jobs t5_309frontier t5_309all
theorem t5_310choices : plan4111.choices=[1,1,7,7,7].map (options 5 3) := by rfl


theorem t5_310part0 : t5_310jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_310frontier : t5_310root.frontier 0=t5_310jobs := by rfl
theorem t5_310all : t5_310jobs.all (Job.check tree)=true := by
  simp only [t5_310jobs,List.all_append,List.all_nil,t5_310part0,Bool.and_self]
theorem t5_310checked : Checked tree [1,1,7,7,7] := by
  refine ⟨plan4111,valid4111,t5_310choices,?_⟩
  exact check_of_frontier tree 0 t5_310root t5_310jobs t5_310frontier t5_310all
theorem t5_311choices : plan3834.choices=[1,1,8,3,7].map (options 5 2) := by rfl


theorem t5_311part0 : t5_311jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_311frontier : t5_311root.frontier 0=t5_311jobs := by rfl
theorem t5_311all : t5_311jobs.all (Job.check tree)=true := by
  simp only [t5_311jobs,List.all_append,List.all_nil,t5_311part0,Bool.and_self]
theorem t5_311checked : Checked tree [1,1,8,3,7] := by
  refine ⟨plan3834,valid3834,t5_311choices,?_⟩
  exact check_of_frontier tree 0 t5_311root t5_311jobs t5_311frontier t5_311all
theorem t5_312choices : plan4112.choices=[1,1,8,6,7].map (options 5 3) := by rfl


theorem t5_312part0 : t5_312jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_312frontier : t5_312root.frontier 0=t5_312jobs := by rfl
theorem t5_312all : t5_312jobs.all (Job.check tree)=true := by
  simp only [t5_312jobs,List.all_append,List.all_nil,t5_312part0,Bool.and_self]
theorem t5_312checked : Checked tree [1,1,8,6,7] := by
  refine ⟨plan4112,valid4112,t5_312choices,?_⟩
  exact check_of_frontier tree 0 t5_312root t5_312jobs t5_312frontier t5_312all
theorem t5_313choices : plan4113.choices=[1,1,8,7,7].map (options 5 3) := by rfl


theorem t5_313part0 : t5_313jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_313frontier : t5_313root.frontier 0=t5_313jobs := by rfl
theorem t5_313all : t5_313jobs.all (Job.check tree)=true := by
  simp only [t5_313jobs,List.all_append,List.all_nil,t5_313part0,Bool.and_self]
theorem t5_313checked : Checked tree [1,1,8,7,7] := by
  refine ⟨plan4113,valid4113,t5_313choices,?_⟩
  exact check_of_frontier tree 0 t5_313root t5_313jobs t5_313frontier t5_313all
theorem t5_314choices : plan4114.choices=[1,1,8,10,7].map (options 5 3) := by rfl


theorem t5_314part0 : t5_314jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_314frontier : t5_314root.frontier 0=t5_314jobs := by rfl
theorem t5_314all : t5_314jobs.all (Job.check tree)=true := by
  simp only [t5_314jobs,List.all_append,List.all_nil,t5_314part0,Bool.and_self]
theorem t5_314checked : Checked tree [1,1,8,10,7] := by
  refine ⟨plan4114,valid4114,t5_314choices,?_⟩
  exact check_of_frontier tree 0 t5_314root t5_314jobs t5_314frontier t5_314all
theorem t5_315choices : plan3703.choices=[1,1,9,3,3].map (options 5 1) := by rfl


theorem t5_315part0 : t5_315jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_315frontier : t5_315root.frontier 0=t5_315jobs := by rfl
theorem t5_315all : t5_315jobs.all (Job.check tree)=true := by
  simp only [t5_315jobs,List.all_append,List.all_nil,t5_315part0,Bool.and_self]
theorem t5_315checked : Checked tree [1,1,9,3,3] := by
  refine ⟨plan3703,valid3703,t5_315choices,?_⟩
  exact check_of_frontier tree 0 t5_315root t5_315jobs t5_315frontier t5_315all
theorem t5_316choices : plan3835.choices=[1,1,9,3,6].map (options 5 2) := by rfl


theorem t5_316part0 : t5_316jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_316frontier : t5_316root.frontier 0=t5_316jobs := by rfl
theorem t5_316all : t5_316jobs.all (Job.check tree)=true := by
  simp only [t5_316jobs,List.all_append,List.all_nil,t5_316part0,Bool.and_self]
theorem t5_316checked : Checked tree [1,1,9,3,6] := by
  refine ⟨plan3835,valid3835,t5_316choices,?_⟩
  exact check_of_frontier tree 0 t5_316root t5_316jobs t5_316frontier t5_316all
theorem t5_317choices : plan3836.choices=[1,1,9,3,7].map (options 5 2) := by rfl


theorem t5_317part0 : t5_317jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_317frontier : t5_317root.frontier 0=t5_317jobs := by rfl
theorem t5_317all : t5_317jobs.all (Job.check tree)=true := by
  simp only [t5_317jobs,List.all_append,List.all_nil,t5_317part0,Bool.and_self]
theorem t5_317checked : Checked tree [1,1,9,3,7] := by
  refine ⟨plan3836,valid3836,t5_317choices,?_⟩
  exact check_of_frontier tree 0 t5_317root t5_317jobs t5_317frontier t5_317all
theorem t5_318choices : plan3837.choices=[1,1,9,3,10].map (options 5 2) := by rfl


theorem t5_318part0 : t5_318jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_318frontier : t5_318root.frontier 0=t5_318jobs := by rfl
theorem t5_318all : t5_318jobs.all (Job.check tree)=true := by
  simp only [t5_318jobs,List.all_append,List.all_nil,t5_318part0,Bool.and_self]
theorem t5_318checked : Checked tree [1,1,9,3,10] := by
  refine ⟨plan3837,valid3837,t5_318choices,?_⟩
  exact check_of_frontier tree 0 t5_318root t5_318jobs t5_318frontier t5_318all
theorem t5_319choices : plan4115.choices=[1,1,9,6,6].map (options 5 3) := by rfl


theorem t5_319part0 : t5_319jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_319frontier : t5_319root.frontier 0=t5_319jobs := by rfl
theorem t5_319all : t5_319jobs.all (Job.check tree)=true := by
  simp only [t5_319jobs,List.all_append,List.all_nil,t5_319part0,Bool.and_self]
theorem t5_319checked : Checked tree [1,1,9,6,6] := by
  refine ⟨plan4115,valid4115,t5_319choices,?_⟩
  exact check_of_frontier tree 0 t5_319root t5_319jobs t5_319frontier t5_319all
theorem t5_320choices : plan4116.choices=[1,1,9,6,7].map (options 5 3) := by rfl


theorem t5_320part0 : t5_320jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_320frontier : t5_320root.frontier 0=t5_320jobs := by rfl
theorem t5_320all : t5_320jobs.all (Job.check tree)=true := by
  simp only [t5_320jobs,List.all_append,List.all_nil,t5_320part0,Bool.and_self]
theorem t5_320checked : Checked tree [1,1,9,6,7] := by
  refine ⟨plan4116,valid4116,t5_320choices,?_⟩
  exact check_of_frontier tree 0 t5_320root t5_320jobs t5_320frontier t5_320all
theorem t5_321choices : plan4117.choices=[1,1,9,6,10].map (options 5 3) := by rfl


theorem t5_321part0 : t5_321jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_321frontier : t5_321root.frontier 0=t5_321jobs := by rfl
theorem t5_321all : t5_321jobs.all (Job.check tree)=true := by
  simp only [t5_321jobs,List.all_append,List.all_nil,t5_321part0,Bool.and_self]
theorem t5_321checked : Checked tree [1,1,9,6,10] := by
  refine ⟨plan4117,valid4117,t5_321choices,?_⟩
  exact check_of_frontier tree 0 t5_321root t5_321jobs t5_321frontier t5_321all
theorem t5_322choices : plan4118.choices=[1,1,9,7,7].map (options 5 3) := by rfl


theorem t5_322part0 : t5_322jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_322frontier : t5_322root.frontier 0=t5_322jobs := by rfl
theorem t5_322all : t5_322jobs.all (Job.check tree)=true := by
  simp only [t5_322jobs,List.all_append,List.all_nil,t5_322part0,Bool.and_self]
theorem t5_322checked : Checked tree [1,1,9,7,7] := by
  refine ⟨plan4118,valid4118,t5_322choices,?_⟩
  exact check_of_frontier tree 0 t5_322root t5_322jobs t5_322frontier t5_322all
theorem t5_323choices : plan4119.choices=[1,1,9,9,7].map (options 5 3) := by rfl


theorem t5_323part0 : t5_323jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_323frontier : t5_323root.frontier 0=t5_323jobs := by rfl
theorem t5_323all : t5_323jobs.all (Job.check tree)=true := by
  simp only [t5_323jobs,List.all_append,List.all_nil,t5_323part0,Bool.and_self]
theorem t5_323checked : Checked tree [1,1,9,9,7] := by
  refine ⟨plan4119,valid4119,t5_323choices,?_⟩
  exact check_of_frontier tree 0 t5_323root t5_323jobs t5_323frontier t5_323all
theorem t5_324choices : plan4120.choices=[1,1,9,10,7].map (options 5 3) := by rfl


theorem t5_324part0 : t5_324jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_324frontier : t5_324root.frontier 0=t5_324jobs := by rfl
theorem t5_324all : t5_324jobs.all (Job.check tree)=true := by
  simp only [t5_324jobs,List.all_append,List.all_nil,t5_324part0,Bool.and_self]
theorem t5_324checked : Checked tree [1,1,9,10,7] := by
  refine ⟨plan4120,valid4120,t5_324choices,?_⟩
  exact check_of_frontier tree 0 t5_324root t5_324jobs t5_324frontier t5_324all
theorem t5_325choices : plan4121.choices=[1,1,9,10,10].map (options 5 3) := by rfl


theorem t5_325part0 : t5_325jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_325frontier : t5_325root.frontier 0=t5_325jobs := by rfl
theorem t5_325all : t5_325jobs.all (Job.check tree)=true := by
  simp only [t5_325jobs,List.all_append,List.all_nil,t5_325part0,Bool.and_self]
theorem t5_325checked : Checked tree [1,1,9,10,10] := by
  refine ⟨plan4121,valid4121,t5_325choices,?_⟩
  exact check_of_frontier tree 0 t5_325root t5_325jobs t5_325frontier t5_325all
theorem t5_326choices : plan4122.choices=[1,1,10,7,7].map (options 5 3) := by rfl


theorem t5_326part0 : t5_326jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_326frontier : t5_326root.frontier 0=t5_326jobs := by rfl
theorem t5_326all : t5_326jobs.all (Job.check tree)=true := by
  simp only [t5_326jobs,List.all_append,List.all_nil,t5_326part0,Bool.and_self]
theorem t5_326checked : Checked tree [1,1,10,7,7] := by
  refine ⟨plan4122,valid4122,t5_326choices,?_⟩
  exact check_of_frontier tree 0 t5_326root t5_326jobs t5_326frontier t5_326all
theorem t5_327choices : plan4123.choices=[1,1,10,10,7].map (options 5 3) := by rfl


theorem t5_327part0 : t5_327jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_327frontier : t5_327root.frontier 0=t5_327jobs := by rfl
theorem t5_327all : t5_327jobs.all (Job.check tree)=true := by
  simp only [t5_327jobs,List.all_append,List.all_nil,t5_327part0,Bool.and_self]
theorem t5_327checked : Checked tree [1,1,10,10,7] := by
  refine ⟨plan4123,valid4123,t5_327choices,?_⟩
  exact check_of_frontier tree 0 t5_327root t5_327jobs t5_327frontier t5_327all
theorem t5_328choices : plan4124.choices=[1,1,10,10,10].map (options 5 3) := by rfl


theorem t5_328part0 : t5_328jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_328frontier : t5_328root.frontier 0=t5_328jobs := by rfl
theorem t5_328all : t5_328jobs.all (Job.check tree)=true := by
  simp only [t5_328jobs,List.all_append,List.all_nil,t5_328part0,Bool.and_self]
theorem t5_328checked : Checked tree [1,1,10,10,10] := by
  refine ⟨plan4124,valid4124,t5_328choices,?_⟩
  exact check_of_frontier tree 0 t5_328root t5_328jobs t5_328frontier t5_328all
theorem t5_329choices : plan3664.choices=[1,2,2,2,3].map (options 5 0) := by rfl


theorem t5_329part0 : t5_329jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_329frontier : t5_329root.frontier 0=t5_329jobs := by rfl
theorem t5_329all : t5_329jobs.all (Job.check tree)=true := by
  simp only [t5_329jobs,List.all_append,List.all_nil,t5_329part0,Bool.and_self]
theorem t5_329checked : Checked tree [1,2,2,2,3] := by
  refine ⟨plan3664,valid3664,t5_329choices,?_⟩
  exact check_of_frontier tree 0 t5_329root t5_329jobs t5_329frontier t5_329all
theorem t5_330choices : plan3704.choices=[1,2,2,2,6].map (options 5 1) := by rfl


theorem t5_330part0 : t5_330jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_330frontier : t5_330root.frontier 0=t5_330jobs := by rfl
theorem t5_330all : t5_330jobs.all (Job.check tree)=true := by
  simp only [t5_330jobs,List.all_append,List.all_nil,t5_330part0,Bool.and_self]
theorem t5_330checked : Checked tree [1,2,2,2,6] := by
  refine ⟨plan3704,valid3704,t5_330choices,?_⟩
  exact check_of_frontier tree 0 t5_330root t5_330jobs t5_330frontier t5_330all
theorem t5_331choices : plan3705.choices=[1,2,2,2,7].map (options 5 1) := by rfl


theorem t5_331part0 : t5_331jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_331frontier : t5_331root.frontier 0=t5_331jobs := by rfl
theorem t5_331all : t5_331jobs.all (Job.check tree)=true := by
  simp only [t5_331jobs,List.all_append,List.all_nil,t5_331part0,Bool.and_self]
theorem t5_331checked : Checked tree [1,2,2,2,7] := by
  refine ⟨plan3705,valid3705,t5_331choices,?_⟩
  exact check_of_frontier tree 0 t5_331root t5_331jobs t5_331frontier t5_331all
theorem t5_332choices : plan3706.choices=[1,2,2,2,10].map (options 5 1) := by rfl


theorem t5_332part0 : t5_332jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_332frontier : t5_332root.frontier 0=t5_332jobs := by rfl
theorem t5_332all : t5_332jobs.all (Job.check tree)=true := by
  simp only [t5_332jobs,List.all_append,List.all_nil,t5_332part0,Bool.and_self]
theorem t5_332checked : Checked tree [1,2,2,2,10] := by
  refine ⟨plan3706,valid3706,t5_332choices,?_⟩
  exact check_of_frontier tree 0 t5_332root t5_332jobs t5_332frontier t5_332all
theorem t5_333choices : plan3665.choices=[1,2,2,3,3].map (options 5 0) := by rfl


theorem t5_333part0 : t5_333jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_333frontier : t5_333root.frontier 0=t5_333jobs := by rfl
theorem t5_333all : t5_333jobs.all (Job.check tree)=true := by
  simp only [t5_333jobs,List.all_append,List.all_nil,t5_333part0,Bool.and_self]
theorem t5_333checked : Checked tree [1,2,2,3,3] := by
  refine ⟨plan3665,valid3665,t5_333choices,?_⟩
  exact check_of_frontier tree 0 t5_333root t5_333jobs t5_333frontier t5_333all
theorem t5_334choices : plan3707.choices=[1,2,2,3,6].map (options 5 1) := by rfl


theorem t5_334part0 : t5_334jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_334frontier : t5_334root.frontier 0=t5_334jobs := by rfl
theorem t5_334all : t5_334jobs.all (Job.check tree)=true := by
  simp only [t5_334jobs,List.all_append,List.all_nil,t5_334part0,Bool.and_self]
theorem t5_334checked : Checked tree [1,2,2,3,6] := by
  refine ⟨plan3707,valid3707,t5_334choices,?_⟩
  exact check_of_frontier tree 0 t5_334root t5_334jobs t5_334frontier t5_334all
theorem t5_335choices : plan3708.choices=[1,2,2,3,7].map (options 5 1) := by rfl


theorem t5_335part0 : t5_335jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_335frontier : t5_335root.frontier 0=t5_335jobs := by rfl
theorem t5_335all : t5_335jobs.all (Job.check tree)=true := by
  simp only [t5_335jobs,List.all_append,List.all_nil,t5_335part0,Bool.and_self]
theorem t5_335checked : Checked tree [1,2,2,3,7] := by
  refine ⟨plan3708,valid3708,t5_335choices,?_⟩
  exact check_of_frontier tree 0 t5_335root t5_335jobs t5_335frontier t5_335all
theorem t5_336choices : plan3709.choices=[1,2,2,3,10].map (options 5 1) := by rfl


theorem t5_336part0 : t5_336jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_336frontier : t5_336root.frontier 0=t5_336jobs := by rfl
theorem t5_336all : t5_336jobs.all (Job.check tree)=true := by
  simp only [t5_336jobs,List.all_append,List.all_nil,t5_336part0,Bool.and_self]
theorem t5_336checked : Checked tree [1,2,2,3,10] := by
  refine ⟨plan3709,valid3709,t5_336choices,?_⟩
  exact check_of_frontier tree 0 t5_336root t5_336jobs t5_336frontier t5_336all
theorem t5_337choices : plan3710.choices=[1,2,2,5,3].map (options 5 1) := by rfl


theorem t5_337part0 : t5_337jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_337frontier : t5_337root.frontier 0=t5_337jobs := by rfl
theorem t5_337all : t5_337jobs.all (Job.check tree)=true := by
  simp only [t5_337jobs,List.all_append,List.all_nil,t5_337part0,Bool.and_self]
theorem t5_337checked : Checked tree [1,2,2,5,3] := by
  refine ⟨plan3710,valid3710,t5_337choices,?_⟩
  exact check_of_frontier tree 0 t5_337root t5_337jobs t5_337frontier t5_337all
theorem t5_338choices : plan3838.choices=[1,2,2,5,6].map (options 5 2) := by rfl


theorem t5_338part0 : t5_338jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_338frontier : t5_338root.frontier 0=t5_338jobs := by rfl
theorem t5_338all : t5_338jobs.all (Job.check tree)=true := by
  simp only [t5_338jobs,List.all_append,List.all_nil,t5_338part0,Bool.and_self]
theorem t5_338checked : Checked tree [1,2,2,5,6] := by
  refine ⟨plan3838,valid3838,t5_338choices,?_⟩
  exact check_of_frontier tree 0 t5_338root t5_338jobs t5_338frontier t5_338all
theorem t5_339choices : plan3839.choices=[1,2,2,5,7].map (options 5 2) := by rfl


theorem t5_339part0 : t5_339jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_339frontier : t5_339root.frontier 0=t5_339jobs := by rfl
theorem t5_339all : t5_339jobs.all (Job.check tree)=true := by
  simp only [t5_339jobs,List.all_append,List.all_nil,t5_339part0,Bool.and_self]
theorem t5_339checked : Checked tree [1,2,2,5,7] := by
  refine ⟨plan3839,valid3839,t5_339choices,?_⟩
  exact check_of_frontier tree 0 t5_339root t5_339jobs t5_339frontier t5_339all
theorem t5_340choices : plan3840.choices=[1,2,2,5,10].map (options 5 2) := by rfl


theorem t5_340part0 : t5_340jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_340frontier : t5_340root.frontier 0=t5_340jobs := by rfl
theorem t5_340all : t5_340jobs.all (Job.check tree)=true := by
  simp only [t5_340jobs,List.all_append,List.all_nil,t5_340part0,Bool.and_self]
theorem t5_340checked : Checked tree [1,2,2,5,10] := by
  refine ⟨plan3840,valid3840,t5_340choices,?_⟩
  exact check_of_frontier tree 0 t5_340root t5_340jobs t5_340frontier t5_340all
theorem t5_341choices : plan3841.choices=[1,2,2,6,6].map (options 5 2) := by rfl


theorem t5_341part0 : t5_341jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_341frontier : t5_341root.frontier 0=t5_341jobs := by rfl
theorem t5_341all : t5_341jobs.all (Job.check tree)=true := by
  simp only [t5_341jobs,List.all_append,List.all_nil,t5_341part0,Bool.and_self]
theorem t5_341checked : Checked tree [1,2,2,6,6] := by
  refine ⟨plan3841,valid3841,t5_341choices,?_⟩
  exact check_of_frontier tree 0 t5_341root t5_341jobs t5_341frontier t5_341all
theorem t5_342choices : plan3842.choices=[1,2,2,6,7].map (options 5 2) := by rfl


theorem t5_342part0 : t5_342jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_342frontier : t5_342root.frontier 0=t5_342jobs := by rfl
theorem t5_342all : t5_342jobs.all (Job.check tree)=true := by
  simp only [t5_342jobs,List.all_append,List.all_nil,t5_342part0,Bool.and_self]
theorem t5_342checked : Checked tree [1,2,2,6,7] := by
  refine ⟨plan3842,valid3842,t5_342choices,?_⟩
  exact check_of_frontier tree 0 t5_342root t5_342jobs t5_342frontier t5_342all
theorem t5_343choices : plan3843.choices=[1,2,2,6,10].map (options 5 2) := by rfl


theorem t5_343part0 : t5_343jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_343frontier : t5_343root.frontier 0=t5_343jobs := by rfl
theorem t5_343all : t5_343jobs.all (Job.check tree)=true := by
  simp only [t5_343jobs,List.all_append,List.all_nil,t5_343part0,Bool.and_self]
theorem t5_343checked : Checked tree [1,2,2,6,10] := by
  refine ⟨plan3843,valid3843,t5_343choices,?_⟩
  exact check_of_frontier tree 0 t5_343root t5_343jobs t5_343frontier t5_343all
theorem t5_344choices : plan3844.choices=[1,2,2,7,7].map (options 5 2) := by rfl


theorem t5_344part0 : t5_344jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_344frontier : t5_344root.frontier 0=t5_344jobs := by rfl
theorem t5_344all : t5_344jobs.all (Job.check tree)=true := by
  simp only [t5_344jobs,List.all_append,List.all_nil,t5_344part0,Bool.and_self]
theorem t5_344checked : Checked tree [1,2,2,7,7] := by
  refine ⟨plan3844,valid3844,t5_344choices,?_⟩
  exact check_of_frontier tree 0 t5_344root t5_344jobs t5_344frontier t5_344all
theorem t5_345choices : plan3711.choices=[1,2,2,9,3].map (options 5 1) := by rfl


theorem t5_345part0 : t5_345jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_345frontier : t5_345root.frontier 0=t5_345jobs := by rfl
theorem t5_345all : t5_345jobs.all (Job.check tree)=true := by
  simp only [t5_345jobs,List.all_append,List.all_nil,t5_345part0,Bool.and_self]
theorem t5_345checked : Checked tree [1,2,2,9,3] := by
  refine ⟨plan3711,valid3711,t5_345choices,?_⟩
  exact check_of_frontier tree 0 t5_345root t5_345jobs t5_345frontier t5_345all
theorem t5_346choices : plan3845.choices=[1,2,2,9,6].map (options 5 2) := by rfl


theorem t5_346part0 : t5_346jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_346frontier : t5_346root.frontier 0=t5_346jobs := by rfl
theorem t5_346all : t5_346jobs.all (Job.check tree)=true := by
  simp only [t5_346jobs,List.all_append,List.all_nil,t5_346part0,Bool.and_self]
theorem t5_346checked : Checked tree [1,2,2,9,6] := by
  refine ⟨plan3845,valid3845,t5_346choices,?_⟩
  exact check_of_frontier tree 0 t5_346root t5_346jobs t5_346frontier t5_346all
theorem t5_347choices : plan3846.choices=[1,2,2,9,7].map (options 5 2) := by rfl


theorem t5_347part0 : t5_347jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_347frontier : t5_347root.frontier 0=t5_347jobs := by rfl
theorem t5_347all : t5_347jobs.all (Job.check tree)=true := by
  simp only [t5_347jobs,List.all_append,List.all_nil,t5_347part0,Bool.and_self]
theorem t5_347checked : Checked tree [1,2,2,9,7] := by
  refine ⟨plan3846,valid3846,t5_347choices,?_⟩
  exact check_of_frontier tree 0 t5_347root t5_347jobs t5_347frontier t5_347all
theorem t5_348choices : plan3847.choices=[1,2,2,9,10].map (options 5 2) := by rfl


theorem t5_348part0 : t5_348jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_348frontier : t5_348root.frontier 0=t5_348jobs := by rfl
theorem t5_348all : t5_348jobs.all (Job.check tree)=true := by
  simp only [t5_348jobs,List.all_append,List.all_nil,t5_348part0,Bool.and_self]
theorem t5_348checked : Checked tree [1,2,2,9,10] := by
  refine ⟨plan3847,valid3847,t5_348choices,?_⟩
  exact check_of_frontier tree 0 t5_348root t5_348jobs t5_348frontier t5_348all
theorem t5_349choices : plan3848.choices=[1,2,2,10,7].map (options 5 2) := by rfl


theorem t5_349part0 : t5_349jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_349frontier : t5_349root.frontier 0=t5_349jobs := by rfl
theorem t5_349all : t5_349jobs.all (Job.check tree)=true := by
  simp only [t5_349jobs,List.all_append,List.all_nil,t5_349part0,Bool.and_self]
theorem t5_349checked : Checked tree [1,2,2,10,7] := by
  refine ⟨plan3848,valid3848,t5_349choices,?_⟩
  exact check_of_frontier tree 0 t5_349root t5_349jobs t5_349frontier t5_349all
theorem t5_350choices : plan3849.choices=[1,2,2,10,10].map (options 5 2) := by rfl


theorem t5_350part0 : t5_350jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_350frontier : t5_350root.frontier 0=t5_350jobs := by rfl
theorem t5_350all : t5_350jobs.all (Job.check tree)=true := by
  simp only [t5_350jobs,List.all_append,List.all_nil,t5_350part0,Bool.and_self]
theorem t5_350checked : Checked tree [1,2,2,10,10] := by
  refine ⟨plan3849,valid3849,t5_350choices,?_⟩
  exact check_of_frontier tree 0 t5_350root t5_350jobs t5_350frontier t5_350all
theorem t5_351choices : plan3666.choices=[1,2,3,3,3].map (options 5 0) := by rfl


theorem t5_351part0 : t5_351jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_351frontier : t5_351root.frontier 0=t5_351jobs := by rfl
theorem t5_351all : t5_351jobs.all (Job.check tree)=true := by
  simp only [t5_351jobs,List.all_append,List.all_nil,t5_351part0,Bool.and_self]
theorem t5_351checked : Checked tree [1,2,3,3,3] := by
  refine ⟨plan3666,valid3666,t5_351choices,?_⟩
  exact check_of_frontier tree 0 t5_351root t5_351jobs t5_351frontier t5_351all
theorem t5_352choices : plan3712.choices=[1,2,3,3,6].map (options 5 1) := by rfl


theorem t5_352part0 : t5_352jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_352frontier : t5_352root.frontier 0=t5_352jobs := by rfl
theorem t5_352all : t5_352jobs.all (Job.check tree)=true := by
  simp only [t5_352jobs,List.all_append,List.all_nil,t5_352part0,Bool.and_self]
theorem t5_352checked : Checked tree [1,2,3,3,6] := by
  refine ⟨plan3712,valid3712,t5_352choices,?_⟩
  exact check_of_frontier tree 0 t5_352root t5_352jobs t5_352frontier t5_352all
theorem t5_353choices : plan3713.choices=[1,2,3,3,7].map (options 5 1) := by rfl


theorem t5_353part0 : t5_353jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_353frontier : t5_353root.frontier 0=t5_353jobs := by rfl
theorem t5_353all : t5_353jobs.all (Job.check tree)=true := by
  simp only [t5_353jobs,List.all_append,List.all_nil,t5_353part0,Bool.and_self]
theorem t5_353checked : Checked tree [1,2,3,3,7] := by
  refine ⟨plan3713,valid3713,t5_353choices,?_⟩
  exact check_of_frontier tree 0 t5_353root t5_353jobs t5_353frontier t5_353all
theorem t5_354choices : plan3714.choices=[1,2,3,3,10].map (options 5 1) := by rfl


theorem t5_354part0 : t5_354jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_354frontier : t5_354root.frontier 0=t5_354jobs := by rfl
theorem t5_354all : t5_354jobs.all (Job.check tree)=true := by
  simp only [t5_354jobs,List.all_append,List.all_nil,t5_354part0,Bool.and_self]
theorem t5_354checked : Checked tree [1,2,3,3,10] := by
  refine ⟨plan3714,valid3714,t5_354choices,?_⟩
  exact check_of_frontier tree 0 t5_354root t5_354jobs t5_354frontier t5_354all
theorem t5_355choices : plan3850.choices=[1,2,3,6,6].map (options 5 2) := by rfl


theorem t5_355part0 : t5_355jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_355frontier : t5_355root.frontier 0=t5_355jobs := by rfl
theorem t5_355all : t5_355jobs.all (Job.check tree)=true := by
  simp only [t5_355jobs,List.all_append,List.all_nil,t5_355part0,Bool.and_self]
theorem t5_355checked : Checked tree [1,2,3,6,6] := by
  refine ⟨plan3850,valid3850,t5_355choices,?_⟩
  exact check_of_frontier tree 0 t5_355root t5_355jobs t5_355frontier t5_355all
theorem t5_356choices : plan3851.choices=[1,2,3,6,7].map (options 5 2) := by rfl


theorem t5_356part0 : t5_356jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_356part1 : t5_356jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_356frontier : t5_356root.frontier 1=t5_356jobs := by rfl
theorem t5_356all : t5_356jobs.all (Job.check tree)=true := by
  simp only [t5_356jobs,List.all_append,List.all_nil,t5_356part0,t5_356part1,Bool.and_self]
theorem t5_356checked : Checked tree [1,2,3,6,7] := by
  refine ⟨plan3851,valid3851,t5_356choices,?_⟩
  exact check_of_frontier tree 1 t5_356root t5_356jobs t5_356frontier t5_356all
theorem t5_357choices : plan3852.choices=[1,2,3,6,10].map (options 5 2) := by rfl


theorem t5_357part0 : t5_357jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_357frontier : t5_357root.frontier 0=t5_357jobs := by rfl
theorem t5_357all : t5_357jobs.all (Job.check tree)=true := by
  simp only [t5_357jobs,List.all_append,List.all_nil,t5_357part0,Bool.and_self]
theorem t5_357checked : Checked tree [1,2,3,6,10] := by
  refine ⟨plan3852,valid3852,t5_357choices,?_⟩
  exact check_of_frontier tree 0 t5_357root t5_357jobs t5_357frontier t5_357all
theorem t5_358choices : plan3853.choices=[1,2,3,7,7].map (options 5 2) := by rfl


theorem t5_358part0 : t5_358jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_358frontier : t5_358root.frontier 0=t5_358jobs := by rfl
theorem t5_358all : t5_358jobs.all (Job.check tree)=true := by
  simp only [t5_358jobs,List.all_append,List.all_nil,t5_358part0,Bool.and_self]
theorem t5_358checked : Checked tree [1,2,3,7,7] := by
  refine ⟨plan3853,valid3853,t5_358choices,?_⟩
  exact check_of_frontier tree 0 t5_358root t5_358jobs t5_358frontier t5_358all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks007 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_232checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_245checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_246checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_247checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_248checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_249checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_250checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_251checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_252checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_253checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_254checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_233checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_255checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_256checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_257checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_258checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_259checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_260checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_261checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_262checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_263checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_264checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_234checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_265checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_266checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_267checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_268checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_269checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_270checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_271checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_272checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_273checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_274checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_235checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_275checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_276checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_277checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_278checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_279checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_280checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_281checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_282checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_283checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_284checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_236checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_285checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_286checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_287checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_288checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_289checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_290checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_291checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_292checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_293checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_294checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_237checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_295checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_296checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_297checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_298checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_299checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_300checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_301checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_302checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_303checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_304checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_238checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_305checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_306checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_307checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_308checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_309checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_310checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_311checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_312checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_313checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_314checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_239checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_315checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_316checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_317checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_318checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_319checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_320checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_321checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_322checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_323checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_324checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_240checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_325checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_326checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_327checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_328checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_329checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_330checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_331checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_332checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_333checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_334checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_241checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_335checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_336checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_337checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_338checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_339checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_340checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_341checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_342checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_343checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_344checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_242checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_345checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_346checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_347checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_348checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_349checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_350checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_351checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_352checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_353checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_354checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_243checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_355checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_356checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_357checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_358checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_244checked⟩
