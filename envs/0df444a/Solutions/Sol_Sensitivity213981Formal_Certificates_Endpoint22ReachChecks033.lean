-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks033
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:04:16.819932+00:00
-- url     : https://prove2.me/submissions/bf22ac4b-b242-4444-99c7-3b9481355b6e

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans052
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



























































































































































































theorem valid94 : plan94.Valid := valid_step _ _ _ valid0 (by decide +kernel)




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







theorem valid100 : plan100.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid102 : plan102.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid105 : plan105.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid106 : plan106.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid108 : plan108.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid109 : plan109.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid111 : plan111.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid113 : plan113.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid114 : plan114.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid116 : plan116.Valid := valid_step _ _ _ valid0 (by decide +kernel)
























































































































































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



























































































































































theorem valid462 : plan462.Valid := valid_step _ _ _ valid94 (by decide +kernel)




































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





theorem valid483 : plan483.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid484 : plan484.Valid := valid_step _ _ _ valid100 (by decide +kernel)

theorem valid485 : plan485.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid486 : plan486.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid487 : plan487.Valid := valid_step _ _ _ valid105 (by decide +kernel)



































theorem valid505 : plan505.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid506 : plan506.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid507 : plan507.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid508 : plan508.Valid := valid_step _ _ _ valid106 (by decide +kernel)





theorem valid511 : plan511.Valid := valid_step _ _ _ valid109 (by decide +kernel)





theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid518 : plan518.Valid := valid_step _ _ _ valid106 (by decide +kernel)









theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid524 : plan524.Valid := valid_step _ _ _ valid111 (by decide +kernel)



theorem valid526 : plan526.Valid := valid_step _ _ _ valid113 (by decide +kernel)

theorem valid527 : plan527.Valid := valid_step _ _ _ valid114 (by decide +kernel)



theorem valid529 : plan529.Valid := valid_step _ _ _ valid116 (by decide +kernel)

theorem valid530 : plan530.Valid := valid_step _ _ _ valid113 (by decide +kernel)

theorem valid531 : plan531.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid532 : plan532.Valid := valid_step _ _ _ valid116 (by decide +kernel)

theorem valid533 : plan533.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid534 : plan534.Valid := valid_step _ _ _ valid113 (by decide +kernel)

theorem valid535 : plan535.Valid := valid_step _ _ _ valid114 (by decide +kernel)



theorem valid537 : plan537.Valid := valid_step _ _ _ valid116 (by decide +kernel)

theorem valid538 : plan538.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid539 : plan539.Valid := valid_step _ _ _ valid116 (by decide +kernel)










































































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























































theorem valid1276 : plan1276.Valid := valid_step _ _ _ valid462 (by decide +kernel)









































theorem valid1297 : plan1297.Valid := valid_step _ _ _ valid462 (by decide +kernel)













































theorem valid1320 : plan1320.Valid := valid_step _ _ _ valid483 (by decide +kernel)

theorem valid1321 : plan1321.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1322 : plan1322.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1323 : plan1323.Valid := valid_step _ _ _ valid487 (by decide +kernel)

























theorem valid1336 : plan1336.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1337 : plan1337.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1338 : plan1338.Valid := valid_step _ _ _ valid487 (by decide +kernel)












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









theorem valid1349 : plan1349.Valid := valid_step _ _ _ valid484 (by decide +kernel)































































theorem valid1381 : plan1381.Valid := valid_step _ _ _ valid484 (by decide +kernel)



































theorem valid1399 : plan1399.Valid := valid_step _ _ _ valid511 (by decide +kernel)

theorem valid1400 : plan1400.Valid := valid_step _ _ _ valid514 (by decide +kernel)













theorem valid1407 : plan1407.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1408 : plan1408.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1409 : plan1409.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1410 : plan1410.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1411 : plan1411.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1412 : plan1412.Valid := valid_step _ _ _ valid524 (by decide +kernel)

theorem valid1413 : plan1413.Valid := valid_step _ _ _ valid506 (by decide +kernel)







theorem valid1417 : plan1417.Valid := valid_step _ _ _ valid505 (by decide +kernel)

theorem valid1418 : plan1418.Valid := valid_step _ _ _ valid506 (by decide +kernel)

theorem valid1419 : plan1419.Valid := valid_step _ _ _ valid507 (by decide +kernel)

theorem valid1420 : plan1420.Valid := valid_step _ _ _ valid508 (by decide +kernel)



















theorem valid1430 : plan1430.Valid := valid_step _ _ _ valid518 (by decide +kernel)




















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













































































































theorem valid2647 : plan2647.Valid := valid_step _ _ _ valid1297 (by decide +kernel)













theorem valid2654 : plan2654.Valid := valid_step _ _ _ valid1276 (by decide +kernel)




































































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





























































theorem valid3967 : plan3967.Valid := valid_step _ _ _ valid2647 (by decide +kernel)

theorem valid3968 : plan3968.Valid := valid_step _ _ _ valid2654 (by decide +kernel)
































































































































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































theorem valid2800 : plan2800.Valid := valid_step _ _ _ valid1349 (by decide +kernel)









theorem valid2805 : plan2805.Valid := valid_step _ _ _ valid1381 (by decide +kernel)







theorem valid2809 : plan2809.Valid := valid_step _ _ _ valid1336 (by decide +kernel)

theorem valid2810 : plan2810.Valid := valid_step _ _ _ valid1337 (by decide +kernel)

theorem valid2811 : plan2811.Valid := valid_step _ _ _ valid1338 (by decide +kernel)













theorem valid2818 : plan2818.Valid := valid_step _ _ _ valid1349 (by decide +kernel)











theorem valid2824 : plan2824.Valid := valid_step _ _ _ valid1381 (by decide +kernel)









theorem valid2829 : plan2829.Valid := valid_step _ _ _ valid1320 (by decide +kernel)

theorem valid2830 : plan2830.Valid := valid_step _ _ _ valid1321 (by decide +kernel)

theorem valid2831 : plan2831.Valid := valid_step _ _ _ valid1322 (by decide +kernel)

theorem valid2832 : plan2832.Valid := valid_step _ _ _ valid1323 (by decide +kernel)
































































































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







theorem valid1444 : plan1444.Valid := valid_step _ _ _ valid506 (by decide +kernel)







theorem valid1448 : plan1448.Valid := valid_step _ _ _ valid505 (by decide +kernel)

theorem valid1449 : plan1449.Valid := valid_step _ _ _ valid506 (by decide +kernel)

theorem valid1450 : plan1450.Valid := valid_step _ _ _ valid507 (by decide +kernel)









theorem valid1455 : plan1455.Valid := valid_step _ _ _ valid518 (by decide +kernel)



















theorem valid1465 : plan1465.Valid := valid_step _ _ _ valid531 (by decide +kernel)

theorem valid1466 : plan1466.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1467 : plan1467.Valid := valid_step _ _ _ valid538 (by decide +kernel)



theorem valid1469 : plan1469.Valid := valid_step _ _ _ valid526 (by decide +kernel)

theorem valid1470 : plan1470.Valid := valid_step _ _ _ valid527 (by decide +kernel)



theorem valid1472 : plan1472.Valid := valid_step _ _ _ valid529 (by decide +kernel)

theorem valid1473 : plan1473.Valid := valid_step _ _ _ valid530 (by decide +kernel)

theorem valid1474 : plan1474.Valid := valid_step _ _ _ valid531 (by decide +kernel)

theorem valid1475 : plan1475.Valid := valid_step _ _ _ valid532 (by decide +kernel)

theorem valid1476 : plan1476.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1477 : plan1477.Valid := valid_step _ _ _ valid534 (by decide +kernel)

theorem valid1478 : plan1478.Valid := valid_step _ _ _ valid535 (by decide +kernel)



theorem valid1480 : plan1480.Valid := valid_step _ _ _ valid537 (by decide +kernel)

theorem valid1481 : plan1481.Valid := valid_step _ _ _ valid538 (by decide +kernel)

theorem valid1482 : plan1482.Valid := valid_step _ _ _ valid539 (by decide +kernel)

theorem valid1483 : plan1483.Valid := valid_step _ _ _ valid530 (by decide +kernel)

theorem valid1484 : plan1484.Valid := valid_step _ _ _ valid531 (by decide +kernel)

theorem valid1485 : plan1485.Valid := valid_step _ _ _ valid532 (by decide +kernel)

theorem valid1486 : plan1486.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1487 : plan1487.Valid := valid_step _ _ _ valid538 (by decide +kernel)

theorem valid1488 : plan1488.Valid := valid_step _ _ _ valid539 (by decide +kernel)

theorem valid1489 : plan1489.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1490 : plan1490.Valid := valid_step _ _ _ valid531 (by decide +kernel)

theorem valid1491 : plan1491.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1492 : plan1492.Valid := valid_step _ _ _ valid538 (by decide +kernel)

theorem valid1493 : plan1493.Valid := valid_step _ _ _ valid530 (by decide +kernel)

theorem valid1494 : plan1494.Valid := valid_step _ _ _ valid531 (by decide +kernel)

theorem valid1495 : plan1495.Valid := valid_step _ _ _ valid532 (by decide +kernel)

theorem valid1496 : plan1496.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1497 : plan1497.Valid := valid_step _ _ _ valid534 (by decide +kernel)

theorem valid1498 : plan1498.Valid := valid_step _ _ _ valid535 (by decide +kernel)



theorem valid1500 : plan1500.Valid := valid_step _ _ _ valid537 (by decide +kernel)

theorem valid1501 : plan1501.Valid := valid_step _ _ _ valid538 (by decide +kernel)

theorem valid1502 : plan1502.Valid := valid_step _ _ _ valid539 (by decide +kernel)

theorem valid1503 : plan1503.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1504 : plan1504.Valid := valid_step _ _ _ valid538 (by decide +kernel)

theorem valid1505 : plan1505.Valid := valid_step _ _ _ valid539 (by decide +kernel)






























































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



























































































theorem valid2926 : plan2926.Valid := valid_step _ _ _ valid1411 (by decide +kernel)

theorem valid2927 : plan2927.Valid := valid_step _ _ _ valid1412 (by decide +kernel)

theorem valid2928 : plan2928.Valid := valid_step _ _ _ valid1413 (by decide +kernel)







theorem valid2932 : plan2932.Valid := valid_step _ _ _ valid1417 (by decide +kernel)

theorem valid2933 : plan2933.Valid := valid_step _ _ _ valid1418 (by decide +kernel)

theorem valid2934 : plan2934.Valid := valid_step _ _ _ valid1419 (by decide +kernel)































theorem valid2950 : plan2950.Valid := valid_step _ _ _ valid1444 (by decide +kernel)







theorem valid2954 : plan2954.Valid := valid_step _ _ _ valid1448 (by decide +kernel)

theorem valid2955 : plan2955.Valid := valid_step _ _ _ valid1449 (by decide +kernel)

theorem valid2956 : plan2956.Valid := valid_step _ _ _ valid1450 (by decide +kernel)





















theorem valid2967 : plan2967.Valid := valid_step _ _ _ valid1407 (by decide +kernel)

theorem valid2968 : plan2968.Valid := valid_step _ _ _ valid1408 (by decide +kernel)

theorem valid2969 : plan2969.Valid := valid_step _ _ _ valid1409 (by decide +kernel)

theorem valid2970 : plan2970.Valid := valid_step _ _ _ valid1410 (by decide +kernel)

theorem valid2971 : plan2971.Valid := valid_step _ _ _ valid1411 (by decide +kernel)

theorem valid2972 : plan2972.Valid := valid_step _ _ _ valid1412 (by decide +kernel)

theorem valid2973 : plan2973.Valid := valid_step _ _ _ valid1417 (by decide +kernel)

theorem valid2974 : plan2974.Valid := valid_step _ _ _ valid1418 (by decide +kernel)

theorem valid2975 : plan2975.Valid := valid_step _ _ _ valid1419 (by decide +kernel)

theorem valid2976 : plan2976.Valid := valid_step _ _ _ valid1420 (by decide +kernel)
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



















theorem valid2986 : plan2986.Valid := valid_step _ _ _ valid1430 (by decide +kernel)



























theorem valid3000 : plan3000.Valid := valid_step _ _ _ valid1448 (by decide +kernel)

theorem valid3001 : plan3001.Valid := valid_step _ _ _ valid1449 (by decide +kernel)

theorem valid3002 : plan3002.Valid := valid_step _ _ _ valid1450 (by decide +kernel)









theorem valid3007 : plan3007.Valid := valid_step _ _ _ valid1455 (by decide +kernel)









































theorem valid3028 : plan3028.Valid := valid_step _ _ _ valid1399 (by decide +kernel)

theorem valid3029 : plan3029.Valid := valid_step _ _ _ valid1400 (by decide +kernel)






















































































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













































































theorem valid3111 : plan3111.Valid := valid_step _ _ _ valid1465 (by decide +kernel)

theorem valid3112 : plan3112.Valid := valid_step _ _ _ valid1466 (by decide +kernel)

theorem valid3113 : plan3113.Valid := valid_step _ _ _ valid1467 (by decide +kernel)

theorem valid3114 : plan3114.Valid := valid_step _ _ _ valid1470 (by decide +kernel)

theorem valid3115 : plan3115.Valid := valid_step _ _ _ valid1473 (by decide +kernel)

theorem valid3116 : plan3116.Valid := valid_step _ _ _ valid1474 (by decide +kernel)

theorem valid3117 : plan3117.Valid := valid_step _ _ _ valid1475 (by decide +kernel)

theorem valid3118 : plan3118.Valid := valid_step _ _ _ valid1476 (by decide +kernel)

theorem valid3119 : plan3119.Valid := valid_step _ _ _ valid1478 (by decide +kernel)

theorem valid3120 : plan3120.Valid := valid_step _ _ _ valid1481 (by decide +kernel)

theorem valid3121 : plan3121.Valid := valid_step _ _ _ valid1482 (by decide +kernel)

theorem valid3122 : plan3122.Valid := valid_step _ _ _ valid1483 (by decide +kernel)

theorem valid3123 : plan3123.Valid := valid_step _ _ _ valid1484 (by decide +kernel)

theorem valid3124 : plan3124.Valid := valid_step _ _ _ valid1485 (by decide +kernel)

theorem valid3125 : plan3125.Valid := valid_step _ _ _ valid1486 (by decide +kernel)

theorem valid3126 : plan3126.Valid := valid_step _ _ _ valid1487 (by decide +kernel)

theorem valid3127 : plan3127.Valid := valid_step _ _ _ valid1488 (by decide +kernel)

theorem valid3128 : plan3128.Valid := valid_step _ _ _ valid1489 (by decide +kernel)

theorem valid3129 : plan3129.Valid := valid_step _ _ _ valid1490 (by decide +kernel)

theorem valid3130 : plan3130.Valid := valid_step _ _ _ valid1491 (by decide +kernel)

theorem valid3131 : plan3131.Valid := valid_step _ _ _ valid1492 (by decide +kernel)

theorem valid3132 : plan3132.Valid := valid_step _ _ _ valid1493 (by decide +kernel)

theorem valid3133 : plan3133.Valid := valid_step _ _ _ valid1494 (by decide +kernel)

theorem valid3134 : plan3134.Valid := valid_step _ _ _ valid1495 (by decide +kernel)

theorem valid3135 : plan3135.Valid := valid_step _ _ _ valid1496 (by decide +kernel)

theorem valid3136 : plan3136.Valid := valid_step _ _ _ valid1498 (by decide +kernel)

theorem valid3137 : plan3137.Valid := valid_step _ _ _ valid1501 (by decide +kernel)

theorem valid3138 : plan3138.Valid := valid_step _ _ _ valid1502 (by decide +kernel)

theorem valid3139 : plan3139.Valid := valid_step _ _ _ valid1503 (by decide +kernel)

theorem valid3140 : plan3140.Valid := valid_step _ _ _ valid1504 (by decide +kernel)

theorem valid3141 : plan3141.Valid := valid_step _ _ _ valid1505 (by decide +kernel)



theorem valid3143 : plan3143.Valid := valid_step _ _ _ valid1469 (by decide +kernel)

theorem valid3144 : plan3144.Valid := valid_step _ _ _ valid1470 (by decide +kernel)



theorem valid3146 : plan3146.Valid := valid_step _ _ _ valid1472 (by decide +kernel)

theorem valid3147 : plan3147.Valid := valid_step _ _ _ valid1473 (by decide +kernel)

theorem valid3148 : plan3148.Valid := valid_step _ _ _ valid1474 (by decide +kernel)

theorem valid3149 : plan3149.Valid := valid_step _ _ _ valid1475 (by decide +kernel)

theorem valid3150 : plan3150.Valid := valid_step _ _ _ valid1476 (by decide +kernel)

theorem valid3151 : plan3151.Valid := valid_step _ _ _ valid1477 (by decide +kernel)

theorem valid3152 : plan3152.Valid := valid_step _ _ _ valid1478 (by decide +kernel)



theorem valid3154 : plan3154.Valid := valid_step _ _ _ valid1480 (by decide +kernel)

theorem valid3155 : plan3155.Valid := valid_step _ _ _ valid1481 (by decide +kernel)

theorem valid3156 : plan3156.Valid := valid_step _ _ _ valid1482 (by decide +kernel)

theorem valid3157 : plan3157.Valid := valid_step _ _ _ valid1483 (by decide +kernel)

theorem valid3158 : plan3158.Valid := valid_step _ _ _ valid1484 (by decide +kernel)

theorem valid3159 : plan3159.Valid := valid_step _ _ _ valid1485 (by decide +kernel)

theorem valid3160 : plan3160.Valid := valid_step _ _ _ valid1486 (by decide +kernel)

theorem valid3161 : plan3161.Valid := valid_step _ _ _ valid1487 (by decide +kernel)

theorem valid3162 : plan3162.Valid := valid_step _ _ _ valid1488 (by decide +kernel)

theorem valid3163 : plan3163.Valid := valid_step _ _ _ valid1489 (by decide +kernel)

theorem valid3164 : plan3164.Valid := valid_step _ _ _ valid1493 (by decide +kernel)

theorem valid3165 : plan3165.Valid := valid_step _ _ _ valid1494 (by decide +kernel)

theorem valid3166 : plan3166.Valid := valid_step _ _ _ valid1495 (by decide +kernel)

theorem valid3167 : plan3167.Valid := valid_step _ _ _ valid1496 (by decide +kernel)

theorem valid3168 : plan3168.Valid := valid_step _ _ _ valid1497 (by decide +kernel)
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



































































theorem valid4354 : plan4354.Valid := valid_step _ _ _ valid2800 (by decide +kernel)

theorem valid4355 : plan4355.Valid := valid_step _ _ _ valid2805 (by decide +kernel)

theorem valid4356 : plan4356.Valid := valid_step _ _ _ valid2809 (by decide +kernel)

theorem valid4357 : plan4357.Valid := valid_step _ _ _ valid2810 (by decide +kernel)

theorem valid4358 : plan4358.Valid := valid_step _ _ _ valid2811 (by decide +kernel)

theorem valid4359 : plan4359.Valid := valid_step _ _ _ valid2818 (by decide +kernel)

theorem valid4360 : plan4360.Valid := valid_step _ _ _ valid2824 (by decide +kernel)

theorem valid4361 : plan4361.Valid := valid_step _ _ _ valid2829 (by decide +kernel)

theorem valid4362 : plan4362.Valid := valid_step _ _ _ valid2830 (by decide +kernel)

theorem valid4363 : plan4363.Valid := valid_step _ _ _ valid2831 (by decide +kernel)

theorem valid4364 : plan4364.Valid := valid_step _ _ _ valid2832 (by decide +kernel)








































































































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

theorem valid4801 : plan4801.Valid := valid_step _ _ _ valid2926 (by decide +kernel)

theorem valid4802 : plan4802.Valid := valid_step _ _ _ valid2927 (by decide +kernel)

theorem valid4803 : plan4803.Valid := valid_step _ _ _ valid2928 (by decide +kernel)

theorem valid4804 : plan4804.Valid := valid_step _ _ _ valid2932 (by decide +kernel)

theorem valid4805 : plan4805.Valid := valid_step _ _ _ valid2933 (by decide +kernel)

theorem valid4806 : plan4806.Valid := valid_step _ _ _ valid2934 (by decide +kernel)

theorem valid4807 : plan4807.Valid := valid_step _ _ _ valid2950 (by decide +kernel)

theorem valid4808 : plan4808.Valid := valid_step _ _ _ valid2954 (by decide +kernel)

theorem valid4809 : plan4809.Valid := valid_step _ _ _ valid2955 (by decide +kernel)

theorem valid4810 : plan4810.Valid := valid_step _ _ _ valid2956 (by decide +kernel)

theorem valid4811 : plan4811.Valid := valid_step _ _ _ valid2967 (by decide +kernel)

theorem valid4812 : plan4812.Valid := valid_step _ _ _ valid2968 (by decide +kernel)

theorem valid4813 : plan4813.Valid := valid_step _ _ _ valid2969 (by decide +kernel)

theorem valid4814 : plan4814.Valid := valid_step _ _ _ valid2970 (by decide +kernel)

theorem valid4815 : plan4815.Valid := valid_step _ _ _ valid2971 (by decide +kernel)

theorem valid4816 : plan4816.Valid := valid_step _ _ _ valid2972 (by decide +kernel)

theorem valid4817 : plan4817.Valid := valid_step _ _ _ valid2973 (by decide +kernel)

theorem valid4818 : plan4818.Valid := valid_step _ _ _ valid2974 (by decide +kernel)

theorem valid4819 : plan4819.Valid := valid_step _ _ _ valid2975 (by decide +kernel)

theorem valid4820 : plan4820.Valid := valid_step _ _ _ valid2976 (by decide +kernel)

theorem valid4821 : plan4821.Valid := valid_step _ _ _ valid2986 (by decide +kernel)

theorem valid4822 : plan4822.Valid := valid_step _ _ _ valid3000 (by decide +kernel)

theorem valid4823 : plan4823.Valid := valid_step _ _ _ valid3001 (by decide +kernel)

theorem valid4824 : plan4824.Valid := valid_step _ _ _ valid3002 (by decide +kernel)

theorem valid4825 : plan4825.Valid := valid_step _ _ _ valid3007 (by decide +kernel)

theorem valid4826 : plan4826.Valid := valid_step _ _ _ valid3028 (by decide +kernel)

theorem valid4827 : plan4827.Valid := valid_step _ _ _ valid3029 (by decide +kernel)










































































































































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

theorem valid3169 : plan3169.Valid := valid_step _ _ _ valid1498 (by decide +kernel)



theorem valid3171 : plan3171.Valid := valid_step _ _ _ valid1500 (by decide +kernel)

theorem valid3172 : plan3172.Valid := valid_step _ _ _ valid1501 (by decide +kernel)

theorem valid3173 : plan3173.Valid := valid_step _ _ _ valid1502 (by decide +kernel)

theorem valid3174 : plan3174.Valid := valid_step _ _ _ valid1503 (by decide +kernel)

theorem valid3175 : plan3175.Valid := valid_step _ _ _ valid1504 (by decide +kernel)

theorem valid3176 : plan3176.Valid := valid_step _ _ _ valid1505 (by decide +kernel)

theorem valid3177 : plan3177.Valid := valid_step _ _ _ valid1483 (by decide +kernel)

theorem valid3178 : plan3178.Valid := valid_step _ _ _ valid1484 (by decide +kernel)

theorem valid3179 : plan3179.Valid := valid_step _ _ _ valid1485 (by decide +kernel)

theorem valid3180 : plan3180.Valid := valid_step _ _ _ valid1486 (by decide +kernel)

theorem valid3181 : plan3181.Valid := valid_step _ _ _ valid1487 (by decide +kernel)

theorem valid3182 : plan3182.Valid := valid_step _ _ _ valid1488 (by decide +kernel)

theorem valid3183 : plan3183.Valid := valid_step _ _ _ valid1489 (by decide +kernel)

theorem valid3184 : plan3184.Valid := valid_step _ _ _ valid1503 (by decide +kernel)

theorem valid3185 : plan3185.Valid := valid_step _ _ _ valid1504 (by decide +kernel)

theorem valid3186 : plan3186.Valid := valid_step _ _ _ valid1505 (by decide +kernel)

theorem valid3187 : plan3187.Valid := valid_step _ _ _ valid1489 (by decide +kernel)


























































































































































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













theorem valid4999 : plan4999.Valid := valid_step _ _ _ valid3111 (by decide +kernel)

theorem valid5000 : plan5000.Valid := valid_step _ _ _ valid3112 (by decide +kernel)

theorem valid5001 : plan5001.Valid := valid_step _ _ _ valid3113 (by decide +kernel)

theorem valid5002 : plan5002.Valid := valid_step _ _ _ valid3114 (by decide +kernel)

theorem valid5003 : plan5003.Valid := valid_step _ _ _ valid3115 (by decide +kernel)

theorem valid5004 : plan5004.Valid := valid_step _ _ _ valid3116 (by decide +kernel)

theorem valid5005 : plan5005.Valid := valid_step _ _ _ valid3117 (by decide +kernel)

theorem valid5006 : plan5006.Valid := valid_step _ _ _ valid3118 (by decide +kernel)

theorem valid5007 : plan5007.Valid := valid_step _ _ _ valid3119 (by decide +kernel)

theorem valid5008 : plan5008.Valid := valid_step _ _ _ valid3120 (by decide +kernel)

theorem valid5009 : plan5009.Valid := valid_step _ _ _ valid3121 (by decide +kernel)

theorem valid5010 : plan5010.Valid := valid_step _ _ _ valid3122 (by decide +kernel)

theorem valid5011 : plan5011.Valid := valid_step _ _ _ valid3123 (by decide +kernel)

theorem valid5012 : plan5012.Valid := valid_step _ _ _ valid3124 (by decide +kernel)

theorem valid5013 : plan5013.Valid := valid_step _ _ _ valid3125 (by decide +kernel)

theorem valid5014 : plan5014.Valid := valid_step _ _ _ valid3126 (by decide +kernel)

theorem valid5015 : plan5015.Valid := valid_step _ _ _ valid3127 (by decide +kernel)

theorem valid5016 : plan5016.Valid := valid_step _ _ _ valid3128 (by decide +kernel)

theorem valid5017 : plan5017.Valid := valid_step _ _ _ valid3129 (by decide +kernel)

theorem valid5018 : plan5018.Valid := valid_step _ _ _ valid3130 (by decide +kernel)

theorem valid5019 : plan5019.Valid := valid_step _ _ _ valid3131 (by decide +kernel)

theorem valid5020 : plan5020.Valid := valid_step _ _ _ valid3132 (by decide +kernel)

theorem valid5021 : plan5021.Valid := valid_step _ _ _ valid3133 (by decide +kernel)

theorem valid5022 : plan5022.Valid := valid_step _ _ _ valid3134 (by decide +kernel)

theorem valid5023 : plan5023.Valid := valid_step _ _ _ valid3135 (by decide +kernel)

theorem valid5024 : plan5024.Valid := valid_step _ _ _ valid3136 (by decide +kernel)

theorem valid5025 : plan5025.Valid := valid_step _ _ _ valid3137 (by decide +kernel)

theorem valid5026 : plan5026.Valid := valid_step _ _ _ valid3138 (by decide +kernel)

theorem valid5027 : plan5027.Valid := valid_step _ _ _ valid3139 (by decide +kernel)

theorem valid5028 : plan5028.Valid := valid_step _ _ _ valid3140 (by decide +kernel)

theorem valid5029 : plan5029.Valid := valid_step _ _ _ valid3141 (by decide +kernel)

theorem valid5030 : plan5030.Valid := valid_step _ _ _ valid3143 (by decide +kernel)

theorem valid5031 : plan5031.Valid := valid_step _ _ _ valid3144 (by decide +kernel)

theorem valid5032 : plan5032.Valid := valid_step _ _ _ valid3146 (by decide +kernel)

theorem valid5033 : plan5033.Valid := valid_step _ _ _ valid3147 (by decide +kernel)

theorem valid5034 : plan5034.Valid := valid_step _ _ _ valid3148 (by decide +kernel)

theorem valid5035 : plan5035.Valid := valid_step _ _ _ valid3149 (by decide +kernel)

theorem valid5036 : plan5036.Valid := valid_step _ _ _ valid3150 (by decide +kernel)

theorem valid5037 : plan5037.Valid := valid_step _ _ _ valid3151 (by decide +kernel)

theorem valid5038 : plan5038.Valid := valid_step _ _ _ valid3152 (by decide +kernel)

theorem valid5039 : plan5039.Valid := valid_step _ _ _ valid3154 (by decide +kernel)

theorem valid5040 : plan5040.Valid := valid_step _ _ _ valid3155 (by decide +kernel)

theorem valid5041 : plan5041.Valid := valid_step _ _ _ valid3156 (by decide +kernel)

theorem valid5042 : plan5042.Valid := valid_step _ _ _ valid3157 (by decide +kernel)

theorem valid5043 : plan5043.Valid := valid_step _ _ _ valid3158 (by decide +kernel)

theorem valid5044 : plan5044.Valid := valid_step _ _ _ valid3159 (by decide +kernel)

theorem valid5045 : plan5045.Valid := valid_step _ _ _ valid3160 (by decide +kernel)

theorem valid5046 : plan5046.Valid := valid_step _ _ _ valid3161 (by decide +kernel)

theorem valid5047 : plan5047.Valid := valid_step _ _ _ valid3162 (by decide +kernel)

theorem valid5048 : plan5048.Valid := valid_step _ _ _ valid3163 (by decide +kernel)

theorem valid5049 : plan5049.Valid := valid_step _ _ _ valid3164 (by decide +kernel)

theorem valid5050 : plan5050.Valid := valid_step _ _ _ valid3165 (by decide +kernel)

theorem valid5051 : plan5051.Valid := valid_step _ _ _ valid3166 (by decide +kernel)

theorem valid5052 : plan5052.Valid := valid_step _ _ _ valid3167 (by decide +kernel)

theorem valid5053 : plan5053.Valid := valid_step _ _ _ valid3168 (by decide +kernel)

theorem valid5054 : plan5054.Valid := valid_step _ _ _ valid3169 (by decide +kernel)

theorem valid5055 : plan5055.Valid := valid_step _ _ _ valid3171 (by decide +kernel)

theorem valid5056 : plan5056.Valid := valid_step _ _ _ valid3172 (by decide +kernel)

theorem valid5057 : plan5057.Valid := valid_step _ _ _ valid3173 (by decide +kernel)

theorem valid5058 : plan5058.Valid := valid_step _ _ _ valid3174 (by decide +kernel)

theorem valid5059 : plan5059.Valid := valid_step _ _ _ valid3175 (by decide +kernel)

theorem valid5060 : plan5060.Valid := valid_step _ _ _ valid3176 (by decide +kernel)

theorem valid5061 : plan5061.Valid := valid_step _ _ _ valid3177 (by decide +kernel)

theorem valid5062 : plan5062.Valid := valid_step _ _ _ valid3178 (by decide +kernel)

theorem valid5063 : plan5063.Valid := valid_step _ _ _ valid3179 (by decide +kernel)

theorem valid5064 : plan5064.Valid := valid_step _ _ _ valid3180 (by decide +kernel)

theorem valid5065 : plan5065.Valid := valid_step _ _ _ valid3181 (by decide +kernel)

theorem valid5066 : plan5066.Valid := valid_step _ _ _ valid3182 (by decide +kernel)

theorem valid5067 : plan5067.Valid := valid_step _ _ _ valid3183 (by decide +kernel)

theorem valid5068 : plan5068.Valid := valid_step _ _ _ valid3184 (by decide +kernel)

theorem valid5069 : plan5069.Valid := valid_step _ _ _ valid3185 (by decide +kernel)

theorem valid5070 : plan5070.Valid := valid_step _ _ _ valid3186 (by decide +kernel)

theorem valid5071 : plan5071.Valid := valid_step _ _ _ valid3187 (by decide +kernel)


































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
theorem t5_1008choices : plan4801.choices=[4,4,3,10,7].map (options 5 4) := by rfl


theorem t5_1008part0 : t5_1008jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1008frontier : t5_1008root.frontier 0=t5_1008jobs := by rfl
theorem t5_1008all : t5_1008jobs.all (Job.check tree)=true := by
  simp only [t5_1008jobs,List.all_append,List.all_nil,t5_1008part0,Bool.and_self]
theorem t5_1008checked : Checked tree [4,4,3,10,7] := by
  refine ⟨plan4801,valid4801,t5_1008choices,?_⟩
  exact check_of_frontier tree 0 t5_1008root t5_1008jobs t5_1008frontier t5_1008all
theorem t5_1009choices : plan4802.choices=[4,4,3,10,10].map (options 5 4) := by rfl


theorem t5_1009part0 : t5_1009jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1009frontier : t5_1009root.frontier 0=t5_1009jobs := by rfl
theorem t5_1009all : t5_1009jobs.all (Job.check tree)=true := by
  simp only [t5_1009jobs,List.all_append,List.all_nil,t5_1009part0,Bool.and_self]
theorem t5_1009checked : Checked tree [4,4,3,10,10] := by
  refine ⟨plan4802,valid4802,t5_1009choices,?_⟩
  exact check_of_frontier tree 0 t5_1009root t5_1009jobs t5_1009frontier t5_1009all
theorem t5_1010choices : plan4803.choices=[4,4,4,3,7].map (options 5 4) := by rfl


theorem t5_1010part0 : t5_1010jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1010frontier : t5_1010root.frontier 0=t5_1010jobs := by rfl
theorem t5_1010all : t5_1010jobs.all (Job.check tree)=true := by
  simp only [t5_1010jobs,List.all_append,List.all_nil,t5_1010part0,Bool.and_self]
theorem t5_1010checked : Checked tree [4,4,4,3,7] := by
  refine ⟨plan4803,valid4803,t5_1010choices,?_⟩
  exact check_of_frontier tree 0 t5_1010root t5_1010jobs t5_1010frontier t5_1010all
theorem t5_1011choices : plan4999.choices=[4,4,4,6,7].map (options 5 5) := by rfl


theorem t5_1011part0 : t5_1011jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1011frontier : t5_1011root.frontier 0=t5_1011jobs := by rfl
theorem t5_1011all : t5_1011jobs.all (Job.check tree)=true := by
  simp only [t5_1011jobs,List.all_append,List.all_nil,t5_1011part0,Bool.and_self]
theorem t5_1011checked : Checked tree [4,4,4,6,7] := by
  refine ⟨plan4999,valid4999,t5_1011choices,?_⟩
  exact check_of_frontier tree 0 t5_1011root t5_1011jobs t5_1011frontier t5_1011all
theorem t5_1012choices : plan5000.choices=[4,4,4,7,7].map (options 5 5) := by rfl


theorem t5_1012part0 : t5_1012jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1012frontier : t5_1012root.frontier 0=t5_1012jobs := by rfl
theorem t5_1012all : t5_1012jobs.all (Job.check tree)=true := by
  simp only [t5_1012jobs,List.all_append,List.all_nil,t5_1012part0,Bool.and_self]
theorem t5_1012checked : Checked tree [4,4,4,7,7] := by
  refine ⟨plan5000,valid5000,t5_1012choices,?_⟩
  exact check_of_frontier tree 0 t5_1012root t5_1012jobs t5_1012frontier t5_1012all
theorem t5_1013choices : plan5001.choices=[4,4,4,10,7].map (options 5 5) := by rfl


theorem t5_1013part0 : t5_1013jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1013frontier : t5_1013root.frontier 0=t5_1013jobs := by rfl
theorem t5_1013all : t5_1013jobs.all (Job.check tree)=true := by
  simp only [t5_1013jobs,List.all_append,List.all_nil,t5_1013part0,Bool.and_self]
theorem t5_1013checked : Checked tree [4,4,4,10,7] := by
  refine ⟨plan5001,valid5001,t5_1013choices,?_⟩
  exact check_of_frontier tree 0 t5_1013root t5_1013jobs t5_1013frontier t5_1013all
theorem t5_1014choices : plan4354.choices=[4,4,5,3,3].map (options 5 3) := by rfl


theorem t5_1014part0 : t5_1014jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1014frontier : t5_1014root.frontier 0=t5_1014jobs := by rfl
theorem t5_1014all : t5_1014jobs.all (Job.check tree)=true := by
  simp only [t5_1014jobs,List.all_append,List.all_nil,t5_1014part0,Bool.and_self]
theorem t5_1014checked : Checked tree [4,4,5,3,3] := by
  refine ⟨plan4354,valid4354,t5_1014choices,?_⟩
  exact check_of_frontier tree 0 t5_1014root t5_1014jobs t5_1014frontier t5_1014all
theorem t5_1015choices : plan4804.choices=[4,4,5,3,6].map (options 5 4) := by rfl


theorem t5_1015part0 : t5_1015jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1015frontier : t5_1015root.frontier 0=t5_1015jobs := by rfl
theorem t5_1015all : t5_1015jobs.all (Job.check tree)=true := by
  simp only [t5_1015jobs,List.all_append,List.all_nil,t5_1015part0,Bool.and_self]
theorem t5_1015checked : Checked tree [4,4,5,3,6] := by
  refine ⟨plan4804,valid4804,t5_1015choices,?_⟩
  exact check_of_frontier tree 0 t5_1015root t5_1015jobs t5_1015frontier t5_1015all
theorem t5_1016choices : plan4805.choices=[4,4,5,3,7].map (options 5 4) := by rfl


theorem t5_1016part0 : t5_1016jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1016frontier : t5_1016root.frontier 0=t5_1016jobs := by rfl
theorem t5_1016all : t5_1016jobs.all (Job.check tree)=true := by
  simp only [t5_1016jobs,List.all_append,List.all_nil,t5_1016part0,Bool.and_self]
theorem t5_1016checked : Checked tree [4,4,5,3,7] := by
  refine ⟨plan4805,valid4805,t5_1016choices,?_⟩
  exact check_of_frontier tree 0 t5_1016root t5_1016jobs t5_1016frontier t5_1016all
theorem t5_1017choices : plan4806.choices=[4,4,5,3,10].map (options 5 4) := by rfl


theorem t5_1017part0 : t5_1017jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1017frontier : t5_1017root.frontier 0=t5_1017jobs := by rfl
theorem t5_1017all : t5_1017jobs.all (Job.check tree)=true := by
  simp only [t5_1017jobs,List.all_append,List.all_nil,t5_1017part0,Bool.and_self]
theorem t5_1017checked : Checked tree [4,4,5,3,10] := by
  refine ⟨plan4806,valid4806,t5_1017choices,?_⟩
  exact check_of_frontier tree 0 t5_1017root t5_1017jobs t5_1017frontier t5_1017all
theorem t5_1018choices : plan5002.choices=[4,4,5,5,7].map (options 5 5) := by rfl


theorem t5_1018part0 : t5_1018jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1018frontier : t5_1018root.frontier 0=t5_1018jobs := by rfl
theorem t5_1018all : t5_1018jobs.all (Job.check tree)=true := by
  simp only [t5_1018jobs,List.all_append,List.all_nil,t5_1018part0,Bool.and_self]
theorem t5_1018checked : Checked tree [4,4,5,5,7] := by
  refine ⟨plan5002,valid5002,t5_1018choices,?_⟩
  exact check_of_frontier tree 0 t5_1018root t5_1018jobs t5_1018frontier t5_1018all
theorem t5_1019choices : plan5003.choices=[4,4,5,6,6].map (options 5 5) := by rfl


theorem t5_1019part0 : t5_1019jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1019frontier : t5_1019root.frontier 0=t5_1019jobs := by rfl
theorem t5_1019all : t5_1019jobs.all (Job.check tree)=true := by
  simp only [t5_1019jobs,List.all_append,List.all_nil,t5_1019part0,Bool.and_self]
theorem t5_1019checked : Checked tree [4,4,5,6,6] := by
  refine ⟨plan5003,valid5003,t5_1019choices,?_⟩
  exact check_of_frontier tree 0 t5_1019root t5_1019jobs t5_1019frontier t5_1019all
theorem t5_1020choices : plan5004.choices=[4,4,5,6,7].map (options 5 5) := by rfl


theorem t5_1020part0 : t5_1020jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1020frontier : t5_1020root.frontier 0=t5_1020jobs := by rfl
theorem t5_1020all : t5_1020jobs.all (Job.check tree)=true := by
  simp only [t5_1020jobs,List.all_append,List.all_nil,t5_1020part0,Bool.and_self]
theorem t5_1020checked : Checked tree [4,4,5,6,7] := by
  refine ⟨plan5004,valid5004,t5_1020choices,?_⟩
  exact check_of_frontier tree 0 t5_1020root t5_1020jobs t5_1020frontier t5_1020all
theorem t5_1021choices : plan5005.choices=[4,4,5,6,10].map (options 5 5) := by rfl


theorem t5_1021part0 : t5_1021jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1021frontier : t5_1021root.frontier 0=t5_1021jobs := by rfl
theorem t5_1021all : t5_1021jobs.all (Job.check tree)=true := by
  simp only [t5_1021jobs,List.all_append,List.all_nil,t5_1021part0,Bool.and_self]
theorem t5_1021checked : Checked tree [4,4,5,6,10] := by
  refine ⟨plan5005,valid5005,t5_1021choices,?_⟩
  exact check_of_frontier tree 0 t5_1021root t5_1021jobs t5_1021frontier t5_1021all
theorem t5_1022choices : plan5006.choices=[4,4,5,7,7].map (options 5 5) := by rfl


theorem t5_1022part0 : t5_1022jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1022frontier : t5_1022root.frontier 0=t5_1022jobs := by rfl
theorem t5_1022all : t5_1022jobs.all (Job.check tree)=true := by
  simp only [t5_1022jobs,List.all_append,List.all_nil,t5_1022part0,Bool.and_self]
theorem t5_1022checked : Checked tree [4,4,5,7,7] := by
  refine ⟨plan5006,valid5006,t5_1022choices,?_⟩
  exact check_of_frontier tree 0 t5_1022root t5_1022jobs t5_1022frontier t5_1022all
theorem t5_1023choices : plan5007.choices=[4,4,5,9,7].map (options 5 5) := by rfl


theorem t5_1023part0 : t5_1023jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1023frontier : t5_1023root.frontier 0=t5_1023jobs := by rfl
theorem t5_1023all : t5_1023jobs.all (Job.check tree)=true := by
  simp only [t5_1023jobs,List.all_append,List.all_nil,t5_1023part0,Bool.and_self]
theorem t5_1023checked : Checked tree [4,4,5,9,7] := by
  refine ⟨plan5007,valid5007,t5_1023choices,?_⟩
  exact check_of_frontier tree 0 t5_1023root t5_1023jobs t5_1023frontier t5_1023all
theorem t5_1024choices : plan5008.choices=[4,4,5,10,7].map (options 5 5) := by rfl


theorem t5_1024part0 : t5_1024jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1024frontier : t5_1024root.frontier 0=t5_1024jobs := by rfl
theorem t5_1024all : t5_1024jobs.all (Job.check tree)=true := by
  simp only [t5_1024jobs,List.all_append,List.all_nil,t5_1024part0,Bool.and_self]
theorem t5_1024checked : Checked tree [4,4,5,10,7] := by
  refine ⟨plan5008,valid5008,t5_1024choices,?_⟩
  exact check_of_frontier tree 0 t5_1024root t5_1024jobs t5_1024frontier t5_1024all
theorem t5_1025choices : plan5009.choices=[4,4,5,10,10].map (options 5 5) := by rfl


theorem t5_1025part0 : t5_1025jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1025frontier : t5_1025root.frontier 0=t5_1025jobs := by rfl
theorem t5_1025all : t5_1025jobs.all (Job.check tree)=true := by
  simp only [t5_1025jobs,List.all_append,List.all_nil,t5_1025part0,Bool.and_self]
theorem t5_1025checked : Checked tree [4,4,5,10,10] := by
  refine ⟨plan5009,valid5009,t5_1025choices,?_⟩
  exact check_of_frontier tree 0 t5_1025root t5_1025jobs t5_1025frontier t5_1025all
theorem t5_1026choices : plan5010.choices=[4,4,6,6,6].map (options 5 5) := by rfl


theorem t5_1026part0 : t5_1026jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1026frontier : t5_1026root.frontier 0=t5_1026jobs := by rfl
theorem t5_1026all : t5_1026jobs.all (Job.check tree)=true := by
  simp only [t5_1026jobs,List.all_append,List.all_nil,t5_1026part0,Bool.and_self]
theorem t5_1026checked : Checked tree [4,4,6,6,6] := by
  refine ⟨plan5010,valid5010,t5_1026choices,?_⟩
  exact check_of_frontier tree 0 t5_1026root t5_1026jobs t5_1026frontier t5_1026all
theorem t5_1027choices : plan5011.choices=[4,4,6,6,7].map (options 5 5) := by rfl


theorem t5_1027part0 : t5_1027jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1027frontier : t5_1027root.frontier 0=t5_1027jobs := by rfl
theorem t5_1027all : t5_1027jobs.all (Job.check tree)=true := by
  simp only [t5_1027jobs,List.all_append,List.all_nil,t5_1027part0,Bool.and_self]
theorem t5_1027checked : Checked tree [4,4,6,6,7] := by
  refine ⟨plan5011,valid5011,t5_1027choices,?_⟩
  exact check_of_frontier tree 0 t5_1027root t5_1027jobs t5_1027frontier t5_1027all
theorem t5_1028choices : plan5012.choices=[4,4,6,6,10].map (options 5 5) := by rfl


theorem t5_1028part0 : t5_1028jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1028frontier : t5_1028root.frontier 0=t5_1028jobs := by rfl
theorem t5_1028all : t5_1028jobs.all (Job.check tree)=true := by
  simp only [t5_1028jobs,List.all_append,List.all_nil,t5_1028part0,Bool.and_self]
theorem t5_1028checked : Checked tree [4,4,6,6,10] := by
  refine ⟨plan5012,valid5012,t5_1028choices,?_⟩
  exact check_of_frontier tree 0 t5_1028root t5_1028jobs t5_1028frontier t5_1028all
theorem t5_1029choices : plan5013.choices=[4,4,6,7,7].map (options 5 5) := by rfl


theorem t5_1029part0 : t5_1029jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1029frontier : t5_1029root.frontier 0=t5_1029jobs := by rfl
theorem t5_1029all : t5_1029jobs.all (Job.check tree)=true := by
  simp only [t5_1029jobs,List.all_append,List.all_nil,t5_1029part0,Bool.and_self]
theorem t5_1029checked : Checked tree [4,4,6,7,7] := by
  refine ⟨plan5013,valid5013,t5_1029choices,?_⟩
  exact check_of_frontier tree 0 t5_1029root t5_1029jobs t5_1029frontier t5_1029all
theorem t5_1030choices : plan5014.choices=[4,4,6,10,7].map (options 5 5) := by rfl


theorem t5_1030part0 : t5_1030jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1030frontier : t5_1030root.frontier 0=t5_1030jobs := by rfl
theorem t5_1030all : t5_1030jobs.all (Job.check tree)=true := by
  simp only [t5_1030jobs,List.all_append,List.all_nil,t5_1030part0,Bool.and_self]
theorem t5_1030checked : Checked tree [4,4,6,10,7] := by
  refine ⟨plan5014,valid5014,t5_1030choices,?_⟩
  exact check_of_frontier tree 0 t5_1030root t5_1030jobs t5_1030frontier t5_1030all
theorem t5_1031choices : plan5015.choices=[4,4,6,10,10].map (options 5 5) := by rfl


theorem t5_1031part0 : t5_1031jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1031frontier : t5_1031root.frontier 0=t5_1031jobs := by rfl
theorem t5_1031all : t5_1031jobs.all (Job.check tree)=true := by
  simp only [t5_1031jobs,List.all_append,List.all_nil,t5_1031part0,Bool.and_self]
theorem t5_1031checked : Checked tree [4,4,6,10,10] := by
  refine ⟨plan5015,valid5015,t5_1031choices,?_⟩
  exact check_of_frontier tree 0 t5_1031root t5_1031jobs t5_1031frontier t5_1031all
theorem t5_1032choices : plan5016.choices=[4,4,7,7,7].map (options 5 5) := by rfl


theorem t5_1032part0 : t5_1032jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1032frontier : t5_1032root.frontier 0=t5_1032jobs := by rfl
theorem t5_1032all : t5_1032jobs.all (Job.check tree)=true := by
  simp only [t5_1032jobs,List.all_append,List.all_nil,t5_1032part0,Bool.and_self]
theorem t5_1032checked : Checked tree [4,4,7,7,7] := by
  refine ⟨plan5016,valid5016,t5_1032choices,?_⟩
  exact check_of_frontier tree 0 t5_1032root t5_1032jobs t5_1032frontier t5_1032all
theorem t5_1033choices : plan4807.choices=[4,4,8,3,7].map (options 5 4) := by rfl


theorem t5_1033part0 : t5_1033jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1033frontier : t5_1033root.frontier 0=t5_1033jobs := by rfl
theorem t5_1033all : t5_1033jobs.all (Job.check tree)=true := by
  simp only [t5_1033jobs,List.all_append,List.all_nil,t5_1033part0,Bool.and_self]
theorem t5_1033checked : Checked tree [4,4,8,3,7] := by
  refine ⟨plan4807,valid4807,t5_1033choices,?_⟩
  exact check_of_frontier tree 0 t5_1033root t5_1033jobs t5_1033frontier t5_1033all
theorem t5_1034choices : plan5017.choices=[4,4,8,6,7].map (options 5 5) := by rfl


theorem t5_1034part0 : t5_1034jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1034frontier : t5_1034root.frontier 0=t5_1034jobs := by rfl
theorem t5_1034all : t5_1034jobs.all (Job.check tree)=true := by
  simp only [t5_1034jobs,List.all_append,List.all_nil,t5_1034part0,Bool.and_self]
theorem t5_1034checked : Checked tree [4,4,8,6,7] := by
  refine ⟨plan5017,valid5017,t5_1034choices,?_⟩
  exact check_of_frontier tree 0 t5_1034root t5_1034jobs t5_1034frontier t5_1034all
theorem t5_1035choices : plan5018.choices=[4,4,8,7,7].map (options 5 5) := by rfl


theorem t5_1035part0 : t5_1035jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1035frontier : t5_1035root.frontier 0=t5_1035jobs := by rfl
theorem t5_1035all : t5_1035jobs.all (Job.check tree)=true := by
  simp only [t5_1035jobs,List.all_append,List.all_nil,t5_1035part0,Bool.and_self]
theorem t5_1035checked : Checked tree [4,4,8,7,7] := by
  refine ⟨plan5018,valid5018,t5_1035choices,?_⟩
  exact check_of_frontier tree 0 t5_1035root t5_1035jobs t5_1035frontier t5_1035all
theorem t5_1036choices : plan5019.choices=[4,4,8,10,7].map (options 5 5) := by rfl


theorem t5_1036part0 : t5_1036jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1036frontier : t5_1036root.frontier 0=t5_1036jobs := by rfl
theorem t5_1036all : t5_1036jobs.all (Job.check tree)=true := by
  simp only [t5_1036jobs,List.all_append,List.all_nil,t5_1036part0,Bool.and_self]
theorem t5_1036checked : Checked tree [4,4,8,10,7] := by
  refine ⟨plan5019,valid5019,t5_1036choices,?_⟩
  exact check_of_frontier tree 0 t5_1036root t5_1036jobs t5_1036frontier t5_1036all
theorem t5_1037choices : plan4355.choices=[4,4,9,3,3].map (options 5 3) := by rfl


theorem t5_1037part0 : t5_1037jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1037frontier : t5_1037root.frontier 0=t5_1037jobs := by rfl
theorem t5_1037all : t5_1037jobs.all (Job.check tree)=true := by
  simp only [t5_1037jobs,List.all_append,List.all_nil,t5_1037part0,Bool.and_self]
theorem t5_1037checked : Checked tree [4,4,9,3,3] := by
  refine ⟨plan4355,valid4355,t5_1037choices,?_⟩
  exact check_of_frontier tree 0 t5_1037root t5_1037jobs t5_1037frontier t5_1037all
theorem t5_1038choices : plan4808.choices=[4,4,9,3,6].map (options 5 4) := by rfl


theorem t5_1038part0 : t5_1038jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1038frontier : t5_1038root.frontier 0=t5_1038jobs := by rfl
theorem t5_1038all : t5_1038jobs.all (Job.check tree)=true := by
  simp only [t5_1038jobs,List.all_append,List.all_nil,t5_1038part0,Bool.and_self]
theorem t5_1038checked : Checked tree [4,4,9,3,6] := by
  refine ⟨plan4808,valid4808,t5_1038choices,?_⟩
  exact check_of_frontier tree 0 t5_1038root t5_1038jobs t5_1038frontier t5_1038all
theorem t5_1039choices : plan4809.choices=[4,4,9,3,7].map (options 5 4) := by rfl


theorem t5_1039part0 : t5_1039jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1039frontier : t5_1039root.frontier 0=t5_1039jobs := by rfl
theorem t5_1039all : t5_1039jobs.all (Job.check tree)=true := by
  simp only [t5_1039jobs,List.all_append,List.all_nil,t5_1039part0,Bool.and_self]
theorem t5_1039checked : Checked tree [4,4,9,3,7] := by
  refine ⟨plan4809,valid4809,t5_1039choices,?_⟩
  exact check_of_frontier tree 0 t5_1039root t5_1039jobs t5_1039frontier t5_1039all
theorem t5_1040choices : plan4810.choices=[4,4,9,3,10].map (options 5 4) := by rfl


theorem t5_1040part0 : t5_1040jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1040frontier : t5_1040root.frontier 0=t5_1040jobs := by rfl
theorem t5_1040all : t5_1040jobs.all (Job.check tree)=true := by
  simp only [t5_1040jobs,List.all_append,List.all_nil,t5_1040part0,Bool.and_self]
theorem t5_1040checked : Checked tree [4,4,9,3,10] := by
  refine ⟨plan4810,valid4810,t5_1040choices,?_⟩
  exact check_of_frontier tree 0 t5_1040root t5_1040jobs t5_1040frontier t5_1040all
theorem t5_1041choices : plan5020.choices=[4,4,9,6,6].map (options 5 5) := by rfl


theorem t5_1041part0 : t5_1041jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1041frontier : t5_1041root.frontier 0=t5_1041jobs := by rfl
theorem t5_1041all : t5_1041jobs.all (Job.check tree)=true := by
  simp only [t5_1041jobs,List.all_append,List.all_nil,t5_1041part0,Bool.and_self]
theorem t5_1041checked : Checked tree [4,4,9,6,6] := by
  refine ⟨plan5020,valid5020,t5_1041choices,?_⟩
  exact check_of_frontier tree 0 t5_1041root t5_1041jobs t5_1041frontier t5_1041all
theorem t5_1042choices : plan5021.choices=[4,4,9,6,7].map (options 5 5) := by rfl


theorem t5_1042part0 : t5_1042jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1042frontier : t5_1042root.frontier 0=t5_1042jobs := by rfl
theorem t5_1042all : t5_1042jobs.all (Job.check tree)=true := by
  simp only [t5_1042jobs,List.all_append,List.all_nil,t5_1042part0,Bool.and_self]
theorem t5_1042checked : Checked tree [4,4,9,6,7] := by
  refine ⟨plan5021,valid5021,t5_1042choices,?_⟩
  exact check_of_frontier tree 0 t5_1042root t5_1042jobs t5_1042frontier t5_1042all
theorem t5_1043choices : plan5022.choices=[4,4,9,6,10].map (options 5 5) := by rfl


theorem t5_1043part0 : t5_1043jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1043frontier : t5_1043root.frontier 0=t5_1043jobs := by rfl
theorem t5_1043all : t5_1043jobs.all (Job.check tree)=true := by
  simp only [t5_1043jobs,List.all_append,List.all_nil,t5_1043part0,Bool.and_self]
theorem t5_1043checked : Checked tree [4,4,9,6,10] := by
  refine ⟨plan5022,valid5022,t5_1043choices,?_⟩
  exact check_of_frontier tree 0 t5_1043root t5_1043jobs t5_1043frontier t5_1043all
theorem t5_1044choices : plan5023.choices=[4,4,9,7,7].map (options 5 5) := by rfl


theorem t5_1044part0 : t5_1044jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1044frontier : t5_1044root.frontier 0=t5_1044jobs := by rfl
theorem t5_1044all : t5_1044jobs.all (Job.check tree)=true := by
  simp only [t5_1044jobs,List.all_append,List.all_nil,t5_1044part0,Bool.and_self]
theorem t5_1044checked : Checked tree [4,4,9,7,7] := by
  refine ⟨plan5023,valid5023,t5_1044choices,?_⟩
  exact check_of_frontier tree 0 t5_1044root t5_1044jobs t5_1044frontier t5_1044all
theorem t5_1045choices : plan5024.choices=[4,4,9,9,7].map (options 5 5) := by rfl


theorem t5_1045part0 : t5_1045jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1045frontier : t5_1045root.frontier 0=t5_1045jobs := by rfl
theorem t5_1045all : t5_1045jobs.all (Job.check tree)=true := by
  simp only [t5_1045jobs,List.all_append,List.all_nil,t5_1045part0,Bool.and_self]
theorem t5_1045checked : Checked tree [4,4,9,9,7] := by
  refine ⟨plan5024,valid5024,t5_1045choices,?_⟩
  exact check_of_frontier tree 0 t5_1045root t5_1045jobs t5_1045frontier t5_1045all
theorem t5_1046choices : plan5025.choices=[4,4,9,10,7].map (options 5 5) := by rfl


theorem t5_1046part0 : t5_1046jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1046frontier : t5_1046root.frontier 0=t5_1046jobs := by rfl
theorem t5_1046all : t5_1046jobs.all (Job.check tree)=true := by
  simp only [t5_1046jobs,List.all_append,List.all_nil,t5_1046part0,Bool.and_self]
theorem t5_1046checked : Checked tree [4,4,9,10,7] := by
  refine ⟨plan5025,valid5025,t5_1046choices,?_⟩
  exact check_of_frontier tree 0 t5_1046root t5_1046jobs t5_1046frontier t5_1046all
theorem t5_1047choices : plan5026.choices=[4,4,9,10,10].map (options 5 5) := by rfl


theorem t5_1047part0 : t5_1047jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1047frontier : t5_1047root.frontier 0=t5_1047jobs := by rfl
theorem t5_1047all : t5_1047jobs.all (Job.check tree)=true := by
  simp only [t5_1047jobs,List.all_append,List.all_nil,t5_1047part0,Bool.and_self]
theorem t5_1047checked : Checked tree [4,4,9,10,10] := by
  refine ⟨plan5026,valid5026,t5_1047choices,?_⟩
  exact check_of_frontier tree 0 t5_1047root t5_1047jobs t5_1047frontier t5_1047all
theorem t5_1048choices : plan5027.choices=[4,4,10,7,7].map (options 5 5) := by rfl


theorem t5_1048part0 : t5_1048jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1048frontier : t5_1048root.frontier 0=t5_1048jobs := by rfl
theorem t5_1048all : t5_1048jobs.all (Job.check tree)=true := by
  simp only [t5_1048jobs,List.all_append,List.all_nil,t5_1048part0,Bool.and_self]
theorem t5_1048checked : Checked tree [4,4,10,7,7] := by
  refine ⟨plan5027,valid5027,t5_1048choices,?_⟩
  exact check_of_frontier tree 0 t5_1048root t5_1048jobs t5_1048frontier t5_1048all
theorem t5_1049choices : plan5028.choices=[4,4,10,10,7].map (options 5 5) := by rfl


theorem t5_1049part0 : t5_1049jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1049frontier : t5_1049root.frontier 0=t5_1049jobs := by rfl
theorem t5_1049all : t5_1049jobs.all (Job.check tree)=true := by
  simp only [t5_1049jobs,List.all_append,List.all_nil,t5_1049part0,Bool.and_self]
theorem t5_1049checked : Checked tree [4,4,10,10,7] := by
  refine ⟨plan5028,valid5028,t5_1049choices,?_⟩
  exact check_of_frontier tree 0 t5_1049root t5_1049jobs t5_1049frontier t5_1049all
theorem t5_1050choices : plan5029.choices=[4,4,10,10,10].map (options 5 5) := by rfl


theorem t5_1050part0 : t5_1050jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1050frontier : t5_1050root.frontier 0=t5_1050jobs := by rfl
theorem t5_1050all : t5_1050jobs.all (Job.check tree)=true := by
  simp only [t5_1050jobs,List.all_append,List.all_nil,t5_1050part0,Bool.and_self]
theorem t5_1050checked : Checked tree [4,4,10,10,10] := by
  refine ⟨plan5029,valid5029,t5_1050choices,?_⟩
  exact check_of_frontier tree 0 t5_1050root t5_1050jobs t5_1050frontier t5_1050all
theorem t5_1051choices : plan3967.choices=[4,5,3,3,3].map (options 5 2) := by rfl


theorem t5_1051part0 : t5_1051jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1051frontier : t5_1051root.frontier 0=t5_1051jobs := by rfl
theorem t5_1051all : t5_1051jobs.all (Job.check tree)=true := by
  simp only [t5_1051jobs,List.all_append,List.all_nil,t5_1051part0,Bool.and_self]
theorem t5_1051checked : Checked tree [4,5,3,3,3] := by
  refine ⟨plan3967,valid3967,t5_1051choices,?_⟩
  exact check_of_frontier tree 0 t5_1051root t5_1051jobs t5_1051frontier t5_1051all
theorem t5_1052choices : plan4356.choices=[4,5,3,3,6].map (options 5 3) := by rfl


theorem t5_1052part0 : t5_1052jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1052frontier : t5_1052root.frontier 0=t5_1052jobs := by rfl
theorem t5_1052all : t5_1052jobs.all (Job.check tree)=true := by
  simp only [t5_1052jobs,List.all_append,List.all_nil,t5_1052part0,Bool.and_self]
theorem t5_1052checked : Checked tree [4,5,3,3,6] := by
  refine ⟨plan4356,valid4356,t5_1052choices,?_⟩
  exact check_of_frontier tree 0 t5_1052root t5_1052jobs t5_1052frontier t5_1052all
theorem t5_1053choices : plan4357.choices=[4,5,3,3,7].map (options 5 3) := by rfl


theorem t5_1053part0 : t5_1053jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1053frontier : t5_1053root.frontier 0=t5_1053jobs := by rfl
theorem t5_1053all : t5_1053jobs.all (Job.check tree)=true := by
  simp only [t5_1053jobs,List.all_append,List.all_nil,t5_1053part0,Bool.and_self]
theorem t5_1053checked : Checked tree [4,5,3,3,7] := by
  refine ⟨plan4357,valid4357,t5_1053choices,?_⟩
  exact check_of_frontier tree 0 t5_1053root t5_1053jobs t5_1053frontier t5_1053all
theorem t5_1054choices : plan4358.choices=[4,5,3,3,10].map (options 5 3) := by rfl


theorem t5_1054part0 : t5_1054jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1054frontier : t5_1054root.frontier 0=t5_1054jobs := by rfl
theorem t5_1054all : t5_1054jobs.all (Job.check tree)=true := by
  simp only [t5_1054jobs,List.all_append,List.all_nil,t5_1054part0,Bool.and_self]
theorem t5_1054checked : Checked tree [4,5,3,3,10] := by
  refine ⟨plan4358,valid4358,t5_1054choices,?_⟩
  exact check_of_frontier tree 0 t5_1054root t5_1054jobs t5_1054frontier t5_1054all
theorem t5_1055choices : plan4811.choices=[4,5,3,6,6].map (options 5 4) := by rfl


theorem t5_1055part0 : t5_1055jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1055frontier : t5_1055root.frontier 0=t5_1055jobs := by rfl
theorem t5_1055all : t5_1055jobs.all (Job.check tree)=true := by
  simp only [t5_1055jobs,List.all_append,List.all_nil,t5_1055part0,Bool.and_self]
theorem t5_1055checked : Checked tree [4,5,3,6,6] := by
  refine ⟨plan4811,valid4811,t5_1055choices,?_⟩
  exact check_of_frontier tree 0 t5_1055root t5_1055jobs t5_1055frontier t5_1055all
theorem t5_1056choices : plan4812.choices=[4,5,3,6,7].map (options 5 4) := by rfl


theorem t5_1056part0 : t5_1056jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1056frontier : t5_1056root.frontier 0=t5_1056jobs := by rfl
theorem t5_1056all : t5_1056jobs.all (Job.check tree)=true := by
  simp only [t5_1056jobs,List.all_append,List.all_nil,t5_1056part0,Bool.and_self]
theorem t5_1056checked : Checked tree [4,5,3,6,7] := by
  refine ⟨plan4812,valid4812,t5_1056choices,?_⟩
  exact check_of_frontier tree 0 t5_1056root t5_1056jobs t5_1056frontier t5_1056all
theorem t5_1057choices : plan4813.choices=[4,5,3,6,10].map (options 5 4) := by rfl


theorem t5_1057part0 : t5_1057jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1057frontier : t5_1057root.frontier 0=t5_1057jobs := by rfl
theorem t5_1057all : t5_1057jobs.all (Job.check tree)=true := by
  simp only [t5_1057jobs,List.all_append,List.all_nil,t5_1057part0,Bool.and_self]
theorem t5_1057checked : Checked tree [4,5,3,6,10] := by
  refine ⟨plan4813,valid4813,t5_1057choices,?_⟩
  exact check_of_frontier tree 0 t5_1057root t5_1057jobs t5_1057frontier t5_1057all
theorem t5_1058choices : plan4814.choices=[4,5,3,7,7].map (options 5 4) := by rfl


theorem t5_1058part0 : t5_1058jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1058frontier : t5_1058root.frontier 0=t5_1058jobs := by rfl
theorem t5_1058all : t5_1058jobs.all (Job.check tree)=true := by
  simp only [t5_1058jobs,List.all_append,List.all_nil,t5_1058part0,Bool.and_self]
theorem t5_1058checked : Checked tree [4,5,3,7,7] := by
  refine ⟨plan4814,valid4814,t5_1058choices,?_⟩
  exact check_of_frontier tree 0 t5_1058root t5_1058jobs t5_1058frontier t5_1058all
theorem t5_1059choices : plan4815.choices=[4,5,3,10,7].map (options 5 4) := by rfl


theorem t5_1059part0 : t5_1059jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1059frontier : t5_1059root.frontier 0=t5_1059jobs := by rfl
theorem t5_1059all : t5_1059jobs.all (Job.check tree)=true := by
  simp only [t5_1059jobs,List.all_append,List.all_nil,t5_1059part0,Bool.and_self]
theorem t5_1059checked : Checked tree [4,5,3,10,7] := by
  refine ⟨plan4815,valid4815,t5_1059choices,?_⟩
  exact check_of_frontier tree 0 t5_1059root t5_1059jobs t5_1059frontier t5_1059all
theorem t5_1060choices : plan4816.choices=[4,5,3,10,10].map (options 5 4) := by rfl


theorem t5_1060part0 : t5_1060jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1060frontier : t5_1060root.frontier 0=t5_1060jobs := by rfl
theorem t5_1060all : t5_1060jobs.all (Job.check tree)=true := by
  simp only [t5_1060jobs,List.all_append,List.all_nil,t5_1060part0,Bool.and_self]
theorem t5_1060checked : Checked tree [4,5,3,10,10] := by
  refine ⟨plan4816,valid4816,t5_1060choices,?_⟩
  exact check_of_frontier tree 0 t5_1060root t5_1060jobs t5_1060frontier t5_1060all
theorem t5_1061choices : plan4359.choices=[4,5,5,3,3].map (options 5 3) := by rfl


theorem t5_1061part0 : t5_1061jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1061frontier : t5_1061root.frontier 0=t5_1061jobs := by rfl
theorem t5_1061all : t5_1061jobs.all (Job.check tree)=true := by
  simp only [t5_1061jobs,List.all_append,List.all_nil,t5_1061part0,Bool.and_self]
theorem t5_1061checked : Checked tree [4,5,5,3,3] := by
  refine ⟨plan4359,valid4359,t5_1061choices,?_⟩
  exact check_of_frontier tree 0 t5_1061root t5_1061jobs t5_1061frontier t5_1061all
theorem t5_1062choices : plan4817.choices=[4,5,5,3,6].map (options 5 4) := by rfl


theorem t5_1062part0 : t5_1062jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1062frontier : t5_1062root.frontier 0=t5_1062jobs := by rfl
theorem t5_1062all : t5_1062jobs.all (Job.check tree)=true := by
  simp only [t5_1062jobs,List.all_append,List.all_nil,t5_1062part0,Bool.and_self]
theorem t5_1062checked : Checked tree [4,5,5,3,6] := by
  refine ⟨plan4817,valid4817,t5_1062choices,?_⟩
  exact check_of_frontier tree 0 t5_1062root t5_1062jobs t5_1062frontier t5_1062all
theorem t5_1063choices : plan4818.choices=[4,5,5,3,7].map (options 5 4) := by rfl


theorem t5_1063part0 : t5_1063jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1063frontier : t5_1063root.frontier 0=t5_1063jobs := by rfl
theorem t5_1063all : t5_1063jobs.all (Job.check tree)=true := by
  simp only [t5_1063jobs,List.all_append,List.all_nil,t5_1063part0,Bool.and_self]
theorem t5_1063checked : Checked tree [4,5,5,3,7] := by
  refine ⟨plan4818,valid4818,t5_1063choices,?_⟩
  exact check_of_frontier tree 0 t5_1063root t5_1063jobs t5_1063frontier t5_1063all
theorem t5_1064choices : plan4819.choices=[4,5,5,3,10].map (options 5 4) := by rfl


theorem t5_1064part0 : t5_1064jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1064frontier : t5_1064root.frontier 0=t5_1064jobs := by rfl
theorem t5_1064all : t5_1064jobs.all (Job.check tree)=true := by
  simp only [t5_1064jobs,List.all_append,List.all_nil,t5_1064part0,Bool.and_self]
theorem t5_1064checked : Checked tree [4,5,5,3,10] := by
  refine ⟨plan4819,valid4819,t5_1064choices,?_⟩
  exact check_of_frontier tree 0 t5_1064root t5_1064jobs t5_1064frontier t5_1064all
theorem t5_1065choices : plan4820.choices=[4,5,5,5,3].map (options 5 4) := by rfl


theorem t5_1065part0 : t5_1065jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1065frontier : t5_1065root.frontier 0=t5_1065jobs := by rfl
theorem t5_1065all : t5_1065jobs.all (Job.check tree)=true := by
  simp only [t5_1065jobs,List.all_append,List.all_nil,t5_1065part0,Bool.and_self]
theorem t5_1065checked : Checked tree [4,5,5,5,3] := by
  refine ⟨plan4820,valid4820,t5_1065choices,?_⟩
  exact check_of_frontier tree 0 t5_1065root t5_1065jobs t5_1065frontier t5_1065all
theorem t5_1066choices : plan5030.choices=[4,5,5,5,6].map (options 5 5) := by rfl


theorem t5_1066part0 : t5_1066jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1066frontier : t5_1066root.frontier 0=t5_1066jobs := by rfl
theorem t5_1066all : t5_1066jobs.all (Job.check tree)=true := by
  simp only [t5_1066jobs,List.all_append,List.all_nil,t5_1066part0,Bool.and_self]
theorem t5_1066checked : Checked tree [4,5,5,5,6] := by
  refine ⟨plan5030,valid5030,t5_1066choices,?_⟩
  exact check_of_frontier tree 0 t5_1066root t5_1066jobs t5_1066frontier t5_1066all
theorem t5_1067choices : plan5031.choices=[4,5,5,5,7].map (options 5 5) := by rfl


theorem t5_1067part0 : t5_1067jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1067frontier : t5_1067root.frontier 0=t5_1067jobs := by rfl
theorem t5_1067all : t5_1067jobs.all (Job.check tree)=true := by
  simp only [t5_1067jobs,List.all_append,List.all_nil,t5_1067part0,Bool.and_self]
theorem t5_1067checked : Checked tree [4,5,5,5,7] := by
  refine ⟨plan5031,valid5031,t5_1067choices,?_⟩
  exact check_of_frontier tree 0 t5_1067root t5_1067jobs t5_1067frontier t5_1067all
theorem t5_1068choices : plan5032.choices=[4,5,5,5,10].map (options 5 5) := by rfl


theorem t5_1068part0 : t5_1068jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1068frontier : t5_1068root.frontier 0=t5_1068jobs := by rfl
theorem t5_1068all : t5_1068jobs.all (Job.check tree)=true := by
  simp only [t5_1068jobs,List.all_append,List.all_nil,t5_1068part0,Bool.and_self]
theorem t5_1068checked : Checked tree [4,5,5,5,10] := by
  refine ⟨plan5032,valid5032,t5_1068choices,?_⟩
  exact check_of_frontier tree 0 t5_1068root t5_1068jobs t5_1068frontier t5_1068all
theorem t5_1069choices : plan5033.choices=[4,5,5,6,6].map (options 5 5) := by rfl


theorem t5_1069part0 : t5_1069jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1069frontier : t5_1069root.frontier 0=t5_1069jobs := by rfl
theorem t5_1069all : t5_1069jobs.all (Job.check tree)=true := by
  simp only [t5_1069jobs,List.all_append,List.all_nil,t5_1069part0,Bool.and_self]
theorem t5_1069checked : Checked tree [4,5,5,6,6] := by
  refine ⟨plan5033,valid5033,t5_1069choices,?_⟩
  exact check_of_frontier tree 0 t5_1069root t5_1069jobs t5_1069frontier t5_1069all
theorem t5_1070choices : plan5034.choices=[4,5,5,6,7].map (options 5 5) := by rfl


theorem t5_1070part0 : t5_1070jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1070frontier : t5_1070root.frontier 0=t5_1070jobs := by rfl
theorem t5_1070all : t5_1070jobs.all (Job.check tree)=true := by
  simp only [t5_1070jobs,List.all_append,List.all_nil,t5_1070part0,Bool.and_self]
theorem t5_1070checked : Checked tree [4,5,5,6,7] := by
  refine ⟨plan5034,valid5034,t5_1070choices,?_⟩
  exact check_of_frontier tree 0 t5_1070root t5_1070jobs t5_1070frontier t5_1070all
theorem t5_1071choices : plan5035.choices=[4,5,5,6,10].map (options 5 5) := by rfl


theorem t5_1071part0 : t5_1071jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1071frontier : t5_1071root.frontier 0=t5_1071jobs := by rfl
theorem t5_1071all : t5_1071jobs.all (Job.check tree)=true := by
  simp only [t5_1071jobs,List.all_append,List.all_nil,t5_1071part0,Bool.and_self]
theorem t5_1071checked : Checked tree [4,5,5,6,10] := by
  refine ⟨plan5035,valid5035,t5_1071choices,?_⟩
  exact check_of_frontier tree 0 t5_1071root t5_1071jobs t5_1071frontier t5_1071all
theorem t5_1072choices : plan5036.choices=[4,5,5,7,7].map (options 5 5) := by rfl


theorem t5_1072part0 : t5_1072jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1072frontier : t5_1072root.frontier 0=t5_1072jobs := by rfl
theorem t5_1072all : t5_1072jobs.all (Job.check tree)=true := by
  simp only [t5_1072jobs,List.all_append,List.all_nil,t5_1072part0,Bool.and_self]
theorem t5_1072checked : Checked tree [4,5,5,7,7] := by
  refine ⟨plan5036,valid5036,t5_1072choices,?_⟩
  exact check_of_frontier tree 0 t5_1072root t5_1072jobs t5_1072frontier t5_1072all
theorem t5_1073choices : plan4821.choices=[4,5,5,9,3].map (options 5 4) := by rfl


theorem t5_1073part0 : t5_1073jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1073frontier : t5_1073root.frontier 0=t5_1073jobs := by rfl
theorem t5_1073all : t5_1073jobs.all (Job.check tree)=true := by
  simp only [t5_1073jobs,List.all_append,List.all_nil,t5_1073part0,Bool.and_self]
theorem t5_1073checked : Checked tree [4,5,5,9,3] := by
  refine ⟨plan4821,valid4821,t5_1073choices,?_⟩
  exact check_of_frontier tree 0 t5_1073root t5_1073jobs t5_1073frontier t5_1073all
theorem t5_1074choices : plan5037.choices=[4,5,5,9,6].map (options 5 5) := by rfl


theorem t5_1074part0 : t5_1074jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1074frontier : t5_1074root.frontier 0=t5_1074jobs := by rfl
theorem t5_1074all : t5_1074jobs.all (Job.check tree)=true := by
  simp only [t5_1074jobs,List.all_append,List.all_nil,t5_1074part0,Bool.and_self]
theorem t5_1074checked : Checked tree [4,5,5,9,6] := by
  refine ⟨plan5037,valid5037,t5_1074choices,?_⟩
  exact check_of_frontier tree 0 t5_1074root t5_1074jobs t5_1074frontier t5_1074all
theorem t5_1075choices : plan5038.choices=[4,5,5,9,7].map (options 5 5) := by rfl


theorem t5_1075part0 : t5_1075jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1075frontier : t5_1075root.frontier 0=t5_1075jobs := by rfl
theorem t5_1075all : t5_1075jobs.all (Job.check tree)=true := by
  simp only [t5_1075jobs,List.all_append,List.all_nil,t5_1075part0,Bool.and_self]
theorem t5_1075checked : Checked tree [4,5,5,9,7] := by
  refine ⟨plan5038,valid5038,t5_1075choices,?_⟩
  exact check_of_frontier tree 0 t5_1075root t5_1075jobs t5_1075frontier t5_1075all
theorem t5_1076choices : plan5039.choices=[4,5,5,9,10].map (options 5 5) := by rfl


theorem t5_1076part0 : t5_1076jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1076frontier : t5_1076root.frontier 0=t5_1076jobs := by rfl
theorem t5_1076all : t5_1076jobs.all (Job.check tree)=true := by
  simp only [t5_1076jobs,List.all_append,List.all_nil,t5_1076part0,Bool.and_self]
theorem t5_1076checked : Checked tree [4,5,5,9,10] := by
  refine ⟨plan5039,valid5039,t5_1076choices,?_⟩
  exact check_of_frontier tree 0 t5_1076root t5_1076jobs t5_1076frontier t5_1076all
theorem t5_1077choices : plan5040.choices=[4,5,5,10,7].map (options 5 5) := by rfl


theorem t5_1077part0 : t5_1077jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1077frontier : t5_1077root.frontier 0=t5_1077jobs := by rfl
theorem t5_1077all : t5_1077jobs.all (Job.check tree)=true := by
  simp only [t5_1077jobs,List.all_append,List.all_nil,t5_1077part0,Bool.and_self]
theorem t5_1077checked : Checked tree [4,5,5,10,7] := by
  refine ⟨plan5040,valid5040,t5_1077choices,?_⟩
  exact check_of_frontier tree 0 t5_1077root t5_1077jobs t5_1077frontier t5_1077all
theorem t5_1078choices : plan5041.choices=[4,5,5,10,10].map (options 5 5) := by rfl


theorem t5_1078part0 : t5_1078jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1078frontier : t5_1078root.frontier 0=t5_1078jobs := by rfl
theorem t5_1078all : t5_1078jobs.all (Job.check tree)=true := by
  simp only [t5_1078jobs,List.all_append,List.all_nil,t5_1078part0,Bool.and_self]
theorem t5_1078checked : Checked tree [4,5,5,10,10] := by
  refine ⟨plan5041,valid5041,t5_1078choices,?_⟩
  exact check_of_frontier tree 0 t5_1078root t5_1078jobs t5_1078frontier t5_1078all
theorem t5_1079choices : plan5042.choices=[4,5,6,6,6].map (options 5 5) := by rfl


theorem t5_1079part0 : t5_1079jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1079frontier : t5_1079root.frontier 0=t5_1079jobs := by rfl
theorem t5_1079all : t5_1079jobs.all (Job.check tree)=true := by
  simp only [t5_1079jobs,List.all_append,List.all_nil,t5_1079part0,Bool.and_self]
theorem t5_1079checked : Checked tree [4,5,6,6,6] := by
  refine ⟨plan5042,valid5042,t5_1079choices,?_⟩
  exact check_of_frontier tree 0 t5_1079root t5_1079jobs t5_1079frontier t5_1079all
theorem t5_1080choices : plan5043.choices=[4,5,6,6,7].map (options 5 5) := by rfl


theorem t5_1080part0 : t5_1080jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1080frontier : t5_1080root.frontier 0=t5_1080jobs := by rfl
theorem t5_1080all : t5_1080jobs.all (Job.check tree)=true := by
  simp only [t5_1080jobs,List.all_append,List.all_nil,t5_1080part0,Bool.and_self]
theorem t5_1080checked : Checked tree [4,5,6,6,7] := by
  refine ⟨plan5043,valid5043,t5_1080choices,?_⟩
  exact check_of_frontier tree 0 t5_1080root t5_1080jobs t5_1080frontier t5_1080all
theorem t5_1081choices : plan5044.choices=[4,5,6,6,10].map (options 5 5) := by rfl


theorem t5_1081part0 : t5_1081jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1081frontier : t5_1081root.frontier 0=t5_1081jobs := by rfl
theorem t5_1081all : t5_1081jobs.all (Job.check tree)=true := by
  simp only [t5_1081jobs,List.all_append,List.all_nil,t5_1081part0,Bool.and_self]
theorem t5_1081checked : Checked tree [4,5,6,6,10] := by
  refine ⟨plan5044,valid5044,t5_1081choices,?_⟩
  exact check_of_frontier tree 0 t5_1081root t5_1081jobs t5_1081frontier t5_1081all
theorem t5_1082choices : plan5045.choices=[4,5,6,7,7].map (options 5 5) := by rfl


theorem t5_1082part0 : t5_1082jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1082frontier : t5_1082root.frontier 0=t5_1082jobs := by rfl
theorem t5_1082all : t5_1082jobs.all (Job.check tree)=true := by
  simp only [t5_1082jobs,List.all_append,List.all_nil,t5_1082part0,Bool.and_self]
theorem t5_1082checked : Checked tree [4,5,6,7,7] := by
  refine ⟨plan5045,valid5045,t5_1082choices,?_⟩
  exact check_of_frontier tree 0 t5_1082root t5_1082jobs t5_1082frontier t5_1082all
theorem t5_1083choices : plan5046.choices=[4,5,6,10,7].map (options 5 5) := by rfl


theorem t5_1083part0 : t5_1083jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1083frontier : t5_1083root.frontier 0=t5_1083jobs := by rfl
theorem t5_1083all : t5_1083jobs.all (Job.check tree)=true := by
  simp only [t5_1083jobs,List.all_append,List.all_nil,t5_1083part0,Bool.and_self]
theorem t5_1083checked : Checked tree [4,5,6,10,7] := by
  refine ⟨plan5046,valid5046,t5_1083choices,?_⟩
  exact check_of_frontier tree 0 t5_1083root t5_1083jobs t5_1083frontier t5_1083all
theorem t5_1084choices : plan5047.choices=[4,5,6,10,10].map (options 5 5) := by rfl


theorem t5_1084part0 : t5_1084jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1084frontier : t5_1084root.frontier 0=t5_1084jobs := by rfl
theorem t5_1084all : t5_1084jobs.all (Job.check tree)=true := by
  simp only [t5_1084jobs,List.all_append,List.all_nil,t5_1084part0,Bool.and_self]
theorem t5_1084checked : Checked tree [4,5,6,10,10] := by
  refine ⟨plan5047,valid5047,t5_1084choices,?_⟩
  exact check_of_frontier tree 0 t5_1084root t5_1084jobs t5_1084frontier t5_1084all
theorem t5_1085choices : plan5048.choices=[4,5,7,7,7].map (options 5 5) := by rfl


theorem t5_1085part0 : t5_1085jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1085frontier : t5_1085root.frontier 0=t5_1085jobs := by rfl
theorem t5_1085all : t5_1085jobs.all (Job.check tree)=true := by
  simp only [t5_1085jobs,List.all_append,List.all_nil,t5_1085part0,Bool.and_self]
theorem t5_1085checked : Checked tree [4,5,7,7,7] := by
  refine ⟨plan5048,valid5048,t5_1085choices,?_⟩
  exact check_of_frontier tree 0 t5_1085root t5_1085jobs t5_1085frontier t5_1085all
theorem t5_1086choices : plan4360.choices=[4,5,9,3,3].map (options 5 3) := by rfl


theorem t5_1086part0 : t5_1086jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1086frontier : t5_1086root.frontier 0=t5_1086jobs := by rfl
theorem t5_1086all : t5_1086jobs.all (Job.check tree)=true := by
  simp only [t5_1086jobs,List.all_append,List.all_nil,t5_1086part0,Bool.and_self]
theorem t5_1086checked : Checked tree [4,5,9,3,3] := by
  refine ⟨plan4360,valid4360,t5_1086choices,?_⟩
  exact check_of_frontier tree 0 t5_1086root t5_1086jobs t5_1086frontier t5_1086all
theorem t5_1087choices : plan4822.choices=[4,5,9,3,6].map (options 5 4) := by rfl


theorem t5_1087part0 : t5_1087jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1087frontier : t5_1087root.frontier 0=t5_1087jobs := by rfl
theorem t5_1087all : t5_1087jobs.all (Job.check tree)=true := by
  simp only [t5_1087jobs,List.all_append,List.all_nil,t5_1087part0,Bool.and_self]
theorem t5_1087checked : Checked tree [4,5,9,3,6] := by
  refine ⟨plan4822,valid4822,t5_1087choices,?_⟩
  exact check_of_frontier tree 0 t5_1087root t5_1087jobs t5_1087frontier t5_1087all
theorem t5_1088choices : plan4823.choices=[4,5,9,3,7].map (options 5 4) := by rfl


theorem t5_1088part0 : t5_1088jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1088frontier : t5_1088root.frontier 0=t5_1088jobs := by rfl
theorem t5_1088all : t5_1088jobs.all (Job.check tree)=true := by
  simp only [t5_1088jobs,List.all_append,List.all_nil,t5_1088part0,Bool.and_self]
theorem t5_1088checked : Checked tree [4,5,9,3,7] := by
  refine ⟨plan4823,valid4823,t5_1088choices,?_⟩
  exact check_of_frontier tree 0 t5_1088root t5_1088jobs t5_1088frontier t5_1088all
theorem t5_1089choices : plan4824.choices=[4,5,9,3,10].map (options 5 4) := by rfl


theorem t5_1089part0 : t5_1089jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1089frontier : t5_1089root.frontier 0=t5_1089jobs := by rfl
theorem t5_1089all : t5_1089jobs.all (Job.check tree)=true := by
  simp only [t5_1089jobs,List.all_append,List.all_nil,t5_1089part0,Bool.and_self]
theorem t5_1089checked : Checked tree [4,5,9,3,10] := by
  refine ⟨plan4824,valid4824,t5_1089choices,?_⟩
  exact check_of_frontier tree 0 t5_1089root t5_1089jobs t5_1089frontier t5_1089all
theorem t5_1090choices : plan5049.choices=[4,5,9,6,6].map (options 5 5) := by rfl


theorem t5_1090part0 : t5_1090jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1090frontier : t5_1090root.frontier 0=t5_1090jobs := by rfl
theorem t5_1090all : t5_1090jobs.all (Job.check tree)=true := by
  simp only [t5_1090jobs,List.all_append,List.all_nil,t5_1090part0,Bool.and_self]
theorem t5_1090checked : Checked tree [4,5,9,6,6] := by
  refine ⟨plan5049,valid5049,t5_1090choices,?_⟩
  exact check_of_frontier tree 0 t5_1090root t5_1090jobs t5_1090frontier t5_1090all
theorem t5_1091choices : plan5050.choices=[4,5,9,6,7].map (options 5 5) := by rfl


theorem t5_1091part0 : t5_1091jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1091frontier : t5_1091root.frontier 0=t5_1091jobs := by rfl
theorem t5_1091all : t5_1091jobs.all (Job.check tree)=true := by
  simp only [t5_1091jobs,List.all_append,List.all_nil,t5_1091part0,Bool.and_self]
theorem t5_1091checked : Checked tree [4,5,9,6,7] := by
  refine ⟨plan5050,valid5050,t5_1091choices,?_⟩
  exact check_of_frontier tree 0 t5_1091root t5_1091jobs t5_1091frontier t5_1091all
theorem t5_1092choices : plan5051.choices=[4,5,9,6,10].map (options 5 5) := by rfl


theorem t5_1092part0 : t5_1092jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1092frontier : t5_1092root.frontier 0=t5_1092jobs := by rfl
theorem t5_1092all : t5_1092jobs.all (Job.check tree)=true := by
  simp only [t5_1092jobs,List.all_append,List.all_nil,t5_1092part0,Bool.and_self]
theorem t5_1092checked : Checked tree [4,5,9,6,10] := by
  refine ⟨plan5051,valid5051,t5_1092choices,?_⟩
  exact check_of_frontier tree 0 t5_1092root t5_1092jobs t5_1092frontier t5_1092all
theorem t5_1093choices : plan5052.choices=[4,5,9,7,7].map (options 5 5) := by rfl


theorem t5_1093part0 : t5_1093jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1093frontier : t5_1093root.frontier 0=t5_1093jobs := by rfl
theorem t5_1093all : t5_1093jobs.all (Job.check tree)=true := by
  simp only [t5_1093jobs,List.all_append,List.all_nil,t5_1093part0,Bool.and_self]
theorem t5_1093checked : Checked tree [4,5,9,7,7] := by
  refine ⟨plan5052,valid5052,t5_1093choices,?_⟩
  exact check_of_frontier tree 0 t5_1093root t5_1093jobs t5_1093frontier t5_1093all
theorem t5_1094choices : plan4825.choices=[4,5,9,9,3].map (options 5 4) := by rfl


theorem t5_1094part0 : t5_1094jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1094frontier : t5_1094root.frontier 0=t5_1094jobs := by rfl
theorem t5_1094all : t5_1094jobs.all (Job.check tree)=true := by
  simp only [t5_1094jobs,List.all_append,List.all_nil,t5_1094part0,Bool.and_self]
theorem t5_1094checked : Checked tree [4,5,9,9,3] := by
  refine ⟨plan4825,valid4825,t5_1094choices,?_⟩
  exact check_of_frontier tree 0 t5_1094root t5_1094jobs t5_1094frontier t5_1094all
theorem t5_1095choices : plan5053.choices=[4,5,9,9,6].map (options 5 5) := by rfl


theorem t5_1095part0 : t5_1095jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1095frontier : t5_1095root.frontier 0=t5_1095jobs := by rfl
theorem t5_1095all : t5_1095jobs.all (Job.check tree)=true := by
  simp only [t5_1095jobs,List.all_append,List.all_nil,t5_1095part0,Bool.and_self]
theorem t5_1095checked : Checked tree [4,5,9,9,6] := by
  refine ⟨plan5053,valid5053,t5_1095choices,?_⟩
  exact check_of_frontier tree 0 t5_1095root t5_1095jobs t5_1095frontier t5_1095all
theorem t5_1096choices : plan5054.choices=[4,5,9,9,7].map (options 5 5) := by rfl


theorem t5_1096part0 : t5_1096jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1096frontier : t5_1096root.frontier 0=t5_1096jobs := by rfl
theorem t5_1096all : t5_1096jobs.all (Job.check tree)=true := by
  simp only [t5_1096jobs,List.all_append,List.all_nil,t5_1096part0,Bool.and_self]
theorem t5_1096checked : Checked tree [4,5,9,9,7] := by
  refine ⟨plan5054,valid5054,t5_1096choices,?_⟩
  exact check_of_frontier tree 0 t5_1096root t5_1096jobs t5_1096frontier t5_1096all
theorem t5_1097choices : plan5055.choices=[4,5,9,9,10].map (options 5 5) := by rfl


theorem t5_1097part0 : t5_1097jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1097frontier : t5_1097root.frontier 0=t5_1097jobs := by rfl
theorem t5_1097all : t5_1097jobs.all (Job.check tree)=true := by
  simp only [t5_1097jobs,List.all_append,List.all_nil,t5_1097part0,Bool.and_self]
theorem t5_1097checked : Checked tree [4,5,9,9,10] := by
  refine ⟨plan5055,valid5055,t5_1097choices,?_⟩
  exact check_of_frontier tree 0 t5_1097root t5_1097jobs t5_1097frontier t5_1097all
theorem t5_1098choices : plan5056.choices=[4,5,9,10,7].map (options 5 5) := by rfl


theorem t5_1098part0 : t5_1098jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1098frontier : t5_1098root.frontier 0=t5_1098jobs := by rfl
theorem t5_1098all : t5_1098jobs.all (Job.check tree)=true := by
  simp only [t5_1098jobs,List.all_append,List.all_nil,t5_1098part0,Bool.and_self]
theorem t5_1098checked : Checked tree [4,5,9,10,7] := by
  refine ⟨plan5056,valid5056,t5_1098choices,?_⟩
  exact check_of_frontier tree 0 t5_1098root t5_1098jobs t5_1098frontier t5_1098all
theorem t5_1099choices : plan5057.choices=[4,5,9,10,10].map (options 5 5) := by rfl


theorem t5_1099part0 : t5_1099jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1099frontier : t5_1099root.frontier 0=t5_1099jobs := by rfl
theorem t5_1099all : t5_1099jobs.all (Job.check tree)=true := by
  simp only [t5_1099jobs,List.all_append,List.all_nil,t5_1099part0,Bool.and_self]
theorem t5_1099checked : Checked tree [4,5,9,10,10] := by
  refine ⟨plan5057,valid5057,t5_1099choices,?_⟩
  exact check_of_frontier tree 0 t5_1099root t5_1099jobs t5_1099frontier t5_1099all
theorem t5_1100choices : plan5058.choices=[4,5,10,7,7].map (options 5 5) := by rfl


theorem t5_1100part0 : t5_1100jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1100frontier : t5_1100root.frontier 0=t5_1100jobs := by rfl
theorem t5_1100all : t5_1100jobs.all (Job.check tree)=true := by
  simp only [t5_1100jobs,List.all_append,List.all_nil,t5_1100part0,Bool.and_self]
theorem t5_1100checked : Checked tree [4,5,10,7,7] := by
  refine ⟨plan5058,valid5058,t5_1100choices,?_⟩
  exact check_of_frontier tree 0 t5_1100root t5_1100jobs t5_1100frontier t5_1100all
theorem t5_1101choices : plan5059.choices=[4,5,10,10,7].map (options 5 5) := by rfl


theorem t5_1101part0 : t5_1101jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1101frontier : t5_1101root.frontier 0=t5_1101jobs := by rfl
theorem t5_1101all : t5_1101jobs.all (Job.check tree)=true := by
  simp only [t5_1101jobs,List.all_append,List.all_nil,t5_1101part0,Bool.and_self]
theorem t5_1101checked : Checked tree [4,5,10,10,7] := by
  refine ⟨plan5059,valid5059,t5_1101choices,?_⟩
  exact check_of_frontier tree 0 t5_1101root t5_1101jobs t5_1101frontier t5_1101all
theorem t5_1102choices : plan5060.choices=[4,5,10,10,10].map (options 5 5) := by rfl


theorem t5_1102part0 : t5_1102jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1102frontier : t5_1102root.frontier 0=t5_1102jobs := by rfl
theorem t5_1102all : t5_1102jobs.all (Job.check tree)=true := by
  simp only [t5_1102jobs,List.all_append,List.all_nil,t5_1102part0,Bool.and_self]
theorem t5_1102checked : Checked tree [4,5,10,10,10] := by
  refine ⟨plan5060,valid5060,t5_1102choices,?_⟩
  exact check_of_frontier tree 0 t5_1102root t5_1102jobs t5_1102frontier t5_1102all
theorem t5_1103choices : plan5061.choices=[4,6,6,6,6].map (options 5 5) := by rfl


theorem t5_1103part0 : t5_1103jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1103frontier : t5_1103root.frontier 0=t5_1103jobs := by rfl
theorem t5_1103all : t5_1103jobs.all (Job.check tree)=true := by
  simp only [t5_1103jobs,List.all_append,List.all_nil,t5_1103part0,Bool.and_self]
theorem t5_1103checked : Checked tree [4,6,6,6,6] := by
  refine ⟨plan5061,valid5061,t5_1103choices,?_⟩
  exact check_of_frontier tree 0 t5_1103root t5_1103jobs t5_1103frontier t5_1103all
theorem t5_1104choices : plan5062.choices=[4,6,6,6,7].map (options 5 5) := by rfl


theorem t5_1104part0 : t5_1104jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1104frontier : t5_1104root.frontier 0=t5_1104jobs := by rfl
theorem t5_1104all : t5_1104jobs.all (Job.check tree)=true := by
  simp only [t5_1104jobs,List.all_append,List.all_nil,t5_1104part0,Bool.and_self]
theorem t5_1104checked : Checked tree [4,6,6,6,7] := by
  refine ⟨plan5062,valid5062,t5_1104choices,?_⟩
  exact check_of_frontier tree 0 t5_1104root t5_1104jobs t5_1104frontier t5_1104all
theorem t5_1105choices : plan5063.choices=[4,6,6,6,10].map (options 5 5) := by rfl


theorem t5_1105part0 : t5_1105jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1105frontier : t5_1105root.frontier 0=t5_1105jobs := by rfl
theorem t5_1105all : t5_1105jobs.all (Job.check tree)=true := by
  simp only [t5_1105jobs,List.all_append,List.all_nil,t5_1105part0,Bool.and_self]
theorem t5_1105checked : Checked tree [4,6,6,6,10] := by
  refine ⟨plan5063,valid5063,t5_1105choices,?_⟩
  exact check_of_frontier tree 0 t5_1105root t5_1105jobs t5_1105frontier t5_1105all
theorem t5_1106choices : plan5064.choices=[4,6,6,7,7].map (options 5 5) := by rfl


theorem t5_1106part0 : t5_1106jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1106frontier : t5_1106root.frontier 0=t5_1106jobs := by rfl
theorem t5_1106all : t5_1106jobs.all (Job.check tree)=true := by
  simp only [t5_1106jobs,List.all_append,List.all_nil,t5_1106part0,Bool.and_self]
theorem t5_1106checked : Checked tree [4,6,6,7,7] := by
  refine ⟨plan5064,valid5064,t5_1106choices,?_⟩
  exact check_of_frontier tree 0 t5_1106root t5_1106jobs t5_1106frontier t5_1106all
theorem t5_1107choices : plan5065.choices=[4,6,6,10,7].map (options 5 5) := by rfl


theorem t5_1107part0 : t5_1107jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1107frontier : t5_1107root.frontier 0=t5_1107jobs := by rfl
theorem t5_1107all : t5_1107jobs.all (Job.check tree)=true := by
  simp only [t5_1107jobs,List.all_append,List.all_nil,t5_1107part0,Bool.and_self]
theorem t5_1107checked : Checked tree [4,6,6,10,7] := by
  refine ⟨plan5065,valid5065,t5_1107choices,?_⟩
  exact check_of_frontier tree 0 t5_1107root t5_1107jobs t5_1107frontier t5_1107all
theorem t5_1108choices : plan5066.choices=[4,6,6,10,10].map (options 5 5) := by rfl


theorem t5_1108part0 : t5_1108jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1108frontier : t5_1108root.frontier 0=t5_1108jobs := by rfl
theorem t5_1108all : t5_1108jobs.all (Job.check tree)=true := by
  simp only [t5_1108jobs,List.all_append,List.all_nil,t5_1108part0,Bool.and_self]
theorem t5_1108checked : Checked tree [4,6,6,10,10] := by
  refine ⟨plan5066,valid5066,t5_1108choices,?_⟩
  exact check_of_frontier tree 0 t5_1108root t5_1108jobs t5_1108frontier t5_1108all
theorem t5_1109choices : plan5067.choices=[4,6,7,7,7].map (options 5 5) := by rfl


theorem t5_1109part0 : t5_1109jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1109frontier : t5_1109root.frontier 0=t5_1109jobs := by rfl
theorem t5_1109all : t5_1109jobs.all (Job.check tree)=true := by
  simp only [t5_1109jobs,List.all_append,List.all_nil,t5_1109part0,Bool.and_self]
theorem t5_1109checked : Checked tree [4,6,7,7,7] := by
  refine ⟨plan5067,valid5067,t5_1109choices,?_⟩
  exact check_of_frontier tree 0 t5_1109root t5_1109jobs t5_1109frontier t5_1109all
theorem t5_1110choices : plan5068.choices=[4,6,10,7,7].map (options 5 5) := by rfl


theorem t5_1110part0 : t5_1110jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1110frontier : t5_1110root.frontier 0=t5_1110jobs := by rfl
theorem t5_1110all : t5_1110jobs.all (Job.check tree)=true := by
  simp only [t5_1110jobs,List.all_append,List.all_nil,t5_1110part0,Bool.and_self]
theorem t5_1110checked : Checked tree [4,6,10,7,7] := by
  refine ⟨plan5068,valid5068,t5_1110choices,?_⟩
  exact check_of_frontier tree 0 t5_1110root t5_1110jobs t5_1110frontier t5_1110all
theorem t5_1111choices : plan5069.choices=[4,6,10,10,7].map (options 5 5) := by rfl


theorem t5_1111part0 : t5_1111jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1111frontier : t5_1111root.frontier 0=t5_1111jobs := by rfl
theorem t5_1111all : t5_1111jobs.all (Job.check tree)=true := by
  simp only [t5_1111jobs,List.all_append,List.all_nil,t5_1111part0,Bool.and_self]
theorem t5_1111checked : Checked tree [4,6,10,10,7] := by
  refine ⟨plan5069,valid5069,t5_1111choices,?_⟩
  exact check_of_frontier tree 0 t5_1111root t5_1111jobs t5_1111frontier t5_1111all
theorem t5_1112choices : plan5070.choices=[4,6,10,10,10].map (options 5 5) := by rfl


theorem t5_1112part0 : t5_1112jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1112frontier : t5_1112root.frontier 0=t5_1112jobs := by rfl
theorem t5_1112all : t5_1112jobs.all (Job.check tree)=true := by
  simp only [t5_1112jobs,List.all_append,List.all_nil,t5_1112part0,Bool.and_self]
theorem t5_1112checked : Checked tree [4,6,10,10,10] := by
  refine ⟨plan5070,valid5070,t5_1112choices,?_⟩
  exact check_of_frontier tree 0 t5_1112root t5_1112jobs t5_1112frontier t5_1112all
theorem t5_1113choices : plan5071.choices=[4,7,7,7,7].map (options 5 5) := by rfl


theorem t5_1113part0 : t5_1113jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1113frontier : t5_1113root.frontier 0=t5_1113jobs := by rfl
theorem t5_1113all : t5_1113jobs.all (Job.check tree)=true := by
  simp only [t5_1113jobs,List.all_append,List.all_nil,t5_1113part0,Bool.and_self]
theorem t5_1113checked : Checked tree [4,7,7,7,7] := by
  refine ⟨plan5071,valid5071,t5_1113choices,?_⟩
  exact check_of_frontier tree 0 t5_1113root t5_1113jobs t5_1113frontier t5_1113all
theorem t5_1114choices : plan4361.choices=[4,8,2,2,7].map (options 5 3) := by rfl


theorem t5_1114part0 : t5_1114jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1114frontier : t5_1114root.frontier 0=t5_1114jobs := by rfl
theorem t5_1114all : t5_1114jobs.all (Job.check tree)=true := by
  simp only [t5_1114jobs,List.all_append,List.all_nil,t5_1114part0,Bool.and_self]
theorem t5_1114checked : Checked tree [4,8,2,2,7] := by
  refine ⟨plan4361,valid4361,t5_1114choices,?_⟩
  exact check_of_frontier tree 0 t5_1114root t5_1114jobs t5_1114frontier t5_1114all
theorem t5_1115choices : plan3968.choices=[4,8,2,3,3].map (options 5 2) := by rfl


theorem t5_1115part0 : t5_1115jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1115frontier : t5_1115root.frontier 0=t5_1115jobs := by rfl
theorem t5_1115all : t5_1115jobs.all (Job.check tree)=true := by
  simp only [t5_1115jobs,List.all_append,List.all_nil,t5_1115part0,Bool.and_self]
theorem t5_1115checked : Checked tree [4,8,2,3,3] := by
  refine ⟨plan3968,valid3968,t5_1115choices,?_⟩
  exact check_of_frontier tree 0 t5_1115root t5_1115jobs t5_1115frontier t5_1115all
theorem t5_1116choices : plan4362.choices=[4,8,2,3,6].map (options 5 3) := by rfl


theorem t5_1116part0 : t5_1116jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1116frontier : t5_1116root.frontier 0=t5_1116jobs := by rfl
theorem t5_1116all : t5_1116jobs.all (Job.check tree)=true := by
  simp only [t5_1116jobs,List.all_append,List.all_nil,t5_1116part0,Bool.and_self]
theorem t5_1116checked : Checked tree [4,8,2,3,6] := by
  refine ⟨plan4362,valid4362,t5_1116choices,?_⟩
  exact check_of_frontier tree 0 t5_1116root t5_1116jobs t5_1116frontier t5_1116all
theorem t5_1117choices : plan4363.choices=[4,8,2,3,7].map (options 5 3) := by rfl


theorem t5_1117part0 : t5_1117jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1117frontier : t5_1117root.frontier 0=t5_1117jobs := by rfl
theorem t5_1117all : t5_1117jobs.all (Job.check tree)=true := by
  simp only [t5_1117jobs,List.all_append,List.all_nil,t5_1117part0,Bool.and_self]
theorem t5_1117checked : Checked tree [4,8,2,3,7] := by
  refine ⟨plan4363,valid4363,t5_1117choices,?_⟩
  exact check_of_frontier tree 0 t5_1117root t5_1117jobs t5_1117frontier t5_1117all
theorem t5_1118choices : plan4364.choices=[4,8,2,3,10].map (options 5 3) := by rfl


theorem t5_1118part0 : t5_1118jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1118frontier : t5_1118root.frontier 0=t5_1118jobs := by rfl
theorem t5_1118all : t5_1118jobs.all (Job.check tree)=true := by
  simp only [t5_1118jobs,List.all_append,List.all_nil,t5_1118part0,Bool.and_self]
theorem t5_1118checked : Checked tree [4,8,2,3,10] := by
  refine ⟨plan4364,valid4364,t5_1118choices,?_⟩
  exact check_of_frontier tree 0 t5_1118root t5_1118jobs t5_1118frontier t5_1118all
theorem t5_1119choices : plan4826.choices=[4,8,2,5,7].map (options 5 4) := by rfl


theorem t5_1119part0 : t5_1119jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1119frontier : t5_1119root.frontier 0=t5_1119jobs := by rfl
theorem t5_1119all : t5_1119jobs.all (Job.check tree)=true := by
  simp only [t5_1119jobs,List.all_append,List.all_nil,t5_1119part0,Bool.and_self]
theorem t5_1119checked : Checked tree [4,8,2,5,7] := by
  refine ⟨plan4826,valid4826,t5_1119choices,?_⟩
  exact check_of_frontier tree 0 t5_1119root t5_1119jobs t5_1119frontier t5_1119all
theorem t5_1120choices : plan4827.choices=[4,8,2,6,6].map (options 5 4) := by rfl


theorem t5_1120part0 : t5_1120jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1120frontier : t5_1120root.frontier 0=t5_1120jobs := by rfl
theorem t5_1120all : t5_1120jobs.all (Job.check tree)=true := by
  simp only [t5_1120jobs,List.all_append,List.all_nil,t5_1120part0,Bool.and_self]
theorem t5_1120checked : Checked tree [4,8,2,6,6] := by
  refine ⟨plan4827,valid4827,t5_1120choices,?_⟩
  exact check_of_frontier tree 0 t5_1120root t5_1120jobs t5_1120frontier t5_1120all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks033 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1021checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1022checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1023checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1024checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1025checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1026checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1027checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1028checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1029checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1009checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1030checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1031checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1032checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1033checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1034checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1035checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1036checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1037checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1038checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1039checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1010checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1040checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1041checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1042checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1043checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1044checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1045checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1046checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1047checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1048checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1049checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1011checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1050checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1051checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1052checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1053checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1054checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1055checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1056checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1057checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1058checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1059checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1012checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1060checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1061checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1062checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1063checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1064checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1065checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1066checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1067checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1068checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1069checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1013checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1070checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1071checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1072checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1073checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1074checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1075checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1076checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1077checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1078checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1079checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1014checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1080checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1081checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1082checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1083checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1084checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1085checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1086checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1087checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1088checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1089checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1015checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1090checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1091checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1092checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1093checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1094checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1095checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1096checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1097checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1098checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1099checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1016checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1100checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1101checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1102checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1103checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1104checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1105checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1106checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1107checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1108checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1109checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1017checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1110checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1111checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1112checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1113checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1114checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1115checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1116checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1117checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1118checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1119checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1018checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1120checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1019checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1008checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1020checked⟩
