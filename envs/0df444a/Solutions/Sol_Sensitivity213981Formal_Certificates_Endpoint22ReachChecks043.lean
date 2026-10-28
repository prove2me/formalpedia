-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks043
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:10:38.833379+00:00
-- url     : https://prove2.me/submissions/b82720f7-6906-4b72-916e-007be873aa91

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks043
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks043
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans054
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



theorem valid520 : plan520.Valid := valid_step _ _ _ valid109 (by decide +kernel)





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

theorem valid1401 : plan1401.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1402 : plan1402.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1403 : plan1403.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1404 : plan1404.Valid := valid_step _ _ _ valid520 (by decide +kernel)

theorem valid1405 : plan1405.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1406 : plan1406.Valid := valid_step _ _ _ valid524 (by decide +kernel)

theorem valid1407 : plan1407.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1408 : plan1408.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1409 : plan1409.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1410 : plan1410.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1411 : plan1411.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1412 : plan1412.Valid := valid_step _ _ _ valid524 (by decide +kernel)









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



























































































































theorem valid2654 : plan2654.Valid := valid_step _ _ _ valid1276 (by decide +kernel)







theorem valid2658 : plan2658.Valid := valid_step _ _ _ valid1297 (by decide +kernel)











theorem valid2664 : plan2664.Valid := valid_step _ _ _ valid1297 (by decide +kernel)
















































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

















































































































theorem valid3993 : plan3993.Valid := valid_step _ _ _ valid2654 (by decide +kernel)

theorem valid3994 : plan3994.Valid := valid_step _ _ _ valid2658 (by decide +kernel)

theorem valid3995 : plan3995.Valid := valid_step _ _ _ valid2664 (by decide +kernel)










































































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



































































theorem valid2818 : plan2818.Valid := valid_step _ _ _ valid1349 (by decide +kernel)











theorem valid2824 : plan2824.Valid := valid_step _ _ _ valid1381 (by decide +kernel)









theorem valid2829 : plan2829.Valid := valid_step _ _ _ valid1320 (by decide +kernel)

theorem valid2830 : plan2830.Valid := valid_step _ _ _ valid1321 (by decide +kernel)

theorem valid2831 : plan2831.Valid := valid_step _ _ _ valid1322 (by decide +kernel)

theorem valid2832 : plan2832.Valid := valid_step _ _ _ valid1323 (by decide +kernel)

















theorem valid2841 : plan2841.Valid := valid_step _ _ _ valid1336 (by decide +kernel)

theorem valid2842 : plan2842.Valid := valid_step _ _ _ valid1337 (by decide +kernel)

theorem valid2843 : plan2843.Valid := valid_step _ _ _ valid1338 (by decide +kernel)













theorem valid2850 : plan2850.Valid := valid_step _ _ _ valid1349 (by decide +kernel)









theorem valid2855 : plan2855.Valid := valid_step _ _ _ valid1381 (by decide +kernel)







theorem valid2859 : plan2859.Valid := valid_step _ _ _ valid1336 (by decide +kernel)

theorem valid2860 : plan2860.Valid := valid_step _ _ _ valid1337 (by decide +kernel)








































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

theorem valid3030 : plan3030.Valid := valid_step _ _ _ valid1401 (by decide +kernel)

theorem valid3031 : plan3031.Valid := valid_step _ _ _ valid1402 (by decide +kernel)

theorem valid3032 : plan3032.Valid := valid_step _ _ _ valid1403 (by decide +kernel)

theorem valid3033 : plan3033.Valid := valid_step _ _ _ valid1404 (by decide +kernel)

theorem valid3034 : plan3034.Valid := valid_step _ _ _ valid1405 (by decide +kernel)

theorem valid3035 : plan3035.Valid := valid_step _ _ _ valid1406 (by decide +kernel)

theorem valid3036 : plan3036.Valid := valid_step _ _ _ valid1407 (by decide +kernel)

theorem valid3037 : plan3037.Valid := valid_step _ _ _ valid1408 (by decide +kernel)

theorem valid3038 : plan3038.Valid := valid_step _ _ _ valid1409 (by decide +kernel)

theorem valid3039 : plan3039.Valid := valid_step _ _ _ valid1410 (by decide +kernel)

theorem valid3040 : plan3040.Valid := valid_step _ _ _ valid1411 (by decide +kernel)

theorem valid3041 : plan3041.Valid := valid_step _ _ _ valid1412 (by decide +kernel)

theorem valid3042 : plan3042.Valid := valid_step _ _ _ valid1417 (by decide +kernel)

theorem valid3043 : plan3043.Valid := valid_step _ _ _ valid1418 (by decide +kernel)

theorem valid3044 : plan3044.Valid := valid_step _ _ _ valid1419 (by decide +kernel)































theorem valid3060 : plan3060.Valid := valid_step _ _ _ valid1444 (by decide +kernel)







theorem valid3064 : plan3064.Valid := valid_step _ _ _ valid1448 (by decide +kernel)

theorem valid3065 : plan3065.Valid := valid_step _ _ _ valid1449 (by decide +kernel)

theorem valid3066 : plan3066.Valid := valid_step _ _ _ valid1450 (by decide +kernel)












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

















theorem valid4425 : plan4425.Valid := valid_step _ _ _ valid2818 (by decide +kernel)

theorem valid4426 : plan4426.Valid := valid_step _ _ _ valid2824 (by decide +kernel)

theorem valid4427 : plan4427.Valid := valid_step _ _ _ valid2829 (by decide +kernel)

theorem valid4428 : plan4428.Valid := valid_step _ _ _ valid2830 (by decide +kernel)

theorem valid4429 : plan4429.Valid := valid_step _ _ _ valid2831 (by decide +kernel)

theorem valid4430 : plan4430.Valid := valid_step _ _ _ valid2832 (by decide +kernel)

theorem valid4431 : plan4431.Valid := valid_step _ _ _ valid2841 (by decide +kernel)

theorem valid4432 : plan4432.Valid := valid_step _ _ _ valid2842 (by decide +kernel)

theorem valid4433 : plan4433.Valid := valid_step _ _ _ valid2843 (by decide +kernel)

theorem valid4434 : plan4434.Valid := valid_step _ _ _ valid2850 (by decide +kernel)

theorem valid4435 : plan4435.Valid := valid_step _ _ _ valid2855 (by decide +kernel)

theorem valid4436 : plan4436.Valid := valid_step _ _ _ valid2859 (by decide +kernel)

theorem valid4437 : plan4437.Valid := valid_step _ _ _ valid2860 (by decide +kernel)






















































































































































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

theorem valid3188 : plan3188.Valid := valid_step _ _ _ valid1470 (by decide +kernel)

theorem valid3189 : plan3189.Valid := valid_step _ _ _ valid1473 (by decide +kernel)

theorem valid3190 : plan3190.Valid := valid_step _ _ _ valid1474 (by decide +kernel)

theorem valid3191 : plan3191.Valid := valid_step _ _ _ valid1475 (by decide +kernel)

theorem valid3192 : plan3192.Valid := valid_step _ _ _ valid1476 (by decide +kernel)

theorem valid3193 : plan3193.Valid := valid_step _ _ _ valid1478 (by decide +kernel)

theorem valid3194 : plan3194.Valid := valid_step _ _ _ valid1481 (by decide +kernel)

theorem valid3195 : plan3195.Valid := valid_step _ _ _ valid1482 (by decide +kernel)

theorem valid3196 : plan3196.Valid := valid_step _ _ _ valid1483 (by decide +kernel)

theorem valid3197 : plan3197.Valid := valid_step _ _ _ valid1484 (by decide +kernel)

theorem valid3198 : plan3198.Valid := valid_step _ _ _ valid1485 (by decide +kernel)

theorem valid3199 : plan3199.Valid := valid_step _ _ _ valid1486 (by decide +kernel)

theorem valid3200 : plan3200.Valid := valid_step _ _ _ valid1487 (by decide +kernel)

theorem valid3201 : plan3201.Valid := valid_step _ _ _ valid1488 (by decide +kernel)

theorem valid3202 : plan3202.Valid := valid_step _ _ _ valid1489 (by decide +kernel)

theorem valid3203 : plan3203.Valid := valid_step _ _ _ valid1490 (by decide +kernel)

theorem valid3204 : plan3204.Valid := valid_step _ _ _ valid1491 (by decide +kernel)

theorem valid3205 : plan3205.Valid := valid_step _ _ _ valid1492 (by decide +kernel)

theorem valid3206 : plan3206.Valid := valid_step _ _ _ valid1493 (by decide +kernel)

theorem valid3207 : plan3207.Valid := valid_step _ _ _ valid1494 (by decide +kernel)

theorem valid3208 : plan3208.Valid := valid_step _ _ _ valid1495 (by decide +kernel)

theorem valid3209 : plan3209.Valid := valid_step _ _ _ valid1496 (by decide +kernel)

theorem valid3210 : plan3210.Valid := valid_step _ _ _ valid1498 (by decide +kernel)

theorem valid3211 : plan3211.Valid := valid_step _ _ _ valid1501 (by decide +kernel)

theorem valid3212 : plan3212.Valid := valid_step _ _ _ valid1502 (by decide +kernel)

theorem valid3213 : plan3213.Valid := valid_step _ _ _ valid1503 (by decide +kernel)

theorem valid3214 : plan3214.Valid := valid_step _ _ _ valid1504 (by decide +kernel)

theorem valid3215 : plan3215.Valid := valid_step _ _ _ valid1505 (by decide +kernel)


































































































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

















































theorem valid5209 : plan5209.Valid := valid_step _ _ _ valid3143 (by decide +kernel)

theorem valid5210 : plan5210.Valid := valid_step _ _ _ valid3144 (by decide +kernel)

theorem valid5211 : plan5211.Valid := valid_step _ _ _ valid3146 (by decide +kernel)

theorem valid5212 : plan5212.Valid := valid_step _ _ _ valid3147 (by decide +kernel)

theorem valid5213 : plan5213.Valid := valid_step _ _ _ valid3148 (by decide +kernel)

theorem valid5214 : plan5214.Valid := valid_step _ _ _ valid3149 (by decide +kernel)

theorem valid5215 : plan5215.Valid := valid_step _ _ _ valid3150 (by decide +kernel)

theorem valid5216 : plan5216.Valid := valid_step _ _ _ valid3151 (by decide +kernel)

theorem valid5217 : plan5217.Valid := valid_step _ _ _ valid3152 (by decide +kernel)

theorem valid5218 : plan5218.Valid := valid_step _ _ _ valid3154 (by decide +kernel)

theorem valid5219 : plan5219.Valid := valid_step _ _ _ valid3155 (by decide +kernel)

theorem valid5220 : plan5220.Valid := valid_step _ _ _ valid3156 (by decide +kernel)

theorem valid5221 : plan5221.Valid := valid_step _ _ _ valid3157 (by decide +kernel)

theorem valid5222 : plan5222.Valid := valid_step _ _ _ valid3158 (by decide +kernel)

theorem valid5223 : plan5223.Valid := valid_step _ _ _ valid3159 (by decide +kernel)

theorem valid5224 : plan5224.Valid := valid_step _ _ _ valid3160 (by decide +kernel)

theorem valid5225 : plan5225.Valid := valid_step _ _ _ valid3161 (by decide +kernel)

theorem valid5226 : plan5226.Valid := valid_step _ _ _ valid3162 (by decide +kernel)

theorem valid5227 : plan5227.Valid := valid_step _ _ _ valid3163 (by decide +kernel)

theorem valid5228 : plan5228.Valid := valid_step _ _ _ valid3164 (by decide +kernel)

theorem valid5229 : plan5229.Valid := valid_step _ _ _ valid3165 (by decide +kernel)

theorem valid5230 : plan5230.Valid := valid_step _ _ _ valid3166 (by decide +kernel)

theorem valid5231 : plan5231.Valid := valid_step _ _ _ valid3167 (by decide +kernel)

theorem valid5232 : plan5232.Valid := valid_step _ _ _ valid3168 (by decide +kernel)

theorem valid5233 : plan5233.Valid := valid_step _ _ _ valid3169 (by decide +kernel)

theorem valid5234 : plan5234.Valid := valid_step _ _ _ valid3171 (by decide +kernel)

theorem valid5235 : plan5235.Valid := valid_step _ _ _ valid3172 (by decide +kernel)

theorem valid5236 : plan5236.Valid := valid_step _ _ _ valid3173 (by decide +kernel)

theorem valid5237 : plan5237.Valid := valid_step _ _ _ valid3174 (by decide +kernel)

theorem valid5238 : plan5238.Valid := valid_step _ _ _ valid3175 (by decide +kernel)

theorem valid5239 : plan5239.Valid := valid_step _ _ _ valid3176 (by decide +kernel)

theorem valid5240 : plan5240.Valid := valid_step _ _ _ valid3177 (by decide +kernel)

theorem valid5241 : plan5241.Valid := valid_step _ _ _ valid3178 (by decide +kernel)

theorem valid5242 : plan5242.Valid := valid_step _ _ _ valid3179 (by decide +kernel)

theorem valid5243 : plan5243.Valid := valid_step _ _ _ valid3180 (by decide +kernel)

theorem valid5244 : plan5244.Valid := valid_step _ _ _ valid3181 (by decide +kernel)

theorem valid5245 : plan5245.Valid := valid_step _ _ _ valid3182 (by decide +kernel)

theorem valid5246 : plan5246.Valid := valid_step _ _ _ valid3183 (by decide +kernel)

theorem valid5247 : plan5247.Valid := valid_step _ _ _ valid3184 (by decide +kernel)

theorem valid5248 : plan5248.Valid := valid_step _ _ _ valid3185 (by decide +kernel)

theorem valid5249 : plan5249.Valid := valid_step _ _ _ valid3186 (by decide +kernel)

theorem valid5250 : plan5250.Valid := valid_step _ _ _ valid3187 (by decide +kernel)

theorem valid5251 : plan5251.Valid := valid_step _ _ _ valid3188 (by decide +kernel)

theorem valid5252 : plan5252.Valid := valid_step _ _ _ valid3189 (by decide +kernel)

theorem valid5253 : plan5253.Valid := valid_step _ _ _ valid3190 (by decide +kernel)

theorem valid5254 : plan5254.Valid := valid_step _ _ _ valid3191 (by decide +kernel)

theorem valid5255 : plan5255.Valid := valid_step _ _ _ valid3192 (by decide +kernel)

theorem valid5256 : plan5256.Valid := valid_step _ _ _ valid3193 (by decide +kernel)

theorem valid5257 : plan5257.Valid := valid_step _ _ _ valid3194 (by decide +kernel)

theorem valid5258 : plan5258.Valid := valid_step _ _ _ valid3195 (by decide +kernel)

theorem valid5259 : plan5259.Valid := valid_step _ _ _ valid3196 (by decide +kernel)

theorem valid5260 : plan5260.Valid := valid_step _ _ _ valid3197 (by decide +kernel)

theorem valid5261 : plan5261.Valid := valid_step _ _ _ valid3198 (by decide +kernel)

theorem valid5262 : plan5262.Valid := valid_step _ _ _ valid3199 (by decide +kernel)

theorem valid5263 : plan5263.Valid := valid_step _ _ _ valid3200 (by decide +kernel)

theorem valid5264 : plan5264.Valid := valid_step _ _ _ valid3201 (by decide +kernel)

theorem valid5265 : plan5265.Valid := valid_step _ _ _ valid3202 (by decide +kernel)

theorem valid5266 : plan5266.Valid := valid_step _ _ _ valid3203 (by decide +kernel)

theorem valid5267 : plan5267.Valid := valid_step _ _ _ valid3204 (by decide +kernel)

theorem valid5268 : plan5268.Valid := valid_step _ _ _ valid3205 (by decide +kernel)

theorem valid5269 : plan5269.Valid := valid_step _ _ _ valid3206 (by decide +kernel)

theorem valid5270 : plan5270.Valid := valid_step _ _ _ valid3207 (by decide +kernel)

theorem valid5271 : plan5271.Valid := valid_step _ _ _ valid3208 (by decide +kernel)

theorem valid5272 : plan5272.Valid := valid_step _ _ _ valid3209 (by decide +kernel)

theorem valid5273 : plan5273.Valid := valid_step _ _ _ valid3210 (by decide +kernel)

theorem valid5274 : plan5274.Valid := valid_step _ _ _ valid3211 (by decide +kernel)

theorem valid5275 : plan5275.Valid := valid_step _ _ _ valid3212 (by decide +kernel)

theorem valid5276 : plan5276.Valid := valid_step _ _ _ valid3213 (by decide +kernel)

theorem valid5277 : plan5277.Valid := valid_step _ _ _ valid3214 (by decide +kernel)

theorem valid5278 : plan5278.Valid := valid_step _ _ _ valid3215 (by decide +kernel)




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













































































theorem valid4935 : plan4935.Valid := valid_step _ _ _ valid2969 (by decide +kernel)

theorem valid4936 : plan4936.Valid := valid_step _ _ _ valid2970 (by decide +kernel)

theorem valid4937 : plan4937.Valid := valid_step _ _ _ valid2971 (by decide +kernel)

theorem valid4938 : plan4938.Valid := valid_step _ _ _ valid2972 (by decide +kernel)

theorem valid4939 : plan4939.Valid := valid_step _ _ _ valid2973 (by decide +kernel)

theorem valid4940 : plan4940.Valid := valid_step _ _ _ valid2974 (by decide +kernel)

theorem valid4941 : plan4941.Valid := valid_step _ _ _ valid2975 (by decide +kernel)

theorem valid4942 : plan4942.Valid := valid_step _ _ _ valid2976 (by decide +kernel)

theorem valid4943 : plan4943.Valid := valid_step _ _ _ valid2986 (by decide +kernel)

theorem valid4944 : plan4944.Valid := valid_step _ _ _ valid3000 (by decide +kernel)

theorem valid4945 : plan4945.Valid := valid_step _ _ _ valid3001 (by decide +kernel)

theorem valid4946 : plan4946.Valid := valid_step _ _ _ valid3002 (by decide +kernel)

theorem valid4947 : plan4947.Valid := valid_step _ _ _ valid3007 (by decide +kernel)

theorem valid4948 : plan4948.Valid := valid_step _ _ _ valid3028 (by decide +kernel)

theorem valid4949 : plan4949.Valid := valid_step _ _ _ valid3029 (by decide +kernel)

theorem valid4950 : plan4950.Valid := valid_step _ _ _ valid3030 (by decide +kernel)

theorem valid4951 : plan4951.Valid := valid_step _ _ _ valid3031 (by decide +kernel)

theorem valid4952 : plan4952.Valid := valid_step _ _ _ valid3032 (by decide +kernel)

theorem valid4953 : plan4953.Valid := valid_step _ _ _ valid3033 (by decide +kernel)

theorem valid4954 : plan4954.Valid := valid_step _ _ _ valid3034 (by decide +kernel)

theorem valid4955 : plan4955.Valid := valid_step _ _ _ valid3035 (by decide +kernel)

theorem valid4956 : plan4956.Valid := valid_step _ _ _ valid3036 (by decide +kernel)

theorem valid4957 : plan4957.Valid := valid_step _ _ _ valid3037 (by decide +kernel)

theorem valid4958 : plan4958.Valid := valid_step _ _ _ valid3038 (by decide +kernel)

theorem valid4959 : plan4959.Valid := valid_step _ _ _ valid3039 (by decide +kernel)

theorem valid4960 : plan4960.Valid := valid_step _ _ _ valid3040 (by decide +kernel)

theorem valid4961 : plan4961.Valid := valid_step _ _ _ valid3041 (by decide +kernel)

theorem valid4962 : plan4962.Valid := valid_step _ _ _ valid3042 (by decide +kernel)

theorem valid4963 : plan4963.Valid := valid_step _ _ _ valid3043 (by decide +kernel)

theorem valid4964 : plan4964.Valid := valid_step _ _ _ valid3044 (by decide +kernel)

theorem valid4965 : plan4965.Valid := valid_step _ _ _ valid3060 (by decide +kernel)

theorem valid4966 : plan4966.Valid := valid_step _ _ _ valid3064 (by decide +kernel)

theorem valid4967 : plan4967.Valid := valid_step _ _ _ valid3065 (by decide +kernel)

theorem valid4968 : plan4968.Valid := valid_step _ _ _ valid3066 (by decide +kernel)
















































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
theorem t5_1454choices : plan4935.choices=[8,5,3,6,10].map (options 5 4) := by rfl


theorem t5_1454part0 : t5_1454jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1454frontier : t5_1454root.frontier 0=t5_1454jobs := by rfl
theorem t5_1454all : t5_1454jobs.all (Job.check tree)=true := by
  simp only [t5_1454jobs,List.all_append,List.all_nil,t5_1454part0,Bool.and_self]
theorem t5_1454checked : Checked tree [8,5,3,6,10] := by
  refine ⟨plan4935,valid4935,t5_1454choices,?_⟩
  exact check_of_frontier tree 0 t5_1454root t5_1454jobs t5_1454frontier t5_1454all
theorem t5_1455choices : plan4936.choices=[8,5,3,7,7].map (options 5 4) := by rfl


theorem t5_1455part0 : t5_1455jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1455frontier : t5_1455root.frontier 0=t5_1455jobs := by rfl
theorem t5_1455all : t5_1455jobs.all (Job.check tree)=true := by
  simp only [t5_1455jobs,List.all_append,List.all_nil,t5_1455part0,Bool.and_self]
theorem t5_1455checked : Checked tree [8,5,3,7,7] := by
  refine ⟨plan4936,valid4936,t5_1455choices,?_⟩
  exact check_of_frontier tree 0 t5_1455root t5_1455jobs t5_1455frontier t5_1455all
theorem t5_1456choices : plan4937.choices=[8,5,3,10,7].map (options 5 4) := by rfl


theorem t5_1456part0 : t5_1456jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1456frontier : t5_1456root.frontier 0=t5_1456jobs := by rfl
theorem t5_1456all : t5_1456jobs.all (Job.check tree)=true := by
  simp only [t5_1456jobs,List.all_append,List.all_nil,t5_1456part0,Bool.and_self]
theorem t5_1456checked : Checked tree [8,5,3,10,7] := by
  refine ⟨plan4937,valid4937,t5_1456choices,?_⟩
  exact check_of_frontier tree 0 t5_1456root t5_1456jobs t5_1456frontier t5_1456all
theorem t5_1457choices : plan4938.choices=[8,5,3,10,10].map (options 5 4) := by rfl


theorem t5_1457part0 : t5_1457jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1457frontier : t5_1457root.frontier 0=t5_1457jobs := by rfl
theorem t5_1457all : t5_1457jobs.all (Job.check tree)=true := by
  simp only [t5_1457jobs,List.all_append,List.all_nil,t5_1457part0,Bool.and_self]
theorem t5_1457checked : Checked tree [8,5,3,10,10] := by
  refine ⟨plan4938,valid4938,t5_1457choices,?_⟩
  exact check_of_frontier tree 0 t5_1457root t5_1457jobs t5_1457frontier t5_1457all
theorem t5_1458choices : plan4425.choices=[8,5,5,3,3].map (options 5 3) := by rfl


theorem t5_1458part0 : t5_1458jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1458frontier : t5_1458root.frontier 0=t5_1458jobs := by rfl
theorem t5_1458all : t5_1458jobs.all (Job.check tree)=true := by
  simp only [t5_1458jobs,List.all_append,List.all_nil,t5_1458part0,Bool.and_self]
theorem t5_1458checked : Checked tree [8,5,5,3,3] := by
  refine ⟨plan4425,valid4425,t5_1458choices,?_⟩
  exact check_of_frontier tree 0 t5_1458root t5_1458jobs t5_1458frontier t5_1458all
theorem t5_1459choices : plan4939.choices=[8,5,5,3,6].map (options 5 4) := by rfl


theorem t5_1459part0 : t5_1459jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1459frontier : t5_1459root.frontier 0=t5_1459jobs := by rfl
theorem t5_1459all : t5_1459jobs.all (Job.check tree)=true := by
  simp only [t5_1459jobs,List.all_append,List.all_nil,t5_1459part0,Bool.and_self]
theorem t5_1459checked : Checked tree [8,5,5,3,6] := by
  refine ⟨plan4939,valid4939,t5_1459choices,?_⟩
  exact check_of_frontier tree 0 t5_1459root t5_1459jobs t5_1459frontier t5_1459all
theorem t5_1460choices : plan4940.choices=[8,5,5,3,7].map (options 5 4) := by rfl


theorem t5_1460part0 : t5_1460jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1460frontier : t5_1460root.frontier 0=t5_1460jobs := by rfl
theorem t5_1460all : t5_1460jobs.all (Job.check tree)=true := by
  simp only [t5_1460jobs,List.all_append,List.all_nil,t5_1460part0,Bool.and_self]
theorem t5_1460checked : Checked tree [8,5,5,3,7] := by
  refine ⟨plan4940,valid4940,t5_1460choices,?_⟩
  exact check_of_frontier tree 0 t5_1460root t5_1460jobs t5_1460frontier t5_1460all
theorem t5_1461choices : plan4941.choices=[8,5,5,3,10].map (options 5 4) := by rfl


theorem t5_1461part0 : t5_1461jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1461frontier : t5_1461root.frontier 0=t5_1461jobs := by rfl
theorem t5_1461all : t5_1461jobs.all (Job.check tree)=true := by
  simp only [t5_1461jobs,List.all_append,List.all_nil,t5_1461part0,Bool.and_self]
theorem t5_1461checked : Checked tree [8,5,5,3,10] := by
  refine ⟨plan4941,valid4941,t5_1461choices,?_⟩
  exact check_of_frontier tree 0 t5_1461root t5_1461jobs t5_1461frontier t5_1461all
theorem t5_1462choices : plan4942.choices=[8,5,5,5,3].map (options 5 4) := by rfl


theorem t5_1462part0 : t5_1462jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1462frontier : t5_1462root.frontier 0=t5_1462jobs := by rfl
theorem t5_1462all : t5_1462jobs.all (Job.check tree)=true := by
  simp only [t5_1462jobs,List.all_append,List.all_nil,t5_1462part0,Bool.and_self]
theorem t5_1462checked : Checked tree [8,5,5,5,3] := by
  refine ⟨plan4942,valid4942,t5_1462choices,?_⟩
  exact check_of_frontier tree 0 t5_1462root t5_1462jobs t5_1462frontier t5_1462all
theorem t5_1463choices : plan5209.choices=[8,5,5,5,6].map (options 5 5) := by rfl


theorem t5_1463part0 : t5_1463jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1463frontier : t5_1463root.frontier 0=t5_1463jobs := by rfl
theorem t5_1463all : t5_1463jobs.all (Job.check tree)=true := by
  simp only [t5_1463jobs,List.all_append,List.all_nil,t5_1463part0,Bool.and_self]
theorem t5_1463checked : Checked tree [8,5,5,5,6] := by
  refine ⟨plan5209,valid5209,t5_1463choices,?_⟩
  exact check_of_frontier tree 0 t5_1463root t5_1463jobs t5_1463frontier t5_1463all
theorem t5_1464choices : plan5210.choices=[8,5,5,5,7].map (options 5 5) := by rfl


theorem t5_1464part0 : t5_1464jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1464frontier : t5_1464root.frontier 0=t5_1464jobs := by rfl
theorem t5_1464all : t5_1464jobs.all (Job.check tree)=true := by
  simp only [t5_1464jobs,List.all_append,List.all_nil,t5_1464part0,Bool.and_self]
theorem t5_1464checked : Checked tree [8,5,5,5,7] := by
  refine ⟨plan5210,valid5210,t5_1464choices,?_⟩
  exact check_of_frontier tree 0 t5_1464root t5_1464jobs t5_1464frontier t5_1464all
theorem t5_1465choices : plan5211.choices=[8,5,5,5,10].map (options 5 5) := by rfl


theorem t5_1465part0 : t5_1465jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1465frontier : t5_1465root.frontier 0=t5_1465jobs := by rfl
theorem t5_1465all : t5_1465jobs.all (Job.check tree)=true := by
  simp only [t5_1465jobs,List.all_append,List.all_nil,t5_1465part0,Bool.and_self]
theorem t5_1465checked : Checked tree [8,5,5,5,10] := by
  refine ⟨plan5211,valid5211,t5_1465choices,?_⟩
  exact check_of_frontier tree 0 t5_1465root t5_1465jobs t5_1465frontier t5_1465all
theorem t5_1466choices : plan5212.choices=[8,5,5,6,6].map (options 5 5) := by rfl


theorem t5_1466part0 : t5_1466jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1466frontier : t5_1466root.frontier 0=t5_1466jobs := by rfl
theorem t5_1466all : t5_1466jobs.all (Job.check tree)=true := by
  simp only [t5_1466jobs,List.all_append,List.all_nil,t5_1466part0,Bool.and_self]
theorem t5_1466checked : Checked tree [8,5,5,6,6] := by
  refine ⟨plan5212,valid5212,t5_1466choices,?_⟩
  exact check_of_frontier tree 0 t5_1466root t5_1466jobs t5_1466frontier t5_1466all
theorem t5_1467choices : plan5213.choices=[8,5,5,6,7].map (options 5 5) := by rfl


theorem t5_1467part0 : t5_1467jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1467frontier : t5_1467root.frontier 0=t5_1467jobs := by rfl
theorem t5_1467all : t5_1467jobs.all (Job.check tree)=true := by
  simp only [t5_1467jobs,List.all_append,List.all_nil,t5_1467part0,Bool.and_self]
theorem t5_1467checked : Checked tree [8,5,5,6,7] := by
  refine ⟨plan5213,valid5213,t5_1467choices,?_⟩
  exact check_of_frontier tree 0 t5_1467root t5_1467jobs t5_1467frontier t5_1467all
theorem t5_1468choices : plan5214.choices=[8,5,5,6,10].map (options 5 5) := by rfl


theorem t5_1468part0 : t5_1468jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1468frontier : t5_1468root.frontier 0=t5_1468jobs := by rfl
theorem t5_1468all : t5_1468jobs.all (Job.check tree)=true := by
  simp only [t5_1468jobs,List.all_append,List.all_nil,t5_1468part0,Bool.and_self]
theorem t5_1468checked : Checked tree [8,5,5,6,10] := by
  refine ⟨plan5214,valid5214,t5_1468choices,?_⟩
  exact check_of_frontier tree 0 t5_1468root t5_1468jobs t5_1468frontier t5_1468all
theorem t5_1469choices : plan5215.choices=[8,5,5,7,7].map (options 5 5) := by rfl


theorem t5_1469part0 : t5_1469jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1469frontier : t5_1469root.frontier 0=t5_1469jobs := by rfl
theorem t5_1469all : t5_1469jobs.all (Job.check tree)=true := by
  simp only [t5_1469jobs,List.all_append,List.all_nil,t5_1469part0,Bool.and_self]
theorem t5_1469checked : Checked tree [8,5,5,7,7] := by
  refine ⟨plan5215,valid5215,t5_1469choices,?_⟩
  exact check_of_frontier tree 0 t5_1469root t5_1469jobs t5_1469frontier t5_1469all
theorem t5_1470choices : plan4943.choices=[8,5,5,9,3].map (options 5 4) := by rfl


theorem t5_1470part0 : t5_1470jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1470frontier : t5_1470root.frontier 0=t5_1470jobs := by rfl
theorem t5_1470all : t5_1470jobs.all (Job.check tree)=true := by
  simp only [t5_1470jobs,List.all_append,List.all_nil,t5_1470part0,Bool.and_self]
theorem t5_1470checked : Checked tree [8,5,5,9,3] := by
  refine ⟨plan4943,valid4943,t5_1470choices,?_⟩
  exact check_of_frontier tree 0 t5_1470root t5_1470jobs t5_1470frontier t5_1470all
theorem t5_1471choices : plan5216.choices=[8,5,5,9,6].map (options 5 5) := by rfl


theorem t5_1471part0 : t5_1471jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1471frontier : t5_1471root.frontier 0=t5_1471jobs := by rfl
theorem t5_1471all : t5_1471jobs.all (Job.check tree)=true := by
  simp only [t5_1471jobs,List.all_append,List.all_nil,t5_1471part0,Bool.and_self]
theorem t5_1471checked : Checked tree [8,5,5,9,6] := by
  refine ⟨plan5216,valid5216,t5_1471choices,?_⟩
  exact check_of_frontier tree 0 t5_1471root t5_1471jobs t5_1471frontier t5_1471all
theorem t5_1472choices : plan5217.choices=[8,5,5,9,7].map (options 5 5) := by rfl


theorem t5_1472part0 : t5_1472jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1472frontier : t5_1472root.frontier 0=t5_1472jobs := by rfl
theorem t5_1472all : t5_1472jobs.all (Job.check tree)=true := by
  simp only [t5_1472jobs,List.all_append,List.all_nil,t5_1472part0,Bool.and_self]
theorem t5_1472checked : Checked tree [8,5,5,9,7] := by
  refine ⟨plan5217,valid5217,t5_1472choices,?_⟩
  exact check_of_frontier tree 0 t5_1472root t5_1472jobs t5_1472frontier t5_1472all
theorem t5_1473choices : plan5218.choices=[8,5,5,9,10].map (options 5 5) := by rfl


theorem t5_1473part0 : t5_1473jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1473frontier : t5_1473root.frontier 0=t5_1473jobs := by rfl
theorem t5_1473all : t5_1473jobs.all (Job.check tree)=true := by
  simp only [t5_1473jobs,List.all_append,List.all_nil,t5_1473part0,Bool.and_self]
theorem t5_1473checked : Checked tree [8,5,5,9,10] := by
  refine ⟨plan5218,valid5218,t5_1473choices,?_⟩
  exact check_of_frontier tree 0 t5_1473root t5_1473jobs t5_1473frontier t5_1473all
theorem t5_1474choices : plan5219.choices=[8,5,5,10,7].map (options 5 5) := by rfl


theorem t5_1474part0 : t5_1474jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1474frontier : t5_1474root.frontier 0=t5_1474jobs := by rfl
theorem t5_1474all : t5_1474jobs.all (Job.check tree)=true := by
  simp only [t5_1474jobs,List.all_append,List.all_nil,t5_1474part0,Bool.and_self]
theorem t5_1474checked : Checked tree [8,5,5,10,7] := by
  refine ⟨plan5219,valid5219,t5_1474choices,?_⟩
  exact check_of_frontier tree 0 t5_1474root t5_1474jobs t5_1474frontier t5_1474all
theorem t5_1475choices : plan5220.choices=[8,5,5,10,10].map (options 5 5) := by rfl


theorem t5_1475part0 : t5_1475jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1475frontier : t5_1475root.frontier 0=t5_1475jobs := by rfl
theorem t5_1475all : t5_1475jobs.all (Job.check tree)=true := by
  simp only [t5_1475jobs,List.all_append,List.all_nil,t5_1475part0,Bool.and_self]
theorem t5_1475checked : Checked tree [8,5,5,10,10] := by
  refine ⟨plan5220,valid5220,t5_1475choices,?_⟩
  exact check_of_frontier tree 0 t5_1475root t5_1475jobs t5_1475frontier t5_1475all
theorem t5_1476choices : plan5221.choices=[8,5,6,6,6].map (options 5 5) := by rfl


theorem t5_1476part0 : t5_1476jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1476frontier : t5_1476root.frontier 0=t5_1476jobs := by rfl
theorem t5_1476all : t5_1476jobs.all (Job.check tree)=true := by
  simp only [t5_1476jobs,List.all_append,List.all_nil,t5_1476part0,Bool.and_self]
theorem t5_1476checked : Checked tree [8,5,6,6,6] := by
  refine ⟨plan5221,valid5221,t5_1476choices,?_⟩
  exact check_of_frontier tree 0 t5_1476root t5_1476jobs t5_1476frontier t5_1476all
theorem t5_1477choices : plan5222.choices=[8,5,6,6,7].map (options 5 5) := by rfl


theorem t5_1477part0 : t5_1477jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1477frontier : t5_1477root.frontier 0=t5_1477jobs := by rfl
theorem t5_1477all : t5_1477jobs.all (Job.check tree)=true := by
  simp only [t5_1477jobs,List.all_append,List.all_nil,t5_1477part0,Bool.and_self]
theorem t5_1477checked : Checked tree [8,5,6,6,7] := by
  refine ⟨plan5222,valid5222,t5_1477choices,?_⟩
  exact check_of_frontier tree 0 t5_1477root t5_1477jobs t5_1477frontier t5_1477all
theorem t5_1478choices : plan5223.choices=[8,5,6,6,10].map (options 5 5) := by rfl


theorem t5_1478part0 : t5_1478jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1478frontier : t5_1478root.frontier 0=t5_1478jobs := by rfl
theorem t5_1478all : t5_1478jobs.all (Job.check tree)=true := by
  simp only [t5_1478jobs,List.all_append,List.all_nil,t5_1478part0,Bool.and_self]
theorem t5_1478checked : Checked tree [8,5,6,6,10] := by
  refine ⟨plan5223,valid5223,t5_1478choices,?_⟩
  exact check_of_frontier tree 0 t5_1478root t5_1478jobs t5_1478frontier t5_1478all
theorem t5_1479choices : plan5224.choices=[8,5,6,7,7].map (options 5 5) := by rfl


theorem t5_1479part0 : t5_1479jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1479frontier : t5_1479root.frontier 0=t5_1479jobs := by rfl
theorem t5_1479all : t5_1479jobs.all (Job.check tree)=true := by
  simp only [t5_1479jobs,List.all_append,List.all_nil,t5_1479part0,Bool.and_self]
theorem t5_1479checked : Checked tree [8,5,6,7,7] := by
  refine ⟨plan5224,valid5224,t5_1479choices,?_⟩
  exact check_of_frontier tree 0 t5_1479root t5_1479jobs t5_1479frontier t5_1479all
theorem t5_1480choices : plan5225.choices=[8,5,6,10,7].map (options 5 5) := by rfl


theorem t5_1480part0 : t5_1480jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1480frontier : t5_1480root.frontier 0=t5_1480jobs := by rfl
theorem t5_1480all : t5_1480jobs.all (Job.check tree)=true := by
  simp only [t5_1480jobs,List.all_append,List.all_nil,t5_1480part0,Bool.and_self]
theorem t5_1480checked : Checked tree [8,5,6,10,7] := by
  refine ⟨plan5225,valid5225,t5_1480choices,?_⟩
  exact check_of_frontier tree 0 t5_1480root t5_1480jobs t5_1480frontier t5_1480all
theorem t5_1481choices : plan5226.choices=[8,5,6,10,10].map (options 5 5) := by rfl


theorem t5_1481part0 : t5_1481jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1481frontier : t5_1481root.frontier 0=t5_1481jobs := by rfl
theorem t5_1481all : t5_1481jobs.all (Job.check tree)=true := by
  simp only [t5_1481jobs,List.all_append,List.all_nil,t5_1481part0,Bool.and_self]
theorem t5_1481checked : Checked tree [8,5,6,10,10] := by
  refine ⟨plan5226,valid5226,t5_1481choices,?_⟩
  exact check_of_frontier tree 0 t5_1481root t5_1481jobs t5_1481frontier t5_1481all
theorem t5_1482choices : plan5227.choices=[8,5,7,7,7].map (options 5 5) := by rfl


theorem t5_1482part0 : t5_1482jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1482frontier : t5_1482root.frontier 0=t5_1482jobs := by rfl
theorem t5_1482all : t5_1482jobs.all (Job.check tree)=true := by
  simp only [t5_1482jobs,List.all_append,List.all_nil,t5_1482part0,Bool.and_self]
theorem t5_1482checked : Checked tree [8,5,7,7,7] := by
  refine ⟨plan5227,valid5227,t5_1482choices,?_⟩
  exact check_of_frontier tree 0 t5_1482root t5_1482jobs t5_1482frontier t5_1482all
theorem t5_1483choices : plan4426.choices=[8,5,9,3,3].map (options 5 3) := by rfl


theorem t5_1483part0 : t5_1483jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1483frontier : t5_1483root.frontier 0=t5_1483jobs := by rfl
theorem t5_1483all : t5_1483jobs.all (Job.check tree)=true := by
  simp only [t5_1483jobs,List.all_append,List.all_nil,t5_1483part0,Bool.and_self]
theorem t5_1483checked : Checked tree [8,5,9,3,3] := by
  refine ⟨plan4426,valid4426,t5_1483choices,?_⟩
  exact check_of_frontier tree 0 t5_1483root t5_1483jobs t5_1483frontier t5_1483all
theorem t5_1484choices : plan4944.choices=[8,5,9,3,6].map (options 5 4) := by rfl


theorem t5_1484part0 : t5_1484jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1484frontier : t5_1484root.frontier 0=t5_1484jobs := by rfl
theorem t5_1484all : t5_1484jobs.all (Job.check tree)=true := by
  simp only [t5_1484jobs,List.all_append,List.all_nil,t5_1484part0,Bool.and_self]
theorem t5_1484checked : Checked tree [8,5,9,3,6] := by
  refine ⟨plan4944,valid4944,t5_1484choices,?_⟩
  exact check_of_frontier tree 0 t5_1484root t5_1484jobs t5_1484frontier t5_1484all
theorem t5_1485choices : plan4945.choices=[8,5,9,3,7].map (options 5 4) := by rfl


theorem t5_1485part0 : t5_1485jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1485frontier : t5_1485root.frontier 0=t5_1485jobs := by rfl
theorem t5_1485all : t5_1485jobs.all (Job.check tree)=true := by
  simp only [t5_1485jobs,List.all_append,List.all_nil,t5_1485part0,Bool.and_self]
theorem t5_1485checked : Checked tree [8,5,9,3,7] := by
  refine ⟨plan4945,valid4945,t5_1485choices,?_⟩
  exact check_of_frontier tree 0 t5_1485root t5_1485jobs t5_1485frontier t5_1485all
theorem t5_1486choices : plan4946.choices=[8,5,9,3,10].map (options 5 4) := by rfl


theorem t5_1486part0 : t5_1486jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1486frontier : t5_1486root.frontier 0=t5_1486jobs := by rfl
theorem t5_1486all : t5_1486jobs.all (Job.check tree)=true := by
  simp only [t5_1486jobs,List.all_append,List.all_nil,t5_1486part0,Bool.and_self]
theorem t5_1486checked : Checked tree [8,5,9,3,10] := by
  refine ⟨plan4946,valid4946,t5_1486choices,?_⟩
  exact check_of_frontier tree 0 t5_1486root t5_1486jobs t5_1486frontier t5_1486all
theorem t5_1487choices : plan5228.choices=[8,5,9,6,6].map (options 5 5) := by rfl


theorem t5_1487part0 : t5_1487jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1487frontier : t5_1487root.frontier 0=t5_1487jobs := by rfl
theorem t5_1487all : t5_1487jobs.all (Job.check tree)=true := by
  simp only [t5_1487jobs,List.all_append,List.all_nil,t5_1487part0,Bool.and_self]
theorem t5_1487checked : Checked tree [8,5,9,6,6] := by
  refine ⟨plan5228,valid5228,t5_1487choices,?_⟩
  exact check_of_frontier tree 0 t5_1487root t5_1487jobs t5_1487frontier t5_1487all
theorem t5_1488choices : plan5229.choices=[8,5,9,6,7].map (options 5 5) := by rfl


theorem t5_1488part0 : t5_1488jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1488frontier : t5_1488root.frontier 0=t5_1488jobs := by rfl
theorem t5_1488all : t5_1488jobs.all (Job.check tree)=true := by
  simp only [t5_1488jobs,List.all_append,List.all_nil,t5_1488part0,Bool.and_self]
theorem t5_1488checked : Checked tree [8,5,9,6,7] := by
  refine ⟨plan5229,valid5229,t5_1488choices,?_⟩
  exact check_of_frontier tree 0 t5_1488root t5_1488jobs t5_1488frontier t5_1488all
theorem t5_1489choices : plan5230.choices=[8,5,9,6,10].map (options 5 5) := by rfl


theorem t5_1489part0 : t5_1489jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1489frontier : t5_1489root.frontier 0=t5_1489jobs := by rfl
theorem t5_1489all : t5_1489jobs.all (Job.check tree)=true := by
  simp only [t5_1489jobs,List.all_append,List.all_nil,t5_1489part0,Bool.and_self]
theorem t5_1489checked : Checked tree [8,5,9,6,10] := by
  refine ⟨plan5230,valid5230,t5_1489choices,?_⟩
  exact check_of_frontier tree 0 t5_1489root t5_1489jobs t5_1489frontier t5_1489all
theorem t5_1490choices : plan5231.choices=[8,5,9,7,7].map (options 5 5) := by rfl


theorem t5_1490part0 : t5_1490jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1490frontier : t5_1490root.frontier 0=t5_1490jobs := by rfl
theorem t5_1490all : t5_1490jobs.all (Job.check tree)=true := by
  simp only [t5_1490jobs,List.all_append,List.all_nil,t5_1490part0,Bool.and_self]
theorem t5_1490checked : Checked tree [8,5,9,7,7] := by
  refine ⟨plan5231,valid5231,t5_1490choices,?_⟩
  exact check_of_frontier tree 0 t5_1490root t5_1490jobs t5_1490frontier t5_1490all
theorem t5_1491choices : plan4947.choices=[8,5,9,9,3].map (options 5 4) := by rfl


theorem t5_1491part0 : t5_1491jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1491frontier : t5_1491root.frontier 0=t5_1491jobs := by rfl
theorem t5_1491all : t5_1491jobs.all (Job.check tree)=true := by
  simp only [t5_1491jobs,List.all_append,List.all_nil,t5_1491part0,Bool.and_self]
theorem t5_1491checked : Checked tree [8,5,9,9,3] := by
  refine ⟨plan4947,valid4947,t5_1491choices,?_⟩
  exact check_of_frontier tree 0 t5_1491root t5_1491jobs t5_1491frontier t5_1491all
theorem t5_1492choices : plan5232.choices=[8,5,9,9,6].map (options 5 5) := by rfl


theorem t5_1492part0 : t5_1492jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1492frontier : t5_1492root.frontier 0=t5_1492jobs := by rfl
theorem t5_1492all : t5_1492jobs.all (Job.check tree)=true := by
  simp only [t5_1492jobs,List.all_append,List.all_nil,t5_1492part0,Bool.and_self]
theorem t5_1492checked : Checked tree [8,5,9,9,6] := by
  refine ⟨plan5232,valid5232,t5_1492choices,?_⟩
  exact check_of_frontier tree 0 t5_1492root t5_1492jobs t5_1492frontier t5_1492all
theorem t5_1493choices : plan5233.choices=[8,5,9,9,7].map (options 5 5) := by rfl


theorem t5_1493part0 : t5_1493jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1493frontier : t5_1493root.frontier 0=t5_1493jobs := by rfl
theorem t5_1493all : t5_1493jobs.all (Job.check tree)=true := by
  simp only [t5_1493jobs,List.all_append,List.all_nil,t5_1493part0,Bool.and_self]
theorem t5_1493checked : Checked tree [8,5,9,9,7] := by
  refine ⟨plan5233,valid5233,t5_1493choices,?_⟩
  exact check_of_frontier tree 0 t5_1493root t5_1493jobs t5_1493frontier t5_1493all
theorem t5_1494choices : plan5234.choices=[8,5,9,9,10].map (options 5 5) := by rfl


theorem t5_1494part0 : t5_1494jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1494frontier : t5_1494root.frontier 0=t5_1494jobs := by rfl
theorem t5_1494all : t5_1494jobs.all (Job.check tree)=true := by
  simp only [t5_1494jobs,List.all_append,List.all_nil,t5_1494part0,Bool.and_self]
theorem t5_1494checked : Checked tree [8,5,9,9,10] := by
  refine ⟨plan5234,valid5234,t5_1494choices,?_⟩
  exact check_of_frontier tree 0 t5_1494root t5_1494jobs t5_1494frontier t5_1494all
theorem t5_1495choices : plan5235.choices=[8,5,9,10,7].map (options 5 5) := by rfl


theorem t5_1495part0 : t5_1495jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1495frontier : t5_1495root.frontier 0=t5_1495jobs := by rfl
theorem t5_1495all : t5_1495jobs.all (Job.check tree)=true := by
  simp only [t5_1495jobs,List.all_append,List.all_nil,t5_1495part0,Bool.and_self]
theorem t5_1495checked : Checked tree [8,5,9,10,7] := by
  refine ⟨plan5235,valid5235,t5_1495choices,?_⟩
  exact check_of_frontier tree 0 t5_1495root t5_1495jobs t5_1495frontier t5_1495all
theorem t5_1496choices : plan5236.choices=[8,5,9,10,10].map (options 5 5) := by rfl


theorem t5_1496part0 : t5_1496jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1496frontier : t5_1496root.frontier 0=t5_1496jobs := by rfl
theorem t5_1496all : t5_1496jobs.all (Job.check tree)=true := by
  simp only [t5_1496jobs,List.all_append,List.all_nil,t5_1496part0,Bool.and_self]
theorem t5_1496checked : Checked tree [8,5,9,10,10] := by
  refine ⟨plan5236,valid5236,t5_1496choices,?_⟩
  exact check_of_frontier tree 0 t5_1496root t5_1496jobs t5_1496frontier t5_1496all
theorem t5_1497choices : plan5237.choices=[8,5,10,7,7].map (options 5 5) := by rfl


theorem t5_1497part0 : t5_1497jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1497frontier : t5_1497root.frontier 0=t5_1497jobs := by rfl
theorem t5_1497all : t5_1497jobs.all (Job.check tree)=true := by
  simp only [t5_1497jobs,List.all_append,List.all_nil,t5_1497part0,Bool.and_self]
theorem t5_1497checked : Checked tree [8,5,10,7,7] := by
  refine ⟨plan5237,valid5237,t5_1497choices,?_⟩
  exact check_of_frontier tree 0 t5_1497root t5_1497jobs t5_1497frontier t5_1497all
theorem t5_1498choices : plan5238.choices=[8,5,10,10,7].map (options 5 5) := by rfl


theorem t5_1498part0 : t5_1498jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1498frontier : t5_1498root.frontier 0=t5_1498jobs := by rfl
theorem t5_1498all : t5_1498jobs.all (Job.check tree)=true := by
  simp only [t5_1498jobs,List.all_append,List.all_nil,t5_1498part0,Bool.and_self]
theorem t5_1498checked : Checked tree [8,5,10,10,7] := by
  refine ⟨plan5238,valid5238,t5_1498choices,?_⟩
  exact check_of_frontier tree 0 t5_1498root t5_1498jobs t5_1498frontier t5_1498all
theorem t5_1499choices : plan5239.choices=[8,5,10,10,10].map (options 5 5) := by rfl


theorem t5_1499part0 : t5_1499jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1499frontier : t5_1499root.frontier 0=t5_1499jobs := by rfl
theorem t5_1499all : t5_1499jobs.all (Job.check tree)=true := by
  simp only [t5_1499jobs,List.all_append,List.all_nil,t5_1499part0,Bool.and_self]
theorem t5_1499checked : Checked tree [8,5,10,10,10] := by
  refine ⟨plan5239,valid5239,t5_1499choices,?_⟩
  exact check_of_frontier tree 0 t5_1499root t5_1499jobs t5_1499frontier t5_1499all
theorem t5_1500choices : plan5240.choices=[8,6,6,6,6].map (options 5 5) := by rfl


theorem t5_1500part0 : t5_1500jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1500frontier : t5_1500root.frontier 0=t5_1500jobs := by rfl
theorem t5_1500all : t5_1500jobs.all (Job.check tree)=true := by
  simp only [t5_1500jobs,List.all_append,List.all_nil,t5_1500part0,Bool.and_self]
theorem t5_1500checked : Checked tree [8,6,6,6,6] := by
  refine ⟨plan5240,valid5240,t5_1500choices,?_⟩
  exact check_of_frontier tree 0 t5_1500root t5_1500jobs t5_1500frontier t5_1500all
theorem t5_1501choices : plan5241.choices=[8,6,6,6,7].map (options 5 5) := by rfl


theorem t5_1501part0 : t5_1501jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1501frontier : t5_1501root.frontier 0=t5_1501jobs := by rfl
theorem t5_1501all : t5_1501jobs.all (Job.check tree)=true := by
  simp only [t5_1501jobs,List.all_append,List.all_nil,t5_1501part0,Bool.and_self]
theorem t5_1501checked : Checked tree [8,6,6,6,7] := by
  refine ⟨plan5241,valid5241,t5_1501choices,?_⟩
  exact check_of_frontier tree 0 t5_1501root t5_1501jobs t5_1501frontier t5_1501all
theorem t5_1502choices : plan5242.choices=[8,6,6,6,10].map (options 5 5) := by rfl


theorem t5_1502part0 : t5_1502jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1502frontier : t5_1502root.frontier 0=t5_1502jobs := by rfl
theorem t5_1502all : t5_1502jobs.all (Job.check tree)=true := by
  simp only [t5_1502jobs,List.all_append,List.all_nil,t5_1502part0,Bool.and_self]
theorem t5_1502checked : Checked tree [8,6,6,6,10] := by
  refine ⟨plan5242,valid5242,t5_1502choices,?_⟩
  exact check_of_frontier tree 0 t5_1502root t5_1502jobs t5_1502frontier t5_1502all
theorem t5_1503choices : plan5243.choices=[8,6,6,7,7].map (options 5 5) := by rfl


theorem t5_1503part0 : t5_1503jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1503frontier : t5_1503root.frontier 0=t5_1503jobs := by rfl
theorem t5_1503all : t5_1503jobs.all (Job.check tree)=true := by
  simp only [t5_1503jobs,List.all_append,List.all_nil,t5_1503part0,Bool.and_self]
theorem t5_1503checked : Checked tree [8,6,6,7,7] := by
  refine ⟨plan5243,valid5243,t5_1503choices,?_⟩
  exact check_of_frontier tree 0 t5_1503root t5_1503jobs t5_1503frontier t5_1503all
theorem t5_1504choices : plan5244.choices=[8,6,6,10,7].map (options 5 5) := by rfl


theorem t5_1504part0 : t5_1504jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1504frontier : t5_1504root.frontier 0=t5_1504jobs := by rfl
theorem t5_1504all : t5_1504jobs.all (Job.check tree)=true := by
  simp only [t5_1504jobs,List.all_append,List.all_nil,t5_1504part0,Bool.and_self]
theorem t5_1504checked : Checked tree [8,6,6,10,7] := by
  refine ⟨plan5244,valid5244,t5_1504choices,?_⟩
  exact check_of_frontier tree 0 t5_1504root t5_1504jobs t5_1504frontier t5_1504all
theorem t5_1505choices : plan5245.choices=[8,6,6,10,10].map (options 5 5) := by rfl


theorem t5_1505part0 : t5_1505jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1505frontier : t5_1505root.frontier 0=t5_1505jobs := by rfl
theorem t5_1505all : t5_1505jobs.all (Job.check tree)=true := by
  simp only [t5_1505jobs,List.all_append,List.all_nil,t5_1505part0,Bool.and_self]
theorem t5_1505checked : Checked tree [8,6,6,10,10] := by
  refine ⟨plan5245,valid5245,t5_1505choices,?_⟩
  exact check_of_frontier tree 0 t5_1505root t5_1505jobs t5_1505frontier t5_1505all
theorem t5_1506choices : plan5246.choices=[8,6,7,7,7].map (options 5 5) := by rfl


theorem t5_1506part0 : t5_1506jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1506frontier : t5_1506root.frontier 0=t5_1506jobs := by rfl
theorem t5_1506all : t5_1506jobs.all (Job.check tree)=true := by
  simp only [t5_1506jobs,List.all_append,List.all_nil,t5_1506part0,Bool.and_self]
theorem t5_1506checked : Checked tree [8,6,7,7,7] := by
  refine ⟨plan5246,valid5246,t5_1506choices,?_⟩
  exact check_of_frontier tree 0 t5_1506root t5_1506jobs t5_1506frontier t5_1506all
theorem t5_1507choices : plan5247.choices=[8,6,10,7,7].map (options 5 5) := by rfl


theorem t5_1507part0 : t5_1507jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1507frontier : t5_1507root.frontier 0=t5_1507jobs := by rfl
theorem t5_1507all : t5_1507jobs.all (Job.check tree)=true := by
  simp only [t5_1507jobs,List.all_append,List.all_nil,t5_1507part0,Bool.and_self]
theorem t5_1507checked : Checked tree [8,6,10,7,7] := by
  refine ⟨plan5247,valid5247,t5_1507choices,?_⟩
  exact check_of_frontier tree 0 t5_1507root t5_1507jobs t5_1507frontier t5_1507all
theorem t5_1508choices : plan5248.choices=[8,6,10,10,7].map (options 5 5) := by rfl


theorem t5_1508part0 : t5_1508jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1508frontier : t5_1508root.frontier 0=t5_1508jobs := by rfl
theorem t5_1508all : t5_1508jobs.all (Job.check tree)=true := by
  simp only [t5_1508jobs,List.all_append,List.all_nil,t5_1508part0,Bool.and_self]
theorem t5_1508checked : Checked tree [8,6,10,10,7] := by
  refine ⟨plan5248,valid5248,t5_1508choices,?_⟩
  exact check_of_frontier tree 0 t5_1508root t5_1508jobs t5_1508frontier t5_1508all
theorem t5_1509choices : plan5249.choices=[8,6,10,10,10].map (options 5 5) := by rfl


theorem t5_1509part0 : t5_1509jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1509frontier : t5_1509root.frontier 0=t5_1509jobs := by rfl
theorem t5_1509all : t5_1509jobs.all (Job.check tree)=true := by
  simp only [t5_1509jobs,List.all_append,List.all_nil,t5_1509part0,Bool.and_self]
theorem t5_1509checked : Checked tree [8,6,10,10,10] := by
  refine ⟨plan5249,valid5249,t5_1509choices,?_⟩
  exact check_of_frontier tree 0 t5_1509root t5_1509jobs t5_1509frontier t5_1509all
theorem t5_1510choices : plan5250.choices=[8,7,7,7,7].map (options 5 5) := by rfl


theorem t5_1510part0 : t5_1510jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1510frontier : t5_1510root.frontier 0=t5_1510jobs := by rfl
theorem t5_1510all : t5_1510jobs.all (Job.check tree)=true := by
  simp only [t5_1510jobs,List.all_append,List.all_nil,t5_1510part0,Bool.and_self]
theorem t5_1510checked : Checked tree [8,7,7,7,7] := by
  refine ⟨plan5250,valid5250,t5_1510choices,?_⟩
  exact check_of_frontier tree 0 t5_1510root t5_1510jobs t5_1510frontier t5_1510all
theorem t5_1511choices : plan4427.choices=[8,8,2,2,7].map (options 5 3) := by rfl


theorem t5_1511part0 : t5_1511jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1511frontier : t5_1511root.frontier 0=t5_1511jobs := by rfl
theorem t5_1511all : t5_1511jobs.all (Job.check tree)=true := by
  simp only [t5_1511jobs,List.all_append,List.all_nil,t5_1511part0,Bool.and_self]
theorem t5_1511checked : Checked tree [8,8,2,2,7] := by
  refine ⟨plan4427,valid4427,t5_1511choices,?_⟩
  exact check_of_frontier tree 0 t5_1511root t5_1511jobs t5_1511frontier t5_1511all
theorem t5_1512choices : plan3993.choices=[8,8,2,3,3].map (options 5 2) := by rfl


theorem t5_1512part0 : t5_1512jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1512frontier : t5_1512root.frontier 0=t5_1512jobs := by rfl
theorem t5_1512all : t5_1512jobs.all (Job.check tree)=true := by
  simp only [t5_1512jobs,List.all_append,List.all_nil,t5_1512part0,Bool.and_self]
theorem t5_1512checked : Checked tree [8,8,2,3,3] := by
  refine ⟨plan3993,valid3993,t5_1512choices,?_⟩
  exact check_of_frontier tree 0 t5_1512root t5_1512jobs t5_1512frontier t5_1512all
theorem t5_1513choices : plan4428.choices=[8,8,2,3,6].map (options 5 3) := by rfl


theorem t5_1513part0 : t5_1513jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1513frontier : t5_1513root.frontier 0=t5_1513jobs := by rfl
theorem t5_1513all : t5_1513jobs.all (Job.check tree)=true := by
  simp only [t5_1513jobs,List.all_append,List.all_nil,t5_1513part0,Bool.and_self]
theorem t5_1513checked : Checked tree [8,8,2,3,6] := by
  refine ⟨plan4428,valid4428,t5_1513choices,?_⟩
  exact check_of_frontier tree 0 t5_1513root t5_1513jobs t5_1513frontier t5_1513all
theorem t5_1514choices : plan4429.choices=[8,8,2,3,7].map (options 5 3) := by rfl


theorem t5_1514part0 : t5_1514jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1514frontier : t5_1514root.frontier 0=t5_1514jobs := by rfl
theorem t5_1514all : t5_1514jobs.all (Job.check tree)=true := by
  simp only [t5_1514jobs,List.all_append,List.all_nil,t5_1514part0,Bool.and_self]
theorem t5_1514checked : Checked tree [8,8,2,3,7] := by
  refine ⟨plan4429,valid4429,t5_1514choices,?_⟩
  exact check_of_frontier tree 0 t5_1514root t5_1514jobs t5_1514frontier t5_1514all
theorem t5_1515choices : plan4430.choices=[8,8,2,3,10].map (options 5 3) := by rfl


theorem t5_1515part0 : t5_1515jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1515frontier : t5_1515root.frontier 0=t5_1515jobs := by rfl
theorem t5_1515all : t5_1515jobs.all (Job.check tree)=true := by
  simp only [t5_1515jobs,List.all_append,List.all_nil,t5_1515part0,Bool.and_self]
theorem t5_1515checked : Checked tree [8,8,2,3,10] := by
  refine ⟨plan4430,valid4430,t5_1515choices,?_⟩
  exact check_of_frontier tree 0 t5_1515root t5_1515jobs t5_1515frontier t5_1515all
theorem t5_1516choices : plan4948.choices=[8,8,2,5,7].map (options 5 4) := by rfl


theorem t5_1516part0 : t5_1516jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1516frontier : t5_1516root.frontier 0=t5_1516jobs := by rfl
theorem t5_1516all : t5_1516jobs.all (Job.check tree)=true := by
  simp only [t5_1516jobs,List.all_append,List.all_nil,t5_1516part0,Bool.and_self]
theorem t5_1516checked : Checked tree [8,8,2,5,7] := by
  refine ⟨plan4948,valid4948,t5_1516choices,?_⟩
  exact check_of_frontier tree 0 t5_1516root t5_1516jobs t5_1516frontier t5_1516all
theorem t5_1517choices : plan4949.choices=[8,8,2,6,6].map (options 5 4) := by rfl


theorem t5_1517part0 : t5_1517jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1517frontier : t5_1517root.frontier 0=t5_1517jobs := by rfl
theorem t5_1517all : t5_1517jobs.all (Job.check tree)=true := by
  simp only [t5_1517jobs,List.all_append,List.all_nil,t5_1517part0,Bool.and_self]
theorem t5_1517checked : Checked tree [8,8,2,6,6] := by
  refine ⟨plan4949,valid4949,t5_1517choices,?_⟩
  exact check_of_frontier tree 0 t5_1517root t5_1517jobs t5_1517frontier t5_1517all
theorem t5_1518choices : plan4950.choices=[8,8,2,6,7].map (options 5 4) := by rfl


theorem t5_1518part0 : t5_1518jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1518frontier : t5_1518root.frontier 0=t5_1518jobs := by rfl
theorem t5_1518all : t5_1518jobs.all (Job.check tree)=true := by
  simp only [t5_1518jobs,List.all_append,List.all_nil,t5_1518part0,Bool.and_self]
theorem t5_1518checked : Checked tree [8,8,2,6,7] := by
  refine ⟨plan4950,valid4950,t5_1518choices,?_⟩
  exact check_of_frontier tree 0 t5_1518root t5_1518jobs t5_1518frontier t5_1518all
theorem t5_1519choices : plan4951.choices=[8,8,2,6,10].map (options 5 4) := by rfl


theorem t5_1519part0 : t5_1519jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1519frontier : t5_1519root.frontier 0=t5_1519jobs := by rfl
theorem t5_1519all : t5_1519jobs.all (Job.check tree)=true := by
  simp only [t5_1519jobs,List.all_append,List.all_nil,t5_1519part0,Bool.and_self]
theorem t5_1519checked : Checked tree [8,8,2,6,10] := by
  refine ⟨plan4951,valid4951,t5_1519choices,?_⟩
  exact check_of_frontier tree 0 t5_1519root t5_1519jobs t5_1519frontier t5_1519all
theorem t5_1520choices : plan4952.choices=[8,8,2,7,7].map (options 5 4) := by rfl


theorem t5_1520part0 : t5_1520jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1520frontier : t5_1520root.frontier 0=t5_1520jobs := by rfl
theorem t5_1520all : t5_1520jobs.all (Job.check tree)=true := by
  simp only [t5_1520jobs,List.all_append,List.all_nil,t5_1520part0,Bool.and_self]
theorem t5_1520checked : Checked tree [8,8,2,7,7] := by
  refine ⟨plan4952,valid4952,t5_1520choices,?_⟩
  exact check_of_frontier tree 0 t5_1520root t5_1520jobs t5_1520frontier t5_1520all
theorem t5_1521choices : plan4953.choices=[8,8,2,9,7].map (options 5 4) := by rfl


theorem t5_1521part0 : t5_1521jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1521frontier : t5_1521root.frontier 0=t5_1521jobs := by rfl
theorem t5_1521all : t5_1521jobs.all (Job.check tree)=true := by
  simp only [t5_1521jobs,List.all_append,List.all_nil,t5_1521part0,Bool.and_self]
theorem t5_1521checked : Checked tree [8,8,2,9,7] := by
  refine ⟨plan4953,valid4953,t5_1521choices,?_⟩
  exact check_of_frontier tree 0 t5_1521root t5_1521jobs t5_1521frontier t5_1521all
theorem t5_1522choices : plan4954.choices=[8,8,2,10,7].map (options 5 4) := by rfl


theorem t5_1522part0 : t5_1522jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1522frontier : t5_1522root.frontier 0=t5_1522jobs := by rfl
theorem t5_1522all : t5_1522jobs.all (Job.check tree)=true := by
  simp only [t5_1522jobs,List.all_append,List.all_nil,t5_1522part0,Bool.and_self]
theorem t5_1522checked : Checked tree [8,8,2,10,7] := by
  refine ⟨plan4954,valid4954,t5_1522choices,?_⟩
  exact check_of_frontier tree 0 t5_1522root t5_1522jobs t5_1522frontier t5_1522all
theorem t5_1523choices : plan4955.choices=[8,8,2,10,10].map (options 5 4) := by rfl


theorem t5_1523part0 : t5_1523jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1523frontier : t5_1523root.frontier 0=t5_1523jobs := by rfl
theorem t5_1523all : t5_1523jobs.all (Job.check tree)=true := by
  simp only [t5_1523jobs,List.all_append,List.all_nil,t5_1523part0,Bool.and_self]
theorem t5_1523checked : Checked tree [8,8,2,10,10] := by
  refine ⟨plan4955,valid4955,t5_1523choices,?_⟩
  exact check_of_frontier tree 0 t5_1523root t5_1523jobs t5_1523frontier t5_1523all
theorem t5_1524choices : plan3994.choices=[8,8,3,3,3].map (options 5 2) := by rfl


theorem t5_1524part0 : t5_1524jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1524frontier : t5_1524root.frontier 0=t5_1524jobs := by rfl
theorem t5_1524all : t5_1524jobs.all (Job.check tree)=true := by
  simp only [t5_1524jobs,List.all_append,List.all_nil,t5_1524part0,Bool.and_self]
theorem t5_1524checked : Checked tree [8,8,3,3,3] := by
  refine ⟨plan3994,valid3994,t5_1524choices,?_⟩
  exact check_of_frontier tree 0 t5_1524root t5_1524jobs t5_1524frontier t5_1524all
theorem t5_1525choices : plan4431.choices=[8,8,3,3,6].map (options 5 3) := by rfl


theorem t5_1525part0 : t5_1525jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1525frontier : t5_1525root.frontier 0=t5_1525jobs := by rfl
theorem t5_1525all : t5_1525jobs.all (Job.check tree)=true := by
  simp only [t5_1525jobs,List.all_append,List.all_nil,t5_1525part0,Bool.and_self]
theorem t5_1525checked : Checked tree [8,8,3,3,6] := by
  refine ⟨plan4431,valid4431,t5_1525choices,?_⟩
  exact check_of_frontier tree 0 t5_1525root t5_1525jobs t5_1525frontier t5_1525all
theorem t5_1526choices : plan4432.choices=[8,8,3,3,7].map (options 5 3) := by rfl


theorem t5_1526part0 : t5_1526jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1526frontier : t5_1526root.frontier 0=t5_1526jobs := by rfl
theorem t5_1526all : t5_1526jobs.all (Job.check tree)=true := by
  simp only [t5_1526jobs,List.all_append,List.all_nil,t5_1526part0,Bool.and_self]
theorem t5_1526checked : Checked tree [8,8,3,3,7] := by
  refine ⟨plan4432,valid4432,t5_1526choices,?_⟩
  exact check_of_frontier tree 0 t5_1526root t5_1526jobs t5_1526frontier t5_1526all
theorem t5_1527choices : plan4433.choices=[8,8,3,3,10].map (options 5 3) := by rfl


theorem t5_1527part0 : t5_1527jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1527frontier : t5_1527root.frontier 0=t5_1527jobs := by rfl
theorem t5_1527all : t5_1527jobs.all (Job.check tree)=true := by
  simp only [t5_1527jobs,List.all_append,List.all_nil,t5_1527part0,Bool.and_self]
theorem t5_1527checked : Checked tree [8,8,3,3,10] := by
  refine ⟨plan4433,valid4433,t5_1527choices,?_⟩
  exact check_of_frontier tree 0 t5_1527root t5_1527jobs t5_1527frontier t5_1527all
theorem t5_1528choices : plan4956.choices=[8,8,3,6,6].map (options 5 4) := by rfl


theorem t5_1528part0 : t5_1528jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1528frontier : t5_1528root.frontier 0=t5_1528jobs := by rfl
theorem t5_1528all : t5_1528jobs.all (Job.check tree)=true := by
  simp only [t5_1528jobs,List.all_append,List.all_nil,t5_1528part0,Bool.and_self]
theorem t5_1528checked : Checked tree [8,8,3,6,6] := by
  refine ⟨plan4956,valid4956,t5_1528choices,?_⟩
  exact check_of_frontier tree 0 t5_1528root t5_1528jobs t5_1528frontier t5_1528all
theorem t5_1529choices : plan4957.choices=[8,8,3,6,7].map (options 5 4) := by rfl


theorem t5_1529part0 : t5_1529jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1529frontier : t5_1529root.frontier 0=t5_1529jobs := by rfl
theorem t5_1529all : t5_1529jobs.all (Job.check tree)=true := by
  simp only [t5_1529jobs,List.all_append,List.all_nil,t5_1529part0,Bool.and_self]
theorem t5_1529checked : Checked tree [8,8,3,6,7] := by
  refine ⟨plan4957,valid4957,t5_1529choices,?_⟩
  exact check_of_frontier tree 0 t5_1529root t5_1529jobs t5_1529frontier t5_1529all
theorem t5_1530choices : plan4958.choices=[8,8,3,6,10].map (options 5 4) := by rfl


theorem t5_1530part0 : t5_1530jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1530frontier : t5_1530root.frontier 0=t5_1530jobs := by rfl
theorem t5_1530all : t5_1530jobs.all (Job.check tree)=true := by
  simp only [t5_1530jobs,List.all_append,List.all_nil,t5_1530part0,Bool.and_self]
theorem t5_1530checked : Checked tree [8,8,3,6,10] := by
  refine ⟨plan4958,valid4958,t5_1530choices,?_⟩
  exact check_of_frontier tree 0 t5_1530root t5_1530jobs t5_1530frontier t5_1530all
theorem t5_1531choices : plan4959.choices=[8,8,3,7,7].map (options 5 4) := by rfl


theorem t5_1531part0 : t5_1531jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1531frontier : t5_1531root.frontier 0=t5_1531jobs := by rfl
theorem t5_1531all : t5_1531jobs.all (Job.check tree)=true := by
  simp only [t5_1531jobs,List.all_append,List.all_nil,t5_1531part0,Bool.and_self]
theorem t5_1531checked : Checked tree [8,8,3,7,7] := by
  refine ⟨plan4959,valid4959,t5_1531choices,?_⟩
  exact check_of_frontier tree 0 t5_1531root t5_1531jobs t5_1531frontier t5_1531all
theorem t5_1532choices : plan4960.choices=[8,8,3,10,7].map (options 5 4) := by rfl


theorem t5_1532part0 : t5_1532jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1532frontier : t5_1532root.frontier 0=t5_1532jobs := by rfl
theorem t5_1532all : t5_1532jobs.all (Job.check tree)=true := by
  simp only [t5_1532jobs,List.all_append,List.all_nil,t5_1532part0,Bool.and_self]
theorem t5_1532checked : Checked tree [8,8,3,10,7] := by
  refine ⟨plan4960,valid4960,t5_1532choices,?_⟩
  exact check_of_frontier tree 0 t5_1532root t5_1532jobs t5_1532frontier t5_1532all
theorem t5_1533choices : plan4961.choices=[8,8,3,10,10].map (options 5 4) := by rfl


theorem t5_1533part0 : t5_1533jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1533frontier : t5_1533root.frontier 0=t5_1533jobs := by rfl
theorem t5_1533all : t5_1533jobs.all (Job.check tree)=true := by
  simp only [t5_1533jobs,List.all_append,List.all_nil,t5_1533part0,Bool.and_self]
theorem t5_1533checked : Checked tree [8,8,3,10,10] := by
  refine ⟨plan4961,valid4961,t5_1533choices,?_⟩
  exact check_of_frontier tree 0 t5_1533root t5_1533jobs t5_1533frontier t5_1533all
theorem t5_1534choices : plan4434.choices=[8,8,5,3,3].map (options 5 3) := by rfl


theorem t5_1534part0 : t5_1534jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1534frontier : t5_1534root.frontier 0=t5_1534jobs := by rfl
theorem t5_1534all : t5_1534jobs.all (Job.check tree)=true := by
  simp only [t5_1534jobs,List.all_append,List.all_nil,t5_1534part0,Bool.and_self]
theorem t5_1534checked : Checked tree [8,8,5,3,3] := by
  refine ⟨plan4434,valid4434,t5_1534choices,?_⟩
  exact check_of_frontier tree 0 t5_1534root t5_1534jobs t5_1534frontier t5_1534all
theorem t5_1535choices : plan4962.choices=[8,8,5,3,6].map (options 5 4) := by rfl


theorem t5_1535part0 : t5_1535jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1535frontier : t5_1535root.frontier 0=t5_1535jobs := by rfl
theorem t5_1535all : t5_1535jobs.all (Job.check tree)=true := by
  simp only [t5_1535jobs,List.all_append,List.all_nil,t5_1535part0,Bool.and_self]
theorem t5_1535checked : Checked tree [8,8,5,3,6] := by
  refine ⟨plan4962,valid4962,t5_1535choices,?_⟩
  exact check_of_frontier tree 0 t5_1535root t5_1535jobs t5_1535frontier t5_1535all
theorem t5_1536choices : plan4963.choices=[8,8,5,3,7].map (options 5 4) := by rfl


theorem t5_1536part0 : t5_1536jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1536frontier : t5_1536root.frontier 0=t5_1536jobs := by rfl
theorem t5_1536all : t5_1536jobs.all (Job.check tree)=true := by
  simp only [t5_1536jobs,List.all_append,List.all_nil,t5_1536part0,Bool.and_self]
theorem t5_1536checked : Checked tree [8,8,5,3,7] := by
  refine ⟨plan4963,valid4963,t5_1536choices,?_⟩
  exact check_of_frontier tree 0 t5_1536root t5_1536jobs t5_1536frontier t5_1536all
theorem t5_1537choices : plan4964.choices=[8,8,5,3,10].map (options 5 4) := by rfl


theorem t5_1537part0 : t5_1537jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1537frontier : t5_1537root.frontier 0=t5_1537jobs := by rfl
theorem t5_1537all : t5_1537jobs.all (Job.check tree)=true := by
  simp only [t5_1537jobs,List.all_append,List.all_nil,t5_1537part0,Bool.and_self]
theorem t5_1537checked : Checked tree [8,8,5,3,10] := by
  refine ⟨plan4964,valid4964,t5_1537choices,?_⟩
  exact check_of_frontier tree 0 t5_1537root t5_1537jobs t5_1537frontier t5_1537all
theorem t5_1538choices : plan5251.choices=[8,8,5,5,7].map (options 5 5) := by rfl


theorem t5_1538part0 : t5_1538jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1538frontier : t5_1538root.frontier 0=t5_1538jobs := by rfl
theorem t5_1538all : t5_1538jobs.all (Job.check tree)=true := by
  simp only [t5_1538jobs,List.all_append,List.all_nil,t5_1538part0,Bool.and_self]
theorem t5_1538checked : Checked tree [8,8,5,5,7] := by
  refine ⟨plan5251,valid5251,t5_1538choices,?_⟩
  exact check_of_frontier tree 0 t5_1538root t5_1538jobs t5_1538frontier t5_1538all
theorem t5_1539choices : plan5252.choices=[8,8,5,6,6].map (options 5 5) := by rfl


theorem t5_1539part0 : t5_1539jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1539frontier : t5_1539root.frontier 0=t5_1539jobs := by rfl
theorem t5_1539all : t5_1539jobs.all (Job.check tree)=true := by
  simp only [t5_1539jobs,List.all_append,List.all_nil,t5_1539part0,Bool.and_self]
theorem t5_1539checked : Checked tree [8,8,5,6,6] := by
  refine ⟨plan5252,valid5252,t5_1539choices,?_⟩
  exact check_of_frontier tree 0 t5_1539root t5_1539jobs t5_1539frontier t5_1539all
theorem t5_1540choices : plan5253.choices=[8,8,5,6,7].map (options 5 5) := by rfl


theorem t5_1540part0 : t5_1540jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1540frontier : t5_1540root.frontier 0=t5_1540jobs := by rfl
theorem t5_1540all : t5_1540jobs.all (Job.check tree)=true := by
  simp only [t5_1540jobs,List.all_append,List.all_nil,t5_1540part0,Bool.and_self]
theorem t5_1540checked : Checked tree [8,8,5,6,7] := by
  refine ⟨plan5253,valid5253,t5_1540choices,?_⟩
  exact check_of_frontier tree 0 t5_1540root t5_1540jobs t5_1540frontier t5_1540all
theorem t5_1541choices : plan5254.choices=[8,8,5,6,10].map (options 5 5) := by rfl


theorem t5_1541part0 : t5_1541jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1541frontier : t5_1541root.frontier 0=t5_1541jobs := by rfl
theorem t5_1541all : t5_1541jobs.all (Job.check tree)=true := by
  simp only [t5_1541jobs,List.all_append,List.all_nil,t5_1541part0,Bool.and_self]
theorem t5_1541checked : Checked tree [8,8,5,6,10] := by
  refine ⟨plan5254,valid5254,t5_1541choices,?_⟩
  exact check_of_frontier tree 0 t5_1541root t5_1541jobs t5_1541frontier t5_1541all
theorem t5_1542choices : plan5255.choices=[8,8,5,7,7].map (options 5 5) := by rfl


theorem t5_1542part0 : t5_1542jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1542frontier : t5_1542root.frontier 0=t5_1542jobs := by rfl
theorem t5_1542all : t5_1542jobs.all (Job.check tree)=true := by
  simp only [t5_1542jobs,List.all_append,List.all_nil,t5_1542part0,Bool.and_self]
theorem t5_1542checked : Checked tree [8,8,5,7,7] := by
  refine ⟨plan5255,valid5255,t5_1542choices,?_⟩
  exact check_of_frontier tree 0 t5_1542root t5_1542jobs t5_1542frontier t5_1542all
theorem t5_1543choices : plan5256.choices=[8,8,5,9,7].map (options 5 5) := by rfl


theorem t5_1543part0 : t5_1543jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1543frontier : t5_1543root.frontier 0=t5_1543jobs := by rfl
theorem t5_1543all : t5_1543jobs.all (Job.check tree)=true := by
  simp only [t5_1543jobs,List.all_append,List.all_nil,t5_1543part0,Bool.and_self]
theorem t5_1543checked : Checked tree [8,8,5,9,7] := by
  refine ⟨plan5256,valid5256,t5_1543choices,?_⟩
  exact check_of_frontier tree 0 t5_1543root t5_1543jobs t5_1543frontier t5_1543all
theorem t5_1544choices : plan5257.choices=[8,8,5,10,7].map (options 5 5) := by rfl


theorem t5_1544part0 : t5_1544jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1544frontier : t5_1544root.frontier 0=t5_1544jobs := by rfl
theorem t5_1544all : t5_1544jobs.all (Job.check tree)=true := by
  simp only [t5_1544jobs,List.all_append,List.all_nil,t5_1544part0,Bool.and_self]
theorem t5_1544checked : Checked tree [8,8,5,10,7] := by
  refine ⟨plan5257,valid5257,t5_1544choices,?_⟩
  exact check_of_frontier tree 0 t5_1544root t5_1544jobs t5_1544frontier t5_1544all
theorem t5_1545choices : plan5258.choices=[8,8,5,10,10].map (options 5 5) := by rfl


theorem t5_1545part0 : t5_1545jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1545frontier : t5_1545root.frontier 0=t5_1545jobs := by rfl
theorem t5_1545all : t5_1545jobs.all (Job.check tree)=true := by
  simp only [t5_1545jobs,List.all_append,List.all_nil,t5_1545part0,Bool.and_self]
theorem t5_1545checked : Checked tree [8,8,5,10,10] := by
  refine ⟨plan5258,valid5258,t5_1545choices,?_⟩
  exact check_of_frontier tree 0 t5_1545root t5_1545jobs t5_1545frontier t5_1545all
theorem t5_1546choices : plan5259.choices=[8,8,6,6,6].map (options 5 5) := by rfl


theorem t5_1546part0 : t5_1546jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1546frontier : t5_1546root.frontier 0=t5_1546jobs := by rfl
theorem t5_1546all : t5_1546jobs.all (Job.check tree)=true := by
  simp only [t5_1546jobs,List.all_append,List.all_nil,t5_1546part0,Bool.and_self]
theorem t5_1546checked : Checked tree [8,8,6,6,6] := by
  refine ⟨plan5259,valid5259,t5_1546choices,?_⟩
  exact check_of_frontier tree 0 t5_1546root t5_1546jobs t5_1546frontier t5_1546all
theorem t5_1547choices : plan5260.choices=[8,8,6,6,7].map (options 5 5) := by rfl


theorem t5_1547part0 : t5_1547jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1547frontier : t5_1547root.frontier 0=t5_1547jobs := by rfl
theorem t5_1547all : t5_1547jobs.all (Job.check tree)=true := by
  simp only [t5_1547jobs,List.all_append,List.all_nil,t5_1547part0,Bool.and_self]
theorem t5_1547checked : Checked tree [8,8,6,6,7] := by
  refine ⟨plan5260,valid5260,t5_1547choices,?_⟩
  exact check_of_frontier tree 0 t5_1547root t5_1547jobs t5_1547frontier t5_1547all
theorem t5_1548choices : plan5261.choices=[8,8,6,6,10].map (options 5 5) := by rfl


theorem t5_1548part0 : t5_1548jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1548frontier : t5_1548root.frontier 0=t5_1548jobs := by rfl
theorem t5_1548all : t5_1548jobs.all (Job.check tree)=true := by
  simp only [t5_1548jobs,List.all_append,List.all_nil,t5_1548part0,Bool.and_self]
theorem t5_1548checked : Checked tree [8,8,6,6,10] := by
  refine ⟨plan5261,valid5261,t5_1548choices,?_⟩
  exact check_of_frontier tree 0 t5_1548root t5_1548jobs t5_1548frontier t5_1548all
theorem t5_1549choices : plan5262.choices=[8,8,6,7,7].map (options 5 5) := by rfl


theorem t5_1549part0 : t5_1549jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1549frontier : t5_1549root.frontier 0=t5_1549jobs := by rfl
theorem t5_1549all : t5_1549jobs.all (Job.check tree)=true := by
  simp only [t5_1549jobs,List.all_append,List.all_nil,t5_1549part0,Bool.and_self]
theorem t5_1549checked : Checked tree [8,8,6,7,7] := by
  refine ⟨plan5262,valid5262,t5_1549choices,?_⟩
  exact check_of_frontier tree 0 t5_1549root t5_1549jobs t5_1549frontier t5_1549all
theorem t5_1550choices : plan5263.choices=[8,8,6,10,7].map (options 5 5) := by rfl


theorem t5_1550part0 : t5_1550jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1550frontier : t5_1550root.frontier 0=t5_1550jobs := by rfl
theorem t5_1550all : t5_1550jobs.all (Job.check tree)=true := by
  simp only [t5_1550jobs,List.all_append,List.all_nil,t5_1550part0,Bool.and_self]
theorem t5_1550checked : Checked tree [8,8,6,10,7] := by
  refine ⟨plan5263,valid5263,t5_1550choices,?_⟩
  exact check_of_frontier tree 0 t5_1550root t5_1550jobs t5_1550frontier t5_1550all
theorem t5_1551choices : plan5264.choices=[8,8,6,10,10].map (options 5 5) := by rfl


theorem t5_1551part0 : t5_1551jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1551frontier : t5_1551root.frontier 0=t5_1551jobs := by rfl
theorem t5_1551all : t5_1551jobs.all (Job.check tree)=true := by
  simp only [t5_1551jobs,List.all_append,List.all_nil,t5_1551part0,Bool.and_self]
theorem t5_1551checked : Checked tree [8,8,6,10,10] := by
  refine ⟨plan5264,valid5264,t5_1551choices,?_⟩
  exact check_of_frontier tree 0 t5_1551root t5_1551jobs t5_1551frontier t5_1551all
theorem t5_1552choices : plan5265.choices=[8,8,7,7,7].map (options 5 5) := by rfl


theorem t5_1552part0 : t5_1552jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1552frontier : t5_1552root.frontier 0=t5_1552jobs := by rfl
theorem t5_1552all : t5_1552jobs.all (Job.check tree)=true := by
  simp only [t5_1552jobs,List.all_append,List.all_nil,t5_1552part0,Bool.and_self]
theorem t5_1552checked : Checked tree [8,8,7,7,7] := by
  refine ⟨plan5265,valid5265,t5_1552choices,?_⟩
  exact check_of_frontier tree 0 t5_1552root t5_1552jobs t5_1552frontier t5_1552all
theorem t5_1553choices : plan4965.choices=[8,8,8,3,7].map (options 5 4) := by rfl


theorem t5_1553part0 : t5_1553jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1553frontier : t5_1553root.frontier 0=t5_1553jobs := by rfl
theorem t5_1553all : t5_1553jobs.all (Job.check tree)=true := by
  simp only [t5_1553jobs,List.all_append,List.all_nil,t5_1553part0,Bool.and_self]
theorem t5_1553checked : Checked tree [8,8,8,3,7] := by
  refine ⟨plan4965,valid4965,t5_1553choices,?_⟩
  exact check_of_frontier tree 0 t5_1553root t5_1553jobs t5_1553frontier t5_1553all
theorem t5_1554choices : plan5266.choices=[8,8,8,6,7].map (options 5 5) := by rfl


theorem t5_1554part0 : t5_1554jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1554frontier : t5_1554root.frontier 0=t5_1554jobs := by rfl
theorem t5_1554all : t5_1554jobs.all (Job.check tree)=true := by
  simp only [t5_1554jobs,List.all_append,List.all_nil,t5_1554part0,Bool.and_self]
theorem t5_1554checked : Checked tree [8,8,8,6,7] := by
  refine ⟨plan5266,valid5266,t5_1554choices,?_⟩
  exact check_of_frontier tree 0 t5_1554root t5_1554jobs t5_1554frontier t5_1554all
theorem t5_1555choices : plan5267.choices=[8,8,8,7,7].map (options 5 5) := by rfl


theorem t5_1555part0 : t5_1555jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1555frontier : t5_1555root.frontier 0=t5_1555jobs := by rfl
theorem t5_1555all : t5_1555jobs.all (Job.check tree)=true := by
  simp only [t5_1555jobs,List.all_append,List.all_nil,t5_1555part0,Bool.and_self]
theorem t5_1555checked : Checked tree [8,8,8,7,7] := by
  refine ⟨plan5267,valid5267,t5_1555choices,?_⟩
  exact check_of_frontier tree 0 t5_1555root t5_1555jobs t5_1555frontier t5_1555all
theorem t5_1556choices : plan5268.choices=[8,8,8,10,7].map (options 5 5) := by rfl


theorem t5_1556part0 : t5_1556jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1556frontier : t5_1556root.frontier 0=t5_1556jobs := by rfl
theorem t5_1556all : t5_1556jobs.all (Job.check tree)=true := by
  simp only [t5_1556jobs,List.all_append,List.all_nil,t5_1556part0,Bool.and_self]
theorem t5_1556checked : Checked tree [8,8,8,10,7] := by
  refine ⟨plan5268,valid5268,t5_1556choices,?_⟩
  exact check_of_frontier tree 0 t5_1556root t5_1556jobs t5_1556frontier t5_1556all
theorem t5_1557choices : plan4435.choices=[8,8,9,3,3].map (options 5 3) := by rfl


theorem t5_1557part0 : t5_1557jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1557frontier : t5_1557root.frontier 0=t5_1557jobs := by rfl
theorem t5_1557all : t5_1557jobs.all (Job.check tree)=true := by
  simp only [t5_1557jobs,List.all_append,List.all_nil,t5_1557part0,Bool.and_self]
theorem t5_1557checked : Checked tree [8,8,9,3,3] := by
  refine ⟨plan4435,valid4435,t5_1557choices,?_⟩
  exact check_of_frontier tree 0 t5_1557root t5_1557jobs t5_1557frontier t5_1557all
theorem t5_1558choices : plan4966.choices=[8,8,9,3,6].map (options 5 4) := by rfl


theorem t5_1558part0 : t5_1558jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1558frontier : t5_1558root.frontier 0=t5_1558jobs := by rfl
theorem t5_1558all : t5_1558jobs.all (Job.check tree)=true := by
  simp only [t5_1558jobs,List.all_append,List.all_nil,t5_1558part0,Bool.and_self]
theorem t5_1558checked : Checked tree [8,8,9,3,6] := by
  refine ⟨plan4966,valid4966,t5_1558choices,?_⟩
  exact check_of_frontier tree 0 t5_1558root t5_1558jobs t5_1558frontier t5_1558all
theorem t5_1559choices : plan4967.choices=[8,8,9,3,7].map (options 5 4) := by rfl


theorem t5_1559part0 : t5_1559jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1559frontier : t5_1559root.frontier 0=t5_1559jobs := by rfl
theorem t5_1559all : t5_1559jobs.all (Job.check tree)=true := by
  simp only [t5_1559jobs,List.all_append,List.all_nil,t5_1559part0,Bool.and_self]
theorem t5_1559checked : Checked tree [8,8,9,3,7] := by
  refine ⟨plan4967,valid4967,t5_1559choices,?_⟩
  exact check_of_frontier tree 0 t5_1559root t5_1559jobs t5_1559frontier t5_1559all
theorem t5_1560choices : plan4968.choices=[8,8,9,3,10].map (options 5 4) := by rfl


theorem t5_1560part0 : t5_1560jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1560frontier : t5_1560root.frontier 0=t5_1560jobs := by rfl
theorem t5_1560all : t5_1560jobs.all (Job.check tree)=true := by
  simp only [t5_1560jobs,List.all_append,List.all_nil,t5_1560part0,Bool.and_self]
theorem t5_1560checked : Checked tree [8,8,9,3,10] := by
  refine ⟨plan4968,valid4968,t5_1560choices,?_⟩
  exact check_of_frontier tree 0 t5_1560root t5_1560jobs t5_1560frontier t5_1560all
theorem t5_1561choices : plan5269.choices=[8,8,9,6,6].map (options 5 5) := by rfl


theorem t5_1561part0 : t5_1561jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1561frontier : t5_1561root.frontier 0=t5_1561jobs := by rfl
theorem t5_1561all : t5_1561jobs.all (Job.check tree)=true := by
  simp only [t5_1561jobs,List.all_append,List.all_nil,t5_1561part0,Bool.and_self]
theorem t5_1561checked : Checked tree [8,8,9,6,6] := by
  refine ⟨plan5269,valid5269,t5_1561choices,?_⟩
  exact check_of_frontier tree 0 t5_1561root t5_1561jobs t5_1561frontier t5_1561all
theorem t5_1562choices : plan5270.choices=[8,8,9,6,7].map (options 5 5) := by rfl


theorem t5_1562part0 : t5_1562jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1562frontier : t5_1562root.frontier 0=t5_1562jobs := by rfl
theorem t5_1562all : t5_1562jobs.all (Job.check tree)=true := by
  simp only [t5_1562jobs,List.all_append,List.all_nil,t5_1562part0,Bool.and_self]
theorem t5_1562checked : Checked tree [8,8,9,6,7] := by
  refine ⟨plan5270,valid5270,t5_1562choices,?_⟩
  exact check_of_frontier tree 0 t5_1562root t5_1562jobs t5_1562frontier t5_1562all
theorem t5_1563choices : plan5271.choices=[8,8,9,6,10].map (options 5 5) := by rfl


theorem t5_1563part0 : t5_1563jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1563frontier : t5_1563root.frontier 0=t5_1563jobs := by rfl
theorem t5_1563all : t5_1563jobs.all (Job.check tree)=true := by
  simp only [t5_1563jobs,List.all_append,List.all_nil,t5_1563part0,Bool.and_self]
theorem t5_1563checked : Checked tree [8,8,9,6,10] := by
  refine ⟨plan5271,valid5271,t5_1563choices,?_⟩
  exact check_of_frontier tree 0 t5_1563root t5_1563jobs t5_1563frontier t5_1563all
theorem t5_1564choices : plan5272.choices=[8,8,9,7,7].map (options 5 5) := by rfl


theorem t5_1564part0 : t5_1564jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1564frontier : t5_1564root.frontier 0=t5_1564jobs := by rfl
theorem t5_1564all : t5_1564jobs.all (Job.check tree)=true := by
  simp only [t5_1564jobs,List.all_append,List.all_nil,t5_1564part0,Bool.and_self]
theorem t5_1564checked : Checked tree [8,8,9,7,7] := by
  refine ⟨plan5272,valid5272,t5_1564choices,?_⟩
  exact check_of_frontier tree 0 t5_1564root t5_1564jobs t5_1564frontier t5_1564all
theorem t5_1565choices : plan5273.choices=[8,8,9,9,7].map (options 5 5) := by rfl


theorem t5_1565part0 : t5_1565jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1565frontier : t5_1565root.frontier 0=t5_1565jobs := by rfl
theorem t5_1565all : t5_1565jobs.all (Job.check tree)=true := by
  simp only [t5_1565jobs,List.all_append,List.all_nil,t5_1565part0,Bool.and_self]
theorem t5_1565checked : Checked tree [8,8,9,9,7] := by
  refine ⟨plan5273,valid5273,t5_1565choices,?_⟩
  exact check_of_frontier tree 0 t5_1565root t5_1565jobs t5_1565frontier t5_1565all
theorem t5_1566choices : plan5274.choices=[8,8,9,10,7].map (options 5 5) := by rfl


theorem t5_1566part0 : t5_1566jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1566frontier : t5_1566root.frontier 0=t5_1566jobs := by rfl
theorem t5_1566all : t5_1566jobs.all (Job.check tree)=true := by
  simp only [t5_1566jobs,List.all_append,List.all_nil,t5_1566part0,Bool.and_self]
theorem t5_1566checked : Checked tree [8,8,9,10,7] := by
  refine ⟨plan5274,valid5274,t5_1566choices,?_⟩
  exact check_of_frontier tree 0 t5_1566root t5_1566jobs t5_1566frontier t5_1566all
theorem t5_1567choices : plan5275.choices=[8,8,9,10,10].map (options 5 5) := by rfl


theorem t5_1567part0 : t5_1567jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1567frontier : t5_1567root.frontier 0=t5_1567jobs := by rfl
theorem t5_1567all : t5_1567jobs.all (Job.check tree)=true := by
  simp only [t5_1567jobs,List.all_append,List.all_nil,t5_1567part0,Bool.and_self]
theorem t5_1567checked : Checked tree [8,8,9,10,10] := by
  refine ⟨plan5275,valid5275,t5_1567choices,?_⟩
  exact check_of_frontier tree 0 t5_1567root t5_1567jobs t5_1567frontier t5_1567all
theorem t5_1568choices : plan5276.choices=[8,8,10,7,7].map (options 5 5) := by rfl


theorem t5_1568part0 : t5_1568jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1568frontier : t5_1568root.frontier 0=t5_1568jobs := by rfl
theorem t5_1568all : t5_1568jobs.all (Job.check tree)=true := by
  simp only [t5_1568jobs,List.all_append,List.all_nil,t5_1568part0,Bool.and_self]
theorem t5_1568checked : Checked tree [8,8,10,7,7] := by
  refine ⟨plan5276,valid5276,t5_1568choices,?_⟩
  exact check_of_frontier tree 0 t5_1568root t5_1568jobs t5_1568frontier t5_1568all
theorem t5_1569choices : plan5277.choices=[8,8,10,10,7].map (options 5 5) := by rfl


theorem t5_1569part0 : t5_1569jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1569frontier : t5_1569root.frontier 0=t5_1569jobs := by rfl
theorem t5_1569all : t5_1569jobs.all (Job.check tree)=true := by
  simp only [t5_1569jobs,List.all_append,List.all_nil,t5_1569part0,Bool.and_self]
theorem t5_1569checked : Checked tree [8,8,10,10,7] := by
  refine ⟨plan5277,valid5277,t5_1569choices,?_⟩
  exact check_of_frontier tree 0 t5_1569root t5_1569jobs t5_1569frontier t5_1569all
theorem t5_1570choices : plan5278.choices=[8,8,10,10,10].map (options 5 5) := by rfl


theorem t5_1570part0 : t5_1570jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1570frontier : t5_1570root.frontier 0=t5_1570jobs := by rfl
theorem t5_1570all : t5_1570jobs.all (Job.check tree)=true := by
  simp only [t5_1570jobs,List.all_append,List.all_nil,t5_1570part0,Bool.and_self]
theorem t5_1570checked : Checked tree [8,8,10,10,10] := by
  refine ⟨plan5278,valid5278,t5_1570choices,?_⟩
  exact check_of_frontier tree 0 t5_1570root t5_1570jobs t5_1570frontier t5_1570all
theorem t5_1571choices : plan3995.choices=[8,9,3,3,3].map (options 5 2) := by rfl


theorem t5_1571part0 : t5_1571jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1571frontier : t5_1571root.frontier 0=t5_1571jobs := by rfl
theorem t5_1571all : t5_1571jobs.all (Job.check tree)=true := by
  simp only [t5_1571jobs,List.all_append,List.all_nil,t5_1571part0,Bool.and_self]
theorem t5_1571checked : Checked tree [8,9,3,3,3] := by
  refine ⟨plan3995,valid3995,t5_1571choices,?_⟩
  exact check_of_frontier tree 0 t5_1571root t5_1571jobs t5_1571frontier t5_1571all
theorem t5_1572choices : plan4436.choices=[8,9,3,3,6].map (options 5 3) := by rfl


theorem t5_1572part0 : t5_1572jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1572frontier : t5_1572root.frontier 0=t5_1572jobs := by rfl
theorem t5_1572all : t5_1572jobs.all (Job.check tree)=true := by
  simp only [t5_1572jobs,List.all_append,List.all_nil,t5_1572part0,Bool.and_self]
theorem t5_1572checked : Checked tree [8,9,3,3,6] := by
  refine ⟨plan4436,valid4436,t5_1572choices,?_⟩
  exact check_of_frontier tree 0 t5_1572root t5_1572jobs t5_1572frontier t5_1572all
theorem t5_1573choices : plan4437.choices=[8,9,3,3,7].map (options 5 3) := by rfl


theorem t5_1573part0 : t5_1573jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1573frontier : t5_1573root.frontier 0=t5_1573jobs := by rfl
theorem t5_1573all : t5_1573jobs.all (Job.check tree)=true := by
  simp only [t5_1573jobs,List.all_append,List.all_nil,t5_1573part0,Bool.and_self]
theorem t5_1573checked : Checked tree [8,9,3,3,7] := by
  refine ⟨plan4437,valid4437,t5_1573choices,?_⟩
  exact check_of_frontier tree 0 t5_1573root t5_1573jobs t5_1573frontier t5_1573all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks043 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1467checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1468checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1469checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1470checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1471checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1472checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1473checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1474checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1475checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1455checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1476checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1477checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1478checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1479checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1480checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1481checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1482checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1483checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1484checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1485checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1456checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1486checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1487checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1488checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1489checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1490checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1491checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1492checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1493checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1494checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1495checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1457checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1496checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1497checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1498checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1499checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1500checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1501checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1502checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1503checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1504checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1505checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1458checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1506checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1507checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1508checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1509checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1510checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1511checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1512checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1513checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1514checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1515checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1459checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1516checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1517checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1518checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1519checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1520checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1521checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1522checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1523checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1524checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1525checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1460checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1526checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1527checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1528checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1529checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1530checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1531checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1532checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1533checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1534checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1535checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1461checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1536checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1537checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1538checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1539checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1540checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1541checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1542checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1543checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1544checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1545checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1462checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1546checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1547checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1548checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1549checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1550checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1551checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1552checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1553checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1554checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1555checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1463checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1556checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1557checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1558checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1559checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1560checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1561checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1562checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1563checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1564checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1565checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1464checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1566checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1567checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1568checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1569checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1570checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1571checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1572checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1573checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1465checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1454checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1466checked⟩
