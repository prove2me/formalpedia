-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks037
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:27.380348+00:00
-- url     : https://prove2.me/submissions/b98f2968-bce0-4dc7-9bec-acae4867bd42

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks037
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans053
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

theorem valid112 : plan112.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid113 : plan113.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid114 : plan114.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid115 : plan115.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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







theorem valid484 : plan484.Valid := valid_step _ _ _ valid100 (by decide +kernel)

theorem valid485 : plan485.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid486 : plan486.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid487 : plan487.Valid := valid_step _ _ _ valid105 (by decide +kernel)



































theorem valid505 : plan505.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid506 : plan506.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid507 : plan507.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid508 : plan508.Valid := valid_step _ _ _ valid106 (by decide +kernel)











theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid518 : plan518.Valid := valid_step _ _ _ valid106 (by decide +kernel)









theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid524 : plan524.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid525 : plan525.Valid := valid_step _ _ _ valid112 (by decide +kernel)

theorem valid526 : plan526.Valid := valid_step _ _ _ valid113 (by decide +kernel)

theorem valid527 : plan527.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid528 : plan528.Valid := valid_step _ _ _ valid115 (by decide +kernel)

theorem valid529 : plan529.Valid := valid_step _ _ _ valid116 (by decide +kernel)

theorem valid530 : plan530.Valid := valid_step _ _ _ valid113 (by decide +kernel)

theorem valid531 : plan531.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid532 : plan532.Valid := valid_step _ _ _ valid116 (by decide +kernel)

theorem valid533 : plan533.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid534 : plan534.Valid := valid_step _ _ _ valid113 (by decide +kernel)

theorem valid535 : plan535.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid536 : plan536.Valid := valid_step _ _ _ valid115 (by decide +kernel)

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

































































































theorem valid1297 : plan1297.Valid := valid_step _ _ _ valid462 (by decide +kernel)













































































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













































































































theorem valid2647 : plan2647.Valid := valid_step _ _ _ valid1297 (by decide +kernel)


















































































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











































































theorem valid3974 : plan3974.Valid := valid_step _ _ _ valid2647 (by decide +kernel)




















































































































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

















































theorem valid2809 : plan2809.Valid := valid_step _ _ _ valid1336 (by decide +kernel)

theorem valid2810 : plan2810.Valid := valid_step _ _ _ valid1337 (by decide +kernel)

theorem valid2811 : plan2811.Valid := valid_step _ _ _ valid1338 (by decide +kernel)













theorem valid2818 : plan2818.Valid := valid_step _ _ _ valid1349 (by decide +kernel)











theorem valid2824 : plan2824.Valid := valid_step _ _ _ valid1381 (by decide +kernel)
















































































































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















theorem valid1448 : plan1448.Valid := valid_step _ _ _ valid505 (by decide +kernel)

theorem valid1449 : plan1449.Valid := valid_step _ _ _ valid506 (by decide +kernel)

theorem valid1450 : plan1450.Valid := valid_step _ _ _ valid507 (by decide +kernel)









theorem valid1455 : plan1455.Valid := valid_step _ _ _ valid518 (by decide +kernel)

















theorem valid1464 : plan1464.Valid := valid_step _ _ _ valid524 (by decide +kernel)







theorem valid1468 : plan1468.Valid := valid_step _ _ _ valid525 (by decide +kernel)

theorem valid1469 : plan1469.Valid := valid_step _ _ _ valid526 (by decide +kernel)

theorem valid1470 : plan1470.Valid := valid_step _ _ _ valid527 (by decide +kernel)

theorem valid1471 : plan1471.Valid := valid_step _ _ _ valid528 (by decide +kernel)

theorem valid1472 : plan1472.Valid := valid_step _ _ _ valid529 (by decide +kernel)

theorem valid1473 : plan1473.Valid := valid_step _ _ _ valid530 (by decide +kernel)

theorem valid1474 : plan1474.Valid := valid_step _ _ _ valid531 (by decide +kernel)

theorem valid1475 : plan1475.Valid := valid_step _ _ _ valid532 (by decide +kernel)

theorem valid1476 : plan1476.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1477 : plan1477.Valid := valid_step _ _ _ valid534 (by decide +kernel)

theorem valid1478 : plan1478.Valid := valid_step _ _ _ valid535 (by decide +kernel)

theorem valid1479 : plan1479.Valid := valid_step _ _ _ valid536 (by decide +kernel)

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







theorem valid1493 : plan1493.Valid := valid_step _ _ _ valid530 (by decide +kernel)

theorem valid1494 : plan1494.Valid := valid_step _ _ _ valid531 (by decide +kernel)

theorem valid1495 : plan1495.Valid := valid_step _ _ _ valid532 (by decide +kernel)

theorem valid1496 : plan1496.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1497 : plan1497.Valid := valid_step _ _ _ valid534 (by decide +kernel)

theorem valid1498 : plan1498.Valid := valid_step _ _ _ valid535 (by decide +kernel)

theorem valid1499 : plan1499.Valid := valid_step _ _ _ valid536 (by decide +kernel)

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

































































theorem valid2913 : plan2913.Valid := valid_step _ _ _ valid1464 (by decide +kernel)











































































































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











































































































































theorem valid3142 : plan3142.Valid := valid_step _ _ _ valid1468 (by decide +kernel)

theorem valid3143 : plan3143.Valid := valid_step _ _ _ valid1469 (by decide +kernel)

theorem valid3144 : plan3144.Valid := valid_step _ _ _ valid1470 (by decide +kernel)

theorem valid3145 : plan3145.Valid := valid_step _ _ _ valid1471 (by decide +kernel)

theorem valid3146 : plan3146.Valid := valid_step _ _ _ valid1472 (by decide +kernel)

theorem valid3147 : plan3147.Valid := valid_step _ _ _ valid1473 (by decide +kernel)

theorem valid3148 : plan3148.Valid := valid_step _ _ _ valid1474 (by decide +kernel)

theorem valid3149 : plan3149.Valid := valid_step _ _ _ valid1475 (by decide +kernel)

theorem valid3150 : plan3150.Valid := valid_step _ _ _ valid1476 (by decide +kernel)

theorem valid3151 : plan3151.Valid := valid_step _ _ _ valid1477 (by decide +kernel)

theorem valid3152 : plan3152.Valid := valid_step _ _ _ valid1478 (by decide +kernel)

theorem valid3153 : plan3153.Valid := valid_step _ _ _ valid1479 (by decide +kernel)

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























































































































theorem valid4380 : plan4380.Valid := valid_step _ _ _ valid2809 (by decide +kernel)

theorem valid4381 : plan4381.Valid := valid_step _ _ _ valid2810 (by decide +kernel)

theorem valid4382 : plan4382.Valid := valid_step _ _ _ valid2811 (by decide +kernel)

theorem valid4383 : plan4383.Valid := valid_step _ _ _ valid2818 (by decide +kernel)

theorem valid4384 : plan4384.Valid := valid_step _ _ _ valid2824 (by decide +kernel)
































































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



































































































































theorem valid4866 : plan4866.Valid := valid_step _ _ _ valid2913 (by decide +kernel)

theorem valid4867 : plan4867.Valid := valid_step _ _ _ valid2967 (by decide +kernel)

theorem valid4868 : plan4868.Valid := valid_step _ _ _ valid2968 (by decide +kernel)

theorem valid4869 : plan4869.Valid := valid_step _ _ _ valid2969 (by decide +kernel)

theorem valid4870 : plan4870.Valid := valid_step _ _ _ valid2970 (by decide +kernel)

theorem valid4871 : plan4871.Valid := valid_step _ _ _ valid2971 (by decide +kernel)

theorem valid4872 : plan4872.Valid := valid_step _ _ _ valid2972 (by decide +kernel)

theorem valid4873 : plan4873.Valid := valid_step _ _ _ valid2973 (by decide +kernel)

theorem valid4874 : plan4874.Valid := valid_step _ _ _ valid2974 (by decide +kernel)

theorem valid4875 : plan4875.Valid := valid_step _ _ _ valid2975 (by decide +kernel)

theorem valid4876 : plan4876.Valid := valid_step _ _ _ valid2976 (by decide +kernel)

theorem valid4877 : plan4877.Valid := valid_step _ _ _ valid2986 (by decide +kernel)

theorem valid4878 : plan4878.Valid := valid_step _ _ _ valid3000 (by decide +kernel)

theorem valid4879 : plan4879.Valid := valid_step _ _ _ valid3001 (by decide +kernel)

theorem valid4880 : plan4880.Valid := valid_step _ _ _ valid3002 (by decide +kernel)

theorem valid4881 : plan4881.Valid := valid_step _ _ _ valid3007 (by decide +kernel)






























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

theorem valid3170 : plan3170.Valid := valid_step _ _ _ valid1499 (by decide +kernel)

theorem valid3171 : plan3171.Valid := valid_step _ _ _ valid1500 (by decide +kernel)

theorem valid3172 : plan3172.Valid := valid_step _ _ _ valid1501 (by decide +kernel)

theorem valid3173 : plan3173.Valid := valid_step _ _ _ valid1502 (by decide +kernel)

theorem valid3174 : plan3174.Valid := valid_step _ _ _ valid1503 (by decide +kernel)

theorem valid3175 : plan3175.Valid := valid_step _ _ _ valid1504 (by decide +kernel)

theorem valid3176 : plan3176.Valid := valid_step _ _ _ valid1505 (by decide +kernel)

theorem valid3177 : plan3177.Valid := valid_step _ _ _ valid1483 (by decide +kernel)

theorem valid3178 : plan3178.Valid := valid_step _ _ _ valid1484 (by decide +kernel)












































































































































































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





































































theorem valid5123 : plan5123.Valid := valid_step _ _ _ valid3142 (by decide +kernel)

theorem valid5124 : plan5124.Valid := valid_step _ _ _ valid3143 (by decide +kernel)

theorem valid5125 : plan5125.Valid := valid_step _ _ _ valid3144 (by decide +kernel)

theorem valid5126 : plan5126.Valid := valid_step _ _ _ valid3145 (by decide +kernel)

theorem valid5127 : plan5127.Valid := valid_step _ _ _ valid3146 (by decide +kernel)

theorem valid5128 : plan5128.Valid := valid_step _ _ _ valid3147 (by decide +kernel)

theorem valid5129 : plan5129.Valid := valid_step _ _ _ valid3148 (by decide +kernel)

theorem valid5130 : plan5130.Valid := valid_step _ _ _ valid3149 (by decide +kernel)

theorem valid5131 : plan5131.Valid := valid_step _ _ _ valid3150 (by decide +kernel)

theorem valid5132 : plan5132.Valid := valid_step _ _ _ valid3151 (by decide +kernel)

theorem valid5133 : plan5133.Valid := valid_step _ _ _ valid3152 (by decide +kernel)

theorem valid5134 : plan5134.Valid := valid_step _ _ _ valid3153 (by decide +kernel)

theorem valid5135 : plan5135.Valid := valid_step _ _ _ valid3154 (by decide +kernel)

theorem valid5136 : plan5136.Valid := valid_step _ _ _ valid3155 (by decide +kernel)

theorem valid5137 : plan5137.Valid := valid_step _ _ _ valid3156 (by decide +kernel)

theorem valid5138 : plan5138.Valid := valid_step _ _ _ valid3157 (by decide +kernel)

theorem valid5139 : plan5139.Valid := valid_step _ _ _ valid3158 (by decide +kernel)

theorem valid5140 : plan5140.Valid := valid_step _ _ _ valid3159 (by decide +kernel)

theorem valid5141 : plan5141.Valid := valid_step _ _ _ valid3160 (by decide +kernel)

theorem valid5142 : plan5142.Valid := valid_step _ _ _ valid3161 (by decide +kernel)

theorem valid5143 : plan5143.Valid := valid_step _ _ _ valid3162 (by decide +kernel)

theorem valid5144 : plan5144.Valid := valid_step _ _ _ valid3163 (by decide +kernel)

theorem valid5145 : plan5145.Valid := valid_step _ _ _ valid3164 (by decide +kernel)

theorem valid5146 : plan5146.Valid := valid_step _ _ _ valid3165 (by decide +kernel)

theorem valid5147 : plan5147.Valid := valid_step _ _ _ valid3166 (by decide +kernel)

theorem valid5148 : plan5148.Valid := valid_step _ _ _ valid3167 (by decide +kernel)

theorem valid5149 : plan5149.Valid := valid_step _ _ _ valid3168 (by decide +kernel)

theorem valid5150 : plan5150.Valid := valid_step _ _ _ valid3169 (by decide +kernel)

theorem valid5151 : plan5151.Valid := valid_step _ _ _ valid3170 (by decide +kernel)

theorem valid5152 : plan5152.Valid := valid_step _ _ _ valid3171 (by decide +kernel)

theorem valid5153 : plan5153.Valid := valid_step _ _ _ valid3172 (by decide +kernel)

theorem valid5154 : plan5154.Valid := valid_step _ _ _ valid3173 (by decide +kernel)

theorem valid5155 : plan5155.Valid := valid_step _ _ _ valid3174 (by decide +kernel)

theorem valid5156 : plan5156.Valid := valid_step _ _ _ valid3175 (by decide +kernel)

theorem valid5157 : plan5157.Valid := valid_step _ _ _ valid3176 (by decide +kernel)

theorem valid5158 : plan5158.Valid := valid_step _ _ _ valid3177 (by decide +kernel)

theorem valid5159 : plan5159.Valid := valid_step _ _ _ valid3178 (by decide +kernel)


















































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
theorem t5_1231choices : plan4866.choices=[5,3,10,10,10].map (options 5 4) := by rfl


theorem t5_1231part0 : t5_1231jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1231frontier : t5_1231root.frontier 0=t5_1231jobs := by rfl
theorem t5_1231all : t5_1231jobs.all (Job.check tree)=true := by
  simp only [t5_1231jobs,List.all_append,List.all_nil,t5_1231part0,Bool.and_self]
theorem t5_1231checked : Checked tree [5,3,10,10,10] := by
  refine ⟨plan4866,valid4866,t5_1231choices,?_⟩
  exact check_of_frontier tree 0 t5_1231root t5_1231jobs t5_1231frontier t5_1231all
theorem t5_1232choices : plan3974.choices=[5,5,3,3,3].map (options 5 2) := by rfl


theorem t5_1232part0 : t5_1232jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1232frontier : t5_1232root.frontier 0=t5_1232jobs := by rfl
theorem t5_1232all : t5_1232jobs.all (Job.check tree)=true := by
  simp only [t5_1232jobs,List.all_append,List.all_nil,t5_1232part0,Bool.and_self]
theorem t5_1232checked : Checked tree [5,5,3,3,3] := by
  refine ⟨plan3974,valid3974,t5_1232choices,?_⟩
  exact check_of_frontier tree 0 t5_1232root t5_1232jobs t5_1232frontier t5_1232all
theorem t5_1233choices : plan4380.choices=[5,5,3,3,6].map (options 5 3) := by rfl


theorem t5_1233part0 : t5_1233jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1233frontier : t5_1233root.frontier 0=t5_1233jobs := by rfl
theorem t5_1233all : t5_1233jobs.all (Job.check tree)=true := by
  simp only [t5_1233jobs,List.all_append,List.all_nil,t5_1233part0,Bool.and_self]
theorem t5_1233checked : Checked tree [5,5,3,3,6] := by
  refine ⟨plan4380,valid4380,t5_1233choices,?_⟩
  exact check_of_frontier tree 0 t5_1233root t5_1233jobs t5_1233frontier t5_1233all
theorem t5_1234choices : plan4381.choices=[5,5,3,3,7].map (options 5 3) := by rfl


theorem t5_1234part0 : t5_1234jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1234part1 : t5_1234jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1234frontier : t5_1234root.frontier 1=t5_1234jobs := by rfl
theorem t5_1234all : t5_1234jobs.all (Job.check tree)=true := by
  simp only [t5_1234jobs,List.all_append,List.all_nil,t5_1234part0,t5_1234part1,Bool.and_self]
theorem t5_1234checked : Checked tree [5,5,3,3,7] := by
  refine ⟨plan4381,valid4381,t5_1234choices,?_⟩
  exact check_of_frontier tree 1 t5_1234root t5_1234jobs t5_1234frontier t5_1234all
theorem t5_1235choices : plan4382.choices=[5,5,3,3,10].map (options 5 3) := by rfl


theorem t5_1235part0 : t5_1235jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1235frontier : t5_1235root.frontier 0=t5_1235jobs := by rfl
theorem t5_1235all : t5_1235jobs.all (Job.check tree)=true := by
  simp only [t5_1235jobs,List.all_append,List.all_nil,t5_1235part0,Bool.and_self]
theorem t5_1235checked : Checked tree [5,5,3,3,10] := by
  refine ⟨plan4382,valid4382,t5_1235choices,?_⟩
  exact check_of_frontier tree 0 t5_1235root t5_1235jobs t5_1235frontier t5_1235all
theorem t5_1236choices : plan4867.choices=[5,5,3,6,6].map (options 5 4) := by rfl


theorem t5_1236part0 : t5_1236jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1236frontier : t5_1236root.frontier 0=t5_1236jobs := by rfl
theorem t5_1236all : t5_1236jobs.all (Job.check tree)=true := by
  simp only [t5_1236jobs,List.all_append,List.all_nil,t5_1236part0,Bool.and_self]
theorem t5_1236checked : Checked tree [5,5,3,6,6] := by
  refine ⟨plan4867,valid4867,t5_1236choices,?_⟩
  exact check_of_frontier tree 0 t5_1236root t5_1236jobs t5_1236frontier t5_1236all
theorem t5_1237choices : plan4868.choices=[5,5,3,6,7].map (options 5 4) := by rfl


theorem t5_1237part0 : t5_1237jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1237part1 : t5_1237jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1237frontier : t5_1237root.frontier 1=t5_1237jobs := by rfl
theorem t5_1237all : t5_1237jobs.all (Job.check tree)=true := by
  simp only [t5_1237jobs,List.all_append,List.all_nil,t5_1237part0,t5_1237part1,Bool.and_self]
theorem t5_1237checked : Checked tree [5,5,3,6,7] := by
  refine ⟨plan4868,valid4868,t5_1237choices,?_⟩
  exact check_of_frontier tree 1 t5_1237root t5_1237jobs t5_1237frontier t5_1237all
theorem t5_1238choices : plan4869.choices=[5,5,3,6,10].map (options 5 4) := by rfl


theorem t5_1238part0 : t5_1238jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1238frontier : t5_1238root.frontier 0=t5_1238jobs := by rfl
theorem t5_1238all : t5_1238jobs.all (Job.check tree)=true := by
  simp only [t5_1238jobs,List.all_append,List.all_nil,t5_1238part0,Bool.and_self]
theorem t5_1238checked : Checked tree [5,5,3,6,10] := by
  refine ⟨plan4869,valid4869,t5_1238choices,?_⟩
  exact check_of_frontier tree 0 t5_1238root t5_1238jobs t5_1238frontier t5_1238all
theorem t5_1239choices : plan4870.choices=[5,5,3,7,7].map (options 5 4) := by rfl


theorem t5_1239part0 : t5_1239jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1239frontier : t5_1239root.frontier 0=t5_1239jobs := by rfl
theorem t5_1239all : t5_1239jobs.all (Job.check tree)=true := by
  simp only [t5_1239jobs,List.all_append,List.all_nil,t5_1239part0,Bool.and_self]
theorem t5_1239checked : Checked tree [5,5,3,7,7] := by
  refine ⟨plan4870,valid4870,t5_1239choices,?_⟩
  exact check_of_frontier tree 0 t5_1239root t5_1239jobs t5_1239frontier t5_1239all
theorem t5_1240choices : plan4871.choices=[5,5,3,10,7].map (options 5 4) := by rfl


theorem t5_1240part0 : t5_1240jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1240part1 : t5_1240jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1240frontier : t5_1240root.frontier 1=t5_1240jobs := by rfl
theorem t5_1240all : t5_1240jobs.all (Job.check tree)=true := by
  simp only [t5_1240jobs,List.all_append,List.all_nil,t5_1240part0,t5_1240part1,Bool.and_self]
theorem t5_1240checked : Checked tree [5,5,3,10,7] := by
  refine ⟨plan4871,valid4871,t5_1240choices,?_⟩
  exact check_of_frontier tree 1 t5_1240root t5_1240jobs t5_1240frontier t5_1240all
theorem t5_1241choices : plan4872.choices=[5,5,3,10,10].map (options 5 4) := by rfl


theorem t5_1241part0 : t5_1241jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1241frontier : t5_1241root.frontier 0=t5_1241jobs := by rfl
theorem t5_1241all : t5_1241jobs.all (Job.check tree)=true := by
  simp only [t5_1241jobs,List.all_append,List.all_nil,t5_1241part0,Bool.and_self]
theorem t5_1241checked : Checked tree [5,5,3,10,10] := by
  refine ⟨plan4872,valid4872,t5_1241choices,?_⟩
  exact check_of_frontier tree 0 t5_1241root t5_1241jobs t5_1241frontier t5_1241all
theorem t5_1242choices : plan4383.choices=[5,5,5,3,3].map (options 5 3) := by rfl


theorem t5_1242part0 : t5_1242jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1242frontier : t5_1242root.frontier 0=t5_1242jobs := by rfl
theorem t5_1242all : t5_1242jobs.all (Job.check tree)=true := by
  simp only [t5_1242jobs,List.all_append,List.all_nil,t5_1242part0,Bool.and_self]
theorem t5_1242checked : Checked tree [5,5,5,3,3] := by
  refine ⟨plan4383,valid4383,t5_1242choices,?_⟩
  exact check_of_frontier tree 0 t5_1242root t5_1242jobs t5_1242frontier t5_1242all
theorem t5_1243choices : plan4873.choices=[5,5,5,3,6].map (options 5 4) := by rfl


theorem t5_1243part0 : t5_1243jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1243frontier : t5_1243root.frontier 0=t5_1243jobs := by rfl
theorem t5_1243all : t5_1243jobs.all (Job.check tree)=true := by
  simp only [t5_1243jobs,List.all_append,List.all_nil,t5_1243part0,Bool.and_self]
theorem t5_1243checked : Checked tree [5,5,5,3,6] := by
  refine ⟨plan4873,valid4873,t5_1243choices,?_⟩
  exact check_of_frontier tree 0 t5_1243root t5_1243jobs t5_1243frontier t5_1243all
theorem t5_1244choices : plan4874.choices=[5,5,5,3,7].map (options 5 4) := by rfl


theorem t5_1244part0 : t5_1244jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1244frontier : t5_1244root.frontier 0=t5_1244jobs := by rfl
theorem t5_1244all : t5_1244jobs.all (Job.check tree)=true := by
  simp only [t5_1244jobs,List.all_append,List.all_nil,t5_1244part0,Bool.and_self]
theorem t5_1244checked : Checked tree [5,5,5,3,7] := by
  refine ⟨plan4874,valid4874,t5_1244choices,?_⟩
  exact check_of_frontier tree 0 t5_1244root t5_1244jobs t5_1244frontier t5_1244all
theorem t5_1245choices : plan4875.choices=[5,5,5,3,10].map (options 5 4) := by rfl


theorem t5_1245part0 : t5_1245jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1245frontier : t5_1245root.frontier 0=t5_1245jobs := by rfl
theorem t5_1245all : t5_1245jobs.all (Job.check tree)=true := by
  simp only [t5_1245jobs,List.all_append,List.all_nil,t5_1245part0,Bool.and_self]
theorem t5_1245checked : Checked tree [5,5,5,3,10] := by
  refine ⟨plan4875,valid4875,t5_1245choices,?_⟩
  exact check_of_frontier tree 0 t5_1245root t5_1245jobs t5_1245frontier t5_1245all
theorem t5_1246choices : plan4876.choices=[5,5,5,5,3].map (options 5 4) := by rfl


theorem t5_1246part0 : t5_1246jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1246frontier : t5_1246root.frontier 0=t5_1246jobs := by rfl
theorem t5_1246all : t5_1246jobs.all (Job.check tree)=true := by
  simp only [t5_1246jobs,List.all_append,List.all_nil,t5_1246part0,Bool.and_self]
theorem t5_1246checked : Checked tree [5,5,5,5,3] := by
  refine ⟨plan4876,valid4876,t5_1246choices,?_⟩
  exact check_of_frontier tree 0 t5_1246root t5_1246jobs t5_1246frontier t5_1246all
theorem t5_1247choices : plan5123.choices=[5,5,5,5,5].map (options 5 5) := by rfl


theorem t5_1247part0 : t5_1247jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1247frontier : t5_1247root.frontier 0=t5_1247jobs := by rfl
theorem t5_1247all : t5_1247jobs.all (Job.check tree)=true := by
  simp only [t5_1247jobs,List.all_append,List.all_nil,t5_1247part0,Bool.and_self]
theorem t5_1247checked : Checked tree [5,5,5,5,5] := by
  refine ⟨plan5123,valid5123,t5_1247choices,?_⟩
  exact check_of_frontier tree 0 t5_1247root t5_1247jobs t5_1247frontier t5_1247all
theorem t5_1248choices : plan5124.choices=[5,5,5,5,6].map (options 5 5) := by rfl


theorem t5_1248part0 : t5_1248jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1248frontier : t5_1248root.frontier 0=t5_1248jobs := by rfl
theorem t5_1248all : t5_1248jobs.all (Job.check tree)=true := by
  simp only [t5_1248jobs,List.all_append,List.all_nil,t5_1248part0,Bool.and_self]
theorem t5_1248checked : Checked tree [5,5,5,5,6] := by
  refine ⟨plan5124,valid5124,t5_1248choices,?_⟩
  exact check_of_frontier tree 0 t5_1248root t5_1248jobs t5_1248frontier t5_1248all
theorem t5_1249choices : plan5125.choices=[5,5,5,5,7].map (options 5 5) := by rfl


theorem t5_1249part0 : t5_1249jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1249frontier : t5_1249root.frontier 0=t5_1249jobs := by rfl
theorem t5_1249all : t5_1249jobs.all (Job.check tree)=true := by
  simp only [t5_1249jobs,List.all_append,List.all_nil,t5_1249part0,Bool.and_self]
theorem t5_1249checked : Checked tree [5,5,5,5,7] := by
  refine ⟨plan5125,valid5125,t5_1249choices,?_⟩
  exact check_of_frontier tree 0 t5_1249root t5_1249jobs t5_1249frontier t5_1249all
theorem t5_1250choices : plan5126.choices=[5,5,5,5,9].map (options 5 5) := by rfl


theorem t5_1250part0 : t5_1250jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1250frontier : t5_1250root.frontier 0=t5_1250jobs := by rfl
theorem t5_1250all : t5_1250jobs.all (Job.check tree)=true := by
  simp only [t5_1250jobs,List.all_append,List.all_nil,t5_1250part0,Bool.and_self]
theorem t5_1250checked : Checked tree [5,5,5,5,9] := by
  refine ⟨plan5126,valid5126,t5_1250choices,?_⟩
  exact check_of_frontier tree 0 t5_1250root t5_1250jobs t5_1250frontier t5_1250all
theorem t5_1251choices : plan5127.choices=[5,5,5,5,10].map (options 5 5) := by rfl


theorem t5_1251part0 : t5_1251jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1251frontier : t5_1251root.frontier 0=t5_1251jobs := by rfl
theorem t5_1251all : t5_1251jobs.all (Job.check tree)=true := by
  simp only [t5_1251jobs,List.all_append,List.all_nil,t5_1251part0,Bool.and_self]
theorem t5_1251checked : Checked tree [5,5,5,5,10] := by
  refine ⟨plan5127,valid5127,t5_1251choices,?_⟩
  exact check_of_frontier tree 0 t5_1251root t5_1251jobs t5_1251frontier t5_1251all
theorem t5_1252choices : plan5128.choices=[5,5,5,6,6].map (options 5 5) := by rfl


theorem t5_1252part0 : t5_1252jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1252frontier : t5_1252root.frontier 0=t5_1252jobs := by rfl
theorem t5_1252all : t5_1252jobs.all (Job.check tree)=true := by
  simp only [t5_1252jobs,List.all_append,List.all_nil,t5_1252part0,Bool.and_self]
theorem t5_1252checked : Checked tree [5,5,5,6,6] := by
  refine ⟨plan5128,valid5128,t5_1252choices,?_⟩
  exact check_of_frontier tree 0 t5_1252root t5_1252jobs t5_1252frontier t5_1252all
theorem t5_1253choices : plan5129.choices=[5,5,5,6,7].map (options 5 5) := by rfl


theorem t5_1253part0 : t5_1253jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1253frontier : t5_1253root.frontier 0=t5_1253jobs := by rfl
theorem t5_1253all : t5_1253jobs.all (Job.check tree)=true := by
  simp only [t5_1253jobs,List.all_append,List.all_nil,t5_1253part0,Bool.and_self]
theorem t5_1253checked : Checked tree [5,5,5,6,7] := by
  refine ⟨plan5129,valid5129,t5_1253choices,?_⟩
  exact check_of_frontier tree 0 t5_1253root t5_1253jobs t5_1253frontier t5_1253all
theorem t5_1254choices : plan5130.choices=[5,5,5,6,10].map (options 5 5) := by rfl


theorem t5_1254part0 : t5_1254jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1254frontier : t5_1254root.frontier 0=t5_1254jobs := by rfl
theorem t5_1254all : t5_1254jobs.all (Job.check tree)=true := by
  simp only [t5_1254jobs,List.all_append,List.all_nil,t5_1254part0,Bool.and_self]
theorem t5_1254checked : Checked tree [5,5,5,6,10] := by
  refine ⟨plan5130,valid5130,t5_1254choices,?_⟩
  exact check_of_frontier tree 0 t5_1254root t5_1254jobs t5_1254frontier t5_1254all
theorem t5_1255choices : plan5131.choices=[5,5,5,7,7].map (options 5 5) := by rfl


theorem t5_1255part0 : t5_1255jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1255frontier : t5_1255root.frontier 0=t5_1255jobs := by rfl
theorem t5_1255all : t5_1255jobs.all (Job.check tree)=true := by
  simp only [t5_1255jobs,List.all_append,List.all_nil,t5_1255part0,Bool.and_self]
theorem t5_1255checked : Checked tree [5,5,5,7,7] := by
  refine ⟨plan5131,valid5131,t5_1255choices,?_⟩
  exact check_of_frontier tree 0 t5_1255root t5_1255jobs t5_1255frontier t5_1255all
theorem t5_1256choices : plan4877.choices=[5,5,5,9,3].map (options 5 4) := by rfl


theorem t5_1256part0 : t5_1256jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1256frontier : t5_1256root.frontier 0=t5_1256jobs := by rfl
theorem t5_1256all : t5_1256jobs.all (Job.check tree)=true := by
  simp only [t5_1256jobs,List.all_append,List.all_nil,t5_1256part0,Bool.and_self]
theorem t5_1256checked : Checked tree [5,5,5,9,3] := by
  refine ⟨plan4877,valid4877,t5_1256choices,?_⟩
  exact check_of_frontier tree 0 t5_1256root t5_1256jobs t5_1256frontier t5_1256all
theorem t5_1257choices : plan5132.choices=[5,5,5,9,6].map (options 5 5) := by rfl


theorem t5_1257part0 : t5_1257jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1257frontier : t5_1257root.frontier 0=t5_1257jobs := by rfl
theorem t5_1257all : t5_1257jobs.all (Job.check tree)=true := by
  simp only [t5_1257jobs,List.all_append,List.all_nil,t5_1257part0,Bool.and_self]
theorem t5_1257checked : Checked tree [5,5,5,9,6] := by
  refine ⟨plan5132,valid5132,t5_1257choices,?_⟩
  exact check_of_frontier tree 0 t5_1257root t5_1257jobs t5_1257frontier t5_1257all
theorem t5_1258choices : plan5133.choices=[5,5,5,9,7].map (options 5 5) := by rfl


theorem t5_1258part0 : t5_1258jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1258frontier : t5_1258root.frontier 0=t5_1258jobs := by rfl
theorem t5_1258all : t5_1258jobs.all (Job.check tree)=true := by
  simp only [t5_1258jobs,List.all_append,List.all_nil,t5_1258part0,Bool.and_self]
theorem t5_1258checked : Checked tree [5,5,5,9,7] := by
  refine ⟨plan5133,valid5133,t5_1258choices,?_⟩
  exact check_of_frontier tree 0 t5_1258root t5_1258jobs t5_1258frontier t5_1258all
theorem t5_1259choices : plan5134.choices=[5,5,5,9,9].map (options 5 5) := by rfl


theorem t5_1259part0 : t5_1259jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1259frontier : t5_1259root.frontier 0=t5_1259jobs := by rfl
theorem t5_1259all : t5_1259jobs.all (Job.check tree)=true := by
  simp only [t5_1259jobs,List.all_append,List.all_nil,t5_1259part0,Bool.and_self]
theorem t5_1259checked : Checked tree [5,5,5,9,9] := by
  refine ⟨plan5134,valid5134,t5_1259choices,?_⟩
  exact check_of_frontier tree 0 t5_1259root t5_1259jobs t5_1259frontier t5_1259all
theorem t5_1260choices : plan5135.choices=[5,5,5,9,10].map (options 5 5) := by rfl


theorem t5_1260part0 : t5_1260jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1260frontier : t5_1260root.frontier 0=t5_1260jobs := by rfl
theorem t5_1260all : t5_1260jobs.all (Job.check tree)=true := by
  simp only [t5_1260jobs,List.all_append,List.all_nil,t5_1260part0,Bool.and_self]
theorem t5_1260checked : Checked tree [5,5,5,9,10] := by
  refine ⟨plan5135,valid5135,t5_1260choices,?_⟩
  exact check_of_frontier tree 0 t5_1260root t5_1260jobs t5_1260frontier t5_1260all
theorem t5_1261choices : plan5136.choices=[5,5,5,10,7].map (options 5 5) := by rfl


theorem t5_1261part0 : t5_1261jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1261frontier : t5_1261root.frontier 0=t5_1261jobs := by rfl
theorem t5_1261all : t5_1261jobs.all (Job.check tree)=true := by
  simp only [t5_1261jobs,List.all_append,List.all_nil,t5_1261part0,Bool.and_self]
theorem t5_1261checked : Checked tree [5,5,5,10,7] := by
  refine ⟨plan5136,valid5136,t5_1261choices,?_⟩
  exact check_of_frontier tree 0 t5_1261root t5_1261jobs t5_1261frontier t5_1261all
theorem t5_1262choices : plan5137.choices=[5,5,5,10,10].map (options 5 5) := by rfl


theorem t5_1262part0 : t5_1262jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1262frontier : t5_1262root.frontier 0=t5_1262jobs := by rfl
theorem t5_1262all : t5_1262jobs.all (Job.check tree)=true := by
  simp only [t5_1262jobs,List.all_append,List.all_nil,t5_1262part0,Bool.and_self]
theorem t5_1262checked : Checked tree [5,5,5,10,10] := by
  refine ⟨plan5137,valid5137,t5_1262choices,?_⟩
  exact check_of_frontier tree 0 t5_1262root t5_1262jobs t5_1262frontier t5_1262all
theorem t5_1263choices : plan5138.choices=[5,5,6,6,6].map (options 5 5) := by rfl


theorem t5_1263part0 : t5_1263jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1263frontier : t5_1263root.frontier 0=t5_1263jobs := by rfl
theorem t5_1263all : t5_1263jobs.all (Job.check tree)=true := by
  simp only [t5_1263jobs,List.all_append,List.all_nil,t5_1263part0,Bool.and_self]
theorem t5_1263checked : Checked tree [5,5,6,6,6] := by
  refine ⟨plan5138,valid5138,t5_1263choices,?_⟩
  exact check_of_frontier tree 0 t5_1263root t5_1263jobs t5_1263frontier t5_1263all
theorem t5_1264choices : plan5139.choices=[5,5,6,6,7].map (options 5 5) := by rfl


theorem t5_1264part0 : t5_1264jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1264frontier : t5_1264root.frontier 0=t5_1264jobs := by rfl
theorem t5_1264all : t5_1264jobs.all (Job.check tree)=true := by
  simp only [t5_1264jobs,List.all_append,List.all_nil,t5_1264part0,Bool.and_self]
theorem t5_1264checked : Checked tree [5,5,6,6,7] := by
  refine ⟨plan5139,valid5139,t5_1264choices,?_⟩
  exact check_of_frontier tree 0 t5_1264root t5_1264jobs t5_1264frontier t5_1264all
theorem t5_1265choices : plan5140.choices=[5,5,6,6,10].map (options 5 5) := by rfl


theorem t5_1265part0 : t5_1265jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1265frontier : t5_1265root.frontier 0=t5_1265jobs := by rfl
theorem t5_1265all : t5_1265jobs.all (Job.check tree)=true := by
  simp only [t5_1265jobs,List.all_append,List.all_nil,t5_1265part0,Bool.and_self]
theorem t5_1265checked : Checked tree [5,5,6,6,10] := by
  refine ⟨plan5140,valid5140,t5_1265choices,?_⟩
  exact check_of_frontier tree 0 t5_1265root t5_1265jobs t5_1265frontier t5_1265all
theorem t5_1266choices : plan5141.choices=[5,5,6,7,7].map (options 5 5) := by rfl


theorem t5_1266part0 : t5_1266jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1266frontier : t5_1266root.frontier 0=t5_1266jobs := by rfl
theorem t5_1266all : t5_1266jobs.all (Job.check tree)=true := by
  simp only [t5_1266jobs,List.all_append,List.all_nil,t5_1266part0,Bool.and_self]
theorem t5_1266checked : Checked tree [5,5,6,7,7] := by
  refine ⟨plan5141,valid5141,t5_1266choices,?_⟩
  exact check_of_frontier tree 0 t5_1266root t5_1266jobs t5_1266frontier t5_1266all
theorem t5_1267choices : plan5142.choices=[5,5,6,10,7].map (options 5 5) := by rfl


theorem t5_1267part0 : t5_1267jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1267frontier : t5_1267root.frontier 0=t5_1267jobs := by rfl
theorem t5_1267all : t5_1267jobs.all (Job.check tree)=true := by
  simp only [t5_1267jobs,List.all_append,List.all_nil,t5_1267part0,Bool.and_self]
theorem t5_1267checked : Checked tree [5,5,6,10,7] := by
  refine ⟨plan5142,valid5142,t5_1267choices,?_⟩
  exact check_of_frontier tree 0 t5_1267root t5_1267jobs t5_1267frontier t5_1267all
theorem t5_1268choices : plan5143.choices=[5,5,6,10,10].map (options 5 5) := by rfl


theorem t5_1268part0 : t5_1268jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1268frontier : t5_1268root.frontier 0=t5_1268jobs := by rfl
theorem t5_1268all : t5_1268jobs.all (Job.check tree)=true := by
  simp only [t5_1268jobs,List.all_append,List.all_nil,t5_1268part0,Bool.and_self]
theorem t5_1268checked : Checked tree [5,5,6,10,10] := by
  refine ⟨plan5143,valid5143,t5_1268choices,?_⟩
  exact check_of_frontier tree 0 t5_1268root t5_1268jobs t5_1268frontier t5_1268all
theorem t5_1269choices : plan5144.choices=[5,5,7,7,7].map (options 5 5) := by rfl


theorem t5_1269part0 : t5_1269jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1269frontier : t5_1269root.frontier 0=t5_1269jobs := by rfl
theorem t5_1269all : t5_1269jobs.all (Job.check tree)=true := by
  simp only [t5_1269jobs,List.all_append,List.all_nil,t5_1269part0,Bool.and_self]
theorem t5_1269checked : Checked tree [5,5,7,7,7] := by
  refine ⟨plan5144,valid5144,t5_1269choices,?_⟩
  exact check_of_frontier tree 0 t5_1269root t5_1269jobs t5_1269frontier t5_1269all
theorem t5_1270choices : plan4384.choices=[5,5,9,3,3].map (options 5 3) := by rfl


theorem t5_1270part0 : t5_1270jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1270frontier : t5_1270root.frontier 0=t5_1270jobs := by rfl
theorem t5_1270all : t5_1270jobs.all (Job.check tree)=true := by
  simp only [t5_1270jobs,List.all_append,List.all_nil,t5_1270part0,Bool.and_self]
theorem t5_1270checked : Checked tree [5,5,9,3,3] := by
  refine ⟨plan4384,valid4384,t5_1270choices,?_⟩
  exact check_of_frontier tree 0 t5_1270root t5_1270jobs t5_1270frontier t5_1270all
theorem t5_1271choices : plan4878.choices=[5,5,9,3,6].map (options 5 4) := by rfl


theorem t5_1271part0 : t5_1271jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1271frontier : t5_1271root.frontier 0=t5_1271jobs := by rfl
theorem t5_1271all : t5_1271jobs.all (Job.check tree)=true := by
  simp only [t5_1271jobs,List.all_append,List.all_nil,t5_1271part0,Bool.and_self]
theorem t5_1271checked : Checked tree [5,5,9,3,6] := by
  refine ⟨plan4878,valid4878,t5_1271choices,?_⟩
  exact check_of_frontier tree 0 t5_1271root t5_1271jobs t5_1271frontier t5_1271all
theorem t5_1272choices : plan4879.choices=[5,5,9,3,7].map (options 5 4) := by rfl


theorem t5_1272part0 : t5_1272jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1272frontier : t5_1272root.frontier 0=t5_1272jobs := by rfl
theorem t5_1272all : t5_1272jobs.all (Job.check tree)=true := by
  simp only [t5_1272jobs,List.all_append,List.all_nil,t5_1272part0,Bool.and_self]
theorem t5_1272checked : Checked tree [5,5,9,3,7] := by
  refine ⟨plan4879,valid4879,t5_1272choices,?_⟩
  exact check_of_frontier tree 0 t5_1272root t5_1272jobs t5_1272frontier t5_1272all
theorem t5_1273choices : plan4880.choices=[5,5,9,3,10].map (options 5 4) := by rfl


theorem t5_1273part0 : t5_1273jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1273frontier : t5_1273root.frontier 0=t5_1273jobs := by rfl
theorem t5_1273all : t5_1273jobs.all (Job.check tree)=true := by
  simp only [t5_1273jobs,List.all_append,List.all_nil,t5_1273part0,Bool.and_self]
theorem t5_1273checked : Checked tree [5,5,9,3,10] := by
  refine ⟨plan4880,valid4880,t5_1273choices,?_⟩
  exact check_of_frontier tree 0 t5_1273root t5_1273jobs t5_1273frontier t5_1273all
theorem t5_1274choices : plan5145.choices=[5,5,9,6,6].map (options 5 5) := by rfl


theorem t5_1274part0 : t5_1274jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1274frontier : t5_1274root.frontier 0=t5_1274jobs := by rfl
theorem t5_1274all : t5_1274jobs.all (Job.check tree)=true := by
  simp only [t5_1274jobs,List.all_append,List.all_nil,t5_1274part0,Bool.and_self]
theorem t5_1274checked : Checked tree [5,5,9,6,6] := by
  refine ⟨plan5145,valid5145,t5_1274choices,?_⟩
  exact check_of_frontier tree 0 t5_1274root t5_1274jobs t5_1274frontier t5_1274all
theorem t5_1275choices : plan5146.choices=[5,5,9,6,7].map (options 5 5) := by rfl


theorem t5_1275part0 : t5_1275jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1275frontier : t5_1275root.frontier 0=t5_1275jobs := by rfl
theorem t5_1275all : t5_1275jobs.all (Job.check tree)=true := by
  simp only [t5_1275jobs,List.all_append,List.all_nil,t5_1275part0,Bool.and_self]
theorem t5_1275checked : Checked tree [5,5,9,6,7] := by
  refine ⟨plan5146,valid5146,t5_1275choices,?_⟩
  exact check_of_frontier tree 0 t5_1275root t5_1275jobs t5_1275frontier t5_1275all
theorem t5_1276choices : plan5147.choices=[5,5,9,6,10].map (options 5 5) := by rfl


theorem t5_1276part0 : t5_1276jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1276frontier : t5_1276root.frontier 0=t5_1276jobs := by rfl
theorem t5_1276all : t5_1276jobs.all (Job.check tree)=true := by
  simp only [t5_1276jobs,List.all_append,List.all_nil,t5_1276part0,Bool.and_self]
theorem t5_1276checked : Checked tree [5,5,9,6,10] := by
  refine ⟨plan5147,valid5147,t5_1276choices,?_⟩
  exact check_of_frontier tree 0 t5_1276root t5_1276jobs t5_1276frontier t5_1276all
theorem t5_1277choices : plan5148.choices=[5,5,9,7,7].map (options 5 5) := by rfl


theorem t5_1277part0 : t5_1277jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1277frontier : t5_1277root.frontier 0=t5_1277jobs := by rfl
theorem t5_1277all : t5_1277jobs.all (Job.check tree)=true := by
  simp only [t5_1277jobs,List.all_append,List.all_nil,t5_1277part0,Bool.and_self]
theorem t5_1277checked : Checked tree [5,5,9,7,7] := by
  refine ⟨plan5148,valid5148,t5_1277choices,?_⟩
  exact check_of_frontier tree 0 t5_1277root t5_1277jobs t5_1277frontier t5_1277all
theorem t5_1278choices : plan4881.choices=[5,5,9,9,3].map (options 5 4) := by rfl


theorem t5_1278part0 : t5_1278jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1278frontier : t5_1278root.frontier 0=t5_1278jobs := by rfl
theorem t5_1278all : t5_1278jobs.all (Job.check tree)=true := by
  simp only [t5_1278jobs,List.all_append,List.all_nil,t5_1278part0,Bool.and_self]
theorem t5_1278checked : Checked tree [5,5,9,9,3] := by
  refine ⟨plan4881,valid4881,t5_1278choices,?_⟩
  exact check_of_frontier tree 0 t5_1278root t5_1278jobs t5_1278frontier t5_1278all
theorem t5_1279choices : plan5149.choices=[5,5,9,9,6].map (options 5 5) := by rfl


theorem t5_1279part0 : t5_1279jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1279frontier : t5_1279root.frontier 0=t5_1279jobs := by rfl
theorem t5_1279all : t5_1279jobs.all (Job.check tree)=true := by
  simp only [t5_1279jobs,List.all_append,List.all_nil,t5_1279part0,Bool.and_self]
theorem t5_1279checked : Checked tree [5,5,9,9,6] := by
  refine ⟨plan5149,valid5149,t5_1279choices,?_⟩
  exact check_of_frontier tree 0 t5_1279root t5_1279jobs t5_1279frontier t5_1279all
theorem t5_1280choices : plan5150.choices=[5,5,9,9,7].map (options 5 5) := by rfl


theorem t5_1280part0 : t5_1280jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1280frontier : t5_1280root.frontier 0=t5_1280jobs := by rfl
theorem t5_1280all : t5_1280jobs.all (Job.check tree)=true := by
  simp only [t5_1280jobs,List.all_append,List.all_nil,t5_1280part0,Bool.and_self]
theorem t5_1280checked : Checked tree [5,5,9,9,7] := by
  refine ⟨plan5150,valid5150,t5_1280choices,?_⟩
  exact check_of_frontier tree 0 t5_1280root t5_1280jobs t5_1280frontier t5_1280all
theorem t5_1281choices : plan5151.choices=[5,5,9,9,9].map (options 5 5) := by rfl


theorem t5_1281part0 : t5_1281jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1281frontier : t5_1281root.frontier 0=t5_1281jobs := by rfl
theorem t5_1281all : t5_1281jobs.all (Job.check tree)=true := by
  simp only [t5_1281jobs,List.all_append,List.all_nil,t5_1281part0,Bool.and_self]
theorem t5_1281checked : Checked tree [5,5,9,9,9] := by
  refine ⟨plan5151,valid5151,t5_1281choices,?_⟩
  exact check_of_frontier tree 0 t5_1281root t5_1281jobs t5_1281frontier t5_1281all
theorem t5_1282choices : plan5152.choices=[5,5,9,9,10].map (options 5 5) := by rfl


theorem t5_1282part0 : t5_1282jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1282frontier : t5_1282root.frontier 0=t5_1282jobs := by rfl
theorem t5_1282all : t5_1282jobs.all (Job.check tree)=true := by
  simp only [t5_1282jobs,List.all_append,List.all_nil,t5_1282part0,Bool.and_self]
theorem t5_1282checked : Checked tree [5,5,9,9,10] := by
  refine ⟨plan5152,valid5152,t5_1282choices,?_⟩
  exact check_of_frontier tree 0 t5_1282root t5_1282jobs t5_1282frontier t5_1282all
theorem t5_1283choices : plan5153.choices=[5,5,9,10,7].map (options 5 5) := by rfl


theorem t5_1283part0 : t5_1283jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1283frontier : t5_1283root.frontier 0=t5_1283jobs := by rfl
theorem t5_1283all : t5_1283jobs.all (Job.check tree)=true := by
  simp only [t5_1283jobs,List.all_append,List.all_nil,t5_1283part0,Bool.and_self]
theorem t5_1283checked : Checked tree [5,5,9,10,7] := by
  refine ⟨plan5153,valid5153,t5_1283choices,?_⟩
  exact check_of_frontier tree 0 t5_1283root t5_1283jobs t5_1283frontier t5_1283all
theorem t5_1284choices : plan5154.choices=[5,5,9,10,10].map (options 5 5) := by rfl


theorem t5_1284part0 : t5_1284jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1284frontier : t5_1284root.frontier 0=t5_1284jobs := by rfl
theorem t5_1284all : t5_1284jobs.all (Job.check tree)=true := by
  simp only [t5_1284jobs,List.all_append,List.all_nil,t5_1284part0,Bool.and_self]
theorem t5_1284checked : Checked tree [5,5,9,10,10] := by
  refine ⟨plan5154,valid5154,t5_1284choices,?_⟩
  exact check_of_frontier tree 0 t5_1284root t5_1284jobs t5_1284frontier t5_1284all
theorem t5_1285choices : plan5155.choices=[5,5,10,7,7].map (options 5 5) := by rfl


theorem t5_1285part0 : t5_1285jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1285frontier : t5_1285root.frontier 0=t5_1285jobs := by rfl
theorem t5_1285all : t5_1285jobs.all (Job.check tree)=true := by
  simp only [t5_1285jobs,List.all_append,List.all_nil,t5_1285part0,Bool.and_self]
theorem t5_1285checked : Checked tree [5,5,10,7,7] := by
  refine ⟨plan5155,valid5155,t5_1285choices,?_⟩
  exact check_of_frontier tree 0 t5_1285root t5_1285jobs t5_1285frontier t5_1285all
theorem t5_1286choices : plan5156.choices=[5,5,10,10,7].map (options 5 5) := by rfl


theorem t5_1286part0 : t5_1286jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1286frontier : t5_1286root.frontier 0=t5_1286jobs := by rfl
theorem t5_1286all : t5_1286jobs.all (Job.check tree)=true := by
  simp only [t5_1286jobs,List.all_append,List.all_nil,t5_1286part0,Bool.and_self]
theorem t5_1286checked : Checked tree [5,5,10,10,7] := by
  refine ⟨plan5156,valid5156,t5_1286choices,?_⟩
  exact check_of_frontier tree 0 t5_1286root t5_1286jobs t5_1286frontier t5_1286all
theorem t5_1287choices : plan5157.choices=[5,5,10,10,10].map (options 5 5) := by rfl


theorem t5_1287part0 : t5_1287jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1287frontier : t5_1287root.frontier 0=t5_1287jobs := by rfl
theorem t5_1287all : t5_1287jobs.all (Job.check tree)=true := by
  simp only [t5_1287jobs,List.all_append,List.all_nil,t5_1287part0,Bool.and_self]
theorem t5_1287checked : Checked tree [5,5,10,10,10] := by
  refine ⟨plan5157,valid5157,t5_1287choices,?_⟩
  exact check_of_frontier tree 0 t5_1287root t5_1287jobs t5_1287frontier t5_1287all
theorem t5_1288choices : plan5158.choices=[5,6,6,6,6].map (options 5 5) := by rfl


theorem t5_1288part0 : t5_1288jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1288frontier : t5_1288root.frontier 0=t5_1288jobs := by rfl
theorem t5_1288all : t5_1288jobs.all (Job.check tree)=true := by
  simp only [t5_1288jobs,List.all_append,List.all_nil,t5_1288part0,Bool.and_self]
theorem t5_1288checked : Checked tree [5,6,6,6,6] := by
  refine ⟨plan5158,valid5158,t5_1288choices,?_⟩
  exact check_of_frontier tree 0 t5_1288root t5_1288jobs t5_1288frontier t5_1288all
theorem t5_1289choices : plan5159.choices=[5,6,6,6,7].map (options 5 5) := by rfl


theorem t5_1289part0 : t5_1289jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1289frontier : t5_1289root.frontier 0=t5_1289jobs := by rfl
theorem t5_1289all : t5_1289jobs.all (Job.check tree)=true := by
  simp only [t5_1289jobs,List.all_append,List.all_nil,t5_1289part0,Bool.and_self]
theorem t5_1289checked : Checked tree [5,6,6,6,7] := by
  refine ⟨plan5159,valid5159,t5_1289choices,?_⟩
  exact check_of_frontier tree 0 t5_1289root t5_1289jobs t5_1289frontier t5_1289all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks037 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1231checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1242checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1243checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1244checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1245checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1246checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1247checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1248checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1249checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1250checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1251checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1232checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1252checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1253checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1254checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1255checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1256checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1257checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1258checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1259checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1260checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1261checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1233checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1262checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1263checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1264checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1265checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1266checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1267checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1268checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1269checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1270checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1271checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1272checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1273checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1274checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1275checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1276checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1277checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1234checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1278checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1279checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1280checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1281checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1282checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1283checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1284checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1285checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1286checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1287checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1235checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1288checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1289checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1236checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1237checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1238checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1239checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1240checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1241checked⟩
