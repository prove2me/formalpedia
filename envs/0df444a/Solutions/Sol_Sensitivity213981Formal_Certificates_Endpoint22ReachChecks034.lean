-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks034
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:09:04.894209+00:00
-- url     : https://prove2.me/submissions/1c4a1097-0666-4afe-b4db-6e09ab904e8c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks034
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans052
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















































































































































































theorem valid88 : plan88.Valid := valid_step _ _ _ valid0 (by decide +kernel)











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









































































































































theorem valid453 : plan453.Valid := valid_step _ _ _ valid88 (by decide +kernel)

















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













theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid518 : plan518.Valid := valid_step _ _ _ valid106 (by decide +kernel)



theorem valid520 : plan520.Valid := valid_step _ _ _ valid109 (by decide +kernel)





theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid524 : plan524.Valid := valid_step _ _ _ valid111 (by decide +kernel)





theorem valid527 : plan527.Valid := valid_step _ _ _ valid114 (by decide +kernel)





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































theorem valid1264 : plan1264.Valid := valid_step _ _ _ valid453 (by decide +kernel)

































































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









































































































theorem valid2549 : plan2549.Valid := valid_step _ _ _ valid1264 (by decide +kernel)






















































































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

















theorem valid3753 : plan3753.Valid := valid_step _ _ _ valid2549 (by decide +kernel)














































































































































































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

































































theorem valid3969 : plan3969.Valid := valid_step _ _ _ valid2658 (by decide +kernel)

theorem valid3970 : plan3970.Valid := valid_step _ _ _ valid2664 (by decide +kernel)




























































































































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

















































































































theorem valid2841 : plan2841.Valid := valid_step _ _ _ valid1336 (by decide +kernel)

theorem valid2842 : plan2842.Valid := valid_step _ _ _ valid1337 (by decide +kernel)

theorem valid2843 : plan2843.Valid := valid_step _ _ _ valid1338 (by decide +kernel)













theorem valid2850 : plan2850.Valid := valid_step _ _ _ valid1349 (by decide +kernel)









theorem valid2855 : plan2855.Valid := valid_step _ _ _ valid1381 (by decide +kernel)







theorem valid2859 : plan2859.Valid := valid_step _ _ _ valid1336 (by decide +kernel)

theorem valid2860 : plan2860.Valid := valid_step _ _ _ valid1337 (by decide +kernel)

theorem valid2861 : plan2861.Valid := valid_step _ _ _ valid1338 (by decide +kernel)













theorem valid2868 : plan2868.Valid := valid_step _ _ _ valid1381 (by decide +kernel)
























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





























theorem valid1470 : plan1470.Valid := valid_step _ _ _ valid527 (by decide +kernel)





theorem valid1473 : plan1473.Valid := valid_step _ _ _ valid530 (by decide +kernel)

theorem valid1474 : plan1474.Valid := valid_step _ _ _ valid531 (by decide +kernel)

theorem valid1475 : plan1475.Valid := valid_step _ _ _ valid532 (by decide +kernel)

theorem valid1476 : plan1476.Valid := valid_step _ _ _ valid533 (by decide +kernel)



theorem valid1478 : plan1478.Valid := valid_step _ _ _ valid535 (by decide +kernel)





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









theorem valid3077 : plan3077.Valid := valid_step _ _ _ valid1407 (by decide +kernel)

theorem valid3078 : plan3078.Valid := valid_step _ _ _ valid1408 (by decide +kernel)

theorem valid3079 : plan3079.Valid := valid_step _ _ _ valid1409 (by decide +kernel)

theorem valid3080 : plan3080.Valid := valid_step _ _ _ valid1410 (by decide +kernel)

theorem valid3081 : plan3081.Valid := valid_step _ _ _ valid1411 (by decide +kernel)

theorem valid3082 : plan3082.Valid := valid_step _ _ _ valid1412 (by decide +kernel)















theorem valid3090 : plan3090.Valid := valid_step _ _ _ valid1448 (by decide +kernel)

theorem valid3091 : plan3091.Valid := valid_step _ _ _ valid1449 (by decide +kernel)

theorem valid3092 : plan3092.Valid := valid_step _ _ _ valid1450 (by decide +kernel)









theorem valid3097 : plan3097.Valid := valid_step _ _ _ valid1455 (by decide +kernel)














































































































































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

























































































theorem valid4365 : plan4365.Valid := valid_step _ _ _ valid2841 (by decide +kernel)

theorem valid4366 : plan4366.Valid := valid_step _ _ _ valid2842 (by decide +kernel)

theorem valid4367 : plan4367.Valid := valid_step _ _ _ valid2843 (by decide +kernel)

theorem valid4368 : plan4368.Valid := valid_step _ _ _ valid2850 (by decide +kernel)

theorem valid4369 : plan4369.Valid := valid_step _ _ _ valid2855 (by decide +kernel)

theorem valid4370 : plan4370.Valid := valid_step _ _ _ valid2859 (by decide +kernel)

theorem valid4371 : plan4371.Valid := valid_step _ _ _ valid2860 (by decide +kernel)

theorem valid4372 : plan4372.Valid := valid_step _ _ _ valid2861 (by decide +kernel)

theorem valid4373 : plan4373.Valid := valid_step _ _ _ valid2868 (by decide +kernel)






















































































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























































theorem valid4828 : plan4828.Valid := valid_step _ _ _ valid3030 (by decide +kernel)

theorem valid4829 : plan4829.Valid := valid_step _ _ _ valid3031 (by decide +kernel)

theorem valid4830 : plan4830.Valid := valid_step _ _ _ valid3032 (by decide +kernel)

theorem valid4831 : plan4831.Valid := valid_step _ _ _ valid3033 (by decide +kernel)

theorem valid4832 : plan4832.Valid := valid_step _ _ _ valid3034 (by decide +kernel)

theorem valid4833 : plan4833.Valid := valid_step _ _ _ valid3035 (by decide +kernel)

theorem valid4834 : plan4834.Valid := valid_step _ _ _ valid3036 (by decide +kernel)

theorem valid4835 : plan4835.Valid := valid_step _ _ _ valid3037 (by decide +kernel)

theorem valid4836 : plan4836.Valid := valid_step _ _ _ valid3038 (by decide +kernel)

theorem valid4837 : plan4837.Valid := valid_step _ _ _ valid3039 (by decide +kernel)

theorem valid4838 : plan4838.Valid := valid_step _ _ _ valid3040 (by decide +kernel)

theorem valid4839 : plan4839.Valid := valid_step _ _ _ valid3041 (by decide +kernel)

theorem valid4840 : plan4840.Valid := valid_step _ _ _ valid3042 (by decide +kernel)

theorem valid4841 : plan4841.Valid := valid_step _ _ _ valid3043 (by decide +kernel)

theorem valid4842 : plan4842.Valid := valid_step _ _ _ valid3044 (by decide +kernel)

theorem valid4843 : plan4843.Valid := valid_step _ _ _ valid3060 (by decide +kernel)

theorem valid4844 : plan4844.Valid := valid_step _ _ _ valid3064 (by decide +kernel)

theorem valid4845 : plan4845.Valid := valid_step _ _ _ valid3065 (by decide +kernel)

theorem valid4846 : plan4846.Valid := valid_step _ _ _ valid3066 (by decide +kernel)

theorem valid4847 : plan4847.Valid := valid_step _ _ _ valid3077 (by decide +kernel)

theorem valid4848 : plan4848.Valid := valid_step _ _ _ valid3078 (by decide +kernel)

theorem valid4849 : plan4849.Valid := valid_step _ _ _ valid3079 (by decide +kernel)

theorem valid4850 : plan4850.Valid := valid_step _ _ _ valid3080 (by decide +kernel)

theorem valid4851 : plan4851.Valid := valid_step _ _ _ valid3081 (by decide +kernel)

theorem valid4852 : plan4852.Valid := valid_step _ _ _ valid3082 (by decide +kernel)

theorem valid4853 : plan4853.Valid := valid_step _ _ _ valid3090 (by decide +kernel)

theorem valid4854 : plan4854.Valid := valid_step _ _ _ valid3091 (by decide +kernel)

theorem valid4855 : plan4855.Valid := valid_step _ _ _ valid3092 (by decide +kernel)

theorem valid4856 : plan4856.Valid := valid_step _ _ _ valid3097 (by decide +kernel)
















































































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

theorem valid3216 : plan3216.Valid := valid_step _ _ _ valid1483 (by decide +kernel)

theorem valid3217 : plan3217.Valid := valid_step _ _ _ valid1484 (by decide +kernel)

theorem valid3218 : plan3218.Valid := valid_step _ _ _ valid1485 (by decide +kernel)

theorem valid3219 : plan3219.Valid := valid_step _ _ _ valid1486 (by decide +kernel)

theorem valid3220 : plan3220.Valid := valid_step _ _ _ valid1487 (by decide +kernel)

theorem valid3221 : plan3221.Valid := valid_step _ _ _ valid1488 (by decide +kernel)

theorem valid3222 : plan3222.Valid := valid_step _ _ _ valid1489 (by decide +kernel)

theorem valid3223 : plan3223.Valid := valid_step _ _ _ valid1493 (by decide +kernel)

theorem valid3224 : plan3224.Valid := valid_step _ _ _ valid1494 (by decide +kernel)

theorem valid3225 : plan3225.Valid := valid_step _ _ _ valid1495 (by decide +kernel)

theorem valid3226 : plan3226.Valid := valid_step _ _ _ valid1496 (by decide +kernel)

theorem valid3227 : plan3227.Valid := valid_step _ _ _ valid1497 (by decide +kernel)

theorem valid3228 : plan3228.Valid := valid_step _ _ _ valid1498 (by decide +kernel)



theorem valid3230 : plan3230.Valid := valid_step _ _ _ valid1500 (by decide +kernel)

theorem valid3231 : plan3231.Valid := valid_step _ _ _ valid1501 (by decide +kernel)

theorem valid3232 : plan3232.Valid := valid_step _ _ _ valid1502 (by decide +kernel)

theorem valid3233 : plan3233.Valid := valid_step _ _ _ valid1503 (by decide +kernel)

theorem valid3234 : plan3234.Valid := valid_step _ _ _ valid1504 (by decide +kernel)

theorem valid3235 : plan3235.Valid := valid_step _ _ _ valid1505 (by decide +kernel)

theorem valid3236 : plan3236.Valid := valid_step _ _ _ valid1489 (by decide +kernel)

theorem valid3237 : plan3237.Valid := valid_step _ _ _ valid1503 (by decide +kernel)

theorem valid3238 : plan3238.Valid := valid_step _ _ _ valid1504 (by decide +kernel)

theorem valid3239 : plan3239.Valid := valid_step _ _ _ valid1505 (by decide +kernel)


















































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































































































































































theorem valid5072 : plan5072.Valid := valid_step _ _ _ valid3188 (by decide +kernel)

theorem valid5073 : plan5073.Valid := valid_step _ _ _ valid3189 (by decide +kernel)

theorem valid5074 : plan5074.Valid := valid_step _ _ _ valid3190 (by decide +kernel)

theorem valid5075 : plan5075.Valid := valid_step _ _ _ valid3191 (by decide +kernel)

theorem valid5076 : plan5076.Valid := valid_step _ _ _ valid3192 (by decide +kernel)

theorem valid5077 : plan5077.Valid := valid_step _ _ _ valid3193 (by decide +kernel)

theorem valid5078 : plan5078.Valid := valid_step _ _ _ valid3194 (by decide +kernel)

theorem valid5079 : plan5079.Valid := valid_step _ _ _ valid3195 (by decide +kernel)

theorem valid5080 : plan5080.Valid := valid_step _ _ _ valid3196 (by decide +kernel)

theorem valid5081 : plan5081.Valid := valid_step _ _ _ valid3197 (by decide +kernel)

theorem valid5082 : plan5082.Valid := valid_step _ _ _ valid3198 (by decide +kernel)

theorem valid5083 : plan5083.Valid := valid_step _ _ _ valid3199 (by decide +kernel)

theorem valid5084 : plan5084.Valid := valid_step _ _ _ valid3200 (by decide +kernel)

theorem valid5085 : plan5085.Valid := valid_step _ _ _ valid3201 (by decide +kernel)

theorem valid5086 : plan5086.Valid := valid_step _ _ _ valid3202 (by decide +kernel)

theorem valid5087 : plan5087.Valid := valid_step _ _ _ valid3203 (by decide +kernel)

theorem valid5088 : plan5088.Valid := valid_step _ _ _ valid3204 (by decide +kernel)
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

theorem valid5089 : plan5089.Valid := valid_step _ _ _ valid3205 (by decide +kernel)

theorem valid5090 : plan5090.Valid := valid_step _ _ _ valid3206 (by decide +kernel)

theorem valid5091 : plan5091.Valid := valid_step _ _ _ valid3207 (by decide +kernel)

theorem valid5092 : plan5092.Valid := valid_step _ _ _ valid3208 (by decide +kernel)

theorem valid5093 : plan5093.Valid := valid_step _ _ _ valid3209 (by decide +kernel)

theorem valid5094 : plan5094.Valid := valid_step _ _ _ valid3210 (by decide +kernel)

theorem valid5095 : plan5095.Valid := valid_step _ _ _ valid3211 (by decide +kernel)

theorem valid5096 : plan5096.Valid := valid_step _ _ _ valid3212 (by decide +kernel)

theorem valid5097 : plan5097.Valid := valid_step _ _ _ valid3213 (by decide +kernel)

theorem valid5098 : plan5098.Valid := valid_step _ _ _ valid3214 (by decide +kernel)

theorem valid5099 : plan5099.Valid := valid_step _ _ _ valid3215 (by decide +kernel)

theorem valid5100 : plan5100.Valid := valid_step _ _ _ valid3216 (by decide +kernel)

theorem valid5101 : plan5101.Valid := valid_step _ _ _ valid3217 (by decide +kernel)

theorem valid5102 : plan5102.Valid := valid_step _ _ _ valid3218 (by decide +kernel)

theorem valid5103 : plan5103.Valid := valid_step _ _ _ valid3219 (by decide +kernel)

theorem valid5104 : plan5104.Valid := valid_step _ _ _ valid3220 (by decide +kernel)

theorem valid5105 : plan5105.Valid := valid_step _ _ _ valid3221 (by decide +kernel)

theorem valid5106 : plan5106.Valid := valid_step _ _ _ valid3222 (by decide +kernel)

theorem valid5107 : plan5107.Valid := valid_step _ _ _ valid3223 (by decide +kernel)

theorem valid5108 : plan5108.Valid := valid_step _ _ _ valid3224 (by decide +kernel)

theorem valid5109 : plan5109.Valid := valid_step _ _ _ valid3225 (by decide +kernel)

theorem valid5110 : plan5110.Valid := valid_step _ _ _ valid3226 (by decide +kernel)

theorem valid5111 : plan5111.Valid := valid_step _ _ _ valid3227 (by decide +kernel)

theorem valid5112 : plan5112.Valid := valid_step _ _ _ valid3228 (by decide +kernel)

theorem valid5113 : plan5113.Valid := valid_step _ _ _ valid3230 (by decide +kernel)

theorem valid5114 : plan5114.Valid := valid_step _ _ _ valid3231 (by decide +kernel)

theorem valid5115 : plan5115.Valid := valid_step _ _ _ valid3232 (by decide +kernel)

theorem valid5116 : plan5116.Valid := valid_step _ _ _ valid3233 (by decide +kernel)

theorem valid5117 : plan5117.Valid := valid_step _ _ _ valid3234 (by decide +kernel)

theorem valid5118 : plan5118.Valid := valid_step _ _ _ valid3235 (by decide +kernel)

theorem valid5119 : plan5119.Valid := valid_step _ _ _ valid3236 (by decide +kernel)

theorem valid5120 : plan5120.Valid := valid_step _ _ _ valid3237 (by decide +kernel)

theorem valid5121 : plan5121.Valid := valid_step _ _ _ valid3238 (by decide +kernel)

theorem valid5122 : plan5122.Valid := valid_step _ _ _ valid3239 (by decide +kernel)




























































































































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
theorem t5_1121choices : plan4828.choices=[4,8,2,6,7].map (options 5 4) := by rfl


theorem t5_1121part0 : t5_1121jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1121frontier : t5_1121root.frontier 0=t5_1121jobs := by rfl
theorem t5_1121all : t5_1121jobs.all (Job.check tree)=true := by
  simp only [t5_1121jobs,List.all_append,List.all_nil,t5_1121part0,Bool.and_self]
theorem t5_1121checked : Checked tree [4,8,2,6,7] := by
  refine ⟨plan4828,valid4828,t5_1121choices,?_⟩
  exact check_of_frontier tree 0 t5_1121root t5_1121jobs t5_1121frontier t5_1121all
theorem t5_1122choices : plan4829.choices=[4,8,2,6,10].map (options 5 4) := by rfl


theorem t5_1122part0 : t5_1122jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1122frontier : t5_1122root.frontier 0=t5_1122jobs := by rfl
theorem t5_1122all : t5_1122jobs.all (Job.check tree)=true := by
  simp only [t5_1122jobs,List.all_append,List.all_nil,t5_1122part0,Bool.and_self]
theorem t5_1122checked : Checked tree [4,8,2,6,10] := by
  refine ⟨plan4829,valid4829,t5_1122choices,?_⟩
  exact check_of_frontier tree 0 t5_1122root t5_1122jobs t5_1122frontier t5_1122all
theorem t5_1123choices : plan4830.choices=[4,8,2,7,7].map (options 5 4) := by rfl


theorem t5_1123part0 : t5_1123jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1123frontier : t5_1123root.frontier 0=t5_1123jobs := by rfl
theorem t5_1123all : t5_1123jobs.all (Job.check tree)=true := by
  simp only [t5_1123jobs,List.all_append,List.all_nil,t5_1123part0,Bool.and_self]
theorem t5_1123checked : Checked tree [4,8,2,7,7] := by
  refine ⟨plan4830,valid4830,t5_1123choices,?_⟩
  exact check_of_frontier tree 0 t5_1123root t5_1123jobs t5_1123frontier t5_1123all
theorem t5_1124choices : plan4831.choices=[4,8,2,9,7].map (options 5 4) := by rfl


theorem t5_1124part0 : t5_1124jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1124frontier : t5_1124root.frontier 0=t5_1124jobs := by rfl
theorem t5_1124all : t5_1124jobs.all (Job.check tree)=true := by
  simp only [t5_1124jobs,List.all_append,List.all_nil,t5_1124part0,Bool.and_self]
theorem t5_1124checked : Checked tree [4,8,2,9,7] := by
  refine ⟨plan4831,valid4831,t5_1124choices,?_⟩
  exact check_of_frontier tree 0 t5_1124root t5_1124jobs t5_1124frontier t5_1124all
theorem t5_1125choices : plan4832.choices=[4,8,2,10,7].map (options 5 4) := by rfl


theorem t5_1125part0 : t5_1125jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1125frontier : t5_1125root.frontier 0=t5_1125jobs := by rfl
theorem t5_1125all : t5_1125jobs.all (Job.check tree)=true := by
  simp only [t5_1125jobs,List.all_append,List.all_nil,t5_1125part0,Bool.and_self]
theorem t5_1125checked : Checked tree [4,8,2,10,7] := by
  refine ⟨plan4832,valid4832,t5_1125choices,?_⟩
  exact check_of_frontier tree 0 t5_1125root t5_1125jobs t5_1125frontier t5_1125all
theorem t5_1126choices : plan4833.choices=[4,8,2,10,10].map (options 5 4) := by rfl


theorem t5_1126part0 : t5_1126jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1126frontier : t5_1126root.frontier 0=t5_1126jobs := by rfl
theorem t5_1126all : t5_1126jobs.all (Job.check tree)=true := by
  simp only [t5_1126jobs,List.all_append,List.all_nil,t5_1126part0,Bool.and_self]
theorem t5_1126checked : Checked tree [4,8,2,10,10] := by
  refine ⟨plan4833,valid4833,t5_1126choices,?_⟩
  exact check_of_frontier tree 0 t5_1126root t5_1126jobs t5_1126frontier t5_1126all
theorem t5_1127choices : plan3969.choices=[4,8,3,3,3].map (options 5 2) := by rfl


theorem t5_1127part0 : t5_1127jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1127frontier : t5_1127root.frontier 0=t5_1127jobs := by rfl
theorem t5_1127all : t5_1127jobs.all (Job.check tree)=true := by
  simp only [t5_1127jobs,List.all_append,List.all_nil,t5_1127part0,Bool.and_self]
theorem t5_1127checked : Checked tree [4,8,3,3,3] := by
  refine ⟨plan3969,valid3969,t5_1127choices,?_⟩
  exact check_of_frontier tree 0 t5_1127root t5_1127jobs t5_1127frontier t5_1127all
theorem t5_1128choices : plan4365.choices=[4,8,3,3,6].map (options 5 3) := by rfl


theorem t5_1128part0 : t5_1128jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1128frontier : t5_1128root.frontier 0=t5_1128jobs := by rfl
theorem t5_1128all : t5_1128jobs.all (Job.check tree)=true := by
  simp only [t5_1128jobs,List.all_append,List.all_nil,t5_1128part0,Bool.and_self]
theorem t5_1128checked : Checked tree [4,8,3,3,6] := by
  refine ⟨plan4365,valid4365,t5_1128choices,?_⟩
  exact check_of_frontier tree 0 t5_1128root t5_1128jobs t5_1128frontier t5_1128all
theorem t5_1129choices : plan4366.choices=[4,8,3,3,7].map (options 5 3) := by rfl


theorem t5_1129part0 : t5_1129jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1129frontier : t5_1129root.frontier 0=t5_1129jobs := by rfl
theorem t5_1129all : t5_1129jobs.all (Job.check tree)=true := by
  simp only [t5_1129jobs,List.all_append,List.all_nil,t5_1129part0,Bool.and_self]
theorem t5_1129checked : Checked tree [4,8,3,3,7] := by
  refine ⟨plan4366,valid4366,t5_1129choices,?_⟩
  exact check_of_frontier tree 0 t5_1129root t5_1129jobs t5_1129frontier t5_1129all
theorem t5_1130choices : plan4367.choices=[4,8,3,3,10].map (options 5 3) := by rfl


theorem t5_1130part0 : t5_1130jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1130frontier : t5_1130root.frontier 0=t5_1130jobs := by rfl
theorem t5_1130all : t5_1130jobs.all (Job.check tree)=true := by
  simp only [t5_1130jobs,List.all_append,List.all_nil,t5_1130part0,Bool.and_self]
theorem t5_1130checked : Checked tree [4,8,3,3,10] := by
  refine ⟨plan4367,valid4367,t5_1130choices,?_⟩
  exact check_of_frontier tree 0 t5_1130root t5_1130jobs t5_1130frontier t5_1130all
theorem t5_1131choices : plan4834.choices=[4,8,3,6,6].map (options 5 4) := by rfl


theorem t5_1131part0 : t5_1131jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1131frontier : t5_1131root.frontier 0=t5_1131jobs := by rfl
theorem t5_1131all : t5_1131jobs.all (Job.check tree)=true := by
  simp only [t5_1131jobs,List.all_append,List.all_nil,t5_1131part0,Bool.and_self]
theorem t5_1131checked : Checked tree [4,8,3,6,6] := by
  refine ⟨plan4834,valid4834,t5_1131choices,?_⟩
  exact check_of_frontier tree 0 t5_1131root t5_1131jobs t5_1131frontier t5_1131all
theorem t5_1132choices : plan4835.choices=[4,8,3,6,7].map (options 5 4) := by rfl


theorem t5_1132part0 : t5_1132jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1132frontier : t5_1132root.frontier 0=t5_1132jobs := by rfl
theorem t5_1132all : t5_1132jobs.all (Job.check tree)=true := by
  simp only [t5_1132jobs,List.all_append,List.all_nil,t5_1132part0,Bool.and_self]
theorem t5_1132checked : Checked tree [4,8,3,6,7] := by
  refine ⟨plan4835,valid4835,t5_1132choices,?_⟩
  exact check_of_frontier tree 0 t5_1132root t5_1132jobs t5_1132frontier t5_1132all
theorem t5_1133choices : plan4836.choices=[4,8,3,6,10].map (options 5 4) := by rfl


theorem t5_1133part0 : t5_1133jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1133frontier : t5_1133root.frontier 0=t5_1133jobs := by rfl
theorem t5_1133all : t5_1133jobs.all (Job.check tree)=true := by
  simp only [t5_1133jobs,List.all_append,List.all_nil,t5_1133part0,Bool.and_self]
theorem t5_1133checked : Checked tree [4,8,3,6,10] := by
  refine ⟨plan4836,valid4836,t5_1133choices,?_⟩
  exact check_of_frontier tree 0 t5_1133root t5_1133jobs t5_1133frontier t5_1133all
theorem t5_1134choices : plan4837.choices=[4,8,3,7,7].map (options 5 4) := by rfl


theorem t5_1134part0 : t5_1134jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1134frontier : t5_1134root.frontier 0=t5_1134jobs := by rfl
theorem t5_1134all : t5_1134jobs.all (Job.check tree)=true := by
  simp only [t5_1134jobs,List.all_append,List.all_nil,t5_1134part0,Bool.and_self]
theorem t5_1134checked : Checked tree [4,8,3,7,7] := by
  refine ⟨plan4837,valid4837,t5_1134choices,?_⟩
  exact check_of_frontier tree 0 t5_1134root t5_1134jobs t5_1134frontier t5_1134all
theorem t5_1135choices : plan4838.choices=[4,8,3,10,7].map (options 5 4) := by rfl


theorem t5_1135part0 : t5_1135jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1135frontier : t5_1135root.frontier 0=t5_1135jobs := by rfl
theorem t5_1135all : t5_1135jobs.all (Job.check tree)=true := by
  simp only [t5_1135jobs,List.all_append,List.all_nil,t5_1135part0,Bool.and_self]
theorem t5_1135checked : Checked tree [4,8,3,10,7] := by
  refine ⟨plan4838,valid4838,t5_1135choices,?_⟩
  exact check_of_frontier tree 0 t5_1135root t5_1135jobs t5_1135frontier t5_1135all
theorem t5_1136choices : plan4839.choices=[4,8,3,10,10].map (options 5 4) := by rfl


theorem t5_1136part0 : t5_1136jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1136frontier : t5_1136root.frontier 0=t5_1136jobs := by rfl
theorem t5_1136all : t5_1136jobs.all (Job.check tree)=true := by
  simp only [t5_1136jobs,List.all_append,List.all_nil,t5_1136part0,Bool.and_self]
theorem t5_1136checked : Checked tree [4,8,3,10,10] := by
  refine ⟨plan4839,valid4839,t5_1136choices,?_⟩
  exact check_of_frontier tree 0 t5_1136root t5_1136jobs t5_1136frontier t5_1136all
theorem t5_1137choices : plan4368.choices=[4,8,5,3,3].map (options 5 3) := by rfl


theorem t5_1137part0 : t5_1137jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1137frontier : t5_1137root.frontier 0=t5_1137jobs := by rfl
theorem t5_1137all : t5_1137jobs.all (Job.check tree)=true := by
  simp only [t5_1137jobs,List.all_append,List.all_nil,t5_1137part0,Bool.and_self]
theorem t5_1137checked : Checked tree [4,8,5,3,3] := by
  refine ⟨plan4368,valid4368,t5_1137choices,?_⟩
  exact check_of_frontier tree 0 t5_1137root t5_1137jobs t5_1137frontier t5_1137all
theorem t5_1138choices : plan4840.choices=[4,8,5,3,6].map (options 5 4) := by rfl


theorem t5_1138part0 : t5_1138jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1138frontier : t5_1138root.frontier 0=t5_1138jobs := by rfl
theorem t5_1138all : t5_1138jobs.all (Job.check tree)=true := by
  simp only [t5_1138jobs,List.all_append,List.all_nil,t5_1138part0,Bool.and_self]
theorem t5_1138checked : Checked tree [4,8,5,3,6] := by
  refine ⟨plan4840,valid4840,t5_1138choices,?_⟩
  exact check_of_frontier tree 0 t5_1138root t5_1138jobs t5_1138frontier t5_1138all
theorem t5_1139choices : plan4841.choices=[4,8,5,3,7].map (options 5 4) := by rfl


theorem t5_1139part0 : t5_1139jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1139frontier : t5_1139root.frontier 0=t5_1139jobs := by rfl
theorem t5_1139all : t5_1139jobs.all (Job.check tree)=true := by
  simp only [t5_1139jobs,List.all_append,List.all_nil,t5_1139part0,Bool.and_self]
theorem t5_1139checked : Checked tree [4,8,5,3,7] := by
  refine ⟨plan4841,valid4841,t5_1139choices,?_⟩
  exact check_of_frontier tree 0 t5_1139root t5_1139jobs t5_1139frontier t5_1139all
theorem t5_1140choices : plan4842.choices=[4,8,5,3,10].map (options 5 4) := by rfl


theorem t5_1140part0 : t5_1140jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1140frontier : t5_1140root.frontier 0=t5_1140jobs := by rfl
theorem t5_1140all : t5_1140jobs.all (Job.check tree)=true := by
  simp only [t5_1140jobs,List.all_append,List.all_nil,t5_1140part0,Bool.and_self]
theorem t5_1140checked : Checked tree [4,8,5,3,10] := by
  refine ⟨plan4842,valid4842,t5_1140choices,?_⟩
  exact check_of_frontier tree 0 t5_1140root t5_1140jobs t5_1140frontier t5_1140all
theorem t5_1141choices : plan5072.choices=[4,8,5,5,7].map (options 5 5) := by rfl


theorem t5_1141part0 : t5_1141jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1141frontier : t5_1141root.frontier 0=t5_1141jobs := by rfl
theorem t5_1141all : t5_1141jobs.all (Job.check tree)=true := by
  simp only [t5_1141jobs,List.all_append,List.all_nil,t5_1141part0,Bool.and_self]
theorem t5_1141checked : Checked tree [4,8,5,5,7] := by
  refine ⟨plan5072,valid5072,t5_1141choices,?_⟩
  exact check_of_frontier tree 0 t5_1141root t5_1141jobs t5_1141frontier t5_1141all
theorem t5_1142choices : plan5073.choices=[4,8,5,6,6].map (options 5 5) := by rfl


theorem t5_1142part0 : t5_1142jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1142frontier : t5_1142root.frontier 0=t5_1142jobs := by rfl
theorem t5_1142all : t5_1142jobs.all (Job.check tree)=true := by
  simp only [t5_1142jobs,List.all_append,List.all_nil,t5_1142part0,Bool.and_self]
theorem t5_1142checked : Checked tree [4,8,5,6,6] := by
  refine ⟨plan5073,valid5073,t5_1142choices,?_⟩
  exact check_of_frontier tree 0 t5_1142root t5_1142jobs t5_1142frontier t5_1142all
theorem t5_1143choices : plan5074.choices=[4,8,5,6,7].map (options 5 5) := by rfl


theorem t5_1143part0 : t5_1143jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1143frontier : t5_1143root.frontier 0=t5_1143jobs := by rfl
theorem t5_1143all : t5_1143jobs.all (Job.check tree)=true := by
  simp only [t5_1143jobs,List.all_append,List.all_nil,t5_1143part0,Bool.and_self]
theorem t5_1143checked : Checked tree [4,8,5,6,7] := by
  refine ⟨plan5074,valid5074,t5_1143choices,?_⟩
  exact check_of_frontier tree 0 t5_1143root t5_1143jobs t5_1143frontier t5_1143all
theorem t5_1144choices : plan5075.choices=[4,8,5,6,10].map (options 5 5) := by rfl


theorem t5_1144part0 : t5_1144jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1144frontier : t5_1144root.frontier 0=t5_1144jobs := by rfl
theorem t5_1144all : t5_1144jobs.all (Job.check tree)=true := by
  simp only [t5_1144jobs,List.all_append,List.all_nil,t5_1144part0,Bool.and_self]
theorem t5_1144checked : Checked tree [4,8,5,6,10] := by
  refine ⟨plan5075,valid5075,t5_1144choices,?_⟩
  exact check_of_frontier tree 0 t5_1144root t5_1144jobs t5_1144frontier t5_1144all
theorem t5_1145choices : plan5076.choices=[4,8,5,7,7].map (options 5 5) := by rfl


theorem t5_1145part0 : t5_1145jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1145frontier : t5_1145root.frontier 0=t5_1145jobs := by rfl
theorem t5_1145all : t5_1145jobs.all (Job.check tree)=true := by
  simp only [t5_1145jobs,List.all_append,List.all_nil,t5_1145part0,Bool.and_self]
theorem t5_1145checked : Checked tree [4,8,5,7,7] := by
  refine ⟨plan5076,valid5076,t5_1145choices,?_⟩
  exact check_of_frontier tree 0 t5_1145root t5_1145jobs t5_1145frontier t5_1145all
theorem t5_1146choices : plan5077.choices=[4,8,5,9,7].map (options 5 5) := by rfl


theorem t5_1146part0 : t5_1146jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1146frontier : t5_1146root.frontier 0=t5_1146jobs := by rfl
theorem t5_1146all : t5_1146jobs.all (Job.check tree)=true := by
  simp only [t5_1146jobs,List.all_append,List.all_nil,t5_1146part0,Bool.and_self]
theorem t5_1146checked : Checked tree [4,8,5,9,7] := by
  refine ⟨plan5077,valid5077,t5_1146choices,?_⟩
  exact check_of_frontier tree 0 t5_1146root t5_1146jobs t5_1146frontier t5_1146all
theorem t5_1147choices : plan5078.choices=[4,8,5,10,7].map (options 5 5) := by rfl


theorem t5_1147part0 : t5_1147jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1147frontier : t5_1147root.frontier 0=t5_1147jobs := by rfl
theorem t5_1147all : t5_1147jobs.all (Job.check tree)=true := by
  simp only [t5_1147jobs,List.all_append,List.all_nil,t5_1147part0,Bool.and_self]
theorem t5_1147checked : Checked tree [4,8,5,10,7] := by
  refine ⟨plan5078,valid5078,t5_1147choices,?_⟩
  exact check_of_frontier tree 0 t5_1147root t5_1147jobs t5_1147frontier t5_1147all
theorem t5_1148choices : plan5079.choices=[4,8,5,10,10].map (options 5 5) := by rfl


theorem t5_1148part0 : t5_1148jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1148frontier : t5_1148root.frontier 0=t5_1148jobs := by rfl
theorem t5_1148all : t5_1148jobs.all (Job.check tree)=true := by
  simp only [t5_1148jobs,List.all_append,List.all_nil,t5_1148part0,Bool.and_self]
theorem t5_1148checked : Checked tree [4,8,5,10,10] := by
  refine ⟨plan5079,valid5079,t5_1148choices,?_⟩
  exact check_of_frontier tree 0 t5_1148root t5_1148jobs t5_1148frontier t5_1148all
theorem t5_1149choices : plan5080.choices=[4,8,6,6,6].map (options 5 5) := by rfl


theorem t5_1149part0 : t5_1149jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1149frontier : t5_1149root.frontier 0=t5_1149jobs := by rfl
theorem t5_1149all : t5_1149jobs.all (Job.check tree)=true := by
  simp only [t5_1149jobs,List.all_append,List.all_nil,t5_1149part0,Bool.and_self]
theorem t5_1149checked : Checked tree [4,8,6,6,6] := by
  refine ⟨plan5080,valid5080,t5_1149choices,?_⟩
  exact check_of_frontier tree 0 t5_1149root t5_1149jobs t5_1149frontier t5_1149all
theorem t5_1150choices : plan5081.choices=[4,8,6,6,7].map (options 5 5) := by rfl


theorem t5_1150part0 : t5_1150jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1150frontier : t5_1150root.frontier 0=t5_1150jobs := by rfl
theorem t5_1150all : t5_1150jobs.all (Job.check tree)=true := by
  simp only [t5_1150jobs,List.all_append,List.all_nil,t5_1150part0,Bool.and_self]
theorem t5_1150checked : Checked tree [4,8,6,6,7] := by
  refine ⟨plan5081,valid5081,t5_1150choices,?_⟩
  exact check_of_frontier tree 0 t5_1150root t5_1150jobs t5_1150frontier t5_1150all
theorem t5_1151choices : plan5082.choices=[4,8,6,6,10].map (options 5 5) := by rfl


theorem t5_1151part0 : t5_1151jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1151frontier : t5_1151root.frontier 0=t5_1151jobs := by rfl
theorem t5_1151all : t5_1151jobs.all (Job.check tree)=true := by
  simp only [t5_1151jobs,List.all_append,List.all_nil,t5_1151part0,Bool.and_self]
theorem t5_1151checked : Checked tree [4,8,6,6,10] := by
  refine ⟨plan5082,valid5082,t5_1151choices,?_⟩
  exact check_of_frontier tree 0 t5_1151root t5_1151jobs t5_1151frontier t5_1151all
theorem t5_1152choices : plan5083.choices=[4,8,6,7,7].map (options 5 5) := by rfl


theorem t5_1152part0 : t5_1152jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1152frontier : t5_1152root.frontier 0=t5_1152jobs := by rfl
theorem t5_1152all : t5_1152jobs.all (Job.check tree)=true := by
  simp only [t5_1152jobs,List.all_append,List.all_nil,t5_1152part0,Bool.and_self]
theorem t5_1152checked : Checked tree [4,8,6,7,7] := by
  refine ⟨plan5083,valid5083,t5_1152choices,?_⟩
  exact check_of_frontier tree 0 t5_1152root t5_1152jobs t5_1152frontier t5_1152all
theorem t5_1153choices : plan5084.choices=[4,8,6,10,7].map (options 5 5) := by rfl


theorem t5_1153part0 : t5_1153jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1153frontier : t5_1153root.frontier 0=t5_1153jobs := by rfl
theorem t5_1153all : t5_1153jobs.all (Job.check tree)=true := by
  simp only [t5_1153jobs,List.all_append,List.all_nil,t5_1153part0,Bool.and_self]
theorem t5_1153checked : Checked tree [4,8,6,10,7] := by
  refine ⟨plan5084,valid5084,t5_1153choices,?_⟩
  exact check_of_frontier tree 0 t5_1153root t5_1153jobs t5_1153frontier t5_1153all
theorem t5_1154choices : plan5085.choices=[4,8,6,10,10].map (options 5 5) := by rfl


theorem t5_1154part0 : t5_1154jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1154frontier : t5_1154root.frontier 0=t5_1154jobs := by rfl
theorem t5_1154all : t5_1154jobs.all (Job.check tree)=true := by
  simp only [t5_1154jobs,List.all_append,List.all_nil,t5_1154part0,Bool.and_self]
theorem t5_1154checked : Checked tree [4,8,6,10,10] := by
  refine ⟨plan5085,valid5085,t5_1154choices,?_⟩
  exact check_of_frontier tree 0 t5_1154root t5_1154jobs t5_1154frontier t5_1154all
theorem t5_1155choices : plan5086.choices=[4,8,7,7,7].map (options 5 5) := by rfl


theorem t5_1155part0 : t5_1155jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1155frontier : t5_1155root.frontier 0=t5_1155jobs := by rfl
theorem t5_1155all : t5_1155jobs.all (Job.check tree)=true := by
  simp only [t5_1155jobs,List.all_append,List.all_nil,t5_1155part0,Bool.and_self]
theorem t5_1155checked : Checked tree [4,8,7,7,7] := by
  refine ⟨plan5086,valid5086,t5_1155choices,?_⟩
  exact check_of_frontier tree 0 t5_1155root t5_1155jobs t5_1155frontier t5_1155all
theorem t5_1156choices : plan4843.choices=[4,8,8,3,7].map (options 5 4) := by rfl


theorem t5_1156part0 : t5_1156jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1156frontier : t5_1156root.frontier 0=t5_1156jobs := by rfl
theorem t5_1156all : t5_1156jobs.all (Job.check tree)=true := by
  simp only [t5_1156jobs,List.all_append,List.all_nil,t5_1156part0,Bool.and_self]
theorem t5_1156checked : Checked tree [4,8,8,3,7] := by
  refine ⟨plan4843,valid4843,t5_1156choices,?_⟩
  exact check_of_frontier tree 0 t5_1156root t5_1156jobs t5_1156frontier t5_1156all
theorem t5_1157choices : plan5087.choices=[4,8,8,6,7].map (options 5 5) := by rfl


theorem t5_1157part0 : t5_1157jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1157frontier : t5_1157root.frontier 0=t5_1157jobs := by rfl
theorem t5_1157all : t5_1157jobs.all (Job.check tree)=true := by
  simp only [t5_1157jobs,List.all_append,List.all_nil,t5_1157part0,Bool.and_self]
theorem t5_1157checked : Checked tree [4,8,8,6,7] := by
  refine ⟨plan5087,valid5087,t5_1157choices,?_⟩
  exact check_of_frontier tree 0 t5_1157root t5_1157jobs t5_1157frontier t5_1157all
theorem t5_1158choices : plan5088.choices=[4,8,8,7,7].map (options 5 5) := by rfl


theorem t5_1158part0 : t5_1158jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1158frontier : t5_1158root.frontier 0=t5_1158jobs := by rfl
theorem t5_1158all : t5_1158jobs.all (Job.check tree)=true := by
  simp only [t5_1158jobs,List.all_append,List.all_nil,t5_1158part0,Bool.and_self]
theorem t5_1158checked : Checked tree [4,8,8,7,7] := by
  refine ⟨plan5088,valid5088,t5_1158choices,?_⟩
  exact check_of_frontier tree 0 t5_1158root t5_1158jobs t5_1158frontier t5_1158all
theorem t5_1159choices : plan5089.choices=[4,8,8,10,7].map (options 5 5) := by rfl


theorem t5_1159part0 : t5_1159jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1159frontier : t5_1159root.frontier 0=t5_1159jobs := by rfl
theorem t5_1159all : t5_1159jobs.all (Job.check tree)=true := by
  simp only [t5_1159jobs,List.all_append,List.all_nil,t5_1159part0,Bool.and_self]
theorem t5_1159checked : Checked tree [4,8,8,10,7] := by
  refine ⟨plan5089,valid5089,t5_1159choices,?_⟩
  exact check_of_frontier tree 0 t5_1159root t5_1159jobs t5_1159frontier t5_1159all
theorem t5_1160choices : plan4369.choices=[4,8,9,3,3].map (options 5 3) := by rfl


theorem t5_1160part0 : t5_1160jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1160frontier : t5_1160root.frontier 0=t5_1160jobs := by rfl
theorem t5_1160all : t5_1160jobs.all (Job.check tree)=true := by
  simp only [t5_1160jobs,List.all_append,List.all_nil,t5_1160part0,Bool.and_self]
theorem t5_1160checked : Checked tree [4,8,9,3,3] := by
  refine ⟨plan4369,valid4369,t5_1160choices,?_⟩
  exact check_of_frontier tree 0 t5_1160root t5_1160jobs t5_1160frontier t5_1160all
theorem t5_1161choices : plan4844.choices=[4,8,9,3,6].map (options 5 4) := by rfl


theorem t5_1161part0 : t5_1161jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1161frontier : t5_1161root.frontier 0=t5_1161jobs := by rfl
theorem t5_1161all : t5_1161jobs.all (Job.check tree)=true := by
  simp only [t5_1161jobs,List.all_append,List.all_nil,t5_1161part0,Bool.and_self]
theorem t5_1161checked : Checked tree [4,8,9,3,6] := by
  refine ⟨plan4844,valid4844,t5_1161choices,?_⟩
  exact check_of_frontier tree 0 t5_1161root t5_1161jobs t5_1161frontier t5_1161all
theorem t5_1162choices : plan4845.choices=[4,8,9,3,7].map (options 5 4) := by rfl


theorem t5_1162part0 : t5_1162jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1162frontier : t5_1162root.frontier 0=t5_1162jobs := by rfl
theorem t5_1162all : t5_1162jobs.all (Job.check tree)=true := by
  simp only [t5_1162jobs,List.all_append,List.all_nil,t5_1162part0,Bool.and_self]
theorem t5_1162checked : Checked tree [4,8,9,3,7] := by
  refine ⟨plan4845,valid4845,t5_1162choices,?_⟩
  exact check_of_frontier tree 0 t5_1162root t5_1162jobs t5_1162frontier t5_1162all
theorem t5_1163choices : plan4846.choices=[4,8,9,3,10].map (options 5 4) := by rfl


theorem t5_1163part0 : t5_1163jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1163frontier : t5_1163root.frontier 0=t5_1163jobs := by rfl
theorem t5_1163all : t5_1163jobs.all (Job.check tree)=true := by
  simp only [t5_1163jobs,List.all_append,List.all_nil,t5_1163part0,Bool.and_self]
theorem t5_1163checked : Checked tree [4,8,9,3,10] := by
  refine ⟨plan4846,valid4846,t5_1163choices,?_⟩
  exact check_of_frontier tree 0 t5_1163root t5_1163jobs t5_1163frontier t5_1163all
theorem t5_1164choices : plan5090.choices=[4,8,9,6,6].map (options 5 5) := by rfl


theorem t5_1164part0 : t5_1164jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1164frontier : t5_1164root.frontier 0=t5_1164jobs := by rfl
theorem t5_1164all : t5_1164jobs.all (Job.check tree)=true := by
  simp only [t5_1164jobs,List.all_append,List.all_nil,t5_1164part0,Bool.and_self]
theorem t5_1164checked : Checked tree [4,8,9,6,6] := by
  refine ⟨plan5090,valid5090,t5_1164choices,?_⟩
  exact check_of_frontier tree 0 t5_1164root t5_1164jobs t5_1164frontier t5_1164all
theorem t5_1165choices : plan5091.choices=[4,8,9,6,7].map (options 5 5) := by rfl


theorem t5_1165part0 : t5_1165jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1165frontier : t5_1165root.frontier 0=t5_1165jobs := by rfl
theorem t5_1165all : t5_1165jobs.all (Job.check tree)=true := by
  simp only [t5_1165jobs,List.all_append,List.all_nil,t5_1165part0,Bool.and_self]
theorem t5_1165checked : Checked tree [4,8,9,6,7] := by
  refine ⟨plan5091,valid5091,t5_1165choices,?_⟩
  exact check_of_frontier tree 0 t5_1165root t5_1165jobs t5_1165frontier t5_1165all
theorem t5_1166choices : plan5092.choices=[4,8,9,6,10].map (options 5 5) := by rfl


theorem t5_1166part0 : t5_1166jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1166frontier : t5_1166root.frontier 0=t5_1166jobs := by rfl
theorem t5_1166all : t5_1166jobs.all (Job.check tree)=true := by
  simp only [t5_1166jobs,List.all_append,List.all_nil,t5_1166part0,Bool.and_self]
theorem t5_1166checked : Checked tree [4,8,9,6,10] := by
  refine ⟨plan5092,valid5092,t5_1166choices,?_⟩
  exact check_of_frontier tree 0 t5_1166root t5_1166jobs t5_1166frontier t5_1166all
theorem t5_1167choices : plan5093.choices=[4,8,9,7,7].map (options 5 5) := by rfl


theorem t5_1167part0 : t5_1167jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1167frontier : t5_1167root.frontier 0=t5_1167jobs := by rfl
theorem t5_1167all : t5_1167jobs.all (Job.check tree)=true := by
  simp only [t5_1167jobs,List.all_append,List.all_nil,t5_1167part0,Bool.and_self]
theorem t5_1167checked : Checked tree [4,8,9,7,7] := by
  refine ⟨plan5093,valid5093,t5_1167choices,?_⟩
  exact check_of_frontier tree 0 t5_1167root t5_1167jobs t5_1167frontier t5_1167all
theorem t5_1168choices : plan5094.choices=[4,8,9,9,7].map (options 5 5) := by rfl


theorem t5_1168part0 : t5_1168jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1168frontier : t5_1168root.frontier 0=t5_1168jobs := by rfl
theorem t5_1168all : t5_1168jobs.all (Job.check tree)=true := by
  simp only [t5_1168jobs,List.all_append,List.all_nil,t5_1168part0,Bool.and_self]
theorem t5_1168checked : Checked tree [4,8,9,9,7] := by
  refine ⟨plan5094,valid5094,t5_1168choices,?_⟩
  exact check_of_frontier tree 0 t5_1168root t5_1168jobs t5_1168frontier t5_1168all
theorem t5_1169choices : plan5095.choices=[4,8,9,10,7].map (options 5 5) := by rfl


theorem t5_1169part0 : t5_1169jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1169frontier : t5_1169root.frontier 0=t5_1169jobs := by rfl
theorem t5_1169all : t5_1169jobs.all (Job.check tree)=true := by
  simp only [t5_1169jobs,List.all_append,List.all_nil,t5_1169part0,Bool.and_self]
theorem t5_1169checked : Checked tree [4,8,9,10,7] := by
  refine ⟨plan5095,valid5095,t5_1169choices,?_⟩
  exact check_of_frontier tree 0 t5_1169root t5_1169jobs t5_1169frontier t5_1169all
theorem t5_1170choices : plan5096.choices=[4,8,9,10,10].map (options 5 5) := by rfl


theorem t5_1170part0 : t5_1170jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1170frontier : t5_1170root.frontier 0=t5_1170jobs := by rfl
theorem t5_1170all : t5_1170jobs.all (Job.check tree)=true := by
  simp only [t5_1170jobs,List.all_append,List.all_nil,t5_1170part0,Bool.and_self]
theorem t5_1170checked : Checked tree [4,8,9,10,10] := by
  refine ⟨plan5096,valid5096,t5_1170choices,?_⟩
  exact check_of_frontier tree 0 t5_1170root t5_1170jobs t5_1170frontier t5_1170all
theorem t5_1171choices : plan5097.choices=[4,8,10,7,7].map (options 5 5) := by rfl


theorem t5_1171part0 : t5_1171jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1171frontier : t5_1171root.frontier 0=t5_1171jobs := by rfl
theorem t5_1171all : t5_1171jobs.all (Job.check tree)=true := by
  simp only [t5_1171jobs,List.all_append,List.all_nil,t5_1171part0,Bool.and_self]
theorem t5_1171checked : Checked tree [4,8,10,7,7] := by
  refine ⟨plan5097,valid5097,t5_1171choices,?_⟩
  exact check_of_frontier tree 0 t5_1171root t5_1171jobs t5_1171frontier t5_1171all
theorem t5_1172choices : plan5098.choices=[4,8,10,10,7].map (options 5 5) := by rfl


theorem t5_1172part0 : t5_1172jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1172frontier : t5_1172root.frontier 0=t5_1172jobs := by rfl
theorem t5_1172all : t5_1172jobs.all (Job.check tree)=true := by
  simp only [t5_1172jobs,List.all_append,List.all_nil,t5_1172part0,Bool.and_self]
theorem t5_1172checked : Checked tree [4,8,10,10,7] := by
  refine ⟨plan5098,valid5098,t5_1172choices,?_⟩
  exact check_of_frontier tree 0 t5_1172root t5_1172jobs t5_1172frontier t5_1172all
theorem t5_1173choices : plan5099.choices=[4,8,10,10,10].map (options 5 5) := by rfl


theorem t5_1173part0 : t5_1173jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1173frontier : t5_1173root.frontier 0=t5_1173jobs := by rfl
theorem t5_1173all : t5_1173jobs.all (Job.check tree)=true := by
  simp only [t5_1173jobs,List.all_append,List.all_nil,t5_1173part0,Bool.and_self]
theorem t5_1173checked : Checked tree [4,8,10,10,10] := by
  refine ⟨plan5099,valid5099,t5_1173choices,?_⟩
  exact check_of_frontier tree 0 t5_1173root t5_1173jobs t5_1173frontier t5_1173all
theorem t5_1174choices : plan3970.choices=[4,9,3,3,3].map (options 5 2) := by rfl


theorem t5_1174part0 : t5_1174jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1174frontier : t5_1174root.frontier 0=t5_1174jobs := by rfl
theorem t5_1174all : t5_1174jobs.all (Job.check tree)=true := by
  simp only [t5_1174jobs,List.all_append,List.all_nil,t5_1174part0,Bool.and_self]
theorem t5_1174checked : Checked tree [4,9,3,3,3] := by
  refine ⟨plan3970,valid3970,t5_1174choices,?_⟩
  exact check_of_frontier tree 0 t5_1174root t5_1174jobs t5_1174frontier t5_1174all
theorem t5_1175choices : plan4370.choices=[4,9,3,3,6].map (options 5 3) := by rfl


theorem t5_1175part0 : t5_1175jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1175frontier : t5_1175root.frontier 0=t5_1175jobs := by rfl
theorem t5_1175all : t5_1175jobs.all (Job.check tree)=true := by
  simp only [t5_1175jobs,List.all_append,List.all_nil,t5_1175part0,Bool.and_self]
theorem t5_1175checked : Checked tree [4,9,3,3,6] := by
  refine ⟨plan4370,valid4370,t5_1175choices,?_⟩
  exact check_of_frontier tree 0 t5_1175root t5_1175jobs t5_1175frontier t5_1175all
theorem t5_1176choices : plan4371.choices=[4,9,3,3,7].map (options 5 3) := by rfl


theorem t5_1176part0 : t5_1176jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1176frontier : t5_1176root.frontier 0=t5_1176jobs := by rfl
theorem t5_1176all : t5_1176jobs.all (Job.check tree)=true := by
  simp only [t5_1176jobs,List.all_append,List.all_nil,t5_1176part0,Bool.and_self]
theorem t5_1176checked : Checked tree [4,9,3,3,7] := by
  refine ⟨plan4371,valid4371,t5_1176choices,?_⟩
  exact check_of_frontier tree 0 t5_1176root t5_1176jobs t5_1176frontier t5_1176all
theorem t5_1177choices : plan4372.choices=[4,9,3,3,10].map (options 5 3) := by rfl


theorem t5_1177part0 : t5_1177jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1177frontier : t5_1177root.frontier 0=t5_1177jobs := by rfl
theorem t5_1177all : t5_1177jobs.all (Job.check tree)=true := by
  simp only [t5_1177jobs,List.all_append,List.all_nil,t5_1177part0,Bool.and_self]
theorem t5_1177checked : Checked tree [4,9,3,3,10] := by
  refine ⟨plan4372,valid4372,t5_1177choices,?_⟩
  exact check_of_frontier tree 0 t5_1177root t5_1177jobs t5_1177frontier t5_1177all
theorem t5_1178choices : plan4847.choices=[4,9,3,6,6].map (options 5 4) := by rfl


theorem t5_1178part0 : t5_1178jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1178frontier : t5_1178root.frontier 0=t5_1178jobs := by rfl
theorem t5_1178all : t5_1178jobs.all (Job.check tree)=true := by
  simp only [t5_1178jobs,List.all_append,List.all_nil,t5_1178part0,Bool.and_self]
theorem t5_1178checked : Checked tree [4,9,3,6,6] := by
  refine ⟨plan4847,valid4847,t5_1178choices,?_⟩
  exact check_of_frontier tree 0 t5_1178root t5_1178jobs t5_1178frontier t5_1178all
theorem t5_1179choices : plan4848.choices=[4,9,3,6,7].map (options 5 4) := by rfl


theorem t5_1179part0 : t5_1179jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1179frontier : t5_1179root.frontier 0=t5_1179jobs := by rfl
theorem t5_1179all : t5_1179jobs.all (Job.check tree)=true := by
  simp only [t5_1179jobs,List.all_append,List.all_nil,t5_1179part0,Bool.and_self]
theorem t5_1179checked : Checked tree [4,9,3,6,7] := by
  refine ⟨plan4848,valid4848,t5_1179choices,?_⟩
  exact check_of_frontier tree 0 t5_1179root t5_1179jobs t5_1179frontier t5_1179all
theorem t5_1180choices : plan4849.choices=[4,9,3,6,10].map (options 5 4) := by rfl


theorem t5_1180part0 : t5_1180jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1180frontier : t5_1180root.frontier 0=t5_1180jobs := by rfl
theorem t5_1180all : t5_1180jobs.all (Job.check tree)=true := by
  simp only [t5_1180jobs,List.all_append,List.all_nil,t5_1180part0,Bool.and_self]
theorem t5_1180checked : Checked tree [4,9,3,6,10] := by
  refine ⟨plan4849,valid4849,t5_1180choices,?_⟩
  exact check_of_frontier tree 0 t5_1180root t5_1180jobs t5_1180frontier t5_1180all
theorem t5_1181choices : plan4850.choices=[4,9,3,7,7].map (options 5 4) := by rfl


theorem t5_1181part0 : t5_1181jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1181frontier : t5_1181root.frontier 0=t5_1181jobs := by rfl
theorem t5_1181all : t5_1181jobs.all (Job.check tree)=true := by
  simp only [t5_1181jobs,List.all_append,List.all_nil,t5_1181part0,Bool.and_self]
theorem t5_1181checked : Checked tree [4,9,3,7,7] := by
  refine ⟨plan4850,valid4850,t5_1181choices,?_⟩
  exact check_of_frontier tree 0 t5_1181root t5_1181jobs t5_1181frontier t5_1181all
theorem t5_1182choices : plan4851.choices=[4,9,3,10,7].map (options 5 4) := by rfl


theorem t5_1182part0 : t5_1182jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1182frontier : t5_1182root.frontier 0=t5_1182jobs := by rfl
theorem t5_1182all : t5_1182jobs.all (Job.check tree)=true := by
  simp only [t5_1182jobs,List.all_append,List.all_nil,t5_1182part0,Bool.and_self]
theorem t5_1182checked : Checked tree [4,9,3,10,7] := by
  refine ⟨plan4851,valid4851,t5_1182choices,?_⟩
  exact check_of_frontier tree 0 t5_1182root t5_1182jobs t5_1182frontier t5_1182all
theorem t5_1183choices : plan4852.choices=[4,9,3,10,10].map (options 5 4) := by rfl


theorem t5_1183part0 : t5_1183jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1183frontier : t5_1183root.frontier 0=t5_1183jobs := by rfl
theorem t5_1183all : t5_1183jobs.all (Job.check tree)=true := by
  simp only [t5_1183jobs,List.all_append,List.all_nil,t5_1183part0,Bool.and_self]
theorem t5_1183checked : Checked tree [4,9,3,10,10] := by
  refine ⟨plan4852,valid4852,t5_1183choices,?_⟩
  exact check_of_frontier tree 0 t5_1183root t5_1183jobs t5_1183frontier t5_1183all
theorem t5_1184choices : plan5100.choices=[4,9,6,6,6].map (options 5 5) := by rfl


theorem t5_1184part0 : t5_1184jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1184frontier : t5_1184root.frontier 0=t5_1184jobs := by rfl
theorem t5_1184all : t5_1184jobs.all (Job.check tree)=true := by
  simp only [t5_1184jobs,List.all_append,List.all_nil,t5_1184part0,Bool.and_self]
theorem t5_1184checked : Checked tree [4,9,6,6,6] := by
  refine ⟨plan5100,valid5100,t5_1184choices,?_⟩
  exact check_of_frontier tree 0 t5_1184root t5_1184jobs t5_1184frontier t5_1184all
theorem t5_1185choices : plan5101.choices=[4,9,6,6,7].map (options 5 5) := by rfl


theorem t5_1185part0 : t5_1185jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1185frontier : t5_1185root.frontier 0=t5_1185jobs := by rfl
theorem t5_1185all : t5_1185jobs.all (Job.check tree)=true := by
  simp only [t5_1185jobs,List.all_append,List.all_nil,t5_1185part0,Bool.and_self]
theorem t5_1185checked : Checked tree [4,9,6,6,7] := by
  refine ⟨plan5101,valid5101,t5_1185choices,?_⟩
  exact check_of_frontier tree 0 t5_1185root t5_1185jobs t5_1185frontier t5_1185all
theorem t5_1186choices : plan5102.choices=[4,9,6,6,10].map (options 5 5) := by rfl


theorem t5_1186part0 : t5_1186jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1186frontier : t5_1186root.frontier 0=t5_1186jobs := by rfl
theorem t5_1186all : t5_1186jobs.all (Job.check tree)=true := by
  simp only [t5_1186jobs,List.all_append,List.all_nil,t5_1186part0,Bool.and_self]
theorem t5_1186checked : Checked tree [4,9,6,6,10] := by
  refine ⟨plan5102,valid5102,t5_1186choices,?_⟩
  exact check_of_frontier tree 0 t5_1186root t5_1186jobs t5_1186frontier t5_1186all
theorem t5_1187choices : plan5103.choices=[4,9,6,7,7].map (options 5 5) := by rfl


theorem t5_1187part0 : t5_1187jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1187frontier : t5_1187root.frontier 0=t5_1187jobs := by rfl
theorem t5_1187all : t5_1187jobs.all (Job.check tree)=true := by
  simp only [t5_1187jobs,List.all_append,List.all_nil,t5_1187part0,Bool.and_self]
theorem t5_1187checked : Checked tree [4,9,6,7,7] := by
  refine ⟨plan5103,valid5103,t5_1187choices,?_⟩
  exact check_of_frontier tree 0 t5_1187root t5_1187jobs t5_1187frontier t5_1187all
theorem t5_1188choices : plan5104.choices=[4,9,6,10,7].map (options 5 5) := by rfl


theorem t5_1188part0 : t5_1188jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1188frontier : t5_1188root.frontier 0=t5_1188jobs := by rfl
theorem t5_1188all : t5_1188jobs.all (Job.check tree)=true := by
  simp only [t5_1188jobs,List.all_append,List.all_nil,t5_1188part0,Bool.and_self]
theorem t5_1188checked : Checked tree [4,9,6,10,7] := by
  refine ⟨plan5104,valid5104,t5_1188choices,?_⟩
  exact check_of_frontier tree 0 t5_1188root t5_1188jobs t5_1188frontier t5_1188all
theorem t5_1189choices : plan5105.choices=[4,9,6,10,10].map (options 5 5) := by rfl


theorem t5_1189part0 : t5_1189jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1189frontier : t5_1189root.frontier 0=t5_1189jobs := by rfl
theorem t5_1189all : t5_1189jobs.all (Job.check tree)=true := by
  simp only [t5_1189jobs,List.all_append,List.all_nil,t5_1189part0,Bool.and_self]
theorem t5_1189checked : Checked tree [4,9,6,10,10] := by
  refine ⟨plan5105,valid5105,t5_1189choices,?_⟩
  exact check_of_frontier tree 0 t5_1189root t5_1189jobs t5_1189frontier t5_1189all
theorem t5_1190choices : plan5106.choices=[4,9,7,7,7].map (options 5 5) := by rfl


theorem t5_1190part0 : t5_1190jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1190frontier : t5_1190root.frontier 0=t5_1190jobs := by rfl
theorem t5_1190all : t5_1190jobs.all (Job.check tree)=true := by
  simp only [t5_1190jobs,List.all_append,List.all_nil,t5_1190part0,Bool.and_self]
theorem t5_1190checked : Checked tree [4,9,7,7,7] := by
  refine ⟨plan5106,valid5106,t5_1190choices,?_⟩
  exact check_of_frontier tree 0 t5_1190root t5_1190jobs t5_1190frontier t5_1190all
theorem t5_1191choices : plan4373.choices=[4,9,9,3,3].map (options 5 3) := by rfl


theorem t5_1191part0 : t5_1191jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1191frontier : t5_1191root.frontier 0=t5_1191jobs := by rfl
theorem t5_1191all : t5_1191jobs.all (Job.check tree)=true := by
  simp only [t5_1191jobs,List.all_append,List.all_nil,t5_1191part0,Bool.and_self]
theorem t5_1191checked : Checked tree [4,9,9,3,3] := by
  refine ⟨plan4373,valid4373,t5_1191choices,?_⟩
  exact check_of_frontier tree 0 t5_1191root t5_1191jobs t5_1191frontier t5_1191all
theorem t5_1192choices : plan4853.choices=[4,9,9,3,6].map (options 5 4) := by rfl


theorem t5_1192part0 : t5_1192jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1192frontier : t5_1192root.frontier 0=t5_1192jobs := by rfl
theorem t5_1192all : t5_1192jobs.all (Job.check tree)=true := by
  simp only [t5_1192jobs,List.all_append,List.all_nil,t5_1192part0,Bool.and_self]
theorem t5_1192checked : Checked tree [4,9,9,3,6] := by
  refine ⟨plan4853,valid4853,t5_1192choices,?_⟩
  exact check_of_frontier tree 0 t5_1192root t5_1192jobs t5_1192frontier t5_1192all
theorem t5_1193choices : plan4854.choices=[4,9,9,3,7].map (options 5 4) := by rfl


theorem t5_1193part0 : t5_1193jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1193frontier : t5_1193root.frontier 0=t5_1193jobs := by rfl
theorem t5_1193all : t5_1193jobs.all (Job.check tree)=true := by
  simp only [t5_1193jobs,List.all_append,List.all_nil,t5_1193part0,Bool.and_self]
theorem t5_1193checked : Checked tree [4,9,9,3,7] := by
  refine ⟨plan4854,valid4854,t5_1193choices,?_⟩
  exact check_of_frontier tree 0 t5_1193root t5_1193jobs t5_1193frontier t5_1193all
theorem t5_1194choices : plan4855.choices=[4,9,9,3,10].map (options 5 4) := by rfl


theorem t5_1194part0 : t5_1194jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1194frontier : t5_1194root.frontier 0=t5_1194jobs := by rfl
theorem t5_1194all : t5_1194jobs.all (Job.check tree)=true := by
  simp only [t5_1194jobs,List.all_append,List.all_nil,t5_1194part0,Bool.and_self]
theorem t5_1194checked : Checked tree [4,9,9,3,10] := by
  refine ⟨plan4855,valid4855,t5_1194choices,?_⟩
  exact check_of_frontier tree 0 t5_1194root t5_1194jobs t5_1194frontier t5_1194all
theorem t5_1195choices : plan5107.choices=[4,9,9,6,6].map (options 5 5) := by rfl


theorem t5_1195part0 : t5_1195jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1195frontier : t5_1195root.frontier 0=t5_1195jobs := by rfl
theorem t5_1195all : t5_1195jobs.all (Job.check tree)=true := by
  simp only [t5_1195jobs,List.all_append,List.all_nil,t5_1195part0,Bool.and_self]
theorem t5_1195checked : Checked tree [4,9,9,6,6] := by
  refine ⟨plan5107,valid5107,t5_1195choices,?_⟩
  exact check_of_frontier tree 0 t5_1195root t5_1195jobs t5_1195frontier t5_1195all
theorem t5_1196choices : plan5108.choices=[4,9,9,6,7].map (options 5 5) := by rfl


theorem t5_1196part0 : t5_1196jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1196frontier : t5_1196root.frontier 0=t5_1196jobs := by rfl
theorem t5_1196all : t5_1196jobs.all (Job.check tree)=true := by
  simp only [t5_1196jobs,List.all_append,List.all_nil,t5_1196part0,Bool.and_self]
theorem t5_1196checked : Checked tree [4,9,9,6,7] := by
  refine ⟨plan5108,valid5108,t5_1196choices,?_⟩
  exact check_of_frontier tree 0 t5_1196root t5_1196jobs t5_1196frontier t5_1196all
theorem t5_1197choices : plan5109.choices=[4,9,9,6,10].map (options 5 5) := by rfl


theorem t5_1197part0 : t5_1197jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1197frontier : t5_1197root.frontier 0=t5_1197jobs := by rfl
theorem t5_1197all : t5_1197jobs.all (Job.check tree)=true := by
  simp only [t5_1197jobs,List.all_append,List.all_nil,t5_1197part0,Bool.and_self]
theorem t5_1197checked : Checked tree [4,9,9,6,10] := by
  refine ⟨plan5109,valid5109,t5_1197choices,?_⟩
  exact check_of_frontier tree 0 t5_1197root t5_1197jobs t5_1197frontier t5_1197all
theorem t5_1198choices : plan5110.choices=[4,9,9,7,7].map (options 5 5) := by rfl


theorem t5_1198part0 : t5_1198jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1198frontier : t5_1198root.frontier 0=t5_1198jobs := by rfl
theorem t5_1198all : t5_1198jobs.all (Job.check tree)=true := by
  simp only [t5_1198jobs,List.all_append,List.all_nil,t5_1198part0,Bool.and_self]
theorem t5_1198checked : Checked tree [4,9,9,7,7] := by
  refine ⟨plan5110,valid5110,t5_1198choices,?_⟩
  exact check_of_frontier tree 0 t5_1198root t5_1198jobs t5_1198frontier t5_1198all
theorem t5_1199choices : plan4856.choices=[4,9,9,9,3].map (options 5 4) := by rfl


theorem t5_1199part0 : t5_1199jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1199frontier : t5_1199root.frontier 0=t5_1199jobs := by rfl
theorem t5_1199all : t5_1199jobs.all (Job.check tree)=true := by
  simp only [t5_1199jobs,List.all_append,List.all_nil,t5_1199part0,Bool.and_self]
theorem t5_1199checked : Checked tree [4,9,9,9,3] := by
  refine ⟨plan4856,valid4856,t5_1199choices,?_⟩
  exact check_of_frontier tree 0 t5_1199root t5_1199jobs t5_1199frontier t5_1199all
theorem t5_1200choices : plan5111.choices=[4,9,9,9,6].map (options 5 5) := by rfl


theorem t5_1200part0 : t5_1200jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1200frontier : t5_1200root.frontier 0=t5_1200jobs := by rfl
theorem t5_1200all : t5_1200jobs.all (Job.check tree)=true := by
  simp only [t5_1200jobs,List.all_append,List.all_nil,t5_1200part0,Bool.and_self]
theorem t5_1200checked : Checked tree [4,9,9,9,6] := by
  refine ⟨plan5111,valid5111,t5_1200choices,?_⟩
  exact check_of_frontier tree 0 t5_1200root t5_1200jobs t5_1200frontier t5_1200all
theorem t5_1201choices : plan5112.choices=[4,9,9,9,7].map (options 5 5) := by rfl


theorem t5_1201part0 : t5_1201jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1201frontier : t5_1201root.frontier 0=t5_1201jobs := by rfl
theorem t5_1201all : t5_1201jobs.all (Job.check tree)=true := by
  simp only [t5_1201jobs,List.all_append,List.all_nil,t5_1201part0,Bool.and_self]
theorem t5_1201checked : Checked tree [4,9,9,9,7] := by
  refine ⟨plan5112,valid5112,t5_1201choices,?_⟩
  exact check_of_frontier tree 0 t5_1201root t5_1201jobs t5_1201frontier t5_1201all
theorem t5_1202choices : plan5113.choices=[4,9,9,9,10].map (options 5 5) := by rfl


theorem t5_1202part0 : t5_1202jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1202frontier : t5_1202root.frontier 0=t5_1202jobs := by rfl
theorem t5_1202all : t5_1202jobs.all (Job.check tree)=true := by
  simp only [t5_1202jobs,List.all_append,List.all_nil,t5_1202part0,Bool.and_self]
theorem t5_1202checked : Checked tree [4,9,9,9,10] := by
  refine ⟨plan5113,valid5113,t5_1202choices,?_⟩
  exact check_of_frontier tree 0 t5_1202root t5_1202jobs t5_1202frontier t5_1202all
theorem t5_1203choices : plan5114.choices=[4,9,9,10,7].map (options 5 5) := by rfl


theorem t5_1203part0 : t5_1203jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1203frontier : t5_1203root.frontier 0=t5_1203jobs := by rfl
theorem t5_1203all : t5_1203jobs.all (Job.check tree)=true := by
  simp only [t5_1203jobs,List.all_append,List.all_nil,t5_1203part0,Bool.and_self]
theorem t5_1203checked : Checked tree [4,9,9,10,7] := by
  refine ⟨plan5114,valid5114,t5_1203choices,?_⟩
  exact check_of_frontier tree 0 t5_1203root t5_1203jobs t5_1203frontier t5_1203all
theorem t5_1204choices : plan5115.choices=[4,9,9,10,10].map (options 5 5) := by rfl


theorem t5_1204part0 : t5_1204jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1204frontier : t5_1204root.frontier 0=t5_1204jobs := by rfl
theorem t5_1204all : t5_1204jobs.all (Job.check tree)=true := by
  simp only [t5_1204jobs,List.all_append,List.all_nil,t5_1204part0,Bool.and_self]
theorem t5_1204checked : Checked tree [4,9,9,10,10] := by
  refine ⟨plan5115,valid5115,t5_1204choices,?_⟩
  exact check_of_frontier tree 0 t5_1204root t5_1204jobs t5_1204frontier t5_1204all
theorem t5_1205choices : plan5116.choices=[4,9,10,7,7].map (options 5 5) := by rfl


theorem t5_1205part0 : t5_1205jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1205frontier : t5_1205root.frontier 0=t5_1205jobs := by rfl
theorem t5_1205all : t5_1205jobs.all (Job.check tree)=true := by
  simp only [t5_1205jobs,List.all_append,List.all_nil,t5_1205part0,Bool.and_self]
theorem t5_1205checked : Checked tree [4,9,10,7,7] := by
  refine ⟨plan5116,valid5116,t5_1205choices,?_⟩
  exact check_of_frontier tree 0 t5_1205root t5_1205jobs t5_1205frontier t5_1205all
theorem t5_1206choices : plan5117.choices=[4,9,10,10,7].map (options 5 5) := by rfl


theorem t5_1206part0 : t5_1206jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1206frontier : t5_1206root.frontier 0=t5_1206jobs := by rfl
theorem t5_1206all : t5_1206jobs.all (Job.check tree)=true := by
  simp only [t5_1206jobs,List.all_append,List.all_nil,t5_1206part0,Bool.and_self]
theorem t5_1206checked : Checked tree [4,9,10,10,7] := by
  refine ⟨plan5117,valid5117,t5_1206choices,?_⟩
  exact check_of_frontier tree 0 t5_1206root t5_1206jobs t5_1206frontier t5_1206all
theorem t5_1207choices : plan5118.choices=[4,9,10,10,10].map (options 5 5) := by rfl


theorem t5_1207part0 : t5_1207jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1207frontier : t5_1207root.frontier 0=t5_1207jobs := by rfl
theorem t5_1207all : t5_1207jobs.all (Job.check tree)=true := by
  simp only [t5_1207jobs,List.all_append,List.all_nil,t5_1207part0,Bool.and_self]
theorem t5_1207checked : Checked tree [4,9,10,10,10] := by
  refine ⟨plan5118,valid5118,t5_1207choices,?_⟩
  exact check_of_frontier tree 0 t5_1207root t5_1207jobs t5_1207frontier t5_1207all
theorem t5_1208choices : plan5119.choices=[4,10,7,7,7].map (options 5 5) := by rfl


theorem t5_1208part0 : t5_1208jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1208frontier : t5_1208root.frontier 0=t5_1208jobs := by rfl
theorem t5_1208all : t5_1208jobs.all (Job.check tree)=true := by
  simp only [t5_1208jobs,List.all_append,List.all_nil,t5_1208part0,Bool.and_self]
theorem t5_1208checked : Checked tree [4,10,7,7,7] := by
  refine ⟨plan5119,valid5119,t5_1208choices,?_⟩
  exact check_of_frontier tree 0 t5_1208root t5_1208jobs t5_1208frontier t5_1208all
theorem t5_1209choices : plan5120.choices=[4,10,10,7,7].map (options 5 5) := by rfl


theorem t5_1209part0 : t5_1209jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1209frontier : t5_1209root.frontier 0=t5_1209jobs := by rfl
theorem t5_1209all : t5_1209jobs.all (Job.check tree)=true := by
  simp only [t5_1209jobs,List.all_append,List.all_nil,t5_1209part0,Bool.and_self]
theorem t5_1209checked : Checked tree [4,10,10,7,7] := by
  refine ⟨plan5120,valid5120,t5_1209choices,?_⟩
  exact check_of_frontier tree 0 t5_1209root t5_1209jobs t5_1209frontier t5_1209all
theorem t5_1210choices : plan5121.choices=[4,10,10,10,7].map (options 5 5) := by rfl


theorem t5_1210part0 : t5_1210jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1210frontier : t5_1210root.frontier 0=t5_1210jobs := by rfl
theorem t5_1210all : t5_1210jobs.all (Job.check tree)=true := by
  simp only [t5_1210jobs,List.all_append,List.all_nil,t5_1210part0,Bool.and_self]
theorem t5_1210checked : Checked tree [4,10,10,10,7] := by
  refine ⟨plan5121,valid5121,t5_1210choices,?_⟩
  exact check_of_frontier tree 0 t5_1210root t5_1210jobs t5_1210frontier t5_1210all
theorem t5_1211choices : plan5122.choices=[4,10,10,10,10].map (options 5 5) := by rfl


theorem t5_1211part0 : t5_1211jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1211frontier : t5_1211root.frontier 0=t5_1211jobs := by rfl
theorem t5_1211all : t5_1211jobs.all (Job.check tree)=true := by
  simp only [t5_1211jobs,List.all_append,List.all_nil,t5_1211part0,Bool.and_self]
theorem t5_1211checked : Checked tree [4,10,10,10,10] := by
  refine ⟨plan5122,valid5122,t5_1211choices,?_⟩
  exact check_of_frontier tree 0 t5_1211root t5_1211jobs t5_1211frontier t5_1211all
theorem t5_1212choices : plan3753.choices=[5,3,3,3,3].map (options 5 1) := by rfl


theorem t5_1212part0 : t5_1212jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1212frontier : t5_1212root.frontier 0=t5_1212jobs := by rfl
theorem t5_1212all : t5_1212jobs.all (Job.check tree)=true := by
  simp only [t5_1212jobs,List.all_append,List.all_nil,t5_1212part0,Bool.and_self]
theorem t5_1212checked : Checked tree [5,3,3,3,3] := by
  refine ⟨plan3753,valid3753,t5_1212choices,?_⟩
  exact check_of_frontier tree 0 t5_1212root t5_1212jobs t5_1212frontier t5_1212all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks034 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1133checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1121checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1134checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1135checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1136checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1137checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1138checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1139checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1140checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1141checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1142checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1143checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1122checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1144checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1145checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1146checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1147checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1148checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1149checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1150checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1151checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1152checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1153checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1123checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1154checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1155checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1156checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1157checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1158checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1159checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1160checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1161checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1162checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1163checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1124checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1164checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1165checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1166checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1167checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1168checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1169checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1170checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1171checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1172checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1173checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1125checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1174checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1175checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1176checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1177checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1178checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1179checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1180checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1181checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1182checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1183checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1126checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1184checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1185checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1186checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1187checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1188checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1189checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1190checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1191checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1192checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1193checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1127checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1194checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1195checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1196checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1197checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1198checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1199checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1200checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1201checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1202checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1203checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1128checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1204checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1205checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1206checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1207checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1208checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1209checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1210checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1211checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1212checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1129checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1130checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1131checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1132checked⟩
