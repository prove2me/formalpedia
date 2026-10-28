-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks044
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:09:38.293181+00:00
-- url     : https://prove2.me/submissions/aedef31b-b704-4e8e-a7a1-ac36ff9d8572

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks044
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks044
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans054
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
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







theorem valid484 : plan484.Valid := valid_step _ _ _ valid100 (by decide +kernel)





theorem valid487 : plan487.Valid := valid_step _ _ _ valid105 (by decide +kernel)













theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)



















theorem valid505 : plan505.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid506 : plan506.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid507 : plan507.Valid := valid_step _ _ _ valid111 (by decide +kernel)













theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid518 : plan518.Valid := valid_step _ _ _ valid106 (by decide +kernel)









theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid524 : plan524.Valid := valid_step _ _ _ valid111 (by decide +kernel)











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



































































theorem valid1298 : plan1298.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1299 : plan1299.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1300 : plan1300.Valid := valid_step _ _ _ valid465 (by decide +kernel)











































































theorem valid1338 : plan1338.Valid := valid_step _ _ _ valid487 (by decide +kernel)

theorem valid1339 : plan1339.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1340 : plan1340.Valid := valid_step _ _ _ valid495 (by decide +kernel)








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









































































theorem valid1381 : plan1381.Valid := valid_step _ _ _ valid484 (by decide +kernel)



















































theorem valid1407 : plan1407.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1408 : plan1408.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1409 : plan1409.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1410 : plan1410.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1411 : plan1411.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1412 : plan1412.Valid := valid_step _ _ _ valid524 (by decide +kernel)
























































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





































































theorem valid2627 : plan2627.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2628 : plan2628.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2629 : plan2629.Valid := valid_step _ _ _ valid1300 (by decide +kernel)






















































































































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



























theorem valid3758 : plan3758.Valid := valid_step _ _ _ valid2549 (by decide +kernel)




































































































































































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



















































































































































theorem valid2762 : plan2762.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2763 : plan2763.Valid := valid_step _ _ _ valid1340 (by decide +kernel)










































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























































































































theorem valid3996 : plan3996.Valid := valid_step _ _ _ valid2627 (by decide +kernel)

theorem valid3997 : plan3997.Valid := valid_step _ _ _ valid2628 (by decide +kernel)

theorem valid3998 : plan3998.Valid := valid_step _ _ _ valid2629 (by decide +kernel)




































































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















theorem valid1448 : plan1448.Valid := valid_step _ _ _ valid505 (by decide +kernel)

theorem valid1449 : plan1449.Valid := valid_step _ _ _ valid506 (by decide +kernel)

theorem valid1450 : plan1450.Valid := valid_step _ _ _ valid507 (by decide +kernel)









theorem valid1455 : plan1455.Valid := valid_step _ _ _ valid518 (by decide +kernel)























































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











































theorem valid4438 : plan4438.Valid := valid_step _ _ _ valid2861 (by decide +kernel)

theorem valid4439 : plan4439.Valid := valid_step _ _ _ valid2868 (by decide +kernel)

theorem valid4440 : plan4440.Valid := valid_step _ _ _ valid2762 (by decide +kernel)

theorem valid4441 : plan4441.Valid := valid_step _ _ _ valid2763 (by decide +kernel)














































































































































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





























































































































































































theorem valid5279 : plan5279.Valid := valid_step _ _ _ valid3216 (by decide +kernel)

theorem valid5280 : plan5280.Valid := valid_step _ _ _ valid3217 (by decide +kernel)
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

















































































































































theorem valid4969 : plan4969.Valid := valid_step _ _ _ valid3077 (by decide +kernel)

theorem valid4970 : plan4970.Valid := valid_step _ _ _ valid3078 (by decide +kernel)

theorem valid4971 : plan4971.Valid := valid_step _ _ _ valid3079 (by decide +kernel)

theorem valid4972 : plan4972.Valid := valid_step _ _ _ valid3080 (by decide +kernel)

theorem valid4973 : plan4973.Valid := valid_step _ _ _ valid3081 (by decide +kernel)

theorem valid4974 : plan4974.Valid := valid_step _ _ _ valid3082 (by decide +kernel)

theorem valid4975 : plan4975.Valid := valid_step _ _ _ valid3090 (by decide +kernel)

theorem valid4976 : plan4976.Valid := valid_step _ _ _ valid3091 (by decide +kernel)

theorem valid4977 : plan4977.Valid := valid_step _ _ _ valid3092 (by decide +kernel)

theorem valid4978 : plan4978.Valid := valid_step _ _ _ valid3097 (by decide +kernel)




























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

theorem valid5281 : plan5281.Valid := valid_step _ _ _ valid3218 (by decide +kernel)

theorem valid5282 : plan5282.Valid := valid_step _ _ _ valid3219 (by decide +kernel)

theorem valid5283 : plan5283.Valid := valid_step _ _ _ valid3220 (by decide +kernel)

theorem valid5284 : plan5284.Valid := valid_step _ _ _ valid3221 (by decide +kernel)

theorem valid5285 : plan5285.Valid := valid_step _ _ _ valid3222 (by decide +kernel)

theorem valid5286 : plan5286.Valid := valid_step _ _ _ valid3223 (by decide +kernel)

theorem valid5287 : plan5287.Valid := valid_step _ _ _ valid3224 (by decide +kernel)

theorem valid5288 : plan5288.Valid := valid_step _ _ _ valid3225 (by decide +kernel)

theorem valid5289 : plan5289.Valid := valid_step _ _ _ valid3226 (by decide +kernel)

theorem valid5290 : plan5290.Valid := valid_step _ _ _ valid3227 (by decide +kernel)

theorem valid5291 : plan5291.Valid := valid_step _ _ _ valid3228 (by decide +kernel)

theorem valid5292 : plan5292.Valid := valid_step _ _ _ valid3230 (by decide +kernel)

theorem valid5293 : plan5293.Valid := valid_step _ _ _ valid3231 (by decide +kernel)

theorem valid5294 : plan5294.Valid := valid_step _ _ _ valid3232 (by decide +kernel)

theorem valid5295 : plan5295.Valid := valid_step _ _ _ valid3233 (by decide +kernel)

theorem valid5296 : plan5296.Valid := valid_step _ _ _ valid3234 (by decide +kernel)

theorem valid5297 : plan5297.Valid := valid_step _ _ _ valid3235 (by decide +kernel)

theorem valid5298 : plan5298.Valid := valid_step _ _ _ valid3236 (by decide +kernel)

theorem valid5299 : plan5299.Valid := valid_step _ _ _ valid3237 (by decide +kernel)

theorem valid5300 : plan5300.Valid := valid_step _ _ _ valid3238 (by decide +kernel)

theorem valid5301 : plan5301.Valid := valid_step _ _ _ valid3239 (by decide +kernel)






















































































































































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
theorem t5_1574choices : plan4438.choices=[8,9,3,3,10].map (options 5 3) := by rfl


theorem t5_1574part0 : t5_1574jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1574frontier : t5_1574root.frontier 0=t5_1574jobs := by rfl
theorem t5_1574all : t5_1574jobs.all (Job.check tree)=true := by
  simp only [t5_1574jobs,List.all_append,List.all_nil,t5_1574part0,Bool.and_self]
theorem t5_1574checked : Checked tree [8,9,3,3,10] := by
  refine ⟨plan4438,valid4438,t5_1574choices,?_⟩
  exact check_of_frontier tree 0 t5_1574root t5_1574jobs t5_1574frontier t5_1574all
theorem t5_1575choices : plan4969.choices=[8,9,3,6,6].map (options 5 4) := by rfl


theorem t5_1575part0 : t5_1575jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1575frontier : t5_1575root.frontier 0=t5_1575jobs := by rfl
theorem t5_1575all : t5_1575jobs.all (Job.check tree)=true := by
  simp only [t5_1575jobs,List.all_append,List.all_nil,t5_1575part0,Bool.and_self]
theorem t5_1575checked : Checked tree [8,9,3,6,6] := by
  refine ⟨plan4969,valid4969,t5_1575choices,?_⟩
  exact check_of_frontier tree 0 t5_1575root t5_1575jobs t5_1575frontier t5_1575all
theorem t5_1576choices : plan4970.choices=[8,9,3,6,7].map (options 5 4) := by rfl


theorem t5_1576part0 : t5_1576jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1576frontier : t5_1576root.frontier 0=t5_1576jobs := by rfl
theorem t5_1576all : t5_1576jobs.all (Job.check tree)=true := by
  simp only [t5_1576jobs,List.all_append,List.all_nil,t5_1576part0,Bool.and_self]
theorem t5_1576checked : Checked tree [8,9,3,6,7] := by
  refine ⟨plan4970,valid4970,t5_1576choices,?_⟩
  exact check_of_frontier tree 0 t5_1576root t5_1576jobs t5_1576frontier t5_1576all
theorem t5_1577choices : plan4971.choices=[8,9,3,6,10].map (options 5 4) := by rfl


theorem t5_1577part0 : t5_1577jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1577frontier : t5_1577root.frontier 0=t5_1577jobs := by rfl
theorem t5_1577all : t5_1577jobs.all (Job.check tree)=true := by
  simp only [t5_1577jobs,List.all_append,List.all_nil,t5_1577part0,Bool.and_self]
theorem t5_1577checked : Checked tree [8,9,3,6,10] := by
  refine ⟨plan4971,valid4971,t5_1577choices,?_⟩
  exact check_of_frontier tree 0 t5_1577root t5_1577jobs t5_1577frontier t5_1577all
theorem t5_1578choices : plan4972.choices=[8,9,3,7,7].map (options 5 4) := by rfl


theorem t5_1578part0 : t5_1578jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1578frontier : t5_1578root.frontier 0=t5_1578jobs := by rfl
theorem t5_1578all : t5_1578jobs.all (Job.check tree)=true := by
  simp only [t5_1578jobs,List.all_append,List.all_nil,t5_1578part0,Bool.and_self]
theorem t5_1578checked : Checked tree [8,9,3,7,7] := by
  refine ⟨plan4972,valid4972,t5_1578choices,?_⟩
  exact check_of_frontier tree 0 t5_1578root t5_1578jobs t5_1578frontier t5_1578all
theorem t5_1579choices : plan4973.choices=[8,9,3,10,7].map (options 5 4) := by rfl


theorem t5_1579part0 : t5_1579jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1579frontier : t5_1579root.frontier 0=t5_1579jobs := by rfl
theorem t5_1579all : t5_1579jobs.all (Job.check tree)=true := by
  simp only [t5_1579jobs,List.all_append,List.all_nil,t5_1579part0,Bool.and_self]
theorem t5_1579checked : Checked tree [8,9,3,10,7] := by
  refine ⟨plan4973,valid4973,t5_1579choices,?_⟩
  exact check_of_frontier tree 0 t5_1579root t5_1579jobs t5_1579frontier t5_1579all
theorem t5_1580choices : plan4974.choices=[8,9,3,10,10].map (options 5 4) := by rfl


theorem t5_1580part0 : t5_1580jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1580frontier : t5_1580root.frontier 0=t5_1580jobs := by rfl
theorem t5_1580all : t5_1580jobs.all (Job.check tree)=true := by
  simp only [t5_1580jobs,List.all_append,List.all_nil,t5_1580part0,Bool.and_self]
theorem t5_1580checked : Checked tree [8,9,3,10,10] := by
  refine ⟨plan4974,valid4974,t5_1580choices,?_⟩
  exact check_of_frontier tree 0 t5_1580root t5_1580jobs t5_1580frontier t5_1580all
theorem t5_1581choices : plan5279.choices=[8,9,6,6,6].map (options 5 5) := by rfl


theorem t5_1581part0 : t5_1581jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1581frontier : t5_1581root.frontier 0=t5_1581jobs := by rfl
theorem t5_1581all : t5_1581jobs.all (Job.check tree)=true := by
  simp only [t5_1581jobs,List.all_append,List.all_nil,t5_1581part0,Bool.and_self]
theorem t5_1581checked : Checked tree [8,9,6,6,6] := by
  refine ⟨plan5279,valid5279,t5_1581choices,?_⟩
  exact check_of_frontier tree 0 t5_1581root t5_1581jobs t5_1581frontier t5_1581all
theorem t5_1582choices : plan5280.choices=[8,9,6,6,7].map (options 5 5) := by rfl


theorem t5_1582part0 : t5_1582jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1582frontier : t5_1582root.frontier 0=t5_1582jobs := by rfl
theorem t5_1582all : t5_1582jobs.all (Job.check tree)=true := by
  simp only [t5_1582jobs,List.all_append,List.all_nil,t5_1582part0,Bool.and_self]
theorem t5_1582checked : Checked tree [8,9,6,6,7] := by
  refine ⟨plan5280,valid5280,t5_1582choices,?_⟩
  exact check_of_frontier tree 0 t5_1582root t5_1582jobs t5_1582frontier t5_1582all
theorem t5_1583choices : plan5281.choices=[8,9,6,6,10].map (options 5 5) := by rfl


theorem t5_1583part0 : t5_1583jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1583frontier : t5_1583root.frontier 0=t5_1583jobs := by rfl
theorem t5_1583all : t5_1583jobs.all (Job.check tree)=true := by
  simp only [t5_1583jobs,List.all_append,List.all_nil,t5_1583part0,Bool.and_self]
theorem t5_1583checked : Checked tree [8,9,6,6,10] := by
  refine ⟨plan5281,valid5281,t5_1583choices,?_⟩
  exact check_of_frontier tree 0 t5_1583root t5_1583jobs t5_1583frontier t5_1583all
theorem t5_1584choices : plan5282.choices=[8,9,6,7,7].map (options 5 5) := by rfl


theorem t5_1584part0 : t5_1584jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1584frontier : t5_1584root.frontier 0=t5_1584jobs := by rfl
theorem t5_1584all : t5_1584jobs.all (Job.check tree)=true := by
  simp only [t5_1584jobs,List.all_append,List.all_nil,t5_1584part0,Bool.and_self]
theorem t5_1584checked : Checked tree [8,9,6,7,7] := by
  refine ⟨plan5282,valid5282,t5_1584choices,?_⟩
  exact check_of_frontier tree 0 t5_1584root t5_1584jobs t5_1584frontier t5_1584all
theorem t5_1585choices : plan5283.choices=[8,9,6,10,7].map (options 5 5) := by rfl


theorem t5_1585part0 : t5_1585jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1585frontier : t5_1585root.frontier 0=t5_1585jobs := by rfl
theorem t5_1585all : t5_1585jobs.all (Job.check tree)=true := by
  simp only [t5_1585jobs,List.all_append,List.all_nil,t5_1585part0,Bool.and_self]
theorem t5_1585checked : Checked tree [8,9,6,10,7] := by
  refine ⟨plan5283,valid5283,t5_1585choices,?_⟩
  exact check_of_frontier tree 0 t5_1585root t5_1585jobs t5_1585frontier t5_1585all
theorem t5_1586choices : plan5284.choices=[8,9,6,10,10].map (options 5 5) := by rfl


theorem t5_1586part0 : t5_1586jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1586frontier : t5_1586root.frontier 0=t5_1586jobs := by rfl
theorem t5_1586all : t5_1586jobs.all (Job.check tree)=true := by
  simp only [t5_1586jobs,List.all_append,List.all_nil,t5_1586part0,Bool.and_self]
theorem t5_1586checked : Checked tree [8,9,6,10,10] := by
  refine ⟨plan5284,valid5284,t5_1586choices,?_⟩
  exact check_of_frontier tree 0 t5_1586root t5_1586jobs t5_1586frontier t5_1586all
theorem t5_1587choices : plan5285.choices=[8,9,7,7,7].map (options 5 5) := by rfl


theorem t5_1587part0 : t5_1587jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1587frontier : t5_1587root.frontier 0=t5_1587jobs := by rfl
theorem t5_1587all : t5_1587jobs.all (Job.check tree)=true := by
  simp only [t5_1587jobs,List.all_append,List.all_nil,t5_1587part0,Bool.and_self]
theorem t5_1587checked : Checked tree [8,9,7,7,7] := by
  refine ⟨plan5285,valid5285,t5_1587choices,?_⟩
  exact check_of_frontier tree 0 t5_1587root t5_1587jobs t5_1587frontier t5_1587all
theorem t5_1588choices : plan4439.choices=[8,9,9,3,3].map (options 5 3) := by rfl


theorem t5_1588part0 : t5_1588jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1588frontier : t5_1588root.frontier 0=t5_1588jobs := by rfl
theorem t5_1588all : t5_1588jobs.all (Job.check tree)=true := by
  simp only [t5_1588jobs,List.all_append,List.all_nil,t5_1588part0,Bool.and_self]
theorem t5_1588checked : Checked tree [8,9,9,3,3] := by
  refine ⟨plan4439,valid4439,t5_1588choices,?_⟩
  exact check_of_frontier tree 0 t5_1588root t5_1588jobs t5_1588frontier t5_1588all
theorem t5_1589choices : plan4975.choices=[8,9,9,3,6].map (options 5 4) := by rfl


theorem t5_1589part0 : t5_1589jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1589frontier : t5_1589root.frontier 0=t5_1589jobs := by rfl
theorem t5_1589all : t5_1589jobs.all (Job.check tree)=true := by
  simp only [t5_1589jobs,List.all_append,List.all_nil,t5_1589part0,Bool.and_self]
theorem t5_1589checked : Checked tree [8,9,9,3,6] := by
  refine ⟨plan4975,valid4975,t5_1589choices,?_⟩
  exact check_of_frontier tree 0 t5_1589root t5_1589jobs t5_1589frontier t5_1589all
theorem t5_1590choices : plan4976.choices=[8,9,9,3,7].map (options 5 4) := by rfl


theorem t5_1590part0 : t5_1590jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1590frontier : t5_1590root.frontier 0=t5_1590jobs := by rfl
theorem t5_1590all : t5_1590jobs.all (Job.check tree)=true := by
  simp only [t5_1590jobs,List.all_append,List.all_nil,t5_1590part0,Bool.and_self]
theorem t5_1590checked : Checked tree [8,9,9,3,7] := by
  refine ⟨plan4976,valid4976,t5_1590choices,?_⟩
  exact check_of_frontier tree 0 t5_1590root t5_1590jobs t5_1590frontier t5_1590all
theorem t5_1591choices : plan4977.choices=[8,9,9,3,10].map (options 5 4) := by rfl


theorem t5_1591part0 : t5_1591jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1591frontier : t5_1591root.frontier 0=t5_1591jobs := by rfl
theorem t5_1591all : t5_1591jobs.all (Job.check tree)=true := by
  simp only [t5_1591jobs,List.all_append,List.all_nil,t5_1591part0,Bool.and_self]
theorem t5_1591checked : Checked tree [8,9,9,3,10] := by
  refine ⟨plan4977,valid4977,t5_1591choices,?_⟩
  exact check_of_frontier tree 0 t5_1591root t5_1591jobs t5_1591frontier t5_1591all
theorem t5_1592choices : plan5286.choices=[8,9,9,6,6].map (options 5 5) := by rfl


theorem t5_1592part0 : t5_1592jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1592frontier : t5_1592root.frontier 0=t5_1592jobs := by rfl
theorem t5_1592all : t5_1592jobs.all (Job.check tree)=true := by
  simp only [t5_1592jobs,List.all_append,List.all_nil,t5_1592part0,Bool.and_self]
theorem t5_1592checked : Checked tree [8,9,9,6,6] := by
  refine ⟨plan5286,valid5286,t5_1592choices,?_⟩
  exact check_of_frontier tree 0 t5_1592root t5_1592jobs t5_1592frontier t5_1592all
theorem t5_1593choices : plan5287.choices=[8,9,9,6,7].map (options 5 5) := by rfl


theorem t5_1593part0 : t5_1593jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1593frontier : t5_1593root.frontier 0=t5_1593jobs := by rfl
theorem t5_1593all : t5_1593jobs.all (Job.check tree)=true := by
  simp only [t5_1593jobs,List.all_append,List.all_nil,t5_1593part0,Bool.and_self]
theorem t5_1593checked : Checked tree [8,9,9,6,7] := by
  refine ⟨plan5287,valid5287,t5_1593choices,?_⟩
  exact check_of_frontier tree 0 t5_1593root t5_1593jobs t5_1593frontier t5_1593all
theorem t5_1594choices : plan5288.choices=[8,9,9,6,10].map (options 5 5) := by rfl


theorem t5_1594part0 : t5_1594jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1594frontier : t5_1594root.frontier 0=t5_1594jobs := by rfl
theorem t5_1594all : t5_1594jobs.all (Job.check tree)=true := by
  simp only [t5_1594jobs,List.all_append,List.all_nil,t5_1594part0,Bool.and_self]
theorem t5_1594checked : Checked tree [8,9,9,6,10] := by
  refine ⟨plan5288,valid5288,t5_1594choices,?_⟩
  exact check_of_frontier tree 0 t5_1594root t5_1594jobs t5_1594frontier t5_1594all
theorem t5_1595choices : plan5289.choices=[8,9,9,7,7].map (options 5 5) := by rfl


theorem t5_1595part0 : t5_1595jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1595frontier : t5_1595root.frontier 0=t5_1595jobs := by rfl
theorem t5_1595all : t5_1595jobs.all (Job.check tree)=true := by
  simp only [t5_1595jobs,List.all_append,List.all_nil,t5_1595part0,Bool.and_self]
theorem t5_1595checked : Checked tree [8,9,9,7,7] := by
  refine ⟨plan5289,valid5289,t5_1595choices,?_⟩
  exact check_of_frontier tree 0 t5_1595root t5_1595jobs t5_1595frontier t5_1595all
theorem t5_1596choices : plan4978.choices=[8,9,9,9,3].map (options 5 4) := by rfl


theorem t5_1596part0 : t5_1596jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1596frontier : t5_1596root.frontier 0=t5_1596jobs := by rfl
theorem t5_1596all : t5_1596jobs.all (Job.check tree)=true := by
  simp only [t5_1596jobs,List.all_append,List.all_nil,t5_1596part0,Bool.and_self]
theorem t5_1596checked : Checked tree [8,9,9,9,3] := by
  refine ⟨plan4978,valid4978,t5_1596choices,?_⟩
  exact check_of_frontier tree 0 t5_1596root t5_1596jobs t5_1596frontier t5_1596all
theorem t5_1597choices : plan5290.choices=[8,9,9,9,6].map (options 5 5) := by rfl


theorem t5_1597part0 : t5_1597jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1597frontier : t5_1597root.frontier 0=t5_1597jobs := by rfl
theorem t5_1597all : t5_1597jobs.all (Job.check tree)=true := by
  simp only [t5_1597jobs,List.all_append,List.all_nil,t5_1597part0,Bool.and_self]
theorem t5_1597checked : Checked tree [8,9,9,9,6] := by
  refine ⟨plan5290,valid5290,t5_1597choices,?_⟩
  exact check_of_frontier tree 0 t5_1597root t5_1597jobs t5_1597frontier t5_1597all
theorem t5_1598choices : plan5291.choices=[8,9,9,9,7].map (options 5 5) := by rfl


theorem t5_1598part0 : t5_1598jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1598frontier : t5_1598root.frontier 0=t5_1598jobs := by rfl
theorem t5_1598all : t5_1598jobs.all (Job.check tree)=true := by
  simp only [t5_1598jobs,List.all_append,List.all_nil,t5_1598part0,Bool.and_self]
theorem t5_1598checked : Checked tree [8,9,9,9,7] := by
  refine ⟨plan5291,valid5291,t5_1598choices,?_⟩
  exact check_of_frontier tree 0 t5_1598root t5_1598jobs t5_1598frontier t5_1598all
theorem t5_1599choices : plan5292.choices=[8,9,9,9,10].map (options 5 5) := by rfl


theorem t5_1599part0 : t5_1599jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1599frontier : t5_1599root.frontier 0=t5_1599jobs := by rfl
theorem t5_1599all : t5_1599jobs.all (Job.check tree)=true := by
  simp only [t5_1599jobs,List.all_append,List.all_nil,t5_1599part0,Bool.and_self]
theorem t5_1599checked : Checked tree [8,9,9,9,10] := by
  refine ⟨plan5292,valid5292,t5_1599choices,?_⟩
  exact check_of_frontier tree 0 t5_1599root t5_1599jobs t5_1599frontier t5_1599all
theorem t5_1600choices : plan5293.choices=[8,9,9,10,7].map (options 5 5) := by rfl


theorem t5_1600part0 : t5_1600jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1600frontier : t5_1600root.frontier 0=t5_1600jobs := by rfl
theorem t5_1600all : t5_1600jobs.all (Job.check tree)=true := by
  simp only [t5_1600jobs,List.all_append,List.all_nil,t5_1600part0,Bool.and_self]
theorem t5_1600checked : Checked tree [8,9,9,10,7] := by
  refine ⟨plan5293,valid5293,t5_1600choices,?_⟩
  exact check_of_frontier tree 0 t5_1600root t5_1600jobs t5_1600frontier t5_1600all
theorem t5_1601choices : plan5294.choices=[8,9,9,10,10].map (options 5 5) := by rfl


theorem t5_1601part0 : t5_1601jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1601frontier : t5_1601root.frontier 0=t5_1601jobs := by rfl
theorem t5_1601all : t5_1601jobs.all (Job.check tree)=true := by
  simp only [t5_1601jobs,List.all_append,List.all_nil,t5_1601part0,Bool.and_self]
theorem t5_1601checked : Checked tree [8,9,9,10,10] := by
  refine ⟨plan5294,valid5294,t5_1601choices,?_⟩
  exact check_of_frontier tree 0 t5_1601root t5_1601jobs t5_1601frontier t5_1601all
theorem t5_1602choices : plan5295.choices=[8,9,10,7,7].map (options 5 5) := by rfl


theorem t5_1602part0 : t5_1602jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1602frontier : t5_1602root.frontier 0=t5_1602jobs := by rfl
theorem t5_1602all : t5_1602jobs.all (Job.check tree)=true := by
  simp only [t5_1602jobs,List.all_append,List.all_nil,t5_1602part0,Bool.and_self]
theorem t5_1602checked : Checked tree [8,9,10,7,7] := by
  refine ⟨plan5295,valid5295,t5_1602choices,?_⟩
  exact check_of_frontier tree 0 t5_1602root t5_1602jobs t5_1602frontier t5_1602all
theorem t5_1603choices : plan5296.choices=[8,9,10,10,7].map (options 5 5) := by rfl


theorem t5_1603part0 : t5_1603jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1603frontier : t5_1603root.frontier 0=t5_1603jobs := by rfl
theorem t5_1603all : t5_1603jobs.all (Job.check tree)=true := by
  simp only [t5_1603jobs,List.all_append,List.all_nil,t5_1603part0,Bool.and_self]
theorem t5_1603checked : Checked tree [8,9,10,10,7] := by
  refine ⟨plan5296,valid5296,t5_1603choices,?_⟩
  exact check_of_frontier tree 0 t5_1603root t5_1603jobs t5_1603frontier t5_1603all
theorem t5_1604choices : plan5297.choices=[8,9,10,10,10].map (options 5 5) := by rfl


theorem t5_1604part0 : t5_1604jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1604frontier : t5_1604root.frontier 0=t5_1604jobs := by rfl
theorem t5_1604all : t5_1604jobs.all (Job.check tree)=true := by
  simp only [t5_1604jobs,List.all_append,List.all_nil,t5_1604part0,Bool.and_self]
theorem t5_1604checked : Checked tree [8,9,10,10,10] := by
  refine ⟨plan5297,valid5297,t5_1604choices,?_⟩
  exact check_of_frontier tree 0 t5_1604root t5_1604jobs t5_1604frontier t5_1604all
theorem t5_1605choices : plan5298.choices=[8,10,7,7,7].map (options 5 5) := by rfl


theorem t5_1605part0 : t5_1605jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1605frontier : t5_1605root.frontier 0=t5_1605jobs := by rfl
theorem t5_1605all : t5_1605jobs.all (Job.check tree)=true := by
  simp only [t5_1605jobs,List.all_append,List.all_nil,t5_1605part0,Bool.and_self]
theorem t5_1605checked : Checked tree [8,10,7,7,7] := by
  refine ⟨plan5298,valid5298,t5_1605choices,?_⟩
  exact check_of_frontier tree 0 t5_1605root t5_1605jobs t5_1605frontier t5_1605all
theorem t5_1606choices : plan5299.choices=[8,10,10,7,7].map (options 5 5) := by rfl


theorem t5_1606part0 : t5_1606jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1606frontier : t5_1606root.frontier 0=t5_1606jobs := by rfl
theorem t5_1606all : t5_1606jobs.all (Job.check tree)=true := by
  simp only [t5_1606jobs,List.all_append,List.all_nil,t5_1606part0,Bool.and_self]
theorem t5_1606checked : Checked tree [8,10,10,7,7] := by
  refine ⟨plan5299,valid5299,t5_1606choices,?_⟩
  exact check_of_frontier tree 0 t5_1606root t5_1606jobs t5_1606frontier t5_1606all
theorem t5_1607choices : plan5300.choices=[8,10,10,10,7].map (options 5 5) := by rfl


theorem t5_1607part0 : t5_1607jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1607frontier : t5_1607root.frontier 0=t5_1607jobs := by rfl
theorem t5_1607all : t5_1607jobs.all (Job.check tree)=true := by
  simp only [t5_1607jobs,List.all_append,List.all_nil,t5_1607part0,Bool.and_self]
theorem t5_1607checked : Checked tree [8,10,10,10,7] := by
  refine ⟨plan5300,valid5300,t5_1607choices,?_⟩
  exact check_of_frontier tree 0 t5_1607root t5_1607jobs t5_1607frontier t5_1607all
theorem t5_1608choices : plan5301.choices=[8,10,10,10,10].map (options 5 5) := by rfl


theorem t5_1608part0 : t5_1608jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1608frontier : t5_1608root.frontier 0=t5_1608jobs := by rfl
theorem t5_1608all : t5_1608jobs.all (Job.check tree)=true := by
  simp only [t5_1608jobs,List.all_append,List.all_nil,t5_1608part0,Bool.and_self]
theorem t5_1608checked : Checked tree [8,10,10,10,10] := by
  refine ⟨plan5301,valid5301,t5_1608choices,?_⟩
  exact check_of_frontier tree 0 t5_1608root t5_1608jobs t5_1608frontier t5_1608all
theorem t5_1609choices : plan3758.choices=[9,3,3,3,3].map (options 5 1) := by rfl


theorem t5_1609part0 : t5_1609jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1609frontier : t5_1609root.frontier 0=t5_1609jobs := by rfl
theorem t5_1609all : t5_1609jobs.all (Job.check tree)=true := by
  simp only [t5_1609jobs,List.all_append,List.all_nil,t5_1609part0,Bool.and_self]
theorem t5_1609checked : Checked tree [9,3,3,3,3] := by
  refine ⟨plan3758,valid3758,t5_1609choices,?_⟩
  exact check_of_frontier tree 0 t5_1609root t5_1609jobs t5_1609frontier t5_1609all
theorem t5_1610choices : plan3996.choices=[9,3,3,3,6].map (options 5 2) := by rfl


theorem t5_1610part0 : t5_1610jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1610part1 : t5_1610jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1610frontier : t5_1610root.frontier 1=t5_1610jobs := by rfl
theorem t5_1610all : t5_1610jobs.all (Job.check tree)=true := by
  simp only [t5_1610jobs,List.all_append,List.all_nil,t5_1610part0,t5_1610part1,Bool.and_self]
theorem t5_1610checked : Checked tree [9,3,3,3,6] := by
  refine ⟨plan3996,valid3996,t5_1610choices,?_⟩
  exact check_of_frontier tree 1 t5_1610root t5_1610jobs t5_1610frontier t5_1610all
theorem t5_1611choices : plan3997.choices=[9,3,3,3,7].map (options 5 2) := by rfl


theorem t5_1611part0 : t5_1611jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1611part1 : t5_1611jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1611frontier : t5_1611root.frontier 1=t5_1611jobs := by rfl
theorem t5_1611all : t5_1611jobs.all (Job.check tree)=true := by
  simp only [t5_1611jobs,List.all_append,List.all_nil,t5_1611part0,t5_1611part1,Bool.and_self]
theorem t5_1611checked : Checked tree [9,3,3,3,7] := by
  refine ⟨plan3997,valid3997,t5_1611choices,?_⟩
  exact check_of_frontier tree 1 t5_1611root t5_1611jobs t5_1611frontier t5_1611all
theorem t5_1612choices : plan3998.choices=[9,3,3,3,10].map (options 5 2) := by rfl


theorem t5_1612part0 : t5_1612jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1612part1 : t5_1612jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1612frontier : t5_1612root.frontier 1=t5_1612jobs := by rfl
theorem t5_1612all : t5_1612jobs.all (Job.check tree)=true := by
  simp only [t5_1612jobs,List.all_append,List.all_nil,t5_1612part0,t5_1612part1,Bool.and_self]
theorem t5_1612checked : Checked tree [9,3,3,3,10] := by
  refine ⟨plan3998,valid3998,t5_1612choices,?_⟩
  exact check_of_frontier tree 1 t5_1612root t5_1612jobs t5_1612frontier t5_1612all
theorem t5_1613choices : plan4440.choices=[9,3,3,6,6].map (options 5 3) := by rfl


theorem t5_1613part0 : t5_1613jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1613part1 : t5_1613jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1613frontier : t5_1613root.frontier 1=t5_1613jobs := by rfl
theorem t5_1613all : t5_1613jobs.all (Job.check tree)=true := by
  simp only [t5_1613jobs,List.all_append,List.all_nil,t5_1613part0,t5_1613part1,Bool.and_self]
theorem t5_1613checked : Checked tree [9,3,3,6,6] := by
  refine ⟨plan4440,valid4440,t5_1613choices,?_⟩
  exact check_of_frontier tree 1 t5_1613root t5_1613jobs t5_1613frontier t5_1613all
theorem t5_1614choices : plan4441.choices=[9,3,3,6,7].map (options 5 3) := by rfl


theorem t5_1614part0 : t5_1614jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1614part1 : t5_1614jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1614part2 : t5_1614jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1614part3 : t5_1614jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_1614frontier : t5_1614root.frontier 1=t5_1614jobs := by rfl
theorem t5_1614all : t5_1614jobs.all (Job.check tree)=true := by
  simp only [t5_1614jobs,List.all_append,List.all_nil,t5_1614part0,t5_1614part1,t5_1614part2,t5_1614part3,Bool.and_self]
theorem t5_1614checked : Checked tree [9,3,3,6,7] := by
  refine ⟨plan4441,valid4441,t5_1614choices,?_⟩
  exact check_of_frontier tree 1 t5_1614root t5_1614jobs t5_1614frontier t5_1614all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks044 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1586checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1574checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1587checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1588checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1589checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1590checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1591checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1592checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1593checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1594checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1595checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1596checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1575checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1597checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1598checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1599checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1600checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1601checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1602checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1603checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1604checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1605checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1606checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1576checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1607checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1608checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1609checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1610checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1611checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1612checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1613checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1577checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1614checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1578checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1579checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1580checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1581checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1582checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1583checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1584checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1585checked⟩
