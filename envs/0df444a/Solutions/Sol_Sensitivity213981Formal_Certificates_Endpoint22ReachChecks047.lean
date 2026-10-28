-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks047
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:04:55.357221+00:00
-- url     : https://prove2.me/submissions/26796710-7388-4cf5-8356-dfa2cee770d9

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks047
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks047
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans052
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
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







theorem valid100 : plan100.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid105 : plan105.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid106 : plan106.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid108 : plan108.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid109 : plan109.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid111 : plan111.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid113 : plan113.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid114 : plan114.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid115 : plan115.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid116 : plan116.Valid := valid_step _ _ _ valid0 (by decide +kernel)







theorem valid120 : plan120.Valid := valid_step _ _ _ valid0 (by decide +kernel)







theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)







theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)


























































































































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









theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid524 : plan524.Valid := valid_step _ _ _ valid111 (by decide +kernel)











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







theorem valid543 : plan543.Valid := valid_step _ _ _ valid120 (by decide +kernel)













theorem valid550 : plan550.Valid := valid_step _ _ _ valid124 (by decide +kernel)



theorem valid552 : plan552.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid553 : plan553.Valid := valid_step _ _ _ valid124 (by decide +kernel)













theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)



theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)











theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)



theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)








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

theorem valid1499 : plan1499.Valid := valid_step _ _ _ valid536 (by decide +kernel)

theorem valid1500 : plan1500.Valid := valid_step _ _ _ valid537 (by decide +kernel)

theorem valid1501 : plan1501.Valid := valid_step _ _ _ valid538 (by decide +kernel)

theorem valid1502 : plan1502.Valid := valid_step _ _ _ valid539 (by decide +kernel)

theorem valid1503 : plan1503.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1504 : plan1504.Valid := valid_step _ _ _ valid538 (by decide +kernel)

theorem valid1505 : plan1505.Valid := valid_step _ _ _ valid539 (by decide +kernel)









theorem valid1510 : plan1510.Valid := valid_step _ _ _ valid543 (by decide +kernel)



















theorem valid1520 : plan1520.Valid := valid_step _ _ _ valid550 (by decide +kernel)



theorem valid1522 : plan1522.Valid := valid_step _ _ _ valid552 (by decide +kernel)

theorem valid1523 : plan1523.Valid := valid_step _ _ _ valid553 (by decide +kernel)























theorem valid1535 : plan1535.Valid := valid_step _ _ _ valid562 (by decide +kernel)


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





























































theorem valid4447 : plan4447.Valid := valid_step _ _ _ valid2860 (by decide +kernel)

theorem valid4448 : plan4448.Valid := valid_step _ _ _ valid2861 (by decide +kernel)

theorem valid4449 : plan4449.Valid := valid_step _ _ _ valid2868 (by decide +kernel)






























































































































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





































theorem valid3187 : plan3187.Valid := valid_step _ _ _ valid1489 (by decide +kernel)

























































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

theorem valid3229 : plan3229.Valid := valid_step _ _ _ valid1499 (by decide +kernel)

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

















theorem valid3248 : plan3248.Valid := valid_step _ _ _ valid1510 (by decide +kernel)





















theorem valid3259 : plan3259.Valid := valid_step _ _ _ valid1522 (by decide +kernel)










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

theorem valid4993 : plan4993.Valid := valid_step _ _ _ valid3081 (by decide +kernel)

theorem valid4994 : plan4994.Valid := valid_step _ _ _ valid3082 (by decide +kernel)

theorem valid4995 : plan4995.Valid := valid_step _ _ _ valid3090 (by decide +kernel)

theorem valid4996 : plan4996.Valid := valid_step _ _ _ valid3091 (by decide +kernel)

theorem valid4997 : plan4997.Valid := valid_step _ _ _ valid3092 (by decide +kernel)

theorem valid4998 : plan4998.Valid := valid_step _ _ _ valid3097 (by decide +kernel)




















































































































































































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

























































































































































































theorem valid4989 : plan4989.Valid := valid_step _ _ _ valid3077 (by decide +kernel)

theorem valid4990 : plan4990.Valid := valid_step _ _ _ valid3078 (by decide +kernel)

theorem valid4991 : plan4991.Valid := valid_step _ _ _ valid3079 (by decide +kernel)

theorem valid4992 : plan4992.Valid := valid_step _ _ _ valid3080 (by decide +kernel)
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













theorem valid1543 : plan1543.Valid := valid_step _ _ _ valid560 (by decide +kernel)



theorem valid1545 : plan1545.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1546 : plan1546.Valid := valid_step _ _ _ valid563 (by decide +kernel)



theorem valid1548 : plan1548.Valid := valid_step _ _ _ valid562 (by decide +kernel)









theorem valid1553 : plan1553.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1554 : plan1554.Valid := valid_step _ _ _ valid563 (by decide +kernel)































theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)



theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)



theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)









theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)








































































































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









theorem valid3269 : plan3269.Valid := valid_step _ _ _ valid1520 (by decide +kernel)



theorem valid3271 : plan3271.Valid := valid_step _ _ _ valid1522 (by decide +kernel)

theorem valid3272 : plan3272.Valid := valid_step _ _ _ valid1523 (by decide +kernel)









































theorem valid3293 : plan3293.Valid := valid_step _ _ _ valid1545 (by decide +kernel)





theorem valid3296 : plan3296.Valid := valid_step _ _ _ valid1548 (by decide +kernel)







theorem valid3300 : plan3300.Valid := valid_step _ _ _ valid1553 (by decide +kernel)

























theorem valid3313 : plan3313.Valid := valid_step _ _ _ valid1543 (by decide +kernel)



theorem valid3315 : plan3315.Valid := valid_step _ _ _ valid1545 (by decide +kernel)

theorem valid3316 : plan3316.Valid := valid_step _ _ _ valid1546 (by decide +kernel)



theorem valid3318 : plan3318.Valid := valid_step _ _ _ valid1548 (by decide +kernel)

theorem valid3319 : plan3319.Valid := valid_step _ _ _ valid1553 (by decide +kernel)

theorem valid3320 : plan3320.Valid := valid_step _ _ _ valid1554 (by decide +kernel)

















theorem valid3329 : plan3329.Valid := valid_step _ _ _ valid1535 (by decide +kernel)






























































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

































































theorem valid5313 : plan5313.Valid := valid_step _ _ _ valid3216 (by decide +kernel)

theorem valid5314 : plan5314.Valid := valid_step _ _ _ valid3217 (by decide +kernel)

theorem valid5315 : plan5315.Valid := valid_step _ _ _ valid3218 (by decide +kernel)

theorem valid5316 : plan5316.Valid := valid_step _ _ _ valid3219 (by decide +kernel)

theorem valid5317 : plan5317.Valid := valid_step _ _ _ valid3220 (by decide +kernel)

theorem valid5318 : plan5318.Valid := valid_step _ _ _ valid3221 (by decide +kernel)

theorem valid5319 : plan5319.Valid := valid_step _ _ _ valid3222 (by decide +kernel)

theorem valid5320 : plan5320.Valid := valid_step _ _ _ valid3223 (by decide +kernel)

theorem valid5321 : plan5321.Valid := valid_step _ _ _ valid3224 (by decide +kernel)

theorem valid5322 : plan5322.Valid := valid_step _ _ _ valid3225 (by decide +kernel)

theorem valid5323 : plan5323.Valid := valid_step _ _ _ valid3226 (by decide +kernel)

theorem valid5324 : plan5324.Valid := valid_step _ _ _ valid3227 (by decide +kernel)

theorem valid5325 : plan5325.Valid := valid_step _ _ _ valid3228 (by decide +kernel)

theorem valid5326 : plan5326.Valid := valid_step _ _ _ valid3229 (by decide +kernel)

theorem valid5327 : plan5327.Valid := valid_step _ _ _ valid3230 (by decide +kernel)

theorem valid5328 : plan5328.Valid := valid_step _ _ _ valid3231 (by decide +kernel)

theorem valid5329 : plan5329.Valid := valid_step _ _ _ valid3232 (by decide +kernel)

theorem valid5330 : plan5330.Valid := valid_step _ _ _ valid3233 (by decide +kernel)

theorem valid5331 : plan5331.Valid := valid_step _ _ _ valid3234 (by decide +kernel)

theorem valid5332 : plan5332.Valid := valid_step _ _ _ valid3235 (by decide +kernel)

theorem valid5333 : plan5333.Valid := valid_step _ _ _ valid3236 (by decide +kernel)

theorem valid5334 : plan5334.Valid := valid_step _ _ _ valid3237 (by decide +kernel)

theorem valid5335 : plan5335.Valid := valid_step _ _ _ valid3238 (by decide +kernel)

theorem valid5336 : plan5336.Valid := valid_step _ _ _ valid3239 (by decide +kernel)

theorem valid5337 : plan5337.Valid := valid_step _ _ _ valid3187 (by decide +kernel)

theorem valid5338 : plan5338.Valid := valid_step _ _ _ valid3236 (by decide +kernel)

theorem valid5339 : plan5339.Valid := valid_step _ _ _ valid3237 (by decide +kernel)

theorem valid5340 : plan5340.Valid := valid_step _ _ _ valid3238 (by decide +kernel)

theorem valid5341 : plan5341.Valid := valid_step _ _ _ valid3239 (by decide +kernel)





















theorem valid5352 : plan5352.Valid := valid_step _ _ _ valid3248 (by decide +kernel)























theorem valid5364 : plan5364.Valid := valid_step _ _ _ valid3271 (by decide +kernel)

















theorem valid5373 : plan5373.Valid := valid_step _ _ _ valid3259 (by decide +kernel)






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











theorem valid5382 : plan5382.Valid := valid_step _ _ _ valid3269 (by decide +kernel)



theorem valid5384 : plan5384.Valid := valid_step _ _ _ valid3271 (by decide +kernel)

theorem valid5385 : plan5385.Valid := valid_step _ _ _ valid3272 (by decide +kernel)































































theorem valid5417 : plan5417.Valid := valid_step _ _ _ valid3296 (by decide +kernel)





theorem valid5420 : plan5420.Valid := valid_step _ _ _ valid3315 (by decide +kernel)



theorem valid5422 : plan5422.Valid := valid_step _ _ _ valid3318 (by decide +kernel)

theorem valid5423 : plan5423.Valid := valid_step _ _ _ valid3319 (by decide +kernel)



























theorem valid5437 : plan5437.Valid := valid_step _ _ _ valid3293 (by decide +kernel)





theorem valid5440 : plan5440.Valid := valid_step _ _ _ valid3296 (by decide +kernel)







theorem valid5444 : plan5444.Valid := valid_step _ _ _ valid3300 (by decide +kernel)



















theorem valid5454 : plan5454.Valid := valid_step _ _ _ valid3313 (by decide +kernel)



theorem valid5456 : plan5456.Valid := valid_step _ _ _ valid3315 (by decide +kernel)

theorem valid5457 : plan5457.Valid := valid_step _ _ _ valid3316 (by decide +kernel)



theorem valid5459 : plan5459.Valid := valid_step _ _ _ valid3318 (by decide +kernel)

theorem valid5460 : plan5460.Valid := valid_step _ _ _ valid3319 (by decide +kernel)

theorem valid5461 : plan5461.Valid := valid_step _ _ _ valid3320 (by decide +kernel)











theorem valid5467 : plan5467.Valid := valid_step _ _ _ valid3329 (by decide +kernel)










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





















































































theorem valid6283 : plan6283.Valid := valid_step _ _ _ valid5352 (by decide +kernel)









































































theorem valid6320 : plan6320.Valid := valid_step _ _ _ valid5364 (by decide +kernel)

theorem valid6321 : plan6321.Valid := valid_step _ _ _ valid5373 (by decide +kernel)

theorem valid6322 : plan6322.Valid := valid_step _ _ _ valid5382 (by decide +kernel)

theorem valid6323 : plan6323.Valid := valid_step _ _ _ valid5384 (by decide +kernel)

theorem valid6324 : plan6324.Valid := valid_step _ _ _ valid5385 (by decide +kernel)
























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





















































theorem valid3387 : plan3387.Valid := valid_step _ _ _ valid1572 (by decide +kernel)





theorem valid3390 : plan3390.Valid := valid_step _ _ _ valid1575 (by decide +kernel)









theorem valid3395 : plan3395.Valid := valid_step _ _ _ valid1580 (by decide +kernel)







theorem valid3399 : plan3399.Valid := valid_step _ _ _ valid1570 (by decide +kernel)



theorem valid3401 : plan3401.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3402 : plan3402.Valid := valid_step _ _ _ valid1573 (by decide +kernel)



theorem valid3404 : plan3404.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3405 : plan3405.Valid := valid_step _ _ _ valid1580 (by decide +kernel)





theorem valid3408 : plan3408.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

































theorem valid3425 : plan3425.Valid := valid_step _ _ _ valid1575 (by decide +kernel)















theorem valid3433 : plan3433.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3434 : plan3434.Valid := valid_step _ _ _ valid1580 (by decide +kernel)












































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



































































































































theorem valid5538 : plan5538.Valid := valid_step _ _ _ valid3390 (by decide +kernel)





theorem valid5541 : plan5541.Valid := valid_step _ _ _ valid3401 (by decide +kernel)



theorem valid5543 : plan5543.Valid := valid_step _ _ _ valid3404 (by decide +kernel)

theorem valid5544 : plan5544.Valid := valid_step _ _ _ valid3405 (by decide +kernel)



theorem valid5546 : plan5546.Valid := valid_step _ _ _ valid3408 (by decide +kernel)





theorem valid5549 : plan5549.Valid := valid_step _ _ _ valid3425 (by decide +kernel)



theorem valid5551 : plan5551.Valid := valid_step _ _ _ valid3433 (by decide +kernel)

theorem valid5552 : plan5552.Valid := valid_step _ _ _ valid3434 (by decide +kernel)
































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



theorem valid6434 : plan6434.Valid := valid_step _ _ _ valid5417 (by decide +kernel)

theorem valid6435 : plan6435.Valid := valid_step _ _ _ valid5420 (by decide +kernel)

theorem valid6436 : plan6436.Valid := valid_step _ _ _ valid5422 (by decide +kernel)

theorem valid6437 : plan6437.Valid := valid_step _ _ _ valid5423 (by decide +kernel)

theorem valid6438 : plan6438.Valid := valid_step _ _ _ valid5437 (by decide +kernel)

theorem valid6439 : plan6439.Valid := valid_step _ _ _ valid5440 (by decide +kernel)

theorem valid6440 : plan6440.Valid := valid_step _ _ _ valid5444 (by decide +kernel)

theorem valid6441 : plan6441.Valid := valid_step _ _ _ valid5454 (by decide +kernel)

theorem valid6442 : plan6442.Valid := valid_step _ _ _ valid5456 (by decide +kernel)

theorem valid6443 : plan6443.Valid := valid_step _ _ _ valid5457 (by decide +kernel)

theorem valid6444 : plan6444.Valid := valid_step _ _ _ valid5459 (by decide +kernel)

theorem valid6445 : plan6445.Valid := valid_step _ _ _ valid5460 (by decide +kernel)

theorem valid6446 : plan6446.Valid := valid_step _ _ _ valid5461 (by decide +kernel)

theorem valid6447 : plan6447.Valid := valid_step _ _ _ valid5467 (by decide +kernel)


































































































































































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

























theorem valid5581 : plan5581.Valid := valid_step _ _ _ valid3387 (by decide +kernel)





theorem valid5584 : plan5584.Valid := valid_step _ _ _ valid3390 (by decide +kernel)







theorem valid5588 : plan5588.Valid := valid_step _ _ _ valid3395 (by decide +kernel)







theorem valid5592 : plan5592.Valid := valid_step _ _ _ valid3399 (by decide +kernel)



theorem valid5594 : plan5594.Valid := valid_step _ _ _ valid3401 (by decide +kernel)

theorem valid5595 : plan5595.Valid := valid_step _ _ _ valid3402 (by decide +kernel)










































































































































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











































































































































theorem valid6694 : plan6694.Valid := valid_step _ _ _ valid5538 (by decide +kernel)

theorem valid6695 : plan6695.Valid := valid_step _ _ _ valid5541 (by decide +kernel)

theorem valid6696 : plan6696.Valid := valid_step _ _ _ valid5543 (by decide +kernel)

theorem valid6697 : plan6697.Valid := valid_step _ _ _ valid5544 (by decide +kernel)

theorem valid6698 : plan6698.Valid := valid_step _ _ _ valid5546 (by decide +kernel)

theorem valid6699 : plan6699.Valid := valid_step _ _ _ valid5549 (by decide +kernel)

theorem valid6700 : plan6700.Valid := valid_step _ _ _ valid5551 (by decide +kernel)

theorem valid6701 : plan6701.Valid := valid_step _ _ _ valid5552 (by decide +kernel)

theorem valid6702 : plan6702.Valid := valid_step _ _ _ valid5581 (by decide +kernel)

theorem valid6703 : plan6703.Valid := valid_step _ _ _ valid5584 (by decide +kernel)

theorem valid6704 : plan6704.Valid := valid_step _ _ _ valid5588 (by decide +kernel)

theorem valid6705 : plan6705.Valid := valid_step _ _ _ valid5592 (by decide +kernel)

theorem valid6706 : plan6706.Valid := valid_step _ _ _ valid5594 (by decide +kernel)

theorem valid6707 : plan6707.Valid := valid_step _ _ _ valid5595 (by decide +kernel)


























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
theorem t5_1642choices : plan4447.choices=[9,9,3,3,7].map (options 5 3) := by rfl


theorem t5_1642part0 : t5_1642jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1642part1 : t5_1642jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1642frontier : t5_1642root.frontier 1=t5_1642jobs := by rfl
theorem t5_1642all : t5_1642jobs.all (Job.check tree)=true := by
  simp only [t5_1642jobs,List.all_append,List.all_nil,t5_1642part0,t5_1642part1,Bool.and_self]
theorem t5_1642checked : Checked tree [9,9,3,3,7] := by
  refine ⟨plan4447,valid4447,t5_1642choices,?_⟩
  exact check_of_frontier tree 1 t5_1642root t5_1642jobs t5_1642frontier t5_1642all
theorem t5_1643choices : plan4448.choices=[9,9,3,3,10].map (options 5 3) := by rfl


theorem t5_1643part0 : t5_1643jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1643frontier : t5_1643root.frontier 0=t5_1643jobs := by rfl
theorem t5_1643all : t5_1643jobs.all (Job.check tree)=true := by
  simp only [t5_1643jobs,List.all_append,List.all_nil,t5_1643part0,Bool.and_self]
theorem t5_1643checked : Checked tree [9,9,3,3,10] := by
  refine ⟨plan4448,valid4448,t5_1643choices,?_⟩
  exact check_of_frontier tree 0 t5_1643root t5_1643jobs t5_1643frontier t5_1643all
theorem t5_1644choices : plan4989.choices=[9,9,3,6,6].map (options 5 4) := by rfl


theorem t5_1644part0 : t5_1644jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1644frontier : t5_1644root.frontier 0=t5_1644jobs := by rfl
theorem t5_1644all : t5_1644jobs.all (Job.check tree)=true := by
  simp only [t5_1644jobs,List.all_append,List.all_nil,t5_1644part0,Bool.and_self]
theorem t5_1644checked : Checked tree [9,9,3,6,6] := by
  refine ⟨plan4989,valid4989,t5_1644choices,?_⟩
  exact check_of_frontier tree 0 t5_1644root t5_1644jobs t5_1644frontier t5_1644all
theorem t5_1645choices : plan4990.choices=[9,9,3,6,7].map (options 5 4) := by rfl


theorem t5_1645part0 : t5_1645jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1645part1 : t5_1645jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1645frontier : t5_1645root.frontier 1=t5_1645jobs := by rfl
theorem t5_1645all : t5_1645jobs.all (Job.check tree)=true := by
  simp only [t5_1645jobs,List.all_append,List.all_nil,t5_1645part0,t5_1645part1,Bool.and_self]
theorem t5_1645checked : Checked tree [9,9,3,6,7] := by
  refine ⟨plan4990,valid4990,t5_1645choices,?_⟩
  exact check_of_frontier tree 1 t5_1645root t5_1645jobs t5_1645frontier t5_1645all
theorem t5_1646choices : plan4991.choices=[9,9,3,6,10].map (options 5 4) := by rfl


theorem t5_1646part0 : t5_1646jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1646frontier : t5_1646root.frontier 0=t5_1646jobs := by rfl
theorem t5_1646all : t5_1646jobs.all (Job.check tree)=true := by
  simp only [t5_1646jobs,List.all_append,List.all_nil,t5_1646part0,Bool.and_self]
theorem t5_1646checked : Checked tree [9,9,3,6,10] := by
  refine ⟨plan4991,valid4991,t5_1646choices,?_⟩
  exact check_of_frontier tree 0 t5_1646root t5_1646jobs t5_1646frontier t5_1646all
theorem t5_1647choices : plan4992.choices=[9,9,3,7,7].map (options 5 4) := by rfl


theorem t5_1647part0 : t5_1647jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1647frontier : t5_1647root.frontier 0=t5_1647jobs := by rfl
theorem t5_1647all : t5_1647jobs.all (Job.check tree)=true := by
  simp only [t5_1647jobs,List.all_append,List.all_nil,t5_1647part0,Bool.and_self]
theorem t5_1647checked : Checked tree [9,9,3,7,7] := by
  refine ⟨plan4992,valid4992,t5_1647choices,?_⟩
  exact check_of_frontier tree 0 t5_1647root t5_1647jobs t5_1647frontier t5_1647all
theorem t5_1648choices : plan4993.choices=[9,9,3,10,7].map (options 5 4) := by rfl


theorem t5_1648part0 : t5_1648jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1648part1 : t5_1648jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1648frontier : t5_1648root.frontier 1=t5_1648jobs := by rfl
theorem t5_1648all : t5_1648jobs.all (Job.check tree)=true := by
  simp only [t5_1648jobs,List.all_append,List.all_nil,t5_1648part0,t5_1648part1,Bool.and_self]
theorem t5_1648checked : Checked tree [9,9,3,10,7] := by
  refine ⟨plan4993,valid4993,t5_1648choices,?_⟩
  exact check_of_frontier tree 1 t5_1648root t5_1648jobs t5_1648frontier t5_1648all
theorem t5_1649choices : plan4994.choices=[9,9,3,10,10].map (options 5 4) := by rfl


theorem t5_1649part0 : t5_1649jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1649frontier : t5_1649root.frontier 0=t5_1649jobs := by rfl
theorem t5_1649all : t5_1649jobs.all (Job.check tree)=true := by
  simp only [t5_1649jobs,List.all_append,List.all_nil,t5_1649part0,Bool.and_self]
theorem t5_1649checked : Checked tree [9,9,3,10,10] := by
  refine ⟨plan4994,valid4994,t5_1649choices,?_⟩
  exact check_of_frontier tree 0 t5_1649root t5_1649jobs t5_1649frontier t5_1649all
theorem t5_1650choices : plan5313.choices=[9,9,6,6,6].map (options 5 5) := by rfl


theorem t5_1650part0 : t5_1650jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1650frontier : t5_1650root.frontier 0=t5_1650jobs := by rfl
theorem t5_1650all : t5_1650jobs.all (Job.check tree)=true := by
  simp only [t5_1650jobs,List.all_append,List.all_nil,t5_1650part0,Bool.and_self]
theorem t5_1650checked : Checked tree [9,9,6,6,6] := by
  refine ⟨plan5313,valid5313,t5_1650choices,?_⟩
  exact check_of_frontier tree 0 t5_1650root t5_1650jobs t5_1650frontier t5_1650all
theorem t5_1651choices : plan5314.choices=[9,9,6,6,7].map (options 5 5) := by rfl


theorem t5_1651part0 : t5_1651jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1651frontier : t5_1651root.frontier 0=t5_1651jobs := by rfl
theorem t5_1651all : t5_1651jobs.all (Job.check tree)=true := by
  simp only [t5_1651jobs,List.all_append,List.all_nil,t5_1651part0,Bool.and_self]
theorem t5_1651checked : Checked tree [9,9,6,6,7] := by
  refine ⟨plan5314,valid5314,t5_1651choices,?_⟩
  exact check_of_frontier tree 0 t5_1651root t5_1651jobs t5_1651frontier t5_1651all
theorem t5_1652choices : plan5315.choices=[9,9,6,6,10].map (options 5 5) := by rfl


theorem t5_1652part0 : t5_1652jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1652frontier : t5_1652root.frontier 0=t5_1652jobs := by rfl
theorem t5_1652all : t5_1652jobs.all (Job.check tree)=true := by
  simp only [t5_1652jobs,List.all_append,List.all_nil,t5_1652part0,Bool.and_self]
theorem t5_1652checked : Checked tree [9,9,6,6,10] := by
  refine ⟨plan5315,valid5315,t5_1652choices,?_⟩
  exact check_of_frontier tree 0 t5_1652root t5_1652jobs t5_1652frontier t5_1652all
theorem t5_1653choices : plan5316.choices=[9,9,6,7,7].map (options 5 5) := by rfl


theorem t5_1653part0 : t5_1653jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1653frontier : t5_1653root.frontier 0=t5_1653jobs := by rfl
theorem t5_1653all : t5_1653jobs.all (Job.check tree)=true := by
  simp only [t5_1653jobs,List.all_append,List.all_nil,t5_1653part0,Bool.and_self]
theorem t5_1653checked : Checked tree [9,9,6,7,7] := by
  refine ⟨plan5316,valid5316,t5_1653choices,?_⟩
  exact check_of_frontier tree 0 t5_1653root t5_1653jobs t5_1653frontier t5_1653all
theorem t5_1654choices : plan5317.choices=[9,9,6,10,7].map (options 5 5) := by rfl


theorem t5_1654part0 : t5_1654jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1654frontier : t5_1654root.frontier 0=t5_1654jobs := by rfl
theorem t5_1654all : t5_1654jobs.all (Job.check tree)=true := by
  simp only [t5_1654jobs,List.all_append,List.all_nil,t5_1654part0,Bool.and_self]
theorem t5_1654checked : Checked tree [9,9,6,10,7] := by
  refine ⟨plan5317,valid5317,t5_1654choices,?_⟩
  exact check_of_frontier tree 0 t5_1654root t5_1654jobs t5_1654frontier t5_1654all
theorem t5_1655choices : plan5318.choices=[9,9,6,10,10].map (options 5 5) := by rfl


theorem t5_1655part0 : t5_1655jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1655frontier : t5_1655root.frontier 0=t5_1655jobs := by rfl
theorem t5_1655all : t5_1655jobs.all (Job.check tree)=true := by
  simp only [t5_1655jobs,List.all_append,List.all_nil,t5_1655part0,Bool.and_self]
theorem t5_1655checked : Checked tree [9,9,6,10,10] := by
  refine ⟨plan5318,valid5318,t5_1655choices,?_⟩
  exact check_of_frontier tree 0 t5_1655root t5_1655jobs t5_1655frontier t5_1655all
theorem t5_1656choices : plan5319.choices=[9,9,7,7,7].map (options 5 5) := by rfl


theorem t5_1656part0 : t5_1656jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1656frontier : t5_1656root.frontier 0=t5_1656jobs := by rfl
theorem t5_1656all : t5_1656jobs.all (Job.check tree)=true := by
  simp only [t5_1656jobs,List.all_append,List.all_nil,t5_1656part0,Bool.and_self]
theorem t5_1656checked : Checked tree [9,9,7,7,7] := by
  refine ⟨plan5319,valid5319,t5_1656choices,?_⟩
  exact check_of_frontier tree 0 t5_1656root t5_1656jobs t5_1656frontier t5_1656all
theorem t5_1657choices : plan4449.choices=[9,9,9,3,3].map (options 5 3) := by rfl


theorem t5_1657part0 : t5_1657jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1657frontier : t5_1657root.frontier 0=t5_1657jobs := by rfl
theorem t5_1657all : t5_1657jobs.all (Job.check tree)=true := by
  simp only [t5_1657jobs,List.all_append,List.all_nil,t5_1657part0,Bool.and_self]
theorem t5_1657checked : Checked tree [9,9,9,3,3] := by
  refine ⟨plan4449,valid4449,t5_1657choices,?_⟩
  exact check_of_frontier tree 0 t5_1657root t5_1657jobs t5_1657frontier t5_1657all
theorem t5_1658choices : plan4995.choices=[9,9,9,3,6].map (options 5 4) := by rfl


theorem t5_1658part0 : t5_1658jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1658frontier : t5_1658root.frontier 0=t5_1658jobs := by rfl
theorem t5_1658all : t5_1658jobs.all (Job.check tree)=true := by
  simp only [t5_1658jobs,List.all_append,List.all_nil,t5_1658part0,Bool.and_self]
theorem t5_1658checked : Checked tree [9,9,9,3,6] := by
  refine ⟨plan4995,valid4995,t5_1658choices,?_⟩
  exact check_of_frontier tree 0 t5_1658root t5_1658jobs t5_1658frontier t5_1658all
theorem t5_1659choices : plan4996.choices=[9,9,9,3,7].map (options 5 4) := by rfl


theorem t5_1659part0 : t5_1659jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1659frontier : t5_1659root.frontier 0=t5_1659jobs := by rfl
theorem t5_1659all : t5_1659jobs.all (Job.check tree)=true := by
  simp only [t5_1659jobs,List.all_append,List.all_nil,t5_1659part0,Bool.and_self]
theorem t5_1659checked : Checked tree [9,9,9,3,7] := by
  refine ⟨plan4996,valid4996,t5_1659choices,?_⟩
  exact check_of_frontier tree 0 t5_1659root t5_1659jobs t5_1659frontier t5_1659all
theorem t5_1660choices : plan4997.choices=[9,9,9,3,10].map (options 5 4) := by rfl


theorem t5_1660part0 : t5_1660jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1660frontier : t5_1660root.frontier 0=t5_1660jobs := by rfl
theorem t5_1660all : t5_1660jobs.all (Job.check tree)=true := by
  simp only [t5_1660jobs,List.all_append,List.all_nil,t5_1660part0,Bool.and_self]
theorem t5_1660checked : Checked tree [9,9,9,3,10] := by
  refine ⟨plan4997,valid4997,t5_1660choices,?_⟩
  exact check_of_frontier tree 0 t5_1660root t5_1660jobs t5_1660frontier t5_1660all
theorem t5_1661choices : plan5320.choices=[9,9,9,6,6].map (options 5 5) := by rfl


theorem t5_1661part0 : t5_1661jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1661frontier : t5_1661root.frontier 0=t5_1661jobs := by rfl
theorem t5_1661all : t5_1661jobs.all (Job.check tree)=true := by
  simp only [t5_1661jobs,List.all_append,List.all_nil,t5_1661part0,Bool.and_self]
theorem t5_1661checked : Checked tree [9,9,9,6,6] := by
  refine ⟨plan5320,valid5320,t5_1661choices,?_⟩
  exact check_of_frontier tree 0 t5_1661root t5_1661jobs t5_1661frontier t5_1661all
theorem t5_1662choices : plan5321.choices=[9,9,9,6,7].map (options 5 5) := by rfl


theorem t5_1662part0 : t5_1662jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1662frontier : t5_1662root.frontier 0=t5_1662jobs := by rfl
theorem t5_1662all : t5_1662jobs.all (Job.check tree)=true := by
  simp only [t5_1662jobs,List.all_append,List.all_nil,t5_1662part0,Bool.and_self]
theorem t5_1662checked : Checked tree [9,9,9,6,7] := by
  refine ⟨plan5321,valid5321,t5_1662choices,?_⟩
  exact check_of_frontier tree 0 t5_1662root t5_1662jobs t5_1662frontier t5_1662all
theorem t5_1663choices : plan5322.choices=[9,9,9,6,10].map (options 5 5) := by rfl


theorem t5_1663part0 : t5_1663jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1663frontier : t5_1663root.frontier 0=t5_1663jobs := by rfl
theorem t5_1663all : t5_1663jobs.all (Job.check tree)=true := by
  simp only [t5_1663jobs,List.all_append,List.all_nil,t5_1663part0,Bool.and_self]
theorem t5_1663checked : Checked tree [9,9,9,6,10] := by
  refine ⟨plan5322,valid5322,t5_1663choices,?_⟩
  exact check_of_frontier tree 0 t5_1663root t5_1663jobs t5_1663frontier t5_1663all
theorem t5_1664choices : plan5323.choices=[9,9,9,7,7].map (options 5 5) := by rfl


theorem t5_1664part0 : t5_1664jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1664frontier : t5_1664root.frontier 0=t5_1664jobs := by rfl
theorem t5_1664all : t5_1664jobs.all (Job.check tree)=true := by
  simp only [t5_1664jobs,List.all_append,List.all_nil,t5_1664part0,Bool.and_self]
theorem t5_1664checked : Checked tree [9,9,9,7,7] := by
  refine ⟨plan5323,valid5323,t5_1664choices,?_⟩
  exact check_of_frontier tree 0 t5_1664root t5_1664jobs t5_1664frontier t5_1664all
theorem t5_1665choices : plan4998.choices=[9,9,9,9,3].map (options 5 4) := by rfl


theorem t5_1665part0 : t5_1665jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1665frontier : t5_1665root.frontier 0=t5_1665jobs := by rfl
theorem t5_1665all : t5_1665jobs.all (Job.check tree)=true := by
  simp only [t5_1665jobs,List.all_append,List.all_nil,t5_1665part0,Bool.and_self]
theorem t5_1665checked : Checked tree [9,9,9,9,3] := by
  refine ⟨plan4998,valid4998,t5_1665choices,?_⟩
  exact check_of_frontier tree 0 t5_1665root t5_1665jobs t5_1665frontier t5_1665all
theorem t5_1666choices : plan5324.choices=[9,9,9,9,6].map (options 5 5) := by rfl


theorem t5_1666part0 : t5_1666jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1666frontier : t5_1666root.frontier 0=t5_1666jobs := by rfl
theorem t5_1666all : t5_1666jobs.all (Job.check tree)=true := by
  simp only [t5_1666jobs,List.all_append,List.all_nil,t5_1666part0,Bool.and_self]
theorem t5_1666checked : Checked tree [9,9,9,9,6] := by
  refine ⟨plan5324,valid5324,t5_1666choices,?_⟩
  exact check_of_frontier tree 0 t5_1666root t5_1666jobs t5_1666frontier t5_1666all
theorem t5_1667choices : plan5325.choices=[9,9,9,9,7].map (options 5 5) := by rfl


theorem t5_1667part0 : t5_1667jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1667frontier : t5_1667root.frontier 0=t5_1667jobs := by rfl
theorem t5_1667all : t5_1667jobs.all (Job.check tree)=true := by
  simp only [t5_1667jobs,List.all_append,List.all_nil,t5_1667part0,Bool.and_self]
theorem t5_1667checked : Checked tree [9,9,9,9,7] := by
  refine ⟨plan5325,valid5325,t5_1667choices,?_⟩
  exact check_of_frontier tree 0 t5_1667root t5_1667jobs t5_1667frontier t5_1667all
theorem t5_1668choices : plan5326.choices=[9,9,9,9,9].map (options 5 5) := by rfl


theorem t5_1668part0 : t5_1668jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1668frontier : t5_1668root.frontier 0=t5_1668jobs := by rfl
theorem t5_1668all : t5_1668jobs.all (Job.check tree)=true := by
  simp only [t5_1668jobs,List.all_append,List.all_nil,t5_1668part0,Bool.and_self]
theorem t5_1668checked : Checked tree [9,9,9,9,9] := by
  refine ⟨plan5326,valid5326,t5_1668choices,?_⟩
  exact check_of_frontier tree 0 t5_1668root t5_1668jobs t5_1668frontier t5_1668all
theorem t5_1669choices : plan5327.choices=[9,9,9,9,10].map (options 5 5) := by rfl


theorem t5_1669part0 : t5_1669jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1669frontier : t5_1669root.frontier 0=t5_1669jobs := by rfl
theorem t5_1669all : t5_1669jobs.all (Job.check tree)=true := by
  simp only [t5_1669jobs,List.all_append,List.all_nil,t5_1669part0,Bool.and_self]
theorem t5_1669checked : Checked tree [9,9,9,9,10] := by
  refine ⟨plan5327,valid5327,t5_1669choices,?_⟩
  exact check_of_frontier tree 0 t5_1669root t5_1669jobs t5_1669frontier t5_1669all
theorem t5_1670choices : plan5328.choices=[9,9,9,10,7].map (options 5 5) := by rfl


theorem t5_1670part0 : t5_1670jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1670frontier : t5_1670root.frontier 0=t5_1670jobs := by rfl
theorem t5_1670all : t5_1670jobs.all (Job.check tree)=true := by
  simp only [t5_1670jobs,List.all_append,List.all_nil,t5_1670part0,Bool.and_self]
theorem t5_1670checked : Checked tree [9,9,9,10,7] := by
  refine ⟨plan5328,valid5328,t5_1670choices,?_⟩
  exact check_of_frontier tree 0 t5_1670root t5_1670jobs t5_1670frontier t5_1670all
theorem t5_1671choices : plan5329.choices=[9,9,9,10,10].map (options 5 5) := by rfl


theorem t5_1671part0 : t5_1671jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1671frontier : t5_1671root.frontier 0=t5_1671jobs := by rfl
theorem t5_1671all : t5_1671jobs.all (Job.check tree)=true := by
  simp only [t5_1671jobs,List.all_append,List.all_nil,t5_1671part0,Bool.and_self]
theorem t5_1671checked : Checked tree [9,9,9,10,10] := by
  refine ⟨plan5329,valid5329,t5_1671choices,?_⟩
  exact check_of_frontier tree 0 t5_1671root t5_1671jobs t5_1671frontier t5_1671all
theorem t5_1672choices : plan5330.choices=[9,9,10,7,7].map (options 5 5) := by rfl


theorem t5_1672part0 : t5_1672jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1672frontier : t5_1672root.frontier 0=t5_1672jobs := by rfl
theorem t5_1672all : t5_1672jobs.all (Job.check tree)=true := by
  simp only [t5_1672jobs,List.all_append,List.all_nil,t5_1672part0,Bool.and_self]
theorem t5_1672checked : Checked tree [9,9,10,7,7] := by
  refine ⟨plan5330,valid5330,t5_1672choices,?_⟩
  exact check_of_frontier tree 0 t5_1672root t5_1672jobs t5_1672frontier t5_1672all
theorem t5_1673choices : plan5331.choices=[9,9,10,10,7].map (options 5 5) := by rfl


theorem t5_1673part0 : t5_1673jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1673frontier : t5_1673root.frontier 0=t5_1673jobs := by rfl
theorem t5_1673all : t5_1673jobs.all (Job.check tree)=true := by
  simp only [t5_1673jobs,List.all_append,List.all_nil,t5_1673part0,Bool.and_self]
theorem t5_1673checked : Checked tree [9,9,10,10,7] := by
  refine ⟨plan5331,valid5331,t5_1673choices,?_⟩
  exact check_of_frontier tree 0 t5_1673root t5_1673jobs t5_1673frontier t5_1673all
theorem t5_1674choices : plan5332.choices=[9,9,10,10,10].map (options 5 5) := by rfl


theorem t5_1674part0 : t5_1674jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1674frontier : t5_1674root.frontier 0=t5_1674jobs := by rfl
theorem t5_1674all : t5_1674jobs.all (Job.check tree)=true := by
  simp only [t5_1674jobs,List.all_append,List.all_nil,t5_1674part0,Bool.and_self]
theorem t5_1674checked : Checked tree [9,9,10,10,10] := by
  refine ⟨plan5332,valid5332,t5_1674choices,?_⟩
  exact check_of_frontier tree 0 t5_1674root t5_1674jobs t5_1674frontier t5_1674all
theorem t5_1675choices : plan5333.choices=[9,10,7,7,7].map (options 5 5) := by rfl


theorem t5_1675part0 : t5_1675jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1675frontier : t5_1675root.frontier 0=t5_1675jobs := by rfl
theorem t5_1675all : t5_1675jobs.all (Job.check tree)=true := by
  simp only [t5_1675jobs,List.all_append,List.all_nil,t5_1675part0,Bool.and_self]
theorem t5_1675checked : Checked tree [9,10,7,7,7] := by
  refine ⟨plan5333,valid5333,t5_1675choices,?_⟩
  exact check_of_frontier tree 0 t5_1675root t5_1675jobs t5_1675frontier t5_1675all
theorem t5_1676choices : plan5334.choices=[9,10,10,7,7].map (options 5 5) := by rfl


theorem t5_1676part0 : t5_1676jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1676frontier : t5_1676root.frontier 0=t5_1676jobs := by rfl
theorem t5_1676all : t5_1676jobs.all (Job.check tree)=true := by
  simp only [t5_1676jobs,List.all_append,List.all_nil,t5_1676part0,Bool.and_self]
theorem t5_1676checked : Checked tree [9,10,10,7,7] := by
  refine ⟨plan5334,valid5334,t5_1676choices,?_⟩
  exact check_of_frontier tree 0 t5_1676root t5_1676jobs t5_1676frontier t5_1676all
theorem t5_1677choices : plan5335.choices=[9,10,10,10,7].map (options 5 5) := by rfl


theorem t5_1677part0 : t5_1677jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1677frontier : t5_1677root.frontier 0=t5_1677jobs := by rfl
theorem t5_1677all : t5_1677jobs.all (Job.check tree)=true := by
  simp only [t5_1677jobs,List.all_append,List.all_nil,t5_1677part0,Bool.and_self]
theorem t5_1677checked : Checked tree [9,10,10,10,7] := by
  refine ⟨plan5335,valid5335,t5_1677choices,?_⟩
  exact check_of_frontier tree 0 t5_1677root t5_1677jobs t5_1677frontier t5_1677all
theorem t5_1678choices : plan5336.choices=[9,10,10,10,10].map (options 5 5) := by rfl


theorem t5_1678part0 : t5_1678jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1678frontier : t5_1678root.frontier 0=t5_1678jobs := by rfl
theorem t5_1678all : t5_1678jobs.all (Job.check tree)=true := by
  simp only [t5_1678jobs,List.all_append,List.all_nil,t5_1678part0,Bool.and_self]
theorem t5_1678checked : Checked tree [9,10,10,10,10] := by
  refine ⟨plan5336,valid5336,t5_1678choices,?_⟩
  exact check_of_frontier tree 0 t5_1678root t5_1678jobs t5_1678frontier t5_1678all
theorem t5_1679choices : plan5337.choices=[10,7,7,7,7].map (options 5 5) := by rfl


theorem t5_1679part0 : t5_1679jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1679frontier : t5_1679root.frontier 0=t5_1679jobs := by rfl
theorem t5_1679all : t5_1679jobs.all (Job.check tree)=true := by
  simp only [t5_1679jobs,List.all_append,List.all_nil,t5_1679part0,Bool.and_self]
theorem t5_1679checked : Checked tree [10,7,7,7,7] := by
  refine ⟨plan5337,valid5337,t5_1679choices,?_⟩
  exact check_of_frontier tree 0 t5_1679root t5_1679jobs t5_1679frontier t5_1679all
theorem t5_1680choices : plan5338.choices=[10,10,7,7,7].map (options 5 5) := by rfl


theorem t5_1680part0 : t5_1680jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1680frontier : t5_1680root.frontier 0=t5_1680jobs := by rfl
theorem t5_1680all : t5_1680jobs.all (Job.check tree)=true := by
  simp only [t5_1680jobs,List.all_append,List.all_nil,t5_1680part0,Bool.and_self]
theorem t5_1680checked : Checked tree [10,10,7,7,7] := by
  refine ⟨plan5338,valid5338,t5_1680choices,?_⟩
  exact check_of_frontier tree 0 t5_1680root t5_1680jobs t5_1680frontier t5_1680all
theorem t5_1681choices : plan5339.choices=[10,10,10,7,7].map (options 5 5) := by rfl


theorem t5_1681part0 : t5_1681jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1681frontier : t5_1681root.frontier 0=t5_1681jobs := by rfl
theorem t5_1681all : t5_1681jobs.all (Job.check tree)=true := by
  simp only [t5_1681jobs,List.all_append,List.all_nil,t5_1681part0,Bool.and_self]
theorem t5_1681checked : Checked tree [10,10,10,7,7] := by
  refine ⟨plan5339,valid5339,t5_1681choices,?_⟩
  exact check_of_frontier tree 0 t5_1681root t5_1681jobs t5_1681frontier t5_1681all
theorem t5_1682choices : plan5340.choices=[10,10,10,10,7].map (options 5 5) := by rfl


theorem t5_1682part0 : t5_1682jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1682frontier : t5_1682root.frontier 0=t5_1682jobs := by rfl
theorem t5_1682all : t5_1682jobs.all (Job.check tree)=true := by
  simp only [t5_1682jobs,List.all_append,List.all_nil,t5_1682part0,Bool.and_self]
theorem t5_1682checked : Checked tree [10,10,10,10,7] := by
  refine ⟨plan5340,valid5340,t5_1682choices,?_⟩
  exact check_of_frontier tree 0 t5_1682root t5_1682jobs t5_1682frontier t5_1682all
theorem t5_1683choices : plan5341.choices=[10,10,10,10,10].map (options 5 5) := by rfl


theorem t5_1683part0 : t5_1683jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1683frontier : t5_1683root.frontier 0=t5_1683jobs := by rfl
theorem t5_1683all : t5_1683jobs.all (Job.check tree)=true := by
  simp only [t5_1683jobs,List.all_append,List.all_nil,t5_1683part0,Bool.and_self]
theorem t5_1683checked : Checked tree [10,10,10,10,10] := by
  refine ⟨plan5341,valid5341,t5_1683choices,?_⟩
  exact check_of_frontier tree 0 t5_1683root t5_1683jobs t5_1683frontier t5_1683all
theorem t6_0choices : plan6434.choices=[0,1,2,7,7,7].map (options 6 3) := by rfl


theorem t6_0part0 : t6_0jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_0frontier : t6_0root.frontier 0=t6_0jobs := by rfl
theorem t6_0all : t6_0jobs.all (Job.check tree)=true := by
  simp only [t6_0jobs,List.all_append,List.all_nil,t6_0part0,Bool.and_self]
theorem t6_0checked : Checked tree [0,1,2,7,7,7] := by
  refine ⟨plan6434,valid6434,t6_0choices,?_⟩
  exact check_of_frontier tree 0 t6_0root t6_0jobs t6_0frontier t6_0all
theorem t6_1choices : plan6320.choices=[0,1,3,3,7,7].map (options 6 2) := by rfl


theorem t6_1part0 : t6_1jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1frontier : t6_1root.frontier 0=t6_1jobs := by rfl
theorem t6_1all : t6_1jobs.all (Job.check tree)=true := by
  simp only [t6_1jobs,List.all_append,List.all_nil,t6_1part0,Bool.and_self]
theorem t6_1checked : Checked tree [0,1,3,3,7,7] := by
  refine ⟨plan6320,valid6320,t6_1choices,?_⟩
  exact check_of_frontier tree 0 t6_1root t6_1jobs t6_1frontier t6_1all
theorem t6_2choices : plan6435.choices=[0,1,3,6,7,7].map (options 6 3) := by rfl


theorem t6_2part0 : t6_2jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_2frontier : t6_2root.frontier 0=t6_2jobs := by rfl
theorem t6_2all : t6_2jobs.all (Job.check tree)=true := by
  simp only [t6_2jobs,List.all_append,List.all_nil,t6_2part0,Bool.and_self]
theorem t6_2checked : Checked tree [0,1,3,6,7,7] := by
  refine ⟨plan6435,valid6435,t6_2choices,?_⟩
  exact check_of_frontier tree 0 t6_2root t6_2jobs t6_2frontier t6_2all
theorem t6_3choices : plan6436.choices=[0,1,3,7,7,7].map (options 6 3) := by rfl


theorem t6_3part0 : t6_3jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_3frontier : t6_3root.frontier 0=t6_3jobs := by rfl
theorem t6_3all : t6_3jobs.all (Job.check tree)=true := by
  simp only [t6_3jobs,List.all_append,List.all_nil,t6_3part0,Bool.and_self]
theorem t6_3checked : Checked tree [0,1,3,7,7,7] := by
  refine ⟨plan6436,valid6436,t6_3choices,?_⟩
  exact check_of_frontier tree 0 t6_3root t6_3jobs t6_3frontier t6_3all
theorem t6_4choices : plan6437.choices=[0,1,3,10,7,7].map (options 6 3) := by rfl


theorem t6_4part0 : t6_4jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_4frontier : t6_4root.frontier 0=t6_4jobs := by rfl
theorem t6_4all : t6_4jobs.all (Job.check tree)=true := by
  simp only [t6_4jobs,List.all_append,List.all_nil,t6_4part0,Bool.and_self]
theorem t6_4checked : Checked tree [0,1,3,10,7,7] := by
  refine ⟨plan6437,valid6437,t6_4choices,?_⟩
  exact check_of_frontier tree 0 t6_4root t6_4jobs t6_4frontier t6_4all
theorem t6_5choices : plan6694.choices=[0,1,5,7,7,7].map (options 6 4) := by rfl


theorem t6_5part0 : t6_5jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_5frontier : t6_5root.frontier 0=t6_5jobs := by rfl
theorem t6_5all : t6_5jobs.all (Job.check tree)=true := by
  simp only [t6_5jobs,List.all_append,List.all_nil,t6_5part0,Bool.and_self]
theorem t6_5checked : Checked tree [0,1,5,7,7,7] := by
  refine ⟨plan6694,valid6694,t6_5choices,?_⟩
  exact check_of_frontier tree 0 t6_5root t6_5jobs t6_5frontier t6_5all
theorem t6_6choices : plan6695.choices=[0,1,6,6,7,7].map (options 6 4) := by rfl


theorem t6_6part0 : t6_6jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_6frontier : t6_6root.frontier 0=t6_6jobs := by rfl
theorem t6_6all : t6_6jobs.all (Job.check tree)=true := by
  simp only [t6_6jobs,List.all_append,List.all_nil,t6_6part0,Bool.and_self]
theorem t6_6checked : Checked tree [0,1,6,6,7,7] := by
  refine ⟨plan6695,valid6695,t6_6choices,?_⟩
  exact check_of_frontier tree 0 t6_6root t6_6jobs t6_6frontier t6_6all
theorem t6_7choices : plan6696.choices=[0,1,6,7,7,7].map (options 6 4) := by rfl


theorem t6_7part0 : t6_7jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_7frontier : t6_7root.frontier 0=t6_7jobs := by rfl
theorem t6_7all : t6_7jobs.all (Job.check tree)=true := by
  simp only [t6_7jobs,List.all_append,List.all_nil,t6_7part0,Bool.and_self]
theorem t6_7checked : Checked tree [0,1,6,7,7,7] := by
  refine ⟨plan6696,valid6696,t6_7choices,?_⟩
  exact check_of_frontier tree 0 t6_7root t6_7jobs t6_7frontier t6_7all
theorem t6_8choices : plan6697.choices=[0,1,6,10,7,7].map (options 6 4) := by rfl


theorem t6_8part0 : t6_8jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_8frontier : t6_8root.frontier 0=t6_8jobs := by rfl
theorem t6_8all : t6_8jobs.all (Job.check tree)=true := by
  simp only [t6_8jobs,List.all_append,List.all_nil,t6_8part0,Bool.and_self]
theorem t6_8checked : Checked tree [0,1,6,10,7,7] := by
  refine ⟨plan6697,valid6697,t6_8choices,?_⟩
  exact check_of_frontier tree 0 t6_8root t6_8jobs t6_8frontier t6_8all
theorem t6_9choices : plan6698.choices=[0,1,7,7,7,7].map (options 6 4) := by rfl


theorem t6_9part0 : t6_9jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_9frontier : t6_9root.frontier 0=t6_9jobs := by rfl
theorem t6_9all : t6_9jobs.all (Job.check tree)=true := by
  simp only [t6_9jobs,List.all_append,List.all_nil,t6_9part0,Bool.and_self]
theorem t6_9checked : Checked tree [0,1,7,7,7,7] := by
  refine ⟨plan6698,valid6698,t6_9choices,?_⟩
  exact check_of_frontier tree 0 t6_9root t6_9jobs t6_9frontier t6_9all
theorem t6_10choices : plan6699.choices=[0,1,9,7,7,7].map (options 6 4) := by rfl


theorem t6_10part0 : t6_10jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_10frontier : t6_10root.frontier 0=t6_10jobs := by rfl
theorem t6_10all : t6_10jobs.all (Job.check tree)=true := by
  simp only [t6_10jobs,List.all_append,List.all_nil,t6_10part0,Bool.and_self]
theorem t6_10checked : Checked tree [0,1,9,7,7,7] := by
  refine ⟨plan6699,valid6699,t6_10choices,?_⟩
  exact check_of_frontier tree 0 t6_10root t6_10jobs t6_10frontier t6_10all
theorem t6_11choices : plan6700.choices=[0,1,10,7,7,7].map (options 6 4) := by rfl


theorem t6_11part0 : t6_11jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_11frontier : t6_11root.frontier 0=t6_11jobs := by rfl
theorem t6_11all : t6_11jobs.all (Job.check tree)=true := by
  simp only [t6_11jobs,List.all_append,List.all_nil,t6_11part0,Bool.and_self]
theorem t6_11checked : Checked tree [0,1,10,7,7,7] := by
  refine ⟨plan6700,valid6700,t6_11choices,?_⟩
  exact check_of_frontier tree 0 t6_11root t6_11jobs t6_11frontier t6_11all
theorem t6_12choices : plan6701.choices=[0,1,10,10,7,7].map (options 6 4) := by rfl


theorem t6_12part0 : t6_12jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_12frontier : t6_12root.frontier 0=t6_12jobs := by rfl
theorem t6_12all : t6_12jobs.all (Job.check tree)=true := by
  simp only [t6_12jobs,List.all_append,List.all_nil,t6_12part0,Bool.and_self]
theorem t6_12checked : Checked tree [0,1,10,10,7,7] := by
  refine ⟨plan6701,valid6701,t6_12choices,?_⟩
  exact check_of_frontier tree 0 t6_12root t6_12jobs t6_12frontier t6_12all
theorem t6_13choices : plan6321.choices=[0,2,2,3,7,7].map (options 6 2) := by rfl


theorem t6_13part0 : t6_13jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_13frontier : t6_13root.frontier 0=t6_13jobs := by rfl
theorem t6_13all : t6_13jobs.all (Job.check tree)=true := by
  simp only [t6_13jobs,List.all_append,List.all_nil,t6_13part0,Bool.and_self]
theorem t6_13checked : Checked tree [0,2,2,3,7,7] := by
  refine ⟨plan6321,valid6321,t6_13choices,?_⟩
  exact check_of_frontier tree 0 t6_13root t6_13jobs t6_13frontier t6_13all
theorem t6_14choices : plan6438.choices=[0,2,2,6,7,7].map (options 6 3) := by rfl


theorem t6_14part0 : t6_14jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_14frontier : t6_14root.frontier 0=t6_14jobs := by rfl
theorem t6_14all : t6_14jobs.all (Job.check tree)=true := by
  simp only [t6_14jobs,List.all_append,List.all_nil,t6_14part0,Bool.and_self]
theorem t6_14checked : Checked tree [0,2,2,6,7,7] := by
  refine ⟨plan6438,valid6438,t6_14choices,?_⟩
  exact check_of_frontier tree 0 t6_14root t6_14jobs t6_14frontier t6_14all
theorem t6_15choices : plan6439.choices=[0,2,2,7,7,7].map (options 6 3) := by rfl


theorem t6_15part0 : t6_15jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_15frontier : t6_15root.frontier 0=t6_15jobs := by rfl
theorem t6_15all : t6_15jobs.all (Job.check tree)=true := by
  simp only [t6_15jobs,List.all_append,List.all_nil,t6_15part0,Bool.and_self]
theorem t6_15checked : Checked tree [0,2,2,7,7,7] := by
  refine ⟨plan6439,valid6439,t6_15choices,?_⟩
  exact check_of_frontier tree 0 t6_15root t6_15jobs t6_15frontier t6_15all
theorem t6_16choices : plan6440.choices=[0,2,2,10,7,7].map (options 6 3) := by rfl


theorem t6_16part0 : t6_16jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_16frontier : t6_16root.frontier 0=t6_16jobs := by rfl
theorem t6_16all : t6_16jobs.all (Job.check tree)=true := by
  simp only [t6_16jobs,List.all_append,List.all_nil,t6_16part0,Bool.and_self]
theorem t6_16checked : Checked tree [0,2,2,10,7,7] := by
  refine ⟨plan6440,valid6440,t6_16choices,?_⟩
  exact check_of_frontier tree 0 t6_16root t6_16jobs t6_16frontier t6_16all
theorem t6_17choices : plan6283.choices=[0,2,3,3,3,7].map (options 6 1) := by rfl


theorem t6_17part0 : t6_17jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_17frontier : t6_17root.frontier 0=t6_17jobs := by rfl
theorem t6_17all : t6_17jobs.all (Job.check tree)=true := by
  simp only [t6_17jobs,List.all_append,List.all_nil,t6_17part0,Bool.and_self]
theorem t6_17checked : Checked tree [0,2,3,3,3,7] := by
  refine ⟨plan6283,valid6283,t6_17choices,?_⟩
  exact check_of_frontier tree 0 t6_17root t6_17jobs t6_17frontier t6_17all
theorem t6_18choices : plan6322.choices=[0,2,3,3,6,7].map (options 6 2) := by rfl


theorem t6_18part0 : t6_18jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_18frontier : t6_18root.frontier 0=t6_18jobs := by rfl
theorem t6_18all : t6_18jobs.all (Job.check tree)=true := by
  simp only [t6_18jobs,List.all_append,List.all_nil,t6_18part0,Bool.and_self]
theorem t6_18checked : Checked tree [0,2,3,3,6,7] := by
  refine ⟨plan6322,valid6322,t6_18choices,?_⟩
  exact check_of_frontier tree 0 t6_18root t6_18jobs t6_18frontier t6_18all
theorem t6_19choices : plan6323.choices=[0,2,3,3,7,7].map (options 6 2) := by rfl


theorem t6_19part0 : t6_19jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_19frontier : t6_19root.frontier 0=t6_19jobs := by rfl
theorem t6_19all : t6_19jobs.all (Job.check tree)=true := by
  simp only [t6_19jobs,List.all_append,List.all_nil,t6_19part0,Bool.and_self]
theorem t6_19checked : Checked tree [0,2,3,3,7,7] := by
  refine ⟨plan6323,valid6323,t6_19choices,?_⟩
  exact check_of_frontier tree 0 t6_19root t6_19jobs t6_19frontier t6_19all
theorem t6_20choices : plan6324.choices=[0,2,3,3,10,7].map (options 6 2) := by rfl


theorem t6_20part0 : t6_20jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_20frontier : t6_20root.frontier 0=t6_20jobs := by rfl
theorem t6_20all : t6_20jobs.all (Job.check tree)=true := by
  simp only [t6_20jobs,List.all_append,List.all_nil,t6_20part0,Bool.and_self]
theorem t6_20checked : Checked tree [0,2,3,3,10,7] := by
  refine ⟨plan6324,valid6324,t6_20choices,?_⟩
  exact check_of_frontier tree 0 t6_20root t6_20jobs t6_20frontier t6_20all
theorem t6_21choices : plan6441.choices=[0,2,3,6,6,7].map (options 6 3) := by rfl


theorem t6_21part0 : t6_21jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_21frontier : t6_21root.frontier 0=t6_21jobs := by rfl
theorem t6_21all : t6_21jobs.all (Job.check tree)=true := by
  simp only [t6_21jobs,List.all_append,List.all_nil,t6_21part0,Bool.and_self]
theorem t6_21checked : Checked tree [0,2,3,6,6,7] := by
  refine ⟨plan6441,valid6441,t6_21choices,?_⟩
  exact check_of_frontier tree 0 t6_21root t6_21jobs t6_21frontier t6_21all
theorem t6_22choices : plan6442.choices=[0,2,3,6,7,7].map (options 6 3) := by rfl


theorem t6_22part0 : t6_22jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_22frontier : t6_22root.frontier 0=t6_22jobs := by rfl
theorem t6_22all : t6_22jobs.all (Job.check tree)=true := by
  simp only [t6_22jobs,List.all_append,List.all_nil,t6_22part0,Bool.and_self]
theorem t6_22checked : Checked tree [0,2,3,6,7,7] := by
  refine ⟨plan6442,valid6442,t6_22choices,?_⟩
  exact check_of_frontier tree 0 t6_22root t6_22jobs t6_22frontier t6_22all
theorem t6_23choices : plan6443.choices=[0,2,3,6,10,7].map (options 6 3) := by rfl


theorem t6_23part0 : t6_23jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_23frontier : t6_23root.frontier 0=t6_23jobs := by rfl
theorem t6_23all : t6_23jobs.all (Job.check tree)=true := by
  simp only [t6_23jobs,List.all_append,List.all_nil,t6_23part0,Bool.and_self]
theorem t6_23checked : Checked tree [0,2,3,6,10,7] := by
  refine ⟨plan6443,valid6443,t6_23choices,?_⟩
  exact check_of_frontier tree 0 t6_23root t6_23jobs t6_23frontier t6_23all
theorem t6_24choices : plan6444.choices=[0,2,3,7,7,7].map (options 6 3) := by rfl


theorem t6_24part0 : t6_24jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_24frontier : t6_24root.frontier 0=t6_24jobs := by rfl
theorem t6_24all : t6_24jobs.all (Job.check tree)=true := by
  simp only [t6_24jobs,List.all_append,List.all_nil,t6_24part0,Bool.and_self]
theorem t6_24checked : Checked tree [0,2,3,7,7,7] := by
  refine ⟨plan6444,valid6444,t6_24choices,?_⟩
  exact check_of_frontier tree 0 t6_24root t6_24jobs t6_24frontier t6_24all
theorem t6_25choices : plan6445.choices=[0,2,3,10,7,7].map (options 6 3) := by rfl


theorem t6_25part0 : t6_25jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_25frontier : t6_25root.frontier 0=t6_25jobs := by rfl
theorem t6_25all : t6_25jobs.all (Job.check tree)=true := by
  simp only [t6_25jobs,List.all_append,List.all_nil,t6_25part0,Bool.and_self]
theorem t6_25checked : Checked tree [0,2,3,10,7,7] := by
  refine ⟨plan6445,valid6445,t6_25choices,?_⟩
  exact check_of_frontier tree 0 t6_25root t6_25jobs t6_25frontier t6_25all
theorem t6_26choices : plan6446.choices=[0,2,3,10,10,7].map (options 6 3) := by rfl


theorem t6_26part0 : t6_26jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_26frontier : t6_26root.frontier 0=t6_26jobs := by rfl
theorem t6_26all : t6_26jobs.all (Job.check tree)=true := by
  simp only [t6_26jobs,List.all_append,List.all_nil,t6_26part0,Bool.and_self]
theorem t6_26checked : Checked tree [0,2,3,10,10,7] := by
  refine ⟨plan6446,valid6446,t6_26choices,?_⟩
  exact check_of_frontier tree 0 t6_26root t6_26jobs t6_26frontier t6_26all
theorem t6_27choices : plan6447.choices=[0,2,5,3,7,7].map (options 6 3) := by rfl


theorem t6_27part0 : t6_27jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_27frontier : t6_27root.frontier 0=t6_27jobs := by rfl
theorem t6_27all : t6_27jobs.all (Job.check tree)=true := by
  simp only [t6_27jobs,List.all_append,List.all_nil,t6_27part0,Bool.and_self]
theorem t6_27checked : Checked tree [0,2,5,3,7,7] := by
  refine ⟨plan6447,valid6447,t6_27choices,?_⟩
  exact check_of_frontier tree 0 t6_27root t6_27jobs t6_27frontier t6_27all
theorem t6_28choices : plan6702.choices=[0,2,5,6,7,7].map (options 6 4) := by rfl


theorem t6_28part0 : t6_28jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_28frontier : t6_28root.frontier 0=t6_28jobs := by rfl
theorem t6_28all : t6_28jobs.all (Job.check tree)=true := by
  simp only [t6_28jobs,List.all_append,List.all_nil,t6_28part0,Bool.and_self]
theorem t6_28checked : Checked tree [0,2,5,6,7,7] := by
  refine ⟨plan6702,valid6702,t6_28choices,?_⟩
  exact check_of_frontier tree 0 t6_28root t6_28jobs t6_28frontier t6_28all
theorem t6_29choices : plan6703.choices=[0,2,5,7,7,7].map (options 6 4) := by rfl


theorem t6_29part0 : t6_29jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_29frontier : t6_29root.frontier 0=t6_29jobs := by rfl
theorem t6_29all : t6_29jobs.all (Job.check tree)=true := by
  simp only [t6_29jobs,List.all_append,List.all_nil,t6_29part0,Bool.and_self]
theorem t6_29checked : Checked tree [0,2,5,7,7,7] := by
  refine ⟨plan6703,valid6703,t6_29choices,?_⟩
  exact check_of_frontier tree 0 t6_29root t6_29jobs t6_29frontier t6_29all
theorem t6_30choices : plan6704.choices=[0,2,5,10,7,7].map (options 6 4) := by rfl


theorem t6_30part0 : t6_30jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_30frontier : t6_30root.frontier 0=t6_30jobs := by rfl
theorem t6_30all : t6_30jobs.all (Job.check tree)=true := by
  simp only [t6_30jobs,List.all_append,List.all_nil,t6_30part0,Bool.and_self]
theorem t6_30checked : Checked tree [0,2,5,10,7,7] := by
  refine ⟨plan6704,valid6704,t6_30choices,?_⟩
  exact check_of_frontier tree 0 t6_30root t6_30jobs t6_30frontier t6_30all
theorem t6_31choices : plan6705.choices=[0,2,6,6,6,7].map (options 6 4) := by rfl


theorem t6_31part0 : t6_31jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_31frontier : t6_31root.frontier 0=t6_31jobs := by rfl
theorem t6_31all : t6_31jobs.all (Job.check tree)=true := by
  simp only [t6_31jobs,List.all_append,List.all_nil,t6_31part0,Bool.and_self]
theorem t6_31checked : Checked tree [0,2,6,6,6,7] := by
  refine ⟨plan6705,valid6705,t6_31choices,?_⟩
  exact check_of_frontier tree 0 t6_31root t6_31jobs t6_31frontier t6_31all
theorem t6_32choices : plan6706.choices=[0,2,6,6,7,7].map (options 6 4) := by rfl


theorem t6_32part0 : t6_32jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_32frontier : t6_32root.frontier 0=t6_32jobs := by rfl
theorem t6_32all : t6_32jobs.all (Job.check tree)=true := by
  simp only [t6_32jobs,List.all_append,List.all_nil,t6_32part0,Bool.and_self]
theorem t6_32checked : Checked tree [0,2,6,6,7,7] := by
  refine ⟨plan6706,valid6706,t6_32choices,?_⟩
  exact check_of_frontier tree 0 t6_32root t6_32jobs t6_32frontier t6_32all
theorem t6_33choices : plan6707.choices=[0,2,6,6,10,7].map (options 6 4) := by rfl


theorem t6_33part0 : t6_33jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_33frontier : t6_33root.frontier 0=t6_33jobs := by rfl
theorem t6_33all : t6_33jobs.all (Job.check tree)=true := by
  simp only [t6_33jobs,List.all_append,List.all_nil,t6_33part0,Bool.and_self]
theorem t6_33checked : Checked tree [0,2,6,6,10,7] := by
  refine ⟨plan6707,valid6707,t6_33choices,?_⟩
  exact check_of_frontier tree 0 t6_33root t6_33jobs t6_33frontier t6_33all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks047 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1653checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1654checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1655checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1656checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1657checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1658checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1659checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1642checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1660checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1661checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1662checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1663checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1664checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1665checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1666checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1667checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1668checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1669checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1643checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1670checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1671checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1672checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1673checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1674checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1675checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1676checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1677checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1678checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1679checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1644checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1680checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1681checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1682checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1683checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_0checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_2checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_3checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_4checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_5checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_6checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_7checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_8checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_9checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_10checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_11checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1645checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_12checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_13checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_14checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_15checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_16checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_17checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_18checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_19checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_20checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_21checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_22checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1646checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_23checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_24checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_25checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_26checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_27checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_28checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_29checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_30checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_31checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_32checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1647checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_33checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1648checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1649checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1650checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1651checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1652checked⟩
