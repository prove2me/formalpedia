-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks048
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:21:55.3724+00:00
-- url     : https://prove2.me/submissions/a04d3a04-eb45-486d-8220-5aa60e6dfe82

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks048
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks048
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
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









































theorem valid117 : plan117.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid119 : plan119.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid120 : plan120.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid121 : plan121.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid123 : plan123.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid125 : plan125.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid133 : plan133.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid134 : plan134.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid135 : plan135.Valid := valid_step _ _ _ valid0 (by decide +kernel)


















































































































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

theorem valid577 : plan577.Valid := valid_step _ _ _ valid135 (by decide +kernel)

theorem valid578 : plan578.Valid := valid_step _ _ _ valid134 (by decide +kernel)

theorem valid579 : plan579.Valid := valid_step _ _ _ valid134 (by decide +kernel)

theorem valid580 : plan580.Valid := valid_step _ _ _ valid135 (by decide +kernel)
























































































































































































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























































































































theorem valid540 : plan540.Valid := valid_step _ _ _ valid117 (by decide +kernel)



theorem valid542 : plan542.Valid := valid_step _ _ _ valid119 (by decide +kernel)

theorem valid543 : plan543.Valid := valid_step _ _ _ valid120 (by decide +kernel)

theorem valid544 : plan544.Valid := valid_step _ _ _ valid121 (by decide +kernel)





theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)



theorem valid549 : plan549.Valid := valid_step _ _ _ valid123 (by decide +kernel)

theorem valid550 : plan550.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid551 : plan551.Valid := valid_step _ _ _ valid125 (by decide +kernel)

theorem valid552 : plan552.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid553 : plan553.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid554 : plan554.Valid := valid_step _ _ _ valid125 (by decide +kernel)









theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)

theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)

theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid573 : plan573.Valid := valid_step _ _ _ valid132 (by decide +kernel)



theorem valid575 : plan575.Valid := valid_step _ _ _ valid133 (by decide +kernel)

theorem valid576 : plan576.Valid := valid_step _ _ _ valid134 (by decide +kernel)
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



































































































































theorem valid1506 : plan1506.Valid := valid_step _ _ _ valid540 (by decide +kernel)





theorem valid1509 : plan1509.Valid := valid_step _ _ _ valid542 (by decide +kernel)

theorem valid1510 : plan1510.Valid := valid_step _ _ _ valid543 (by decide +kernel)

theorem valid1511 : plan1511.Valid := valid_step _ _ _ valid544 (by decide +kernel)











theorem valid1517 : plan1517.Valid := valid_step _ _ _ valid547 (by decide +kernel)



theorem valid1519 : plan1519.Valid := valid_step _ _ _ valid549 (by decide +kernel)

theorem valid1520 : plan1520.Valid := valid_step _ _ _ valid550 (by decide +kernel)

theorem valid1521 : plan1521.Valid := valid_step _ _ _ valid551 (by decide +kernel)

theorem valid1522 : plan1522.Valid := valid_step _ _ _ valid552 (by decide +kernel)

theorem valid1523 : plan1523.Valid := valid_step _ _ _ valid553 (by decide +kernel)

theorem valid1524 : plan1524.Valid := valid_step _ _ _ valid554 (by decide +kernel)

















theorem valid1533 : plan1533.Valid := valid_step _ _ _ valid560 (by decide +kernel)



theorem valid1535 : plan1535.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1536 : plan1536.Valid := valid_step _ _ _ valid563 (by decide +kernel)
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

















































































































































theorem valid3241 : plan3241.Valid := valid_step _ _ _ valid1506 (by decide +kernel)











theorem valid3247 : plan3247.Valid := valid_step _ _ _ valid1509 (by decide +kernel)

theorem valid3248 : plan3248.Valid := valid_step _ _ _ valid1510 (by decide +kernel)

theorem valid3249 : plan3249.Valid := valid_step _ _ _ valid1511 (by decide +kernel)






























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











theorem valid1542 : plan1542.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1543 : plan1543.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1544 : plan1544.Valid := valid_step _ _ _ valid561 (by decide +kernel)

theorem valid1545 : plan1545.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1546 : plan1546.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1547 : plan1547.Valid := valid_step _ _ _ valid564 (by decide +kernel)

theorem valid1548 : plan1548.Valid := valid_step _ _ _ valid562 (by decide +kernel)









theorem valid1553 : plan1553.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1554 : plan1554.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1555 : plan1555.Valid := valid_step _ _ _ valid564 (by decide +kernel)













theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)













theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)

theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)









theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1582 : plan1582.Valid := valid_step _ _ _ valid573 (by decide +kernel)





















theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)









theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1606 : plan1606.Valid := valid_step _ _ _ valid580 (by decide +kernel)




















































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



theorem valid3266 : plan3266.Valid := valid_step _ _ _ valid1517 (by decide +kernel)



theorem valid3268 : plan3268.Valid := valid_step _ _ _ valid1519 (by decide +kernel)

theorem valid3269 : plan3269.Valid := valid_step _ _ _ valid1520 (by decide +kernel)

theorem valid3270 : plan3270.Valid := valid_step _ _ _ valid1521 (by decide +kernel)

theorem valid3271 : plan3271.Valid := valid_step _ _ _ valid1522 (by decide +kernel)

theorem valid3272 : plan3272.Valid := valid_step _ _ _ valid1523 (by decide +kernel)

theorem valid3273 : plan3273.Valid := valid_step _ _ _ valid1524 (by decide +kernel)



































































theorem valid3307 : plan3307.Valid := valid_step _ _ _ valid1533 (by decide +kernel)



theorem valid3309 : plan3309.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3310 : plan3310.Valid := valid_step _ _ _ valid1536 (by decide +kernel)



theorem valid3312 : plan3312.Valid := valid_step _ _ _ valid1542 (by decide +kernel)

theorem valid3313 : plan3313.Valid := valid_step _ _ _ valid1543 (by decide +kernel)

theorem valid3314 : plan3314.Valid := valid_step _ _ _ valid1544 (by decide +kernel)

theorem valid3315 : plan3315.Valid := valid_step _ _ _ valid1545 (by decide +kernel)

theorem valid3316 : plan3316.Valid := valid_step _ _ _ valid1546 (by decide +kernel)

theorem valid3317 : plan3317.Valid := valid_step _ _ _ valid1547 (by decide +kernel)

theorem valid3318 : plan3318.Valid := valid_step _ _ _ valid1548 (by decide +kernel)

theorem valid3319 : plan3319.Valid := valid_step _ _ _ valid1553 (by decide +kernel)

theorem valid3320 : plan3320.Valid := valid_step _ _ _ valid1554 (by decide +kernel)

theorem valid3321 : plan3321.Valid := valid_step _ _ _ valid1555 (by decide +kernel)







































theorem valid3341 : plan3341.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

















theorem valid3350 : plan3350.Valid := valid_step _ _ _ valid1575 (by decide +kernel)




















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































































































































theorem valid5344 : plan5344.Valid := valid_step _ _ _ valid3241 (by decide +kernel)

























theorem valid5357 : plan5357.Valid := valid_step _ _ _ valid3247 (by decide +kernel)

theorem valid5358 : plan5358.Valid := valid_step _ _ _ valid3248 (by decide +kernel)

theorem valid5359 : plan5359.Valid := valid_step _ _ _ valid3249 (by decide +kernel)


































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







































theorem valid5396 : plan5396.Valid := valid_step _ _ _ valid3268 (by decide +kernel)

theorem valid5397 : plan5397.Valid := valid_step _ _ _ valid3269 (by decide +kernel)

theorem valid5398 : plan5398.Valid := valid_step _ _ _ valid3270 (by decide +kernel)

theorem valid5399 : plan5399.Valid := valid_step _ _ _ valid3271 (by decide +kernel)

theorem valid5400 : plan5400.Valid := valid_step _ _ _ valid3272 (by decide +kernel)

theorem valid5401 : plan5401.Valid := valid_step _ _ _ valid3273 (by decide +kernel)







theorem valid5405 : plan5405.Valid := valid_step _ _ _ valid3266 (by decide +kernel)













theorem valid5412 : plan5412.Valid := valid_step _ _ _ valid3266 (by decide +kernel)
























































































































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







































































theorem valid6276 : plan6276.Valid := valid_step _ _ _ valid5344 (by decide +kernel)















theorem valid6284 : plan6284.Valid := valid_step _ _ _ valid5357 (by decide +kernel)

theorem valid6285 : plan6285.Valid := valid_step _ _ _ valid5358 (by decide +kernel)

theorem valid6286 : plan6286.Valid := valid_step _ _ _ valid5359 (by decide +kernel)













































































theorem valid6325 : plan6325.Valid := valid_step _ _ _ valid5396 (by decide +kernel)

theorem valid6326 : plan6326.Valid := valid_step _ _ _ valid5397 (by decide +kernel)

theorem valid6327 : plan6327.Valid := valid_step _ _ _ valid5398 (by decide +kernel)

theorem valid6328 : plan6328.Valid := valid_step _ _ _ valid5399 (by decide +kernel)

theorem valid6329 : plan6329.Valid := valid_step _ _ _ valid5400 (by decide +kernel)

theorem valid6330 : plan6330.Valid := valid_step _ _ _ valid5401 (by decide +kernel)

theorem valid6331 : plan6331.Valid := valid_step _ _ _ valid5405 (by decide +kernel)

theorem valid6332 : plan6332.Valid := valid_step _ _ _ valid5412 (by decide +kernel)








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

theorem valid3361 : plan3361.Valid := valid_step _ _ _ valid1570 (by decide +kernel)



theorem valid3363 : plan3363.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3364 : plan3364.Valid := valid_step _ _ _ valid1573 (by decide +kernel)



theorem valid3366 : plan3366.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3367 : plan3367.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3368 : plan3368.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

















theorem valid3377 : plan3377.Valid := valid_step _ _ _ valid1562 (by decide +kernel)









































theorem valid3398 : plan3398.Valid := valid_step _ _ _ valid1569 (by decide +kernel)

theorem valid3399 : plan3399.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3400 : plan3400.Valid := valid_step _ _ _ valid1571 (by decide +kernel)

theorem valid3401 : plan3401.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3402 : plan3402.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3403 : plan3403.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3404 : plan3404.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3405 : plan3405.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3406 : plan3406.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3407 : plan3407.Valid := valid_step _ _ _ valid1582 (by decide +kernel)

theorem valid3408 : plan3408.Valid := valid_step _ _ _ valid1575 (by decide +kernel)















theorem valid3416 : plan3416.Valid := valid_step _ _ _ valid1562 (by decide +kernel)











theorem valid3422 : plan3422.Valid := valid_step _ _ _ valid1572 (by decide +kernel)





theorem valid3425 : plan3425.Valid := valid_step _ _ _ valid1575 (by decide +kernel)









theorem valid3430 : plan3430.Valid := valid_step _ _ _ valid1580 (by decide +kernel)





theorem valid3433 : plan3433.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3434 : plan3434.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3435 : plan3435.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3436 : plan3436.Valid := valid_step _ _ _ valid1582 (by decide +kernel)








































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







theorem valid5476 : plan5476.Valid := valid_step _ _ _ valid3341 (by decide +kernel)



















theorem valid5486 : plan5486.Valid := valid_step _ _ _ valid3312 (by decide +kernel)

theorem valid5487 : plan5487.Valid := valid_step _ _ _ valid3313 (by decide +kernel)

theorem valid5488 : plan5488.Valid := valid_step _ _ _ valid3314 (by decide +kernel)

theorem valid5489 : plan5489.Valid := valid_step _ _ _ valid3315 (by decide +kernel)

theorem valid5490 : plan5490.Valid := valid_step _ _ _ valid3316 (by decide +kernel)

theorem valid5491 : plan5491.Valid := valid_step _ _ _ valid3317 (by decide +kernel)

theorem valid5492 : plan5492.Valid := valid_step _ _ _ valid3318 (by decide +kernel)

theorem valid5493 : plan5493.Valid := valid_step _ _ _ valid3319 (by decide +kernel)

theorem valid5494 : plan5494.Valid := valid_step _ _ _ valid3320 (by decide +kernel)

theorem valid5495 : plan5495.Valid := valid_step _ _ _ valid3321 (by decide +kernel)







theorem valid5499 : plan5499.Valid := valid_step _ _ _ valid3309 (by decide +kernel)











theorem valid5505 : plan5505.Valid := valid_step _ _ _ valid3307 (by decide +kernel)



theorem valid5507 : plan5507.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5508 : plan5508.Valid := valid_step _ _ _ valid3310 (by decide +kernel)

























theorem valid5521 : plan5521.Valid := valid_step _ _ _ valid3309 (by decide +kernel)











theorem valid5527 : plan5527.Valid := valid_step _ _ _ valid3307 (by decide +kernel)



theorem valid5529 : plan5529.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5530 : plan5530.Valid := valid_step _ _ _ valid3310 (by decide +kernel)












































































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































theorem valid6448 : plan6448.Valid := valid_step _ _ _ valid5476 (by decide +kernel)

theorem valid6449 : plan6449.Valid := valid_step _ _ _ valid5486 (by decide +kernel)

theorem valid6450 : plan6450.Valid := valid_step _ _ _ valid5487 (by decide +kernel)

theorem valid6451 : plan6451.Valid := valid_step _ _ _ valid5488 (by decide +kernel)

theorem valid6452 : plan6452.Valid := valid_step _ _ _ valid5489 (by decide +kernel)

theorem valid6453 : plan6453.Valid := valid_step _ _ _ valid5490 (by decide +kernel)

theorem valid6454 : plan6454.Valid := valid_step _ _ _ valid5491 (by decide +kernel)

theorem valid6455 : plan6455.Valid := valid_step _ _ _ valid5492 (by decide +kernel)

theorem valid6456 : plan6456.Valid := valid_step _ _ _ valid5493 (by decide +kernel)

theorem valid6457 : plan6457.Valid := valid_step _ _ _ valid5494 (by decide +kernel)

theorem valid6458 : plan6458.Valid := valid_step _ _ _ valid5495 (by decide +kernel)

theorem valid6459 : plan6459.Valid := valid_step _ _ _ valid5499 (by decide +kernel)

theorem valid6460 : plan6460.Valid := valid_step _ _ _ valid5505 (by decide +kernel)

theorem valid6461 : plan6461.Valid := valid_step _ _ _ valid5507 (by decide +kernel)

theorem valid6462 : plan6462.Valid := valid_step _ _ _ valid5508 (by decide +kernel)

theorem valid6463 : plan6463.Valid := valid_step _ _ _ valid5521 (by decide +kernel)

theorem valid6464 : plan6464.Valid := valid_step _ _ _ valid5527 (by decide +kernel)

theorem valid6465 : plan6465.Valid := valid_step _ _ _ valid5529 (by decide +kernel)

theorem valid6466 : plan6466.Valid := valid_step _ _ _ valid5530 (by decide +kernel)




























































































































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

























































theorem valid5597 : plan5597.Valid := valid_step _ _ _ valid3404 (by decide +kernel)

theorem valid5598 : plan5598.Valid := valid_step _ _ _ valid3405 (by decide +kernel)

theorem valid5599 : plan5599.Valid := valid_step _ _ _ valid3406 (by decide +kernel)



theorem valid5601 : plan5601.Valid := valid_step _ _ _ valid3408 (by decide +kernel)













theorem valid5608 : plan5608.Valid := valid_step _ _ _ valid3422 (by decide +kernel)





theorem valid5611 : plan5611.Valid := valid_step _ _ _ valid3425 (by decide +kernel)







theorem valid5615 : plan5615.Valid := valid_step _ _ _ valid3430 (by decide +kernel)





theorem valid5618 : plan5618.Valid := valid_step _ _ _ valid3433 (by decide +kernel)

theorem valid5619 : plan5619.Valid := valid_step _ _ _ valid3434 (by decide +kernel)

theorem valid5620 : plan5620.Valid := valid_step _ _ _ valid3435 (by decide +kernel)























theorem valid5632 : plan5632.Valid := valid_step _ _ _ valid3398 (by decide +kernel)

theorem valid5633 : plan5633.Valid := valid_step _ _ _ valid3399 (by decide +kernel)

theorem valid5634 : plan5634.Valid := valid_step _ _ _ valid3400 (by decide +kernel)

theorem valid5635 : plan5635.Valid := valid_step _ _ _ valid3401 (by decide +kernel)

theorem valid5636 : plan5636.Valid := valid_step _ _ _ valid3402 (by decide +kernel)

theorem valid5637 : plan5637.Valid := valid_step _ _ _ valid3403 (by decide +kernel)

theorem valid5638 : plan5638.Valid := valid_step _ _ _ valid3404 (by decide +kernel)

theorem valid5639 : plan5639.Valid := valid_step _ _ _ valid3405 (by decide +kernel)

theorem valid5640 : plan5640.Valid := valid_step _ _ _ valid3406 (by decide +kernel)

theorem valid5641 : plan5641.Valid := valid_step _ _ _ valid3407 (by decide +kernel)

theorem valid5642 : plan5642.Valid := valid_step _ _ _ valid3408 (by decide +kernel)

theorem valid5643 : plan5643.Valid := valid_step _ _ _ valid3433 (by decide +kernel)

theorem valid5644 : plan5644.Valid := valid_step _ _ _ valid3434 (by decide +kernel)

theorem valid5645 : plan5645.Valid := valid_step _ _ _ valid3435 (by decide +kernel)

theorem valid5646 : plan5646.Valid := valid_step _ _ _ valid3436 (by decide +kernel)





theorem valid5649 : plan5649.Valid := valid_step _ _ _ valid3350 (by decide +kernel)











theorem valid5655 : plan5655.Valid := valid_step _ _ _ valid3363 (by decide +kernel)



theorem valid5657 : plan5657.Valid := valid_step _ _ _ valid3366 (by decide +kernel)

theorem valid5658 : plan5658.Valid := valid_step _ _ _ valid3367 (by decide +kernel)












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







































































































































































theorem valid6708 : plan6708.Valid := valid_step _ _ _ valid5597 (by decide +kernel)

theorem valid6709 : plan6709.Valid := valid_step _ _ _ valid5598 (by decide +kernel)

theorem valid6710 : plan6710.Valid := valid_step _ _ _ valid5599 (by decide +kernel)

theorem valid6711 : plan6711.Valid := valid_step _ _ _ valid5601 (by decide +kernel)

theorem valid6712 : plan6712.Valid := valid_step _ _ _ valid5608 (by decide +kernel)

theorem valid6713 : plan6713.Valid := valid_step _ _ _ valid5611 (by decide +kernel)

theorem valid6714 : plan6714.Valid := valid_step _ _ _ valid5615 (by decide +kernel)

theorem valid6715 : plan6715.Valid := valid_step _ _ _ valid5618 (by decide +kernel)

theorem valid6716 : plan6716.Valid := valid_step _ _ _ valid5619 (by decide +kernel)

theorem valid6717 : plan6717.Valid := valid_step _ _ _ valid5620 (by decide +kernel)

theorem valid6718 : plan6718.Valid := valid_step _ _ _ valid5632 (by decide +kernel)

theorem valid6719 : plan6719.Valid := valid_step _ _ _ valid5633 (by decide +kernel)

theorem valid6720 : plan6720.Valid := valid_step _ _ _ valid5634 (by decide +kernel)
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















theorem valid3464 : plan3464.Valid := valid_step _ _ _ valid1596 (by decide +kernel)





theorem valid3467 : plan3467.Valid := valid_step _ _ _ valid1599 (by decide +kernel)









theorem valid3472 : plan3472.Valid := valid_step _ _ _ valid1604 (by decide +kernel)





theorem valid3475 : plan3475.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3477 : plan3477.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)





















theorem valid3496 : plan3496.Valid := valid_step _ _ _ valid1596 (by decide +kernel)





theorem valid3499 : plan3499.Valid := valid_step _ _ _ valid1599 (by decide +kernel)









theorem valid3504 : plan3504.Valid := valid_step _ _ _ valid1604 (by decide +kernel)





theorem valid3507 : plan3507.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3508 : plan3508.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3509 : plan3509.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3510 : plan3510.Valid := valid_step _ _ _ valid1606 (by decide +kernel)




















































































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









theorem valid5669 : plan5669.Valid := valid_step _ _ _ valid3361 (by decide +kernel)



theorem valid5671 : plan5671.Valid := valid_step _ _ _ valid3363 (by decide +kernel)

theorem valid5672 : plan5672.Valid := valid_step _ _ _ valid3364 (by decide +kernel)



theorem valid5674 : plan5674.Valid := valid_step _ _ _ valid3366 (by decide +kernel)

theorem valid5675 : plan5675.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5676 : plan5676.Valid := valid_step _ _ _ valid3368 (by decide +kernel)















theorem valid5684 : plan5684.Valid := valid_step _ _ _ valid3377 (by decide +kernel)





















theorem valid5695 : plan5695.Valid := valid_step _ _ _ valid3416 (by decide +kernel)











theorem valid5701 : plan5701.Valid := valid_step _ _ _ valid3350 (by decide +kernel)











theorem valid5707 : plan5707.Valid := valid_step _ _ _ valid3363 (by decide +kernel)



theorem valid5709 : plan5709.Valid := valid_step _ _ _ valid3366 (by decide +kernel)

theorem valid5710 : plan5710.Valid := valid_step _ _ _ valid3367 (by decide +kernel)





















theorem valid5721 : plan5721.Valid := valid_step _ _ _ valid3361 (by decide +kernel)














































































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

theorem valid6721 : plan6721.Valid := valid_step _ _ _ valid5635 (by decide +kernel)

theorem valid6722 : plan6722.Valid := valid_step _ _ _ valid5636 (by decide +kernel)

theorem valid6723 : plan6723.Valid := valid_step _ _ _ valid5637 (by decide +kernel)

theorem valid6724 : plan6724.Valid := valid_step _ _ _ valid5638 (by decide +kernel)

theorem valid6725 : plan6725.Valid := valid_step _ _ _ valid5639 (by decide +kernel)

theorem valid6726 : plan6726.Valid := valid_step _ _ _ valid5640 (by decide +kernel)

theorem valid6727 : plan6727.Valid := valid_step _ _ _ valid5641 (by decide +kernel)

theorem valid6728 : plan6728.Valid := valid_step _ _ _ valid5642 (by decide +kernel)

theorem valid6729 : plan6729.Valid := valid_step _ _ _ valid5643 (by decide +kernel)

theorem valid6730 : plan6730.Valid := valid_step _ _ _ valid5644 (by decide +kernel)

theorem valid6731 : plan6731.Valid := valid_step _ _ _ valid5645 (by decide +kernel)

theorem valid6732 : plan6732.Valid := valid_step _ _ _ valid5646 (by decide +kernel)

theorem valid6733 : plan6733.Valid := valid_step _ _ _ valid5649 (by decide +kernel)

theorem valid6734 : plan6734.Valid := valid_step _ _ _ valid5655 (by decide +kernel)

theorem valid6735 : plan6735.Valid := valid_step _ _ _ valid5657 (by decide +kernel)

theorem valid6736 : plan6736.Valid := valid_step _ _ _ valid5658 (by decide +kernel)

theorem valid6737 : plan6737.Valid := valid_step _ _ _ valid5669 (by decide +kernel)

theorem valid6738 : plan6738.Valid := valid_step _ _ _ valid5671 (by decide +kernel)

theorem valid6739 : plan6739.Valid := valid_step _ _ _ valid5672 (by decide +kernel)

theorem valid6740 : plan6740.Valid := valid_step _ _ _ valid5674 (by decide +kernel)

theorem valid6741 : plan6741.Valid := valid_step _ _ _ valid5675 (by decide +kernel)

theorem valid6742 : plan6742.Valid := valid_step _ _ _ valid5676 (by decide +kernel)

theorem valid6743 : plan6743.Valid := valid_step _ _ _ valid5684 (by decide +kernel)

theorem valid6744 : plan6744.Valid := valid_step _ _ _ valid5695 (by decide +kernel)

theorem valid6745 : plan6745.Valid := valid_step _ _ _ valid5701 (by decide +kernel)

theorem valid6746 : plan6746.Valid := valid_step _ _ _ valid5707 (by decide +kernel)

theorem valid6747 : plan6747.Valid := valid_step _ _ _ valid5709 (by decide +kernel)

theorem valid6748 : plan6748.Valid := valid_step _ _ _ valid5710 (by decide +kernel)

theorem valid6749 : plan6749.Valid := valid_step _ _ _ valid5721 (by decide +kernel)






































































































































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









































































theorem valid5797 : plan5797.Valid := valid_step _ _ _ valid3467 (by decide +kernel)





theorem valid5800 : plan5800.Valid := valid_step _ _ _ valid3478 (by decide +kernel)



theorem valid5802 : plan5802.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5803 : plan5803.Valid := valid_step _ _ _ valid3482 (by decide +kernel)



theorem valid5805 : plan5805.Valid := valid_step _ _ _ valid3485 (by decide +kernel)







theorem valid5809 : plan5809.Valid := valid_step _ _ _ valid3499 (by decide +kernel)



theorem valid5811 : plan5811.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5812 : plan5812.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

















































theorem valid5837 : plan5837.Valid := valid_step _ _ _ valid3464 (by decide +kernel)





theorem valid5840 : plan5840.Valid := valid_step _ _ _ valid3467 (by decide +kernel)









theorem valid5845 : plan5845.Valid := valid_step _ _ _ valid3472 (by decide +kernel)







theorem valid5849 : plan5849.Valid := valid_step _ _ _ valid3476 (by decide +kernel)



theorem valid5851 : plan5851.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5852 : plan5852.Valid := valid_step _ _ _ valid3479 (by decide +kernel)



theorem valid5854 : plan5854.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5855 : plan5855.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5856 : plan5856.Valid := valid_step _ _ _ valid3483 (by decide +kernel)
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



theorem valid5858 : plan5858.Valid := valid_step _ _ _ valid3485 (by decide +kernel)



















theorem valid5868 : plan5868.Valid := valid_step _ _ _ valid3496 (by decide +kernel)





theorem valid5871 : plan5871.Valid := valid_step _ _ _ valid3499 (by decide +kernel)









theorem valid5876 : plan5876.Valid := valid_step _ _ _ valid3504 (by decide +kernel)





theorem valid5879 : plan5879.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5880 : plan5880.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5881 : plan5881.Valid := valid_step _ _ _ valid3509 (by decide +kernel)



theorem valid5883 : plan5883.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5884 : plan5884.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5885 : plan5885.Valid := valid_step _ _ _ valid3477 (by decide +kernel)

theorem valid5886 : plan5886.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5887 : plan5887.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5888 : plan5888.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5889 : plan5889.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5890 : plan5890.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5891 : plan5891.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5892 : plan5892.Valid := valid_step _ _ _ valid3484 (by decide +kernel)

theorem valid5893 : plan5893.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5894 : plan5894.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5895 : plan5895.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5896 : plan5896.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5897 : plan5897.Valid := valid_step _ _ _ valid3510 (by decide +kernel)

theorem valid5898 : plan5898.Valid := valid_step _ _ _ valid3485 (by decide +kernel)























theorem valid5910 : plan5910.Valid := valid_step _ _ _ valid3467 (by decide +kernel)





theorem valid5913 : plan5913.Valid := valid_step _ _ _ valid3478 (by decide +kernel)



theorem valid5915 : plan5915.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5916 : plan5916.Valid := valid_step _ _ _ valid3482 (by decide +kernel)



theorem valid5918 : plan5918.Valid := valid_step _ _ _ valid3485 (by decide +kernel)







theorem valid5922 : plan5922.Valid := valid_step _ _ _ valid3499 (by decide +kernel)



theorem valid5924 : plan5924.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5925 : plan5925.Valid := valid_step _ _ _ valid3508 (by decide +kernel)






















































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



















































































theorem valid7146 : plan7146.Valid := valid_step _ _ _ valid5797 (by decide +kernel)

theorem valid7147 : plan7147.Valid := valid_step _ _ _ valid5800 (by decide +kernel)

theorem valid7148 : plan7148.Valid := valid_step _ _ _ valid5802 (by decide +kernel)

theorem valid7149 : plan7149.Valid := valid_step _ _ _ valid5803 (by decide +kernel)

theorem valid7150 : plan7150.Valid := valid_step _ _ _ valid5805 (by decide +kernel)

theorem valid7151 : plan7151.Valid := valid_step _ _ _ valid5809 (by decide +kernel)

theorem valid7152 : plan7152.Valid := valid_step _ _ _ valid5811 (by decide +kernel)

theorem valid7153 : plan7153.Valid := valid_step _ _ _ valid5812 (by decide +kernel)

theorem valid7154 : plan7154.Valid := valid_step _ _ _ valid5837 (by decide +kernel)

theorem valid7155 : plan7155.Valid := valid_step _ _ _ valid5840 (by decide +kernel)

theorem valid7156 : plan7156.Valid := valid_step _ _ _ valid5845 (by decide +kernel)

theorem valid7157 : plan7157.Valid := valid_step _ _ _ valid5849 (by decide +kernel)

theorem valid7158 : plan7158.Valid := valid_step _ _ _ valid5851 (by decide +kernel)

theorem valid7159 : plan7159.Valid := valid_step _ _ _ valid5852 (by decide +kernel)

theorem valid7160 : plan7160.Valid := valid_step _ _ _ valid5854 (by decide +kernel)

theorem valid7161 : plan7161.Valid := valid_step _ _ _ valid5855 (by decide +kernel)

theorem valid7162 : plan7162.Valid := valid_step _ _ _ valid5856 (by decide +kernel)

theorem valid7163 : plan7163.Valid := valid_step _ _ _ valid5858 (by decide +kernel)

theorem valid7164 : plan7164.Valid := valid_step _ _ _ valid5868 (by decide +kernel)

theorem valid7165 : plan7165.Valid := valid_step _ _ _ valid5871 (by decide +kernel)

theorem valid7166 : plan7166.Valid := valid_step _ _ _ valid5876 (by decide +kernel)

theorem valid7167 : plan7167.Valid := valid_step _ _ _ valid5879 (by decide +kernel)

theorem valid7168 : plan7168.Valid := valid_step _ _ _ valid5880 (by decide +kernel)

theorem valid7169 : plan7169.Valid := valid_step _ _ _ valid5881 (by decide +kernel)

theorem valid7170 : plan7170.Valid := valid_step _ _ _ valid5883 (by decide +kernel)

theorem valid7171 : plan7171.Valid := valid_step _ _ _ valid5884 (by decide +kernel)

theorem valid7172 : plan7172.Valid := valid_step _ _ _ valid5885 (by decide +kernel)

theorem valid7173 : plan7173.Valid := valid_step _ _ _ valid5886 (by decide +kernel)

theorem valid7174 : plan7174.Valid := valid_step _ _ _ valid5887 (by decide +kernel)

theorem valid7175 : plan7175.Valid := valid_step _ _ _ valid5888 (by decide +kernel)

theorem valid7176 : plan7176.Valid := valid_step _ _ _ valid5889 (by decide +kernel)

theorem valid7177 : plan7177.Valid := valid_step _ _ _ valid5890 (by decide +kernel)

theorem valid7178 : plan7178.Valid := valid_step _ _ _ valid5891 (by decide +kernel)

theorem valid7179 : plan7179.Valid := valid_step _ _ _ valid5892 (by decide +kernel)

theorem valid7180 : plan7180.Valid := valid_step _ _ _ valid5893 (by decide +kernel)

theorem valid7181 : plan7181.Valid := valid_step _ _ _ valid5894 (by decide +kernel)

theorem valid7182 : plan7182.Valid := valid_step _ _ _ valid5895 (by decide +kernel)

theorem valid7183 : plan7183.Valid := valid_step _ _ _ valid5896 (by decide +kernel)

theorem valid7184 : plan7184.Valid := valid_step _ _ _ valid5897 (by decide +kernel)

theorem valid7185 : plan7185.Valid := valid_step _ _ _ valid5898 (by decide +kernel)

theorem valid7186 : plan7186.Valid := valid_step _ _ _ valid5910 (by decide +kernel)

theorem valid7187 : plan7187.Valid := valid_step _ _ _ valid5913 (by decide +kernel)

theorem valid7188 : plan7188.Valid := valid_step _ _ _ valid5915 (by decide +kernel)

theorem valid7189 : plan7189.Valid := valid_step _ _ _ valid5916 (by decide +kernel)

theorem valid7190 : plan7190.Valid := valid_step _ _ _ valid5918 (by decide +kernel)

theorem valid7191 : plan7191.Valid := valid_step _ _ _ valid5922 (by decide +kernel)

theorem valid7192 : plan7192.Valid := valid_step _ _ _ valid5924 (by decide +kernel)

theorem valid7193 : plan7193.Valid := valid_step _ _ _ valid5925 (by decide +kernel)














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
theorem t6_34choices : plan6708.choices=[0,2,6,7,7,7].map (options 6 4) := by rfl


theorem t6_34part0 : t6_34jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_34frontier : t6_34root.frontier 0=t6_34jobs := by rfl
theorem t6_34all : t6_34jobs.all (Job.check tree)=true := by
  simp only [t6_34jobs,List.all_append,List.all_nil,t6_34part0,Bool.and_self]
theorem t6_34checked : Checked tree [0,2,6,7,7,7] := by
  refine ⟨plan6708,valid6708,t6_34choices,?_⟩
  exact check_of_frontier tree 0 t6_34root t6_34jobs t6_34frontier t6_34all
theorem t6_35choices : plan6709.choices=[0,2,6,10,7,7].map (options 6 4) := by rfl


theorem t6_35part0 : t6_35jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_35frontier : t6_35root.frontier 0=t6_35jobs := by rfl
theorem t6_35all : t6_35jobs.all (Job.check tree)=true := by
  simp only [t6_35jobs,List.all_append,List.all_nil,t6_35part0,Bool.and_self]
theorem t6_35checked : Checked tree [0,2,6,10,7,7] := by
  refine ⟨plan6709,valid6709,t6_35choices,?_⟩
  exact check_of_frontier tree 0 t6_35root t6_35jobs t6_35frontier t6_35all
theorem t6_36choices : plan6710.choices=[0,2,6,10,10,7].map (options 6 4) := by rfl


theorem t6_36part0 : t6_36jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_36frontier : t6_36root.frontier 0=t6_36jobs := by rfl
theorem t6_36all : t6_36jobs.all (Job.check tree)=true := by
  simp only [t6_36jobs,List.all_append,List.all_nil,t6_36part0,Bool.and_self]
theorem t6_36checked : Checked tree [0,2,6,10,10,7] := by
  refine ⟨plan6710,valid6710,t6_36choices,?_⟩
  exact check_of_frontier tree 0 t6_36root t6_36jobs t6_36frontier t6_36all
theorem t6_37choices : plan6711.choices=[0,2,7,7,7,7].map (options 6 4) := by rfl


theorem t6_37part0 : t6_37jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_37frontier : t6_37root.frontier 0=t6_37jobs := by rfl
theorem t6_37all : t6_37jobs.all (Job.check tree)=true := by
  simp only [t6_37jobs,List.all_append,List.all_nil,t6_37part0,Bool.and_self]
theorem t6_37checked : Checked tree [0,2,7,7,7,7] := by
  refine ⟨plan6711,valid6711,t6_37choices,?_⟩
  exact check_of_frontier tree 0 t6_37root t6_37jobs t6_37frontier t6_37all
theorem t6_38choices : plan6448.choices=[0,2,9,3,7,7].map (options 6 3) := by rfl


theorem t6_38part0 : t6_38jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_38frontier : t6_38root.frontier 0=t6_38jobs := by rfl
theorem t6_38all : t6_38jobs.all (Job.check tree)=true := by
  simp only [t6_38jobs,List.all_append,List.all_nil,t6_38part0,Bool.and_self]
theorem t6_38checked : Checked tree [0,2,9,3,7,7] := by
  refine ⟨plan6448,valid6448,t6_38choices,?_⟩
  exact check_of_frontier tree 0 t6_38root t6_38jobs t6_38frontier t6_38all
theorem t6_39choices : plan6712.choices=[0,2,9,6,7,7].map (options 6 4) := by rfl


theorem t6_39part0 : t6_39jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_39frontier : t6_39root.frontier 0=t6_39jobs := by rfl
theorem t6_39all : t6_39jobs.all (Job.check tree)=true := by
  simp only [t6_39jobs,List.all_append,List.all_nil,t6_39part0,Bool.and_self]
theorem t6_39checked : Checked tree [0,2,9,6,7,7] := by
  refine ⟨plan6712,valid6712,t6_39choices,?_⟩
  exact check_of_frontier tree 0 t6_39root t6_39jobs t6_39frontier t6_39all
theorem t6_40choices : plan6713.choices=[0,2,9,7,7,7].map (options 6 4) := by rfl


theorem t6_40part0 : t6_40jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_40frontier : t6_40root.frontier 0=t6_40jobs := by rfl
theorem t6_40all : t6_40jobs.all (Job.check tree)=true := by
  simp only [t6_40jobs,List.all_append,List.all_nil,t6_40part0,Bool.and_self]
theorem t6_40checked : Checked tree [0,2,9,7,7,7] := by
  refine ⟨plan6713,valid6713,t6_40choices,?_⟩
  exact check_of_frontier tree 0 t6_40root t6_40jobs t6_40frontier t6_40all
theorem t6_41choices : plan6714.choices=[0,2,9,10,7,7].map (options 6 4) := by rfl


theorem t6_41part0 : t6_41jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_41frontier : t6_41root.frontier 0=t6_41jobs := by rfl
theorem t6_41all : t6_41jobs.all (Job.check tree)=true := by
  simp only [t6_41jobs,List.all_append,List.all_nil,t6_41part0,Bool.and_self]
theorem t6_41checked : Checked tree [0,2,9,10,7,7] := by
  refine ⟨plan6714,valid6714,t6_41choices,?_⟩
  exact check_of_frontier tree 0 t6_41root t6_41jobs t6_41frontier t6_41all
theorem t6_42choices : plan6715.choices=[0,2,10,7,7,7].map (options 6 4) := by rfl


theorem t6_42part0 : t6_42jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_42frontier : t6_42root.frontier 0=t6_42jobs := by rfl
theorem t6_42all : t6_42jobs.all (Job.check tree)=true := by
  simp only [t6_42jobs,List.all_append,List.all_nil,t6_42part0,Bool.and_self]
theorem t6_42checked : Checked tree [0,2,10,7,7,7] := by
  refine ⟨plan6715,valid6715,t6_42choices,?_⟩
  exact check_of_frontier tree 0 t6_42root t6_42jobs t6_42frontier t6_42all
theorem t6_43choices : plan6716.choices=[0,2,10,10,7,7].map (options 6 4) := by rfl


theorem t6_43part0 : t6_43jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_43frontier : t6_43root.frontier 0=t6_43jobs := by rfl
theorem t6_43all : t6_43jobs.all (Job.check tree)=true := by
  simp only [t6_43jobs,List.all_append,List.all_nil,t6_43part0,Bool.and_self]
theorem t6_43checked : Checked tree [0,2,10,10,7,7] := by
  refine ⟨plan6716,valid6716,t6_43choices,?_⟩
  exact check_of_frontier tree 0 t6_43root t6_43jobs t6_43frontier t6_43all
theorem t6_44choices : plan6717.choices=[0,2,10,10,10,7].map (options 6 4) := by rfl


theorem t6_44part0 : t6_44jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_44frontier : t6_44root.frontier 0=t6_44jobs := by rfl
theorem t6_44all : t6_44jobs.all (Job.check tree)=true := by
  simp only [t6_44jobs,List.all_append,List.all_nil,t6_44part0,Bool.and_self]
theorem t6_44checked : Checked tree [0,2,10,10,10,7] := by
  refine ⟨plan6717,valid6717,t6_44choices,?_⟩
  exact check_of_frontier tree 0 t6_44root t6_44jobs t6_44frontier t6_44all
theorem t6_45choices : plan6276.choices=[0,3,3,3,3,3].map (options 6 0) := by rfl


theorem t6_45part0 : t6_45jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_45frontier : t6_45root.frontier 0=t6_45jobs := by rfl
theorem t6_45all : t6_45jobs.all (Job.check tree)=true := by
  simp only [t6_45jobs,List.all_append,List.all_nil,t6_45part0,Bool.and_self]
theorem t6_45checked : Checked tree [0,3,3,3,3,3] := by
  refine ⟨plan6276,valid6276,t6_45choices,?_⟩
  exact check_of_frontier tree 0 t6_45root t6_45jobs t6_45frontier t6_45all
theorem t6_46choices : plan6284.choices=[0,3,3,3,3,6].map (options 6 1) := by rfl


theorem t6_46part0 : t6_46jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_46frontier : t6_46root.frontier 0=t6_46jobs := by rfl
theorem t6_46all : t6_46jobs.all (Job.check tree)=true := by
  simp only [t6_46jobs,List.all_append,List.all_nil,t6_46part0,Bool.and_self]
theorem t6_46checked : Checked tree [0,3,3,3,3,6] := by
  refine ⟨plan6284,valid6284,t6_46choices,?_⟩
  exact check_of_frontier tree 0 t6_46root t6_46jobs t6_46frontier t6_46all
theorem t6_47choices : plan6285.choices=[0,3,3,3,3,7].map (options 6 1) := by rfl


theorem t6_47part0 : t6_47jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_47frontier : t6_47root.frontier 0=t6_47jobs := by rfl
theorem t6_47all : t6_47jobs.all (Job.check tree)=true := by
  simp only [t6_47jobs,List.all_append,List.all_nil,t6_47part0,Bool.and_self]
theorem t6_47checked : Checked tree [0,3,3,3,3,7] := by
  refine ⟨plan6285,valid6285,t6_47choices,?_⟩
  exact check_of_frontier tree 0 t6_47root t6_47jobs t6_47frontier t6_47all
theorem t6_48choices : plan6286.choices=[0,3,3,3,3,10].map (options 6 1) := by rfl


theorem t6_48part0 : t6_48jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_48frontier : t6_48root.frontier 0=t6_48jobs := by rfl
theorem t6_48all : t6_48jobs.all (Job.check tree)=true := by
  simp only [t6_48jobs,List.all_append,List.all_nil,t6_48part0,Bool.and_self]
theorem t6_48checked : Checked tree [0,3,3,3,3,10] := by
  refine ⟨plan6286,valid6286,t6_48choices,?_⟩
  exact check_of_frontier tree 0 t6_48root t6_48jobs t6_48frontier t6_48all
theorem t6_49choices : plan6325.choices=[0,3,3,3,6,6].map (options 6 2) := by rfl


theorem t6_49part0 : t6_49jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_49frontier : t6_49root.frontier 0=t6_49jobs := by rfl
theorem t6_49all : t6_49jobs.all (Job.check tree)=true := by
  simp only [t6_49jobs,List.all_append,List.all_nil,t6_49part0,Bool.and_self]
theorem t6_49checked : Checked tree [0,3,3,3,6,6] := by
  refine ⟨plan6325,valid6325,t6_49choices,?_⟩
  exact check_of_frontier tree 0 t6_49root t6_49jobs t6_49frontier t6_49all
theorem t6_50choices : plan6326.choices=[0,3,3,3,6,7].map (options 6 2) := by rfl


theorem t6_50part0 : t6_50jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_50frontier : t6_50root.frontier 0=t6_50jobs := by rfl
theorem t6_50all : t6_50jobs.all (Job.check tree)=true := by
  simp only [t6_50jobs,List.all_append,List.all_nil,t6_50part0,Bool.and_self]
theorem t6_50checked : Checked tree [0,3,3,3,6,7] := by
  refine ⟨plan6326,valid6326,t6_50choices,?_⟩
  exact check_of_frontier tree 0 t6_50root t6_50jobs t6_50frontier t6_50all
theorem t6_51choices : plan6327.choices=[0,3,3,3,6,10].map (options 6 2) := by rfl


theorem t6_51part0 : t6_51jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_51frontier : t6_51root.frontier 0=t6_51jobs := by rfl
theorem t6_51all : t6_51jobs.all (Job.check tree)=true := by
  simp only [t6_51jobs,List.all_append,List.all_nil,t6_51part0,Bool.and_self]
theorem t6_51checked : Checked tree [0,3,3,3,6,10] := by
  refine ⟨plan6327,valid6327,t6_51choices,?_⟩
  exact check_of_frontier tree 0 t6_51root t6_51jobs t6_51frontier t6_51all
theorem t6_52choices : plan6328.choices=[0,3,3,3,7,7].map (options 6 2) := by rfl


theorem t6_52part0 : t6_52jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_52frontier : t6_52root.frontier 0=t6_52jobs := by rfl
theorem t6_52all : t6_52jobs.all (Job.check tree)=true := by
  simp only [t6_52jobs,List.all_append,List.all_nil,t6_52part0,Bool.and_self]
theorem t6_52checked : Checked tree [0,3,3,3,7,7] := by
  refine ⟨plan6328,valid6328,t6_52choices,?_⟩
  exact check_of_frontier tree 0 t6_52root t6_52jobs t6_52frontier t6_52all
theorem t6_53choices : plan6329.choices=[0,3,3,3,10,7].map (options 6 2) := by rfl


theorem t6_53part0 : t6_53jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_53frontier : t6_53root.frontier 0=t6_53jobs := by rfl
theorem t6_53all : t6_53jobs.all (Job.check tree)=true := by
  simp only [t6_53jobs,List.all_append,List.all_nil,t6_53part0,Bool.and_self]
theorem t6_53checked : Checked tree [0,3,3,3,10,7] := by
  refine ⟨plan6329,valid6329,t6_53choices,?_⟩
  exact check_of_frontier tree 0 t6_53root t6_53jobs t6_53frontier t6_53all
theorem t6_54choices : plan6330.choices=[0,3,3,3,10,10].map (options 6 2) := by rfl


theorem t6_54part0 : t6_54jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_54frontier : t6_54root.frontier 0=t6_54jobs := by rfl
theorem t6_54all : t6_54jobs.all (Job.check tree)=true := by
  simp only [t6_54jobs,List.all_append,List.all_nil,t6_54part0,Bool.and_self]
theorem t6_54checked : Checked tree [0,3,3,3,10,10] := by
  refine ⟨plan6330,valid6330,t6_54choices,?_⟩
  exact check_of_frontier tree 0 t6_54root t6_54jobs t6_54frontier t6_54all
theorem t6_55choices : plan6449.choices=[0,3,3,6,6,6].map (options 6 3) := by rfl


theorem t6_55part0 : t6_55jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_55frontier : t6_55root.frontier 0=t6_55jobs := by rfl
theorem t6_55all : t6_55jobs.all (Job.check tree)=true := by
  simp only [t6_55jobs,List.all_append,List.all_nil,t6_55part0,Bool.and_self]
theorem t6_55checked : Checked tree [0,3,3,6,6,6] := by
  refine ⟨plan6449,valid6449,t6_55choices,?_⟩
  exact check_of_frontier tree 0 t6_55root t6_55jobs t6_55frontier t6_55all
theorem t6_56choices : plan6450.choices=[0,3,3,6,6,7].map (options 6 3) := by rfl


theorem t6_56part0 : t6_56jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_56frontier : t6_56root.frontier 0=t6_56jobs := by rfl
theorem t6_56all : t6_56jobs.all (Job.check tree)=true := by
  simp only [t6_56jobs,List.all_append,List.all_nil,t6_56part0,Bool.and_self]
theorem t6_56checked : Checked tree [0,3,3,6,6,7] := by
  refine ⟨plan6450,valid6450,t6_56choices,?_⟩
  exact check_of_frontier tree 0 t6_56root t6_56jobs t6_56frontier t6_56all
theorem t6_57choices : plan6451.choices=[0,3,3,6,6,10].map (options 6 3) := by rfl


theorem t6_57part0 : t6_57jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_57frontier : t6_57root.frontier 0=t6_57jobs := by rfl
theorem t6_57all : t6_57jobs.all (Job.check tree)=true := by
  simp only [t6_57jobs,List.all_append,List.all_nil,t6_57part0,Bool.and_self]
theorem t6_57checked : Checked tree [0,3,3,6,6,10] := by
  refine ⟨plan6451,valid6451,t6_57choices,?_⟩
  exact check_of_frontier tree 0 t6_57root t6_57jobs t6_57frontier t6_57all
theorem t6_58choices : plan6452.choices=[0,3,3,6,7,7].map (options 6 3) := by rfl


theorem t6_58part0 : t6_58jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_58frontier : t6_58root.frontier 0=t6_58jobs := by rfl
theorem t6_58all : t6_58jobs.all (Job.check tree)=true := by
  simp only [t6_58jobs,List.all_append,List.all_nil,t6_58part0,Bool.and_self]
theorem t6_58checked : Checked tree [0,3,3,6,7,7] := by
  refine ⟨plan6452,valid6452,t6_58choices,?_⟩
  exact check_of_frontier tree 0 t6_58root t6_58jobs t6_58frontier t6_58all
theorem t6_59choices : plan6453.choices=[0,3,3,6,10,7].map (options 6 3) := by rfl


theorem t6_59part0 : t6_59jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_59frontier : t6_59root.frontier 0=t6_59jobs := by rfl
theorem t6_59all : t6_59jobs.all (Job.check tree)=true := by
  simp only [t6_59jobs,List.all_append,List.all_nil,t6_59part0,Bool.and_self]
theorem t6_59checked : Checked tree [0,3,3,6,10,7] := by
  refine ⟨plan6453,valid6453,t6_59choices,?_⟩
  exact check_of_frontier tree 0 t6_59root t6_59jobs t6_59frontier t6_59all
theorem t6_60choices : plan6454.choices=[0,3,3,6,10,10].map (options 6 3) := by rfl


theorem t6_60part0 : t6_60jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_60frontier : t6_60root.frontier 0=t6_60jobs := by rfl
theorem t6_60all : t6_60jobs.all (Job.check tree)=true := by
  simp only [t6_60jobs,List.all_append,List.all_nil,t6_60part0,Bool.and_self]
theorem t6_60checked : Checked tree [0,3,3,6,10,10] := by
  refine ⟨plan6454,valid6454,t6_60choices,?_⟩
  exact check_of_frontier tree 0 t6_60root t6_60jobs t6_60frontier t6_60all
theorem t6_61choices : plan6455.choices=[0,3,3,7,7,7].map (options 6 3) := by rfl


theorem t6_61part0 : t6_61jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_61frontier : t6_61root.frontier 0=t6_61jobs := by rfl
theorem t6_61all : t6_61jobs.all (Job.check tree)=true := by
  simp only [t6_61jobs,List.all_append,List.all_nil,t6_61part0,Bool.and_self]
theorem t6_61checked : Checked tree [0,3,3,7,7,7] := by
  refine ⟨plan6455,valid6455,t6_61choices,?_⟩
  exact check_of_frontier tree 0 t6_61root t6_61jobs t6_61frontier t6_61all
theorem t6_62choices : plan6456.choices=[0,3,3,10,7,7].map (options 6 3) := by rfl


theorem t6_62part0 : t6_62jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_62frontier : t6_62root.frontier 0=t6_62jobs := by rfl
theorem t6_62all : t6_62jobs.all (Job.check tree)=true := by
  simp only [t6_62jobs,List.all_append,List.all_nil,t6_62part0,Bool.and_self]
theorem t6_62checked : Checked tree [0,3,3,10,7,7] := by
  refine ⟨plan6456,valid6456,t6_62choices,?_⟩
  exact check_of_frontier tree 0 t6_62root t6_62jobs t6_62frontier t6_62all
theorem t6_63choices : plan6457.choices=[0,3,3,10,10,7].map (options 6 3) := by rfl


theorem t6_63part0 : t6_63jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_63frontier : t6_63root.frontier 0=t6_63jobs := by rfl
theorem t6_63all : t6_63jobs.all (Job.check tree)=true := by
  simp only [t6_63jobs,List.all_append,List.all_nil,t6_63part0,Bool.and_self]
theorem t6_63checked : Checked tree [0,3,3,10,10,7] := by
  refine ⟨plan6457,valid6457,t6_63choices,?_⟩
  exact check_of_frontier tree 0 t6_63root t6_63jobs t6_63frontier t6_63all
theorem t6_64choices : plan6458.choices=[0,3,3,10,10,10].map (options 6 3) := by rfl


theorem t6_64part0 : t6_64jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_64frontier : t6_64root.frontier 0=t6_64jobs := by rfl
theorem t6_64all : t6_64jobs.all (Job.check tree)=true := by
  simp only [t6_64jobs,List.all_append,List.all_nil,t6_64part0,Bool.and_self]
theorem t6_64checked : Checked tree [0,3,3,10,10,10] := by
  refine ⟨plan6458,valid6458,t6_64choices,?_⟩
  exact check_of_frontier tree 0 t6_64root t6_64jobs t6_64frontier t6_64all
theorem t6_65choices : plan6718.choices=[0,3,6,6,6,6].map (options 6 4) := by rfl


theorem t6_65part0 : t6_65jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_65frontier : t6_65root.frontier 0=t6_65jobs := by rfl
theorem t6_65all : t6_65jobs.all (Job.check tree)=true := by
  simp only [t6_65jobs,List.all_append,List.all_nil,t6_65part0,Bool.and_self]
theorem t6_65checked : Checked tree [0,3,6,6,6,6] := by
  refine ⟨plan6718,valid6718,t6_65choices,?_⟩
  exact check_of_frontier tree 0 t6_65root t6_65jobs t6_65frontier t6_65all
theorem t6_66choices : plan6719.choices=[0,3,6,6,6,7].map (options 6 4) := by rfl


theorem t6_66part0 : t6_66jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_66frontier : t6_66root.frontier 0=t6_66jobs := by rfl
theorem t6_66all : t6_66jobs.all (Job.check tree)=true := by
  simp only [t6_66jobs,List.all_append,List.all_nil,t6_66part0,Bool.and_self]
theorem t6_66checked : Checked tree [0,3,6,6,6,7] := by
  refine ⟨plan6719,valid6719,t6_66choices,?_⟩
  exact check_of_frontier tree 0 t6_66root t6_66jobs t6_66frontier t6_66all
theorem t6_67choices : plan6720.choices=[0,3,6,6,6,10].map (options 6 4) := by rfl


theorem t6_67part0 : t6_67jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_67frontier : t6_67root.frontier 0=t6_67jobs := by rfl
theorem t6_67all : t6_67jobs.all (Job.check tree)=true := by
  simp only [t6_67jobs,List.all_append,List.all_nil,t6_67part0,Bool.and_self]
theorem t6_67checked : Checked tree [0,3,6,6,6,10] := by
  refine ⟨plan6720,valid6720,t6_67choices,?_⟩
  exact check_of_frontier tree 0 t6_67root t6_67jobs t6_67frontier t6_67all
theorem t6_68choices : plan6721.choices=[0,3,6,6,7,7].map (options 6 4) := by rfl


theorem t6_68part0 : t6_68jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_68frontier : t6_68root.frontier 0=t6_68jobs := by rfl
theorem t6_68all : t6_68jobs.all (Job.check tree)=true := by
  simp only [t6_68jobs,List.all_append,List.all_nil,t6_68part0,Bool.and_self]
theorem t6_68checked : Checked tree [0,3,6,6,7,7] := by
  refine ⟨plan6721,valid6721,t6_68choices,?_⟩
  exact check_of_frontier tree 0 t6_68root t6_68jobs t6_68frontier t6_68all
theorem t6_69choices : plan6722.choices=[0,3,6,6,10,7].map (options 6 4) := by rfl


theorem t6_69part0 : t6_69jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_69frontier : t6_69root.frontier 0=t6_69jobs := by rfl
theorem t6_69all : t6_69jobs.all (Job.check tree)=true := by
  simp only [t6_69jobs,List.all_append,List.all_nil,t6_69part0,Bool.and_self]
theorem t6_69checked : Checked tree [0,3,6,6,10,7] := by
  refine ⟨plan6722,valid6722,t6_69choices,?_⟩
  exact check_of_frontier tree 0 t6_69root t6_69jobs t6_69frontier t6_69all
theorem t6_70choices : plan6723.choices=[0,3,6,6,10,10].map (options 6 4) := by rfl


theorem t6_70part0 : t6_70jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_70frontier : t6_70root.frontier 0=t6_70jobs := by rfl
theorem t6_70all : t6_70jobs.all (Job.check tree)=true := by
  simp only [t6_70jobs,List.all_append,List.all_nil,t6_70part0,Bool.and_self]
theorem t6_70checked : Checked tree [0,3,6,6,10,10] := by
  refine ⟨plan6723,valid6723,t6_70choices,?_⟩
  exact check_of_frontier tree 0 t6_70root t6_70jobs t6_70frontier t6_70all
theorem t6_71choices : plan6724.choices=[0,3,6,7,7,7].map (options 6 4) := by rfl


theorem t6_71part0 : t6_71jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_71frontier : t6_71root.frontier 0=t6_71jobs := by rfl
theorem t6_71all : t6_71jobs.all (Job.check tree)=true := by
  simp only [t6_71jobs,List.all_append,List.all_nil,t6_71part0,Bool.and_self]
theorem t6_71checked : Checked tree [0,3,6,7,7,7] := by
  refine ⟨plan6724,valid6724,t6_71choices,?_⟩
  exact check_of_frontier tree 0 t6_71root t6_71jobs t6_71frontier t6_71all
theorem t6_72choices : plan6725.choices=[0,3,6,10,7,7].map (options 6 4) := by rfl


theorem t6_72part0 : t6_72jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_72frontier : t6_72root.frontier 0=t6_72jobs := by rfl
theorem t6_72all : t6_72jobs.all (Job.check tree)=true := by
  simp only [t6_72jobs,List.all_append,List.all_nil,t6_72part0,Bool.and_self]
theorem t6_72checked : Checked tree [0,3,6,10,7,7] := by
  refine ⟨plan6725,valid6725,t6_72choices,?_⟩
  exact check_of_frontier tree 0 t6_72root t6_72jobs t6_72frontier t6_72all
theorem t6_73choices : plan6726.choices=[0,3,6,10,10,7].map (options 6 4) := by rfl


theorem t6_73part0 : t6_73jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_73frontier : t6_73root.frontier 0=t6_73jobs := by rfl
theorem t6_73all : t6_73jobs.all (Job.check tree)=true := by
  simp only [t6_73jobs,List.all_append,List.all_nil,t6_73part0,Bool.and_self]
theorem t6_73checked : Checked tree [0,3,6,10,10,7] := by
  refine ⟨plan6726,valid6726,t6_73choices,?_⟩
  exact check_of_frontier tree 0 t6_73root t6_73jobs t6_73frontier t6_73all
theorem t6_74choices : plan6727.choices=[0,3,6,10,10,10].map (options 6 4) := by rfl


theorem t6_74part0 : t6_74jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_74frontier : t6_74root.frontier 0=t6_74jobs := by rfl
theorem t6_74all : t6_74jobs.all (Job.check tree)=true := by
  simp only [t6_74jobs,List.all_append,List.all_nil,t6_74part0,Bool.and_self]
theorem t6_74checked : Checked tree [0,3,6,10,10,10] := by
  refine ⟨plan6727,valid6727,t6_74choices,?_⟩
  exact check_of_frontier tree 0 t6_74root t6_74jobs t6_74frontier t6_74all
theorem t6_75choices : plan6728.choices=[0,3,7,7,7,7].map (options 6 4) := by rfl


theorem t6_75part0 : t6_75jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_75frontier : t6_75root.frontier 0=t6_75jobs := by rfl
theorem t6_75all : t6_75jobs.all (Job.check tree)=true := by
  simp only [t6_75jobs,List.all_append,List.all_nil,t6_75part0,Bool.and_self]
theorem t6_75checked : Checked tree [0,3,7,7,7,7] := by
  refine ⟨plan6728,valid6728,t6_75choices,?_⟩
  exact check_of_frontier tree 0 t6_75root t6_75jobs t6_75frontier t6_75all
theorem t6_76choices : plan6729.choices=[0,3,10,7,7,7].map (options 6 4) := by rfl


theorem t6_76part0 : t6_76jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_76frontier : t6_76root.frontier 0=t6_76jobs := by rfl
theorem t6_76all : t6_76jobs.all (Job.check tree)=true := by
  simp only [t6_76jobs,List.all_append,List.all_nil,t6_76part0,Bool.and_self]
theorem t6_76checked : Checked tree [0,3,10,7,7,7] := by
  refine ⟨plan6729,valid6729,t6_76choices,?_⟩
  exact check_of_frontier tree 0 t6_76root t6_76jobs t6_76frontier t6_76all
theorem t6_77choices : plan6730.choices=[0,3,10,10,7,7].map (options 6 4) := by rfl


theorem t6_77part0 : t6_77jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_77frontier : t6_77root.frontier 0=t6_77jobs := by rfl
theorem t6_77all : t6_77jobs.all (Job.check tree)=true := by
  simp only [t6_77jobs,List.all_append,List.all_nil,t6_77part0,Bool.and_self]
theorem t6_77checked : Checked tree [0,3,10,10,7,7] := by
  refine ⟨plan6730,valid6730,t6_77choices,?_⟩
  exact check_of_frontier tree 0 t6_77root t6_77jobs t6_77frontier t6_77all
theorem t6_78choices : plan6731.choices=[0,3,10,10,10,7].map (options 6 4) := by rfl


theorem t6_78part0 : t6_78jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_78frontier : t6_78root.frontier 0=t6_78jobs := by rfl
theorem t6_78all : t6_78jobs.all (Job.check tree)=true := by
  simp only [t6_78jobs,List.all_append,List.all_nil,t6_78part0,Bool.and_self]
theorem t6_78checked : Checked tree [0,3,10,10,10,7] := by
  refine ⟨plan6731,valid6731,t6_78choices,?_⟩
  exact check_of_frontier tree 0 t6_78root t6_78jobs t6_78frontier t6_78all
theorem t6_79choices : plan6732.choices=[0,3,10,10,10,10].map (options 6 4) := by rfl


theorem t6_79part0 : t6_79jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_79frontier : t6_79root.frontier 0=t6_79jobs := by rfl
theorem t6_79all : t6_79jobs.all (Job.check tree)=true := by
  simp only [t6_79jobs,List.all_append,List.all_nil,t6_79part0,Bool.and_self]
theorem t6_79checked : Checked tree [0,3,10,10,10,10] := by
  refine ⟨plan6732,valid6732,t6_79choices,?_⟩
  exact check_of_frontier tree 0 t6_79root t6_79jobs t6_79frontier t6_79all
theorem t6_80choices : plan6733.choices=[0,4,2,7,7,7].map (options 6 4) := by rfl


theorem t6_80part0 : t6_80jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_80frontier : t6_80root.frontier 0=t6_80jobs := by rfl
theorem t6_80all : t6_80jobs.all (Job.check tree)=true := by
  simp only [t6_80jobs,List.all_append,List.all_nil,t6_80part0,Bool.and_self]
theorem t6_80checked : Checked tree [0,4,2,7,7,7] := by
  refine ⟨plan6733,valid6733,t6_80choices,?_⟩
  exact check_of_frontier tree 0 t6_80root t6_80jobs t6_80frontier t6_80all
theorem t6_81choices : plan6459.choices=[0,4,3,3,7,7].map (options 6 3) := by rfl


theorem t6_81part0 : t6_81jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_81frontier : t6_81root.frontier 0=t6_81jobs := by rfl
theorem t6_81all : t6_81jobs.all (Job.check tree)=true := by
  simp only [t6_81jobs,List.all_append,List.all_nil,t6_81part0,Bool.and_self]
theorem t6_81checked : Checked tree [0,4,3,3,7,7] := by
  refine ⟨plan6459,valid6459,t6_81choices,?_⟩
  exact check_of_frontier tree 0 t6_81root t6_81jobs t6_81frontier t6_81all
theorem t6_82choices : plan6734.choices=[0,4,3,6,7,7].map (options 6 4) := by rfl


theorem t6_82part0 : t6_82jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_82frontier : t6_82root.frontier 0=t6_82jobs := by rfl
theorem t6_82all : t6_82jobs.all (Job.check tree)=true := by
  simp only [t6_82jobs,List.all_append,List.all_nil,t6_82part0,Bool.and_self]
theorem t6_82checked : Checked tree [0,4,3,6,7,7] := by
  refine ⟨plan6734,valid6734,t6_82choices,?_⟩
  exact check_of_frontier tree 0 t6_82root t6_82jobs t6_82frontier t6_82all
theorem t6_83choices : plan6735.choices=[0,4,3,7,7,7].map (options 6 4) := by rfl


theorem t6_83part0 : t6_83jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_83frontier : t6_83root.frontier 0=t6_83jobs := by rfl
theorem t6_83all : t6_83jobs.all (Job.check tree)=true := by
  simp only [t6_83jobs,List.all_append,List.all_nil,t6_83part0,Bool.and_self]
theorem t6_83checked : Checked tree [0,4,3,7,7,7] := by
  refine ⟨plan6735,valid6735,t6_83choices,?_⟩
  exact check_of_frontier tree 0 t6_83root t6_83jobs t6_83frontier t6_83all
theorem t6_84choices : plan6736.choices=[0,4,3,10,7,7].map (options 6 4) := by rfl


theorem t6_84part0 : t6_84jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_84frontier : t6_84root.frontier 0=t6_84jobs := by rfl
theorem t6_84all : t6_84jobs.all (Job.check tree)=true := by
  simp only [t6_84jobs,List.all_append,List.all_nil,t6_84part0,Bool.and_self]
theorem t6_84checked : Checked tree [0,4,3,10,7,7] := by
  refine ⟨plan6736,valid6736,t6_84choices,?_⟩
  exact check_of_frontier tree 0 t6_84root t6_84jobs t6_84frontier t6_84all
theorem t6_85choices : plan7146.choices=[0,4,5,7,7,7].map (options 6 5) := by rfl


theorem t6_85part0 : t6_85jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_85frontier : t6_85root.frontier 0=t6_85jobs := by rfl
theorem t6_85all : t6_85jobs.all (Job.check tree)=true := by
  simp only [t6_85jobs,List.all_append,List.all_nil,t6_85part0,Bool.and_self]
theorem t6_85checked : Checked tree [0,4,5,7,7,7] := by
  refine ⟨plan7146,valid7146,t6_85choices,?_⟩
  exact check_of_frontier tree 0 t6_85root t6_85jobs t6_85frontier t6_85all
theorem t6_86choices : plan7147.choices=[0,4,6,6,7,7].map (options 6 5) := by rfl


theorem t6_86part0 : t6_86jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_86frontier : t6_86root.frontier 0=t6_86jobs := by rfl
theorem t6_86all : t6_86jobs.all (Job.check tree)=true := by
  simp only [t6_86jobs,List.all_append,List.all_nil,t6_86part0,Bool.and_self]
theorem t6_86checked : Checked tree [0,4,6,6,7,7] := by
  refine ⟨plan7147,valid7147,t6_86choices,?_⟩
  exact check_of_frontier tree 0 t6_86root t6_86jobs t6_86frontier t6_86all
theorem t6_87choices : plan7148.choices=[0,4,6,7,7,7].map (options 6 5) := by rfl


theorem t6_87part0 : t6_87jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_87frontier : t6_87root.frontier 0=t6_87jobs := by rfl
theorem t6_87all : t6_87jobs.all (Job.check tree)=true := by
  simp only [t6_87jobs,List.all_append,List.all_nil,t6_87part0,Bool.and_self]
theorem t6_87checked : Checked tree [0,4,6,7,7,7] := by
  refine ⟨plan7148,valid7148,t6_87choices,?_⟩
  exact check_of_frontier tree 0 t6_87root t6_87jobs t6_87frontier t6_87all
theorem t6_88choices : plan7149.choices=[0,4,6,10,7,7].map (options 6 5) := by rfl


theorem t6_88part0 : t6_88jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_88frontier : t6_88root.frontier 0=t6_88jobs := by rfl
theorem t6_88all : t6_88jobs.all (Job.check tree)=true := by
  simp only [t6_88jobs,List.all_append,List.all_nil,t6_88part0,Bool.and_self]
theorem t6_88checked : Checked tree [0,4,6,10,7,7] := by
  refine ⟨plan7149,valid7149,t6_88choices,?_⟩
  exact check_of_frontier tree 0 t6_88root t6_88jobs t6_88frontier t6_88all
theorem t6_89choices : plan7150.choices=[0,4,7,7,7,7].map (options 6 5) := by rfl


theorem t6_89part0 : t6_89jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_89frontier : t6_89root.frontier 0=t6_89jobs := by rfl
theorem t6_89all : t6_89jobs.all (Job.check tree)=true := by
  simp only [t6_89jobs,List.all_append,List.all_nil,t6_89part0,Bool.and_self]
theorem t6_89checked : Checked tree [0,4,7,7,7,7] := by
  refine ⟨plan7150,valid7150,t6_89choices,?_⟩
  exact check_of_frontier tree 0 t6_89root t6_89jobs t6_89frontier t6_89all
theorem t6_90choices : plan7151.choices=[0,4,9,7,7,7].map (options 6 5) := by rfl


theorem t6_90part0 : t6_90jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_90frontier : t6_90root.frontier 0=t6_90jobs := by rfl
theorem t6_90all : t6_90jobs.all (Job.check tree)=true := by
  simp only [t6_90jobs,List.all_append,List.all_nil,t6_90part0,Bool.and_self]
theorem t6_90checked : Checked tree [0,4,9,7,7,7] := by
  refine ⟨plan7151,valid7151,t6_90choices,?_⟩
  exact check_of_frontier tree 0 t6_90root t6_90jobs t6_90frontier t6_90all
theorem t6_91choices : plan7152.choices=[0,4,10,7,7,7].map (options 6 5) := by rfl


theorem t6_91part0 : t6_91jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_91frontier : t6_91root.frontier 0=t6_91jobs := by rfl
theorem t6_91all : t6_91jobs.all (Job.check tree)=true := by
  simp only [t6_91jobs,List.all_append,List.all_nil,t6_91part0,Bool.and_self]
theorem t6_91checked : Checked tree [0,4,10,7,7,7] := by
  refine ⟨plan7152,valid7152,t6_91choices,?_⟩
  exact check_of_frontier tree 0 t6_91root t6_91jobs t6_91frontier t6_91all
theorem t6_92choices : plan7153.choices=[0,4,10,10,7,7].map (options 6 5) := by rfl


theorem t6_92part0 : t6_92jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_92frontier : t6_92root.frontier 0=t6_92jobs := by rfl
theorem t6_92all : t6_92jobs.all (Job.check tree)=true := by
  simp only [t6_92jobs,List.all_append,List.all_nil,t6_92part0,Bool.and_self]
theorem t6_92checked : Checked tree [0,4,10,10,7,7] := by
  refine ⟨plan7153,valid7153,t6_92choices,?_⟩
  exact check_of_frontier tree 0 t6_92root t6_92jobs t6_92frontier t6_92all
theorem t6_93choices : plan6331.choices=[0,5,3,3,3,7].map (options 6 2) := by rfl


theorem t6_93part0 : t6_93jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_93frontier : t6_93root.frontier 0=t6_93jobs := by rfl
theorem t6_93all : t6_93jobs.all (Job.check tree)=true := by
  simp only [t6_93jobs,List.all_append,List.all_nil,t6_93part0,Bool.and_self]
theorem t6_93checked : Checked tree [0,5,3,3,3,7] := by
  refine ⟨plan6331,valid6331,t6_93choices,?_⟩
  exact check_of_frontier tree 0 t6_93root t6_93jobs t6_93frontier t6_93all
theorem t6_94choices : plan6460.choices=[0,5,3,3,6,7].map (options 6 3) := by rfl


theorem t6_94part0 : t6_94jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_94frontier : t6_94root.frontier 0=t6_94jobs := by rfl
theorem t6_94all : t6_94jobs.all (Job.check tree)=true := by
  simp only [t6_94jobs,List.all_append,List.all_nil,t6_94part0,Bool.and_self]
theorem t6_94checked : Checked tree [0,5,3,3,6,7] := by
  refine ⟨plan6460,valid6460,t6_94choices,?_⟩
  exact check_of_frontier tree 0 t6_94root t6_94jobs t6_94frontier t6_94all
theorem t6_95choices : plan6461.choices=[0,5,3,3,7,7].map (options 6 3) := by rfl


theorem t6_95part0 : t6_95jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_95frontier : t6_95root.frontier 0=t6_95jobs := by rfl
theorem t6_95all : t6_95jobs.all (Job.check tree)=true := by
  simp only [t6_95jobs,List.all_append,List.all_nil,t6_95part0,Bool.and_self]
theorem t6_95checked : Checked tree [0,5,3,3,7,7] := by
  refine ⟨plan6461,valid6461,t6_95choices,?_⟩
  exact check_of_frontier tree 0 t6_95root t6_95jobs t6_95frontier t6_95all
theorem t6_96choices : plan6462.choices=[0,5,3,3,10,7].map (options 6 3) := by rfl


theorem t6_96part0 : t6_96jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_96frontier : t6_96root.frontier 0=t6_96jobs := by rfl
theorem t6_96all : t6_96jobs.all (Job.check tree)=true := by
  simp only [t6_96jobs,List.all_append,List.all_nil,t6_96part0,Bool.and_self]
theorem t6_96checked : Checked tree [0,5,3,3,10,7] := by
  refine ⟨plan6462,valid6462,t6_96choices,?_⟩
  exact check_of_frontier tree 0 t6_96root t6_96jobs t6_96frontier t6_96all
theorem t6_97choices : plan6737.choices=[0,5,3,6,6,7].map (options 6 4) := by rfl


theorem t6_97part0 : t6_97jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_97frontier : t6_97root.frontier 0=t6_97jobs := by rfl
theorem t6_97all : t6_97jobs.all (Job.check tree)=true := by
  simp only [t6_97jobs,List.all_append,List.all_nil,t6_97part0,Bool.and_self]
theorem t6_97checked : Checked tree [0,5,3,6,6,7] := by
  refine ⟨plan6737,valid6737,t6_97choices,?_⟩
  exact check_of_frontier tree 0 t6_97root t6_97jobs t6_97frontier t6_97all
theorem t6_98choices : plan6738.choices=[0,5,3,6,7,7].map (options 6 4) := by rfl


theorem t6_98part0 : t6_98jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_98frontier : t6_98root.frontier 0=t6_98jobs := by rfl
theorem t6_98all : t6_98jobs.all (Job.check tree)=true := by
  simp only [t6_98jobs,List.all_append,List.all_nil,t6_98part0,Bool.and_self]
theorem t6_98checked : Checked tree [0,5,3,6,7,7] := by
  refine ⟨plan6738,valid6738,t6_98choices,?_⟩
  exact check_of_frontier tree 0 t6_98root t6_98jobs t6_98frontier t6_98all
theorem t6_99choices : plan6739.choices=[0,5,3,6,10,7].map (options 6 4) := by rfl


theorem t6_99part0 : t6_99jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_99frontier : t6_99root.frontier 0=t6_99jobs := by rfl
theorem t6_99all : t6_99jobs.all (Job.check tree)=true := by
  simp only [t6_99jobs,List.all_append,List.all_nil,t6_99part0,Bool.and_self]
theorem t6_99checked : Checked tree [0,5,3,6,10,7] := by
  refine ⟨plan6739,valid6739,t6_99choices,?_⟩
  exact check_of_frontier tree 0 t6_99root t6_99jobs t6_99frontier t6_99all
theorem t6_100choices : plan6740.choices=[0,5,3,7,7,7].map (options 6 4) := by rfl


theorem t6_100part0 : t6_100jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_100frontier : t6_100root.frontier 0=t6_100jobs := by rfl
theorem t6_100all : t6_100jobs.all (Job.check tree)=true := by
  simp only [t6_100jobs,List.all_append,List.all_nil,t6_100part0,Bool.and_self]
theorem t6_100checked : Checked tree [0,5,3,7,7,7] := by
  refine ⟨plan6740,valid6740,t6_100choices,?_⟩
  exact check_of_frontier tree 0 t6_100root t6_100jobs t6_100frontier t6_100all
theorem t6_101choices : plan6741.choices=[0,5,3,10,7,7].map (options 6 4) := by rfl


theorem t6_101part0 : t6_101jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_101frontier : t6_101root.frontier 0=t6_101jobs := by rfl
theorem t6_101all : t6_101jobs.all (Job.check tree)=true := by
  simp only [t6_101jobs,List.all_append,List.all_nil,t6_101part0,Bool.and_self]
theorem t6_101checked : Checked tree [0,5,3,10,7,7] := by
  refine ⟨plan6741,valid6741,t6_101choices,?_⟩
  exact check_of_frontier tree 0 t6_101root t6_101jobs t6_101frontier t6_101all
theorem t6_102choices : plan6742.choices=[0,5,3,10,10,7].map (options 6 4) := by rfl


theorem t6_102part0 : t6_102jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_102frontier : t6_102root.frontier 0=t6_102jobs := by rfl
theorem t6_102all : t6_102jobs.all (Job.check tree)=true := by
  simp only [t6_102jobs,List.all_append,List.all_nil,t6_102part0,Bool.and_self]
theorem t6_102checked : Checked tree [0,5,3,10,10,7] := by
  refine ⟨plan6742,valid6742,t6_102choices,?_⟩
  exact check_of_frontier tree 0 t6_102root t6_102jobs t6_102frontier t6_102all
theorem t6_103choices : plan6743.choices=[0,5,5,3,7,7].map (options 6 4) := by rfl


theorem t6_103part0 : t6_103jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_103frontier : t6_103root.frontier 0=t6_103jobs := by rfl
theorem t6_103all : t6_103jobs.all (Job.check tree)=true := by
  simp only [t6_103jobs,List.all_append,List.all_nil,t6_103part0,Bool.and_self]
theorem t6_103checked : Checked tree [0,5,5,3,7,7] := by
  refine ⟨plan6743,valid6743,t6_103choices,?_⟩
  exact check_of_frontier tree 0 t6_103root t6_103jobs t6_103frontier t6_103all
theorem t6_104choices : plan7154.choices=[0,5,5,6,7,7].map (options 6 5) := by rfl


theorem t6_104part0 : t6_104jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_104frontier : t6_104root.frontier 0=t6_104jobs := by rfl
theorem t6_104all : t6_104jobs.all (Job.check tree)=true := by
  simp only [t6_104jobs,List.all_append,List.all_nil,t6_104part0,Bool.and_self]
theorem t6_104checked : Checked tree [0,5,5,6,7,7] := by
  refine ⟨plan7154,valid7154,t6_104choices,?_⟩
  exact check_of_frontier tree 0 t6_104root t6_104jobs t6_104frontier t6_104all
theorem t6_105choices : plan7155.choices=[0,5,5,7,7,7].map (options 6 5) := by rfl


theorem t6_105part0 : t6_105jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_105frontier : t6_105root.frontier 0=t6_105jobs := by rfl
theorem t6_105all : t6_105jobs.all (Job.check tree)=true := by
  simp only [t6_105jobs,List.all_append,List.all_nil,t6_105part0,Bool.and_self]
theorem t6_105checked : Checked tree [0,5,5,7,7,7] := by
  refine ⟨plan7155,valid7155,t6_105choices,?_⟩
  exact check_of_frontier tree 0 t6_105root t6_105jobs t6_105frontier t6_105all
theorem t6_106choices : plan7156.choices=[0,5,5,10,7,7].map (options 6 5) := by rfl


theorem t6_106part0 : t6_106jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_106frontier : t6_106root.frontier 0=t6_106jobs := by rfl
theorem t6_106all : t6_106jobs.all (Job.check tree)=true := by
  simp only [t6_106jobs,List.all_append,List.all_nil,t6_106part0,Bool.and_self]
theorem t6_106checked : Checked tree [0,5,5,10,7,7] := by
  refine ⟨plan7156,valid7156,t6_106choices,?_⟩
  exact check_of_frontier tree 0 t6_106root t6_106jobs t6_106frontier t6_106all
theorem t6_107choices : plan7157.choices=[0,5,6,6,6,7].map (options 6 5) := by rfl


theorem t6_107part0 : t6_107jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_107frontier : t6_107root.frontier 0=t6_107jobs := by rfl
theorem t6_107all : t6_107jobs.all (Job.check tree)=true := by
  simp only [t6_107jobs,List.all_append,List.all_nil,t6_107part0,Bool.and_self]
theorem t6_107checked : Checked tree [0,5,6,6,6,7] := by
  refine ⟨plan7157,valid7157,t6_107choices,?_⟩
  exact check_of_frontier tree 0 t6_107root t6_107jobs t6_107frontier t6_107all
theorem t6_108choices : plan7158.choices=[0,5,6,6,7,7].map (options 6 5) := by rfl


theorem t6_108part0 : t6_108jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_108frontier : t6_108root.frontier 0=t6_108jobs := by rfl
theorem t6_108all : t6_108jobs.all (Job.check tree)=true := by
  simp only [t6_108jobs,List.all_append,List.all_nil,t6_108part0,Bool.and_self]
theorem t6_108checked : Checked tree [0,5,6,6,7,7] := by
  refine ⟨plan7158,valid7158,t6_108choices,?_⟩
  exact check_of_frontier tree 0 t6_108root t6_108jobs t6_108frontier t6_108all
theorem t6_109choices : plan7159.choices=[0,5,6,6,10,7].map (options 6 5) := by rfl


theorem t6_109part0 : t6_109jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_109frontier : t6_109root.frontier 0=t6_109jobs := by rfl
theorem t6_109all : t6_109jobs.all (Job.check tree)=true := by
  simp only [t6_109jobs,List.all_append,List.all_nil,t6_109part0,Bool.and_self]
theorem t6_109checked : Checked tree [0,5,6,6,10,7] := by
  refine ⟨plan7159,valid7159,t6_109choices,?_⟩
  exact check_of_frontier tree 0 t6_109root t6_109jobs t6_109frontier t6_109all
theorem t6_110choices : plan7160.choices=[0,5,6,7,7,7].map (options 6 5) := by rfl


theorem t6_110part0 : t6_110jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_110frontier : t6_110root.frontier 0=t6_110jobs := by rfl
theorem t6_110all : t6_110jobs.all (Job.check tree)=true := by
  simp only [t6_110jobs,List.all_append,List.all_nil,t6_110part0,Bool.and_self]
theorem t6_110checked : Checked tree [0,5,6,7,7,7] := by
  refine ⟨plan7160,valid7160,t6_110choices,?_⟩
  exact check_of_frontier tree 0 t6_110root t6_110jobs t6_110frontier t6_110all
theorem t6_111choices : plan7161.choices=[0,5,6,10,7,7].map (options 6 5) := by rfl


theorem t6_111part0 : t6_111jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_111frontier : t6_111root.frontier 0=t6_111jobs := by rfl
theorem t6_111all : t6_111jobs.all (Job.check tree)=true := by
  simp only [t6_111jobs,List.all_append,List.all_nil,t6_111part0,Bool.and_self]
theorem t6_111checked : Checked tree [0,5,6,10,7,7] := by
  refine ⟨plan7161,valid7161,t6_111choices,?_⟩
  exact check_of_frontier tree 0 t6_111root t6_111jobs t6_111frontier t6_111all
theorem t6_112choices : plan7162.choices=[0,5,6,10,10,7].map (options 6 5) := by rfl


theorem t6_112part0 : t6_112jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_112frontier : t6_112root.frontier 0=t6_112jobs := by rfl
theorem t6_112all : t6_112jobs.all (Job.check tree)=true := by
  simp only [t6_112jobs,List.all_append,List.all_nil,t6_112part0,Bool.and_self]
theorem t6_112checked : Checked tree [0,5,6,10,10,7] := by
  refine ⟨plan7162,valid7162,t6_112choices,?_⟩
  exact check_of_frontier tree 0 t6_112root t6_112jobs t6_112frontier t6_112all
theorem t6_113choices : plan7163.choices=[0,5,7,7,7,7].map (options 6 5) := by rfl


theorem t6_113part0 : t6_113jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_113frontier : t6_113root.frontier 0=t6_113jobs := by rfl
theorem t6_113all : t6_113jobs.all (Job.check tree)=true := by
  simp only [t6_113jobs,List.all_append,List.all_nil,t6_113part0,Bool.and_self]
theorem t6_113checked : Checked tree [0,5,7,7,7,7] := by
  refine ⟨plan7163,valid7163,t6_113choices,?_⟩
  exact check_of_frontier tree 0 t6_113root t6_113jobs t6_113frontier t6_113all
theorem t6_114choices : plan6744.choices=[0,5,9,3,7,7].map (options 6 4) := by rfl


theorem t6_114part0 : t6_114jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_114frontier : t6_114root.frontier 0=t6_114jobs := by rfl
theorem t6_114all : t6_114jobs.all (Job.check tree)=true := by
  simp only [t6_114jobs,List.all_append,List.all_nil,t6_114part0,Bool.and_self]
theorem t6_114checked : Checked tree [0,5,9,3,7,7] := by
  refine ⟨plan6744,valid6744,t6_114choices,?_⟩
  exact check_of_frontier tree 0 t6_114root t6_114jobs t6_114frontier t6_114all
theorem t6_115choices : plan7164.choices=[0,5,9,6,7,7].map (options 6 5) := by rfl


theorem t6_115part0 : t6_115jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_115frontier : t6_115root.frontier 0=t6_115jobs := by rfl
theorem t6_115all : t6_115jobs.all (Job.check tree)=true := by
  simp only [t6_115jobs,List.all_append,List.all_nil,t6_115part0,Bool.and_self]
theorem t6_115checked : Checked tree [0,5,9,6,7,7] := by
  refine ⟨plan7164,valid7164,t6_115choices,?_⟩
  exact check_of_frontier tree 0 t6_115root t6_115jobs t6_115frontier t6_115all
theorem t6_116choices : plan7165.choices=[0,5,9,7,7,7].map (options 6 5) := by rfl


theorem t6_116part0 : t6_116jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_116frontier : t6_116root.frontier 0=t6_116jobs := by rfl
theorem t6_116all : t6_116jobs.all (Job.check tree)=true := by
  simp only [t6_116jobs,List.all_append,List.all_nil,t6_116part0,Bool.and_self]
theorem t6_116checked : Checked tree [0,5,9,7,7,7] := by
  refine ⟨plan7165,valid7165,t6_116choices,?_⟩
  exact check_of_frontier tree 0 t6_116root t6_116jobs t6_116frontier t6_116all
theorem t6_117choices : plan7166.choices=[0,5,9,10,7,7].map (options 6 5) := by rfl


theorem t6_117part0 : t6_117jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_117frontier : t6_117root.frontier 0=t6_117jobs := by rfl
theorem t6_117all : t6_117jobs.all (Job.check tree)=true := by
  simp only [t6_117jobs,List.all_append,List.all_nil,t6_117part0,Bool.and_self]
theorem t6_117checked : Checked tree [0,5,9,10,7,7] := by
  refine ⟨plan7166,valid7166,t6_117choices,?_⟩
  exact check_of_frontier tree 0 t6_117root t6_117jobs t6_117frontier t6_117all
theorem t6_118choices : plan7167.choices=[0,5,10,7,7,7].map (options 6 5) := by rfl


theorem t6_118part0 : t6_118jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_118frontier : t6_118root.frontier 0=t6_118jobs := by rfl
theorem t6_118all : t6_118jobs.all (Job.check tree)=true := by
  simp only [t6_118jobs,List.all_append,List.all_nil,t6_118part0,Bool.and_self]
theorem t6_118checked : Checked tree [0,5,10,7,7,7] := by
  refine ⟨plan7167,valid7167,t6_118choices,?_⟩
  exact check_of_frontier tree 0 t6_118root t6_118jobs t6_118frontier t6_118all
theorem t6_119choices : plan7168.choices=[0,5,10,10,7,7].map (options 6 5) := by rfl


theorem t6_119part0 : t6_119jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_119frontier : t6_119root.frontier 0=t6_119jobs := by rfl
theorem t6_119all : t6_119jobs.all (Job.check tree)=true := by
  simp only [t6_119jobs,List.all_append,List.all_nil,t6_119part0,Bool.and_self]
theorem t6_119checked : Checked tree [0,5,10,10,7,7] := by
  refine ⟨plan7168,valid7168,t6_119choices,?_⟩
  exact check_of_frontier tree 0 t6_119root t6_119jobs t6_119frontier t6_119all
theorem t6_120choices : plan7169.choices=[0,5,10,10,10,7].map (options 6 5) := by rfl


theorem t6_120part0 : t6_120jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_120frontier : t6_120root.frontier 0=t6_120jobs := by rfl
theorem t6_120all : t6_120jobs.all (Job.check tree)=true := by
  simp only [t6_120jobs,List.all_append,List.all_nil,t6_120part0,Bool.and_self]
theorem t6_120checked : Checked tree [0,5,10,10,10,7] := by
  refine ⟨plan7169,valid7169,t6_120choices,?_⟩
  exact check_of_frontier tree 0 t6_120root t6_120jobs t6_120frontier t6_120all
theorem t6_121choices : plan7170.choices=[0,6,6,6,6,6].map (options 6 5) := by rfl


theorem t6_121part0 : t6_121jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_121frontier : t6_121root.frontier 0=t6_121jobs := by rfl
theorem t6_121all : t6_121jobs.all (Job.check tree)=true := by
  simp only [t6_121jobs,List.all_append,List.all_nil,t6_121part0,Bool.and_self]
theorem t6_121checked : Checked tree [0,6,6,6,6,6] := by
  refine ⟨plan7170,valid7170,t6_121choices,?_⟩
  exact check_of_frontier tree 0 t6_121root t6_121jobs t6_121frontier t6_121all
theorem t6_122choices : plan7171.choices=[0,6,6,6,6,7].map (options 6 5) := by rfl


theorem t6_122part0 : t6_122jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_122frontier : t6_122root.frontier 0=t6_122jobs := by rfl
theorem t6_122all : t6_122jobs.all (Job.check tree)=true := by
  simp only [t6_122jobs,List.all_append,List.all_nil,t6_122part0,Bool.and_self]
theorem t6_122checked : Checked tree [0,6,6,6,6,7] := by
  refine ⟨plan7171,valid7171,t6_122choices,?_⟩
  exact check_of_frontier tree 0 t6_122root t6_122jobs t6_122frontier t6_122all
theorem t6_123choices : plan7172.choices=[0,6,6,6,6,10].map (options 6 5) := by rfl


theorem t6_123part0 : t6_123jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_123frontier : t6_123root.frontier 0=t6_123jobs := by rfl
theorem t6_123all : t6_123jobs.all (Job.check tree)=true := by
  simp only [t6_123jobs,List.all_append,List.all_nil,t6_123part0,Bool.and_self]
theorem t6_123checked : Checked tree [0,6,6,6,6,10] := by
  refine ⟨plan7172,valid7172,t6_123choices,?_⟩
  exact check_of_frontier tree 0 t6_123root t6_123jobs t6_123frontier t6_123all
theorem t6_124choices : plan7173.choices=[0,6,6,6,7,7].map (options 6 5) := by rfl


theorem t6_124part0 : t6_124jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_124frontier : t6_124root.frontier 0=t6_124jobs := by rfl
theorem t6_124all : t6_124jobs.all (Job.check tree)=true := by
  simp only [t6_124jobs,List.all_append,List.all_nil,t6_124part0,Bool.and_self]
theorem t6_124checked : Checked tree [0,6,6,6,7,7] := by
  refine ⟨plan7173,valid7173,t6_124choices,?_⟩
  exact check_of_frontier tree 0 t6_124root t6_124jobs t6_124frontier t6_124all
theorem t6_125choices : plan7174.choices=[0,6,6,6,10,7].map (options 6 5) := by rfl


theorem t6_125part0 : t6_125jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_125frontier : t6_125root.frontier 0=t6_125jobs := by rfl
theorem t6_125all : t6_125jobs.all (Job.check tree)=true := by
  simp only [t6_125jobs,List.all_append,List.all_nil,t6_125part0,Bool.and_self]
theorem t6_125checked : Checked tree [0,6,6,6,10,7] := by
  refine ⟨plan7174,valid7174,t6_125choices,?_⟩
  exact check_of_frontier tree 0 t6_125root t6_125jobs t6_125frontier t6_125all
theorem t6_126choices : plan7175.choices=[0,6,6,6,10,10].map (options 6 5) := by rfl


theorem t6_126part0 : t6_126jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_126frontier : t6_126root.frontier 0=t6_126jobs := by rfl
theorem t6_126all : t6_126jobs.all (Job.check tree)=true := by
  simp only [t6_126jobs,List.all_append,List.all_nil,t6_126part0,Bool.and_self]
theorem t6_126checked : Checked tree [0,6,6,6,10,10] := by
  refine ⟨plan7175,valid7175,t6_126choices,?_⟩
  exact check_of_frontier tree 0 t6_126root t6_126jobs t6_126frontier t6_126all
theorem t6_127choices : plan7176.choices=[0,6,6,7,7,7].map (options 6 5) := by rfl


theorem t6_127part0 : t6_127jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_127frontier : t6_127root.frontier 0=t6_127jobs := by rfl
theorem t6_127all : t6_127jobs.all (Job.check tree)=true := by
  simp only [t6_127jobs,List.all_append,List.all_nil,t6_127part0,Bool.and_self]
theorem t6_127checked : Checked tree [0,6,6,7,7,7] := by
  refine ⟨plan7176,valid7176,t6_127choices,?_⟩
  exact check_of_frontier tree 0 t6_127root t6_127jobs t6_127frontier t6_127all
theorem t6_128choices : plan7177.choices=[0,6,6,10,7,7].map (options 6 5) := by rfl


theorem t6_128part0 : t6_128jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_128frontier : t6_128root.frontier 0=t6_128jobs := by rfl
theorem t6_128all : t6_128jobs.all (Job.check tree)=true := by
  simp only [t6_128jobs,List.all_append,List.all_nil,t6_128part0,Bool.and_self]
theorem t6_128checked : Checked tree [0,6,6,10,7,7] := by
  refine ⟨plan7177,valid7177,t6_128choices,?_⟩
  exact check_of_frontier tree 0 t6_128root t6_128jobs t6_128frontier t6_128all
theorem t6_129choices : plan7178.choices=[0,6,6,10,10,7].map (options 6 5) := by rfl


theorem t6_129part0 : t6_129jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_129frontier : t6_129root.frontier 0=t6_129jobs := by rfl
theorem t6_129all : t6_129jobs.all (Job.check tree)=true := by
  simp only [t6_129jobs,List.all_append,List.all_nil,t6_129part0,Bool.and_self]
theorem t6_129checked : Checked tree [0,6,6,10,10,7] := by
  refine ⟨plan7178,valid7178,t6_129choices,?_⟩
  exact check_of_frontier tree 0 t6_129root t6_129jobs t6_129frontier t6_129all
theorem t6_130choices : plan7179.choices=[0,6,6,10,10,10].map (options 6 5) := by rfl


theorem t6_130part0 : t6_130jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_130frontier : t6_130root.frontier 0=t6_130jobs := by rfl
theorem t6_130all : t6_130jobs.all (Job.check tree)=true := by
  simp only [t6_130jobs,List.all_append,List.all_nil,t6_130part0,Bool.and_self]
theorem t6_130checked : Checked tree [0,6,6,10,10,10] := by
  refine ⟨plan7179,valid7179,t6_130choices,?_⟩
  exact check_of_frontier tree 0 t6_130root t6_130jobs t6_130frontier t6_130all
theorem t6_131choices : plan7180.choices=[0,6,7,7,7,7].map (options 6 5) := by rfl


theorem t6_131part0 : t6_131jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_131frontier : t6_131root.frontier 0=t6_131jobs := by rfl
theorem t6_131all : t6_131jobs.all (Job.check tree)=true := by
  simp only [t6_131jobs,List.all_append,List.all_nil,t6_131part0,Bool.and_self]
theorem t6_131checked : Checked tree [0,6,7,7,7,7] := by
  refine ⟨plan7180,valid7180,t6_131choices,?_⟩
  exact check_of_frontier tree 0 t6_131root t6_131jobs t6_131frontier t6_131all
theorem t6_132choices : plan7181.choices=[0,6,10,7,7,7].map (options 6 5) := by rfl


theorem t6_132part0 : t6_132jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_132frontier : t6_132root.frontier 0=t6_132jobs := by rfl
theorem t6_132all : t6_132jobs.all (Job.check tree)=true := by
  simp only [t6_132jobs,List.all_append,List.all_nil,t6_132part0,Bool.and_self]
theorem t6_132checked : Checked tree [0,6,10,7,7,7] := by
  refine ⟨plan7181,valid7181,t6_132choices,?_⟩
  exact check_of_frontier tree 0 t6_132root t6_132jobs t6_132frontier t6_132all
theorem t6_133choices : plan7182.choices=[0,6,10,10,7,7].map (options 6 5) := by rfl


theorem t6_133part0 : t6_133jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_133frontier : t6_133root.frontier 0=t6_133jobs := by rfl
theorem t6_133all : t6_133jobs.all (Job.check tree)=true := by
  simp only [t6_133jobs,List.all_append,List.all_nil,t6_133part0,Bool.and_self]
theorem t6_133checked : Checked tree [0,6,10,10,7,7] := by
  refine ⟨plan7182,valid7182,t6_133choices,?_⟩
  exact check_of_frontier tree 0 t6_133root t6_133jobs t6_133frontier t6_133all
theorem t6_134choices : plan7183.choices=[0,6,10,10,10,7].map (options 6 5) := by rfl


theorem t6_134part0 : t6_134jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_134frontier : t6_134root.frontier 0=t6_134jobs := by rfl
theorem t6_134all : t6_134jobs.all (Job.check tree)=true := by
  simp only [t6_134jobs,List.all_append,List.all_nil,t6_134part0,Bool.and_self]
theorem t6_134checked : Checked tree [0,6,10,10,10,7] := by
  refine ⟨plan7183,valid7183,t6_134choices,?_⟩
  exact check_of_frontier tree 0 t6_134root t6_134jobs t6_134frontier t6_134all
theorem t6_135choices : plan7184.choices=[0,6,10,10,10,10].map (options 6 5) := by rfl


theorem t6_135part0 : t6_135jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_135frontier : t6_135root.frontier 0=t6_135jobs := by rfl
theorem t6_135all : t6_135jobs.all (Job.check tree)=true := by
  simp only [t6_135jobs,List.all_append,List.all_nil,t6_135part0,Bool.and_self]
theorem t6_135checked : Checked tree [0,6,10,10,10,10] := by
  refine ⟨plan7184,valid7184,t6_135choices,?_⟩
  exact check_of_frontier tree 0 t6_135root t6_135jobs t6_135frontier t6_135all
theorem t6_136choices : plan7185.choices=[0,7,7,7,7,7].map (options 6 5) := by rfl


theorem t6_136part0 : t6_136jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_136frontier : t6_136root.frontier 0=t6_136jobs := by rfl
theorem t6_136all : t6_136jobs.all (Job.check tree)=true := by
  simp only [t6_136jobs,List.all_append,List.all_nil,t6_136part0,Bool.and_self]
theorem t6_136checked : Checked tree [0,7,7,7,7,7] := by
  refine ⟨plan7185,valid7185,t6_136choices,?_⟩
  exact check_of_frontier tree 0 t6_136root t6_136jobs t6_136frontier t6_136all
theorem t6_137choices : plan6745.choices=[0,8,2,7,7,7].map (options 6 4) := by rfl


theorem t6_137part0 : t6_137jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_137frontier : t6_137root.frontier 0=t6_137jobs := by rfl
theorem t6_137all : t6_137jobs.all (Job.check tree)=true := by
  simp only [t6_137jobs,List.all_append,List.all_nil,t6_137part0,Bool.and_self]
theorem t6_137checked : Checked tree [0,8,2,7,7,7] := by
  refine ⟨plan6745,valid6745,t6_137choices,?_⟩
  exact check_of_frontier tree 0 t6_137root t6_137jobs t6_137frontier t6_137all
theorem t6_138choices : plan6463.choices=[0,8,3,3,7,7].map (options 6 3) := by rfl


theorem t6_138part0 : t6_138jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_138frontier : t6_138root.frontier 0=t6_138jobs := by rfl
theorem t6_138all : t6_138jobs.all (Job.check tree)=true := by
  simp only [t6_138jobs,List.all_append,List.all_nil,t6_138part0,Bool.and_self]
theorem t6_138checked : Checked tree [0,8,3,3,7,7] := by
  refine ⟨plan6463,valid6463,t6_138choices,?_⟩
  exact check_of_frontier tree 0 t6_138root t6_138jobs t6_138frontier t6_138all
theorem t6_139choices : plan6746.choices=[0,8,3,6,7,7].map (options 6 4) := by rfl


theorem t6_139part0 : t6_139jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_139frontier : t6_139root.frontier 0=t6_139jobs := by rfl
theorem t6_139all : t6_139jobs.all (Job.check tree)=true := by
  simp only [t6_139jobs,List.all_append,List.all_nil,t6_139part0,Bool.and_self]
theorem t6_139checked : Checked tree [0,8,3,6,7,7] := by
  refine ⟨plan6746,valid6746,t6_139choices,?_⟩
  exact check_of_frontier tree 0 t6_139root t6_139jobs t6_139frontier t6_139all
theorem t6_140choices : plan6747.choices=[0,8,3,7,7,7].map (options 6 4) := by rfl


theorem t6_140part0 : t6_140jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_140frontier : t6_140root.frontier 0=t6_140jobs := by rfl
theorem t6_140all : t6_140jobs.all (Job.check tree)=true := by
  simp only [t6_140jobs,List.all_append,List.all_nil,t6_140part0,Bool.and_self]
theorem t6_140checked : Checked tree [0,8,3,7,7,7] := by
  refine ⟨plan6747,valid6747,t6_140choices,?_⟩
  exact check_of_frontier tree 0 t6_140root t6_140jobs t6_140frontier t6_140all
theorem t6_141choices : plan6748.choices=[0,8,3,10,7,7].map (options 6 4) := by rfl


theorem t6_141part0 : t6_141jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_141frontier : t6_141root.frontier 0=t6_141jobs := by rfl
theorem t6_141all : t6_141jobs.all (Job.check tree)=true := by
  simp only [t6_141jobs,List.all_append,List.all_nil,t6_141part0,Bool.and_self]
theorem t6_141checked : Checked tree [0,8,3,10,7,7] := by
  refine ⟨plan6748,valid6748,t6_141choices,?_⟩
  exact check_of_frontier tree 0 t6_141root t6_141jobs t6_141frontier t6_141all
theorem t6_142choices : plan7186.choices=[0,8,5,7,7,7].map (options 6 5) := by rfl


theorem t6_142part0 : t6_142jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_142frontier : t6_142root.frontier 0=t6_142jobs := by rfl
theorem t6_142all : t6_142jobs.all (Job.check tree)=true := by
  simp only [t6_142jobs,List.all_append,List.all_nil,t6_142part0,Bool.and_self]
theorem t6_142checked : Checked tree [0,8,5,7,7,7] := by
  refine ⟨plan7186,valid7186,t6_142choices,?_⟩
  exact check_of_frontier tree 0 t6_142root t6_142jobs t6_142frontier t6_142all
theorem t6_143choices : plan7187.choices=[0,8,6,6,7,7].map (options 6 5) := by rfl


theorem t6_143part0 : t6_143jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_143frontier : t6_143root.frontier 0=t6_143jobs := by rfl
theorem t6_143all : t6_143jobs.all (Job.check tree)=true := by
  simp only [t6_143jobs,List.all_append,List.all_nil,t6_143part0,Bool.and_self]
theorem t6_143checked : Checked tree [0,8,6,6,7,7] := by
  refine ⟨plan7187,valid7187,t6_143choices,?_⟩
  exact check_of_frontier tree 0 t6_143root t6_143jobs t6_143frontier t6_143all
theorem t6_144choices : plan7188.choices=[0,8,6,7,7,7].map (options 6 5) := by rfl


theorem t6_144part0 : t6_144jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_144frontier : t6_144root.frontier 0=t6_144jobs := by rfl
theorem t6_144all : t6_144jobs.all (Job.check tree)=true := by
  simp only [t6_144jobs,List.all_append,List.all_nil,t6_144part0,Bool.and_self]
theorem t6_144checked : Checked tree [0,8,6,7,7,7] := by
  refine ⟨plan7188,valid7188,t6_144choices,?_⟩
  exact check_of_frontier tree 0 t6_144root t6_144jobs t6_144frontier t6_144all
theorem t6_145choices : plan7189.choices=[0,8,6,10,7,7].map (options 6 5) := by rfl


theorem t6_145part0 : t6_145jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_145frontier : t6_145root.frontier 0=t6_145jobs := by rfl
theorem t6_145all : t6_145jobs.all (Job.check tree)=true := by
  simp only [t6_145jobs,List.all_append,List.all_nil,t6_145part0,Bool.and_self]
theorem t6_145checked : Checked tree [0,8,6,10,7,7] := by
  refine ⟨plan7189,valid7189,t6_145choices,?_⟩
  exact check_of_frontier tree 0 t6_145root t6_145jobs t6_145frontier t6_145all
theorem t6_146choices : plan7190.choices=[0,8,7,7,7,7].map (options 6 5) := by rfl


theorem t6_146part0 : t6_146jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_146frontier : t6_146root.frontier 0=t6_146jobs := by rfl
theorem t6_146all : t6_146jobs.all (Job.check tree)=true := by
  simp only [t6_146jobs,List.all_append,List.all_nil,t6_146part0,Bool.and_self]
theorem t6_146checked : Checked tree [0,8,7,7,7,7] := by
  refine ⟨plan7190,valid7190,t6_146choices,?_⟩
  exact check_of_frontier tree 0 t6_146root t6_146jobs t6_146frontier t6_146all
theorem t6_147choices : plan7191.choices=[0,8,9,7,7,7].map (options 6 5) := by rfl


theorem t6_147part0 : t6_147jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_147frontier : t6_147root.frontier 0=t6_147jobs := by rfl
theorem t6_147all : t6_147jobs.all (Job.check tree)=true := by
  simp only [t6_147jobs,List.all_append,List.all_nil,t6_147part0,Bool.and_self]
theorem t6_147checked : Checked tree [0,8,9,7,7,7] := by
  refine ⟨plan7191,valid7191,t6_147choices,?_⟩
  exact check_of_frontier tree 0 t6_147root t6_147jobs t6_147frontier t6_147all
theorem t6_148choices : plan7192.choices=[0,8,10,7,7,7].map (options 6 5) := by rfl


theorem t6_148part0 : t6_148jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_148frontier : t6_148root.frontier 0=t6_148jobs := by rfl
theorem t6_148all : t6_148jobs.all (Job.check tree)=true := by
  simp only [t6_148jobs,List.all_append,List.all_nil,t6_148part0,Bool.and_self]
theorem t6_148checked : Checked tree [0,8,10,7,7,7] := by
  refine ⟨plan7192,valid7192,t6_148choices,?_⟩
  exact check_of_frontier tree 0 t6_148root t6_148jobs t6_148frontier t6_148all
theorem t6_149choices : plan7193.choices=[0,8,10,10,7,7].map (options 6 5) := by rfl


theorem t6_149part0 : t6_149jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_149frontier : t6_149root.frontier 0=t6_149jobs := by rfl
theorem t6_149all : t6_149jobs.all (Job.check tree)=true := by
  simp only [t6_149jobs,List.all_append,List.all_nil,t6_149part0,Bool.and_self]
theorem t6_149checked : Checked tree [0,8,10,10,7,7] := by
  refine ⟨plan7193,valid7193,t6_149choices,?_⟩
  exact check_of_frontier tree 0 t6_149root t6_149jobs t6_149frontier t6_149all
theorem t6_150choices : plan6332.choices=[0,9,3,3,3,7].map (options 6 2) := by rfl


theorem t6_150part0 : t6_150jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_150frontier : t6_150root.frontier 0=t6_150jobs := by rfl
theorem t6_150all : t6_150jobs.all (Job.check tree)=true := by
  simp only [t6_150jobs,List.all_append,List.all_nil,t6_150part0,Bool.and_self]
theorem t6_150checked : Checked tree [0,9,3,3,3,7] := by
  refine ⟨plan6332,valid6332,t6_150choices,?_⟩
  exact check_of_frontier tree 0 t6_150root t6_150jobs t6_150frontier t6_150all
theorem t6_151choices : plan6464.choices=[0,9,3,3,6,7].map (options 6 3) := by rfl


theorem t6_151part0 : t6_151jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_151frontier : t6_151root.frontier 0=t6_151jobs := by rfl
theorem t6_151all : t6_151jobs.all (Job.check tree)=true := by
  simp only [t6_151jobs,List.all_append,List.all_nil,t6_151part0,Bool.and_self]
theorem t6_151checked : Checked tree [0,9,3,3,6,7] := by
  refine ⟨plan6464,valid6464,t6_151choices,?_⟩
  exact check_of_frontier tree 0 t6_151root t6_151jobs t6_151frontier t6_151all
theorem t6_152choices : plan6465.choices=[0,9,3,3,7,7].map (options 6 3) := by rfl


theorem t6_152part0 : t6_152jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_152frontier : t6_152root.frontier 0=t6_152jobs := by rfl
theorem t6_152all : t6_152jobs.all (Job.check tree)=true := by
  simp only [t6_152jobs,List.all_append,List.all_nil,t6_152part0,Bool.and_self]
theorem t6_152checked : Checked tree [0,9,3,3,7,7] := by
  refine ⟨plan6465,valid6465,t6_152choices,?_⟩
  exact check_of_frontier tree 0 t6_152root t6_152jobs t6_152frontier t6_152all
theorem t6_153choices : plan6466.choices=[0,9,3,3,10,7].map (options 6 3) := by rfl


theorem t6_153part0 : t6_153jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_153frontier : t6_153root.frontier 0=t6_153jobs := by rfl
theorem t6_153all : t6_153jobs.all (Job.check tree)=true := by
  simp only [t6_153jobs,List.all_append,List.all_nil,t6_153part0,Bool.and_self]
theorem t6_153checked : Checked tree [0,9,3,3,10,7] := by
  refine ⟨plan6466,valid6466,t6_153choices,?_⟩
  exact check_of_frontier tree 0 t6_153root t6_153jobs t6_153frontier t6_153all
theorem t6_154choices : plan6749.choices=[0,9,3,6,6,7].map (options 6 4) := by rfl


theorem t6_154part0 : t6_154jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_154frontier : t6_154root.frontier 0=t6_154jobs := by rfl
theorem t6_154all : t6_154jobs.all (Job.check tree)=true := by
  simp only [t6_154jobs,List.all_append,List.all_nil,t6_154part0,Bool.and_self]
theorem t6_154checked : Checked tree [0,9,3,6,6,7] := by
  refine ⟨plan6749,valid6749,t6_154choices,?_⟩
  exact check_of_frontier tree 0 t6_154root t6_154jobs t6_154frontier t6_154all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks048 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_34checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_47checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_48checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_49checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_50checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_51checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_52checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_53checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_54checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_55checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_56checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_35checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_57checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_58checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_59checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_60checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_61checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_62checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_63checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_64checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_65checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_66checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_36checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_67checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_68checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_69checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_70checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_71checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_72checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_73checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_74checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_75checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_76checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_37checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_77checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_78checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_79checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_80checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_81checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_82checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_83checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_84checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_85checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_86checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_38checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_87checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_88checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_89checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_90checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_91checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_92checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_93checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_94checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_95checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_96checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_39checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_97checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_98checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_99checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_100checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_101checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_102checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_103checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_104checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_105checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_106checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_40checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_107checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_108checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_109checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_110checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_111checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_112checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_113checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_114checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_115checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_116checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_41checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_117checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_118checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_119checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_120checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_121checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_122checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_123checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_124checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_125checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_42checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_126checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_127checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_128checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_129checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_130checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_131checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_132checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_133checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_134checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_135checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_43checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_136checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_137checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_138checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_139checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_140checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_141checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_142checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_143checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_144checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_145checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_44checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_146checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_147checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_148checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_149checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_150checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_151checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_152checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_153checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_154checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_45checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_46checked⟩
