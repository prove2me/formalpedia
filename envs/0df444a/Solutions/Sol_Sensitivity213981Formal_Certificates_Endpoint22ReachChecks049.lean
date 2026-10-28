-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks049
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:10:14.068581+00:00
-- url     : https://prove2.me/submissions/40c75409-0c74-4e1b-b1c7-21853616db7c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks049
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks049
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans075
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



theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)





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











theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)



theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)







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



theorem valid1513 : plan1513.Valid := valid_step _ _ _ valid552 (by decide +kernel)











theorem valid1519 : plan1519.Valid := valid_step _ _ _ valid549 (by decide +kernel)

theorem valid1520 : plan1520.Valid := valid_step _ _ _ valid550 (by decide +kernel)

theorem valid1521 : plan1521.Valid := valid_step _ _ _ valid551 (by decide +kernel)

theorem valid1522 : plan1522.Valid := valid_step _ _ _ valid552 (by decide +kernel)

theorem valid1523 : plan1523.Valid := valid_step _ _ _ valid553 (by decide +kernel)

theorem valid1524 : plan1524.Valid := valid_step _ _ _ valid554 (by decide +kernel)





















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

















































































































































theorem valid3241 : plan3241.Valid := valid_step _ _ _ valid1506 (by decide +kernel)





theorem valid3244 : plan3244.Valid := valid_step _ _ _ valid1510 (by decide +kernel)





theorem valid3247 : plan3247.Valid := valid_step _ _ _ valid1509 (by decide +kernel)

theorem valid3248 : plan3248.Valid := valid_step _ _ _ valid1510 (by decide +kernel)

theorem valid3249 : plan3249.Valid := valid_step _ _ _ valid1511 (by decide +kernel)







theorem valid3253 : plan3253.Valid := valid_step _ _ _ valid1513 (by decide +kernel)







theorem valid3257 : plan3257.Valid := valid_step _ _ _ valid1520 (by decide +kernel)



theorem valid3259 : plan3259.Valid := valid_step _ _ _ valid1522 (by decide +kernel)

theorem valid3260 : plan3260.Valid := valid_step _ _ _ valid1523 (by decide +kernel)








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







theorem valid1540 : plan1540.Valid := valid_step _ _ _ valid562 (by decide +kernel)



theorem valid1542 : plan1542.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1543 : plan1543.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1544 : plan1544.Valid := valid_step _ _ _ valid561 (by decide +kernel)

theorem valid1545 : plan1545.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1546 : plan1546.Valid := valid_step _ _ _ valid563 (by decide +kernel)



theorem valid1548 : plan1548.Valid := valid_step _ _ _ valid562 (by decide +kernel)





theorem valid1551 : plan1551.Valid := valid_step _ _ _ valid562 (by decide +kernel)



theorem valid1553 : plan1553.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1554 : plan1554.Valid := valid_step _ _ _ valid563 (by decide +kernel)















theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)















theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)



theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)



theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)









theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)

























theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)



theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)



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







theorem valid3268 : plan3268.Valid := valid_step _ _ _ valid1519 (by decide +kernel)

theorem valid3269 : plan3269.Valid := valid_step _ _ _ valid1520 (by decide +kernel)

theorem valid3270 : plan3270.Valid := valid_step _ _ _ valid1521 (by decide +kernel)

theorem valid3271 : plan3271.Valid := valid_step _ _ _ valid1522 (by decide +kernel)

theorem valid3272 : plan3272.Valid := valid_step _ _ _ valid1523 (by decide +kernel)

theorem valid3273 : plan3273.Valid := valid_step _ _ _ valid1524 (by decide +kernel)

















theorem valid3282 : plan3282.Valid := valid_step _ _ _ valid1548 (by decide +kernel)











theorem valid3288 : plan3288.Valid := valid_step _ _ _ valid1540 (by decide +kernel)





theorem valid3291 : plan3291.Valid := valid_step _ _ _ valid1543 (by decide +kernel)



theorem valid3293 : plan3293.Valid := valid_step _ _ _ valid1545 (by decide +kernel)

theorem valid3294 : plan3294.Valid := valid_step _ _ _ valid1546 (by decide +kernel)



theorem valid3296 : plan3296.Valid := valid_step _ _ _ valid1548 (by decide +kernel)



theorem valid3298 : plan3298.Valid := valid_step _ _ _ valid1551 (by decide +kernel)



theorem valid3300 : plan3300.Valid := valid_step _ _ _ valid1553 (by decide +kernel)

theorem valid3301 : plan3301.Valid := valid_step _ _ _ valid1554 (by decide +kernel)





















theorem valid3312 : plan3312.Valid := valid_step _ _ _ valid1542 (by decide +kernel)

theorem valid3313 : plan3313.Valid := valid_step _ _ _ valid1543 (by decide +kernel)

theorem valid3314 : plan3314.Valid := valid_step _ _ _ valid1544 (by decide +kernel)

theorem valid3315 : plan3315.Valid := valid_step _ _ _ valid1545 (by decide +kernel)

theorem valid3316 : plan3316.Valid := valid_step _ _ _ valid1546 (by decide +kernel)



theorem valid3318 : plan3318.Valid := valid_step _ _ _ valid1548 (by decide +kernel)

theorem valid3319 : plan3319.Valid := valid_step _ _ _ valid1553 (by decide +kernel)

theorem valid3320 : plan3320.Valid := valid_step _ _ _ valid1554 (by decide +kernel)

















theorem valid3329 : plan3329.Valid := valid_step _ _ _ valid1535 (by decide +kernel)























theorem valid3341 : plan3341.Valid := valid_step _ _ _ valid1535 (by decide +kernel)






































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





























































































































theorem valid5343 : plan5343.Valid := valid_step _ _ _ valid3241 (by decide +kernel)



theorem valid5345 : plan5345.Valid := valid_step _ _ _ valid3248 (by decide +kernel)





theorem valid5348 : plan5348.Valid := valid_step _ _ _ valid3244 (by decide +kernel)





theorem valid5351 : plan5351.Valid := valid_step _ _ _ valid3247 (by decide +kernel)

theorem valid5352 : plan5352.Valid := valid_step _ _ _ valid3248 (by decide +kernel)

theorem valid5353 : plan5353.Valid := valid_step _ _ _ valid3249 (by decide +kernel)

















theorem valid5362 : plan5362.Valid := valid_step _ _ _ valid3259 (by decide +kernel)

theorem valid5363 : plan5363.Valid := valid_step _ _ _ valid3269 (by decide +kernel)

theorem valid5364 : plan5364.Valid := valid_step _ _ _ valid3271 (by decide +kernel)

theorem valid5365 : plan5365.Valid := valid_step _ _ _ valid3272 (by decide +kernel)



theorem valid5367 : plan5367.Valid := valid_step _ _ _ valid3253 (by decide +kernel)







theorem valid5371 : plan5371.Valid := valid_step _ _ _ valid3257 (by decide +kernel)



theorem valid5373 : plan5373.Valid := valid_step _ _ _ valid3259 (by decide +kernel)

theorem valid5374 : plan5374.Valid := valid_step _ _ _ valid3260 (by decide +kernel)




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









theorem valid5381 : plan5381.Valid := valid_step _ _ _ valid3268 (by decide +kernel)

theorem valid5382 : plan5382.Valid := valid_step _ _ _ valid3269 (by decide +kernel)

theorem valid5383 : plan5383.Valid := valid_step _ _ _ valid3270 (by decide +kernel)

theorem valid5384 : plan5384.Valid := valid_step _ _ _ valid3271 (by decide +kernel)

theorem valid5385 : plan5385.Valid := valid_step _ _ _ valid3272 (by decide +kernel)

theorem valid5386 : plan5386.Valid := valid_step _ _ _ valid3273 (by decide +kernel)

























































theorem valid5415 : plan5415.Valid := valid_step _ _ _ valid3282 (by decide +kernel)

theorem valid5416 : plan5416.Valid := valid_step _ _ _ valid3293 (by decide +kernel)

theorem valid5417 : plan5417.Valid := valid_step _ _ _ valid3296 (by decide +kernel)

theorem valid5418 : plan5418.Valid := valid_step _ _ _ valid3300 (by decide +kernel)

theorem valid5419 : plan5419.Valid := valid_step _ _ _ valid3313 (by decide +kernel)

theorem valid5420 : plan5420.Valid := valid_step _ _ _ valid3315 (by decide +kernel)

theorem valid5421 : plan5421.Valid := valid_step _ _ _ valid3316 (by decide +kernel)

theorem valid5422 : plan5422.Valid := valid_step _ _ _ valid3318 (by decide +kernel)

theorem valid5423 : plan5423.Valid := valid_step _ _ _ valid3319 (by decide +kernel)

theorem valid5424 : plan5424.Valid := valid_step _ _ _ valid3320 (by decide +kernel)

theorem valid5425 : plan5425.Valid := valid_step _ _ _ valid3329 (by decide +kernel)

theorem valid5426 : plan5426.Valid := valid_step _ _ _ valid3341 (by decide +kernel)











theorem valid5432 : plan5432.Valid := valid_step _ _ _ valid3288 (by decide +kernel)





theorem valid5435 : plan5435.Valid := valid_step _ _ _ valid3291 (by decide +kernel)



theorem valid5437 : plan5437.Valid := valid_step _ _ _ valid3293 (by decide +kernel)

theorem valid5438 : plan5438.Valid := valid_step _ _ _ valid3294 (by decide +kernel)



theorem valid5440 : plan5440.Valid := valid_step _ _ _ valid3296 (by decide +kernel)



theorem valid5442 : plan5442.Valid := valid_step _ _ _ valid3298 (by decide +kernel)



theorem valid5444 : plan5444.Valid := valid_step _ _ _ valid3300 (by decide +kernel)

theorem valid5445 : plan5445.Valid := valid_step _ _ _ valid3301 (by decide +kernel)















theorem valid5453 : plan5453.Valid := valid_step _ _ _ valid3312 (by decide +kernel)

theorem valid5454 : plan5454.Valid := valid_step _ _ _ valid3313 (by decide +kernel)

theorem valid5455 : plan5455.Valid := valid_step _ _ _ valid3314 (by decide +kernel)


































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









































































theorem valid6277 : plan6277.Valid := valid_step _ _ _ valid5343 (by decide +kernel)



















theorem valid6287 : plan6287.Valid := valid_step _ _ _ valid5345 (by decide +kernel)

theorem valid6288 : plan6288.Valid := valid_step _ _ _ valid5348 (by decide +kernel)

theorem valid6289 : plan6289.Valid := valid_step _ _ _ valid5351 (by decide +kernel)

theorem valid6290 : plan6290.Valid := valid_step _ _ _ valid5352 (by decide +kernel)

theorem valid6291 : plan6291.Valid := valid_step _ _ _ valid5353 (by decide +kernel)



















































































theorem valid6333 : plan6333.Valid := valid_step _ _ _ valid5362 (by decide +kernel)

theorem valid6334 : plan6334.Valid := valid_step _ _ _ valid5363 (by decide +kernel)

theorem valid6335 : plan6335.Valid := valid_step _ _ _ valid5364 (by decide +kernel)

theorem valid6336 : plan6336.Valid := valid_step _ _ _ valid5365 (by decide +kernel)
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





theorem valid3363 : plan3363.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3364 : plan3364.Valid := valid_step _ _ _ valid1573 (by decide +kernel)



theorem valid3366 : plan3366.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3367 : plan3367.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3368 : plan3368.Valid := valid_step _ _ _ valid1581 (by decide +kernel)



theorem valid3370 : plan3370.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

































theorem valid3387 : plan3387.Valid := valid_step _ _ _ valid1572 (by decide +kernel)





theorem valid3390 : plan3390.Valid := valid_step _ _ _ valid1575 (by decide +kernel)









theorem valid3395 : plan3395.Valid := valid_step _ _ _ valid1580 (by decide +kernel)







theorem valid3399 : plan3399.Valid := valid_step _ _ _ valid1570 (by decide +kernel)



theorem valid3401 : plan3401.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3402 : plan3402.Valid := valid_step _ _ _ valid1573 (by decide +kernel)



theorem valid3404 : plan3404.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3405 : plan3405.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3406 : plan3406.Valid := valid_step _ _ _ valid1581 (by decide +kernel)



theorem valid3408 : plan3408.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3409 : plan3409.Valid := valid_step _ _ _ valid1575 (by decide +kernel)













theorem valid3416 : plan3416.Valid := valid_step _ _ _ valid1562 (by decide +kernel)











theorem valid3422 : plan3422.Valid := valid_step _ _ _ valid1572 (by decide +kernel)





theorem valid3425 : plan3425.Valid := valid_step _ _ _ valid1575 (by decide +kernel)









theorem valid3430 : plan3430.Valid := valid_step _ _ _ valid1580 (by decide +kernel)





theorem valid3433 : plan3433.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3434 : plan3434.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3435 : plan3435.Valid := valid_step _ _ _ valid1581 (by decide +kernel)










































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































































































































theorem valid5536 : plan5536.Valid := valid_step _ _ _ valid3370 (by decide +kernel)

theorem valid5537 : plan5537.Valid := valid_step _ _ _ valid3387 (by decide +kernel)

theorem valid5538 : plan5538.Valid := valid_step _ _ _ valid3390 (by decide +kernel)

theorem valid5539 : plan5539.Valid := valid_step _ _ _ valid3395 (by decide +kernel)

theorem valid5540 : plan5540.Valid := valid_step _ _ _ valid3399 (by decide +kernel)

theorem valid5541 : plan5541.Valid := valid_step _ _ _ valid3401 (by decide +kernel)

theorem valid5542 : plan5542.Valid := valid_step _ _ _ valid3402 (by decide +kernel)

theorem valid5543 : plan5543.Valid := valid_step _ _ _ valid3404 (by decide +kernel)

theorem valid5544 : plan5544.Valid := valid_step _ _ _ valid3405 (by decide +kernel)

theorem valid5545 : plan5545.Valid := valid_step _ _ _ valid3406 (by decide +kernel)

theorem valid5546 : plan5546.Valid := valid_step _ _ _ valid3408 (by decide +kernel)

theorem valid5547 : plan5547.Valid := valid_step _ _ _ valid3409 (by decide +kernel)

theorem valid5548 : plan5548.Valid := valid_step _ _ _ valid3422 (by decide +kernel)

theorem valid5549 : plan5549.Valid := valid_step _ _ _ valid3425 (by decide +kernel)

theorem valid5550 : plan5550.Valid := valid_step _ _ _ valid3430 (by decide +kernel)

theorem valid5551 : plan5551.Valid := valid_step _ _ _ valid3433 (by decide +kernel)

theorem valid5552 : plan5552.Valid := valid_step _ _ _ valid3434 (by decide +kernel)

theorem valid5553 : plan5553.Valid := valid_step _ _ _ valid3435 (by decide +kernel)






























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





































































theorem valid6467 : plan6467.Valid := valid_step _ _ _ valid5415 (by decide +kernel)

theorem valid6468 : plan6468.Valid := valid_step _ _ _ valid5416 (by decide +kernel)

theorem valid6469 : plan6469.Valid := valid_step _ _ _ valid5417 (by decide +kernel)

theorem valid6470 : plan6470.Valid := valid_step _ _ _ valid5418 (by decide +kernel)

theorem valid6471 : plan6471.Valid := valid_step _ _ _ valid5419 (by decide +kernel)

theorem valid6472 : plan6472.Valid := valid_step _ _ _ valid5420 (by decide +kernel)

theorem valid6473 : plan6473.Valid := valid_step _ _ _ valid5421 (by decide +kernel)

theorem valid6474 : plan6474.Valid := valid_step _ _ _ valid5422 (by decide +kernel)

theorem valid6475 : plan6475.Valid := valid_step _ _ _ valid5423 (by decide +kernel)

theorem valid6476 : plan6476.Valid := valid_step _ _ _ valid5424 (by decide +kernel)

theorem valid6477 : plan6477.Valid := valid_step _ _ _ valid5425 (by decide +kernel)

theorem valid6478 : plan6478.Valid := valid_step _ _ _ valid5426 (by decide +kernel)

theorem valid6479 : plan6479.Valid := valid_step _ _ _ valid5432 (by decide +kernel)

theorem valid6480 : plan6480.Valid := valid_step _ _ _ valid5435 (by decide +kernel)

theorem valid6481 : plan6481.Valid := valid_step _ _ _ valid5437 (by decide +kernel)

theorem valid6482 : plan6482.Valid := valid_step _ _ _ valid5438 (by decide +kernel)

theorem valid6483 : plan6483.Valid := valid_step _ _ _ valid5440 (by decide +kernel)

theorem valid6484 : plan6484.Valid := valid_step _ _ _ valid5442 (by decide +kernel)

theorem valid6485 : plan6485.Valid := valid_step _ _ _ valid5444 (by decide +kernel)

theorem valid6486 : plan6486.Valid := valid_step _ _ _ valid5445 (by decide +kernel)

theorem valid6487 : plan6487.Valid := valid_step _ _ _ valid5453 (by decide +kernel)

theorem valid6488 : plan6488.Valid := valid_step _ _ _ valid5454 (by decide +kernel)

theorem valid6489 : plan6489.Valid := valid_step _ _ _ valid5455 (by decide +kernel)














































































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







































theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)



theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)



theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)



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





















































































































theorem valid5723 : plan5723.Valid := valid_step _ _ _ valid3363 (by decide +kernel)

theorem valid5724 : plan5724.Valid := valid_step _ _ _ valid3364 (by decide +kernel)



theorem valid5726 : plan5726.Valid := valid_step _ _ _ valid3366 (by decide +kernel)

theorem valid5727 : plan5727.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5728 : plan5728.Valid := valid_step _ _ _ valid3368 (by decide +kernel)















theorem valid5736 : plan5736.Valid := valid_step _ _ _ valid3416 (by decide +kernel)
















































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



























































theorem valid6750 : plan6750.Valid := valid_step _ _ _ valid5723 (by decide +kernel)

theorem valid6751 : plan6751.Valid := valid_step _ _ _ valid5724 (by decide +kernel)

theorem valid6752 : plan6752.Valid := valid_step _ _ _ valid5726 (by decide +kernel)

theorem valid6753 : plan6753.Valid := valid_step _ _ _ valid5727 (by decide +kernel)

theorem valid6754 : plan6754.Valid := valid_step _ _ _ valid5728 (by decide +kernel)

theorem valid6755 : plan6755.Valid := valid_step _ _ _ valid5736 (by decide +kernel)

theorem valid6756 : plan6756.Valid := valid_step _ _ _ valid5536 (by decide +kernel)

theorem valid6757 : plan6757.Valid := valid_step _ _ _ valid5537 (by decide +kernel)

theorem valid6758 : plan6758.Valid := valid_step _ _ _ valid5538 (by decide +kernel)

theorem valid6759 : plan6759.Valid := valid_step _ _ _ valid5539 (by decide +kernel)

theorem valid6760 : plan6760.Valid := valid_step _ _ _ valid5540 (by decide +kernel)

theorem valid6761 : plan6761.Valid := valid_step _ _ _ valid5541 (by decide +kernel)

theorem valid6762 : plan6762.Valid := valid_step _ _ _ valid5542 (by decide +kernel)

theorem valid6763 : plan6763.Valid := valid_step _ _ _ valid5543 (by decide +kernel)

theorem valid6764 : plan6764.Valid := valid_step _ _ _ valid5544 (by decide +kernel)

theorem valid6765 : plan6765.Valid := valid_step _ _ _ valid5545 (by decide +kernel)

theorem valid6766 : plan6766.Valid := valid_step _ _ _ valid5546 (by decide +kernel)

theorem valid6767 : plan6767.Valid := valid_step _ _ _ valid5547 (by decide +kernel)

theorem valid6768 : plan6768.Valid := valid_step _ _ _ valid5548 (by decide +kernel)

theorem valid6769 : plan6769.Valid := valid_step _ _ _ valid5549 (by decide +kernel)

theorem valid6770 : plan6770.Valid := valid_step _ _ _ valid5550 (by decide +kernel)

theorem valid6771 : plan6771.Valid := valid_step _ _ _ valid5551 (by decide +kernel)

theorem valid6772 : plan6772.Valid := valid_step _ _ _ valid5552 (by decide +kernel)

theorem valid6773 : plan6773.Valid := valid_step _ _ _ valid5553 (by decide +kernel)






















































































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



































































































































































theorem valid5938 : plan5938.Valid := valid_step _ _ _ valid3476 (by decide +kernel)



theorem valid5940 : plan5940.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5941 : plan5941.Valid := valid_step _ _ _ valid3479 (by decide +kernel)



theorem valid5943 : plan5943.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5944 : plan5944.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5945 : plan5945.Valid := valid_step _ _ _ valid3483 (by decide +kernel)



theorem valid5947 : plan5947.Valid := valid_step _ _ _ valid3485 (by decide +kernel)










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



















































































































































































theorem valid7194 : plan7194.Valid := valid_step _ _ _ valid5938 (by decide +kernel)

theorem valid7195 : plan7195.Valid := valid_step _ _ _ valid5940 (by decide +kernel)

theorem valid7196 : plan7196.Valid := valid_step _ _ _ valid5941 (by decide +kernel)

theorem valid7197 : plan7197.Valid := valid_step _ _ _ valid5943 (by decide +kernel)

theorem valid7198 : plan7198.Valid := valid_step _ _ _ valid5944 (by decide +kernel)

theorem valid7199 : plan7199.Valid := valid_step _ _ _ valid5945 (by decide +kernel)

theorem valid7200 : plan7200.Valid := valid_step _ _ _ valid5947 (by decide +kernel)
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

theorem valid6337 : plan6337.Valid := valid_step _ _ _ valid5367 (by decide +kernel)

theorem valid6338 : plan6338.Valid := valid_step _ _ _ valid5371 (by decide +kernel)

theorem valid6339 : plan6339.Valid := valid_step _ _ _ valid5373 (by decide +kernel)

theorem valid6340 : plan6340.Valid := valid_step _ _ _ valid5374 (by decide +kernel)

theorem valid6341 : plan6341.Valid := valid_step _ _ _ valid5381 (by decide +kernel)

theorem valid6342 : plan6342.Valid := valid_step _ _ _ valid5382 (by decide +kernel)

theorem valid6343 : plan6343.Valid := valid_step _ _ _ valid5383 (by decide +kernel)

theorem valid6344 : plan6344.Valid := valid_step _ _ _ valid5384 (by decide +kernel)

theorem valid6345 : plan6345.Valid := valid_step _ _ _ valid5385 (by decide +kernel)

theorem valid6346 : plan6346.Valid := valid_step _ _ _ valid5386 (by decide +kernel)












































































































































































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









theorem valid5957 : plan5957.Valid := valid_step _ _ _ valid3496 (by decide +kernel)





theorem valid5960 : plan5960.Valid := valid_step _ _ _ valid3499 (by decide +kernel)









theorem valid5965 : plan5965.Valid := valid_step _ _ _ valid3504 (by decide +kernel)





theorem valid5968 : plan5968.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5969 : plan5969.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5970 : plan5970.Valid := valid_step _ _ _ valid3509 (by decide +kernel)



theorem valid5972 : plan5972.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5973 : plan5973.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5974 : plan5974.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5975 : plan5975.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5976 : plan5976.Valid := valid_step _ _ _ valid3510 (by decide +kernel)
















































































































































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

theorem valid7201 : plan7201.Valid := valid_step _ _ _ valid5957 (by decide +kernel)

theorem valid7202 : plan7202.Valid := valid_step _ _ _ valid5960 (by decide +kernel)

theorem valid7203 : plan7203.Valid := valid_step _ _ _ valid5965 (by decide +kernel)

theorem valid7204 : plan7204.Valid := valid_step _ _ _ valid5968 (by decide +kernel)

theorem valid7205 : plan7205.Valid := valid_step _ _ _ valid5969 (by decide +kernel)

theorem valid7206 : plan7206.Valid := valid_step _ _ _ valid5970 (by decide +kernel)

theorem valid7207 : plan7207.Valid := valid_step _ _ _ valid5972 (by decide +kernel)

theorem valid7208 : plan7208.Valid := valid_step _ _ _ valid5973 (by decide +kernel)

theorem valid7209 : plan7209.Valid := valid_step _ _ _ valid5974 (by decide +kernel)

theorem valid7210 : plan7210.Valid := valid_step _ _ _ valid5975 (by decide +kernel)

theorem valid7211 : plan7211.Valid := valid_step _ _ _ valid5976 (by decide +kernel)










































































































































































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
theorem t6_155choices : plan6750.choices=[0,9,3,6,7,7].map (options 6 4) := by rfl


theorem t6_155part0 : t6_155jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_155frontier : t6_155root.frontier 0=t6_155jobs := by rfl
theorem t6_155all : t6_155jobs.all (Job.check tree)=true := by
  simp only [t6_155jobs,List.all_append,List.all_nil,t6_155part0,Bool.and_self]
theorem t6_155checked : Checked tree [0,9,3,6,7,7] := by
  refine ⟨plan6750,valid6750,t6_155choices,?_⟩
  exact check_of_frontier tree 0 t6_155root t6_155jobs t6_155frontier t6_155all
theorem t6_156choices : plan6751.choices=[0,9,3,6,10,7].map (options 6 4) := by rfl


theorem t6_156part0 : t6_156jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_156frontier : t6_156root.frontier 0=t6_156jobs := by rfl
theorem t6_156all : t6_156jobs.all (Job.check tree)=true := by
  simp only [t6_156jobs,List.all_append,List.all_nil,t6_156part0,Bool.and_self]
theorem t6_156checked : Checked tree [0,9,3,6,10,7] := by
  refine ⟨plan6751,valid6751,t6_156choices,?_⟩
  exact check_of_frontier tree 0 t6_156root t6_156jobs t6_156frontier t6_156all
theorem t6_157choices : plan6752.choices=[0,9,3,7,7,7].map (options 6 4) := by rfl


theorem t6_157part0 : t6_157jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_157frontier : t6_157root.frontier 0=t6_157jobs := by rfl
theorem t6_157all : t6_157jobs.all (Job.check tree)=true := by
  simp only [t6_157jobs,List.all_append,List.all_nil,t6_157part0,Bool.and_self]
theorem t6_157checked : Checked tree [0,9,3,7,7,7] := by
  refine ⟨plan6752,valid6752,t6_157choices,?_⟩
  exact check_of_frontier tree 0 t6_157root t6_157jobs t6_157frontier t6_157all
theorem t6_158choices : plan6753.choices=[0,9,3,10,7,7].map (options 6 4) := by rfl


theorem t6_158part0 : t6_158jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_158frontier : t6_158root.frontier 0=t6_158jobs := by rfl
theorem t6_158all : t6_158jobs.all (Job.check tree)=true := by
  simp only [t6_158jobs,List.all_append,List.all_nil,t6_158part0,Bool.and_self]
theorem t6_158checked : Checked tree [0,9,3,10,7,7] := by
  refine ⟨plan6753,valid6753,t6_158choices,?_⟩
  exact check_of_frontier tree 0 t6_158root t6_158jobs t6_158frontier t6_158all
theorem t6_159choices : plan6754.choices=[0,9,3,10,10,7].map (options 6 4) := by rfl


theorem t6_159part0 : t6_159jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_159frontier : t6_159root.frontier 0=t6_159jobs := by rfl
theorem t6_159all : t6_159jobs.all (Job.check tree)=true := by
  simp only [t6_159jobs,List.all_append,List.all_nil,t6_159part0,Bool.and_self]
theorem t6_159checked : Checked tree [0,9,3,10,10,7] := by
  refine ⟨plan6754,valid6754,t6_159choices,?_⟩
  exact check_of_frontier tree 0 t6_159root t6_159jobs t6_159frontier t6_159all
theorem t6_160choices : plan7194.choices=[0,9,6,6,6,7].map (options 6 5) := by rfl


theorem t6_160part0 : t6_160jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_160frontier : t6_160root.frontier 0=t6_160jobs := by rfl
theorem t6_160all : t6_160jobs.all (Job.check tree)=true := by
  simp only [t6_160jobs,List.all_append,List.all_nil,t6_160part0,Bool.and_self]
theorem t6_160checked : Checked tree [0,9,6,6,6,7] := by
  refine ⟨plan7194,valid7194,t6_160choices,?_⟩
  exact check_of_frontier tree 0 t6_160root t6_160jobs t6_160frontier t6_160all
theorem t6_161choices : plan7195.choices=[0,9,6,6,7,7].map (options 6 5) := by rfl


theorem t6_161part0 : t6_161jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_161frontier : t6_161root.frontier 0=t6_161jobs := by rfl
theorem t6_161all : t6_161jobs.all (Job.check tree)=true := by
  simp only [t6_161jobs,List.all_append,List.all_nil,t6_161part0,Bool.and_self]
theorem t6_161checked : Checked tree [0,9,6,6,7,7] := by
  refine ⟨plan7195,valid7195,t6_161choices,?_⟩
  exact check_of_frontier tree 0 t6_161root t6_161jobs t6_161frontier t6_161all
theorem t6_162choices : plan7196.choices=[0,9,6,6,10,7].map (options 6 5) := by rfl


theorem t6_162part0 : t6_162jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_162frontier : t6_162root.frontier 0=t6_162jobs := by rfl
theorem t6_162all : t6_162jobs.all (Job.check tree)=true := by
  simp only [t6_162jobs,List.all_append,List.all_nil,t6_162part0,Bool.and_self]
theorem t6_162checked : Checked tree [0,9,6,6,10,7] := by
  refine ⟨plan7196,valid7196,t6_162choices,?_⟩
  exact check_of_frontier tree 0 t6_162root t6_162jobs t6_162frontier t6_162all
theorem t6_163choices : plan7197.choices=[0,9,6,7,7,7].map (options 6 5) := by rfl


theorem t6_163part0 : t6_163jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_163frontier : t6_163root.frontier 0=t6_163jobs := by rfl
theorem t6_163all : t6_163jobs.all (Job.check tree)=true := by
  simp only [t6_163jobs,List.all_append,List.all_nil,t6_163part0,Bool.and_self]
theorem t6_163checked : Checked tree [0,9,6,7,7,7] := by
  refine ⟨plan7197,valid7197,t6_163choices,?_⟩
  exact check_of_frontier tree 0 t6_163root t6_163jobs t6_163frontier t6_163all
theorem t6_164choices : plan7198.choices=[0,9,6,10,7,7].map (options 6 5) := by rfl


theorem t6_164part0 : t6_164jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_164frontier : t6_164root.frontier 0=t6_164jobs := by rfl
theorem t6_164all : t6_164jobs.all (Job.check tree)=true := by
  simp only [t6_164jobs,List.all_append,List.all_nil,t6_164part0,Bool.and_self]
theorem t6_164checked : Checked tree [0,9,6,10,7,7] := by
  refine ⟨plan7198,valid7198,t6_164choices,?_⟩
  exact check_of_frontier tree 0 t6_164root t6_164jobs t6_164frontier t6_164all
theorem t6_165choices : plan7199.choices=[0,9,6,10,10,7].map (options 6 5) := by rfl


theorem t6_165part0 : t6_165jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_165frontier : t6_165root.frontier 0=t6_165jobs := by rfl
theorem t6_165all : t6_165jobs.all (Job.check tree)=true := by
  simp only [t6_165jobs,List.all_append,List.all_nil,t6_165part0,Bool.and_self]
theorem t6_165checked : Checked tree [0,9,6,10,10,7] := by
  refine ⟨plan7199,valid7199,t6_165choices,?_⟩
  exact check_of_frontier tree 0 t6_165root t6_165jobs t6_165frontier t6_165all
theorem t6_166choices : plan7200.choices=[0,9,7,7,7,7].map (options 6 5) := by rfl


theorem t6_166part0 : t6_166jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_166frontier : t6_166root.frontier 0=t6_166jobs := by rfl
theorem t6_166all : t6_166jobs.all (Job.check tree)=true := by
  simp only [t6_166jobs,List.all_append,List.all_nil,t6_166part0,Bool.and_self]
theorem t6_166checked : Checked tree [0,9,7,7,7,7] := by
  refine ⟨plan7200,valid7200,t6_166choices,?_⟩
  exact check_of_frontier tree 0 t6_166root t6_166jobs t6_166frontier t6_166all
theorem t6_167choices : plan6755.choices=[0,9,9,3,7,7].map (options 6 4) := by rfl


theorem t6_167part0 : t6_167jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_167frontier : t6_167root.frontier 0=t6_167jobs := by rfl
theorem t6_167all : t6_167jobs.all (Job.check tree)=true := by
  simp only [t6_167jobs,List.all_append,List.all_nil,t6_167part0,Bool.and_self]
theorem t6_167checked : Checked tree [0,9,9,3,7,7] := by
  refine ⟨plan6755,valid6755,t6_167choices,?_⟩
  exact check_of_frontier tree 0 t6_167root t6_167jobs t6_167frontier t6_167all
theorem t6_168choices : plan7201.choices=[0,9,9,6,7,7].map (options 6 5) := by rfl


theorem t6_168part0 : t6_168jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_168frontier : t6_168root.frontier 0=t6_168jobs := by rfl
theorem t6_168all : t6_168jobs.all (Job.check tree)=true := by
  simp only [t6_168jobs,List.all_append,List.all_nil,t6_168part0,Bool.and_self]
theorem t6_168checked : Checked tree [0,9,9,6,7,7] := by
  refine ⟨plan7201,valid7201,t6_168choices,?_⟩
  exact check_of_frontier tree 0 t6_168root t6_168jobs t6_168frontier t6_168all
theorem t6_169choices : plan7202.choices=[0,9,9,7,7,7].map (options 6 5) := by rfl


theorem t6_169part0 : t6_169jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_169frontier : t6_169root.frontier 0=t6_169jobs := by rfl
theorem t6_169all : t6_169jobs.all (Job.check tree)=true := by
  simp only [t6_169jobs,List.all_append,List.all_nil,t6_169part0,Bool.and_self]
theorem t6_169checked : Checked tree [0,9,9,7,7,7] := by
  refine ⟨plan7202,valid7202,t6_169choices,?_⟩
  exact check_of_frontier tree 0 t6_169root t6_169jobs t6_169frontier t6_169all
theorem t6_170choices : plan7203.choices=[0,9,9,10,7,7].map (options 6 5) := by rfl


theorem t6_170part0 : t6_170jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_170frontier : t6_170root.frontier 0=t6_170jobs := by rfl
theorem t6_170all : t6_170jobs.all (Job.check tree)=true := by
  simp only [t6_170jobs,List.all_append,List.all_nil,t6_170part0,Bool.and_self]
theorem t6_170checked : Checked tree [0,9,9,10,7,7] := by
  refine ⟨plan7203,valid7203,t6_170choices,?_⟩
  exact check_of_frontier tree 0 t6_170root t6_170jobs t6_170frontier t6_170all
theorem t6_171choices : plan7204.choices=[0,9,10,7,7,7].map (options 6 5) := by rfl


theorem t6_171part0 : t6_171jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_171frontier : t6_171root.frontier 0=t6_171jobs := by rfl
theorem t6_171all : t6_171jobs.all (Job.check tree)=true := by
  simp only [t6_171jobs,List.all_append,List.all_nil,t6_171part0,Bool.and_self]
theorem t6_171checked : Checked tree [0,9,10,7,7,7] := by
  refine ⟨plan7204,valid7204,t6_171choices,?_⟩
  exact check_of_frontier tree 0 t6_171root t6_171jobs t6_171frontier t6_171all
theorem t6_172choices : plan7205.choices=[0,9,10,10,7,7].map (options 6 5) := by rfl


theorem t6_172part0 : t6_172jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_172frontier : t6_172root.frontier 0=t6_172jobs := by rfl
theorem t6_172all : t6_172jobs.all (Job.check tree)=true := by
  simp only [t6_172jobs,List.all_append,List.all_nil,t6_172part0,Bool.and_self]
theorem t6_172checked : Checked tree [0,9,10,10,7,7] := by
  refine ⟨plan7205,valid7205,t6_172choices,?_⟩
  exact check_of_frontier tree 0 t6_172root t6_172jobs t6_172frontier t6_172all
theorem t6_173choices : plan7206.choices=[0,9,10,10,10,7].map (options 6 5) := by rfl


theorem t6_173part0 : t6_173jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_173frontier : t6_173root.frontier 0=t6_173jobs := by rfl
theorem t6_173all : t6_173jobs.all (Job.check tree)=true := by
  simp only [t6_173jobs,List.all_append,List.all_nil,t6_173part0,Bool.and_self]
theorem t6_173checked : Checked tree [0,9,10,10,10,7] := by
  refine ⟨plan7206,valid7206,t6_173choices,?_⟩
  exact check_of_frontier tree 0 t6_173root t6_173jobs t6_173frontier t6_173all
theorem t6_174choices : plan7207.choices=[0,10,7,7,7,7].map (options 6 5) := by rfl


theorem t6_174part0 : t6_174jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_174frontier : t6_174root.frontier 0=t6_174jobs := by rfl
theorem t6_174all : t6_174jobs.all (Job.check tree)=true := by
  simp only [t6_174jobs,List.all_append,List.all_nil,t6_174part0,Bool.and_self]
theorem t6_174checked : Checked tree [0,10,7,7,7,7] := by
  refine ⟨plan7207,valid7207,t6_174choices,?_⟩
  exact check_of_frontier tree 0 t6_174root t6_174jobs t6_174frontier t6_174all
theorem t6_175choices : plan7208.choices=[0,10,10,7,7,7].map (options 6 5) := by rfl


theorem t6_175part0 : t6_175jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_175frontier : t6_175root.frontier 0=t6_175jobs := by rfl
theorem t6_175all : t6_175jobs.all (Job.check tree)=true := by
  simp only [t6_175jobs,List.all_append,List.all_nil,t6_175part0,Bool.and_self]
theorem t6_175checked : Checked tree [0,10,10,7,7,7] := by
  refine ⟨plan7208,valid7208,t6_175choices,?_⟩
  exact check_of_frontier tree 0 t6_175root t6_175jobs t6_175frontier t6_175all
theorem t6_176choices : plan7209.choices=[0,10,10,10,7,7].map (options 6 5) := by rfl


theorem t6_176part0 : t6_176jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_176frontier : t6_176root.frontier 0=t6_176jobs := by rfl
theorem t6_176all : t6_176jobs.all (Job.check tree)=true := by
  simp only [t6_176jobs,List.all_append,List.all_nil,t6_176part0,Bool.and_self]
theorem t6_176checked : Checked tree [0,10,10,10,7,7] := by
  refine ⟨plan7209,valid7209,t6_176choices,?_⟩
  exact check_of_frontier tree 0 t6_176root t6_176jobs t6_176frontier t6_176all
theorem t6_177choices : plan7210.choices=[0,10,10,10,10,7].map (options 6 5) := by rfl


theorem t6_177part0 : t6_177jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_177frontier : t6_177root.frontier 0=t6_177jobs := by rfl
theorem t6_177all : t6_177jobs.all (Job.check tree)=true := by
  simp only [t6_177jobs,List.all_append,List.all_nil,t6_177part0,Bool.and_self]
theorem t6_177checked : Checked tree [0,10,10,10,10,7] := by
  refine ⟨plan7210,valid7210,t6_177choices,?_⟩
  exact check_of_frontier tree 0 t6_177root t6_177jobs t6_177frontier t6_177all
theorem t6_178choices : plan7211.choices=[0,10,10,10,10,10].map (options 6 5) := by rfl


theorem t6_178part0 : t6_178jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_178frontier : t6_178root.frontier 0=t6_178jobs := by rfl
theorem t6_178all : t6_178jobs.all (Job.check tree)=true := by
  simp only [t6_178jobs,List.all_append,List.all_nil,t6_178part0,Bool.and_self]
theorem t6_178checked : Checked tree [0,10,10,10,10,10] := by
  refine ⟨plan7211,valid7211,t6_178choices,?_⟩
  exact check_of_frontier tree 0 t6_178root t6_178jobs t6_178frontier t6_178all
theorem t6_179choices : plan6467.choices=[1,1,1,7,7,7].map (options 6 3) := by rfl


theorem t6_179part0 : t6_179jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_179frontier : t6_179root.frontier 0=t6_179jobs := by rfl
theorem t6_179all : t6_179jobs.all (Job.check tree)=true := by
  simp only [t6_179jobs,List.all_append,List.all_nil,t6_179part0,Bool.and_self]
theorem t6_179checked : Checked tree [1,1,1,7,7,7] := by
  refine ⟨plan6467,valid6467,t6_179choices,?_⟩
  exact check_of_frontier tree 0 t6_179root t6_179jobs t6_179frontier t6_179all
theorem t6_180choices : plan6333.choices=[1,1,2,3,7,7].map (options 6 2) := by rfl


theorem t6_180part0 : t6_180jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_180frontier : t6_180root.frontier 0=t6_180jobs := by rfl
theorem t6_180all : t6_180jobs.all (Job.check tree)=true := by
  simp only [t6_180jobs,List.all_append,List.all_nil,t6_180part0,Bool.and_self]
theorem t6_180checked : Checked tree [1,1,2,3,7,7] := by
  refine ⟨plan6333,valid6333,t6_180choices,?_⟩
  exact check_of_frontier tree 0 t6_180root t6_180jobs t6_180frontier t6_180all
theorem t6_181choices : plan6468.choices=[1,1,2,6,7,7].map (options 6 3) := by rfl


theorem t6_181part0 : t6_181jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_181frontier : t6_181root.frontier 0=t6_181jobs := by rfl
theorem t6_181all : t6_181jobs.all (Job.check tree)=true := by
  simp only [t6_181jobs,List.all_append,List.all_nil,t6_181part0,Bool.and_self]
theorem t6_181checked : Checked tree [1,1,2,6,7,7] := by
  refine ⟨plan6468,valid6468,t6_181choices,?_⟩
  exact check_of_frontier tree 0 t6_181root t6_181jobs t6_181frontier t6_181all
theorem t6_182choices : plan6469.choices=[1,1,2,7,7,7].map (options 6 3) := by rfl


theorem t6_182part0 : t6_182jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_182frontier : t6_182root.frontier 0=t6_182jobs := by rfl
theorem t6_182all : t6_182jobs.all (Job.check tree)=true := by
  simp only [t6_182jobs,List.all_append,List.all_nil,t6_182part0,Bool.and_self]
theorem t6_182checked : Checked tree [1,1,2,7,7,7] := by
  refine ⟨plan6469,valid6469,t6_182choices,?_⟩
  exact check_of_frontier tree 0 t6_182root t6_182jobs t6_182frontier t6_182all
theorem t6_183choices : plan6470.choices=[1,1,2,10,7,7].map (options 6 3) := by rfl


theorem t6_183part0 : t6_183jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_183frontier : t6_183root.frontier 0=t6_183jobs := by rfl
theorem t6_183all : t6_183jobs.all (Job.check tree)=true := by
  simp only [t6_183jobs,List.all_append,List.all_nil,t6_183part0,Bool.and_self]
theorem t6_183checked : Checked tree [1,1,2,10,7,7] := by
  refine ⟨plan6470,valid6470,t6_183choices,?_⟩
  exact check_of_frontier tree 0 t6_183root t6_183jobs t6_183frontier t6_183all
theorem t6_184choices : plan6287.choices=[1,1,3,3,3,7].map (options 6 1) := by rfl


theorem t6_184part0 : t6_184jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_184frontier : t6_184root.frontier 0=t6_184jobs := by rfl
theorem t6_184all : t6_184jobs.all (Job.check tree)=true := by
  simp only [t6_184jobs,List.all_append,List.all_nil,t6_184part0,Bool.and_self]
theorem t6_184checked : Checked tree [1,1,3,3,3,7] := by
  refine ⟨plan6287,valid6287,t6_184choices,?_⟩
  exact check_of_frontier tree 0 t6_184root t6_184jobs t6_184frontier t6_184all
theorem t6_185choices : plan6334.choices=[1,1,3,3,6,7].map (options 6 2) := by rfl


theorem t6_185part0 : t6_185jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_185frontier : t6_185root.frontier 0=t6_185jobs := by rfl
theorem t6_185all : t6_185jobs.all (Job.check tree)=true := by
  simp only [t6_185jobs,List.all_append,List.all_nil,t6_185part0,Bool.and_self]
theorem t6_185checked : Checked tree [1,1,3,3,6,7] := by
  refine ⟨plan6334,valid6334,t6_185choices,?_⟩
  exact check_of_frontier tree 0 t6_185root t6_185jobs t6_185frontier t6_185all
theorem t6_186choices : plan6335.choices=[1,1,3,3,7,7].map (options 6 2) := by rfl


theorem t6_186part0 : t6_186jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_186frontier : t6_186root.frontier 0=t6_186jobs := by rfl
theorem t6_186all : t6_186jobs.all (Job.check tree)=true := by
  simp only [t6_186jobs,List.all_append,List.all_nil,t6_186part0,Bool.and_self]
theorem t6_186checked : Checked tree [1,1,3,3,7,7] := by
  refine ⟨plan6335,valid6335,t6_186choices,?_⟩
  exact check_of_frontier tree 0 t6_186root t6_186jobs t6_186frontier t6_186all
theorem t6_187choices : plan6336.choices=[1,1,3,3,10,7].map (options 6 2) := by rfl


theorem t6_187part0 : t6_187jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_187frontier : t6_187root.frontier 0=t6_187jobs := by rfl
theorem t6_187all : t6_187jobs.all (Job.check tree)=true := by
  simp only [t6_187jobs,List.all_append,List.all_nil,t6_187part0,Bool.and_self]
theorem t6_187checked : Checked tree [1,1,3,3,10,7] := by
  refine ⟨plan6336,valid6336,t6_187choices,?_⟩
  exact check_of_frontier tree 0 t6_187root t6_187jobs t6_187frontier t6_187all
theorem t6_188choices : plan6471.choices=[1,1,3,6,6,7].map (options 6 3) := by rfl


theorem t6_188part0 : t6_188jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_188frontier : t6_188root.frontier 0=t6_188jobs := by rfl
theorem t6_188all : t6_188jobs.all (Job.check tree)=true := by
  simp only [t6_188jobs,List.all_append,List.all_nil,t6_188part0,Bool.and_self]
theorem t6_188checked : Checked tree [1,1,3,6,6,7] := by
  refine ⟨plan6471,valid6471,t6_188choices,?_⟩
  exact check_of_frontier tree 0 t6_188root t6_188jobs t6_188frontier t6_188all
theorem t6_189choices : plan6472.choices=[1,1,3,6,7,7].map (options 6 3) := by rfl


theorem t6_189part0 : t6_189jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_189frontier : t6_189root.frontier 0=t6_189jobs := by rfl
theorem t6_189all : t6_189jobs.all (Job.check tree)=true := by
  simp only [t6_189jobs,List.all_append,List.all_nil,t6_189part0,Bool.and_self]
theorem t6_189checked : Checked tree [1,1,3,6,7,7] := by
  refine ⟨plan6472,valid6472,t6_189choices,?_⟩
  exact check_of_frontier tree 0 t6_189root t6_189jobs t6_189frontier t6_189all
theorem t6_190choices : plan6473.choices=[1,1,3,6,10,7].map (options 6 3) := by rfl


theorem t6_190part0 : t6_190jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_190frontier : t6_190root.frontier 0=t6_190jobs := by rfl
theorem t6_190all : t6_190jobs.all (Job.check tree)=true := by
  simp only [t6_190jobs,List.all_append,List.all_nil,t6_190part0,Bool.and_self]
theorem t6_190checked : Checked tree [1,1,3,6,10,7] := by
  refine ⟨plan6473,valid6473,t6_190choices,?_⟩
  exact check_of_frontier tree 0 t6_190root t6_190jobs t6_190frontier t6_190all
theorem t6_191choices : plan6474.choices=[1,1,3,7,7,7].map (options 6 3) := by rfl


theorem t6_191part0 : t6_191jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_191frontier : t6_191root.frontier 0=t6_191jobs := by rfl
theorem t6_191all : t6_191jobs.all (Job.check tree)=true := by
  simp only [t6_191jobs,List.all_append,List.all_nil,t6_191part0,Bool.and_self]
theorem t6_191checked : Checked tree [1,1,3,7,7,7] := by
  refine ⟨plan6474,valid6474,t6_191choices,?_⟩
  exact check_of_frontier tree 0 t6_191root t6_191jobs t6_191frontier t6_191all
theorem t6_192choices : plan6475.choices=[1,1,3,10,7,7].map (options 6 3) := by rfl


theorem t6_192part0 : t6_192jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_192frontier : t6_192root.frontier 0=t6_192jobs := by rfl
theorem t6_192all : t6_192jobs.all (Job.check tree)=true := by
  simp only [t6_192jobs,List.all_append,List.all_nil,t6_192part0,Bool.and_self]
theorem t6_192checked : Checked tree [1,1,3,10,7,7] := by
  refine ⟨plan6475,valid6475,t6_192choices,?_⟩
  exact check_of_frontier tree 0 t6_192root t6_192jobs t6_192frontier t6_192all
theorem t6_193choices : plan6476.choices=[1,1,3,10,10,7].map (options 6 3) := by rfl


theorem t6_193part0 : t6_193jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_193frontier : t6_193root.frontier 0=t6_193jobs := by rfl
theorem t6_193all : t6_193jobs.all (Job.check tree)=true := by
  simp only [t6_193jobs,List.all_append,List.all_nil,t6_193part0,Bool.and_self]
theorem t6_193checked : Checked tree [1,1,3,10,10,7] := by
  refine ⟨plan6476,valid6476,t6_193choices,?_⟩
  exact check_of_frontier tree 0 t6_193root t6_193jobs t6_193frontier t6_193all
theorem t6_194choices : plan6756.choices=[1,1,4,7,7,7].map (options 6 4) := by rfl


theorem t6_194part0 : t6_194jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_194frontier : t6_194root.frontier 0=t6_194jobs := by rfl
theorem t6_194all : t6_194jobs.all (Job.check tree)=true := by
  simp only [t6_194jobs,List.all_append,List.all_nil,t6_194part0,Bool.and_self]
theorem t6_194checked : Checked tree [1,1,4,7,7,7] := by
  refine ⟨plan6756,valid6756,t6_194choices,?_⟩
  exact check_of_frontier tree 0 t6_194root t6_194jobs t6_194frontier t6_194all
theorem t6_195choices : plan6477.choices=[1,1,5,3,7,7].map (options 6 3) := by rfl


theorem t6_195part0 : t6_195jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_195frontier : t6_195root.frontier 0=t6_195jobs := by rfl
theorem t6_195all : t6_195jobs.all (Job.check tree)=true := by
  simp only [t6_195jobs,List.all_append,List.all_nil,t6_195part0,Bool.and_self]
theorem t6_195checked : Checked tree [1,1,5,3,7,7] := by
  refine ⟨plan6477,valid6477,t6_195choices,?_⟩
  exact check_of_frontier tree 0 t6_195root t6_195jobs t6_195frontier t6_195all
theorem t6_196choices : plan6757.choices=[1,1,5,6,7,7].map (options 6 4) := by rfl


theorem t6_196part0 : t6_196jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_196frontier : t6_196root.frontier 0=t6_196jobs := by rfl
theorem t6_196all : t6_196jobs.all (Job.check tree)=true := by
  simp only [t6_196jobs,List.all_append,List.all_nil,t6_196part0,Bool.and_self]
theorem t6_196checked : Checked tree [1,1,5,6,7,7] := by
  refine ⟨plan6757,valid6757,t6_196choices,?_⟩
  exact check_of_frontier tree 0 t6_196root t6_196jobs t6_196frontier t6_196all
theorem t6_197choices : plan6758.choices=[1,1,5,7,7,7].map (options 6 4) := by rfl


theorem t6_197part0 : t6_197jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_197frontier : t6_197root.frontier 0=t6_197jobs := by rfl
theorem t6_197all : t6_197jobs.all (Job.check tree)=true := by
  simp only [t6_197jobs,List.all_append,List.all_nil,t6_197part0,Bool.and_self]
theorem t6_197checked : Checked tree [1,1,5,7,7,7] := by
  refine ⟨plan6758,valid6758,t6_197choices,?_⟩
  exact check_of_frontier tree 0 t6_197root t6_197jobs t6_197frontier t6_197all
theorem t6_198choices : plan6759.choices=[1,1,5,10,7,7].map (options 6 4) := by rfl


theorem t6_198part0 : t6_198jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_198frontier : t6_198root.frontier 0=t6_198jobs := by rfl
theorem t6_198all : t6_198jobs.all (Job.check tree)=true := by
  simp only [t6_198jobs,List.all_append,List.all_nil,t6_198part0,Bool.and_self]
theorem t6_198checked : Checked tree [1,1,5,10,7,7] := by
  refine ⟨plan6759,valid6759,t6_198choices,?_⟩
  exact check_of_frontier tree 0 t6_198root t6_198jobs t6_198frontier t6_198all
theorem t6_199choices : plan6760.choices=[1,1,6,6,6,7].map (options 6 4) := by rfl


theorem t6_199part0 : t6_199jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_199frontier : t6_199root.frontier 0=t6_199jobs := by rfl
theorem t6_199all : t6_199jobs.all (Job.check tree)=true := by
  simp only [t6_199jobs,List.all_append,List.all_nil,t6_199part0,Bool.and_self]
theorem t6_199checked : Checked tree [1,1,6,6,6,7] := by
  refine ⟨plan6760,valid6760,t6_199choices,?_⟩
  exact check_of_frontier tree 0 t6_199root t6_199jobs t6_199frontier t6_199all
theorem t6_200choices : plan6761.choices=[1,1,6,6,7,7].map (options 6 4) := by rfl


theorem t6_200part0 : t6_200jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_200frontier : t6_200root.frontier 0=t6_200jobs := by rfl
theorem t6_200all : t6_200jobs.all (Job.check tree)=true := by
  simp only [t6_200jobs,List.all_append,List.all_nil,t6_200part0,Bool.and_self]
theorem t6_200checked : Checked tree [1,1,6,6,7,7] := by
  refine ⟨plan6761,valid6761,t6_200choices,?_⟩
  exact check_of_frontier tree 0 t6_200root t6_200jobs t6_200frontier t6_200all
theorem t6_201choices : plan6762.choices=[1,1,6,6,10,7].map (options 6 4) := by rfl


theorem t6_201part0 : t6_201jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_201frontier : t6_201root.frontier 0=t6_201jobs := by rfl
theorem t6_201all : t6_201jobs.all (Job.check tree)=true := by
  simp only [t6_201jobs,List.all_append,List.all_nil,t6_201part0,Bool.and_self]
theorem t6_201checked : Checked tree [1,1,6,6,10,7] := by
  refine ⟨plan6762,valid6762,t6_201choices,?_⟩
  exact check_of_frontier tree 0 t6_201root t6_201jobs t6_201frontier t6_201all
theorem t6_202choices : plan6763.choices=[1,1,6,7,7,7].map (options 6 4) := by rfl


theorem t6_202part0 : t6_202jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_202frontier : t6_202root.frontier 0=t6_202jobs := by rfl
theorem t6_202all : t6_202jobs.all (Job.check tree)=true := by
  simp only [t6_202jobs,List.all_append,List.all_nil,t6_202part0,Bool.and_self]
theorem t6_202checked : Checked tree [1,1,6,7,7,7] := by
  refine ⟨plan6763,valid6763,t6_202choices,?_⟩
  exact check_of_frontier tree 0 t6_202root t6_202jobs t6_202frontier t6_202all
theorem t6_203choices : plan6764.choices=[1,1,6,10,7,7].map (options 6 4) := by rfl


theorem t6_203part0 : t6_203jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_203frontier : t6_203root.frontier 0=t6_203jobs := by rfl
theorem t6_203all : t6_203jobs.all (Job.check tree)=true := by
  simp only [t6_203jobs,List.all_append,List.all_nil,t6_203part0,Bool.and_self]
theorem t6_203checked : Checked tree [1,1,6,10,7,7] := by
  refine ⟨plan6764,valid6764,t6_203choices,?_⟩
  exact check_of_frontier tree 0 t6_203root t6_203jobs t6_203frontier t6_203all
theorem t6_204choices : plan6765.choices=[1,1,6,10,10,7].map (options 6 4) := by rfl


theorem t6_204part0 : t6_204jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_204frontier : t6_204root.frontier 0=t6_204jobs := by rfl
theorem t6_204all : t6_204jobs.all (Job.check tree)=true := by
  simp only [t6_204jobs,List.all_append,List.all_nil,t6_204part0,Bool.and_self]
theorem t6_204checked : Checked tree [1,1,6,10,10,7] := by
  refine ⟨plan6765,valid6765,t6_204choices,?_⟩
  exact check_of_frontier tree 0 t6_204root t6_204jobs t6_204frontier t6_204all
theorem t6_205choices : plan6766.choices=[1,1,7,7,7,7].map (options 6 4) := by rfl


theorem t6_205part0 : t6_205jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_205frontier : t6_205root.frontier 0=t6_205jobs := by rfl
theorem t6_205all : t6_205jobs.all (Job.check tree)=true := by
  simp only [t6_205jobs,List.all_append,List.all_nil,t6_205part0,Bool.and_self]
theorem t6_205checked : Checked tree [1,1,7,7,7,7] := by
  refine ⟨plan6766,valid6766,t6_205choices,?_⟩
  exact check_of_frontier tree 0 t6_205root t6_205jobs t6_205frontier t6_205all
theorem t6_206choices : plan6767.choices=[1,1,8,7,7,7].map (options 6 4) := by rfl


theorem t6_206part0 : t6_206jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_206frontier : t6_206root.frontier 0=t6_206jobs := by rfl
theorem t6_206all : t6_206jobs.all (Job.check tree)=true := by
  simp only [t6_206jobs,List.all_append,List.all_nil,t6_206part0,Bool.and_self]
theorem t6_206checked : Checked tree [1,1,8,7,7,7] := by
  refine ⟨plan6767,valid6767,t6_206choices,?_⟩
  exact check_of_frontier tree 0 t6_206root t6_206jobs t6_206frontier t6_206all
theorem t6_207choices : plan6478.choices=[1,1,9,3,7,7].map (options 6 3) := by rfl


theorem t6_207part0 : t6_207jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_207frontier : t6_207root.frontier 0=t6_207jobs := by rfl
theorem t6_207all : t6_207jobs.all (Job.check tree)=true := by
  simp only [t6_207jobs,List.all_append,List.all_nil,t6_207part0,Bool.and_self]
theorem t6_207checked : Checked tree [1,1,9,3,7,7] := by
  refine ⟨plan6478,valid6478,t6_207choices,?_⟩
  exact check_of_frontier tree 0 t6_207root t6_207jobs t6_207frontier t6_207all
theorem t6_208choices : plan6768.choices=[1,1,9,6,7,7].map (options 6 4) := by rfl


theorem t6_208part0 : t6_208jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_208frontier : t6_208root.frontier 0=t6_208jobs := by rfl
theorem t6_208all : t6_208jobs.all (Job.check tree)=true := by
  simp only [t6_208jobs,List.all_append,List.all_nil,t6_208part0,Bool.and_self]
theorem t6_208checked : Checked tree [1,1,9,6,7,7] := by
  refine ⟨plan6768,valid6768,t6_208choices,?_⟩
  exact check_of_frontier tree 0 t6_208root t6_208jobs t6_208frontier t6_208all
theorem t6_209choices : plan6769.choices=[1,1,9,7,7,7].map (options 6 4) := by rfl


theorem t6_209part0 : t6_209jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_209frontier : t6_209root.frontier 0=t6_209jobs := by rfl
theorem t6_209all : t6_209jobs.all (Job.check tree)=true := by
  simp only [t6_209jobs,List.all_append,List.all_nil,t6_209part0,Bool.and_self]
theorem t6_209checked : Checked tree [1,1,9,7,7,7] := by
  refine ⟨plan6769,valid6769,t6_209choices,?_⟩
  exact check_of_frontier tree 0 t6_209root t6_209jobs t6_209frontier t6_209all
theorem t6_210choices : plan6770.choices=[1,1,9,10,7,7].map (options 6 4) := by rfl


theorem t6_210part0 : t6_210jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_210frontier : t6_210root.frontier 0=t6_210jobs := by rfl
theorem t6_210all : t6_210jobs.all (Job.check tree)=true := by
  simp only [t6_210jobs,List.all_append,List.all_nil,t6_210part0,Bool.and_self]
theorem t6_210checked : Checked tree [1,1,9,10,7,7] := by
  refine ⟨plan6770,valid6770,t6_210choices,?_⟩
  exact check_of_frontier tree 0 t6_210root t6_210jobs t6_210frontier t6_210all
theorem t6_211choices : plan6771.choices=[1,1,10,7,7,7].map (options 6 4) := by rfl


theorem t6_211part0 : t6_211jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_211frontier : t6_211root.frontier 0=t6_211jobs := by rfl
theorem t6_211all : t6_211jobs.all (Job.check tree)=true := by
  simp only [t6_211jobs,List.all_append,List.all_nil,t6_211part0,Bool.and_self]
theorem t6_211checked : Checked tree [1,1,10,7,7,7] := by
  refine ⟨plan6771,valid6771,t6_211choices,?_⟩
  exact check_of_frontier tree 0 t6_211root t6_211jobs t6_211frontier t6_211all
theorem t6_212choices : plan6772.choices=[1,1,10,10,7,7].map (options 6 4) := by rfl


theorem t6_212part0 : t6_212jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_212frontier : t6_212root.frontier 0=t6_212jobs := by rfl
theorem t6_212all : t6_212jobs.all (Job.check tree)=true := by
  simp only [t6_212jobs,List.all_append,List.all_nil,t6_212part0,Bool.and_self]
theorem t6_212checked : Checked tree [1,1,10,10,7,7] := by
  refine ⟨plan6772,valid6772,t6_212choices,?_⟩
  exact check_of_frontier tree 0 t6_212root t6_212jobs t6_212frontier t6_212all
theorem t6_213choices : plan6773.choices=[1,1,10,10,10,7].map (options 6 4) := by rfl


theorem t6_213part0 : t6_213jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_213frontier : t6_213root.frontier 0=t6_213jobs := by rfl
theorem t6_213all : t6_213jobs.all (Job.check tree)=true := by
  simp only [t6_213jobs,List.all_append,List.all_nil,t6_213part0,Bool.and_self]
theorem t6_213checked : Checked tree [1,1,10,10,10,7] := by
  refine ⟨plan6773,valid6773,t6_213choices,?_⟩
  exact check_of_frontier tree 0 t6_213root t6_213jobs t6_213frontier t6_213all
theorem t6_214choices : plan6337.choices=[1,2,2,2,7,7].map (options 6 2) := by rfl


theorem t6_214part0 : t6_214jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_214frontier : t6_214root.frontier 0=t6_214jobs := by rfl
theorem t6_214all : t6_214jobs.all (Job.check tree)=true := by
  simp only [t6_214jobs,List.all_append,List.all_nil,t6_214part0,Bool.and_self]
theorem t6_214checked : Checked tree [1,2,2,2,7,7] := by
  refine ⟨plan6337,valid6337,t6_214choices,?_⟩
  exact check_of_frontier tree 0 t6_214root t6_214jobs t6_214frontier t6_214all
theorem t6_215choices : plan6288.choices=[1,2,2,3,3,7].map (options 6 1) := by rfl


theorem t6_215part0 : t6_215jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_215frontier : t6_215root.frontier 0=t6_215jobs := by rfl
theorem t6_215all : t6_215jobs.all (Job.check tree)=true := by
  simp only [t6_215jobs,List.all_append,List.all_nil,t6_215part0,Bool.and_self]
theorem t6_215checked : Checked tree [1,2,2,3,3,7] := by
  refine ⟨plan6288,valid6288,t6_215choices,?_⟩
  exact check_of_frontier tree 0 t6_215root t6_215jobs t6_215frontier t6_215all
theorem t6_216choices : plan6338.choices=[1,2,2,3,6,7].map (options 6 2) := by rfl


theorem t6_216part0 : t6_216jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_216frontier : t6_216root.frontier 0=t6_216jobs := by rfl
theorem t6_216all : t6_216jobs.all (Job.check tree)=true := by
  simp only [t6_216jobs,List.all_append,List.all_nil,t6_216part0,Bool.and_self]
theorem t6_216checked : Checked tree [1,2,2,3,6,7] := by
  refine ⟨plan6338,valid6338,t6_216choices,?_⟩
  exact check_of_frontier tree 0 t6_216root t6_216jobs t6_216frontier t6_216all
theorem t6_217choices : plan6339.choices=[1,2,2,3,7,7].map (options 6 2) := by rfl


theorem t6_217part0 : t6_217jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_217frontier : t6_217root.frontier 0=t6_217jobs := by rfl
theorem t6_217all : t6_217jobs.all (Job.check tree)=true := by
  simp only [t6_217jobs,List.all_append,List.all_nil,t6_217part0,Bool.and_self]
theorem t6_217checked : Checked tree [1,2,2,3,7,7] := by
  refine ⟨plan6339,valid6339,t6_217choices,?_⟩
  exact check_of_frontier tree 0 t6_217root t6_217jobs t6_217frontier t6_217all
theorem t6_218choices : plan6340.choices=[1,2,2,3,10,7].map (options 6 2) := by rfl


theorem t6_218part0 : t6_218jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_218frontier : t6_218root.frontier 0=t6_218jobs := by rfl
theorem t6_218all : t6_218jobs.all (Job.check tree)=true := by
  simp only [t6_218jobs,List.all_append,List.all_nil,t6_218part0,Bool.and_self]
theorem t6_218checked : Checked tree [1,2,2,3,10,7] := by
  refine ⟨plan6340,valid6340,t6_218choices,?_⟩
  exact check_of_frontier tree 0 t6_218root t6_218jobs t6_218frontier t6_218all
theorem t6_219choices : plan6479.choices=[1,2,2,5,7,7].map (options 6 3) := by rfl


theorem t6_219part0 : t6_219jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_219frontier : t6_219root.frontier 0=t6_219jobs := by rfl
theorem t6_219all : t6_219jobs.all (Job.check tree)=true := by
  simp only [t6_219jobs,List.all_append,List.all_nil,t6_219part0,Bool.and_self]
theorem t6_219checked : Checked tree [1,2,2,5,7,7] := by
  refine ⟨plan6479,valid6479,t6_219choices,?_⟩
  exact check_of_frontier tree 0 t6_219root t6_219jobs t6_219frontier t6_219all
theorem t6_220choices : plan6480.choices=[1,2,2,6,6,7].map (options 6 3) := by rfl


theorem t6_220part0 : t6_220jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_220frontier : t6_220root.frontier 0=t6_220jobs := by rfl
theorem t6_220all : t6_220jobs.all (Job.check tree)=true := by
  simp only [t6_220jobs,List.all_append,List.all_nil,t6_220part0,Bool.and_self]
theorem t6_220checked : Checked tree [1,2,2,6,6,7] := by
  refine ⟨plan6480,valid6480,t6_220choices,?_⟩
  exact check_of_frontier tree 0 t6_220root t6_220jobs t6_220frontier t6_220all
theorem t6_221choices : plan6481.choices=[1,2,2,6,7,7].map (options 6 3) := by rfl


theorem t6_221part0 : t6_221jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_221frontier : t6_221root.frontier 0=t6_221jobs := by rfl
theorem t6_221all : t6_221jobs.all (Job.check tree)=true := by
  simp only [t6_221jobs,List.all_append,List.all_nil,t6_221part0,Bool.and_self]
theorem t6_221checked : Checked tree [1,2,2,6,7,7] := by
  refine ⟨plan6481,valid6481,t6_221choices,?_⟩
  exact check_of_frontier tree 0 t6_221root t6_221jobs t6_221frontier t6_221all
theorem t6_222choices : plan6482.choices=[1,2,2,6,10,7].map (options 6 3) := by rfl


theorem t6_222part0 : t6_222jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_222frontier : t6_222root.frontier 0=t6_222jobs := by rfl
theorem t6_222all : t6_222jobs.all (Job.check tree)=true := by
  simp only [t6_222jobs,List.all_append,List.all_nil,t6_222part0,Bool.and_self]
theorem t6_222checked : Checked tree [1,2,2,6,10,7] := by
  refine ⟨plan6482,valid6482,t6_222choices,?_⟩
  exact check_of_frontier tree 0 t6_222root t6_222jobs t6_222frontier t6_222all
theorem t6_223choices : plan6483.choices=[1,2,2,7,7,7].map (options 6 3) := by rfl


theorem t6_223part0 : t6_223jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_223frontier : t6_223root.frontier 0=t6_223jobs := by rfl
theorem t6_223all : t6_223jobs.all (Job.check tree)=true := by
  simp only [t6_223jobs,List.all_append,List.all_nil,t6_223part0,Bool.and_self]
theorem t6_223checked : Checked tree [1,2,2,7,7,7] := by
  refine ⟨plan6483,valid6483,t6_223choices,?_⟩
  exact check_of_frontier tree 0 t6_223root t6_223jobs t6_223frontier t6_223all
theorem t6_224choices : plan6484.choices=[1,2,2,9,7,7].map (options 6 3) := by rfl


theorem t6_224part0 : t6_224jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_224frontier : t6_224root.frontier 0=t6_224jobs := by rfl
theorem t6_224all : t6_224jobs.all (Job.check tree)=true := by
  simp only [t6_224jobs,List.all_append,List.all_nil,t6_224part0,Bool.and_self]
theorem t6_224checked : Checked tree [1,2,2,9,7,7] := by
  refine ⟨plan6484,valid6484,t6_224choices,?_⟩
  exact check_of_frontier tree 0 t6_224root t6_224jobs t6_224frontier t6_224all
theorem t6_225choices : plan6485.choices=[1,2,2,10,7,7].map (options 6 3) := by rfl


theorem t6_225part0 : t6_225jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_225frontier : t6_225root.frontier 0=t6_225jobs := by rfl
theorem t6_225all : t6_225jobs.all (Job.check tree)=true := by
  simp only [t6_225jobs,List.all_append,List.all_nil,t6_225part0,Bool.and_self]
theorem t6_225checked : Checked tree [1,2,2,10,7,7] := by
  refine ⟨plan6485,valid6485,t6_225choices,?_⟩
  exact check_of_frontier tree 0 t6_225root t6_225jobs t6_225frontier t6_225all
theorem t6_226choices : plan6486.choices=[1,2,2,10,10,7].map (options 6 3) := by rfl


theorem t6_226part0 : t6_226jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_226frontier : t6_226root.frontier 0=t6_226jobs := by rfl
theorem t6_226all : t6_226jobs.all (Job.check tree)=true := by
  simp only [t6_226jobs,List.all_append,List.all_nil,t6_226part0,Bool.and_self]
theorem t6_226checked : Checked tree [1,2,2,10,10,7] := by
  refine ⟨plan6486,valid6486,t6_226choices,?_⟩
  exact check_of_frontier tree 0 t6_226root t6_226jobs t6_226frontier t6_226all
theorem t6_227choices : plan6277.choices=[1,2,3,3,3,3].map (options 6 0) := by rfl


theorem t6_227part0 : t6_227jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_227frontier : t6_227root.frontier 0=t6_227jobs := by rfl
theorem t6_227all : t6_227jobs.all (Job.check tree)=true := by
  simp only [t6_227jobs,List.all_append,List.all_nil,t6_227part0,Bool.and_self]
theorem t6_227checked : Checked tree [1,2,3,3,3,3] := by
  refine ⟨plan6277,valid6277,t6_227choices,?_⟩
  exact check_of_frontier tree 0 t6_227root t6_227jobs t6_227frontier t6_227all
theorem t6_228choices : plan6289.choices=[1,2,3,3,3,6].map (options 6 1) := by rfl


theorem t6_228part0 : t6_228jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_228frontier : t6_228root.frontier 0=t6_228jobs := by rfl
theorem t6_228all : t6_228jobs.all (Job.check tree)=true := by
  simp only [t6_228jobs,List.all_append,List.all_nil,t6_228part0,Bool.and_self]
theorem t6_228checked : Checked tree [1,2,3,3,3,6] := by
  refine ⟨plan6289,valid6289,t6_228choices,?_⟩
  exact check_of_frontier tree 0 t6_228root t6_228jobs t6_228frontier t6_228all
theorem t6_229choices : plan6290.choices=[1,2,3,3,3,7].map (options 6 1) := by rfl


theorem t6_229part0 : t6_229jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_229frontier : t6_229root.frontier 0=t6_229jobs := by rfl
theorem t6_229all : t6_229jobs.all (Job.check tree)=true := by
  simp only [t6_229jobs,List.all_append,List.all_nil,t6_229part0,Bool.and_self]
theorem t6_229checked : Checked tree [1,2,3,3,3,7] := by
  refine ⟨plan6290,valid6290,t6_229choices,?_⟩
  exact check_of_frontier tree 0 t6_229root t6_229jobs t6_229frontier t6_229all
theorem t6_230choices : plan6291.choices=[1,2,3,3,3,10].map (options 6 1) := by rfl


theorem t6_230part0 : t6_230jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_230frontier : t6_230root.frontier 0=t6_230jobs := by rfl
theorem t6_230all : t6_230jobs.all (Job.check tree)=true := by
  simp only [t6_230jobs,List.all_append,List.all_nil,t6_230part0,Bool.and_self]
theorem t6_230checked : Checked tree [1,2,3,3,3,10] := by
  refine ⟨plan6291,valid6291,t6_230choices,?_⟩
  exact check_of_frontier tree 0 t6_230root t6_230jobs t6_230frontier t6_230all
theorem t6_231choices : plan6341.choices=[1,2,3,3,6,6].map (options 6 2) := by rfl


theorem t6_231part0 : t6_231jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_231frontier : t6_231root.frontier 0=t6_231jobs := by rfl
theorem t6_231all : t6_231jobs.all (Job.check tree)=true := by
  simp only [t6_231jobs,List.all_append,List.all_nil,t6_231part0,Bool.and_self]
theorem t6_231checked : Checked tree [1,2,3,3,6,6] := by
  refine ⟨plan6341,valid6341,t6_231choices,?_⟩
  exact check_of_frontier tree 0 t6_231root t6_231jobs t6_231frontier t6_231all
theorem t6_232choices : plan6342.choices=[1,2,3,3,6,7].map (options 6 2) := by rfl


theorem t6_232part0 : t6_232jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_232part1 : t6_232jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_232frontier : t6_232root.frontier 1=t6_232jobs := by rfl
theorem t6_232all : t6_232jobs.all (Job.check tree)=true := by
  simp only [t6_232jobs,List.all_append,List.all_nil,t6_232part0,t6_232part1,Bool.and_self]
theorem t6_232checked : Checked tree [1,2,3,3,6,7] := by
  refine ⟨plan6342,valid6342,t6_232choices,?_⟩
  exact check_of_frontier tree 1 t6_232root t6_232jobs t6_232frontier t6_232all
theorem t6_233choices : plan6343.choices=[1,2,3,3,6,10].map (options 6 2) := by rfl


theorem t6_233part0 : t6_233jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_233frontier : t6_233root.frontier 0=t6_233jobs := by rfl
theorem t6_233all : t6_233jobs.all (Job.check tree)=true := by
  simp only [t6_233jobs,List.all_append,List.all_nil,t6_233part0,Bool.and_self]
theorem t6_233checked : Checked tree [1,2,3,3,6,10] := by
  refine ⟨plan6343,valid6343,t6_233choices,?_⟩
  exact check_of_frontier tree 0 t6_233root t6_233jobs t6_233frontier t6_233all
theorem t6_234choices : plan6344.choices=[1,2,3,3,7,7].map (options 6 2) := by rfl


theorem t6_234part0 : t6_234jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_234part1 : t6_234jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_234frontier : t6_234root.frontier 1=t6_234jobs := by rfl
theorem t6_234all : t6_234jobs.all (Job.check tree)=true := by
  simp only [t6_234jobs,List.all_append,List.all_nil,t6_234part0,t6_234part1,Bool.and_self]
theorem t6_234checked : Checked tree [1,2,3,3,7,7] := by
  refine ⟨plan6344,valid6344,t6_234choices,?_⟩
  exact check_of_frontier tree 1 t6_234root t6_234jobs t6_234frontier t6_234all
theorem t6_235choices : plan6345.choices=[1,2,3,3,10,7].map (options 6 2) := by rfl


theorem t6_235part0 : t6_235jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_235part1 : t6_235jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_235frontier : t6_235root.frontier 1=t6_235jobs := by rfl
theorem t6_235all : t6_235jobs.all (Job.check tree)=true := by
  simp only [t6_235jobs,List.all_append,List.all_nil,t6_235part0,t6_235part1,Bool.and_self]
theorem t6_235checked : Checked tree [1,2,3,3,10,7] := by
  refine ⟨plan6345,valid6345,t6_235choices,?_⟩
  exact check_of_frontier tree 1 t6_235root t6_235jobs t6_235frontier t6_235all
theorem t6_236choices : plan6346.choices=[1,2,3,3,10,10].map (options 6 2) := by rfl


theorem t6_236part0 : t6_236jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_236frontier : t6_236root.frontier 0=t6_236jobs := by rfl
theorem t6_236all : t6_236jobs.all (Job.check tree)=true := by
  simp only [t6_236jobs,List.all_append,List.all_nil,t6_236part0,Bool.and_self]
theorem t6_236checked : Checked tree [1,2,3,3,10,10] := by
  refine ⟨plan6346,valid6346,t6_236choices,?_⟩
  exact check_of_frontier tree 0 t6_236root t6_236jobs t6_236frontier t6_236all
theorem t6_237choices : plan6487.choices=[1,2,3,6,6,6].map (options 6 3) := by rfl


theorem t6_237part0 : t6_237jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_237frontier : t6_237root.frontier 0=t6_237jobs := by rfl
theorem t6_237all : t6_237jobs.all (Job.check tree)=true := by
  simp only [t6_237jobs,List.all_append,List.all_nil,t6_237part0,Bool.and_self]
theorem t6_237checked : Checked tree [1,2,3,6,6,6] := by
  refine ⟨plan6487,valid6487,t6_237choices,?_⟩
  exact check_of_frontier tree 0 t6_237root t6_237jobs t6_237frontier t6_237all
theorem t6_238choices : plan6488.choices=[1,2,3,6,6,7].map (options 6 3) := by rfl


theorem t6_238part0 : t6_238jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_238part1 : t6_238jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_238frontier : t6_238root.frontier 1=t6_238jobs := by rfl
theorem t6_238all : t6_238jobs.all (Job.check tree)=true := by
  simp only [t6_238jobs,List.all_append,List.all_nil,t6_238part0,t6_238part1,Bool.and_self]
theorem t6_238checked : Checked tree [1,2,3,6,6,7] := by
  refine ⟨plan6488,valid6488,t6_238choices,?_⟩
  exact check_of_frontier tree 1 t6_238root t6_238jobs t6_238frontier t6_238all
theorem t6_239choices : plan6489.choices=[1,2,3,6,6,10].map (options 6 3) := by rfl


theorem t6_239part0 : t6_239jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_239frontier : t6_239root.frontier 0=t6_239jobs := by rfl
theorem t6_239all : t6_239jobs.all (Job.check tree)=true := by
  simp only [t6_239jobs,List.all_append,List.all_nil,t6_239part0,Bool.and_self]
theorem t6_239checked : Checked tree [1,2,3,6,6,10] := by
  refine ⟨plan6489,valid6489,t6_239choices,?_⟩
  exact check_of_frontier tree 0 t6_239root t6_239jobs t6_239frontier t6_239all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks049 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_155checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_168checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_169checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_170checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_171checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_172checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_173checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_174checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_175checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_176checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_177checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_156checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_178checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_179checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_180checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_181checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_182checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_183checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_184checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_185checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_186checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_187checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_157checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_188checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_189checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_190checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_191checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_192checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_193checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_194checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_195checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_196checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_197checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_158checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_198checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_199checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_200checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_201checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_202checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_203checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_204checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_205checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_206checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_207checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_159checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_208checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_209checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_210checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_211checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_212checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_213checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_214checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_215checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_216checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_217checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_160checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_218checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_219checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_220checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_221checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_222checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_223checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_224checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_225checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_226checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_227checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_161checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_228checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_229checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_230checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_231checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_232checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_233checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_234checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_235checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_236checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_162checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_237checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_238checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_239checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_163checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_164checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_165checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_166checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_167checked⟩
