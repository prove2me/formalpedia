-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks059
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:15:52.294212+00:00
-- url     : https://prove2.me/submissions/6fc33024-3502-441c-a2db-42c4943ced24

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks059
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
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











































theorem valid118 : plan118.Valid := valid_step _ _ _ valid0 (by decide +kernel)









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

























































































































theorem valid541 : plan541.Valid := valid_step _ _ _ valid118 (by decide +kernel)









theorem valid546 : plan546.Valid := valid_step _ _ _ valid123 (by decide +kernel)

theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid548 : plan548.Valid := valid_step _ _ _ valid125 (by decide +kernel)





















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







































































































































theorem valid1508 : plan1508.Valid := valid_step _ _ _ valid541 (by decide +kernel)















theorem valid1516 : plan1516.Valid := valid_step _ _ _ valid546 (by decide +kernel)

theorem valid1517 : plan1517.Valid := valid_step _ _ _ valid547 (by decide +kernel)

theorem valid1518 : plan1518.Valid := valid_step _ _ _ valid548 (by decide +kernel)



























theorem valid1532 : plan1532.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1533 : plan1533.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1534 : plan1534.Valid := valid_step _ _ _ valid561 (by decide +kernel)

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



























































































































































theorem valid3246 : plan3246.Valid := valid_step _ _ _ valid1508 (by decide +kernel)




































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

theorem valid3265 : plan3265.Valid := valid_step _ _ _ valid1516 (by decide +kernel)

theorem valid3266 : plan3266.Valid := valid_step _ _ _ valid1517 (by decide +kernel)

theorem valid3267 : plan3267.Valid := valid_step _ _ _ valid1518 (by decide +kernel)



































theorem valid3285 : plan3285.Valid := valid_step _ _ _ valid1535 (by decide +kernel)









































theorem valid3306 : plan3306.Valid := valid_step _ _ _ valid1532 (by decide +kernel)

theorem valid3307 : plan3307.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3308 : plan3308.Valid := valid_step _ _ _ valid1534 (by decide +kernel)

theorem valid3309 : plan3309.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3310 : plan3310.Valid := valid_step _ _ _ valid1536 (by decide +kernel)











































































theorem valid3348 : plan3348.Valid := valid_step _ _ _ valid1572 (by decide +kernel)



theorem valid3350 : plan3350.Valid := valid_step _ _ _ valid1575 (by decide +kernel)



theorem valid3352 : plan3352.Valid := valid_step _ _ _ valid1580 (by decide +kernel)
















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

































































































































































theorem valid5361 : plan5361.Valid := valid_step _ _ _ valid3246 (by decide +kernel)






























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

































































theorem valid5409 : plan5409.Valid := valid_step _ _ _ valid3266 (by decide +kernel)



theorem valid5411 : plan5411.Valid := valid_step _ _ _ valid3265 (by decide +kernel)

theorem valid5412 : plan5412.Valid := valid_step _ _ _ valid3266 (by decide +kernel)

theorem valid5413 : plan5413.Valid := valid_step _ _ _ valid3267 (by decide +kernel)






















































































































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















































































































theorem valid6296 : plan6296.Valid := valid_step _ _ _ valid5361 (by decide +kernel)
















































































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













































































theorem valid3416 : plan3416.Valid := valid_step _ _ _ valid1562 (by decide +kernel)
















































































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



























































































theorem valid5518 : plan5518.Valid := valid_step _ _ _ valid3285 (by decide +kernel)



theorem valid5520 : plan5520.Valid := valid_step _ _ _ valid3307 (by decide +kernel)

theorem valid5521 : plan5521.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5522 : plan5522.Valid := valid_step _ _ _ valid3310 (by decide +kernel)







theorem valid5526 : plan5526.Valid := valid_step _ _ _ valid3306 (by decide +kernel)

theorem valid5527 : plan5527.Valid := valid_step _ _ _ valid3307 (by decide +kernel)

theorem valid5528 : plan5528.Valid := valid_step _ _ _ valid3308 (by decide +kernel)

theorem valid5529 : plan5529.Valid := valid_step _ _ _ valid3309 (by decide +kernel)














































































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

























































































































































































theorem valid6525 : plan6525.Valid := valid_step _ _ _ valid5518 (by decide +kernel)

theorem valid6526 : plan6526.Valid := valid_step _ _ _ valid5520 (by decide +kernel)

theorem valid6527 : plan6527.Valid := valid_step _ _ _ valid5521 (by decide +kernel)

theorem valid6528 : plan6528.Valid := valid_step _ _ _ valid5522 (by decide +kernel)
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







theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)



theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)



theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)



theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3486 : plan3486.Valid := valid_step _ _ _ valid1599 (by decide +kernel)



















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







































































theorem valid5700 : plan5700.Valid := valid_step _ _ _ valid3348 (by decide +kernel)

theorem valid5701 : plan5701.Valid := valid_step _ _ _ valid3350 (by decide +kernel)

theorem valid5702 : plan5702.Valid := valid_step _ _ _ valid3352 (by decide +kernel)







theorem valid5706 : plan5706.Valid := valid_step _ _ _ valid3361 (by decide +kernel)

theorem valid5707 : plan5707.Valid := valid_step _ _ _ valid3363 (by decide +kernel)

theorem valid5708 : plan5708.Valid := valid_step _ _ _ valid3364 (by decide +kernel)

theorem valid5709 : plan5709.Valid := valid_step _ _ _ valid3366 (by decide +kernel)

theorem valid5710 : plan5710.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5711 : plan5711.Valid := valid_step _ _ _ valid3368 (by decide +kernel)

theorem valid5712 : plan5712.Valid := valid_step _ _ _ valid3377 (by decide +kernel)

theorem valid5713 : plan5713.Valid := valid_step _ _ _ valid3416 (by decide +kernel)






























































































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











































































theorem valid5894 : plan5894.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5895 : plan5895.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5896 : plan5896.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5897 : plan5897.Valid := valid_step _ _ _ valid3510 (by decide +kernel)

theorem valid5898 : plan5898.Valid := valid_step _ _ _ valid3485 (by decide +kernel)





















theorem valid5909 : plan5909.Valid := valid_step _ _ _ valid3464 (by decide +kernel)

theorem valid5910 : plan5910.Valid := valid_step _ _ _ valid3467 (by decide +kernel)

theorem valid5911 : plan5911.Valid := valid_step _ _ _ valid3472 (by decide +kernel)

theorem valid5912 : plan5912.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5913 : plan5913.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5914 : plan5914.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5915 : plan5915.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5916 : plan5916.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5917 : plan5917.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5918 : plan5918.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5919 : plan5919.Valid := valid_step _ _ _ valid3486 (by decide +kernel)



theorem valid5921 : plan5921.Valid := valid_step _ _ _ valid3496 (by decide +kernel)

theorem valid5922 : plan5922.Valid := valid_step _ _ _ valid3499 (by decide +kernel)

theorem valid5923 : plan5923.Valid := valid_step _ _ _ valid3504 (by decide +kernel)

theorem valid5924 : plan5924.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5925 : plan5925.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5926 : plan5926.Valid := valid_step _ _ _ valid3509 (by decide +kernel)




















































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













































theorem valid6359 : plan6359.Valid := valid_step _ _ _ valid5409 (by decide +kernel)

theorem valid6360 : plan6360.Valid := valid_step _ _ _ valid5411 (by decide +kernel)

theorem valid6361 : plan6361.Valid := valid_step _ _ _ valid5412 (by decide +kernel)

theorem valid6362 : plan6362.Valid := valid_step _ _ _ valid5413 (by decide +kernel)












































































































































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













































































































































theorem valid7271 : plan7271.Valid := valid_step _ _ _ valid5894 (by decide +kernel)

theorem valid7272 : plan7272.Valid := valid_step _ _ _ valid5895 (by decide +kernel)

theorem valid7273 : plan7273.Valid := valid_step _ _ _ valid5896 (by decide +kernel)

theorem valid7274 : plan7274.Valid := valid_step _ _ _ valid5897 (by decide +kernel)

theorem valid7275 : plan7275.Valid := valid_step _ _ _ valid5898 (by decide +kernel)

theorem valid7276 : plan7276.Valid := valid_step _ _ _ valid5909 (by decide +kernel)

theorem valid7277 : plan7277.Valid := valid_step _ _ _ valid5910 (by decide +kernel)

theorem valid7278 : plan7278.Valid := valid_step _ _ _ valid5911 (by decide +kernel)

theorem valid7279 : plan7279.Valid := valid_step _ _ _ valid5912 (by decide +kernel)

theorem valid7280 : plan7280.Valid := valid_step _ _ _ valid5913 (by decide +kernel)

theorem valid7281 : plan7281.Valid := valid_step _ _ _ valid5914 (by decide +kernel)

theorem valid7282 : plan7282.Valid := valid_step _ _ _ valid5915 (by decide +kernel)

theorem valid7283 : plan7283.Valid := valid_step _ _ _ valid5916 (by decide +kernel)

theorem valid7284 : plan7284.Valid := valid_step _ _ _ valid5917 (by decide +kernel)

theorem valid7285 : plan7285.Valid := valid_step _ _ _ valid5918 (by decide +kernel)

theorem valid7286 : plan7286.Valid := valid_step _ _ _ valid5919 (by decide +kernel)

theorem valid7287 : plan7287.Valid := valid_step _ _ _ valid5921 (by decide +kernel)

theorem valid7288 : plan7288.Valid := valid_step _ _ _ valid5922 (by decide +kernel)

theorem valid7289 : plan7289.Valid := valid_step _ _ _ valid5923 (by decide +kernel)

theorem valid7290 : plan7290.Valid := valid_step _ _ _ valid5924 (by decide +kernel)

theorem valid7291 : plan7291.Valid := valid_step _ _ _ valid5925 (by decide +kernel)

theorem valid7292 : plan7292.Valid := valid_step _ _ _ valid5926 (by decide +kernel)








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



























































theorem valid6846 : plan6846.Valid := valid_step _ _ _ valid5700 (by decide +kernel)

theorem valid6847 : plan6847.Valid := valid_step _ _ _ valid5701 (by decide +kernel)

theorem valid6848 : plan6848.Valid := valid_step _ _ _ valid5702 (by decide +kernel)

theorem valid6849 : plan6849.Valid := valid_step _ _ _ valid5706 (by decide +kernel)

theorem valid6850 : plan6850.Valid := valid_step _ _ _ valid5707 (by decide +kernel)

theorem valid6851 : plan6851.Valid := valid_step _ _ _ valid5708 (by decide +kernel)

theorem valid6852 : plan6852.Valid := valid_step _ _ _ valid5709 (by decide +kernel)

theorem valid6853 : plan6853.Valid := valid_step _ _ _ valid5710 (by decide +kernel)

theorem valid6854 : plan6854.Valid := valid_step _ _ _ valid5711 (by decide +kernel)

theorem valid6855 : plan6855.Valid := valid_step _ _ _ valid5712 (by decide +kernel)

theorem valid6856 : plan6856.Valid := valid_step _ _ _ valid5713 (by decide +kernel)
















































































































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

theorem valid6529 : plan6529.Valid := valid_step _ _ _ valid5526 (by decide +kernel)

theorem valid6530 : plan6530.Valid := valid_step _ _ _ valid5527 (by decide +kernel)

theorem valid6531 : plan6531.Valid := valid_step _ _ _ valid5528 (by decide +kernel)

theorem valid6532 : plan6532.Valid := valid_step _ _ _ valid5529 (by decide +kernel)
























































































































































































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
theorem t6_423choices : plan7271.choices=[1,6,10,7,7,7].map (options 6 5) := by rfl


theorem t6_423part0 : t6_423jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_423part1 : t6_423jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_423frontier : t6_423root.frontier 2=t6_423jobs := by rfl
theorem t6_423all : t6_423jobs.all (Job.check tree)=true := by
  simp only [t6_423jobs,List.all_append,List.all_nil,t6_423part0,t6_423part1,Bool.and_self]
theorem t6_423checked : Checked tree [1,6,10,7,7,7] := by
  refine ⟨plan7271,valid7271,t6_423choices,?_⟩
  exact check_of_frontier tree 2 t6_423root t6_423jobs t6_423frontier t6_423all
theorem t6_424choices : plan7272.choices=[1,6,10,10,7,7].map (options 6 5) := by rfl


theorem t6_424part0 : t6_424jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_424frontier : t6_424root.frontier 0=t6_424jobs := by rfl
theorem t6_424all : t6_424jobs.all (Job.check tree)=true := by
  simp only [t6_424jobs,List.all_append,List.all_nil,t6_424part0,Bool.and_self]
theorem t6_424checked : Checked tree [1,6,10,10,7,7] := by
  refine ⟨plan7272,valid7272,t6_424choices,?_⟩
  exact check_of_frontier tree 0 t6_424root t6_424jobs t6_424frontier t6_424all
theorem t6_425choices : plan7273.choices=[1,6,10,10,10,7].map (options 6 5) := by rfl


theorem t6_425part0 : t6_425jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_425frontier : t6_425root.frontier 0=t6_425jobs := by rfl
theorem t6_425all : t6_425jobs.all (Job.check tree)=true := by
  simp only [t6_425jobs,List.all_append,List.all_nil,t6_425part0,Bool.and_self]
theorem t6_425checked : Checked tree [1,6,10,10,10,7] := by
  refine ⟨plan7273,valid7273,t6_425choices,?_⟩
  exact check_of_frontier tree 0 t6_425root t6_425jobs t6_425frontier t6_425all
theorem t6_426choices : plan7274.choices=[1,6,10,10,10,10].map (options 6 5) := by rfl


theorem t6_426part0 : t6_426jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_426frontier : t6_426root.frontier 0=t6_426jobs := by rfl
theorem t6_426all : t6_426jobs.all (Job.check tree)=true := by
  simp only [t6_426jobs,List.all_append,List.all_nil,t6_426part0,Bool.and_self]
theorem t6_426checked : Checked tree [1,6,10,10,10,10] := by
  refine ⟨plan7274,valid7274,t6_426choices,?_⟩
  exact check_of_frontier tree 0 t6_426root t6_426jobs t6_426frontier t6_426all
theorem t6_427choices : plan7275.choices=[1,7,7,7,7,7].map (options 6 5) := by rfl


theorem t6_427part0 : t6_427jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_427frontier : t6_427root.frontier 0=t6_427jobs := by rfl
theorem t6_427all : t6_427jobs.all (Job.check tree)=true := by
  simp only [t6_427jobs,List.all_append,List.all_nil,t6_427part0,Bool.and_self]
theorem t6_427checked : Checked tree [1,7,7,7,7,7] := by
  refine ⟨plan7275,valid7275,t6_427choices,?_⟩
  exact check_of_frontier tree 0 t6_427root t6_427jobs t6_427frontier t6_427all
theorem t6_428choices : plan6525.choices=[1,8,2,3,7,7].map (options 6 3) := by rfl


theorem t6_428part0 : t6_428jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_428frontier : t6_428root.frontier 0=t6_428jobs := by rfl
theorem t6_428all : t6_428jobs.all (Job.check tree)=true := by
  simp only [t6_428jobs,List.all_append,List.all_nil,t6_428part0,Bool.and_self]
theorem t6_428checked : Checked tree [1,8,2,3,7,7] := by
  refine ⟨plan6525,valid6525,t6_428choices,?_⟩
  exact check_of_frontier tree 0 t6_428root t6_428jobs t6_428frontier t6_428all
theorem t6_429choices : plan6846.choices=[1,8,2,6,7,7].map (options 6 4) := by rfl


theorem t6_429part0 : t6_429jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_429frontier : t6_429root.frontier 0=t6_429jobs := by rfl
theorem t6_429all : t6_429jobs.all (Job.check tree)=true := by
  simp only [t6_429jobs,List.all_append,List.all_nil,t6_429part0,Bool.and_self]
theorem t6_429checked : Checked tree [1,8,2,6,7,7] := by
  refine ⟨plan6846,valid6846,t6_429choices,?_⟩
  exact check_of_frontier tree 0 t6_429root t6_429jobs t6_429frontier t6_429all
theorem t6_430choices : plan6847.choices=[1,8,2,7,7,7].map (options 6 4) := by rfl


theorem t6_430part0 : t6_430jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_430frontier : t6_430root.frontier 0=t6_430jobs := by rfl
theorem t6_430all : t6_430jobs.all (Job.check tree)=true := by
  simp only [t6_430jobs,List.all_append,List.all_nil,t6_430part0,Bool.and_self]
theorem t6_430checked : Checked tree [1,8,2,7,7,7] := by
  refine ⟨plan6847,valid6847,t6_430choices,?_⟩
  exact check_of_frontier tree 0 t6_430root t6_430jobs t6_430frontier t6_430all
theorem t6_431choices : plan6848.choices=[1,8,2,10,7,7].map (options 6 4) := by rfl


theorem t6_431part0 : t6_431jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_431frontier : t6_431root.frontier 0=t6_431jobs := by rfl
theorem t6_431all : t6_431jobs.all (Job.check tree)=true := by
  simp only [t6_431jobs,List.all_append,List.all_nil,t6_431part0,Bool.and_self]
theorem t6_431checked : Checked tree [1,8,2,10,7,7] := by
  refine ⟨plan6848,valid6848,t6_431choices,?_⟩
  exact check_of_frontier tree 0 t6_431root t6_431jobs t6_431frontier t6_431all
theorem t6_432choices : plan6359.choices=[1,8,3,3,3,7].map (options 6 2) := by rfl


theorem t6_432part0 : t6_432jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_432frontier : t6_432root.frontier 0=t6_432jobs := by rfl
theorem t6_432all : t6_432jobs.all (Job.check tree)=true := by
  simp only [t6_432jobs,List.all_append,List.all_nil,t6_432part0,Bool.and_self]
theorem t6_432checked : Checked tree [1,8,3,3,3,7] := by
  refine ⟨plan6359,valid6359,t6_432choices,?_⟩
  exact check_of_frontier tree 0 t6_432root t6_432jobs t6_432frontier t6_432all
theorem t6_433choices : plan6526.choices=[1,8,3,3,6,7].map (options 6 3) := by rfl


theorem t6_433part0 : t6_433jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_433frontier : t6_433root.frontier 0=t6_433jobs := by rfl
theorem t6_433all : t6_433jobs.all (Job.check tree)=true := by
  simp only [t6_433jobs,List.all_append,List.all_nil,t6_433part0,Bool.and_self]
theorem t6_433checked : Checked tree [1,8,3,3,6,7] := by
  refine ⟨plan6526,valid6526,t6_433choices,?_⟩
  exact check_of_frontier tree 0 t6_433root t6_433jobs t6_433frontier t6_433all
theorem t6_434choices : plan6527.choices=[1,8,3,3,7,7].map (options 6 3) := by rfl


theorem t6_434part0 : t6_434jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_434frontier : t6_434root.frontier 0=t6_434jobs := by rfl
theorem t6_434all : t6_434jobs.all (Job.check tree)=true := by
  simp only [t6_434jobs,List.all_append,List.all_nil,t6_434part0,Bool.and_self]
theorem t6_434checked : Checked tree [1,8,3,3,7,7] := by
  refine ⟨plan6527,valid6527,t6_434choices,?_⟩
  exact check_of_frontier tree 0 t6_434root t6_434jobs t6_434frontier t6_434all
theorem t6_435choices : plan6528.choices=[1,8,3,3,10,7].map (options 6 3) := by rfl


theorem t6_435part0 : t6_435jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_435frontier : t6_435root.frontier 0=t6_435jobs := by rfl
theorem t6_435all : t6_435jobs.all (Job.check tree)=true := by
  simp only [t6_435jobs,List.all_append,List.all_nil,t6_435part0,Bool.and_self]
theorem t6_435checked : Checked tree [1,8,3,3,10,7] := by
  refine ⟨plan6528,valid6528,t6_435choices,?_⟩
  exact check_of_frontier tree 0 t6_435root t6_435jobs t6_435frontier t6_435all
theorem t6_436choices : plan6849.choices=[1,8,3,6,6,7].map (options 6 4) := by rfl


theorem t6_436part0 : t6_436jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_436frontier : t6_436root.frontier 0=t6_436jobs := by rfl
theorem t6_436all : t6_436jobs.all (Job.check tree)=true := by
  simp only [t6_436jobs,List.all_append,List.all_nil,t6_436part0,Bool.and_self]
theorem t6_436checked : Checked tree [1,8,3,6,6,7] := by
  refine ⟨plan6849,valid6849,t6_436choices,?_⟩
  exact check_of_frontier tree 0 t6_436root t6_436jobs t6_436frontier t6_436all
theorem t6_437choices : plan6850.choices=[1,8,3,6,7,7].map (options 6 4) := by rfl


theorem t6_437part0 : t6_437jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_437frontier : t6_437root.frontier 0=t6_437jobs := by rfl
theorem t6_437all : t6_437jobs.all (Job.check tree)=true := by
  simp only [t6_437jobs,List.all_append,List.all_nil,t6_437part0,Bool.and_self]
theorem t6_437checked : Checked tree [1,8,3,6,7,7] := by
  refine ⟨plan6850,valid6850,t6_437choices,?_⟩
  exact check_of_frontier tree 0 t6_437root t6_437jobs t6_437frontier t6_437all
theorem t6_438choices : plan6851.choices=[1,8,3,6,10,7].map (options 6 4) := by rfl


theorem t6_438part0 : t6_438jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_438frontier : t6_438root.frontier 0=t6_438jobs := by rfl
theorem t6_438all : t6_438jobs.all (Job.check tree)=true := by
  simp only [t6_438jobs,List.all_append,List.all_nil,t6_438part0,Bool.and_self]
theorem t6_438checked : Checked tree [1,8,3,6,10,7] := by
  refine ⟨plan6851,valid6851,t6_438choices,?_⟩
  exact check_of_frontier tree 0 t6_438root t6_438jobs t6_438frontier t6_438all
theorem t6_439choices : plan6852.choices=[1,8,3,7,7,7].map (options 6 4) := by rfl


theorem t6_439part0 : t6_439jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_439frontier : t6_439root.frontier 0=t6_439jobs := by rfl
theorem t6_439all : t6_439jobs.all (Job.check tree)=true := by
  simp only [t6_439jobs,List.all_append,List.all_nil,t6_439part0,Bool.and_self]
theorem t6_439checked : Checked tree [1,8,3,7,7,7] := by
  refine ⟨plan6852,valid6852,t6_439choices,?_⟩
  exact check_of_frontier tree 0 t6_439root t6_439jobs t6_439frontier t6_439all
theorem t6_440choices : plan6853.choices=[1,8,3,10,7,7].map (options 6 4) := by rfl


theorem t6_440part0 : t6_440jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_440frontier : t6_440root.frontier 0=t6_440jobs := by rfl
theorem t6_440all : t6_440jobs.all (Job.check tree)=true := by
  simp only [t6_440jobs,List.all_append,List.all_nil,t6_440part0,Bool.and_self]
theorem t6_440checked : Checked tree [1,8,3,10,7,7] := by
  refine ⟨plan6853,valid6853,t6_440choices,?_⟩
  exact check_of_frontier tree 0 t6_440root t6_440jobs t6_440frontier t6_440all
theorem t6_441choices : plan6854.choices=[1,8,3,10,10,7].map (options 6 4) := by rfl


theorem t6_441part0 : t6_441jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_441frontier : t6_441root.frontier 0=t6_441jobs := by rfl
theorem t6_441all : t6_441jobs.all (Job.check tree)=true := by
  simp only [t6_441jobs,List.all_append,List.all_nil,t6_441part0,Bool.and_self]
theorem t6_441checked : Checked tree [1,8,3,10,10,7] := by
  refine ⟨plan6854,valid6854,t6_441choices,?_⟩
  exact check_of_frontier tree 0 t6_441root t6_441jobs t6_441frontier t6_441all
theorem t6_442choices : plan6855.choices=[1,8,5,3,7,7].map (options 6 4) := by rfl


theorem t6_442part0 : t6_442jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_442frontier : t6_442root.frontier 0=t6_442jobs := by rfl
theorem t6_442all : t6_442jobs.all (Job.check tree)=true := by
  simp only [t6_442jobs,List.all_append,List.all_nil,t6_442part0,Bool.and_self]
theorem t6_442checked : Checked tree [1,8,5,3,7,7] := by
  refine ⟨plan6855,valid6855,t6_442choices,?_⟩
  exact check_of_frontier tree 0 t6_442root t6_442jobs t6_442frontier t6_442all
theorem t6_443choices : plan7276.choices=[1,8,5,6,7,7].map (options 6 5) := by rfl


theorem t6_443part0 : t6_443jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_443frontier : t6_443root.frontier 0=t6_443jobs := by rfl
theorem t6_443all : t6_443jobs.all (Job.check tree)=true := by
  simp only [t6_443jobs,List.all_append,List.all_nil,t6_443part0,Bool.and_self]
theorem t6_443checked : Checked tree [1,8,5,6,7,7] := by
  refine ⟨plan7276,valid7276,t6_443choices,?_⟩
  exact check_of_frontier tree 0 t6_443root t6_443jobs t6_443frontier t6_443all
theorem t6_444choices : plan7277.choices=[1,8,5,7,7,7].map (options 6 5) := by rfl


theorem t6_444part0 : t6_444jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_444frontier : t6_444root.frontier 0=t6_444jobs := by rfl
theorem t6_444all : t6_444jobs.all (Job.check tree)=true := by
  simp only [t6_444jobs,List.all_append,List.all_nil,t6_444part0,Bool.and_self]
theorem t6_444checked : Checked tree [1,8,5,7,7,7] := by
  refine ⟨plan7277,valid7277,t6_444choices,?_⟩
  exact check_of_frontier tree 0 t6_444root t6_444jobs t6_444frontier t6_444all
theorem t6_445choices : plan7278.choices=[1,8,5,10,7,7].map (options 6 5) := by rfl


theorem t6_445part0 : t6_445jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_445frontier : t6_445root.frontier 0=t6_445jobs := by rfl
theorem t6_445all : t6_445jobs.all (Job.check tree)=true := by
  simp only [t6_445jobs,List.all_append,List.all_nil,t6_445part0,Bool.and_self]
theorem t6_445checked : Checked tree [1,8,5,10,7,7] := by
  refine ⟨plan7278,valid7278,t6_445choices,?_⟩
  exact check_of_frontier tree 0 t6_445root t6_445jobs t6_445frontier t6_445all
theorem t6_446choices : plan7279.choices=[1,8,6,6,6,7].map (options 6 5) := by rfl


theorem t6_446part0 : t6_446jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_446frontier : t6_446root.frontier 0=t6_446jobs := by rfl
theorem t6_446all : t6_446jobs.all (Job.check tree)=true := by
  simp only [t6_446jobs,List.all_append,List.all_nil,t6_446part0,Bool.and_self]
theorem t6_446checked : Checked tree [1,8,6,6,6,7] := by
  refine ⟨plan7279,valid7279,t6_446choices,?_⟩
  exact check_of_frontier tree 0 t6_446root t6_446jobs t6_446frontier t6_446all
theorem t6_447choices : plan7280.choices=[1,8,6,6,7,7].map (options 6 5) := by rfl


theorem t6_447part0 : t6_447jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_447frontier : t6_447root.frontier 0=t6_447jobs := by rfl
theorem t6_447all : t6_447jobs.all (Job.check tree)=true := by
  simp only [t6_447jobs,List.all_append,List.all_nil,t6_447part0,Bool.and_self]
theorem t6_447checked : Checked tree [1,8,6,6,7,7] := by
  refine ⟨plan7280,valid7280,t6_447choices,?_⟩
  exact check_of_frontier tree 0 t6_447root t6_447jobs t6_447frontier t6_447all
theorem t6_448choices : plan7281.choices=[1,8,6,6,10,7].map (options 6 5) := by rfl


theorem t6_448part0 : t6_448jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_448frontier : t6_448root.frontier 0=t6_448jobs := by rfl
theorem t6_448all : t6_448jobs.all (Job.check tree)=true := by
  simp only [t6_448jobs,List.all_append,List.all_nil,t6_448part0,Bool.and_self]
theorem t6_448checked : Checked tree [1,8,6,6,10,7] := by
  refine ⟨plan7281,valid7281,t6_448choices,?_⟩
  exact check_of_frontier tree 0 t6_448root t6_448jobs t6_448frontier t6_448all
theorem t6_449choices : plan7282.choices=[1,8,6,7,7,7].map (options 6 5) := by rfl


theorem t6_449part0 : t6_449jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_449frontier : t6_449root.frontier 0=t6_449jobs := by rfl
theorem t6_449all : t6_449jobs.all (Job.check tree)=true := by
  simp only [t6_449jobs,List.all_append,List.all_nil,t6_449part0,Bool.and_self]
theorem t6_449checked : Checked tree [1,8,6,7,7,7] := by
  refine ⟨plan7282,valid7282,t6_449choices,?_⟩
  exact check_of_frontier tree 0 t6_449root t6_449jobs t6_449frontier t6_449all
theorem t6_450choices : plan7283.choices=[1,8,6,10,7,7].map (options 6 5) := by rfl


theorem t6_450part0 : t6_450jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_450frontier : t6_450root.frontier 0=t6_450jobs := by rfl
theorem t6_450all : t6_450jobs.all (Job.check tree)=true := by
  simp only [t6_450jobs,List.all_append,List.all_nil,t6_450part0,Bool.and_self]
theorem t6_450checked : Checked tree [1,8,6,10,7,7] := by
  refine ⟨plan7283,valid7283,t6_450choices,?_⟩
  exact check_of_frontier tree 0 t6_450root t6_450jobs t6_450frontier t6_450all
theorem t6_451choices : plan7284.choices=[1,8,6,10,10,7].map (options 6 5) := by rfl


theorem t6_451part0 : t6_451jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_451frontier : t6_451root.frontier 0=t6_451jobs := by rfl
theorem t6_451all : t6_451jobs.all (Job.check tree)=true := by
  simp only [t6_451jobs,List.all_append,List.all_nil,t6_451part0,Bool.and_self]
theorem t6_451checked : Checked tree [1,8,6,10,10,7] := by
  refine ⟨plan7284,valid7284,t6_451choices,?_⟩
  exact check_of_frontier tree 0 t6_451root t6_451jobs t6_451frontier t6_451all
theorem t6_452choices : plan7285.choices=[1,8,7,7,7,7].map (options 6 5) := by rfl


theorem t6_452part0 : t6_452jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_452frontier : t6_452root.frontier 0=t6_452jobs := by rfl
theorem t6_452all : t6_452jobs.all (Job.check tree)=true := by
  simp only [t6_452jobs,List.all_append,List.all_nil,t6_452part0,Bool.and_self]
theorem t6_452checked : Checked tree [1,8,7,7,7,7] := by
  refine ⟨plan7285,valid7285,t6_452choices,?_⟩
  exact check_of_frontier tree 0 t6_452root t6_452jobs t6_452frontier t6_452all
theorem t6_453choices : plan7286.choices=[1,8,8,7,7,7].map (options 6 5) := by rfl


theorem t6_453part0 : t6_453jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_453frontier : t6_453root.frontier 0=t6_453jobs := by rfl
theorem t6_453all : t6_453jobs.all (Job.check tree)=true := by
  simp only [t6_453jobs,List.all_append,List.all_nil,t6_453part0,Bool.and_self]
theorem t6_453checked : Checked tree [1,8,8,7,7,7] := by
  refine ⟨plan7286,valid7286,t6_453choices,?_⟩
  exact check_of_frontier tree 0 t6_453root t6_453jobs t6_453frontier t6_453all
theorem t6_454choices : plan6856.choices=[1,8,9,3,7,7].map (options 6 4) := by rfl


theorem t6_454part0 : t6_454jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_454frontier : t6_454root.frontier 0=t6_454jobs := by rfl
theorem t6_454all : t6_454jobs.all (Job.check tree)=true := by
  simp only [t6_454jobs,List.all_append,List.all_nil,t6_454part0,Bool.and_self]
theorem t6_454checked : Checked tree [1,8,9,3,7,7] := by
  refine ⟨plan6856,valid6856,t6_454choices,?_⟩
  exact check_of_frontier tree 0 t6_454root t6_454jobs t6_454frontier t6_454all
theorem t6_455choices : plan7287.choices=[1,8,9,6,7,7].map (options 6 5) := by rfl


theorem t6_455part0 : t6_455jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_455frontier : t6_455root.frontier 0=t6_455jobs := by rfl
theorem t6_455all : t6_455jobs.all (Job.check tree)=true := by
  simp only [t6_455jobs,List.all_append,List.all_nil,t6_455part0,Bool.and_self]
theorem t6_455checked : Checked tree [1,8,9,6,7,7] := by
  refine ⟨plan7287,valid7287,t6_455choices,?_⟩
  exact check_of_frontier tree 0 t6_455root t6_455jobs t6_455frontier t6_455all
theorem t6_456choices : plan7288.choices=[1,8,9,7,7,7].map (options 6 5) := by rfl


theorem t6_456part0 : t6_456jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_456frontier : t6_456root.frontier 0=t6_456jobs := by rfl
theorem t6_456all : t6_456jobs.all (Job.check tree)=true := by
  simp only [t6_456jobs,List.all_append,List.all_nil,t6_456part0,Bool.and_self]
theorem t6_456checked : Checked tree [1,8,9,7,7,7] := by
  refine ⟨plan7288,valid7288,t6_456choices,?_⟩
  exact check_of_frontier tree 0 t6_456root t6_456jobs t6_456frontier t6_456all
theorem t6_457choices : plan7289.choices=[1,8,9,10,7,7].map (options 6 5) := by rfl


theorem t6_457part0 : t6_457jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_457frontier : t6_457root.frontier 0=t6_457jobs := by rfl
theorem t6_457all : t6_457jobs.all (Job.check tree)=true := by
  simp only [t6_457jobs,List.all_append,List.all_nil,t6_457part0,Bool.and_self]
theorem t6_457checked : Checked tree [1,8,9,10,7,7] := by
  refine ⟨plan7289,valid7289,t6_457choices,?_⟩
  exact check_of_frontier tree 0 t6_457root t6_457jobs t6_457frontier t6_457all
theorem t6_458choices : plan7290.choices=[1,8,10,7,7,7].map (options 6 5) := by rfl


theorem t6_458part0 : t6_458jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_458frontier : t6_458root.frontier 0=t6_458jobs := by rfl
theorem t6_458all : t6_458jobs.all (Job.check tree)=true := by
  simp only [t6_458jobs,List.all_append,List.all_nil,t6_458part0,Bool.and_self]
theorem t6_458checked : Checked tree [1,8,10,7,7,7] := by
  refine ⟨plan7290,valid7290,t6_458choices,?_⟩
  exact check_of_frontier tree 0 t6_458root t6_458jobs t6_458frontier t6_458all
theorem t6_459choices : plan7291.choices=[1,8,10,10,7,7].map (options 6 5) := by rfl


theorem t6_459part0 : t6_459jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_459frontier : t6_459root.frontier 0=t6_459jobs := by rfl
theorem t6_459all : t6_459jobs.all (Job.check tree)=true := by
  simp only [t6_459jobs,List.all_append,List.all_nil,t6_459part0,Bool.and_self]
theorem t6_459checked : Checked tree [1,8,10,10,7,7] := by
  refine ⟨plan7291,valid7291,t6_459choices,?_⟩
  exact check_of_frontier tree 0 t6_459root t6_459jobs t6_459frontier t6_459all
theorem t6_460choices : plan7292.choices=[1,8,10,10,10,7].map (options 6 5) := by rfl


theorem t6_460part0 : t6_460jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_460frontier : t6_460root.frontier 0=t6_460jobs := by rfl
theorem t6_460all : t6_460jobs.all (Job.check tree)=true := by
  simp only [t6_460jobs,List.all_append,List.all_nil,t6_460part0,Bool.and_self]
theorem t6_460checked : Checked tree [1,8,10,10,10,7] := by
  refine ⟨plan7292,valid7292,t6_460choices,?_⟩
  exact check_of_frontier tree 0 t6_460root t6_460jobs t6_460frontier t6_460all
theorem t6_461choices : plan6296.choices=[1,9,3,3,3,3].map (options 6 1) := by rfl


theorem t6_461part0 : t6_461jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_461frontier : t6_461root.frontier 0=t6_461jobs := by rfl
theorem t6_461all : t6_461jobs.all (Job.check tree)=true := by
  simp only [t6_461jobs,List.all_append,List.all_nil,t6_461part0,Bool.and_self]
theorem t6_461checked : Checked tree [1,9,3,3,3,3] := by
  refine ⟨plan6296,valid6296,t6_461choices,?_⟩
  exact check_of_frontier tree 0 t6_461root t6_461jobs t6_461frontier t6_461all
theorem t6_462choices : plan6360.choices=[1,9,3,3,3,6].map (options 6 2) := by rfl


theorem t6_462part0 : t6_462jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_462frontier : t6_462root.frontier 0=t6_462jobs := by rfl
theorem t6_462all : t6_462jobs.all (Job.check tree)=true := by
  simp only [t6_462jobs,List.all_append,List.all_nil,t6_462part0,Bool.and_self]
theorem t6_462checked : Checked tree [1,9,3,3,3,6] := by
  refine ⟨plan6360,valid6360,t6_462choices,?_⟩
  exact check_of_frontier tree 0 t6_462root t6_462jobs t6_462frontier t6_462all
theorem t6_463choices : plan6361.choices=[1,9,3,3,3,7].map (options 6 2) := by rfl


theorem t6_463part0 : t6_463jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_463frontier : t6_463root.frontier 0=t6_463jobs := by rfl
theorem t6_463all : t6_463jobs.all (Job.check tree)=true := by
  simp only [t6_463jobs,List.all_append,List.all_nil,t6_463part0,Bool.and_self]
theorem t6_463checked : Checked tree [1,9,3,3,3,7] := by
  refine ⟨plan6361,valid6361,t6_463choices,?_⟩
  exact check_of_frontier tree 0 t6_463root t6_463jobs t6_463frontier t6_463all
theorem t6_464choices : plan6362.choices=[1,9,3,3,3,10].map (options 6 2) := by rfl


theorem t6_464part0 : t6_464jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_464frontier : t6_464root.frontier 0=t6_464jobs := by rfl
theorem t6_464all : t6_464jobs.all (Job.check tree)=true := by
  simp only [t6_464jobs,List.all_append,List.all_nil,t6_464part0,Bool.and_self]
theorem t6_464checked : Checked tree [1,9,3,3,3,10] := by
  refine ⟨plan6362,valid6362,t6_464choices,?_⟩
  exact check_of_frontier tree 0 t6_464root t6_464jobs t6_464frontier t6_464all
theorem t6_465choices : plan6529.choices=[1,9,3,3,6,6].map (options 6 3) := by rfl


theorem t6_465part0 : t6_465jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_465frontier : t6_465root.frontier 0=t6_465jobs := by rfl
theorem t6_465all : t6_465jobs.all (Job.check tree)=true := by
  simp only [t6_465jobs,List.all_append,List.all_nil,t6_465part0,Bool.and_self]
theorem t6_465checked : Checked tree [1,9,3,3,6,6] := by
  refine ⟨plan6529,valid6529,t6_465choices,?_⟩
  exact check_of_frontier tree 0 t6_465root t6_465jobs t6_465frontier t6_465all
theorem t6_466choices : plan6530.choices=[1,9,3,3,6,7].map (options 6 3) := by rfl


theorem t6_466part0 : t6_466jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_466part1 : t6_466jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_466frontier : t6_466root.frontier 1=t6_466jobs := by rfl
theorem t6_466all : t6_466jobs.all (Job.check tree)=true := by
  simp only [t6_466jobs,List.all_append,List.all_nil,t6_466part0,t6_466part1,Bool.and_self]
theorem t6_466checked : Checked tree [1,9,3,3,6,7] := by
  refine ⟨plan6530,valid6530,t6_466choices,?_⟩
  exact check_of_frontier tree 1 t6_466root t6_466jobs t6_466frontier t6_466all
theorem t6_467choices : plan6531.choices=[1,9,3,3,6,10].map (options 6 3) := by rfl


theorem t6_467part0 : t6_467jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_467frontier : t6_467root.frontier 0=t6_467jobs := by rfl
theorem t6_467all : t6_467jobs.all (Job.check tree)=true := by
  simp only [t6_467jobs,List.all_append,List.all_nil,t6_467part0,Bool.and_self]
theorem t6_467checked : Checked tree [1,9,3,3,6,10] := by
  refine ⟨plan6531,valid6531,t6_467choices,?_⟩
  exact check_of_frontier tree 0 t6_467root t6_467jobs t6_467frontier t6_467all
theorem t6_468choices : plan6532.choices=[1,9,3,3,7,7].map (options 6 3) := by rfl


theorem t6_468part0 : t6_468jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_468part1 : t6_468jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_468frontier : t6_468root.frontier 1=t6_468jobs := by rfl
theorem t6_468all : t6_468jobs.all (Job.check tree)=true := by
  simp only [t6_468jobs,List.all_append,List.all_nil,t6_468part0,t6_468part1,Bool.and_self]
theorem t6_468checked : Checked tree [1,9,3,3,7,7] := by
  refine ⟨plan6532,valid6532,t6_468choices,?_⟩
  exact check_of_frontier tree 1 t6_468root t6_468jobs t6_468frontier t6_468all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks059 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_434checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_435checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_436checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_437checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_438checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_439checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_440checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_441checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_442checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_443checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_444checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_445checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_446checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_447checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_448checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_449checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_450checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_423checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_451checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_452checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_453checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_454checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_455checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_456checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_457checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_458checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_459checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_460checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_424checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_461checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_462checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_463checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_464checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_465checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_466checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_467checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_468checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_425checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_426checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_427checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_428checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_429checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_430checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_431checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_432checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_433checked⟩
