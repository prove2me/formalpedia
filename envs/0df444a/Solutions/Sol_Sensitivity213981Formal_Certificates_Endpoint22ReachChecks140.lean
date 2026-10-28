-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks140
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:53:26.482351+00:00
-- url     : https://prove2.me/submissions/eb4799ae-c0c5-4795-934e-c887b959efe8

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks140
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks140
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
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

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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

















theorem valid557 : plan557.Valid := valid_step _ _ _ valid128 (by decide +kernel)



theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)

theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)

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























theorem valid1530 : plan1530.Valid := valid_step _ _ _ valid557 (by decide +kernel)



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

theorem valid1537 : plan1537.Valid := valid_step _ _ _ valid564 (by decide +kernel)













































theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)



theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)











theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

















































theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)



theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)



theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)





theorem valid1602 : plan1602.Valid := valid_step _ _ _ valid578 (by decide +kernel)



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













































































theorem valid3306 : plan3306.Valid := valid_step _ _ _ valid1532 (by decide +kernel)

theorem valid3307 : plan3307.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3308 : plan3308.Valid := valid_step _ _ _ valid1534 (by decide +kernel)

theorem valid3309 : plan3309.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3310 : plan3310.Valid := valid_step _ _ _ valid1536 (by decide +kernel)

theorem valid3311 : plan3311.Valid := valid_step _ _ _ valid1537 (by decide +kernel)

















































theorem valid3336 : plan3336.Valid := valid_step _ _ _ valid1530 (by decide +kernel)















































theorem valid3360 : plan3360.Valid := valid_step _ _ _ valid1569 (by decide +kernel)
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























































































































































theorem valid5356 : plan5356.Valid := valid_step _ _ _ valid3246 (by decide +kernel)








































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

































theorem valid5393 : plan5393.Valid := valid_step _ _ _ valid3265 (by decide +kernel)

theorem valid5394 : plan5394.Valid := valid_step _ _ _ valid3266 (by decide +kernel)

theorem valid5395 : plan5395.Valid := valid_step _ _ _ valid3267 (by decide +kernel)

























































































































































theorem valid5472 : plan5472.Valid := valid_step _ _ _ valid3336 (by decide +kernel)
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



























































































































































theorem valid6318 : plan6318.Valid := valid_step _ _ _ valid5356 (by decide +kernel)




































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











































































































theorem valid3414 : plan3414.Valid := valid_step _ _ _ valid1560 (by decide +kernel)



theorem valid3416 : plan3416.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3417 : plan3417.Valid := valid_step _ _ _ valid1563 (by decide +kernel)














































































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















theorem valid5480 : plan5480.Valid := valid_step _ _ _ valid3306 (by decide +kernel)

theorem valid5481 : plan5481.Valid := valid_step _ _ _ valid3307 (by decide +kernel)

theorem valid5482 : plan5482.Valid := valid_step _ _ _ valid3308 (by decide +kernel)

theorem valid5483 : plan5483.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5484 : plan5484.Valid := valid_step _ _ _ valid3310 (by decide +kernel)

theorem valid5485 : plan5485.Valid := valid_step _ _ _ valid3311 (by decide +kernel)






































































































































































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



































































theorem valid5602 : plan5602.Valid := valid_step _ _ _ valid3414 (by decide +kernel)

theorem valid5603 : plan5603.Valid := valid_step _ _ _ valid3416 (by decide +kernel)

theorem valid5604 : plan5604.Valid := valid_step _ _ _ valid3417 (by decide +kernel)



































theorem valid5622 : plan5622.Valid := valid_step _ _ _ valid3360 (by decide +kernel)




















































































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



























































































theorem valid6670 : plan6670.Valid := valid_step _ _ _ valid5472 (by decide +kernel)

theorem valid6671 : plan6671.Valid := valid_step _ _ _ valid5480 (by decide +kernel)

theorem valid6672 : plan6672.Valid := valid_step _ _ _ valid5481 (by decide +kernel)

theorem valid6673 : plan6673.Valid := valid_step _ _ _ valid5482 (by decide +kernel)

theorem valid6674 : plan6674.Valid := valid_step _ _ _ valid5483 (by decide +kernel)

theorem valid6675 : plan6675.Valid := valid_step _ _ _ valid5484 (by decide +kernel)

theorem valid6676 : plan6676.Valid := valid_step _ _ _ valid5485 (by decide +kernel)
























































































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

























































theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

















theorem valid3494 : plan3494.Valid := valid_step _ _ _ valid1594 (by decide +kernel)



theorem valid3496 : plan3496.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3497 : plan3497.Valid := valid_step _ _ _ valid1597 (by decide +kernel)



theorem valid3499 : plan3499.Valid := valid_step _ _ _ valid1599 (by decide +kernel)





theorem valid3502 : plan3502.Valid := valid_step _ _ _ valid1602 (by decide +kernel)



theorem valid3504 : plan3504.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3505 : plan3505.Valid := valid_step _ _ _ valid1605 (by decide +kernel)



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



























































































































































































theorem valid5758 : plan5758.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5759 : plan5759.Valid := valid_step _ _ _ valid3494 (by decide +kernel)

theorem valid5760 : plan5760.Valid := valid_step _ _ _ valid3496 (by decide +kernel)
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

theorem valid5761 : plan5761.Valid := valid_step _ _ _ valid3497 (by decide +kernel)

theorem valid5762 : plan5762.Valid := valid_step _ _ _ valid3499 (by decide +kernel)

theorem valid5763 : plan5763.Valid := valid_step _ _ _ valid3502 (by decide +kernel)

theorem valid5764 : plan5764.Valid := valid_step _ _ _ valid3504 (by decide +kernel)

theorem valid5765 : plan5765.Valid := valid_step _ _ _ valid3505 (by decide +kernel)

theorem valid5766 : plan5766.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5767 : plan5767.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5768 : plan5768.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5769 : plan5769.Valid := valid_step _ _ _ valid3510 (by decide +kernel)














































































































































































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

















































































































































































theorem valid6425 : plan6425.Valid := valid_step _ _ _ valid5393 (by decide +kernel)

theorem valid6426 : plan6426.Valid := valid_step _ _ _ valid5394 (by decide +kernel)

theorem valid6427 : plan6427.Valid := valid_step _ _ _ valid5395 (by decide +kernel)










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













































































































































































theorem valid7095 : plan7095.Valid := valid_step _ _ _ valid5602 (by decide +kernel)

theorem valid7096 : plan7096.Valid := valid_step _ _ _ valid5603 (by decide +kernel)

theorem valid7097 : plan7097.Valid := valid_step _ _ _ valid5604 (by decide +kernel)

theorem valid7098 : plan7098.Valid := valid_step _ _ _ valid5622 (by decide +kernel)












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









































theorem valid7605 : plan7605.Valid := valid_step _ _ _ valid5758 (by decide +kernel)

theorem valid7606 : plan7606.Valid := valid_step _ _ _ valid5759 (by decide +kernel)

theorem valid7607 : plan7607.Valid := valid_step _ _ _ valid5760 (by decide +kernel)

theorem valid7608 : plan7608.Valid := valid_step _ _ _ valid5761 (by decide +kernel)

theorem valid7609 : plan7609.Valid := valid_step _ _ _ valid5762 (by decide +kernel)

theorem valid7610 : plan7610.Valid := valid_step _ _ _ valid5763 (by decide +kernel)

theorem valid7611 : plan7611.Valid := valid_step _ _ _ valid5764 (by decide +kernel)

theorem valid7612 : plan7612.Valid := valid_step _ _ _ valid5765 (by decide +kernel)

theorem valid7613 : plan7613.Valid := valid_step _ _ _ valid5766 (by decide +kernel)

theorem valid7614 : plan7614.Valid := valid_step _ _ _ valid5767 (by decide +kernel)

theorem valid7615 : plan7615.Valid := valid_step _ _ _ valid5768 (by decide +kernel)

theorem valid7616 : plan7616.Valid := valid_step _ _ _ valid5769 (by decide +kernel)
































































































































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
theorem t6_1466choices : plan7605.choices=[8,2,7,7,7,7].map (options 6 5) := by rfl


theorem t6_1466part0 : t6_1466jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1466frontier : t6_1466root.frontier 0=t6_1466jobs := by rfl
theorem t6_1466all : t6_1466jobs.all (Job.check tree)=true := by
  simp only [t6_1466jobs,List.all_append,List.all_nil,t6_1466part0,Bool.and_self]
theorem t6_1466checked : Checked tree [8,2,7,7,7,7] := by
  refine ⟨plan7605,valid7605,t6_1466choices,?_⟩
  exact check_of_frontier tree 0 t6_1466root t6_1466jobs t6_1466frontier t6_1466all
theorem t6_1467choices : plan6670.choices=[8,2,9,3,3,7].map (options 6 3) := by rfl


theorem t6_1467part0 : t6_1467jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1467frontier : t6_1467root.frontier 0=t6_1467jobs := by rfl
theorem t6_1467all : t6_1467jobs.all (Job.check tree)=true := by
  simp only [t6_1467jobs,List.all_append,List.all_nil,t6_1467part0,Bool.and_self]
theorem t6_1467checked : Checked tree [8,2,9,3,3,7] := by
  refine ⟨plan6670,valid6670,t6_1467choices,?_⟩
  exact check_of_frontier tree 0 t6_1467root t6_1467jobs t6_1467frontier t6_1467all
theorem t6_1468choices : plan7095.choices=[8,2,9,3,6,7].map (options 6 4) := by rfl


theorem t6_1468part0 : t6_1468jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1468frontier : t6_1468root.frontier 0=t6_1468jobs := by rfl
theorem t6_1468all : t6_1468jobs.all (Job.check tree)=true := by
  simp only [t6_1468jobs,List.all_append,List.all_nil,t6_1468part0,Bool.and_self]
theorem t6_1468checked : Checked tree [8,2,9,3,6,7] := by
  refine ⟨plan7095,valid7095,t6_1468choices,?_⟩
  exact check_of_frontier tree 0 t6_1468root t6_1468jobs t6_1468frontier t6_1468all
theorem t6_1469choices : plan7096.choices=[8,2,9,3,7,7].map (options 6 4) := by rfl


theorem t6_1469part0 : t6_1469jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1469part1 : t6_1469jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1469frontier : t6_1469root.frontier 1=t6_1469jobs := by rfl
theorem t6_1469all : t6_1469jobs.all (Job.check tree)=true := by
  simp only [t6_1469jobs,List.all_append,List.all_nil,t6_1469part0,t6_1469part1,Bool.and_self]
theorem t6_1469checked : Checked tree [8,2,9,3,7,7] := by
  refine ⟨plan7096,valid7096,t6_1469choices,?_⟩
  exact check_of_frontier tree 1 t6_1469root t6_1469jobs t6_1469frontier t6_1469all
theorem t6_1470choices : plan7097.choices=[8,2,9,3,10,7].map (options 6 4) := by rfl


theorem t6_1470part0 : t6_1470jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1470frontier : t6_1470root.frontier 0=t6_1470jobs := by rfl
theorem t6_1470all : t6_1470jobs.all (Job.check tree)=true := by
  simp only [t6_1470jobs,List.all_append,List.all_nil,t6_1470part0,Bool.and_self]
theorem t6_1470checked : Checked tree [8,2,9,3,10,7] := by
  refine ⟨plan7097,valid7097,t6_1470choices,?_⟩
  exact check_of_frontier tree 0 t6_1470root t6_1470jobs t6_1470frontier t6_1470all
theorem t6_1471choices : plan7606.choices=[8,2,9,6,6,7].map (options 6 5) := by rfl


theorem t6_1471part0 : t6_1471jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1471frontier : t6_1471root.frontier 0=t6_1471jobs := by rfl
theorem t6_1471all : t6_1471jobs.all (Job.check tree)=true := by
  simp only [t6_1471jobs,List.all_append,List.all_nil,t6_1471part0,Bool.and_self]
theorem t6_1471checked : Checked tree [8,2,9,6,6,7] := by
  refine ⟨plan7606,valid7606,t6_1471choices,?_⟩
  exact check_of_frontier tree 0 t6_1471root t6_1471jobs t6_1471frontier t6_1471all
theorem t6_1472choices : plan7607.choices=[8,2,9,6,7,7].map (options 6 5) := by rfl


theorem t6_1472part0 : t6_1472jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1472frontier : t6_1472root.frontier 0=t6_1472jobs := by rfl
theorem t6_1472all : t6_1472jobs.all (Job.check tree)=true := by
  simp only [t6_1472jobs,List.all_append,List.all_nil,t6_1472part0,Bool.and_self]
theorem t6_1472checked : Checked tree [8,2,9,6,7,7] := by
  refine ⟨plan7607,valid7607,t6_1472choices,?_⟩
  exact check_of_frontier tree 0 t6_1472root t6_1472jobs t6_1472frontier t6_1472all
theorem t6_1473choices : plan7608.choices=[8,2,9,6,10,7].map (options 6 5) := by rfl


theorem t6_1473part0 : t6_1473jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1473frontier : t6_1473root.frontier 0=t6_1473jobs := by rfl
theorem t6_1473all : t6_1473jobs.all (Job.check tree)=true := by
  simp only [t6_1473jobs,List.all_append,List.all_nil,t6_1473part0,Bool.and_self]
theorem t6_1473checked : Checked tree [8,2,9,6,10,7] := by
  refine ⟨plan7608,valid7608,t6_1473choices,?_⟩
  exact check_of_frontier tree 0 t6_1473root t6_1473jobs t6_1473frontier t6_1473all
theorem t6_1474choices : plan7609.choices=[8,2,9,7,7,7].map (options 6 5) := by rfl


theorem t6_1474part0 : t6_1474jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1474frontier : t6_1474root.frontier 0=t6_1474jobs := by rfl
theorem t6_1474all : t6_1474jobs.all (Job.check tree)=true := by
  simp only [t6_1474jobs,List.all_append,List.all_nil,t6_1474part0,Bool.and_self]
theorem t6_1474checked : Checked tree [8,2,9,7,7,7] := by
  refine ⟨plan7609,valid7609,t6_1474choices,?_⟩
  exact check_of_frontier tree 0 t6_1474root t6_1474jobs t6_1474frontier t6_1474all
theorem t6_1475choices : plan7610.choices=[8,2,9,9,7,7].map (options 6 5) := by rfl


theorem t6_1475part0 : t6_1475jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1475frontier : t6_1475root.frontier 0=t6_1475jobs := by rfl
theorem t6_1475all : t6_1475jobs.all (Job.check tree)=true := by
  simp only [t6_1475jobs,List.all_append,List.all_nil,t6_1475part0,Bool.and_self]
theorem t6_1475checked : Checked tree [8,2,9,9,7,7] := by
  refine ⟨plan7610,valid7610,t6_1475choices,?_⟩
  exact check_of_frontier tree 0 t6_1475root t6_1475jobs t6_1475frontier t6_1475all
theorem t6_1476choices : plan7611.choices=[8,2,9,10,7,7].map (options 6 5) := by rfl


theorem t6_1476part0 : t6_1476jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1476frontier : t6_1476root.frontier 0=t6_1476jobs := by rfl
theorem t6_1476all : t6_1476jobs.all (Job.check tree)=true := by
  simp only [t6_1476jobs,List.all_append,List.all_nil,t6_1476part0,Bool.and_self]
theorem t6_1476checked : Checked tree [8,2,9,10,7,7] := by
  refine ⟨plan7611,valid7611,t6_1476choices,?_⟩
  exact check_of_frontier tree 0 t6_1476root t6_1476jobs t6_1476frontier t6_1476all
theorem t6_1477choices : plan7612.choices=[8,2,9,10,10,7].map (options 6 5) := by rfl


theorem t6_1477part0 : t6_1477jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1477frontier : t6_1477root.frontier 0=t6_1477jobs := by rfl
theorem t6_1477all : t6_1477jobs.all (Job.check tree)=true := by
  simp only [t6_1477jobs,List.all_append,List.all_nil,t6_1477part0,Bool.and_self]
theorem t6_1477checked : Checked tree [8,2,9,10,10,7] := by
  refine ⟨plan7612,valid7612,t6_1477choices,?_⟩
  exact check_of_frontier tree 0 t6_1477root t6_1477jobs t6_1477frontier t6_1477all
theorem t6_1478choices : plan7613.choices=[8,2,10,7,7,7].map (options 6 5) := by rfl


theorem t6_1478part0 : t6_1478jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1478frontier : t6_1478root.frontier 0=t6_1478jobs := by rfl
theorem t6_1478all : t6_1478jobs.all (Job.check tree)=true := by
  simp only [t6_1478jobs,List.all_append,List.all_nil,t6_1478part0,Bool.and_self]
theorem t6_1478checked : Checked tree [8,2,10,7,7,7] := by
  refine ⟨plan7613,valid7613,t6_1478choices,?_⟩
  exact check_of_frontier tree 0 t6_1478root t6_1478jobs t6_1478frontier t6_1478all
theorem t6_1479choices : plan7614.choices=[8,2,10,10,7,7].map (options 6 5) := by rfl


theorem t6_1479part0 : t6_1479jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1479frontier : t6_1479root.frontier 0=t6_1479jobs := by rfl
theorem t6_1479all : t6_1479jobs.all (Job.check tree)=true := by
  simp only [t6_1479jobs,List.all_append,List.all_nil,t6_1479part0,Bool.and_self]
theorem t6_1479checked : Checked tree [8,2,10,10,7,7] := by
  refine ⟨plan7614,valid7614,t6_1479choices,?_⟩
  exact check_of_frontier tree 0 t6_1479root t6_1479jobs t6_1479frontier t6_1479all
theorem t6_1480choices : plan7615.choices=[8,2,10,10,10,7].map (options 6 5) := by rfl


theorem t6_1480part0 : t6_1480jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1480frontier : t6_1480root.frontier 0=t6_1480jobs := by rfl
theorem t6_1480all : t6_1480jobs.all (Job.check tree)=true := by
  simp only [t6_1480jobs,List.all_append,List.all_nil,t6_1480part0,Bool.and_self]
theorem t6_1480checked : Checked tree [8,2,10,10,10,7] := by
  refine ⟨plan7615,valid7615,t6_1480choices,?_⟩
  exact check_of_frontier tree 0 t6_1480root t6_1480jobs t6_1480frontier t6_1480all
theorem t6_1481choices : plan7616.choices=[8,2,10,10,10,10].map (options 6 5) := by rfl


theorem t6_1481part0 : t6_1481jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1481frontier : t6_1481root.frontier 0=t6_1481jobs := by rfl
theorem t6_1481all : t6_1481jobs.all (Job.check tree)=true := by
  simp only [t6_1481jobs,List.all_append,List.all_nil,t6_1481part0,Bool.and_self]
theorem t6_1481checked : Checked tree [8,2,10,10,10,10] := by
  refine ⟨plan7616,valid7616,t6_1481choices,?_⟩
  exact check_of_frontier tree 0 t6_1481root t6_1481jobs t6_1481frontier t6_1481all
theorem t6_1482choices : plan6318.choices=[8,3,3,3,3,3].map (options 6 1) := by rfl


theorem t6_1482part0 : t6_1482jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1482frontier : t6_1482root.frontier 0=t6_1482jobs := by rfl
theorem t6_1482all : t6_1482jobs.all (Job.check tree)=true := by
  simp only [t6_1482jobs,List.all_append,List.all_nil,t6_1482part0,Bool.and_self]
theorem t6_1482checked : Checked tree [8,3,3,3,3,3] := by
  refine ⟨plan6318,valid6318,t6_1482choices,?_⟩
  exact check_of_frontier tree 0 t6_1482root t6_1482jobs t6_1482frontier t6_1482all
theorem t6_1483choices : plan6425.choices=[8,3,3,3,3,6].map (options 6 2) := by rfl


theorem t6_1483part0 : t6_1483jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1483frontier : t6_1483root.frontier 0=t6_1483jobs := by rfl
theorem t6_1483all : t6_1483jobs.all (Job.check tree)=true := by
  simp only [t6_1483jobs,List.all_append,List.all_nil,t6_1483part0,Bool.and_self]
theorem t6_1483checked : Checked tree [8,3,3,3,3,6] := by
  refine ⟨plan6425,valid6425,t6_1483choices,?_⟩
  exact check_of_frontier tree 0 t6_1483root t6_1483jobs t6_1483frontier t6_1483all
theorem t6_1484choices : plan6426.choices=[8,3,3,3,3,7].map (options 6 2) := by rfl


theorem t6_1484part0 : t6_1484jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1484frontier : t6_1484root.frontier 0=t6_1484jobs := by rfl
theorem t6_1484all : t6_1484jobs.all (Job.check tree)=true := by
  simp only [t6_1484jobs,List.all_append,List.all_nil,t6_1484part0,Bool.and_self]
theorem t6_1484checked : Checked tree [8,3,3,3,3,7] := by
  refine ⟨plan6426,valid6426,t6_1484choices,?_⟩
  exact check_of_frontier tree 0 t6_1484root t6_1484jobs t6_1484frontier t6_1484all
theorem t6_1485choices : plan6427.choices=[8,3,3,3,3,10].map (options 6 2) := by rfl


theorem t6_1485part0 : t6_1485jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1485frontier : t6_1485root.frontier 0=t6_1485jobs := by rfl
theorem t6_1485all : t6_1485jobs.all (Job.check tree)=true := by
  simp only [t6_1485jobs,List.all_append,List.all_nil,t6_1485part0,Bool.and_self]
theorem t6_1485checked : Checked tree [8,3,3,3,3,10] := by
  refine ⟨plan6427,valid6427,t6_1485choices,?_⟩
  exact check_of_frontier tree 0 t6_1485root t6_1485jobs t6_1485frontier t6_1485all
theorem t6_1486choices : plan6671.choices=[8,3,3,3,6,6].map (options 6 3) := by rfl


theorem t6_1486part0 : t6_1486jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1486frontier : t6_1486root.frontier 0=t6_1486jobs := by rfl
theorem t6_1486all : t6_1486jobs.all (Job.check tree)=true := by
  simp only [t6_1486jobs,List.all_append,List.all_nil,t6_1486part0,Bool.and_self]
theorem t6_1486checked : Checked tree [8,3,3,3,6,6] := by
  refine ⟨plan6671,valid6671,t6_1486choices,?_⟩
  exact check_of_frontier tree 0 t6_1486root t6_1486jobs t6_1486frontier t6_1486all
theorem t6_1487choices : plan6672.choices=[8,3,3,3,6,7].map (options 6 3) := by rfl


theorem t6_1487part0 : t6_1487jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1487part1 : t6_1487jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1487part2 : t6_1487jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1487frontier : t6_1487root.frontier 1=t6_1487jobs := by rfl
theorem t6_1487all : t6_1487jobs.all (Job.check tree)=true := by
  simp only [t6_1487jobs,List.all_append,List.all_nil,t6_1487part0,t6_1487part1,t6_1487part2,Bool.and_self]
theorem t6_1487checked : Checked tree [8,3,3,3,6,7] := by
  refine ⟨plan6672,valid6672,t6_1487choices,?_⟩
  exact check_of_frontier tree 1 t6_1487root t6_1487jobs t6_1487frontier t6_1487all
theorem t6_1488choices : plan6673.choices=[8,3,3,3,6,10].map (options 6 3) := by rfl


theorem t6_1488part0 : t6_1488jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1488frontier : t6_1488root.frontier 0=t6_1488jobs := by rfl
theorem t6_1488all : t6_1488jobs.all (Job.check tree)=true := by
  simp only [t6_1488jobs,List.all_append,List.all_nil,t6_1488part0,Bool.and_self]
theorem t6_1488checked : Checked tree [8,3,3,3,6,10] := by
  refine ⟨plan6673,valid6673,t6_1488choices,?_⟩
  exact check_of_frontier tree 0 t6_1488root t6_1488jobs t6_1488frontier t6_1488all
theorem t6_1489choices : plan6674.choices=[8,3,3,3,7,7].map (options 6 3) := by rfl


theorem t6_1489part0 : t6_1489jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1489part1 : t6_1489jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1489part2 : t6_1489jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1489frontier : t6_1489root.frontier 1=t6_1489jobs := by rfl
theorem t6_1489all : t6_1489jobs.all (Job.check tree)=true := by
  simp only [t6_1489jobs,List.all_append,List.all_nil,t6_1489part0,t6_1489part1,t6_1489part2,Bool.and_self]
theorem t6_1489checked : Checked tree [8,3,3,3,7,7] := by
  refine ⟨plan6674,valid6674,t6_1489choices,?_⟩
  exact check_of_frontier tree 1 t6_1489root t6_1489jobs t6_1489frontier t6_1489all
theorem t6_1490choices : plan6675.choices=[8,3,3,3,10,7].map (options 6 3) := by rfl


theorem t6_1490part0 : t6_1490jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1490part1 : t6_1490jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1490part2 : t6_1490jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1490frontier : t6_1490root.frontier 1=t6_1490jobs := by rfl
theorem t6_1490all : t6_1490jobs.all (Job.check tree)=true := by
  simp only [t6_1490jobs,List.all_append,List.all_nil,t6_1490part0,t6_1490part1,t6_1490part2,Bool.and_self]
theorem t6_1490checked : Checked tree [8,3,3,3,10,7] := by
  refine ⟨plan6675,valid6675,t6_1490choices,?_⟩
  exact check_of_frontier tree 1 t6_1490root t6_1490jobs t6_1490frontier t6_1490all
theorem t6_1491choices : plan6676.choices=[8,3,3,3,10,10].map (options 6 3) := by rfl


theorem t6_1491part0 : t6_1491jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1491frontier : t6_1491root.frontier 0=t6_1491jobs := by rfl
theorem t6_1491all : t6_1491jobs.all (Job.check tree)=true := by
  simp only [t6_1491jobs,List.all_append,List.all_nil,t6_1491part0,Bool.and_self]
theorem t6_1491checked : Checked tree [8,3,3,3,10,10] := by
  refine ⟨plan6676,valid6676,t6_1491choices,?_⟩
  exact check_of_frontier tree 0 t6_1491root t6_1491jobs t6_1491frontier t6_1491all
theorem t6_1492choices : plan7098.choices=[8,3,3,6,6,6].map (options 6 4) := by rfl


theorem t6_1492part0 : t6_1492jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1492frontier : t6_1492root.frontier 0=t6_1492jobs := by rfl
theorem t6_1492all : t6_1492jobs.all (Job.check tree)=true := by
  simp only [t6_1492jobs,List.all_append,List.all_nil,t6_1492part0,Bool.and_self]
theorem t6_1492checked : Checked tree [8,3,3,6,6,6] := by
  refine ⟨plan7098,valid7098,t6_1492choices,?_⟩
  exact check_of_frontier tree 0 t6_1492root t6_1492jobs t6_1492frontier t6_1492all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks140 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1466checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1478checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1479checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1480checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1481checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1482checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1483checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1484checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1485checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1486checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1487checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1467checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1488checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1489checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1490checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1491checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1492checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1468checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1469checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1470checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1471checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1472checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1473checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1474checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1475checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1476checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1477checked⟩
