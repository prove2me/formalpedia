-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks143
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:54:47.902021+00:00
-- url     : https://prove2.me/submissions/690381d8-474f-4e0e-a2df-9b438d2929fd

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks143
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks143
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans082
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



















































theorem valid122 : plan122.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid133 : plan133.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid134 : plan134.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid135 : plan135.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid136 : plan136.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid137 : plan137.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid138 : plan138.Valid := valid_step _ _ _ valid0 (by decide +kernel)












































































































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

theorem valid581 : plan581.Valid := valid_step _ _ _ valid136 (by decide +kernel)

theorem valid582 : plan582.Valid := valid_step _ _ _ valid137 (by decide +kernel)

theorem valid583 : plan583.Valid := valid_step _ _ _ valid138 (by decide +kernel)

theorem valid584 : plan584.Valid := valid_step _ _ _ valid137 (by decide +kernel)

theorem valid585 : plan585.Valid := valid_step _ _ _ valid137 (by decide +kernel)

theorem valid586 : plan586.Valid := valid_step _ _ _ valid138 (by decide +kernel)












































































































































































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

































































































































theorem valid545 : plan545.Valid := valid_step _ _ _ valid122 (by decide +kernel)





















theorem valid556 : plan556.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid557 : plan557.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid558 : plan558.Valid := valid_step _ _ _ valid129 (by decide +kernel)















theorem valid566 : plan566.Valid := valid_step _ _ _ valid131 (by decide +kernel)



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





















































































































































theorem valid1515 : plan1515.Valid := valid_step _ _ _ valid545 (by decide +kernel)



























theorem valid1529 : plan1529.Valid := valid_step _ _ _ valid556 (by decide +kernel)

theorem valid1530 : plan1530.Valid := valid_step _ _ _ valid557 (by decide +kernel)

theorem valid1531 : plan1531.Valid := valid_step _ _ _ valid558 (by decide +kernel)










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































































































































































































theorem valid3264 : plan3264.Valid := valid_step _ _ _ valid1515 (by decide +kernel)
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









































theorem valid1557 : plan1557.Valid := valid_step _ _ _ valid566 (by decide +kernel)



theorem valid1559 : plan1559.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1561 : plan1561.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1564 : plan1564.Valid := valid_step _ _ _ valid573 (by decide +kernel)







































theorem valid1584 : plan1584.Valid := valid_step _ _ _ valid576 (by decide +kernel)



theorem valid1586 : plan1586.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1587 : plan1587.Valid := valid_step _ _ _ valid579 (by decide +kernel)











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



theorem valid1608 : plan1608.Valid := valid_step _ _ _ valid584 (by decide +kernel)



theorem valid1610 : plan1610.Valid := valid_step _ _ _ valid581 (by decide +kernel)

theorem valid1611 : plan1611.Valid := valid_step _ _ _ valid582 (by decide +kernel)

theorem valid1612 : plan1612.Valid := valid_step _ _ _ valid583 (by decide +kernel)

theorem valid1613 : plan1613.Valid := valid_step _ _ _ valid584 (by decide +kernel)

theorem valid1614 : plan1614.Valid := valid_step _ _ _ valid585 (by decide +kernel)

theorem valid1615 : plan1615.Valid := valid_step _ _ _ valid586 (by decide +kernel)

theorem valid1616 : plan1616.Valid := valid_step _ _ _ valid584 (by decide +kernel)



theorem valid1618 : plan1618.Valid := valid_step _ _ _ valid584 (by decide +kernel)



theorem valid1620 : plan1620.Valid := valid_step _ _ _ valid584 (by decide +kernel)

theorem valid1621 : plan1621.Valid := valid_step _ _ _ valid585 (by decide +kernel)

theorem valid1622 : plan1622.Valid := valid_step _ _ _ valid586 (by decide +kernel)




















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













































































theorem valid3303 : plan3303.Valid := valid_step _ _ _ valid1529 (by decide +kernel)

theorem valid3304 : plan3304.Valid := valid_step _ _ _ valid1530 (by decide +kernel)

theorem valid3305 : plan3305.Valid := valid_step _ _ _ valid1531 (by decide +kernel)

































































































theorem valid3354 : plan3354.Valid := valid_step _ _ _ valid1559 (by decide +kernel)

theorem valid3355 : plan3355.Valid := valid_step _ _ _ valid1560 (by decide +kernel)

theorem valid3356 : plan3356.Valid := valid_step _ _ _ valid1561 (by decide +kernel)

theorem valid3357 : plan3357.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3358 : plan3358.Valid := valid_step _ _ _ valid1563 (by decide +kernel)

theorem valid3359 : plan3359.Valid := valid_step _ _ _ valid1564 (by decide +kernel)


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

theorem valid3553 : plan3553.Valid := valid_step _ _ _ valid1616 (by decide +kernel)

theorem valid3554 : plan3554.Valid := valid_step _ _ _ valid1620 (by decide +kernel)

theorem valid3555 : plan3555.Valid := valid_step _ _ _ valid1621 (by decide +kernel)

theorem valid3556 : plan3556.Valid := valid_step _ _ _ valid1622 (by decide +kernel)
























































































































































































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





















































theorem valid5403 : plan5403.Valid := valid_step _ _ _ valid3264 (by decide +kernel)










































































































































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























theorem valid3372 : plan3372.Valid := valid_step _ _ _ valid1557 (by decide +kernel)













































































theorem valid3411 : plan3411.Valid := valid_step _ _ _ valid1557 (by decide +kernel)

























































theorem valid3440 : plan3440.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3441 : plan3441.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3442 : plan3442.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3443 : plan3443.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3444 : plan3444.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3445 : plan3445.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3446 : plan3446.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3447 : plan3447.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3448 : plan3448.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3449 : plan3449.Valid := valid_step _ _ _ valid1606 (by decide +kernel)





theorem valid3452 : plan3452.Valid := valid_step _ _ _ valid1584 (by decide +kernel)



theorem valid3454 : plan3454.Valid := valid_step _ _ _ valid1586 (by decide +kernel)

theorem valid3455 : plan3455.Valid := valid_step _ _ _ valid1587 (by decide +kernel)


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

























































theorem valid5501 : plan5501.Valid := valid_step _ _ _ valid3303 (by decide +kernel)

theorem valid5502 : plan5502.Valid := valid_step _ _ _ valid3304 (by decide +kernel)

theorem valid5503 : plan5503.Valid := valid_step _ _ _ valid3305 (by decide +kernel)


































































































































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



























































































































































































theorem valid5662 : plan5662.Valid := valid_step _ _ _ valid3354 (by decide +kernel)

theorem valid5663 : plan5663.Valid := valid_step _ _ _ valid3355 (by decide +kernel)

theorem valid5664 : plan5664.Valid := valid_step _ _ _ valid3356 (by decide +kernel)
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









































































































theorem valid6677 : plan6677.Valid := valid_step _ _ _ valid5501 (by decide +kernel)

theorem valid6678 : plan6678.Valid := valid_step _ _ _ valid5502 (by decide +kernel)

theorem valid6679 : plan6679.Valid := valid_step _ _ _ valid5503 (by decide +kernel)


















































































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































































theorem valid3488 : plan3488.Valid := valid_step _ _ _ valid1584 (by decide +kernel)



theorem valid3490 : plan3490.Valid := valid_step _ _ _ valid1586 (by decide +kernel)

theorem valid3491 : plan3491.Valid := valid_step _ _ _ valid1587 (by decide +kernel)





































theorem valid3510 : plan3510.Valid := valid_step _ _ _ valid1606 (by decide +kernel)





theorem valid3513 : plan3513.Valid := valid_step _ _ _ valid1608 (by decide +kernel)





theorem valid3516 : plan3516.Valid := valid_step _ _ _ valid1611 (by decide +kernel)



theorem valid3518 : plan3518.Valid := valid_step _ _ _ valid1613 (by decide +kernel)

theorem valid3519 : plan3519.Valid := valid_step _ _ _ valid1614 (by decide +kernel)



theorem valid3521 : plan3521.Valid := valid_step _ _ _ valid1616 (by decide +kernel)



theorem valid3523 : plan3523.Valid := valid_step _ _ _ valid1618 (by decide +kernel)



theorem valid3525 : plan3525.Valid := valid_step _ _ _ valid1620 (by decide +kernel)

theorem valid3526 : plan3526.Valid := valid_step _ _ _ valid1621 (by decide +kernel)



theorem valid3528 : plan3528.Valid := valid_step _ _ _ valid1610 (by decide +kernel)

theorem valid3529 : plan3529.Valid := valid_step _ _ _ valid1611 (by decide +kernel)

theorem valid3530 : plan3530.Valid := valid_step _ _ _ valid1612 (by decide +kernel)

theorem valid3531 : plan3531.Valid := valid_step _ _ _ valid1613 (by decide +kernel)

theorem valid3532 : plan3532.Valid := valid_step _ _ _ valid1614 (by decide +kernel)

theorem valid3533 : plan3533.Valid := valid_step _ _ _ valid1615 (by decide +kernel)

theorem valid3534 : plan3534.Valid := valid_step _ _ _ valid1616 (by decide +kernel)

theorem valid3535 : plan3535.Valid := valid_step _ _ _ valid1620 (by decide +kernel)

theorem valid3536 : plan3536.Valid := valid_step _ _ _ valid1621 (by decide +kernel)

theorem valid3537 : plan3537.Valid := valid_step _ _ _ valid1622 (by decide +kernel)

theorem valid3538 : plan3538.Valid := valid_step _ _ _ valid1616 (by decide +kernel)





theorem valid3541 : plan3541.Valid := valid_step _ _ _ valid1611 (by decide +kernel)



theorem valid3543 : plan3543.Valid := valid_step _ _ _ valid1613 (by decide +kernel)

theorem valid3544 : plan3544.Valid := valid_step _ _ _ valid1614 (by decide +kernel)



theorem valid3546 : plan3546.Valid := valid_step _ _ _ valid1616 (by decide +kernel)



theorem valid3548 : plan3548.Valid := valid_step _ _ _ valid1618 (by decide +kernel)



theorem valid3550 : plan3550.Valid := valid_step _ _ _ valid1620 (by decide +kernel)

theorem valid3551 : plan3551.Valid := valid_step _ _ _ valid1621 (by decide +kernel)


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

theorem valid5665 : plan5665.Valid := valid_step _ _ _ valid3357 (by decide +kernel)

theorem valid5666 : plan5666.Valid := valid_step _ _ _ valid3358 (by decide +kernel)

theorem valid5667 : plan5667.Valid := valid_step _ _ _ valid3359 (by decide +kernel)























theorem valid5679 : plan5679.Valid := valid_step _ _ _ valid3372 (by decide +kernel)





















theorem valid5690 : plan5690.Valid := valid_step _ _ _ valid3411 (by decide +kernel)












































































































































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















































theorem valid5784 : plan5784.Valid := valid_step _ _ _ valid3510 (by decide +kernel)



























































theorem valid5814 : plan5814.Valid := valid_step _ _ _ valid3440 (by decide +kernel)

theorem valid5815 : plan5815.Valid := valid_step _ _ _ valid3441 (by decide +kernel)

theorem valid5816 : plan5816.Valid := valid_step _ _ _ valid3442 (by decide +kernel)

theorem valid5817 : plan5817.Valid := valid_step _ _ _ valid3443 (by decide +kernel)

theorem valid5818 : plan5818.Valid := valid_step _ _ _ valid3444 (by decide +kernel)

theorem valid5819 : plan5819.Valid := valid_step _ _ _ valid3445 (by decide +kernel)

theorem valid5820 : plan5820.Valid := valid_step _ _ _ valid3446 (by decide +kernel)

theorem valid5821 : plan5821.Valid := valid_step _ _ _ valid3447 (by decide +kernel)

theorem valid5822 : plan5822.Valid := valid_step _ _ _ valid3448 (by decide +kernel)

theorem valid5823 : plan5823.Valid := valid_step _ _ _ valid3449 (by decide +kernel)



theorem valid5825 : plan5825.Valid := valid_step _ _ _ valid3452 (by decide +kernel)



theorem valid5827 : plan5827.Valid := valid_step _ _ _ valid3454 (by decide +kernel)

theorem valid5828 : plan5828.Valid := valid_step _ _ _ valid3455 (by decide +kernel)
























































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







theorem valid5860 : plan5860.Valid := valid_step _ _ _ valid3488 (by decide +kernel)



theorem valid5862 : plan5862.Valid := valid_step _ _ _ valid3490 (by decide +kernel)

theorem valid5863 : plan5863.Valid := valid_step _ _ _ valid3491 (by decide +kernel)


















































































































































































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







theorem valid7108 : plan7108.Valid := valid_step _ _ _ valid5662 (by decide +kernel)

theorem valid7109 : plan7109.Valid := valid_step _ _ _ valid5663 (by decide +kernel)

theorem valid7110 : plan7110.Valid := valid_step _ _ _ valid5664 (by decide +kernel)

theorem valid7111 : plan7111.Valid := valid_step _ _ _ valid5665 (by decide +kernel)

theorem valid7112 : plan7112.Valid := valid_step _ _ _ valid5666 (by decide +kernel)

theorem valid7113 : plan7113.Valid := valid_step _ _ _ valid5667 (by decide +kernel)

theorem valid7114 : plan7114.Valid := valid_step _ _ _ valid5679 (by decide +kernel)

theorem valid7115 : plan7115.Valid := valid_step _ _ _ valid5690 (by decide +kernel)










































































































































































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























































































































































































theorem valid6428 : plan6428.Valid := valid_step _ _ _ valid5403 (by decide +kernel)








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























































































theorem valid5996 : plan5996.Valid := valid_step _ _ _ valid3513 (by decide +kernel)





theorem valid5999 : plan5999.Valid := valid_step _ _ _ valid3516 (by decide +kernel)



theorem valid6001 : plan6001.Valid := valid_step _ _ _ valid3518 (by decide +kernel)

theorem valid6002 : plan6002.Valid := valid_step _ _ _ valid3519 (by decide +kernel)



theorem valid6004 : plan6004.Valid := valid_step _ _ _ valid3521 (by decide +kernel)



theorem valid6006 : plan6006.Valid := valid_step _ _ _ valid3523 (by decide +kernel)



theorem valid6008 : plan6008.Valid := valid_step _ _ _ valid3525 (by decide +kernel)

theorem valid6009 : plan6009.Valid := valid_step _ _ _ valid3526 (by decide +kernel)



theorem valid6011 : plan6011.Valid := valid_step _ _ _ valid3528 (by decide +kernel)

theorem valid6012 : plan6012.Valid := valid_step _ _ _ valid3529 (by decide +kernel)

theorem valid6013 : plan6013.Valid := valid_step _ _ _ valid3530 (by decide +kernel)

theorem valid6014 : plan6014.Valid := valid_step _ _ _ valid3531 (by decide +kernel)

theorem valid6015 : plan6015.Valid := valid_step _ _ _ valid3532 (by decide +kernel)

theorem valid6016 : plan6016.Valid := valid_step _ _ _ valid3533 (by decide +kernel)

theorem valid6017 : plan6017.Valid := valid_step _ _ _ valid3534 (by decide +kernel)

theorem valid6018 : plan6018.Valid := valid_step _ _ _ valid3535 (by decide +kernel)

theorem valid6019 : plan6019.Valid := valid_step _ _ _ valid3536 (by decide +kernel)

theorem valid6020 : plan6020.Valid := valid_step _ _ _ valid3537 (by decide +kernel)

theorem valid6021 : plan6021.Valid := valid_step _ _ _ valid3538 (by decide +kernel)



theorem valid6023 : plan6023.Valid := valid_step _ _ _ valid3541 (by decide +kernel)



theorem valid6025 : plan6025.Valid := valid_step _ _ _ valid3543 (by decide +kernel)

theorem valid6026 : plan6026.Valid := valid_step _ _ _ valid3544 (by decide +kernel)



theorem valid6028 : plan6028.Valid := valid_step _ _ _ valid3546 (by decide +kernel)



theorem valid6030 : plan6030.Valid := valid_step _ _ _ valid3548 (by decide +kernel)



theorem valid6032 : plan6032.Valid := valid_step _ _ _ valid3550 (by decide +kernel)

theorem valid6033 : plan6033.Valid := valid_step _ _ _ valid3551 (by decide +kernel)



theorem valid6035 : plan6035.Valid := valid_step _ _ _ valid3553 (by decide +kernel)

theorem valid6036 : plan6036.Valid := valid_step _ _ _ valid3554 (by decide +kernel)

theorem valid6037 : plan6037.Valid := valid_step _ _ _ valid3555 (by decide +kernel)

theorem valid6038 : plan6038.Valid := valid_step _ _ _ valid3556 (by decide +kernel)

theorem valid6039 : plan6039.Valid := valid_step _ _ _ valid3528 (by decide +kernel)

theorem valid6040 : plan6040.Valid := valid_step _ _ _ valid3529 (by decide +kernel)

theorem valid6041 : plan6041.Valid := valid_step _ _ _ valid3530 (by decide +kernel)

theorem valid6042 : plan6042.Valid := valid_step _ _ _ valid3531 (by decide +kernel)

theorem valid6043 : plan6043.Valid := valid_step _ _ _ valid3532 (by decide +kernel)

theorem valid6044 : plan6044.Valid := valid_step _ _ _ valid3533 (by decide +kernel)

theorem valid6045 : plan6045.Valid := valid_step _ _ _ valid3534 (by decide +kernel)






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





























































































theorem valid7631 : plan7631.Valid := valid_step _ _ _ valid5784 (by decide +kernel)

theorem valid7632 : plan7632.Valid := valid_step _ _ _ valid5814 (by decide +kernel)

theorem valid7633 : plan7633.Valid := valid_step _ _ _ valid5815 (by decide +kernel)

theorem valid7634 : plan7634.Valid := valid_step _ _ _ valid5816 (by decide +kernel)

theorem valid7635 : plan7635.Valid := valid_step _ _ _ valid5817 (by decide +kernel)

theorem valid7636 : plan7636.Valid := valid_step _ _ _ valid5818 (by decide +kernel)

theorem valid7637 : plan7637.Valid := valid_step _ _ _ valid5819 (by decide +kernel)

theorem valid7638 : plan7638.Valid := valid_step _ _ _ valid5820 (by decide +kernel)

theorem valid7639 : plan7639.Valid := valid_step _ _ _ valid5821 (by decide +kernel)

theorem valid7640 : plan7640.Valid := valid_step _ _ _ valid5822 (by decide +kernel)

theorem valid7641 : plan7641.Valid := valid_step _ _ _ valid5823 (by decide +kernel)

theorem valid7642 : plan7642.Valid := valid_step _ _ _ valid5825 (by decide +kernel)

theorem valid7643 : plan7643.Valid := valid_step _ _ _ valid5827 (by decide +kernel)

theorem valid7644 : plan7644.Valid := valid_step _ _ _ valid5828 (by decide +kernel)

theorem valid7645 : plan7645.Valid := valid_step _ _ _ valid5860 (by decide +kernel)

theorem valid7646 : plan7646.Valid := valid_step _ _ _ valid5862 (by decide +kernel)

theorem valid7647 : plan7647.Valid := valid_step _ _ _ valid5863 (by decide +kernel)


































































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













































































































theorem valid7927 : plan7927.Valid := valid_step _ _ _ valid5996 (by decide +kernel)

theorem valid7928 : plan7928.Valid := valid_step _ _ _ valid5999 (by decide +kernel)

theorem valid7929 : plan7929.Valid := valid_step _ _ _ valid6001 (by decide +kernel)

theorem valid7930 : plan7930.Valid := valid_step _ _ _ valid6002 (by decide +kernel)

theorem valid7931 : plan7931.Valid := valid_step _ _ _ valid6004 (by decide +kernel)

theorem valid7932 : plan7932.Valid := valid_step _ _ _ valid6006 (by decide +kernel)

theorem valid7933 : plan7933.Valid := valid_step _ _ _ valid6008 (by decide +kernel)

theorem valid7934 : plan7934.Valid := valid_step _ _ _ valid6009 (by decide +kernel)

theorem valid7935 : plan7935.Valid := valid_step _ _ _ valid6011 (by decide +kernel)

theorem valid7936 : plan7936.Valid := valid_step _ _ _ valid6012 (by decide +kernel)

theorem valid7937 : plan7937.Valid := valid_step _ _ _ valid6013 (by decide +kernel)

theorem valid7938 : plan7938.Valid := valid_step _ _ _ valid6014 (by decide +kernel)

theorem valid7939 : plan7939.Valid := valid_step _ _ _ valid6015 (by decide +kernel)

theorem valid7940 : plan7940.Valid := valid_step _ _ _ valid6016 (by decide +kernel)

theorem valid7941 : plan7941.Valid := valid_step _ _ _ valid6017 (by decide +kernel)

theorem valid7942 : plan7942.Valid := valid_step _ _ _ valid6018 (by decide +kernel)

theorem valid7943 : plan7943.Valid := valid_step _ _ _ valid6019 (by decide +kernel)

theorem valid7944 : plan7944.Valid := valid_step _ _ _ valid6020 (by decide +kernel)

theorem valid7945 : plan7945.Valid := valid_step _ _ _ valid6021 (by decide +kernel)

theorem valid7946 : plan7946.Valid := valid_step _ _ _ valid6023 (by decide +kernel)

theorem valid7947 : plan7947.Valid := valid_step _ _ _ valid6025 (by decide +kernel)

theorem valid7948 : plan7948.Valid := valid_step _ _ _ valid6026 (by decide +kernel)

theorem valid7949 : plan7949.Valid := valid_step _ _ _ valid6028 (by decide +kernel)

theorem valid7950 : plan7950.Valid := valid_step _ _ _ valid6030 (by decide +kernel)

theorem valid7951 : plan7951.Valid := valid_step _ _ _ valid6032 (by decide +kernel)

theorem valid7952 : plan7952.Valid := valid_step _ _ _ valid6033 (by decide +kernel)

theorem valid7953 : plan7953.Valid := valid_step _ _ _ valid6035 (by decide +kernel)

theorem valid7954 : plan7954.Valid := valid_step _ _ _ valid6036 (by decide +kernel)

theorem valid7955 : plan7955.Valid := valid_step _ _ _ valid6037 (by decide +kernel)

theorem valid7956 : plan7956.Valid := valid_step _ _ _ valid6038 (by decide +kernel)

theorem valid7957 : plan7957.Valid := valid_step _ _ _ valid6039 (by decide +kernel)

theorem valid7958 : plan7958.Valid := valid_step _ _ _ valid6040 (by decide +kernel)

theorem valid7959 : plan7959.Valid := valid_step _ _ _ valid6041 (by decide +kernel)

theorem valid7960 : plan7960.Valid := valid_step _ _ _ valid6042 (by decide +kernel)

theorem valid7961 : plan7961.Valid := valid_step _ _ _ valid6043 (by decide +kernel)

theorem valid7962 : plan7962.Valid := valid_step _ _ _ valid6044 (by decide +kernel)

theorem valid7963 : plan7963.Valid := valid_step _ _ _ valid6045 (by decide +kernel)










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
theorem t6_1516choices : plan7631.choices=[8,3,10,10,10,10].map (options 6 5) := by rfl


theorem t6_1516part0 : t6_1516jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1516frontier : t6_1516root.frontier 0=t6_1516jobs := by rfl
theorem t6_1516all : t6_1516jobs.all (Job.check tree)=true := by
  simp only [t6_1516jobs,List.all_append,List.all_nil,t6_1516part0,Bool.and_self]
theorem t6_1516checked : Checked tree [8,3,10,10,10,10] := by
  refine ⟨plan7631,valid7631,t6_1516choices,?_⟩
  exact check_of_frontier tree 0 t6_1516root t6_1516jobs t6_1516frontier t6_1516all
theorem t6_1517choices : plan6428.choices=[8,5,3,3,3,3].map (options 6 2) := by rfl


theorem t6_1517part0 : t6_1517jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1517frontier : t6_1517root.frontier 0=t6_1517jobs := by rfl
theorem t6_1517all : t6_1517jobs.all (Job.check tree)=true := by
  simp only [t6_1517jobs,List.all_append,List.all_nil,t6_1517part0,Bool.and_self]
theorem t6_1517checked : Checked tree [8,5,3,3,3,3] := by
  refine ⟨plan6428,valid6428,t6_1517choices,?_⟩
  exact check_of_frontier tree 0 t6_1517root t6_1517jobs t6_1517frontier t6_1517all
theorem t6_1518choices : plan6677.choices=[8,5,3,3,3,6].map (options 6 3) := by rfl


theorem t6_1518part0 : t6_1518jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1518frontier : t6_1518root.frontier 0=t6_1518jobs := by rfl
theorem t6_1518all : t6_1518jobs.all (Job.check tree)=true := by
  simp only [t6_1518jobs,List.all_append,List.all_nil,t6_1518part0,Bool.and_self]
theorem t6_1518checked : Checked tree [8,5,3,3,3,6] := by
  refine ⟨plan6677,valid6677,t6_1518choices,?_⟩
  exact check_of_frontier tree 0 t6_1518root t6_1518jobs t6_1518frontier t6_1518all
theorem t6_1519choices : plan6678.choices=[8,5,3,3,3,7].map (options 6 3) := by rfl


theorem t6_1519part0 : t6_1519jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1519frontier : t6_1519root.frontier 0=t6_1519jobs := by rfl
theorem t6_1519all : t6_1519jobs.all (Job.check tree)=true := by
  simp only [t6_1519jobs,List.all_append,List.all_nil,t6_1519part0,Bool.and_self]
theorem t6_1519checked : Checked tree [8,5,3,3,3,7] := by
  refine ⟨plan6678,valid6678,t6_1519choices,?_⟩
  exact check_of_frontier tree 0 t6_1519root t6_1519jobs t6_1519frontier t6_1519all
theorem t6_1520choices : plan6679.choices=[8,5,3,3,3,10].map (options 6 3) := by rfl


theorem t6_1520part0 : t6_1520jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1520frontier : t6_1520root.frontier 0=t6_1520jobs := by rfl
theorem t6_1520all : t6_1520jobs.all (Job.check tree)=true := by
  simp only [t6_1520jobs,List.all_append,List.all_nil,t6_1520part0,Bool.and_self]
theorem t6_1520checked : Checked tree [8,5,3,3,3,10] := by
  refine ⟨plan6679,valid6679,t6_1520choices,?_⟩
  exact check_of_frontier tree 0 t6_1520root t6_1520jobs t6_1520frontier t6_1520all
theorem t6_1521choices : plan7108.choices=[8,5,3,3,6,6].map (options 6 4) := by rfl


theorem t6_1521part0 : t6_1521jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1521frontier : t6_1521root.frontier 0=t6_1521jobs := by rfl
theorem t6_1521all : t6_1521jobs.all (Job.check tree)=true := by
  simp only [t6_1521jobs,List.all_append,List.all_nil,t6_1521part0,Bool.and_self]
theorem t6_1521checked : Checked tree [8,5,3,3,6,6] := by
  refine ⟨plan7108,valid7108,t6_1521choices,?_⟩
  exact check_of_frontier tree 0 t6_1521root t6_1521jobs t6_1521frontier t6_1521all
theorem t6_1522choices : plan7109.choices=[8,5,3,3,6,7].map (options 6 4) := by rfl


theorem t6_1522part0 : t6_1522jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1522part1 : t6_1522jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1522frontier : t6_1522root.frontier 1=t6_1522jobs := by rfl
theorem t6_1522all : t6_1522jobs.all (Job.check tree)=true := by
  simp only [t6_1522jobs,List.all_append,List.all_nil,t6_1522part0,t6_1522part1,Bool.and_self]
theorem t6_1522checked : Checked tree [8,5,3,3,6,7] := by
  refine ⟨plan7109,valid7109,t6_1522choices,?_⟩
  exact check_of_frontier tree 1 t6_1522root t6_1522jobs t6_1522frontier t6_1522all
theorem t6_1523choices : plan7110.choices=[8,5,3,3,6,10].map (options 6 4) := by rfl


theorem t6_1523part0 : t6_1523jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1523frontier : t6_1523root.frontier 0=t6_1523jobs := by rfl
theorem t6_1523all : t6_1523jobs.all (Job.check tree)=true := by
  simp only [t6_1523jobs,List.all_append,List.all_nil,t6_1523part0,Bool.and_self]
theorem t6_1523checked : Checked tree [8,5,3,3,6,10] := by
  refine ⟨plan7110,valid7110,t6_1523choices,?_⟩
  exact check_of_frontier tree 0 t6_1523root t6_1523jobs t6_1523frontier t6_1523all
theorem t6_1524choices : plan7111.choices=[8,5,3,3,7,7].map (options 6 4) := by rfl


theorem t6_1524part0 : t6_1524jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1524part1 : t6_1524jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1524frontier : t6_1524root.frontier 1=t6_1524jobs := by rfl
theorem t6_1524all : t6_1524jobs.all (Job.check tree)=true := by
  simp only [t6_1524jobs,List.all_append,List.all_nil,t6_1524part0,t6_1524part1,Bool.and_self]
theorem t6_1524checked : Checked tree [8,5,3,3,7,7] := by
  refine ⟨plan7111,valid7111,t6_1524choices,?_⟩
  exact check_of_frontier tree 1 t6_1524root t6_1524jobs t6_1524frontier t6_1524all
theorem t6_1525choices : plan7112.choices=[8,5,3,3,10,7].map (options 6 4) := by rfl


theorem t6_1525part0 : t6_1525jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1525part1 : t6_1525jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1525frontier : t6_1525root.frontier 1=t6_1525jobs := by rfl
theorem t6_1525all : t6_1525jobs.all (Job.check tree)=true := by
  simp only [t6_1525jobs,List.all_append,List.all_nil,t6_1525part0,t6_1525part1,Bool.and_self]
theorem t6_1525checked : Checked tree [8,5,3,3,10,7] := by
  refine ⟨plan7112,valid7112,t6_1525choices,?_⟩
  exact check_of_frontier tree 1 t6_1525root t6_1525jobs t6_1525frontier t6_1525all
theorem t6_1526choices : plan7113.choices=[8,5,3,3,10,10].map (options 6 4) := by rfl


theorem t6_1526part0 : t6_1526jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1526frontier : t6_1526root.frontier 0=t6_1526jobs := by rfl
theorem t6_1526all : t6_1526jobs.all (Job.check tree)=true := by
  simp only [t6_1526jobs,List.all_append,List.all_nil,t6_1526part0,Bool.and_self]
theorem t6_1526checked : Checked tree [8,5,3,3,10,10] := by
  refine ⟨plan7113,valid7113,t6_1526choices,?_⟩
  exact check_of_frontier tree 0 t6_1526root t6_1526jobs t6_1526frontier t6_1526all
theorem t6_1527choices : plan7632.choices=[8,5,3,6,6,6].map (options 6 5) := by rfl


theorem t6_1527part0 : t6_1527jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1527frontier : t6_1527root.frontier 0=t6_1527jobs := by rfl
theorem t6_1527all : t6_1527jobs.all (Job.check tree)=true := by
  simp only [t6_1527jobs,List.all_append,List.all_nil,t6_1527part0,Bool.and_self]
theorem t6_1527checked : Checked tree [8,5,3,6,6,6] := by
  refine ⟨plan7632,valid7632,t6_1527choices,?_⟩
  exact check_of_frontier tree 0 t6_1527root t6_1527jobs t6_1527frontier t6_1527all
theorem t6_1528choices : plan7633.choices=[8,5,3,6,6,7].map (options 6 5) := by rfl


theorem t6_1528part0 : t6_1528jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1528frontier : t6_1528root.frontier 0=t6_1528jobs := by rfl
theorem t6_1528all : t6_1528jobs.all (Job.check tree)=true := by
  simp only [t6_1528jobs,List.all_append,List.all_nil,t6_1528part0,Bool.and_self]
theorem t6_1528checked : Checked tree [8,5,3,6,6,7] := by
  refine ⟨plan7633,valid7633,t6_1528choices,?_⟩
  exact check_of_frontier tree 0 t6_1528root t6_1528jobs t6_1528frontier t6_1528all
theorem t6_1529choices : plan7634.choices=[8,5,3,6,6,10].map (options 6 5) := by rfl


theorem t6_1529part0 : t6_1529jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1529frontier : t6_1529root.frontier 0=t6_1529jobs := by rfl
theorem t6_1529all : t6_1529jobs.all (Job.check tree)=true := by
  simp only [t6_1529jobs,List.all_append,List.all_nil,t6_1529part0,Bool.and_self]
theorem t6_1529checked : Checked tree [8,5,3,6,6,10] := by
  refine ⟨plan7634,valid7634,t6_1529choices,?_⟩
  exact check_of_frontier tree 0 t6_1529root t6_1529jobs t6_1529frontier t6_1529all
theorem t6_1530choices : plan7635.choices=[8,5,3,6,7,7].map (options 6 5) := by rfl


theorem t6_1530part0 : t6_1530jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1530part1 : t6_1530jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1530frontier : t6_1530root.frontier 1=t6_1530jobs := by rfl
theorem t6_1530all : t6_1530jobs.all (Job.check tree)=true := by
  simp only [t6_1530jobs,List.all_append,List.all_nil,t6_1530part0,t6_1530part1,Bool.and_self]
theorem t6_1530checked : Checked tree [8,5,3,6,7,7] := by
  refine ⟨plan7635,valid7635,t6_1530choices,?_⟩
  exact check_of_frontier tree 1 t6_1530root t6_1530jobs t6_1530frontier t6_1530all
theorem t6_1531choices : plan7636.choices=[8,5,3,6,10,7].map (options 6 5) := by rfl


theorem t6_1531part0 : t6_1531jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1531frontier : t6_1531root.frontier 0=t6_1531jobs := by rfl
theorem t6_1531all : t6_1531jobs.all (Job.check tree)=true := by
  simp only [t6_1531jobs,List.all_append,List.all_nil,t6_1531part0,Bool.and_self]
theorem t6_1531checked : Checked tree [8,5,3,6,10,7] := by
  refine ⟨plan7636,valid7636,t6_1531choices,?_⟩
  exact check_of_frontier tree 0 t6_1531root t6_1531jobs t6_1531frontier t6_1531all
theorem t6_1532choices : plan7637.choices=[8,5,3,6,10,10].map (options 6 5) := by rfl


theorem t6_1532part0 : t6_1532jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1532frontier : t6_1532root.frontier 0=t6_1532jobs := by rfl
theorem t6_1532all : t6_1532jobs.all (Job.check tree)=true := by
  simp only [t6_1532jobs,List.all_append,List.all_nil,t6_1532part0,Bool.and_self]
theorem t6_1532checked : Checked tree [8,5,3,6,10,10] := by
  refine ⟨plan7637,valid7637,t6_1532choices,?_⟩
  exact check_of_frontier tree 0 t6_1532root t6_1532jobs t6_1532frontier t6_1532all
theorem t6_1533choices : plan7638.choices=[8,5,3,7,7,7].map (options 6 5) := by rfl


theorem t6_1533part0 : t6_1533jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1533part1 : t6_1533jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1533frontier : t6_1533root.frontier 1=t6_1533jobs := by rfl
theorem t6_1533all : t6_1533jobs.all (Job.check tree)=true := by
  simp only [t6_1533jobs,List.all_append,List.all_nil,t6_1533part0,t6_1533part1,Bool.and_self]
theorem t6_1533checked : Checked tree [8,5,3,7,7,7] := by
  refine ⟨plan7638,valid7638,t6_1533choices,?_⟩
  exact check_of_frontier tree 1 t6_1533root t6_1533jobs t6_1533frontier t6_1533all
theorem t6_1534choices : plan7639.choices=[8,5,3,10,7,7].map (options 6 5) := by rfl


theorem t6_1534part0 : t6_1534jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1534part1 : t6_1534jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1534frontier : t6_1534root.frontier 1=t6_1534jobs := by rfl
theorem t6_1534all : t6_1534jobs.all (Job.check tree)=true := by
  simp only [t6_1534jobs,List.all_append,List.all_nil,t6_1534part0,t6_1534part1,Bool.and_self]
theorem t6_1534checked : Checked tree [8,5,3,10,7,7] := by
  refine ⟨plan7639,valid7639,t6_1534choices,?_⟩
  exact check_of_frontier tree 1 t6_1534root t6_1534jobs t6_1534frontier t6_1534all
theorem t6_1535choices : plan7640.choices=[8,5,3,10,10,7].map (options 6 5) := by rfl


theorem t6_1535part0 : t6_1535jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1535frontier : t6_1535root.frontier 0=t6_1535jobs := by rfl
theorem t6_1535all : t6_1535jobs.all (Job.check tree)=true := by
  simp only [t6_1535jobs,List.all_append,List.all_nil,t6_1535part0,Bool.and_self]
theorem t6_1535checked : Checked tree [8,5,3,10,10,7] := by
  refine ⟨plan7640,valid7640,t6_1535choices,?_⟩
  exact check_of_frontier tree 0 t6_1535root t6_1535jobs t6_1535frontier t6_1535all
theorem t6_1536choices : plan7641.choices=[8,5,3,10,10,10].map (options 6 5) := by rfl


theorem t6_1536part0 : t6_1536jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1536frontier : t6_1536root.frontier 0=t6_1536jobs := by rfl
theorem t6_1536all : t6_1536jobs.all (Job.check tree)=true := by
  simp only [t6_1536jobs,List.all_append,List.all_nil,t6_1536part0,Bool.and_self]
theorem t6_1536checked : Checked tree [8,5,3,10,10,10] := by
  refine ⟨plan7641,valid7641,t6_1536choices,?_⟩
  exact check_of_frontier tree 0 t6_1536root t6_1536jobs t6_1536frontier t6_1536all
theorem t6_1537choices : plan7114.choices=[8,5,5,3,3,7].map (options 6 4) := by rfl


theorem t6_1537part0 : t6_1537jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1537frontier : t6_1537root.frontier 0=t6_1537jobs := by rfl
theorem t6_1537all : t6_1537jobs.all (Job.check tree)=true := by
  simp only [t6_1537jobs,List.all_append,List.all_nil,t6_1537part0,Bool.and_self]
theorem t6_1537checked : Checked tree [8,5,5,3,3,7] := by
  refine ⟨plan7114,valid7114,t6_1537choices,?_⟩
  exact check_of_frontier tree 0 t6_1537root t6_1537jobs t6_1537frontier t6_1537all
theorem t6_1538choices : plan7642.choices=[8,5,5,3,6,7].map (options 6 5) := by rfl


theorem t6_1538part0 : t6_1538jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1538frontier : t6_1538root.frontier 0=t6_1538jobs := by rfl
theorem t6_1538all : t6_1538jobs.all (Job.check tree)=true := by
  simp only [t6_1538jobs,List.all_append,List.all_nil,t6_1538part0,Bool.and_self]
theorem t6_1538checked : Checked tree [8,5,5,3,6,7] := by
  refine ⟨plan7642,valid7642,t6_1538choices,?_⟩
  exact check_of_frontier tree 0 t6_1538root t6_1538jobs t6_1538frontier t6_1538all
theorem t6_1539choices : plan7643.choices=[8,5,5,3,7,7].map (options 6 5) := by rfl


theorem t6_1539part0 : t6_1539jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1539frontier : t6_1539root.frontier 0=t6_1539jobs := by rfl
theorem t6_1539all : t6_1539jobs.all (Job.check tree)=true := by
  simp only [t6_1539jobs,List.all_append,List.all_nil,t6_1539part0,Bool.and_self]
theorem t6_1539checked : Checked tree [8,5,5,3,7,7] := by
  refine ⟨plan7643,valid7643,t6_1539choices,?_⟩
  exact check_of_frontier tree 0 t6_1539root t6_1539jobs t6_1539frontier t6_1539all
theorem t6_1540choices : plan7644.choices=[8,5,5,3,10,7].map (options 6 5) := by rfl


theorem t6_1540part0 : t6_1540jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1540frontier : t6_1540root.frontier 0=t6_1540jobs := by rfl
theorem t6_1540all : t6_1540jobs.all (Job.check tree)=true := by
  simp only [t6_1540jobs,List.all_append,List.all_nil,t6_1540part0,Bool.and_self]
theorem t6_1540checked : Checked tree [8,5,5,3,10,7] := by
  refine ⟨plan7644,valid7644,t6_1540choices,?_⟩
  exact check_of_frontier tree 0 t6_1540root t6_1540jobs t6_1540frontier t6_1540all
theorem t6_1541choices : plan7927.choices=[8,5,5,5,7,7].map (options 6 6) := by rfl


theorem t6_1541part0 : t6_1541jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1541frontier : t6_1541root.frontier 0=t6_1541jobs := by rfl
theorem t6_1541all : t6_1541jobs.all (Job.check tree)=true := by
  simp only [t6_1541jobs,List.all_append,List.all_nil,t6_1541part0,Bool.and_self]
theorem t6_1541checked : Checked tree [8,5,5,5,7,7] := by
  refine ⟨plan7927,valid7927,t6_1541choices,?_⟩
  exact check_of_frontier tree 0 t6_1541root t6_1541jobs t6_1541frontier t6_1541all
theorem t6_1542choices : plan7928.choices=[8,5,5,6,6,7].map (options 6 6) := by rfl


theorem t6_1542part0 : t6_1542jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1542frontier : t6_1542root.frontier 0=t6_1542jobs := by rfl
theorem t6_1542all : t6_1542jobs.all (Job.check tree)=true := by
  simp only [t6_1542jobs,List.all_append,List.all_nil,t6_1542part0,Bool.and_self]
theorem t6_1542checked : Checked tree [8,5,5,6,6,7] := by
  refine ⟨plan7928,valid7928,t6_1542choices,?_⟩
  exact check_of_frontier tree 0 t6_1542root t6_1542jobs t6_1542frontier t6_1542all
theorem t6_1543choices : plan7929.choices=[8,5,5,6,7,7].map (options 6 6) := by rfl


theorem t6_1543part0 : t6_1543jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1543frontier : t6_1543root.frontier 0=t6_1543jobs := by rfl
theorem t6_1543all : t6_1543jobs.all (Job.check tree)=true := by
  simp only [t6_1543jobs,List.all_append,List.all_nil,t6_1543part0,Bool.and_self]
theorem t6_1543checked : Checked tree [8,5,5,6,7,7] := by
  refine ⟨plan7929,valid7929,t6_1543choices,?_⟩
  exact check_of_frontier tree 0 t6_1543root t6_1543jobs t6_1543frontier t6_1543all
theorem t6_1544choices : plan7930.choices=[8,5,5,6,10,7].map (options 6 6) := by rfl


theorem t6_1544part0 : t6_1544jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1544frontier : t6_1544root.frontier 0=t6_1544jobs := by rfl
theorem t6_1544all : t6_1544jobs.all (Job.check tree)=true := by
  simp only [t6_1544jobs,List.all_append,List.all_nil,t6_1544part0,Bool.and_self]
theorem t6_1544checked : Checked tree [8,5,5,6,10,7] := by
  refine ⟨plan7930,valid7930,t6_1544choices,?_⟩
  exact check_of_frontier tree 0 t6_1544root t6_1544jobs t6_1544frontier t6_1544all
theorem t6_1545choices : plan7931.choices=[8,5,5,7,7,7].map (options 6 6) := by rfl


theorem t6_1545part0 : t6_1545jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1545frontier : t6_1545root.frontier 0=t6_1545jobs := by rfl
theorem t6_1545all : t6_1545jobs.all (Job.check tree)=true := by
  simp only [t6_1545jobs,List.all_append,List.all_nil,t6_1545part0,Bool.and_self]
theorem t6_1545checked : Checked tree [8,5,5,7,7,7] := by
  refine ⟨plan7931,valid7931,t6_1545choices,?_⟩
  exact check_of_frontier tree 0 t6_1545root t6_1545jobs t6_1545frontier t6_1545all
theorem t6_1546choices : plan7932.choices=[8,5,5,9,7,7].map (options 6 6) := by rfl


theorem t6_1546part0 : t6_1546jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1546frontier : t6_1546root.frontier 0=t6_1546jobs := by rfl
theorem t6_1546all : t6_1546jobs.all (Job.check tree)=true := by
  simp only [t6_1546jobs,List.all_append,List.all_nil,t6_1546part0,Bool.and_self]
theorem t6_1546checked : Checked tree [8,5,5,9,7,7] := by
  refine ⟨plan7932,valid7932,t6_1546choices,?_⟩
  exact check_of_frontier tree 0 t6_1546root t6_1546jobs t6_1546frontier t6_1546all
theorem t6_1547choices : plan7933.choices=[8,5,5,10,7,7].map (options 6 6) := by rfl


theorem t6_1547part0 : t6_1547jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1547frontier : t6_1547root.frontier 0=t6_1547jobs := by rfl
theorem t6_1547all : t6_1547jobs.all (Job.check tree)=true := by
  simp only [t6_1547jobs,List.all_append,List.all_nil,t6_1547part0,Bool.and_self]
theorem t6_1547checked : Checked tree [8,5,5,10,7,7] := by
  refine ⟨plan7933,valid7933,t6_1547choices,?_⟩
  exact check_of_frontier tree 0 t6_1547root t6_1547jobs t6_1547frontier t6_1547all
theorem t6_1548choices : plan7934.choices=[8,5,5,10,10,7].map (options 6 6) := by rfl


theorem t6_1548part0 : t6_1548jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1548frontier : t6_1548root.frontier 0=t6_1548jobs := by rfl
theorem t6_1548all : t6_1548jobs.all (Job.check tree)=true := by
  simp only [t6_1548jobs,List.all_append,List.all_nil,t6_1548part0,Bool.and_self]
theorem t6_1548checked : Checked tree [8,5,5,10,10,7] := by
  refine ⟨plan7934,valid7934,t6_1548choices,?_⟩
  exact check_of_frontier tree 0 t6_1548root t6_1548jobs t6_1548frontier t6_1548all
theorem t6_1549choices : plan7935.choices=[8,5,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1549part0 : t6_1549jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1549frontier : t6_1549root.frontier 0=t6_1549jobs := by rfl
theorem t6_1549all : t6_1549jobs.all (Job.check tree)=true := by
  simp only [t6_1549jobs,List.all_append,List.all_nil,t6_1549part0,Bool.and_self]
theorem t6_1549checked : Checked tree [8,5,6,6,6,6] := by
  refine ⟨plan7935,valid7935,t6_1549choices,?_⟩
  exact check_of_frontier tree 0 t6_1549root t6_1549jobs t6_1549frontier t6_1549all
theorem t6_1550choices : plan7936.choices=[8,5,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1550part0 : t6_1550jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1550frontier : t6_1550root.frontier 0=t6_1550jobs := by rfl
theorem t6_1550all : t6_1550jobs.all (Job.check tree)=true := by
  simp only [t6_1550jobs,List.all_append,List.all_nil,t6_1550part0,Bool.and_self]
theorem t6_1550checked : Checked tree [8,5,6,6,6,7] := by
  refine ⟨plan7936,valid7936,t6_1550choices,?_⟩
  exact check_of_frontier tree 0 t6_1550root t6_1550jobs t6_1550frontier t6_1550all
theorem t6_1551choices : plan7937.choices=[8,5,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1551part0 : t6_1551jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1551frontier : t6_1551root.frontier 0=t6_1551jobs := by rfl
theorem t6_1551all : t6_1551jobs.all (Job.check tree)=true := by
  simp only [t6_1551jobs,List.all_append,List.all_nil,t6_1551part0,Bool.and_self]
theorem t6_1551checked : Checked tree [8,5,6,6,6,10] := by
  refine ⟨plan7937,valid7937,t6_1551choices,?_⟩
  exact check_of_frontier tree 0 t6_1551root t6_1551jobs t6_1551frontier t6_1551all
theorem t6_1552choices : plan7938.choices=[8,5,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1552part0 : t6_1552jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1552frontier : t6_1552root.frontier 0=t6_1552jobs := by rfl
theorem t6_1552all : t6_1552jobs.all (Job.check tree)=true := by
  simp only [t6_1552jobs,List.all_append,List.all_nil,t6_1552part0,Bool.and_self]
theorem t6_1552checked : Checked tree [8,5,6,6,7,7] := by
  refine ⟨plan7938,valid7938,t6_1552choices,?_⟩
  exact check_of_frontier tree 0 t6_1552root t6_1552jobs t6_1552frontier t6_1552all
theorem t6_1553choices : plan7939.choices=[8,5,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1553part0 : t6_1553jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1553frontier : t6_1553root.frontier 0=t6_1553jobs := by rfl
theorem t6_1553all : t6_1553jobs.all (Job.check tree)=true := by
  simp only [t6_1553jobs,List.all_append,List.all_nil,t6_1553part0,Bool.and_self]
theorem t6_1553checked : Checked tree [8,5,6,6,10,7] := by
  refine ⟨plan7939,valid7939,t6_1553choices,?_⟩
  exact check_of_frontier tree 0 t6_1553root t6_1553jobs t6_1553frontier t6_1553all
theorem t6_1554choices : plan7940.choices=[8,5,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1554part0 : t6_1554jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1554frontier : t6_1554root.frontier 0=t6_1554jobs := by rfl
theorem t6_1554all : t6_1554jobs.all (Job.check tree)=true := by
  simp only [t6_1554jobs,List.all_append,List.all_nil,t6_1554part0,Bool.and_self]
theorem t6_1554checked : Checked tree [8,5,6,6,10,10] := by
  refine ⟨plan7940,valid7940,t6_1554choices,?_⟩
  exact check_of_frontier tree 0 t6_1554root t6_1554jobs t6_1554frontier t6_1554all
theorem t6_1555choices : plan7941.choices=[8,5,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1555part0 : t6_1555jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1555frontier : t6_1555root.frontier 0=t6_1555jobs := by rfl
theorem t6_1555all : t6_1555jobs.all (Job.check tree)=true := by
  simp only [t6_1555jobs,List.all_append,List.all_nil,t6_1555part0,Bool.and_self]
theorem t6_1555checked : Checked tree [8,5,6,7,7,7] := by
  refine ⟨plan7941,valid7941,t6_1555choices,?_⟩
  exact check_of_frontier tree 0 t6_1555root t6_1555jobs t6_1555frontier t6_1555all
theorem t6_1556choices : plan7942.choices=[8,5,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1556part0 : t6_1556jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1556frontier : t6_1556root.frontier 0=t6_1556jobs := by rfl
theorem t6_1556all : t6_1556jobs.all (Job.check tree)=true := by
  simp only [t6_1556jobs,List.all_append,List.all_nil,t6_1556part0,Bool.and_self]
theorem t6_1556checked : Checked tree [8,5,6,10,7,7] := by
  refine ⟨plan7942,valid7942,t6_1556choices,?_⟩
  exact check_of_frontier tree 0 t6_1556root t6_1556jobs t6_1556frontier t6_1556all
theorem t6_1557choices : plan7943.choices=[8,5,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1557part0 : t6_1557jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1557frontier : t6_1557root.frontier 0=t6_1557jobs := by rfl
theorem t6_1557all : t6_1557jobs.all (Job.check tree)=true := by
  simp only [t6_1557jobs,List.all_append,List.all_nil,t6_1557part0,Bool.and_self]
theorem t6_1557checked : Checked tree [8,5,6,10,10,7] := by
  refine ⟨plan7943,valid7943,t6_1557choices,?_⟩
  exact check_of_frontier tree 0 t6_1557root t6_1557jobs t6_1557frontier t6_1557all
theorem t6_1558choices : plan7944.choices=[8,5,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1558part0 : t6_1558jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1558frontier : t6_1558root.frontier 0=t6_1558jobs := by rfl
theorem t6_1558all : t6_1558jobs.all (Job.check tree)=true := by
  simp only [t6_1558jobs,List.all_append,List.all_nil,t6_1558part0,Bool.and_self]
theorem t6_1558checked : Checked tree [8,5,6,10,10,10] := by
  refine ⟨plan7944,valid7944,t6_1558choices,?_⟩
  exact check_of_frontier tree 0 t6_1558root t6_1558jobs t6_1558frontier t6_1558all
theorem t6_1559choices : plan7945.choices=[8,5,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1559part0 : t6_1559jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1559frontier : t6_1559root.frontier 0=t6_1559jobs := by rfl
theorem t6_1559all : t6_1559jobs.all (Job.check tree)=true := by
  simp only [t6_1559jobs,List.all_append,List.all_nil,t6_1559part0,Bool.and_self]
theorem t6_1559checked : Checked tree [8,5,7,7,7,7] := by
  refine ⟨plan7945,valid7945,t6_1559choices,?_⟩
  exact check_of_frontier tree 0 t6_1559root t6_1559jobs t6_1559frontier t6_1559all
theorem t6_1560choices : plan7115.choices=[8,5,9,3,3,7].map (options 6 4) := by rfl


theorem t6_1560part0 : t6_1560jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1560frontier : t6_1560root.frontier 0=t6_1560jobs := by rfl
theorem t6_1560all : t6_1560jobs.all (Job.check tree)=true := by
  simp only [t6_1560jobs,List.all_append,List.all_nil,t6_1560part0,Bool.and_self]
theorem t6_1560checked : Checked tree [8,5,9,3,3,7] := by
  refine ⟨plan7115,valid7115,t6_1560choices,?_⟩
  exact check_of_frontier tree 0 t6_1560root t6_1560jobs t6_1560frontier t6_1560all
theorem t6_1561choices : plan7645.choices=[8,5,9,3,6,7].map (options 6 5) := by rfl


theorem t6_1561part0 : t6_1561jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1561frontier : t6_1561root.frontier 0=t6_1561jobs := by rfl
theorem t6_1561all : t6_1561jobs.all (Job.check tree)=true := by
  simp only [t6_1561jobs,List.all_append,List.all_nil,t6_1561part0,Bool.and_self]
theorem t6_1561checked : Checked tree [8,5,9,3,6,7] := by
  refine ⟨plan7645,valid7645,t6_1561choices,?_⟩
  exact check_of_frontier tree 0 t6_1561root t6_1561jobs t6_1561frontier t6_1561all
theorem t6_1562choices : plan7646.choices=[8,5,9,3,7,7].map (options 6 5) := by rfl


theorem t6_1562part0 : t6_1562jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1562frontier : t6_1562root.frontier 0=t6_1562jobs := by rfl
theorem t6_1562all : t6_1562jobs.all (Job.check tree)=true := by
  simp only [t6_1562jobs,List.all_append,List.all_nil,t6_1562part0,Bool.and_self]
theorem t6_1562checked : Checked tree [8,5,9,3,7,7] := by
  refine ⟨plan7646,valid7646,t6_1562choices,?_⟩
  exact check_of_frontier tree 0 t6_1562root t6_1562jobs t6_1562frontier t6_1562all
theorem t6_1563choices : plan7647.choices=[8,5,9,3,10,7].map (options 6 5) := by rfl


theorem t6_1563part0 : t6_1563jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1563frontier : t6_1563root.frontier 0=t6_1563jobs := by rfl
theorem t6_1563all : t6_1563jobs.all (Job.check tree)=true := by
  simp only [t6_1563jobs,List.all_append,List.all_nil,t6_1563part0,Bool.and_self]
theorem t6_1563checked : Checked tree [8,5,9,3,10,7] := by
  refine ⟨plan7647,valid7647,t6_1563choices,?_⟩
  exact check_of_frontier tree 0 t6_1563root t6_1563jobs t6_1563frontier t6_1563all
theorem t6_1564choices : plan7946.choices=[8,5,9,6,6,7].map (options 6 6) := by rfl


theorem t6_1564part0 : t6_1564jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1564frontier : t6_1564root.frontier 0=t6_1564jobs := by rfl
theorem t6_1564all : t6_1564jobs.all (Job.check tree)=true := by
  simp only [t6_1564jobs,List.all_append,List.all_nil,t6_1564part0,Bool.and_self]
theorem t6_1564checked : Checked tree [8,5,9,6,6,7] := by
  refine ⟨plan7946,valid7946,t6_1564choices,?_⟩
  exact check_of_frontier tree 0 t6_1564root t6_1564jobs t6_1564frontier t6_1564all
theorem t6_1565choices : plan7947.choices=[8,5,9,6,7,7].map (options 6 6) := by rfl


theorem t6_1565part0 : t6_1565jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1565frontier : t6_1565root.frontier 0=t6_1565jobs := by rfl
theorem t6_1565all : t6_1565jobs.all (Job.check tree)=true := by
  simp only [t6_1565jobs,List.all_append,List.all_nil,t6_1565part0,Bool.and_self]
theorem t6_1565checked : Checked tree [8,5,9,6,7,7] := by
  refine ⟨plan7947,valid7947,t6_1565choices,?_⟩
  exact check_of_frontier tree 0 t6_1565root t6_1565jobs t6_1565frontier t6_1565all
theorem t6_1566choices : plan7948.choices=[8,5,9,6,10,7].map (options 6 6) := by rfl


theorem t6_1566part0 : t6_1566jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1566frontier : t6_1566root.frontier 0=t6_1566jobs := by rfl
theorem t6_1566all : t6_1566jobs.all (Job.check tree)=true := by
  simp only [t6_1566jobs,List.all_append,List.all_nil,t6_1566part0,Bool.and_self]
theorem t6_1566checked : Checked tree [8,5,9,6,10,7] := by
  refine ⟨plan7948,valid7948,t6_1566choices,?_⟩
  exact check_of_frontier tree 0 t6_1566root t6_1566jobs t6_1566frontier t6_1566all
theorem t6_1567choices : plan7949.choices=[8,5,9,7,7,7].map (options 6 6) := by rfl


theorem t6_1567part0 : t6_1567jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1567frontier : t6_1567root.frontier 0=t6_1567jobs := by rfl
theorem t6_1567all : t6_1567jobs.all (Job.check tree)=true := by
  simp only [t6_1567jobs,List.all_append,List.all_nil,t6_1567part0,Bool.and_self]
theorem t6_1567checked : Checked tree [8,5,9,7,7,7] := by
  refine ⟨plan7949,valid7949,t6_1567choices,?_⟩
  exact check_of_frontier tree 0 t6_1567root t6_1567jobs t6_1567frontier t6_1567all
theorem t6_1568choices : plan7950.choices=[8,5,9,9,7,7].map (options 6 6) := by rfl


theorem t6_1568part0 : t6_1568jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1568frontier : t6_1568root.frontier 0=t6_1568jobs := by rfl
theorem t6_1568all : t6_1568jobs.all (Job.check tree)=true := by
  simp only [t6_1568jobs,List.all_append,List.all_nil,t6_1568part0,Bool.and_self]
theorem t6_1568checked : Checked tree [8,5,9,9,7,7] := by
  refine ⟨plan7950,valid7950,t6_1568choices,?_⟩
  exact check_of_frontier tree 0 t6_1568root t6_1568jobs t6_1568frontier t6_1568all
theorem t6_1569choices : plan7951.choices=[8,5,9,10,7,7].map (options 6 6) := by rfl


theorem t6_1569part0 : t6_1569jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1569frontier : t6_1569root.frontier 0=t6_1569jobs := by rfl
theorem t6_1569all : t6_1569jobs.all (Job.check tree)=true := by
  simp only [t6_1569jobs,List.all_append,List.all_nil,t6_1569part0,Bool.and_self]
theorem t6_1569checked : Checked tree [8,5,9,10,7,7] := by
  refine ⟨plan7951,valid7951,t6_1569choices,?_⟩
  exact check_of_frontier tree 0 t6_1569root t6_1569jobs t6_1569frontier t6_1569all
theorem t6_1570choices : plan7952.choices=[8,5,9,10,10,7].map (options 6 6) := by rfl


theorem t6_1570part0 : t6_1570jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1570frontier : t6_1570root.frontier 0=t6_1570jobs := by rfl
theorem t6_1570all : t6_1570jobs.all (Job.check tree)=true := by
  simp only [t6_1570jobs,List.all_append,List.all_nil,t6_1570part0,Bool.and_self]
theorem t6_1570checked : Checked tree [8,5,9,10,10,7] := by
  refine ⟨plan7952,valid7952,t6_1570choices,?_⟩
  exact check_of_frontier tree 0 t6_1570root t6_1570jobs t6_1570frontier t6_1570all
theorem t6_1571choices : plan7953.choices=[8,5,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1571part0 : t6_1571jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1571frontier : t6_1571root.frontier 0=t6_1571jobs := by rfl
theorem t6_1571all : t6_1571jobs.all (Job.check tree)=true := by
  simp only [t6_1571jobs,List.all_append,List.all_nil,t6_1571part0,Bool.and_self]
theorem t6_1571checked : Checked tree [8,5,10,7,7,7] := by
  refine ⟨plan7953,valid7953,t6_1571choices,?_⟩
  exact check_of_frontier tree 0 t6_1571root t6_1571jobs t6_1571frontier t6_1571all
theorem t6_1572choices : plan7954.choices=[8,5,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1572part0 : t6_1572jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1572frontier : t6_1572root.frontier 0=t6_1572jobs := by rfl
theorem t6_1572all : t6_1572jobs.all (Job.check tree)=true := by
  simp only [t6_1572jobs,List.all_append,List.all_nil,t6_1572part0,Bool.and_self]
theorem t6_1572checked : Checked tree [8,5,10,10,7,7] := by
  refine ⟨plan7954,valid7954,t6_1572choices,?_⟩
  exact check_of_frontier tree 0 t6_1572root t6_1572jobs t6_1572frontier t6_1572all
theorem t6_1573choices : plan7955.choices=[8,5,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1573part0 : t6_1573jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1573frontier : t6_1573root.frontier 0=t6_1573jobs := by rfl
theorem t6_1573all : t6_1573jobs.all (Job.check tree)=true := by
  simp only [t6_1573jobs,List.all_append,List.all_nil,t6_1573part0,Bool.and_self]
theorem t6_1573checked : Checked tree [8,5,10,10,10,7] := by
  refine ⟨plan7955,valid7955,t6_1573choices,?_⟩
  exact check_of_frontier tree 0 t6_1573root t6_1573jobs t6_1573frontier t6_1573all
theorem t6_1574choices : plan7956.choices=[8,5,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1574part0 : t6_1574jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1574frontier : t6_1574root.frontier 0=t6_1574jobs := by rfl
theorem t6_1574all : t6_1574jobs.all (Job.check tree)=true := by
  simp only [t6_1574jobs,List.all_append,List.all_nil,t6_1574part0,Bool.and_self]
theorem t6_1574checked : Checked tree [8,5,10,10,10,10] := by
  refine ⟨plan7956,valid7956,t6_1574choices,?_⟩
  exact check_of_frontier tree 0 t6_1574root t6_1574jobs t6_1574frontier t6_1574all
theorem t6_1575choices : plan7957.choices=[8,6,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1575part0 : t6_1575jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1575frontier : t6_1575root.frontier 0=t6_1575jobs := by rfl
theorem t6_1575all : t6_1575jobs.all (Job.check tree)=true := by
  simp only [t6_1575jobs,List.all_append,List.all_nil,t6_1575part0,Bool.and_self]
theorem t6_1575checked : Checked tree [8,6,6,6,6,6] := by
  refine ⟨plan7957,valid7957,t6_1575choices,?_⟩
  exact check_of_frontier tree 0 t6_1575root t6_1575jobs t6_1575frontier t6_1575all
theorem t6_1576choices : plan7958.choices=[8,6,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1576part0 : t6_1576jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1576frontier : t6_1576root.frontier 0=t6_1576jobs := by rfl
theorem t6_1576all : t6_1576jobs.all (Job.check tree)=true := by
  simp only [t6_1576jobs,List.all_append,List.all_nil,t6_1576part0,Bool.and_self]
theorem t6_1576checked : Checked tree [8,6,6,6,6,7] := by
  refine ⟨plan7958,valid7958,t6_1576choices,?_⟩
  exact check_of_frontier tree 0 t6_1576root t6_1576jobs t6_1576frontier t6_1576all
theorem t6_1577choices : plan7959.choices=[8,6,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1577part0 : t6_1577jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1577frontier : t6_1577root.frontier 0=t6_1577jobs := by rfl
theorem t6_1577all : t6_1577jobs.all (Job.check tree)=true := by
  simp only [t6_1577jobs,List.all_append,List.all_nil,t6_1577part0,Bool.and_self]
theorem t6_1577checked : Checked tree [8,6,6,6,6,10] := by
  refine ⟨plan7959,valid7959,t6_1577choices,?_⟩
  exact check_of_frontier tree 0 t6_1577root t6_1577jobs t6_1577frontier t6_1577all
theorem t6_1578choices : plan7960.choices=[8,6,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1578part0 : t6_1578jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1578frontier : t6_1578root.frontier 0=t6_1578jobs := by rfl
theorem t6_1578all : t6_1578jobs.all (Job.check tree)=true := by
  simp only [t6_1578jobs,List.all_append,List.all_nil,t6_1578part0,Bool.and_self]
theorem t6_1578checked : Checked tree [8,6,6,6,7,7] := by
  refine ⟨plan7960,valid7960,t6_1578choices,?_⟩
  exact check_of_frontier tree 0 t6_1578root t6_1578jobs t6_1578frontier t6_1578all
theorem t6_1579choices : plan7961.choices=[8,6,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1579part0 : t6_1579jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1579frontier : t6_1579root.frontier 0=t6_1579jobs := by rfl
theorem t6_1579all : t6_1579jobs.all (Job.check tree)=true := by
  simp only [t6_1579jobs,List.all_append,List.all_nil,t6_1579part0,Bool.and_self]
theorem t6_1579checked : Checked tree [8,6,6,6,10,7] := by
  refine ⟨plan7961,valid7961,t6_1579choices,?_⟩
  exact check_of_frontier tree 0 t6_1579root t6_1579jobs t6_1579frontier t6_1579all
theorem t6_1580choices : plan7962.choices=[8,6,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1580part0 : t6_1580jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1580frontier : t6_1580root.frontier 0=t6_1580jobs := by rfl
theorem t6_1580all : t6_1580jobs.all (Job.check tree)=true := by
  simp only [t6_1580jobs,List.all_append,List.all_nil,t6_1580part0,Bool.and_self]
theorem t6_1580checked : Checked tree [8,6,6,6,10,10] := by
  refine ⟨plan7962,valid7962,t6_1580choices,?_⟩
  exact check_of_frontier tree 0 t6_1580root t6_1580jobs t6_1580frontier t6_1580all
theorem t6_1581choices : plan7963.choices=[8,6,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1581part0 : t6_1581jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1581frontier : t6_1581root.frontier 0=t6_1581jobs := by rfl
theorem t6_1581all : t6_1581jobs.all (Job.check tree)=true := by
  simp only [t6_1581jobs,List.all_append,List.all_nil,t6_1581part0,Bool.and_self]
theorem t6_1581checked : Checked tree [8,6,6,7,7,7] := by
  refine ⟨plan7963,valid7963,t6_1581choices,?_⟩
  exact check_of_frontier tree 0 t6_1581root t6_1581jobs t6_1581frontier t6_1581all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks143 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1527checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1516checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1528checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1529checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1530checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1531checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1532checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1533checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1534checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1535checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1536checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1517checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1537checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1538checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1539checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1540checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1541checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1542checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1543checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1544checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1545checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1518checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1546checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1547checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1548checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1549checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1550checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1551checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1552checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1553checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1554checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1555checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1519checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1556checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1557checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1558checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1559checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1560checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1561checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1562checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1563checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1564checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1565checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1520checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1566checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1567checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1568checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1569checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1570checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1571checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1572checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1573checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1574checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1575checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1521checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1576checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1577checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1578checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1579checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1580checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1581checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1522checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1523checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1524checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1525checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1526checked⟩
