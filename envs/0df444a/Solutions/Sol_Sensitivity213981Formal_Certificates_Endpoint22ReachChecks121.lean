-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks121
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:45:45.953991+00:00
-- url     : https://prove2.me/submissions/cec924fa-f605-4bf5-bd74-e8fc5004ee02

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks121
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks121
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans080
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

























theorem valid6637 : plan6637.Valid := valid_step _ _ _ valid5501 (by decide +kernel)

theorem valid6638 : plan6638.Valid := valid_step _ _ _ valid5502 (by decide +kernel)

theorem valid6639 : plan6639.Valid := valid_step _ _ _ valid5503 (by decide +kernel)


































































































































































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









































theorem valid3511 : plan3511.Valid := valid_step _ _ _ valid1616 (by decide +kernel)



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

theorem valid3539 : plan3539.Valid := valid_step _ _ _ valid1616 (by decide +kernel)







theorem valid3543 : plan3543.Valid := valid_step _ _ _ valid1613 (by decide +kernel)





theorem valid3546 : plan3546.Valid := valid_step _ _ _ valid1616 (by decide +kernel)







theorem valid3550 : plan3550.Valid := valid_step _ _ _ valid1620 (by decide +kernel)




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



























































theorem valid5790 : plan5790.Valid := valid_step _ _ _ valid3444 (by decide +kernel)

theorem valid5791 : plan5791.Valid := valid_step _ _ _ valid3446 (by decide +kernel)

theorem valid5792 : plan5792.Valid := valid_step _ _ _ valid3447 (by decide +kernel)

theorem valid5793 : plan5793.Valid := valid_step _ _ _ valid3448 (by decide +kernel)



theorem valid5795 : plan5795.Valid := valid_step _ _ _ valid3454 (by decide +kernel)























theorem valid5807 : plan5807.Valid := valid_step _ _ _ valid3490 (by decide +kernel)













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



























































































































































theorem valid6414 : plan6414.Valid := valid_step _ _ _ valid5403 (by decide +kernel)




































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

















































theorem valid5977 : plan5977.Valid := valid_step _ _ _ valid3511 (by decide +kernel)

theorem valid5978 : plan5978.Valid := valid_step _ _ _ valid3518 (by decide +kernel)

theorem valid5979 : plan5979.Valid := valid_step _ _ _ valid3521 (by decide +kernel)

theorem valid5980 : plan5980.Valid := valid_step _ _ _ valid3525 (by decide +kernel)

theorem valid5981 : plan5981.Valid := valid_step _ _ _ valid3529 (by decide +kernel)

theorem valid5982 : plan5982.Valid := valid_step _ _ _ valid3531 (by decide +kernel)

theorem valid5983 : plan5983.Valid := valid_step _ _ _ valid3532 (by decide +kernel)

theorem valid5984 : plan5984.Valid := valid_step _ _ _ valid3534 (by decide +kernel)

theorem valid5985 : plan5985.Valid := valid_step _ _ _ valid3535 (by decide +kernel)

theorem valid5986 : plan5986.Valid := valid_step _ _ _ valid3536 (by decide +kernel)

theorem valid5987 : plan5987.Valid := valid_step _ _ _ valid3538 (by decide +kernel)

theorem valid5988 : plan5988.Valid := valid_step _ _ _ valid3539 (by decide +kernel)

theorem valid5989 : plan5989.Valid := valid_step _ _ _ valid3543 (by decide +kernel)

theorem valid5990 : plan5990.Valid := valid_step _ _ _ valid3546 (by decide +kernel)

theorem valid5991 : plan5991.Valid := valid_step _ _ _ valid3550 (by decide +kernel)

theorem valid5992 : plan5992.Valid := valid_step _ _ _ valid3553 (by decide +kernel)

theorem valid5993 : plan5993.Valid := valid_step _ _ _ valid3554 (by decide +kernel)

theorem valid5994 : plan5994.Valid := valid_step _ _ _ valid3555 (by decide +kernel)



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























































































































































































theorem valid7484 : plan7484.Valid := valid_step _ _ _ valid5790 (by decide +kernel)

theorem valid7485 : plan7485.Valid := valid_step _ _ _ valid5791 (by decide +kernel)

theorem valid7486 : plan7486.Valid := valid_step _ _ _ valid5792 (by decide +kernel)

theorem valid7487 : plan7487.Valid := valid_step _ _ _ valid5793 (by decide +kernel)

theorem valid7488 : plan7488.Valid := valid_step _ _ _ valid5795 (by decide +kernel)
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































theorem valid7024 : plan7024.Valid := valid_step _ _ _ valid5662 (by decide +kernel)

theorem valid7025 : plan7025.Valid := valid_step _ _ _ valid5663 (by decide +kernel)

theorem valid7026 : plan7026.Valid := valid_step _ _ _ valid5664 (by decide +kernel)

theorem valid7027 : plan7027.Valid := valid_step _ _ _ valid5665 (by decide +kernel)

theorem valid7028 : plan7028.Valid := valid_step _ _ _ valid5666 (by decide +kernel)

theorem valid7029 : plan7029.Valid := valid_step _ _ _ valid5667 (by decide +kernel)

theorem valid7030 : plan7030.Valid := valid_step _ _ _ valid5679 (by decide +kernel)

theorem valid7031 : plan7031.Valid := valid_step _ _ _ valid5690 (by decide +kernel)


















































































































































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

theorem valid7489 : plan7489.Valid := valid_step _ _ _ valid5807 (by decide +kernel)

theorem valid7490 : plan7490.Valid := valid_step _ _ _ valid5814 (by decide +kernel)

theorem valid7491 : plan7491.Valid := valid_step _ _ _ valid5815 (by decide +kernel)

theorem valid7492 : plan7492.Valid := valid_step _ _ _ valid5816 (by decide +kernel)

theorem valid7493 : plan7493.Valid := valid_step _ _ _ valid5817 (by decide +kernel)

theorem valid7494 : plan7494.Valid := valid_step _ _ _ valid5818 (by decide +kernel)

theorem valid7495 : plan7495.Valid := valid_step _ _ _ valid5819 (by decide +kernel)

theorem valid7496 : plan7496.Valid := valid_step _ _ _ valid5820 (by decide +kernel)

theorem valid7497 : plan7497.Valid := valid_step _ _ _ valid5821 (by decide +kernel)

theorem valid7498 : plan7498.Valid := valid_step _ _ _ valid5822 (by decide +kernel)

theorem valid7499 : plan7499.Valid := valid_step _ _ _ valid5823 (by decide +kernel)

theorem valid7500 : plan7500.Valid := valid_step _ _ _ valid5825 (by decide +kernel)

theorem valid7501 : plan7501.Valid := valid_step _ _ _ valid5827 (by decide +kernel)

theorem valid7502 : plan7502.Valid := valid_step _ _ _ valid5828 (by decide +kernel)

theorem valid7503 : plan7503.Valid := valid_step _ _ _ valid5860 (by decide +kernel)


































































































































































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















































theorem valid7704 : plan7704.Valid := valid_step _ _ _ valid5977 (by decide +kernel)

theorem valid7705 : plan7705.Valid := valid_step _ _ _ valid5978 (by decide +kernel)

theorem valid7706 : plan7706.Valid := valid_step _ _ _ valid5979 (by decide +kernel)

theorem valid7707 : plan7707.Valid := valid_step _ _ _ valid5980 (by decide +kernel)

theorem valid7708 : plan7708.Valid := valid_step _ _ _ valid5981 (by decide +kernel)

theorem valid7709 : plan7709.Valid := valid_step _ _ _ valid5982 (by decide +kernel)

theorem valid7710 : plan7710.Valid := valid_step _ _ _ valid5983 (by decide +kernel)

theorem valid7711 : plan7711.Valid := valid_step _ _ _ valid5984 (by decide +kernel)

theorem valid7712 : plan7712.Valid := valid_step _ _ _ valid5985 (by decide +kernel)

theorem valid7713 : plan7713.Valid := valid_step _ _ _ valid5986 (by decide +kernel)

theorem valid7714 : plan7714.Valid := valid_step _ _ _ valid5987 (by decide +kernel)

theorem valid7715 : plan7715.Valid := valid_step _ _ _ valid5988 (by decide +kernel)

theorem valid7716 : plan7716.Valid := valid_step _ _ _ valid5989 (by decide +kernel)

theorem valid7717 : plan7717.Valid := valid_step _ _ _ valid5990 (by decide +kernel)

theorem valid7718 : plan7718.Valid := valid_step _ _ _ valid5991 (by decide +kernel)

theorem valid7719 : plan7719.Valid := valid_step _ _ _ valid5992 (by decide +kernel)

theorem valid7720 : plan7720.Valid := valid_step _ _ _ valid5993 (by decide +kernel)

theorem valid7721 : plan7721.Valid := valid_step _ _ _ valid5994 (by decide +kernel)

theorem valid7722 : plan7722.Valid := valid_step _ _ _ valid5996 (by decide +kernel)

theorem valid7723 : plan7723.Valid := valid_step _ _ _ valid5999 (by decide +kernel)

theorem valid7724 : plan7724.Valid := valid_step _ _ _ valid6001 (by decide +kernel)

theorem valid7725 : plan7725.Valid := valid_step _ _ _ valid6002 (by decide +kernel)

theorem valid7726 : plan7726.Valid := valid_step _ _ _ valid6004 (by decide +kernel)

theorem valid7727 : plan7727.Valid := valid_step _ _ _ valid6006 (by decide +kernel)

theorem valid7728 : plan7728.Valid := valid_step _ _ _ valid6008 (by decide +kernel)

theorem valid7729 : plan7729.Valid := valid_step _ _ _ valid6009 (by decide +kernel)

theorem valid7730 : plan7730.Valid := valid_step _ _ _ valid6011 (by decide +kernel)

theorem valid7731 : plan7731.Valid := valid_step _ _ _ valid6012 (by decide +kernel)

theorem valid7732 : plan7732.Valid := valid_step _ _ _ valid6013 (by decide +kernel)

theorem valid7733 : plan7733.Valid := valid_step _ _ _ valid6014 (by decide +kernel)

theorem valid7734 : plan7734.Valid := valid_step _ _ _ valid6015 (by decide +kernel)

theorem valid7735 : plan7735.Valid := valid_step _ _ _ valid6016 (by decide +kernel)

theorem valid7736 : plan7736.Valid := valid_step _ _ _ valid6017 (by decide +kernel)

theorem valid7737 : plan7737.Valid := valid_step _ _ _ valid6018 (by decide +kernel)

theorem valid7738 : plan7738.Valid := valid_step _ _ _ valid6019 (by decide +kernel)

theorem valid7739 : plan7739.Valid := valid_step _ _ _ valid6020 (by decide +kernel)

theorem valid7740 : plan7740.Valid := valid_step _ _ _ valid6021 (by decide +kernel)








































































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
theorem t6_1005choices : plan7484.choices=[4,4,3,6,10,7].map (options 6 5) := by rfl


theorem t6_1005part0 : t6_1005jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1005frontier : t6_1005root.frontier 0=t6_1005jobs := by rfl
theorem t6_1005all : t6_1005jobs.all (Job.check tree)=true := by
  simp only [t6_1005jobs,List.all_append,List.all_nil,t6_1005part0,Bool.and_self]
theorem t6_1005checked : Checked tree [4,4,3,6,10,7] := by
  refine ⟨plan7484,valid7484,t6_1005choices,?_⟩
  exact check_of_frontier tree 0 t6_1005root t6_1005jobs t6_1005frontier t6_1005all
theorem t6_1006choices : plan7485.choices=[4,4,3,7,7,7].map (options 6 5) := by rfl


theorem t6_1006part0 : t6_1006jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1006frontier : t6_1006root.frontier 0=t6_1006jobs := by rfl
theorem t6_1006all : t6_1006jobs.all (Job.check tree)=true := by
  simp only [t6_1006jobs,List.all_append,List.all_nil,t6_1006part0,Bool.and_self]
theorem t6_1006checked : Checked tree [4,4,3,7,7,7] := by
  refine ⟨plan7485,valid7485,t6_1006choices,?_⟩
  exact check_of_frontier tree 0 t6_1006root t6_1006jobs t6_1006frontier t6_1006all
theorem t6_1007choices : plan7486.choices=[4,4,3,10,7,7].map (options 6 5) := by rfl


theorem t6_1007part0 : t6_1007jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1007frontier : t6_1007root.frontier 0=t6_1007jobs := by rfl
theorem t6_1007all : t6_1007jobs.all (Job.check tree)=true := by
  simp only [t6_1007jobs,List.all_append,List.all_nil,t6_1007part0,Bool.and_self]
theorem t6_1007checked : Checked tree [4,4,3,10,7,7] := by
  refine ⟨plan7486,valid7486,t6_1007choices,?_⟩
  exact check_of_frontier tree 0 t6_1007root t6_1007jobs t6_1007frontier t6_1007all
theorem t6_1008choices : plan7487.choices=[4,4,3,10,10,7].map (options 6 5) := by rfl


theorem t6_1008part0 : t6_1008jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1008frontier : t6_1008root.frontier 0=t6_1008jobs := by rfl
theorem t6_1008all : t6_1008jobs.all (Job.check tree)=true := by
  simp only [t6_1008jobs,List.all_append,List.all_nil,t6_1008part0,Bool.and_self]
theorem t6_1008checked : Checked tree [4,4,3,10,10,7] := by
  refine ⟨plan7487,valid7487,t6_1008choices,?_⟩
  exact check_of_frontier tree 0 t6_1008root t6_1008jobs t6_1008frontier t6_1008all
theorem t6_1009choices : plan7704.choices=[4,4,4,7,7,7].map (options 6 6) := by rfl


theorem t6_1009part0 : t6_1009jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1009frontier : t6_1009root.frontier 0=t6_1009jobs := by rfl
theorem t6_1009all : t6_1009jobs.all (Job.check tree)=true := by
  simp only [t6_1009jobs,List.all_append,List.all_nil,t6_1009part0,Bool.and_self]
theorem t6_1009checked : Checked tree [4,4,4,7,7,7] := by
  refine ⟨plan7704,valid7704,t6_1009choices,?_⟩
  exact check_of_frontier tree 0 t6_1009root t6_1009jobs t6_1009frontier t6_1009all
theorem t6_1010choices : plan7488.choices=[4,4,5,3,7,7].map (options 6 5) := by rfl


theorem t6_1010part0 : t6_1010jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1010frontier : t6_1010root.frontier 0=t6_1010jobs := by rfl
theorem t6_1010all : t6_1010jobs.all (Job.check tree)=true := by
  simp only [t6_1010jobs,List.all_append,List.all_nil,t6_1010part0,Bool.and_self]
theorem t6_1010checked : Checked tree [4,4,5,3,7,7] := by
  refine ⟨plan7488,valid7488,t6_1010choices,?_⟩
  exact check_of_frontier tree 0 t6_1010root t6_1010jobs t6_1010frontier t6_1010all
theorem t6_1011choices : plan7705.choices=[4,4,5,6,7,7].map (options 6 6) := by rfl


theorem t6_1011part0 : t6_1011jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1011frontier : t6_1011root.frontier 0=t6_1011jobs := by rfl
theorem t6_1011all : t6_1011jobs.all (Job.check tree)=true := by
  simp only [t6_1011jobs,List.all_append,List.all_nil,t6_1011part0,Bool.and_self]
theorem t6_1011checked : Checked tree [4,4,5,6,7,7] := by
  refine ⟨plan7705,valid7705,t6_1011choices,?_⟩
  exact check_of_frontier tree 0 t6_1011root t6_1011jobs t6_1011frontier t6_1011all
theorem t6_1012choices : plan7706.choices=[4,4,5,7,7,7].map (options 6 6) := by rfl


theorem t6_1012part0 : t6_1012jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1012frontier : t6_1012root.frontier 0=t6_1012jobs := by rfl
theorem t6_1012all : t6_1012jobs.all (Job.check tree)=true := by
  simp only [t6_1012jobs,List.all_append,List.all_nil,t6_1012part0,Bool.and_self]
theorem t6_1012checked : Checked tree [4,4,5,7,7,7] := by
  refine ⟨plan7706,valid7706,t6_1012choices,?_⟩
  exact check_of_frontier tree 0 t6_1012root t6_1012jobs t6_1012frontier t6_1012all
theorem t6_1013choices : plan7707.choices=[4,4,5,10,7,7].map (options 6 6) := by rfl


theorem t6_1013part0 : t6_1013jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1013frontier : t6_1013root.frontier 0=t6_1013jobs := by rfl
theorem t6_1013all : t6_1013jobs.all (Job.check tree)=true := by
  simp only [t6_1013jobs,List.all_append,List.all_nil,t6_1013part0,Bool.and_self]
theorem t6_1013checked : Checked tree [4,4,5,10,7,7] := by
  refine ⟨plan7707,valid7707,t6_1013choices,?_⟩
  exact check_of_frontier tree 0 t6_1013root t6_1013jobs t6_1013frontier t6_1013all
theorem t6_1014choices : plan7708.choices=[4,4,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1014part0 : t6_1014jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1014frontier : t6_1014root.frontier 0=t6_1014jobs := by rfl
theorem t6_1014all : t6_1014jobs.all (Job.check tree)=true := by
  simp only [t6_1014jobs,List.all_append,List.all_nil,t6_1014part0,Bool.and_self]
theorem t6_1014checked : Checked tree [4,4,6,6,6,7] := by
  refine ⟨plan7708,valid7708,t6_1014choices,?_⟩
  exact check_of_frontier tree 0 t6_1014root t6_1014jobs t6_1014frontier t6_1014all
theorem t6_1015choices : plan7709.choices=[4,4,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1015part0 : t6_1015jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1015frontier : t6_1015root.frontier 0=t6_1015jobs := by rfl
theorem t6_1015all : t6_1015jobs.all (Job.check tree)=true := by
  simp only [t6_1015jobs,List.all_append,List.all_nil,t6_1015part0,Bool.and_self]
theorem t6_1015checked : Checked tree [4,4,6,6,7,7] := by
  refine ⟨plan7709,valid7709,t6_1015choices,?_⟩
  exact check_of_frontier tree 0 t6_1015root t6_1015jobs t6_1015frontier t6_1015all
theorem t6_1016choices : plan7710.choices=[4,4,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1016part0 : t6_1016jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1016frontier : t6_1016root.frontier 0=t6_1016jobs := by rfl
theorem t6_1016all : t6_1016jobs.all (Job.check tree)=true := by
  simp only [t6_1016jobs,List.all_append,List.all_nil,t6_1016part0,Bool.and_self]
theorem t6_1016checked : Checked tree [4,4,6,6,10,7] := by
  refine ⟨plan7710,valid7710,t6_1016choices,?_⟩
  exact check_of_frontier tree 0 t6_1016root t6_1016jobs t6_1016frontier t6_1016all
theorem t6_1017choices : plan7711.choices=[4,4,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1017part0 : t6_1017jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1017frontier : t6_1017root.frontier 0=t6_1017jobs := by rfl
theorem t6_1017all : t6_1017jobs.all (Job.check tree)=true := by
  simp only [t6_1017jobs,List.all_append,List.all_nil,t6_1017part0,Bool.and_self]
theorem t6_1017checked : Checked tree [4,4,6,7,7,7] := by
  refine ⟨plan7711,valid7711,t6_1017choices,?_⟩
  exact check_of_frontier tree 0 t6_1017root t6_1017jobs t6_1017frontier t6_1017all
theorem t6_1018choices : plan7712.choices=[4,4,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1018part0 : t6_1018jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1018frontier : t6_1018root.frontier 0=t6_1018jobs := by rfl
theorem t6_1018all : t6_1018jobs.all (Job.check tree)=true := by
  simp only [t6_1018jobs,List.all_append,List.all_nil,t6_1018part0,Bool.and_self]
theorem t6_1018checked : Checked tree [4,4,6,10,7,7] := by
  refine ⟨plan7712,valid7712,t6_1018choices,?_⟩
  exact check_of_frontier tree 0 t6_1018root t6_1018jobs t6_1018frontier t6_1018all
theorem t6_1019choices : plan7713.choices=[4,4,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1019part0 : t6_1019jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1019frontier : t6_1019root.frontier 0=t6_1019jobs := by rfl
theorem t6_1019all : t6_1019jobs.all (Job.check tree)=true := by
  simp only [t6_1019jobs,List.all_append,List.all_nil,t6_1019part0,Bool.and_self]
theorem t6_1019checked : Checked tree [4,4,6,10,10,7] := by
  refine ⟨plan7713,valid7713,t6_1019choices,?_⟩
  exact check_of_frontier tree 0 t6_1019root t6_1019jobs t6_1019frontier t6_1019all
theorem t6_1020choices : plan7714.choices=[4,4,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1020part0 : t6_1020jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1020frontier : t6_1020root.frontier 0=t6_1020jobs := by rfl
theorem t6_1020all : t6_1020jobs.all (Job.check tree)=true := by
  simp only [t6_1020jobs,List.all_append,List.all_nil,t6_1020part0,Bool.and_self]
theorem t6_1020checked : Checked tree [4,4,7,7,7,7] := by
  refine ⟨plan7714,valid7714,t6_1020choices,?_⟩
  exact check_of_frontier tree 0 t6_1020root t6_1020jobs t6_1020frontier t6_1020all
theorem t6_1021choices : plan7715.choices=[4,4,8,7,7,7].map (options 6 6) := by rfl


theorem t6_1021part0 : t6_1021jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1021frontier : t6_1021root.frontier 0=t6_1021jobs := by rfl
theorem t6_1021all : t6_1021jobs.all (Job.check tree)=true := by
  simp only [t6_1021jobs,List.all_append,List.all_nil,t6_1021part0,Bool.and_self]
theorem t6_1021checked : Checked tree [4,4,8,7,7,7] := by
  refine ⟨plan7715,valid7715,t6_1021choices,?_⟩
  exact check_of_frontier tree 0 t6_1021root t6_1021jobs t6_1021frontier t6_1021all
theorem t6_1022choices : plan7489.choices=[4,4,9,3,7,7].map (options 6 5) := by rfl


theorem t6_1022part0 : t6_1022jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1022frontier : t6_1022root.frontier 0=t6_1022jobs := by rfl
theorem t6_1022all : t6_1022jobs.all (Job.check tree)=true := by
  simp only [t6_1022jobs,List.all_append,List.all_nil,t6_1022part0,Bool.and_self]
theorem t6_1022checked : Checked tree [4,4,9,3,7,7] := by
  refine ⟨plan7489,valid7489,t6_1022choices,?_⟩
  exact check_of_frontier tree 0 t6_1022root t6_1022jobs t6_1022frontier t6_1022all
theorem t6_1023choices : plan7716.choices=[4,4,9,6,7,7].map (options 6 6) := by rfl


theorem t6_1023part0 : t6_1023jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1023frontier : t6_1023root.frontier 0=t6_1023jobs := by rfl
theorem t6_1023all : t6_1023jobs.all (Job.check tree)=true := by
  simp only [t6_1023jobs,List.all_append,List.all_nil,t6_1023part0,Bool.and_self]
theorem t6_1023checked : Checked tree [4,4,9,6,7,7] := by
  refine ⟨plan7716,valid7716,t6_1023choices,?_⟩
  exact check_of_frontier tree 0 t6_1023root t6_1023jobs t6_1023frontier t6_1023all
theorem t6_1024choices : plan7717.choices=[4,4,9,7,7,7].map (options 6 6) := by rfl


theorem t6_1024part0 : t6_1024jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1024frontier : t6_1024root.frontier 0=t6_1024jobs := by rfl
theorem t6_1024all : t6_1024jobs.all (Job.check tree)=true := by
  simp only [t6_1024jobs,List.all_append,List.all_nil,t6_1024part0,Bool.and_self]
theorem t6_1024checked : Checked tree [4,4,9,7,7,7] := by
  refine ⟨plan7717,valid7717,t6_1024choices,?_⟩
  exact check_of_frontier tree 0 t6_1024root t6_1024jobs t6_1024frontier t6_1024all
theorem t6_1025choices : plan7718.choices=[4,4,9,10,7,7].map (options 6 6) := by rfl


theorem t6_1025part0 : t6_1025jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1025frontier : t6_1025root.frontier 0=t6_1025jobs := by rfl
theorem t6_1025all : t6_1025jobs.all (Job.check tree)=true := by
  simp only [t6_1025jobs,List.all_append,List.all_nil,t6_1025part0,Bool.and_self]
theorem t6_1025checked : Checked tree [4,4,9,10,7,7] := by
  refine ⟨plan7718,valid7718,t6_1025choices,?_⟩
  exact check_of_frontier tree 0 t6_1025root t6_1025jobs t6_1025frontier t6_1025all
theorem t6_1026choices : plan7719.choices=[4,4,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1026part0 : t6_1026jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1026frontier : t6_1026root.frontier 0=t6_1026jobs := by rfl
theorem t6_1026all : t6_1026jobs.all (Job.check tree)=true := by
  simp only [t6_1026jobs,List.all_append,List.all_nil,t6_1026part0,Bool.and_self]
theorem t6_1026checked : Checked tree [4,4,10,7,7,7] := by
  refine ⟨plan7719,valid7719,t6_1026choices,?_⟩
  exact check_of_frontier tree 0 t6_1026root t6_1026jobs t6_1026frontier t6_1026all
theorem t6_1027choices : plan7720.choices=[4,4,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1027part0 : t6_1027jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1027frontier : t6_1027root.frontier 0=t6_1027jobs := by rfl
theorem t6_1027all : t6_1027jobs.all (Job.check tree)=true := by
  simp only [t6_1027jobs,List.all_append,List.all_nil,t6_1027part0,Bool.and_self]
theorem t6_1027checked : Checked tree [4,4,10,10,7,7] := by
  refine ⟨plan7720,valid7720,t6_1027choices,?_⟩
  exact check_of_frontier tree 0 t6_1027root t6_1027jobs t6_1027frontier t6_1027all
theorem t6_1028choices : plan7721.choices=[4,4,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1028part0 : t6_1028jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1028frontier : t6_1028root.frontier 0=t6_1028jobs := by rfl
theorem t6_1028all : t6_1028jobs.all (Job.check tree)=true := by
  simp only [t6_1028jobs,List.all_append,List.all_nil,t6_1028part0,Bool.and_self]
theorem t6_1028checked : Checked tree [4,4,10,10,10,7] := by
  refine ⟨plan7721,valid7721,t6_1028choices,?_⟩
  exact check_of_frontier tree 0 t6_1028root t6_1028jobs t6_1028frontier t6_1028all
theorem t6_1029choices : plan6414.choices=[4,5,3,3,3,3].map (options 6 2) := by rfl


theorem t6_1029part0 : t6_1029jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1029frontier : t6_1029root.frontier 0=t6_1029jobs := by rfl
theorem t6_1029all : t6_1029jobs.all (Job.check tree)=true := by
  simp only [t6_1029jobs,List.all_append,List.all_nil,t6_1029part0,Bool.and_self]
theorem t6_1029checked : Checked tree [4,5,3,3,3,3] := by
  refine ⟨plan6414,valid6414,t6_1029choices,?_⟩
  exact check_of_frontier tree 0 t6_1029root t6_1029jobs t6_1029frontier t6_1029all
theorem t6_1030choices : plan6637.choices=[4,5,3,3,3,6].map (options 6 3) := by rfl


theorem t6_1030part0 : t6_1030jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1030frontier : t6_1030root.frontier 0=t6_1030jobs := by rfl
theorem t6_1030all : t6_1030jobs.all (Job.check tree)=true := by
  simp only [t6_1030jobs,List.all_append,List.all_nil,t6_1030part0,Bool.and_self]
theorem t6_1030checked : Checked tree [4,5,3,3,3,6] := by
  refine ⟨plan6637,valid6637,t6_1030choices,?_⟩
  exact check_of_frontier tree 0 t6_1030root t6_1030jobs t6_1030frontier t6_1030all
theorem t6_1031choices : plan6638.choices=[4,5,3,3,3,7].map (options 6 3) := by rfl


theorem t6_1031part0 : t6_1031jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1031frontier : t6_1031root.frontier 0=t6_1031jobs := by rfl
theorem t6_1031all : t6_1031jobs.all (Job.check tree)=true := by
  simp only [t6_1031jobs,List.all_append,List.all_nil,t6_1031part0,Bool.and_self]
theorem t6_1031checked : Checked tree [4,5,3,3,3,7] := by
  refine ⟨plan6638,valid6638,t6_1031choices,?_⟩
  exact check_of_frontier tree 0 t6_1031root t6_1031jobs t6_1031frontier t6_1031all
theorem t6_1032choices : plan6639.choices=[4,5,3,3,3,10].map (options 6 3) := by rfl


theorem t6_1032part0 : t6_1032jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1032frontier : t6_1032root.frontier 0=t6_1032jobs := by rfl
theorem t6_1032all : t6_1032jobs.all (Job.check tree)=true := by
  simp only [t6_1032jobs,List.all_append,List.all_nil,t6_1032part0,Bool.and_self]
theorem t6_1032checked : Checked tree [4,5,3,3,3,10] := by
  refine ⟨plan6639,valid6639,t6_1032choices,?_⟩
  exact check_of_frontier tree 0 t6_1032root t6_1032jobs t6_1032frontier t6_1032all
theorem t6_1033choices : plan7024.choices=[4,5,3,3,6,6].map (options 6 4) := by rfl


theorem t6_1033part0 : t6_1033jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1033frontier : t6_1033root.frontier 0=t6_1033jobs := by rfl
theorem t6_1033all : t6_1033jobs.all (Job.check tree)=true := by
  simp only [t6_1033jobs,List.all_append,List.all_nil,t6_1033part0,Bool.and_self]
theorem t6_1033checked : Checked tree [4,5,3,3,6,6] := by
  refine ⟨plan7024,valid7024,t6_1033choices,?_⟩
  exact check_of_frontier tree 0 t6_1033root t6_1033jobs t6_1033frontier t6_1033all
theorem t6_1034choices : plan7025.choices=[4,5,3,3,6,7].map (options 6 4) := by rfl


theorem t6_1034part0 : t6_1034jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1034part1 : t6_1034jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1034frontier : t6_1034root.frontier 1=t6_1034jobs := by rfl
theorem t6_1034all : t6_1034jobs.all (Job.check tree)=true := by
  simp only [t6_1034jobs,List.all_append,List.all_nil,t6_1034part0,t6_1034part1,Bool.and_self]
theorem t6_1034checked : Checked tree [4,5,3,3,6,7] := by
  refine ⟨plan7025,valid7025,t6_1034choices,?_⟩
  exact check_of_frontier tree 1 t6_1034root t6_1034jobs t6_1034frontier t6_1034all
theorem t6_1035choices : plan7026.choices=[4,5,3,3,6,10].map (options 6 4) := by rfl


theorem t6_1035part0 : t6_1035jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1035frontier : t6_1035root.frontier 0=t6_1035jobs := by rfl
theorem t6_1035all : t6_1035jobs.all (Job.check tree)=true := by
  simp only [t6_1035jobs,List.all_append,List.all_nil,t6_1035part0,Bool.and_self]
theorem t6_1035checked : Checked tree [4,5,3,3,6,10] := by
  refine ⟨plan7026,valid7026,t6_1035choices,?_⟩
  exact check_of_frontier tree 0 t6_1035root t6_1035jobs t6_1035frontier t6_1035all
theorem t6_1036choices : plan7027.choices=[4,5,3,3,7,7].map (options 6 4) := by rfl


theorem t6_1036part0 : t6_1036jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1036part1 : t6_1036jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1036frontier : t6_1036root.frontier 1=t6_1036jobs := by rfl
theorem t6_1036all : t6_1036jobs.all (Job.check tree)=true := by
  simp only [t6_1036jobs,List.all_append,List.all_nil,t6_1036part0,t6_1036part1,Bool.and_self]
theorem t6_1036checked : Checked tree [4,5,3,3,7,7] := by
  refine ⟨plan7027,valid7027,t6_1036choices,?_⟩
  exact check_of_frontier tree 1 t6_1036root t6_1036jobs t6_1036frontier t6_1036all
theorem t6_1037choices : plan7028.choices=[4,5,3,3,10,7].map (options 6 4) := by rfl


theorem t6_1037part0 : t6_1037jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1037part1 : t6_1037jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1037frontier : t6_1037root.frontier 1=t6_1037jobs := by rfl
theorem t6_1037all : t6_1037jobs.all (Job.check tree)=true := by
  simp only [t6_1037jobs,List.all_append,List.all_nil,t6_1037part0,t6_1037part1,Bool.and_self]
theorem t6_1037checked : Checked tree [4,5,3,3,10,7] := by
  refine ⟨plan7028,valid7028,t6_1037choices,?_⟩
  exact check_of_frontier tree 1 t6_1037root t6_1037jobs t6_1037frontier t6_1037all
theorem t6_1038choices : plan7029.choices=[4,5,3,3,10,10].map (options 6 4) := by rfl


theorem t6_1038part0 : t6_1038jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1038frontier : t6_1038root.frontier 0=t6_1038jobs := by rfl
theorem t6_1038all : t6_1038jobs.all (Job.check tree)=true := by
  simp only [t6_1038jobs,List.all_append,List.all_nil,t6_1038part0,Bool.and_self]
theorem t6_1038checked : Checked tree [4,5,3,3,10,10] := by
  refine ⟨plan7029,valid7029,t6_1038choices,?_⟩
  exact check_of_frontier tree 0 t6_1038root t6_1038jobs t6_1038frontier t6_1038all
theorem t6_1039choices : plan7490.choices=[4,5,3,6,6,6].map (options 6 5) := by rfl


theorem t6_1039part0 : t6_1039jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1039frontier : t6_1039root.frontier 0=t6_1039jobs := by rfl
theorem t6_1039all : t6_1039jobs.all (Job.check tree)=true := by
  simp only [t6_1039jobs,List.all_append,List.all_nil,t6_1039part0,Bool.and_self]
theorem t6_1039checked : Checked tree [4,5,3,6,6,6] := by
  refine ⟨plan7490,valid7490,t6_1039choices,?_⟩
  exact check_of_frontier tree 0 t6_1039root t6_1039jobs t6_1039frontier t6_1039all
theorem t6_1040choices : plan7491.choices=[4,5,3,6,6,7].map (options 6 5) := by rfl


theorem t6_1040part0 : t6_1040jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1040frontier : t6_1040root.frontier 0=t6_1040jobs := by rfl
theorem t6_1040all : t6_1040jobs.all (Job.check tree)=true := by
  simp only [t6_1040jobs,List.all_append,List.all_nil,t6_1040part0,Bool.and_self]
theorem t6_1040checked : Checked tree [4,5,3,6,6,7] := by
  refine ⟨plan7491,valid7491,t6_1040choices,?_⟩
  exact check_of_frontier tree 0 t6_1040root t6_1040jobs t6_1040frontier t6_1040all
theorem t6_1041choices : plan7492.choices=[4,5,3,6,6,10].map (options 6 5) := by rfl


theorem t6_1041part0 : t6_1041jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1041frontier : t6_1041root.frontier 0=t6_1041jobs := by rfl
theorem t6_1041all : t6_1041jobs.all (Job.check tree)=true := by
  simp only [t6_1041jobs,List.all_append,List.all_nil,t6_1041part0,Bool.and_self]
theorem t6_1041checked : Checked tree [4,5,3,6,6,10] := by
  refine ⟨plan7492,valid7492,t6_1041choices,?_⟩
  exact check_of_frontier tree 0 t6_1041root t6_1041jobs t6_1041frontier t6_1041all
theorem t6_1042choices : plan7493.choices=[4,5,3,6,7,7].map (options 6 5) := by rfl


theorem t6_1042part0 : t6_1042jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1042part1 : t6_1042jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1042frontier : t6_1042root.frontier 1=t6_1042jobs := by rfl
theorem t6_1042all : t6_1042jobs.all (Job.check tree)=true := by
  simp only [t6_1042jobs,List.all_append,List.all_nil,t6_1042part0,t6_1042part1,Bool.and_self]
theorem t6_1042checked : Checked tree [4,5,3,6,7,7] := by
  refine ⟨plan7493,valid7493,t6_1042choices,?_⟩
  exact check_of_frontier tree 1 t6_1042root t6_1042jobs t6_1042frontier t6_1042all
theorem t6_1043choices : plan7494.choices=[4,5,3,6,10,7].map (options 6 5) := by rfl


theorem t6_1043part0 : t6_1043jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1043frontier : t6_1043root.frontier 0=t6_1043jobs := by rfl
theorem t6_1043all : t6_1043jobs.all (Job.check tree)=true := by
  simp only [t6_1043jobs,List.all_append,List.all_nil,t6_1043part0,Bool.and_self]
theorem t6_1043checked : Checked tree [4,5,3,6,10,7] := by
  refine ⟨plan7494,valid7494,t6_1043choices,?_⟩
  exact check_of_frontier tree 0 t6_1043root t6_1043jobs t6_1043frontier t6_1043all
theorem t6_1044choices : plan7495.choices=[4,5,3,6,10,10].map (options 6 5) := by rfl


theorem t6_1044part0 : t6_1044jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1044frontier : t6_1044root.frontier 0=t6_1044jobs := by rfl
theorem t6_1044all : t6_1044jobs.all (Job.check tree)=true := by
  simp only [t6_1044jobs,List.all_append,List.all_nil,t6_1044part0,Bool.and_self]
theorem t6_1044checked : Checked tree [4,5,3,6,10,10] := by
  refine ⟨plan7495,valid7495,t6_1044choices,?_⟩
  exact check_of_frontier tree 0 t6_1044root t6_1044jobs t6_1044frontier t6_1044all
theorem t6_1045choices : plan7496.choices=[4,5,3,7,7,7].map (options 6 5) := by rfl


theorem t6_1045part0 : t6_1045jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1045part1 : t6_1045jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1045frontier : t6_1045root.frontier 1=t6_1045jobs := by rfl
theorem t6_1045all : t6_1045jobs.all (Job.check tree)=true := by
  simp only [t6_1045jobs,List.all_append,List.all_nil,t6_1045part0,t6_1045part1,Bool.and_self]
theorem t6_1045checked : Checked tree [4,5,3,7,7,7] := by
  refine ⟨plan7496,valid7496,t6_1045choices,?_⟩
  exact check_of_frontier tree 1 t6_1045root t6_1045jobs t6_1045frontier t6_1045all
theorem t6_1046choices : plan7497.choices=[4,5,3,10,7,7].map (options 6 5) := by rfl


theorem t6_1046part0 : t6_1046jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1046part1 : t6_1046jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1046frontier : t6_1046root.frontier 1=t6_1046jobs := by rfl
theorem t6_1046all : t6_1046jobs.all (Job.check tree)=true := by
  simp only [t6_1046jobs,List.all_append,List.all_nil,t6_1046part0,t6_1046part1,Bool.and_self]
theorem t6_1046checked : Checked tree [4,5,3,10,7,7] := by
  refine ⟨plan7497,valid7497,t6_1046choices,?_⟩
  exact check_of_frontier tree 1 t6_1046root t6_1046jobs t6_1046frontier t6_1046all
theorem t6_1047choices : plan7498.choices=[4,5,3,10,10,7].map (options 6 5) := by rfl


theorem t6_1047part0 : t6_1047jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1047frontier : t6_1047root.frontier 0=t6_1047jobs := by rfl
theorem t6_1047all : t6_1047jobs.all (Job.check tree)=true := by
  simp only [t6_1047jobs,List.all_append,List.all_nil,t6_1047part0,Bool.and_self]
theorem t6_1047checked : Checked tree [4,5,3,10,10,7] := by
  refine ⟨plan7498,valid7498,t6_1047choices,?_⟩
  exact check_of_frontier tree 0 t6_1047root t6_1047jobs t6_1047frontier t6_1047all
theorem t6_1048choices : plan7499.choices=[4,5,3,10,10,10].map (options 6 5) := by rfl


theorem t6_1048part0 : t6_1048jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1048frontier : t6_1048root.frontier 0=t6_1048jobs := by rfl
theorem t6_1048all : t6_1048jobs.all (Job.check tree)=true := by
  simp only [t6_1048jobs,List.all_append,List.all_nil,t6_1048part0,Bool.and_self]
theorem t6_1048checked : Checked tree [4,5,3,10,10,10] := by
  refine ⟨plan7499,valid7499,t6_1048choices,?_⟩
  exact check_of_frontier tree 0 t6_1048root t6_1048jobs t6_1048frontier t6_1048all
theorem t6_1049choices : plan7030.choices=[4,5,5,3,3,7].map (options 6 4) := by rfl


theorem t6_1049part0 : t6_1049jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1049frontier : t6_1049root.frontier 0=t6_1049jobs := by rfl
theorem t6_1049all : t6_1049jobs.all (Job.check tree)=true := by
  simp only [t6_1049jobs,List.all_append,List.all_nil,t6_1049part0,Bool.and_self]
theorem t6_1049checked : Checked tree [4,5,5,3,3,7] := by
  refine ⟨plan7030,valid7030,t6_1049choices,?_⟩
  exact check_of_frontier tree 0 t6_1049root t6_1049jobs t6_1049frontier t6_1049all
theorem t6_1050choices : plan7500.choices=[4,5,5,3,6,7].map (options 6 5) := by rfl


theorem t6_1050part0 : t6_1050jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1050frontier : t6_1050root.frontier 0=t6_1050jobs := by rfl
theorem t6_1050all : t6_1050jobs.all (Job.check tree)=true := by
  simp only [t6_1050jobs,List.all_append,List.all_nil,t6_1050part0,Bool.and_self]
theorem t6_1050checked : Checked tree [4,5,5,3,6,7] := by
  refine ⟨plan7500,valid7500,t6_1050choices,?_⟩
  exact check_of_frontier tree 0 t6_1050root t6_1050jobs t6_1050frontier t6_1050all
theorem t6_1051choices : plan7501.choices=[4,5,5,3,7,7].map (options 6 5) := by rfl


theorem t6_1051part0 : t6_1051jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1051frontier : t6_1051root.frontier 0=t6_1051jobs := by rfl
theorem t6_1051all : t6_1051jobs.all (Job.check tree)=true := by
  simp only [t6_1051jobs,List.all_append,List.all_nil,t6_1051part0,Bool.and_self]
theorem t6_1051checked : Checked tree [4,5,5,3,7,7] := by
  refine ⟨plan7501,valid7501,t6_1051choices,?_⟩
  exact check_of_frontier tree 0 t6_1051root t6_1051jobs t6_1051frontier t6_1051all
theorem t6_1052choices : plan7502.choices=[4,5,5,3,10,7].map (options 6 5) := by rfl


theorem t6_1052part0 : t6_1052jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1052frontier : t6_1052root.frontier 0=t6_1052jobs := by rfl
theorem t6_1052all : t6_1052jobs.all (Job.check tree)=true := by
  simp only [t6_1052jobs,List.all_append,List.all_nil,t6_1052part0,Bool.and_self]
theorem t6_1052checked : Checked tree [4,5,5,3,10,7] := by
  refine ⟨plan7502,valid7502,t6_1052choices,?_⟩
  exact check_of_frontier tree 0 t6_1052root t6_1052jobs t6_1052frontier t6_1052all
theorem t6_1053choices : plan7722.choices=[4,5,5,5,7,7].map (options 6 6) := by rfl


theorem t6_1053part0 : t6_1053jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1053frontier : t6_1053root.frontier 0=t6_1053jobs := by rfl
theorem t6_1053all : t6_1053jobs.all (Job.check tree)=true := by
  simp only [t6_1053jobs,List.all_append,List.all_nil,t6_1053part0,Bool.and_self]
theorem t6_1053checked : Checked tree [4,5,5,5,7,7] := by
  refine ⟨plan7722,valid7722,t6_1053choices,?_⟩
  exact check_of_frontier tree 0 t6_1053root t6_1053jobs t6_1053frontier t6_1053all
theorem t6_1054choices : plan7723.choices=[4,5,5,6,6,7].map (options 6 6) := by rfl


theorem t6_1054part0 : t6_1054jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1054frontier : t6_1054root.frontier 0=t6_1054jobs := by rfl
theorem t6_1054all : t6_1054jobs.all (Job.check tree)=true := by
  simp only [t6_1054jobs,List.all_append,List.all_nil,t6_1054part0,Bool.and_self]
theorem t6_1054checked : Checked tree [4,5,5,6,6,7] := by
  refine ⟨plan7723,valid7723,t6_1054choices,?_⟩
  exact check_of_frontier tree 0 t6_1054root t6_1054jobs t6_1054frontier t6_1054all
theorem t6_1055choices : plan7724.choices=[4,5,5,6,7,7].map (options 6 6) := by rfl


theorem t6_1055part0 : t6_1055jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1055frontier : t6_1055root.frontier 0=t6_1055jobs := by rfl
theorem t6_1055all : t6_1055jobs.all (Job.check tree)=true := by
  simp only [t6_1055jobs,List.all_append,List.all_nil,t6_1055part0,Bool.and_self]
theorem t6_1055checked : Checked tree [4,5,5,6,7,7] := by
  refine ⟨plan7724,valid7724,t6_1055choices,?_⟩
  exact check_of_frontier tree 0 t6_1055root t6_1055jobs t6_1055frontier t6_1055all
theorem t6_1056choices : plan7725.choices=[4,5,5,6,10,7].map (options 6 6) := by rfl


theorem t6_1056part0 : t6_1056jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1056frontier : t6_1056root.frontier 0=t6_1056jobs := by rfl
theorem t6_1056all : t6_1056jobs.all (Job.check tree)=true := by
  simp only [t6_1056jobs,List.all_append,List.all_nil,t6_1056part0,Bool.and_self]
theorem t6_1056checked : Checked tree [4,5,5,6,10,7] := by
  refine ⟨plan7725,valid7725,t6_1056choices,?_⟩
  exact check_of_frontier tree 0 t6_1056root t6_1056jobs t6_1056frontier t6_1056all
theorem t6_1057choices : plan7726.choices=[4,5,5,7,7,7].map (options 6 6) := by rfl


theorem t6_1057part0 : t6_1057jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1057frontier : t6_1057root.frontier 0=t6_1057jobs := by rfl
theorem t6_1057all : t6_1057jobs.all (Job.check tree)=true := by
  simp only [t6_1057jobs,List.all_append,List.all_nil,t6_1057part0,Bool.and_self]
theorem t6_1057checked : Checked tree [4,5,5,7,7,7] := by
  refine ⟨plan7726,valid7726,t6_1057choices,?_⟩
  exact check_of_frontier tree 0 t6_1057root t6_1057jobs t6_1057frontier t6_1057all
theorem t6_1058choices : plan7727.choices=[4,5,5,9,7,7].map (options 6 6) := by rfl


theorem t6_1058part0 : t6_1058jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1058frontier : t6_1058root.frontier 0=t6_1058jobs := by rfl
theorem t6_1058all : t6_1058jobs.all (Job.check tree)=true := by
  simp only [t6_1058jobs,List.all_append,List.all_nil,t6_1058part0,Bool.and_self]
theorem t6_1058checked : Checked tree [4,5,5,9,7,7] := by
  refine ⟨plan7727,valid7727,t6_1058choices,?_⟩
  exact check_of_frontier tree 0 t6_1058root t6_1058jobs t6_1058frontier t6_1058all
theorem t6_1059choices : plan7728.choices=[4,5,5,10,7,7].map (options 6 6) := by rfl


theorem t6_1059part0 : t6_1059jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1059frontier : t6_1059root.frontier 0=t6_1059jobs := by rfl
theorem t6_1059all : t6_1059jobs.all (Job.check tree)=true := by
  simp only [t6_1059jobs,List.all_append,List.all_nil,t6_1059part0,Bool.and_self]
theorem t6_1059checked : Checked tree [4,5,5,10,7,7] := by
  refine ⟨plan7728,valid7728,t6_1059choices,?_⟩
  exact check_of_frontier tree 0 t6_1059root t6_1059jobs t6_1059frontier t6_1059all
theorem t6_1060choices : plan7729.choices=[4,5,5,10,10,7].map (options 6 6) := by rfl


theorem t6_1060part0 : t6_1060jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1060frontier : t6_1060root.frontier 0=t6_1060jobs := by rfl
theorem t6_1060all : t6_1060jobs.all (Job.check tree)=true := by
  simp only [t6_1060jobs,List.all_append,List.all_nil,t6_1060part0,Bool.and_self]
theorem t6_1060checked : Checked tree [4,5,5,10,10,7] := by
  refine ⟨plan7729,valid7729,t6_1060choices,?_⟩
  exact check_of_frontier tree 0 t6_1060root t6_1060jobs t6_1060frontier t6_1060all
theorem t6_1061choices : plan7730.choices=[4,5,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1061part0 : t6_1061jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1061frontier : t6_1061root.frontier 0=t6_1061jobs := by rfl
theorem t6_1061all : t6_1061jobs.all (Job.check tree)=true := by
  simp only [t6_1061jobs,List.all_append,List.all_nil,t6_1061part0,Bool.and_self]
theorem t6_1061checked : Checked tree [4,5,6,6,6,6] := by
  refine ⟨plan7730,valid7730,t6_1061choices,?_⟩
  exact check_of_frontier tree 0 t6_1061root t6_1061jobs t6_1061frontier t6_1061all
theorem t6_1062choices : plan7731.choices=[4,5,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1062part0 : t6_1062jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1062frontier : t6_1062root.frontier 0=t6_1062jobs := by rfl
theorem t6_1062all : t6_1062jobs.all (Job.check tree)=true := by
  simp only [t6_1062jobs,List.all_append,List.all_nil,t6_1062part0,Bool.and_self]
theorem t6_1062checked : Checked tree [4,5,6,6,6,7] := by
  refine ⟨plan7731,valid7731,t6_1062choices,?_⟩
  exact check_of_frontier tree 0 t6_1062root t6_1062jobs t6_1062frontier t6_1062all
theorem t6_1063choices : plan7732.choices=[4,5,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1063part0 : t6_1063jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1063frontier : t6_1063root.frontier 0=t6_1063jobs := by rfl
theorem t6_1063all : t6_1063jobs.all (Job.check tree)=true := by
  simp only [t6_1063jobs,List.all_append,List.all_nil,t6_1063part0,Bool.and_self]
theorem t6_1063checked : Checked tree [4,5,6,6,6,10] := by
  refine ⟨plan7732,valid7732,t6_1063choices,?_⟩
  exact check_of_frontier tree 0 t6_1063root t6_1063jobs t6_1063frontier t6_1063all
theorem t6_1064choices : plan7733.choices=[4,5,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1064part0 : t6_1064jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1064frontier : t6_1064root.frontier 0=t6_1064jobs := by rfl
theorem t6_1064all : t6_1064jobs.all (Job.check tree)=true := by
  simp only [t6_1064jobs,List.all_append,List.all_nil,t6_1064part0,Bool.and_self]
theorem t6_1064checked : Checked tree [4,5,6,6,7,7] := by
  refine ⟨plan7733,valid7733,t6_1064choices,?_⟩
  exact check_of_frontier tree 0 t6_1064root t6_1064jobs t6_1064frontier t6_1064all
theorem t6_1065choices : plan7734.choices=[4,5,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1065part0 : t6_1065jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1065frontier : t6_1065root.frontier 0=t6_1065jobs := by rfl
theorem t6_1065all : t6_1065jobs.all (Job.check tree)=true := by
  simp only [t6_1065jobs,List.all_append,List.all_nil,t6_1065part0,Bool.and_self]
theorem t6_1065checked : Checked tree [4,5,6,6,10,7] := by
  refine ⟨plan7734,valid7734,t6_1065choices,?_⟩
  exact check_of_frontier tree 0 t6_1065root t6_1065jobs t6_1065frontier t6_1065all
theorem t6_1066choices : plan7735.choices=[4,5,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1066part0 : t6_1066jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1066frontier : t6_1066root.frontier 0=t6_1066jobs := by rfl
theorem t6_1066all : t6_1066jobs.all (Job.check tree)=true := by
  simp only [t6_1066jobs,List.all_append,List.all_nil,t6_1066part0,Bool.and_self]
theorem t6_1066checked : Checked tree [4,5,6,6,10,10] := by
  refine ⟨plan7735,valid7735,t6_1066choices,?_⟩
  exact check_of_frontier tree 0 t6_1066root t6_1066jobs t6_1066frontier t6_1066all
theorem t6_1067choices : plan7736.choices=[4,5,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1067part0 : t6_1067jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1067frontier : t6_1067root.frontier 0=t6_1067jobs := by rfl
theorem t6_1067all : t6_1067jobs.all (Job.check tree)=true := by
  simp only [t6_1067jobs,List.all_append,List.all_nil,t6_1067part0,Bool.and_self]
theorem t6_1067checked : Checked tree [4,5,6,7,7,7] := by
  refine ⟨plan7736,valid7736,t6_1067choices,?_⟩
  exact check_of_frontier tree 0 t6_1067root t6_1067jobs t6_1067frontier t6_1067all
theorem t6_1068choices : plan7737.choices=[4,5,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1068part0 : t6_1068jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1068frontier : t6_1068root.frontier 0=t6_1068jobs := by rfl
theorem t6_1068all : t6_1068jobs.all (Job.check tree)=true := by
  simp only [t6_1068jobs,List.all_append,List.all_nil,t6_1068part0,Bool.and_self]
theorem t6_1068checked : Checked tree [4,5,6,10,7,7] := by
  refine ⟨plan7737,valid7737,t6_1068choices,?_⟩
  exact check_of_frontier tree 0 t6_1068root t6_1068jobs t6_1068frontier t6_1068all
theorem t6_1069choices : plan7738.choices=[4,5,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1069part0 : t6_1069jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1069frontier : t6_1069root.frontier 0=t6_1069jobs := by rfl
theorem t6_1069all : t6_1069jobs.all (Job.check tree)=true := by
  simp only [t6_1069jobs,List.all_append,List.all_nil,t6_1069part0,Bool.and_self]
theorem t6_1069checked : Checked tree [4,5,6,10,10,7] := by
  refine ⟨plan7738,valid7738,t6_1069choices,?_⟩
  exact check_of_frontier tree 0 t6_1069root t6_1069jobs t6_1069frontier t6_1069all
theorem t6_1070choices : plan7739.choices=[4,5,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1070part0 : t6_1070jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1070frontier : t6_1070root.frontier 0=t6_1070jobs := by rfl
theorem t6_1070all : t6_1070jobs.all (Job.check tree)=true := by
  simp only [t6_1070jobs,List.all_append,List.all_nil,t6_1070part0,Bool.and_self]
theorem t6_1070checked : Checked tree [4,5,6,10,10,10] := by
  refine ⟨plan7739,valid7739,t6_1070choices,?_⟩
  exact check_of_frontier tree 0 t6_1070root t6_1070jobs t6_1070frontier t6_1070all
theorem t6_1071choices : plan7740.choices=[4,5,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1071part0 : t6_1071jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1071frontier : t6_1071root.frontier 0=t6_1071jobs := by rfl
theorem t6_1071all : t6_1071jobs.all (Job.check tree)=true := by
  simp only [t6_1071jobs,List.all_append,List.all_nil,t6_1071part0,Bool.and_self]
theorem t6_1071checked : Checked tree [4,5,7,7,7,7] := by
  refine ⟨plan7740,valid7740,t6_1071choices,?_⟩
  exact check_of_frontier tree 0 t6_1071root t6_1071jobs t6_1071frontier t6_1071all
theorem t6_1072choices : plan7031.choices=[4,5,9,3,3,7].map (options 6 4) := by rfl


theorem t6_1072part0 : t6_1072jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1072frontier : t6_1072root.frontier 0=t6_1072jobs := by rfl
theorem t6_1072all : t6_1072jobs.all (Job.check tree)=true := by
  simp only [t6_1072jobs,List.all_append,List.all_nil,t6_1072part0,Bool.and_self]
theorem t6_1072checked : Checked tree [4,5,9,3,3,7] := by
  refine ⟨plan7031,valid7031,t6_1072choices,?_⟩
  exact check_of_frontier tree 0 t6_1072root t6_1072jobs t6_1072frontier t6_1072all
theorem t6_1073choices : plan7503.choices=[4,5,9,3,6,7].map (options 6 5) := by rfl


theorem t6_1073part0 : t6_1073jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1073frontier : t6_1073root.frontier 0=t6_1073jobs := by rfl
theorem t6_1073all : t6_1073jobs.all (Job.check tree)=true := by
  simp only [t6_1073jobs,List.all_append,List.all_nil,t6_1073part0,Bool.and_self]
theorem t6_1073checked : Checked tree [4,5,9,3,6,7] := by
  refine ⟨plan7503,valid7503,t6_1073choices,?_⟩
  exact check_of_frontier tree 0 t6_1073root t6_1073jobs t6_1073frontier t6_1073all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks121 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1017checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1005checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1018checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1019checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1020checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1021checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1022checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1023checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1024checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1025checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1026checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1027checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1006checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1028checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1029checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1030checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1031checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1032checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1033checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1034checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1035checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1036checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1007checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1037checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1038checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1039checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1040checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1041checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1042checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1043checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1044checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1045checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1008checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1046checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1047checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1048checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1049checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1050checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1051checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1052checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1053checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1054checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1055checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1009checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1056checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1057checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1058checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1059checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1060checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1061checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1062checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1063checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1064checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1065checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1010checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1066checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1067checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1068checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1069checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1070checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1071checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1072checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1073checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1011checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1012checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1013checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1014checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1015checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1016checked⟩
