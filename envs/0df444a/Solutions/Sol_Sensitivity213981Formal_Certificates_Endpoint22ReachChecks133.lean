-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks133
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:49:22.638564+00:00
-- url     : https://prove2.me/submissions/fc26c119-c3a8-41f7-9b93-32c3a85a84f3

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks133
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks133
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans081
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



























































theorem valid126 : plan126.Valid := valid_step _ _ _ valid0 (by decide +kernel)







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





















































































































































theorem valid555 : plan555.Valid := valid_step _ _ _ valid126 (by decide +kernel)



















theorem valid565 : plan565.Valid := valid_step _ _ _ valid130 (by decide +kernel)

theorem valid566 : plan566.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid567 : plan567.Valid := valid_step _ _ _ valid132 (by decide +kernel)













theorem valid574 : plan574.Valid := valid_step _ _ _ valid134 (by decide +kernel)

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















































































































































































theorem valid1528 : plan1528.Valid := valid_step _ _ _ valid555 (by decide +kernel)
















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







































theorem valid1556 : plan1556.Valid := valid_step _ _ _ valid565 (by decide +kernel)

theorem valid1557 : plan1557.Valid := valid_step _ _ _ valid566 (by decide +kernel)

theorem valid1558 : plan1558.Valid := valid_step _ _ _ valid567 (by decide +kernel)

















































theorem valid1583 : plan1583.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1584 : plan1584.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1585 : plan1585.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1586 : plan1586.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1587 : plan1587.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1588 : plan1588.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1589 : plan1589.Valid := valid_step _ _ _ valid574 (by decide +kernel)













theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1600 : plan1600.Valid := valid_step _ _ _ valid574 (by decide +kernel)







theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1606 : plan1606.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1607 : plan1607.Valid := valid_step _ _ _ valid582 (by decide +kernel)

theorem valid1608 : plan1608.Valid := valid_step _ _ _ valid584 (by decide +kernel)

theorem valid1609 : plan1609.Valid := valid_step _ _ _ valid585 (by decide +kernel)

theorem valid1610 : plan1610.Valid := valid_step _ _ _ valid581 (by decide +kernel)

theorem valid1611 : plan1611.Valid := valid_step _ _ _ valid582 (by decide +kernel)

theorem valid1612 : plan1612.Valid := valid_step _ _ _ valid583 (by decide +kernel)

theorem valid1613 : plan1613.Valid := valid_step _ _ _ valid584 (by decide +kernel)

theorem valid1614 : plan1614.Valid := valid_step _ _ _ valid585 (by decide +kernel)

theorem valid1615 : plan1615.Valid := valid_step _ _ _ valid586 (by decide +kernel)

theorem valid1616 : plan1616.Valid := valid_step _ _ _ valid584 (by decide +kernel)

theorem valid1617 : plan1617.Valid := valid_step _ _ _ valid582 (by decide +kernel)

theorem valid1618 : plan1618.Valid := valid_step _ _ _ valid584 (by decide +kernel)

theorem valid1619 : plan1619.Valid := valid_step _ _ _ valid585 (by decide +kernel)

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



















































































































theorem valid3322 : plan3322.Valid := valid_step _ _ _ valid1528 (by decide +kernel)























theorem valid3334 : plan3334.Valid := valid_step _ _ _ valid1528 (by decide +kernel)




















































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





















theorem valid3371 : plan3371.Valid := valid_step _ _ _ valid1556 (by decide +kernel)

theorem valid3372 : plan3372.Valid := valid_step _ _ _ valid1557 (by decide +kernel)

theorem valid3373 : plan3373.Valid := valid_step _ _ _ valid1558 (by decide +kernel)









































































theorem valid3410 : plan3410.Valid := valid_step _ _ _ valid1556 (by decide +kernel)

theorem valid3411 : plan3411.Valid := valid_step _ _ _ valid1557 (by decide +kernel)

theorem valid3412 : plan3412.Valid := valid_step _ _ _ valid1558 (by decide +kernel)





























































theorem valid3443 : plan3443.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3444 : plan3444.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3445 : plan3445.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3446 : plan3446.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3447 : plan3447.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3448 : plan3448.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3449 : plan3449.Valid := valid_step _ _ _ valid1606 (by decide +kernel)



theorem valid3451 : plan3451.Valid := valid_step _ _ _ valid1583 (by decide +kernel)

theorem valid3452 : plan3452.Valid := valid_step _ _ _ valid1584 (by decide +kernel)

theorem valid3453 : plan3453.Valid := valid_step _ _ _ valid1585 (by decide +kernel)

theorem valid3454 : plan3454.Valid := valid_step _ _ _ valid1586 (by decide +kernel)

theorem valid3455 : plan3455.Valid := valid_step _ _ _ valid1587 (by decide +kernel)

theorem valid3456 : plan3456.Valid := valid_step _ _ _ valid1588 (by decide +kernel)
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











































































theorem valid5510 : plan5510.Valid := valid_step _ _ _ valid3322 (by decide +kernel)







theorem valid5514 : plan5514.Valid := valid_step _ _ _ valid3334 (by decide +kernel)












































































































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

























































theorem valid6653 : plan6653.Valid := valid_step _ _ _ valid5510 (by decide +kernel)

theorem valid6654 : plan6654.Valid := valid_step _ _ _ valid5514 (by decide +kernel)




































































































































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

theorem valid3457 : plan3457.Valid := valid_step _ _ _ valid1589 (by decide +kernel)





















theorem valid3468 : plan3468.Valid := valid_step _ _ _ valid1600 (by decide +kernel)





































theorem valid3487 : plan3487.Valid := valid_step _ _ _ valid1583 (by decide +kernel)

theorem valid3488 : plan3488.Valid := valid_step _ _ _ valid1584 (by decide +kernel)

theorem valid3489 : plan3489.Valid := valid_step _ _ _ valid1585 (by decide +kernel)













































theorem valid3512 : plan3512.Valid := valid_step _ _ _ valid1607 (by decide +kernel)

theorem valid3513 : plan3513.Valid := valid_step _ _ _ valid1608 (by decide +kernel)

theorem valid3514 : plan3514.Valid := valid_step _ _ _ valid1609 (by decide +kernel)

theorem valid3515 : plan3515.Valid := valid_step _ _ _ valid1610 (by decide +kernel)

theorem valid3516 : plan3516.Valid := valid_step _ _ _ valid1611 (by decide +kernel)

theorem valid3517 : plan3517.Valid := valid_step _ _ _ valid1612 (by decide +kernel)

theorem valid3518 : plan3518.Valid := valid_step _ _ _ valid1613 (by decide +kernel)

theorem valid3519 : plan3519.Valid := valid_step _ _ _ valid1614 (by decide +kernel)

theorem valid3520 : plan3520.Valid := valid_step _ _ _ valid1615 (by decide +kernel)

theorem valid3521 : plan3521.Valid := valid_step _ _ _ valid1616 (by decide +kernel)

theorem valid3522 : plan3522.Valid := valid_step _ _ _ valid1617 (by decide +kernel)

theorem valid3523 : plan3523.Valid := valid_step _ _ _ valid1618 (by decide +kernel)

theorem valid3524 : plan3524.Valid := valid_step _ _ _ valid1619 (by decide +kernel)

theorem valid3525 : plan3525.Valid := valid_step _ _ _ valid1620 (by decide +kernel)

theorem valid3526 : plan3526.Valid := valid_step _ _ _ valid1621 (by decide +kernel)

theorem valid3527 : plan3527.Valid := valid_step _ _ _ valid1622 (by decide +kernel)

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



























theorem valid5678 : plan5678.Valid := valid_step _ _ _ valid3371 (by decide +kernel)

theorem valid5679 : plan5679.Valid := valid_step _ _ _ valid3372 (by decide +kernel)

theorem valid5680 : plan5680.Valid := valid_step _ _ _ valid3373 (by decide +kernel)

















theorem valid5689 : plan5689.Valid := valid_step _ _ _ valid3410 (by decide +kernel)

theorem valid5690 : plan5690.Valid := valid_step _ _ _ valid3411 (by decide +kernel)

theorem valid5691 : plan5691.Valid := valid_step _ _ _ valid3412 (by decide +kernel)










































































































































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

















































































































theorem valid5817 : plan5817.Valid := valid_step _ _ _ valid3443 (by decide +kernel)

theorem valid5818 : plan5818.Valid := valid_step _ _ _ valid3444 (by decide +kernel)

theorem valid5819 : plan5819.Valid := valid_step _ _ _ valid3445 (by decide +kernel)

theorem valid5820 : plan5820.Valid := valid_step _ _ _ valid3446 (by decide +kernel)

theorem valid5821 : plan5821.Valid := valid_step _ _ _ valid3447 (by decide +kernel)

theorem valid5822 : plan5822.Valid := valid_step _ _ _ valid3448 (by decide +kernel)

theorem valid5823 : plan5823.Valid := valid_step _ _ _ valid3449 (by decide +kernel)

theorem valid5824 : plan5824.Valid := valid_step _ _ _ valid3451 (by decide +kernel)

theorem valid5825 : plan5825.Valid := valid_step _ _ _ valid3452 (by decide +kernel)

theorem valid5826 : plan5826.Valid := valid_step _ _ _ valid3453 (by decide +kernel)

theorem valid5827 : plan5827.Valid := valid_step _ _ _ valid3454 (by decide +kernel)

theorem valid5828 : plan5828.Valid := valid_step _ _ _ valid3455 (by decide +kernel)

theorem valid5829 : plan5829.Valid := valid_step _ _ _ valid3456 (by decide +kernel)

theorem valid5830 : plan5830.Valid := valid_step _ _ _ valid3457 (by decide +kernel)





















theorem valid5841 : plan5841.Valid := valid_step _ _ _ valid3468 (by decide +kernel)






























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





theorem valid5859 : plan5859.Valid := valid_step _ _ _ valid3487 (by decide +kernel)

theorem valid5860 : plan5860.Valid := valid_step _ _ _ valid3488 (by decide +kernel)

theorem valid5861 : plan5861.Valid := valid_step _ _ _ valid3489 (by decide +kernel)






















































































































































































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





















































































theorem valid5995 : plan5995.Valid := valid_step _ _ _ valid3512 (by decide +kernel)

theorem valid5996 : plan5996.Valid := valid_step _ _ _ valid3513 (by decide +kernel)

theorem valid5997 : plan5997.Valid := valid_step _ _ _ valid3514 (by decide +kernel)

theorem valid5998 : plan5998.Valid := valid_step _ _ _ valid3515 (by decide +kernel)

theorem valid5999 : plan5999.Valid := valid_step _ _ _ valid3516 (by decide +kernel)

theorem valid6000 : plan6000.Valid := valid_step _ _ _ valid3517 (by decide +kernel)

theorem valid6001 : plan6001.Valid := valid_step _ _ _ valid3518 (by decide +kernel)

theorem valid6002 : plan6002.Valid := valid_step _ _ _ valid3519 (by decide +kernel)

theorem valid6003 : plan6003.Valid := valid_step _ _ _ valid3520 (by decide +kernel)

theorem valid6004 : plan6004.Valid := valid_step _ _ _ valid3521 (by decide +kernel)

theorem valid6005 : plan6005.Valid := valid_step _ _ _ valid3522 (by decide +kernel)

theorem valid6006 : plan6006.Valid := valid_step _ _ _ valid3523 (by decide +kernel)

theorem valid6007 : plan6007.Valid := valid_step _ _ _ valid3524 (by decide +kernel)

theorem valid6008 : plan6008.Valid := valid_step _ _ _ valid3525 (by decide +kernel)

theorem valid6009 : plan6009.Valid := valid_step _ _ _ valid3526 (by decide +kernel)

theorem valid6010 : plan6010.Valid := valid_step _ _ _ valid3527 (by decide +kernel)

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





































































































theorem valid7059 : plan7059.Valid := valid_step _ _ _ valid5678 (by decide +kernel)

theorem valid7060 : plan7060.Valid := valid_step _ _ _ valid5679 (by decide +kernel)

theorem valid7061 : plan7061.Valid := valid_step _ _ _ valid5680 (by decide +kernel)

theorem valid7062 : plan7062.Valid := valid_step _ _ _ valid5689 (by decide +kernel)

theorem valid7063 : plan7063.Valid := valid_step _ _ _ valid5690 (by decide +kernel)

theorem valid7064 : plan7064.Valid := valid_step _ _ _ valid5691 (by decide +kernel)
















































































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























































































































theorem valid7548 : plan7548.Valid := valid_step _ _ _ valid5817 (by decide +kernel)

theorem valid7549 : plan7549.Valid := valid_step _ _ _ valid5818 (by decide +kernel)

theorem valid7550 : plan7550.Valid := valid_step _ _ _ valid5819 (by decide +kernel)

theorem valid7551 : plan7551.Valid := valid_step _ _ _ valid5820 (by decide +kernel)

theorem valid7552 : plan7552.Valid := valid_step _ _ _ valid5821 (by decide +kernel)

theorem valid7553 : plan7553.Valid := valid_step _ _ _ valid5822 (by decide +kernel)

theorem valid7554 : plan7554.Valid := valid_step _ _ _ valid5823 (by decide +kernel)

theorem valid7555 : plan7555.Valid := valid_step _ _ _ valid5824 (by decide +kernel)

theorem valid7556 : plan7556.Valid := valid_step _ _ _ valid5825 (by decide +kernel)

theorem valid7557 : plan7557.Valid := valid_step _ _ _ valid5826 (by decide +kernel)

theorem valid7558 : plan7558.Valid := valid_step _ _ _ valid5827 (by decide +kernel)

theorem valid7559 : plan7559.Valid := valid_step _ _ _ valid5828 (by decide +kernel)

theorem valid7560 : plan7560.Valid := valid_step _ _ _ valid5829 (by decide +kernel)

theorem valid7561 : plan7561.Valid := valid_step _ _ _ valid5830 (by decide +kernel)

theorem valid7562 : plan7562.Valid := valid_step _ _ _ valid5841 (by decide +kernel)

theorem valid7563 : plan7563.Valid := valid_step _ _ _ valid5859 (by decide +kernel)

theorem valid7564 : plan7564.Valid := valid_step _ _ _ valid5860 (by decide +kernel)

theorem valid7565 : plan7565.Valid := valid_step _ _ _ valid5861 (by decide +kernel)






































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







































































theorem valid7812 : plan7812.Valid := valid_step _ _ _ valid5995 (by decide +kernel)

theorem valid7813 : plan7813.Valid := valid_step _ _ _ valid5996 (by decide +kernel)

theorem valid7814 : plan7814.Valid := valid_step _ _ _ valid5997 (by decide +kernel)

theorem valid7815 : plan7815.Valid := valid_step _ _ _ valid5998 (by decide +kernel)

theorem valid7816 : plan7816.Valid := valid_step _ _ _ valid5999 (by decide +kernel)

theorem valid7817 : plan7817.Valid := valid_step _ _ _ valid6000 (by decide +kernel)

theorem valid7818 : plan7818.Valid := valid_step _ _ _ valid6001 (by decide +kernel)

theorem valid7819 : plan7819.Valid := valid_step _ _ _ valid6002 (by decide +kernel)

theorem valid7820 : plan7820.Valid := valid_step _ _ _ valid6003 (by decide +kernel)

theorem valid7821 : plan7821.Valid := valid_step _ _ _ valid6004 (by decide +kernel)

theorem valid7822 : plan7822.Valid := valid_step _ _ _ valid6005 (by decide +kernel)

theorem valid7823 : plan7823.Valid := valid_step _ _ _ valid6006 (by decide +kernel)

theorem valid7824 : plan7824.Valid := valid_step _ _ _ valid6007 (by decide +kernel)

theorem valid7825 : plan7825.Valid := valid_step _ _ _ valid6008 (by decide +kernel)

theorem valid7826 : plan7826.Valid := valid_step _ _ _ valid6009 (by decide +kernel)

theorem valid7827 : plan7827.Valid := valid_step _ _ _ valid6010 (by decide +kernel)

theorem valid7828 : plan7828.Valid := valid_step _ _ _ valid6011 (by decide +kernel)

theorem valid7829 : plan7829.Valid := valid_step _ _ _ valid6012 (by decide +kernel)

theorem valid7830 : plan7830.Valid := valid_step _ _ _ valid6013 (by decide +kernel)

theorem valid7831 : plan7831.Valid := valid_step _ _ _ valid6014 (by decide +kernel)

theorem valid7832 : plan7832.Valid := valid_step _ _ _ valid6015 (by decide +kernel)

theorem valid7833 : plan7833.Valid := valid_step _ _ _ valid6016 (by decide +kernel)

theorem valid7834 : plan7834.Valid := valid_step _ _ _ valid6017 (by decide +kernel)

theorem valid7835 : plan7835.Valid := valid_step _ _ _ valid6018 (by decide +kernel)

theorem valid7836 : plan7836.Valid := valid_step _ _ _ valid6019 (by decide +kernel)

theorem valid7837 : plan7837.Valid := valid_step _ _ _ valid6020 (by decide +kernel)

theorem valid7838 : plan7838.Valid := valid_step _ _ _ valid6021 (by decide +kernel)




































































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
theorem t6_1235choices : plan7548.choices=[5,5,3,6,7,7].map (options 6 5) := by rfl


theorem t6_1235part0 : t6_1235jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1235part1 : t6_1235jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1235part2 : t6_1235jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1235frontier : t6_1235root.frontier 1=t6_1235jobs := by rfl
theorem t6_1235all : t6_1235jobs.all (Job.check tree)=true := by
  simp only [t6_1235jobs,List.all_append,List.all_nil,t6_1235part0,t6_1235part1,t6_1235part2,Bool.and_self]
theorem t6_1235checked : Checked tree [5,5,3,6,7,7] := by
  refine ⟨plan7548,valid7548,t6_1235choices,?_⟩
  exact check_of_frontier tree 1 t6_1235root t6_1235jobs t6_1235frontier t6_1235all
theorem t6_1236choices : plan7549.choices=[5,5,3,6,10,7].map (options 6 5) := by rfl


theorem t6_1236part0 : t6_1236jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1236part1 : t6_1236jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1236frontier : t6_1236root.frontier 1=t6_1236jobs := by rfl
theorem t6_1236all : t6_1236jobs.all (Job.check tree)=true := by
  simp only [t6_1236jobs,List.all_append,List.all_nil,t6_1236part0,t6_1236part1,Bool.and_self]
theorem t6_1236checked : Checked tree [5,5,3,6,10,7] := by
  refine ⟨plan7549,valid7549,t6_1236choices,?_⟩
  exact check_of_frontier tree 1 t6_1236root t6_1236jobs t6_1236frontier t6_1236all
theorem t6_1237choices : plan7550.choices=[5,5,3,6,10,10].map (options 6 5) := by rfl


theorem t6_1237part0 : t6_1237jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1237frontier : t6_1237root.frontier 0=t6_1237jobs := by rfl
theorem t6_1237all : t6_1237jobs.all (Job.check tree)=true := by
  simp only [t6_1237jobs,List.all_append,List.all_nil,t6_1237part0,Bool.and_self]
theorem t6_1237checked : Checked tree [5,5,3,6,10,10] := by
  refine ⟨plan7550,valid7550,t6_1237choices,?_⟩
  exact check_of_frontier tree 0 t6_1237root t6_1237jobs t6_1237frontier t6_1237all
theorem t6_1238choices : plan7551.choices=[5,5,3,7,7,7].map (options 6 5) := by rfl


theorem t6_1238part0 : t6_1238jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1238part1 : t6_1238jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1238frontier : t6_1238root.frontier 1=t6_1238jobs := by rfl
theorem t6_1238all : t6_1238jobs.all (Job.check tree)=true := by
  simp only [t6_1238jobs,List.all_append,List.all_nil,t6_1238part0,t6_1238part1,Bool.and_self]
theorem t6_1238checked : Checked tree [5,5,3,7,7,7] := by
  refine ⟨plan7551,valid7551,t6_1238choices,?_⟩
  exact check_of_frontier tree 1 t6_1238root t6_1238jobs t6_1238frontier t6_1238all
theorem t6_1239choices : plan7552.choices=[5,5,3,10,7,7].map (options 6 5) := by rfl


theorem t6_1239part0 : t6_1239jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1239part1 : t6_1239jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1239part2 : t6_1239jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1239frontier : t6_1239root.frontier 1=t6_1239jobs := by rfl
theorem t6_1239all : t6_1239jobs.all (Job.check tree)=true := by
  simp only [t6_1239jobs,List.all_append,List.all_nil,t6_1239part0,t6_1239part1,t6_1239part2,Bool.and_self]
theorem t6_1239checked : Checked tree [5,5,3,10,7,7] := by
  refine ⟨plan7552,valid7552,t6_1239choices,?_⟩
  exact check_of_frontier tree 1 t6_1239root t6_1239jobs t6_1239frontier t6_1239all
theorem t6_1240choices : plan7553.choices=[5,5,3,10,10,7].map (options 6 5) := by rfl


theorem t6_1240part0 : t6_1240jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1240part1 : t6_1240jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1240frontier : t6_1240root.frontier 1=t6_1240jobs := by rfl
theorem t6_1240all : t6_1240jobs.all (Job.check tree)=true := by
  simp only [t6_1240jobs,List.all_append,List.all_nil,t6_1240part0,t6_1240part1,Bool.and_self]
theorem t6_1240checked : Checked tree [5,5,3,10,10,7] := by
  refine ⟨plan7553,valid7553,t6_1240choices,?_⟩
  exact check_of_frontier tree 1 t6_1240root t6_1240jobs t6_1240frontier t6_1240all
theorem t6_1241choices : plan7554.choices=[5,5,3,10,10,10].map (options 6 5) := by rfl


theorem t6_1241part0 : t6_1241jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1241frontier : t6_1241root.frontier 0=t6_1241jobs := by rfl
theorem t6_1241all : t6_1241jobs.all (Job.check tree)=true := by
  simp only [t6_1241jobs,List.all_append,List.all_nil,t6_1241part0,Bool.and_self]
theorem t6_1241checked : Checked tree [5,5,3,10,10,10] := by
  refine ⟨plan7554,valid7554,t6_1241choices,?_⟩
  exact check_of_frontier tree 0 t6_1241root t6_1241jobs t6_1241frontier t6_1241all
theorem t6_1242choices : plan6653.choices=[5,5,5,3,3,3].map (options 6 3) := by rfl


theorem t6_1242part0 : t6_1242jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1242frontier : t6_1242root.frontier 0=t6_1242jobs := by rfl
theorem t6_1242all : t6_1242jobs.all (Job.check tree)=true := by
  simp only [t6_1242jobs,List.all_append,List.all_nil,t6_1242part0,Bool.and_self]
theorem t6_1242checked : Checked tree [5,5,5,3,3,3] := by
  refine ⟨plan6653,valid6653,t6_1242choices,?_⟩
  exact check_of_frontier tree 0 t6_1242root t6_1242jobs t6_1242frontier t6_1242all
theorem t6_1243choices : plan7059.choices=[5,5,5,3,3,6].map (options 6 4) := by rfl


theorem t6_1243part0 : t6_1243jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1243frontier : t6_1243root.frontier 0=t6_1243jobs := by rfl
theorem t6_1243all : t6_1243jobs.all (Job.check tree)=true := by
  simp only [t6_1243jobs,List.all_append,List.all_nil,t6_1243part0,Bool.and_self]
theorem t6_1243checked : Checked tree [5,5,5,3,3,6] := by
  refine ⟨plan7059,valid7059,t6_1243choices,?_⟩
  exact check_of_frontier tree 0 t6_1243root t6_1243jobs t6_1243frontier t6_1243all
theorem t6_1244choices : plan7060.choices=[5,5,5,3,3,7].map (options 6 4) := by rfl


theorem t6_1244part0 : t6_1244jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1244frontier : t6_1244root.frontier 0=t6_1244jobs := by rfl
theorem t6_1244all : t6_1244jobs.all (Job.check tree)=true := by
  simp only [t6_1244jobs,List.all_append,List.all_nil,t6_1244part0,Bool.and_self]
theorem t6_1244checked : Checked tree [5,5,5,3,3,7] := by
  refine ⟨plan7060,valid7060,t6_1244choices,?_⟩
  exact check_of_frontier tree 0 t6_1244root t6_1244jobs t6_1244frontier t6_1244all
theorem t6_1245choices : plan7061.choices=[5,5,5,3,3,10].map (options 6 4) := by rfl


theorem t6_1245part0 : t6_1245jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1245frontier : t6_1245root.frontier 0=t6_1245jobs := by rfl
theorem t6_1245all : t6_1245jobs.all (Job.check tree)=true := by
  simp only [t6_1245jobs,List.all_append,List.all_nil,t6_1245part0,Bool.and_self]
theorem t6_1245checked : Checked tree [5,5,5,3,3,10] := by
  refine ⟨plan7061,valid7061,t6_1245choices,?_⟩
  exact check_of_frontier tree 0 t6_1245root t6_1245jobs t6_1245frontier t6_1245all
theorem t6_1246choices : plan7555.choices=[5,5,5,3,6,6].map (options 6 5) := by rfl


theorem t6_1246part0 : t6_1246jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1246frontier : t6_1246root.frontier 0=t6_1246jobs := by rfl
theorem t6_1246all : t6_1246jobs.all (Job.check tree)=true := by
  simp only [t6_1246jobs,List.all_append,List.all_nil,t6_1246part0,Bool.and_self]
theorem t6_1246checked : Checked tree [5,5,5,3,6,6] := by
  refine ⟨plan7555,valid7555,t6_1246choices,?_⟩
  exact check_of_frontier tree 0 t6_1246root t6_1246jobs t6_1246frontier t6_1246all
theorem t6_1247choices : plan7556.choices=[5,5,5,3,6,7].map (options 6 5) := by rfl


theorem t6_1247part0 : t6_1247jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1247frontier : t6_1247root.frontier 0=t6_1247jobs := by rfl
theorem t6_1247all : t6_1247jobs.all (Job.check tree)=true := by
  simp only [t6_1247jobs,List.all_append,List.all_nil,t6_1247part0,Bool.and_self]
theorem t6_1247checked : Checked tree [5,5,5,3,6,7] := by
  refine ⟨plan7556,valid7556,t6_1247choices,?_⟩
  exact check_of_frontier tree 0 t6_1247root t6_1247jobs t6_1247frontier t6_1247all
theorem t6_1248choices : plan7557.choices=[5,5,5,3,6,10].map (options 6 5) := by rfl


theorem t6_1248part0 : t6_1248jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1248frontier : t6_1248root.frontier 0=t6_1248jobs := by rfl
theorem t6_1248all : t6_1248jobs.all (Job.check tree)=true := by
  simp only [t6_1248jobs,List.all_append,List.all_nil,t6_1248part0,Bool.and_self]
theorem t6_1248checked : Checked tree [5,5,5,3,6,10] := by
  refine ⟨plan7557,valid7557,t6_1248choices,?_⟩
  exact check_of_frontier tree 0 t6_1248root t6_1248jobs t6_1248frontier t6_1248all
theorem t6_1249choices : plan7558.choices=[5,5,5,3,7,7].map (options 6 5) := by rfl


theorem t6_1249part0 : t6_1249jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1249frontier : t6_1249root.frontier 0=t6_1249jobs := by rfl
theorem t6_1249all : t6_1249jobs.all (Job.check tree)=true := by
  simp only [t6_1249jobs,List.all_append,List.all_nil,t6_1249part0,Bool.and_self]
theorem t6_1249checked : Checked tree [5,5,5,3,7,7] := by
  refine ⟨plan7558,valid7558,t6_1249choices,?_⟩
  exact check_of_frontier tree 0 t6_1249root t6_1249jobs t6_1249frontier t6_1249all
theorem t6_1250choices : plan7559.choices=[5,5,5,3,10,7].map (options 6 5) := by rfl


theorem t6_1250part0 : t6_1250jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1250frontier : t6_1250root.frontier 0=t6_1250jobs := by rfl
theorem t6_1250all : t6_1250jobs.all (Job.check tree)=true := by
  simp only [t6_1250jobs,List.all_append,List.all_nil,t6_1250part0,Bool.and_self]
theorem t6_1250checked : Checked tree [5,5,5,3,10,7] := by
  refine ⟨plan7559,valid7559,t6_1250choices,?_⟩
  exact check_of_frontier tree 0 t6_1250root t6_1250jobs t6_1250frontier t6_1250all
theorem t6_1251choices : plan7560.choices=[5,5,5,3,10,10].map (options 6 5) := by rfl


theorem t6_1251part0 : t6_1251jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1251frontier : t6_1251root.frontier 0=t6_1251jobs := by rfl
theorem t6_1251all : t6_1251jobs.all (Job.check tree)=true := by
  simp only [t6_1251jobs,List.all_append,List.all_nil,t6_1251part0,Bool.and_self]
theorem t6_1251checked : Checked tree [5,5,5,3,10,10] := by
  refine ⟨plan7560,valid7560,t6_1251choices,?_⟩
  exact check_of_frontier tree 0 t6_1251root t6_1251jobs t6_1251frontier t6_1251all
theorem t6_1252choices : plan7561.choices=[5,5,5,5,3,7].map (options 6 5) := by rfl


theorem t6_1252part0 : t6_1252jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1252frontier : t6_1252root.frontier 0=t6_1252jobs := by rfl
theorem t6_1252all : t6_1252jobs.all (Job.check tree)=true := by
  simp only [t6_1252jobs,List.all_append,List.all_nil,t6_1252part0,Bool.and_self]
theorem t6_1252checked : Checked tree [5,5,5,5,3,7] := by
  refine ⟨plan7561,valid7561,t6_1252choices,?_⟩
  exact check_of_frontier tree 0 t6_1252root t6_1252jobs t6_1252frontier t6_1252all
theorem t6_1253choices : plan7812.choices=[5,5,5,5,6,7].map (options 6 6) := by rfl


theorem t6_1253part0 : t6_1253jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1253frontier : t6_1253root.frontier 0=t6_1253jobs := by rfl
theorem t6_1253all : t6_1253jobs.all (Job.check tree)=true := by
  simp only [t6_1253jobs,List.all_append,List.all_nil,t6_1253part0,Bool.and_self]
theorem t6_1253checked : Checked tree [5,5,5,5,6,7] := by
  refine ⟨plan7812,valid7812,t6_1253choices,?_⟩
  exact check_of_frontier tree 0 t6_1253root t6_1253jobs t6_1253frontier t6_1253all
theorem t6_1254choices : plan7813.choices=[5,5,5,5,7,7].map (options 6 6) := by rfl


theorem t6_1254part0 : t6_1254jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1254frontier : t6_1254root.frontier 0=t6_1254jobs := by rfl
theorem t6_1254all : t6_1254jobs.all (Job.check tree)=true := by
  simp only [t6_1254jobs,List.all_append,List.all_nil,t6_1254part0,Bool.and_self]
theorem t6_1254checked : Checked tree [5,5,5,5,7,7] := by
  refine ⟨plan7813,valid7813,t6_1254choices,?_⟩
  exact check_of_frontier tree 0 t6_1254root t6_1254jobs t6_1254frontier t6_1254all
theorem t6_1255choices : plan7814.choices=[5,5,5,5,10,7].map (options 6 6) := by rfl


theorem t6_1255part0 : t6_1255jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1255frontier : t6_1255root.frontier 0=t6_1255jobs := by rfl
theorem t6_1255all : t6_1255jobs.all (Job.check tree)=true := by
  simp only [t6_1255jobs,List.all_append,List.all_nil,t6_1255part0,Bool.and_self]
theorem t6_1255checked : Checked tree [5,5,5,5,10,7] := by
  refine ⟨plan7814,valid7814,t6_1255choices,?_⟩
  exact check_of_frontier tree 0 t6_1255root t6_1255jobs t6_1255frontier t6_1255all
theorem t6_1256choices : plan7815.choices=[5,5,5,6,6,6].map (options 6 6) := by rfl


theorem t6_1256part0 : t6_1256jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1256frontier : t6_1256root.frontier 0=t6_1256jobs := by rfl
theorem t6_1256all : t6_1256jobs.all (Job.check tree)=true := by
  simp only [t6_1256jobs,List.all_append,List.all_nil,t6_1256part0,Bool.and_self]
theorem t6_1256checked : Checked tree [5,5,5,6,6,6] := by
  refine ⟨plan7815,valid7815,t6_1256choices,?_⟩
  exact check_of_frontier tree 0 t6_1256root t6_1256jobs t6_1256frontier t6_1256all
theorem t6_1257choices : plan7816.choices=[5,5,5,6,6,7].map (options 6 6) := by rfl


theorem t6_1257part0 : t6_1257jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1257frontier : t6_1257root.frontier 0=t6_1257jobs := by rfl
theorem t6_1257all : t6_1257jobs.all (Job.check tree)=true := by
  simp only [t6_1257jobs,List.all_append,List.all_nil,t6_1257part0,Bool.and_self]
theorem t6_1257checked : Checked tree [5,5,5,6,6,7] := by
  refine ⟨plan7816,valid7816,t6_1257choices,?_⟩
  exact check_of_frontier tree 0 t6_1257root t6_1257jobs t6_1257frontier t6_1257all
theorem t6_1258choices : plan7817.choices=[5,5,5,6,6,10].map (options 6 6) := by rfl


theorem t6_1258part0 : t6_1258jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1258frontier : t6_1258root.frontier 0=t6_1258jobs := by rfl
theorem t6_1258all : t6_1258jobs.all (Job.check tree)=true := by
  simp only [t6_1258jobs,List.all_append,List.all_nil,t6_1258part0,Bool.and_self]
theorem t6_1258checked : Checked tree [5,5,5,6,6,10] := by
  refine ⟨plan7817,valid7817,t6_1258choices,?_⟩
  exact check_of_frontier tree 0 t6_1258root t6_1258jobs t6_1258frontier t6_1258all
theorem t6_1259choices : plan7818.choices=[5,5,5,6,7,7].map (options 6 6) := by rfl


theorem t6_1259part0 : t6_1259jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1259frontier : t6_1259root.frontier 0=t6_1259jobs := by rfl
theorem t6_1259all : t6_1259jobs.all (Job.check tree)=true := by
  simp only [t6_1259jobs,List.all_append,List.all_nil,t6_1259part0,Bool.and_self]
theorem t6_1259checked : Checked tree [5,5,5,6,7,7] := by
  refine ⟨plan7818,valid7818,t6_1259choices,?_⟩
  exact check_of_frontier tree 0 t6_1259root t6_1259jobs t6_1259frontier t6_1259all
theorem t6_1260choices : plan7819.choices=[5,5,5,6,10,7].map (options 6 6) := by rfl


theorem t6_1260part0 : t6_1260jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1260frontier : t6_1260root.frontier 0=t6_1260jobs := by rfl
theorem t6_1260all : t6_1260jobs.all (Job.check tree)=true := by
  simp only [t6_1260jobs,List.all_append,List.all_nil,t6_1260part0,Bool.and_self]
theorem t6_1260checked : Checked tree [5,5,5,6,10,7] := by
  refine ⟨plan7819,valid7819,t6_1260choices,?_⟩
  exact check_of_frontier tree 0 t6_1260root t6_1260jobs t6_1260frontier t6_1260all
theorem t6_1261choices : plan7820.choices=[5,5,5,6,10,10].map (options 6 6) := by rfl


theorem t6_1261part0 : t6_1261jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1261frontier : t6_1261root.frontier 0=t6_1261jobs := by rfl
theorem t6_1261all : t6_1261jobs.all (Job.check tree)=true := by
  simp only [t6_1261jobs,List.all_append,List.all_nil,t6_1261part0,Bool.and_self]
theorem t6_1261checked : Checked tree [5,5,5,6,10,10] := by
  refine ⟨plan7820,valid7820,t6_1261choices,?_⟩
  exact check_of_frontier tree 0 t6_1261root t6_1261jobs t6_1261frontier t6_1261all
theorem t6_1262choices : plan7821.choices=[5,5,5,7,7,7].map (options 6 6) := by rfl


theorem t6_1262part0 : t6_1262jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1262frontier : t6_1262root.frontier 0=t6_1262jobs := by rfl
theorem t6_1262all : t6_1262jobs.all (Job.check tree)=true := by
  simp only [t6_1262jobs,List.all_append,List.all_nil,t6_1262part0,Bool.and_self]
theorem t6_1262checked : Checked tree [5,5,5,7,7,7] := by
  refine ⟨plan7821,valid7821,t6_1262choices,?_⟩
  exact check_of_frontier tree 0 t6_1262root t6_1262jobs t6_1262frontier t6_1262all
theorem t6_1263choices : plan7562.choices=[5,5,5,9,3,7].map (options 6 5) := by rfl


theorem t6_1263part0 : t6_1263jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1263frontier : t6_1263root.frontier 0=t6_1263jobs := by rfl
theorem t6_1263all : t6_1263jobs.all (Job.check tree)=true := by
  simp only [t6_1263jobs,List.all_append,List.all_nil,t6_1263part0,Bool.and_self]
theorem t6_1263checked : Checked tree [5,5,5,9,3,7] := by
  refine ⟨plan7562,valid7562,t6_1263choices,?_⟩
  exact check_of_frontier tree 0 t6_1263root t6_1263jobs t6_1263frontier t6_1263all
theorem t6_1264choices : plan7822.choices=[5,5,5,9,6,7].map (options 6 6) := by rfl


theorem t6_1264part0 : t6_1264jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1264frontier : t6_1264root.frontier 0=t6_1264jobs := by rfl
theorem t6_1264all : t6_1264jobs.all (Job.check tree)=true := by
  simp only [t6_1264jobs,List.all_append,List.all_nil,t6_1264part0,Bool.and_self]
theorem t6_1264checked : Checked tree [5,5,5,9,6,7] := by
  refine ⟨plan7822,valid7822,t6_1264choices,?_⟩
  exact check_of_frontier tree 0 t6_1264root t6_1264jobs t6_1264frontier t6_1264all
theorem t6_1265choices : plan7823.choices=[5,5,5,9,7,7].map (options 6 6) := by rfl


theorem t6_1265part0 : t6_1265jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1265frontier : t6_1265root.frontier 0=t6_1265jobs := by rfl
theorem t6_1265all : t6_1265jobs.all (Job.check tree)=true := by
  simp only [t6_1265jobs,List.all_append,List.all_nil,t6_1265part0,Bool.and_self]
theorem t6_1265checked : Checked tree [5,5,5,9,7,7] := by
  refine ⟨plan7823,valid7823,t6_1265choices,?_⟩
  exact check_of_frontier tree 0 t6_1265root t6_1265jobs t6_1265frontier t6_1265all
theorem t6_1266choices : plan7824.choices=[5,5,5,9,10,7].map (options 6 6) := by rfl


theorem t6_1266part0 : t6_1266jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1266frontier : t6_1266root.frontier 0=t6_1266jobs := by rfl
theorem t6_1266all : t6_1266jobs.all (Job.check tree)=true := by
  simp only [t6_1266jobs,List.all_append,List.all_nil,t6_1266part0,Bool.and_self]
theorem t6_1266checked : Checked tree [5,5,5,9,10,7] := by
  refine ⟨plan7824,valid7824,t6_1266choices,?_⟩
  exact check_of_frontier tree 0 t6_1266root t6_1266jobs t6_1266frontier t6_1266all
theorem t6_1267choices : plan7825.choices=[5,5,5,10,7,7].map (options 6 6) := by rfl


theorem t6_1267part0 : t6_1267jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1267frontier : t6_1267root.frontier 0=t6_1267jobs := by rfl
theorem t6_1267all : t6_1267jobs.all (Job.check tree)=true := by
  simp only [t6_1267jobs,List.all_append,List.all_nil,t6_1267part0,Bool.and_self]
theorem t6_1267checked : Checked tree [5,5,5,10,7,7] := by
  refine ⟨plan7825,valid7825,t6_1267choices,?_⟩
  exact check_of_frontier tree 0 t6_1267root t6_1267jobs t6_1267frontier t6_1267all
theorem t6_1268choices : plan7826.choices=[5,5,5,10,10,7].map (options 6 6) := by rfl


theorem t6_1268part0 : t6_1268jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1268frontier : t6_1268root.frontier 0=t6_1268jobs := by rfl
theorem t6_1268all : t6_1268jobs.all (Job.check tree)=true := by
  simp only [t6_1268jobs,List.all_append,List.all_nil,t6_1268part0,Bool.and_self]
theorem t6_1268checked : Checked tree [5,5,5,10,10,7] := by
  refine ⟨plan7826,valid7826,t6_1268choices,?_⟩
  exact check_of_frontier tree 0 t6_1268root t6_1268jobs t6_1268frontier t6_1268all
theorem t6_1269choices : plan7827.choices=[5,5,5,10,10,10].map (options 6 6) := by rfl


theorem t6_1269part0 : t6_1269jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1269frontier : t6_1269root.frontier 0=t6_1269jobs := by rfl
theorem t6_1269all : t6_1269jobs.all (Job.check tree)=true := by
  simp only [t6_1269jobs,List.all_append,List.all_nil,t6_1269part0,Bool.and_self]
theorem t6_1269checked : Checked tree [5,5,5,10,10,10] := by
  refine ⟨plan7827,valid7827,t6_1269choices,?_⟩
  exact check_of_frontier tree 0 t6_1269root t6_1269jobs t6_1269frontier t6_1269all
theorem t6_1270choices : plan7828.choices=[5,5,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1270part0 : t6_1270jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1270frontier : t6_1270root.frontier 0=t6_1270jobs := by rfl
theorem t6_1270all : t6_1270jobs.all (Job.check tree)=true := by
  simp only [t6_1270jobs,List.all_append,List.all_nil,t6_1270part0,Bool.and_self]
theorem t6_1270checked : Checked tree [5,5,6,6,6,6] := by
  refine ⟨plan7828,valid7828,t6_1270choices,?_⟩
  exact check_of_frontier tree 0 t6_1270root t6_1270jobs t6_1270frontier t6_1270all
theorem t6_1271choices : plan7829.choices=[5,5,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1271part0 : t6_1271jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1271frontier : t6_1271root.frontier 0=t6_1271jobs := by rfl
theorem t6_1271all : t6_1271jobs.all (Job.check tree)=true := by
  simp only [t6_1271jobs,List.all_append,List.all_nil,t6_1271part0,Bool.and_self]
theorem t6_1271checked : Checked tree [5,5,6,6,6,7] := by
  refine ⟨plan7829,valid7829,t6_1271choices,?_⟩
  exact check_of_frontier tree 0 t6_1271root t6_1271jobs t6_1271frontier t6_1271all
theorem t6_1272choices : plan7830.choices=[5,5,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1272part0 : t6_1272jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1272frontier : t6_1272root.frontier 0=t6_1272jobs := by rfl
theorem t6_1272all : t6_1272jobs.all (Job.check tree)=true := by
  simp only [t6_1272jobs,List.all_append,List.all_nil,t6_1272part0,Bool.and_self]
theorem t6_1272checked : Checked tree [5,5,6,6,6,10] := by
  refine ⟨plan7830,valid7830,t6_1272choices,?_⟩
  exact check_of_frontier tree 0 t6_1272root t6_1272jobs t6_1272frontier t6_1272all
theorem t6_1273choices : plan7831.choices=[5,5,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1273part0 : t6_1273jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1273frontier : t6_1273root.frontier 0=t6_1273jobs := by rfl
theorem t6_1273all : t6_1273jobs.all (Job.check tree)=true := by
  simp only [t6_1273jobs,List.all_append,List.all_nil,t6_1273part0,Bool.and_self]
theorem t6_1273checked : Checked tree [5,5,6,6,7,7] := by
  refine ⟨plan7831,valid7831,t6_1273choices,?_⟩
  exact check_of_frontier tree 0 t6_1273root t6_1273jobs t6_1273frontier t6_1273all
theorem t6_1274choices : plan7832.choices=[5,5,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1274part0 : t6_1274jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1274frontier : t6_1274root.frontier 0=t6_1274jobs := by rfl
theorem t6_1274all : t6_1274jobs.all (Job.check tree)=true := by
  simp only [t6_1274jobs,List.all_append,List.all_nil,t6_1274part0,Bool.and_self]
theorem t6_1274checked : Checked tree [5,5,6,6,10,7] := by
  refine ⟨plan7832,valid7832,t6_1274choices,?_⟩
  exact check_of_frontier tree 0 t6_1274root t6_1274jobs t6_1274frontier t6_1274all
theorem t6_1275choices : plan7833.choices=[5,5,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1275part0 : t6_1275jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1275frontier : t6_1275root.frontier 0=t6_1275jobs := by rfl
theorem t6_1275all : t6_1275jobs.all (Job.check tree)=true := by
  simp only [t6_1275jobs,List.all_append,List.all_nil,t6_1275part0,Bool.and_self]
theorem t6_1275checked : Checked tree [5,5,6,6,10,10] := by
  refine ⟨plan7833,valid7833,t6_1275choices,?_⟩
  exact check_of_frontier tree 0 t6_1275root t6_1275jobs t6_1275frontier t6_1275all
theorem t6_1276choices : plan7834.choices=[5,5,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1276part0 : t6_1276jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1276frontier : t6_1276root.frontier 0=t6_1276jobs := by rfl
theorem t6_1276all : t6_1276jobs.all (Job.check tree)=true := by
  simp only [t6_1276jobs,List.all_append,List.all_nil,t6_1276part0,Bool.and_self]
theorem t6_1276checked : Checked tree [5,5,6,7,7,7] := by
  refine ⟨plan7834,valid7834,t6_1276choices,?_⟩
  exact check_of_frontier tree 0 t6_1276root t6_1276jobs t6_1276frontier t6_1276all
theorem t6_1277choices : plan7835.choices=[5,5,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1277part0 : t6_1277jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1277frontier : t6_1277root.frontier 0=t6_1277jobs := by rfl
theorem t6_1277all : t6_1277jobs.all (Job.check tree)=true := by
  simp only [t6_1277jobs,List.all_append,List.all_nil,t6_1277part0,Bool.and_self]
theorem t6_1277checked : Checked tree [5,5,6,10,7,7] := by
  refine ⟨plan7835,valid7835,t6_1277choices,?_⟩
  exact check_of_frontier tree 0 t6_1277root t6_1277jobs t6_1277frontier t6_1277all
theorem t6_1278choices : plan7836.choices=[5,5,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1278part0 : t6_1278jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1278frontier : t6_1278root.frontier 0=t6_1278jobs := by rfl
theorem t6_1278all : t6_1278jobs.all (Job.check tree)=true := by
  simp only [t6_1278jobs,List.all_append,List.all_nil,t6_1278part0,Bool.and_self]
theorem t6_1278checked : Checked tree [5,5,6,10,10,7] := by
  refine ⟨plan7836,valid7836,t6_1278choices,?_⟩
  exact check_of_frontier tree 0 t6_1278root t6_1278jobs t6_1278frontier t6_1278all
theorem t6_1279choices : plan7837.choices=[5,5,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1279part0 : t6_1279jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1279frontier : t6_1279root.frontier 0=t6_1279jobs := by rfl
theorem t6_1279all : t6_1279jobs.all (Job.check tree)=true := by
  simp only [t6_1279jobs,List.all_append,List.all_nil,t6_1279part0,Bool.and_self]
theorem t6_1279checked : Checked tree [5,5,6,10,10,10] := by
  refine ⟨plan7837,valid7837,t6_1279choices,?_⟩
  exact check_of_frontier tree 0 t6_1279root t6_1279jobs t6_1279frontier t6_1279all
theorem t6_1280choices : plan7838.choices=[5,5,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1280part0 : t6_1280jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1280frontier : t6_1280root.frontier 0=t6_1280jobs := by rfl
theorem t6_1280all : t6_1280jobs.all (Job.check tree)=true := by
  simp only [t6_1280jobs,List.all_append,List.all_nil,t6_1280part0,Bool.and_self]
theorem t6_1280checked : Checked tree [5,5,7,7,7,7] := by
  refine ⟨plan7838,valid7838,t6_1280choices,?_⟩
  exact check_of_frontier tree 0 t6_1280root t6_1280jobs t6_1280frontier t6_1280all
theorem t6_1281choices : plan6654.choices=[5,5,9,3,3,3].map (options 6 3) := by rfl


theorem t6_1281part0 : t6_1281jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1281frontier : t6_1281root.frontier 0=t6_1281jobs := by rfl
theorem t6_1281all : t6_1281jobs.all (Job.check tree)=true := by
  simp only [t6_1281jobs,List.all_append,List.all_nil,t6_1281part0,Bool.and_self]
theorem t6_1281checked : Checked tree [5,5,9,3,3,3] := by
  refine ⟨plan6654,valid6654,t6_1281choices,?_⟩
  exact check_of_frontier tree 0 t6_1281root t6_1281jobs t6_1281frontier t6_1281all
theorem t6_1282choices : plan7062.choices=[5,5,9,3,3,6].map (options 6 4) := by rfl


theorem t6_1282part0 : t6_1282jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1282frontier : t6_1282root.frontier 0=t6_1282jobs := by rfl
theorem t6_1282all : t6_1282jobs.all (Job.check tree)=true := by
  simp only [t6_1282jobs,List.all_append,List.all_nil,t6_1282part0,Bool.and_self]
theorem t6_1282checked : Checked tree [5,5,9,3,3,6] := by
  refine ⟨plan7062,valid7062,t6_1282choices,?_⟩
  exact check_of_frontier tree 0 t6_1282root t6_1282jobs t6_1282frontier t6_1282all
theorem t6_1283choices : plan7063.choices=[5,5,9,3,3,7].map (options 6 4) := by rfl


theorem t6_1283part0 : t6_1283jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1283frontier : t6_1283root.frontier 0=t6_1283jobs := by rfl
theorem t6_1283all : t6_1283jobs.all (Job.check tree)=true := by
  simp only [t6_1283jobs,List.all_append,List.all_nil,t6_1283part0,Bool.and_self]
theorem t6_1283checked : Checked tree [5,5,9,3,3,7] := by
  refine ⟨plan7063,valid7063,t6_1283choices,?_⟩
  exact check_of_frontier tree 0 t6_1283root t6_1283jobs t6_1283frontier t6_1283all
theorem t6_1284choices : plan7064.choices=[5,5,9,3,3,10].map (options 6 4) := by rfl


theorem t6_1284part0 : t6_1284jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1284frontier : t6_1284root.frontier 0=t6_1284jobs := by rfl
theorem t6_1284all : t6_1284jobs.all (Job.check tree)=true := by
  simp only [t6_1284jobs,List.all_append,List.all_nil,t6_1284part0,Bool.and_self]
theorem t6_1284checked : Checked tree [5,5,9,3,3,10] := by
  refine ⟨plan7064,valid7064,t6_1284choices,?_⟩
  exact check_of_frontier tree 0 t6_1284root t6_1284jobs t6_1284frontier t6_1284all
theorem t6_1285choices : plan7563.choices=[5,5,9,3,6,6].map (options 6 5) := by rfl


theorem t6_1285part0 : t6_1285jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1285frontier : t6_1285root.frontier 0=t6_1285jobs := by rfl
theorem t6_1285all : t6_1285jobs.all (Job.check tree)=true := by
  simp only [t6_1285jobs,List.all_append,List.all_nil,t6_1285part0,Bool.and_self]
theorem t6_1285checked : Checked tree [5,5,9,3,6,6] := by
  refine ⟨plan7563,valid7563,t6_1285choices,?_⟩
  exact check_of_frontier tree 0 t6_1285root t6_1285jobs t6_1285frontier t6_1285all
theorem t6_1286choices : plan7564.choices=[5,5,9,3,6,7].map (options 6 5) := by rfl


theorem t6_1286part0 : t6_1286jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1286frontier : t6_1286root.frontier 0=t6_1286jobs := by rfl
theorem t6_1286all : t6_1286jobs.all (Job.check tree)=true := by
  simp only [t6_1286jobs,List.all_append,List.all_nil,t6_1286part0,Bool.and_self]
theorem t6_1286checked : Checked tree [5,5,9,3,6,7] := by
  refine ⟨plan7564,valid7564,t6_1286choices,?_⟩
  exact check_of_frontier tree 0 t6_1286root t6_1286jobs t6_1286frontier t6_1286all
theorem t6_1287choices : plan7565.choices=[5,5,9,3,6,10].map (options 6 5) := by rfl


theorem t6_1287part0 : t6_1287jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1287frontier : t6_1287root.frontier 0=t6_1287jobs := by rfl
theorem t6_1287all : t6_1287jobs.all (Job.check tree)=true := by
  simp only [t6_1287jobs,List.all_append,List.all_nil,t6_1287part0,Bool.and_self]
theorem t6_1287checked : Checked tree [5,5,9,3,6,10] := by
  refine ⟨plan7565,valid7565,t6_1287choices,?_⟩
  exact check_of_frontier tree 0 t6_1287root t6_1287jobs t6_1287frontier t6_1287all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks133 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1244checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1245checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1246checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1247checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1248checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1249checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1250checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1251checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1235checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1252checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1253checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1254checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1255checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1256checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1257checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1258checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1259checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1260checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1261checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1262checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1263checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1264checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1265checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1266checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1236checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1267checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1268checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1269checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1270checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1271checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1272checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1273checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1274checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1275checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1276checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1237checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1277checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1278checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1279checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1280checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1281checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1282checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1283checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1284checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1285checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1286checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1287checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1238checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1239checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1240checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1241checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1242checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1243checked⟩
