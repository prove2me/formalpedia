-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks137
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:51:38.692692+00:00
-- url     : https://prove2.me/submissions/e25730d2-95d7-43c3-8143-be50a86767c1

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks137
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks137
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans081
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























theorem valid1600 : plan1600.Valid := valid_step _ _ _ valid574 (by decide +kernel)









theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1606 : plan1606.Valid := valid_step _ _ _ valid580 (by decide +kernel)







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



































































































theorem valid3410 : plan3410.Valid := valid_step _ _ _ valid1556 (by decide +kernel)

theorem valid3411 : plan3411.Valid := valid_step _ _ _ valid1557 (by decide +kernel)

theorem valid3412 : plan3412.Valid := valid_step _ _ _ valid1558 (by decide +kernel)







































































theorem valid3448 : plan3448.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3449 : plan3449.Valid := valid_step _ _ _ valid1606 (by decide +kernel)














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























































































































theorem valid5532 : plan5532.Valid := valid_step _ _ _ valid3334 (by decide +kernel)








































































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



































































theorem valid6658 : plan6658.Valid := valid_step _ _ _ valid5532 (by decide +kernel)




























































































































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





























































theorem valid3487 : plan3487.Valid := valid_step _ _ _ valid1583 (by decide +kernel)

theorem valid3488 : plan3488.Valid := valid_step _ _ _ valid1584 (by decide +kernel)

theorem valid3489 : plan3489.Valid := valid_step _ _ _ valid1585 (by decide +kernel)

theorem valid3490 : plan3490.Valid := valid_step _ _ _ valid1586 (by decide +kernel)

theorem valid3491 : plan3491.Valid := valid_step _ _ _ valid1587 (by decide +kernel)

theorem valid3492 : plan3492.Valid := valid_step _ _ _ valid1588 (by decide +kernel)















theorem valid3500 : plan3500.Valid := valid_step _ _ _ valid1600 (by decide +kernel)























































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



theorem valid3540 : plan3540.Valid := valid_step _ _ _ valid1610 (by decide +kernel)

theorem valid3541 : plan3541.Valid := valid_step _ _ _ valid1611 (by decide +kernel)

theorem valid3542 : plan3542.Valid := valid_step _ _ _ valid1612 (by decide +kernel)

theorem valid3543 : plan3543.Valid := valid_step _ _ _ valid1613 (by decide +kernel)

theorem valid3544 : plan3544.Valid := valid_step _ _ _ valid1614 (by decide +kernel)

theorem valid3545 : plan3545.Valid := valid_step _ _ _ valid1615 (by decide +kernel)

theorem valid3546 : plan3546.Valid := valid_step _ _ _ valid1616 (by decide +kernel)

theorem valid3547 : plan3547.Valid := valid_step _ _ _ valid1617 (by decide +kernel)

theorem valid3548 : plan3548.Valid := valid_step _ _ _ valid1618 (by decide +kernel)

theorem valid3549 : plan3549.Valid := valid_step _ _ _ valid1619 (by decide +kernel)

theorem valid3550 : plan3550.Valid := valid_step _ _ _ valid1620 (by decide +kernel)

theorem valid3551 : plan3551.Valid := valid_step _ _ _ valid1621 (by decide +kernel)

theorem valid3552 : plan3552.Valid := valid_step _ _ _ valid1622 (by decide +kernel)
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



































































































































theorem valid5730 : plan5730.Valid := valid_step _ _ _ valid3410 (by decide +kernel)

theorem valid5731 : plan5731.Valid := valid_step _ _ _ valid3411 (by decide +kernel)

theorem valid5732 : plan5732.Valid := valid_step _ _ _ valid3412 (by decide +kernel)
























































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





























































































































































theorem valid5935 : plan5935.Valid := valid_step _ _ _ valid3448 (by decide +kernel)

theorem valid5936 : plan5936.Valid := valid_step _ _ _ valid3449 (by decide +kernel)























theorem valid5948 : plan5948.Valid := valid_step _ _ _ valid3487 (by decide +kernel)

theorem valid5949 : plan5949.Valid := valid_step _ _ _ valid3488 (by decide +kernel)

theorem valid5950 : plan5950.Valid := valid_step _ _ _ valid3489 (by decide +kernel)

theorem valid5951 : plan5951.Valid := valid_step _ _ _ valid3490 (by decide +kernel)

theorem valid5952 : plan5952.Valid := valid_step _ _ _ valid3491 (by decide +kernel)
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

theorem valid5953 : plan5953.Valid := valid_step _ _ _ valid3492 (by decide +kernel)















theorem valid5961 : plan5961.Valid := valid_step _ _ _ valid3500 (by decide +kernel)



























































































































































theorem valid6039 : plan6039.Valid := valid_step _ _ _ valid3528 (by decide +kernel)

theorem valid6040 : plan6040.Valid := valid_step _ _ _ valid3529 (by decide +kernel)

theorem valid6041 : plan6041.Valid := valid_step _ _ _ valid3530 (by decide +kernel)

theorem valid6042 : plan6042.Valid := valid_step _ _ _ valid3531 (by decide +kernel)

theorem valid6043 : plan6043.Valid := valid_step _ _ _ valid3532 (by decide +kernel)

theorem valid6044 : plan6044.Valid := valid_step _ _ _ valid3533 (by decide +kernel)

theorem valid6045 : plan6045.Valid := valid_step _ _ _ valid3534 (by decide +kernel)

theorem valid6046 : plan6046.Valid := valid_step _ _ _ valid3535 (by decide +kernel)

theorem valid6047 : plan6047.Valid := valid_step _ _ _ valid3536 (by decide +kernel)

theorem valid6048 : plan6048.Valid := valid_step _ _ _ valid3537 (by decide +kernel)
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





























































































































theorem valid7071 : plan7071.Valid := valid_step _ _ _ valid5730 (by decide +kernel)

theorem valid7072 : plan7072.Valid := valid_step _ _ _ valid5731 (by decide +kernel)

theorem valid7073 : plan7073.Valid := valid_step _ _ _ valid5732 (by decide +kernel)






























































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



















































































































































































theorem valid7578 : plan7578.Valid := valid_step _ _ _ valid5935 (by decide +kernel)

theorem valid7579 : plan7579.Valid := valid_step _ _ _ valid5936 (by decide +kernel)

theorem valid7580 : plan7580.Valid := valid_step _ _ _ valid5948 (by decide +kernel)

theorem valid7581 : plan7581.Valid := valid_step _ _ _ valid5949 (by decide +kernel)

theorem valid7582 : plan7582.Valid := valid_step _ _ _ valid5950 (by decide +kernel)

theorem valid7583 : plan7583.Valid := valid_step _ _ _ valid5951 (by decide +kernel)

theorem valid7584 : plan7584.Valid := valid_step _ _ _ valid5952 (by decide +kernel)
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

theorem valid6049 : plan6049.Valid := valid_step _ _ _ valid3538 (by decide +kernel)

theorem valid6050 : plan6050.Valid := valid_step _ _ _ valid3553 (by decide +kernel)

theorem valid6051 : plan6051.Valid := valid_step _ _ _ valid3554 (by decide +kernel)

theorem valid6052 : plan6052.Valid := valid_step _ _ _ valid3555 (by decide +kernel)

theorem valid6053 : plan6053.Valid := valid_step _ _ _ valid3556 (by decide +kernel)

theorem valid6054 : plan6054.Valid := valid_step _ _ _ valid3538 (by decide +kernel)



































theorem valid6072 : plan6072.Valid := valid_step _ _ _ valid3528 (by decide +kernel)

theorem valid6073 : plan6073.Valid := valid_step _ _ _ valid3529 (by decide +kernel)

theorem valid6074 : plan6074.Valid := valid_step _ _ _ valid3530 (by decide +kernel)

theorem valid6075 : plan6075.Valid := valid_step _ _ _ valid3531 (by decide +kernel)

theorem valid6076 : plan6076.Valid := valid_step _ _ _ valid3532 (by decide +kernel)

theorem valid6077 : plan6077.Valid := valid_step _ _ _ valid3533 (by decide +kernel)

theorem valid6078 : plan6078.Valid := valid_step _ _ _ valid3534 (by decide +kernel)

theorem valid6079 : plan6079.Valid := valid_step _ _ _ valid3535 (by decide +kernel)

theorem valid6080 : plan6080.Valid := valid_step _ _ _ valid3536 (by decide +kernel)

theorem valid6081 : plan6081.Valid := valid_step _ _ _ valid3537 (by decide +kernel)

theorem valid6082 : plan6082.Valid := valid_step _ _ _ valid3538 (by decide +kernel)

theorem valid6083 : plan6083.Valid := valid_step _ _ _ valid3540 (by decide +kernel)

theorem valid6084 : plan6084.Valid := valid_step _ _ _ valid3541 (by decide +kernel)

theorem valid6085 : plan6085.Valid := valid_step _ _ _ valid3542 (by decide +kernel)

theorem valid6086 : plan6086.Valid := valid_step _ _ _ valid3543 (by decide +kernel)

theorem valid6087 : plan6087.Valid := valid_step _ _ _ valid3544 (by decide +kernel)

theorem valid6088 : plan6088.Valid := valid_step _ _ _ valid3545 (by decide +kernel)

theorem valid6089 : plan6089.Valid := valid_step _ _ _ valid3546 (by decide +kernel)

theorem valid6090 : plan6090.Valid := valid_step _ _ _ valid3547 (by decide +kernel)

theorem valid6091 : plan6091.Valid := valid_step _ _ _ valid3548 (by decide +kernel)

theorem valid6092 : plan6092.Valid := valid_step _ _ _ valid3549 (by decide +kernel)

theorem valid6093 : plan6093.Valid := valid_step _ _ _ valid3550 (by decide +kernel)

theorem valid6094 : plan6094.Valid := valid_step _ _ _ valid3551 (by decide +kernel)

theorem valid6095 : plan6095.Valid := valid_step _ _ _ valid3552 (by decide +kernel)

theorem valid6096 : plan6096.Valid := valid_step _ _ _ valid3553 (by decide +kernel)

theorem valid6097 : plan6097.Valid := valid_step _ _ _ valid3554 (by decide +kernel)

theorem valid6098 : plan6098.Valid := valid_step _ _ _ valid3555 (by decide +kernel)

theorem valid6099 : plan6099.Valid := valid_step _ _ _ valid3556 (by decide +kernel)

theorem valid6100 : plan6100.Valid := valid_step _ _ _ valid3538 (by decide +kernel)

theorem valid6101 : plan6101.Valid := valid_step _ _ _ valid3553 (by decide +kernel)

theorem valid6102 : plan6102.Valid := valid_step _ _ _ valid3554 (by decide +kernel)

theorem valid6103 : plan6103.Valid := valid_step _ _ _ valid3555 (by decide +kernel)

theorem valid6104 : plan6104.Valid := valid_step _ _ _ valid3556 (by decide +kernel)
















































































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































































































































































































theorem valid7872 : plan7872.Valid := valid_step _ _ _ valid6072 (by decide +kernel)
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

theorem valid7585 : plan7585.Valid := valid_step _ _ _ valid5953 (by decide +kernel)

theorem valid7586 : plan7586.Valid := valid_step _ _ _ valid5961 (by decide +kernel)




























































































































































































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

theorem valid7873 : plan7873.Valid := valid_step _ _ _ valid6073 (by decide +kernel)

theorem valid7874 : plan7874.Valid := valid_step _ _ _ valid6074 (by decide +kernel)

theorem valid7875 : plan7875.Valid := valid_step _ _ _ valid6075 (by decide +kernel)

theorem valid7876 : plan7876.Valid := valid_step _ _ _ valid6076 (by decide +kernel)

theorem valid7877 : plan7877.Valid := valid_step _ _ _ valid6077 (by decide +kernel)

theorem valid7878 : plan7878.Valid := valid_step _ _ _ valid6078 (by decide +kernel)

theorem valid7879 : plan7879.Valid := valid_step _ _ _ valid6079 (by decide +kernel)

theorem valid7880 : plan7880.Valid := valid_step _ _ _ valid6080 (by decide +kernel)

theorem valid7881 : plan7881.Valid := valid_step _ _ _ valid6081 (by decide +kernel)

theorem valid7882 : plan7882.Valid := valid_step _ _ _ valid6082 (by decide +kernel)

theorem valid7883 : plan7883.Valid := valid_step _ _ _ valid6083 (by decide +kernel)

theorem valid7884 : plan7884.Valid := valid_step _ _ _ valid6084 (by decide +kernel)

theorem valid7885 : plan7885.Valid := valid_step _ _ _ valid6085 (by decide +kernel)

theorem valid7886 : plan7886.Valid := valid_step _ _ _ valid6086 (by decide +kernel)

theorem valid7887 : plan7887.Valid := valid_step _ _ _ valid6087 (by decide +kernel)

theorem valid7888 : plan7888.Valid := valid_step _ _ _ valid6088 (by decide +kernel)

theorem valid7889 : plan7889.Valid := valid_step _ _ _ valid6089 (by decide +kernel)

theorem valid7890 : plan7890.Valid := valid_step _ _ _ valid6090 (by decide +kernel)

theorem valid7891 : plan7891.Valid := valid_step _ _ _ valid6091 (by decide +kernel)

theorem valid7892 : plan7892.Valid := valid_step _ _ _ valid6092 (by decide +kernel)

theorem valid7893 : plan7893.Valid := valid_step _ _ _ valid6093 (by decide +kernel)

theorem valid7894 : plan7894.Valid := valid_step _ _ _ valid6094 (by decide +kernel)

theorem valid7895 : plan7895.Valid := valid_step _ _ _ valid6095 (by decide +kernel)

theorem valid7896 : plan7896.Valid := valid_step _ _ _ valid6096 (by decide +kernel)

theorem valid7897 : plan7897.Valid := valid_step _ _ _ valid6097 (by decide +kernel)

theorem valid7898 : plan7898.Valid := valid_step _ _ _ valid6098 (by decide +kernel)

theorem valid7899 : plan7899.Valid := valid_step _ _ _ valid6099 (by decide +kernel)

theorem valid7900 : plan7900.Valid := valid_step _ _ _ valid6100 (by decide +kernel)

theorem valid7901 : plan7901.Valid := valid_step _ _ _ valid6101 (by decide +kernel)

theorem valid7902 : plan7902.Valid := valid_step _ _ _ valid6102 (by decide +kernel)

theorem valid7903 : plan7903.Valid := valid_step _ _ _ valid6103 (by decide +kernel)

theorem valid7904 : plan7904.Valid := valid_step _ _ _ valid6104 (by decide +kernel)

theorem valid7905 : plan7905.Valid := valid_step _ _ _ valid6039 (by decide +kernel)

theorem valid7906 : plan7906.Valid := valid_step _ _ _ valid6040 (by decide +kernel)

theorem valid7907 : plan7907.Valid := valid_step _ _ _ valid6041 (by decide +kernel)

theorem valid7908 : plan7908.Valid := valid_step _ _ _ valid6042 (by decide +kernel)

theorem valid7909 : plan7909.Valid := valid_step _ _ _ valid6043 (by decide +kernel)

theorem valid7910 : plan7910.Valid := valid_step _ _ _ valid6044 (by decide +kernel)

theorem valid7911 : plan7911.Valid := valid_step _ _ _ valid6045 (by decide +kernel)

theorem valid7912 : plan7912.Valid := valid_step _ _ _ valid6046 (by decide +kernel)

theorem valid7913 : plan7913.Valid := valid_step _ _ _ valid6047 (by decide +kernel)

theorem valid7914 : plan7914.Valid := valid_step _ _ _ valid6048 (by decide +kernel)

theorem valid7915 : plan7915.Valid := valid_step _ _ _ valid6049 (by decide +kernel)

theorem valid7916 : plan7916.Valid := valid_step _ _ _ valid6050 (by decide +kernel)

theorem valid7917 : plan7917.Valid := valid_step _ _ _ valid6051 (by decide +kernel)

theorem valid7918 : plan7918.Valid := valid_step _ _ _ valid6052 (by decide +kernel)

theorem valid7919 : plan7919.Valid := valid_step _ _ _ valid6053 (by decide +kernel)

theorem valid7920 : plan7920.Valid := valid_step _ _ _ valid6054 (by decide +kernel)

theorem valid7921 : plan7921.Valid := valid_step _ _ _ valid6100 (by decide +kernel)






























































































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
theorem t6_1343choices : plan7578.choices=[5,9,3,10,10,7].map (options 6 5) := by rfl


theorem t6_1343part0 : t6_1343jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1343part1 : t6_1343jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1343part2 : t6_1343jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1343frontier : t6_1343root.frontier 1=t6_1343jobs := by rfl
theorem t6_1343all : t6_1343jobs.all (Job.check tree)=true := by
  simp only [t6_1343jobs,List.all_append,List.all_nil,t6_1343part0,t6_1343part1,t6_1343part2,Bool.and_self]
theorem t6_1343checked : Checked tree [5,9,3,10,10,7] := by
  refine ⟨plan7578,valid7578,t6_1343choices,?_⟩
  exact check_of_frontier tree 1 t6_1343root t6_1343jobs t6_1343frontier t6_1343all
theorem t6_1344choices : plan7579.choices=[5,9,3,10,10,10].map (options 6 5) := by rfl


theorem t6_1344part0 : t6_1344jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1344frontier : t6_1344root.frontier 0=t6_1344jobs := by rfl
theorem t6_1344all : t6_1344jobs.all (Job.check tree)=true := by
  simp only [t6_1344jobs,List.all_append,List.all_nil,t6_1344part0,Bool.and_self]
theorem t6_1344checked : Checked tree [5,9,3,10,10,10] := by
  refine ⟨plan7579,valid7579,t6_1344choices,?_⟩
  exact check_of_frontier tree 0 t6_1344root t6_1344jobs t6_1344frontier t6_1344all
theorem t6_1345choices : plan7872.choices=[5,9,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1345part0 : t6_1345jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1345frontier : t6_1345root.frontier 0=t6_1345jobs := by rfl
theorem t6_1345all : t6_1345jobs.all (Job.check tree)=true := by
  simp only [t6_1345jobs,List.all_append,List.all_nil,t6_1345part0,Bool.and_self]
theorem t6_1345checked : Checked tree [5,9,6,6,6,6] := by
  refine ⟨plan7872,valid7872,t6_1345choices,?_⟩
  exact check_of_frontier tree 0 t6_1345root t6_1345jobs t6_1345frontier t6_1345all
theorem t6_1346choices : plan7873.choices=[5,9,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1346part0 : t6_1346jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1346frontier : t6_1346root.frontier 0=t6_1346jobs := by rfl
theorem t6_1346all : t6_1346jobs.all (Job.check tree)=true := by
  simp only [t6_1346jobs,List.all_append,List.all_nil,t6_1346part0,Bool.and_self]
theorem t6_1346checked : Checked tree [5,9,6,6,6,7] := by
  refine ⟨plan7873,valid7873,t6_1346choices,?_⟩
  exact check_of_frontier tree 0 t6_1346root t6_1346jobs t6_1346frontier t6_1346all
theorem t6_1347choices : plan7874.choices=[5,9,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1347part0 : t6_1347jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1347frontier : t6_1347root.frontier 0=t6_1347jobs := by rfl
theorem t6_1347all : t6_1347jobs.all (Job.check tree)=true := by
  simp only [t6_1347jobs,List.all_append,List.all_nil,t6_1347part0,Bool.and_self]
theorem t6_1347checked : Checked tree [5,9,6,6,6,10] := by
  refine ⟨plan7874,valid7874,t6_1347choices,?_⟩
  exact check_of_frontier tree 0 t6_1347root t6_1347jobs t6_1347frontier t6_1347all
theorem t6_1348choices : plan7875.choices=[5,9,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1348part0 : t6_1348jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1348frontier : t6_1348root.frontier 0=t6_1348jobs := by rfl
theorem t6_1348all : t6_1348jobs.all (Job.check tree)=true := by
  simp only [t6_1348jobs,List.all_append,List.all_nil,t6_1348part0,Bool.and_self]
theorem t6_1348checked : Checked tree [5,9,6,6,7,7] := by
  refine ⟨plan7875,valid7875,t6_1348choices,?_⟩
  exact check_of_frontier tree 0 t6_1348root t6_1348jobs t6_1348frontier t6_1348all
theorem t6_1349choices : plan7876.choices=[5,9,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1349part0 : t6_1349jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1349frontier : t6_1349root.frontier 0=t6_1349jobs := by rfl
theorem t6_1349all : t6_1349jobs.all (Job.check tree)=true := by
  simp only [t6_1349jobs,List.all_append,List.all_nil,t6_1349part0,Bool.and_self]
theorem t6_1349checked : Checked tree [5,9,6,6,10,7] := by
  refine ⟨plan7876,valid7876,t6_1349choices,?_⟩
  exact check_of_frontier tree 0 t6_1349root t6_1349jobs t6_1349frontier t6_1349all
theorem t6_1350choices : plan7877.choices=[5,9,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1350part0 : t6_1350jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1350frontier : t6_1350root.frontier 0=t6_1350jobs := by rfl
theorem t6_1350all : t6_1350jobs.all (Job.check tree)=true := by
  simp only [t6_1350jobs,List.all_append,List.all_nil,t6_1350part0,Bool.and_self]
theorem t6_1350checked : Checked tree [5,9,6,6,10,10] := by
  refine ⟨plan7877,valid7877,t6_1350choices,?_⟩
  exact check_of_frontier tree 0 t6_1350root t6_1350jobs t6_1350frontier t6_1350all
theorem t6_1351choices : plan7878.choices=[5,9,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1351part0 : t6_1351jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1351frontier : t6_1351root.frontier 0=t6_1351jobs := by rfl
theorem t6_1351all : t6_1351jobs.all (Job.check tree)=true := by
  simp only [t6_1351jobs,List.all_append,List.all_nil,t6_1351part0,Bool.and_self]
theorem t6_1351checked : Checked tree [5,9,6,7,7,7] := by
  refine ⟨plan7878,valid7878,t6_1351choices,?_⟩
  exact check_of_frontier tree 0 t6_1351root t6_1351jobs t6_1351frontier t6_1351all
theorem t6_1352choices : plan7879.choices=[5,9,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1352part0 : t6_1352jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1352frontier : t6_1352root.frontier 0=t6_1352jobs := by rfl
theorem t6_1352all : t6_1352jobs.all (Job.check tree)=true := by
  simp only [t6_1352jobs,List.all_append,List.all_nil,t6_1352part0,Bool.and_self]
theorem t6_1352checked : Checked tree [5,9,6,10,7,7] := by
  refine ⟨plan7879,valid7879,t6_1352choices,?_⟩
  exact check_of_frontier tree 0 t6_1352root t6_1352jobs t6_1352frontier t6_1352all
theorem t6_1353choices : plan7880.choices=[5,9,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1353part0 : t6_1353jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1353frontier : t6_1353root.frontier 0=t6_1353jobs := by rfl
theorem t6_1353all : t6_1353jobs.all (Job.check tree)=true := by
  simp only [t6_1353jobs,List.all_append,List.all_nil,t6_1353part0,Bool.and_self]
theorem t6_1353checked : Checked tree [5,9,6,10,10,7] := by
  refine ⟨plan7880,valid7880,t6_1353choices,?_⟩
  exact check_of_frontier tree 0 t6_1353root t6_1353jobs t6_1353frontier t6_1353all
theorem t6_1354choices : plan7881.choices=[5,9,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1354part0 : t6_1354jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1354frontier : t6_1354root.frontier 0=t6_1354jobs := by rfl
theorem t6_1354all : t6_1354jobs.all (Job.check tree)=true := by
  simp only [t6_1354jobs,List.all_append,List.all_nil,t6_1354part0,Bool.and_self]
theorem t6_1354checked : Checked tree [5,9,6,10,10,10] := by
  refine ⟨plan7881,valid7881,t6_1354choices,?_⟩
  exact check_of_frontier tree 0 t6_1354root t6_1354jobs t6_1354frontier t6_1354all
theorem t6_1355choices : plan7882.choices=[5,9,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1355part0 : t6_1355jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1355frontier : t6_1355root.frontier 0=t6_1355jobs := by rfl
theorem t6_1355all : t6_1355jobs.all (Job.check tree)=true := by
  simp only [t6_1355jobs,List.all_append,List.all_nil,t6_1355part0,Bool.and_self]
theorem t6_1355checked : Checked tree [5,9,7,7,7,7] := by
  refine ⟨plan7882,valid7882,t6_1355choices,?_⟩
  exact check_of_frontier tree 0 t6_1355root t6_1355jobs t6_1355frontier t6_1355all
theorem t6_1356choices : plan6658.choices=[5,9,9,3,3,3].map (options 6 3) := by rfl


theorem t6_1356part0 : t6_1356jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1356frontier : t6_1356root.frontier 0=t6_1356jobs := by rfl
theorem t6_1356all : t6_1356jobs.all (Job.check tree)=true := by
  simp only [t6_1356jobs,List.all_append,List.all_nil,t6_1356part0,Bool.and_self]
theorem t6_1356checked : Checked tree [5,9,9,3,3,3] := by
  refine ⟨plan6658,valid6658,t6_1356choices,?_⟩
  exact check_of_frontier tree 0 t6_1356root t6_1356jobs t6_1356frontier t6_1356all
theorem t6_1357choices : plan7071.choices=[5,9,9,3,3,6].map (options 6 4) := by rfl


theorem t6_1357part0 : t6_1357jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1357frontier : t6_1357root.frontier 0=t6_1357jobs := by rfl
theorem t6_1357all : t6_1357jobs.all (Job.check tree)=true := by
  simp only [t6_1357jobs,List.all_append,List.all_nil,t6_1357part0,Bool.and_self]
theorem t6_1357checked : Checked tree [5,9,9,3,3,6] := by
  refine ⟨plan7071,valid7071,t6_1357choices,?_⟩
  exact check_of_frontier tree 0 t6_1357root t6_1357jobs t6_1357frontier t6_1357all
theorem t6_1358choices : plan7072.choices=[5,9,9,3,3,7].map (options 6 4) := by rfl


theorem t6_1358part0 : t6_1358jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1358frontier : t6_1358root.frontier 0=t6_1358jobs := by rfl
theorem t6_1358all : t6_1358jobs.all (Job.check tree)=true := by
  simp only [t6_1358jobs,List.all_append,List.all_nil,t6_1358part0,Bool.and_self]
theorem t6_1358checked : Checked tree [5,9,9,3,3,7] := by
  refine ⟨plan7072,valid7072,t6_1358choices,?_⟩
  exact check_of_frontier tree 0 t6_1358root t6_1358jobs t6_1358frontier t6_1358all
theorem t6_1359choices : plan7073.choices=[5,9,9,3,3,10].map (options 6 4) := by rfl


theorem t6_1359part0 : t6_1359jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1359frontier : t6_1359root.frontier 0=t6_1359jobs := by rfl
theorem t6_1359all : t6_1359jobs.all (Job.check tree)=true := by
  simp only [t6_1359jobs,List.all_append,List.all_nil,t6_1359part0,Bool.and_self]
theorem t6_1359checked : Checked tree [5,9,9,3,3,10] := by
  refine ⟨plan7073,valid7073,t6_1359choices,?_⟩
  exact check_of_frontier tree 0 t6_1359root t6_1359jobs t6_1359frontier t6_1359all
theorem t6_1360choices : plan7580.choices=[5,9,9,3,6,6].map (options 6 5) := by rfl


theorem t6_1360part0 : t6_1360jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1360frontier : t6_1360root.frontier 0=t6_1360jobs := by rfl
theorem t6_1360all : t6_1360jobs.all (Job.check tree)=true := by
  simp only [t6_1360jobs,List.all_append,List.all_nil,t6_1360part0,Bool.and_self]
theorem t6_1360checked : Checked tree [5,9,9,3,6,6] := by
  refine ⟨plan7580,valid7580,t6_1360choices,?_⟩
  exact check_of_frontier tree 0 t6_1360root t6_1360jobs t6_1360frontier t6_1360all
theorem t6_1361choices : plan7581.choices=[5,9,9,3,6,7].map (options 6 5) := by rfl


theorem t6_1361part0 : t6_1361jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1361frontier : t6_1361root.frontier 0=t6_1361jobs := by rfl
theorem t6_1361all : t6_1361jobs.all (Job.check tree)=true := by
  simp only [t6_1361jobs,List.all_append,List.all_nil,t6_1361part0,Bool.and_self]
theorem t6_1361checked : Checked tree [5,9,9,3,6,7] := by
  refine ⟨plan7581,valid7581,t6_1361choices,?_⟩
  exact check_of_frontier tree 0 t6_1361root t6_1361jobs t6_1361frontier t6_1361all
theorem t6_1362choices : plan7582.choices=[5,9,9,3,6,10].map (options 6 5) := by rfl


theorem t6_1362part0 : t6_1362jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1362frontier : t6_1362root.frontier 0=t6_1362jobs := by rfl
theorem t6_1362all : t6_1362jobs.all (Job.check tree)=true := by
  simp only [t6_1362jobs,List.all_append,List.all_nil,t6_1362part0,Bool.and_self]
theorem t6_1362checked : Checked tree [5,9,9,3,6,10] := by
  refine ⟨plan7582,valid7582,t6_1362choices,?_⟩
  exact check_of_frontier tree 0 t6_1362root t6_1362jobs t6_1362frontier t6_1362all
theorem t6_1363choices : plan7583.choices=[5,9,9,3,7,7].map (options 6 5) := by rfl


theorem t6_1363part0 : t6_1363jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1363part1 : t6_1363jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1363frontier : t6_1363root.frontier 1=t6_1363jobs := by rfl
theorem t6_1363all : t6_1363jobs.all (Job.check tree)=true := by
  simp only [t6_1363jobs,List.all_append,List.all_nil,t6_1363part0,t6_1363part1,Bool.and_self]
theorem t6_1363checked : Checked tree [5,9,9,3,7,7] := by
  refine ⟨plan7583,valid7583,t6_1363choices,?_⟩
  exact check_of_frontier tree 1 t6_1363root t6_1363jobs t6_1363frontier t6_1363all
theorem t6_1364choices : plan7584.choices=[5,9,9,3,10,7].map (options 6 5) := by rfl


theorem t6_1364part0 : t6_1364jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1364frontier : t6_1364root.frontier 0=t6_1364jobs := by rfl
theorem t6_1364all : t6_1364jobs.all (Job.check tree)=true := by
  simp only [t6_1364jobs,List.all_append,List.all_nil,t6_1364part0,Bool.and_self]
theorem t6_1364checked : Checked tree [5,9,9,3,10,7] := by
  refine ⟨plan7584,valid7584,t6_1364choices,?_⟩
  exact check_of_frontier tree 0 t6_1364root t6_1364jobs t6_1364frontier t6_1364all
theorem t6_1365choices : plan7585.choices=[5,9,9,3,10,10].map (options 6 5) := by rfl


theorem t6_1365part0 : t6_1365jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1365frontier : t6_1365root.frontier 0=t6_1365jobs := by rfl
theorem t6_1365all : t6_1365jobs.all (Job.check tree)=true := by
  simp only [t6_1365jobs,List.all_append,List.all_nil,t6_1365part0,Bool.and_self]
theorem t6_1365checked : Checked tree [5,9,9,3,10,10] := by
  refine ⟨plan7585,valid7585,t6_1365choices,?_⟩
  exact check_of_frontier tree 0 t6_1365root t6_1365jobs t6_1365frontier t6_1365all
theorem t6_1366choices : plan7883.choices=[5,9,9,6,6,6].map (options 6 6) := by rfl


theorem t6_1366part0 : t6_1366jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1366frontier : t6_1366root.frontier 0=t6_1366jobs := by rfl
theorem t6_1366all : t6_1366jobs.all (Job.check tree)=true := by
  simp only [t6_1366jobs,List.all_append,List.all_nil,t6_1366part0,Bool.and_self]
theorem t6_1366checked : Checked tree [5,9,9,6,6,6] := by
  refine ⟨plan7883,valid7883,t6_1366choices,?_⟩
  exact check_of_frontier tree 0 t6_1366root t6_1366jobs t6_1366frontier t6_1366all
theorem t6_1367choices : plan7884.choices=[5,9,9,6,6,7].map (options 6 6) := by rfl


theorem t6_1367part0 : t6_1367jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1367frontier : t6_1367root.frontier 0=t6_1367jobs := by rfl
theorem t6_1367all : t6_1367jobs.all (Job.check tree)=true := by
  simp only [t6_1367jobs,List.all_append,List.all_nil,t6_1367part0,Bool.and_self]
theorem t6_1367checked : Checked tree [5,9,9,6,6,7] := by
  refine ⟨plan7884,valid7884,t6_1367choices,?_⟩
  exact check_of_frontier tree 0 t6_1367root t6_1367jobs t6_1367frontier t6_1367all
theorem t6_1368choices : plan7885.choices=[5,9,9,6,6,10].map (options 6 6) := by rfl


theorem t6_1368part0 : t6_1368jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1368frontier : t6_1368root.frontier 0=t6_1368jobs := by rfl
theorem t6_1368all : t6_1368jobs.all (Job.check tree)=true := by
  simp only [t6_1368jobs,List.all_append,List.all_nil,t6_1368part0,Bool.and_self]
theorem t6_1368checked : Checked tree [5,9,9,6,6,10] := by
  refine ⟨plan7885,valid7885,t6_1368choices,?_⟩
  exact check_of_frontier tree 0 t6_1368root t6_1368jobs t6_1368frontier t6_1368all
theorem t6_1369choices : plan7886.choices=[5,9,9,6,7,7].map (options 6 6) := by rfl


theorem t6_1369part0 : t6_1369jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1369frontier : t6_1369root.frontier 0=t6_1369jobs := by rfl
theorem t6_1369all : t6_1369jobs.all (Job.check tree)=true := by
  simp only [t6_1369jobs,List.all_append,List.all_nil,t6_1369part0,Bool.and_self]
theorem t6_1369checked : Checked tree [5,9,9,6,7,7] := by
  refine ⟨plan7886,valid7886,t6_1369choices,?_⟩
  exact check_of_frontier tree 0 t6_1369root t6_1369jobs t6_1369frontier t6_1369all
theorem t6_1370choices : plan7887.choices=[5,9,9,6,10,7].map (options 6 6) := by rfl


theorem t6_1370part0 : t6_1370jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1370frontier : t6_1370root.frontier 0=t6_1370jobs := by rfl
theorem t6_1370all : t6_1370jobs.all (Job.check tree)=true := by
  simp only [t6_1370jobs,List.all_append,List.all_nil,t6_1370part0,Bool.and_self]
theorem t6_1370checked : Checked tree [5,9,9,6,10,7] := by
  refine ⟨plan7887,valid7887,t6_1370choices,?_⟩
  exact check_of_frontier tree 0 t6_1370root t6_1370jobs t6_1370frontier t6_1370all
theorem t6_1371choices : plan7888.choices=[5,9,9,6,10,10].map (options 6 6) := by rfl


theorem t6_1371part0 : t6_1371jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1371frontier : t6_1371root.frontier 0=t6_1371jobs := by rfl
theorem t6_1371all : t6_1371jobs.all (Job.check tree)=true := by
  simp only [t6_1371jobs,List.all_append,List.all_nil,t6_1371part0,Bool.and_self]
theorem t6_1371checked : Checked tree [5,9,9,6,10,10] := by
  refine ⟨plan7888,valid7888,t6_1371choices,?_⟩
  exact check_of_frontier tree 0 t6_1371root t6_1371jobs t6_1371frontier t6_1371all
theorem t6_1372choices : plan7889.choices=[5,9,9,7,7,7].map (options 6 6) := by rfl


theorem t6_1372part0 : t6_1372jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1372frontier : t6_1372root.frontier 0=t6_1372jobs := by rfl
theorem t6_1372all : t6_1372jobs.all (Job.check tree)=true := by
  simp only [t6_1372jobs,List.all_append,List.all_nil,t6_1372part0,Bool.and_self]
theorem t6_1372checked : Checked tree [5,9,9,7,7,7] := by
  refine ⟨plan7889,valid7889,t6_1372choices,?_⟩
  exact check_of_frontier tree 0 t6_1372root t6_1372jobs t6_1372frontier t6_1372all
theorem t6_1373choices : plan7586.choices=[5,9,9,9,3,7].map (options 6 5) := by rfl


theorem t6_1373part0 : t6_1373jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1373frontier : t6_1373root.frontier 0=t6_1373jobs := by rfl
theorem t6_1373all : t6_1373jobs.all (Job.check tree)=true := by
  simp only [t6_1373jobs,List.all_append,List.all_nil,t6_1373part0,Bool.and_self]
theorem t6_1373checked : Checked tree [5,9,9,9,3,7] := by
  refine ⟨plan7586,valid7586,t6_1373choices,?_⟩
  exact check_of_frontier tree 0 t6_1373root t6_1373jobs t6_1373frontier t6_1373all
theorem t6_1374choices : plan7890.choices=[5,9,9,9,6,7].map (options 6 6) := by rfl


theorem t6_1374part0 : t6_1374jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1374frontier : t6_1374root.frontier 0=t6_1374jobs := by rfl
theorem t6_1374all : t6_1374jobs.all (Job.check tree)=true := by
  simp only [t6_1374jobs,List.all_append,List.all_nil,t6_1374part0,Bool.and_self]
theorem t6_1374checked : Checked tree [5,9,9,9,6,7] := by
  refine ⟨plan7890,valid7890,t6_1374choices,?_⟩
  exact check_of_frontier tree 0 t6_1374root t6_1374jobs t6_1374frontier t6_1374all
theorem t6_1375choices : plan7891.choices=[5,9,9,9,7,7].map (options 6 6) := by rfl


theorem t6_1375part0 : t6_1375jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1375frontier : t6_1375root.frontier 0=t6_1375jobs := by rfl
theorem t6_1375all : t6_1375jobs.all (Job.check tree)=true := by
  simp only [t6_1375jobs,List.all_append,List.all_nil,t6_1375part0,Bool.and_self]
theorem t6_1375checked : Checked tree [5,9,9,9,7,7] := by
  refine ⟨plan7891,valid7891,t6_1375choices,?_⟩
  exact check_of_frontier tree 0 t6_1375root t6_1375jobs t6_1375frontier t6_1375all
theorem t6_1376choices : plan7892.choices=[5,9,9,9,10,7].map (options 6 6) := by rfl


theorem t6_1376part0 : t6_1376jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1376frontier : t6_1376root.frontier 0=t6_1376jobs := by rfl
theorem t6_1376all : t6_1376jobs.all (Job.check tree)=true := by
  simp only [t6_1376jobs,List.all_append,List.all_nil,t6_1376part0,Bool.and_self]
theorem t6_1376checked : Checked tree [5,9,9,9,10,7] := by
  refine ⟨plan7892,valid7892,t6_1376choices,?_⟩
  exact check_of_frontier tree 0 t6_1376root t6_1376jobs t6_1376frontier t6_1376all
theorem t6_1377choices : plan7893.choices=[5,9,9,10,7,7].map (options 6 6) := by rfl


theorem t6_1377part0 : t6_1377jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1377frontier : t6_1377root.frontier 0=t6_1377jobs := by rfl
theorem t6_1377all : t6_1377jobs.all (Job.check tree)=true := by
  simp only [t6_1377jobs,List.all_append,List.all_nil,t6_1377part0,Bool.and_self]
theorem t6_1377checked : Checked tree [5,9,9,10,7,7] := by
  refine ⟨plan7893,valid7893,t6_1377choices,?_⟩
  exact check_of_frontier tree 0 t6_1377root t6_1377jobs t6_1377frontier t6_1377all
theorem t6_1378choices : plan7894.choices=[5,9,9,10,10,7].map (options 6 6) := by rfl


theorem t6_1378part0 : t6_1378jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1378frontier : t6_1378root.frontier 0=t6_1378jobs := by rfl
theorem t6_1378all : t6_1378jobs.all (Job.check tree)=true := by
  simp only [t6_1378jobs,List.all_append,List.all_nil,t6_1378part0,Bool.and_self]
theorem t6_1378checked : Checked tree [5,9,9,10,10,7] := by
  refine ⟨plan7894,valid7894,t6_1378choices,?_⟩
  exact check_of_frontier tree 0 t6_1378root t6_1378jobs t6_1378frontier t6_1378all
theorem t6_1379choices : plan7895.choices=[5,9,9,10,10,10].map (options 6 6) := by rfl


theorem t6_1379part0 : t6_1379jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1379frontier : t6_1379root.frontier 0=t6_1379jobs := by rfl
theorem t6_1379all : t6_1379jobs.all (Job.check tree)=true := by
  simp only [t6_1379jobs,List.all_append,List.all_nil,t6_1379part0,Bool.and_self]
theorem t6_1379checked : Checked tree [5,9,9,10,10,10] := by
  refine ⟨plan7895,valid7895,t6_1379choices,?_⟩
  exact check_of_frontier tree 0 t6_1379root t6_1379jobs t6_1379frontier t6_1379all
theorem t6_1380choices : plan7896.choices=[5,9,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1380part0 : t6_1380jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1380frontier : t6_1380root.frontier 0=t6_1380jobs := by rfl
theorem t6_1380all : t6_1380jobs.all (Job.check tree)=true := by
  simp only [t6_1380jobs,List.all_append,List.all_nil,t6_1380part0,Bool.and_self]
theorem t6_1380checked : Checked tree [5,9,10,7,7,7] := by
  refine ⟨plan7896,valid7896,t6_1380choices,?_⟩
  exact check_of_frontier tree 0 t6_1380root t6_1380jobs t6_1380frontier t6_1380all
theorem t6_1381choices : plan7897.choices=[5,9,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1381part0 : t6_1381jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1381frontier : t6_1381root.frontier 0=t6_1381jobs := by rfl
theorem t6_1381all : t6_1381jobs.all (Job.check tree)=true := by
  simp only [t6_1381jobs,List.all_append,List.all_nil,t6_1381part0,Bool.and_self]
theorem t6_1381checked : Checked tree [5,9,10,10,7,7] := by
  refine ⟨plan7897,valid7897,t6_1381choices,?_⟩
  exact check_of_frontier tree 0 t6_1381root t6_1381jobs t6_1381frontier t6_1381all
theorem t6_1382choices : plan7898.choices=[5,9,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1382part0 : t6_1382jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1382frontier : t6_1382root.frontier 0=t6_1382jobs := by rfl
theorem t6_1382all : t6_1382jobs.all (Job.check tree)=true := by
  simp only [t6_1382jobs,List.all_append,List.all_nil,t6_1382part0,Bool.and_self]
theorem t6_1382checked : Checked tree [5,9,10,10,10,7] := by
  refine ⟨plan7898,valid7898,t6_1382choices,?_⟩
  exact check_of_frontier tree 0 t6_1382root t6_1382jobs t6_1382frontier t6_1382all
theorem t6_1383choices : plan7899.choices=[5,9,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1383part0 : t6_1383jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1383frontier : t6_1383root.frontier 0=t6_1383jobs := by rfl
theorem t6_1383all : t6_1383jobs.all (Job.check tree)=true := by
  simp only [t6_1383jobs,List.all_append,List.all_nil,t6_1383part0,Bool.and_self]
theorem t6_1383checked : Checked tree [5,9,10,10,10,10] := by
  refine ⟨plan7899,valid7899,t6_1383choices,?_⟩
  exact check_of_frontier tree 0 t6_1383root t6_1383jobs t6_1383frontier t6_1383all
theorem t6_1384choices : plan7900.choices=[5,10,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1384part0 : t6_1384jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1384frontier : t6_1384root.frontier 0=t6_1384jobs := by rfl
theorem t6_1384all : t6_1384jobs.all (Job.check tree)=true := by
  simp only [t6_1384jobs,List.all_append,List.all_nil,t6_1384part0,Bool.and_self]
theorem t6_1384checked : Checked tree [5,10,7,7,7,7] := by
  refine ⟨plan7900,valid7900,t6_1384choices,?_⟩
  exact check_of_frontier tree 0 t6_1384root t6_1384jobs t6_1384frontier t6_1384all
theorem t6_1385choices : plan7901.choices=[5,10,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1385part0 : t6_1385jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1385frontier : t6_1385root.frontier 0=t6_1385jobs := by rfl
theorem t6_1385all : t6_1385jobs.all (Job.check tree)=true := by
  simp only [t6_1385jobs,List.all_append,List.all_nil,t6_1385part0,Bool.and_self]
theorem t6_1385checked : Checked tree [5,10,10,7,7,7] := by
  refine ⟨plan7901,valid7901,t6_1385choices,?_⟩
  exact check_of_frontier tree 0 t6_1385root t6_1385jobs t6_1385frontier t6_1385all
theorem t6_1386choices : plan7902.choices=[5,10,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1386part0 : t6_1386jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1386frontier : t6_1386root.frontier 0=t6_1386jobs := by rfl
theorem t6_1386all : t6_1386jobs.all (Job.check tree)=true := by
  simp only [t6_1386jobs,List.all_append,List.all_nil,t6_1386part0,Bool.and_self]
theorem t6_1386checked : Checked tree [5,10,10,10,7,7] := by
  refine ⟨plan7902,valid7902,t6_1386choices,?_⟩
  exact check_of_frontier tree 0 t6_1386root t6_1386jobs t6_1386frontier t6_1386all
theorem t6_1387choices : plan7903.choices=[5,10,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1387part0 : t6_1387jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1387frontier : t6_1387root.frontier 0=t6_1387jobs := by rfl
theorem t6_1387all : t6_1387jobs.all (Job.check tree)=true := by
  simp only [t6_1387jobs,List.all_append,List.all_nil,t6_1387part0,Bool.and_self]
theorem t6_1387checked : Checked tree [5,10,10,10,10,7] := by
  refine ⟨plan7903,valid7903,t6_1387choices,?_⟩
  exact check_of_frontier tree 0 t6_1387root t6_1387jobs t6_1387frontier t6_1387all
theorem t6_1388choices : plan7904.choices=[5,10,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1388part0 : t6_1388jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1388frontier : t6_1388root.frontier 0=t6_1388jobs := by rfl
theorem t6_1388all : t6_1388jobs.all (Job.check tree)=true := by
  simp only [t6_1388jobs,List.all_append,List.all_nil,t6_1388part0,Bool.and_self]
theorem t6_1388checked : Checked tree [5,10,10,10,10,10] := by
  refine ⟨plan7904,valid7904,t6_1388choices,?_⟩
  exact check_of_frontier tree 0 t6_1388root t6_1388jobs t6_1388frontier t6_1388all
theorem t6_1389choices : plan7905.choices=[6,6,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1389part0 : t6_1389jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1389frontier : t6_1389root.frontier 0=t6_1389jobs := by rfl
theorem t6_1389all : t6_1389jobs.all (Job.check tree)=true := by
  simp only [t6_1389jobs,List.all_append,List.all_nil,t6_1389part0,Bool.and_self]
theorem t6_1389checked : Checked tree [6,6,6,6,6,6] := by
  refine ⟨plan7905,valid7905,t6_1389choices,?_⟩
  exact check_of_frontier tree 0 t6_1389root t6_1389jobs t6_1389frontier t6_1389all
theorem t6_1390choices : plan7906.choices=[6,6,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1390part0 : t6_1390jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1390frontier : t6_1390root.frontier 0=t6_1390jobs := by rfl
theorem t6_1390all : t6_1390jobs.all (Job.check tree)=true := by
  simp only [t6_1390jobs,List.all_append,List.all_nil,t6_1390part0,Bool.and_self]
theorem t6_1390checked : Checked tree [6,6,6,6,6,7] := by
  refine ⟨plan7906,valid7906,t6_1390choices,?_⟩
  exact check_of_frontier tree 0 t6_1390root t6_1390jobs t6_1390frontier t6_1390all
theorem t6_1391choices : plan7907.choices=[6,6,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1391part0 : t6_1391jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1391frontier : t6_1391root.frontier 0=t6_1391jobs := by rfl
theorem t6_1391all : t6_1391jobs.all (Job.check tree)=true := by
  simp only [t6_1391jobs,List.all_append,List.all_nil,t6_1391part0,Bool.and_self]
theorem t6_1391checked : Checked tree [6,6,6,6,6,10] := by
  refine ⟨plan7907,valid7907,t6_1391choices,?_⟩
  exact check_of_frontier tree 0 t6_1391root t6_1391jobs t6_1391frontier t6_1391all
theorem t6_1392choices : plan7908.choices=[6,6,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1392part0 : t6_1392jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1392frontier : t6_1392root.frontier 0=t6_1392jobs := by rfl
theorem t6_1392all : t6_1392jobs.all (Job.check tree)=true := by
  simp only [t6_1392jobs,List.all_append,List.all_nil,t6_1392part0,Bool.and_self]
theorem t6_1392checked : Checked tree [6,6,6,6,7,7] := by
  refine ⟨plan7908,valid7908,t6_1392choices,?_⟩
  exact check_of_frontier tree 0 t6_1392root t6_1392jobs t6_1392frontier t6_1392all
theorem t6_1393choices : plan7909.choices=[6,6,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1393part0 : t6_1393jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1393frontier : t6_1393root.frontier 0=t6_1393jobs := by rfl
theorem t6_1393all : t6_1393jobs.all (Job.check tree)=true := by
  simp only [t6_1393jobs,List.all_append,List.all_nil,t6_1393part0,Bool.and_self]
theorem t6_1393checked : Checked tree [6,6,6,6,10,7] := by
  refine ⟨plan7909,valid7909,t6_1393choices,?_⟩
  exact check_of_frontier tree 0 t6_1393root t6_1393jobs t6_1393frontier t6_1393all
theorem t6_1394choices : plan7910.choices=[6,6,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1394part0 : t6_1394jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1394frontier : t6_1394root.frontier 0=t6_1394jobs := by rfl
theorem t6_1394all : t6_1394jobs.all (Job.check tree)=true := by
  simp only [t6_1394jobs,List.all_append,List.all_nil,t6_1394part0,Bool.and_self]
theorem t6_1394checked : Checked tree [6,6,6,6,10,10] := by
  refine ⟨plan7910,valid7910,t6_1394choices,?_⟩
  exact check_of_frontier tree 0 t6_1394root t6_1394jobs t6_1394frontier t6_1394all
theorem t6_1395choices : plan7911.choices=[6,6,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1395part0 : t6_1395jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1395frontier : t6_1395root.frontier 0=t6_1395jobs := by rfl
theorem t6_1395all : t6_1395jobs.all (Job.check tree)=true := by
  simp only [t6_1395jobs,List.all_append,List.all_nil,t6_1395part0,Bool.and_self]
theorem t6_1395checked : Checked tree [6,6,6,7,7,7] := by
  refine ⟨plan7911,valid7911,t6_1395choices,?_⟩
  exact check_of_frontier tree 0 t6_1395root t6_1395jobs t6_1395frontier t6_1395all
theorem t6_1396choices : plan7912.choices=[6,6,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1396part0 : t6_1396jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1396frontier : t6_1396root.frontier 0=t6_1396jobs := by rfl
theorem t6_1396all : t6_1396jobs.all (Job.check tree)=true := by
  simp only [t6_1396jobs,List.all_append,List.all_nil,t6_1396part0,Bool.and_self]
theorem t6_1396checked : Checked tree [6,6,6,10,7,7] := by
  refine ⟨plan7912,valid7912,t6_1396choices,?_⟩
  exact check_of_frontier tree 0 t6_1396root t6_1396jobs t6_1396frontier t6_1396all
theorem t6_1397choices : plan7913.choices=[6,6,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1397part0 : t6_1397jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1397frontier : t6_1397root.frontier 0=t6_1397jobs := by rfl
theorem t6_1397all : t6_1397jobs.all (Job.check tree)=true := by
  simp only [t6_1397jobs,List.all_append,List.all_nil,t6_1397part0,Bool.and_self]
theorem t6_1397checked : Checked tree [6,6,6,10,10,7] := by
  refine ⟨plan7913,valid7913,t6_1397choices,?_⟩
  exact check_of_frontier tree 0 t6_1397root t6_1397jobs t6_1397frontier t6_1397all
theorem t6_1398choices : plan7914.choices=[6,6,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1398part0 : t6_1398jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1398frontier : t6_1398root.frontier 0=t6_1398jobs := by rfl
theorem t6_1398all : t6_1398jobs.all (Job.check tree)=true := by
  simp only [t6_1398jobs,List.all_append,List.all_nil,t6_1398part0,Bool.and_self]
theorem t6_1398checked : Checked tree [6,6,6,10,10,10] := by
  refine ⟨plan7914,valid7914,t6_1398choices,?_⟩
  exact check_of_frontier tree 0 t6_1398root t6_1398jobs t6_1398frontier t6_1398all
theorem t6_1399choices : plan7915.choices=[6,6,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1399part0 : t6_1399jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1399frontier : t6_1399root.frontier 0=t6_1399jobs := by rfl
theorem t6_1399all : t6_1399jobs.all (Job.check tree)=true := by
  simp only [t6_1399jobs,List.all_append,List.all_nil,t6_1399part0,Bool.and_self]
theorem t6_1399checked : Checked tree [6,6,7,7,7,7] := by
  refine ⟨plan7915,valid7915,t6_1399choices,?_⟩
  exact check_of_frontier tree 0 t6_1399root t6_1399jobs t6_1399frontier t6_1399all
theorem t6_1400choices : plan7916.choices=[6,6,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1400part0 : t6_1400jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1400frontier : t6_1400root.frontier 0=t6_1400jobs := by rfl
theorem t6_1400all : t6_1400jobs.all (Job.check tree)=true := by
  simp only [t6_1400jobs,List.all_append,List.all_nil,t6_1400part0,Bool.and_self]
theorem t6_1400checked : Checked tree [6,6,10,7,7,7] := by
  refine ⟨plan7916,valid7916,t6_1400choices,?_⟩
  exact check_of_frontier tree 0 t6_1400root t6_1400jobs t6_1400frontier t6_1400all
theorem t6_1401choices : plan7917.choices=[6,6,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1401part0 : t6_1401jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1401frontier : t6_1401root.frontier 0=t6_1401jobs := by rfl
theorem t6_1401all : t6_1401jobs.all (Job.check tree)=true := by
  simp only [t6_1401jobs,List.all_append,List.all_nil,t6_1401part0,Bool.and_self]
theorem t6_1401checked : Checked tree [6,6,10,10,7,7] := by
  refine ⟨plan7917,valid7917,t6_1401choices,?_⟩
  exact check_of_frontier tree 0 t6_1401root t6_1401jobs t6_1401frontier t6_1401all
theorem t6_1402choices : plan7918.choices=[6,6,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1402part0 : t6_1402jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1402frontier : t6_1402root.frontier 0=t6_1402jobs := by rfl
theorem t6_1402all : t6_1402jobs.all (Job.check tree)=true := by
  simp only [t6_1402jobs,List.all_append,List.all_nil,t6_1402part0,Bool.and_self]
theorem t6_1402checked : Checked tree [6,6,10,10,10,7] := by
  refine ⟨plan7918,valid7918,t6_1402choices,?_⟩
  exact check_of_frontier tree 0 t6_1402root t6_1402jobs t6_1402frontier t6_1402all
theorem t6_1403choices : plan7919.choices=[6,6,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1403part0 : t6_1403jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1403frontier : t6_1403root.frontier 0=t6_1403jobs := by rfl
theorem t6_1403all : t6_1403jobs.all (Job.check tree)=true := by
  simp only [t6_1403jobs,List.all_append,List.all_nil,t6_1403part0,Bool.and_self]
theorem t6_1403checked : Checked tree [6,6,10,10,10,10] := by
  refine ⟨plan7919,valid7919,t6_1403choices,?_⟩
  exact check_of_frontier tree 0 t6_1403root t6_1403jobs t6_1403frontier t6_1403all
theorem t6_1404choices : plan7920.choices=[6,7,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1404part0 : t6_1404jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1404frontier : t6_1404root.frontier 0=t6_1404jobs := by rfl
theorem t6_1404all : t6_1404jobs.all (Job.check tree)=true := by
  simp only [t6_1404jobs,List.all_append,List.all_nil,t6_1404part0,Bool.and_self]
theorem t6_1404checked : Checked tree [6,7,7,7,7,7] := by
  refine ⟨plan7920,valid7920,t6_1404choices,?_⟩
  exact check_of_frontier tree 0 t6_1404root t6_1404jobs t6_1404frontier t6_1404all
theorem t6_1405choices : plan7921.choices=[6,10,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1405part0 : t6_1405jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1405frontier : t6_1405root.frontier 0=t6_1405jobs := by rfl
theorem t6_1405all : t6_1405jobs.all (Job.check tree)=true := by
  simp only [t6_1405jobs,List.all_append,List.all_nil,t6_1405part0,Bool.and_self]
theorem t6_1405checked : Checked tree [6,10,7,7,7,7] := by
  refine ⟨plan7921,valid7921,t6_1405choices,?_⟩
  exact check_of_frontier tree 0 t6_1405root t6_1405jobs t6_1405frontier t6_1405all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks137 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1355checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1356checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1357checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1358checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1359checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1360checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1361checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1362checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1343checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1363checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1364checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1365checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1366checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1367checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1368checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1369checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1370checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1371checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1344checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1372checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1373checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1374checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1375checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1376checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1377checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1378checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1379checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1380checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1381checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1345checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1382checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1383checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1384checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1385checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1386checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1387checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1388checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1389checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1390checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1391checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1346checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1392checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1393checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1394checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1395checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1396checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1397checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1398checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1399checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1400checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1401checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1347checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1402checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1403checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1404checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1405checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1348checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1349checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1350checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1351checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1352checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1353checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1354checked⟩
