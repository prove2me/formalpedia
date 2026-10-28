-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks134
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:49:54.977157+00:00
-- url     : https://prove2.me/submissions/5dc748d0-a5ba-4b58-8414-1c3f51af43ee

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks134
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks134
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
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



















































theorem valid122 : plan122.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)







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



















theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)











theorem valid574 : plan574.Valid := valid_step _ _ _ valid134 (by decide +kernel)




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













































theorem valid1559 : plan1559.Valid := valid_step _ _ _ valid568 (by decide +kernel)





















































theorem valid1586 : plan1586.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1587 : plan1587.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1588 : plan1588.Valid := valid_step _ _ _ valid580 (by decide +kernel)























theorem valid1600 : plan1600.Valid := valid_step _ _ _ valid574 (by decide +kernel)



















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













































































theorem valid3303 : plan3303.Valid := valid_step _ _ _ valid1529 (by decide +kernel)

theorem valid3304 : plan3304.Valid := valid_step _ _ _ valid1530 (by decide +kernel)

theorem valid3305 : plan3305.Valid := valid_step _ _ _ valid1531 (by decide +kernel)

































































































theorem valid3354 : plan3354.Valid := valid_step _ _ _ valid1559 (by decide +kernel)












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



































































theorem valid5410 : plan5410.Valid := valid_step _ _ _ valid3264 (by decide +kernel)




























































































































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





































































































theorem valid5523 : plan5523.Valid := valid_step _ _ _ valid3303 (by decide +kernel)

theorem valid5524 : plan5524.Valid := valid_step _ _ _ valid3304 (by decide +kernel)

theorem valid5525 : plan5525.Valid := valid_step _ _ _ valid3305 (by decide +kernel)






















































































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





























































theorem valid6655 : plan6655.Valid := valid_step _ _ _ valid5523 (by decide +kernel)

theorem valid6656 : plan6656.Valid := valid_step _ _ _ valid5524 (by decide +kernel)

theorem valid6657 : plan6657.Valid := valid_step _ _ _ valid5525 (by decide +kernel)






























































































































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



































































































theorem valid5714 : plan5714.Valid := valid_step _ _ _ valid3354 (by decide +kernel)




























































































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











theorem valid5862 : plan5862.Valid := valid_step _ _ _ valid3490 (by decide +kernel)

theorem valid5863 : plan5863.Valid := valid_step _ _ _ valid3491 (by decide +kernel)

theorem valid5864 : plan5864.Valid := valid_step _ _ _ valid3492 (by decide +kernel)















theorem valid5872 : plan5872.Valid := valid_step _ _ _ valid3500 (by decide +kernel)
































































































































































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







































































































































































theorem valid6420 : plan6420.Valid := valid_step _ _ _ valid5410 (by decide +kernel)
























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











































































































































theorem valid6022 : plan6022.Valid := valid_step _ _ _ valid3540 (by decide +kernel)

theorem valid6023 : plan6023.Valid := valid_step _ _ _ valid3541 (by decide +kernel)

theorem valid6024 : plan6024.Valid := valid_step _ _ _ valid3542 (by decide +kernel)

theorem valid6025 : plan6025.Valid := valid_step _ _ _ valid3543 (by decide +kernel)

theorem valid6026 : plan6026.Valid := valid_step _ _ _ valid3544 (by decide +kernel)

theorem valid6027 : plan6027.Valid := valid_step _ _ _ valid3545 (by decide +kernel)

theorem valid6028 : plan6028.Valid := valid_step _ _ _ valid3546 (by decide +kernel)

theorem valid6029 : plan6029.Valid := valid_step _ _ _ valid3547 (by decide +kernel)

theorem valid6030 : plan6030.Valid := valid_step _ _ _ valid3548 (by decide +kernel)

theorem valid6031 : plan6031.Valid := valid_step _ _ _ valid3549 (by decide +kernel)

theorem valid6032 : plan6032.Valid := valid_step _ _ _ valid3550 (by decide +kernel)

theorem valid6033 : plan6033.Valid := valid_step _ _ _ valid3551 (by decide +kernel)

theorem valid6034 : plan6034.Valid := valid_step _ _ _ valid3552 (by decide +kernel)

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

















































































































theorem valid7065 : plan7065.Valid := valid_step _ _ _ valid5714 (by decide +kernel)














































































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



























































































































































theorem valid7566 : plan7566.Valid := valid_step _ _ _ valid5862 (by decide +kernel)

theorem valid7567 : plan7567.Valid := valid_step _ _ _ valid5863 (by decide +kernel)

theorem valid7568 : plan7568.Valid := valid_step _ _ _ valid5864 (by decide +kernel)

theorem valid7569 : plan7569.Valid := valid_step _ _ _ valid5872 (by decide +kernel)






























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





























































































































theorem valid7839 : plan7839.Valid := valid_step _ _ _ valid6022 (by decide +kernel)

theorem valid7840 : plan7840.Valid := valid_step _ _ _ valid6023 (by decide +kernel)

theorem valid7841 : plan7841.Valid := valid_step _ _ _ valid6024 (by decide +kernel)

theorem valid7842 : plan7842.Valid := valid_step _ _ _ valid6025 (by decide +kernel)

theorem valid7843 : plan7843.Valid := valid_step _ _ _ valid6026 (by decide +kernel)

theorem valid7844 : plan7844.Valid := valid_step _ _ _ valid6027 (by decide +kernel)

theorem valid7845 : plan7845.Valid := valid_step _ _ _ valid6028 (by decide +kernel)

theorem valid7846 : plan7846.Valid := valid_step _ _ _ valid6029 (by decide +kernel)

theorem valid7847 : plan7847.Valid := valid_step _ _ _ valid6030 (by decide +kernel)

theorem valid7848 : plan7848.Valid := valid_step _ _ _ valid6031 (by decide +kernel)

theorem valid7849 : plan7849.Valid := valid_step _ _ _ valid6032 (by decide +kernel)

theorem valid7850 : plan7850.Valid := valid_step _ _ _ valid6033 (by decide +kernel)

theorem valid7851 : plan7851.Valid := valid_step _ _ _ valid6034 (by decide +kernel)

theorem valid7852 : plan7852.Valid := valid_step _ _ _ valid6035 (by decide +kernel)

theorem valid7853 : plan7853.Valid := valid_step _ _ _ valid6036 (by decide +kernel)

theorem valid7854 : plan7854.Valid := valid_step _ _ _ valid6037 (by decide +kernel)

theorem valid7855 : plan7855.Valid := valid_step _ _ _ valid6038 (by decide +kernel)

theorem valid7856 : plan7856.Valid := valid_step _ _ _ valid6039 (by decide +kernel)

theorem valid7857 : plan7857.Valid := valid_step _ _ _ valid6040 (by decide +kernel)

theorem valid7858 : plan7858.Valid := valid_step _ _ _ valid6041 (by decide +kernel)

theorem valid7859 : plan7859.Valid := valid_step _ _ _ valid6042 (by decide +kernel)

theorem valid7860 : plan7860.Valid := valid_step _ _ _ valid6043 (by decide +kernel)

theorem valid7861 : plan7861.Valid := valid_step _ _ _ valid6044 (by decide +kernel)

theorem valid7862 : plan7862.Valid := valid_step _ _ _ valid6045 (by decide +kernel)

theorem valid7863 : plan7863.Valid := valid_step _ _ _ valid6046 (by decide +kernel)

theorem valid7864 : plan7864.Valid := valid_step _ _ _ valid6047 (by decide +kernel)

theorem valid7865 : plan7865.Valid := valid_step _ _ _ valid6048 (by decide +kernel)

theorem valid7866 : plan7866.Valid := valid_step _ _ _ valid6049 (by decide +kernel)

theorem valid7867 : plan7867.Valid := valid_step _ _ _ valid6050 (by decide +kernel)

theorem valid7868 : plan7868.Valid := valid_step _ _ _ valid6051 (by decide +kernel)

theorem valid7869 : plan7869.Valid := valid_step _ _ _ valid6052 (by decide +kernel)

theorem valid7870 : plan7870.Valid := valid_step _ _ _ valid6053 (by decide +kernel)

theorem valid7871 : plan7871.Valid := valid_step _ _ _ valid6054 (by decide +kernel)


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
theorem t6_1288choices : plan7566.choices=[5,5,9,3,7,7].map (options 6 5) := by rfl


theorem t6_1288part0 : t6_1288jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1288part1 : t6_1288jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1288frontier : t6_1288root.frontier 1=t6_1288jobs := by rfl
theorem t6_1288all : t6_1288jobs.all (Job.check tree)=true := by
  simp only [t6_1288jobs,List.all_append,List.all_nil,t6_1288part0,t6_1288part1,Bool.and_self]
theorem t6_1288checked : Checked tree [5,5,9,3,7,7] := by
  refine ⟨plan7566,valid7566,t6_1288choices,?_⟩
  exact check_of_frontier tree 1 t6_1288root t6_1288jobs t6_1288frontier t6_1288all
theorem t6_1289choices : plan7567.choices=[5,5,9,3,10,7].map (options 6 5) := by rfl


theorem t6_1289part0 : t6_1289jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1289frontier : t6_1289root.frontier 0=t6_1289jobs := by rfl
theorem t6_1289all : t6_1289jobs.all (Job.check tree)=true := by
  simp only [t6_1289jobs,List.all_append,List.all_nil,t6_1289part0,Bool.and_self]
theorem t6_1289checked : Checked tree [5,5,9,3,10,7] := by
  refine ⟨plan7567,valid7567,t6_1289choices,?_⟩
  exact check_of_frontier tree 0 t6_1289root t6_1289jobs t6_1289frontier t6_1289all
theorem t6_1290choices : plan7568.choices=[5,5,9,3,10,10].map (options 6 5) := by rfl


theorem t6_1290part0 : t6_1290jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1290frontier : t6_1290root.frontier 0=t6_1290jobs := by rfl
theorem t6_1290all : t6_1290jobs.all (Job.check tree)=true := by
  simp only [t6_1290jobs,List.all_append,List.all_nil,t6_1290part0,Bool.and_self]
theorem t6_1290checked : Checked tree [5,5,9,3,10,10] := by
  refine ⟨plan7568,valid7568,t6_1290choices,?_⟩
  exact check_of_frontier tree 0 t6_1290root t6_1290jobs t6_1290frontier t6_1290all
theorem t6_1291choices : plan7839.choices=[5,5,9,6,6,6].map (options 6 6) := by rfl


theorem t6_1291part0 : t6_1291jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1291frontier : t6_1291root.frontier 0=t6_1291jobs := by rfl
theorem t6_1291all : t6_1291jobs.all (Job.check tree)=true := by
  simp only [t6_1291jobs,List.all_append,List.all_nil,t6_1291part0,Bool.and_self]
theorem t6_1291checked : Checked tree [5,5,9,6,6,6] := by
  refine ⟨plan7839,valid7839,t6_1291choices,?_⟩
  exact check_of_frontier tree 0 t6_1291root t6_1291jobs t6_1291frontier t6_1291all
theorem t6_1292choices : plan7840.choices=[5,5,9,6,6,7].map (options 6 6) := by rfl


theorem t6_1292part0 : t6_1292jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1292frontier : t6_1292root.frontier 0=t6_1292jobs := by rfl
theorem t6_1292all : t6_1292jobs.all (Job.check tree)=true := by
  simp only [t6_1292jobs,List.all_append,List.all_nil,t6_1292part0,Bool.and_self]
theorem t6_1292checked : Checked tree [5,5,9,6,6,7] := by
  refine ⟨plan7840,valid7840,t6_1292choices,?_⟩
  exact check_of_frontier tree 0 t6_1292root t6_1292jobs t6_1292frontier t6_1292all
theorem t6_1293choices : plan7841.choices=[5,5,9,6,6,10].map (options 6 6) := by rfl


theorem t6_1293part0 : t6_1293jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1293frontier : t6_1293root.frontier 0=t6_1293jobs := by rfl
theorem t6_1293all : t6_1293jobs.all (Job.check tree)=true := by
  simp only [t6_1293jobs,List.all_append,List.all_nil,t6_1293part0,Bool.and_self]
theorem t6_1293checked : Checked tree [5,5,9,6,6,10] := by
  refine ⟨plan7841,valid7841,t6_1293choices,?_⟩
  exact check_of_frontier tree 0 t6_1293root t6_1293jobs t6_1293frontier t6_1293all
theorem t6_1294choices : plan7842.choices=[5,5,9,6,7,7].map (options 6 6) := by rfl


theorem t6_1294part0 : t6_1294jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1294frontier : t6_1294root.frontier 0=t6_1294jobs := by rfl
theorem t6_1294all : t6_1294jobs.all (Job.check tree)=true := by
  simp only [t6_1294jobs,List.all_append,List.all_nil,t6_1294part0,Bool.and_self]
theorem t6_1294checked : Checked tree [5,5,9,6,7,7] := by
  refine ⟨plan7842,valid7842,t6_1294choices,?_⟩
  exact check_of_frontier tree 0 t6_1294root t6_1294jobs t6_1294frontier t6_1294all
theorem t6_1295choices : plan7843.choices=[5,5,9,6,10,7].map (options 6 6) := by rfl


theorem t6_1295part0 : t6_1295jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1295frontier : t6_1295root.frontier 0=t6_1295jobs := by rfl
theorem t6_1295all : t6_1295jobs.all (Job.check tree)=true := by
  simp only [t6_1295jobs,List.all_append,List.all_nil,t6_1295part0,Bool.and_self]
theorem t6_1295checked : Checked tree [5,5,9,6,10,7] := by
  refine ⟨plan7843,valid7843,t6_1295choices,?_⟩
  exact check_of_frontier tree 0 t6_1295root t6_1295jobs t6_1295frontier t6_1295all
theorem t6_1296choices : plan7844.choices=[5,5,9,6,10,10].map (options 6 6) := by rfl


theorem t6_1296part0 : t6_1296jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1296frontier : t6_1296root.frontier 0=t6_1296jobs := by rfl
theorem t6_1296all : t6_1296jobs.all (Job.check tree)=true := by
  simp only [t6_1296jobs,List.all_append,List.all_nil,t6_1296part0,Bool.and_self]
theorem t6_1296checked : Checked tree [5,5,9,6,10,10] := by
  refine ⟨plan7844,valid7844,t6_1296choices,?_⟩
  exact check_of_frontier tree 0 t6_1296root t6_1296jobs t6_1296frontier t6_1296all
theorem t6_1297choices : plan7845.choices=[5,5,9,7,7,7].map (options 6 6) := by rfl


theorem t6_1297part0 : t6_1297jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1297frontier : t6_1297root.frontier 0=t6_1297jobs := by rfl
theorem t6_1297all : t6_1297jobs.all (Job.check tree)=true := by
  simp only [t6_1297jobs,List.all_append,List.all_nil,t6_1297part0,Bool.and_self]
theorem t6_1297checked : Checked tree [5,5,9,7,7,7] := by
  refine ⟨plan7845,valid7845,t6_1297choices,?_⟩
  exact check_of_frontier tree 0 t6_1297root t6_1297jobs t6_1297frontier t6_1297all
theorem t6_1298choices : plan7569.choices=[5,5,9,9,3,7].map (options 6 5) := by rfl


theorem t6_1298part0 : t6_1298jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1298frontier : t6_1298root.frontier 0=t6_1298jobs := by rfl
theorem t6_1298all : t6_1298jobs.all (Job.check tree)=true := by
  simp only [t6_1298jobs,List.all_append,List.all_nil,t6_1298part0,Bool.and_self]
theorem t6_1298checked : Checked tree [5,5,9,9,3,7] := by
  refine ⟨plan7569,valid7569,t6_1298choices,?_⟩
  exact check_of_frontier tree 0 t6_1298root t6_1298jobs t6_1298frontier t6_1298all
theorem t6_1299choices : plan7846.choices=[5,5,9,9,6,7].map (options 6 6) := by rfl


theorem t6_1299part0 : t6_1299jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1299frontier : t6_1299root.frontier 0=t6_1299jobs := by rfl
theorem t6_1299all : t6_1299jobs.all (Job.check tree)=true := by
  simp only [t6_1299jobs,List.all_append,List.all_nil,t6_1299part0,Bool.and_self]
theorem t6_1299checked : Checked tree [5,5,9,9,6,7] := by
  refine ⟨plan7846,valid7846,t6_1299choices,?_⟩
  exact check_of_frontier tree 0 t6_1299root t6_1299jobs t6_1299frontier t6_1299all
theorem t6_1300choices : plan7847.choices=[5,5,9,9,7,7].map (options 6 6) := by rfl


theorem t6_1300part0 : t6_1300jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1300frontier : t6_1300root.frontier 0=t6_1300jobs := by rfl
theorem t6_1300all : t6_1300jobs.all (Job.check tree)=true := by
  simp only [t6_1300jobs,List.all_append,List.all_nil,t6_1300part0,Bool.and_self]
theorem t6_1300checked : Checked tree [5,5,9,9,7,7] := by
  refine ⟨plan7847,valid7847,t6_1300choices,?_⟩
  exact check_of_frontier tree 0 t6_1300root t6_1300jobs t6_1300frontier t6_1300all
theorem t6_1301choices : plan7848.choices=[5,5,9,9,10,7].map (options 6 6) := by rfl


theorem t6_1301part0 : t6_1301jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1301frontier : t6_1301root.frontier 0=t6_1301jobs := by rfl
theorem t6_1301all : t6_1301jobs.all (Job.check tree)=true := by
  simp only [t6_1301jobs,List.all_append,List.all_nil,t6_1301part0,Bool.and_self]
theorem t6_1301checked : Checked tree [5,5,9,9,10,7] := by
  refine ⟨plan7848,valid7848,t6_1301choices,?_⟩
  exact check_of_frontier tree 0 t6_1301root t6_1301jobs t6_1301frontier t6_1301all
theorem t6_1302choices : plan7849.choices=[5,5,9,10,7,7].map (options 6 6) := by rfl


theorem t6_1302part0 : t6_1302jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1302frontier : t6_1302root.frontier 0=t6_1302jobs := by rfl
theorem t6_1302all : t6_1302jobs.all (Job.check tree)=true := by
  simp only [t6_1302jobs,List.all_append,List.all_nil,t6_1302part0,Bool.and_self]
theorem t6_1302checked : Checked tree [5,5,9,10,7,7] := by
  refine ⟨plan7849,valid7849,t6_1302choices,?_⟩
  exact check_of_frontier tree 0 t6_1302root t6_1302jobs t6_1302frontier t6_1302all
theorem t6_1303choices : plan7850.choices=[5,5,9,10,10,7].map (options 6 6) := by rfl


theorem t6_1303part0 : t6_1303jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1303frontier : t6_1303root.frontier 0=t6_1303jobs := by rfl
theorem t6_1303all : t6_1303jobs.all (Job.check tree)=true := by
  simp only [t6_1303jobs,List.all_append,List.all_nil,t6_1303part0,Bool.and_self]
theorem t6_1303checked : Checked tree [5,5,9,10,10,7] := by
  refine ⟨plan7850,valid7850,t6_1303choices,?_⟩
  exact check_of_frontier tree 0 t6_1303root t6_1303jobs t6_1303frontier t6_1303all
theorem t6_1304choices : plan7851.choices=[5,5,9,10,10,10].map (options 6 6) := by rfl


theorem t6_1304part0 : t6_1304jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1304frontier : t6_1304root.frontier 0=t6_1304jobs := by rfl
theorem t6_1304all : t6_1304jobs.all (Job.check tree)=true := by
  simp only [t6_1304jobs,List.all_append,List.all_nil,t6_1304part0,Bool.and_self]
theorem t6_1304checked : Checked tree [5,5,9,10,10,10] := by
  refine ⟨plan7851,valid7851,t6_1304choices,?_⟩
  exact check_of_frontier tree 0 t6_1304root t6_1304jobs t6_1304frontier t6_1304all
theorem t6_1305choices : plan7852.choices=[5,5,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1305part0 : t6_1305jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1305frontier : t6_1305root.frontier 0=t6_1305jobs := by rfl
theorem t6_1305all : t6_1305jobs.all (Job.check tree)=true := by
  simp only [t6_1305jobs,List.all_append,List.all_nil,t6_1305part0,Bool.and_self]
theorem t6_1305checked : Checked tree [5,5,10,7,7,7] := by
  refine ⟨plan7852,valid7852,t6_1305choices,?_⟩
  exact check_of_frontier tree 0 t6_1305root t6_1305jobs t6_1305frontier t6_1305all
theorem t6_1306choices : plan7853.choices=[5,5,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1306part0 : t6_1306jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1306frontier : t6_1306root.frontier 0=t6_1306jobs := by rfl
theorem t6_1306all : t6_1306jobs.all (Job.check tree)=true := by
  simp only [t6_1306jobs,List.all_append,List.all_nil,t6_1306part0,Bool.and_self]
theorem t6_1306checked : Checked tree [5,5,10,10,7,7] := by
  refine ⟨plan7853,valid7853,t6_1306choices,?_⟩
  exact check_of_frontier tree 0 t6_1306root t6_1306jobs t6_1306frontier t6_1306all
theorem t6_1307choices : plan7854.choices=[5,5,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1307part0 : t6_1307jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1307frontier : t6_1307root.frontier 0=t6_1307jobs := by rfl
theorem t6_1307all : t6_1307jobs.all (Job.check tree)=true := by
  simp only [t6_1307jobs,List.all_append,List.all_nil,t6_1307part0,Bool.and_self]
theorem t6_1307checked : Checked tree [5,5,10,10,10,7] := by
  refine ⟨plan7854,valid7854,t6_1307choices,?_⟩
  exact check_of_frontier tree 0 t6_1307root t6_1307jobs t6_1307frontier t6_1307all
theorem t6_1308choices : plan7855.choices=[5,5,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1308part0 : t6_1308jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1308frontier : t6_1308root.frontier 0=t6_1308jobs := by rfl
theorem t6_1308all : t6_1308jobs.all (Job.check tree)=true := by
  simp only [t6_1308jobs,List.all_append,List.all_nil,t6_1308part0,Bool.and_self]
theorem t6_1308checked : Checked tree [5,5,10,10,10,10] := by
  refine ⟨plan7855,valid7855,t6_1308choices,?_⟩
  exact check_of_frontier tree 0 t6_1308root t6_1308jobs t6_1308frontier t6_1308all
theorem t6_1309choices : plan7856.choices=[5,6,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1309part0 : t6_1309jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1309frontier : t6_1309root.frontier 0=t6_1309jobs := by rfl
theorem t6_1309all : t6_1309jobs.all (Job.check tree)=true := by
  simp only [t6_1309jobs,List.all_append,List.all_nil,t6_1309part0,Bool.and_self]
theorem t6_1309checked : Checked tree [5,6,6,6,6,6] := by
  refine ⟨plan7856,valid7856,t6_1309choices,?_⟩
  exact check_of_frontier tree 0 t6_1309root t6_1309jobs t6_1309frontier t6_1309all
theorem t6_1310choices : plan7857.choices=[5,6,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1310part0 : t6_1310jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1310frontier : t6_1310root.frontier 0=t6_1310jobs := by rfl
theorem t6_1310all : t6_1310jobs.all (Job.check tree)=true := by
  simp only [t6_1310jobs,List.all_append,List.all_nil,t6_1310part0,Bool.and_self]
theorem t6_1310checked : Checked tree [5,6,6,6,6,7] := by
  refine ⟨plan7857,valid7857,t6_1310choices,?_⟩
  exact check_of_frontier tree 0 t6_1310root t6_1310jobs t6_1310frontier t6_1310all
theorem t6_1311choices : plan7858.choices=[5,6,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1311part0 : t6_1311jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1311frontier : t6_1311root.frontier 0=t6_1311jobs := by rfl
theorem t6_1311all : t6_1311jobs.all (Job.check tree)=true := by
  simp only [t6_1311jobs,List.all_append,List.all_nil,t6_1311part0,Bool.and_self]
theorem t6_1311checked : Checked tree [5,6,6,6,6,10] := by
  refine ⟨plan7858,valid7858,t6_1311choices,?_⟩
  exact check_of_frontier tree 0 t6_1311root t6_1311jobs t6_1311frontier t6_1311all
theorem t6_1312choices : plan7859.choices=[5,6,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1312part0 : t6_1312jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1312frontier : t6_1312root.frontier 0=t6_1312jobs := by rfl
theorem t6_1312all : t6_1312jobs.all (Job.check tree)=true := by
  simp only [t6_1312jobs,List.all_append,List.all_nil,t6_1312part0,Bool.and_self]
theorem t6_1312checked : Checked tree [5,6,6,6,7,7] := by
  refine ⟨plan7859,valid7859,t6_1312choices,?_⟩
  exact check_of_frontier tree 0 t6_1312root t6_1312jobs t6_1312frontier t6_1312all
theorem t6_1313choices : plan7860.choices=[5,6,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1313part0 : t6_1313jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1313frontier : t6_1313root.frontier 0=t6_1313jobs := by rfl
theorem t6_1313all : t6_1313jobs.all (Job.check tree)=true := by
  simp only [t6_1313jobs,List.all_append,List.all_nil,t6_1313part0,Bool.and_self]
theorem t6_1313checked : Checked tree [5,6,6,6,10,7] := by
  refine ⟨plan7860,valid7860,t6_1313choices,?_⟩
  exact check_of_frontier tree 0 t6_1313root t6_1313jobs t6_1313frontier t6_1313all
theorem t6_1314choices : plan7861.choices=[5,6,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1314part0 : t6_1314jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1314frontier : t6_1314root.frontier 0=t6_1314jobs := by rfl
theorem t6_1314all : t6_1314jobs.all (Job.check tree)=true := by
  simp only [t6_1314jobs,List.all_append,List.all_nil,t6_1314part0,Bool.and_self]
theorem t6_1314checked : Checked tree [5,6,6,6,10,10] := by
  refine ⟨plan7861,valid7861,t6_1314choices,?_⟩
  exact check_of_frontier tree 0 t6_1314root t6_1314jobs t6_1314frontier t6_1314all
theorem t6_1315choices : plan7862.choices=[5,6,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1315part0 : t6_1315jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1315frontier : t6_1315root.frontier 0=t6_1315jobs := by rfl
theorem t6_1315all : t6_1315jobs.all (Job.check tree)=true := by
  simp only [t6_1315jobs,List.all_append,List.all_nil,t6_1315part0,Bool.and_self]
theorem t6_1315checked : Checked tree [5,6,6,7,7,7] := by
  refine ⟨plan7862,valid7862,t6_1315choices,?_⟩
  exact check_of_frontier tree 0 t6_1315root t6_1315jobs t6_1315frontier t6_1315all
theorem t6_1316choices : plan7863.choices=[5,6,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1316part0 : t6_1316jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1316frontier : t6_1316root.frontier 0=t6_1316jobs := by rfl
theorem t6_1316all : t6_1316jobs.all (Job.check tree)=true := by
  simp only [t6_1316jobs,List.all_append,List.all_nil,t6_1316part0,Bool.and_self]
theorem t6_1316checked : Checked tree [5,6,6,10,7,7] := by
  refine ⟨plan7863,valid7863,t6_1316choices,?_⟩
  exact check_of_frontier tree 0 t6_1316root t6_1316jobs t6_1316frontier t6_1316all
theorem t6_1317choices : plan7864.choices=[5,6,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1317part0 : t6_1317jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1317frontier : t6_1317root.frontier 0=t6_1317jobs := by rfl
theorem t6_1317all : t6_1317jobs.all (Job.check tree)=true := by
  simp only [t6_1317jobs,List.all_append,List.all_nil,t6_1317part0,Bool.and_self]
theorem t6_1317checked : Checked tree [5,6,6,10,10,7] := by
  refine ⟨plan7864,valid7864,t6_1317choices,?_⟩
  exact check_of_frontier tree 0 t6_1317root t6_1317jobs t6_1317frontier t6_1317all
theorem t6_1318choices : plan7865.choices=[5,6,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1318part0 : t6_1318jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1318frontier : t6_1318root.frontier 0=t6_1318jobs := by rfl
theorem t6_1318all : t6_1318jobs.all (Job.check tree)=true := by
  simp only [t6_1318jobs,List.all_append,List.all_nil,t6_1318part0,Bool.and_self]
theorem t6_1318checked : Checked tree [5,6,6,10,10,10] := by
  refine ⟨plan7865,valid7865,t6_1318choices,?_⟩
  exact check_of_frontier tree 0 t6_1318root t6_1318jobs t6_1318frontier t6_1318all
theorem t6_1319choices : plan7866.choices=[5,6,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1319part0 : t6_1319jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1319frontier : t6_1319root.frontier 0=t6_1319jobs := by rfl
theorem t6_1319all : t6_1319jobs.all (Job.check tree)=true := by
  simp only [t6_1319jobs,List.all_append,List.all_nil,t6_1319part0,Bool.and_self]
theorem t6_1319checked : Checked tree [5,6,7,7,7,7] := by
  refine ⟨plan7866,valid7866,t6_1319choices,?_⟩
  exact check_of_frontier tree 0 t6_1319root t6_1319jobs t6_1319frontier t6_1319all
theorem t6_1320choices : plan7867.choices=[5,6,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1320part0 : t6_1320jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1320frontier : t6_1320root.frontier 0=t6_1320jobs := by rfl
theorem t6_1320all : t6_1320jobs.all (Job.check tree)=true := by
  simp only [t6_1320jobs,List.all_append,List.all_nil,t6_1320part0,Bool.and_self]
theorem t6_1320checked : Checked tree [5,6,10,7,7,7] := by
  refine ⟨plan7867,valid7867,t6_1320choices,?_⟩
  exact check_of_frontier tree 0 t6_1320root t6_1320jobs t6_1320frontier t6_1320all
theorem t6_1321choices : plan7868.choices=[5,6,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1321part0 : t6_1321jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1321frontier : t6_1321root.frontier 0=t6_1321jobs := by rfl
theorem t6_1321all : t6_1321jobs.all (Job.check tree)=true := by
  simp only [t6_1321jobs,List.all_append,List.all_nil,t6_1321part0,Bool.and_self]
theorem t6_1321checked : Checked tree [5,6,10,10,7,7] := by
  refine ⟨plan7868,valid7868,t6_1321choices,?_⟩
  exact check_of_frontier tree 0 t6_1321root t6_1321jobs t6_1321frontier t6_1321all
theorem t6_1322choices : plan7869.choices=[5,6,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1322part0 : t6_1322jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1322frontier : t6_1322root.frontier 0=t6_1322jobs := by rfl
theorem t6_1322all : t6_1322jobs.all (Job.check tree)=true := by
  simp only [t6_1322jobs,List.all_append,List.all_nil,t6_1322part0,Bool.and_self]
theorem t6_1322checked : Checked tree [5,6,10,10,10,7] := by
  refine ⟨plan7869,valid7869,t6_1322choices,?_⟩
  exact check_of_frontier tree 0 t6_1322root t6_1322jobs t6_1322frontier t6_1322all
theorem t6_1323choices : plan7870.choices=[5,6,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1323part0 : t6_1323jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1323frontier : t6_1323root.frontier 0=t6_1323jobs := by rfl
theorem t6_1323all : t6_1323jobs.all (Job.check tree)=true := by
  simp only [t6_1323jobs,List.all_append,List.all_nil,t6_1323part0,Bool.and_self]
theorem t6_1323checked : Checked tree [5,6,10,10,10,10] := by
  refine ⟨plan7870,valid7870,t6_1323choices,?_⟩
  exact check_of_frontier tree 0 t6_1323root t6_1323jobs t6_1323frontier t6_1323all
theorem t6_1324choices : plan7871.choices=[5,7,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1324part0 : t6_1324jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1324frontier : t6_1324root.frontier 0=t6_1324jobs := by rfl
theorem t6_1324all : t6_1324jobs.all (Job.check tree)=true := by
  simp only [t6_1324jobs,List.all_append,List.all_nil,t6_1324part0,Bool.and_self]
theorem t6_1324checked : Checked tree [5,7,7,7,7,7] := by
  refine ⟨plan7871,valid7871,t6_1324choices,?_⟩
  exact check_of_frontier tree 0 t6_1324root t6_1324jobs t6_1324frontier t6_1324all
theorem t6_1325choices : plan6420.choices=[5,9,3,3,3,3].map (options 6 2) := by rfl


theorem t6_1325part0 : t6_1325jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1325frontier : t6_1325root.frontier 0=t6_1325jobs := by rfl
theorem t6_1325all : t6_1325jobs.all (Job.check tree)=true := by
  simp only [t6_1325jobs,List.all_append,List.all_nil,t6_1325part0,Bool.and_self]
theorem t6_1325checked : Checked tree [5,9,3,3,3,3] := by
  refine ⟨plan6420,valid6420,t6_1325choices,?_⟩
  exact check_of_frontier tree 0 t6_1325root t6_1325jobs t6_1325frontier t6_1325all
theorem t6_1326choices : plan6655.choices=[5,9,3,3,3,6].map (options 6 3) := by rfl


theorem t6_1326part0 : t6_1326jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1326part1 : t6_1326jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1326frontier : t6_1326root.frontier 1=t6_1326jobs := by rfl
theorem t6_1326all : t6_1326jobs.all (Job.check tree)=true := by
  simp only [t6_1326jobs,List.all_append,List.all_nil,t6_1326part0,t6_1326part1,Bool.and_self]
theorem t6_1326checked : Checked tree [5,9,3,3,3,6] := by
  refine ⟨plan6655,valid6655,t6_1326choices,?_⟩
  exact check_of_frontier tree 1 t6_1326root t6_1326jobs t6_1326frontier t6_1326all
theorem t6_1327choices : plan6656.choices=[5,9,3,3,3,7].map (options 6 3) := by rfl


theorem t6_1327part0 : t6_1327jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1327part1 : t6_1327jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1327part2 : t6_1327jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1327part3 : t6_1327jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1327frontier : t6_1327root.frontier 1=t6_1327jobs := by rfl
theorem t6_1327all : t6_1327jobs.all (Job.check tree)=true := by
  simp only [t6_1327jobs,List.all_append,List.all_nil,t6_1327part0,t6_1327part1,t6_1327part2,t6_1327part3,Bool.and_self]
theorem t6_1327checked : Checked tree [5,9,3,3,3,7] := by
  refine ⟨plan6656,valid6656,t6_1327choices,?_⟩
  exact check_of_frontier tree 1 t6_1327root t6_1327jobs t6_1327frontier t6_1327all
theorem t6_1328choices : plan6657.choices=[5,9,3,3,3,10].map (options 6 3) := by rfl


theorem t6_1328part0 : t6_1328jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1328part1 : t6_1328jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1328frontier : t6_1328root.frontier 1=t6_1328jobs := by rfl
theorem t6_1328all : t6_1328jobs.all (Job.check tree)=true := by
  simp only [t6_1328jobs,List.all_append,List.all_nil,t6_1328part0,t6_1328part1,Bool.and_self]
theorem t6_1328checked : Checked tree [5,9,3,3,3,10] := by
  refine ⟨plan6657,valid6657,t6_1328choices,?_⟩
  exact check_of_frontier tree 1 t6_1328root t6_1328jobs t6_1328frontier t6_1328all
theorem t6_1329choices : plan7065.choices=[5,9,3,3,6,6].map (options 6 4) := by rfl


theorem t6_1329part0 : t6_1329jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1329frontier : t6_1329root.frontier 0=t6_1329jobs := by rfl
theorem t6_1329all : t6_1329jobs.all (Job.check tree)=true := by
  simp only [t6_1329jobs,List.all_append,List.all_nil,t6_1329part0,Bool.and_self]
theorem t6_1329checked : Checked tree [5,9,3,3,6,6] := by
  refine ⟨plan7065,valid7065,t6_1329choices,?_⟩
  exact check_of_frontier tree 0 t6_1329root t6_1329jobs t6_1329frontier t6_1329all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks134 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1300checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1301checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1302checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1303checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1304checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1305checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1288checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1306checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1307checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1308checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1309checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1310checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1311checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1312checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1313checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1314checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1315checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1289checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1316checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1317checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1318checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1319checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1320checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1321checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1322checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1323checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1324checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1325checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1290checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1326checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1327checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1328checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1329checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1291checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1292checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1293checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1294checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1295checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1296checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1297checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1298checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1299checked⟩
