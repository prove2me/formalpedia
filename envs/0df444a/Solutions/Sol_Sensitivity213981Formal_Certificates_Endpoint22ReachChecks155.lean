-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks155
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:12:47.686677+00:00
-- url     : https://prove2.me/submissions/2d485b8b-2296-4cb4-b9e2-14313a892c5b

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks155
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks155
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans080
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans083
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans086
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
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











































































theorem valid134 : plan134.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid135 : plan135.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid136 : plan136.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid137 : plan137.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid138 : plan138.Valid := valid_step _ _ _ valid0 (by decide +kernel)











theorem valid144 : plan144.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid147 : plan147.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid150 : plan150.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid153 : plan153.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid156 : plan156.Valid := valid_step _ _ _ valid0 (by decide +kernel)








































































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

















theorem valid595 : plan595.Valid := valid_step _ _ _ valid144 (by decide +kernel)











theorem valid601 : plan601.Valid := valid_step _ _ _ valid147 (by decide +kernel)











theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)











theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)











theorem valid619 : plan619.Valid := valid_step _ _ _ valid156 (by decide +kernel)










































































































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















theorem valid1640 : plan1640.Valid := valid_step _ _ _ valid601 (by decide +kernel)





theorem valid1643 : plan1643.Valid := valid_step _ _ _ valid601 (by decide +kernel)

theorem valid1644 : plan1644.Valid := valid_step _ _ _ valid601 (by decide +kernel)













theorem valid1651 : plan1651.Valid := valid_step _ _ _ valid607 (by decide +kernel)





theorem valid1654 : plan1654.Valid := valid_step _ _ _ valid607 (by decide +kernel)



















theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)



















theorem valid1674 : plan1674.Valid := valid_step _ _ _ valid619 (by decide +kernel)












































































































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

















theorem valid1631 : plan1631.Valid := valid_step _ _ _ valid595 (by decide +kernel)


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

















theorem valid3565 : plan3565.Valid := valid_step _ _ _ valid1631 (by decide +kernel)

















theorem valid3574 : plan3574.Valid := valid_step _ _ _ valid1640 (by decide +kernel)





theorem valid3577 : plan3577.Valid := valid_step _ _ _ valid1643 (by decide +kernel)

theorem valid3578 : plan3578.Valid := valid_step _ _ _ valid1644 (by decide +kernel)

























theorem valid3591 : plan3591.Valid := valid_step _ _ _ valid1651 (by decide +kernel)





theorem valid3594 : plan3594.Valid := valid_step _ _ _ valid1654 (by decide +kernel)







theorem valid3598 : plan3598.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

theorem valid3599 : plan3599.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

























theorem valid3612 : plan3612.Valid := valid_step _ _ _ valid1664 (by decide +kernel)







theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3617 : plan3617.Valid := valid_step _ _ _ valid1664 (by decide +kernel)





















theorem valid3628 : plan3628.Valid := valid_step _ _ _ valid1674 (by decide +kernel)







theorem valid3632 : plan3632.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3633 : plan3633.Valid := valid_step _ _ _ valid1674 (by decide +kernel)






























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











theorem valid6054 : plan6054.Valid := valid_step _ _ _ valid3538 (by decide +kernel)

























































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

















theorem valid6113 : plan6113.Valid := valid_step _ _ _ valid3565 (by decide +kernel)



















theorem valid6123 : plan6123.Valid := valid_step _ _ _ valid3574 (by decide +kernel)





theorem valid6126 : plan6126.Valid := valid_step _ _ _ valid3577 (by decide +kernel)

theorem valid6127 : plan6127.Valid := valid_step _ _ _ valid3578 (by decide +kernel)







theorem valid6131 : plan6131.Valid := valid_step _ _ _ valid3598 (by decide +kernel)























theorem valid6143 : plan6143.Valid := valid_step _ _ _ valid3591 (by decide +kernel)


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







































theorem valid7700 : plan7700.Valid := valid_step _ _ _ valid5951 (by decide +kernel)

theorem valid7701 : plan7701.Valid := valid_step _ _ _ valid5952 (by decide +kernel)

theorem valid7702 : plan7702.Valid := valid_step _ _ _ valid5953 (by decide +kernel)

theorem valid7703 : plan7703.Valid := valid_step _ _ _ valid5961 (by decide +kernel)


















































































































































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























































































































































theorem valid8044 : plan8044.Valid := valid_step _ _ _ valid6083 (by decide +kernel)

theorem valid8045 : plan8045.Valid := valid_step _ _ _ valid6084 (by decide +kernel)

theorem valid8046 : plan8046.Valid := valid_step _ _ _ valid6085 (by decide +kernel)

theorem valid8047 : plan8047.Valid := valid_step _ _ _ valid6086 (by decide +kernel)

theorem valid8048 : plan8048.Valid := valid_step _ _ _ valid6087 (by decide +kernel)

theorem valid8049 : plan8049.Valid := valid_step _ _ _ valid6088 (by decide +kernel)

theorem valid8050 : plan8050.Valid := valid_step _ _ _ valid6089 (by decide +kernel)

theorem valid8051 : plan8051.Valid := valid_step _ _ _ valid6090 (by decide +kernel)

theorem valid8052 : plan8052.Valid := valid_step _ _ _ valid6091 (by decide +kernel)

theorem valid8053 : plan8053.Valid := valid_step _ _ _ valid6092 (by decide +kernel)

theorem valid8054 : plan8054.Valid := valid_step _ _ _ valid6093 (by decide +kernel)

theorem valid8055 : plan8055.Valid := valid_step _ _ _ valid6094 (by decide +kernel)

theorem valid8056 : plan8056.Valid := valid_step _ _ _ valid6095 (by decide +kernel)

theorem valid8057 : plan8057.Valid := valid_step _ _ _ valid6096 (by decide +kernel)

theorem valid8058 : plan8058.Valid := valid_step _ _ _ valid6097 (by decide +kernel)

theorem valid8059 : plan8059.Valid := valid_step _ _ _ valid6098 (by decide +kernel)

theorem valid8060 : plan8060.Valid := valid_step _ _ _ valid6099 (by decide +kernel)

theorem valid8061 : plan8061.Valid := valid_step _ _ _ valid6100 (by decide +kernel)

theorem valid8062 : plan8062.Valid := valid_step _ _ _ valid6101 (by decide +kernel)

theorem valid8063 : plan8063.Valid := valid_step _ _ _ valid6102 (by decide +kernel)

theorem valid8064 : plan8064.Valid := valid_step _ _ _ valid6103 (by decide +kernel)
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



theorem valid6146 : plan6146.Valid := valid_step _ _ _ valid3594 (by decide +kernel)







theorem valid6150 : plan6150.Valid := valid_step _ _ _ valid3598 (by decide +kernel)

theorem valid6151 : plan6151.Valid := valid_step _ _ _ valid3599 (by decide +kernel)































theorem valid6167 : plan6167.Valid := valid_step _ _ _ valid3616 (by decide +kernel)











theorem valid6173 : plan6173.Valid := valid_step _ _ _ valid3616 (by decide +kernel)















theorem valid6181 : plan6181.Valid := valid_step _ _ _ valid3612 (by decide +kernel)







theorem valid6185 : plan6185.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6186 : plan6186.Valid := valid_step _ _ _ valid3617 (by decide +kernel)







theorem valid6190 : plan6190.Valid := valid_step _ _ _ valid3616 (by decide +kernel)





theorem valid6193 : plan6193.Valid := valid_step _ _ _ valid3616 (by decide +kernel)



theorem valid6195 : plan6195.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6196 : plan6196.Valid := valid_step _ _ _ valid3617 (by decide +kernel)







































theorem valid6216 : plan6216.Valid := valid_step _ _ _ valid3628 (by decide +kernel)







theorem valid6220 : plan6220.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6221 : plan6221.Valid := valid_step _ _ _ valid3633 (by decide +kernel)







theorem valid6225 : plan6225.Valid := valid_step _ _ _ valid3632 (by decide +kernel)









theorem valid6230 : plan6230.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6231 : plan6231.Valid := valid_step _ _ _ valid3633 (by decide +kernel)


















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

theorem valid8065 : plan8065.Valid := valid_step _ _ _ valid6104 (by decide +kernel)

theorem valid8066 : plan8066.Valid := valid_step _ _ _ valid6054 (by decide +kernel)

theorem valid8067 : plan8067.Valid := valid_step _ _ _ valid6100 (by decide +kernel)

theorem valid8068 : plan8068.Valid := valid_step _ _ _ valid6101 (by decide +kernel)

theorem valid8069 : plan8069.Valid := valid_step _ _ _ valid6102 (by decide +kernel)

theorem valid8070 : plan8070.Valid := valid_step _ _ _ valid6103 (by decide +kernel)

theorem valid8071 : plan8071.Valid := valid_step _ _ _ valid6104 (by decide +kernel)



















theorem valid8081 : plan8081.Valid := valid_step _ _ _ valid6113 (by decide +kernel)









theorem valid8086 : plan8086.Valid := valid_step _ _ _ valid6126 (by decide +kernel)















theorem valid8094 : plan8094.Valid := valid_step _ _ _ valid6123 (by decide +kernel)





theorem valid8097 : plan8097.Valid := valid_step _ _ _ valid6126 (by decide +kernel)

theorem valid8098 : plan8098.Valid := valid_step _ _ _ valid6127 (by decide +kernel)









theorem valid8103 : plan8103.Valid := valid_step _ _ _ valid6150 (by decide +kernel)



theorem valid8105 : plan8105.Valid := valid_step _ _ _ valid6131 (by decide +kernel)







theorem valid8109 : plan8109.Valid := valid_step _ _ _ valid6146 (by decide +kernel)



theorem valid8111 : plan8111.Valid := valid_step _ _ _ valid6150 (by decide +kernel)

theorem valid8112 : plan8112.Valid := valid_step _ _ _ valid6151 (by decide +kernel)

























theorem valid8125 : plan8125.Valid := valid_step _ _ _ valid6143 (by decide +kernel)





theorem valid8128 : plan8128.Valid := valid_step _ _ _ valid6146 (by decide +kernel)







theorem valid8132 : plan8132.Valid := valid_step _ _ _ valid6150 (by decide +kernel)

theorem valid8133 : plan8133.Valid := valid_step _ _ _ valid6151 (by decide +kernel)























theorem valid8145 : plan8145.Valid := valid_step _ _ _ valid6185 (by decide +kernel)

theorem valid8146 : plan8146.Valid := valid_step _ _ _ valid6190 (by decide +kernel)

theorem valid8147 : plan8147.Valid := valid_step _ _ _ valid6195 (by decide +kernel)











theorem valid8153 : plan8153.Valid := valid_step _ _ _ valid6173 (by decide +kernel)





theorem valid8156 : plan8156.Valid := valid_step _ _ _ valid6181 (by decide +kernel)



theorem valid8158 : plan8158.Valid := valid_step _ _ _ valid6185 (by decide +kernel)

theorem valid8159 : plan8159.Valid := valid_step _ _ _ valid6186 (by decide +kernel)


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

































































































































theorem valid8417 : plan8417.Valid := valid_step _ _ _ valid8081 (by decide +kernel)

























theorem valid8430 : plan8430.Valid := valid_step _ _ _ valid8097 (by decide +kernel)

theorem valid8431 : plan8431.Valid := valid_step _ _ _ valid8086 (by decide +kernel)

theorem valid8432 : plan8432.Valid := valid_step _ _ _ valid8094 (by decide +kernel)

theorem valid8433 : plan8433.Valid := valid_step _ _ _ valid8097 (by decide +kernel)

theorem valid8434 : plan8434.Valid := valid_step _ _ _ valid8098 (by decide +kernel)




























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

































theorem valid8465 : plan8465.Valid := valid_step _ _ _ valid8111 (by decide +kernel)

theorem valid8466 : plan8466.Valid := valid_step _ _ _ valid8128 (by decide +kernel)

theorem valid8467 : plan8467.Valid := valid_step _ _ _ valid8132 (by decide +kernel)

theorem valid8468 : plan8468.Valid := valid_step _ _ _ valid8133 (by decide +kernel)

theorem valid8469 : plan8469.Valid := valid_step _ _ _ valid8103 (by decide +kernel)

theorem valid8470 : plan8470.Valid := valid_step _ _ _ valid8105 (by decide +kernel)

theorem valid8471 : plan8471.Valid := valid_step _ _ _ valid8109 (by decide +kernel)

theorem valid8472 : plan8472.Valid := valid_step _ _ _ valid8111 (by decide +kernel)

theorem valid8473 : plan8473.Valid := valid_step _ _ _ valid8112 (by decide +kernel)

theorem valid8474 : plan8474.Valid := valid_step _ _ _ valid8125 (by decide +kernel)












































































































































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

theorem valid8161 : plan8161.Valid := valid_step _ _ _ valid6190 (by decide +kernel)



theorem valid8163 : plan8163.Valid := valid_step _ _ _ valid6193 (by decide +kernel)



theorem valid8165 : plan8165.Valid := valid_step _ _ _ valid6195 (by decide +kernel)

theorem valid8166 : plan8166.Valid := valid_step _ _ _ valid6196 (by decide +kernel)



































theorem valid8184 : plan8184.Valid := valid_step _ _ _ valid6181 (by decide +kernel)







theorem valid8188 : plan8188.Valid := valid_step _ _ _ valid6185 (by decide +kernel)

theorem valid8189 : plan8189.Valid := valid_step _ _ _ valid6186 (by decide +kernel)







theorem valid8193 : plan8193.Valid := valid_step _ _ _ valid6190 (by decide +kernel)

theorem valid8194 : plan8194.Valid := valid_step _ _ _ valid6195 (by decide +kernel)

theorem valid8195 : plan8195.Valid := valid_step _ _ _ valid6196 (by decide +kernel)





















theorem valid8206 : plan8206.Valid := valid_step _ _ _ valid6167 (by decide +kernel)























theorem valid8218 : plan8218.Valid := valid_step _ _ _ valid6167 (by decide +kernel)

























































theorem valid8247 : plan8247.Valid := valid_step _ _ _ valid6225 (by decide +kernel)


















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





theorem valid8547 : plan8547.Valid := valid_step _ _ _ valid8146 (by decide +kernel)

theorem valid8548 : plan8548.Valid := valid_step _ _ _ valid8158 (by decide +kernel)

theorem valid8549 : plan8549.Valid := valid_step _ _ _ valid8161 (by decide +kernel)

theorem valid8550 : plan8550.Valid := valid_step _ _ _ valid8165 (by decide +kernel)

theorem valid8551 : plan8551.Valid := valid_step _ _ _ valid8184 (by decide +kernel)

theorem valid8552 : plan8552.Valid := valid_step _ _ _ valid8188 (by decide +kernel)

theorem valid8553 : plan8553.Valid := valid_step _ _ _ valid8189 (by decide +kernel)

theorem valid8554 : plan8554.Valid := valid_step _ _ _ valid8193 (by decide +kernel)

theorem valid8555 : plan8555.Valid := valid_step _ _ _ valid8194 (by decide +kernel)

theorem valid8556 : plan8556.Valid := valid_step _ _ _ valid8195 (by decide +kernel)

theorem valid8557 : plan8557.Valid := valid_step _ _ _ valid8206 (by decide +kernel)

theorem valid8558 : plan8558.Valid := valid_step _ _ _ valid8218 (by decide +kernel)

theorem valid8559 : plan8559.Valid := valid_step _ _ _ valid8145 (by decide +kernel)

theorem valid8560 : plan8560.Valid := valid_step _ _ _ valid8146 (by decide +kernel)

theorem valid8561 : plan8561.Valid := valid_step _ _ _ valid8147 (by decide +kernel)

theorem valid8562 : plan8562.Valid := valid_step _ _ _ valid8153 (by decide +kernel)

theorem valid8563 : plan8563.Valid := valid_step _ _ _ valid8156 (by decide +kernel)

theorem valid8564 : plan8564.Valid := valid_step _ _ _ valid8158 (by decide +kernel)

theorem valid8565 : plan8565.Valid := valid_step _ _ _ valid8159 (by decide +kernel)

theorem valid8566 : plan8566.Valid := valid_step _ _ _ valid8161 (by decide +kernel)

theorem valid8567 : plan8567.Valid := valid_step _ _ _ valid8163 (by decide +kernel)

theorem valid8568 : plan8568.Valid := valid_step _ _ _ valid8165 (by decide +kernel)

theorem valid8569 : plan8569.Valid := valid_step _ _ _ valid8166 (by decide +kernel)














































































































































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











theorem valid8262 : plan8262.Valid := valid_step _ _ _ valid6220 (by decide +kernel)





theorem valid8265 : plan8265.Valid := valid_step _ _ _ valid6225 (by decide +kernel)









theorem valid8270 : plan8270.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

















theorem valid8279 : plan8279.Valid := valid_step _ _ _ valid6216 (by decide +kernel)







theorem valid8283 : plan8283.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8284 : plan8284.Valid := valid_step _ _ _ valid6221 (by decide +kernel)







theorem valid8288 : plan8288.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8289 : plan8289.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8290 : plan8290.Valid := valid_step _ _ _ valid6231 (by decide +kernel)







theorem valid8294 : plan8294.Valid := valid_step _ _ _ valid6225 (by decide +kernel)





theorem valid8297 : plan8297.Valid := valid_step _ _ _ valid6225 (by decide +kernel)





















theorem valid8308 : plan8308.Valid := valid_step _ _ _ valid6220 (by decide +kernel)





theorem valid8311 : plan8311.Valid := valid_step _ _ _ valid6225 (by decide +kernel)









theorem valid8316 : plan8316.Valid := valid_step _ _ _ valid6230 (by decide +kernel)





theorem valid8319 : plan8319.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8320 : plan8320.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8321 : plan8321.Valid := valid_step _ _ _ valid6231 (by decide +kernel)






























































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







































































































































theorem valid8708 : plan8708.Valid := valid_step _ _ _ valid8247 (by decide +kernel)

theorem valid8709 : plan8709.Valid := valid_step _ _ _ valid8262 (by decide +kernel)

theorem valid8710 : plan8710.Valid := valid_step _ _ _ valid8265 (by decide +kernel)

theorem valid8711 : plan8711.Valid := valid_step _ _ _ valid8270 (by decide +kernel)

theorem valid8712 : plan8712.Valid := valid_step _ _ _ valid8279 (by decide +kernel)

theorem valid8713 : plan8713.Valid := valid_step _ _ _ valid8283 (by decide +kernel)

theorem valid8714 : plan8714.Valid := valid_step _ _ _ valid8284 (by decide +kernel)

theorem valid8715 : plan8715.Valid := valid_step _ _ _ valid8288 (by decide +kernel)

theorem valid8716 : plan8716.Valid := valid_step _ _ _ valid8289 (by decide +kernel)

theorem valid8717 : plan8717.Valid := valid_step _ _ _ valid8290 (by decide +kernel)

theorem valid8718 : plan8718.Valid := valid_step _ _ _ valid8294 (by decide +kernel)

theorem valid8719 : plan8719.Valid := valid_step _ _ _ valid8297 (by decide +kernel)

theorem valid8720 : plan8720.Valid := valid_step _ _ _ valid8308 (by decide +kernel)

theorem valid8721 : plan8721.Valid := valid_step _ _ _ valid8311 (by decide +kernel)

theorem valid8722 : plan8722.Valid := valid_step _ _ _ valid8316 (by decide +kernel)

theorem valid8723 : plan8723.Valid := valid_step _ _ _ valid8319 (by decide +kernel)

theorem valid8724 : plan8724.Valid := valid_step _ _ _ valid8320 (by decide +kernel)

theorem valid8725 : plan8725.Valid := valid_step _ _ _ valid8321 (by decide +kernel)






















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
theorem t6_1764choices : plan7700.choices=[9,9,9,3,7,7].map (options 6 5) := by rfl


theorem t6_1764part0 : t6_1764jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1764frontier : t6_1764root.frontier 0=t6_1764jobs := by rfl
theorem t6_1764all : t6_1764jobs.all (Job.check tree)=true := by
  simp only [t6_1764jobs,List.all_append,List.all_nil,t6_1764part0,Bool.and_self]
theorem t6_1764checked : Checked tree [9,9,9,3,7,7] := by
  refine ⟨plan7700,valid7700,t6_1764choices,?_⟩
  exact check_of_frontier tree 0 t6_1764root t6_1764jobs t6_1764frontier t6_1764all
theorem t6_1765choices : plan7701.choices=[9,9,9,3,10,7].map (options 6 5) := by rfl


theorem t6_1765part0 : t6_1765jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1765frontier : t6_1765root.frontier 0=t6_1765jobs := by rfl
theorem t6_1765all : t6_1765jobs.all (Job.check tree)=true := by
  simp only [t6_1765jobs,List.all_append,List.all_nil,t6_1765part0,Bool.and_self]
theorem t6_1765checked : Checked tree [9,9,9,3,10,7] := by
  refine ⟨plan7701,valid7701,t6_1765choices,?_⟩
  exact check_of_frontier tree 0 t6_1765root t6_1765jobs t6_1765frontier t6_1765all
theorem t6_1766choices : plan7702.choices=[9,9,9,3,10,10].map (options 6 5) := by rfl


theorem t6_1766part0 : t6_1766jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1766frontier : t6_1766root.frontier 0=t6_1766jobs := by rfl
theorem t6_1766all : t6_1766jobs.all (Job.check tree)=true := by
  simp only [t6_1766jobs,List.all_append,List.all_nil,t6_1766part0,Bool.and_self]
theorem t6_1766checked : Checked tree [9,9,9,3,10,10] := by
  refine ⟨plan7702,valid7702,t6_1766choices,?_⟩
  exact check_of_frontier tree 0 t6_1766root t6_1766jobs t6_1766frontier t6_1766all
theorem t6_1767choices : plan8044.choices=[9,9,9,6,6,6].map (options 6 6) := by rfl


theorem t6_1767part0 : t6_1767jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1767frontier : t6_1767root.frontier 0=t6_1767jobs := by rfl
theorem t6_1767all : t6_1767jobs.all (Job.check tree)=true := by
  simp only [t6_1767jobs,List.all_append,List.all_nil,t6_1767part0,Bool.and_self]
theorem t6_1767checked : Checked tree [9,9,9,6,6,6] := by
  refine ⟨plan8044,valid8044,t6_1767choices,?_⟩
  exact check_of_frontier tree 0 t6_1767root t6_1767jobs t6_1767frontier t6_1767all
theorem t6_1768choices : plan8045.choices=[9,9,9,6,6,7].map (options 6 6) := by rfl


theorem t6_1768part0 : t6_1768jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1768frontier : t6_1768root.frontier 0=t6_1768jobs := by rfl
theorem t6_1768all : t6_1768jobs.all (Job.check tree)=true := by
  simp only [t6_1768jobs,List.all_append,List.all_nil,t6_1768part0,Bool.and_self]
theorem t6_1768checked : Checked tree [9,9,9,6,6,7] := by
  refine ⟨plan8045,valid8045,t6_1768choices,?_⟩
  exact check_of_frontier tree 0 t6_1768root t6_1768jobs t6_1768frontier t6_1768all
theorem t6_1769choices : plan8046.choices=[9,9,9,6,6,10].map (options 6 6) := by rfl


theorem t6_1769part0 : t6_1769jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1769frontier : t6_1769root.frontier 0=t6_1769jobs := by rfl
theorem t6_1769all : t6_1769jobs.all (Job.check tree)=true := by
  simp only [t6_1769jobs,List.all_append,List.all_nil,t6_1769part0,Bool.and_self]
theorem t6_1769checked : Checked tree [9,9,9,6,6,10] := by
  refine ⟨plan8046,valid8046,t6_1769choices,?_⟩
  exact check_of_frontier tree 0 t6_1769root t6_1769jobs t6_1769frontier t6_1769all
theorem t6_1770choices : plan8047.choices=[9,9,9,6,7,7].map (options 6 6) := by rfl


theorem t6_1770part0 : t6_1770jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1770frontier : t6_1770root.frontier 0=t6_1770jobs := by rfl
theorem t6_1770all : t6_1770jobs.all (Job.check tree)=true := by
  simp only [t6_1770jobs,List.all_append,List.all_nil,t6_1770part0,Bool.and_self]
theorem t6_1770checked : Checked tree [9,9,9,6,7,7] := by
  refine ⟨plan8047,valid8047,t6_1770choices,?_⟩
  exact check_of_frontier tree 0 t6_1770root t6_1770jobs t6_1770frontier t6_1770all
theorem t6_1771choices : plan8048.choices=[9,9,9,6,10,7].map (options 6 6) := by rfl


theorem t6_1771part0 : t6_1771jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1771frontier : t6_1771root.frontier 0=t6_1771jobs := by rfl
theorem t6_1771all : t6_1771jobs.all (Job.check tree)=true := by
  simp only [t6_1771jobs,List.all_append,List.all_nil,t6_1771part0,Bool.and_self]
theorem t6_1771checked : Checked tree [9,9,9,6,10,7] := by
  refine ⟨plan8048,valid8048,t6_1771choices,?_⟩
  exact check_of_frontier tree 0 t6_1771root t6_1771jobs t6_1771frontier t6_1771all
theorem t6_1772choices : plan8049.choices=[9,9,9,6,10,10].map (options 6 6) := by rfl


theorem t6_1772part0 : t6_1772jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1772frontier : t6_1772root.frontier 0=t6_1772jobs := by rfl
theorem t6_1772all : t6_1772jobs.all (Job.check tree)=true := by
  simp only [t6_1772jobs,List.all_append,List.all_nil,t6_1772part0,Bool.and_self]
theorem t6_1772checked : Checked tree [9,9,9,6,10,10] := by
  refine ⟨plan8049,valid8049,t6_1772choices,?_⟩
  exact check_of_frontier tree 0 t6_1772root t6_1772jobs t6_1772frontier t6_1772all
theorem t6_1773choices : plan8050.choices=[9,9,9,7,7,7].map (options 6 6) := by rfl


theorem t6_1773part0 : t6_1773jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1773frontier : t6_1773root.frontier 0=t6_1773jobs := by rfl
theorem t6_1773all : t6_1773jobs.all (Job.check tree)=true := by
  simp only [t6_1773jobs,List.all_append,List.all_nil,t6_1773part0,Bool.and_self]
theorem t6_1773checked : Checked tree [9,9,9,7,7,7] := by
  refine ⟨plan8050,valid8050,t6_1773choices,?_⟩
  exact check_of_frontier tree 0 t6_1773root t6_1773jobs t6_1773frontier t6_1773all
theorem t6_1774choices : plan7703.choices=[9,9,9,9,3,7].map (options 6 5) := by rfl


theorem t6_1774part0 : t6_1774jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1774frontier : t6_1774root.frontier 0=t6_1774jobs := by rfl
theorem t6_1774all : t6_1774jobs.all (Job.check tree)=true := by
  simp only [t6_1774jobs,List.all_append,List.all_nil,t6_1774part0,Bool.and_self]
theorem t6_1774checked : Checked tree [9,9,9,9,3,7] := by
  refine ⟨plan7703,valid7703,t6_1774choices,?_⟩
  exact check_of_frontier tree 0 t6_1774root t6_1774jobs t6_1774frontier t6_1774all
theorem t6_1775choices : plan8051.choices=[9,9,9,9,6,7].map (options 6 6) := by rfl


theorem t6_1775part0 : t6_1775jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1775frontier : t6_1775root.frontier 0=t6_1775jobs := by rfl
theorem t6_1775all : t6_1775jobs.all (Job.check tree)=true := by
  simp only [t6_1775jobs,List.all_append,List.all_nil,t6_1775part0,Bool.and_self]
theorem t6_1775checked : Checked tree [9,9,9,9,6,7] := by
  refine ⟨plan8051,valid8051,t6_1775choices,?_⟩
  exact check_of_frontier tree 0 t6_1775root t6_1775jobs t6_1775frontier t6_1775all
theorem t6_1776choices : plan8052.choices=[9,9,9,9,7,7].map (options 6 6) := by rfl


theorem t6_1776part0 : t6_1776jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1776frontier : t6_1776root.frontier 0=t6_1776jobs := by rfl
theorem t6_1776all : t6_1776jobs.all (Job.check tree)=true := by
  simp only [t6_1776jobs,List.all_append,List.all_nil,t6_1776part0,Bool.and_self]
theorem t6_1776checked : Checked tree [9,9,9,9,7,7] := by
  refine ⟨plan8052,valid8052,t6_1776choices,?_⟩
  exact check_of_frontier tree 0 t6_1776root t6_1776jobs t6_1776frontier t6_1776all
theorem t6_1777choices : plan8053.choices=[9,9,9,9,10,7].map (options 6 6) := by rfl


theorem t6_1777part0 : t6_1777jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1777frontier : t6_1777root.frontier 0=t6_1777jobs := by rfl
theorem t6_1777all : t6_1777jobs.all (Job.check tree)=true := by
  simp only [t6_1777jobs,List.all_append,List.all_nil,t6_1777part0,Bool.and_self]
theorem t6_1777checked : Checked tree [9,9,9,9,10,7] := by
  refine ⟨plan8053,valid8053,t6_1777choices,?_⟩
  exact check_of_frontier tree 0 t6_1777root t6_1777jobs t6_1777frontier t6_1777all
theorem t6_1778choices : plan8054.choices=[9,9,9,10,7,7].map (options 6 6) := by rfl


theorem t6_1778part0 : t6_1778jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1778frontier : t6_1778root.frontier 0=t6_1778jobs := by rfl
theorem t6_1778all : t6_1778jobs.all (Job.check tree)=true := by
  simp only [t6_1778jobs,List.all_append,List.all_nil,t6_1778part0,Bool.and_self]
theorem t6_1778checked : Checked tree [9,9,9,10,7,7] := by
  refine ⟨plan8054,valid8054,t6_1778choices,?_⟩
  exact check_of_frontier tree 0 t6_1778root t6_1778jobs t6_1778frontier t6_1778all
theorem t6_1779choices : plan8055.choices=[9,9,9,10,10,7].map (options 6 6) := by rfl


theorem t6_1779part0 : t6_1779jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1779frontier : t6_1779root.frontier 0=t6_1779jobs := by rfl
theorem t6_1779all : t6_1779jobs.all (Job.check tree)=true := by
  simp only [t6_1779jobs,List.all_append,List.all_nil,t6_1779part0,Bool.and_self]
theorem t6_1779checked : Checked tree [9,9,9,10,10,7] := by
  refine ⟨plan8055,valid8055,t6_1779choices,?_⟩
  exact check_of_frontier tree 0 t6_1779root t6_1779jobs t6_1779frontier t6_1779all
theorem t6_1780choices : plan8056.choices=[9,9,9,10,10,10].map (options 6 6) := by rfl


theorem t6_1780part0 : t6_1780jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1780frontier : t6_1780root.frontier 0=t6_1780jobs := by rfl
theorem t6_1780all : t6_1780jobs.all (Job.check tree)=true := by
  simp only [t6_1780jobs,List.all_append,List.all_nil,t6_1780part0,Bool.and_self]
theorem t6_1780checked : Checked tree [9,9,9,10,10,10] := by
  refine ⟨plan8056,valid8056,t6_1780choices,?_⟩
  exact check_of_frontier tree 0 t6_1780root t6_1780jobs t6_1780frontier t6_1780all
theorem t6_1781choices : plan8057.choices=[9,9,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1781part0 : t6_1781jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1781frontier : t6_1781root.frontier 0=t6_1781jobs := by rfl
theorem t6_1781all : t6_1781jobs.all (Job.check tree)=true := by
  simp only [t6_1781jobs,List.all_append,List.all_nil,t6_1781part0,Bool.and_self]
theorem t6_1781checked : Checked tree [9,9,10,7,7,7] := by
  refine ⟨plan8057,valid8057,t6_1781choices,?_⟩
  exact check_of_frontier tree 0 t6_1781root t6_1781jobs t6_1781frontier t6_1781all
theorem t6_1782choices : plan8058.choices=[9,9,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1782part0 : t6_1782jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1782frontier : t6_1782root.frontier 0=t6_1782jobs := by rfl
theorem t6_1782all : t6_1782jobs.all (Job.check tree)=true := by
  simp only [t6_1782jobs,List.all_append,List.all_nil,t6_1782part0,Bool.and_self]
theorem t6_1782checked : Checked tree [9,9,10,10,7,7] := by
  refine ⟨plan8058,valid8058,t6_1782choices,?_⟩
  exact check_of_frontier tree 0 t6_1782root t6_1782jobs t6_1782frontier t6_1782all
theorem t6_1783choices : plan8059.choices=[9,9,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1783part0 : t6_1783jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1783frontier : t6_1783root.frontier 0=t6_1783jobs := by rfl
theorem t6_1783all : t6_1783jobs.all (Job.check tree)=true := by
  simp only [t6_1783jobs,List.all_append,List.all_nil,t6_1783part0,Bool.and_self]
theorem t6_1783checked : Checked tree [9,9,10,10,10,7] := by
  refine ⟨plan8059,valid8059,t6_1783choices,?_⟩
  exact check_of_frontier tree 0 t6_1783root t6_1783jobs t6_1783frontier t6_1783all
theorem t6_1784choices : plan8060.choices=[9,9,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1784part0 : t6_1784jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1784frontier : t6_1784root.frontier 0=t6_1784jobs := by rfl
theorem t6_1784all : t6_1784jobs.all (Job.check tree)=true := by
  simp only [t6_1784jobs,List.all_append,List.all_nil,t6_1784part0,Bool.and_self]
theorem t6_1784checked : Checked tree [9,9,10,10,10,10] := by
  refine ⟨plan8060,valid8060,t6_1784choices,?_⟩
  exact check_of_frontier tree 0 t6_1784root t6_1784jobs t6_1784frontier t6_1784all
theorem t6_1785choices : plan8061.choices=[9,10,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1785part0 : t6_1785jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1785frontier : t6_1785root.frontier 0=t6_1785jobs := by rfl
theorem t6_1785all : t6_1785jobs.all (Job.check tree)=true := by
  simp only [t6_1785jobs,List.all_append,List.all_nil,t6_1785part0,Bool.and_self]
theorem t6_1785checked : Checked tree [9,10,7,7,7,7] := by
  refine ⟨plan8061,valid8061,t6_1785choices,?_⟩
  exact check_of_frontier tree 0 t6_1785root t6_1785jobs t6_1785frontier t6_1785all
theorem t6_1786choices : plan8062.choices=[9,10,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1786part0 : t6_1786jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1786frontier : t6_1786root.frontier 0=t6_1786jobs := by rfl
theorem t6_1786all : t6_1786jobs.all (Job.check tree)=true := by
  simp only [t6_1786jobs,List.all_append,List.all_nil,t6_1786part0,Bool.and_self]
theorem t6_1786checked : Checked tree [9,10,10,7,7,7] := by
  refine ⟨plan8062,valid8062,t6_1786choices,?_⟩
  exact check_of_frontier tree 0 t6_1786root t6_1786jobs t6_1786frontier t6_1786all
theorem t6_1787choices : plan8063.choices=[9,10,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1787part0 : t6_1787jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1787frontier : t6_1787root.frontier 0=t6_1787jobs := by rfl
theorem t6_1787all : t6_1787jobs.all (Job.check tree)=true := by
  simp only [t6_1787jobs,List.all_append,List.all_nil,t6_1787part0,Bool.and_self]
theorem t6_1787checked : Checked tree [9,10,10,10,7,7] := by
  refine ⟨plan8063,valid8063,t6_1787choices,?_⟩
  exact check_of_frontier tree 0 t6_1787root t6_1787jobs t6_1787frontier t6_1787all
theorem t6_1788choices : plan8064.choices=[9,10,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1788part0 : t6_1788jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1788frontier : t6_1788root.frontier 0=t6_1788jobs := by rfl
theorem t6_1788all : t6_1788jobs.all (Job.check tree)=true := by
  simp only [t6_1788jobs,List.all_append,List.all_nil,t6_1788part0,Bool.and_self]
theorem t6_1788checked : Checked tree [9,10,10,10,10,7] := by
  refine ⟨plan8064,valid8064,t6_1788choices,?_⟩
  exact check_of_frontier tree 0 t6_1788root t6_1788jobs t6_1788frontier t6_1788all
theorem t6_1789choices : plan8065.choices=[9,10,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1789part0 : t6_1789jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1789frontier : t6_1789root.frontier 0=t6_1789jobs := by rfl
theorem t6_1789all : t6_1789jobs.all (Job.check tree)=true := by
  simp only [t6_1789jobs,List.all_append,List.all_nil,t6_1789part0,Bool.and_self]
theorem t6_1789checked : Checked tree [9,10,10,10,10,10] := by
  refine ⟨plan8065,valid8065,t6_1789choices,?_⟩
  exact check_of_frontier tree 0 t6_1789root t6_1789jobs t6_1789frontier t6_1789all
theorem t6_1790choices : plan8066.choices=[10,7,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1790part0 : t6_1790jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1790frontier : t6_1790root.frontier 0=t6_1790jobs := by rfl
theorem t6_1790all : t6_1790jobs.all (Job.check tree)=true := by
  simp only [t6_1790jobs,List.all_append,List.all_nil,t6_1790part0,Bool.and_self]
theorem t6_1790checked : Checked tree [10,7,7,7,7,7] := by
  refine ⟨plan8066,valid8066,t6_1790choices,?_⟩
  exact check_of_frontier tree 0 t6_1790root t6_1790jobs t6_1790frontier t6_1790all
theorem t6_1791choices : plan8067.choices=[10,10,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1791part0 : t6_1791jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1791frontier : t6_1791root.frontier 0=t6_1791jobs := by rfl
theorem t6_1791all : t6_1791jobs.all (Job.check tree)=true := by
  simp only [t6_1791jobs,List.all_append,List.all_nil,t6_1791part0,Bool.and_self]
theorem t6_1791checked : Checked tree [10,10,7,7,7,7] := by
  refine ⟨plan8067,valid8067,t6_1791choices,?_⟩
  exact check_of_frontier tree 0 t6_1791root t6_1791jobs t6_1791frontier t6_1791all
theorem t6_1792choices : plan8068.choices=[10,10,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1792part0 : t6_1792jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1792frontier : t6_1792root.frontier 0=t6_1792jobs := by rfl
theorem t6_1792all : t6_1792jobs.all (Job.check tree)=true := by
  simp only [t6_1792jobs,List.all_append,List.all_nil,t6_1792part0,Bool.and_self]
theorem t6_1792checked : Checked tree [10,10,10,7,7,7] := by
  refine ⟨plan8068,valid8068,t6_1792choices,?_⟩
  exact check_of_frontier tree 0 t6_1792root t6_1792jobs t6_1792frontier t6_1792all
theorem t6_1793choices : plan8069.choices=[10,10,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1793part0 : t6_1793jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1793frontier : t6_1793root.frontier 0=t6_1793jobs := by rfl
theorem t6_1793all : t6_1793jobs.all (Job.check tree)=true := by
  simp only [t6_1793jobs,List.all_append,List.all_nil,t6_1793part0,Bool.and_self]
theorem t6_1793checked : Checked tree [10,10,10,10,7,7] := by
  refine ⟨plan8069,valid8069,t6_1793choices,?_⟩
  exact check_of_frontier tree 0 t6_1793root t6_1793jobs t6_1793frontier t6_1793all
theorem t6_1794choices : plan8070.choices=[10,10,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1794part0 : t6_1794jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1794frontier : t6_1794root.frontier 0=t6_1794jobs := by rfl
theorem t6_1794all : t6_1794jobs.all (Job.check tree)=true := by
  simp only [t6_1794jobs,List.all_append,List.all_nil,t6_1794part0,Bool.and_self]
theorem t6_1794checked : Checked tree [10,10,10,10,10,7] := by
  refine ⟨plan8070,valid8070,t6_1794choices,?_⟩
  exact check_of_frontier tree 0 t6_1794root t6_1794jobs t6_1794frontier t6_1794all
theorem t6_1795choices : plan8071.choices=[10,10,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1795part0 : t6_1795jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1795frontier : t6_1795root.frontier 0=t6_1795jobs := by rfl
theorem t6_1795all : t6_1795jobs.all (Job.check tree)=true := by
  simp only [t6_1795jobs,List.all_append,List.all_nil,t6_1795part0,Bool.and_self]
theorem t6_1795checked : Checked tree [10,10,10,10,10,10] := by
  refine ⟨plan8071,valid8071,t6_1795choices,?_⟩
  exact check_of_frontier tree 0 t6_1795root t6_1795jobs t6_1795frontier t6_1795all
theorem t7_0choices : plan8547.choices=[0,1,7,7,7,7,7].map (options 7 5) := by rfl


theorem t7_0part0 : t7_0jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_0frontier : t7_0root.frontier 0=t7_0jobs := by rfl
theorem t7_0all : t7_0jobs.all (Job.check tree)=true := by
  simp only [t7_0jobs,List.all_append,List.all_nil,t7_0part0,Bool.and_self]
theorem t7_0checked : Checked tree [0,1,7,7,7,7,7] := by
  refine ⟨plan8547,valid8547,t7_0choices,?_⟩
  exact check_of_frontier tree 0 t7_0root t7_0jobs t7_0frontier t7_0all
theorem t7_1choices : plan8465.choices=[0,2,3,7,7,7,7].map (options 7 4) := by rfl


theorem t7_1part0 : t7_1jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_1frontier : t7_1root.frontier 0=t7_1jobs := by rfl
theorem t7_1all : t7_1jobs.all (Job.check tree)=true := by
  simp only [t7_1jobs,List.all_append,List.all_nil,t7_1part0,Bool.and_self]
theorem t7_1checked : Checked tree [0,2,3,7,7,7,7] := by
  refine ⟨plan8465,valid8465,t7_1choices,?_⟩
  exact check_of_frontier tree 0 t7_1root t7_1jobs t7_1frontier t7_1all
theorem t7_2choices : plan8548.choices=[0,2,6,7,7,7,7].map (options 7 5) := by rfl


theorem t7_2part0 : t7_2jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_2frontier : t7_2root.frontier 0=t7_2jobs := by rfl
theorem t7_2all : t7_2jobs.all (Job.check tree)=true := by
  simp only [t7_2jobs,List.all_append,List.all_nil,t7_2part0,Bool.and_self]
theorem t7_2checked : Checked tree [0,2,6,7,7,7,7] := by
  refine ⟨plan8548,valid8548,t7_2choices,?_⟩
  exact check_of_frontier tree 0 t7_2root t7_2jobs t7_2frontier t7_2all
theorem t7_3choices : plan8549.choices=[0,2,7,7,7,7,7].map (options 7 5) := by rfl


theorem t7_3part0 : t7_3jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_3frontier : t7_3root.frontier 0=t7_3jobs := by rfl
theorem t7_3all : t7_3jobs.all (Job.check tree)=true := by
  simp only [t7_3jobs,List.all_append,List.all_nil,t7_3part0,Bool.and_self]
theorem t7_3checked : Checked tree [0,2,7,7,7,7,7] := by
  refine ⟨plan8549,valid8549,t7_3choices,?_⟩
  exact check_of_frontier tree 0 t7_3root t7_3jobs t7_3frontier t7_3all
theorem t7_4choices : plan8550.choices=[0,2,10,7,7,7,7].map (options 7 5) := by rfl


theorem t7_4part0 : t7_4jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_4frontier : t7_4root.frontier 0=t7_4jobs := by rfl
theorem t7_4all : t7_4jobs.all (Job.check tree)=true := by
  simp only [t7_4jobs,List.all_append,List.all_nil,t7_4part0,Bool.and_self]
theorem t7_4checked : Checked tree [0,2,10,7,7,7,7] := by
  refine ⟨plan8550,valid8550,t7_4choices,?_⟩
  exact check_of_frontier tree 0 t7_4root t7_4jobs t7_4frontier t7_4all
theorem t7_5choices : plan8430.choices=[0,3,3,3,7,7,7].map (options 7 3) := by rfl


theorem t7_5part0 : t7_5jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_5frontier : t7_5root.frontier 0=t7_5jobs := by rfl
theorem t7_5all : t7_5jobs.all (Job.check tree)=true := by
  simp only [t7_5jobs,List.all_append,List.all_nil,t7_5part0,Bool.and_self]
theorem t7_5checked : Checked tree [0,3,3,3,7,7,7] := by
  refine ⟨plan8430,valid8430,t7_5choices,?_⟩
  exact check_of_frontier tree 0 t7_5root t7_5jobs t7_5frontier t7_5all
theorem t7_6choices : plan8466.choices=[0,3,3,6,7,7,7].map (options 7 4) := by rfl


theorem t7_6part0 : t7_6jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_6frontier : t7_6root.frontier 0=t7_6jobs := by rfl
theorem t7_6all : t7_6jobs.all (Job.check tree)=true := by
  simp only [t7_6jobs,List.all_append,List.all_nil,t7_6part0,Bool.and_self]
theorem t7_6checked : Checked tree [0,3,3,6,7,7,7] := by
  refine ⟨plan8466,valid8466,t7_6choices,?_⟩
  exact check_of_frontier tree 0 t7_6root t7_6jobs t7_6frontier t7_6all
theorem t7_7choices : plan8467.choices=[0,3,3,7,7,7,7].map (options 7 4) := by rfl


theorem t7_7part0 : t7_7jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_7frontier : t7_7root.frontier 0=t7_7jobs := by rfl
theorem t7_7all : t7_7jobs.all (Job.check tree)=true := by
  simp only [t7_7jobs,List.all_append,List.all_nil,t7_7part0,Bool.and_self]
theorem t7_7checked : Checked tree [0,3,3,7,7,7,7] := by
  refine ⟨plan8467,valid8467,t7_7choices,?_⟩
  exact check_of_frontier tree 0 t7_7root t7_7jobs t7_7frontier t7_7all
theorem t7_8choices : plan8468.choices=[0,3,3,10,7,7,7].map (options 7 4) := by rfl


theorem t7_8part0 : t7_8jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_8frontier : t7_8root.frontier 0=t7_8jobs := by rfl
theorem t7_8all : t7_8jobs.all (Job.check tree)=true := by
  simp only [t7_8jobs,List.all_append,List.all_nil,t7_8part0,Bool.and_self]
theorem t7_8checked : Checked tree [0,3,3,10,7,7,7] := by
  refine ⟨plan8468,valid8468,t7_8choices,?_⟩
  exact check_of_frontier tree 0 t7_8root t7_8jobs t7_8frontier t7_8all
theorem t7_9choices : plan8551.choices=[0,3,6,6,7,7,7].map (options 7 5) := by rfl


theorem t7_9part0 : t7_9jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_9frontier : t7_9root.frontier 0=t7_9jobs := by rfl
theorem t7_9all : t7_9jobs.all (Job.check tree)=true := by
  simp only [t7_9jobs,List.all_append,List.all_nil,t7_9part0,Bool.and_self]
theorem t7_9checked : Checked tree [0,3,6,6,7,7,7] := by
  refine ⟨plan8551,valid8551,t7_9choices,?_⟩
  exact check_of_frontier tree 0 t7_9root t7_9jobs t7_9frontier t7_9all
theorem t7_10choices : plan8552.choices=[0,3,6,7,7,7,7].map (options 7 5) := by rfl


theorem t7_10part0 : t7_10jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_10frontier : t7_10root.frontier 0=t7_10jobs := by rfl
theorem t7_10all : t7_10jobs.all (Job.check tree)=true := by
  simp only [t7_10jobs,List.all_append,List.all_nil,t7_10part0,Bool.and_self]
theorem t7_10checked : Checked tree [0,3,6,7,7,7,7] := by
  refine ⟨plan8552,valid8552,t7_10choices,?_⟩
  exact check_of_frontier tree 0 t7_10root t7_10jobs t7_10frontier t7_10all
theorem t7_11choices : plan8553.choices=[0,3,6,10,7,7,7].map (options 7 5) := by rfl


theorem t7_11part0 : t7_11jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_11frontier : t7_11root.frontier 0=t7_11jobs := by rfl
theorem t7_11all : t7_11jobs.all (Job.check tree)=true := by
  simp only [t7_11jobs,List.all_append,List.all_nil,t7_11part0,Bool.and_self]
theorem t7_11checked : Checked tree [0,3,6,10,7,7,7] := by
  refine ⟨plan8553,valid8553,t7_11choices,?_⟩
  exact check_of_frontier tree 0 t7_11root t7_11jobs t7_11frontier t7_11all
theorem t7_12choices : plan8554.choices=[0,3,7,7,7,7,7].map (options 7 5) := by rfl


theorem t7_12part0 : t7_12jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_12frontier : t7_12root.frontier 0=t7_12jobs := by rfl
theorem t7_12all : t7_12jobs.all (Job.check tree)=true := by
  simp only [t7_12jobs,List.all_append,List.all_nil,t7_12part0,Bool.and_self]
theorem t7_12checked : Checked tree [0,3,7,7,7,7,7] := by
  refine ⟨plan8554,valid8554,t7_12choices,?_⟩
  exact check_of_frontier tree 0 t7_12root t7_12jobs t7_12frontier t7_12all
theorem t7_13choices : plan8555.choices=[0,3,10,7,7,7,7].map (options 7 5) := by rfl


theorem t7_13part0 : t7_13jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_13frontier : t7_13root.frontier 0=t7_13jobs := by rfl
theorem t7_13all : t7_13jobs.all (Job.check tree)=true := by
  simp only [t7_13jobs,List.all_append,List.all_nil,t7_13part0,Bool.and_self]
theorem t7_13checked : Checked tree [0,3,10,7,7,7,7] := by
  refine ⟨plan8555,valid8555,t7_13choices,?_⟩
  exact check_of_frontier tree 0 t7_13root t7_13jobs t7_13frontier t7_13all
theorem t7_14choices : plan8556.choices=[0,3,10,10,7,7,7].map (options 7 5) := by rfl


theorem t7_14part0 : t7_14jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_14frontier : t7_14root.frontier 0=t7_14jobs := by rfl
theorem t7_14all : t7_14jobs.all (Job.check tree)=true := by
  simp only [t7_14jobs,List.all_append,List.all_nil,t7_14part0,Bool.and_self]
theorem t7_14checked : Checked tree [0,3,10,10,7,7,7] := by
  refine ⟨plan8556,valid8556,t7_14choices,?_⟩
  exact check_of_frontier tree 0 t7_14root t7_14jobs t7_14frontier t7_14all
theorem t7_15choices : plan8708.choices=[0,4,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_15part0 : t7_15jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_15frontier : t7_15root.frontier 0=t7_15jobs := by rfl
theorem t7_15all : t7_15jobs.all (Job.check tree)=true := by
  simp only [t7_15jobs,List.all_append,List.all_nil,t7_15part0,Bool.and_self]
theorem t7_15checked : Checked tree [0,4,7,7,7,7,7] := by
  refine ⟨plan8708,valid8708,t7_15choices,?_⟩
  exact check_of_frontier tree 0 t7_15root t7_15jobs t7_15frontier t7_15all
theorem t7_16choices : plan8557.choices=[0,5,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_16part0 : t7_16jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_16frontier : t7_16root.frontier 0=t7_16jobs := by rfl
theorem t7_16all : t7_16jobs.all (Job.check tree)=true := by
  simp only [t7_16jobs,List.all_append,List.all_nil,t7_16part0,Bool.and_self]
theorem t7_16checked : Checked tree [0,5,3,7,7,7,7] := by
  refine ⟨plan8557,valid8557,t7_16choices,?_⟩
  exact check_of_frontier tree 0 t7_16root t7_16jobs t7_16frontier t7_16all
theorem t7_17choices : plan8709.choices=[0,5,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_17part0 : t7_17jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_17frontier : t7_17root.frontier 0=t7_17jobs := by rfl
theorem t7_17all : t7_17jobs.all (Job.check tree)=true := by
  simp only [t7_17jobs,List.all_append,List.all_nil,t7_17part0,Bool.and_self]
theorem t7_17checked : Checked tree [0,5,6,7,7,7,7] := by
  refine ⟨plan8709,valid8709,t7_17choices,?_⟩
  exact check_of_frontier tree 0 t7_17root t7_17jobs t7_17frontier t7_17all
theorem t7_18choices : plan8710.choices=[0,5,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_18part0 : t7_18jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_18frontier : t7_18root.frontier 0=t7_18jobs := by rfl
theorem t7_18all : t7_18jobs.all (Job.check tree)=true := by
  simp only [t7_18jobs,List.all_append,List.all_nil,t7_18part0,Bool.and_self]
theorem t7_18checked : Checked tree [0,5,7,7,7,7,7] := by
  refine ⟨plan8710,valid8710,t7_18choices,?_⟩
  exact check_of_frontier tree 0 t7_18root t7_18jobs t7_18frontier t7_18all
theorem t7_19choices : plan8711.choices=[0,5,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_19part0 : t7_19jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_19frontier : t7_19root.frontier 0=t7_19jobs := by rfl
theorem t7_19all : t7_19jobs.all (Job.check tree)=true := by
  simp only [t7_19jobs,List.all_append,List.all_nil,t7_19part0,Bool.and_self]
theorem t7_19checked : Checked tree [0,5,10,7,7,7,7] := by
  refine ⟨plan8711,valid8711,t7_19choices,?_⟩
  exact check_of_frontier tree 0 t7_19root t7_19jobs t7_19frontier t7_19all
theorem t7_20choices : plan8712.choices=[0,6,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_20part0 : t7_20jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_20frontier : t7_20root.frontier 0=t7_20jobs := by rfl
theorem t7_20all : t7_20jobs.all (Job.check tree)=true := by
  simp only [t7_20jobs,List.all_append,List.all_nil,t7_20part0,Bool.and_self]
theorem t7_20checked : Checked tree [0,6,6,6,7,7,7] := by
  refine ⟨plan8712,valid8712,t7_20choices,?_⟩
  exact check_of_frontier tree 0 t7_20root t7_20jobs t7_20frontier t7_20all
theorem t7_21choices : plan8713.choices=[0,6,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_21part0 : t7_21jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_21frontier : t7_21root.frontier 0=t7_21jobs := by rfl
theorem t7_21all : t7_21jobs.all (Job.check tree)=true := by
  simp only [t7_21jobs,List.all_append,List.all_nil,t7_21part0,Bool.and_self]
theorem t7_21checked : Checked tree [0,6,6,7,7,7,7] := by
  refine ⟨plan8713,valid8713,t7_21choices,?_⟩
  exact check_of_frontier tree 0 t7_21root t7_21jobs t7_21frontier t7_21all
theorem t7_22choices : plan8714.choices=[0,6,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_22part0 : t7_22jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_22frontier : t7_22root.frontier 0=t7_22jobs := by rfl
theorem t7_22all : t7_22jobs.all (Job.check tree)=true := by
  simp only [t7_22jobs,List.all_append,List.all_nil,t7_22part0,Bool.and_self]
theorem t7_22checked : Checked tree [0,6,6,10,7,7,7] := by
  refine ⟨plan8714,valid8714,t7_22choices,?_⟩
  exact check_of_frontier tree 0 t7_22root t7_22jobs t7_22frontier t7_22all
theorem t7_23choices : plan8715.choices=[0,6,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_23part0 : t7_23jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_23frontier : t7_23root.frontier 0=t7_23jobs := by rfl
theorem t7_23all : t7_23jobs.all (Job.check tree)=true := by
  simp only [t7_23jobs,List.all_append,List.all_nil,t7_23part0,Bool.and_self]
theorem t7_23checked : Checked tree [0,6,7,7,7,7,7] := by
  refine ⟨plan8715,valid8715,t7_23choices,?_⟩
  exact check_of_frontier tree 0 t7_23root t7_23jobs t7_23frontier t7_23all
theorem t7_24choices : plan8716.choices=[0,6,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_24part0 : t7_24jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_24frontier : t7_24root.frontier 0=t7_24jobs := by rfl
theorem t7_24all : t7_24jobs.all (Job.check tree)=true := by
  simp only [t7_24jobs,List.all_append,List.all_nil,t7_24part0,Bool.and_self]
theorem t7_24checked : Checked tree [0,6,10,7,7,7,7] := by
  refine ⟨plan8716,valid8716,t7_24choices,?_⟩
  exact check_of_frontier tree 0 t7_24root t7_24jobs t7_24frontier t7_24all
theorem t7_25choices : plan8717.choices=[0,6,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_25part0 : t7_25jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_25frontier : t7_25root.frontier 0=t7_25jobs := by rfl
theorem t7_25all : t7_25jobs.all (Job.check tree)=true := by
  simp only [t7_25jobs,List.all_append,List.all_nil,t7_25part0,Bool.and_self]
theorem t7_25checked : Checked tree [0,6,10,10,7,7,7] := by
  refine ⟨plan8717,valid8717,t7_25choices,?_⟩
  exact check_of_frontier tree 0 t7_25root t7_25jobs t7_25frontier t7_25all
theorem t7_26choices : plan8718.choices=[0,7,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_26part0 : t7_26jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_26frontier : t7_26root.frontier 0=t7_26jobs := by rfl
theorem t7_26all : t7_26jobs.all (Job.check tree)=true := by
  simp only [t7_26jobs,List.all_append,List.all_nil,t7_26part0,Bool.and_self]
theorem t7_26checked : Checked tree [0,7,7,7,7,7,7] := by
  refine ⟨plan8718,valid8718,t7_26choices,?_⟩
  exact check_of_frontier tree 0 t7_26root t7_26jobs t7_26frontier t7_26all
theorem t7_27choices : plan8719.choices=[0,8,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_27part0 : t7_27jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_27frontier : t7_27root.frontier 0=t7_27jobs := by rfl
theorem t7_27all : t7_27jobs.all (Job.check tree)=true := by
  simp only [t7_27jobs,List.all_append,List.all_nil,t7_27part0,Bool.and_self]
theorem t7_27checked : Checked tree [0,8,7,7,7,7,7] := by
  refine ⟨plan8719,valid8719,t7_27choices,?_⟩
  exact check_of_frontier tree 0 t7_27root t7_27jobs t7_27frontier t7_27all
theorem t7_28choices : plan8558.choices=[0,9,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_28part0 : t7_28jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_28frontier : t7_28root.frontier 0=t7_28jobs := by rfl
theorem t7_28all : t7_28jobs.all (Job.check tree)=true := by
  simp only [t7_28jobs,List.all_append,List.all_nil,t7_28part0,Bool.and_self]
theorem t7_28checked : Checked tree [0,9,3,7,7,7,7] := by
  refine ⟨plan8558,valid8558,t7_28choices,?_⟩
  exact check_of_frontier tree 0 t7_28root t7_28jobs t7_28frontier t7_28all
theorem t7_29choices : plan8720.choices=[0,9,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_29part0 : t7_29jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_29frontier : t7_29root.frontier 0=t7_29jobs := by rfl
theorem t7_29all : t7_29jobs.all (Job.check tree)=true := by
  simp only [t7_29jobs,List.all_append,List.all_nil,t7_29part0,Bool.and_self]
theorem t7_29checked : Checked tree [0,9,6,7,7,7,7] := by
  refine ⟨plan8720,valid8720,t7_29choices,?_⟩
  exact check_of_frontier tree 0 t7_29root t7_29jobs t7_29frontier t7_29all
theorem t7_30choices : plan8721.choices=[0,9,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_30part0 : t7_30jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_30frontier : t7_30root.frontier 0=t7_30jobs := by rfl
theorem t7_30all : t7_30jobs.all (Job.check tree)=true := by
  simp only [t7_30jobs,List.all_append,List.all_nil,t7_30part0,Bool.and_self]
theorem t7_30checked : Checked tree [0,9,7,7,7,7,7] := by
  refine ⟨plan8721,valid8721,t7_30choices,?_⟩
  exact check_of_frontier tree 0 t7_30root t7_30jobs t7_30frontier t7_30all
theorem t7_31choices : plan8722.choices=[0,9,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_31part0 : t7_31jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_31frontier : t7_31root.frontier 0=t7_31jobs := by rfl
theorem t7_31all : t7_31jobs.all (Job.check tree)=true := by
  simp only [t7_31jobs,List.all_append,List.all_nil,t7_31part0,Bool.and_self]
theorem t7_31checked : Checked tree [0,9,10,7,7,7,7] := by
  refine ⟨plan8722,valid8722,t7_31choices,?_⟩
  exact check_of_frontier tree 0 t7_31root t7_31jobs t7_31frontier t7_31all
theorem t7_32choices : plan8723.choices=[0,10,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_32part0 : t7_32jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_32frontier : t7_32root.frontier 0=t7_32jobs := by rfl
theorem t7_32all : t7_32jobs.all (Job.check tree)=true := by
  simp only [t7_32jobs,List.all_append,List.all_nil,t7_32part0,Bool.and_self]
theorem t7_32checked : Checked tree [0,10,7,7,7,7,7] := by
  refine ⟨plan8723,valid8723,t7_32choices,?_⟩
  exact check_of_frontier tree 0 t7_32root t7_32jobs t7_32frontier t7_32all
theorem t7_33choices : plan8724.choices=[0,10,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_33part0 : t7_33jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_33frontier : t7_33root.frontier 0=t7_33jobs := by rfl
theorem t7_33all : t7_33jobs.all (Job.check tree)=true := by
  simp only [t7_33jobs,List.all_append,List.all_nil,t7_33part0,Bool.and_self]
theorem t7_33checked : Checked tree [0,10,10,7,7,7,7] := by
  refine ⟨plan8724,valid8724,t7_33choices,?_⟩
  exact check_of_frontier tree 0 t7_33root t7_33jobs t7_33frontier t7_33all
theorem t7_34choices : plan8725.choices=[0,10,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_34part0 : t7_34jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_34frontier : t7_34root.frontier 0=t7_34jobs := by rfl
theorem t7_34all : t7_34jobs.all (Job.check tree)=true := by
  simp only [t7_34jobs,List.all_append,List.all_nil,t7_34part0,Bool.and_self]
theorem t7_34checked : Checked tree [0,10,10,10,7,7,7] := by
  refine ⟨plan8725,valid8725,t7_34choices,?_⟩
  exact check_of_frontier tree 0 t7_34root t7_34jobs t7_34frontier t7_34all
theorem t7_35choices : plan8469.choices=[1,1,3,7,7,7,7].map (options 7 4) := by rfl


theorem t7_35part0 : t7_35jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_35frontier : t7_35root.frontier 0=t7_35jobs := by rfl
theorem t7_35all : t7_35jobs.all (Job.check tree)=true := by
  simp only [t7_35jobs,List.all_append,List.all_nil,t7_35part0,Bool.and_self]
theorem t7_35checked : Checked tree [1,1,3,7,7,7,7] := by
  refine ⟨plan8469,valid8469,t7_35choices,?_⟩
  exact check_of_frontier tree 0 t7_35root t7_35jobs t7_35frontier t7_35all
theorem t7_36choices : plan8559.choices=[1,1,6,7,7,7,7].map (options 7 5) := by rfl


theorem t7_36part0 : t7_36jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_36frontier : t7_36root.frontier 0=t7_36jobs := by rfl
theorem t7_36all : t7_36jobs.all (Job.check tree)=true := by
  simp only [t7_36jobs,List.all_append,List.all_nil,t7_36part0,Bool.and_self]
theorem t7_36checked : Checked tree [1,1,6,7,7,7,7] := by
  refine ⟨plan8559,valid8559,t7_36choices,?_⟩
  exact check_of_frontier tree 0 t7_36root t7_36jobs t7_36frontier t7_36all
theorem t7_37choices : plan8560.choices=[1,1,7,7,7,7,7].map (options 7 5) := by rfl


theorem t7_37part0 : t7_37jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_37frontier : t7_37root.frontier 0=t7_37jobs := by rfl
theorem t7_37all : t7_37jobs.all (Job.check tree)=true := by
  simp only [t7_37jobs,List.all_append,List.all_nil,t7_37part0,Bool.and_self]
theorem t7_37checked : Checked tree [1,1,7,7,7,7,7] := by
  refine ⟨plan8560,valid8560,t7_37choices,?_⟩
  exact check_of_frontier tree 0 t7_37root t7_37jobs t7_37frontier t7_37all
theorem t7_38choices : plan8561.choices=[1,1,10,7,7,7,7].map (options 7 5) := by rfl


theorem t7_38part0 : t7_38jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_38frontier : t7_38root.frontier 0=t7_38jobs := by rfl
theorem t7_38all : t7_38jobs.all (Job.check tree)=true := by
  simp only [t7_38jobs,List.all_append,List.all_nil,t7_38part0,Bool.and_self]
theorem t7_38checked : Checked tree [1,1,10,7,7,7,7] := by
  refine ⟨plan8561,valid8561,t7_38choices,?_⟩
  exact check_of_frontier tree 0 t7_38root t7_38jobs t7_38frontier t7_38all
theorem t7_39choices : plan8470.choices=[1,2,2,7,7,7,7].map (options 7 4) := by rfl


theorem t7_39part0 : t7_39jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_39frontier : t7_39root.frontier 0=t7_39jobs := by rfl
theorem t7_39all : t7_39jobs.all (Job.check tree)=true := by
  simp only [t7_39jobs,List.all_append,List.all_nil,t7_39part0,Bool.and_self]
theorem t7_39checked : Checked tree [1,2,2,7,7,7,7] := by
  refine ⟨plan8470,valid8470,t7_39choices,?_⟩
  exact check_of_frontier tree 0 t7_39root t7_39jobs t7_39frontier t7_39all
theorem t7_40choices : plan8431.choices=[1,2,3,3,7,7,7].map (options 7 3) := by rfl


theorem t7_40part0 : t7_40jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_40frontier : t7_40root.frontier 0=t7_40jobs := by rfl
theorem t7_40all : t7_40jobs.all (Job.check tree)=true := by
  simp only [t7_40jobs,List.all_append,List.all_nil,t7_40part0,Bool.and_self]
theorem t7_40checked : Checked tree [1,2,3,3,7,7,7] := by
  refine ⟨plan8431,valid8431,t7_40choices,?_⟩
  exact check_of_frontier tree 0 t7_40root t7_40jobs t7_40frontier t7_40all
theorem t7_41choices : plan8471.choices=[1,2,3,6,7,7,7].map (options 7 4) := by rfl


theorem t7_41part0 : t7_41jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_41frontier : t7_41root.frontier 0=t7_41jobs := by rfl
theorem t7_41all : t7_41jobs.all (Job.check tree)=true := by
  simp only [t7_41jobs,List.all_append,List.all_nil,t7_41part0,Bool.and_self]
theorem t7_41checked : Checked tree [1,2,3,6,7,7,7] := by
  refine ⟨plan8471,valid8471,t7_41choices,?_⟩
  exact check_of_frontier tree 0 t7_41root t7_41jobs t7_41frontier t7_41all
theorem t7_42choices : plan8472.choices=[1,2,3,7,7,7,7].map (options 7 4) := by rfl


theorem t7_42part0 : t7_42jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_42frontier : t7_42root.frontier 0=t7_42jobs := by rfl
theorem t7_42all : t7_42jobs.all (Job.check tree)=true := by
  simp only [t7_42jobs,List.all_append,List.all_nil,t7_42part0,Bool.and_self]
theorem t7_42checked : Checked tree [1,2,3,7,7,7,7] := by
  refine ⟨plan8472,valid8472,t7_42choices,?_⟩
  exact check_of_frontier tree 0 t7_42root t7_42jobs t7_42frontier t7_42all
theorem t7_43choices : plan8473.choices=[1,2,3,10,7,7,7].map (options 7 4) := by rfl


theorem t7_43part0 : t7_43jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_43frontier : t7_43root.frontier 0=t7_43jobs := by rfl
theorem t7_43all : t7_43jobs.all (Job.check tree)=true := by
  simp only [t7_43jobs,List.all_append,List.all_nil,t7_43part0,Bool.and_self]
theorem t7_43checked : Checked tree [1,2,3,10,7,7,7] := by
  refine ⟨plan8473,valid8473,t7_43choices,?_⟩
  exact check_of_frontier tree 0 t7_43root t7_43jobs t7_43frontier t7_43all
theorem t7_44choices : plan8562.choices=[1,2,5,7,7,7,7].map (options 7 5) := by rfl


theorem t7_44part0 : t7_44jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_44frontier : t7_44root.frontier 0=t7_44jobs := by rfl
theorem t7_44all : t7_44jobs.all (Job.check tree)=true := by
  simp only [t7_44jobs,List.all_append,List.all_nil,t7_44part0,Bool.and_self]
theorem t7_44checked : Checked tree [1,2,5,7,7,7,7] := by
  refine ⟨plan8562,valid8562,t7_44choices,?_⟩
  exact check_of_frontier tree 0 t7_44root t7_44jobs t7_44frontier t7_44all
theorem t7_45choices : plan8563.choices=[1,2,6,6,7,7,7].map (options 7 5) := by rfl


theorem t7_45part0 : t7_45jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_45frontier : t7_45root.frontier 0=t7_45jobs := by rfl
theorem t7_45all : t7_45jobs.all (Job.check tree)=true := by
  simp only [t7_45jobs,List.all_append,List.all_nil,t7_45part0,Bool.and_self]
theorem t7_45checked : Checked tree [1,2,6,6,7,7,7] := by
  refine ⟨plan8563,valid8563,t7_45choices,?_⟩
  exact check_of_frontier tree 0 t7_45root t7_45jobs t7_45frontier t7_45all
theorem t7_46choices : plan8564.choices=[1,2,6,7,7,7,7].map (options 7 5) := by rfl


theorem t7_46part0 : t7_46jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_46frontier : t7_46root.frontier 0=t7_46jobs := by rfl
theorem t7_46all : t7_46jobs.all (Job.check tree)=true := by
  simp only [t7_46jobs,List.all_append,List.all_nil,t7_46part0,Bool.and_self]
theorem t7_46checked : Checked tree [1,2,6,7,7,7,7] := by
  refine ⟨plan8564,valid8564,t7_46choices,?_⟩
  exact check_of_frontier tree 0 t7_46root t7_46jobs t7_46frontier t7_46all
theorem t7_47choices : plan8565.choices=[1,2,6,10,7,7,7].map (options 7 5) := by rfl


theorem t7_47part0 : t7_47jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_47frontier : t7_47root.frontier 0=t7_47jobs := by rfl
theorem t7_47all : t7_47jobs.all (Job.check tree)=true := by
  simp only [t7_47jobs,List.all_append,List.all_nil,t7_47part0,Bool.and_self]
theorem t7_47checked : Checked tree [1,2,6,10,7,7,7] := by
  refine ⟨plan8565,valid8565,t7_47choices,?_⟩
  exact check_of_frontier tree 0 t7_47root t7_47jobs t7_47frontier t7_47all
theorem t7_48choices : plan8566.choices=[1,2,7,7,7,7,7].map (options 7 5) := by rfl


theorem t7_48part0 : t7_48jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_48frontier : t7_48root.frontier 0=t7_48jobs := by rfl
theorem t7_48all : t7_48jobs.all (Job.check tree)=true := by
  simp only [t7_48jobs,List.all_append,List.all_nil,t7_48part0,Bool.and_self]
theorem t7_48checked : Checked tree [1,2,7,7,7,7,7] := by
  refine ⟨plan8566,valid8566,t7_48choices,?_⟩
  exact check_of_frontier tree 0 t7_48root t7_48jobs t7_48frontier t7_48all
theorem t7_49choices : plan8567.choices=[1,2,9,7,7,7,7].map (options 7 5) := by rfl


theorem t7_49part0 : t7_49jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_49frontier : t7_49root.frontier 0=t7_49jobs := by rfl
theorem t7_49all : t7_49jobs.all (Job.check tree)=true := by
  simp only [t7_49jobs,List.all_append,List.all_nil,t7_49part0,Bool.and_self]
theorem t7_49checked : Checked tree [1,2,9,7,7,7,7] := by
  refine ⟨plan8567,valid8567,t7_49choices,?_⟩
  exact check_of_frontier tree 0 t7_49root t7_49jobs t7_49frontier t7_49all
theorem t7_50choices : plan8568.choices=[1,2,10,7,7,7,7].map (options 7 5) := by rfl


theorem t7_50part0 : t7_50jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_50frontier : t7_50root.frontier 0=t7_50jobs := by rfl
theorem t7_50all : t7_50jobs.all (Job.check tree)=true := by
  simp only [t7_50jobs,List.all_append,List.all_nil,t7_50part0,Bool.and_self]
theorem t7_50checked : Checked tree [1,2,10,7,7,7,7] := by
  refine ⟨plan8568,valid8568,t7_50choices,?_⟩
  exact check_of_frontier tree 0 t7_50root t7_50jobs t7_50frontier t7_50all
theorem t7_51choices : plan8569.choices=[1,2,10,10,7,7,7].map (options 7 5) := by rfl


theorem t7_51part0 : t7_51jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_51frontier : t7_51root.frontier 0=t7_51jobs := by rfl
theorem t7_51all : t7_51jobs.all (Job.check tree)=true := by
  simp only [t7_51jobs,List.all_append,List.all_nil,t7_51part0,Bool.and_self]
theorem t7_51checked : Checked tree [1,2,10,10,7,7,7] := by
  refine ⟨plan8569,valid8569,t7_51choices,?_⟩
  exact check_of_frontier tree 0 t7_51root t7_51jobs t7_51frontier t7_51all
theorem t7_52choices : plan8417.choices=[1,3,3,3,3,7,7].map (options 7 2) := by rfl


theorem t7_52part0 : t7_52jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_52frontier : t7_52root.frontier 0=t7_52jobs := by rfl
theorem t7_52all : t7_52jobs.all (Job.check tree)=true := by
  simp only [t7_52jobs,List.all_append,List.all_nil,t7_52part0,Bool.and_self]
theorem t7_52checked : Checked tree [1,3,3,3,3,7,7] := by
  refine ⟨plan8417,valid8417,t7_52choices,?_⟩
  exact check_of_frontier tree 0 t7_52root t7_52jobs t7_52frontier t7_52all
theorem t7_53choices : plan8432.choices=[1,3,3,3,6,7,7].map (options 7 3) := by rfl


theorem t7_53part0 : t7_53jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_53frontier : t7_53root.frontier 0=t7_53jobs := by rfl
theorem t7_53all : t7_53jobs.all (Job.check tree)=true := by
  simp only [t7_53jobs,List.all_append,List.all_nil,t7_53part0,Bool.and_self]
theorem t7_53checked : Checked tree [1,3,3,3,6,7,7] := by
  refine ⟨plan8432,valid8432,t7_53choices,?_⟩
  exact check_of_frontier tree 0 t7_53root t7_53jobs t7_53frontier t7_53all
theorem t7_54choices : plan8433.choices=[1,3,3,3,7,7,7].map (options 7 3) := by rfl


theorem t7_54part0 : t7_54jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_54frontier : t7_54root.frontier 0=t7_54jobs := by rfl
theorem t7_54all : t7_54jobs.all (Job.check tree)=true := by
  simp only [t7_54jobs,List.all_append,List.all_nil,t7_54part0,Bool.and_self]
theorem t7_54checked : Checked tree [1,3,3,3,7,7,7] := by
  refine ⟨plan8433,valid8433,t7_54choices,?_⟩
  exact check_of_frontier tree 0 t7_54root t7_54jobs t7_54frontier t7_54all
theorem t7_55choices : plan8434.choices=[1,3,3,3,10,7,7].map (options 7 3) := by rfl


theorem t7_55part0 : t7_55jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_55frontier : t7_55root.frontier 0=t7_55jobs := by rfl
theorem t7_55all : t7_55jobs.all (Job.check tree)=true := by
  simp only [t7_55jobs,List.all_append,List.all_nil,t7_55part0,Bool.and_self]
theorem t7_55checked : Checked tree [1,3,3,3,10,7,7] := by
  refine ⟨plan8434,valid8434,t7_55choices,?_⟩
  exact check_of_frontier tree 0 t7_55root t7_55jobs t7_55frontier t7_55all
theorem t7_56choices : plan8474.choices=[1,3,3,6,6,7,7].map (options 7 4) := by rfl


theorem t7_56part0 : t7_56jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_56frontier : t7_56root.frontier 0=t7_56jobs := by rfl
theorem t7_56all : t7_56jobs.all (Job.check tree)=true := by
  simp only [t7_56jobs,List.all_append,List.all_nil,t7_56part0,Bool.and_self]
theorem t7_56checked : Checked tree [1,3,3,6,6,7,7] := by
  refine ⟨plan8474,valid8474,t7_56choices,?_⟩
  exact check_of_frontier tree 0 t7_56root t7_56jobs t7_56frontier t7_56all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks155 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1776checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1777checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1764checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1778checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1779checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1780checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1781checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1782checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1783checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1784checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1785checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1786checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1765checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1787checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1788checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1789checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1790checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1791checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1792checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1793checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1794checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1795checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_0checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_1checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1766checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_2checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_3checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_4checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_5checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_6checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_7checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_8checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_9checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_10checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_11checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1767checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_12checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_13checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_14checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_15checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_16checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_17checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_18checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_19checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_20checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_21checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_22checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1768checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_23checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_24checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_25checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_26checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_27checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_28checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_29checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_30checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_31checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_32checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1769checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_33checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_34checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_35checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_36checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_37checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_38checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_39checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_40checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_41checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_42checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_43checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1770checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_44checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_45checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_46checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_47checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_48checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_49checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_50checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_51checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_52checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_53checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1771checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_54checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_55checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_56checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1772checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1773checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1774checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1775checked⟩
