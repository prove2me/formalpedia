-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks153
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:06:09.154354+00:00
-- url     : https://prove2.me/submissions/91af87f1-2d8b-4d30-8ebe-00761a8ac74f

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks153
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks153
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans080
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans083
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

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)

theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)










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

theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1561 : plan1561.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)





















































































theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1606 : plan1606.Valid := valid_step _ _ _ valid580 (by decide +kernel)







theorem valid1610 : plan1610.Valid := valid_step _ _ _ valid581 (by decide +kernel)

theorem valid1611 : plan1611.Valid := valid_step _ _ _ valid582 (by decide +kernel)

theorem valid1612 : plan1612.Valid := valid_step _ _ _ valid583 (by decide +kernel)

theorem valid1613 : plan1613.Valid := valid_step _ _ _ valid584 (by decide +kernel)

theorem valid1614 : plan1614.Valid := valid_step _ _ _ valid585 (by decide +kernel)

theorem valid1615 : plan1615.Valid := valid_step _ _ _ valid586 (by decide +kernel)

theorem valid1616 : plan1616.Valid := valid_step _ _ _ valid584 (by decide +kernel)







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

theorem valid6433 : plan6433.Valid := valid_step _ _ _ valid5410 (by decide +kernel)






























































































































































































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



































































































































theorem valid6690 : plan6690.Valid := valid_step _ _ _ valid5523 (by decide +kernel)

theorem valid6691 : plan6691.Valid := valid_step _ _ _ valid5524 (by decide +kernel)

theorem valid6692 : plan6692.Valid := valid_step _ _ _ valid5525 (by decide +kernel)
























































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









































































































theorem valid3509 : plan3509.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3510 : plan3510.Valid := valid_step _ _ _ valid1606 (by decide +kernel)



































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



































































































theorem valid5714 : plan5714.Valid := valid_step _ _ _ valid3354 (by decide +kernel)

theorem valid5715 : plan5715.Valid := valid_step _ _ _ valid3355 (by decide +kernel)

theorem valid5716 : plan5716.Valid := valid_step _ _ _ valid3356 (by decide +kernel)

theorem valid5717 : plan5717.Valid := valid_step _ _ _ valid3357 (by decide +kernel)






















































































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













































theorem valid5783 : plan5783.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5784 : plan5784.Valid := valid_step _ _ _ valid3510 (by decide +kernel)
















































































































































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

































































theorem valid7137 : plan7137.Valid := valid_step _ _ _ valid5714 (by decide +kernel)

theorem valid7138 : plan7138.Valid := valid_step _ _ _ valid5715 (by decide +kernel)

theorem valid7139 : plan7139.Valid := valid_step _ _ _ valid5716 (by decide +kernel)

theorem valid7140 : plan7140.Valid := valid_step _ _ _ valid5717 (by decide +kernel)
























































































































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









theorem valid7685 : plan7685.Valid := valid_step _ _ _ valid5783 (by decide +kernel)

theorem valid7686 : plan7686.Valid := valid_step _ _ _ valid5784 (by decide +kernel)




















































































































































































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

































































































theorem valid8017 : plan8017.Valid := valid_step _ _ _ valid6039 (by decide +kernel)

theorem valid8018 : plan8018.Valid := valid_step _ _ _ valid6040 (by decide +kernel)

theorem valid8019 : plan8019.Valid := valid_step _ _ _ valid6041 (by decide +kernel)

theorem valid8020 : plan8020.Valid := valid_step _ _ _ valid6042 (by decide +kernel)

theorem valid8021 : plan8021.Valid := valid_step _ _ _ valid6043 (by decide +kernel)

theorem valid8022 : plan8022.Valid := valid_step _ _ _ valid6044 (by decide +kernel)

theorem valid8023 : plan8023.Valid := valid_step _ _ _ valid6045 (by decide +kernel)

theorem valid8024 : plan8024.Valid := valid_step _ _ _ valid6046 (by decide +kernel)

theorem valid8025 : plan8025.Valid := valid_step _ _ _ valid6047 (by decide +kernel)

theorem valid8026 : plan8026.Valid := valid_step _ _ _ valid6048 (by decide +kernel)

theorem valid8027 : plan8027.Valid := valid_step _ _ _ valid6049 (by decide +kernel)

theorem valid8028 : plan8028.Valid := valid_step _ _ _ valid6050 (by decide +kernel)

theorem valid8029 : plan8029.Valid := valid_step _ _ _ valid6051 (by decide +kernel)

theorem valid8030 : plan8030.Valid := valid_step _ _ _ valid6052 (by decide +kernel)

theorem valid8031 : plan8031.Valid := valid_step _ _ _ valid6053 (by decide +kernel)

theorem valid8032 : plan8032.Valid := valid_step _ _ _ valid6054 (by decide +kernel)
































































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
theorem t6_1708choices : plan7685.choices=[9,3,10,10,10,7].map (options 6 5) := by rfl


theorem t6_1708part0 : t6_1708jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1708part1 : t6_1708jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1708frontier : t6_1708root.frontier 1=t6_1708jobs := by rfl
theorem t6_1708all : t6_1708jobs.all (Job.check tree)=true := by
  simp only [t6_1708jobs,List.all_append,List.all_nil,t6_1708part0,t6_1708part1,Bool.and_self]
theorem t6_1708checked : Checked tree [9,3,10,10,10,7] := by
  refine ⟨plan7685,valid7685,t6_1708choices,?_⟩
  exact check_of_frontier tree 1 t6_1708root t6_1708jobs t6_1708frontier t6_1708all
theorem t6_1709choices : plan7686.choices=[9,3,10,10,10,10].map (options 6 5) := by rfl


theorem t6_1709part0 : t6_1709jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1709frontier : t6_1709root.frontier 0=t6_1709jobs := by rfl
theorem t6_1709all : t6_1709jobs.all (Job.check tree)=true := by
  simp only [t6_1709jobs,List.all_append,List.all_nil,t6_1709part0,Bool.and_self]
theorem t6_1709checked : Checked tree [9,3,10,10,10,10] := by
  refine ⟨plan7686,valid7686,t6_1709choices,?_⟩
  exact check_of_frontier tree 0 t6_1709root t6_1709jobs t6_1709frontier t6_1709all
theorem t6_1710choices : plan8017.choices=[9,6,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1710part0 : t6_1710jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1710frontier : t6_1710root.frontier 0=t6_1710jobs := by rfl
theorem t6_1710all : t6_1710jobs.all (Job.check tree)=true := by
  simp only [t6_1710jobs,List.all_append,List.all_nil,t6_1710part0,Bool.and_self]
theorem t6_1710checked : Checked tree [9,6,6,6,6,6] := by
  refine ⟨plan8017,valid8017,t6_1710choices,?_⟩
  exact check_of_frontier tree 0 t6_1710root t6_1710jobs t6_1710frontier t6_1710all
theorem t6_1711choices : plan8018.choices=[9,6,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1711part0 : t6_1711jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1711frontier : t6_1711root.frontier 0=t6_1711jobs := by rfl
theorem t6_1711all : t6_1711jobs.all (Job.check tree)=true := by
  simp only [t6_1711jobs,List.all_append,List.all_nil,t6_1711part0,Bool.and_self]
theorem t6_1711checked : Checked tree [9,6,6,6,6,7] := by
  refine ⟨plan8018,valid8018,t6_1711choices,?_⟩
  exact check_of_frontier tree 0 t6_1711root t6_1711jobs t6_1711frontier t6_1711all
theorem t6_1712choices : plan8019.choices=[9,6,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1712part0 : t6_1712jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1712frontier : t6_1712root.frontier 0=t6_1712jobs := by rfl
theorem t6_1712all : t6_1712jobs.all (Job.check tree)=true := by
  simp only [t6_1712jobs,List.all_append,List.all_nil,t6_1712part0,Bool.and_self]
theorem t6_1712checked : Checked tree [9,6,6,6,6,10] := by
  refine ⟨plan8019,valid8019,t6_1712choices,?_⟩
  exact check_of_frontier tree 0 t6_1712root t6_1712jobs t6_1712frontier t6_1712all
theorem t6_1713choices : plan8020.choices=[9,6,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1713part0 : t6_1713jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1713frontier : t6_1713root.frontier 0=t6_1713jobs := by rfl
theorem t6_1713all : t6_1713jobs.all (Job.check tree)=true := by
  simp only [t6_1713jobs,List.all_append,List.all_nil,t6_1713part0,Bool.and_self]
theorem t6_1713checked : Checked tree [9,6,6,6,7,7] := by
  refine ⟨plan8020,valid8020,t6_1713choices,?_⟩
  exact check_of_frontier tree 0 t6_1713root t6_1713jobs t6_1713frontier t6_1713all
theorem t6_1714choices : plan8021.choices=[9,6,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1714part0 : t6_1714jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1714frontier : t6_1714root.frontier 0=t6_1714jobs := by rfl
theorem t6_1714all : t6_1714jobs.all (Job.check tree)=true := by
  simp only [t6_1714jobs,List.all_append,List.all_nil,t6_1714part0,Bool.and_self]
theorem t6_1714checked : Checked tree [9,6,6,6,10,7] := by
  refine ⟨plan8021,valid8021,t6_1714choices,?_⟩
  exact check_of_frontier tree 0 t6_1714root t6_1714jobs t6_1714frontier t6_1714all
theorem t6_1715choices : plan8022.choices=[9,6,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1715part0 : t6_1715jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1715frontier : t6_1715root.frontier 0=t6_1715jobs := by rfl
theorem t6_1715all : t6_1715jobs.all (Job.check tree)=true := by
  simp only [t6_1715jobs,List.all_append,List.all_nil,t6_1715part0,Bool.and_self]
theorem t6_1715checked : Checked tree [9,6,6,6,10,10] := by
  refine ⟨plan8022,valid8022,t6_1715choices,?_⟩
  exact check_of_frontier tree 0 t6_1715root t6_1715jobs t6_1715frontier t6_1715all
theorem t6_1716choices : plan8023.choices=[9,6,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1716part0 : t6_1716jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1716frontier : t6_1716root.frontier 0=t6_1716jobs := by rfl
theorem t6_1716all : t6_1716jobs.all (Job.check tree)=true := by
  simp only [t6_1716jobs,List.all_append,List.all_nil,t6_1716part0,Bool.and_self]
theorem t6_1716checked : Checked tree [9,6,6,7,7,7] := by
  refine ⟨plan8023,valid8023,t6_1716choices,?_⟩
  exact check_of_frontier tree 0 t6_1716root t6_1716jobs t6_1716frontier t6_1716all
theorem t6_1717choices : plan8024.choices=[9,6,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1717part0 : t6_1717jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1717frontier : t6_1717root.frontier 0=t6_1717jobs := by rfl
theorem t6_1717all : t6_1717jobs.all (Job.check tree)=true := by
  simp only [t6_1717jobs,List.all_append,List.all_nil,t6_1717part0,Bool.and_self]
theorem t6_1717checked : Checked tree [9,6,6,10,7,7] := by
  refine ⟨plan8024,valid8024,t6_1717choices,?_⟩
  exact check_of_frontier tree 0 t6_1717root t6_1717jobs t6_1717frontier t6_1717all
theorem t6_1718choices : plan8025.choices=[9,6,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1718part0 : t6_1718jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1718frontier : t6_1718root.frontier 0=t6_1718jobs := by rfl
theorem t6_1718all : t6_1718jobs.all (Job.check tree)=true := by
  simp only [t6_1718jobs,List.all_append,List.all_nil,t6_1718part0,Bool.and_self]
theorem t6_1718checked : Checked tree [9,6,6,10,10,7] := by
  refine ⟨plan8025,valid8025,t6_1718choices,?_⟩
  exact check_of_frontier tree 0 t6_1718root t6_1718jobs t6_1718frontier t6_1718all
theorem t6_1719choices : plan8026.choices=[9,6,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1719part0 : t6_1719jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1719frontier : t6_1719root.frontier 0=t6_1719jobs := by rfl
theorem t6_1719all : t6_1719jobs.all (Job.check tree)=true := by
  simp only [t6_1719jobs,List.all_append,List.all_nil,t6_1719part0,Bool.and_self]
theorem t6_1719checked : Checked tree [9,6,6,10,10,10] := by
  refine ⟨plan8026,valid8026,t6_1719choices,?_⟩
  exact check_of_frontier tree 0 t6_1719root t6_1719jobs t6_1719frontier t6_1719all
theorem t6_1720choices : plan8027.choices=[9,6,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1720part0 : t6_1720jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1720frontier : t6_1720root.frontier 0=t6_1720jobs := by rfl
theorem t6_1720all : t6_1720jobs.all (Job.check tree)=true := by
  simp only [t6_1720jobs,List.all_append,List.all_nil,t6_1720part0,Bool.and_self]
theorem t6_1720checked : Checked tree [9,6,7,7,7,7] := by
  refine ⟨plan8027,valid8027,t6_1720choices,?_⟩
  exact check_of_frontier tree 0 t6_1720root t6_1720jobs t6_1720frontier t6_1720all
theorem t6_1721choices : plan8028.choices=[9,6,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1721part0 : t6_1721jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1721frontier : t6_1721root.frontier 0=t6_1721jobs := by rfl
theorem t6_1721all : t6_1721jobs.all (Job.check tree)=true := by
  simp only [t6_1721jobs,List.all_append,List.all_nil,t6_1721part0,Bool.and_self]
theorem t6_1721checked : Checked tree [9,6,10,7,7,7] := by
  refine ⟨plan8028,valid8028,t6_1721choices,?_⟩
  exact check_of_frontier tree 0 t6_1721root t6_1721jobs t6_1721frontier t6_1721all
theorem t6_1722choices : plan8029.choices=[9,6,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1722part0 : t6_1722jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1722frontier : t6_1722root.frontier 0=t6_1722jobs := by rfl
theorem t6_1722all : t6_1722jobs.all (Job.check tree)=true := by
  simp only [t6_1722jobs,List.all_append,List.all_nil,t6_1722part0,Bool.and_self]
theorem t6_1722checked : Checked tree [9,6,10,10,7,7] := by
  refine ⟨plan8029,valid8029,t6_1722choices,?_⟩
  exact check_of_frontier tree 0 t6_1722root t6_1722jobs t6_1722frontier t6_1722all
theorem t6_1723choices : plan8030.choices=[9,6,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1723part0 : t6_1723jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1723frontier : t6_1723root.frontier 0=t6_1723jobs := by rfl
theorem t6_1723all : t6_1723jobs.all (Job.check tree)=true := by
  simp only [t6_1723jobs,List.all_append,List.all_nil,t6_1723part0,Bool.and_self]
theorem t6_1723checked : Checked tree [9,6,10,10,10,7] := by
  refine ⟨plan8030,valid8030,t6_1723choices,?_⟩
  exact check_of_frontier tree 0 t6_1723root t6_1723jobs t6_1723frontier t6_1723all
theorem t6_1724choices : plan8031.choices=[9,6,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1724part0 : t6_1724jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1724frontier : t6_1724root.frontier 0=t6_1724jobs := by rfl
theorem t6_1724all : t6_1724jobs.all (Job.check tree)=true := by
  simp only [t6_1724jobs,List.all_append,List.all_nil,t6_1724part0,Bool.and_self]
theorem t6_1724checked : Checked tree [9,6,10,10,10,10] := by
  refine ⟨plan8031,valid8031,t6_1724choices,?_⟩
  exact check_of_frontier tree 0 t6_1724root t6_1724jobs t6_1724frontier t6_1724all
theorem t6_1725choices : plan8032.choices=[9,7,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1725part0 : t6_1725jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1725frontier : t6_1725root.frontier 0=t6_1725jobs := by rfl
theorem t6_1725all : t6_1725jobs.all (Job.check tree)=true := by
  simp only [t6_1725jobs,List.all_append,List.all_nil,t6_1725part0,Bool.and_self]
theorem t6_1725checked : Checked tree [9,7,7,7,7,7] := by
  refine ⟨plan8032,valid8032,t6_1725choices,?_⟩
  exact check_of_frontier tree 0 t6_1725root t6_1725jobs t6_1725frontier t6_1725all
theorem t6_1726choices : plan6433.choices=[9,9,3,3,3,3].map (options 6 2) := by rfl


theorem t6_1726part0 : t6_1726jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1726frontier : t6_1726root.frontier 0=t6_1726jobs := by rfl
theorem t6_1726all : t6_1726jobs.all (Job.check tree)=true := by
  simp only [t6_1726jobs,List.all_append,List.all_nil,t6_1726part0,Bool.and_self]
theorem t6_1726checked : Checked tree [9,9,3,3,3,3] := by
  refine ⟨plan6433,valid6433,t6_1726choices,?_⟩
  exact check_of_frontier tree 0 t6_1726root t6_1726jobs t6_1726frontier t6_1726all
theorem t6_1727choices : plan6690.choices=[9,9,3,3,3,6].map (options 6 3) := by rfl


theorem t6_1727part0 : t6_1727jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1727frontier : t6_1727root.frontier 0=t6_1727jobs := by rfl
theorem t6_1727all : t6_1727jobs.all (Job.check tree)=true := by
  simp only [t6_1727jobs,List.all_append,List.all_nil,t6_1727part0,Bool.and_self]
theorem t6_1727checked : Checked tree [9,9,3,3,3,6] := by
  refine ⟨plan6690,valid6690,t6_1727choices,?_⟩
  exact check_of_frontier tree 0 t6_1727root t6_1727jobs t6_1727frontier t6_1727all
theorem t6_1728choices : plan6691.choices=[9,9,3,3,3,7].map (options 6 3) := by rfl


theorem t6_1728part0 : t6_1728jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1728part1 : t6_1728jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1728frontier : t6_1728root.frontier 1=t6_1728jobs := by rfl
theorem t6_1728all : t6_1728jobs.all (Job.check tree)=true := by
  simp only [t6_1728jobs,List.all_append,List.all_nil,t6_1728part0,t6_1728part1,Bool.and_self]
theorem t6_1728checked : Checked tree [9,9,3,3,3,7] := by
  refine ⟨plan6691,valid6691,t6_1728choices,?_⟩
  exact check_of_frontier tree 1 t6_1728root t6_1728jobs t6_1728frontier t6_1728all
theorem t6_1729choices : plan6692.choices=[9,9,3,3,3,10].map (options 6 3) := by rfl


theorem t6_1729part0 : t6_1729jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1729frontier : t6_1729root.frontier 0=t6_1729jobs := by rfl
theorem t6_1729all : t6_1729jobs.all (Job.check tree)=true := by
  simp only [t6_1729jobs,List.all_append,List.all_nil,t6_1729part0,Bool.and_self]
theorem t6_1729checked : Checked tree [9,9,3,3,3,10] := by
  refine ⟨plan6692,valid6692,t6_1729choices,?_⟩
  exact check_of_frontier tree 0 t6_1729root t6_1729jobs t6_1729frontier t6_1729all
theorem t6_1730choices : plan7137.choices=[9,9,3,3,6,6].map (options 6 4) := by rfl


theorem t6_1730part0 : t6_1730jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1730frontier : t6_1730root.frontier 0=t6_1730jobs := by rfl
theorem t6_1730all : t6_1730jobs.all (Job.check tree)=true := by
  simp only [t6_1730jobs,List.all_append,List.all_nil,t6_1730part0,Bool.and_self]
theorem t6_1730checked : Checked tree [9,9,3,3,6,6] := by
  refine ⟨plan7137,valid7137,t6_1730choices,?_⟩
  exact check_of_frontier tree 0 t6_1730root t6_1730jobs t6_1730frontier t6_1730all
theorem t6_1731choices : plan7138.choices=[9,9,3,3,6,7].map (options 6 4) := by rfl


theorem t6_1731part0 : t6_1731jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1731part1 : t6_1731jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1731part2 : t6_1731jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1731frontier : t6_1731root.frontier 1=t6_1731jobs := by rfl
theorem t6_1731all : t6_1731jobs.all (Job.check tree)=true := by
  simp only [t6_1731jobs,List.all_append,List.all_nil,t6_1731part0,t6_1731part1,t6_1731part2,Bool.and_self]
theorem t6_1731checked : Checked tree [9,9,3,3,6,7] := by
  refine ⟨plan7138,valid7138,t6_1731choices,?_⟩
  exact check_of_frontier tree 1 t6_1731root t6_1731jobs t6_1731frontier t6_1731all
theorem t6_1732choices : plan7139.choices=[9,9,3,3,6,10].map (options 6 4) := by rfl


theorem t6_1732part0 : t6_1732jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1732frontier : t6_1732root.frontier 0=t6_1732jobs := by rfl
theorem t6_1732all : t6_1732jobs.all (Job.check tree)=true := by
  simp only [t6_1732jobs,List.all_append,List.all_nil,t6_1732part0,Bool.and_self]
theorem t6_1732checked : Checked tree [9,9,3,3,6,10] := by
  refine ⟨plan7139,valid7139,t6_1732choices,?_⟩
  exact check_of_frontier tree 0 t6_1732root t6_1732jobs t6_1732frontier t6_1732all
theorem t6_1733choices : plan7140.choices=[9,9,3,3,7,7].map (options 6 4) := by rfl


theorem t6_1733part0 : t6_1733jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1733part1 : t6_1733jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1733part2 : t6_1733jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1733part3 : t6_1733jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1733frontier : t6_1733root.frontier 1=t6_1733jobs := by rfl
theorem t6_1733all : t6_1733jobs.all (Job.check tree)=true := by
  simp only [t6_1733jobs,List.all_append,List.all_nil,t6_1733part0,t6_1733part1,t6_1733part2,t6_1733part3,Bool.and_self]
theorem t6_1733checked : Checked tree [9,9,3,3,7,7] := by
  refine ⟨plan7140,valid7140,t6_1733choices,?_⟩
  exact check_of_frontier tree 1 t6_1733root t6_1733jobs t6_1733frontier t6_1733all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks153 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1720checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1721checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1722checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1723checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1724checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1725checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1708checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1726checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1727checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1728checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1729checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1730checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1731checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1732checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1709checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1733checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1710checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1711checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1712checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1713checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1714checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1715checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1716checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1717checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1718checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1719checked⟩
