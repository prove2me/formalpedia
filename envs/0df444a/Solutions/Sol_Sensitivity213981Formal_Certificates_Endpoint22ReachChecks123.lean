-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks123
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:47:15.169713+00:00
-- url     : https://prove2.me/submissions/17cd18fa-3167-49e3-acfd-06c5302c5a9d

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks123
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks123
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
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











































theorem valid118 : plan118.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid123 : plan123.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid125 : plan125.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)







theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)





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

























































































































theorem valid541 : plan541.Valid := valid_step _ _ _ valid118 (by decide +kernel)









theorem valid546 : plan546.Valid := valid_step _ _ _ valid123 (by decide +kernel)

theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid548 : plan548.Valid := valid_step _ _ _ valid125 (by decide +kernel)





















theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)













theorem valid566 : plan566.Valid := valid_step _ _ _ valid131 (by decide +kernel)



















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









































theorem valid1557 : plan1557.Valid := valid_step _ _ _ valid566 (by decide +kernel)





















































theorem valid1584 : plan1584.Valid := valid_step _ _ _ valid576 (by decide +kernel)



theorem valid1586 : plan1586.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1587 : plan1587.Valid := valid_step _ _ _ valid579 (by decide +kernel)



















theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)









theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1606 : plan1606.Valid := valid_step _ _ _ valid580 (by decide +kernel)







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

theorem valid3265 : plan3265.Valid := valid_step _ _ _ valid1516 (by decide +kernel)

theorem valid3266 : plan3266.Valid := valid_step _ _ _ valid1517 (by decide +kernel)

theorem valid3267 : plan3267.Valid := valid_step _ _ _ valid1518 (by decide +kernel)













































































theorem valid3306 : plan3306.Valid := valid_step _ _ _ valid1532 (by decide +kernel)












































































































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

































theorem valid5393 : plan5393.Valid := valid_step _ _ _ valid3265 (by decide +kernel)

theorem valid5394 : plan5394.Valid := valid_step _ _ _ valid3266 (by decide +kernel)

theorem valid5395 : plan5395.Valid := valid_step _ _ _ valid3267 (by decide +kernel)


























































































































































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























































































































































theorem valid6316 : plan6316.Valid := valid_step _ _ _ valid5356 (by decide +kernel)








































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





































































































theorem valid3411 : plan3411.Valid := valid_step _ _ _ valid1557 (by decide +kernel)

































































theorem valid3444 : plan3444.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3445 : plan3445.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3446 : plan3446.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3447 : plan3447.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

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















theorem valid5480 : plan5480.Valid := valid_step _ _ _ valid3306 (by decide +kernel)
















































































































































































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







































theorem valid6644 : plan6644.Valid := valid_step _ _ _ valid5480 (by decide +kernel)
























































































































































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





































































































































theorem valid5731 : plan5731.Valid := valid_step _ _ _ valid3411 (by decide +kernel)


























































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





















































































































































theorem valid5931 : plan5931.Valid := valid_step _ _ _ valid3444 (by decide +kernel)

theorem valid5932 : plan5932.Valid := valid_step _ _ _ valid3445 (by decide +kernel)

theorem valid5933 : plan5933.Valid := valid_step _ _ _ valid3446 (by decide +kernel)

theorem valid5934 : plan5934.Valid := valid_step _ _ _ valid3447 (by decide +kernel)

theorem valid5935 : plan5935.Valid := valid_step _ _ _ valid3448 (by decide +kernel)

theorem valid5936 : plan5936.Valid := valid_step _ _ _ valid3449 (by decide +kernel)

























theorem valid5949 : plan5949.Valid := valid_step _ _ _ valid3488 (by decide +kernel)



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































































































































































theorem valid6416 : plan6416.Valid := valid_step _ _ _ valid5393 (by decide +kernel)

theorem valid6417 : plan6417.Valid := valid_step _ _ _ valid5394 (by decide +kernel)

theorem valid6418 : plan6418.Valid := valid_step _ _ _ valid5395 (by decide +kernel)




























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



































































theorem valid7042 : plan7042.Valid := valid_step _ _ _ valid5731 (by decide +kernel)




























































































































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

































































theorem valid7521 : plan7521.Valid := valid_step _ _ _ valid5931 (by decide +kernel)

theorem valid7522 : plan7522.Valid := valid_step _ _ _ valid5932 (by decide +kernel)

theorem valid7523 : plan7523.Valid := valid_step _ _ _ valid5933 (by decide +kernel)

theorem valid7524 : plan7524.Valid := valid_step _ _ _ valid5934 (by decide +kernel)

theorem valid7525 : plan7525.Valid := valid_step _ _ _ valid5935 (by decide +kernel)

theorem valid7526 : plan7526.Valid := valid_step _ _ _ valid5936 (by decide +kernel)

theorem valid7527 : plan7527.Valid := valid_step _ _ _ valid5949 (by decide +kernel)

theorem valid7528 : plan7528.Valid := valid_step _ _ _ valid5951 (by decide +kernel)

theorem valid7529 : plan7529.Valid := valid_step _ _ _ valid5952 (by decide +kernel)














































































































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



theorem valid6084 : plan6084.Valid := valid_step _ _ _ valid3541 (by decide +kernel)



theorem valid6086 : plan6086.Valid := valid_step _ _ _ valid3543 (by decide +kernel)

theorem valid6087 : plan6087.Valid := valid_step _ _ _ valid3544 (by decide +kernel)



theorem valid6089 : plan6089.Valid := valid_step _ _ _ valid3546 (by decide +kernel)



theorem valid6091 : plan6091.Valid := valid_step _ _ _ valid3548 (by decide +kernel)



theorem valid6093 : plan6093.Valid := valid_step _ _ _ valid3550 (by decide +kernel)

theorem valid6094 : plan6094.Valid := valid_step _ _ _ valid3551 (by decide +kernel)



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

















theorem valid7785 : plan7785.Valid := valid_step _ _ _ valid6072 (by decide +kernel)

theorem valid7786 : plan7786.Valid := valid_step _ _ _ valid6073 (by decide +kernel)

theorem valid7787 : plan7787.Valid := valid_step _ _ _ valid6074 (by decide +kernel)

theorem valid7788 : plan7788.Valid := valid_step _ _ _ valid6075 (by decide +kernel)

theorem valid7789 : plan7789.Valid := valid_step _ _ _ valid6076 (by decide +kernel)

theorem valid7790 : plan7790.Valid := valid_step _ _ _ valid6077 (by decide +kernel)

theorem valid7791 : plan7791.Valid := valid_step _ _ _ valid6078 (by decide +kernel)

theorem valid7792 : plan7792.Valid := valid_step _ _ _ valid6079 (by decide +kernel)

theorem valid7793 : plan7793.Valid := valid_step _ _ _ valid6080 (by decide +kernel)

theorem valid7794 : plan7794.Valid := valid_step _ _ _ valid6081 (by decide +kernel)

theorem valid7795 : plan7795.Valid := valid_step _ _ _ valid6082 (by decide +kernel)

theorem valid7796 : plan7796.Valid := valid_step _ _ _ valid6084 (by decide +kernel)

theorem valid7797 : plan7797.Valid := valid_step _ _ _ valid6086 (by decide +kernel)

theorem valid7798 : plan7798.Valid := valid_step _ _ _ valid6087 (by decide +kernel)

theorem valid7799 : plan7799.Valid := valid_step _ _ _ valid6089 (by decide +kernel)

theorem valid7800 : plan7800.Valid := valid_step _ _ _ valid6091 (by decide +kernel)

theorem valid7801 : plan7801.Valid := valid_step _ _ _ valid6093 (by decide +kernel)

theorem valid7802 : plan7802.Valid := valid_step _ _ _ valid6094 (by decide +kernel)

theorem valid7803 : plan7803.Valid := valid_step _ _ _ valid6096 (by decide +kernel)

theorem valid7804 : plan7804.Valid := valid_step _ _ _ valid6097 (by decide +kernel)

theorem valid7805 : plan7805.Valid := valid_step _ _ _ valid6098 (by decide +kernel)

theorem valid7806 : plan7806.Valid := valid_step _ _ _ valid6099 (by decide +kernel)

theorem valid7807 : plan7807.Valid := valid_step _ _ _ valid6100 (by decide +kernel)

theorem valid7808 : plan7808.Valid := valid_step _ _ _ valid6101 (by decide +kernel)

theorem valid7809 : plan7809.Valid := valid_step _ _ _ valid6102 (by decide +kernel)

theorem valid7810 : plan7810.Valid := valid_step _ _ _ valid6103 (by decide +kernel)

theorem valid7811 : plan7811.Valid := valid_step _ _ _ valid6104 (by decide +kernel)


























































































































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
theorem t6_1150choices : plan7521.choices=[4,9,3,6,10,7].map (options 6 5) := by rfl


theorem t6_1150part0 : t6_1150jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1150frontier : t6_1150root.frontier 0=t6_1150jobs := by rfl
theorem t6_1150all : t6_1150jobs.all (Job.check tree)=true := by
  simp only [t6_1150jobs,List.all_append,List.all_nil,t6_1150part0,Bool.and_self]
theorem t6_1150checked : Checked tree [4,9,3,6,10,7] := by
  refine ⟨plan7521,valid7521,t6_1150choices,?_⟩
  exact check_of_frontier tree 0 t6_1150root t6_1150jobs t6_1150frontier t6_1150all
theorem t6_1151choices : plan7522.choices=[4,9,3,6,10,10].map (options 6 5) := by rfl


theorem t6_1151part0 : t6_1151jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1151frontier : t6_1151root.frontier 0=t6_1151jobs := by rfl
theorem t6_1151all : t6_1151jobs.all (Job.check tree)=true := by
  simp only [t6_1151jobs,List.all_append,List.all_nil,t6_1151part0,Bool.and_self]
theorem t6_1151checked : Checked tree [4,9,3,6,10,10] := by
  refine ⟨plan7522,valid7522,t6_1151choices,?_⟩
  exact check_of_frontier tree 0 t6_1151root t6_1151jobs t6_1151frontier t6_1151all
theorem t6_1152choices : plan7523.choices=[4,9,3,7,7,7].map (options 6 5) := by rfl


theorem t6_1152part0 : t6_1152jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1152part1 : t6_1152jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1152frontier : t6_1152root.frontier 1=t6_1152jobs := by rfl
theorem t6_1152all : t6_1152jobs.all (Job.check tree)=true := by
  simp only [t6_1152jobs,List.all_append,List.all_nil,t6_1152part0,t6_1152part1,Bool.and_self]
theorem t6_1152checked : Checked tree [4,9,3,7,7,7] := by
  refine ⟨plan7523,valid7523,t6_1152choices,?_⟩
  exact check_of_frontier tree 1 t6_1152root t6_1152jobs t6_1152frontier t6_1152all
theorem t6_1153choices : plan7524.choices=[4,9,3,10,7,7].map (options 6 5) := by rfl


theorem t6_1153part0 : t6_1153jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1153part1 : t6_1153jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1153frontier : t6_1153root.frontier 1=t6_1153jobs := by rfl
theorem t6_1153all : t6_1153jobs.all (Job.check tree)=true := by
  simp only [t6_1153jobs,List.all_append,List.all_nil,t6_1153part0,t6_1153part1,Bool.and_self]
theorem t6_1153checked : Checked tree [4,9,3,10,7,7] := by
  refine ⟨plan7524,valid7524,t6_1153choices,?_⟩
  exact check_of_frontier tree 1 t6_1153root t6_1153jobs t6_1153frontier t6_1153all
theorem t6_1154choices : plan7525.choices=[4,9,3,10,10,7].map (options 6 5) := by rfl


theorem t6_1154part0 : t6_1154jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1154frontier : t6_1154root.frontier 0=t6_1154jobs := by rfl
theorem t6_1154all : t6_1154jobs.all (Job.check tree)=true := by
  simp only [t6_1154jobs,List.all_append,List.all_nil,t6_1154part0,Bool.and_self]
theorem t6_1154checked : Checked tree [4,9,3,10,10,7] := by
  refine ⟨plan7525,valid7525,t6_1154choices,?_⟩
  exact check_of_frontier tree 0 t6_1154root t6_1154jobs t6_1154frontier t6_1154all
theorem t6_1155choices : plan7526.choices=[4,9,3,10,10,10].map (options 6 5) := by rfl


theorem t6_1155part0 : t6_1155jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1155frontier : t6_1155root.frontier 0=t6_1155jobs := by rfl
theorem t6_1155all : t6_1155jobs.all (Job.check tree)=true := by
  simp only [t6_1155jobs,List.all_append,List.all_nil,t6_1155part0,Bool.and_self]
theorem t6_1155checked : Checked tree [4,9,3,10,10,10] := by
  refine ⟨plan7526,valid7526,t6_1155choices,?_⟩
  exact check_of_frontier tree 0 t6_1155root t6_1155jobs t6_1155frontier t6_1155all
theorem t6_1156choices : plan7785.choices=[4,9,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1156part0 : t6_1156jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1156frontier : t6_1156root.frontier 0=t6_1156jobs := by rfl
theorem t6_1156all : t6_1156jobs.all (Job.check tree)=true := by
  simp only [t6_1156jobs,List.all_append,List.all_nil,t6_1156part0,Bool.and_self]
theorem t6_1156checked : Checked tree [4,9,6,6,6,6] := by
  refine ⟨plan7785,valid7785,t6_1156choices,?_⟩
  exact check_of_frontier tree 0 t6_1156root t6_1156jobs t6_1156frontier t6_1156all
theorem t6_1157choices : plan7786.choices=[4,9,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1157part0 : t6_1157jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1157frontier : t6_1157root.frontier 0=t6_1157jobs := by rfl
theorem t6_1157all : t6_1157jobs.all (Job.check tree)=true := by
  simp only [t6_1157jobs,List.all_append,List.all_nil,t6_1157part0,Bool.and_self]
theorem t6_1157checked : Checked tree [4,9,6,6,6,7] := by
  refine ⟨plan7786,valid7786,t6_1157choices,?_⟩
  exact check_of_frontier tree 0 t6_1157root t6_1157jobs t6_1157frontier t6_1157all
theorem t6_1158choices : plan7787.choices=[4,9,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1158part0 : t6_1158jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1158frontier : t6_1158root.frontier 0=t6_1158jobs := by rfl
theorem t6_1158all : t6_1158jobs.all (Job.check tree)=true := by
  simp only [t6_1158jobs,List.all_append,List.all_nil,t6_1158part0,Bool.and_self]
theorem t6_1158checked : Checked tree [4,9,6,6,6,10] := by
  refine ⟨plan7787,valid7787,t6_1158choices,?_⟩
  exact check_of_frontier tree 0 t6_1158root t6_1158jobs t6_1158frontier t6_1158all
theorem t6_1159choices : plan7788.choices=[4,9,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1159part0 : t6_1159jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1159frontier : t6_1159root.frontier 0=t6_1159jobs := by rfl
theorem t6_1159all : t6_1159jobs.all (Job.check tree)=true := by
  simp only [t6_1159jobs,List.all_append,List.all_nil,t6_1159part0,Bool.and_self]
theorem t6_1159checked : Checked tree [4,9,6,6,7,7] := by
  refine ⟨plan7788,valid7788,t6_1159choices,?_⟩
  exact check_of_frontier tree 0 t6_1159root t6_1159jobs t6_1159frontier t6_1159all
theorem t6_1160choices : plan7789.choices=[4,9,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1160part0 : t6_1160jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1160frontier : t6_1160root.frontier 0=t6_1160jobs := by rfl
theorem t6_1160all : t6_1160jobs.all (Job.check tree)=true := by
  simp only [t6_1160jobs,List.all_append,List.all_nil,t6_1160part0,Bool.and_self]
theorem t6_1160checked : Checked tree [4,9,6,6,10,7] := by
  refine ⟨plan7789,valid7789,t6_1160choices,?_⟩
  exact check_of_frontier tree 0 t6_1160root t6_1160jobs t6_1160frontier t6_1160all
theorem t6_1161choices : plan7790.choices=[4,9,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1161part0 : t6_1161jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1161frontier : t6_1161root.frontier 0=t6_1161jobs := by rfl
theorem t6_1161all : t6_1161jobs.all (Job.check tree)=true := by
  simp only [t6_1161jobs,List.all_append,List.all_nil,t6_1161part0,Bool.and_self]
theorem t6_1161checked : Checked tree [4,9,6,6,10,10] := by
  refine ⟨plan7790,valid7790,t6_1161choices,?_⟩
  exact check_of_frontier tree 0 t6_1161root t6_1161jobs t6_1161frontier t6_1161all
theorem t6_1162choices : plan7791.choices=[4,9,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1162part0 : t6_1162jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1162frontier : t6_1162root.frontier 0=t6_1162jobs := by rfl
theorem t6_1162all : t6_1162jobs.all (Job.check tree)=true := by
  simp only [t6_1162jobs,List.all_append,List.all_nil,t6_1162part0,Bool.and_self]
theorem t6_1162checked : Checked tree [4,9,6,7,7,7] := by
  refine ⟨plan7791,valid7791,t6_1162choices,?_⟩
  exact check_of_frontier tree 0 t6_1162root t6_1162jobs t6_1162frontier t6_1162all
theorem t6_1163choices : plan7792.choices=[4,9,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1163part0 : t6_1163jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1163frontier : t6_1163root.frontier 0=t6_1163jobs := by rfl
theorem t6_1163all : t6_1163jobs.all (Job.check tree)=true := by
  simp only [t6_1163jobs,List.all_append,List.all_nil,t6_1163part0,Bool.and_self]
theorem t6_1163checked : Checked tree [4,9,6,10,7,7] := by
  refine ⟨plan7792,valid7792,t6_1163choices,?_⟩
  exact check_of_frontier tree 0 t6_1163root t6_1163jobs t6_1163frontier t6_1163all
theorem t6_1164choices : plan7793.choices=[4,9,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1164part0 : t6_1164jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1164frontier : t6_1164root.frontier 0=t6_1164jobs := by rfl
theorem t6_1164all : t6_1164jobs.all (Job.check tree)=true := by
  simp only [t6_1164jobs,List.all_append,List.all_nil,t6_1164part0,Bool.and_self]
theorem t6_1164checked : Checked tree [4,9,6,10,10,7] := by
  refine ⟨plan7793,valid7793,t6_1164choices,?_⟩
  exact check_of_frontier tree 0 t6_1164root t6_1164jobs t6_1164frontier t6_1164all
theorem t6_1165choices : plan7794.choices=[4,9,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1165part0 : t6_1165jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1165frontier : t6_1165root.frontier 0=t6_1165jobs := by rfl
theorem t6_1165all : t6_1165jobs.all (Job.check tree)=true := by
  simp only [t6_1165jobs,List.all_append,List.all_nil,t6_1165part0,Bool.and_self]
theorem t6_1165checked : Checked tree [4,9,6,10,10,10] := by
  refine ⟨plan7794,valid7794,t6_1165choices,?_⟩
  exact check_of_frontier tree 0 t6_1165root t6_1165jobs t6_1165frontier t6_1165all
theorem t6_1166choices : plan7795.choices=[4,9,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1166part0 : t6_1166jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1166frontier : t6_1166root.frontier 0=t6_1166jobs := by rfl
theorem t6_1166all : t6_1166jobs.all (Job.check tree)=true := by
  simp only [t6_1166jobs,List.all_append,List.all_nil,t6_1166part0,Bool.and_self]
theorem t6_1166checked : Checked tree [4,9,7,7,7,7] := by
  refine ⟨plan7795,valid7795,t6_1166choices,?_⟩
  exact check_of_frontier tree 0 t6_1166root t6_1166jobs t6_1166frontier t6_1166all
theorem t6_1167choices : plan7042.choices=[4,9,9,3,3,7].map (options 6 4) := by rfl


theorem t6_1167part0 : t6_1167jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1167frontier : t6_1167root.frontier 0=t6_1167jobs := by rfl
theorem t6_1167all : t6_1167jobs.all (Job.check tree)=true := by
  simp only [t6_1167jobs,List.all_append,List.all_nil,t6_1167part0,Bool.and_self]
theorem t6_1167checked : Checked tree [4,9,9,3,3,7] := by
  refine ⟨plan7042,valid7042,t6_1167choices,?_⟩
  exact check_of_frontier tree 0 t6_1167root t6_1167jobs t6_1167frontier t6_1167all
theorem t6_1168choices : plan7527.choices=[4,9,9,3,6,7].map (options 6 5) := by rfl


theorem t6_1168part0 : t6_1168jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1168frontier : t6_1168root.frontier 0=t6_1168jobs := by rfl
theorem t6_1168all : t6_1168jobs.all (Job.check tree)=true := by
  simp only [t6_1168jobs,List.all_append,List.all_nil,t6_1168part0,Bool.and_self]
theorem t6_1168checked : Checked tree [4,9,9,3,6,7] := by
  refine ⟨plan7527,valid7527,t6_1168choices,?_⟩
  exact check_of_frontier tree 0 t6_1168root t6_1168jobs t6_1168frontier t6_1168all
theorem t6_1169choices : plan7528.choices=[4,9,9,3,7,7].map (options 6 5) := by rfl


theorem t6_1169part0 : t6_1169jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1169frontier : t6_1169root.frontier 0=t6_1169jobs := by rfl
theorem t6_1169all : t6_1169jobs.all (Job.check tree)=true := by
  simp only [t6_1169jobs,List.all_append,List.all_nil,t6_1169part0,Bool.and_self]
theorem t6_1169checked : Checked tree [4,9,9,3,7,7] := by
  refine ⟨plan7528,valid7528,t6_1169choices,?_⟩
  exact check_of_frontier tree 0 t6_1169root t6_1169jobs t6_1169frontier t6_1169all
theorem t6_1170choices : plan7529.choices=[4,9,9,3,10,7].map (options 6 5) := by rfl


theorem t6_1170part0 : t6_1170jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1170frontier : t6_1170root.frontier 0=t6_1170jobs := by rfl
theorem t6_1170all : t6_1170jobs.all (Job.check tree)=true := by
  simp only [t6_1170jobs,List.all_append,List.all_nil,t6_1170part0,Bool.and_self]
theorem t6_1170checked : Checked tree [4,9,9,3,10,7] := by
  refine ⟨plan7529,valid7529,t6_1170choices,?_⟩
  exact check_of_frontier tree 0 t6_1170root t6_1170jobs t6_1170frontier t6_1170all
theorem t6_1171choices : plan7796.choices=[4,9,9,6,6,7].map (options 6 6) := by rfl


theorem t6_1171part0 : t6_1171jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1171frontier : t6_1171root.frontier 0=t6_1171jobs := by rfl
theorem t6_1171all : t6_1171jobs.all (Job.check tree)=true := by
  simp only [t6_1171jobs,List.all_append,List.all_nil,t6_1171part0,Bool.and_self]
theorem t6_1171checked : Checked tree [4,9,9,6,6,7] := by
  refine ⟨plan7796,valid7796,t6_1171choices,?_⟩
  exact check_of_frontier tree 0 t6_1171root t6_1171jobs t6_1171frontier t6_1171all
theorem t6_1172choices : plan7797.choices=[4,9,9,6,7,7].map (options 6 6) := by rfl


theorem t6_1172part0 : t6_1172jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1172frontier : t6_1172root.frontier 0=t6_1172jobs := by rfl
theorem t6_1172all : t6_1172jobs.all (Job.check tree)=true := by
  simp only [t6_1172jobs,List.all_append,List.all_nil,t6_1172part0,Bool.and_self]
theorem t6_1172checked : Checked tree [4,9,9,6,7,7] := by
  refine ⟨plan7797,valid7797,t6_1172choices,?_⟩
  exact check_of_frontier tree 0 t6_1172root t6_1172jobs t6_1172frontier t6_1172all
theorem t6_1173choices : plan7798.choices=[4,9,9,6,10,7].map (options 6 6) := by rfl


theorem t6_1173part0 : t6_1173jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1173frontier : t6_1173root.frontier 0=t6_1173jobs := by rfl
theorem t6_1173all : t6_1173jobs.all (Job.check tree)=true := by
  simp only [t6_1173jobs,List.all_append,List.all_nil,t6_1173part0,Bool.and_self]
theorem t6_1173checked : Checked tree [4,9,9,6,10,7] := by
  refine ⟨plan7798,valid7798,t6_1173choices,?_⟩
  exact check_of_frontier tree 0 t6_1173root t6_1173jobs t6_1173frontier t6_1173all
theorem t6_1174choices : plan7799.choices=[4,9,9,7,7,7].map (options 6 6) := by rfl


theorem t6_1174part0 : t6_1174jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1174frontier : t6_1174root.frontier 0=t6_1174jobs := by rfl
theorem t6_1174all : t6_1174jobs.all (Job.check tree)=true := by
  simp only [t6_1174jobs,List.all_append,List.all_nil,t6_1174part0,Bool.and_self]
theorem t6_1174checked : Checked tree [4,9,9,7,7,7] := by
  refine ⟨plan7799,valid7799,t6_1174choices,?_⟩
  exact check_of_frontier tree 0 t6_1174root t6_1174jobs t6_1174frontier t6_1174all
theorem t6_1175choices : plan7800.choices=[4,9,9,9,7,7].map (options 6 6) := by rfl


theorem t6_1175part0 : t6_1175jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1175frontier : t6_1175root.frontier 0=t6_1175jobs := by rfl
theorem t6_1175all : t6_1175jobs.all (Job.check tree)=true := by
  simp only [t6_1175jobs,List.all_append,List.all_nil,t6_1175part0,Bool.and_self]
theorem t6_1175checked : Checked tree [4,9,9,9,7,7] := by
  refine ⟨plan7800,valid7800,t6_1175choices,?_⟩
  exact check_of_frontier tree 0 t6_1175root t6_1175jobs t6_1175frontier t6_1175all
theorem t6_1176choices : plan7801.choices=[4,9,9,10,7,7].map (options 6 6) := by rfl


theorem t6_1176part0 : t6_1176jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1176frontier : t6_1176root.frontier 0=t6_1176jobs := by rfl
theorem t6_1176all : t6_1176jobs.all (Job.check tree)=true := by
  simp only [t6_1176jobs,List.all_append,List.all_nil,t6_1176part0,Bool.and_self]
theorem t6_1176checked : Checked tree [4,9,9,10,7,7] := by
  refine ⟨plan7801,valid7801,t6_1176choices,?_⟩
  exact check_of_frontier tree 0 t6_1176root t6_1176jobs t6_1176frontier t6_1176all
theorem t6_1177choices : plan7802.choices=[4,9,9,10,10,7].map (options 6 6) := by rfl


theorem t6_1177part0 : t6_1177jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1177frontier : t6_1177root.frontier 0=t6_1177jobs := by rfl
theorem t6_1177all : t6_1177jobs.all (Job.check tree)=true := by
  simp only [t6_1177jobs,List.all_append,List.all_nil,t6_1177part0,Bool.and_self]
theorem t6_1177checked : Checked tree [4,9,9,10,10,7] := by
  refine ⟨plan7802,valid7802,t6_1177choices,?_⟩
  exact check_of_frontier tree 0 t6_1177root t6_1177jobs t6_1177frontier t6_1177all
theorem t6_1178choices : plan7803.choices=[4,9,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1178part0 : t6_1178jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1178frontier : t6_1178root.frontier 0=t6_1178jobs := by rfl
theorem t6_1178all : t6_1178jobs.all (Job.check tree)=true := by
  simp only [t6_1178jobs,List.all_append,List.all_nil,t6_1178part0,Bool.and_self]
theorem t6_1178checked : Checked tree [4,9,10,7,7,7] := by
  refine ⟨plan7803,valid7803,t6_1178choices,?_⟩
  exact check_of_frontier tree 0 t6_1178root t6_1178jobs t6_1178frontier t6_1178all
theorem t6_1179choices : plan7804.choices=[4,9,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1179part0 : t6_1179jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1179frontier : t6_1179root.frontier 0=t6_1179jobs := by rfl
theorem t6_1179all : t6_1179jobs.all (Job.check tree)=true := by
  simp only [t6_1179jobs,List.all_append,List.all_nil,t6_1179part0,Bool.and_self]
theorem t6_1179checked : Checked tree [4,9,10,10,7,7] := by
  refine ⟨plan7804,valid7804,t6_1179choices,?_⟩
  exact check_of_frontier tree 0 t6_1179root t6_1179jobs t6_1179frontier t6_1179all
theorem t6_1180choices : plan7805.choices=[4,9,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1180part0 : t6_1180jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1180frontier : t6_1180root.frontier 0=t6_1180jobs := by rfl
theorem t6_1180all : t6_1180jobs.all (Job.check tree)=true := by
  simp only [t6_1180jobs,List.all_append,List.all_nil,t6_1180part0,Bool.and_self]
theorem t6_1180checked : Checked tree [4,9,10,10,10,7] := by
  refine ⟨plan7805,valid7805,t6_1180choices,?_⟩
  exact check_of_frontier tree 0 t6_1180root t6_1180jobs t6_1180frontier t6_1180all
theorem t6_1181choices : plan7806.choices=[4,9,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1181part0 : t6_1181jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1181frontier : t6_1181root.frontier 0=t6_1181jobs := by rfl
theorem t6_1181all : t6_1181jobs.all (Job.check tree)=true := by
  simp only [t6_1181jobs,List.all_append,List.all_nil,t6_1181part0,Bool.and_self]
theorem t6_1181checked : Checked tree [4,9,10,10,10,10] := by
  refine ⟨plan7806,valid7806,t6_1181choices,?_⟩
  exact check_of_frontier tree 0 t6_1181root t6_1181jobs t6_1181frontier t6_1181all
theorem t6_1182choices : plan7807.choices=[4,10,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1182part0 : t6_1182jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1182frontier : t6_1182root.frontier 0=t6_1182jobs := by rfl
theorem t6_1182all : t6_1182jobs.all (Job.check tree)=true := by
  simp only [t6_1182jobs,List.all_append,List.all_nil,t6_1182part0,Bool.and_self]
theorem t6_1182checked : Checked tree [4,10,7,7,7,7] := by
  refine ⟨plan7807,valid7807,t6_1182choices,?_⟩
  exact check_of_frontier tree 0 t6_1182root t6_1182jobs t6_1182frontier t6_1182all
theorem t6_1183choices : plan7808.choices=[4,10,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1183part0 : t6_1183jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1183frontier : t6_1183root.frontier 0=t6_1183jobs := by rfl
theorem t6_1183all : t6_1183jobs.all (Job.check tree)=true := by
  simp only [t6_1183jobs,List.all_append,List.all_nil,t6_1183part0,Bool.and_self]
theorem t6_1183checked : Checked tree [4,10,10,7,7,7] := by
  refine ⟨plan7808,valid7808,t6_1183choices,?_⟩
  exact check_of_frontier tree 0 t6_1183root t6_1183jobs t6_1183frontier t6_1183all
theorem t6_1184choices : plan7809.choices=[4,10,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1184part0 : t6_1184jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1184frontier : t6_1184root.frontier 0=t6_1184jobs := by rfl
theorem t6_1184all : t6_1184jobs.all (Job.check tree)=true := by
  simp only [t6_1184jobs,List.all_append,List.all_nil,t6_1184part0,Bool.and_self]
theorem t6_1184checked : Checked tree [4,10,10,10,7,7] := by
  refine ⟨plan7809,valid7809,t6_1184choices,?_⟩
  exact check_of_frontier tree 0 t6_1184root t6_1184jobs t6_1184frontier t6_1184all
theorem t6_1185choices : plan7810.choices=[4,10,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1185part0 : t6_1185jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1185frontier : t6_1185root.frontier 0=t6_1185jobs := by rfl
theorem t6_1185all : t6_1185jobs.all (Job.check tree)=true := by
  simp only [t6_1185jobs,List.all_append,List.all_nil,t6_1185part0,Bool.and_self]
theorem t6_1185checked : Checked tree [4,10,10,10,10,7] := by
  refine ⟨plan7810,valid7810,t6_1185choices,?_⟩
  exact check_of_frontier tree 0 t6_1185root t6_1185jobs t6_1185frontier t6_1185all
theorem t6_1186choices : plan7811.choices=[4,10,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1186part0 : t6_1186jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1186frontier : t6_1186root.frontier 0=t6_1186jobs := by rfl
theorem t6_1186all : t6_1186jobs.all (Job.check tree)=true := by
  simp only [t6_1186jobs,List.all_append,List.all_nil,t6_1186part0,Bool.and_self]
theorem t6_1186checked : Checked tree [4,10,10,10,10,10] := by
  refine ⟨plan7811,valid7811,t6_1186choices,?_⟩
  exact check_of_frontier tree 0 t6_1186root t6_1186jobs t6_1186frontier t6_1186all
theorem t6_1187choices : plan6316.choices=[5,3,3,3,3,3].map (options 6 1) := by rfl


theorem t6_1187part0 : t6_1187jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1187frontier : t6_1187root.frontier 0=t6_1187jobs := by rfl
theorem t6_1187all : t6_1187jobs.all (Job.check tree)=true := by
  simp only [t6_1187jobs,List.all_append,List.all_nil,t6_1187part0,Bool.and_self]
theorem t6_1187checked : Checked tree [5,3,3,3,3,3] := by
  refine ⟨plan6316,valid6316,t6_1187choices,?_⟩
  exact check_of_frontier tree 0 t6_1187root t6_1187jobs t6_1187frontier t6_1187all
theorem t6_1188choices : plan6416.choices=[5,3,3,3,3,6].map (options 6 2) := by rfl


theorem t6_1188part0 : t6_1188jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1188frontier : t6_1188root.frontier 0=t6_1188jobs := by rfl
theorem t6_1188all : t6_1188jobs.all (Job.check tree)=true := by
  simp only [t6_1188jobs,List.all_append,List.all_nil,t6_1188part0,Bool.and_self]
theorem t6_1188checked : Checked tree [5,3,3,3,3,6] := by
  refine ⟨plan6416,valid6416,t6_1188choices,?_⟩
  exact check_of_frontier tree 0 t6_1188root t6_1188jobs t6_1188frontier t6_1188all
theorem t6_1189choices : plan6417.choices=[5,3,3,3,3,7].map (options 6 2) := by rfl


theorem t6_1189part0 : t6_1189jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1189part1 : t6_1189jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1189part2 : t6_1189jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1189frontier : t6_1189root.frontier 1=t6_1189jobs := by rfl
theorem t6_1189all : t6_1189jobs.all (Job.check tree)=true := by
  simp only [t6_1189jobs,List.all_append,List.all_nil,t6_1189part0,t6_1189part1,t6_1189part2,Bool.and_self]
theorem t6_1189checked : Checked tree [5,3,3,3,3,7] := by
  refine ⟨plan6417,valid6417,t6_1189choices,?_⟩
  exact check_of_frontier tree 1 t6_1189root t6_1189jobs t6_1189frontier t6_1189all
theorem t6_1190choices : plan6418.choices=[5,3,3,3,3,10].map (options 6 2) := by rfl


theorem t6_1190part0 : t6_1190jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1190frontier : t6_1190root.frontier 0=t6_1190jobs := by rfl
theorem t6_1190all : t6_1190jobs.all (Job.check tree)=true := by
  simp only [t6_1190jobs,List.all_append,List.all_nil,t6_1190part0,Bool.and_self]
theorem t6_1190checked : Checked tree [5,3,3,3,3,10] := by
  refine ⟨plan6418,valid6418,t6_1190choices,?_⟩
  exact check_of_frontier tree 0 t6_1190root t6_1190jobs t6_1190frontier t6_1190all
theorem t6_1191choices : plan6644.choices=[5,3,3,3,6,6].map (options 6 3) := by rfl


theorem t6_1191part0 : t6_1191jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1191part1 : t6_1191jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1191frontier : t6_1191root.frontier 1=t6_1191jobs := by rfl
theorem t6_1191all : t6_1191jobs.all (Job.check tree)=true := by
  simp only [t6_1191jobs,List.all_append,List.all_nil,t6_1191part0,t6_1191part1,Bool.and_self]
theorem t6_1191checked : Checked tree [5,3,3,3,6,6] := by
  refine ⟨plan6644,valid6644,t6_1191choices,?_⟩
  exact check_of_frontier tree 1 t6_1191root t6_1191jobs t6_1191frontier t6_1191all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks123 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1150checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1162checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1163checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1164checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1165checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1166checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1167checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1168checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1169checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1170checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1171checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1151checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1172checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1173checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1174checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1175checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1176checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1177checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1178checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1179checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1180checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1181checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1182checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1183checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1184checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1185checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1152checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1186checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1187checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1188checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1189checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1190checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1191checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1153checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1154checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1155checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1156checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1157checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1158checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1159checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1160checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1161checked⟩
