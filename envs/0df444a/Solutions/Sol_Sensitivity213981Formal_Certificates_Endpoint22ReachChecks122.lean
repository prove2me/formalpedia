-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks122
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:44:53.302427+00:00
-- url     : https://prove2.me/submissions/008ff817-56ea-4663-ab87-9022bcef5841

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks122
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks122
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans080
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













































theorem valid1559 : plan1559.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1561 : plan1561.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1564 : plan1564.Valid := valid_step _ _ _ valid573 (by decide +kernel)











































theorem valid1586 : plan1586.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1587 : plan1587.Valid := valid_step _ _ _ valid579 (by decide +kernel)











theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)



theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)









theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)









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















































































theorem valid3345 : plan3345.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

















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

























































































































































theorem valid3437 : plan3437.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3438 : plan3438.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3439 : plan3439.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3440 : plan3440.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3441 : plan3441.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3442 : plan3442.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3443 : plan3443.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3444 : plan3444.Valid := valid_step _ _ _ valid1597 (by decide +kernel)



theorem valid3446 : plan3446.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3447 : plan3447.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3448 : plan3448.Valid := valid_step _ _ _ valid1605 (by decide +kernel)











theorem valid3454 : plan3454.Valid := valid_step _ _ _ valid1586 (by decide +kernel)




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





























































































theorem valid5519 : plan5519.Valid := valid_step _ _ _ valid3304 (by decide +kernel)







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































theorem valid6640 : plan6640.Valid := valid_step _ _ _ valid5519 (by decide +kernel)

theorem valid6641 : plan6641.Valid := valid_step _ _ _ valid5523 (by decide +kernel)

theorem valid6642 : plan6642.Valid := valid_step _ _ _ valid5524 (by decide +kernel)

theorem valid6643 : plan6643.Valid := valid_step _ _ _ valid5525 (by decide +kernel)


























































































































































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





















































theorem valid3518 : plan3518.Valid := valid_step _ _ _ valid1613 (by decide +kernel)





theorem valid3521 : plan3521.Valid := valid_step _ _ _ valid1616 (by decide +kernel)







theorem valid3525 : plan3525.Valid := valid_step _ _ _ valid1620 (by decide +kernel)





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





































































theorem valid5699 : plan5699.Valid := valid_step _ _ _ valid3345 (by decide +kernel)







theorem valid5703 : plan5703.Valid := valid_step _ _ _ valid3355 (by decide +kernel)

theorem valid5704 : plan5704.Valid := valid_step _ _ _ valid3357 (by decide +kernel)

theorem valid5705 : plan5705.Valid := valid_step _ _ _ valid3358 (by decide +kernel)

















theorem valid5714 : plan5714.Valid := valid_step _ _ _ valid3354 (by decide +kernel)

theorem valid5715 : plan5715.Valid := valid_step _ _ _ valid3355 (by decide +kernel)

theorem valid5716 : plan5716.Valid := valid_step _ _ _ valid3356 (by decide +kernel)

theorem valid5717 : plan5717.Valid := valid_step _ _ _ valid3357 (by decide +kernel)

theorem valid5718 : plan5718.Valid := valid_step _ _ _ valid3358 (by decide +kernel)

theorem valid5719 : plan5719.Valid := valid_step _ _ _ valid3359 (by decide +kernel)


















































































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







































































theorem valid5899 : plan5899.Valid := valid_step _ _ _ valid3437 (by decide +kernel)

theorem valid5900 : plan5900.Valid := valid_step _ _ _ valid3438 (by decide +kernel)

theorem valid5901 : plan5901.Valid := valid_step _ _ _ valid3439 (by decide +kernel)

theorem valid5902 : plan5902.Valid := valid_step _ _ _ valid3441 (by decide +kernel)

theorem valid5903 : plan5903.Valid := valid_step _ _ _ valid3443 (by decide +kernel)

theorem valid5904 : plan5904.Valid := valid_step _ _ _ valid3444 (by decide +kernel)

theorem valid5905 : plan5905.Valid := valid_step _ _ _ valid3446 (by decide +kernel)

theorem valid5906 : plan5906.Valid := valid_step _ _ _ valid3447 (by decide +kernel)

theorem valid5907 : plan5907.Valid := valid_step _ _ _ valid3448 (by decide +kernel)

theorem valid5908 : plan5908.Valid := valid_step _ _ _ valid3454 (by decide +kernel)























theorem valid5920 : plan5920.Valid := valid_step _ _ _ valid3490 (by decide +kernel)













theorem valid5927 : plan5927.Valid := valid_step _ _ _ valid3440 (by decide +kernel)

theorem valid5928 : plan5928.Valid := valid_step _ _ _ valid3441 (by decide +kernel)

theorem valid5929 : plan5929.Valid := valid_step _ _ _ valid3442 (by decide +kernel)

theorem valid5930 : plan5930.Valid := valid_step _ _ _ valid3443 (by decide +kernel)












































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





























































































































































theorem valid6415 : plan6415.Valid := valid_step _ _ _ valid5410 (by decide +kernel)


































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















































theorem valid7032 : plan7032.Valid := valid_step _ _ _ valid5699 (by decide +kernel)

theorem valid7033 : plan7033.Valid := valid_step _ _ _ valid5703 (by decide +kernel)

theorem valid7034 : plan7034.Valid := valid_step _ _ _ valid5704 (by decide +kernel)

theorem valid7035 : plan7035.Valid := valid_step _ _ _ valid5705 (by decide +kernel)

theorem valid7036 : plan7036.Valid := valid_step _ _ _ valid5714 (by decide +kernel)

theorem valid7037 : plan7037.Valid := valid_step _ _ _ valid5715 (by decide +kernel)

theorem valid7038 : plan7038.Valid := valid_step _ _ _ valid5716 (by decide +kernel)

theorem valid7039 : plan7039.Valid := valid_step _ _ _ valid5717 (by decide +kernel)

theorem valid7040 : plan7040.Valid := valid_step _ _ _ valid5718 (by decide +kernel)

theorem valid7041 : plan7041.Valid := valid_step _ _ _ valid5719 (by decide +kernel)






























































































































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































theorem valid7504 : plan7504.Valid := valid_step _ _ _ valid5862 (by decide +kernel)

theorem valid7505 : plan7505.Valid := valid_step _ _ _ valid5863 (by decide +kernel)

theorem valid7506 : plan7506.Valid := valid_step _ _ _ valid5899 (by decide +kernel)

theorem valid7507 : plan7507.Valid := valid_step _ _ _ valid5900 (by decide +kernel)

theorem valid7508 : plan7508.Valid := valid_step _ _ _ valid5901 (by decide +kernel)

theorem valid7509 : plan7509.Valid := valid_step _ _ _ valid5902 (by decide +kernel)

theorem valid7510 : plan7510.Valid := valid_step _ _ _ valid5903 (by decide +kernel)

theorem valid7511 : plan7511.Valid := valid_step _ _ _ valid5904 (by decide +kernel)

theorem valid7512 : plan7512.Valid := valid_step _ _ _ valid5905 (by decide +kernel)

theorem valid7513 : plan7513.Valid := valid_step _ _ _ valid5906 (by decide +kernel)

theorem valid7514 : plan7514.Valid := valid_step _ _ _ valid5907 (by decide +kernel)

theorem valid7515 : plan7515.Valid := valid_step _ _ _ valid5908 (by decide +kernel)

theorem valid7516 : plan7516.Valid := valid_step _ _ _ valid5920 (by decide +kernel)

theorem valid7517 : plan7517.Valid := valid_step _ _ _ valid5927 (by decide +kernel)

theorem valid7518 : plan7518.Valid := valid_step _ _ _ valid5928 (by decide +kernel)

theorem valid7519 : plan7519.Valid := valid_step _ _ _ valid5929 (by decide +kernel)

theorem valid7520 : plan7520.Valid := valid_step _ _ _ valid5930 (by decide +kernel)
































































































































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

theorem valid6055 : plan6055.Valid := valid_step _ _ _ valid3518 (by decide +kernel)

theorem valid6056 : plan6056.Valid := valid_step _ _ _ valid3521 (by decide +kernel)

theorem valid6057 : plan6057.Valid := valid_step _ _ _ valid3525 (by decide +kernel)

theorem valid6058 : plan6058.Valid := valid_step _ _ _ valid3529 (by decide +kernel)

theorem valid6059 : plan6059.Valid := valid_step _ _ _ valid3531 (by decide +kernel)

theorem valid6060 : plan6060.Valid := valid_step _ _ _ valid3532 (by decide +kernel)

theorem valid6061 : plan6061.Valid := valid_step _ _ _ valid3534 (by decide +kernel)

theorem valid6062 : plan6062.Valid := valid_step _ _ _ valid3535 (by decide +kernel)

theorem valid6063 : plan6063.Valid := valid_step _ _ _ valid3536 (by decide +kernel)

theorem valid6064 : plan6064.Valid := valid_step _ _ _ valid3538 (by decide +kernel)

theorem valid6065 : plan6065.Valid := valid_step _ _ _ valid3539 (by decide +kernel)

theorem valid6066 : plan6066.Valid := valid_step _ _ _ valid3543 (by decide +kernel)

theorem valid6067 : plan6067.Valid := valid_step _ _ _ valid3546 (by decide +kernel)

theorem valid6068 : plan6068.Valid := valid_step _ _ _ valid3550 (by decide +kernel)

theorem valid6069 : plan6069.Valid := valid_step _ _ _ valid3553 (by decide +kernel)

theorem valid6070 : plan6070.Valid := valid_step _ _ _ valid3554 (by decide +kernel)

theorem valid6071 : plan6071.Valid := valid_step _ _ _ valid3555 (by decide +kernel)


















































































































































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

























































































































theorem valid7741 : plan7741.Valid := valid_step _ _ _ valid6023 (by decide +kernel)

theorem valid7742 : plan7742.Valid := valid_step _ _ _ valid6025 (by decide +kernel)

theorem valid7743 : plan7743.Valid := valid_step _ _ _ valid6026 (by decide +kernel)

theorem valid7744 : plan7744.Valid := valid_step _ _ _ valid6028 (by decide +kernel)

theorem valid7745 : plan7745.Valid := valid_step _ _ _ valid6030 (by decide +kernel)

theorem valid7746 : plan7746.Valid := valid_step _ _ _ valid6032 (by decide +kernel)

theorem valid7747 : plan7747.Valid := valid_step _ _ _ valid6033 (by decide +kernel)

theorem valid7748 : plan7748.Valid := valid_step _ _ _ valid6035 (by decide +kernel)

theorem valid7749 : plan7749.Valid := valid_step _ _ _ valid6036 (by decide +kernel)

theorem valid7750 : plan7750.Valid := valid_step _ _ _ valid6037 (by decide +kernel)

theorem valid7751 : plan7751.Valid := valid_step _ _ _ valid6038 (by decide +kernel)

theorem valid7752 : plan7752.Valid := valid_step _ _ _ valid6039 (by decide +kernel)

theorem valid7753 : plan7753.Valid := valid_step _ _ _ valid6040 (by decide +kernel)

theorem valid7754 : plan7754.Valid := valid_step _ _ _ valid6041 (by decide +kernel)

theorem valid7755 : plan7755.Valid := valid_step _ _ _ valid6042 (by decide +kernel)

theorem valid7756 : plan7756.Valid := valid_step _ _ _ valid6043 (by decide +kernel)

theorem valid7757 : plan7757.Valid := valid_step _ _ _ valid6044 (by decide +kernel)

theorem valid7758 : plan7758.Valid := valid_step _ _ _ valid6045 (by decide +kernel)

theorem valid7759 : plan7759.Valid := valid_step _ _ _ valid6046 (by decide +kernel)

theorem valid7760 : plan7760.Valid := valid_step _ _ _ valid6047 (by decide +kernel)

theorem valid7761 : plan7761.Valid := valid_step _ _ _ valid6048 (by decide +kernel)

theorem valid7762 : plan7762.Valid := valid_step _ _ _ valid6049 (by decide +kernel)

theorem valid7763 : plan7763.Valid := valid_step _ _ _ valid6050 (by decide +kernel)

theorem valid7764 : plan7764.Valid := valid_step _ _ _ valid6051 (by decide +kernel)

theorem valid7765 : plan7765.Valid := valid_step _ _ _ valid6052 (by decide +kernel)

theorem valid7766 : plan7766.Valid := valid_step _ _ _ valid6053 (by decide +kernel)

theorem valid7767 : plan7767.Valid := valid_step _ _ _ valid6054 (by decide +kernel)

theorem valid7768 : plan7768.Valid := valid_step _ _ _ valid6055 (by decide +kernel)

theorem valid7769 : plan7769.Valid := valid_step _ _ _ valid6056 (by decide +kernel)

theorem valid7770 : plan7770.Valid := valid_step _ _ _ valid6057 (by decide +kernel)

theorem valid7771 : plan7771.Valid := valid_step _ _ _ valid6058 (by decide +kernel)

theorem valid7772 : plan7772.Valid := valid_step _ _ _ valid6059 (by decide +kernel)

theorem valid7773 : plan7773.Valid := valid_step _ _ _ valid6060 (by decide +kernel)

theorem valid7774 : plan7774.Valid := valid_step _ _ _ valid6061 (by decide +kernel)

theorem valid7775 : plan7775.Valid := valid_step _ _ _ valid6062 (by decide +kernel)

theorem valid7776 : plan7776.Valid := valid_step _ _ _ valid6063 (by decide +kernel)
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

theorem valid7777 : plan7777.Valid := valid_step _ _ _ valid6064 (by decide +kernel)

theorem valid7778 : plan7778.Valid := valid_step _ _ _ valid6065 (by decide +kernel)

theorem valid7779 : plan7779.Valid := valid_step _ _ _ valid6066 (by decide +kernel)

theorem valid7780 : plan7780.Valid := valid_step _ _ _ valid6067 (by decide +kernel)

theorem valid7781 : plan7781.Valid := valid_step _ _ _ valid6068 (by decide +kernel)

theorem valid7782 : plan7782.Valid := valid_step _ _ _ valid6069 (by decide +kernel)

theorem valid7783 : plan7783.Valid := valid_step _ _ _ valid6070 (by decide +kernel)

theorem valid7784 : plan7784.Valid := valid_step _ _ _ valid6071 (by decide +kernel)
















































































































































































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
theorem t6_1074choices : plan7504.choices=[4,5,9,3,7,7].map (options 6 5) := by rfl


theorem t6_1074part0 : t6_1074jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1074frontier : t6_1074root.frontier 0=t6_1074jobs := by rfl
theorem t6_1074all : t6_1074jobs.all (Job.check tree)=true := by
  simp only [t6_1074jobs,List.all_append,List.all_nil,t6_1074part0,Bool.and_self]
theorem t6_1074checked : Checked tree [4,5,9,3,7,7] := by
  refine ⟨plan7504,valid7504,t6_1074choices,?_⟩
  exact check_of_frontier tree 0 t6_1074root t6_1074jobs t6_1074frontier t6_1074all
theorem t6_1075choices : plan7505.choices=[4,5,9,3,10,7].map (options 6 5) := by rfl


theorem t6_1075part0 : t6_1075jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1075frontier : t6_1075root.frontier 0=t6_1075jobs := by rfl
theorem t6_1075all : t6_1075jobs.all (Job.check tree)=true := by
  simp only [t6_1075jobs,List.all_append,List.all_nil,t6_1075part0,Bool.and_self]
theorem t6_1075checked : Checked tree [4,5,9,3,10,7] := by
  refine ⟨plan7505,valid7505,t6_1075choices,?_⟩
  exact check_of_frontier tree 0 t6_1075root t6_1075jobs t6_1075frontier t6_1075all
theorem t6_1076choices : plan7741.choices=[4,5,9,6,6,7].map (options 6 6) := by rfl


theorem t6_1076part0 : t6_1076jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1076frontier : t6_1076root.frontier 0=t6_1076jobs := by rfl
theorem t6_1076all : t6_1076jobs.all (Job.check tree)=true := by
  simp only [t6_1076jobs,List.all_append,List.all_nil,t6_1076part0,Bool.and_self]
theorem t6_1076checked : Checked tree [4,5,9,6,6,7] := by
  refine ⟨plan7741,valid7741,t6_1076choices,?_⟩
  exact check_of_frontier tree 0 t6_1076root t6_1076jobs t6_1076frontier t6_1076all
theorem t6_1077choices : plan7742.choices=[4,5,9,6,7,7].map (options 6 6) := by rfl


theorem t6_1077part0 : t6_1077jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1077frontier : t6_1077root.frontier 0=t6_1077jobs := by rfl
theorem t6_1077all : t6_1077jobs.all (Job.check tree)=true := by
  simp only [t6_1077jobs,List.all_append,List.all_nil,t6_1077part0,Bool.and_self]
theorem t6_1077checked : Checked tree [4,5,9,6,7,7] := by
  refine ⟨plan7742,valid7742,t6_1077choices,?_⟩
  exact check_of_frontier tree 0 t6_1077root t6_1077jobs t6_1077frontier t6_1077all
theorem t6_1078choices : plan7743.choices=[4,5,9,6,10,7].map (options 6 6) := by rfl


theorem t6_1078part0 : t6_1078jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1078frontier : t6_1078root.frontier 0=t6_1078jobs := by rfl
theorem t6_1078all : t6_1078jobs.all (Job.check tree)=true := by
  simp only [t6_1078jobs,List.all_append,List.all_nil,t6_1078part0,Bool.and_self]
theorem t6_1078checked : Checked tree [4,5,9,6,10,7] := by
  refine ⟨plan7743,valid7743,t6_1078choices,?_⟩
  exact check_of_frontier tree 0 t6_1078root t6_1078jobs t6_1078frontier t6_1078all
theorem t6_1079choices : plan7744.choices=[4,5,9,7,7,7].map (options 6 6) := by rfl


theorem t6_1079part0 : t6_1079jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1079frontier : t6_1079root.frontier 0=t6_1079jobs := by rfl
theorem t6_1079all : t6_1079jobs.all (Job.check tree)=true := by
  simp only [t6_1079jobs,List.all_append,List.all_nil,t6_1079part0,Bool.and_self]
theorem t6_1079checked : Checked tree [4,5,9,7,7,7] := by
  refine ⟨plan7744,valid7744,t6_1079choices,?_⟩
  exact check_of_frontier tree 0 t6_1079root t6_1079jobs t6_1079frontier t6_1079all
theorem t6_1080choices : plan7745.choices=[4,5,9,9,7,7].map (options 6 6) := by rfl


theorem t6_1080part0 : t6_1080jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1080frontier : t6_1080root.frontier 0=t6_1080jobs := by rfl
theorem t6_1080all : t6_1080jobs.all (Job.check tree)=true := by
  simp only [t6_1080jobs,List.all_append,List.all_nil,t6_1080part0,Bool.and_self]
theorem t6_1080checked : Checked tree [4,5,9,9,7,7] := by
  refine ⟨plan7745,valid7745,t6_1080choices,?_⟩
  exact check_of_frontier tree 0 t6_1080root t6_1080jobs t6_1080frontier t6_1080all
theorem t6_1081choices : plan7746.choices=[4,5,9,10,7,7].map (options 6 6) := by rfl


theorem t6_1081part0 : t6_1081jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1081frontier : t6_1081root.frontier 0=t6_1081jobs := by rfl
theorem t6_1081all : t6_1081jobs.all (Job.check tree)=true := by
  simp only [t6_1081jobs,List.all_append,List.all_nil,t6_1081part0,Bool.and_self]
theorem t6_1081checked : Checked tree [4,5,9,10,7,7] := by
  refine ⟨plan7746,valid7746,t6_1081choices,?_⟩
  exact check_of_frontier tree 0 t6_1081root t6_1081jobs t6_1081frontier t6_1081all
theorem t6_1082choices : plan7747.choices=[4,5,9,10,10,7].map (options 6 6) := by rfl


theorem t6_1082part0 : t6_1082jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1082frontier : t6_1082root.frontier 0=t6_1082jobs := by rfl
theorem t6_1082all : t6_1082jobs.all (Job.check tree)=true := by
  simp only [t6_1082jobs,List.all_append,List.all_nil,t6_1082part0,Bool.and_self]
theorem t6_1082checked : Checked tree [4,5,9,10,10,7] := by
  refine ⟨plan7747,valid7747,t6_1082choices,?_⟩
  exact check_of_frontier tree 0 t6_1082root t6_1082jobs t6_1082frontier t6_1082all
theorem t6_1083choices : plan7748.choices=[4,5,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1083part0 : t6_1083jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1083frontier : t6_1083root.frontier 0=t6_1083jobs := by rfl
theorem t6_1083all : t6_1083jobs.all (Job.check tree)=true := by
  simp only [t6_1083jobs,List.all_append,List.all_nil,t6_1083part0,Bool.and_self]
theorem t6_1083checked : Checked tree [4,5,10,7,7,7] := by
  refine ⟨plan7748,valid7748,t6_1083choices,?_⟩
  exact check_of_frontier tree 0 t6_1083root t6_1083jobs t6_1083frontier t6_1083all
theorem t6_1084choices : plan7749.choices=[4,5,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1084part0 : t6_1084jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1084frontier : t6_1084root.frontier 0=t6_1084jobs := by rfl
theorem t6_1084all : t6_1084jobs.all (Job.check tree)=true := by
  simp only [t6_1084jobs,List.all_append,List.all_nil,t6_1084part0,Bool.and_self]
theorem t6_1084checked : Checked tree [4,5,10,10,7,7] := by
  refine ⟨plan7749,valid7749,t6_1084choices,?_⟩
  exact check_of_frontier tree 0 t6_1084root t6_1084jobs t6_1084frontier t6_1084all
theorem t6_1085choices : plan7750.choices=[4,5,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1085part0 : t6_1085jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1085frontier : t6_1085root.frontier 0=t6_1085jobs := by rfl
theorem t6_1085all : t6_1085jobs.all (Job.check tree)=true := by
  simp only [t6_1085jobs,List.all_append,List.all_nil,t6_1085part0,Bool.and_self]
theorem t6_1085checked : Checked tree [4,5,10,10,10,7] := by
  refine ⟨plan7750,valid7750,t6_1085choices,?_⟩
  exact check_of_frontier tree 0 t6_1085root t6_1085jobs t6_1085frontier t6_1085all
theorem t6_1086choices : plan7751.choices=[4,5,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1086part0 : t6_1086jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1086frontier : t6_1086root.frontier 0=t6_1086jobs := by rfl
theorem t6_1086all : t6_1086jobs.all (Job.check tree)=true := by
  simp only [t6_1086jobs,List.all_append,List.all_nil,t6_1086part0,Bool.and_self]
theorem t6_1086checked : Checked tree [4,5,10,10,10,10] := by
  refine ⟨plan7751,valid7751,t6_1086choices,?_⟩
  exact check_of_frontier tree 0 t6_1086root t6_1086jobs t6_1086frontier t6_1086all
theorem t6_1087choices : plan7752.choices=[4,6,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1087part0 : t6_1087jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1087frontier : t6_1087root.frontier 0=t6_1087jobs := by rfl
theorem t6_1087all : t6_1087jobs.all (Job.check tree)=true := by
  simp only [t6_1087jobs,List.all_append,List.all_nil,t6_1087part0,Bool.and_self]
theorem t6_1087checked : Checked tree [4,6,6,6,6,6] := by
  refine ⟨plan7752,valid7752,t6_1087choices,?_⟩
  exact check_of_frontier tree 0 t6_1087root t6_1087jobs t6_1087frontier t6_1087all
theorem t6_1088choices : plan7753.choices=[4,6,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1088part0 : t6_1088jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1088frontier : t6_1088root.frontier 0=t6_1088jobs := by rfl
theorem t6_1088all : t6_1088jobs.all (Job.check tree)=true := by
  simp only [t6_1088jobs,List.all_append,List.all_nil,t6_1088part0,Bool.and_self]
theorem t6_1088checked : Checked tree [4,6,6,6,6,7] := by
  refine ⟨plan7753,valid7753,t6_1088choices,?_⟩
  exact check_of_frontier tree 0 t6_1088root t6_1088jobs t6_1088frontier t6_1088all
theorem t6_1089choices : plan7754.choices=[4,6,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1089part0 : t6_1089jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1089frontier : t6_1089root.frontier 0=t6_1089jobs := by rfl
theorem t6_1089all : t6_1089jobs.all (Job.check tree)=true := by
  simp only [t6_1089jobs,List.all_append,List.all_nil,t6_1089part0,Bool.and_self]
theorem t6_1089checked : Checked tree [4,6,6,6,6,10] := by
  refine ⟨plan7754,valid7754,t6_1089choices,?_⟩
  exact check_of_frontier tree 0 t6_1089root t6_1089jobs t6_1089frontier t6_1089all
theorem t6_1090choices : plan7755.choices=[4,6,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1090part0 : t6_1090jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1090frontier : t6_1090root.frontier 0=t6_1090jobs := by rfl
theorem t6_1090all : t6_1090jobs.all (Job.check tree)=true := by
  simp only [t6_1090jobs,List.all_append,List.all_nil,t6_1090part0,Bool.and_self]
theorem t6_1090checked : Checked tree [4,6,6,6,7,7] := by
  refine ⟨plan7755,valid7755,t6_1090choices,?_⟩
  exact check_of_frontier tree 0 t6_1090root t6_1090jobs t6_1090frontier t6_1090all
theorem t6_1091choices : plan7756.choices=[4,6,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1091part0 : t6_1091jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1091frontier : t6_1091root.frontier 0=t6_1091jobs := by rfl
theorem t6_1091all : t6_1091jobs.all (Job.check tree)=true := by
  simp only [t6_1091jobs,List.all_append,List.all_nil,t6_1091part0,Bool.and_self]
theorem t6_1091checked : Checked tree [4,6,6,6,10,7] := by
  refine ⟨plan7756,valid7756,t6_1091choices,?_⟩
  exact check_of_frontier tree 0 t6_1091root t6_1091jobs t6_1091frontier t6_1091all
theorem t6_1092choices : plan7757.choices=[4,6,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1092part0 : t6_1092jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1092frontier : t6_1092root.frontier 0=t6_1092jobs := by rfl
theorem t6_1092all : t6_1092jobs.all (Job.check tree)=true := by
  simp only [t6_1092jobs,List.all_append,List.all_nil,t6_1092part0,Bool.and_self]
theorem t6_1092checked : Checked tree [4,6,6,6,10,10] := by
  refine ⟨plan7757,valid7757,t6_1092choices,?_⟩
  exact check_of_frontier tree 0 t6_1092root t6_1092jobs t6_1092frontier t6_1092all
theorem t6_1093choices : plan7758.choices=[4,6,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1093part0 : t6_1093jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1093frontier : t6_1093root.frontier 0=t6_1093jobs := by rfl
theorem t6_1093all : t6_1093jobs.all (Job.check tree)=true := by
  simp only [t6_1093jobs,List.all_append,List.all_nil,t6_1093part0,Bool.and_self]
theorem t6_1093checked : Checked tree [4,6,6,7,7,7] := by
  refine ⟨plan7758,valid7758,t6_1093choices,?_⟩
  exact check_of_frontier tree 0 t6_1093root t6_1093jobs t6_1093frontier t6_1093all
theorem t6_1094choices : plan7759.choices=[4,6,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1094part0 : t6_1094jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1094frontier : t6_1094root.frontier 0=t6_1094jobs := by rfl
theorem t6_1094all : t6_1094jobs.all (Job.check tree)=true := by
  simp only [t6_1094jobs,List.all_append,List.all_nil,t6_1094part0,Bool.and_self]
theorem t6_1094checked : Checked tree [4,6,6,10,7,7] := by
  refine ⟨plan7759,valid7759,t6_1094choices,?_⟩
  exact check_of_frontier tree 0 t6_1094root t6_1094jobs t6_1094frontier t6_1094all
theorem t6_1095choices : plan7760.choices=[4,6,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1095part0 : t6_1095jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1095frontier : t6_1095root.frontier 0=t6_1095jobs := by rfl
theorem t6_1095all : t6_1095jobs.all (Job.check tree)=true := by
  simp only [t6_1095jobs,List.all_append,List.all_nil,t6_1095part0,Bool.and_self]
theorem t6_1095checked : Checked tree [4,6,6,10,10,7] := by
  refine ⟨plan7760,valid7760,t6_1095choices,?_⟩
  exact check_of_frontier tree 0 t6_1095root t6_1095jobs t6_1095frontier t6_1095all
theorem t6_1096choices : plan7761.choices=[4,6,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1096part0 : t6_1096jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1096frontier : t6_1096root.frontier 0=t6_1096jobs := by rfl
theorem t6_1096all : t6_1096jobs.all (Job.check tree)=true := by
  simp only [t6_1096jobs,List.all_append,List.all_nil,t6_1096part0,Bool.and_self]
theorem t6_1096checked : Checked tree [4,6,6,10,10,10] := by
  refine ⟨plan7761,valid7761,t6_1096choices,?_⟩
  exact check_of_frontier tree 0 t6_1096root t6_1096jobs t6_1096frontier t6_1096all
theorem t6_1097choices : plan7762.choices=[4,6,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1097part0 : t6_1097jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1097frontier : t6_1097root.frontier 0=t6_1097jobs := by rfl
theorem t6_1097all : t6_1097jobs.all (Job.check tree)=true := by
  simp only [t6_1097jobs,List.all_append,List.all_nil,t6_1097part0,Bool.and_self]
theorem t6_1097checked : Checked tree [4,6,7,7,7,7] := by
  refine ⟨plan7762,valid7762,t6_1097choices,?_⟩
  exact check_of_frontier tree 0 t6_1097root t6_1097jobs t6_1097frontier t6_1097all
theorem t6_1098choices : plan7763.choices=[4,6,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1098part0 : t6_1098jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1098frontier : t6_1098root.frontier 0=t6_1098jobs := by rfl
theorem t6_1098all : t6_1098jobs.all (Job.check tree)=true := by
  simp only [t6_1098jobs,List.all_append,List.all_nil,t6_1098part0,Bool.and_self]
theorem t6_1098checked : Checked tree [4,6,10,7,7,7] := by
  refine ⟨plan7763,valid7763,t6_1098choices,?_⟩
  exact check_of_frontier tree 0 t6_1098root t6_1098jobs t6_1098frontier t6_1098all
theorem t6_1099choices : plan7764.choices=[4,6,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1099part0 : t6_1099jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1099frontier : t6_1099root.frontier 0=t6_1099jobs := by rfl
theorem t6_1099all : t6_1099jobs.all (Job.check tree)=true := by
  simp only [t6_1099jobs,List.all_append,List.all_nil,t6_1099part0,Bool.and_self]
theorem t6_1099checked : Checked tree [4,6,10,10,7,7] := by
  refine ⟨plan7764,valid7764,t6_1099choices,?_⟩
  exact check_of_frontier tree 0 t6_1099root t6_1099jobs t6_1099frontier t6_1099all
theorem t6_1100choices : plan7765.choices=[4,6,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1100part0 : t6_1100jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1100frontier : t6_1100root.frontier 0=t6_1100jobs := by rfl
theorem t6_1100all : t6_1100jobs.all (Job.check tree)=true := by
  simp only [t6_1100jobs,List.all_append,List.all_nil,t6_1100part0,Bool.and_self]
theorem t6_1100checked : Checked tree [4,6,10,10,10,7] := by
  refine ⟨plan7765,valid7765,t6_1100choices,?_⟩
  exact check_of_frontier tree 0 t6_1100root t6_1100jobs t6_1100frontier t6_1100all
theorem t6_1101choices : plan7766.choices=[4,6,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1101part0 : t6_1101jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1101frontier : t6_1101root.frontier 0=t6_1101jobs := by rfl
theorem t6_1101all : t6_1101jobs.all (Job.check tree)=true := by
  simp only [t6_1101jobs,List.all_append,List.all_nil,t6_1101part0,Bool.and_self]
theorem t6_1101checked : Checked tree [4,6,10,10,10,10] := by
  refine ⟨plan7766,valid7766,t6_1101choices,?_⟩
  exact check_of_frontier tree 0 t6_1101root t6_1101jobs t6_1101frontier t6_1101all
theorem t6_1102choices : plan7767.choices=[4,7,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1102part0 : t6_1102jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1102frontier : t6_1102root.frontier 0=t6_1102jobs := by rfl
theorem t6_1102all : t6_1102jobs.all (Job.check tree)=true := by
  simp only [t6_1102jobs,List.all_append,List.all_nil,t6_1102part0,Bool.and_self]
theorem t6_1102checked : Checked tree [4,7,7,7,7,7] := by
  refine ⟨plan7767,valid7767,t6_1102choices,?_⟩
  exact check_of_frontier tree 0 t6_1102root t6_1102jobs t6_1102frontier t6_1102all
theorem t6_1103choices : plan7032.choices=[4,8,2,3,7,7].map (options 6 4) := by rfl


theorem t6_1103part0 : t6_1103jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1103frontier : t6_1103root.frontier 0=t6_1103jobs := by rfl
theorem t6_1103all : t6_1103jobs.all (Job.check tree)=true := by
  simp only [t6_1103jobs,List.all_append,List.all_nil,t6_1103part0,Bool.and_self]
theorem t6_1103checked : Checked tree [4,8,2,3,7,7] := by
  refine ⟨plan7032,valid7032,t6_1103choices,?_⟩
  exact check_of_frontier tree 0 t6_1103root t6_1103jobs t6_1103frontier t6_1103all
theorem t6_1104choices : plan7506.choices=[4,8,2,6,7,7].map (options 6 5) := by rfl


theorem t6_1104part0 : t6_1104jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1104frontier : t6_1104root.frontier 0=t6_1104jobs := by rfl
theorem t6_1104all : t6_1104jobs.all (Job.check tree)=true := by
  simp only [t6_1104jobs,List.all_append,List.all_nil,t6_1104part0,Bool.and_self]
theorem t6_1104checked : Checked tree [4,8,2,6,7,7] := by
  refine ⟨plan7506,valid7506,t6_1104choices,?_⟩
  exact check_of_frontier tree 0 t6_1104root t6_1104jobs t6_1104frontier t6_1104all
theorem t6_1105choices : plan7507.choices=[4,8,2,7,7,7].map (options 6 5) := by rfl


theorem t6_1105part0 : t6_1105jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1105frontier : t6_1105root.frontier 0=t6_1105jobs := by rfl
theorem t6_1105all : t6_1105jobs.all (Job.check tree)=true := by
  simp only [t6_1105jobs,List.all_append,List.all_nil,t6_1105part0,Bool.and_self]
theorem t6_1105checked : Checked tree [4,8,2,7,7,7] := by
  refine ⟨plan7507,valid7507,t6_1105choices,?_⟩
  exact check_of_frontier tree 0 t6_1105root t6_1105jobs t6_1105frontier t6_1105all
theorem t6_1106choices : plan7508.choices=[4,8,2,10,7,7].map (options 6 5) := by rfl


theorem t6_1106part0 : t6_1106jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1106frontier : t6_1106root.frontier 0=t6_1106jobs := by rfl
theorem t6_1106all : t6_1106jobs.all (Job.check tree)=true := by
  simp only [t6_1106jobs,List.all_append,List.all_nil,t6_1106part0,Bool.and_self]
theorem t6_1106checked : Checked tree [4,8,2,10,7,7] := by
  refine ⟨plan7508,valid7508,t6_1106choices,?_⟩
  exact check_of_frontier tree 0 t6_1106root t6_1106jobs t6_1106frontier t6_1106all
theorem t6_1107choices : plan6640.choices=[4,8,3,3,3,7].map (options 6 3) := by rfl


theorem t6_1107part0 : t6_1107jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1107frontier : t6_1107root.frontier 0=t6_1107jobs := by rfl
theorem t6_1107all : t6_1107jobs.all (Job.check tree)=true := by
  simp only [t6_1107jobs,List.all_append,List.all_nil,t6_1107part0,Bool.and_self]
theorem t6_1107checked : Checked tree [4,8,3,3,3,7] := by
  refine ⟨plan6640,valid6640,t6_1107choices,?_⟩
  exact check_of_frontier tree 0 t6_1107root t6_1107jobs t6_1107frontier t6_1107all
theorem t6_1108choices : plan7033.choices=[4,8,3,3,6,7].map (options 6 4) := by rfl


theorem t6_1108part0 : t6_1108jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1108frontier : t6_1108root.frontier 0=t6_1108jobs := by rfl
theorem t6_1108all : t6_1108jobs.all (Job.check tree)=true := by
  simp only [t6_1108jobs,List.all_append,List.all_nil,t6_1108part0,Bool.and_self]
theorem t6_1108checked : Checked tree [4,8,3,3,6,7] := by
  refine ⟨plan7033,valid7033,t6_1108choices,?_⟩
  exact check_of_frontier tree 0 t6_1108root t6_1108jobs t6_1108frontier t6_1108all
theorem t6_1109choices : plan7034.choices=[4,8,3,3,7,7].map (options 6 4) := by rfl


theorem t6_1109part0 : t6_1109jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1109frontier : t6_1109root.frontier 0=t6_1109jobs := by rfl
theorem t6_1109all : t6_1109jobs.all (Job.check tree)=true := by
  simp only [t6_1109jobs,List.all_append,List.all_nil,t6_1109part0,Bool.and_self]
theorem t6_1109checked : Checked tree [4,8,3,3,7,7] := by
  refine ⟨plan7034,valid7034,t6_1109choices,?_⟩
  exact check_of_frontier tree 0 t6_1109root t6_1109jobs t6_1109frontier t6_1109all
theorem t6_1110choices : plan7035.choices=[4,8,3,3,10,7].map (options 6 4) := by rfl


theorem t6_1110part0 : t6_1110jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1110frontier : t6_1110root.frontier 0=t6_1110jobs := by rfl
theorem t6_1110all : t6_1110jobs.all (Job.check tree)=true := by
  simp only [t6_1110jobs,List.all_append,List.all_nil,t6_1110part0,Bool.and_self]
theorem t6_1110checked : Checked tree [4,8,3,3,10,7] := by
  refine ⟨plan7035,valid7035,t6_1110choices,?_⟩
  exact check_of_frontier tree 0 t6_1110root t6_1110jobs t6_1110frontier t6_1110all
theorem t6_1111choices : plan7509.choices=[4,8,3,6,6,7].map (options 6 5) := by rfl


theorem t6_1111part0 : t6_1111jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1111frontier : t6_1111root.frontier 0=t6_1111jobs := by rfl
theorem t6_1111all : t6_1111jobs.all (Job.check tree)=true := by
  simp only [t6_1111jobs,List.all_append,List.all_nil,t6_1111part0,Bool.and_self]
theorem t6_1111checked : Checked tree [4,8,3,6,6,7] := by
  refine ⟨plan7509,valid7509,t6_1111choices,?_⟩
  exact check_of_frontier tree 0 t6_1111root t6_1111jobs t6_1111frontier t6_1111all
theorem t6_1112choices : plan7510.choices=[4,8,3,6,7,7].map (options 6 5) := by rfl


theorem t6_1112part0 : t6_1112jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1112frontier : t6_1112root.frontier 0=t6_1112jobs := by rfl
theorem t6_1112all : t6_1112jobs.all (Job.check tree)=true := by
  simp only [t6_1112jobs,List.all_append,List.all_nil,t6_1112part0,Bool.and_self]
theorem t6_1112checked : Checked tree [4,8,3,6,7,7] := by
  refine ⟨plan7510,valid7510,t6_1112choices,?_⟩
  exact check_of_frontier tree 0 t6_1112root t6_1112jobs t6_1112frontier t6_1112all
theorem t6_1113choices : plan7511.choices=[4,8,3,6,10,7].map (options 6 5) := by rfl


theorem t6_1113part0 : t6_1113jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1113frontier : t6_1113root.frontier 0=t6_1113jobs := by rfl
theorem t6_1113all : t6_1113jobs.all (Job.check tree)=true := by
  simp only [t6_1113jobs,List.all_append,List.all_nil,t6_1113part0,Bool.and_self]
theorem t6_1113checked : Checked tree [4,8,3,6,10,7] := by
  refine ⟨plan7511,valid7511,t6_1113choices,?_⟩
  exact check_of_frontier tree 0 t6_1113root t6_1113jobs t6_1113frontier t6_1113all
theorem t6_1114choices : plan7512.choices=[4,8,3,7,7,7].map (options 6 5) := by rfl


theorem t6_1114part0 : t6_1114jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1114frontier : t6_1114root.frontier 0=t6_1114jobs := by rfl
theorem t6_1114all : t6_1114jobs.all (Job.check tree)=true := by
  simp only [t6_1114jobs,List.all_append,List.all_nil,t6_1114part0,Bool.and_self]
theorem t6_1114checked : Checked tree [4,8,3,7,7,7] := by
  refine ⟨plan7512,valid7512,t6_1114choices,?_⟩
  exact check_of_frontier tree 0 t6_1114root t6_1114jobs t6_1114frontier t6_1114all
theorem t6_1115choices : plan7513.choices=[4,8,3,10,7,7].map (options 6 5) := by rfl


theorem t6_1115part0 : t6_1115jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1115frontier : t6_1115root.frontier 0=t6_1115jobs := by rfl
theorem t6_1115all : t6_1115jobs.all (Job.check tree)=true := by
  simp only [t6_1115jobs,List.all_append,List.all_nil,t6_1115part0,Bool.and_self]
theorem t6_1115checked : Checked tree [4,8,3,10,7,7] := by
  refine ⟨plan7513,valid7513,t6_1115choices,?_⟩
  exact check_of_frontier tree 0 t6_1115root t6_1115jobs t6_1115frontier t6_1115all
theorem t6_1116choices : plan7514.choices=[4,8,3,10,10,7].map (options 6 5) := by rfl


theorem t6_1116part0 : t6_1116jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1116frontier : t6_1116root.frontier 0=t6_1116jobs := by rfl
theorem t6_1116all : t6_1116jobs.all (Job.check tree)=true := by
  simp only [t6_1116jobs,List.all_append,List.all_nil,t6_1116part0,Bool.and_self]
theorem t6_1116checked : Checked tree [4,8,3,10,10,7] := by
  refine ⟨plan7514,valid7514,t6_1116choices,?_⟩
  exact check_of_frontier tree 0 t6_1116root t6_1116jobs t6_1116frontier t6_1116all
theorem t6_1117choices : plan7515.choices=[4,8,5,3,7,7].map (options 6 5) := by rfl


theorem t6_1117part0 : t6_1117jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1117frontier : t6_1117root.frontier 0=t6_1117jobs := by rfl
theorem t6_1117all : t6_1117jobs.all (Job.check tree)=true := by
  simp only [t6_1117jobs,List.all_append,List.all_nil,t6_1117part0,Bool.and_self]
theorem t6_1117checked : Checked tree [4,8,5,3,7,7] := by
  refine ⟨plan7515,valid7515,t6_1117choices,?_⟩
  exact check_of_frontier tree 0 t6_1117root t6_1117jobs t6_1117frontier t6_1117all
theorem t6_1118choices : plan7768.choices=[4,8,5,6,7,7].map (options 6 6) := by rfl


theorem t6_1118part0 : t6_1118jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1118frontier : t6_1118root.frontier 0=t6_1118jobs := by rfl
theorem t6_1118all : t6_1118jobs.all (Job.check tree)=true := by
  simp only [t6_1118jobs,List.all_append,List.all_nil,t6_1118part0,Bool.and_self]
theorem t6_1118checked : Checked tree [4,8,5,6,7,7] := by
  refine ⟨plan7768,valid7768,t6_1118choices,?_⟩
  exact check_of_frontier tree 0 t6_1118root t6_1118jobs t6_1118frontier t6_1118all
theorem t6_1119choices : plan7769.choices=[4,8,5,7,7,7].map (options 6 6) := by rfl


theorem t6_1119part0 : t6_1119jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1119frontier : t6_1119root.frontier 0=t6_1119jobs := by rfl
theorem t6_1119all : t6_1119jobs.all (Job.check tree)=true := by
  simp only [t6_1119jobs,List.all_append,List.all_nil,t6_1119part0,Bool.and_self]
theorem t6_1119checked : Checked tree [4,8,5,7,7,7] := by
  refine ⟨plan7769,valid7769,t6_1119choices,?_⟩
  exact check_of_frontier tree 0 t6_1119root t6_1119jobs t6_1119frontier t6_1119all
theorem t6_1120choices : plan7770.choices=[4,8,5,10,7,7].map (options 6 6) := by rfl


theorem t6_1120part0 : t6_1120jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1120frontier : t6_1120root.frontier 0=t6_1120jobs := by rfl
theorem t6_1120all : t6_1120jobs.all (Job.check tree)=true := by
  simp only [t6_1120jobs,List.all_append,List.all_nil,t6_1120part0,Bool.and_self]
theorem t6_1120checked : Checked tree [4,8,5,10,7,7] := by
  refine ⟨plan7770,valid7770,t6_1120choices,?_⟩
  exact check_of_frontier tree 0 t6_1120root t6_1120jobs t6_1120frontier t6_1120all
theorem t6_1121choices : plan7771.choices=[4,8,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1121part0 : t6_1121jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1121frontier : t6_1121root.frontier 0=t6_1121jobs := by rfl
theorem t6_1121all : t6_1121jobs.all (Job.check tree)=true := by
  simp only [t6_1121jobs,List.all_append,List.all_nil,t6_1121part0,Bool.and_self]
theorem t6_1121checked : Checked tree [4,8,6,6,6,7] := by
  refine ⟨plan7771,valid7771,t6_1121choices,?_⟩
  exact check_of_frontier tree 0 t6_1121root t6_1121jobs t6_1121frontier t6_1121all
theorem t6_1122choices : plan7772.choices=[4,8,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1122part0 : t6_1122jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1122frontier : t6_1122root.frontier 0=t6_1122jobs := by rfl
theorem t6_1122all : t6_1122jobs.all (Job.check tree)=true := by
  simp only [t6_1122jobs,List.all_append,List.all_nil,t6_1122part0,Bool.and_self]
theorem t6_1122checked : Checked tree [4,8,6,6,7,7] := by
  refine ⟨plan7772,valid7772,t6_1122choices,?_⟩
  exact check_of_frontier tree 0 t6_1122root t6_1122jobs t6_1122frontier t6_1122all
theorem t6_1123choices : plan7773.choices=[4,8,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1123part0 : t6_1123jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1123frontier : t6_1123root.frontier 0=t6_1123jobs := by rfl
theorem t6_1123all : t6_1123jobs.all (Job.check tree)=true := by
  simp only [t6_1123jobs,List.all_append,List.all_nil,t6_1123part0,Bool.and_self]
theorem t6_1123checked : Checked tree [4,8,6,6,10,7] := by
  refine ⟨plan7773,valid7773,t6_1123choices,?_⟩
  exact check_of_frontier tree 0 t6_1123root t6_1123jobs t6_1123frontier t6_1123all
theorem t6_1124choices : plan7774.choices=[4,8,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1124part0 : t6_1124jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1124frontier : t6_1124root.frontier 0=t6_1124jobs := by rfl
theorem t6_1124all : t6_1124jobs.all (Job.check tree)=true := by
  simp only [t6_1124jobs,List.all_append,List.all_nil,t6_1124part0,Bool.and_self]
theorem t6_1124checked : Checked tree [4,8,6,7,7,7] := by
  refine ⟨plan7774,valid7774,t6_1124choices,?_⟩
  exact check_of_frontier tree 0 t6_1124root t6_1124jobs t6_1124frontier t6_1124all
theorem t6_1125choices : plan7775.choices=[4,8,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1125part0 : t6_1125jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1125frontier : t6_1125root.frontier 0=t6_1125jobs := by rfl
theorem t6_1125all : t6_1125jobs.all (Job.check tree)=true := by
  simp only [t6_1125jobs,List.all_append,List.all_nil,t6_1125part0,Bool.and_self]
theorem t6_1125checked : Checked tree [4,8,6,10,7,7] := by
  refine ⟨plan7775,valid7775,t6_1125choices,?_⟩
  exact check_of_frontier tree 0 t6_1125root t6_1125jobs t6_1125frontier t6_1125all
theorem t6_1126choices : plan7776.choices=[4,8,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1126part0 : t6_1126jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1126frontier : t6_1126root.frontier 0=t6_1126jobs := by rfl
theorem t6_1126all : t6_1126jobs.all (Job.check tree)=true := by
  simp only [t6_1126jobs,List.all_append,List.all_nil,t6_1126part0,Bool.and_self]
theorem t6_1126checked : Checked tree [4,8,6,10,10,7] := by
  refine ⟨plan7776,valid7776,t6_1126choices,?_⟩
  exact check_of_frontier tree 0 t6_1126root t6_1126jobs t6_1126frontier t6_1126all
theorem t6_1127choices : plan7777.choices=[4,8,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1127part0 : t6_1127jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1127frontier : t6_1127root.frontier 0=t6_1127jobs := by rfl
theorem t6_1127all : t6_1127jobs.all (Job.check tree)=true := by
  simp only [t6_1127jobs,List.all_append,List.all_nil,t6_1127part0,Bool.and_self]
theorem t6_1127checked : Checked tree [4,8,7,7,7,7] := by
  refine ⟨plan7777,valid7777,t6_1127choices,?_⟩
  exact check_of_frontier tree 0 t6_1127root t6_1127jobs t6_1127frontier t6_1127all
theorem t6_1128choices : plan7778.choices=[4,8,8,7,7,7].map (options 6 6) := by rfl


theorem t6_1128part0 : t6_1128jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1128frontier : t6_1128root.frontier 0=t6_1128jobs := by rfl
theorem t6_1128all : t6_1128jobs.all (Job.check tree)=true := by
  simp only [t6_1128jobs,List.all_append,List.all_nil,t6_1128part0,Bool.and_self]
theorem t6_1128checked : Checked tree [4,8,8,7,7,7] := by
  refine ⟨plan7778,valid7778,t6_1128choices,?_⟩
  exact check_of_frontier tree 0 t6_1128root t6_1128jobs t6_1128frontier t6_1128all
theorem t6_1129choices : plan7516.choices=[4,8,9,3,7,7].map (options 6 5) := by rfl


theorem t6_1129part0 : t6_1129jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1129frontier : t6_1129root.frontier 0=t6_1129jobs := by rfl
theorem t6_1129all : t6_1129jobs.all (Job.check tree)=true := by
  simp only [t6_1129jobs,List.all_append,List.all_nil,t6_1129part0,Bool.and_self]
theorem t6_1129checked : Checked tree [4,8,9,3,7,7] := by
  refine ⟨plan7516,valid7516,t6_1129choices,?_⟩
  exact check_of_frontier tree 0 t6_1129root t6_1129jobs t6_1129frontier t6_1129all
theorem t6_1130choices : plan7779.choices=[4,8,9,6,7,7].map (options 6 6) := by rfl


theorem t6_1130part0 : t6_1130jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1130frontier : t6_1130root.frontier 0=t6_1130jobs := by rfl
theorem t6_1130all : t6_1130jobs.all (Job.check tree)=true := by
  simp only [t6_1130jobs,List.all_append,List.all_nil,t6_1130part0,Bool.and_self]
theorem t6_1130checked : Checked tree [4,8,9,6,7,7] := by
  refine ⟨plan7779,valid7779,t6_1130choices,?_⟩
  exact check_of_frontier tree 0 t6_1130root t6_1130jobs t6_1130frontier t6_1130all
theorem t6_1131choices : plan7780.choices=[4,8,9,7,7,7].map (options 6 6) := by rfl


theorem t6_1131part0 : t6_1131jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1131frontier : t6_1131root.frontier 0=t6_1131jobs := by rfl
theorem t6_1131all : t6_1131jobs.all (Job.check tree)=true := by
  simp only [t6_1131jobs,List.all_append,List.all_nil,t6_1131part0,Bool.and_self]
theorem t6_1131checked : Checked tree [4,8,9,7,7,7] := by
  refine ⟨plan7780,valid7780,t6_1131choices,?_⟩
  exact check_of_frontier tree 0 t6_1131root t6_1131jobs t6_1131frontier t6_1131all
theorem t6_1132choices : plan7781.choices=[4,8,9,10,7,7].map (options 6 6) := by rfl


theorem t6_1132part0 : t6_1132jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1132frontier : t6_1132root.frontier 0=t6_1132jobs := by rfl
theorem t6_1132all : t6_1132jobs.all (Job.check tree)=true := by
  simp only [t6_1132jobs,List.all_append,List.all_nil,t6_1132part0,Bool.and_self]
theorem t6_1132checked : Checked tree [4,8,9,10,7,7] := by
  refine ⟨plan7781,valid7781,t6_1132choices,?_⟩
  exact check_of_frontier tree 0 t6_1132root t6_1132jobs t6_1132frontier t6_1132all
theorem t6_1133choices : plan7782.choices=[4,8,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1133part0 : t6_1133jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1133frontier : t6_1133root.frontier 0=t6_1133jobs := by rfl
theorem t6_1133all : t6_1133jobs.all (Job.check tree)=true := by
  simp only [t6_1133jobs,List.all_append,List.all_nil,t6_1133part0,Bool.and_self]
theorem t6_1133checked : Checked tree [4,8,10,7,7,7] := by
  refine ⟨plan7782,valid7782,t6_1133choices,?_⟩
  exact check_of_frontier tree 0 t6_1133root t6_1133jobs t6_1133frontier t6_1133all
theorem t6_1134choices : plan7783.choices=[4,8,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1134part0 : t6_1134jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1134frontier : t6_1134root.frontier 0=t6_1134jobs := by rfl
theorem t6_1134all : t6_1134jobs.all (Job.check tree)=true := by
  simp only [t6_1134jobs,List.all_append,List.all_nil,t6_1134part0,Bool.and_self]
theorem t6_1134checked : Checked tree [4,8,10,10,7,7] := by
  refine ⟨plan7783,valid7783,t6_1134choices,?_⟩
  exact check_of_frontier tree 0 t6_1134root t6_1134jobs t6_1134frontier t6_1134all
theorem t6_1135choices : plan7784.choices=[4,8,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1135part0 : t6_1135jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1135frontier : t6_1135root.frontier 0=t6_1135jobs := by rfl
theorem t6_1135all : t6_1135jobs.all (Job.check tree)=true := by
  simp only [t6_1135jobs,List.all_append,List.all_nil,t6_1135part0,Bool.and_self]
theorem t6_1135checked : Checked tree [4,8,10,10,10,7] := by
  refine ⟨plan7784,valid7784,t6_1135choices,?_⟩
  exact check_of_frontier tree 0 t6_1135root t6_1135jobs t6_1135frontier t6_1135all
theorem t6_1136choices : plan6415.choices=[4,9,3,3,3,3].map (options 6 2) := by rfl


theorem t6_1136part0 : t6_1136jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1136frontier : t6_1136root.frontier 0=t6_1136jobs := by rfl
theorem t6_1136all : t6_1136jobs.all (Job.check tree)=true := by
  simp only [t6_1136jobs,List.all_append,List.all_nil,t6_1136part0,Bool.and_self]
theorem t6_1136checked : Checked tree [4,9,3,3,3,3] := by
  refine ⟨plan6415,valid6415,t6_1136choices,?_⟩
  exact check_of_frontier tree 0 t6_1136root t6_1136jobs t6_1136frontier t6_1136all
theorem t6_1137choices : plan6641.choices=[4,9,3,3,3,6].map (options 6 3) := by rfl


theorem t6_1137part0 : t6_1137jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1137frontier : t6_1137root.frontier 0=t6_1137jobs := by rfl
theorem t6_1137all : t6_1137jobs.all (Job.check tree)=true := by
  simp only [t6_1137jobs,List.all_append,List.all_nil,t6_1137part0,Bool.and_self]
theorem t6_1137checked : Checked tree [4,9,3,3,3,6] := by
  refine ⟨plan6641,valid6641,t6_1137choices,?_⟩
  exact check_of_frontier tree 0 t6_1137root t6_1137jobs t6_1137frontier t6_1137all
theorem t6_1138choices : plan6642.choices=[4,9,3,3,3,7].map (options 6 3) := by rfl


theorem t6_1138part0 : t6_1138jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1138frontier : t6_1138root.frontier 0=t6_1138jobs := by rfl
theorem t6_1138all : t6_1138jobs.all (Job.check tree)=true := by
  simp only [t6_1138jobs,List.all_append,List.all_nil,t6_1138part0,Bool.and_self]
theorem t6_1138checked : Checked tree [4,9,3,3,3,7] := by
  refine ⟨plan6642,valid6642,t6_1138choices,?_⟩
  exact check_of_frontier tree 0 t6_1138root t6_1138jobs t6_1138frontier t6_1138all
theorem t6_1139choices : plan6643.choices=[4,9,3,3,3,10].map (options 6 3) := by rfl


theorem t6_1139part0 : t6_1139jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1139frontier : t6_1139root.frontier 0=t6_1139jobs := by rfl
theorem t6_1139all : t6_1139jobs.all (Job.check tree)=true := by
  simp only [t6_1139jobs,List.all_append,List.all_nil,t6_1139part0,Bool.and_self]
theorem t6_1139checked : Checked tree [4,9,3,3,3,10] := by
  refine ⟨plan6643,valid6643,t6_1139choices,?_⟩
  exact check_of_frontier tree 0 t6_1139root t6_1139jobs t6_1139frontier t6_1139all
theorem t6_1140choices : plan7036.choices=[4,9,3,3,6,6].map (options 6 4) := by rfl


theorem t6_1140part0 : t6_1140jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1140frontier : t6_1140root.frontier 0=t6_1140jobs := by rfl
theorem t6_1140all : t6_1140jobs.all (Job.check tree)=true := by
  simp only [t6_1140jobs,List.all_append,List.all_nil,t6_1140part0,Bool.and_self]
theorem t6_1140checked : Checked tree [4,9,3,3,6,6] := by
  refine ⟨plan7036,valid7036,t6_1140choices,?_⟩
  exact check_of_frontier tree 0 t6_1140root t6_1140jobs t6_1140frontier t6_1140all
theorem t6_1141choices : plan7037.choices=[4,9,3,3,6,7].map (options 6 4) := by rfl


theorem t6_1141part0 : t6_1141jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1141part1 : t6_1141jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1141frontier : t6_1141root.frontier 1=t6_1141jobs := by rfl
theorem t6_1141all : t6_1141jobs.all (Job.check tree)=true := by
  simp only [t6_1141jobs,List.all_append,List.all_nil,t6_1141part0,t6_1141part1,Bool.and_self]
theorem t6_1141checked : Checked tree [4,9,3,3,6,7] := by
  refine ⟨plan7037,valid7037,t6_1141choices,?_⟩
  exact check_of_frontier tree 1 t6_1141root t6_1141jobs t6_1141frontier t6_1141all
theorem t6_1142choices : plan7038.choices=[4,9,3,3,6,10].map (options 6 4) := by rfl


theorem t6_1142part0 : t6_1142jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1142frontier : t6_1142root.frontier 0=t6_1142jobs := by rfl
theorem t6_1142all : t6_1142jobs.all (Job.check tree)=true := by
  simp only [t6_1142jobs,List.all_append,List.all_nil,t6_1142part0,Bool.and_self]
theorem t6_1142checked : Checked tree [4,9,3,3,6,10] := by
  refine ⟨plan7038,valid7038,t6_1142choices,?_⟩
  exact check_of_frontier tree 0 t6_1142root t6_1142jobs t6_1142frontier t6_1142all
theorem t6_1143choices : plan7039.choices=[4,9,3,3,7,7].map (options 6 4) := by rfl


theorem t6_1143part0 : t6_1143jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1143part1 : t6_1143jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1143frontier : t6_1143root.frontier 1=t6_1143jobs := by rfl
theorem t6_1143all : t6_1143jobs.all (Job.check tree)=true := by
  simp only [t6_1143jobs,List.all_append,List.all_nil,t6_1143part0,t6_1143part1,Bool.and_self]
theorem t6_1143checked : Checked tree [4,9,3,3,7,7] := by
  refine ⟨plan7039,valid7039,t6_1143choices,?_⟩
  exact check_of_frontier tree 1 t6_1143root t6_1143jobs t6_1143frontier t6_1143all
theorem t6_1144choices : plan7040.choices=[4,9,3,3,10,7].map (options 6 4) := by rfl


theorem t6_1144part0 : t6_1144jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1144part1 : t6_1144jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1144frontier : t6_1144root.frontier 1=t6_1144jobs := by rfl
theorem t6_1144all : t6_1144jobs.all (Job.check tree)=true := by
  simp only [t6_1144jobs,List.all_append,List.all_nil,t6_1144part0,t6_1144part1,Bool.and_self]
theorem t6_1144checked : Checked tree [4,9,3,3,10,7] := by
  refine ⟨plan7040,valid7040,t6_1144choices,?_⟩
  exact check_of_frontier tree 1 t6_1144root t6_1144jobs t6_1144frontier t6_1144all
theorem t6_1145choices : plan7041.choices=[4,9,3,3,10,10].map (options 6 4) := by rfl


theorem t6_1145part0 : t6_1145jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1145frontier : t6_1145root.frontier 0=t6_1145jobs := by rfl
theorem t6_1145all : t6_1145jobs.all (Job.check tree)=true := by
  simp only [t6_1145jobs,List.all_append,List.all_nil,t6_1145part0,Bool.and_self]
theorem t6_1145checked : Checked tree [4,9,3,3,10,10] := by
  refine ⟨plan7041,valid7041,t6_1145choices,?_⟩
  exact check_of_frontier tree 0 t6_1145root t6_1145jobs t6_1145frontier t6_1145all
theorem t6_1146choices : plan7517.choices=[4,9,3,6,6,6].map (options 6 5) := by rfl


theorem t6_1146part0 : t6_1146jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1146frontier : t6_1146root.frontier 0=t6_1146jobs := by rfl
theorem t6_1146all : t6_1146jobs.all (Job.check tree)=true := by
  simp only [t6_1146jobs,List.all_append,List.all_nil,t6_1146part0,Bool.and_self]
theorem t6_1146checked : Checked tree [4,9,3,6,6,6] := by
  refine ⟨plan7517,valid7517,t6_1146choices,?_⟩
  exact check_of_frontier tree 0 t6_1146root t6_1146jobs t6_1146frontier t6_1146all
theorem t6_1147choices : plan7518.choices=[4,9,3,6,6,7].map (options 6 5) := by rfl


theorem t6_1147part0 : t6_1147jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1147frontier : t6_1147root.frontier 0=t6_1147jobs := by rfl
theorem t6_1147all : t6_1147jobs.all (Job.check tree)=true := by
  simp only [t6_1147jobs,List.all_append,List.all_nil,t6_1147part0,Bool.and_self]
theorem t6_1147checked : Checked tree [4,9,3,6,6,7] := by
  refine ⟨plan7518,valid7518,t6_1147choices,?_⟩
  exact check_of_frontier tree 0 t6_1147root t6_1147jobs t6_1147frontier t6_1147all
theorem t6_1148choices : plan7519.choices=[4,9,3,6,6,10].map (options 6 5) := by rfl


theorem t6_1148part0 : t6_1148jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1148frontier : t6_1148root.frontier 0=t6_1148jobs := by rfl
theorem t6_1148all : t6_1148jobs.all (Job.check tree)=true := by
  simp only [t6_1148jobs,List.all_append,List.all_nil,t6_1148part0,Bool.and_self]
theorem t6_1148checked : Checked tree [4,9,3,6,6,10] := by
  refine ⟨plan7519,valid7519,t6_1148choices,?_⟩
  exact check_of_frontier tree 0 t6_1148root t6_1148jobs t6_1148frontier t6_1148all
theorem t6_1149choices : plan7520.choices=[4,9,3,6,7,7].map (options 6 5) := by rfl


theorem t6_1149part0 : t6_1149jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1149part1 : t6_1149jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1149frontier : t6_1149root.frontier 1=t6_1149jobs := by rfl
theorem t6_1149all : t6_1149jobs.all (Job.check tree)=true := by
  simp only [t6_1149jobs,List.all_append,List.all_nil,t6_1149part0,t6_1149part1,Bool.and_self]
theorem t6_1149checked : Checked tree [4,9,3,6,7,7] := by
  refine ⟨plan7520,valid7520,t6_1149choices,?_⟩
  exact check_of_frontier tree 1 t6_1149root t6_1149jobs t6_1149frontier t6_1149all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks122 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1086checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1074checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1087checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1088checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1089checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1090checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1091checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1092checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1093checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1094checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1095checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1096checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1075checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1097checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1098checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1099checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1100checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1101checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1102checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1103checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1104checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1105checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1106checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1076checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1107checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1108checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1109checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1110checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1111checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1112checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1113checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1114checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1115checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1116checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1077checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1117checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1118checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1119checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1120checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1121checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1122checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1123checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1124checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1125checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1126checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1078checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1127checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1128checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1129checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1130checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1131checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1132checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1133checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1134checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1135checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1136checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1079checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1137checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1138checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1139checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1140checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1141checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1142checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1143checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1144checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1145checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1080checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1146checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1147checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1148checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1149checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1081checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1082checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1083checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1084checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1085checked⟩
