-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks144
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:56:14.147025+00:00
-- url     : https://prove2.me/submissions/7854d21b-2a82-4d5d-bc1e-8689b1ebdb23

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks144
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks144
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans082
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

theorem valid133 : plan133.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid134 : plan134.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid135 : plan135.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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



theorem valid582 : plan582.Valid := valid_step _ _ _ valid137 (by decide +kernel)



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













theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)









theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)











theorem valid1611 : plan1611.Valid := valid_step _ _ _ valid582 (by decide +kernel)



theorem valid1613 : plan1613.Valid := valid_step _ _ _ valid584 (by decide +kernel)

theorem valid1614 : plan1614.Valid := valid_step _ _ _ valid585 (by decide +kernel)



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

theorem valid3445 : plan3445.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

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















































































































theorem valid6680 : plan6680.Valid := valid_step _ _ _ valid5519 (by decide +kernel)

theorem valid6681 : plan6681.Valid := valid_step _ _ _ valid5523 (by decide +kernel)

theorem valid6682 : plan6682.Valid := valid_step _ _ _ valid5524 (by decide +kernel)

theorem valid6683 : plan6683.Valid := valid_step _ _ _ valid5525 (by decide +kernel)










































































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























































theorem valid3518 : plan3518.Valid := valid_step _ _ _ valid1613 (by decide +kernel)





theorem valid3521 : plan3521.Valid := valid_step _ _ _ valid1616 (by decide +kernel)







theorem valid3525 : plan3525.Valid := valid_step _ _ _ valid1620 (by decide +kernel)







theorem valid3529 : plan3529.Valid := valid_step _ _ _ valid1611 (by decide +kernel)



theorem valid3531 : plan3531.Valid := valid_step _ _ _ valid1613 (by decide +kernel)

theorem valid3532 : plan3532.Valid := valid_step _ _ _ valid1614 (by decide +kernel)



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

theorem valid5931 : plan5931.Valid := valid_step _ _ _ valid3444 (by decide +kernel)

theorem valid5932 : plan5932.Valid := valid_step _ _ _ valid3445 (by decide +kernel)

theorem valid5933 : plan5933.Valid := valid_step _ _ _ valid3446 (by decide +kernel)

theorem valid5934 : plan5934.Valid := valid_step _ _ _ valid3447 (by decide +kernel)




































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























theorem valid7116 : plan7116.Valid := valid_step _ _ _ valid5699 (by decide +kernel)

theorem valid7117 : plan7117.Valid := valid_step _ _ _ valid5703 (by decide +kernel)

theorem valid7118 : plan7118.Valid := valid_step _ _ _ valid5704 (by decide +kernel)

theorem valid7119 : plan7119.Valid := valid_step _ _ _ valid5705 (by decide +kernel)

theorem valid7120 : plan7120.Valid := valid_step _ _ _ valid5714 (by decide +kernel)

theorem valid7121 : plan7121.Valid := valid_step _ _ _ valid5715 (by decide +kernel)

theorem valid7122 : plan7122.Valid := valid_step _ _ _ valid5716 (by decide +kernel)

theorem valid7123 : plan7123.Valid := valid_step _ _ _ valid5717 (by decide +kernel)

theorem valid7124 : plan7124.Valid := valid_step _ _ _ valid5718 (by decide +kernel)

theorem valid7125 : plan7125.Valid := valid_step _ _ _ valid5719 (by decide +kernel)






















































































































































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

























































































































































































theorem valid6429 : plan6429.Valid := valid_step _ _ _ valid5410 (by decide +kernel)






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































































































































theorem valid7648 : plan7648.Valid := valid_step _ _ _ valid5899 (by decide +kernel)

theorem valid7649 : plan7649.Valid := valid_step _ _ _ valid5900 (by decide +kernel)

theorem valid7650 : plan7650.Valid := valid_step _ _ _ valid5901 (by decide +kernel)

theorem valid7651 : plan7651.Valid := valid_step _ _ _ valid5902 (by decide +kernel)

theorem valid7652 : plan7652.Valid := valid_step _ _ _ valid5903 (by decide +kernel)

theorem valid7653 : plan7653.Valid := valid_step _ _ _ valid5904 (by decide +kernel)

theorem valid7654 : plan7654.Valid := valid_step _ _ _ valid5905 (by decide +kernel)

theorem valid7655 : plan7655.Valid := valid_step _ _ _ valid5906 (by decide +kernel)

theorem valid7656 : plan7656.Valid := valid_step _ _ _ valid5907 (by decide +kernel)

theorem valid7657 : plan7657.Valid := valid_step _ _ _ valid5908 (by decide +kernel)

theorem valid7658 : plan7658.Valid := valid_step _ _ _ valid5920 (by decide +kernel)

theorem valid7659 : plan7659.Valid := valid_step _ _ _ valid5927 (by decide +kernel)

theorem valid7660 : plan7660.Valid := valid_step _ _ _ valid5928 (by decide +kernel)

theorem valid7661 : plan7661.Valid := valid_step _ _ _ valid5929 (by decide +kernel)

theorem valid7662 : plan7662.Valid := valid_step _ _ _ valid5930 (by decide +kernel)

theorem valid7663 : plan7663.Valid := valid_step _ _ _ valid5931 (by decide +kernel)

theorem valid7664 : plan7664.Valid := valid_step _ _ _ valid5932 (by decide +kernel)

theorem valid7665 : plan7665.Valid := valid_step _ _ _ valid5933 (by decide +kernel)

theorem valid7666 : plan7666.Valid := valid_step _ _ _ valid5934 (by decide +kernel)




























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























































































































































































theorem valid7964 : plan7964.Valid := valid_step _ _ _ valid6046 (by decide +kernel)

theorem valid7965 : plan7965.Valid := valid_step _ _ _ valid6047 (by decide +kernel)

theorem valid7966 : plan7966.Valid := valid_step _ _ _ valid6048 (by decide +kernel)

theorem valid7967 : plan7967.Valid := valid_step _ _ _ valid6049 (by decide +kernel)

theorem valid7968 : plan7968.Valid := valid_step _ _ _ valid6050 (by decide +kernel)
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

theorem valid7969 : plan7969.Valid := valid_step _ _ _ valid6051 (by decide +kernel)

theorem valid7970 : plan7970.Valid := valid_step _ _ _ valid6052 (by decide +kernel)

theorem valid7971 : plan7971.Valid := valid_step _ _ _ valid6053 (by decide +kernel)

theorem valid7972 : plan7972.Valid := valid_step _ _ _ valid6054 (by decide +kernel)

theorem valid7973 : plan7973.Valid := valid_step _ _ _ valid6055 (by decide +kernel)

theorem valid7974 : plan7974.Valid := valid_step _ _ _ valid6056 (by decide +kernel)

theorem valid7975 : plan7975.Valid := valid_step _ _ _ valid6057 (by decide +kernel)

theorem valid7976 : plan7976.Valid := valid_step _ _ _ valid6058 (by decide +kernel)

theorem valid7977 : plan7977.Valid := valid_step _ _ _ valid6059 (by decide +kernel)

theorem valid7978 : plan7978.Valid := valid_step _ _ _ valid6060 (by decide +kernel)

theorem valid7979 : plan7979.Valid := valid_step _ _ _ valid6061 (by decide +kernel)

theorem valid7980 : plan7980.Valid := valid_step _ _ _ valid6062 (by decide +kernel)

theorem valid7981 : plan7981.Valid := valid_step _ _ _ valid6063 (by decide +kernel)

theorem valid7982 : plan7982.Valid := valid_step _ _ _ valid6064 (by decide +kernel)

theorem valid7983 : plan7983.Valid := valid_step _ _ _ valid6065 (by decide +kernel)

theorem valid7984 : plan7984.Valid := valid_step _ _ _ valid6066 (by decide +kernel)

theorem valid7985 : plan7985.Valid := valid_step _ _ _ valid6067 (by decide +kernel)

theorem valid7986 : plan7986.Valid := valid_step _ _ _ valid6068 (by decide +kernel)

theorem valid7987 : plan7987.Valid := valid_step _ _ _ valid6069 (by decide +kernel)

theorem valid7988 : plan7988.Valid := valid_step _ _ _ valid6070 (by decide +kernel)

theorem valid7989 : plan7989.Valid := valid_step _ _ _ valid6071 (by decide +kernel)






















































































































































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
theorem t6_1582choices : plan7964.choices=[8,6,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1582part0 : t6_1582jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1582frontier : t6_1582root.frontier 0=t6_1582jobs := by rfl
theorem t6_1582all : t6_1582jobs.all (Job.check tree)=true := by
  simp only [t6_1582jobs,List.all_append,List.all_nil,t6_1582part0,Bool.and_self]
theorem t6_1582checked : Checked tree [8,6,6,10,7,7] := by
  refine ⟨plan7964,valid7964,t6_1582choices,?_⟩
  exact check_of_frontier tree 0 t6_1582root t6_1582jobs t6_1582frontier t6_1582all
theorem t6_1583choices : plan7965.choices=[8,6,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1583part0 : t6_1583jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1583frontier : t6_1583root.frontier 0=t6_1583jobs := by rfl
theorem t6_1583all : t6_1583jobs.all (Job.check tree)=true := by
  simp only [t6_1583jobs,List.all_append,List.all_nil,t6_1583part0,Bool.and_self]
theorem t6_1583checked : Checked tree [8,6,6,10,10,7] := by
  refine ⟨plan7965,valid7965,t6_1583choices,?_⟩
  exact check_of_frontier tree 0 t6_1583root t6_1583jobs t6_1583frontier t6_1583all
theorem t6_1584choices : plan7966.choices=[8,6,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1584part0 : t6_1584jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1584frontier : t6_1584root.frontier 0=t6_1584jobs := by rfl
theorem t6_1584all : t6_1584jobs.all (Job.check tree)=true := by
  simp only [t6_1584jobs,List.all_append,List.all_nil,t6_1584part0,Bool.and_self]
theorem t6_1584checked : Checked tree [8,6,6,10,10,10] := by
  refine ⟨plan7966,valid7966,t6_1584choices,?_⟩
  exact check_of_frontier tree 0 t6_1584root t6_1584jobs t6_1584frontier t6_1584all
theorem t6_1585choices : plan7967.choices=[8,6,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1585part0 : t6_1585jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1585frontier : t6_1585root.frontier 0=t6_1585jobs := by rfl
theorem t6_1585all : t6_1585jobs.all (Job.check tree)=true := by
  simp only [t6_1585jobs,List.all_append,List.all_nil,t6_1585part0,Bool.and_self]
theorem t6_1585checked : Checked tree [8,6,7,7,7,7] := by
  refine ⟨plan7967,valid7967,t6_1585choices,?_⟩
  exact check_of_frontier tree 0 t6_1585root t6_1585jobs t6_1585frontier t6_1585all
theorem t6_1586choices : plan7968.choices=[8,6,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1586part0 : t6_1586jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1586frontier : t6_1586root.frontier 0=t6_1586jobs := by rfl
theorem t6_1586all : t6_1586jobs.all (Job.check tree)=true := by
  simp only [t6_1586jobs,List.all_append,List.all_nil,t6_1586part0,Bool.and_self]
theorem t6_1586checked : Checked tree [8,6,10,7,7,7] := by
  refine ⟨plan7968,valid7968,t6_1586choices,?_⟩
  exact check_of_frontier tree 0 t6_1586root t6_1586jobs t6_1586frontier t6_1586all
theorem t6_1587choices : plan7969.choices=[8,6,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1587part0 : t6_1587jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1587frontier : t6_1587root.frontier 0=t6_1587jobs := by rfl
theorem t6_1587all : t6_1587jobs.all (Job.check tree)=true := by
  simp only [t6_1587jobs,List.all_append,List.all_nil,t6_1587part0,Bool.and_self]
theorem t6_1587checked : Checked tree [8,6,10,10,7,7] := by
  refine ⟨plan7969,valid7969,t6_1587choices,?_⟩
  exact check_of_frontier tree 0 t6_1587root t6_1587jobs t6_1587frontier t6_1587all
theorem t6_1588choices : plan7970.choices=[8,6,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1588part0 : t6_1588jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1588frontier : t6_1588root.frontier 0=t6_1588jobs := by rfl
theorem t6_1588all : t6_1588jobs.all (Job.check tree)=true := by
  simp only [t6_1588jobs,List.all_append,List.all_nil,t6_1588part0,Bool.and_self]
theorem t6_1588checked : Checked tree [8,6,10,10,10,7] := by
  refine ⟨plan7970,valid7970,t6_1588choices,?_⟩
  exact check_of_frontier tree 0 t6_1588root t6_1588jobs t6_1588frontier t6_1588all
theorem t6_1589choices : plan7971.choices=[8,6,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1589part0 : t6_1589jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1589frontier : t6_1589root.frontier 0=t6_1589jobs := by rfl
theorem t6_1589all : t6_1589jobs.all (Job.check tree)=true := by
  simp only [t6_1589jobs,List.all_append,List.all_nil,t6_1589part0,Bool.and_self]
theorem t6_1589checked : Checked tree [8,6,10,10,10,10] := by
  refine ⟨plan7971,valid7971,t6_1589choices,?_⟩
  exact check_of_frontier tree 0 t6_1589root t6_1589jobs t6_1589frontier t6_1589all
theorem t6_1590choices : plan7972.choices=[8,7,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1590part0 : t6_1590jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1590frontier : t6_1590root.frontier 0=t6_1590jobs := by rfl
theorem t6_1590all : t6_1590jobs.all (Job.check tree)=true := by
  simp only [t6_1590jobs,List.all_append,List.all_nil,t6_1590part0,Bool.and_self]
theorem t6_1590checked : Checked tree [8,7,7,7,7,7] := by
  refine ⟨plan7972,valid7972,t6_1590choices,?_⟩
  exact check_of_frontier tree 0 t6_1590root t6_1590jobs t6_1590frontier t6_1590all
theorem t6_1591choices : plan7116.choices=[8,8,2,3,7,7].map (options 6 4) := by rfl


theorem t6_1591part0 : t6_1591jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1591frontier : t6_1591root.frontier 0=t6_1591jobs := by rfl
theorem t6_1591all : t6_1591jobs.all (Job.check tree)=true := by
  simp only [t6_1591jobs,List.all_append,List.all_nil,t6_1591part0,Bool.and_self]
theorem t6_1591checked : Checked tree [8,8,2,3,7,7] := by
  refine ⟨plan7116,valid7116,t6_1591choices,?_⟩
  exact check_of_frontier tree 0 t6_1591root t6_1591jobs t6_1591frontier t6_1591all
theorem t6_1592choices : plan7648.choices=[8,8,2,6,7,7].map (options 6 5) := by rfl


theorem t6_1592part0 : t6_1592jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1592frontier : t6_1592root.frontier 0=t6_1592jobs := by rfl
theorem t6_1592all : t6_1592jobs.all (Job.check tree)=true := by
  simp only [t6_1592jobs,List.all_append,List.all_nil,t6_1592part0,Bool.and_self]
theorem t6_1592checked : Checked tree [8,8,2,6,7,7] := by
  refine ⟨plan7648,valid7648,t6_1592choices,?_⟩
  exact check_of_frontier tree 0 t6_1592root t6_1592jobs t6_1592frontier t6_1592all
theorem t6_1593choices : plan7649.choices=[8,8,2,7,7,7].map (options 6 5) := by rfl


theorem t6_1593part0 : t6_1593jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1593frontier : t6_1593root.frontier 0=t6_1593jobs := by rfl
theorem t6_1593all : t6_1593jobs.all (Job.check tree)=true := by
  simp only [t6_1593jobs,List.all_append,List.all_nil,t6_1593part0,Bool.and_self]
theorem t6_1593checked : Checked tree [8,8,2,7,7,7] := by
  refine ⟨plan7649,valid7649,t6_1593choices,?_⟩
  exact check_of_frontier tree 0 t6_1593root t6_1593jobs t6_1593frontier t6_1593all
theorem t6_1594choices : plan7650.choices=[8,8,2,10,7,7].map (options 6 5) := by rfl


theorem t6_1594part0 : t6_1594jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1594frontier : t6_1594root.frontier 0=t6_1594jobs := by rfl
theorem t6_1594all : t6_1594jobs.all (Job.check tree)=true := by
  simp only [t6_1594jobs,List.all_append,List.all_nil,t6_1594part0,Bool.and_self]
theorem t6_1594checked : Checked tree [8,8,2,10,7,7] := by
  refine ⟨plan7650,valid7650,t6_1594choices,?_⟩
  exact check_of_frontier tree 0 t6_1594root t6_1594jobs t6_1594frontier t6_1594all
theorem t6_1595choices : plan6680.choices=[8,8,3,3,3,7].map (options 6 3) := by rfl


theorem t6_1595part0 : t6_1595jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1595frontier : t6_1595root.frontier 0=t6_1595jobs := by rfl
theorem t6_1595all : t6_1595jobs.all (Job.check tree)=true := by
  simp only [t6_1595jobs,List.all_append,List.all_nil,t6_1595part0,Bool.and_self]
theorem t6_1595checked : Checked tree [8,8,3,3,3,7] := by
  refine ⟨plan6680,valid6680,t6_1595choices,?_⟩
  exact check_of_frontier tree 0 t6_1595root t6_1595jobs t6_1595frontier t6_1595all
theorem t6_1596choices : plan7117.choices=[8,8,3,3,6,7].map (options 6 4) := by rfl


theorem t6_1596part0 : t6_1596jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1596frontier : t6_1596root.frontier 0=t6_1596jobs := by rfl
theorem t6_1596all : t6_1596jobs.all (Job.check tree)=true := by
  simp only [t6_1596jobs,List.all_append,List.all_nil,t6_1596part0,Bool.and_self]
theorem t6_1596checked : Checked tree [8,8,3,3,6,7] := by
  refine ⟨plan7117,valid7117,t6_1596choices,?_⟩
  exact check_of_frontier tree 0 t6_1596root t6_1596jobs t6_1596frontier t6_1596all
theorem t6_1597choices : plan7118.choices=[8,8,3,3,7,7].map (options 6 4) := by rfl


theorem t6_1597part0 : t6_1597jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1597frontier : t6_1597root.frontier 0=t6_1597jobs := by rfl
theorem t6_1597all : t6_1597jobs.all (Job.check tree)=true := by
  simp only [t6_1597jobs,List.all_append,List.all_nil,t6_1597part0,Bool.and_self]
theorem t6_1597checked : Checked tree [8,8,3,3,7,7] := by
  refine ⟨plan7118,valid7118,t6_1597choices,?_⟩
  exact check_of_frontier tree 0 t6_1597root t6_1597jobs t6_1597frontier t6_1597all
theorem t6_1598choices : plan7119.choices=[8,8,3,3,10,7].map (options 6 4) := by rfl


theorem t6_1598part0 : t6_1598jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1598frontier : t6_1598root.frontier 0=t6_1598jobs := by rfl
theorem t6_1598all : t6_1598jobs.all (Job.check tree)=true := by
  simp only [t6_1598jobs,List.all_append,List.all_nil,t6_1598part0,Bool.and_self]
theorem t6_1598checked : Checked tree [8,8,3,3,10,7] := by
  refine ⟨plan7119,valid7119,t6_1598choices,?_⟩
  exact check_of_frontier tree 0 t6_1598root t6_1598jobs t6_1598frontier t6_1598all
theorem t6_1599choices : plan7651.choices=[8,8,3,6,6,7].map (options 6 5) := by rfl


theorem t6_1599part0 : t6_1599jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1599frontier : t6_1599root.frontier 0=t6_1599jobs := by rfl
theorem t6_1599all : t6_1599jobs.all (Job.check tree)=true := by
  simp only [t6_1599jobs,List.all_append,List.all_nil,t6_1599part0,Bool.and_self]
theorem t6_1599checked : Checked tree [8,8,3,6,6,7] := by
  refine ⟨plan7651,valid7651,t6_1599choices,?_⟩
  exact check_of_frontier tree 0 t6_1599root t6_1599jobs t6_1599frontier t6_1599all
theorem t6_1600choices : plan7652.choices=[8,8,3,6,7,7].map (options 6 5) := by rfl


theorem t6_1600part0 : t6_1600jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1600frontier : t6_1600root.frontier 0=t6_1600jobs := by rfl
theorem t6_1600all : t6_1600jobs.all (Job.check tree)=true := by
  simp only [t6_1600jobs,List.all_append,List.all_nil,t6_1600part0,Bool.and_self]
theorem t6_1600checked : Checked tree [8,8,3,6,7,7] := by
  refine ⟨plan7652,valid7652,t6_1600choices,?_⟩
  exact check_of_frontier tree 0 t6_1600root t6_1600jobs t6_1600frontier t6_1600all
theorem t6_1601choices : plan7653.choices=[8,8,3,6,10,7].map (options 6 5) := by rfl


theorem t6_1601part0 : t6_1601jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1601frontier : t6_1601root.frontier 0=t6_1601jobs := by rfl
theorem t6_1601all : t6_1601jobs.all (Job.check tree)=true := by
  simp only [t6_1601jobs,List.all_append,List.all_nil,t6_1601part0,Bool.and_self]
theorem t6_1601checked : Checked tree [8,8,3,6,10,7] := by
  refine ⟨plan7653,valid7653,t6_1601choices,?_⟩
  exact check_of_frontier tree 0 t6_1601root t6_1601jobs t6_1601frontier t6_1601all
theorem t6_1602choices : plan7654.choices=[8,8,3,7,7,7].map (options 6 5) := by rfl


theorem t6_1602part0 : t6_1602jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1602frontier : t6_1602root.frontier 0=t6_1602jobs := by rfl
theorem t6_1602all : t6_1602jobs.all (Job.check tree)=true := by
  simp only [t6_1602jobs,List.all_append,List.all_nil,t6_1602part0,Bool.and_self]
theorem t6_1602checked : Checked tree [8,8,3,7,7,7] := by
  refine ⟨plan7654,valid7654,t6_1602choices,?_⟩
  exact check_of_frontier tree 0 t6_1602root t6_1602jobs t6_1602frontier t6_1602all
theorem t6_1603choices : plan7655.choices=[8,8,3,10,7,7].map (options 6 5) := by rfl


theorem t6_1603part0 : t6_1603jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1603frontier : t6_1603root.frontier 0=t6_1603jobs := by rfl
theorem t6_1603all : t6_1603jobs.all (Job.check tree)=true := by
  simp only [t6_1603jobs,List.all_append,List.all_nil,t6_1603part0,Bool.and_self]
theorem t6_1603checked : Checked tree [8,8,3,10,7,7] := by
  refine ⟨plan7655,valid7655,t6_1603choices,?_⟩
  exact check_of_frontier tree 0 t6_1603root t6_1603jobs t6_1603frontier t6_1603all
theorem t6_1604choices : plan7656.choices=[8,8,3,10,10,7].map (options 6 5) := by rfl


theorem t6_1604part0 : t6_1604jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1604frontier : t6_1604root.frontier 0=t6_1604jobs := by rfl
theorem t6_1604all : t6_1604jobs.all (Job.check tree)=true := by
  simp only [t6_1604jobs,List.all_append,List.all_nil,t6_1604part0,Bool.and_self]
theorem t6_1604checked : Checked tree [8,8,3,10,10,7] := by
  refine ⟨plan7656,valid7656,t6_1604choices,?_⟩
  exact check_of_frontier tree 0 t6_1604root t6_1604jobs t6_1604frontier t6_1604all
theorem t6_1605choices : plan7657.choices=[8,8,5,3,7,7].map (options 6 5) := by rfl


theorem t6_1605part0 : t6_1605jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1605frontier : t6_1605root.frontier 0=t6_1605jobs := by rfl
theorem t6_1605all : t6_1605jobs.all (Job.check tree)=true := by
  simp only [t6_1605jobs,List.all_append,List.all_nil,t6_1605part0,Bool.and_self]
theorem t6_1605checked : Checked tree [8,8,5,3,7,7] := by
  refine ⟨plan7657,valid7657,t6_1605choices,?_⟩
  exact check_of_frontier tree 0 t6_1605root t6_1605jobs t6_1605frontier t6_1605all
theorem t6_1606choices : plan7973.choices=[8,8,5,6,7,7].map (options 6 6) := by rfl


theorem t6_1606part0 : t6_1606jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1606frontier : t6_1606root.frontier 0=t6_1606jobs := by rfl
theorem t6_1606all : t6_1606jobs.all (Job.check tree)=true := by
  simp only [t6_1606jobs,List.all_append,List.all_nil,t6_1606part0,Bool.and_self]
theorem t6_1606checked : Checked tree [8,8,5,6,7,7] := by
  refine ⟨plan7973,valid7973,t6_1606choices,?_⟩
  exact check_of_frontier tree 0 t6_1606root t6_1606jobs t6_1606frontier t6_1606all
theorem t6_1607choices : plan7974.choices=[8,8,5,7,7,7].map (options 6 6) := by rfl


theorem t6_1607part0 : t6_1607jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1607frontier : t6_1607root.frontier 0=t6_1607jobs := by rfl
theorem t6_1607all : t6_1607jobs.all (Job.check tree)=true := by
  simp only [t6_1607jobs,List.all_append,List.all_nil,t6_1607part0,Bool.and_self]
theorem t6_1607checked : Checked tree [8,8,5,7,7,7] := by
  refine ⟨plan7974,valid7974,t6_1607choices,?_⟩
  exact check_of_frontier tree 0 t6_1607root t6_1607jobs t6_1607frontier t6_1607all
theorem t6_1608choices : plan7975.choices=[8,8,5,10,7,7].map (options 6 6) := by rfl


theorem t6_1608part0 : t6_1608jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1608frontier : t6_1608root.frontier 0=t6_1608jobs := by rfl
theorem t6_1608all : t6_1608jobs.all (Job.check tree)=true := by
  simp only [t6_1608jobs,List.all_append,List.all_nil,t6_1608part0,Bool.and_self]
theorem t6_1608checked : Checked tree [8,8,5,10,7,7] := by
  refine ⟨plan7975,valid7975,t6_1608choices,?_⟩
  exact check_of_frontier tree 0 t6_1608root t6_1608jobs t6_1608frontier t6_1608all
theorem t6_1609choices : plan7976.choices=[8,8,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1609part0 : t6_1609jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1609frontier : t6_1609root.frontier 0=t6_1609jobs := by rfl
theorem t6_1609all : t6_1609jobs.all (Job.check tree)=true := by
  simp only [t6_1609jobs,List.all_append,List.all_nil,t6_1609part0,Bool.and_self]
theorem t6_1609checked : Checked tree [8,8,6,6,6,7] := by
  refine ⟨plan7976,valid7976,t6_1609choices,?_⟩
  exact check_of_frontier tree 0 t6_1609root t6_1609jobs t6_1609frontier t6_1609all
theorem t6_1610choices : plan7977.choices=[8,8,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1610part0 : t6_1610jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1610frontier : t6_1610root.frontier 0=t6_1610jobs := by rfl
theorem t6_1610all : t6_1610jobs.all (Job.check tree)=true := by
  simp only [t6_1610jobs,List.all_append,List.all_nil,t6_1610part0,Bool.and_self]
theorem t6_1610checked : Checked tree [8,8,6,6,7,7] := by
  refine ⟨plan7977,valid7977,t6_1610choices,?_⟩
  exact check_of_frontier tree 0 t6_1610root t6_1610jobs t6_1610frontier t6_1610all
theorem t6_1611choices : plan7978.choices=[8,8,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1611part0 : t6_1611jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1611frontier : t6_1611root.frontier 0=t6_1611jobs := by rfl
theorem t6_1611all : t6_1611jobs.all (Job.check tree)=true := by
  simp only [t6_1611jobs,List.all_append,List.all_nil,t6_1611part0,Bool.and_self]
theorem t6_1611checked : Checked tree [8,8,6,6,10,7] := by
  refine ⟨plan7978,valid7978,t6_1611choices,?_⟩
  exact check_of_frontier tree 0 t6_1611root t6_1611jobs t6_1611frontier t6_1611all
theorem t6_1612choices : plan7979.choices=[8,8,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1612part0 : t6_1612jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1612frontier : t6_1612root.frontier 0=t6_1612jobs := by rfl
theorem t6_1612all : t6_1612jobs.all (Job.check tree)=true := by
  simp only [t6_1612jobs,List.all_append,List.all_nil,t6_1612part0,Bool.and_self]
theorem t6_1612checked : Checked tree [8,8,6,7,7,7] := by
  refine ⟨plan7979,valid7979,t6_1612choices,?_⟩
  exact check_of_frontier tree 0 t6_1612root t6_1612jobs t6_1612frontier t6_1612all
theorem t6_1613choices : plan7980.choices=[8,8,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1613part0 : t6_1613jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1613frontier : t6_1613root.frontier 0=t6_1613jobs := by rfl
theorem t6_1613all : t6_1613jobs.all (Job.check tree)=true := by
  simp only [t6_1613jobs,List.all_append,List.all_nil,t6_1613part0,Bool.and_self]
theorem t6_1613checked : Checked tree [8,8,6,10,7,7] := by
  refine ⟨plan7980,valid7980,t6_1613choices,?_⟩
  exact check_of_frontier tree 0 t6_1613root t6_1613jobs t6_1613frontier t6_1613all
theorem t6_1614choices : plan7981.choices=[8,8,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1614part0 : t6_1614jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1614frontier : t6_1614root.frontier 0=t6_1614jobs := by rfl
theorem t6_1614all : t6_1614jobs.all (Job.check tree)=true := by
  simp only [t6_1614jobs,List.all_append,List.all_nil,t6_1614part0,Bool.and_self]
theorem t6_1614checked : Checked tree [8,8,6,10,10,7] := by
  refine ⟨plan7981,valid7981,t6_1614choices,?_⟩
  exact check_of_frontier tree 0 t6_1614root t6_1614jobs t6_1614frontier t6_1614all
theorem t6_1615choices : plan7982.choices=[8,8,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1615part0 : t6_1615jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1615frontier : t6_1615root.frontier 0=t6_1615jobs := by rfl
theorem t6_1615all : t6_1615jobs.all (Job.check tree)=true := by
  simp only [t6_1615jobs,List.all_append,List.all_nil,t6_1615part0,Bool.and_self]
theorem t6_1615checked : Checked tree [8,8,7,7,7,7] := by
  refine ⟨plan7982,valid7982,t6_1615choices,?_⟩
  exact check_of_frontier tree 0 t6_1615root t6_1615jobs t6_1615frontier t6_1615all
theorem t6_1616choices : plan7983.choices=[8,8,8,7,7,7].map (options 6 6) := by rfl


theorem t6_1616part0 : t6_1616jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1616frontier : t6_1616root.frontier 0=t6_1616jobs := by rfl
theorem t6_1616all : t6_1616jobs.all (Job.check tree)=true := by
  simp only [t6_1616jobs,List.all_append,List.all_nil,t6_1616part0,Bool.and_self]
theorem t6_1616checked : Checked tree [8,8,8,7,7,7] := by
  refine ⟨plan7983,valid7983,t6_1616choices,?_⟩
  exact check_of_frontier tree 0 t6_1616root t6_1616jobs t6_1616frontier t6_1616all
theorem t6_1617choices : plan7658.choices=[8,8,9,3,7,7].map (options 6 5) := by rfl


theorem t6_1617part0 : t6_1617jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1617frontier : t6_1617root.frontier 0=t6_1617jobs := by rfl
theorem t6_1617all : t6_1617jobs.all (Job.check tree)=true := by
  simp only [t6_1617jobs,List.all_append,List.all_nil,t6_1617part0,Bool.and_self]
theorem t6_1617checked : Checked tree [8,8,9,3,7,7] := by
  refine ⟨plan7658,valid7658,t6_1617choices,?_⟩
  exact check_of_frontier tree 0 t6_1617root t6_1617jobs t6_1617frontier t6_1617all
theorem t6_1618choices : plan7984.choices=[8,8,9,6,7,7].map (options 6 6) := by rfl


theorem t6_1618part0 : t6_1618jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1618frontier : t6_1618root.frontier 0=t6_1618jobs := by rfl
theorem t6_1618all : t6_1618jobs.all (Job.check tree)=true := by
  simp only [t6_1618jobs,List.all_append,List.all_nil,t6_1618part0,Bool.and_self]
theorem t6_1618checked : Checked tree [8,8,9,6,7,7] := by
  refine ⟨plan7984,valid7984,t6_1618choices,?_⟩
  exact check_of_frontier tree 0 t6_1618root t6_1618jobs t6_1618frontier t6_1618all
theorem t6_1619choices : plan7985.choices=[8,8,9,7,7,7].map (options 6 6) := by rfl


theorem t6_1619part0 : t6_1619jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1619frontier : t6_1619root.frontier 0=t6_1619jobs := by rfl
theorem t6_1619all : t6_1619jobs.all (Job.check tree)=true := by
  simp only [t6_1619jobs,List.all_append,List.all_nil,t6_1619part0,Bool.and_self]
theorem t6_1619checked : Checked tree [8,8,9,7,7,7] := by
  refine ⟨plan7985,valid7985,t6_1619choices,?_⟩
  exact check_of_frontier tree 0 t6_1619root t6_1619jobs t6_1619frontier t6_1619all
theorem t6_1620choices : plan7986.choices=[8,8,9,10,7,7].map (options 6 6) := by rfl


theorem t6_1620part0 : t6_1620jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1620frontier : t6_1620root.frontier 0=t6_1620jobs := by rfl
theorem t6_1620all : t6_1620jobs.all (Job.check tree)=true := by
  simp only [t6_1620jobs,List.all_append,List.all_nil,t6_1620part0,Bool.and_self]
theorem t6_1620checked : Checked tree [8,8,9,10,7,7] := by
  refine ⟨plan7986,valid7986,t6_1620choices,?_⟩
  exact check_of_frontier tree 0 t6_1620root t6_1620jobs t6_1620frontier t6_1620all
theorem t6_1621choices : plan7987.choices=[8,8,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1621part0 : t6_1621jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1621frontier : t6_1621root.frontier 0=t6_1621jobs := by rfl
theorem t6_1621all : t6_1621jobs.all (Job.check tree)=true := by
  simp only [t6_1621jobs,List.all_append,List.all_nil,t6_1621part0,Bool.and_self]
theorem t6_1621checked : Checked tree [8,8,10,7,7,7] := by
  refine ⟨plan7987,valid7987,t6_1621choices,?_⟩
  exact check_of_frontier tree 0 t6_1621root t6_1621jobs t6_1621frontier t6_1621all
theorem t6_1622choices : plan7988.choices=[8,8,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1622part0 : t6_1622jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1622frontier : t6_1622root.frontier 0=t6_1622jobs := by rfl
theorem t6_1622all : t6_1622jobs.all (Job.check tree)=true := by
  simp only [t6_1622jobs,List.all_append,List.all_nil,t6_1622part0,Bool.and_self]
theorem t6_1622checked : Checked tree [8,8,10,10,7,7] := by
  refine ⟨plan7988,valid7988,t6_1622choices,?_⟩
  exact check_of_frontier tree 0 t6_1622root t6_1622jobs t6_1622frontier t6_1622all
theorem t6_1623choices : plan7989.choices=[8,8,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1623part0 : t6_1623jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1623frontier : t6_1623root.frontier 0=t6_1623jobs := by rfl
theorem t6_1623all : t6_1623jobs.all (Job.check tree)=true := by
  simp only [t6_1623jobs,List.all_append,List.all_nil,t6_1623part0,Bool.and_self]
theorem t6_1623checked : Checked tree [8,8,10,10,10,7] := by
  refine ⟨plan7989,valid7989,t6_1623choices,?_⟩
  exact check_of_frontier tree 0 t6_1623root t6_1623jobs t6_1623frontier t6_1623all
theorem t6_1624choices : plan6429.choices=[8,9,3,3,3,3].map (options 6 2) := by rfl


theorem t6_1624part0 : t6_1624jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1624frontier : t6_1624root.frontier 0=t6_1624jobs := by rfl
theorem t6_1624all : t6_1624jobs.all (Job.check tree)=true := by
  simp only [t6_1624jobs,List.all_append,List.all_nil,t6_1624part0,Bool.and_self]
theorem t6_1624checked : Checked tree [8,9,3,3,3,3] := by
  refine ⟨plan6429,valid6429,t6_1624choices,?_⟩
  exact check_of_frontier tree 0 t6_1624root t6_1624jobs t6_1624frontier t6_1624all
theorem t6_1625choices : plan6681.choices=[8,9,3,3,3,6].map (options 6 3) := by rfl


theorem t6_1625part0 : t6_1625jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1625frontier : t6_1625root.frontier 0=t6_1625jobs := by rfl
theorem t6_1625all : t6_1625jobs.all (Job.check tree)=true := by
  simp only [t6_1625jobs,List.all_append,List.all_nil,t6_1625part0,Bool.and_self]
theorem t6_1625checked : Checked tree [8,9,3,3,3,6] := by
  refine ⟨plan6681,valid6681,t6_1625choices,?_⟩
  exact check_of_frontier tree 0 t6_1625root t6_1625jobs t6_1625frontier t6_1625all
theorem t6_1626choices : plan6682.choices=[8,9,3,3,3,7].map (options 6 3) := by rfl


theorem t6_1626part0 : t6_1626jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1626frontier : t6_1626root.frontier 0=t6_1626jobs := by rfl
theorem t6_1626all : t6_1626jobs.all (Job.check tree)=true := by
  simp only [t6_1626jobs,List.all_append,List.all_nil,t6_1626part0,Bool.and_self]
theorem t6_1626checked : Checked tree [8,9,3,3,3,7] := by
  refine ⟨plan6682,valid6682,t6_1626choices,?_⟩
  exact check_of_frontier tree 0 t6_1626root t6_1626jobs t6_1626frontier t6_1626all
theorem t6_1627choices : plan6683.choices=[8,9,3,3,3,10].map (options 6 3) := by rfl


theorem t6_1627part0 : t6_1627jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1627frontier : t6_1627root.frontier 0=t6_1627jobs := by rfl
theorem t6_1627all : t6_1627jobs.all (Job.check tree)=true := by
  simp only [t6_1627jobs,List.all_append,List.all_nil,t6_1627part0,Bool.and_self]
theorem t6_1627checked : Checked tree [8,9,3,3,3,10] := by
  refine ⟨plan6683,valid6683,t6_1627choices,?_⟩
  exact check_of_frontier tree 0 t6_1627root t6_1627jobs t6_1627frontier t6_1627all
theorem t6_1628choices : plan7120.choices=[8,9,3,3,6,6].map (options 6 4) := by rfl


theorem t6_1628part0 : t6_1628jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1628frontier : t6_1628root.frontier 0=t6_1628jobs := by rfl
theorem t6_1628all : t6_1628jobs.all (Job.check tree)=true := by
  simp only [t6_1628jobs,List.all_append,List.all_nil,t6_1628part0,Bool.and_self]
theorem t6_1628checked : Checked tree [8,9,3,3,6,6] := by
  refine ⟨plan7120,valid7120,t6_1628choices,?_⟩
  exact check_of_frontier tree 0 t6_1628root t6_1628jobs t6_1628frontier t6_1628all
theorem t6_1629choices : plan7121.choices=[8,9,3,3,6,7].map (options 6 4) := by rfl


theorem t6_1629part0 : t6_1629jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1629part1 : t6_1629jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1629frontier : t6_1629root.frontier 1=t6_1629jobs := by rfl
theorem t6_1629all : t6_1629jobs.all (Job.check tree)=true := by
  simp only [t6_1629jobs,List.all_append,List.all_nil,t6_1629part0,t6_1629part1,Bool.and_self]
theorem t6_1629checked : Checked tree [8,9,3,3,6,7] := by
  refine ⟨plan7121,valid7121,t6_1629choices,?_⟩
  exact check_of_frontier tree 1 t6_1629root t6_1629jobs t6_1629frontier t6_1629all
theorem t6_1630choices : plan7122.choices=[8,9,3,3,6,10].map (options 6 4) := by rfl


theorem t6_1630part0 : t6_1630jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1630frontier : t6_1630root.frontier 0=t6_1630jobs := by rfl
theorem t6_1630all : t6_1630jobs.all (Job.check tree)=true := by
  simp only [t6_1630jobs,List.all_append,List.all_nil,t6_1630part0,Bool.and_self]
theorem t6_1630checked : Checked tree [8,9,3,3,6,10] := by
  refine ⟨plan7122,valid7122,t6_1630choices,?_⟩
  exact check_of_frontier tree 0 t6_1630root t6_1630jobs t6_1630frontier t6_1630all
theorem t6_1631choices : plan7123.choices=[8,9,3,3,7,7].map (options 6 4) := by rfl


theorem t6_1631part0 : t6_1631jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1631part1 : t6_1631jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1631frontier : t6_1631root.frontier 1=t6_1631jobs := by rfl
theorem t6_1631all : t6_1631jobs.all (Job.check tree)=true := by
  simp only [t6_1631jobs,List.all_append,List.all_nil,t6_1631part0,t6_1631part1,Bool.and_self]
theorem t6_1631checked : Checked tree [8,9,3,3,7,7] := by
  refine ⟨plan7123,valid7123,t6_1631choices,?_⟩
  exact check_of_frontier tree 1 t6_1631root t6_1631jobs t6_1631frontier t6_1631all
theorem t6_1632choices : plan7124.choices=[8,9,3,3,10,7].map (options 6 4) := by rfl


theorem t6_1632part0 : t6_1632jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1632part1 : t6_1632jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1632frontier : t6_1632root.frontier 1=t6_1632jobs := by rfl
theorem t6_1632all : t6_1632jobs.all (Job.check tree)=true := by
  simp only [t6_1632jobs,List.all_append,List.all_nil,t6_1632part0,t6_1632part1,Bool.and_self]
theorem t6_1632checked : Checked tree [8,9,3,3,10,7] := by
  refine ⟨plan7124,valid7124,t6_1632choices,?_⟩
  exact check_of_frontier tree 1 t6_1632root t6_1632jobs t6_1632frontier t6_1632all
theorem t6_1633choices : plan7125.choices=[8,9,3,3,10,10].map (options 6 4) := by rfl


theorem t6_1633part0 : t6_1633jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1633frontier : t6_1633root.frontier 0=t6_1633jobs := by rfl
theorem t6_1633all : t6_1633jobs.all (Job.check tree)=true := by
  simp only [t6_1633jobs,List.all_append,List.all_nil,t6_1633part0,Bool.and_self]
theorem t6_1633checked : Checked tree [8,9,3,3,10,10] := by
  refine ⟨plan7125,valid7125,t6_1633choices,?_⟩
  exact check_of_frontier tree 0 t6_1633root t6_1633jobs t6_1633frontier t6_1633all
theorem t6_1634choices : plan7659.choices=[8,9,3,6,6,6].map (options 6 5) := by rfl


theorem t6_1634part0 : t6_1634jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1634frontier : t6_1634root.frontier 0=t6_1634jobs := by rfl
theorem t6_1634all : t6_1634jobs.all (Job.check tree)=true := by
  simp only [t6_1634jobs,List.all_append,List.all_nil,t6_1634part0,Bool.and_self]
theorem t6_1634checked : Checked tree [8,9,3,6,6,6] := by
  refine ⟨plan7659,valid7659,t6_1634choices,?_⟩
  exact check_of_frontier tree 0 t6_1634root t6_1634jobs t6_1634frontier t6_1634all
theorem t6_1635choices : plan7660.choices=[8,9,3,6,6,7].map (options 6 5) := by rfl


theorem t6_1635part0 : t6_1635jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1635frontier : t6_1635root.frontier 0=t6_1635jobs := by rfl
theorem t6_1635all : t6_1635jobs.all (Job.check tree)=true := by
  simp only [t6_1635jobs,List.all_append,List.all_nil,t6_1635part0,Bool.and_self]
theorem t6_1635checked : Checked tree [8,9,3,6,6,7] := by
  refine ⟨plan7660,valid7660,t6_1635choices,?_⟩
  exact check_of_frontier tree 0 t6_1635root t6_1635jobs t6_1635frontier t6_1635all
theorem t6_1636choices : plan7661.choices=[8,9,3,6,6,10].map (options 6 5) := by rfl


theorem t6_1636part0 : t6_1636jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1636frontier : t6_1636root.frontier 0=t6_1636jobs := by rfl
theorem t6_1636all : t6_1636jobs.all (Job.check tree)=true := by
  simp only [t6_1636jobs,List.all_append,List.all_nil,t6_1636part0,Bool.and_self]
theorem t6_1636checked : Checked tree [8,9,3,6,6,10] := by
  refine ⟨plan7661,valid7661,t6_1636choices,?_⟩
  exact check_of_frontier tree 0 t6_1636root t6_1636jobs t6_1636frontier t6_1636all
theorem t6_1637choices : plan7662.choices=[8,9,3,6,7,7].map (options 6 5) := by rfl


theorem t6_1637part0 : t6_1637jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1637part1 : t6_1637jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1637frontier : t6_1637root.frontier 1=t6_1637jobs := by rfl
theorem t6_1637all : t6_1637jobs.all (Job.check tree)=true := by
  simp only [t6_1637jobs,List.all_append,List.all_nil,t6_1637part0,t6_1637part1,Bool.and_self]
theorem t6_1637checked : Checked tree [8,9,3,6,7,7] := by
  refine ⟨plan7662,valid7662,t6_1637choices,?_⟩
  exact check_of_frontier tree 1 t6_1637root t6_1637jobs t6_1637frontier t6_1637all
theorem t6_1638choices : plan7663.choices=[8,9,3,6,10,7].map (options 6 5) := by rfl


theorem t6_1638part0 : t6_1638jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1638frontier : t6_1638root.frontier 0=t6_1638jobs := by rfl
theorem t6_1638all : t6_1638jobs.all (Job.check tree)=true := by
  simp only [t6_1638jobs,List.all_append,List.all_nil,t6_1638part0,Bool.and_self]
theorem t6_1638checked : Checked tree [8,9,3,6,10,7] := by
  refine ⟨plan7663,valid7663,t6_1638choices,?_⟩
  exact check_of_frontier tree 0 t6_1638root t6_1638jobs t6_1638frontier t6_1638all
theorem t6_1639choices : plan7664.choices=[8,9,3,6,10,10].map (options 6 5) := by rfl


theorem t6_1639part0 : t6_1639jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1639frontier : t6_1639root.frontier 0=t6_1639jobs := by rfl
theorem t6_1639all : t6_1639jobs.all (Job.check tree)=true := by
  simp only [t6_1639jobs,List.all_append,List.all_nil,t6_1639part0,Bool.and_self]
theorem t6_1639checked : Checked tree [8,9,3,6,10,10] := by
  refine ⟨plan7664,valid7664,t6_1639choices,?_⟩
  exact check_of_frontier tree 0 t6_1639root t6_1639jobs t6_1639frontier t6_1639all
theorem t6_1640choices : plan7665.choices=[8,9,3,7,7,7].map (options 6 5) := by rfl


theorem t6_1640part0 : t6_1640jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1640part1 : t6_1640jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1640frontier : t6_1640root.frontier 1=t6_1640jobs := by rfl
theorem t6_1640all : t6_1640jobs.all (Job.check tree)=true := by
  simp only [t6_1640jobs,List.all_append,List.all_nil,t6_1640part0,t6_1640part1,Bool.and_self]
theorem t6_1640checked : Checked tree [8,9,3,7,7,7] := by
  refine ⟨plan7665,valid7665,t6_1640choices,?_⟩
  exact check_of_frontier tree 1 t6_1640root t6_1640jobs t6_1640frontier t6_1640all
theorem t6_1641choices : plan7666.choices=[8,9,3,10,7,7].map (options 6 5) := by rfl


theorem t6_1641part0 : t6_1641jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1641part1 : t6_1641jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1641frontier : t6_1641root.frontier 1=t6_1641jobs := by rfl
theorem t6_1641all : t6_1641jobs.all (Job.check tree)=true := by
  simp only [t6_1641jobs,List.all_append,List.all_nil,t6_1641part0,t6_1641part1,Bool.and_self]
theorem t6_1641checked : Checked tree [8,9,3,10,7,7] := by
  refine ⟨plan7666,valid7666,t6_1641choices,?_⟩
  exact check_of_frontier tree 1 t6_1641root t6_1641jobs t6_1641frontier t6_1641all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks144 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1594checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1582checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1595checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1596checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1597checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1598checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1599checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1600checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1601checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1602checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1603checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1604checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1583checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1605checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1606checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1607checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1608checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1609checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1610checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1611checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1612checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1613checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1614checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1584checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1615checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1616checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1617checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1618checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1619checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1620checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1621checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1622checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1623checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1624checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1585checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1625checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1626checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1627checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1628checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1629checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1630checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1631checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1632checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1633checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1586checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1634checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1635checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1636checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1637checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1638checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1639checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1640checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1641checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1587checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1588checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1589checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1590checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1591checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1592checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1593checked⟩
