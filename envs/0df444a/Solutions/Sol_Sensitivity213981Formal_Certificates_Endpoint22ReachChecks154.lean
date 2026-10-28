-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks154
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:10:48.614479+00:00
-- url     : https://prove2.me/submissions/7216a1c0-5143-43a4-8709-12a1de075c8d

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks154
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks154
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
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









theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1564 : plan1564.Valid := valid_step _ _ _ valid573 (by decide +kernel)





































theorem valid1583 : plan1583.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1584 : plan1584.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1585 : plan1585.Valid := valid_step _ _ _ valid577 (by decide +kernel)















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











































































































































theorem valid3334 : plan3334.Valid := valid_step _ _ _ valid1528 (by decide +kernel)















































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



































































































theorem valid3410 : plan3410.Valid := valid_step _ _ _ valid1556 (by decide +kernel)

theorem valid3411 : plan3411.Valid := valid_step _ _ _ valid1557 (by decide +kernel)

theorem valid3412 : plan3412.Valid := valid_step _ _ _ valid1558 (by decide +kernel)























































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









































































































































theorem valid6693 : plan6693.Valid := valid_step _ _ _ valid5532 (by decide +kernel)






















































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











































































































theorem valid5718 : plan5718.Valid := valid_step _ _ _ valid3358 (by decide +kernel)

theorem valid5719 : plan5719.Valid := valid_step _ _ _ valid3359 (by decide +kernel)





















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













































































































































theorem valid5927 : plan5927.Valid := valid_step _ _ _ valid3440 (by decide +kernel)

theorem valid5928 : plan5928.Valid := valid_step _ _ _ valid3441 (by decide +kernel)

theorem valid5929 : plan5929.Valid := valid_step _ _ _ valid3442 (by decide +kernel)

theorem valid5930 : plan5930.Valid := valid_step _ _ _ valid3443 (by decide +kernel)

theorem valid5931 : plan5931.Valid := valid_step _ _ _ valid3444 (by decide +kernel)

theorem valid5932 : plan5932.Valid := valid_step _ _ _ valid3445 (by decide +kernel)

theorem valid5933 : plan5933.Valid := valid_step _ _ _ valid3446 (by decide +kernel)

theorem valid5934 : plan5934.Valid := valid_step _ _ _ valid3447 (by decide +kernel)

theorem valid5935 : plan5935.Valid := valid_step _ _ _ valid3448 (by decide +kernel)

theorem valid5936 : plan5936.Valid := valid_step _ _ _ valid3449 (by decide +kernel)























theorem valid5948 : plan5948.Valid := valid_step _ _ _ valid3487 (by decide +kernel)

theorem valid5949 : plan5949.Valid := valid_step _ _ _ valid3488 (by decide +kernel)

theorem valid5950 : plan5950.Valid := valid_step _ _ _ valid3489 (by decide +kernel)




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









































































theorem valid7141 : plan7141.Valid := valid_step _ _ _ valid5718 (by decide +kernel)

theorem valid7142 : plan7142.Valid := valid_step _ _ _ valid5719 (by decide +kernel)

theorem valid7143 : plan7143.Valid := valid_step _ _ _ valid5730 (by decide +kernel)

theorem valid7144 : plan7144.Valid := valid_step _ _ _ valid5731 (by decide +kernel)

theorem valid7145 : plan7145.Valid := valid_step _ _ _ valid5732 (by decide +kernel)














































































































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













theorem valid7687 : plan7687.Valid := valid_step _ _ _ valid5927 (by decide +kernel)

theorem valid7688 : plan7688.Valid := valid_step _ _ _ valid5928 (by decide +kernel)

theorem valid7689 : plan7689.Valid := valid_step _ _ _ valid5929 (by decide +kernel)

theorem valid7690 : plan7690.Valid := valid_step _ _ _ valid5930 (by decide +kernel)

theorem valid7691 : plan7691.Valid := valid_step _ _ _ valid5931 (by decide +kernel)

theorem valid7692 : plan7692.Valid := valid_step _ _ _ valid5932 (by decide +kernel)

theorem valid7693 : plan7693.Valid := valid_step _ _ _ valid5933 (by decide +kernel)

theorem valid7694 : plan7694.Valid := valid_step _ _ _ valid5934 (by decide +kernel)

theorem valid7695 : plan7695.Valid := valid_step _ _ _ valid5935 (by decide +kernel)

theorem valid7696 : plan7696.Valid := valid_step _ _ _ valid5936 (by decide +kernel)

theorem valid7697 : plan7697.Valid := valid_step _ _ _ valid5948 (by decide +kernel)

theorem valid7698 : plan7698.Valid := valid_step _ _ _ valid5949 (by decide +kernel)

theorem valid7699 : plan7699.Valid := valid_step _ _ _ valid5950 (by decide +kernel)


























































































































































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

































































































































theorem valid8033 : plan8033.Valid := valid_step _ _ _ valid6072 (by decide +kernel)

theorem valid8034 : plan8034.Valid := valid_step _ _ _ valid6073 (by decide +kernel)

theorem valid8035 : plan8035.Valid := valid_step _ _ _ valid6074 (by decide +kernel)

theorem valid8036 : plan8036.Valid := valid_step _ _ _ valid6075 (by decide +kernel)

theorem valid8037 : plan8037.Valid := valid_step _ _ _ valid6076 (by decide +kernel)

theorem valid8038 : plan8038.Valid := valid_step _ _ _ valid6077 (by decide +kernel)

theorem valid8039 : plan8039.Valid := valid_step _ _ _ valid6078 (by decide +kernel)

theorem valid8040 : plan8040.Valid := valid_step _ _ _ valid6079 (by decide +kernel)

theorem valid8041 : plan8041.Valid := valid_step _ _ _ valid6080 (by decide +kernel)

theorem valid8042 : plan8042.Valid := valid_step _ _ _ valid6081 (by decide +kernel)

theorem valid8043 : plan8043.Valid := valid_step _ _ _ valid6082 (by decide +kernel)










































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
theorem t6_1734choices : plan7141.choices=[9,9,3,3,10,7].map (options 6 4) := by rfl


theorem t6_1734part0 : t6_1734jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1734part1 : t6_1734jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1734part2 : t6_1734jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1734frontier : t6_1734root.frontier 1=t6_1734jobs := by rfl
theorem t6_1734all : t6_1734jobs.all (Job.check tree)=true := by
  simp only [t6_1734jobs,List.all_append,List.all_nil,t6_1734part0,t6_1734part1,t6_1734part2,Bool.and_self]
theorem t6_1734checked : Checked tree [9,9,3,3,10,7] := by
  refine ⟨plan7141,valid7141,t6_1734choices,?_⟩
  exact check_of_frontier tree 1 t6_1734root t6_1734jobs t6_1734frontier t6_1734all
theorem t6_1735choices : plan7142.choices=[9,9,3,3,10,10].map (options 6 4) := by rfl


theorem t6_1735part0 : t6_1735jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1735frontier : t6_1735root.frontier 0=t6_1735jobs := by rfl
theorem t6_1735all : t6_1735jobs.all (Job.check tree)=true := by
  simp only [t6_1735jobs,List.all_append,List.all_nil,t6_1735part0,Bool.and_self]
theorem t6_1735checked : Checked tree [9,9,3,3,10,10] := by
  refine ⟨plan7142,valid7142,t6_1735choices,?_⟩
  exact check_of_frontier tree 0 t6_1735root t6_1735jobs t6_1735frontier t6_1735all
theorem t6_1736choices : plan7687.choices=[9,9,3,6,6,6].map (options 6 5) := by rfl


theorem t6_1736part0 : t6_1736jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1736frontier : t6_1736root.frontier 0=t6_1736jobs := by rfl
theorem t6_1736all : t6_1736jobs.all (Job.check tree)=true := by
  simp only [t6_1736jobs,List.all_append,List.all_nil,t6_1736part0,Bool.and_self]
theorem t6_1736checked : Checked tree [9,9,3,6,6,6] := by
  refine ⟨plan7687,valid7687,t6_1736choices,?_⟩
  exact check_of_frontier tree 0 t6_1736root t6_1736jobs t6_1736frontier t6_1736all
theorem t6_1737choices : plan7688.choices=[9,9,3,6,6,7].map (options 6 5) := by rfl


theorem t6_1737part0 : t6_1737jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1737part1 : t6_1737jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1737frontier : t6_1737root.frontier 1=t6_1737jobs := by rfl
theorem t6_1737all : t6_1737jobs.all (Job.check tree)=true := by
  simp only [t6_1737jobs,List.all_append,List.all_nil,t6_1737part0,t6_1737part1,Bool.and_self]
theorem t6_1737checked : Checked tree [9,9,3,6,6,7] := by
  refine ⟨plan7688,valid7688,t6_1737choices,?_⟩
  exact check_of_frontier tree 1 t6_1737root t6_1737jobs t6_1737frontier t6_1737all
theorem t6_1738choices : plan7689.choices=[9,9,3,6,6,10].map (options 6 5) := by rfl


theorem t6_1738part0 : t6_1738jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1738frontier : t6_1738root.frontier 0=t6_1738jobs := by rfl
theorem t6_1738all : t6_1738jobs.all (Job.check tree)=true := by
  simp only [t6_1738jobs,List.all_append,List.all_nil,t6_1738part0,Bool.and_self]
theorem t6_1738checked : Checked tree [9,9,3,6,6,10] := by
  refine ⟨plan7689,valid7689,t6_1738choices,?_⟩
  exact check_of_frontier tree 0 t6_1738root t6_1738jobs t6_1738frontier t6_1738all
theorem t6_1739choices : plan7690.choices=[9,9,3,6,7,7].map (options 6 5) := by rfl


theorem t6_1739part0 : t6_1739jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1739part1 : t6_1739jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1739part2 : t6_1739jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1739frontier : t6_1739root.frontier 1=t6_1739jobs := by rfl
theorem t6_1739all : t6_1739jobs.all (Job.check tree)=true := by
  simp only [t6_1739jobs,List.all_append,List.all_nil,t6_1739part0,t6_1739part1,t6_1739part2,Bool.and_self]
theorem t6_1739checked : Checked tree [9,9,3,6,7,7] := by
  refine ⟨plan7690,valid7690,t6_1739choices,?_⟩
  exact check_of_frontier tree 1 t6_1739root t6_1739jobs t6_1739frontier t6_1739all
theorem t6_1740choices : plan7691.choices=[9,9,3,6,10,7].map (options 6 5) := by rfl


theorem t6_1740part0 : t6_1740jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1740part1 : t6_1740jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1740frontier : t6_1740root.frontier 1=t6_1740jobs := by rfl
theorem t6_1740all : t6_1740jobs.all (Job.check tree)=true := by
  simp only [t6_1740jobs,List.all_append,List.all_nil,t6_1740part0,t6_1740part1,Bool.and_self]
theorem t6_1740checked : Checked tree [9,9,3,6,10,7] := by
  refine ⟨plan7691,valid7691,t6_1740choices,?_⟩
  exact check_of_frontier tree 1 t6_1740root t6_1740jobs t6_1740frontier t6_1740all
theorem t6_1741choices : plan7692.choices=[9,9,3,6,10,10].map (options 6 5) := by rfl


theorem t6_1741part0 : t6_1741jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1741frontier : t6_1741root.frontier 0=t6_1741jobs := by rfl
theorem t6_1741all : t6_1741jobs.all (Job.check tree)=true := by
  simp only [t6_1741jobs,List.all_append,List.all_nil,t6_1741part0,Bool.and_self]
theorem t6_1741checked : Checked tree [9,9,3,6,10,10] := by
  refine ⟨plan7692,valid7692,t6_1741choices,?_⟩
  exact check_of_frontier tree 0 t6_1741root t6_1741jobs t6_1741frontier t6_1741all
theorem t6_1742choices : plan7693.choices=[9,9,3,7,7,7].map (options 6 5) := by rfl


theorem t6_1742part0 : t6_1742jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1742part1 : t6_1742jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1742frontier : t6_1742root.frontier 1=t6_1742jobs := by rfl
theorem t6_1742all : t6_1742jobs.all (Job.check tree)=true := by
  simp only [t6_1742jobs,List.all_append,List.all_nil,t6_1742part0,t6_1742part1,Bool.and_self]
theorem t6_1742checked : Checked tree [9,9,3,7,7,7] := by
  refine ⟨plan7693,valid7693,t6_1742choices,?_⟩
  exact check_of_frontier tree 1 t6_1742root t6_1742jobs t6_1742frontier t6_1742all
theorem t6_1743choices : plan7694.choices=[9,9,3,10,7,7].map (options 6 5) := by rfl


theorem t6_1743part0 : t6_1743jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1743part1 : t6_1743jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1743part2 : t6_1743jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1743frontier : t6_1743root.frontier 1=t6_1743jobs := by rfl
theorem t6_1743all : t6_1743jobs.all (Job.check tree)=true := by
  simp only [t6_1743jobs,List.all_append,List.all_nil,t6_1743part0,t6_1743part1,t6_1743part2,Bool.and_self]
theorem t6_1743checked : Checked tree [9,9,3,10,7,7] := by
  refine ⟨plan7694,valid7694,t6_1743choices,?_⟩
  exact check_of_frontier tree 1 t6_1743root t6_1743jobs t6_1743frontier t6_1743all
theorem t6_1744choices : plan7695.choices=[9,9,3,10,10,7].map (options 6 5) := by rfl


theorem t6_1744part0 : t6_1744jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1744part1 : t6_1744jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1744frontier : t6_1744root.frontier 1=t6_1744jobs := by rfl
theorem t6_1744all : t6_1744jobs.all (Job.check tree)=true := by
  simp only [t6_1744jobs,List.all_append,List.all_nil,t6_1744part0,t6_1744part1,Bool.and_self]
theorem t6_1744checked : Checked tree [9,9,3,10,10,7] := by
  refine ⟨plan7695,valid7695,t6_1744choices,?_⟩
  exact check_of_frontier tree 1 t6_1744root t6_1744jobs t6_1744frontier t6_1744all
theorem t6_1745choices : plan7696.choices=[9,9,3,10,10,10].map (options 6 5) := by rfl


theorem t6_1745part0 : t6_1745jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1745frontier : t6_1745root.frontier 0=t6_1745jobs := by rfl
theorem t6_1745all : t6_1745jobs.all (Job.check tree)=true := by
  simp only [t6_1745jobs,List.all_append,List.all_nil,t6_1745part0,Bool.and_self]
theorem t6_1745checked : Checked tree [9,9,3,10,10,10] := by
  refine ⟨plan7696,valid7696,t6_1745choices,?_⟩
  exact check_of_frontier tree 0 t6_1745root t6_1745jobs t6_1745frontier t6_1745all
theorem t6_1746choices : plan8033.choices=[9,9,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1746part0 : t6_1746jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1746frontier : t6_1746root.frontier 0=t6_1746jobs := by rfl
theorem t6_1746all : t6_1746jobs.all (Job.check tree)=true := by
  simp only [t6_1746jobs,List.all_append,List.all_nil,t6_1746part0,Bool.and_self]
theorem t6_1746checked : Checked tree [9,9,6,6,6,6] := by
  refine ⟨plan8033,valid8033,t6_1746choices,?_⟩
  exact check_of_frontier tree 0 t6_1746root t6_1746jobs t6_1746frontier t6_1746all
theorem t6_1747choices : plan8034.choices=[9,9,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1747part0 : t6_1747jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1747frontier : t6_1747root.frontier 0=t6_1747jobs := by rfl
theorem t6_1747all : t6_1747jobs.all (Job.check tree)=true := by
  simp only [t6_1747jobs,List.all_append,List.all_nil,t6_1747part0,Bool.and_self]
theorem t6_1747checked : Checked tree [9,9,6,6,6,7] := by
  refine ⟨plan8034,valid8034,t6_1747choices,?_⟩
  exact check_of_frontier tree 0 t6_1747root t6_1747jobs t6_1747frontier t6_1747all
theorem t6_1748choices : plan8035.choices=[9,9,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1748part0 : t6_1748jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1748frontier : t6_1748root.frontier 0=t6_1748jobs := by rfl
theorem t6_1748all : t6_1748jobs.all (Job.check tree)=true := by
  simp only [t6_1748jobs,List.all_append,List.all_nil,t6_1748part0,Bool.and_self]
theorem t6_1748checked : Checked tree [9,9,6,6,6,10] := by
  refine ⟨plan8035,valid8035,t6_1748choices,?_⟩
  exact check_of_frontier tree 0 t6_1748root t6_1748jobs t6_1748frontier t6_1748all
theorem t6_1749choices : plan8036.choices=[9,9,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1749part0 : t6_1749jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1749frontier : t6_1749root.frontier 0=t6_1749jobs := by rfl
theorem t6_1749all : t6_1749jobs.all (Job.check tree)=true := by
  simp only [t6_1749jobs,List.all_append,List.all_nil,t6_1749part0,Bool.and_self]
theorem t6_1749checked : Checked tree [9,9,6,6,7,7] := by
  refine ⟨plan8036,valid8036,t6_1749choices,?_⟩
  exact check_of_frontier tree 0 t6_1749root t6_1749jobs t6_1749frontier t6_1749all
theorem t6_1750choices : plan8037.choices=[9,9,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1750part0 : t6_1750jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1750frontier : t6_1750root.frontier 0=t6_1750jobs := by rfl
theorem t6_1750all : t6_1750jobs.all (Job.check tree)=true := by
  simp only [t6_1750jobs,List.all_append,List.all_nil,t6_1750part0,Bool.and_self]
theorem t6_1750checked : Checked tree [9,9,6,6,10,7] := by
  refine ⟨plan8037,valid8037,t6_1750choices,?_⟩
  exact check_of_frontier tree 0 t6_1750root t6_1750jobs t6_1750frontier t6_1750all
theorem t6_1751choices : plan8038.choices=[9,9,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1751part0 : t6_1751jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1751frontier : t6_1751root.frontier 0=t6_1751jobs := by rfl
theorem t6_1751all : t6_1751jobs.all (Job.check tree)=true := by
  simp only [t6_1751jobs,List.all_append,List.all_nil,t6_1751part0,Bool.and_self]
theorem t6_1751checked : Checked tree [9,9,6,6,10,10] := by
  refine ⟨plan8038,valid8038,t6_1751choices,?_⟩
  exact check_of_frontier tree 0 t6_1751root t6_1751jobs t6_1751frontier t6_1751all
theorem t6_1752choices : plan8039.choices=[9,9,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1752part0 : t6_1752jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1752frontier : t6_1752root.frontier 0=t6_1752jobs := by rfl
theorem t6_1752all : t6_1752jobs.all (Job.check tree)=true := by
  simp only [t6_1752jobs,List.all_append,List.all_nil,t6_1752part0,Bool.and_self]
theorem t6_1752checked : Checked tree [9,9,6,7,7,7] := by
  refine ⟨plan8039,valid8039,t6_1752choices,?_⟩
  exact check_of_frontier tree 0 t6_1752root t6_1752jobs t6_1752frontier t6_1752all
theorem t6_1753choices : plan8040.choices=[9,9,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1753part0 : t6_1753jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1753frontier : t6_1753root.frontier 0=t6_1753jobs := by rfl
theorem t6_1753all : t6_1753jobs.all (Job.check tree)=true := by
  simp only [t6_1753jobs,List.all_append,List.all_nil,t6_1753part0,Bool.and_self]
theorem t6_1753checked : Checked tree [9,9,6,10,7,7] := by
  refine ⟨plan8040,valid8040,t6_1753choices,?_⟩
  exact check_of_frontier tree 0 t6_1753root t6_1753jobs t6_1753frontier t6_1753all
theorem t6_1754choices : plan8041.choices=[9,9,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1754part0 : t6_1754jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1754frontier : t6_1754root.frontier 0=t6_1754jobs := by rfl
theorem t6_1754all : t6_1754jobs.all (Job.check tree)=true := by
  simp only [t6_1754jobs,List.all_append,List.all_nil,t6_1754part0,Bool.and_self]
theorem t6_1754checked : Checked tree [9,9,6,10,10,7] := by
  refine ⟨plan8041,valid8041,t6_1754choices,?_⟩
  exact check_of_frontier tree 0 t6_1754root t6_1754jobs t6_1754frontier t6_1754all
theorem t6_1755choices : plan8042.choices=[9,9,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1755part0 : t6_1755jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1755frontier : t6_1755root.frontier 0=t6_1755jobs := by rfl
theorem t6_1755all : t6_1755jobs.all (Job.check tree)=true := by
  simp only [t6_1755jobs,List.all_append,List.all_nil,t6_1755part0,Bool.and_self]
theorem t6_1755checked : Checked tree [9,9,6,10,10,10] := by
  refine ⟨plan8042,valid8042,t6_1755choices,?_⟩
  exact check_of_frontier tree 0 t6_1755root t6_1755jobs t6_1755frontier t6_1755all
theorem t6_1756choices : plan8043.choices=[9,9,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1756part0 : t6_1756jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1756frontier : t6_1756root.frontier 0=t6_1756jobs := by rfl
theorem t6_1756all : t6_1756jobs.all (Job.check tree)=true := by
  simp only [t6_1756jobs,List.all_append,List.all_nil,t6_1756part0,Bool.and_self]
theorem t6_1756checked : Checked tree [9,9,7,7,7,7] := by
  refine ⟨plan8043,valid8043,t6_1756choices,?_⟩
  exact check_of_frontier tree 0 t6_1756root t6_1756jobs t6_1756frontier t6_1756all
theorem t6_1757choices : plan6693.choices=[9,9,9,3,3,3].map (options 6 3) := by rfl


theorem t6_1757part0 : t6_1757jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1757frontier : t6_1757root.frontier 0=t6_1757jobs := by rfl
theorem t6_1757all : t6_1757jobs.all (Job.check tree)=true := by
  simp only [t6_1757jobs,List.all_append,List.all_nil,t6_1757part0,Bool.and_self]
theorem t6_1757checked : Checked tree [9,9,9,3,3,3] := by
  refine ⟨plan6693,valid6693,t6_1757choices,?_⟩
  exact check_of_frontier tree 0 t6_1757root t6_1757jobs t6_1757frontier t6_1757all
theorem t6_1758choices : plan7143.choices=[9,9,9,3,3,6].map (options 6 4) := by rfl


theorem t6_1758part0 : t6_1758jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1758frontier : t6_1758root.frontier 0=t6_1758jobs := by rfl
theorem t6_1758all : t6_1758jobs.all (Job.check tree)=true := by
  simp only [t6_1758jobs,List.all_append,List.all_nil,t6_1758part0,Bool.and_self]
theorem t6_1758checked : Checked tree [9,9,9,3,3,6] := by
  refine ⟨plan7143,valid7143,t6_1758choices,?_⟩
  exact check_of_frontier tree 0 t6_1758root t6_1758jobs t6_1758frontier t6_1758all
theorem t6_1759choices : plan7144.choices=[9,9,9,3,3,7].map (options 6 4) := by rfl


theorem t6_1759part0 : t6_1759jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1759frontier : t6_1759root.frontier 0=t6_1759jobs := by rfl
theorem t6_1759all : t6_1759jobs.all (Job.check tree)=true := by
  simp only [t6_1759jobs,List.all_append,List.all_nil,t6_1759part0,Bool.and_self]
theorem t6_1759checked : Checked tree [9,9,9,3,3,7] := by
  refine ⟨plan7144,valid7144,t6_1759choices,?_⟩
  exact check_of_frontier tree 0 t6_1759root t6_1759jobs t6_1759frontier t6_1759all
theorem t6_1760choices : plan7145.choices=[9,9,9,3,3,10].map (options 6 4) := by rfl


theorem t6_1760part0 : t6_1760jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1760frontier : t6_1760root.frontier 0=t6_1760jobs := by rfl
theorem t6_1760all : t6_1760jobs.all (Job.check tree)=true := by
  simp only [t6_1760jobs,List.all_append,List.all_nil,t6_1760part0,Bool.and_self]
theorem t6_1760checked : Checked tree [9,9,9,3,3,10] := by
  refine ⟨plan7145,valid7145,t6_1760choices,?_⟩
  exact check_of_frontier tree 0 t6_1760root t6_1760jobs t6_1760frontier t6_1760all
theorem t6_1761choices : plan7697.choices=[9,9,9,3,6,6].map (options 6 5) := by rfl


theorem t6_1761part0 : t6_1761jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1761frontier : t6_1761root.frontier 0=t6_1761jobs := by rfl
theorem t6_1761all : t6_1761jobs.all (Job.check tree)=true := by
  simp only [t6_1761jobs,List.all_append,List.all_nil,t6_1761part0,Bool.and_self]
theorem t6_1761checked : Checked tree [9,9,9,3,6,6] := by
  refine ⟨plan7697,valid7697,t6_1761choices,?_⟩
  exact check_of_frontier tree 0 t6_1761root t6_1761jobs t6_1761frontier t6_1761all
theorem t6_1762choices : plan7698.choices=[9,9,9,3,6,7].map (options 6 5) := by rfl


theorem t6_1762part0 : t6_1762jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1762frontier : t6_1762root.frontier 0=t6_1762jobs := by rfl
theorem t6_1762all : t6_1762jobs.all (Job.check tree)=true := by
  simp only [t6_1762jobs,List.all_append,List.all_nil,t6_1762part0,Bool.and_self]
theorem t6_1762checked : Checked tree [9,9,9,3,6,7] := by
  refine ⟨plan7698,valid7698,t6_1762choices,?_⟩
  exact check_of_frontier tree 0 t6_1762root t6_1762jobs t6_1762frontier t6_1762all
theorem t6_1763choices : plan7699.choices=[9,9,9,3,6,10].map (options 6 5) := by rfl


theorem t6_1763part0 : t6_1763jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1763frontier : t6_1763root.frontier 0=t6_1763jobs := by rfl
theorem t6_1763all : t6_1763jobs.all (Job.check tree)=true := by
  simp only [t6_1763jobs,List.all_append,List.all_nil,t6_1763part0,Bool.and_self]
theorem t6_1763checked : Checked tree [9,9,9,3,6,10] := by
  refine ⟨plan7699,valid7699,t6_1763choices,?_⟩
  exact check_of_frontier tree 0 t6_1763root t6_1763jobs t6_1763frontier t6_1763all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks154 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1743checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1744checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1745checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1746checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1747checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1748checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1749checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1734checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1750checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1751checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1752checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1753checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1754checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1755checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1756checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1757checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1758checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1759checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1735checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1760checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1761checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1762checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1763checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1736checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1737checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1738checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1739checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1740checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1741checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1742checked⟩
