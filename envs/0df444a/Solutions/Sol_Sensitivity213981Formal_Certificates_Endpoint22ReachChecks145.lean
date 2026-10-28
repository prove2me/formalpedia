-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks145
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:57:25.252988+00:00
-- url     : https://prove2.me/submissions/f290562d-ccf4-434a-8991-ff3235e7e566

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks145
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks145
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
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











































theorem valid118 : plan118.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid123 : plan123.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid125 : plan125.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)





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

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)











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

theorem valid1533 : plan1533.Valid := valid_step _ _ _ valid560 (by decide +kernel)






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

theorem valid3307 : plan3307.Valid := valid_step _ _ _ valid1533 (by decide +kernel)










































































































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





























































































































































theorem valid6319 : plan6319.Valid := valid_step _ _ _ valid5356 (by decide +kernel)


































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

theorem valid5481 : plan5481.Valid := valid_step _ _ _ valid3307 (by decide +kernel)














































































































































































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























































































































theorem valid6684 : plan6684.Valid := valid_step _ _ _ valid5480 (by decide +kernel)

theorem valid6685 : plan6685.Valid := valid_step _ _ _ valid5481 (by decide +kernel)






































































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











































theorem valid7126 : plan7126.Valid := valid_step _ _ _ valid5731 (by decide +kernel)




















































































































































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



























































































































































































theorem valid6430 : plan6430.Valid := valid_step _ _ _ valid5393 (by decide +kernel)

theorem valid6431 : plan6431.Valid := valid_step _ _ _ valid5394 (by decide +kernel)

theorem valid6432 : plan6432.Valid := valid_step _ _ _ valid5395 (by decide +kernel)
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





































































































































































theorem valid7667 : plan7667.Valid := valid_step _ _ _ valid5935 (by decide +kernel)

theorem valid7668 : plan7668.Valid := valid_step _ _ _ valid5936 (by decide +kernel)

theorem valid7669 : plan7669.Valid := valid_step _ _ _ valid5949 (by decide +kernel)

theorem valid7670 : plan7670.Valid := valid_step _ _ _ valid5951 (by decide +kernel)

theorem valid7671 : plan7671.Valid := valid_step _ _ _ valid5952 (by decide +kernel)


















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











































theorem valid7990 : plan7990.Valid := valid_step _ _ _ valid6072 (by decide +kernel)

theorem valid7991 : plan7991.Valid := valid_step _ _ _ valid6073 (by decide +kernel)

theorem valid7992 : plan7992.Valid := valid_step _ _ _ valid6074 (by decide +kernel)

theorem valid7993 : plan7993.Valid := valid_step _ _ _ valid6075 (by decide +kernel)

theorem valid7994 : plan7994.Valid := valid_step _ _ _ valid6076 (by decide +kernel)

theorem valid7995 : plan7995.Valid := valid_step _ _ _ valid6077 (by decide +kernel)

theorem valid7996 : plan7996.Valid := valid_step _ _ _ valid6078 (by decide +kernel)

theorem valid7997 : plan7997.Valid := valid_step _ _ _ valid6079 (by decide +kernel)

theorem valid7998 : plan7998.Valid := valid_step _ _ _ valid6080 (by decide +kernel)

theorem valid7999 : plan7999.Valid := valid_step _ _ _ valid6081 (by decide +kernel)

theorem valid8000 : plan8000.Valid := valid_step _ _ _ valid6082 (by decide +kernel)

theorem valid8001 : plan8001.Valid := valid_step _ _ _ valid6084 (by decide +kernel)

theorem valid8002 : plan8002.Valid := valid_step _ _ _ valid6086 (by decide +kernel)

theorem valid8003 : plan8003.Valid := valid_step _ _ _ valid6087 (by decide +kernel)

theorem valid8004 : plan8004.Valid := valid_step _ _ _ valid6089 (by decide +kernel)

theorem valid8005 : plan8005.Valid := valid_step _ _ _ valid6091 (by decide +kernel)

theorem valid8006 : plan8006.Valid := valid_step _ _ _ valid6093 (by decide +kernel)

theorem valid8007 : plan8007.Valid := valid_step _ _ _ valid6094 (by decide +kernel)

theorem valid8008 : plan8008.Valid := valid_step _ _ _ valid6096 (by decide +kernel)

theorem valid8009 : plan8009.Valid := valid_step _ _ _ valid6097 (by decide +kernel)

theorem valid8010 : plan8010.Valid := valid_step _ _ _ valid6098 (by decide +kernel)

theorem valid8011 : plan8011.Valid := valid_step _ _ _ valid6099 (by decide +kernel)

theorem valid8012 : plan8012.Valid := valid_step _ _ _ valid6100 (by decide +kernel)

theorem valid8013 : plan8013.Valid := valid_step _ _ _ valid6101 (by decide +kernel)

theorem valid8014 : plan8014.Valid := valid_step _ _ _ valid6102 (by decide +kernel)

theorem valid8015 : plan8015.Valid := valid_step _ _ _ valid6103 (by decide +kernel)

theorem valid8016 : plan8016.Valid := valid_step _ _ _ valid6104 (by decide +kernel)
































































































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
theorem t6_1642choices : plan7667.choices=[8,9,3,10,10,7].map (options 6 5) := by rfl


theorem t6_1642part0 : t6_1642jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1642frontier : t6_1642root.frontier 0=t6_1642jobs := by rfl
theorem t6_1642all : t6_1642jobs.all (Job.check tree)=true := by
  simp only [t6_1642jobs,List.all_append,List.all_nil,t6_1642part0,Bool.and_self]
theorem t6_1642checked : Checked tree [8,9,3,10,10,7] := by
  refine ⟨plan7667,valid7667,t6_1642choices,?_⟩
  exact check_of_frontier tree 0 t6_1642root t6_1642jobs t6_1642frontier t6_1642all
theorem t6_1643choices : plan7668.choices=[8,9,3,10,10,10].map (options 6 5) := by rfl


theorem t6_1643part0 : t6_1643jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1643frontier : t6_1643root.frontier 0=t6_1643jobs := by rfl
theorem t6_1643all : t6_1643jobs.all (Job.check tree)=true := by
  simp only [t6_1643jobs,List.all_append,List.all_nil,t6_1643part0,Bool.and_self]
theorem t6_1643checked : Checked tree [8,9,3,10,10,10] := by
  refine ⟨plan7668,valid7668,t6_1643choices,?_⟩
  exact check_of_frontier tree 0 t6_1643root t6_1643jobs t6_1643frontier t6_1643all
theorem t6_1644choices : plan7990.choices=[8,9,6,6,6,6].map (options 6 6) := by rfl


theorem t6_1644part0 : t6_1644jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1644frontier : t6_1644root.frontier 0=t6_1644jobs := by rfl
theorem t6_1644all : t6_1644jobs.all (Job.check tree)=true := by
  simp only [t6_1644jobs,List.all_append,List.all_nil,t6_1644part0,Bool.and_self]
theorem t6_1644checked : Checked tree [8,9,6,6,6,6] := by
  refine ⟨plan7990,valid7990,t6_1644choices,?_⟩
  exact check_of_frontier tree 0 t6_1644root t6_1644jobs t6_1644frontier t6_1644all
theorem t6_1645choices : plan7991.choices=[8,9,6,6,6,7].map (options 6 6) := by rfl


theorem t6_1645part0 : t6_1645jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1645frontier : t6_1645root.frontier 0=t6_1645jobs := by rfl
theorem t6_1645all : t6_1645jobs.all (Job.check tree)=true := by
  simp only [t6_1645jobs,List.all_append,List.all_nil,t6_1645part0,Bool.and_self]
theorem t6_1645checked : Checked tree [8,9,6,6,6,7] := by
  refine ⟨plan7991,valid7991,t6_1645choices,?_⟩
  exact check_of_frontier tree 0 t6_1645root t6_1645jobs t6_1645frontier t6_1645all
theorem t6_1646choices : plan7992.choices=[8,9,6,6,6,10].map (options 6 6) := by rfl


theorem t6_1646part0 : t6_1646jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1646frontier : t6_1646root.frontier 0=t6_1646jobs := by rfl
theorem t6_1646all : t6_1646jobs.all (Job.check tree)=true := by
  simp only [t6_1646jobs,List.all_append,List.all_nil,t6_1646part0,Bool.and_self]
theorem t6_1646checked : Checked tree [8,9,6,6,6,10] := by
  refine ⟨plan7992,valid7992,t6_1646choices,?_⟩
  exact check_of_frontier tree 0 t6_1646root t6_1646jobs t6_1646frontier t6_1646all
theorem t6_1647choices : plan7993.choices=[8,9,6,6,7,7].map (options 6 6) := by rfl


theorem t6_1647part0 : t6_1647jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1647frontier : t6_1647root.frontier 0=t6_1647jobs := by rfl
theorem t6_1647all : t6_1647jobs.all (Job.check tree)=true := by
  simp only [t6_1647jobs,List.all_append,List.all_nil,t6_1647part0,Bool.and_self]
theorem t6_1647checked : Checked tree [8,9,6,6,7,7] := by
  refine ⟨plan7993,valid7993,t6_1647choices,?_⟩
  exact check_of_frontier tree 0 t6_1647root t6_1647jobs t6_1647frontier t6_1647all
theorem t6_1648choices : plan7994.choices=[8,9,6,6,10,7].map (options 6 6) := by rfl


theorem t6_1648part0 : t6_1648jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1648frontier : t6_1648root.frontier 0=t6_1648jobs := by rfl
theorem t6_1648all : t6_1648jobs.all (Job.check tree)=true := by
  simp only [t6_1648jobs,List.all_append,List.all_nil,t6_1648part0,Bool.and_self]
theorem t6_1648checked : Checked tree [8,9,6,6,10,7] := by
  refine ⟨plan7994,valid7994,t6_1648choices,?_⟩
  exact check_of_frontier tree 0 t6_1648root t6_1648jobs t6_1648frontier t6_1648all
theorem t6_1649choices : plan7995.choices=[8,9,6,6,10,10].map (options 6 6) := by rfl


theorem t6_1649part0 : t6_1649jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1649frontier : t6_1649root.frontier 0=t6_1649jobs := by rfl
theorem t6_1649all : t6_1649jobs.all (Job.check tree)=true := by
  simp only [t6_1649jobs,List.all_append,List.all_nil,t6_1649part0,Bool.and_self]
theorem t6_1649checked : Checked tree [8,9,6,6,10,10] := by
  refine ⟨plan7995,valid7995,t6_1649choices,?_⟩
  exact check_of_frontier tree 0 t6_1649root t6_1649jobs t6_1649frontier t6_1649all
theorem t6_1650choices : plan7996.choices=[8,9,6,7,7,7].map (options 6 6) := by rfl


theorem t6_1650part0 : t6_1650jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1650frontier : t6_1650root.frontier 0=t6_1650jobs := by rfl
theorem t6_1650all : t6_1650jobs.all (Job.check tree)=true := by
  simp only [t6_1650jobs,List.all_append,List.all_nil,t6_1650part0,Bool.and_self]
theorem t6_1650checked : Checked tree [8,9,6,7,7,7] := by
  refine ⟨plan7996,valid7996,t6_1650choices,?_⟩
  exact check_of_frontier tree 0 t6_1650root t6_1650jobs t6_1650frontier t6_1650all
theorem t6_1651choices : plan7997.choices=[8,9,6,10,7,7].map (options 6 6) := by rfl


theorem t6_1651part0 : t6_1651jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1651frontier : t6_1651root.frontier 0=t6_1651jobs := by rfl
theorem t6_1651all : t6_1651jobs.all (Job.check tree)=true := by
  simp only [t6_1651jobs,List.all_append,List.all_nil,t6_1651part0,Bool.and_self]
theorem t6_1651checked : Checked tree [8,9,6,10,7,7] := by
  refine ⟨plan7997,valid7997,t6_1651choices,?_⟩
  exact check_of_frontier tree 0 t6_1651root t6_1651jobs t6_1651frontier t6_1651all
theorem t6_1652choices : plan7998.choices=[8,9,6,10,10,7].map (options 6 6) := by rfl


theorem t6_1652part0 : t6_1652jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1652frontier : t6_1652root.frontier 0=t6_1652jobs := by rfl
theorem t6_1652all : t6_1652jobs.all (Job.check tree)=true := by
  simp only [t6_1652jobs,List.all_append,List.all_nil,t6_1652part0,Bool.and_self]
theorem t6_1652checked : Checked tree [8,9,6,10,10,7] := by
  refine ⟨plan7998,valid7998,t6_1652choices,?_⟩
  exact check_of_frontier tree 0 t6_1652root t6_1652jobs t6_1652frontier t6_1652all
theorem t6_1653choices : plan7999.choices=[8,9,6,10,10,10].map (options 6 6) := by rfl


theorem t6_1653part0 : t6_1653jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1653frontier : t6_1653root.frontier 0=t6_1653jobs := by rfl
theorem t6_1653all : t6_1653jobs.all (Job.check tree)=true := by
  simp only [t6_1653jobs,List.all_append,List.all_nil,t6_1653part0,Bool.and_self]
theorem t6_1653checked : Checked tree [8,9,6,10,10,10] := by
  refine ⟨plan7999,valid7999,t6_1653choices,?_⟩
  exact check_of_frontier tree 0 t6_1653root t6_1653jobs t6_1653frontier t6_1653all
theorem t6_1654choices : plan8000.choices=[8,9,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1654part0 : t6_1654jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1654frontier : t6_1654root.frontier 0=t6_1654jobs := by rfl
theorem t6_1654all : t6_1654jobs.all (Job.check tree)=true := by
  simp only [t6_1654jobs,List.all_append,List.all_nil,t6_1654part0,Bool.and_self]
theorem t6_1654checked : Checked tree [8,9,7,7,7,7] := by
  refine ⟨plan8000,valid8000,t6_1654choices,?_⟩
  exact check_of_frontier tree 0 t6_1654root t6_1654jobs t6_1654frontier t6_1654all
theorem t6_1655choices : plan7126.choices=[8,9,9,3,3,7].map (options 6 4) := by rfl


theorem t6_1655part0 : t6_1655jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1655frontier : t6_1655root.frontier 0=t6_1655jobs := by rfl
theorem t6_1655all : t6_1655jobs.all (Job.check tree)=true := by
  simp only [t6_1655jobs,List.all_append,List.all_nil,t6_1655part0,Bool.and_self]
theorem t6_1655checked : Checked tree [8,9,9,3,3,7] := by
  refine ⟨plan7126,valid7126,t6_1655choices,?_⟩
  exact check_of_frontier tree 0 t6_1655root t6_1655jobs t6_1655frontier t6_1655all
theorem t6_1656choices : plan7669.choices=[8,9,9,3,6,7].map (options 6 5) := by rfl


theorem t6_1656part0 : t6_1656jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1656frontier : t6_1656root.frontier 0=t6_1656jobs := by rfl
theorem t6_1656all : t6_1656jobs.all (Job.check tree)=true := by
  simp only [t6_1656jobs,List.all_append,List.all_nil,t6_1656part0,Bool.and_self]
theorem t6_1656checked : Checked tree [8,9,9,3,6,7] := by
  refine ⟨plan7669,valid7669,t6_1656choices,?_⟩
  exact check_of_frontier tree 0 t6_1656root t6_1656jobs t6_1656frontier t6_1656all
theorem t6_1657choices : plan7670.choices=[8,9,9,3,7,7].map (options 6 5) := by rfl


theorem t6_1657part0 : t6_1657jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1657frontier : t6_1657root.frontier 0=t6_1657jobs := by rfl
theorem t6_1657all : t6_1657jobs.all (Job.check tree)=true := by
  simp only [t6_1657jobs,List.all_append,List.all_nil,t6_1657part0,Bool.and_self]
theorem t6_1657checked : Checked tree [8,9,9,3,7,7] := by
  refine ⟨plan7670,valid7670,t6_1657choices,?_⟩
  exact check_of_frontier tree 0 t6_1657root t6_1657jobs t6_1657frontier t6_1657all
theorem t6_1658choices : plan7671.choices=[8,9,9,3,10,7].map (options 6 5) := by rfl


theorem t6_1658part0 : t6_1658jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1658frontier : t6_1658root.frontier 0=t6_1658jobs := by rfl
theorem t6_1658all : t6_1658jobs.all (Job.check tree)=true := by
  simp only [t6_1658jobs,List.all_append,List.all_nil,t6_1658part0,Bool.and_self]
theorem t6_1658checked : Checked tree [8,9,9,3,10,7] := by
  refine ⟨plan7671,valid7671,t6_1658choices,?_⟩
  exact check_of_frontier tree 0 t6_1658root t6_1658jobs t6_1658frontier t6_1658all
theorem t6_1659choices : plan8001.choices=[8,9,9,6,6,7].map (options 6 6) := by rfl


theorem t6_1659part0 : t6_1659jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1659frontier : t6_1659root.frontier 0=t6_1659jobs := by rfl
theorem t6_1659all : t6_1659jobs.all (Job.check tree)=true := by
  simp only [t6_1659jobs,List.all_append,List.all_nil,t6_1659part0,Bool.and_self]
theorem t6_1659checked : Checked tree [8,9,9,6,6,7] := by
  refine ⟨plan8001,valid8001,t6_1659choices,?_⟩
  exact check_of_frontier tree 0 t6_1659root t6_1659jobs t6_1659frontier t6_1659all
theorem t6_1660choices : plan8002.choices=[8,9,9,6,7,7].map (options 6 6) := by rfl


theorem t6_1660part0 : t6_1660jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1660frontier : t6_1660root.frontier 0=t6_1660jobs := by rfl
theorem t6_1660all : t6_1660jobs.all (Job.check tree)=true := by
  simp only [t6_1660jobs,List.all_append,List.all_nil,t6_1660part0,Bool.and_self]
theorem t6_1660checked : Checked tree [8,9,9,6,7,7] := by
  refine ⟨plan8002,valid8002,t6_1660choices,?_⟩
  exact check_of_frontier tree 0 t6_1660root t6_1660jobs t6_1660frontier t6_1660all
theorem t6_1661choices : plan8003.choices=[8,9,9,6,10,7].map (options 6 6) := by rfl


theorem t6_1661part0 : t6_1661jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1661frontier : t6_1661root.frontier 0=t6_1661jobs := by rfl
theorem t6_1661all : t6_1661jobs.all (Job.check tree)=true := by
  simp only [t6_1661jobs,List.all_append,List.all_nil,t6_1661part0,Bool.and_self]
theorem t6_1661checked : Checked tree [8,9,9,6,10,7] := by
  refine ⟨plan8003,valid8003,t6_1661choices,?_⟩
  exact check_of_frontier tree 0 t6_1661root t6_1661jobs t6_1661frontier t6_1661all
theorem t6_1662choices : plan8004.choices=[8,9,9,7,7,7].map (options 6 6) := by rfl


theorem t6_1662part0 : t6_1662jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1662frontier : t6_1662root.frontier 0=t6_1662jobs := by rfl
theorem t6_1662all : t6_1662jobs.all (Job.check tree)=true := by
  simp only [t6_1662jobs,List.all_append,List.all_nil,t6_1662part0,Bool.and_self]
theorem t6_1662checked : Checked tree [8,9,9,7,7,7] := by
  refine ⟨plan8004,valid8004,t6_1662choices,?_⟩
  exact check_of_frontier tree 0 t6_1662root t6_1662jobs t6_1662frontier t6_1662all
theorem t6_1663choices : plan8005.choices=[8,9,9,9,7,7].map (options 6 6) := by rfl


theorem t6_1663part0 : t6_1663jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1663frontier : t6_1663root.frontier 0=t6_1663jobs := by rfl
theorem t6_1663all : t6_1663jobs.all (Job.check tree)=true := by
  simp only [t6_1663jobs,List.all_append,List.all_nil,t6_1663part0,Bool.and_self]
theorem t6_1663checked : Checked tree [8,9,9,9,7,7] := by
  refine ⟨plan8005,valid8005,t6_1663choices,?_⟩
  exact check_of_frontier tree 0 t6_1663root t6_1663jobs t6_1663frontier t6_1663all
theorem t6_1664choices : plan8006.choices=[8,9,9,10,7,7].map (options 6 6) := by rfl


theorem t6_1664part0 : t6_1664jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1664frontier : t6_1664root.frontier 0=t6_1664jobs := by rfl
theorem t6_1664all : t6_1664jobs.all (Job.check tree)=true := by
  simp only [t6_1664jobs,List.all_append,List.all_nil,t6_1664part0,Bool.and_self]
theorem t6_1664checked : Checked tree [8,9,9,10,7,7] := by
  refine ⟨plan8006,valid8006,t6_1664choices,?_⟩
  exact check_of_frontier tree 0 t6_1664root t6_1664jobs t6_1664frontier t6_1664all
theorem t6_1665choices : plan8007.choices=[8,9,9,10,10,7].map (options 6 6) := by rfl


theorem t6_1665part0 : t6_1665jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1665frontier : t6_1665root.frontier 0=t6_1665jobs := by rfl
theorem t6_1665all : t6_1665jobs.all (Job.check tree)=true := by
  simp only [t6_1665jobs,List.all_append,List.all_nil,t6_1665part0,Bool.and_self]
theorem t6_1665checked : Checked tree [8,9,9,10,10,7] := by
  refine ⟨plan8007,valid8007,t6_1665choices,?_⟩
  exact check_of_frontier tree 0 t6_1665root t6_1665jobs t6_1665frontier t6_1665all
theorem t6_1666choices : plan8008.choices=[8,9,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1666part0 : t6_1666jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1666frontier : t6_1666root.frontier 0=t6_1666jobs := by rfl
theorem t6_1666all : t6_1666jobs.all (Job.check tree)=true := by
  simp only [t6_1666jobs,List.all_append,List.all_nil,t6_1666part0,Bool.and_self]
theorem t6_1666checked : Checked tree [8,9,10,7,7,7] := by
  refine ⟨plan8008,valid8008,t6_1666choices,?_⟩
  exact check_of_frontier tree 0 t6_1666root t6_1666jobs t6_1666frontier t6_1666all
theorem t6_1667choices : plan8009.choices=[8,9,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1667part0 : t6_1667jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1667frontier : t6_1667root.frontier 0=t6_1667jobs := by rfl
theorem t6_1667all : t6_1667jobs.all (Job.check tree)=true := by
  simp only [t6_1667jobs,List.all_append,List.all_nil,t6_1667part0,Bool.and_self]
theorem t6_1667checked : Checked tree [8,9,10,10,7,7] := by
  refine ⟨plan8009,valid8009,t6_1667choices,?_⟩
  exact check_of_frontier tree 0 t6_1667root t6_1667jobs t6_1667frontier t6_1667all
theorem t6_1668choices : plan8010.choices=[8,9,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1668part0 : t6_1668jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1668frontier : t6_1668root.frontier 0=t6_1668jobs := by rfl
theorem t6_1668all : t6_1668jobs.all (Job.check tree)=true := by
  simp only [t6_1668jobs,List.all_append,List.all_nil,t6_1668part0,Bool.and_self]
theorem t6_1668checked : Checked tree [8,9,10,10,10,7] := by
  refine ⟨plan8010,valid8010,t6_1668choices,?_⟩
  exact check_of_frontier tree 0 t6_1668root t6_1668jobs t6_1668frontier t6_1668all
theorem t6_1669choices : plan8011.choices=[8,9,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1669part0 : t6_1669jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1669frontier : t6_1669root.frontier 0=t6_1669jobs := by rfl
theorem t6_1669all : t6_1669jobs.all (Job.check tree)=true := by
  simp only [t6_1669jobs,List.all_append,List.all_nil,t6_1669part0,Bool.and_self]
theorem t6_1669checked : Checked tree [8,9,10,10,10,10] := by
  refine ⟨plan8011,valid8011,t6_1669choices,?_⟩
  exact check_of_frontier tree 0 t6_1669root t6_1669jobs t6_1669frontier t6_1669all
theorem t6_1670choices : plan8012.choices=[8,10,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1670part0 : t6_1670jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1670frontier : t6_1670root.frontier 0=t6_1670jobs := by rfl
theorem t6_1670all : t6_1670jobs.all (Job.check tree)=true := by
  simp only [t6_1670jobs,List.all_append,List.all_nil,t6_1670part0,Bool.and_self]
theorem t6_1670checked : Checked tree [8,10,7,7,7,7] := by
  refine ⟨plan8012,valid8012,t6_1670choices,?_⟩
  exact check_of_frontier tree 0 t6_1670root t6_1670jobs t6_1670frontier t6_1670all
theorem t6_1671choices : plan8013.choices=[8,10,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1671part0 : t6_1671jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1671frontier : t6_1671root.frontier 0=t6_1671jobs := by rfl
theorem t6_1671all : t6_1671jobs.all (Job.check tree)=true := by
  simp only [t6_1671jobs,List.all_append,List.all_nil,t6_1671part0,Bool.and_self]
theorem t6_1671checked : Checked tree [8,10,10,7,7,7] := by
  refine ⟨plan8013,valid8013,t6_1671choices,?_⟩
  exact check_of_frontier tree 0 t6_1671root t6_1671jobs t6_1671frontier t6_1671all
theorem t6_1672choices : plan8014.choices=[8,10,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1672part0 : t6_1672jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1672frontier : t6_1672root.frontier 0=t6_1672jobs := by rfl
theorem t6_1672all : t6_1672jobs.all (Job.check tree)=true := by
  simp only [t6_1672jobs,List.all_append,List.all_nil,t6_1672part0,Bool.and_self]
theorem t6_1672checked : Checked tree [8,10,10,10,7,7] := by
  refine ⟨plan8014,valid8014,t6_1672choices,?_⟩
  exact check_of_frontier tree 0 t6_1672root t6_1672jobs t6_1672frontier t6_1672all
theorem t6_1673choices : plan8015.choices=[8,10,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1673part0 : t6_1673jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1673frontier : t6_1673root.frontier 0=t6_1673jobs := by rfl
theorem t6_1673all : t6_1673jobs.all (Job.check tree)=true := by
  simp only [t6_1673jobs,List.all_append,List.all_nil,t6_1673part0,Bool.and_self]
theorem t6_1673checked : Checked tree [8,10,10,10,10,7] := by
  refine ⟨plan8015,valid8015,t6_1673choices,?_⟩
  exact check_of_frontier tree 0 t6_1673root t6_1673jobs t6_1673frontier t6_1673all
theorem t6_1674choices : plan8016.choices=[8,10,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1674part0 : t6_1674jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1674frontier : t6_1674root.frontier 0=t6_1674jobs := by rfl
theorem t6_1674all : t6_1674jobs.all (Job.check tree)=true := by
  simp only [t6_1674jobs,List.all_append,List.all_nil,t6_1674part0,Bool.and_self]
theorem t6_1674checked : Checked tree [8,10,10,10,10,10] := by
  refine ⟨plan8016,valid8016,t6_1674choices,?_⟩
  exact check_of_frontier tree 0 t6_1674root t6_1674jobs t6_1674frontier t6_1674all
theorem t6_1675choices : plan6319.choices=[9,3,3,3,3,3].map (options 6 1) := by rfl


theorem t6_1675part0 : t6_1675jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1675frontier : t6_1675root.frontier 0=t6_1675jobs := by rfl
theorem t6_1675all : t6_1675jobs.all (Job.check tree)=true := by
  simp only [t6_1675jobs,List.all_append,List.all_nil,t6_1675part0,Bool.and_self]
theorem t6_1675checked : Checked tree [9,3,3,3,3,3] := by
  refine ⟨plan6319,valid6319,t6_1675choices,?_⟩
  exact check_of_frontier tree 0 t6_1675root t6_1675jobs t6_1675frontier t6_1675all
theorem t6_1676choices : plan6430.choices=[9,3,3,3,3,6].map (options 6 2) := by rfl


theorem t6_1676part0 : t6_1676jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1676frontier : t6_1676root.frontier 0=t6_1676jobs := by rfl
theorem t6_1676all : t6_1676jobs.all (Job.check tree)=true := by
  simp only [t6_1676jobs,List.all_append,List.all_nil,t6_1676part0,Bool.and_self]
theorem t6_1676checked : Checked tree [9,3,3,3,3,6] := by
  refine ⟨plan6430,valid6430,t6_1676choices,?_⟩
  exact check_of_frontier tree 0 t6_1676root t6_1676jobs t6_1676frontier t6_1676all
theorem t6_1677choices : plan6431.choices=[9,3,3,3,3,7].map (options 6 2) := by rfl


theorem t6_1677part0 : t6_1677jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1677part1 : t6_1677jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1677part2 : t6_1677jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1677frontier : t6_1677root.frontier 1=t6_1677jobs := by rfl
theorem t6_1677all : t6_1677jobs.all (Job.check tree)=true := by
  simp only [t6_1677jobs,List.all_append,List.all_nil,t6_1677part0,t6_1677part1,t6_1677part2,Bool.and_self]
theorem t6_1677checked : Checked tree [9,3,3,3,3,7] := by
  refine ⟨plan6431,valid6431,t6_1677choices,?_⟩
  exact check_of_frontier tree 1 t6_1677root t6_1677jobs t6_1677frontier t6_1677all
theorem t6_1678choices : plan6432.choices=[9,3,3,3,3,10].map (options 6 2) := by rfl


theorem t6_1678part0 : t6_1678jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1678frontier : t6_1678root.frontier 0=t6_1678jobs := by rfl
theorem t6_1678all : t6_1678jobs.all (Job.check tree)=true := by
  simp only [t6_1678jobs,List.all_append,List.all_nil,t6_1678part0,Bool.and_self]
theorem t6_1678checked : Checked tree [9,3,3,3,3,10] := by
  refine ⟨plan6432,valid6432,t6_1678choices,?_⟩
  exact check_of_frontier tree 0 t6_1678root t6_1678jobs t6_1678frontier t6_1678all
theorem t6_1679choices : plan6684.choices=[9,3,3,3,6,6].map (options 6 3) := by rfl


theorem t6_1679part0 : t6_1679jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1679part1 : t6_1679jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1679frontier : t6_1679root.frontier 1=t6_1679jobs := by rfl
theorem t6_1679all : t6_1679jobs.all (Job.check tree)=true := by
  simp only [t6_1679jobs,List.all_append,List.all_nil,t6_1679part0,t6_1679part1,Bool.and_self]
theorem t6_1679checked : Checked tree [9,3,3,3,6,6] := by
  refine ⟨plan6684,valid6684,t6_1679choices,?_⟩
  exact check_of_frontier tree 1 t6_1679root t6_1679jobs t6_1679frontier t6_1679all
theorem t6_1680choices : plan6685.choices=[9,3,3,3,6,7].map (options 6 3) := by rfl


theorem t6_1680part0 : t6_1680jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1680part1 : t6_1680jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1680part2 : t6_1680jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1680part3 : t6_1680jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1680part4 : t6_1680jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1680part5 : t6_1680jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1680frontier : t6_1680root.frontier 2=t6_1680jobs := by rfl
theorem t6_1680all : t6_1680jobs.all (Job.check tree)=true := by
  simp only [t6_1680jobs,List.all_append,List.all_nil,t6_1680part0,t6_1680part1,t6_1680part2,t6_1680part3,t6_1680part4,t6_1680part5,Bool.and_self]
theorem t6_1680checked : Checked tree [9,3,3,3,6,7] := by
  refine ⟨plan6685,valid6685,t6_1680choices,?_⟩
  exact check_of_frontier tree 2 t6_1680root t6_1680jobs t6_1680frontier t6_1680all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks145 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1654checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1642checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1655checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1656checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1657checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1658checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1659checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1660checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1661checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1662checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1663checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1664checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1643checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1665checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1666checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1667checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1668checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1669checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1670checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1671checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1672checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1673checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1674checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1644checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1675checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1676checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1677checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1678checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1679checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1645checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1680checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1646checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1647checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1648checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1649checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1650checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1651checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1652checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1653checked⟩
