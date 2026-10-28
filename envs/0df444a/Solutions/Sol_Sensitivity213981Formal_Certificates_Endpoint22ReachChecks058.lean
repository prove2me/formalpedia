-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks058
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:08:45.573038+00:00
-- url     : https://prove2.me/submissions/11f01d7a-d3b4-4e7b-a8fe-2745887dddb6

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks058
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans075
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































































theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid133 : plan133.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid134 : plan134.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid135 : plan135.Valid := valid_step _ _ _ valid0 (by decide +kernel)


















































































































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

























































































































































theorem valid557 : plan557.Valid := valid_step _ _ _ valid128 (by decide +kernel)























theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)



theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)





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



















































































































































































theorem valid1530 : plan1530.Valid := valid_step _ _ _ valid557 (by decide +kernel)












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















































theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)



theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)























































theorem valid1591 : plan1591.Valid := valid_step _ _ _ valid578 (by decide +kernel)



theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)





theorem valid1602 : plan1602.Valid := valid_step _ _ _ valid578 (by decide +kernel)



theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1606 : plan1606.Valid := valid_step _ _ _ valid580 (by decide +kernel)




















































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























































































































theorem valid3324 : plan3324.Valid := valid_step _ _ _ valid1530 (by decide +kernel)























theorem valid3336 : plan3336.Valid := valid_step _ _ _ valid1530 (by decide +kernel)
















































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





























theorem valid3375 : plan3375.Valid := valid_step _ _ _ valid1560 (by decide +kernel)



theorem valid3377 : plan3377.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3378 : plan3378.Valid := valid_step _ _ _ valid1563 (by decide +kernel)







































































theorem valid3414 : plan3414.Valid := valid_step _ _ _ valid1560 (by decide +kernel)



theorem valid3416 : plan3416.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3417 : plan3417.Valid := valid_step _ _ _ valid1563 (by decide +kernel)














































































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















































































theorem valid5512 : plan5512.Valid := valid_step _ _ _ valid3324 (by decide +kernel)







theorem valid5516 : plan5516.Valid := valid_step _ _ _ valid3336 (by decide +kernel)








































































































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





















































































































































































theorem valid6523 : plan6523.Valid := valid_step _ _ _ valid5512 (by decide +kernel)

theorem valid6524 : plan6524.Valid := valid_step _ _ _ valid5516 (by decide +kernel)








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





theorem valid3459 : plan3459.Valid := valid_step _ _ _ valid1591 (by decide +kernel)





theorem valid3462 : plan3462.Valid := valid_step _ _ _ valid1594 (by decide +kernel)



theorem valid3464 : plan3464.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3465 : plan3465.Valid := valid_step _ _ _ valid1597 (by decide +kernel)



theorem valid3467 : plan3467.Valid := valid_step _ _ _ valid1599 (by decide +kernel)





theorem valid3470 : plan3470.Valid := valid_step _ _ _ valid1602 (by decide +kernel)



theorem valid3472 : plan3472.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3473 : plan3473.Valid := valid_step _ _ _ valid1605 (by decide +kernel)



theorem valid3475 : plan3475.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3477 : plan3477.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

















theorem valid3494 : plan3494.Valid := valid_step _ _ _ valid1594 (by decide +kernel)



theorem valid3496 : plan3496.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3497 : plan3497.Valid := valid_step _ _ _ valid1597 (by decide +kernel)



theorem valid3499 : plan3499.Valid := valid_step _ _ _ valid1599 (by decide +kernel)





theorem valid3502 : plan3502.Valid := valid_step _ _ _ valid1602 (by decide +kernel)



theorem valid3504 : plan3504.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3505 : plan3505.Valid := valid_step _ _ _ valid1605 (by decide +kernel)



theorem valid3507 : plan3507.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3508 : plan3508.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3509 : plan3509.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3510 : plan3510.Valid := valid_step _ _ _ valid1606 (by decide +kernel)




















































































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



































theorem valid5682 : plan5682.Valid := valid_step _ _ _ valid3375 (by decide +kernel)



theorem valid5684 : plan5684.Valid := valid_step _ _ _ valid3377 (by decide +kernel)

theorem valid5685 : plan5685.Valid := valid_step _ _ _ valid3378 (by decide +kernel)















theorem valid5693 : plan5693.Valid := valid_step _ _ _ valid3414 (by decide +kernel)



theorem valid5695 : plan5695.Valid := valid_step _ _ _ valid3416 (by decide +kernel)

theorem valid5696 : plan5696.Valid := valid_step _ _ _ valid3417 (by decide +kernel)
































































































































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















































































































































theorem valid5832 : plan5832.Valid := valid_step _ _ _ valid3459 (by decide +kernel)





theorem valid5835 : plan5835.Valid := valid_step _ _ _ valid3462 (by decide +kernel)



theorem valid5837 : plan5837.Valid := valid_step _ _ _ valid3464 (by decide +kernel)

theorem valid5838 : plan5838.Valid := valid_step _ _ _ valid3465 (by decide +kernel)



theorem valid5840 : plan5840.Valid := valid_step _ _ _ valid3467 (by decide +kernel)





theorem valid5843 : plan5843.Valid := valid_step _ _ _ valid3470 (by decide +kernel)



theorem valid5845 : plan5845.Valid := valid_step _ _ _ valid3472 (by decide +kernel)

theorem valid5846 : plan5846.Valid := valid_step _ _ _ valid3473 (by decide +kernel)



theorem valid5848 : plan5848.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5849 : plan5849.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5850 : plan5850.Valid := valid_step _ _ _ valid3477 (by decide +kernel)

theorem valid5851 : plan5851.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5852 : plan5852.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5853 : plan5853.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5854 : plan5854.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5855 : plan5855.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5856 : plan5856.Valid := valid_step _ _ _ valid3483 (by decide +kernel)
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

theorem valid5857 : plan5857.Valid := valid_step _ _ _ valid3484 (by decide +kernel)

theorem valid5858 : plan5858.Valid := valid_step _ _ _ valid3485 (by decide +kernel)















theorem valid5866 : plan5866.Valid := valid_step _ _ _ valid3494 (by decide +kernel)



theorem valid5868 : plan5868.Valid := valid_step _ _ _ valid3496 (by decide +kernel)

theorem valid5869 : plan5869.Valid := valid_step _ _ _ valid3497 (by decide +kernel)



theorem valid5871 : plan5871.Valid := valid_step _ _ _ valid3499 (by decide +kernel)





theorem valid5874 : plan5874.Valid := valid_step _ _ _ valid3502 (by decide +kernel)



theorem valid5876 : plan5876.Valid := valid_step _ _ _ valid3504 (by decide +kernel)

theorem valid5877 : plan5877.Valid := valid_step _ _ _ valid3505 (by decide +kernel)



theorem valid5879 : plan5879.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5880 : plan5880.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5881 : plan5881.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5882 : plan5882.Valid := valid_step _ _ _ valid3510 (by decide +kernel)

theorem valid5883 : plan5883.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5884 : plan5884.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5885 : plan5885.Valid := valid_step _ _ _ valid3477 (by decide +kernel)

theorem valid5886 : plan5886.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5887 : plan5887.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5888 : plan5888.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5889 : plan5889.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5890 : plan5890.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5891 : plan5891.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5892 : plan5892.Valid := valid_step _ _ _ valid3484 (by decide +kernel)

theorem valid5893 : plan5893.Valid := valid_step _ _ _ valid3485 (by decide +kernel)






















































































































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



























































theorem valid7230 : plan7230.Valid := valid_step _ _ _ valid5832 (by decide +kernel)

theorem valid7231 : plan7231.Valid := valid_step _ _ _ valid5835 (by decide +kernel)

theorem valid7232 : plan7232.Valid := valid_step _ _ _ valid5837 (by decide +kernel)

theorem valid7233 : plan7233.Valid := valid_step _ _ _ valid5838 (by decide +kernel)

theorem valid7234 : plan7234.Valid := valid_step _ _ _ valid5840 (by decide +kernel)

theorem valid7235 : plan7235.Valid := valid_step _ _ _ valid5843 (by decide +kernel)

theorem valid7236 : plan7236.Valid := valid_step _ _ _ valid5845 (by decide +kernel)

theorem valid7237 : plan7237.Valid := valid_step _ _ _ valid5846 (by decide +kernel)

theorem valid7238 : plan7238.Valid := valid_step _ _ _ valid5848 (by decide +kernel)

theorem valid7239 : plan7239.Valid := valid_step _ _ _ valid5849 (by decide +kernel)

theorem valid7240 : plan7240.Valid := valid_step _ _ _ valid5850 (by decide +kernel)

theorem valid7241 : plan7241.Valid := valid_step _ _ _ valid5851 (by decide +kernel)

theorem valid7242 : plan7242.Valid := valid_step _ _ _ valid5852 (by decide +kernel)

theorem valid7243 : plan7243.Valid := valid_step _ _ _ valid5853 (by decide +kernel)

theorem valid7244 : plan7244.Valid := valid_step _ _ _ valid5854 (by decide +kernel)

theorem valid7245 : plan7245.Valid := valid_step _ _ _ valid5855 (by decide +kernel)

theorem valid7246 : plan7246.Valid := valid_step _ _ _ valid5856 (by decide +kernel)

theorem valid7247 : plan7247.Valid := valid_step _ _ _ valid5857 (by decide +kernel)

theorem valid7248 : plan7248.Valid := valid_step _ _ _ valid5858 (by decide +kernel)

theorem valid7249 : plan7249.Valid := valid_step _ _ _ valid5866 (by decide +kernel)

theorem valid7250 : plan7250.Valid := valid_step _ _ _ valid5868 (by decide +kernel)

theorem valid7251 : plan7251.Valid := valid_step _ _ _ valid5869 (by decide +kernel)

theorem valid7252 : plan7252.Valid := valid_step _ _ _ valid5871 (by decide +kernel)

theorem valid7253 : plan7253.Valid := valid_step _ _ _ valid5874 (by decide +kernel)

theorem valid7254 : plan7254.Valid := valid_step _ _ _ valid5876 (by decide +kernel)

theorem valid7255 : plan7255.Valid := valid_step _ _ _ valid5877 (by decide +kernel)

theorem valid7256 : plan7256.Valid := valid_step _ _ _ valid5879 (by decide +kernel)

theorem valid7257 : plan7257.Valid := valid_step _ _ _ valid5880 (by decide +kernel)

theorem valid7258 : plan7258.Valid := valid_step _ _ _ valid5881 (by decide +kernel)

theorem valid7259 : plan7259.Valid := valid_step _ _ _ valid5882 (by decide +kernel)

theorem valid7260 : plan7260.Valid := valid_step _ _ _ valid5883 (by decide +kernel)

theorem valid7261 : plan7261.Valid := valid_step _ _ _ valid5884 (by decide +kernel)

theorem valid7262 : plan7262.Valid := valid_step _ _ _ valid5885 (by decide +kernel)

theorem valid7263 : plan7263.Valid := valid_step _ _ _ valid5886 (by decide +kernel)

theorem valid7264 : plan7264.Valid := valid_step _ _ _ valid5887 (by decide +kernel)

theorem valid7265 : plan7265.Valid := valid_step _ _ _ valid5888 (by decide +kernel)

theorem valid7266 : plan7266.Valid := valid_step _ _ _ valid5889 (by decide +kernel)

theorem valid7267 : plan7267.Valid := valid_step _ _ _ valid5890 (by decide +kernel)

theorem valid7268 : plan7268.Valid := valid_step _ _ _ valid5891 (by decide +kernel)

theorem valid7269 : plan7269.Valid := valid_step _ _ _ valid5892 (by decide +kernel)

theorem valid7270 : plan7270.Valid := valid_step _ _ _ valid5893 (by decide +kernel)




















































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















































theorem valid6840 : plan6840.Valid := valid_step _ _ _ valid5682 (by decide +kernel)

theorem valid6841 : plan6841.Valid := valid_step _ _ _ valid5684 (by decide +kernel)

theorem valid6842 : plan6842.Valid := valid_step _ _ _ valid5685 (by decide +kernel)

theorem valid6843 : plan6843.Valid := valid_step _ _ _ valid5693 (by decide +kernel)

theorem valid6844 : plan6844.Valid := valid_step _ _ _ valid5695 (by decide +kernel)

theorem valid6845 : plan6845.Valid := valid_step _ _ _ valid5696 (by decide +kernel)






































































































































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
theorem t6_374choices : plan6523.choices=[1,5,5,3,3,7].map (options 6 3) := by rfl


theorem t6_374part0 : t6_374jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_374frontier : t6_374root.frontier 0=t6_374jobs := by rfl
theorem t6_374all : t6_374jobs.all (Job.check tree)=true := by
  simp only [t6_374jobs,List.all_append,List.all_nil,t6_374part0,Bool.and_self]
theorem t6_374checked : Checked tree [1,5,5,3,3,7] := by
  refine ⟨plan6523,valid6523,t6_374choices,?_⟩
  exact check_of_frontier tree 0 t6_374root t6_374jobs t6_374frontier t6_374all
theorem t6_375choices : plan6840.choices=[1,5,5,3,6,7].map (options 6 4) := by rfl


theorem t6_375part0 : t6_375jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_375frontier : t6_375root.frontier 0=t6_375jobs := by rfl
theorem t6_375all : t6_375jobs.all (Job.check tree)=true := by
  simp only [t6_375jobs,List.all_append,List.all_nil,t6_375part0,Bool.and_self]
theorem t6_375checked : Checked tree [1,5,5,3,6,7] := by
  refine ⟨plan6840,valid6840,t6_375choices,?_⟩
  exact check_of_frontier tree 0 t6_375root t6_375jobs t6_375frontier t6_375all
theorem t6_376choices : plan6841.choices=[1,5,5,3,7,7].map (options 6 4) := by rfl


theorem t6_376part0 : t6_376jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_376frontier : t6_376root.frontier 0=t6_376jobs := by rfl
theorem t6_376all : t6_376jobs.all (Job.check tree)=true := by
  simp only [t6_376jobs,List.all_append,List.all_nil,t6_376part0,Bool.and_self]
theorem t6_376checked : Checked tree [1,5,5,3,7,7] := by
  refine ⟨plan6841,valid6841,t6_376choices,?_⟩
  exact check_of_frontier tree 0 t6_376root t6_376jobs t6_376frontier t6_376all
theorem t6_377choices : plan6842.choices=[1,5,5,3,10,7].map (options 6 4) := by rfl


theorem t6_377part0 : t6_377jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_377frontier : t6_377root.frontier 0=t6_377jobs := by rfl
theorem t6_377all : t6_377jobs.all (Job.check tree)=true := by
  simp only [t6_377jobs,List.all_append,List.all_nil,t6_377part0,Bool.and_self]
theorem t6_377checked : Checked tree [1,5,5,3,10,7] := by
  refine ⟨plan6842,valid6842,t6_377choices,?_⟩
  exact check_of_frontier tree 0 t6_377root t6_377jobs t6_377frontier t6_377all
theorem t6_378choices : plan7230.choices=[1,5,5,5,7,7].map (options 6 5) := by rfl


theorem t6_378part0 : t6_378jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_378frontier : t6_378root.frontier 0=t6_378jobs := by rfl
theorem t6_378all : t6_378jobs.all (Job.check tree)=true := by
  simp only [t6_378jobs,List.all_append,List.all_nil,t6_378part0,Bool.and_self]
theorem t6_378checked : Checked tree [1,5,5,5,7,7] := by
  refine ⟨plan7230,valid7230,t6_378choices,?_⟩
  exact check_of_frontier tree 0 t6_378root t6_378jobs t6_378frontier t6_378all
theorem t6_379choices : plan7231.choices=[1,5,5,6,6,7].map (options 6 5) := by rfl


theorem t6_379part0 : t6_379jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_379frontier : t6_379root.frontier 0=t6_379jobs := by rfl
theorem t6_379all : t6_379jobs.all (Job.check tree)=true := by
  simp only [t6_379jobs,List.all_append,List.all_nil,t6_379part0,Bool.and_self]
theorem t6_379checked : Checked tree [1,5,5,6,6,7] := by
  refine ⟨plan7231,valid7231,t6_379choices,?_⟩
  exact check_of_frontier tree 0 t6_379root t6_379jobs t6_379frontier t6_379all
theorem t6_380choices : plan7232.choices=[1,5,5,6,7,7].map (options 6 5) := by rfl


theorem t6_380part0 : t6_380jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_380frontier : t6_380root.frontier 0=t6_380jobs := by rfl
theorem t6_380all : t6_380jobs.all (Job.check tree)=true := by
  simp only [t6_380jobs,List.all_append,List.all_nil,t6_380part0,Bool.and_self]
theorem t6_380checked : Checked tree [1,5,5,6,7,7] := by
  refine ⟨plan7232,valid7232,t6_380choices,?_⟩
  exact check_of_frontier tree 0 t6_380root t6_380jobs t6_380frontier t6_380all
theorem t6_381choices : plan7233.choices=[1,5,5,6,10,7].map (options 6 5) := by rfl


theorem t6_381part0 : t6_381jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_381frontier : t6_381root.frontier 0=t6_381jobs := by rfl
theorem t6_381all : t6_381jobs.all (Job.check tree)=true := by
  simp only [t6_381jobs,List.all_append,List.all_nil,t6_381part0,Bool.and_self]
theorem t6_381checked : Checked tree [1,5,5,6,10,7] := by
  refine ⟨plan7233,valid7233,t6_381choices,?_⟩
  exact check_of_frontier tree 0 t6_381root t6_381jobs t6_381frontier t6_381all
theorem t6_382choices : plan7234.choices=[1,5,5,7,7,7].map (options 6 5) := by rfl


theorem t6_382part0 : t6_382jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_382frontier : t6_382root.frontier 0=t6_382jobs := by rfl
theorem t6_382all : t6_382jobs.all (Job.check tree)=true := by
  simp only [t6_382jobs,List.all_append,List.all_nil,t6_382part0,Bool.and_self]
theorem t6_382checked : Checked tree [1,5,5,7,7,7] := by
  refine ⟨plan7234,valid7234,t6_382choices,?_⟩
  exact check_of_frontier tree 0 t6_382root t6_382jobs t6_382frontier t6_382all
theorem t6_383choices : plan7235.choices=[1,5,5,9,7,7].map (options 6 5) := by rfl


theorem t6_383part0 : t6_383jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_383frontier : t6_383root.frontier 0=t6_383jobs := by rfl
theorem t6_383all : t6_383jobs.all (Job.check tree)=true := by
  simp only [t6_383jobs,List.all_append,List.all_nil,t6_383part0,Bool.and_self]
theorem t6_383checked : Checked tree [1,5,5,9,7,7] := by
  refine ⟨plan7235,valid7235,t6_383choices,?_⟩
  exact check_of_frontier tree 0 t6_383root t6_383jobs t6_383frontier t6_383all
theorem t6_384choices : plan7236.choices=[1,5,5,10,7,7].map (options 6 5) := by rfl


theorem t6_384part0 : t6_384jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_384frontier : t6_384root.frontier 0=t6_384jobs := by rfl
theorem t6_384all : t6_384jobs.all (Job.check tree)=true := by
  simp only [t6_384jobs,List.all_append,List.all_nil,t6_384part0,Bool.and_self]
theorem t6_384checked : Checked tree [1,5,5,10,7,7] := by
  refine ⟨plan7236,valid7236,t6_384choices,?_⟩
  exact check_of_frontier tree 0 t6_384root t6_384jobs t6_384frontier t6_384all
theorem t6_385choices : plan7237.choices=[1,5,5,10,10,7].map (options 6 5) := by rfl


theorem t6_385part0 : t6_385jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_385frontier : t6_385root.frontier 0=t6_385jobs := by rfl
theorem t6_385all : t6_385jobs.all (Job.check tree)=true := by
  simp only [t6_385jobs,List.all_append,List.all_nil,t6_385part0,Bool.and_self]
theorem t6_385checked : Checked tree [1,5,5,10,10,7] := by
  refine ⟨plan7237,valid7237,t6_385choices,?_⟩
  exact check_of_frontier tree 0 t6_385root t6_385jobs t6_385frontier t6_385all
theorem t6_386choices : plan7238.choices=[1,5,6,6,6,6].map (options 6 5) := by rfl


theorem t6_386part0 : t6_386jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_386frontier : t6_386root.frontier 0=t6_386jobs := by rfl
theorem t6_386all : t6_386jobs.all (Job.check tree)=true := by
  simp only [t6_386jobs,List.all_append,List.all_nil,t6_386part0,Bool.and_self]
theorem t6_386checked : Checked tree [1,5,6,6,6,6] := by
  refine ⟨plan7238,valid7238,t6_386choices,?_⟩
  exact check_of_frontier tree 0 t6_386root t6_386jobs t6_386frontier t6_386all
theorem t6_387choices : plan7239.choices=[1,5,6,6,6,7].map (options 6 5) := by rfl


theorem t6_387part0 : t6_387jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_387frontier : t6_387root.frontier 0=t6_387jobs := by rfl
theorem t6_387all : t6_387jobs.all (Job.check tree)=true := by
  simp only [t6_387jobs,List.all_append,List.all_nil,t6_387part0,Bool.and_self]
theorem t6_387checked : Checked tree [1,5,6,6,6,7] := by
  refine ⟨plan7239,valid7239,t6_387choices,?_⟩
  exact check_of_frontier tree 0 t6_387root t6_387jobs t6_387frontier t6_387all
theorem t6_388choices : plan7240.choices=[1,5,6,6,6,10].map (options 6 5) := by rfl


theorem t6_388part0 : t6_388jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_388frontier : t6_388root.frontier 0=t6_388jobs := by rfl
theorem t6_388all : t6_388jobs.all (Job.check tree)=true := by
  simp only [t6_388jobs,List.all_append,List.all_nil,t6_388part0,Bool.and_self]
theorem t6_388checked : Checked tree [1,5,6,6,6,10] := by
  refine ⟨plan7240,valid7240,t6_388choices,?_⟩
  exact check_of_frontier tree 0 t6_388root t6_388jobs t6_388frontier t6_388all
theorem t6_389choices : plan7241.choices=[1,5,6,6,7,7].map (options 6 5) := by rfl


theorem t6_389part0 : t6_389jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_389frontier : t6_389root.frontier 0=t6_389jobs := by rfl
theorem t6_389all : t6_389jobs.all (Job.check tree)=true := by
  simp only [t6_389jobs,List.all_append,List.all_nil,t6_389part0,Bool.and_self]
theorem t6_389checked : Checked tree [1,5,6,6,7,7] := by
  refine ⟨plan7241,valid7241,t6_389choices,?_⟩
  exact check_of_frontier tree 0 t6_389root t6_389jobs t6_389frontier t6_389all
theorem t6_390choices : plan7242.choices=[1,5,6,6,10,7].map (options 6 5) := by rfl


theorem t6_390part0 : t6_390jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_390frontier : t6_390root.frontier 0=t6_390jobs := by rfl
theorem t6_390all : t6_390jobs.all (Job.check tree)=true := by
  simp only [t6_390jobs,List.all_append,List.all_nil,t6_390part0,Bool.and_self]
theorem t6_390checked : Checked tree [1,5,6,6,10,7] := by
  refine ⟨plan7242,valid7242,t6_390choices,?_⟩
  exact check_of_frontier tree 0 t6_390root t6_390jobs t6_390frontier t6_390all
theorem t6_391choices : plan7243.choices=[1,5,6,6,10,10].map (options 6 5) := by rfl


theorem t6_391part0 : t6_391jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_391frontier : t6_391root.frontier 0=t6_391jobs := by rfl
theorem t6_391all : t6_391jobs.all (Job.check tree)=true := by
  simp only [t6_391jobs,List.all_append,List.all_nil,t6_391part0,Bool.and_self]
theorem t6_391checked : Checked tree [1,5,6,6,10,10] := by
  refine ⟨plan7243,valid7243,t6_391choices,?_⟩
  exact check_of_frontier tree 0 t6_391root t6_391jobs t6_391frontier t6_391all
theorem t6_392choices : plan7244.choices=[1,5,6,7,7,7].map (options 6 5) := by rfl


theorem t6_392part0 : t6_392jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_392frontier : t6_392root.frontier 0=t6_392jobs := by rfl
theorem t6_392all : t6_392jobs.all (Job.check tree)=true := by
  simp only [t6_392jobs,List.all_append,List.all_nil,t6_392part0,Bool.and_self]
theorem t6_392checked : Checked tree [1,5,6,7,7,7] := by
  refine ⟨plan7244,valid7244,t6_392choices,?_⟩
  exact check_of_frontier tree 0 t6_392root t6_392jobs t6_392frontier t6_392all
theorem t6_393choices : plan7245.choices=[1,5,6,10,7,7].map (options 6 5) := by rfl


theorem t6_393part0 : t6_393jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_393frontier : t6_393root.frontier 0=t6_393jobs := by rfl
theorem t6_393all : t6_393jobs.all (Job.check tree)=true := by
  simp only [t6_393jobs,List.all_append,List.all_nil,t6_393part0,Bool.and_self]
theorem t6_393checked : Checked tree [1,5,6,10,7,7] := by
  refine ⟨plan7245,valid7245,t6_393choices,?_⟩
  exact check_of_frontier tree 0 t6_393root t6_393jobs t6_393frontier t6_393all
theorem t6_394choices : plan7246.choices=[1,5,6,10,10,7].map (options 6 5) := by rfl


theorem t6_394part0 : t6_394jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_394frontier : t6_394root.frontier 0=t6_394jobs := by rfl
theorem t6_394all : t6_394jobs.all (Job.check tree)=true := by
  simp only [t6_394jobs,List.all_append,List.all_nil,t6_394part0,Bool.and_self]
theorem t6_394checked : Checked tree [1,5,6,10,10,7] := by
  refine ⟨plan7246,valid7246,t6_394choices,?_⟩
  exact check_of_frontier tree 0 t6_394root t6_394jobs t6_394frontier t6_394all
theorem t6_395choices : plan7247.choices=[1,5,6,10,10,10].map (options 6 5) := by rfl


theorem t6_395part0 : t6_395jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_395frontier : t6_395root.frontier 0=t6_395jobs := by rfl
theorem t6_395all : t6_395jobs.all (Job.check tree)=true := by
  simp only [t6_395jobs,List.all_append,List.all_nil,t6_395part0,Bool.and_self]
theorem t6_395checked : Checked tree [1,5,6,10,10,10] := by
  refine ⟨plan7247,valid7247,t6_395choices,?_⟩
  exact check_of_frontier tree 0 t6_395root t6_395jobs t6_395frontier t6_395all
theorem t6_396choices : plan7248.choices=[1,5,7,7,7,7].map (options 6 5) := by rfl


theorem t6_396part0 : t6_396jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_396frontier : t6_396root.frontier 0=t6_396jobs := by rfl
theorem t6_396all : t6_396jobs.all (Job.check tree)=true := by
  simp only [t6_396jobs,List.all_append,List.all_nil,t6_396part0,Bool.and_self]
theorem t6_396checked : Checked tree [1,5,7,7,7,7] := by
  refine ⟨plan7248,valid7248,t6_396choices,?_⟩
  exact check_of_frontier tree 0 t6_396root t6_396jobs t6_396frontier t6_396all
theorem t6_397choices : plan6524.choices=[1,5,9,3,3,7].map (options 6 3) := by rfl


theorem t6_397part0 : t6_397jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_397frontier : t6_397root.frontier 0=t6_397jobs := by rfl
theorem t6_397all : t6_397jobs.all (Job.check tree)=true := by
  simp only [t6_397jobs,List.all_append,List.all_nil,t6_397part0,Bool.and_self]
theorem t6_397checked : Checked tree [1,5,9,3,3,7] := by
  refine ⟨plan6524,valid6524,t6_397choices,?_⟩
  exact check_of_frontier tree 0 t6_397root t6_397jobs t6_397frontier t6_397all
theorem t6_398choices : plan6843.choices=[1,5,9,3,6,7].map (options 6 4) := by rfl


theorem t6_398part0 : t6_398jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_398frontier : t6_398root.frontier 0=t6_398jobs := by rfl
theorem t6_398all : t6_398jobs.all (Job.check tree)=true := by
  simp only [t6_398jobs,List.all_append,List.all_nil,t6_398part0,Bool.and_self]
theorem t6_398checked : Checked tree [1,5,9,3,6,7] := by
  refine ⟨plan6843,valid6843,t6_398choices,?_⟩
  exact check_of_frontier tree 0 t6_398root t6_398jobs t6_398frontier t6_398all
theorem t6_399choices : plan6844.choices=[1,5,9,3,7,7].map (options 6 4) := by rfl


theorem t6_399part0 : t6_399jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_399part1 : t6_399jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_399frontier : t6_399root.frontier 1=t6_399jobs := by rfl
theorem t6_399all : t6_399jobs.all (Job.check tree)=true := by
  simp only [t6_399jobs,List.all_append,List.all_nil,t6_399part0,t6_399part1,Bool.and_self]
theorem t6_399checked : Checked tree [1,5,9,3,7,7] := by
  refine ⟨plan6844,valid6844,t6_399choices,?_⟩
  exact check_of_frontier tree 1 t6_399root t6_399jobs t6_399frontier t6_399all
theorem t6_400choices : plan6845.choices=[1,5,9,3,10,7].map (options 6 4) := by rfl


theorem t6_400part0 : t6_400jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_400frontier : t6_400root.frontier 0=t6_400jobs := by rfl
theorem t6_400all : t6_400jobs.all (Job.check tree)=true := by
  simp only [t6_400jobs,List.all_append,List.all_nil,t6_400part0,Bool.and_self]
theorem t6_400checked : Checked tree [1,5,9,3,10,7] := by
  refine ⟨plan6845,valid6845,t6_400choices,?_⟩
  exact check_of_frontier tree 0 t6_400root t6_400jobs t6_400frontier t6_400all
theorem t6_401choices : plan7249.choices=[1,5,9,6,6,7].map (options 6 5) := by rfl


theorem t6_401part0 : t6_401jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_401frontier : t6_401root.frontier 0=t6_401jobs := by rfl
theorem t6_401all : t6_401jobs.all (Job.check tree)=true := by
  simp only [t6_401jobs,List.all_append,List.all_nil,t6_401part0,Bool.and_self]
theorem t6_401checked : Checked tree [1,5,9,6,6,7] := by
  refine ⟨plan7249,valid7249,t6_401choices,?_⟩
  exact check_of_frontier tree 0 t6_401root t6_401jobs t6_401frontier t6_401all
theorem t6_402choices : plan7250.choices=[1,5,9,6,7,7].map (options 6 5) := by rfl


theorem t6_402part0 : t6_402jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_402frontier : t6_402root.frontier 0=t6_402jobs := by rfl
theorem t6_402all : t6_402jobs.all (Job.check tree)=true := by
  simp only [t6_402jobs,List.all_append,List.all_nil,t6_402part0,Bool.and_self]
theorem t6_402checked : Checked tree [1,5,9,6,7,7] := by
  refine ⟨plan7250,valid7250,t6_402choices,?_⟩
  exact check_of_frontier tree 0 t6_402root t6_402jobs t6_402frontier t6_402all
theorem t6_403choices : plan7251.choices=[1,5,9,6,10,7].map (options 6 5) := by rfl


theorem t6_403part0 : t6_403jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_403frontier : t6_403root.frontier 0=t6_403jobs := by rfl
theorem t6_403all : t6_403jobs.all (Job.check tree)=true := by
  simp only [t6_403jobs,List.all_append,List.all_nil,t6_403part0,Bool.and_self]
theorem t6_403checked : Checked tree [1,5,9,6,10,7] := by
  refine ⟨plan7251,valid7251,t6_403choices,?_⟩
  exact check_of_frontier tree 0 t6_403root t6_403jobs t6_403frontier t6_403all
theorem t6_404choices : plan7252.choices=[1,5,9,7,7,7].map (options 6 5) := by rfl


theorem t6_404part0 : t6_404jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_404frontier : t6_404root.frontier 0=t6_404jobs := by rfl
theorem t6_404all : t6_404jobs.all (Job.check tree)=true := by
  simp only [t6_404jobs,List.all_append,List.all_nil,t6_404part0,Bool.and_self]
theorem t6_404checked : Checked tree [1,5,9,7,7,7] := by
  refine ⟨plan7252,valid7252,t6_404choices,?_⟩
  exact check_of_frontier tree 0 t6_404root t6_404jobs t6_404frontier t6_404all
theorem t6_405choices : plan7253.choices=[1,5,9,9,7,7].map (options 6 5) := by rfl


theorem t6_405part0 : t6_405jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_405frontier : t6_405root.frontier 0=t6_405jobs := by rfl
theorem t6_405all : t6_405jobs.all (Job.check tree)=true := by
  simp only [t6_405jobs,List.all_append,List.all_nil,t6_405part0,Bool.and_self]
theorem t6_405checked : Checked tree [1,5,9,9,7,7] := by
  refine ⟨plan7253,valid7253,t6_405choices,?_⟩
  exact check_of_frontier tree 0 t6_405root t6_405jobs t6_405frontier t6_405all
theorem t6_406choices : plan7254.choices=[1,5,9,10,7,7].map (options 6 5) := by rfl


theorem t6_406part0 : t6_406jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_406frontier : t6_406root.frontier 0=t6_406jobs := by rfl
theorem t6_406all : t6_406jobs.all (Job.check tree)=true := by
  simp only [t6_406jobs,List.all_append,List.all_nil,t6_406part0,Bool.and_self]
theorem t6_406checked : Checked tree [1,5,9,10,7,7] := by
  refine ⟨plan7254,valid7254,t6_406choices,?_⟩
  exact check_of_frontier tree 0 t6_406root t6_406jobs t6_406frontier t6_406all
theorem t6_407choices : plan7255.choices=[1,5,9,10,10,7].map (options 6 5) := by rfl


theorem t6_407part0 : t6_407jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_407frontier : t6_407root.frontier 0=t6_407jobs := by rfl
theorem t6_407all : t6_407jobs.all (Job.check tree)=true := by
  simp only [t6_407jobs,List.all_append,List.all_nil,t6_407part0,Bool.and_self]
theorem t6_407checked : Checked tree [1,5,9,10,10,7] := by
  refine ⟨plan7255,valid7255,t6_407choices,?_⟩
  exact check_of_frontier tree 0 t6_407root t6_407jobs t6_407frontier t6_407all
theorem t6_408choices : plan7256.choices=[1,5,10,7,7,7].map (options 6 5) := by rfl


theorem t6_408part0 : t6_408jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_408frontier : t6_408root.frontier 0=t6_408jobs := by rfl
theorem t6_408all : t6_408jobs.all (Job.check tree)=true := by
  simp only [t6_408jobs,List.all_append,List.all_nil,t6_408part0,Bool.and_self]
theorem t6_408checked : Checked tree [1,5,10,7,7,7] := by
  refine ⟨plan7256,valid7256,t6_408choices,?_⟩
  exact check_of_frontier tree 0 t6_408root t6_408jobs t6_408frontier t6_408all
theorem t6_409choices : plan7257.choices=[1,5,10,10,7,7].map (options 6 5) := by rfl


theorem t6_409part0 : t6_409jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_409frontier : t6_409root.frontier 0=t6_409jobs := by rfl
theorem t6_409all : t6_409jobs.all (Job.check tree)=true := by
  simp only [t6_409jobs,List.all_append,List.all_nil,t6_409part0,Bool.and_self]
theorem t6_409checked : Checked tree [1,5,10,10,7,7] := by
  refine ⟨plan7257,valid7257,t6_409choices,?_⟩
  exact check_of_frontier tree 0 t6_409root t6_409jobs t6_409frontier t6_409all
theorem t6_410choices : plan7258.choices=[1,5,10,10,10,7].map (options 6 5) := by rfl


theorem t6_410part0 : t6_410jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_410frontier : t6_410root.frontier 0=t6_410jobs := by rfl
theorem t6_410all : t6_410jobs.all (Job.check tree)=true := by
  simp only [t6_410jobs,List.all_append,List.all_nil,t6_410part0,Bool.and_self]
theorem t6_410checked : Checked tree [1,5,10,10,10,7] := by
  refine ⟨plan7258,valid7258,t6_410choices,?_⟩
  exact check_of_frontier tree 0 t6_410root t6_410jobs t6_410frontier t6_410all
theorem t6_411choices : plan7259.choices=[1,5,10,10,10,10].map (options 6 5) := by rfl


theorem t6_411part0 : t6_411jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_411frontier : t6_411root.frontier 0=t6_411jobs := by rfl
theorem t6_411all : t6_411jobs.all (Job.check tree)=true := by
  simp only [t6_411jobs,List.all_append,List.all_nil,t6_411part0,Bool.and_self]
theorem t6_411checked : Checked tree [1,5,10,10,10,10] := by
  refine ⟨plan7259,valid7259,t6_411choices,?_⟩
  exact check_of_frontier tree 0 t6_411root t6_411jobs t6_411frontier t6_411all
theorem t6_412choices : plan7260.choices=[1,6,6,6,6,6].map (options 6 5) := by rfl


theorem t6_412part0 : t6_412jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_412frontier : t6_412root.frontier 0=t6_412jobs := by rfl
theorem t6_412all : t6_412jobs.all (Job.check tree)=true := by
  simp only [t6_412jobs,List.all_append,List.all_nil,t6_412part0,Bool.and_self]
theorem t6_412checked : Checked tree [1,6,6,6,6,6] := by
  refine ⟨plan7260,valid7260,t6_412choices,?_⟩
  exact check_of_frontier tree 0 t6_412root t6_412jobs t6_412frontier t6_412all
theorem t6_413choices : plan7261.choices=[1,6,6,6,6,7].map (options 6 5) := by rfl


theorem t6_413part0 : t6_413jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_413frontier : t6_413root.frontier 0=t6_413jobs := by rfl
theorem t6_413all : t6_413jobs.all (Job.check tree)=true := by
  simp only [t6_413jobs,List.all_append,List.all_nil,t6_413part0,Bool.and_self]
theorem t6_413checked : Checked tree [1,6,6,6,6,7] := by
  refine ⟨plan7261,valid7261,t6_413choices,?_⟩
  exact check_of_frontier tree 0 t6_413root t6_413jobs t6_413frontier t6_413all
theorem t6_414choices : plan7262.choices=[1,6,6,6,6,10].map (options 6 5) := by rfl


theorem t6_414part0 : t6_414jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_414frontier : t6_414root.frontier 0=t6_414jobs := by rfl
theorem t6_414all : t6_414jobs.all (Job.check tree)=true := by
  simp only [t6_414jobs,List.all_append,List.all_nil,t6_414part0,Bool.and_self]
theorem t6_414checked : Checked tree [1,6,6,6,6,10] := by
  refine ⟨plan7262,valid7262,t6_414choices,?_⟩
  exact check_of_frontier tree 0 t6_414root t6_414jobs t6_414frontier t6_414all
theorem t6_415choices : plan7263.choices=[1,6,6,6,7,7].map (options 6 5) := by rfl


theorem t6_415part0 : t6_415jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_415frontier : t6_415root.frontier 0=t6_415jobs := by rfl
theorem t6_415all : t6_415jobs.all (Job.check tree)=true := by
  simp only [t6_415jobs,List.all_append,List.all_nil,t6_415part0,Bool.and_self]
theorem t6_415checked : Checked tree [1,6,6,6,7,7] := by
  refine ⟨plan7263,valid7263,t6_415choices,?_⟩
  exact check_of_frontier tree 0 t6_415root t6_415jobs t6_415frontier t6_415all
theorem t6_416choices : plan7264.choices=[1,6,6,6,10,7].map (options 6 5) := by rfl


theorem t6_416part0 : t6_416jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_416frontier : t6_416root.frontier 0=t6_416jobs := by rfl
theorem t6_416all : t6_416jobs.all (Job.check tree)=true := by
  simp only [t6_416jobs,List.all_append,List.all_nil,t6_416part0,Bool.and_self]
theorem t6_416checked : Checked tree [1,6,6,6,10,7] := by
  refine ⟨plan7264,valid7264,t6_416choices,?_⟩
  exact check_of_frontier tree 0 t6_416root t6_416jobs t6_416frontier t6_416all
theorem t6_417choices : plan7265.choices=[1,6,6,6,10,10].map (options 6 5) := by rfl


theorem t6_417part0 : t6_417jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_417frontier : t6_417root.frontier 0=t6_417jobs := by rfl
theorem t6_417all : t6_417jobs.all (Job.check tree)=true := by
  simp only [t6_417jobs,List.all_append,List.all_nil,t6_417part0,Bool.and_self]
theorem t6_417checked : Checked tree [1,6,6,6,10,10] := by
  refine ⟨plan7265,valid7265,t6_417choices,?_⟩
  exact check_of_frontier tree 0 t6_417root t6_417jobs t6_417frontier t6_417all
theorem t6_418choices : plan7266.choices=[1,6,6,7,7,7].map (options 6 5) := by rfl


theorem t6_418part0 : t6_418jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_418frontier : t6_418root.frontier 0=t6_418jobs := by rfl
theorem t6_418all : t6_418jobs.all (Job.check tree)=true := by
  simp only [t6_418jobs,List.all_append,List.all_nil,t6_418part0,Bool.and_self]
theorem t6_418checked : Checked tree [1,6,6,7,7,7] := by
  refine ⟨plan7266,valid7266,t6_418choices,?_⟩
  exact check_of_frontier tree 0 t6_418root t6_418jobs t6_418frontier t6_418all
theorem t6_419choices : plan7267.choices=[1,6,6,10,7,7].map (options 6 5) := by rfl


theorem t6_419part0 : t6_419jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_419frontier : t6_419root.frontier 0=t6_419jobs := by rfl
theorem t6_419all : t6_419jobs.all (Job.check tree)=true := by
  simp only [t6_419jobs,List.all_append,List.all_nil,t6_419part0,Bool.and_self]
theorem t6_419checked : Checked tree [1,6,6,10,7,7] := by
  refine ⟨plan7267,valid7267,t6_419choices,?_⟩
  exact check_of_frontier tree 0 t6_419root t6_419jobs t6_419frontier t6_419all
theorem t6_420choices : plan7268.choices=[1,6,6,10,10,7].map (options 6 5) := by rfl


theorem t6_420part0 : t6_420jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_420frontier : t6_420root.frontier 0=t6_420jobs := by rfl
theorem t6_420all : t6_420jobs.all (Job.check tree)=true := by
  simp only [t6_420jobs,List.all_append,List.all_nil,t6_420part0,Bool.and_self]
theorem t6_420checked : Checked tree [1,6,6,10,10,7] := by
  refine ⟨plan7268,valid7268,t6_420choices,?_⟩
  exact check_of_frontier tree 0 t6_420root t6_420jobs t6_420frontier t6_420all
theorem t6_421choices : plan7269.choices=[1,6,6,10,10,10].map (options 6 5) := by rfl


theorem t6_421part0 : t6_421jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_421frontier : t6_421root.frontier 0=t6_421jobs := by rfl
theorem t6_421all : t6_421jobs.all (Job.check tree)=true := by
  simp only [t6_421jobs,List.all_append,List.all_nil,t6_421part0,Bool.and_self]
theorem t6_421checked : Checked tree [1,6,6,10,10,10] := by
  refine ⟨plan7269,valid7269,t6_421choices,?_⟩
  exact check_of_frontier tree 0 t6_421root t6_421jobs t6_421frontier t6_421all
theorem t6_422choices : plan7270.choices=[1,6,7,7,7,7].map (options 6 5) := by rfl


theorem t6_422part0 : t6_422jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_422frontier : t6_422root.frontier 0=t6_422jobs := by rfl
theorem t6_422all : t6_422jobs.all (Job.check tree)=true := by
  simp only [t6_422jobs,List.all_append,List.all_nil,t6_422part0,Bool.and_self]
theorem t6_422checked : Checked tree [1,6,7,7,7,7] := by
  refine ⟨plan7270,valid7270,t6_422choices,?_⟩
  exact check_of_frontier tree 0 t6_422root t6_422jobs t6_422frontier t6_422all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks058 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_387checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_388checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_389checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_390checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_391checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_392checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_393checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_394checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_395checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_375checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_396checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_397checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_398checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_399checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_400checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_401checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_402checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_403checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_404checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_405checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_376checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_406checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_407checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_408checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_409checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_410checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_411checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_412checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_413checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_414checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_415checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_377checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_416checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_417checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_418checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_419checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_420checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_421checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_422checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_378checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_379checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_380checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_381checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_382checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_383checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_384checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_385checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_374checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_386checked⟩
