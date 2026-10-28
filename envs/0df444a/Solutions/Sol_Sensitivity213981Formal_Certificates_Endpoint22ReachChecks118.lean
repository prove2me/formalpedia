-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks118
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:43:03.82134+00:00
-- url     : https://prove2.me/submissions/548f6298-6d8a-48a6-8335-27698d9d349b

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks118
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks118
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
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

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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

























































































































theorem valid541 : plan541.Valid := valid_step _ _ _ valid118 (by decide +kernel)









theorem valid546 : plan546.Valid := valid_step _ _ _ valid123 (by decide +kernel)

theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid548 : plan548.Valid := valid_step _ _ _ valid125 (by decide +kernel)





















theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)

theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)












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

theorem valid1534 : plan1534.Valid := valid_step _ _ _ valid561 (by decide +kernel)

theorem valid1535 : plan1535.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1536 : plan1536.Valid := valid_step _ _ _ valid563 (by decide +kernel)
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

theorem valid1537 : plan1537.Valid := valid_step _ _ _ valid564 (by decide +kernel)































































theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)























































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

theorem valid3265 : plan3265.Valid := valid_step _ _ _ valid1516 (by decide +kernel)

theorem valid3266 : plan3266.Valid := valid_step _ _ _ valid1517 (by decide +kernel)

theorem valid3267 : plan3267.Valid := valid_step _ _ _ valid1518 (by decide +kernel)













































































theorem valid3306 : plan3306.Valid := valid_step _ _ _ valid1532 (by decide +kernel)

theorem valid3307 : plan3307.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3308 : plan3308.Valid := valid_step _ _ _ valid1534 (by decide +kernel)

theorem valid3309 : plan3309.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3310 : plan3310.Valid := valid_step _ _ _ valid1536 (by decide +kernel)

theorem valid3311 : plan3311.Valid := valid_step _ _ _ valid1537 (by decide +kernel)

































































































theorem valid3360 : plan3360.Valid := valid_step _ _ _ valid1569 (by decide +kernel)
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





















































































































































theorem valid6315 : plan6315.Valid := valid_step _ _ _ valid5356 (by decide +kernel)










































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

theorem valid3361 : plan3361.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3362 : plan3362.Valid := valid_step _ _ _ valid1571 (by decide +kernel)




























































































































































































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

theorem valid5482 : plan5482.Valid := valid_step _ _ _ valid3308 (by decide +kernel)

theorem valid5483 : plan5483.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5484 : plan5484.Valid := valid_step _ _ _ valid3310 (by decide +kernel)

theorem valid5485 : plan5485.Valid := valid_step _ _ _ valid3311 (by decide +kernel)






































































































































































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











































































































theorem valid5622 : plan5622.Valid := valid_step _ _ _ valid3360 (by decide +kernel)

theorem valid5623 : plan5623.Valid := valid_step _ _ _ valid3361 (by decide +kernel)

theorem valid5624 : plan5624.Valid := valid_step _ _ _ valid3362 (by decide +kernel)
















































































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











theorem valid6630 : plan6630.Valid := valid_step _ _ _ valid5480 (by decide +kernel)

theorem valid6631 : plan6631.Valid := valid_step _ _ _ valid5481 (by decide +kernel)

theorem valid6632 : plan6632.Valid := valid_step _ _ _ valid5482 (by decide +kernel)

theorem valid6633 : plan6633.Valid := valid_step _ _ _ valid5483 (by decide +kernel)

theorem valid6634 : plan6634.Valid := valid_step _ _ _ valid5484 (by decide +kernel)

theorem valid6635 : plan6635.Valid := valid_step _ _ _ valid5485 (by decide +kernel)










































































































































































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



theorem valid5762 : plan5762.Valid := valid_step _ _ _ valid3499 (by decide +kernel)

theorem valid5763 : plan5763.Valid := valid_step _ _ _ valid3502 (by decide +kernel)

theorem valid5764 : plan5764.Valid := valid_step _ _ _ valid3504 (by decide +kernel)

theorem valid5765 : plan5765.Valid := valid_step _ _ _ valid3505 (by decide +kernel)

theorem valid5766 : plan5766.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5767 : plan5767.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5768 : plan5768.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5769 : plan5769.Valid := valid_step _ _ _ valid3510 (by decide +kernel)














































































































































































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





















































































































































theorem valid6411 : plan6411.Valid := valid_step _ _ _ valid5393 (by decide +kernel)

theorem valid6412 : plan6412.Valid := valid_step _ _ _ valid5394 (by decide +kernel)

theorem valid6413 : plan6413.Valid := valid_step _ _ _ valid5395 (by decide +kernel)






































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































































































































theorem valid7456 : plan7456.Valid := valid_step _ _ _ valid5762 (by decide +kernel)

theorem valid7457 : plan7457.Valid := valid_step _ _ _ valid5763 (by decide +kernel)

theorem valid7458 : plan7458.Valid := valid_step _ _ _ valid5764 (by decide +kernel)

theorem valid7459 : plan7459.Valid := valid_step _ _ _ valid5765 (by decide +kernel)

theorem valid7460 : plan7460.Valid := valid_step _ _ _ valid5766 (by decide +kernel)

theorem valid7461 : plan7461.Valid := valid_step _ _ _ valid5767 (by decide +kernel)

theorem valid7462 : plan7462.Valid := valid_step _ _ _ valid5768 (by decide +kernel)

theorem valid7463 : plan7463.Valid := valid_step _ _ _ valid5769 (by decide +kernel)


















































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



theorem valid7010 : plan7010.Valid := valid_step _ _ _ valid5622 (by decide +kernel)

theorem valid7011 : plan7011.Valid := valid_step _ _ _ valid5623 (by decide +kernel)

theorem valid7012 : plan7012.Valid := valid_step _ _ _ valid5624 (by decide +kernel)
























































































































































































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
theorem t6_952choices : plan7456.choices=[4,2,9,7,7,7].map (options 6 5) := by rfl


theorem t6_952part0 : t6_952jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_952frontier : t6_952root.frontier 0=t6_952jobs := by rfl
theorem t6_952all : t6_952jobs.all (Job.check tree)=true := by
  simp only [t6_952jobs,List.all_append,List.all_nil,t6_952part0,Bool.and_self]
theorem t6_952checked : Checked tree [4,2,9,7,7,7] := by
  refine ⟨plan7456,valid7456,t6_952choices,?_⟩
  exact check_of_frontier tree 0 t6_952root t6_952jobs t6_952frontier t6_952all
theorem t6_953choices : plan7457.choices=[4,2,9,9,7,7].map (options 6 5) := by rfl


theorem t6_953part0 : t6_953jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_953frontier : t6_953root.frontier 0=t6_953jobs := by rfl
theorem t6_953all : t6_953jobs.all (Job.check tree)=true := by
  simp only [t6_953jobs,List.all_append,List.all_nil,t6_953part0,Bool.and_self]
theorem t6_953checked : Checked tree [4,2,9,9,7,7] := by
  refine ⟨plan7457,valid7457,t6_953choices,?_⟩
  exact check_of_frontier tree 0 t6_953root t6_953jobs t6_953frontier t6_953all
theorem t6_954choices : plan7458.choices=[4,2,9,10,7,7].map (options 6 5) := by rfl


theorem t6_954part0 : t6_954jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_954frontier : t6_954root.frontier 0=t6_954jobs := by rfl
theorem t6_954all : t6_954jobs.all (Job.check tree)=true := by
  simp only [t6_954jobs,List.all_append,List.all_nil,t6_954part0,Bool.and_self]
theorem t6_954checked : Checked tree [4,2,9,10,7,7] := by
  refine ⟨plan7458,valid7458,t6_954choices,?_⟩
  exact check_of_frontier tree 0 t6_954root t6_954jobs t6_954frontier t6_954all
theorem t6_955choices : plan7459.choices=[4,2,9,10,10,7].map (options 6 5) := by rfl


theorem t6_955part0 : t6_955jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_955frontier : t6_955root.frontier 0=t6_955jobs := by rfl
theorem t6_955all : t6_955jobs.all (Job.check tree)=true := by
  simp only [t6_955jobs,List.all_append,List.all_nil,t6_955part0,Bool.and_self]
theorem t6_955checked : Checked tree [4,2,9,10,10,7] := by
  refine ⟨plan7459,valid7459,t6_955choices,?_⟩
  exact check_of_frontier tree 0 t6_955root t6_955jobs t6_955frontier t6_955all
theorem t6_956choices : plan7460.choices=[4,2,10,7,7,7].map (options 6 5) := by rfl


theorem t6_956part0 : t6_956jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_956frontier : t6_956root.frontier 0=t6_956jobs := by rfl
theorem t6_956all : t6_956jobs.all (Job.check tree)=true := by
  simp only [t6_956jobs,List.all_append,List.all_nil,t6_956part0,Bool.and_self]
theorem t6_956checked : Checked tree [4,2,10,7,7,7] := by
  refine ⟨plan7460,valid7460,t6_956choices,?_⟩
  exact check_of_frontier tree 0 t6_956root t6_956jobs t6_956frontier t6_956all
theorem t6_957choices : plan7461.choices=[4,2,10,10,7,7].map (options 6 5) := by rfl


theorem t6_957part0 : t6_957jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_957frontier : t6_957root.frontier 0=t6_957jobs := by rfl
theorem t6_957all : t6_957jobs.all (Job.check tree)=true := by
  simp only [t6_957jobs,List.all_append,List.all_nil,t6_957part0,Bool.and_self]
theorem t6_957checked : Checked tree [4,2,10,10,7,7] := by
  refine ⟨plan7461,valid7461,t6_957choices,?_⟩
  exact check_of_frontier tree 0 t6_957root t6_957jobs t6_957frontier t6_957all
theorem t6_958choices : plan7462.choices=[4,2,10,10,10,7].map (options 6 5) := by rfl


theorem t6_958part0 : t6_958jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_958frontier : t6_958root.frontier 0=t6_958jobs := by rfl
theorem t6_958all : t6_958jobs.all (Job.check tree)=true := by
  simp only [t6_958jobs,List.all_append,List.all_nil,t6_958part0,Bool.and_self]
theorem t6_958checked : Checked tree [4,2,10,10,10,7] := by
  refine ⟨plan7462,valid7462,t6_958choices,?_⟩
  exact check_of_frontier tree 0 t6_958root t6_958jobs t6_958frontier t6_958all
theorem t6_959choices : plan7463.choices=[4,2,10,10,10,10].map (options 6 5) := by rfl


theorem t6_959part0 : t6_959jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_959frontier : t6_959root.frontier 0=t6_959jobs := by rfl
theorem t6_959all : t6_959jobs.all (Job.check tree)=true := by
  simp only [t6_959jobs,List.all_append,List.all_nil,t6_959part0,Bool.and_self]
theorem t6_959checked : Checked tree [4,2,10,10,10,10] := by
  refine ⟨plan7463,valid7463,t6_959choices,?_⟩
  exact check_of_frontier tree 0 t6_959root t6_959jobs t6_959frontier t6_959all
theorem t6_960choices : plan6315.choices=[4,3,3,3,3,3].map (options 6 1) := by rfl


theorem t6_960part0 : t6_960jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_960frontier : t6_960root.frontier 0=t6_960jobs := by rfl
theorem t6_960all : t6_960jobs.all (Job.check tree)=true := by
  simp only [t6_960jobs,List.all_append,List.all_nil,t6_960part0,Bool.and_self]
theorem t6_960checked : Checked tree [4,3,3,3,3,3] := by
  refine ⟨plan6315,valid6315,t6_960choices,?_⟩
  exact check_of_frontier tree 0 t6_960root t6_960jobs t6_960frontier t6_960all
theorem t6_961choices : plan6411.choices=[4,3,3,3,3,6].map (options 6 2) := by rfl


theorem t6_961part0 : t6_961jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_961frontier : t6_961root.frontier 0=t6_961jobs := by rfl
theorem t6_961all : t6_961jobs.all (Job.check tree)=true := by
  simp only [t6_961jobs,List.all_append,List.all_nil,t6_961part0,Bool.and_self]
theorem t6_961checked : Checked tree [4,3,3,3,3,6] := by
  refine ⟨plan6411,valid6411,t6_961choices,?_⟩
  exact check_of_frontier tree 0 t6_961root t6_961jobs t6_961frontier t6_961all
theorem t6_962choices : plan6412.choices=[4,3,3,3,3,7].map (options 6 2) := by rfl


theorem t6_962part0 : t6_962jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_962frontier : t6_962root.frontier 0=t6_962jobs := by rfl
theorem t6_962all : t6_962jobs.all (Job.check tree)=true := by
  simp only [t6_962jobs,List.all_append,List.all_nil,t6_962part0,Bool.and_self]
theorem t6_962checked : Checked tree [4,3,3,3,3,7] := by
  refine ⟨plan6412,valid6412,t6_962choices,?_⟩
  exact check_of_frontier tree 0 t6_962root t6_962jobs t6_962frontier t6_962all
theorem t6_963choices : plan6413.choices=[4,3,3,3,3,10].map (options 6 2) := by rfl


theorem t6_963part0 : t6_963jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_963frontier : t6_963root.frontier 0=t6_963jobs := by rfl
theorem t6_963all : t6_963jobs.all (Job.check tree)=true := by
  simp only [t6_963jobs,List.all_append,List.all_nil,t6_963part0,Bool.and_self]
theorem t6_963checked : Checked tree [4,3,3,3,3,10] := by
  refine ⟨plan6413,valid6413,t6_963choices,?_⟩
  exact check_of_frontier tree 0 t6_963root t6_963jobs t6_963frontier t6_963all
theorem t6_964choices : plan6630.choices=[4,3,3,3,6,6].map (options 6 3) := by rfl


theorem t6_964part0 : t6_964jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_964frontier : t6_964root.frontier 0=t6_964jobs := by rfl
theorem t6_964all : t6_964jobs.all (Job.check tree)=true := by
  simp only [t6_964jobs,List.all_append,List.all_nil,t6_964part0,Bool.and_self]
theorem t6_964checked : Checked tree [4,3,3,3,6,6] := by
  refine ⟨plan6630,valid6630,t6_964choices,?_⟩
  exact check_of_frontier tree 0 t6_964root t6_964jobs t6_964frontier t6_964all
theorem t6_965choices : plan6631.choices=[4,3,3,3,6,7].map (options 6 3) := by rfl


theorem t6_965part0 : t6_965jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_965part1 : t6_965jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_965part2 : t6_965jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_965frontier : t6_965root.frontier 1=t6_965jobs := by rfl
theorem t6_965all : t6_965jobs.all (Job.check tree)=true := by
  simp only [t6_965jobs,List.all_append,List.all_nil,t6_965part0,t6_965part1,t6_965part2,Bool.and_self]
theorem t6_965checked : Checked tree [4,3,3,3,6,7] := by
  refine ⟨plan6631,valid6631,t6_965choices,?_⟩
  exact check_of_frontier tree 1 t6_965root t6_965jobs t6_965frontier t6_965all
theorem t6_966choices : plan6632.choices=[4,3,3,3,6,10].map (options 6 3) := by rfl


theorem t6_966part0 : t6_966jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_966frontier : t6_966root.frontier 0=t6_966jobs := by rfl
theorem t6_966all : t6_966jobs.all (Job.check tree)=true := by
  simp only [t6_966jobs,List.all_append,List.all_nil,t6_966part0,Bool.and_self]
theorem t6_966checked : Checked tree [4,3,3,3,6,10] := by
  refine ⟨plan6632,valid6632,t6_966choices,?_⟩
  exact check_of_frontier tree 0 t6_966root t6_966jobs t6_966frontier t6_966all
theorem t6_967choices : plan6633.choices=[4,3,3,3,7,7].map (options 6 3) := by rfl


theorem t6_967part0 : t6_967jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_967part1 : t6_967jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_967part2 : t6_967jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_967frontier : t6_967root.frontier 1=t6_967jobs := by rfl
theorem t6_967all : t6_967jobs.all (Job.check tree)=true := by
  simp only [t6_967jobs,List.all_append,List.all_nil,t6_967part0,t6_967part1,t6_967part2,Bool.and_self]
theorem t6_967checked : Checked tree [4,3,3,3,7,7] := by
  refine ⟨plan6633,valid6633,t6_967choices,?_⟩
  exact check_of_frontier tree 1 t6_967root t6_967jobs t6_967frontier t6_967all
theorem t6_968choices : plan6634.choices=[4,3,3,3,10,7].map (options 6 3) := by rfl


theorem t6_968part0 : t6_968jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_968part1 : t6_968jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_968part2 : t6_968jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_968frontier : t6_968root.frontier 1=t6_968jobs := by rfl
theorem t6_968all : t6_968jobs.all (Job.check tree)=true := by
  simp only [t6_968jobs,List.all_append,List.all_nil,t6_968part0,t6_968part1,t6_968part2,Bool.and_self]
theorem t6_968checked : Checked tree [4,3,3,3,10,7] := by
  refine ⟨plan6634,valid6634,t6_968choices,?_⟩
  exact check_of_frontier tree 1 t6_968root t6_968jobs t6_968frontier t6_968all
theorem t6_969choices : plan6635.choices=[4,3,3,3,10,10].map (options 6 3) := by rfl


theorem t6_969part0 : t6_969jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_969frontier : t6_969root.frontier 0=t6_969jobs := by rfl
theorem t6_969all : t6_969jobs.all (Job.check tree)=true := by
  simp only [t6_969jobs,List.all_append,List.all_nil,t6_969part0,Bool.and_self]
theorem t6_969checked : Checked tree [4,3,3,3,10,10] := by
  refine ⟨plan6635,valid6635,t6_969choices,?_⟩
  exact check_of_frontier tree 0 t6_969root t6_969jobs t6_969frontier t6_969all
theorem t6_970choices : plan7010.choices=[4,3,3,6,6,6].map (options 6 4) := by rfl


theorem t6_970part0 : t6_970jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_970frontier : t6_970root.frontier 0=t6_970jobs := by rfl
theorem t6_970all : t6_970jobs.all (Job.check tree)=true := by
  simp only [t6_970jobs,List.all_append,List.all_nil,t6_970part0,Bool.and_self]
theorem t6_970checked : Checked tree [4,3,3,6,6,6] := by
  refine ⟨plan7010,valid7010,t6_970choices,?_⟩
  exact check_of_frontier tree 0 t6_970root t6_970jobs t6_970frontier t6_970all
theorem t6_971choices : plan7011.choices=[4,3,3,6,6,7].map (options 6 4) := by rfl


theorem t6_971part0 : t6_971jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_971part1 : t6_971jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_971frontier : t6_971root.frontier 1=t6_971jobs := by rfl
theorem t6_971all : t6_971jobs.all (Job.check tree)=true := by
  simp only [t6_971jobs,List.all_append,List.all_nil,t6_971part0,t6_971part1,Bool.and_self]
theorem t6_971checked : Checked tree [4,3,3,6,6,7] := by
  refine ⟨plan7011,valid7011,t6_971choices,?_⟩
  exact check_of_frontier tree 1 t6_971root t6_971jobs t6_971frontier t6_971all
theorem t6_972choices : plan7012.choices=[4,3,3,6,6,10].map (options 6 4) := by rfl


theorem t6_972part0 : t6_972jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_972frontier : t6_972root.frontier 0=t6_972jobs := by rfl
theorem t6_972all : t6_972jobs.all (Job.check tree)=true := by
  simp only [t6_972jobs,List.all_append,List.all_nil,t6_972part0,Bool.and_self]
theorem t6_972checked : Checked tree [4,3,3,6,6,10] := by
  refine ⟨plan7012,valid7012,t6_972choices,?_⟩
  exact check_of_frontier tree 0 t6_972root t6_972jobs t6_972frontier t6_972all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks118 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_952checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_965checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_966checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_967checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_968checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_969checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_970checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_971checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_972checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_953checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_954checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_955checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_956checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_957checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_958checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_959checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_960checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_961checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_962checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_963checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_964checked⟩
