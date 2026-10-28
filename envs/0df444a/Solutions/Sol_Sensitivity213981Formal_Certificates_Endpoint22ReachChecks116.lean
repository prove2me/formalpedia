-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks116
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:41:08.451212+00:00
-- url     : https://prove2.me/submissions/c746f3de-de85-43bb-a5c5-c472c2209595

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks116
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks116
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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

theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid573 : plan573.Valid := valid_step _ _ _ valid132 (by decide +kernel)






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

theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)

theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)





theorem valid1578 : plan1578.Valid := valid_step _ _ _ valid571 (by decide +kernel)



theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)






































































































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













































































theorem valid3350 : plan3350.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3351 : plan3351.Valid := valid_step _ _ _ valid1578 (by decide +kernel)

theorem valid3352 : plan3352.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3353 : plan3353.Valid := valid_step _ _ _ valid1581 (by decide +kernel)













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











































































































































theorem valid5350 : plan5350.Valid := valid_step _ _ _ valid3246 (by decide +kernel)




















































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



theorem valid5378 : plan5378.Valid := valid_step _ _ _ valid3265 (by decide +kernel)

theorem valid5379 : plan5379.Valid := valid_step _ _ _ valid3266 (by decide +kernel)

theorem valid5380 : plan5380.Valid := valid_step _ _ _ valid3267 (by decide +kernel)





































































































































theorem valid5447 : plan5447.Valid := valid_step _ _ _ valid3306 (by decide +kernel)

theorem valid5448 : plan5448.Valid := valid_step _ _ _ valid3307 (by decide +kernel)

theorem valid5449 : plan5449.Valid := valid_step _ _ _ valid3308 (by decide +kernel)

theorem valid5450 : plan5450.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5451 : plan5451.Valid := valid_step _ _ _ valid3310 (by decide +kernel)

theorem valid5452 : plan5452.Valid := valid_step _ _ _ valid3311 (by decide +kernel)








































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



















































































































































theorem valid6314 : plan6314.Valid := valid_step _ _ _ valid5350 (by decide +kernel)












































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

theorem valid3363 : plan3363.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3364 : plan3364.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3365 : plan3365.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3366 : plan3366.Valid := valid_step _ _ _ valid1575 (by decide +kernel)




















































































































































































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











































































































































































theorem valid5558 : plan5558.Valid := valid_step _ _ _ valid3350 (by decide +kernel)

theorem valid5559 : plan5559.Valid := valid_step _ _ _ valid3351 (by decide +kernel)

theorem valid5560 : plan5560.Valid := valid_step _ _ _ valid3352 (by decide +kernel)

theorem valid5561 : plan5561.Valid := valid_step _ _ _ valid3353 (by decide +kernel)

theorem valid5562 : plan5562.Valid := valid_step _ _ _ valid3360 (by decide +kernel)

theorem valid5563 : plan5563.Valid := valid_step _ _ _ valid3361 (by decide +kernel)

theorem valid5564 : plan5564.Valid := valid_step _ _ _ valid3362 (by decide +kernel)

theorem valid5565 : plan5565.Valid := valid_step _ _ _ valid3363 (by decide +kernel)

theorem valid5566 : plan5566.Valid := valid_step _ _ _ valid3364 (by decide +kernel)

theorem valid5567 : plan5567.Valid := valid_step _ _ _ valid3365 (by decide +kernel)

theorem valid5568 : plan5568.Valid := valid_step _ _ _ valid3366 (by decide +kernel)
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

theorem valid6625 : plan6625.Valid := valid_step _ _ _ valid5450 (by decide +kernel)

theorem valid6626 : plan6626.Valid := valid_step _ _ _ valid5451 (by decide +kernel)

theorem valid6627 : plan6627.Valid := valid_step _ _ _ valid5452 (by decide +kernel)


























































































































































































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















































































































































theorem valid6408 : plan6408.Valid := valid_step _ _ _ valid5378 (by decide +kernel)

theorem valid6409 : plan6409.Valid := valid_step _ _ _ valid5379 (by decide +kernel)

theorem valid6410 : plan6410.Valid := valid_step _ _ _ valid5380 (by decide +kernel)












































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



























































































































































































theorem valid6622 : plan6622.Valid := valid_step _ _ _ valid5447 (by decide +kernel)

theorem valid6623 : plan6623.Valid := valid_step _ _ _ valid5448 (by decide +kernel)

theorem valid6624 : plan6624.Valid := valid_step _ _ _ valid5449 (by decide +kernel)
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



























































































































































theorem valid6990 : plan6990.Valid := valid_step _ _ _ valid5558 (by decide +kernel)

theorem valid6991 : plan6991.Valid := valid_step _ _ _ valid5559 (by decide +kernel)

theorem valid6992 : plan6992.Valid := valid_step _ _ _ valid5560 (by decide +kernel)

theorem valid6993 : plan6993.Valid := valid_step _ _ _ valid5561 (by decide +kernel)

theorem valid6994 : plan6994.Valid := valid_step _ _ _ valid5562 (by decide +kernel)

theorem valid6995 : plan6995.Valid := valid_step _ _ _ valid5563 (by decide +kernel)

theorem valid6996 : plan6996.Valid := valid_step _ _ _ valid5564 (by decide +kernel)

theorem valid6997 : plan6997.Valid := valid_step _ _ _ valid5565 (by decide +kernel)

theorem valid6998 : plan6998.Valid := valid_step _ _ _ valid5566 (by decide +kernel)

theorem valid6999 : plan6999.Valid := valid_step _ _ _ valid5567 (by decide +kernel)

theorem valid7000 : plan7000.Valid := valid_step _ _ _ valid5568 (by decide +kernel)
















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
theorem t6_898choices : plan6990.choices=[4,2,2,7,7,7].map (options 6 4) := by rfl


theorem t6_898part0 : t6_898jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_898frontier : t6_898root.frontier 0=t6_898jobs := by rfl
theorem t6_898all : t6_898jobs.all (Job.check tree)=true := by
  simp only [t6_898jobs,List.all_append,List.all_nil,t6_898part0,Bool.and_self]
theorem t6_898checked : Checked tree [4,2,2,7,7,7] := by
  refine ⟨plan6990,valid6990,t6_898choices,?_⟩
  exact check_of_frontier tree 0 t6_898root t6_898jobs t6_898frontier t6_898all
theorem t6_899choices : plan6991.choices=[4,2,2,9,7,7].map (options 6 4) := by rfl


theorem t6_899part0 : t6_899jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_899frontier : t6_899root.frontier 0=t6_899jobs := by rfl
theorem t6_899all : t6_899jobs.all (Job.check tree)=true := by
  simp only [t6_899jobs,List.all_append,List.all_nil,t6_899part0,Bool.and_self]
theorem t6_899checked : Checked tree [4,2,2,9,7,7] := by
  refine ⟨plan6991,valid6991,t6_899choices,?_⟩
  exact check_of_frontier tree 0 t6_899root t6_899jobs t6_899frontier t6_899all
theorem t6_900choices : plan6992.choices=[4,2,2,10,7,7].map (options 6 4) := by rfl


theorem t6_900part0 : t6_900jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_900frontier : t6_900root.frontier 0=t6_900jobs := by rfl
theorem t6_900all : t6_900jobs.all (Job.check tree)=true := by
  simp only [t6_900jobs,List.all_append,List.all_nil,t6_900part0,Bool.and_self]
theorem t6_900checked : Checked tree [4,2,2,10,7,7] := by
  refine ⟨plan6992,valid6992,t6_900choices,?_⟩
  exact check_of_frontier tree 0 t6_900root t6_900jobs t6_900frontier t6_900all
theorem t6_901choices : plan6993.choices=[4,2,2,10,10,7].map (options 6 4) := by rfl


theorem t6_901part0 : t6_901jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_901frontier : t6_901root.frontier 0=t6_901jobs := by rfl
theorem t6_901all : t6_901jobs.all (Job.check tree)=true := by
  simp only [t6_901jobs,List.all_append,List.all_nil,t6_901part0,Bool.and_self]
theorem t6_901checked : Checked tree [4,2,2,10,10,7] := by
  refine ⟨plan6993,valid6993,t6_901choices,?_⟩
  exact check_of_frontier tree 0 t6_901root t6_901jobs t6_901frontier t6_901all
theorem t6_902choices : plan6314.choices=[4,2,3,3,3,3].map (options 6 1) := by rfl


theorem t6_902part0 : t6_902jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_902frontier : t6_902root.frontier 0=t6_902jobs := by rfl
theorem t6_902all : t6_902jobs.all (Job.check tree)=true := by
  simp only [t6_902jobs,List.all_append,List.all_nil,t6_902part0,Bool.and_self]
theorem t6_902checked : Checked tree [4,2,3,3,3,3] := by
  refine ⟨plan6314,valid6314,t6_902choices,?_⟩
  exact check_of_frontier tree 0 t6_902root t6_902jobs t6_902frontier t6_902all
theorem t6_903choices : plan6408.choices=[4,2,3,3,3,6].map (options 6 2) := by rfl


theorem t6_903part0 : t6_903jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_903frontier : t6_903root.frontier 0=t6_903jobs := by rfl
theorem t6_903all : t6_903jobs.all (Job.check tree)=true := by
  simp only [t6_903jobs,List.all_append,List.all_nil,t6_903part0,Bool.and_self]
theorem t6_903checked : Checked tree [4,2,3,3,3,6] := by
  refine ⟨plan6408,valid6408,t6_903choices,?_⟩
  exact check_of_frontier tree 0 t6_903root t6_903jobs t6_903frontier t6_903all
theorem t6_904choices : plan6409.choices=[4,2,3,3,3,7].map (options 6 2) := by rfl


theorem t6_904part0 : t6_904jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_904frontier : t6_904root.frontier 0=t6_904jobs := by rfl
theorem t6_904all : t6_904jobs.all (Job.check tree)=true := by
  simp only [t6_904jobs,List.all_append,List.all_nil,t6_904part0,Bool.and_self]
theorem t6_904checked : Checked tree [4,2,3,3,3,7] := by
  refine ⟨plan6409,valid6409,t6_904choices,?_⟩
  exact check_of_frontier tree 0 t6_904root t6_904jobs t6_904frontier t6_904all
theorem t6_905choices : plan6410.choices=[4,2,3,3,3,10].map (options 6 2) := by rfl


theorem t6_905part0 : t6_905jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_905frontier : t6_905root.frontier 0=t6_905jobs := by rfl
theorem t6_905all : t6_905jobs.all (Job.check tree)=true := by
  simp only [t6_905jobs,List.all_append,List.all_nil,t6_905part0,Bool.and_self]
theorem t6_905checked : Checked tree [4,2,3,3,3,10] := by
  refine ⟨plan6410,valid6410,t6_905choices,?_⟩
  exact check_of_frontier tree 0 t6_905root t6_905jobs t6_905frontier t6_905all
theorem t6_906choices : plan6622.choices=[4,2,3,3,6,6].map (options 6 3) := by rfl


theorem t6_906part0 : t6_906jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_906frontier : t6_906root.frontier 0=t6_906jobs := by rfl
theorem t6_906all : t6_906jobs.all (Job.check tree)=true := by
  simp only [t6_906jobs,List.all_append,List.all_nil,t6_906part0,Bool.and_self]
theorem t6_906checked : Checked tree [4,2,3,3,6,6] := by
  refine ⟨plan6622,valid6622,t6_906choices,?_⟩
  exact check_of_frontier tree 0 t6_906root t6_906jobs t6_906frontier t6_906all
theorem t6_907choices : plan6623.choices=[4,2,3,3,6,7].map (options 6 3) := by rfl


theorem t6_907part0 : t6_907jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_907part1 : t6_907jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_907frontier : t6_907root.frontier 1=t6_907jobs := by rfl
theorem t6_907all : t6_907jobs.all (Job.check tree)=true := by
  simp only [t6_907jobs,List.all_append,List.all_nil,t6_907part0,t6_907part1,Bool.and_self]
theorem t6_907checked : Checked tree [4,2,3,3,6,7] := by
  refine ⟨plan6623,valid6623,t6_907choices,?_⟩
  exact check_of_frontier tree 1 t6_907root t6_907jobs t6_907frontier t6_907all
theorem t6_908choices : plan6624.choices=[4,2,3,3,6,10].map (options 6 3) := by rfl


theorem t6_908part0 : t6_908jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_908frontier : t6_908root.frontier 0=t6_908jobs := by rfl
theorem t6_908all : t6_908jobs.all (Job.check tree)=true := by
  simp only [t6_908jobs,List.all_append,List.all_nil,t6_908part0,Bool.and_self]
theorem t6_908checked : Checked tree [4,2,3,3,6,10] := by
  refine ⟨plan6624,valid6624,t6_908choices,?_⟩
  exact check_of_frontier tree 0 t6_908root t6_908jobs t6_908frontier t6_908all
theorem t6_909choices : plan6625.choices=[4,2,3,3,7,7].map (options 6 3) := by rfl


theorem t6_909part0 : t6_909jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_909part1 : t6_909jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_909part2 : t6_909jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_909frontier : t6_909root.frontier 1=t6_909jobs := by rfl
theorem t6_909all : t6_909jobs.all (Job.check tree)=true := by
  simp only [t6_909jobs,List.all_append,List.all_nil,t6_909part0,t6_909part1,t6_909part2,Bool.and_self]
theorem t6_909checked : Checked tree [4,2,3,3,7,7] := by
  refine ⟨plan6625,valid6625,t6_909choices,?_⟩
  exact check_of_frontier tree 1 t6_909root t6_909jobs t6_909frontier t6_909all
theorem t6_910choices : plan6626.choices=[4,2,3,3,10,7].map (options 6 3) := by rfl


theorem t6_910part0 : t6_910jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_910part1 : t6_910jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_910frontier : t6_910root.frontier 1=t6_910jobs := by rfl
theorem t6_910all : t6_910jobs.all (Job.check tree)=true := by
  simp only [t6_910jobs,List.all_append,List.all_nil,t6_910part0,t6_910part1,Bool.and_self]
theorem t6_910checked : Checked tree [4,2,3,3,10,7] := by
  refine ⟨plan6626,valid6626,t6_910choices,?_⟩
  exact check_of_frontier tree 1 t6_910root t6_910jobs t6_910frontier t6_910all
theorem t6_911choices : plan6627.choices=[4,2,3,3,10,10].map (options 6 3) := by rfl


theorem t6_911part0 : t6_911jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_911frontier : t6_911root.frontier 0=t6_911jobs := by rfl
theorem t6_911all : t6_911jobs.all (Job.check tree)=true := by
  simp only [t6_911jobs,List.all_append,List.all_nil,t6_911part0,Bool.and_self]
theorem t6_911checked : Checked tree [4,2,3,3,10,10] := by
  refine ⟨plan6627,valid6627,t6_911choices,?_⟩
  exact check_of_frontier tree 0 t6_911root t6_911jobs t6_911frontier t6_911all
theorem t6_912choices : plan6994.choices=[4,2,3,6,6,6].map (options 6 4) := by rfl


theorem t6_912part0 : t6_912jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_912frontier : t6_912root.frontier 0=t6_912jobs := by rfl
theorem t6_912all : t6_912jobs.all (Job.check tree)=true := by
  simp only [t6_912jobs,List.all_append,List.all_nil,t6_912part0,Bool.and_self]
theorem t6_912checked : Checked tree [4,2,3,6,6,6] := by
  refine ⟨plan6994,valid6994,t6_912choices,?_⟩
  exact check_of_frontier tree 0 t6_912root t6_912jobs t6_912frontier t6_912all
theorem t6_913choices : plan6995.choices=[4,2,3,6,6,7].map (options 6 4) := by rfl


theorem t6_913part0 : t6_913jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_913part1 : t6_913jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_913frontier : t6_913root.frontier 1=t6_913jobs := by rfl
theorem t6_913all : t6_913jobs.all (Job.check tree)=true := by
  simp only [t6_913jobs,List.all_append,List.all_nil,t6_913part0,t6_913part1,Bool.and_self]
theorem t6_913checked : Checked tree [4,2,3,6,6,7] := by
  refine ⟨plan6995,valid6995,t6_913choices,?_⟩
  exact check_of_frontier tree 1 t6_913root t6_913jobs t6_913frontier t6_913all
theorem t6_914choices : plan6996.choices=[4,2,3,6,6,10].map (options 6 4) := by rfl


theorem t6_914part0 : t6_914jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_914frontier : t6_914root.frontier 0=t6_914jobs := by rfl
theorem t6_914all : t6_914jobs.all (Job.check tree)=true := by
  simp only [t6_914jobs,List.all_append,List.all_nil,t6_914part0,Bool.and_self]
theorem t6_914checked : Checked tree [4,2,3,6,6,10] := by
  refine ⟨plan6996,valid6996,t6_914choices,?_⟩
  exact check_of_frontier tree 0 t6_914root t6_914jobs t6_914frontier t6_914all
theorem t6_915choices : plan6997.choices=[4,2,3,6,7,7].map (options 6 4) := by rfl


theorem t6_915part0 : t6_915jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_915part1 : t6_915jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_915part2 : t6_915jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_915frontier : t6_915root.frontier 2=t6_915jobs := by rfl
theorem t6_915all : t6_915jobs.all (Job.check tree)=true := by
  simp only [t6_915jobs,List.all_append,List.all_nil,t6_915part0,t6_915part1,t6_915part2,Bool.and_self]
theorem t6_915checked : Checked tree [4,2,3,6,7,7] := by
  refine ⟨plan6997,valid6997,t6_915choices,?_⟩
  exact check_of_frontier tree 2 t6_915root t6_915jobs t6_915frontier t6_915all
theorem t6_916choices : plan6998.choices=[4,2,3,6,10,7].map (options 6 4) := by rfl


theorem t6_916part0 : t6_916jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_916part1 : t6_916jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_916frontier : t6_916root.frontier 1=t6_916jobs := by rfl
theorem t6_916all : t6_916jobs.all (Job.check tree)=true := by
  simp only [t6_916jobs,List.all_append,List.all_nil,t6_916part0,t6_916part1,Bool.and_self]
theorem t6_916checked : Checked tree [4,2,3,6,10,7] := by
  refine ⟨plan6998,valid6998,t6_916choices,?_⟩
  exact check_of_frontier tree 1 t6_916root t6_916jobs t6_916frontier t6_916all
theorem t6_917choices : plan6999.choices=[4,2,3,6,10,10].map (options 6 4) := by rfl


theorem t6_917part0 : t6_917jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_917frontier : t6_917root.frontier 0=t6_917jobs := by rfl
theorem t6_917all : t6_917jobs.all (Job.check tree)=true := by
  simp only [t6_917jobs,List.all_append,List.all_nil,t6_917part0,Bool.and_self]
theorem t6_917checked : Checked tree [4,2,3,6,10,10] := by
  refine ⟨plan6999,valid6999,t6_917choices,?_⟩
  exact check_of_frontier tree 0 t6_917root t6_917jobs t6_917frontier t6_917all
theorem t6_918choices : plan7000.choices=[4,2,3,7,7,7].map (options 6 4) := by rfl


theorem t6_918part0 : t6_918jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_918part1 : t6_918jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_918frontier : t6_918root.frontier 1=t6_918jobs := by rfl
theorem t6_918all : t6_918jobs.all (Job.check tree)=true := by
  simp only [t6_918jobs,List.all_append,List.all_nil,t6_918part0,t6_918part1,Bool.and_self]
theorem t6_918checked : Checked tree [4,2,3,7,7,7] := by
  refine ⟨plan7000,valid7000,t6_918choices,?_⟩
  exact check_of_frontier tree 1 t6_918root t6_918jobs t6_918frontier t6_918all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks116 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_898checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_910checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_911checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_912checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_913checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_914checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_915checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_916checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_899checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_917checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_918checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_900checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_901checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_902checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_903checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_904checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_905checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_906checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_907checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_908checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_909checked⟩
