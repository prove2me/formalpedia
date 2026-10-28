-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks088
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:32:15.801102+00:00
-- url     : https://prove2.me/submissions/f1575559-575f-44d4-be43-72f09cd660ad

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
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





































































theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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











































































































































































theorem valid566 : plan566.Valid := valid_step _ _ _ valid131 (by decide +kernel)







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

















































theorem valid1561 : plan1561.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1564 : plan1564.Valid := valid_step _ _ _ valid573 (by decide +kernel)























theorem valid1576 : plan1576.Valid := valid_step _ _ _ valid566 (by decide +kernel)

































theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)



theorem valid1601 : plan1601.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1602 : plan1602.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1603 : plan1603.Valid := valid_step _ _ _ valid579 (by decide +kernel)

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













































































































theorem valid3415 : plan3415.Valid := valid_step _ _ _ valid1561 (by decide +kernel)

theorem valid3416 : plan3416.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3417 : plan3417.Valid := valid_step _ _ _ valid1563 (by decide +kernel)

theorem valid3418 : plan3418.Valid := valid_step _ _ _ valid1564 (by decide +kernel)















theorem valid3426 : plan3426.Valid := valid_step _ _ _ valid1576 (by decide +kernel)




























































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









































































theorem valid3493 : plan3493.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3494 : plan3494.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3495 : plan3495.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3496 : plan3496.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3497 : plan3497.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3498 : plan3498.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3499 : plan3499.Valid := valid_step _ _ _ valid1599 (by decide +kernel)



theorem valid3501 : plan3501.Valid := valid_step _ _ _ valid1601 (by decide +kernel)

theorem valid3502 : plan3502.Valid := valid_step _ _ _ valid1602 (by decide +kernel)

theorem valid3503 : plan3503.Valid := valid_step _ _ _ valid1603 (by decide +kernel)

theorem valid3504 : plan3504.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3505 : plan3505.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3506 : plan3506.Valid := valid_step _ _ _ valid1606 (by decide +kernel)




























































































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



























































theorem valid5694 : plan5694.Valid := valid_step _ _ _ valid3415 (by decide +kernel)

theorem valid5695 : plan5695.Valid := valid_step _ _ _ valid3416 (by decide +kernel)

theorem valid5696 : plan5696.Valid := valid_step _ _ _ valid3417 (by decide +kernel)

theorem valid5697 : plan5697.Valid := valid_step _ _ _ valid3418 (by decide +kernel)

theorem valid5698 : plan5698.Valid := valid_step _ _ _ valid3426 (by decide +kernel)




























































































































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

















theorem valid5865 : plan5865.Valid := valid_step _ _ _ valid3493 (by decide +kernel)

theorem valid5866 : plan5866.Valid := valid_step _ _ _ valid3494 (by decide +kernel)

theorem valid5867 : plan5867.Valid := valid_step _ _ _ valid3495 (by decide +kernel)

theorem valid5868 : plan5868.Valid := valid_step _ _ _ valid3496 (by decide +kernel)

theorem valid5869 : plan5869.Valid := valid_step _ _ _ valid3497 (by decide +kernel)

theorem valid5870 : plan5870.Valid := valid_step _ _ _ valid3498 (by decide +kernel)

theorem valid5871 : plan5871.Valid := valid_step _ _ _ valid3499 (by decide +kernel)



theorem valid5873 : plan5873.Valid := valid_step _ _ _ valid3501 (by decide +kernel)

theorem valid5874 : plan5874.Valid := valid_step _ _ _ valid3502 (by decide +kernel)

theorem valid5875 : plan5875.Valid := valid_step _ _ _ valid3503 (by decide +kernel)

theorem valid5876 : plan5876.Valid := valid_step _ _ _ valid3504 (by decide +kernel)

theorem valid5877 : plan5877.Valid := valid_step _ _ _ valid3505 (by decide +kernel)

theorem valid5878 : plan5878.Valid := valid_step _ _ _ valid3506 (by decide +kernel)




















































































































































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





































































































theorem valid7347 : plan7347.Valid := valid_step _ _ _ valid5865 (by decide +kernel)

theorem valid7348 : plan7348.Valid := valid_step _ _ _ valid5866 (by decide +kernel)

theorem valid7349 : plan7349.Valid := valid_step _ _ _ valid5867 (by decide +kernel)

theorem valid7350 : plan7350.Valid := valid_step _ _ _ valid5868 (by decide +kernel)

theorem valid7351 : plan7351.Valid := valid_step _ _ _ valid5869 (by decide +kernel)

theorem valid7352 : plan7352.Valid := valid_step _ _ _ valid5870 (by decide +kernel)

theorem valid7353 : plan7353.Valid := valid_step _ _ _ valid5871 (by decide +kernel)

theorem valid7354 : plan7354.Valid := valid_step _ _ _ valid5873 (by decide +kernel)

theorem valid7355 : plan7355.Valid := valid_step _ _ _ valid5874 (by decide +kernel)

theorem valid7356 : plan7356.Valid := valid_step _ _ _ valid5875 (by decide +kernel)

theorem valid7357 : plan7357.Valid := valid_step _ _ _ valid5876 (by decide +kernel)

theorem valid7358 : plan7358.Valid := valid_step _ _ _ valid5877 (by decide +kernel)

theorem valid7359 : plan7359.Valid := valid_step _ _ _ valid5878 (by decide +kernel)


































































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









































































theorem valid6949 : plan6949.Valid := valid_step _ _ _ valid5694 (by decide +kernel)

theorem valid6950 : plan6950.Valid := valid_step _ _ _ valid5695 (by decide +kernel)

theorem valid6951 : plan6951.Valid := valid_step _ _ _ valid5696 (by decide +kernel)

theorem valid6952 : plan6952.Valid := valid_step _ _ _ valid5697 (by decide +kernel)

theorem valid6953 : plan6953.Valid := valid_step _ _ _ valid5698 (by decide +kernel)














































































































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
theorem t6_731choices : plan6949.choices=[2,5,9,3,6,10].map (options 6 4) := by rfl


theorem t6_731part0 : t6_731jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_731frontier : t6_731root.frontier 0=t6_731jobs := by rfl
theorem t6_731all : t6_731jobs.all (Job.check tree)=true := by
  simp only [t6_731jobs,List.all_append,List.all_nil,t6_731part0,Bool.and_self]
theorem t6_731checked : Checked tree [2,5,9,3,6,10] := by
  refine ⟨plan6949,valid6949,t6_731choices,?_⟩
  exact check_of_frontier tree 0 t6_731root t6_731jobs t6_731frontier t6_731all
theorem t6_732choices : plan6950.choices=[2,5,9,3,7,7].map (options 6 4) := by rfl


theorem t6_732part0 : t6_732jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_732part1 : t6_732jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_732part2 : t6_732jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_732part3 : t6_732jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_732part4 : t6_732jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_732frontier : t6_732root.frontier 2=t6_732jobs := by rfl
theorem t6_732all : t6_732jobs.all (Job.check tree)=true := by
  simp only [t6_732jobs,List.all_append,List.all_nil,t6_732part0,t6_732part1,t6_732part2,t6_732part3,t6_732part4,Bool.and_self]
theorem t6_732checked : Checked tree [2,5,9,3,7,7] := by
  refine ⟨plan6950,valid6950,t6_732choices,?_⟩
  exact check_of_frontier tree 2 t6_732root t6_732jobs t6_732frontier t6_732all
theorem t6_733choices : plan6951.choices=[2,5,9,3,10,7].map (options 6 4) := by rfl


theorem t6_733part0 : t6_733jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_733part1 : t6_733jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_733part2 : t6_733jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_733part3 : t6_733jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_733frontier : t6_733root.frontier 2=t6_733jobs := by rfl
theorem t6_733all : t6_733jobs.all (Job.check tree)=true := by
  simp only [t6_733jobs,List.all_append,List.all_nil,t6_733part0,t6_733part1,t6_733part2,t6_733part3,Bool.and_self]
theorem t6_733checked : Checked tree [2,5,9,3,10,7] := by
  refine ⟨plan6951,valid6951,t6_733choices,?_⟩
  exact check_of_frontier tree 2 t6_733root t6_733jobs t6_733frontier t6_733all
theorem t6_734choices : plan6952.choices=[2,5,9,3,10,10].map (options 6 4) := by rfl


theorem t6_734part0 : t6_734jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_734frontier : t6_734root.frontier 0=t6_734jobs := by rfl
theorem t6_734all : t6_734jobs.all (Job.check tree)=true := by
  simp only [t6_734jobs,List.all_append,List.all_nil,t6_734part0,Bool.and_self]
theorem t6_734checked : Checked tree [2,5,9,3,10,10] := by
  refine ⟨plan6952,valid6952,t6_734choices,?_⟩
  exact check_of_frontier tree 0 t6_734root t6_734jobs t6_734frontier t6_734all
theorem t6_735choices : plan7347.choices=[2,5,9,6,6,6].map (options 6 5) := by rfl


theorem t6_735part0 : t6_735jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_735frontier : t6_735root.frontier 0=t6_735jobs := by rfl
theorem t6_735all : t6_735jobs.all (Job.check tree)=true := by
  simp only [t6_735jobs,List.all_append,List.all_nil,t6_735part0,Bool.and_self]
theorem t6_735checked : Checked tree [2,5,9,6,6,6] := by
  refine ⟨plan7347,valid7347,t6_735choices,?_⟩
  exact check_of_frontier tree 0 t6_735root t6_735jobs t6_735frontier t6_735all
theorem t6_736choices : plan7348.choices=[2,5,9,6,6,7].map (options 6 5) := by rfl


theorem t6_736part0 : t6_736jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_736frontier : t6_736root.frontier 0=t6_736jobs := by rfl
theorem t6_736all : t6_736jobs.all (Job.check tree)=true := by
  simp only [t6_736jobs,List.all_append,List.all_nil,t6_736part0,Bool.and_self]
theorem t6_736checked : Checked tree [2,5,9,6,6,7] := by
  refine ⟨plan7348,valid7348,t6_736choices,?_⟩
  exact check_of_frontier tree 0 t6_736root t6_736jobs t6_736frontier t6_736all
theorem t6_737choices : plan7349.choices=[2,5,9,6,6,10].map (options 6 5) := by rfl


theorem t6_737part0 : t6_737jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_737frontier : t6_737root.frontier 0=t6_737jobs := by rfl
theorem t6_737all : t6_737jobs.all (Job.check tree)=true := by
  simp only [t6_737jobs,List.all_append,List.all_nil,t6_737part0,Bool.and_self]
theorem t6_737checked : Checked tree [2,5,9,6,6,10] := by
  refine ⟨plan7349,valid7349,t6_737choices,?_⟩
  exact check_of_frontier tree 0 t6_737root t6_737jobs t6_737frontier t6_737all
theorem t6_738choices : plan7350.choices=[2,5,9,6,7,7].map (options 6 5) := by rfl


theorem t6_738part0 : t6_738jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_738part1 : t6_738jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_738frontier : t6_738root.frontier 2=t6_738jobs := by rfl
theorem t6_738all : t6_738jobs.all (Job.check tree)=true := by
  simp only [t6_738jobs,List.all_append,List.all_nil,t6_738part0,t6_738part1,Bool.and_self]
theorem t6_738checked : Checked tree [2,5,9,6,7,7] := by
  refine ⟨plan7350,valid7350,t6_738choices,?_⟩
  exact check_of_frontier tree 2 t6_738root t6_738jobs t6_738frontier t6_738all
theorem t6_739choices : plan7351.choices=[2,5,9,6,10,7].map (options 6 5) := by rfl


theorem t6_739part0 : t6_739jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_739frontier : t6_739root.frontier 0=t6_739jobs := by rfl
theorem t6_739all : t6_739jobs.all (Job.check tree)=true := by
  simp only [t6_739jobs,List.all_append,List.all_nil,t6_739part0,Bool.and_self]
theorem t6_739checked : Checked tree [2,5,9,6,10,7] := by
  refine ⟨plan7351,valid7351,t6_739choices,?_⟩
  exact check_of_frontier tree 0 t6_739root t6_739jobs t6_739frontier t6_739all
theorem t6_740choices : plan7352.choices=[2,5,9,6,10,10].map (options 6 5) := by rfl


theorem t6_740part0 : t6_740jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_740frontier : t6_740root.frontier 0=t6_740jobs := by rfl
theorem t6_740all : t6_740jobs.all (Job.check tree)=true := by
  simp only [t6_740jobs,List.all_append,List.all_nil,t6_740part0,Bool.and_self]
theorem t6_740checked : Checked tree [2,5,9,6,10,10] := by
  refine ⟨plan7352,valid7352,t6_740choices,?_⟩
  exact check_of_frontier tree 0 t6_740root t6_740jobs t6_740frontier t6_740all
theorem t6_741choices : plan7353.choices=[2,5,9,7,7,7].map (options 6 5) := by rfl


theorem t6_741part0 : t6_741jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_741part1 : t6_741jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_741frontier : t6_741root.frontier 1=t6_741jobs := by rfl
theorem t6_741all : t6_741jobs.all (Job.check tree)=true := by
  simp only [t6_741jobs,List.all_append,List.all_nil,t6_741part0,t6_741part1,Bool.and_self]
theorem t6_741checked : Checked tree [2,5,9,7,7,7] := by
  refine ⟨plan7353,valid7353,t6_741choices,?_⟩
  exact check_of_frontier tree 1 t6_741root t6_741jobs t6_741frontier t6_741all
theorem t6_742choices : plan6953.choices=[2,5,9,9,3,7].map (options 6 4) := by rfl


theorem t6_742part0 : t6_742jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_742frontier : t6_742root.frontier 0=t6_742jobs := by rfl
theorem t6_742all : t6_742jobs.all (Job.check tree)=true := by
  simp only [t6_742jobs,List.all_append,List.all_nil,t6_742part0,Bool.and_self]
theorem t6_742checked : Checked tree [2,5,9,9,3,7] := by
  refine ⟨plan6953,valid6953,t6_742choices,?_⟩
  exact check_of_frontier tree 0 t6_742root t6_742jobs t6_742frontier t6_742all
theorem t6_743choices : plan7354.choices=[2,5,9,9,6,7].map (options 6 5) := by rfl


theorem t6_743part0 : t6_743jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_743frontier : t6_743root.frontier 0=t6_743jobs := by rfl
theorem t6_743all : t6_743jobs.all (Job.check tree)=true := by
  simp only [t6_743jobs,List.all_append,List.all_nil,t6_743part0,Bool.and_self]
theorem t6_743checked : Checked tree [2,5,9,9,6,7] := by
  refine ⟨plan7354,valid7354,t6_743choices,?_⟩
  exact check_of_frontier tree 0 t6_743root t6_743jobs t6_743frontier t6_743all
theorem t6_744choices : plan7355.choices=[2,5,9,9,7,7].map (options 6 5) := by rfl


theorem t6_744part0 : t6_744jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_744frontier : t6_744root.frontier 0=t6_744jobs := by rfl
theorem t6_744all : t6_744jobs.all (Job.check tree)=true := by
  simp only [t6_744jobs,List.all_append,List.all_nil,t6_744part0,Bool.and_self]
theorem t6_744checked : Checked tree [2,5,9,9,7,7] := by
  refine ⟨plan7355,valid7355,t6_744choices,?_⟩
  exact check_of_frontier tree 0 t6_744root t6_744jobs t6_744frontier t6_744all
theorem t6_745choices : plan7356.choices=[2,5,9,9,10,7].map (options 6 5) := by rfl


theorem t6_745part0 : t6_745jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_745frontier : t6_745root.frontier 0=t6_745jobs := by rfl
theorem t6_745all : t6_745jobs.all (Job.check tree)=true := by
  simp only [t6_745jobs,List.all_append,List.all_nil,t6_745part0,Bool.and_self]
theorem t6_745checked : Checked tree [2,5,9,9,10,7] := by
  refine ⟨plan7356,valid7356,t6_745choices,?_⟩
  exact check_of_frontier tree 0 t6_745root t6_745jobs t6_745frontier t6_745all
theorem t6_746choices : plan7357.choices=[2,5,9,10,7,7].map (options 6 5) := by rfl


theorem t6_746part0 : t6_746jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_746part1 : t6_746jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_746frontier : t6_746root.frontier 2=t6_746jobs := by rfl
theorem t6_746all : t6_746jobs.all (Job.check tree)=true := by
  simp only [t6_746jobs,List.all_append,List.all_nil,t6_746part0,t6_746part1,Bool.and_self]
theorem t6_746checked : Checked tree [2,5,9,10,7,7] := by
  refine ⟨plan7357,valid7357,t6_746choices,?_⟩
  exact check_of_frontier tree 2 t6_746root t6_746jobs t6_746frontier t6_746all
theorem t6_747choices : plan7358.choices=[2,5,9,10,10,7].map (options 6 5) := by rfl


theorem t6_747part0 : t6_747jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_747frontier : t6_747root.frontier 0=t6_747jobs := by rfl
theorem t6_747all : t6_747jobs.all (Job.check tree)=true := by
  simp only [t6_747jobs,List.all_append,List.all_nil,t6_747part0,Bool.and_self]
theorem t6_747checked : Checked tree [2,5,9,10,10,7] := by
  refine ⟨plan7358,valid7358,t6_747choices,?_⟩
  exact check_of_frontier tree 0 t6_747root t6_747jobs t6_747frontier t6_747all
theorem t6_748choices : plan7359.choices=[2,5,9,10,10,10].map (options 6 5) := by rfl


theorem t6_748part0 : t6_748jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_748frontier : t6_748root.frontier 0=t6_748jobs := by rfl
theorem t6_748all : t6_748jobs.all (Job.check tree)=true := by
  simp only [t6_748jobs,List.all_append,List.all_nil,t6_748part0,Bool.and_self]
theorem t6_748checked : Checked tree [2,5,9,10,10,10] := by
  refine ⟨plan7359,valid7359,t6_748choices,?_⟩
  exact check_of_frontier tree 0 t6_748root t6_748jobs t6_748frontier t6_748all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks088 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_737checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_738checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_739checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_740checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_741checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_742checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_743checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_744checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_745checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_746checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_747checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_748checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_732checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_733checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_734checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_735checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_731checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_736checked⟩
