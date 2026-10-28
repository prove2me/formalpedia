-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks125
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:48:40.548027+00:00
-- url     : https://prove2.me/submissions/21e99e43-660d-431a-9e11-11923c425633

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks125
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks125
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
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

theorem valid1537 : plan1537.Valid := valid_step _ _ _ valid564 (by decide +kernel)































































theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)


























































































































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















































theorem valid6648 : plan6648.Valid := valid_step _ _ _ valid5484 (by decide +kernel)

theorem valid6649 : plan6649.Valid := valid_step _ _ _ valid5485 (by decide +kernel)














































































































































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





































































theorem valid7043 : plan7043.Valid := valid_step _ _ _ valid5622 (by decide +kernel)

theorem valid7044 : plan7044.Valid := valid_step _ _ _ valid5623 (by decide +kernel)

theorem valid7045 : plan7045.Valid := valid_step _ _ _ valid5624 (by decide +kernel)






















































































































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
theorem t6_1195choices : plan6648.choices=[5,3,3,3,10,7].map (options 6 3) := by rfl


theorem t6_1195part0 : t6_1195jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1195part1 : t6_1195jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1195part2 : t6_1195jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1195part3 : t6_1195jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1195part4 : t6_1195jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1195part5 : t6_1195jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1195frontier : t6_1195root.frontier 2=t6_1195jobs := by rfl
theorem t6_1195all : t6_1195jobs.all (Job.check tree)=true := by
  simp only [t6_1195jobs,List.all_append,List.all_nil,t6_1195part0,t6_1195part1,t6_1195part2,t6_1195part3,t6_1195part4,t6_1195part5,Bool.and_self]
theorem t6_1195checked : Checked tree [5,3,3,3,10,7] := by
  refine ⟨plan6648,valid6648,t6_1195choices,?_⟩
  exact check_of_frontier tree 2 t6_1195root t6_1195jobs t6_1195frontier t6_1195all
theorem t6_1196choices : plan6649.choices=[5,3,3,3,10,10].map (options 6 3) := by rfl


theorem t6_1196part0 : t6_1196jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1196part1 : t6_1196jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1196frontier : t6_1196root.frontier 1=t6_1196jobs := by rfl
theorem t6_1196all : t6_1196jobs.all (Job.check tree)=true := by
  simp only [t6_1196jobs,List.all_append,List.all_nil,t6_1196part0,t6_1196part1,Bool.and_self]
theorem t6_1196checked : Checked tree [5,3,3,3,10,10] := by
  refine ⟨plan6649,valid6649,t6_1196choices,?_⟩
  exact check_of_frontier tree 1 t6_1196root t6_1196jobs t6_1196frontier t6_1196all
theorem t6_1197choices : plan7043.choices=[5,3,3,6,6,6].map (options 6 4) := by rfl


theorem t6_1197part0 : t6_1197jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1197part1 : t6_1197jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1197frontier : t6_1197root.frontier 1=t6_1197jobs := by rfl
theorem t6_1197all : t6_1197jobs.all (Job.check tree)=true := by
  simp only [t6_1197jobs,List.all_append,List.all_nil,t6_1197part0,t6_1197part1,Bool.and_self]
theorem t6_1197checked : Checked tree [5,3,3,6,6,6] := by
  refine ⟨plan7043,valid7043,t6_1197choices,?_⟩
  exact check_of_frontier tree 1 t6_1197root t6_1197jobs t6_1197frontier t6_1197all
theorem t6_1198choices : plan7044.choices=[5,3,3,6,6,7].map (options 6 4) := by rfl


theorem t6_1198part0 : t6_1198jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1198part1 : t6_1198jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1198part2 : t6_1198jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1198part3 : t6_1198jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1198part4 : t6_1198jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1198part5 : t6_1198jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1198frontier : t6_1198root.frontier 2=t6_1198jobs := by rfl
theorem t6_1198all : t6_1198jobs.all (Job.check tree)=true := by
  simp only [t6_1198jobs,List.all_append,List.all_nil,t6_1198part0,t6_1198part1,t6_1198part2,t6_1198part3,t6_1198part4,t6_1198part5,Bool.and_self]
theorem t6_1198checked : Checked tree [5,3,3,6,6,7] := by
  refine ⟨plan7044,valid7044,t6_1198choices,?_⟩
  exact check_of_frontier tree 2 t6_1198root t6_1198jobs t6_1198frontier t6_1198all
theorem t6_1199choices : plan7045.choices=[5,3,3,6,6,10].map (options 6 4) := by rfl


theorem t6_1199part0 : t6_1199jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1199part1 : t6_1199jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1199part2 : t6_1199jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1199part3 : t6_1199jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1199frontier : t6_1199root.frontier 1=t6_1199jobs := by rfl
theorem t6_1199all : t6_1199jobs.all (Job.check tree)=true := by
  simp only [t6_1199jobs,List.all_append,List.all_nil,t6_1199part0,t6_1199part1,t6_1199part2,t6_1199part3,Bool.and_self]
theorem t6_1199checked : Checked tree [5,3,3,6,6,10] := by
  refine ⟨plan7045,valid7045,t6_1199choices,?_⟩
  exact check_of_frontier tree 1 t6_1199root t6_1199jobs t6_1199frontier t6_1199all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks125 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1198checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1199checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1195checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1196checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1197checked⟩
