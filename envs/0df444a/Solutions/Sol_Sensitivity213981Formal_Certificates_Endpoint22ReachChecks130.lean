-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks130
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:50:49.848969+00:00
-- url     : https://prove2.me/submissions/786bceef-8439-4ff4-9ea0-29417085af5a

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks130
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks130
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
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

























































































































theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)









theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)
























































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













































theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)












































































































































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



























theorem valid5774 : plan5774.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5775 : plan5775.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5776 : plan5776.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5777 : plan5777.Valid := valid_step _ _ _ valid3482 (by decide +kernel)






























































































































































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



























































































theorem valid7534 : plan7534.Valid := valid_step _ _ _ valid5774 (by decide +kernel)

theorem valid7535 : plan7535.Valid := valid_step _ _ _ valid5775 (by decide +kernel)

theorem valid7536 : plan7536.Valid := valid_step _ _ _ valid5776 (by decide +kernel)

theorem valid7537 : plan7537.Valid := valid_step _ _ _ valid5777 (by decide +kernel)






























































































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
theorem t6_1211choices : plan7534.choices=[5,3,6,6,10,7].map (options 6 5) := by rfl


theorem t6_1211part0 : t6_1211jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1211part1 : t6_1211jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1211part2 : t6_1211jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1211part3 : t6_1211jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1211frontier : t6_1211root.frontier 2=t6_1211jobs := by rfl
theorem t6_1211all : t6_1211jobs.all (Job.check tree)=true := by
  simp only [t6_1211jobs,List.all_append,List.all_nil,t6_1211part0,t6_1211part1,t6_1211part2,t6_1211part3,Bool.and_self]
theorem t6_1211checked : Checked tree [5,3,6,6,10,7] := by
  refine ⟨plan7534,valid7534,t6_1211choices,?_⟩
  exact check_of_frontier tree 2 t6_1211root t6_1211jobs t6_1211frontier t6_1211all
theorem t6_1212choices : plan7535.choices=[5,3,6,6,10,10].map (options 6 5) := by rfl


theorem t6_1212part0 : t6_1212jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1212frontier : t6_1212root.frontier 0=t6_1212jobs := by rfl
theorem t6_1212all : t6_1212jobs.all (Job.check tree)=true := by
  simp only [t6_1212jobs,List.all_append,List.all_nil,t6_1212part0,Bool.and_self]
theorem t6_1212checked : Checked tree [5,3,6,6,10,10] := by
  refine ⟨plan7535,valid7535,t6_1212choices,?_⟩
  exact check_of_frontier tree 0 t6_1212root t6_1212jobs t6_1212frontier t6_1212all
theorem t6_1213choices : plan7536.choices=[5,3,6,7,7,7].map (options 6 5) := by rfl


theorem t6_1213part0 : t6_1213jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1213part1 : t6_1213jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1213part2 : t6_1213jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1213part3 : t6_1213jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1213part4 : t6_1213jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1213part5 : t6_1213jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1213part6 : t6_1213jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_1213frontier : t6_1213root.frontier 2=t6_1213jobs := by rfl
theorem t6_1213all : t6_1213jobs.all (Job.check tree)=true := by
  simp only [t6_1213jobs,List.all_append,List.all_nil,t6_1213part0,t6_1213part1,t6_1213part2,t6_1213part3,t6_1213part4,t6_1213part5,t6_1213part6,Bool.and_self]
theorem t6_1213checked : Checked tree [5,3,6,7,7,7] := by
  refine ⟨plan7536,valid7536,t6_1213choices,?_⟩
  exact check_of_frontier tree 2 t6_1213root t6_1213jobs t6_1213frontier t6_1213all
theorem t6_1214choices : plan7537.choices=[5,3,6,10,7,7].map (options 6 5) := by rfl


theorem t6_1214part0 : t6_1214jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1214part1 : t6_1214jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1214part2 : t6_1214jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1214part3 : t6_1214jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1214part4 : t6_1214jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1214part5 : t6_1214jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1214part6 : t6_1214jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_1214frontier : t6_1214root.frontier 3=t6_1214jobs := by rfl
theorem t6_1214all : t6_1214jobs.all (Job.check tree)=true := by
  simp only [t6_1214jobs,List.all_append,List.all_nil,t6_1214part0,t6_1214part1,t6_1214part2,t6_1214part3,t6_1214part4,t6_1214part5,t6_1214part6,Bool.and_self]
theorem t6_1214checked : Checked tree [5,3,6,10,7,7] := by
  refine ⟨plan7537,valid7537,t6_1214choices,?_⟩
  exact check_of_frontier tree 3 t6_1214root t6_1214jobs t6_1214frontier t6_1214all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks130 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1214checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1211checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1212checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1213checked⟩
