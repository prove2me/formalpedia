-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks063
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:13:40.222973+00:00
-- url     : https://prove2.me/submissions/c258518b-f6c4-4a61-adaa-b92a0c8f4219

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
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



































































































































































theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)
























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

















theorem valid1545 : plan1545.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1546 : plan1546.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1547 : plan1547.Valid := valid_step _ _ _ valid564 (by decide +kernel)

theorem valid1548 : plan1548.Valid := valid_step _ _ _ valid562 (by decide +kernel)








































































































































































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





































































































theorem valid3315 : plan3315.Valid := valid_step _ _ _ valid1545 (by decide +kernel)

theorem valid3316 : plan3316.Valid := valid_step _ _ _ valid1546 (by decide +kernel)

theorem valid3317 : plan3317.Valid := valid_step _ _ _ valid1547 (by decide +kernel)

theorem valid3318 : plan3318.Valid := valid_step _ _ _ valid1548 (by decide +kernel)




















































































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































































































































































theorem valid5456 : plan5456.Valid := valid_step _ _ _ valid3315 (by decide +kernel)

theorem valid5457 : plan5457.Valid := valid_step _ _ _ valid3316 (by decide +kernel)

theorem valid5458 : plan5458.Valid := valid_step _ _ _ valid3317 (by decide +kernel)

theorem valid5459 : plan5459.Valid := valid_step _ _ _ valid3318 (by decide +kernel)


























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





















































theorem valid6555 : plan6555.Valid := valid_step _ _ _ valid5456 (by decide +kernel)

theorem valid6556 : plan6556.Valid := valid_step _ _ _ valid5457 (by decide +kernel)

theorem valid6557 : plan6557.Valid := valid_step _ _ _ valid5458 (by decide +kernel)

theorem valid6558 : plan6558.Valid := valid_step _ _ _ valid5459 (by decide +kernel)




































































































































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
theorem t6_557choices : plan6555.choices=[2,2,3,6,7,7].map (options 6 3) := by rfl


theorem t6_557part0 : t6_557jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_557part1 : t6_557jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_557part2 : t6_557jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_557part3 : t6_557jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_557part4 : t6_557jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_557part5 : t6_557jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_557part6 : t6_557jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_557frontier : t6_557root.frontier 2=t6_557jobs := by rfl
theorem t6_557all : t6_557jobs.all (Job.check tree)=true := by
  simp only [t6_557jobs,List.all_append,List.all_nil,t6_557part0,t6_557part1,t6_557part2,t6_557part3,t6_557part4,t6_557part5,t6_557part6,Bool.and_self]
theorem t6_557checked : Checked tree [2,2,3,6,7,7] := by
  refine ⟨plan6555,valid6555,t6_557choices,?_⟩
  exact check_of_frontier tree 2 t6_557root t6_557jobs t6_557frontier t6_557all
theorem t6_558choices : plan6556.choices=[2,2,3,6,10,7].map (options 6 3) := by rfl


theorem t6_558part0 : t6_558jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_558part1 : t6_558jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_558part2 : t6_558jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_558part3 : t6_558jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_558part4 : t6_558jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_558part5 : t6_558jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_558part6 : t6_558jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_558frontier : t6_558root.frontier 2=t6_558jobs := by rfl
theorem t6_558all : t6_558jobs.all (Job.check tree)=true := by
  simp only [t6_558jobs,List.all_append,List.all_nil,t6_558part0,t6_558part1,t6_558part2,t6_558part3,t6_558part4,t6_558part5,t6_558part6,Bool.and_self]
theorem t6_558checked : Checked tree [2,2,3,6,10,7] := by
  refine ⟨plan6556,valid6556,t6_558choices,?_⟩
  exact check_of_frontier tree 2 t6_558root t6_558jobs t6_558frontier t6_558all
theorem t6_559choices : plan6557.choices=[2,2,3,6,10,10].map (options 6 3) := by rfl


theorem t6_559part0 : t6_559jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_559part1 : t6_559jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_559frontier : t6_559root.frontier 1=t6_559jobs := by rfl
theorem t6_559all : t6_559jobs.all (Job.check tree)=true := by
  simp only [t6_559jobs,List.all_append,List.all_nil,t6_559part0,t6_559part1,Bool.and_self]
theorem t6_559checked : Checked tree [2,2,3,6,10,10] := by
  refine ⟨plan6557,valid6557,t6_559choices,?_⟩
  exact check_of_frontier tree 1 t6_559root t6_559jobs t6_559frontier t6_559all
theorem t6_560choices : plan6558.choices=[2,2,3,7,7,7].map (options 6 3) := by rfl


theorem t6_560part0 : t6_560jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_560part1 : t6_560jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_560part2 : t6_560jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_560part3 : t6_560jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_560frontier : t6_560root.frontier 1=t6_560jobs := by rfl
theorem t6_560all : t6_560jobs.all (Job.check tree)=true := by
  simp only [t6_560jobs,List.all_append,List.all_nil,t6_560part0,t6_560part1,t6_560part2,t6_560part3,Bool.and_self]
theorem t6_560checked : Checked tree [2,2,3,7,7,7] := by
  refine ⟨plan6558,valid6558,t6_560choices,?_⟩
  exact check_of_frontier tree 1 t6_560root t6_560jobs t6_560frontier t6_560all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks063 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_557checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_558checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_559checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_560checked⟩
