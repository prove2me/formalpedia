-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks070
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:20:13.109212+00:00
-- url     : https://prove2.me/submissions/8eedd4e3-75ae-4f28-b042-66707472e783

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks070
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks070
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
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

































































































































































theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)

theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)




























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















theorem valid1544 : plan1544.Valid := valid_step _ _ _ valid561 (by decide +kernel)

theorem valid1545 : plan1545.Valid := valid_step _ _ _ valid562 (by decide +kernel)














































































































































































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



































































































theorem valid3314 : plan3314.Valid := valid_step _ _ _ valid1544 (by decide +kernel)

theorem valid3315 : plan3315.Valid := valid_step _ _ _ valid1545 (by decide +kernel)


























































































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































theorem valid5488 : plan5488.Valid := valid_step _ _ _ valid3314 (by decide +kernel)

theorem valid5489 : plan5489.Valid := valid_step _ _ _ valid3315 (by decide +kernel)






























































































































































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





































































































theorem valid6579 : plan6579.Valid := valid_step _ _ _ valid5488 (by decide +kernel)

theorem valid6580 : plan6580.Valid := valid_step _ _ _ valid5489 (by decide +kernel)
























































































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
theorem t6_643choices : plan6579.choices=[2,3,3,6,6,10].map (options 6 3) := by rfl


theorem t6_643part0 : t6_643jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_643part1 : t6_643jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_643part2 : t6_643jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_643part3 : t6_643jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_643frontier : t6_643root.frontier 2=t6_643jobs := by rfl
theorem t6_643all : t6_643jobs.all (Job.check tree)=true := by
  simp only [t6_643jobs,List.all_append,List.all_nil,t6_643part0,t6_643part1,t6_643part2,t6_643part3,Bool.and_self]
theorem t6_643checked : Checked tree [2,3,3,6,6,10] := by
  refine ⟨plan6579,valid6579,t6_643choices,?_⟩
  exact check_of_frontier tree 2 t6_643root t6_643jobs t6_643frontier t6_643all
theorem t6_644choices : plan6580.choices=[2,3,3,6,7,7].map (options 6 3) := by rfl


theorem t6_644part0 : t6_644jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_644part1 : t6_644jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_644part2 : t6_644jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_644part3 : t6_644jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_644part4 : t6_644jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_644part5 : t6_644jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_644part6 : t6_644jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_644part7 : t6_644jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_644part8 : t6_644jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_644part9 : t6_644jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_644part10 : t6_644jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_644part11 : t6_644jobs11.all (Job.check tree)=true := by decide +kernel

theorem t6_644frontier : t6_644root.frontier 2=t6_644jobs := by rfl
theorem t6_644all : t6_644jobs.all (Job.check tree)=true := by
  simp only [t6_644jobs,List.all_append,List.all_nil,t6_644part0,t6_644part1,t6_644part2,t6_644part3,t6_644part4,t6_644part5,t6_644part6,t6_644part7,t6_644part8,t6_644part9,t6_644part10,t6_644part11,Bool.and_self]
theorem t6_644checked : Checked tree [2,3,3,6,7,7] := by
  refine ⟨plan6580,valid6580,t6_644choices,?_⟩
  exact check_of_frontier tree 2 t6_644root t6_644jobs t6_644frontier t6_644all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks070 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_644checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_643checked⟩
