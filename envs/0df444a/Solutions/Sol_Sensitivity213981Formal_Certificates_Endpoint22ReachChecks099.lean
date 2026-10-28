-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks099
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:43:47.412998+00:00
-- url     : https://prove2.me/submissions/b03f3e19-71bb-4907-b1ac-8502abbdf781

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks099
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks099
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





























































theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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





























































































































































theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)






























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











theorem valid1542 : plan1542.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1543 : plan1543.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1544 : plan1544.Valid := valid_step _ _ _ valid561 (by decide +kernel)
















































































































































































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































































































theorem valid3312 : plan3312.Valid := valid_step _ _ _ valid1542 (by decide +kernel)

theorem valid3313 : plan3313.Valid := valid_step _ _ _ valid1543 (by decide +kernel)

theorem valid3314 : plan3314.Valid := valid_step _ _ _ valid1544 (by decide +kernel)




























































































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



























theorem valid5486 : plan5486.Valid := valid_step _ _ _ valid3312 (by decide +kernel)

theorem valid5487 : plan5487.Valid := valid_step _ _ _ valid3313 (by decide +kernel)

theorem valid5488 : plan5488.Valid := valid_step _ _ _ valid3314 (by decide +kernel)
































































































































































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































































































































































theorem valid6608 : plan6608.Valid := valid_step _ _ _ valid5486 (by decide +kernel)

theorem valid6609 : plan6609.Valid := valid_step _ _ _ valid5487 (by decide +kernel)

theorem valid6610 : plan6610.Valid := valid_step _ _ _ valid5488 (by decide +kernel)




























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
theorem t6_843choices : plan6608.choices=[3,3,3,6,6,6].map (options 6 3) := by rfl


theorem t6_843part0 : t6_843jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_843part1 : t6_843jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_843frontier : t6_843root.frontier 1=t6_843jobs := by rfl
theorem t6_843all : t6_843jobs.all (Job.check tree)=true := by
  simp only [t6_843jobs,List.all_append,List.all_nil,t6_843part0,t6_843part1,Bool.and_self]
theorem t6_843checked : Checked tree [3,3,3,6,6,6] := by
  refine ⟨plan6608,valid6608,t6_843choices,?_⟩
  exact check_of_frontier tree 1 t6_843root t6_843jobs t6_843frontier t6_843all
theorem t6_844choices : plan6609.choices=[3,3,3,6,6,7].map (options 6 3) := by rfl


theorem t6_844part0 : t6_844jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_844part1 : t6_844jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_844part2 : t6_844jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_844part3 : t6_844jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_844part4 : t6_844jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_844part5 : t6_844jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_844frontier : t6_844root.frontier 2=t6_844jobs := by rfl
theorem t6_844all : t6_844jobs.all (Job.check tree)=true := by
  simp only [t6_844jobs,List.all_append,List.all_nil,t6_844part0,t6_844part1,t6_844part2,t6_844part3,t6_844part4,t6_844part5,Bool.and_self]
theorem t6_844checked : Checked tree [3,3,3,6,6,7] := by
  refine ⟨plan6609,valid6609,t6_844choices,?_⟩
  exact check_of_frontier tree 2 t6_844root t6_844jobs t6_844frontier t6_844all
theorem t6_845choices : plan6610.choices=[3,3,3,6,6,10].map (options 6 3) := by rfl


theorem t6_845part0 : t6_845jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_845part1 : t6_845jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_845part2 : t6_845jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_845part3 : t6_845jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_845frontier : t6_845root.frontier 1=t6_845jobs := by rfl
theorem t6_845all : t6_845jobs.all (Job.check tree)=true := by
  simp only [t6_845jobs,List.all_append,List.all_nil,t6_845part0,t6_845part1,t6_845part2,t6_845part3,Bool.and_self]
theorem t6_845checked : Checked tree [3,3,3,6,6,10] := by
  refine ⟨plan6610,valid6610,t6_845choices,?_⟩
  exact check_of_frontier tree 1 t6_845root t6_845jobs t6_845frontier t6_845all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks099 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_843checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_844checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_845checked⟩
