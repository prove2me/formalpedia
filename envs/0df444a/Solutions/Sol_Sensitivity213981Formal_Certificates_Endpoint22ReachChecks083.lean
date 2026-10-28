-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks083
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:19:55.552367+00:00
-- url     : https://prove2.me/submissions/5cedee3b-48ef-4173-84e1-681b34b8bd6c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks083
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks083
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
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

















































































































































































theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)

theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)










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



































































theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)
























































































































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









theorem valid5669 : plan5669.Valid := valid_step _ _ _ valid3361 (by decide +kernel)

theorem valid5670 : plan5670.Valid := valid_step _ _ _ valid3362 (by decide +kernel)

theorem valid5671 : plan5671.Valid := valid_step _ _ _ valid3363 (by decide +kernel)


















































































































































































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



































theorem valid6930 : plan6930.Valid := valid_step _ _ _ valid5669 (by decide +kernel)

theorem valid6931 : plan6931.Valid := valid_step _ _ _ valid5670 (by decide +kernel)

theorem valid6932 : plan6932.Valid := valid_step _ _ _ valid5671 (by decide +kernel)
























































































































































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
theorem t6_677choices : plan6930.choices=[2,5,3,6,6,7].map (options 6 4) := by rfl


theorem t6_677part0 : t6_677jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_677part1 : t6_677jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_677part2 : t6_677jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_677part3 : t6_677jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_677part4 : t6_677jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_677part5 : t6_677jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_677frontier : t6_677root.frontier 2=t6_677jobs := by rfl
theorem t6_677all : t6_677jobs.all (Job.check tree)=true := by
  simp only [t6_677jobs,List.all_append,List.all_nil,t6_677part0,t6_677part1,t6_677part2,t6_677part3,t6_677part4,t6_677part5,Bool.and_self]
theorem t6_677checked : Checked tree [2,5,3,6,6,7] := by
  refine ⟨plan6930,valid6930,t6_677choices,?_⟩
  exact check_of_frontier tree 2 t6_677root t6_677jobs t6_677frontier t6_677all
theorem t6_678choices : plan6931.choices=[2,5,3,6,6,10].map (options 6 4) := by rfl


theorem t6_678part0 : t6_678jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_678part1 : t6_678jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_678frontier : t6_678root.frontier 1=t6_678jobs := by rfl
theorem t6_678all : t6_678jobs.all (Job.check tree)=true := by
  simp only [t6_678jobs,List.all_append,List.all_nil,t6_678part0,t6_678part1,Bool.and_self]
theorem t6_678checked : Checked tree [2,5,3,6,6,10] := by
  refine ⟨plan6931,valid6931,t6_678choices,?_⟩
  exact check_of_frontier tree 1 t6_678root t6_678jobs t6_678frontier t6_678all
theorem t6_679choices : plan6932.choices=[2,5,3,6,7,7].map (options 6 4) := by rfl


theorem t6_679part0 : t6_679jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_679part1 : t6_679jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_679part2 : t6_679jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_679part3 : t6_679jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_679part4 : t6_679jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_679part5 : t6_679jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_679part6 : t6_679jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_679part7 : t6_679jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_679part8 : t6_679jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_679part9 : t6_679jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_679part10 : t6_679jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_679frontier : t6_679root.frontier 2=t6_679jobs := by rfl
theorem t6_679all : t6_679jobs.all (Job.check tree)=true := by
  simp only [t6_679jobs,List.all_append,List.all_nil,t6_679part0,t6_679part1,t6_679part2,t6_679part3,t6_679part4,t6_679part5,t6_679part6,t6_679part7,t6_679part8,t6_679part9,t6_679part10,Bool.and_self]
theorem t6_679checked : Checked tree [2,5,3,6,7,7] := by
  refine ⟨plan6932,valid6932,t6_679choices,?_⟩
  exact check_of_frontier tree 2 t6_679root t6_679jobs t6_679frontier t6_679all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks083 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_677checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_678checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_679checked⟩
