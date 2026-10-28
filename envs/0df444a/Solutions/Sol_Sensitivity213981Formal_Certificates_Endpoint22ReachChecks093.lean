-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks093
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:34:05.565173+00:00
-- url     : https://prove2.me/submissions/1201ec59-8031-4f94-b535-9019714ef1f9

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks093
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks093
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

















































































































theorem valid5721 : plan5721.Valid := valid_step _ _ _ valid3361 (by decide +kernel)

theorem valid5722 : plan5722.Valid := valid_step _ _ _ valid3362 (by decide +kernel)

theorem valid5723 : plan5723.Valid := valid_step _ _ _ valid3363 (by decide +kernel)










































































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





















































































theorem valid6955 : plan6955.Valid := valid_step _ _ _ valid5721 (by decide +kernel)

theorem valid6956 : plan6956.Valid := valid_step _ _ _ valid5722 (by decide +kernel)

theorem valid6957 : plan6957.Valid := valid_step _ _ _ valid5723 (by decide +kernel)






































































































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
theorem t6_780choices : plan6955.choices=[2,9,3,6,6,7].map (options 6 4) := by rfl


theorem t6_780part0 : t6_780jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_780part1 : t6_780jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_780part2 : t6_780jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_780part3 : t6_780jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_780part4 : t6_780jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_780part5 : t6_780jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_780frontier : t6_780root.frontier 2=t6_780jobs := by rfl
theorem t6_780all : t6_780jobs.all (Job.check tree)=true := by
  simp only [t6_780jobs,List.all_append,List.all_nil,t6_780part0,t6_780part1,t6_780part2,t6_780part3,t6_780part4,t6_780part5,Bool.and_self]
theorem t6_780checked : Checked tree [2,9,3,6,6,7] := by
  refine ⟨plan6955,valid6955,t6_780choices,?_⟩
  exact check_of_frontier tree 2 t6_780root t6_780jobs t6_780frontier t6_780all
theorem t6_781choices : plan6956.choices=[2,9,3,6,6,10].map (options 6 4) := by rfl


theorem t6_781part0 : t6_781jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_781part1 : t6_781jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_781frontier : t6_781root.frontier 1=t6_781jobs := by rfl
theorem t6_781all : t6_781jobs.all (Job.check tree)=true := by
  simp only [t6_781jobs,List.all_append,List.all_nil,t6_781part0,t6_781part1,Bool.and_self]
theorem t6_781checked : Checked tree [2,9,3,6,6,10] := by
  refine ⟨plan6956,valid6956,t6_781choices,?_⟩
  exact check_of_frontier tree 1 t6_781root t6_781jobs t6_781frontier t6_781all
theorem t6_782choices : plan6957.choices=[2,9,3,6,7,7].map (options 6 4) := by rfl


theorem t6_782part0 : t6_782jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_782part1 : t6_782jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_782part2 : t6_782jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_782part3 : t6_782jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_782part4 : t6_782jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_782part5 : t6_782jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_782part6 : t6_782jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_782part7 : t6_782jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_782part8 : t6_782jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_782part9 : t6_782jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_782part10 : t6_782jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_782frontier : t6_782root.frontier 2=t6_782jobs := by rfl
theorem t6_782all : t6_782jobs.all (Job.check tree)=true := by
  simp only [t6_782jobs,List.all_append,List.all_nil,t6_782part0,t6_782part1,t6_782part2,t6_782part3,t6_782part4,t6_782part5,t6_782part6,t6_782part7,t6_782part8,t6_782part9,t6_782part10,Bool.and_self]
theorem t6_782checked : Checked tree [2,9,3,6,7,7] := by
  refine ⟨plan6957,valid6957,t6_782choices,?_⟩
  exact check_of_frontier tree 2 t6_782root t6_782jobs t6_782frontier t6_782all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks093 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_780checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_781checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_782checked⟩
