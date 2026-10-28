-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks084
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:25:31.739266+00:00
-- url     : https://prove2.me/submissions/5ee1d77f-adfe-4844-8d2f-882d0c870e0c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks084
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









































































theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)

theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)


















































































































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















theorem valid5672 : plan5672.Valid := valid_step _ _ _ valid3364 (by decide +kernel)

theorem valid5673 : plan5673.Valid := valid_step _ _ _ valid3365 (by decide +kernel)

theorem valid5674 : plan5674.Valid := valid_step _ _ _ valid3366 (by decide +kernel)












































































































































































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









































theorem valid6933 : plan6933.Valid := valid_step _ _ _ valid5672 (by decide +kernel)

theorem valid6934 : plan6934.Valid := valid_step _ _ _ valid5673 (by decide +kernel)

theorem valid6935 : plan6935.Valid := valid_step _ _ _ valid5674 (by decide +kernel)


















































































































































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
theorem t6_680choices : plan6933.choices=[2,5,3,6,10,7].map (options 6 4) := by rfl


theorem t6_680part0 : t6_680jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_680part1 : t6_680jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_680part2 : t6_680jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_680part3 : t6_680jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_680part4 : t6_680jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_680part5 : t6_680jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_680part6 : t6_680jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_680part7 : t6_680jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_680part8 : t6_680jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_680part9 : t6_680jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_680part10 : t6_680jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_680frontier : t6_680root.frontier 2=t6_680jobs := by rfl
theorem t6_680all : t6_680jobs.all (Job.check tree)=true := by
  simp only [t6_680jobs,List.all_append,List.all_nil,t6_680part0,t6_680part1,t6_680part2,t6_680part3,t6_680part4,t6_680part5,t6_680part6,t6_680part7,t6_680part8,t6_680part9,t6_680part10,Bool.and_self]
theorem t6_680checked : Checked tree [2,5,3,6,10,7] := by
  refine ⟨plan6933,valid6933,t6_680choices,?_⟩
  exact check_of_frontier tree 2 t6_680root t6_680jobs t6_680frontier t6_680all
theorem t6_681choices : plan6934.choices=[2,5,3,6,10,10].map (options 6 4) := by rfl


theorem t6_681part0 : t6_681jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_681part1 : t6_681jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_681frontier : t6_681root.frontier 1=t6_681jobs := by rfl
theorem t6_681all : t6_681jobs.all (Job.check tree)=true := by
  simp only [t6_681jobs,List.all_append,List.all_nil,t6_681part0,t6_681part1,Bool.and_self]
theorem t6_681checked : Checked tree [2,5,3,6,10,10] := by
  refine ⟨plan6934,valid6934,t6_681choices,?_⟩
  exact check_of_frontier tree 1 t6_681root t6_681jobs t6_681frontier t6_681all
theorem t6_682choices : plan6935.choices=[2,5,3,7,7,7].map (options 6 4) := by rfl


theorem t6_682part0 : t6_682jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_682part1 : t6_682jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_682part2 : t6_682jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_682part3 : t6_682jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_682part4 : t6_682jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_682part5 : t6_682jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_682frontier : t6_682root.frontier 2=t6_682jobs := by rfl
theorem t6_682all : t6_682jobs.all (Job.check tree)=true := by
  simp only [t6_682jobs,List.all_append,List.all_nil,t6_682part0,t6_682part1,t6_682part2,t6_682part3,t6_682part4,t6_682part5,Bool.and_self]
theorem t6_682checked : Checked tree [2,5,3,7,7,7] := by
  refine ⟨plan6935,valid6935,t6_682choices,?_⟩
  exact check_of_frontier tree 2 t6_682root t6_682jobs t6_682frontier t6_682all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks084 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_680checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_681checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_682checked⟩
