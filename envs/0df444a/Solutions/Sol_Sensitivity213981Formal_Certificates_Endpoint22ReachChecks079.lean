-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks079
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:19:28.067891+00:00
-- url     : https://prove2.me/submissions/6d0c66f7-6dfe-4b3f-98ca-5204dcf1c909

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks079
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks079
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
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































































































theorem valid3408 : plan3408.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

















































theorem valid3433 : plan3433.Valid := valid_step _ _ _ valid1575 (by decide +kernel)














































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



















































































































































theorem valid5642 : plan5642.Valid := valid_step _ _ _ valid3408 (by decide +kernel)

theorem valid5643 : plan5643.Valid := valid_step _ _ _ valid3433 (by decide +kernel)










































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























theorem valid6924 : plan6924.Valid := valid_step _ _ _ valid5642 (by decide +kernel)

theorem valid6925 : plan6925.Valid := valid_step _ _ _ valid5643 (by decide +kernel)






































































































































































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
theorem t6_661choices : plan6924.choices=[2,3,7,7,7,7].map (options 6 4) := by rfl


theorem t6_661part0 : t6_661jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_661part1 : t6_661jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_661part2 : t6_661jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_661part3 : t6_661jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_661part4 : t6_661jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_661part5 : t6_661jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_661part6 : t6_661jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_661frontier : t6_661root.frontier 2=t6_661jobs := by rfl
theorem t6_661all : t6_661jobs.all (Job.check tree)=true := by
  simp only [t6_661jobs,List.all_append,List.all_nil,t6_661part0,t6_661part1,t6_661part2,t6_661part3,t6_661part4,t6_661part5,t6_661part6,Bool.and_self]
theorem t6_661checked : Checked tree [2,3,7,7,7,7] := by
  refine ⟨plan6924,valid6924,t6_661choices,?_⟩
  exact check_of_frontier tree 2 t6_661root t6_661jobs t6_661frontier t6_661all
theorem t6_662choices : plan6925.choices=[2,3,10,7,7,7].map (options 6 4) := by rfl


theorem t6_662part0 : t6_662jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_662part1 : t6_662jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_662part2 : t6_662jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_662part3 : t6_662jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_662part4 : t6_662jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_662part5 : t6_662jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_662part6 : t6_662jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_662part7 : t6_662jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_662part8 : t6_662jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_662part9 : t6_662jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_662frontier : t6_662root.frontier 3=t6_662jobs := by rfl
theorem t6_662all : t6_662jobs.all (Job.check tree)=true := by
  simp only [t6_662jobs,List.all_append,List.all_nil,t6_662part0,t6_662part1,t6_662part2,t6_662part3,t6_662part4,t6_662part5,t6_662part6,t6_662part7,t6_662part8,t6_662part9,Bool.and_self]
theorem t6_662checked : Checked tree [2,3,10,7,7,7] := by
  refine ⟨plan6925,valid6925,t6_662choices,?_⟩
  exact check_of_frontier tree 3 t6_662root t6_662jobs t6_662frontier t6_662all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks079 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_662checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_661checked⟩
