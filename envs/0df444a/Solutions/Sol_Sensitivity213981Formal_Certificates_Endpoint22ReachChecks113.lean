-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks113
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:40:53.128111+00:00
-- url     : https://prove2.me/submissions/32fb2a9c-4f78-481c-8948-0f884c89db3c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks113
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks113
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
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





























































































































theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)


































































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

























































theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)











































theorem valid3507 : plan3507.Valid := valid_step _ _ _ valid1599 (by decide +kernel)


























































































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









































































theorem valid5893 : plan5893.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5894 : plan5894.Valid := valid_step _ _ _ valid3507 (by decide +kernel)




















































































































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





























































theorem valid7423 : plan7423.Valid := valid_step _ _ _ valid5893 (by decide +kernel)

theorem valid7424 : plan7424.Valid := valid_step _ _ _ valid5894 (by decide +kernel)
































































































































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
theorem t6_878choices : plan7423.choices=[3,6,7,7,7,7].map (options 6 5) := by rfl


theorem t6_878part0 : t6_878jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_878part1 : t6_878jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_878part2 : t6_878jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_878part3 : t6_878jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_878part4 : t6_878jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_878part5 : t6_878jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_878frontier : t6_878root.frontier 2=t6_878jobs := by rfl
theorem t6_878all : t6_878jobs.all (Job.check tree)=true := by
  simp only [t6_878jobs,List.all_append,List.all_nil,t6_878part0,t6_878part1,t6_878part2,t6_878part3,t6_878part4,t6_878part5,Bool.and_self]
theorem t6_878checked : Checked tree [3,6,7,7,7,7] := by
  refine ⟨plan7423,valid7423,t6_878choices,?_⟩
  exact check_of_frontier tree 2 t6_878root t6_878jobs t6_878frontier t6_878all
theorem t6_879choices : plan7424.choices=[3,6,10,7,7,7].map (options 6 5) := by rfl


theorem t6_879part0 : t6_879jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_879part1 : t6_879jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_879part2 : t6_879jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_879part3 : t6_879jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_879part4 : t6_879jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_879part5 : t6_879jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_879part6 : t6_879jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_879part7 : t6_879jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_879part8 : t6_879jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_879part9 : t6_879jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_879part10 : t6_879jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_879frontier : t6_879root.frontier 2=t6_879jobs := by rfl
theorem t6_879all : t6_879jobs.all (Job.check tree)=true := by
  simp only [t6_879jobs,List.all_append,List.all_nil,t6_879part0,t6_879part1,t6_879part2,t6_879part3,t6_879part4,t6_879part5,t6_879part6,t6_879part7,t6_879part8,t6_879part9,t6_879part10,Bool.and_self]
theorem t6_879checked : Checked tree [3,6,10,7,7,7] := by
  refine ⟨plan7424,valid7424,t6_879choices,?_⟩
  exact check_of_frontier tree 2 t6_879root t6_879jobs t6_879frontier t6_879all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks113 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_878checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_879checked⟩
