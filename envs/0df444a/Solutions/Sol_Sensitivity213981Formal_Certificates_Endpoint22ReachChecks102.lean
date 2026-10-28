-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks102
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:39:30.238985+00:00
-- url     : https://prove2.me/submissions/47235685-e2ac-4647-a075-98e5ffa59a3c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks102
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks102
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























theorem valid1548 : plan1548.Valid := valid_step _ _ _ valid562 (by decide +kernel)









theorem valid1553 : plan1553.Valid := valid_step _ _ _ valid562 (by decide +kernel)






























































































































































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











































































































theorem valid3318 : plan3318.Valid := valid_step _ _ _ valid1548 (by decide +kernel)

theorem valid3319 : plan3319.Valid := valid_step _ _ _ valid1553 (by decide +kernel)


















































































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







































theorem valid5492 : plan5492.Valid := valid_step _ _ _ valid3318 (by decide +kernel)

theorem valid5493 : plan5493.Valid := valid_step _ _ _ valid3319 (by decide +kernel)






















































































































































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











































































































































































theorem valid6614 : plan6614.Valid := valid_step _ _ _ valid5492 (by decide +kernel)

theorem valid6615 : plan6615.Valid := valid_step _ _ _ valid5493 (by decide +kernel)


















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
theorem t6_849choices : plan6614.choices=[3,3,3,7,7,7].map (options 6 3) := by rfl


theorem t6_849part0 : t6_849jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_849part1 : t6_849jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_849part2 : t6_849jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_849part3 : t6_849jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_849part4 : t6_849jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_849frontier : t6_849root.frontier 1=t6_849jobs := by rfl
theorem t6_849all : t6_849jobs.all (Job.check tree)=true := by
  simp only [t6_849jobs,List.all_append,List.all_nil,t6_849part0,t6_849part1,t6_849part2,t6_849part3,t6_849part4,Bool.and_self]
theorem t6_849checked : Checked tree [3,3,3,7,7,7] := by
  refine ⟨plan6614,valid6614,t6_849choices,?_⟩
  exact check_of_frontier tree 1 t6_849root t6_849jobs t6_849frontier t6_849all
theorem t6_850choices : plan6615.choices=[3,3,3,10,7,7].map (options 6 3) := by rfl


theorem t6_850part0 : t6_850jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_850part1 : t6_850jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_850part2 : t6_850jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_850part3 : t6_850jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_850part4 : t6_850jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_850part5 : t6_850jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_850part6 : t6_850jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_850part7 : t6_850jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_850part8 : t6_850jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_850frontier : t6_850root.frontier 2=t6_850jobs := by rfl
theorem t6_850all : t6_850jobs.all (Job.check tree)=true := by
  simp only [t6_850jobs,List.all_append,List.all_nil,t6_850part0,t6_850part1,t6_850part2,t6_850part3,t6_850part4,t6_850part5,t6_850part6,t6_850part7,t6_850part8,Bool.and_self]
theorem t6_850checked : Checked tree [3,3,3,10,7,7] := by
  refine ⟨plan6615,valid6615,t6_850choices,?_⟩
  exact check_of_frontier tree 2 t6_850root t6_850jobs t6_850frontier t6_850all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks102 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_849checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_850checked⟩
