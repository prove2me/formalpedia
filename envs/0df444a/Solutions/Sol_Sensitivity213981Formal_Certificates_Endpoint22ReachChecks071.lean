-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks071
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:19:37.256155+00:00
-- url     : https://prove2.me/submissions/b90eaa1f-9ecd-4cd6-b3a4-80f1d3168b2b

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks071
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks071
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



















theorem valid1546 : plan1546.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1547 : plan1547.Valid := valid_step _ _ _ valid564 (by decide +kernel)










































































































































































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







































































































theorem valid3316 : plan3316.Valid := valid_step _ _ _ valid1546 (by decide +kernel)

theorem valid3317 : plan3317.Valid := valid_step _ _ _ valid1547 (by decide +kernel)






















































































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



































theorem valid5490 : plan5490.Valid := valid_step _ _ _ valid3316 (by decide +kernel)

theorem valid5491 : plan5491.Valid := valid_step _ _ _ valid3317 (by decide +kernel)


























































































































































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









































































































theorem valid6581 : plan6581.Valid := valid_step _ _ _ valid5490 (by decide +kernel)

theorem valid6582 : plan6582.Valid := valid_step _ _ _ valid5491 (by decide +kernel)




















































































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
theorem t6_645choices : plan6581.choices=[2,3,3,6,10,7].map (options 6 3) := by rfl


theorem t6_645part0 : t6_645jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_645part1 : t6_645jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_645part2 : t6_645jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_645part3 : t6_645jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_645part4 : t6_645jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_645part5 : t6_645jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_645part6 : t6_645jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_645part7 : t6_645jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_645part8 : t6_645jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_645part9 : t6_645jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_645part10 : t6_645jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_645part11 : t6_645jobs11.all (Job.check tree)=true := by decide +kernel

theorem t6_645part12 : t6_645jobs12.all (Job.check tree)=true := by decide +kernel

theorem t6_645part13 : t6_645jobs13.all (Job.check tree)=true := by decide +kernel

theorem t6_645part14 : t6_645jobs14.all (Job.check tree)=true := by decide +kernel

theorem t6_645part15 : t6_645jobs15.all (Job.check tree)=true := by decide +kernel

theorem t6_645part16 : t6_645jobs16.all (Job.check tree)=true := by decide +kernel

theorem t6_645part17 : t6_645jobs17.all (Job.check tree)=true := by decide +kernel

theorem t6_645frontier : t6_645root.frontier 2=t6_645jobs := by rfl
theorem t6_645all : t6_645jobs.all (Job.check tree)=true := by
  simp only [t6_645jobs,List.all_append,List.all_nil,t6_645part0,t6_645part1,t6_645part2,t6_645part3,t6_645part4,t6_645part5,t6_645part6,t6_645part7,t6_645part8,t6_645part9,t6_645part10,t6_645part11,t6_645part12,t6_645part13,t6_645part14,t6_645part15,t6_645part16,t6_645part17,Bool.and_self]
theorem t6_645checked : Checked tree [2,3,3,6,10,7] := by
  refine ⟨plan6581,valid6581,t6_645choices,?_⟩
  exact check_of_frontier tree 2 t6_645root t6_645jobs t6_645frontier t6_645all
theorem t6_646choices : plan6582.choices=[2,3,3,6,10,10].map (options 6 3) := by rfl


theorem t6_646part0 : t6_646jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_646part1 : t6_646jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_646part2 : t6_646jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_646part3 : t6_646jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_646frontier : t6_646root.frontier 2=t6_646jobs := by rfl
theorem t6_646all : t6_646jobs.all (Job.check tree)=true := by
  simp only [t6_646jobs,List.all_append,List.all_nil,t6_646part0,t6_646part1,t6_646part2,t6_646part3,Bool.and_self]
theorem t6_646checked : Checked tree [2,3,3,6,10,10] := by
  refine ⟨plan6582,valid6582,t6_646choices,?_⟩
  exact check_of_frontier tree 2 t6_646root t6_646jobs t6_646frontier t6_646all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks071 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_646checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_645checked⟩
