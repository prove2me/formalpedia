-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks147
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:57:25.851008+00:00
-- url     : https://prove2.me/submissions/09c48735-5720-4745-b5bc-0c6b7afbcbfa

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks147
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks147
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
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













































































































theorem valid5623 : plan5623.Valid := valid_step _ _ _ valid3361 (by decide +kernel)

theorem valid5624 : plan5624.Valid := valid_step _ _ _ valid3362 (by decide +kernel)

theorem valid5625 : plan5625.Valid := valid_step _ _ _ valid3363 (by decide +kernel)














































































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















































theorem valid7128 : plan7128.Valid := valid_step _ _ _ valid5623 (by decide +kernel)

theorem valid7129 : plan7129.Valid := valid_step _ _ _ valid5624 (by decide +kernel)

theorem valid7130 : plan7130.Valid := valid_step _ _ _ valid5625 (by decide +kernel)












































































































































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
theorem t6_1686choices : plan7128.choices=[9,3,3,6,6,7].map (options 6 4) := by rfl


theorem t6_1686part0 : t6_1686jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1686part1 : t6_1686jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1686part2 : t6_1686jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1686part3 : t6_1686jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1686part4 : t6_1686jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1686part5 : t6_1686jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1686frontier : t6_1686root.frontier 2=t6_1686jobs := by rfl
theorem t6_1686all : t6_1686jobs.all (Job.check tree)=true := by
  simp only [t6_1686jobs,List.all_append,List.all_nil,t6_1686part0,t6_1686part1,t6_1686part2,t6_1686part3,t6_1686part4,t6_1686part5,Bool.and_self]
theorem t6_1686checked : Checked tree [9,3,3,6,6,7] := by
  refine ⟨plan7128,valid7128,t6_1686choices,?_⟩
  exact check_of_frontier tree 2 t6_1686root t6_1686jobs t6_1686frontier t6_1686all
theorem t6_1687choices : plan7129.choices=[9,3,3,6,6,10].map (options 6 4) := by rfl


theorem t6_1687part0 : t6_1687jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1687part1 : t6_1687jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1687part2 : t6_1687jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1687part3 : t6_1687jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1687frontier : t6_1687root.frontier 1=t6_1687jobs := by rfl
theorem t6_1687all : t6_1687jobs.all (Job.check tree)=true := by
  simp only [t6_1687jobs,List.all_append,List.all_nil,t6_1687part0,t6_1687part1,t6_1687part2,t6_1687part3,Bool.and_self]
theorem t6_1687checked : Checked tree [9,3,3,6,6,10] := by
  refine ⟨plan7129,valid7129,t6_1687choices,?_⟩
  exact check_of_frontier tree 1 t6_1687root t6_1687jobs t6_1687frontier t6_1687all
theorem t6_1688choices : plan7130.choices=[9,3,3,6,7,7].map (options 6 4) := by rfl


theorem t6_1688part0 : t6_1688jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1688part1 : t6_1688jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1688part2 : t6_1688jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1688part3 : t6_1688jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1688part4 : t6_1688jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1688part5 : t6_1688jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1688part6 : t6_1688jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_1688part7 : t6_1688jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_1688part8 : t6_1688jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_1688part9 : t6_1688jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_1688frontier : t6_1688root.frontier 2=t6_1688jobs := by rfl
theorem t6_1688all : t6_1688jobs.all (Job.check tree)=true := by
  simp only [t6_1688jobs,List.all_append,List.all_nil,t6_1688part0,t6_1688part1,t6_1688part2,t6_1688part3,t6_1688part4,t6_1688part5,t6_1688part6,t6_1688part7,t6_1688part8,t6_1688part9,Bool.and_self]
theorem t6_1688checked : Checked tree [9,3,3,6,7,7] := by
  refine ⟨plan7130,valid7130,t6_1688choices,?_⟩
  exact check_of_frontier tree 2 t6_1688root t6_1688jobs t6_1688frontier t6_1688all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks147 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1688checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1686checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1687checked⟩
