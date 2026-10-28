-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks152
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:01:02.844508+00:00
-- url     : https://prove2.me/submissions/fb7ae05f-3d8a-48bd-afcb-c8f9db04cd4e

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks152
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks152
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans080
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

theorem valid135 : plan135.Valid := valid_step _ _ _ valid0 (by decide +kernel)


















































































































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

theorem valid579 : plan579.Valid := valid_step _ _ _ valid134 (by decide +kernel)

theorem valid580 : plan580.Valid := valid_step _ _ _ valid135 (by decide +kernel)
























































































































































































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









theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1606 : plan1606.Valid := valid_step _ _ _ valid580 (by decide +kernel)




















































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





















































theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)











































theorem valid3507 : plan3507.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3508 : plan3508.Valid := valid_step _ _ _ valid1604 (by decide +kernel)
























































































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



































theorem valid5778 : plan5778.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5779 : plan5779.Valid := valid_step _ _ _ valid3484 (by decide +kernel)

theorem valid5780 : plan5780.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5781 : plan5781.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5782 : plan5782.Valid := valid_step _ _ _ valid3508 (by decide +kernel)




















































































































































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

theorem valid7681 : plan7681.Valid := valid_step _ _ _ valid5779 (by decide +kernel)

theorem valid7682 : plan7682.Valid := valid_step _ _ _ valid5780 (by decide +kernel)

theorem valid7683 : plan7683.Valid := valid_step _ _ _ valid5781 (by decide +kernel)

theorem valid7684 : plan7684.Valid := valid_step _ _ _ valid5782 (by decide +kernel)
























































































































































































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































































































































































































theorem valid7680 : plan7680.Valid := valid_step _ _ _ valid5778 (by decide +kernel)
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
theorem t6_1703choices : plan7680.choices=[9,3,6,10,10,7].map (options 6 5) := by rfl


theorem t6_1703part0 : t6_1703jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1703part1 : t6_1703jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1703part2 : t6_1703jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1703part3 : t6_1703jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1703frontier : t6_1703root.frontier 2=t6_1703jobs := by rfl
theorem t6_1703all : t6_1703jobs.all (Job.check tree)=true := by
  simp only [t6_1703jobs,List.all_append,List.all_nil,t6_1703part0,t6_1703part1,t6_1703part2,t6_1703part3,Bool.and_self]
theorem t6_1703checked : Checked tree [9,3,6,10,10,7] := by
  refine ⟨plan7680,valid7680,t6_1703choices,?_⟩
  exact check_of_frontier tree 2 t6_1703root t6_1703jobs t6_1703frontier t6_1703all
theorem t6_1704choices : plan7681.choices=[9,3,6,10,10,10].map (options 6 5) := by rfl


theorem t6_1704part0 : t6_1704jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1704frontier : t6_1704root.frontier 0=t6_1704jobs := by rfl
theorem t6_1704all : t6_1704jobs.all (Job.check tree)=true := by
  simp only [t6_1704jobs,List.all_append,List.all_nil,t6_1704part0,Bool.and_self]
theorem t6_1704checked : Checked tree [9,3,6,10,10,10] := by
  refine ⟨plan7681,valid7681,t6_1704choices,?_⟩
  exact check_of_frontier tree 0 t6_1704root t6_1704jobs t6_1704frontier t6_1704all
theorem t6_1705choices : plan7682.choices=[9,3,7,7,7,7].map (options 6 5) := by rfl


theorem t6_1705part0 : t6_1705jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1705part1 : t6_1705jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1705part2 : t6_1705jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1705part3 : t6_1705jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1705frontier : t6_1705root.frontier 1=t6_1705jobs := by rfl
theorem t6_1705all : t6_1705jobs.all (Job.check tree)=true := by
  simp only [t6_1705jobs,List.all_append,List.all_nil,t6_1705part0,t6_1705part1,t6_1705part2,t6_1705part3,Bool.and_self]
theorem t6_1705checked : Checked tree [9,3,7,7,7,7] := by
  refine ⟨plan7682,valid7682,t6_1705choices,?_⟩
  exact check_of_frontier tree 1 t6_1705root t6_1705jobs t6_1705frontier t6_1705all
theorem t6_1706choices : plan7683.choices=[9,3,10,7,7,7].map (options 6 5) := by rfl


theorem t6_1706part0 : t6_1706jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1706part1 : t6_1706jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1706part2 : t6_1706jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1706part3 : t6_1706jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1706part4 : t6_1706jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1706part5 : t6_1706jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1706part6 : t6_1706jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_1706frontier : t6_1706root.frontier 2=t6_1706jobs := by rfl
theorem t6_1706all : t6_1706jobs.all (Job.check tree)=true := by
  simp only [t6_1706jobs,List.all_append,List.all_nil,t6_1706part0,t6_1706part1,t6_1706part2,t6_1706part3,t6_1706part4,t6_1706part5,t6_1706part6,Bool.and_self]
theorem t6_1706checked : Checked tree [9,3,10,7,7,7] := by
  refine ⟨plan7683,valid7683,t6_1706choices,?_⟩
  exact check_of_frontier tree 2 t6_1706root t6_1706jobs t6_1706frontier t6_1706all
theorem t6_1707choices : plan7684.choices=[9,3,10,10,7,7].map (options 6 5) := by rfl


theorem t6_1707part0 : t6_1707jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1707part1 : t6_1707jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1707part2 : t6_1707jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1707part3 : t6_1707jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1707part4 : t6_1707jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1707frontier : t6_1707root.frontier 2=t6_1707jobs := by rfl
theorem t6_1707all : t6_1707jobs.all (Job.check tree)=true := by
  simp only [t6_1707jobs,List.all_append,List.all_nil,t6_1707part0,t6_1707part1,t6_1707part2,t6_1707part3,t6_1707part4,Bool.and_self]
theorem t6_1707checked : Checked tree [9,3,10,10,7,7] := by
  refine ⟨plan7684,valid7684,t6_1707choices,?_⟩
  exact check_of_frontier tree 2 t6_1707root t6_1707jobs t6_1707frontier t6_1707all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks152 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1707checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1703checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1704checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1705checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1706checked⟩
