-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks131
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:49:54.09749+00:00
-- url     : https://prove2.me/submissions/aa26732a-93d8-4cbb-84dc-b5ce5a3b773b

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks131
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks131
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
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



































































































theorem valid7538 : plan7538.Valid := valid_step _ _ _ valid5778 (by decide +kernel)

theorem valid7539 : plan7539.Valid := valid_step _ _ _ valid5779 (by decide +kernel)

theorem valid7540 : plan7540.Valid := valid_step _ _ _ valid5780 (by decide +kernel)

theorem valid7541 : plan7541.Valid := valid_step _ _ _ valid5781 (by decide +kernel)

theorem valid7542 : plan7542.Valid := valid_step _ _ _ valid5782 (by decide +kernel)




















































































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
theorem t6_1215choices : plan7538.choices=[5,3,6,10,10,7].map (options 6 5) := by rfl


theorem t6_1215part0 : t6_1215jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1215part1 : t6_1215jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1215part2 : t6_1215jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1215part3 : t6_1215jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1215frontier : t6_1215root.frontier 2=t6_1215jobs := by rfl
theorem t6_1215all : t6_1215jobs.all (Job.check tree)=true := by
  simp only [t6_1215jobs,List.all_append,List.all_nil,t6_1215part0,t6_1215part1,t6_1215part2,t6_1215part3,Bool.and_self]
theorem t6_1215checked : Checked tree [5,3,6,10,10,7] := by
  refine ⟨plan7538,valid7538,t6_1215choices,?_⟩
  exact check_of_frontier tree 2 t6_1215root t6_1215jobs t6_1215frontier t6_1215all
theorem t6_1216choices : plan7539.choices=[5,3,6,10,10,10].map (options 6 5) := by rfl


theorem t6_1216part0 : t6_1216jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1216frontier : t6_1216root.frontier 0=t6_1216jobs := by rfl
theorem t6_1216all : t6_1216jobs.all (Job.check tree)=true := by
  simp only [t6_1216jobs,List.all_append,List.all_nil,t6_1216part0,Bool.and_self]
theorem t6_1216checked : Checked tree [5,3,6,10,10,10] := by
  refine ⟨plan7539,valid7539,t6_1216choices,?_⟩
  exact check_of_frontier tree 0 t6_1216root t6_1216jobs t6_1216frontier t6_1216all
theorem t6_1217choices : plan7540.choices=[5,3,7,7,7,7].map (options 6 5) := by rfl


theorem t6_1217part0 : t6_1217jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1217part1 : t6_1217jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1217part2 : t6_1217jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1217part3 : t6_1217jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1217frontier : t6_1217root.frontier 1=t6_1217jobs := by rfl
theorem t6_1217all : t6_1217jobs.all (Job.check tree)=true := by
  simp only [t6_1217jobs,List.all_append,List.all_nil,t6_1217part0,t6_1217part1,t6_1217part2,t6_1217part3,Bool.and_self]
theorem t6_1217checked : Checked tree [5,3,7,7,7,7] := by
  refine ⟨plan7540,valid7540,t6_1217choices,?_⟩
  exact check_of_frontier tree 1 t6_1217root t6_1217jobs t6_1217frontier t6_1217all
theorem t6_1218choices : plan7541.choices=[5,3,10,7,7,7].map (options 6 5) := by rfl


theorem t6_1218part0 : t6_1218jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1218part1 : t6_1218jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1218part2 : t6_1218jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1218part3 : t6_1218jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1218part4 : t6_1218jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1218part5 : t6_1218jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1218part6 : t6_1218jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_1218frontier : t6_1218root.frontier 2=t6_1218jobs := by rfl
theorem t6_1218all : t6_1218jobs.all (Job.check tree)=true := by
  simp only [t6_1218jobs,List.all_append,List.all_nil,t6_1218part0,t6_1218part1,t6_1218part2,t6_1218part3,t6_1218part4,t6_1218part5,t6_1218part6,Bool.and_self]
theorem t6_1218checked : Checked tree [5,3,10,7,7,7] := by
  refine ⟨plan7541,valid7541,t6_1218choices,?_⟩
  exact check_of_frontier tree 2 t6_1218root t6_1218jobs t6_1218frontier t6_1218all
theorem t6_1219choices : plan7542.choices=[5,3,10,10,7,7].map (options 6 5) := by rfl


theorem t6_1219part0 : t6_1219jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1219part1 : t6_1219jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1219part2 : t6_1219jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1219part3 : t6_1219jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1219part4 : t6_1219jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1219frontier : t6_1219root.frontier 2=t6_1219jobs := by rfl
theorem t6_1219all : t6_1219jobs.all (Job.check tree)=true := by
  simp only [t6_1219jobs,List.all_append,List.all_nil,t6_1219part0,t6_1219part1,t6_1219part2,t6_1219part3,t6_1219part4,Bool.and_self]
theorem t6_1219checked : Checked tree [5,3,10,10,7,7] := by
  refine ⟨plan7542,valid7542,t6_1219choices,?_⟩
  exact check_of_frontier tree 2 t6_1219root t6_1219jobs t6_1219frontier t6_1219all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks131 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1219checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1215checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1216checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1217checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1218checked⟩
