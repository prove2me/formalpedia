-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks114
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:41:38.418416+00:00
-- url     : https://prove2.me/submissions/90212533-5e7d-4438-96dd-36b5e048c685

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks114
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks114
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

























































theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)













































theorem valid3508 : plan3508.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3509 : plan3509.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3510 : plan3510.Valid := valid_step _ _ _ valid1606 (by decide +kernel)




















































































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













































































theorem valid5895 : plan5895.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5896 : plan5896.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5897 : plan5897.Valid := valid_step _ _ _ valid3510 (by decide +kernel)

theorem valid5898 : plan5898.Valid := valid_step _ _ _ valid3485 (by decide +kernel)












































































































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

































































theorem valid7425 : plan7425.Valid := valid_step _ _ _ valid5895 (by decide +kernel)

theorem valid7426 : plan7426.Valid := valid_step _ _ _ valid5896 (by decide +kernel)

theorem valid7427 : plan7427.Valid := valid_step _ _ _ valid5897 (by decide +kernel)

theorem valid7428 : plan7428.Valid := valid_step _ _ _ valid5898 (by decide +kernel)
























































































































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
theorem t6_880choices : plan7425.choices=[3,6,10,10,7,7].map (options 6 5) := by rfl


theorem t6_880part0 : t6_880jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_880part1 : t6_880jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_880part2 : t6_880jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_880part3 : t6_880jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_880part4 : t6_880jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_880part5 : t6_880jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_880part6 : t6_880jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_880part7 : t6_880jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_880part8 : t6_880jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_880frontier : t6_880root.frontier 2=t6_880jobs := by rfl
theorem t6_880all : t6_880jobs.all (Job.check tree)=true := by
  simp only [t6_880jobs,List.all_append,List.all_nil,t6_880part0,t6_880part1,t6_880part2,t6_880part3,t6_880part4,t6_880part5,t6_880part6,t6_880part7,t6_880part8,Bool.and_self]
theorem t6_880checked : Checked tree [3,6,10,10,7,7] := by
  refine ⟨plan7425,valid7425,t6_880choices,?_⟩
  exact check_of_frontier tree 2 t6_880root t6_880jobs t6_880frontier t6_880all
theorem t6_881choices : plan7426.choices=[3,6,10,10,10,7].map (options 6 5) := by rfl


theorem t6_881part0 : t6_881jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_881part1 : t6_881jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_881part2 : t6_881jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_881part3 : t6_881jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_881frontier : t6_881root.frontier 2=t6_881jobs := by rfl
theorem t6_881all : t6_881jobs.all (Job.check tree)=true := by
  simp only [t6_881jobs,List.all_append,List.all_nil,t6_881part0,t6_881part1,t6_881part2,t6_881part3,Bool.and_self]
theorem t6_881checked : Checked tree [3,6,10,10,10,7] := by
  refine ⟨plan7426,valid7426,t6_881choices,?_⟩
  exact check_of_frontier tree 2 t6_881root t6_881jobs t6_881frontier t6_881all
theorem t6_882choices : plan7427.choices=[3,6,10,10,10,10].map (options 6 5) := by rfl


theorem t6_882part0 : t6_882jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_882frontier : t6_882root.frontier 0=t6_882jobs := by rfl
theorem t6_882all : t6_882jobs.all (Job.check tree)=true := by
  simp only [t6_882jobs,List.all_append,List.all_nil,t6_882part0,Bool.and_self]
theorem t6_882checked : Checked tree [3,6,10,10,10,10] := by
  refine ⟨plan7427,valid7427,t6_882choices,?_⟩
  exact check_of_frontier tree 0 t6_882root t6_882jobs t6_882frontier t6_882all
theorem t6_883choices : plan7428.choices=[3,7,7,7,7,7].map (options 6 5) := by rfl


theorem t6_883part0 : t6_883jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_883part1 : t6_883jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_883part2 : t6_883jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_883frontier : t6_883root.frontier 1=t6_883jobs := by rfl
theorem t6_883all : t6_883jobs.all (Job.check tree)=true := by
  simp only [t6_883jobs,List.all_append,List.all_nil,t6_883part0,t6_883part1,t6_883part2,Bool.and_self]
theorem t6_883checked : Checked tree [3,7,7,7,7,7] := by
  refine ⟨plan7428,valid7428,t6_883choices,?_⟩
  exact check_of_frontier tree 1 t6_883root t6_883jobs t6_883frontier t6_883all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks114 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_880checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_881checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_882checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_883checked⟩
