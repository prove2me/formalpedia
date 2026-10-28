-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks151
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:00:55.567998+00:00
-- url     : https://prove2.me/submissions/f55ffb8d-82bb-4ede-9886-359a950ef641

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks151
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks151
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
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

























































































































theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)









theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)
























































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













































theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)












































































































































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



























theorem valid5774 : plan5774.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5775 : plan5775.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5776 : plan5776.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5777 : plan5777.Valid := valid_step _ _ _ valid3482 (by decide +kernel)






























































































































































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























































































































































































theorem valid7676 : plan7676.Valid := valid_step _ _ _ valid5774 (by decide +kernel)

theorem valid7677 : plan7677.Valid := valid_step _ _ _ valid5775 (by decide +kernel)

theorem valid7678 : plan7678.Valid := valid_step _ _ _ valid5776 (by decide +kernel)

theorem valid7679 : plan7679.Valid := valid_step _ _ _ valid5777 (by decide +kernel)


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
theorem t6_1699choices : plan7676.choices=[9,3,6,6,10,7].map (options 6 5) := by rfl


theorem t6_1699part0 : t6_1699jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1699part1 : t6_1699jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1699part2 : t6_1699jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1699part3 : t6_1699jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1699frontier : t6_1699root.frontier 2=t6_1699jobs := by rfl
theorem t6_1699all : t6_1699jobs.all (Job.check tree)=true := by
  simp only [t6_1699jobs,List.all_append,List.all_nil,t6_1699part0,t6_1699part1,t6_1699part2,t6_1699part3,Bool.and_self]
theorem t6_1699checked : Checked tree [9,3,6,6,10,7] := by
  refine ⟨plan7676,valid7676,t6_1699choices,?_⟩
  exact check_of_frontier tree 2 t6_1699root t6_1699jobs t6_1699frontier t6_1699all
theorem t6_1700choices : plan7677.choices=[9,3,6,6,10,10].map (options 6 5) := by rfl


theorem t6_1700part0 : t6_1700jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1700frontier : t6_1700root.frontier 0=t6_1700jobs := by rfl
theorem t6_1700all : t6_1700jobs.all (Job.check tree)=true := by
  simp only [t6_1700jobs,List.all_append,List.all_nil,t6_1700part0,Bool.and_self]
theorem t6_1700checked : Checked tree [9,3,6,6,10,10] := by
  refine ⟨plan7677,valid7677,t6_1700choices,?_⟩
  exact check_of_frontier tree 0 t6_1700root t6_1700jobs t6_1700frontier t6_1700all
theorem t6_1701choices : plan7678.choices=[9,3,6,7,7,7].map (options 6 5) := by rfl


theorem t6_1701part0 : t6_1701jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1701part1 : t6_1701jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1701part2 : t6_1701jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1701part3 : t6_1701jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1701part4 : t6_1701jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1701part5 : t6_1701jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1701part6 : t6_1701jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_1701frontier : t6_1701root.frontier 2=t6_1701jobs := by rfl
theorem t6_1701all : t6_1701jobs.all (Job.check tree)=true := by
  simp only [t6_1701jobs,List.all_append,List.all_nil,t6_1701part0,t6_1701part1,t6_1701part2,t6_1701part3,t6_1701part4,t6_1701part5,t6_1701part6,Bool.and_self]
theorem t6_1701checked : Checked tree [9,3,6,7,7,7] := by
  refine ⟨plan7678,valid7678,t6_1701choices,?_⟩
  exact check_of_frontier tree 2 t6_1701root t6_1701jobs t6_1701frontier t6_1701all
theorem t6_1702choices : plan7679.choices=[9,3,6,10,7,7].map (options 6 5) := by rfl


theorem t6_1702part0 : t6_1702jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1702part1 : t6_1702jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1702part2 : t6_1702jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1702part3 : t6_1702jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1702part4 : t6_1702jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1702part5 : t6_1702jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1702part6 : t6_1702jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_1702frontier : t6_1702root.frontier 3=t6_1702jobs := by rfl
theorem t6_1702all : t6_1702jobs.all (Job.check tree)=true := by
  simp only [t6_1702jobs,List.all_append,List.all_nil,t6_1702part0,t6_1702part1,t6_1702part2,t6_1702part3,t6_1702part4,t6_1702part5,t6_1702part6,Bool.and_self]
theorem t6_1702checked : Checked tree [9,3,6,10,7,7] := by
  refine ⟨plan7679,valid7679,t6_1702choices,?_⟩
  exact check_of_frontier tree 3 t6_1702root t6_1702jobs t6_1702frontier t6_1702all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks151 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1702checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1699checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1700checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1701checked⟩
