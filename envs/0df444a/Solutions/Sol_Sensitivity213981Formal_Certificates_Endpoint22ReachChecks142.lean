-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks142
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:58:24.158418+00:00
-- url     : https://prove2.me/submissions/bdcfdddb-2f0e-4e02-8cf7-ff7d18b70ce8

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks142
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks142
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























































































































theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

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











































theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)











































theorem valid3507 : plan3507.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3508 : plan3508.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3509 : plan3509.Valid := valid_step _ _ _ valid1605 (by decide +kernel)






















































































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

























theorem valid5773 : plan5773.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5774 : plan5774.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5775 : plan5775.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5776 : plan5776.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5777 : plan5777.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5778 : plan5778.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5779 : plan5779.Valid := valid_step _ _ _ valid3484 (by decide +kernel)

theorem valid5780 : plan5780.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5781 : plan5781.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5782 : plan5782.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5783 : plan5783.Valid := valid_step _ _ _ valid3509 (by decide +kernel)


















































































































































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







































































theorem valid7620 : plan7620.Valid := valid_step _ _ _ valid5773 (by decide +kernel)

theorem valid7621 : plan7621.Valid := valid_step _ _ _ valid5774 (by decide +kernel)

theorem valid7622 : plan7622.Valid := valid_step _ _ _ valid5775 (by decide +kernel)

theorem valid7623 : plan7623.Valid := valid_step _ _ _ valid5776 (by decide +kernel)

theorem valid7624 : plan7624.Valid := valid_step _ _ _ valid5777 (by decide +kernel)

theorem valid7625 : plan7625.Valid := valid_step _ _ _ valid5778 (by decide +kernel)

theorem valid7626 : plan7626.Valid := valid_step _ _ _ valid5779 (by decide +kernel)

theorem valid7627 : plan7627.Valid := valid_step _ _ _ valid5780 (by decide +kernel)

theorem valid7628 : plan7628.Valid := valid_step _ _ _ valid5781 (by decide +kernel)

theorem valid7629 : plan7629.Valid := valid_step _ _ _ valid5782 (by decide +kernel)

theorem valid7630 : plan7630.Valid := valid_step _ _ _ valid5783 (by decide +kernel)




































































































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
theorem t6_1505choices : plan7620.choices=[8,3,6,6,7,7].map (options 6 5) := by rfl


theorem t6_1505part0 : t6_1505jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1505part1 : t6_1505jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1505frontier : t6_1505root.frontier 1=t6_1505jobs := by rfl
theorem t6_1505all : t6_1505jobs.all (Job.check tree)=true := by
  simp only [t6_1505jobs,List.all_append,List.all_nil,t6_1505part0,t6_1505part1,Bool.and_self]
theorem t6_1505checked : Checked tree [8,3,6,6,7,7] := by
  refine ⟨plan7620,valid7620,t6_1505choices,?_⟩
  exact check_of_frontier tree 1 t6_1505root t6_1505jobs t6_1505frontier t6_1505all
theorem t6_1506choices : plan7621.choices=[8,3,6,6,10,7].map (options 6 5) := by rfl


theorem t6_1506part0 : t6_1506jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1506part1 : t6_1506jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1506frontier : t6_1506root.frontier 1=t6_1506jobs := by rfl
theorem t6_1506all : t6_1506jobs.all (Job.check tree)=true := by
  simp only [t6_1506jobs,List.all_append,List.all_nil,t6_1506part0,t6_1506part1,Bool.and_self]
theorem t6_1506checked : Checked tree [8,3,6,6,10,7] := by
  refine ⟨plan7621,valid7621,t6_1506choices,?_⟩
  exact check_of_frontier tree 1 t6_1506root t6_1506jobs t6_1506frontier t6_1506all
theorem t6_1507choices : plan7622.choices=[8,3,6,6,10,10].map (options 6 5) := by rfl


theorem t6_1507part0 : t6_1507jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1507frontier : t6_1507root.frontier 0=t6_1507jobs := by rfl
theorem t6_1507all : t6_1507jobs.all (Job.check tree)=true := by
  simp only [t6_1507jobs,List.all_append,List.all_nil,t6_1507part0,Bool.and_self]
theorem t6_1507checked : Checked tree [8,3,6,6,10,10] := by
  refine ⟨plan7622,valid7622,t6_1507choices,?_⟩
  exact check_of_frontier tree 0 t6_1507root t6_1507jobs t6_1507frontier t6_1507all
theorem t6_1508choices : plan7623.choices=[8,3,6,7,7,7].map (options 6 5) := by rfl


theorem t6_1508part0 : t6_1508jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1508part1 : t6_1508jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1508part2 : t6_1508jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1508frontier : t6_1508root.frontier 1=t6_1508jobs := by rfl
theorem t6_1508all : t6_1508jobs.all (Job.check tree)=true := by
  simp only [t6_1508jobs,List.all_append,List.all_nil,t6_1508part0,t6_1508part1,t6_1508part2,Bool.and_self]
theorem t6_1508checked : Checked tree [8,3,6,7,7,7] := by
  refine ⟨plan7623,valid7623,t6_1508choices,?_⟩
  exact check_of_frontier tree 1 t6_1508root t6_1508jobs t6_1508frontier t6_1508all
theorem t6_1509choices : plan7624.choices=[8,3,6,10,7,7].map (options 6 5) := by rfl


theorem t6_1509part0 : t6_1509jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1509part1 : t6_1509jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1509part2 : t6_1509jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1509frontier : t6_1509root.frontier 2=t6_1509jobs := by rfl
theorem t6_1509all : t6_1509jobs.all (Job.check tree)=true := by
  simp only [t6_1509jobs,List.all_append,List.all_nil,t6_1509part0,t6_1509part1,t6_1509part2,Bool.and_self]
theorem t6_1509checked : Checked tree [8,3,6,10,7,7] := by
  refine ⟨plan7624,valid7624,t6_1509choices,?_⟩
  exact check_of_frontier tree 2 t6_1509root t6_1509jobs t6_1509frontier t6_1509all
theorem t6_1510choices : plan7625.choices=[8,3,6,10,10,7].map (options 6 5) := by rfl


theorem t6_1510part0 : t6_1510jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1510part1 : t6_1510jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1510frontier : t6_1510root.frontier 1=t6_1510jobs := by rfl
theorem t6_1510all : t6_1510jobs.all (Job.check tree)=true := by
  simp only [t6_1510jobs,List.all_append,List.all_nil,t6_1510part0,t6_1510part1,Bool.and_self]
theorem t6_1510checked : Checked tree [8,3,6,10,10,7] := by
  refine ⟨plan7625,valid7625,t6_1510choices,?_⟩
  exact check_of_frontier tree 1 t6_1510root t6_1510jobs t6_1510frontier t6_1510all
theorem t6_1511choices : plan7626.choices=[8,3,6,10,10,10].map (options 6 5) := by rfl


theorem t6_1511part0 : t6_1511jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1511frontier : t6_1511root.frontier 0=t6_1511jobs := by rfl
theorem t6_1511all : t6_1511jobs.all (Job.check tree)=true := by
  simp only [t6_1511jobs,List.all_append,List.all_nil,t6_1511part0,Bool.and_self]
theorem t6_1511checked : Checked tree [8,3,6,10,10,10] := by
  refine ⟨plan7626,valid7626,t6_1511choices,?_⟩
  exact check_of_frontier tree 0 t6_1511root t6_1511jobs t6_1511frontier t6_1511all
theorem t6_1512choices : plan7627.choices=[8,3,7,7,7,7].map (options 6 5) := by rfl


theorem t6_1512part0 : t6_1512jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1512part1 : t6_1512jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1512frontier : t6_1512root.frontier 1=t6_1512jobs := by rfl
theorem t6_1512all : t6_1512jobs.all (Job.check tree)=true := by
  simp only [t6_1512jobs,List.all_append,List.all_nil,t6_1512part0,t6_1512part1,Bool.and_self]
theorem t6_1512checked : Checked tree [8,3,7,7,7,7] := by
  refine ⟨plan7627,valid7627,t6_1512choices,?_⟩
  exact check_of_frontier tree 1 t6_1512root t6_1512jobs t6_1512frontier t6_1512all
theorem t6_1513choices : plan7628.choices=[8,3,10,7,7,7].map (options 6 5) := by rfl


theorem t6_1513part0 : t6_1513jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1513part1 : t6_1513jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1513part2 : t6_1513jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1513frontier : t6_1513root.frontier 1=t6_1513jobs := by rfl
theorem t6_1513all : t6_1513jobs.all (Job.check tree)=true := by
  simp only [t6_1513jobs,List.all_append,List.all_nil,t6_1513part0,t6_1513part1,t6_1513part2,Bool.and_self]
theorem t6_1513checked : Checked tree [8,3,10,7,7,7] := by
  refine ⟨plan7628,valid7628,t6_1513choices,?_⟩
  exact check_of_frontier tree 1 t6_1513root t6_1513jobs t6_1513frontier t6_1513all
theorem t6_1514choices : plan7629.choices=[8,3,10,10,7,7].map (options 6 5) := by rfl


theorem t6_1514part0 : t6_1514jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1514part1 : t6_1514jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1514frontier : t6_1514root.frontier 1=t6_1514jobs := by rfl
theorem t6_1514all : t6_1514jobs.all (Job.check tree)=true := by
  simp only [t6_1514jobs,List.all_append,List.all_nil,t6_1514part0,t6_1514part1,Bool.and_self]
theorem t6_1514checked : Checked tree [8,3,10,10,7,7] := by
  refine ⟨plan7629,valid7629,t6_1514choices,?_⟩
  exact check_of_frontier tree 1 t6_1514root t6_1514jobs t6_1514frontier t6_1514all
theorem t6_1515choices : plan7630.choices=[8,3,10,10,10,7].map (options 6 5) := by rfl


theorem t6_1515part0 : t6_1515jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1515frontier : t6_1515root.frontier 0=t6_1515jobs := by rfl
theorem t6_1515all : t6_1515jobs.all (Job.check tree)=true := by
  simp only [t6_1515jobs,List.all_append,List.all_nil,t6_1515part0,Bool.and_self]
theorem t6_1515checked : Checked tree [8,3,10,10,10,7] := by
  refine ⟨plan7630,valid7630,t6_1515choices,?_⟩
  exact check_of_frontier tree 0 t6_1515root t6_1515jobs t6_1515frontier t6_1515all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks142 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1513checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1514checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1515checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1505checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1506checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1507checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1508checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1509checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1510checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1511checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1512checked⟩
