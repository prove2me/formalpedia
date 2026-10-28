-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks135
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:52:26.881278+00:00
-- url     : https://prove2.me/submissions/db5f31b6-46d1-4b56-b136-d14d313beb1b

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks135
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks135
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
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





































































theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid133 : plan133.Valid := valid_step _ _ _ valid0 (by decide +kernel)






















































































































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

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid573 : plan573.Valid := valid_step _ _ _ valid132 (by decide +kernel)



theorem valid575 : plan575.Valid := valid_step _ _ _ valid133 (by decide +kernel)


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















































theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1561 : plan1561.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1564 : plan1564.Valid := valid_step _ _ _ valid573 (by decide +kernel)

























































theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)














































































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





















































































































































































theorem valid3355 : plan3355.Valid := valid_step _ _ _ valid1560 (by decide +kernel)

theorem valid3356 : plan3356.Valid := valid_step _ _ _ valid1561 (by decide +kernel)

theorem valid3357 : plan3357.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3358 : plan3358.Valid := valid_step _ _ _ valid1563 (by decide +kernel)

theorem valid3359 : plan3359.Valid := valid_step _ _ _ valid1564 (by decide +kernel)


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































































































































































theorem valid3440 : plan3440.Valid := valid_step _ _ _ valid1593 (by decide +kernel)
































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





































































































theorem valid5715 : plan5715.Valid := valid_step _ _ _ valid3355 (by decide +kernel)

theorem valid5716 : plan5716.Valid := valid_step _ _ _ valid3356 (by decide +kernel)

theorem valid5717 : plan5717.Valid := valid_step _ _ _ valid3357 (by decide +kernel)

theorem valid5718 : plan5718.Valid := valid_step _ _ _ valid3358 (by decide +kernel)

theorem valid5719 : plan5719.Valid := valid_step _ _ _ valid3359 (by decide +kernel)


















































































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













































































































































theorem valid5927 : plan5927.Valid := valid_step _ _ _ valid3440 (by decide +kernel)


















































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



















































































































theorem valid7066 : plan7066.Valid := valid_step _ _ _ valid5715 (by decide +kernel)

theorem valid7067 : plan7067.Valid := valid_step _ _ _ valid5716 (by decide +kernel)

theorem valid7068 : plan7068.Valid := valid_step _ _ _ valid5717 (by decide +kernel)

theorem valid7069 : plan7069.Valid := valid_step _ _ _ valid5718 (by decide +kernel)

theorem valid7070 : plan7070.Valid := valid_step _ _ _ valid5719 (by decide +kernel)




































































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



































































































































































theorem valid7570 : plan7570.Valid := valid_step _ _ _ valid5927 (by decide +kernel)




























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
theorem t6_1330choices : plan7066.choices=[5,9,3,3,6,7].map (options 6 4) := by rfl


theorem t6_1330part0 : t6_1330jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1330part1 : t6_1330jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1330part2 : t6_1330jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1330part3 : t6_1330jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1330part4 : t6_1330jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1330frontier : t6_1330root.frontier 2=t6_1330jobs := by rfl
theorem t6_1330all : t6_1330jobs.all (Job.check tree)=true := by
  simp only [t6_1330jobs,List.all_append,List.all_nil,t6_1330part0,t6_1330part1,t6_1330part2,t6_1330part3,t6_1330part4,Bool.and_self]
theorem t6_1330checked : Checked tree [5,9,3,3,6,7] := by
  refine ⟨plan7066,valid7066,t6_1330choices,?_⟩
  exact check_of_frontier tree 2 t6_1330root t6_1330jobs t6_1330frontier t6_1330all
theorem t6_1331choices : plan7067.choices=[5,9,3,3,6,10].map (options 6 4) := by rfl


theorem t6_1331part0 : t6_1331jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1331part1 : t6_1331jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1331frontier : t6_1331root.frontier 1=t6_1331jobs := by rfl
theorem t6_1331all : t6_1331jobs.all (Job.check tree)=true := by
  simp only [t6_1331jobs,List.all_append,List.all_nil,t6_1331part0,t6_1331part1,Bool.and_self]
theorem t6_1331checked : Checked tree [5,9,3,3,6,10] := by
  refine ⟨plan7067,valid7067,t6_1331choices,?_⟩
  exact check_of_frontier tree 1 t6_1331root t6_1331jobs t6_1331frontier t6_1331all
theorem t6_1332choices : plan7068.choices=[5,9,3,3,7,7].map (options 6 4) := by rfl


theorem t6_1332part0 : t6_1332jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1332part1 : t6_1332jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1332part2 : t6_1332jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1332part3 : t6_1332jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1332part4 : t6_1332jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1332frontier : t6_1332root.frontier 2=t6_1332jobs := by rfl
theorem t6_1332all : t6_1332jobs.all (Job.check tree)=true := by
  simp only [t6_1332jobs,List.all_append,List.all_nil,t6_1332part0,t6_1332part1,t6_1332part2,t6_1332part3,t6_1332part4,Bool.and_self]
theorem t6_1332checked : Checked tree [5,9,3,3,7,7] := by
  refine ⟨plan7068,valid7068,t6_1332choices,?_⟩
  exact check_of_frontier tree 2 t6_1332root t6_1332jobs t6_1332frontier t6_1332all
theorem t6_1333choices : plan7069.choices=[5,9,3,3,10,7].map (options 6 4) := by rfl


theorem t6_1333part0 : t6_1333jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1333part1 : t6_1333jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1333part2 : t6_1333jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1333part3 : t6_1333jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1333part4 : t6_1333jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1333frontier : t6_1333root.frontier 2=t6_1333jobs := by rfl
theorem t6_1333all : t6_1333jobs.all (Job.check tree)=true := by
  simp only [t6_1333jobs,List.all_append,List.all_nil,t6_1333part0,t6_1333part1,t6_1333part2,t6_1333part3,t6_1333part4,Bool.and_self]
theorem t6_1333checked : Checked tree [5,9,3,3,10,7] := by
  refine ⟨plan7069,valid7069,t6_1333choices,?_⟩
  exact check_of_frontier tree 2 t6_1333root t6_1333jobs t6_1333frontier t6_1333all
theorem t6_1334choices : plan7070.choices=[5,9,3,3,10,10].map (options 6 4) := by rfl


theorem t6_1334part0 : t6_1334jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1334frontier : t6_1334root.frontier 0=t6_1334jobs := by rfl
theorem t6_1334all : t6_1334jobs.all (Job.check tree)=true := by
  simp only [t6_1334jobs,List.all_append,List.all_nil,t6_1334part0,Bool.and_self]
theorem t6_1334checked : Checked tree [5,9,3,3,10,10] := by
  refine ⟨plan7070,valid7070,t6_1334choices,?_⟩
  exact check_of_frontier tree 0 t6_1334root t6_1334jobs t6_1334frontier t6_1334all
theorem t6_1335choices : plan7570.choices=[5,9,3,6,6,6].map (options 6 5) := by rfl


theorem t6_1335part0 : t6_1335jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1335frontier : t6_1335root.frontier 0=t6_1335jobs := by rfl
theorem t6_1335all : t6_1335jobs.all (Job.check tree)=true := by
  simp only [t6_1335jobs,List.all_append,List.all_nil,t6_1335part0,Bool.and_self]
theorem t6_1335checked : Checked tree [5,9,3,6,6,6] := by
  refine ⟨plan7570,valid7570,t6_1335choices,?_⟩
  exact check_of_frontier tree 0 t6_1335root t6_1335jobs t6_1335frontier t6_1335all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks135 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1333checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1334checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1335checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1330checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1331checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1332checked⟩
