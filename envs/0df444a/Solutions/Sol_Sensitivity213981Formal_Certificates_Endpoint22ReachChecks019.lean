-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks019
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:47:29.92789+00:00
-- url     : https://prove2.me/submissions/ef75115e-702e-4c47-968b-3fd025077dae

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks019
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks019
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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















































































































































































theorem valid88 : plan88.Valid := valid_step _ _ _ valid0 (by decide +kernel)















theorem valid96 : plan96.Valid := valid_step _ _ _ valid0 (by decide +kernel)
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

theorem valid97 : plan97.Valid := valid_step _ _ _ valid0 (by decide +kernel)











theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid105 : plan105.Valid := valid_step _ _ _ valid0 (by decide +kernel)














































































































































































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









































































































































theorem valid453 : plan453.Valid := valid_step _ _ _ valid88 (by decide +kernel)



















theorem valid463 : plan463.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid464 : plan464.Valid := valid_step _ _ _ valid97 (by decide +kernel)
































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

































theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)











theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)
















































































































































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































theorem valid1264 : plan1264.Valid := valid_step _ _ _ valid453 (by decide +kernel)



































































theorem valid1298 : plan1298.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1299 : plan1299.Valid := valid_step _ _ _ valid464 (by decide +kernel)


























































































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





















































































































theorem valid2555 : plan2555.Valid := valid_step _ _ _ valid1264 (by decide +kernel)










































































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































































































































































































theorem valid3744 : plan3744.Valid := valid_step _ _ _ valid2555 (by decide +kernel)
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





























































theorem valid1375 : plan1375.Valid := valid_step _ _ _ valid504 (by decide +kernel)

theorem valid1376 : plan1376.Valid := valid_step _ _ _ valid497 (by decide +kernel)







































theorem valid1396 : plan1396.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1397 : plan1397.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1398 : plan1398.Valid := valid_step _ _ _ valid504 (by decide +kernel)




















































































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















































































































theorem valid2648 : plan2648.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2649 : plan2649.Valid := valid_step _ _ _ valid1299 (by decide +kernel)














































































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









































































































































































theorem valid2773 : plan2773.Valid := valid_step _ _ _ valid1375 (by decide +kernel)

theorem valid2774 : plan2774.Valid := valid_step _ _ _ valid1376 (by decide +kernel)

theorem valid2775 : plan2775.Valid := valid_step _ _ _ valid1396 (by decide +kernel)

theorem valid2776 : plan2776.Valid := valid_step _ _ _ valid1397 (by decide +kernel)

theorem valid2777 : plan2777.Valid := valid_step _ _ _ valid1398 (by decide +kernel)














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



























































































































































































theorem valid3934 : plan3934.Valid := valid_step _ _ _ valid2648 (by decide +kernel)

theorem valid3935 : plan3935.Valid := valid_step _ _ _ valid2649 (by decide +kernel)


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



































































































theorem valid4274 : plan4274.Valid := valid_step _ _ _ valid2773 (by decide +kernel)

theorem valid4275 : plan4275.Valid := valid_step _ _ _ valid2774 (by decide +kernel)

theorem valid4276 : plan4276.Valid := valid_step _ _ _ valid2775 (by decide +kernel)

theorem valid4277 : plan4277.Valid := valid_step _ _ _ valid2776 (by decide +kernel)

theorem valid4278 : plan4278.Valid := valid_step _ _ _ valid2777 (by decide +kernel)




















































































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
theorem t5_747choices : plan4274.choices=[2,3,6,10,10].map (options 5 3) := by rfl


theorem t5_747part0 : t5_747jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_747part1 : t5_747jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_747part2 : t5_747jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_747part3 : t5_747jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_747frontier : t5_747root.frontier 1=t5_747jobs := by rfl
theorem t5_747all : t5_747jobs.all (Job.check tree)=true := by
  simp only [t5_747jobs,List.all_append,List.all_nil,t5_747part0,t5_747part1,t5_747part2,t5_747part3,Bool.and_self]
theorem t5_747checked : Checked tree [2,3,6,10,10] := by
  refine ⟨plan4274,valid4274,t5_747choices,?_⟩
  exact check_of_frontier tree 1 t5_747root t5_747jobs t5_747frontier t5_747all
theorem t5_748choices : plan4275.choices=[2,3,7,7,7].map (options 5 3) := by rfl


theorem t5_748part0 : t5_748jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_748part1 : t5_748jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_748frontier : t5_748root.frontier 1=t5_748jobs := by rfl
theorem t5_748all : t5_748jobs.all (Job.check tree)=true := by
  simp only [t5_748jobs,List.all_append,List.all_nil,t5_748part0,t5_748part1,Bool.and_self]
theorem t5_748checked : Checked tree [2,3,7,7,7] := by
  refine ⟨plan4275,valid4275,t5_748choices,?_⟩
  exact check_of_frontier tree 1 t5_748root t5_748jobs t5_748frontier t5_748all
theorem t5_749choices : plan4276.choices=[2,3,10,7,7].map (options 5 3) := by rfl


theorem t5_749part0 : t5_749jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_749part1 : t5_749jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_749part2 : t5_749jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_749part3 : t5_749jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_749frontier : t5_749root.frontier 1=t5_749jobs := by rfl
theorem t5_749all : t5_749jobs.all (Job.check tree)=true := by
  simp only [t5_749jobs,List.all_append,List.all_nil,t5_749part0,t5_749part1,t5_749part2,t5_749part3,Bool.and_self]
theorem t5_749checked : Checked tree [2,3,10,7,7] := by
  refine ⟨plan4276,valid4276,t5_749choices,?_⟩
  exact check_of_frontier tree 1 t5_749root t5_749jobs t5_749frontier t5_749all
theorem t5_750choices : plan4277.choices=[2,3,10,10,7].map (options 5 3) := by rfl


theorem t5_750part0 : t5_750jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_750part1 : t5_750jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_750part2 : t5_750jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_750part3 : t5_750jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_750frontier : t5_750root.frontier 1=t5_750jobs := by rfl
theorem t5_750all : t5_750jobs.all (Job.check tree)=true := by
  simp only [t5_750jobs,List.all_append,List.all_nil,t5_750part0,t5_750part1,t5_750part2,t5_750part3,Bool.and_self]
theorem t5_750checked : Checked tree [2,3,10,10,7] := by
  refine ⟨plan4277,valid4277,t5_750choices,?_⟩
  exact check_of_frontier tree 1 t5_750root t5_750jobs t5_750frontier t5_750all
theorem t5_751choices : plan4278.choices=[2,3,10,10,10].map (options 5 3) := by rfl


theorem t5_751part0 : t5_751jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_751part1 : t5_751jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_751frontier : t5_751root.frontier 1=t5_751jobs := by rfl
theorem t5_751all : t5_751jobs.all (Job.check tree)=true := by
  simp only [t5_751jobs,List.all_append,List.all_nil,t5_751part0,t5_751part1,Bool.and_self]
theorem t5_751checked : Checked tree [2,3,10,10,10] := by
  refine ⟨plan4278,valid4278,t5_751choices,?_⟩
  exact check_of_frontier tree 1 t5_751root t5_751jobs t5_751frontier t5_751all
theorem t5_752choices : plan3744.choices=[2,5,3,3,3].map (options 5 1) := by rfl


theorem t5_752part0 : t5_752jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_752frontier : t5_752root.frontier 0=t5_752jobs := by rfl
theorem t5_752all : t5_752jobs.all (Job.check tree)=true := by
  simp only [t5_752jobs,List.all_append,List.all_nil,t5_752part0,Bool.and_self]
theorem t5_752checked : Checked tree [2,5,3,3,3] := by
  refine ⟨plan3744,valid3744,t5_752choices,?_⟩
  exact check_of_frontier tree 0 t5_752root t5_752jobs t5_752frontier t5_752all
theorem t5_753choices : plan3934.choices=[2,5,3,3,6].map (options 5 2) := by rfl


theorem t5_753part0 : t5_753jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_753part1 : t5_753jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_753frontier : t5_753root.frontier 1=t5_753jobs := by rfl
theorem t5_753all : t5_753jobs.all (Job.check tree)=true := by
  simp only [t5_753jobs,List.all_append,List.all_nil,t5_753part0,t5_753part1,Bool.and_self]
theorem t5_753checked : Checked tree [2,5,3,3,6] := by
  refine ⟨plan3934,valid3934,t5_753choices,?_⟩
  exact check_of_frontier tree 1 t5_753root t5_753jobs t5_753frontier t5_753all
theorem t5_754choices : plan3935.choices=[2,5,3,3,7].map (options 5 2) := by rfl


theorem t5_754part0 : t5_754jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_754part1 : t5_754jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_754part2 : t5_754jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_754frontier : t5_754root.frontier 1=t5_754jobs := by rfl
theorem t5_754all : t5_754jobs.all (Job.check tree)=true := by
  simp only [t5_754jobs,List.all_append,List.all_nil,t5_754part0,t5_754part1,t5_754part2,Bool.and_self]
theorem t5_754checked : Checked tree [2,5,3,3,7] := by
  refine ⟨plan3935,valid3935,t5_754choices,?_⟩
  exact check_of_frontier tree 1 t5_754root t5_754jobs t5_754frontier t5_754all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks019 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_754checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_747checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_748checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_749checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_750checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_751checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_752checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_753checked⟩
