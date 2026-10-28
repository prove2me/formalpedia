-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks024
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:21.697813+00:00
-- url     : https://prove2.me/submissions/1983d2f4-a8b7-4b60-b636-cf6bdd319c87

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks024
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks024
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
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



theorem valid99 : plan99.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid102 : plan102.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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





























































































































































theorem valid463 : plan463.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid464 : plan464.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid465 : plan465.Valid := valid_step _ _ _ valid99 (by decide +kernel)






























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



























theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)






























































































































































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



































































































theorem valid1298 : plan1298.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1299 : plan1299.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1300 : plan1300.Valid := valid_step _ _ _ valid465 (by decide +kernel)













































































theorem valid1339 : plan1339.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1340 : plan1340.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1341 : plan1341.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1342 : plan1342.Valid := valid_step _ _ _ valid497 (by decide +kernel)




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

















































































































































theorem valid2665 : plan2665.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2666 : plan2666.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2667 : plan2667.Valid := valid_step _ _ _ valid1300 (by decide +kernel)










































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





theorem valid3939 : plan3939.Valid := valid_step _ _ _ valid2665 (by decide +kernel)

theorem valid3940 : plan3940.Valid := valid_step _ _ _ valid2666 (by decide +kernel)

theorem valid3941 : plan3941.Valid := valid_step _ _ _ valid2667 (by decide +kernel)






















































































































































































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



























































































































































theorem valid2862 : plan2862.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2863 : plan2863.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2864 : plan2864.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2865 : plan2865.Valid := valid_step _ _ _ valid1342 (by decide +kernel)






























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











































































































































theorem valid4294 : plan4294.Valid := valid_step _ _ _ valid2862 (by decide +kernel)

theorem valid4295 : plan4295.Valid := valid_step _ _ _ valid2863 (by decide +kernel)

theorem valid4296 : plan4296.Valid := valid_step _ _ _ valid2864 (by decide +kernel)

theorem valid4297 : plan4297.Valid := valid_step _ _ _ valid2865 (by decide +kernel)














































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
theorem t5_820choices : plan3939.choices=[2,9,3,3,6].map (options 5 2) := by rfl


theorem t5_820part0 : t5_820jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_820part1 : t5_820jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_820frontier : t5_820root.frontier 1=t5_820jobs := by rfl
theorem t5_820all : t5_820jobs.all (Job.check tree)=true := by
  simp only [t5_820jobs,List.all_append,List.all_nil,t5_820part0,t5_820part1,Bool.and_self]
theorem t5_820checked : Checked tree [2,9,3,3,6] := by
  refine ⟨plan3939,valid3939,t5_820choices,?_⟩
  exact check_of_frontier tree 1 t5_820root t5_820jobs t5_820frontier t5_820all
theorem t5_821choices : plan3940.choices=[2,9,3,3,7].map (options 5 2) := by rfl


theorem t5_821part0 : t5_821jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_821part1 : t5_821jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_821part2 : t5_821jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_821frontier : t5_821root.frontier 1=t5_821jobs := by rfl
theorem t5_821all : t5_821jobs.all (Job.check tree)=true := by
  simp only [t5_821jobs,List.all_append,List.all_nil,t5_821part0,t5_821part1,t5_821part2,Bool.and_self]
theorem t5_821checked : Checked tree [2,9,3,3,7] := by
  refine ⟨plan3940,valid3940,t5_821choices,?_⟩
  exact check_of_frontier tree 1 t5_821root t5_821jobs t5_821frontier t5_821all
theorem t5_822choices : plan3941.choices=[2,9,3,3,10].map (options 5 2) := by rfl


theorem t5_822part0 : t5_822jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_822part1 : t5_822jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_822frontier : t5_822root.frontier 1=t5_822jobs := by rfl
theorem t5_822all : t5_822jobs.all (Job.check tree)=true := by
  simp only [t5_822jobs,List.all_append,List.all_nil,t5_822part0,t5_822part1,Bool.and_self]
theorem t5_822checked : Checked tree [2,9,3,3,10] := by
  refine ⟨plan3941,valid3941,t5_822choices,?_⟩
  exact check_of_frontier tree 1 t5_822root t5_822jobs t5_822frontier t5_822all
theorem t5_823choices : plan4294.choices=[2,9,3,6,6].map (options 5 3) := by rfl


theorem t5_823part0 : t5_823jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_823part1 : t5_823jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_823frontier : t5_823root.frontier 1=t5_823jobs := by rfl
theorem t5_823all : t5_823jobs.all (Job.check tree)=true := by
  simp only [t5_823jobs,List.all_append,List.all_nil,t5_823part0,t5_823part1,Bool.and_self]
theorem t5_823checked : Checked tree [2,9,3,6,6] := by
  refine ⟨plan4294,valid4294,t5_823choices,?_⟩
  exact check_of_frontier tree 1 t5_823root t5_823jobs t5_823frontier t5_823all
theorem t5_824choices : plan4295.choices=[2,9,3,6,7].map (options 5 3) := by rfl


theorem t5_824part0 : t5_824jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_824part1 : t5_824jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_824part2 : t5_824jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_824part3 : t5_824jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_824frontier : t5_824root.frontier 1=t5_824jobs := by rfl
theorem t5_824all : t5_824jobs.all (Job.check tree)=true := by
  simp only [t5_824jobs,List.all_append,List.all_nil,t5_824part0,t5_824part1,t5_824part2,t5_824part3,Bool.and_self]
theorem t5_824checked : Checked tree [2,9,3,6,7] := by
  refine ⟨plan4295,valid4295,t5_824choices,?_⟩
  exact check_of_frontier tree 1 t5_824root t5_824jobs t5_824frontier t5_824all
theorem t5_825choices : plan4296.choices=[2,9,3,6,10].map (options 5 3) := by rfl


theorem t5_825part0 : t5_825jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_825part1 : t5_825jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_825part2 : t5_825jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_825part3 : t5_825jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_825frontier : t5_825root.frontier 1=t5_825jobs := by rfl
theorem t5_825all : t5_825jobs.all (Job.check tree)=true := by
  simp only [t5_825jobs,List.all_append,List.all_nil,t5_825part0,t5_825part1,t5_825part2,t5_825part3,Bool.and_self]
theorem t5_825checked : Checked tree [2,9,3,6,10] := by
  refine ⟨plan4296,valid4296,t5_825choices,?_⟩
  exact check_of_frontier tree 1 t5_825root t5_825jobs t5_825frontier t5_825all
theorem t5_826choices : plan4297.choices=[2,9,3,7,7].map (options 5 3) := by rfl


theorem t5_826part0 : t5_826jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_826part1 : t5_826jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_826part2 : t5_826jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_826part3 : t5_826jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_826frontier : t5_826root.frontier 1=t5_826jobs := by rfl
theorem t5_826all : t5_826jobs.all (Job.check tree)=true := by
  simp only [t5_826jobs,List.all_append,List.all_nil,t5_826part0,t5_826part1,t5_826part2,t5_826part3,Bool.and_self]
theorem t5_826checked : Checked tree [2,9,3,7,7] := by
  refine ⟨plan4297,valid4297,t5_826choices,?_⟩
  exact check_of_frontier tree 1 t5_826root t5_826jobs t5_826frontier t5_826all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks024 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_820checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_821checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_822checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_823checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_824checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_825checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_826checked⟩
