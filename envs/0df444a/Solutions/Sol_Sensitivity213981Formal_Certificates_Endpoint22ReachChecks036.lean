-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks036
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:02:51.125292+00:00
-- url     : https://prove2.me/submissions/76c26682-f2b5-4f2d-ac7f-e683b9833fd7

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
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























theorem valid108 : plan108.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid109 : plan109.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid111 : plan111.Valid := valid_step _ _ _ valid0 (by decide +kernel)


































































































































































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



































































theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)











theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid524 : plan524.Valid := valid_step _ _ _ valid111 (by decide +kernel)








































































































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

























































































































































































theorem valid1437 : plan1437.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1438 : plan1438.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1439 : plan1439.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1440 : plan1440.Valid := valid_step _ _ _ valid517 (by decide +kernel)
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

theorem valid1441 : plan1441.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1442 : plan1442.Valid := valid_step _ _ _ valid524 (by decide +kernel)

theorem valid1443 : plan1443.Valid := valid_step _ _ _ valid517 (by decide +kernel)





































theorem valid1462 : plan1462.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1463 : plan1463.Valid := valid_step _ _ _ valid523 (by decide +kernel)


















































































































































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















































theorem valid2904 : plan2904.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid2905 : plan2905.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid2906 : plan2906.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid2907 : plan2907.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid2908 : plan2908.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid2909 : plan2909.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid2910 : plan2910.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

theorem valid2911 : plan2911.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid2912 : plan2912.Valid := valid_step _ _ _ valid1463 (by decide +kernel)
































































































































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

















































































































theorem valid4857 : plan4857.Valid := valid_step _ _ _ valid2904 (by decide +kernel)

theorem valid4858 : plan4858.Valid := valid_step _ _ _ valid2905 (by decide +kernel)

theorem valid4859 : plan4859.Valid := valid_step _ _ _ valid2906 (by decide +kernel)

theorem valid4860 : plan4860.Valid := valid_step _ _ _ valid2907 (by decide +kernel)

theorem valid4861 : plan4861.Valid := valid_step _ _ _ valid2908 (by decide +kernel)

theorem valid4862 : plan4862.Valid := valid_step _ _ _ valid2909 (by decide +kernel)

theorem valid4863 : plan4863.Valid := valid_step _ _ _ valid2910 (by decide +kernel)

theorem valid4864 : plan4864.Valid := valid_step _ _ _ valid2911 (by decide +kernel)

theorem valid4865 : plan4865.Valid := valid_step _ _ _ valid2912 (by decide +kernel)






























































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
theorem t5_1222choices : plan4857.choices=[5,3,6,6,6].map (options 5 4) := by rfl


theorem t5_1222part0 : t5_1222jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1222frontier : t5_1222root.frontier 0=t5_1222jobs := by rfl
theorem t5_1222all : t5_1222jobs.all (Job.check tree)=true := by
  simp only [t5_1222jobs,List.all_append,List.all_nil,t5_1222part0,Bool.and_self]
theorem t5_1222checked : Checked tree [5,3,6,6,6] := by
  refine ⟨plan4857,valid4857,t5_1222choices,?_⟩
  exact check_of_frontier tree 0 t5_1222root t5_1222jobs t5_1222frontier t5_1222all
theorem t5_1223choices : plan4858.choices=[5,3,6,6,7].map (options 5 4) := by rfl


theorem t5_1223part0 : t5_1223jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1223part1 : t5_1223jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1223frontier : t5_1223root.frontier 1=t5_1223jobs := by rfl
theorem t5_1223all : t5_1223jobs.all (Job.check tree)=true := by
  simp only [t5_1223jobs,List.all_append,List.all_nil,t5_1223part0,t5_1223part1,Bool.and_self]
theorem t5_1223checked : Checked tree [5,3,6,6,7] := by
  refine ⟨plan4858,valid4858,t5_1223choices,?_⟩
  exact check_of_frontier tree 1 t5_1223root t5_1223jobs t5_1223frontier t5_1223all
theorem t5_1224choices : plan4859.choices=[5,3,6,6,10].map (options 5 4) := by rfl


theorem t5_1224part0 : t5_1224jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1224part1 : t5_1224jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1224frontier : t5_1224root.frontier 1=t5_1224jobs := by rfl
theorem t5_1224all : t5_1224jobs.all (Job.check tree)=true := by
  simp only [t5_1224jobs,List.all_append,List.all_nil,t5_1224part0,t5_1224part1,Bool.and_self]
theorem t5_1224checked : Checked tree [5,3,6,6,10] := by
  refine ⟨plan4859,valid4859,t5_1224choices,?_⟩
  exact check_of_frontier tree 1 t5_1224root t5_1224jobs t5_1224frontier t5_1224all
theorem t5_1225choices : plan4860.choices=[5,3,6,7,7].map (options 5 4) := by rfl


theorem t5_1225part0 : t5_1225jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1225part1 : t5_1225jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1225part2 : t5_1225jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1225frontier : t5_1225root.frontier 1=t5_1225jobs := by rfl
theorem t5_1225all : t5_1225jobs.all (Job.check tree)=true := by
  simp only [t5_1225jobs,List.all_append,List.all_nil,t5_1225part0,t5_1225part1,t5_1225part2,Bool.and_self]
theorem t5_1225checked : Checked tree [5,3,6,7,7] := by
  refine ⟨plan4860,valid4860,t5_1225choices,?_⟩
  exact check_of_frontier tree 1 t5_1225root t5_1225jobs t5_1225frontier t5_1225all
theorem t5_1226choices : plan4861.choices=[5,3,6,10,7].map (options 5 4) := by rfl


theorem t5_1226part0 : t5_1226jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1226part1 : t5_1226jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1226part2 : t5_1226jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1226part3 : t5_1226jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_1226part4 : t5_1226jobs4.all (Job.check tree)=true := by decide +kernel

theorem t5_1226frontier : t5_1226root.frontier 1=t5_1226jobs := by rfl
theorem t5_1226all : t5_1226jobs.all (Job.check tree)=true := by
  simp only [t5_1226jobs,List.all_append,List.all_nil,t5_1226part0,t5_1226part1,t5_1226part2,t5_1226part3,t5_1226part4,Bool.and_self]
theorem t5_1226checked : Checked tree [5,3,6,10,7] := by
  refine ⟨plan4861,valid4861,t5_1226choices,?_⟩
  exact check_of_frontier tree 1 t5_1226root t5_1226jobs t5_1226frontier t5_1226all
theorem t5_1227choices : plan4862.choices=[5,3,6,10,10].map (options 5 4) := by rfl


theorem t5_1227part0 : t5_1227jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1227part1 : t5_1227jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1227frontier : t5_1227root.frontier 1=t5_1227jobs := by rfl
theorem t5_1227all : t5_1227jobs.all (Job.check tree)=true := by
  simp only [t5_1227jobs,List.all_append,List.all_nil,t5_1227part0,t5_1227part1,Bool.and_self]
theorem t5_1227checked : Checked tree [5,3,6,10,10] := by
  refine ⟨plan4862,valid4862,t5_1227choices,?_⟩
  exact check_of_frontier tree 1 t5_1227root t5_1227jobs t5_1227frontier t5_1227all
theorem t5_1228choices : plan4863.choices=[5,3,7,7,7].map (options 5 4) := by rfl


theorem t5_1228part0 : t5_1228jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1228part1 : t5_1228jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1228frontier : t5_1228root.frontier 1=t5_1228jobs := by rfl
theorem t5_1228all : t5_1228jobs.all (Job.check tree)=true := by
  simp only [t5_1228jobs,List.all_append,List.all_nil,t5_1228part0,t5_1228part1,Bool.and_self]
theorem t5_1228checked : Checked tree [5,3,7,7,7] := by
  refine ⟨plan4863,valid4863,t5_1228choices,?_⟩
  exact check_of_frontier tree 1 t5_1228root t5_1228jobs t5_1228frontier t5_1228all
theorem t5_1229choices : plan4864.choices=[5,3,10,7,7].map (options 5 4) := by rfl


theorem t5_1229part0 : t5_1229jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1229part1 : t5_1229jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1229part2 : t5_1229jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1229frontier : t5_1229root.frontier 1=t5_1229jobs := by rfl
theorem t5_1229all : t5_1229jobs.all (Job.check tree)=true := by
  simp only [t5_1229jobs,List.all_append,List.all_nil,t5_1229part0,t5_1229part1,t5_1229part2,Bool.and_self]
theorem t5_1229checked : Checked tree [5,3,10,7,7] := by
  refine ⟨plan4864,valid4864,t5_1229choices,?_⟩
  exact check_of_frontier tree 1 t5_1229root t5_1229jobs t5_1229frontier t5_1229all
theorem t5_1230choices : plan4865.choices=[5,3,10,10,7].map (options 5 4) := by rfl


theorem t5_1230part0 : t5_1230jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1230part1 : t5_1230jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1230frontier : t5_1230root.frontier 1=t5_1230jobs := by rfl
theorem t5_1230all : t5_1230jobs.all (Job.check tree)=true := by
  simp only [t5_1230jobs,List.all_append,List.all_nil,t5_1230part0,t5_1230part1,Bool.and_self]
theorem t5_1230checked : Checked tree [5,3,10,10,7] := by
  refine ⟨plan4865,valid4865,t5_1230choices,?_⟩
  exact check_of_frontier tree 1 t5_1230root t5_1230jobs t5_1230frontier t5_1230all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks036 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1230checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1223checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1224checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1225checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1226checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1227checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1228checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1222checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1229checked⟩
