-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks035
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:01:54.331435+00:00
-- url     : https://prove2.me/submissions/c21a1872-2e02-4613-90c2-78ec78e055ea

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
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



































































































theorem valid1298 : plan1298.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1299 : plan1299.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1300 : plan1300.Valid := valid_step _ _ _ valid465 (by decide +kernel)













































































theorem valid1339 : plan1339.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1340 : plan1340.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1341 : plan1341.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1342 : plan1342.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1343 : plan1343.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1344 : plan1344.Valid := valid_step _ _ _ valid504 (by decide +kernel)
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





































































theorem valid2627 : plan2627.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2628 : plan2628.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2629 : plan2629.Valid := valid_step _ _ _ valid1300 (by decide +kernel)






















































































































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



















































































































































theorem valid2762 : plan2762.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2763 : plan2763.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2764 : plan2764.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2765 : plan2765.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2766 : plan2766.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2767 : plan2767.Valid := valid_step _ _ _ valid1344 (by decide +kernel)


































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





































































theorem valid3971 : plan3971.Valid := valid_step _ _ _ valid2627 (by decide +kernel)

theorem valid3972 : plan3972.Valid := valid_step _ _ _ valid2628 (by decide +kernel)

theorem valid3973 : plan3973.Valid := valid_step _ _ _ valid2629 (by decide +kernel)






















































































































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











































































































theorem valid4374 : plan4374.Valid := valid_step _ _ _ valid2762 (by decide +kernel)

theorem valid4375 : plan4375.Valid := valid_step _ _ _ valid2763 (by decide +kernel)

theorem valid4376 : plan4376.Valid := valid_step _ _ _ valid2764 (by decide +kernel)

theorem valid4377 : plan4377.Valid := valid_step _ _ _ valid2765 (by decide +kernel)

theorem valid4378 : plan4378.Valid := valid_step _ _ _ valid2766 (by decide +kernel)

theorem valid4379 : plan4379.Valid := valid_step _ _ _ valid2767 (by decide +kernel)










































































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
theorem t5_1213choices : plan3971.choices=[5,3,3,3,6].map (options 5 2) := by rfl


theorem t5_1213part0 : t5_1213jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1213part1 : t5_1213jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1213frontier : t5_1213root.frontier 1=t5_1213jobs := by rfl
theorem t5_1213all : t5_1213jobs.all (Job.check tree)=true := by
  simp only [t5_1213jobs,List.all_append,List.all_nil,t5_1213part0,t5_1213part1,Bool.and_self]
theorem t5_1213checked : Checked tree [5,3,3,3,6] := by
  refine ⟨plan3971,valid3971,t5_1213choices,?_⟩
  exact check_of_frontier tree 1 t5_1213root t5_1213jobs t5_1213frontier t5_1213all
theorem t5_1214choices : plan3972.choices=[5,3,3,3,7].map (options 5 2) := by rfl


theorem t5_1214part0 : t5_1214jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1214part1 : t5_1214jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1214frontier : t5_1214root.frontier 1=t5_1214jobs := by rfl
theorem t5_1214all : t5_1214jobs.all (Job.check tree)=true := by
  simp only [t5_1214jobs,List.all_append,List.all_nil,t5_1214part0,t5_1214part1,Bool.and_self]
theorem t5_1214checked : Checked tree [5,3,3,3,7] := by
  refine ⟨plan3972,valid3972,t5_1214choices,?_⟩
  exact check_of_frontier tree 1 t5_1214root t5_1214jobs t5_1214frontier t5_1214all
theorem t5_1215choices : plan3973.choices=[5,3,3,3,10].map (options 5 2) := by rfl


theorem t5_1215part0 : t5_1215jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1215part1 : t5_1215jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1215frontier : t5_1215root.frontier 1=t5_1215jobs := by rfl
theorem t5_1215all : t5_1215jobs.all (Job.check tree)=true := by
  simp only [t5_1215jobs,List.all_append,List.all_nil,t5_1215part0,t5_1215part1,Bool.and_self]
theorem t5_1215checked : Checked tree [5,3,3,3,10] := by
  refine ⟨plan3973,valid3973,t5_1215choices,?_⟩
  exact check_of_frontier tree 1 t5_1215root t5_1215jobs t5_1215frontier t5_1215all
theorem t5_1216choices : plan4374.choices=[5,3,3,6,6].map (options 5 3) := by rfl


theorem t5_1216part0 : t5_1216jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1216part1 : t5_1216jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1216frontier : t5_1216root.frontier 1=t5_1216jobs := by rfl
theorem t5_1216all : t5_1216jobs.all (Job.check tree)=true := by
  simp only [t5_1216jobs,List.all_append,List.all_nil,t5_1216part0,t5_1216part1,Bool.and_self]
theorem t5_1216checked : Checked tree [5,3,3,6,6] := by
  refine ⟨plan4374,valid4374,t5_1216choices,?_⟩
  exact check_of_frontier tree 1 t5_1216root t5_1216jobs t5_1216frontier t5_1216all
theorem t5_1217choices : plan4375.choices=[5,3,3,6,7].map (options 5 3) := by rfl


theorem t5_1217part0 : t5_1217jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1217part1 : t5_1217jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1217part2 : t5_1217jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1217part3 : t5_1217jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_1217frontier : t5_1217root.frontier 1=t5_1217jobs := by rfl
theorem t5_1217all : t5_1217jobs.all (Job.check tree)=true := by
  simp only [t5_1217jobs,List.all_append,List.all_nil,t5_1217part0,t5_1217part1,t5_1217part2,t5_1217part3,Bool.and_self]
theorem t5_1217checked : Checked tree [5,3,3,6,7] := by
  refine ⟨plan4375,valid4375,t5_1217choices,?_⟩
  exact check_of_frontier tree 1 t5_1217root t5_1217jobs t5_1217frontier t5_1217all
theorem t5_1218choices : plan4376.choices=[5,3,3,6,10].map (options 5 3) := by rfl


theorem t5_1218part0 : t5_1218jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1218part1 : t5_1218jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1218part2 : t5_1218jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1218frontier : t5_1218root.frontier 1=t5_1218jobs := by rfl
theorem t5_1218all : t5_1218jobs.all (Job.check tree)=true := by
  simp only [t5_1218jobs,List.all_append,List.all_nil,t5_1218part0,t5_1218part1,t5_1218part2,Bool.and_self]
theorem t5_1218checked : Checked tree [5,3,3,6,10] := by
  refine ⟨plan4376,valid4376,t5_1218choices,?_⟩
  exact check_of_frontier tree 1 t5_1218root t5_1218jobs t5_1218frontier t5_1218all
theorem t5_1219choices : plan4377.choices=[5,3,3,7,7].map (options 5 3) := by rfl


theorem t5_1219part0 : t5_1219jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1219part1 : t5_1219jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1219part2 : t5_1219jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1219frontier : t5_1219root.frontier 1=t5_1219jobs := by rfl
theorem t5_1219all : t5_1219jobs.all (Job.check tree)=true := by
  simp only [t5_1219jobs,List.all_append,List.all_nil,t5_1219part0,t5_1219part1,t5_1219part2,Bool.and_self]
theorem t5_1219checked : Checked tree [5,3,3,7,7] := by
  refine ⟨plan4377,valid4377,t5_1219choices,?_⟩
  exact check_of_frontier tree 1 t5_1219root t5_1219jobs t5_1219frontier t5_1219all
theorem t5_1220choices : plan4378.choices=[5,3,3,10,7].map (options 5 3) := by rfl


theorem t5_1220part0 : t5_1220jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1220part1 : t5_1220jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1220part2 : t5_1220jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1220part3 : t5_1220jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_1220frontier : t5_1220root.frontier 1=t5_1220jobs := by rfl
theorem t5_1220all : t5_1220jobs.all (Job.check tree)=true := by
  simp only [t5_1220jobs,List.all_append,List.all_nil,t5_1220part0,t5_1220part1,t5_1220part2,t5_1220part3,Bool.and_self]
theorem t5_1220checked : Checked tree [5,3,3,10,7] := by
  refine ⟨plan4378,valid4378,t5_1220choices,?_⟩
  exact check_of_frontier tree 1 t5_1220root t5_1220jobs t5_1220frontier t5_1220all
theorem t5_1221choices : plan4379.choices=[5,3,3,10,10].map (options 5 3) := by rfl


theorem t5_1221part0 : t5_1221jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1221part1 : t5_1221jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1221frontier : t5_1221root.frontier 1=t5_1221jobs := by rfl
theorem t5_1221all : t5_1221jobs.all (Job.check tree)=true := by
  simp only [t5_1221jobs,List.all_append,List.all_nil,t5_1221part0,t5_1221part1,Bool.and_self]
theorem t5_1221checked : Checked tree [5,3,3,10,10] := by
  refine ⟨plan4379,valid4379,t5_1221choices,?_⟩
  exact check_of_frontier tree 1 t5_1221root t5_1221jobs t5_1221frontier t5_1221all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks035 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1220checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1221checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1213checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1214checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1215checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1216checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1217checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1218checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1219checked⟩
