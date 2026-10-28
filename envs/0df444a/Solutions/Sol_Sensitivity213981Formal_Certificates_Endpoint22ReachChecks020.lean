-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks020
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:47:11.712661+00:00
-- url     : https://prove2.me/submissions/30a765ce-5c72-4425-8af4-c511a8254daa

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks020
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks020
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
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







































































































theorem valid1300 : plan1300.Valid := valid_step _ _ _ valid465 (by decide +kernel)













































































theorem valid1339 : plan1339.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1340 : plan1340.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1341 : plan1341.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1342 : plan1342.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1343 : plan1343.Valid := valid_step _ _ _ valid503 (by decide +kernel)


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



















































































































theorem valid2650 : plan2650.Valid := valid_step _ _ _ valid1300 (by decide +kernel)












































































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























































theorem valid2812 : plan2812.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2813 : plan2813.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2814 : plan2814.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2815 : plan2815.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2816 : plan2816.Valid := valid_step _ _ _ valid1343 (by decide +kernel)
































































































































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































































































































































































theorem valid3936 : plan3936.Valid := valid_step _ _ _ valid2650 (by decide +kernel)
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













































































































theorem valid4279 : plan4279.Valid := valid_step _ _ _ valid2812 (by decide +kernel)

theorem valid4280 : plan4280.Valid := valid_step _ _ _ valid2813 (by decide +kernel)

theorem valid4281 : plan4281.Valid := valid_step _ _ _ valid2814 (by decide +kernel)

theorem valid4282 : plan4282.Valid := valid_step _ _ _ valid2815 (by decide +kernel)

theorem valid4283 : plan4283.Valid := valid_step _ _ _ valid2816 (by decide +kernel)










































































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
theorem t5_755choices : plan3936.choices=[2,5,3,3,10].map (options 5 2) := by rfl


theorem t5_755part0 : t5_755jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_755part1 : t5_755jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_755frontier : t5_755root.frontier 1=t5_755jobs := by rfl
theorem t5_755all : t5_755jobs.all (Job.check tree)=true := by
  simp only [t5_755jobs,List.all_append,List.all_nil,t5_755part0,t5_755part1,Bool.and_self]
theorem t5_755checked : Checked tree [2,5,3,3,10] := by
  refine ⟨plan3936,valid3936,t5_755choices,?_⟩
  exact check_of_frontier tree 1 t5_755root t5_755jobs t5_755frontier t5_755all
theorem t5_756choices : plan4279.choices=[2,5,3,6,6].map (options 5 3) := by rfl


theorem t5_756part0 : t5_756jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_756part1 : t5_756jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_756frontier : t5_756root.frontier 1=t5_756jobs := by rfl
theorem t5_756all : t5_756jobs.all (Job.check tree)=true := by
  simp only [t5_756jobs,List.all_append,List.all_nil,t5_756part0,t5_756part1,Bool.and_self]
theorem t5_756checked : Checked tree [2,5,3,6,6] := by
  refine ⟨plan4279,valid4279,t5_756choices,?_⟩
  exact check_of_frontier tree 1 t5_756root t5_756jobs t5_756frontier t5_756all
theorem t5_757choices : plan4280.choices=[2,5,3,6,7].map (options 5 3) := by rfl


theorem t5_757part0 : t5_757jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_757part1 : t5_757jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_757part2 : t5_757jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_757part3 : t5_757jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_757frontier : t5_757root.frontier 1=t5_757jobs := by rfl
theorem t5_757all : t5_757jobs.all (Job.check tree)=true := by
  simp only [t5_757jobs,List.all_append,List.all_nil,t5_757part0,t5_757part1,t5_757part2,t5_757part3,Bool.and_self]
theorem t5_757checked : Checked tree [2,5,3,6,7] := by
  refine ⟨plan4280,valid4280,t5_757choices,?_⟩
  exact check_of_frontier tree 1 t5_757root t5_757jobs t5_757frontier t5_757all
theorem t5_758choices : plan4281.choices=[2,5,3,6,10].map (options 5 3) := by rfl


theorem t5_758part0 : t5_758jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_758part1 : t5_758jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_758part2 : t5_758jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_758part3 : t5_758jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_758frontier : t5_758root.frontier 1=t5_758jobs := by rfl
theorem t5_758all : t5_758jobs.all (Job.check tree)=true := by
  simp only [t5_758jobs,List.all_append,List.all_nil,t5_758part0,t5_758part1,t5_758part2,t5_758part3,Bool.and_self]
theorem t5_758checked : Checked tree [2,5,3,6,10] := by
  refine ⟨plan4281,valid4281,t5_758choices,?_⟩
  exact check_of_frontier tree 1 t5_758root t5_758jobs t5_758frontier t5_758all
theorem t5_759choices : plan4282.choices=[2,5,3,7,7].map (options 5 3) := by rfl


theorem t5_759part0 : t5_759jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_759part1 : t5_759jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_759part2 : t5_759jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_759part3 : t5_759jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_759frontier : t5_759root.frontier 1=t5_759jobs := by rfl
theorem t5_759all : t5_759jobs.all (Job.check tree)=true := by
  simp only [t5_759jobs,List.all_append,List.all_nil,t5_759part0,t5_759part1,t5_759part2,t5_759part3,Bool.and_self]
theorem t5_759checked : Checked tree [2,5,3,7,7] := by
  refine ⟨plan4282,valid4282,t5_759choices,?_⟩
  exact check_of_frontier tree 1 t5_759root t5_759jobs t5_759frontier t5_759all
theorem t5_760choices : plan4283.choices=[2,5,3,10,7].map (options 5 3) := by rfl


theorem t5_760part0 : t5_760jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_760part1 : t5_760jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_760part2 : t5_760jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_760part3 : t5_760jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_760frontier : t5_760root.frontier 1=t5_760jobs := by rfl
theorem t5_760all : t5_760jobs.all (Job.check tree)=true := by
  simp only [t5_760jobs,List.all_append,List.all_nil,t5_760part0,t5_760part1,t5_760part2,t5_760part3,Bool.and_self]
theorem t5_760checked : Checked tree [2,5,3,10,7] := by
  refine ⟨plan4283,valid4283,t5_760choices,?_⟩
  exact check_of_frontier tree 1 t5_760root t5_760jobs t5_760frontier t5_760all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks020 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_755checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_756checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_757checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_758checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_759checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_760checked⟩
