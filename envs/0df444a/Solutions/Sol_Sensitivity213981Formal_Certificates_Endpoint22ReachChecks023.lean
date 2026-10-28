-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks023
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:21.079648+00:00
-- url     : https://prove2.me/submissions/03ed5538-7a2a-4d06-8e35-084b6c4a85dc

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks023
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks023
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans048
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans049
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









































































































































theorem valid453 : plan453.Valid := valid_step _ _ _ valid88 (by decide +kernel)






















































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































theorem valid1264 : plan1264.Valid := valid_step _ _ _ valid453 (by decide +kernel)
































































































































































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



























































































































theorem valid2558 : plan2558.Valid := valid_step _ _ _ valid1264 (by decide +kernel)




































































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

theorem valid3745 : plan3745.Valid := valid_step _ _ _ valid2558 (by decide +kernel)






























































































































































































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

theorem valid1464 : plan1464.Valid := valid_step _ _ _ valid524 (by decide +kernel)
















































































































































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











































































theorem valid3014 : plan3014.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3015 : plan3015.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid3016 : plan3016.Valid := valid_step _ _ _ valid1464 (by decide +kernel)

theorem valid3017 : plan3017.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid3018 : plan3018.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid3019 : plan3019.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid3020 : plan3020.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid3021 : plan3021.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid3022 : plan3022.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid3023 : plan3023.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

theorem valid3024 : plan3024.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3025 : plan3025.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid3026 : plan3026.Valid := valid_step _ _ _ valid1464 (by decide +kernel)

theorem valid3027 : plan3027.Valid := valid_step _ _ _ valid1443 (by decide +kernel)


























































































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













































































































































































theorem valid4695 : plan4695.Valid := valid_step _ _ _ valid3014 (by decide +kernel)

theorem valid4696 : plan4696.Valid := valid_step _ _ _ valid3015 (by decide +kernel)

theorem valid4697 : plan4697.Valid := valid_step _ _ _ valid3016 (by decide +kernel)

theorem valid4698 : plan4698.Valid := valid_step _ _ _ valid3017 (by decide +kernel)

theorem valid4699 : plan4699.Valid := valid_step _ _ _ valid3018 (by decide +kernel)

theorem valid4700 : plan4700.Valid := valid_step _ _ _ valid3019 (by decide +kernel)

theorem valid4701 : plan4701.Valid := valid_step _ _ _ valid3020 (by decide +kernel)

theorem valid4702 : plan4702.Valid := valid_step _ _ _ valid3021 (by decide +kernel)

theorem valid4703 : plan4703.Valid := valid_step _ _ _ valid3022 (by decide +kernel)

theorem valid4704 : plan4704.Valid := valid_step _ _ _ valid3023 (by decide +kernel)
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

theorem valid4705 : plan4705.Valid := valid_step _ _ _ valid3024 (by decide +kernel)

theorem valid4706 : plan4706.Valid := valid_step _ _ _ valid3025 (by decide +kernel)

theorem valid4707 : plan4707.Valid := valid_step _ _ _ valid3026 (by decide +kernel)

theorem valid4708 : plan4708.Valid := valid_step _ _ _ valid3027 (by decide +kernel)
























































































































































































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
theorem t5_805choices : plan4695.choices=[2,5,10,7,7].map (options 5 4) := by rfl


theorem t5_805part0 : t5_805jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_805part1 : t5_805jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_805frontier : t5_805root.frontier 1=t5_805jobs := by rfl
theorem t5_805all : t5_805jobs.all (Job.check tree)=true := by
  simp only [t5_805jobs,List.all_append,List.all_nil,t5_805part0,t5_805part1,Bool.and_self]
theorem t5_805checked : Checked tree [2,5,10,7,7] := by
  refine ⟨plan4695,valid4695,t5_805choices,?_⟩
  exact check_of_frontier tree 1 t5_805root t5_805jobs t5_805frontier t5_805all
theorem t5_806choices : plan4696.choices=[2,5,10,10,7].map (options 5 4) := by rfl


theorem t5_806part0 : t5_806jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_806part1 : t5_806jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_806frontier : t5_806root.frontier 1=t5_806jobs := by rfl
theorem t5_806all : t5_806jobs.all (Job.check tree)=true := by
  simp only [t5_806jobs,List.all_append,List.all_nil,t5_806part0,t5_806part1,Bool.and_self]
theorem t5_806checked : Checked tree [2,5,10,10,7] := by
  refine ⟨plan4696,valid4696,t5_806choices,?_⟩
  exact check_of_frontier tree 1 t5_806root t5_806jobs t5_806frontier t5_806all
theorem t5_807choices : plan4697.choices=[2,5,10,10,10].map (options 5 4) := by rfl


theorem t5_807part0 : t5_807jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_807frontier : t5_807root.frontier 0=t5_807jobs := by rfl
theorem t5_807all : t5_807jobs.all (Job.check tree)=true := by
  simp only [t5_807jobs,List.all_append,List.all_nil,t5_807part0,Bool.and_self]
theorem t5_807checked : Checked tree [2,5,10,10,10] := by
  refine ⟨plan4697,valid4697,t5_807choices,?_⟩
  exact check_of_frontier tree 0 t5_807root t5_807jobs t5_807frontier t5_807all
theorem t5_808choices : plan4698.choices=[2,6,6,6,6].map (options 5 4) := by rfl


theorem t5_808part0 : t5_808jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_808frontier : t5_808root.frontier 0=t5_808jobs := by rfl
theorem t5_808all : t5_808jobs.all (Job.check tree)=true := by
  simp only [t5_808jobs,List.all_append,List.all_nil,t5_808part0,Bool.and_self]
theorem t5_808checked : Checked tree [2,6,6,6,6] := by
  refine ⟨plan4698,valid4698,t5_808choices,?_⟩
  exact check_of_frontier tree 0 t5_808root t5_808jobs t5_808frontier t5_808all
theorem t5_809choices : plan4699.choices=[2,6,6,6,7].map (options 5 4) := by rfl


theorem t5_809part0 : t5_809jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_809frontier : t5_809root.frontier 0=t5_809jobs := by rfl
theorem t5_809all : t5_809jobs.all (Job.check tree)=true := by
  simp only [t5_809jobs,List.all_append,List.all_nil,t5_809part0,Bool.and_self]
theorem t5_809checked : Checked tree [2,6,6,6,7] := by
  refine ⟨plan4699,valid4699,t5_809choices,?_⟩
  exact check_of_frontier tree 0 t5_809root t5_809jobs t5_809frontier t5_809all
theorem t5_810choices : plan4700.choices=[2,6,6,6,10].map (options 5 4) := by rfl


theorem t5_810part0 : t5_810jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_810frontier : t5_810root.frontier 0=t5_810jobs := by rfl
theorem t5_810all : t5_810jobs.all (Job.check tree)=true := by
  simp only [t5_810jobs,List.all_append,List.all_nil,t5_810part0,Bool.and_self]
theorem t5_810checked : Checked tree [2,6,6,6,10] := by
  refine ⟨plan4700,valid4700,t5_810choices,?_⟩
  exact check_of_frontier tree 0 t5_810root t5_810jobs t5_810frontier t5_810all
theorem t5_811choices : plan4701.choices=[2,6,6,7,7].map (options 5 4) := by rfl


theorem t5_811part0 : t5_811jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_811part1 : t5_811jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_811frontier : t5_811root.frontier 1=t5_811jobs := by rfl
theorem t5_811all : t5_811jobs.all (Job.check tree)=true := by
  simp only [t5_811jobs,List.all_append,List.all_nil,t5_811part0,t5_811part1,Bool.and_self]
theorem t5_811checked : Checked tree [2,6,6,7,7] := by
  refine ⟨plan4701,valid4701,t5_811choices,?_⟩
  exact check_of_frontier tree 1 t5_811root t5_811jobs t5_811frontier t5_811all
theorem t5_812choices : plan4702.choices=[2,6,6,10,7].map (options 5 4) := by rfl


theorem t5_812part0 : t5_812jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_812part1 : t5_812jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_812frontier : t5_812root.frontier 1=t5_812jobs := by rfl
theorem t5_812all : t5_812jobs.all (Job.check tree)=true := by
  simp only [t5_812jobs,List.all_append,List.all_nil,t5_812part0,t5_812part1,Bool.and_self]
theorem t5_812checked : Checked tree [2,6,6,10,7] := by
  refine ⟨plan4702,valid4702,t5_812choices,?_⟩
  exact check_of_frontier tree 1 t5_812root t5_812jobs t5_812frontier t5_812all
theorem t5_813choices : plan4703.choices=[2,6,6,10,10].map (options 5 4) := by rfl


theorem t5_813part0 : t5_813jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_813frontier : t5_813root.frontier 0=t5_813jobs := by rfl
theorem t5_813all : t5_813jobs.all (Job.check tree)=true := by
  simp only [t5_813jobs,List.all_append,List.all_nil,t5_813part0,Bool.and_self]
theorem t5_813checked : Checked tree [2,6,6,10,10] := by
  refine ⟨plan4703,valid4703,t5_813choices,?_⟩
  exact check_of_frontier tree 0 t5_813root t5_813jobs t5_813frontier t5_813all
theorem t5_814choices : plan4704.choices=[2,6,7,7,7].map (options 5 4) := by rfl


theorem t5_814part0 : t5_814jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_814part1 : t5_814jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_814frontier : t5_814root.frontier 1=t5_814jobs := by rfl
theorem t5_814all : t5_814jobs.all (Job.check tree)=true := by
  simp only [t5_814jobs,List.all_append,List.all_nil,t5_814part0,t5_814part1,Bool.and_self]
theorem t5_814checked : Checked tree [2,6,7,7,7] := by
  refine ⟨plan4704,valid4704,t5_814choices,?_⟩
  exact check_of_frontier tree 1 t5_814root t5_814jobs t5_814frontier t5_814all
theorem t5_815choices : plan4705.choices=[2,6,10,7,7].map (options 5 4) := by rfl


theorem t5_815part0 : t5_815jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_815part1 : t5_815jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_815part2 : t5_815jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_815frontier : t5_815root.frontier 2=t5_815jobs := by rfl
theorem t5_815all : t5_815jobs.all (Job.check tree)=true := by
  simp only [t5_815jobs,List.all_append,List.all_nil,t5_815part0,t5_815part1,t5_815part2,Bool.and_self]
theorem t5_815checked : Checked tree [2,6,10,7,7] := by
  refine ⟨plan4705,valid4705,t5_815choices,?_⟩
  exact check_of_frontier tree 2 t5_815root t5_815jobs t5_815frontier t5_815all
theorem t5_816choices : plan4706.choices=[2,6,10,10,7].map (options 5 4) := by rfl


theorem t5_816part0 : t5_816jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_816part1 : t5_816jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_816frontier : t5_816root.frontier 2=t5_816jobs := by rfl
theorem t5_816all : t5_816jobs.all (Job.check tree)=true := by
  simp only [t5_816jobs,List.all_append,List.all_nil,t5_816part0,t5_816part1,Bool.and_self]
theorem t5_816checked : Checked tree [2,6,10,10,7] := by
  refine ⟨plan4706,valid4706,t5_816choices,?_⟩
  exact check_of_frontier tree 2 t5_816root t5_816jobs t5_816frontier t5_816all
theorem t5_817choices : plan4707.choices=[2,6,10,10,10].map (options 5 4) := by rfl


theorem t5_817part0 : t5_817jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_817frontier : t5_817root.frontier 0=t5_817jobs := by rfl
theorem t5_817all : t5_817jobs.all (Job.check tree)=true := by
  simp only [t5_817jobs,List.all_append,List.all_nil,t5_817part0,Bool.and_self]
theorem t5_817checked : Checked tree [2,6,10,10,10] := by
  refine ⟨plan4707,valid4707,t5_817choices,?_⟩
  exact check_of_frontier tree 0 t5_817root t5_817jobs t5_817frontier t5_817all
theorem t5_818choices : plan4708.choices=[2,7,7,7,7].map (options 5 4) := by rfl


theorem t5_818part0 : t5_818jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_818frontier : t5_818root.frontier 0=t5_818jobs := by rfl
theorem t5_818all : t5_818jobs.all (Job.check tree)=true := by
  simp only [t5_818jobs,List.all_append,List.all_nil,t5_818part0,Bool.and_self]
theorem t5_818checked : Checked tree [2,7,7,7,7] := by
  refine ⟨plan4708,valid4708,t5_818choices,?_⟩
  exact check_of_frontier tree 0 t5_818root t5_818jobs t5_818frontier t5_818all
theorem t5_819choices : plan3745.choices=[2,9,3,3,3].map (options 5 1) := by rfl


theorem t5_819part0 : t5_819jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_819frontier : t5_819root.frontier 0=t5_819jobs := by rfl
theorem t5_819all : t5_819jobs.all (Job.check tree)=true := by
  simp only [t5_819jobs,List.all_append,List.all_nil,t5_819part0,Bool.and_self]
theorem t5_819checked : Checked tree [2,9,3,3,3] := by
  refine ⟨plan3745,valid3745,t5_819choices,?_⟩
  exact check_of_frontier tree 0 t5_819root t5_819jobs t5_819frontier t5_819all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks023 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_815checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_805checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_816checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_817checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_818checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_819checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_806checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_807checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_808checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_809checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_810checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_811checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_812checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_813checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_814checked⟩
