-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks090
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:32:29.333992+00:00
-- url     : https://prove2.me/submissions/4c0073b7-e77f-411c-bf5f-a51c33300fc2

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
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











































theorem valid118 : plan118.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid123 : plan123.Valid := valid_step _ _ _ valid0 (by decide +kernel)





















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

























































































































theorem valid541 : plan541.Valid := valid_step _ _ _ valid118 (by decide +kernel)









theorem valid546 : plan546.Valid := valid_step _ _ _ valid123 (by decide +kernel)




























































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







































































































































theorem valid1508 : plan1508.Valid := valid_step _ _ _ valid541 (by decide +kernel)















theorem valid1516 : plan1516.Valid := valid_step _ _ _ valid546 (by decide +kernel)








































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



























































































































































theorem valid3246 : plan3246.Valid := valid_step _ _ _ valid1508 (by decide +kernel)




































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

theorem valid3265 : plan3265.Valid := valid_step _ _ _ valid1516 (by decide +kernel)






























































































































































































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

































































































































































theorem valid5361 : plan5361.Valid := valid_step _ _ _ valid3246 (by decide +kernel)






























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





































































theorem valid5411 : plan5411.Valid := valid_step _ _ _ valid3265 (by decide +kernel)


























































































































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











































































































































theorem valid6310 : plan6310.Valid := valid_step _ _ _ valid5361 (by decide +kernel)




















































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





















































theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)











































theorem valid3507 : plan3507.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

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





































































theorem valid5891 : plan5891.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5892 : plan5892.Valid := valid_step _ _ _ valid3484 (by decide +kernel)

theorem valid5893 : plan5893.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5894 : plan5894.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

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

























































































































theorem valid6397 : plan6397.Valid := valid_step _ _ _ valid5411 (by decide +kernel)






































































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























































































































































theorem valid7372 : plan7372.Valid := valid_step _ _ _ valid5891 (by decide +kernel)

theorem valid7373 : plan7373.Valid := valid_step _ _ _ valid5892 (by decide +kernel)

theorem valid7374 : plan7374.Valid := valid_step _ _ _ valid5893 (by decide +kernel)

theorem valid7375 : plan7375.Valid := valid_step _ _ _ valid5894 (by decide +kernel)

theorem valid7376 : plan7376.Valid := valid_step _ _ _ valid5895 (by decide +kernel)

theorem valid7377 : plan7377.Valid := valid_step _ _ _ valid5896 (by decide +kernel)

theorem valid7378 : plan7378.Valid := valid_step _ _ _ valid5897 (by decide +kernel)

theorem valid7379 : plan7379.Valid := valid_step _ _ _ valid5898 (by decide +kernel)


























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
theorem t6_761choices : plan7372.choices=[2,6,6,10,10,7].map (options 6 5) := by rfl


theorem t6_761part0 : t6_761jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_761part1 : t6_761jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_761frontier : t6_761root.frontier 2=t6_761jobs := by rfl
theorem t6_761all : t6_761jobs.all (Job.check tree)=true := by
  simp only [t6_761jobs,List.all_append,List.all_nil,t6_761part0,t6_761part1,Bool.and_self]
theorem t6_761checked : Checked tree [2,6,6,10,10,7] := by
  refine ⟨plan7372,valid7372,t6_761choices,?_⟩
  exact check_of_frontier tree 2 t6_761root t6_761jobs t6_761frontier t6_761all
theorem t6_762choices : plan7373.choices=[2,6,6,10,10,10].map (options 6 5) := by rfl


theorem t6_762part0 : t6_762jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_762frontier : t6_762root.frontier 0=t6_762jobs := by rfl
theorem t6_762all : t6_762jobs.all (Job.check tree)=true := by
  simp only [t6_762jobs,List.all_append,List.all_nil,t6_762part0,Bool.and_self]
theorem t6_762checked : Checked tree [2,6,6,10,10,10] := by
  refine ⟨plan7373,valid7373,t6_762choices,?_⟩
  exact check_of_frontier tree 0 t6_762root t6_762jobs t6_762frontier t6_762all
theorem t6_763choices : plan7374.choices=[2,6,7,7,7,7].map (options 6 5) := by rfl


theorem t6_763part0 : t6_763jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_763part1 : t6_763jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_763part2 : t6_763jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_763frontier : t6_763root.frontier 2=t6_763jobs := by rfl
theorem t6_763all : t6_763jobs.all (Job.check tree)=true := by
  simp only [t6_763jobs,List.all_append,List.all_nil,t6_763part0,t6_763part1,t6_763part2,Bool.and_self]
theorem t6_763checked : Checked tree [2,6,7,7,7,7] := by
  refine ⟨plan7374,valid7374,t6_763choices,?_⟩
  exact check_of_frontier tree 2 t6_763root t6_763jobs t6_763frontier t6_763all
theorem t6_764choices : plan7375.choices=[2,6,10,7,7,7].map (options 6 5) := by rfl


theorem t6_764part0 : t6_764jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_764part1 : t6_764jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_764part2 : t6_764jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_764part3 : t6_764jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_764part4 : t6_764jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_764frontier : t6_764root.frontier 2=t6_764jobs := by rfl
theorem t6_764all : t6_764jobs.all (Job.check tree)=true := by
  simp only [t6_764jobs,List.all_append,List.all_nil,t6_764part0,t6_764part1,t6_764part2,t6_764part3,t6_764part4,Bool.and_self]
theorem t6_764checked : Checked tree [2,6,10,7,7,7] := by
  refine ⟨plan7375,valid7375,t6_764choices,?_⟩
  exact check_of_frontier tree 2 t6_764root t6_764jobs t6_764frontier t6_764all
theorem t6_765choices : plan7376.choices=[2,6,10,10,7,7].map (options 6 5) := by rfl


theorem t6_765part0 : t6_765jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_765part1 : t6_765jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_765part2 : t6_765jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_765part3 : t6_765jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_765frontier : t6_765root.frontier 2=t6_765jobs := by rfl
theorem t6_765all : t6_765jobs.all (Job.check tree)=true := by
  simp only [t6_765jobs,List.all_append,List.all_nil,t6_765part0,t6_765part1,t6_765part2,t6_765part3,Bool.and_self]
theorem t6_765checked : Checked tree [2,6,10,10,7,7] := by
  refine ⟨plan7376,valid7376,t6_765choices,?_⟩
  exact check_of_frontier tree 2 t6_765root t6_765jobs t6_765frontier t6_765all
theorem t6_766choices : plan7377.choices=[2,6,10,10,10,7].map (options 6 5) := by rfl


theorem t6_766part0 : t6_766jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_766part1 : t6_766jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_766frontier : t6_766root.frontier 2=t6_766jobs := by rfl
theorem t6_766all : t6_766jobs.all (Job.check tree)=true := by
  simp only [t6_766jobs,List.all_append,List.all_nil,t6_766part0,t6_766part1,Bool.and_self]
theorem t6_766checked : Checked tree [2,6,10,10,10,7] := by
  refine ⟨plan7377,valid7377,t6_766choices,?_⟩
  exact check_of_frontier tree 2 t6_766root t6_766jobs t6_766frontier t6_766all
theorem t6_767choices : plan7378.choices=[2,6,10,10,10,10].map (options 6 5) := by rfl


theorem t6_767part0 : t6_767jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_767frontier : t6_767root.frontier 0=t6_767jobs := by rfl
theorem t6_767all : t6_767jobs.all (Job.check tree)=true := by
  simp only [t6_767jobs,List.all_append,List.all_nil,t6_767part0,Bool.and_self]
theorem t6_767checked : Checked tree [2,6,10,10,10,10] := by
  refine ⟨plan7378,valid7378,t6_767choices,?_⟩
  exact check_of_frontier tree 0 t6_767root t6_767jobs t6_767frontier t6_767all
theorem t6_768choices : plan7379.choices=[2,7,7,7,7,7].map (options 6 5) := by rfl


theorem t6_768part0 : t6_768jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_768part1 : t6_768jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_768frontier : t6_768root.frontier 1=t6_768jobs := by rfl
theorem t6_768all : t6_768jobs.all (Job.check tree)=true := by
  simp only [t6_768jobs,List.all_append,List.all_nil,t6_768part0,t6_768part1,Bool.and_self]
theorem t6_768checked : Checked tree [2,7,7,7,7,7] := by
  refine ⟨plan7379,valid7379,t6_768choices,?_⟩
  exact check_of_frontier tree 1 t6_768root t6_768jobs t6_768frontier t6_768all
theorem t6_769choices : plan6310.choices=[2,9,3,3,3,3].map (options 6 1) := by rfl


theorem t6_769part0 : t6_769jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_769frontier : t6_769root.frontier 0=t6_769jobs := by rfl
theorem t6_769all : t6_769jobs.all (Job.check tree)=true := by
  simp only [t6_769jobs,List.all_append,List.all_nil,t6_769part0,Bool.and_self]
theorem t6_769checked : Checked tree [2,9,3,3,3,3] := by
  refine ⟨plan6310,valid6310,t6_769choices,?_⟩
  exact check_of_frontier tree 0 t6_769root t6_769jobs t6_769frontier t6_769all
theorem t6_770choices : plan6397.choices=[2,9,3,3,3,6].map (options 6 2) := by rfl


theorem t6_770part0 : t6_770jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_770frontier : t6_770root.frontier 0=t6_770jobs := by rfl
theorem t6_770all : t6_770jobs.all (Job.check tree)=true := by
  simp only [t6_770jobs,List.all_append,List.all_nil,t6_770part0,Bool.and_self]
theorem t6_770checked : Checked tree [2,9,3,3,3,6] := by
  refine ⟨plan6397,valid6397,t6_770choices,?_⟩
  exact check_of_frontier tree 0 t6_770root t6_770jobs t6_770frontier t6_770all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks090 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_765checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_766checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_767checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_768checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_769checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_770checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_761checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_762checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_763checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_764checked⟩
