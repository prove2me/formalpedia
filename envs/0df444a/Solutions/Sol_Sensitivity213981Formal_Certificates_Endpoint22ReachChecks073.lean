-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks073
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:18:16.68631+00:00
-- url     : https://prove2.me/submissions/7caba473-cde6-417f-9031-a12ed1fd47c8

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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































































theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)
























































































































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





































































































































































theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)












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



































theorem valid1554 : plan1554.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1555 : plan1555.Valid := valid_step _ _ _ valid564 (by decide +kernel)



























theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)


























































































































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















































































































theorem valid3320 : plan3320.Valid := valid_step _ _ _ valid1554 (by decide +kernel)

theorem valid3321 : plan3321.Valid := valid_step _ _ _ valid1555 (by decide +kernel)














































































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











































































theorem valid3398 : plan3398.Valid := valid_step _ _ _ valid1569 (by decide +kernel)

theorem valid3399 : plan3399.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3400 : plan3400.Valid := valid_step _ _ _ valid1571 (by decide +kernel)
















































































































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











































theorem valid5494 : plan5494.Valid := valid_step _ _ _ valid3320 (by decide +kernel)

theorem valid5495 : plan5495.Valid := valid_step _ _ _ valid3321 (by decide +kernel)


















































































































































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































































































































theorem valid5632 : plan5632.Valid := valid_step _ _ _ valid3398 (by decide +kernel)

theorem valid5633 : plan5633.Valid := valid_step _ _ _ valid3399 (by decide +kernel)

theorem valid5634 : plan5634.Valid := valid_step _ _ _ valid3400 (by decide +kernel)




























































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

















































































































theorem valid6585 : plan6585.Valid := valid_step _ _ _ valid5494 (by decide +kernel)

theorem valid6586 : plan6586.Valid := valid_step _ _ _ valid5495 (by decide +kernel)












































































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



theorem valid6914 : plan6914.Valid := valid_step _ _ _ valid5632 (by decide +kernel)

theorem valid6915 : plan6915.Valid := valid_step _ _ _ valid5633 (by decide +kernel)

theorem valid6916 : plan6916.Valid := valid_step _ _ _ valid5634 (by decide +kernel)
























































































































































































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
theorem t6_649choices : plan6585.choices=[2,3,3,10,10,7].map (options 6 3) := by rfl


theorem t6_649part0 : t6_649jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_649part1 : t6_649jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_649part2 : t6_649jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_649part3 : t6_649jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_649part4 : t6_649jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_649part5 : t6_649jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_649part6 : t6_649jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_649part7 : t6_649jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_649frontier : t6_649root.frontier 2=t6_649jobs := by rfl
theorem t6_649all : t6_649jobs.all (Job.check tree)=true := by
  simp only [t6_649jobs,List.all_append,List.all_nil,t6_649part0,t6_649part1,t6_649part2,t6_649part3,t6_649part4,t6_649part5,t6_649part6,t6_649part7,Bool.and_self]
theorem t6_649checked : Checked tree [2,3,3,10,10,7] := by
  refine ⟨plan6585,valid6585,t6_649choices,?_⟩
  exact check_of_frontier tree 2 t6_649root t6_649jobs t6_649frontier t6_649all
theorem t6_650choices : plan6586.choices=[2,3,3,10,10,10].map (options 6 3) := by rfl


theorem t6_650part0 : t6_650jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_650part1 : t6_650jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_650frontier : t6_650root.frontier 1=t6_650jobs := by rfl
theorem t6_650all : t6_650jobs.all (Job.check tree)=true := by
  simp only [t6_650jobs,List.all_append,List.all_nil,t6_650part0,t6_650part1,Bool.and_self]
theorem t6_650checked : Checked tree [2,3,3,10,10,10] := by
  refine ⟨plan6586,valid6586,t6_650choices,?_⟩
  exact check_of_frontier tree 1 t6_650root t6_650jobs t6_650frontier t6_650all
theorem t6_651choices : plan6914.choices=[2,3,6,6,6,6].map (options 6 4) := by rfl


theorem t6_651part0 : t6_651jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_651frontier : t6_651root.frontier 0=t6_651jobs := by rfl
theorem t6_651all : t6_651jobs.all (Job.check tree)=true := by
  simp only [t6_651jobs,List.all_append,List.all_nil,t6_651part0,Bool.and_self]
theorem t6_651checked : Checked tree [2,3,6,6,6,6] := by
  refine ⟨plan6914,valid6914,t6_651choices,?_⟩
  exact check_of_frontier tree 0 t6_651root t6_651jobs t6_651frontier t6_651all
theorem t6_652choices : plan6915.choices=[2,3,6,6,6,7].map (options 6 4) := by rfl


theorem t6_652part0 : t6_652jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_652part1 : t6_652jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_652part2 : t6_652jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_652part3 : t6_652jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_652part4 : t6_652jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_652frontier : t6_652root.frontier 2=t6_652jobs := by rfl
theorem t6_652all : t6_652jobs.all (Job.check tree)=true := by
  simp only [t6_652jobs,List.all_append,List.all_nil,t6_652part0,t6_652part1,t6_652part2,t6_652part3,t6_652part4,Bool.and_self]
theorem t6_652checked : Checked tree [2,3,6,6,6,7] := by
  refine ⟨plan6915,valid6915,t6_652choices,?_⟩
  exact check_of_frontier tree 2 t6_652root t6_652jobs t6_652frontier t6_652all
theorem t6_653choices : plan6916.choices=[2,3,6,6,6,10].map (options 6 4) := by rfl


theorem t6_653part0 : t6_653jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_653part1 : t6_653jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_653part2 : t6_653jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_653frontier : t6_653root.frontier 1=t6_653jobs := by rfl
theorem t6_653all : t6_653jobs.all (Job.check tree)=true := by
  simp only [t6_653jobs,List.all_append,List.all_nil,t6_653part0,t6_653part1,t6_653part2,Bool.and_self]
theorem t6_653checked : Checked tree [2,3,6,6,6,10] := by
  refine ⟨plan6916,valid6916,t6_653choices,?_⟩
  exact check_of_frontier tree 1 t6_653root t6_653jobs t6_653frontier t6_653all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks073 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_652checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_653checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_649checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_650checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_651checked⟩
