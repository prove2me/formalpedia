-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks057
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:07:25.957716+00:00
-- url     : https://prove2.me/submissions/27571587-8981-4af8-8c57-d936fec09e68

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
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



































































































































































theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)

theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid573 : plan573.Valid := valid_step _ _ _ valid132 (by decide +kernel)






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





























































































































































































theorem valid1535 : plan1535.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1536 : plan1536.Valid := valid_step _ _ _ valid563 (by decide +kernel)
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

theorem valid1537 : plan1537.Valid := valid_step _ _ _ valid564 (by decide +kernel)































































theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)

theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)









theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1582 : plan1582.Valid := valid_step _ _ _ valid573 (by decide +kernel)




































































































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

























































































theorem valid3309 : plan3309.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3310 : plan3310.Valid := valid_step _ _ _ valid1536 (by decide +kernel)

theorem valid3311 : plan3311.Valid := valid_step _ _ _ valid1537 (by decide +kernel)

































































































theorem valid3360 : plan3360.Valid := valid_step _ _ _ valid1569 (by decide +kernel)
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

theorem valid3361 : plan3361.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3362 : plan3362.Valid := valid_step _ _ _ valid1571 (by decide +kernel)

theorem valid3363 : plan3363.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3364 : plan3364.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3365 : plan3365.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3366 : plan3366.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3367 : plan3367.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3368 : plan3368.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3369 : plan3369.Valid := valid_step _ _ _ valid1582 (by decide +kernel)














































































































































































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





































































theorem valid5507 : plan5507.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5508 : plan5508.Valid := valid_step _ _ _ valid3310 (by decide +kernel)

theorem valid5509 : plan5509.Valid := valid_step _ _ _ valid3311 (by decide +kernel)






















































































































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















































































































































































theorem valid6520 : plan6520.Valid := valid_step _ _ _ valid5507 (by decide +kernel)

theorem valid6521 : plan6521.Valid := valid_step _ _ _ valid5508 (by decide +kernel)

theorem valid6522 : plan6522.Valid := valid_step _ _ _ valid5509 (by decide +kernel)












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







theorem valid5668 : plan5668.Valid := valid_step _ _ _ valid3360 (by decide +kernel)

theorem valid5669 : plan5669.Valid := valid_step _ _ _ valid3361 (by decide +kernel)

theorem valid5670 : plan5670.Valid := valid_step _ _ _ valid3362 (by decide +kernel)

theorem valid5671 : plan5671.Valid := valid_step _ _ _ valid3363 (by decide +kernel)

theorem valid5672 : plan5672.Valid := valid_step _ _ _ valid3364 (by decide +kernel)

theorem valid5673 : plan5673.Valid := valid_step _ _ _ valid3365 (by decide +kernel)

theorem valid5674 : plan5674.Valid := valid_step _ _ _ valid3366 (by decide +kernel)

theorem valid5675 : plan5675.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5676 : plan5676.Valid := valid_step _ _ _ valid3368 (by decide +kernel)

theorem valid5677 : plan5677.Valid := valid_step _ _ _ valid3369 (by decide +kernel)






































































































































































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



























theorem valid6830 : plan6830.Valid := valid_step _ _ _ valid5668 (by decide +kernel)

theorem valid6831 : plan6831.Valid := valid_step _ _ _ valid5669 (by decide +kernel)

theorem valid6832 : plan6832.Valid := valid_step _ _ _ valid5670 (by decide +kernel)

theorem valid6833 : plan6833.Valid := valid_step _ _ _ valid5671 (by decide +kernel)

theorem valid6834 : plan6834.Valid := valid_step _ _ _ valid5672 (by decide +kernel)

theorem valid6835 : plan6835.Valid := valid_step _ _ _ valid5673 (by decide +kernel)

theorem valid6836 : plan6836.Valid := valid_step _ _ _ valid5674 (by decide +kernel)

theorem valid6837 : plan6837.Valid := valid_step _ _ _ valid5675 (by decide +kernel)

theorem valid6838 : plan6838.Valid := valid_step _ _ _ valid5676 (by decide +kernel)

theorem valid6839 : plan6839.Valid := valid_step _ _ _ valid5677 (by decide +kernel)


















































































































































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
theorem t6_361choices : plan6520.choices=[1,5,3,3,7,7].map (options 6 3) := by rfl


theorem t6_361part0 : t6_361jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_361part1 : t6_361jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_361frontier : t6_361root.frontier 1=t6_361jobs := by rfl
theorem t6_361all : t6_361jobs.all (Job.check tree)=true := by
  simp only [t6_361jobs,List.all_append,List.all_nil,t6_361part0,t6_361part1,Bool.and_self]
theorem t6_361checked : Checked tree [1,5,3,3,7,7] := by
  refine ⟨plan6520,valid6520,t6_361choices,?_⟩
  exact check_of_frontier tree 1 t6_361root t6_361jobs t6_361frontier t6_361all
theorem t6_362choices : plan6521.choices=[1,5,3,3,10,7].map (options 6 3) := by rfl


theorem t6_362part0 : t6_362jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_362part1 : t6_362jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_362frontier : t6_362root.frontier 1=t6_362jobs := by rfl
theorem t6_362all : t6_362jobs.all (Job.check tree)=true := by
  simp only [t6_362jobs,List.all_append,List.all_nil,t6_362part0,t6_362part1,Bool.and_self]
theorem t6_362checked : Checked tree [1,5,3,3,10,7] := by
  refine ⟨plan6521,valid6521,t6_362choices,?_⟩
  exact check_of_frontier tree 1 t6_362root t6_362jobs t6_362frontier t6_362all
theorem t6_363choices : plan6522.choices=[1,5,3,3,10,10].map (options 6 3) := by rfl


theorem t6_363part0 : t6_363jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_363frontier : t6_363root.frontier 0=t6_363jobs := by rfl
theorem t6_363all : t6_363jobs.all (Job.check tree)=true := by
  simp only [t6_363jobs,List.all_append,List.all_nil,t6_363part0,Bool.and_self]
theorem t6_363checked : Checked tree [1,5,3,3,10,10] := by
  refine ⟨plan6522,valid6522,t6_363choices,?_⟩
  exact check_of_frontier tree 0 t6_363root t6_363jobs t6_363frontier t6_363all
theorem t6_364choices : plan6830.choices=[1,5,3,6,6,6].map (options 6 4) := by rfl


theorem t6_364part0 : t6_364jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_364frontier : t6_364root.frontier 0=t6_364jobs := by rfl
theorem t6_364all : t6_364jobs.all (Job.check tree)=true := by
  simp only [t6_364jobs,List.all_append,List.all_nil,t6_364part0,Bool.and_self]
theorem t6_364checked : Checked tree [1,5,3,6,6,6] := by
  refine ⟨plan6830,valid6830,t6_364choices,?_⟩
  exact check_of_frontier tree 0 t6_364root t6_364jobs t6_364frontier t6_364all
theorem t6_365choices : plan6831.choices=[1,5,3,6,6,7].map (options 6 4) := by rfl


theorem t6_365part0 : t6_365jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_365part1 : t6_365jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_365frontier : t6_365root.frontier 1=t6_365jobs := by rfl
theorem t6_365all : t6_365jobs.all (Job.check tree)=true := by
  simp only [t6_365jobs,List.all_append,List.all_nil,t6_365part0,t6_365part1,Bool.and_self]
theorem t6_365checked : Checked tree [1,5,3,6,6,7] := by
  refine ⟨plan6831,valid6831,t6_365choices,?_⟩
  exact check_of_frontier tree 1 t6_365root t6_365jobs t6_365frontier t6_365all
theorem t6_366choices : plan6832.choices=[1,5,3,6,6,10].map (options 6 4) := by rfl


theorem t6_366part0 : t6_366jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_366frontier : t6_366root.frontier 0=t6_366jobs := by rfl
theorem t6_366all : t6_366jobs.all (Job.check tree)=true := by
  simp only [t6_366jobs,List.all_append,List.all_nil,t6_366part0,Bool.and_self]
theorem t6_366checked : Checked tree [1,5,3,6,6,10] := by
  refine ⟨plan6832,valid6832,t6_366choices,?_⟩
  exact check_of_frontier tree 0 t6_366root t6_366jobs t6_366frontier t6_366all
theorem t6_367choices : plan6833.choices=[1,5,3,6,7,7].map (options 6 4) := by rfl


theorem t6_367part0 : t6_367jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_367part1 : t6_367jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_367part2 : t6_367jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_367frontier : t6_367root.frontier 2=t6_367jobs := by rfl
theorem t6_367all : t6_367jobs.all (Job.check tree)=true := by
  simp only [t6_367jobs,List.all_append,List.all_nil,t6_367part0,t6_367part1,t6_367part2,Bool.and_self]
theorem t6_367checked : Checked tree [1,5,3,6,7,7] := by
  refine ⟨plan6833,valid6833,t6_367choices,?_⟩
  exact check_of_frontier tree 2 t6_367root t6_367jobs t6_367frontier t6_367all
theorem t6_368choices : plan6834.choices=[1,5,3,6,10,7].map (options 6 4) := by rfl


theorem t6_368part0 : t6_368jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_368part1 : t6_368jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_368part2 : t6_368jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_368frontier : t6_368root.frontier 2=t6_368jobs := by rfl
theorem t6_368all : t6_368jobs.all (Job.check tree)=true := by
  simp only [t6_368jobs,List.all_append,List.all_nil,t6_368part0,t6_368part1,t6_368part2,Bool.and_self]
theorem t6_368checked : Checked tree [1,5,3,6,10,7] := by
  refine ⟨plan6834,valid6834,t6_368choices,?_⟩
  exact check_of_frontier tree 2 t6_368root t6_368jobs t6_368frontier t6_368all
theorem t6_369choices : plan6835.choices=[1,5,3,6,10,10].map (options 6 4) := by rfl


theorem t6_369part0 : t6_369jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_369frontier : t6_369root.frontier 0=t6_369jobs := by rfl
theorem t6_369all : t6_369jobs.all (Job.check tree)=true := by
  simp only [t6_369jobs,List.all_append,List.all_nil,t6_369part0,Bool.and_self]
theorem t6_369checked : Checked tree [1,5,3,6,10,10] := by
  refine ⟨plan6835,valid6835,t6_369choices,?_⟩
  exact check_of_frontier tree 0 t6_369root t6_369jobs t6_369frontier t6_369all
theorem t6_370choices : plan6836.choices=[1,5,3,7,7,7].map (options 6 4) := by rfl


theorem t6_370part0 : t6_370jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_370part1 : t6_370jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_370part2 : t6_370jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_370frontier : t6_370root.frontier 1=t6_370jobs := by rfl
theorem t6_370all : t6_370jobs.all (Job.check tree)=true := by
  simp only [t6_370jobs,List.all_append,List.all_nil,t6_370part0,t6_370part1,t6_370part2,Bool.and_self]
theorem t6_370checked : Checked tree [1,5,3,7,7,7] := by
  refine ⟨plan6836,valid6836,t6_370choices,?_⟩
  exact check_of_frontier tree 1 t6_370root t6_370jobs t6_370frontier t6_370all
theorem t6_371choices : plan6837.choices=[1,5,3,10,7,7].map (options 6 4) := by rfl


theorem t6_371part0 : t6_371jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_371part1 : t6_371jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_371part2 : t6_371jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_371frontier : t6_371root.frontier 2=t6_371jobs := by rfl
theorem t6_371all : t6_371jobs.all (Job.check tree)=true := by
  simp only [t6_371jobs,List.all_append,List.all_nil,t6_371part0,t6_371part1,t6_371part2,Bool.and_self]
theorem t6_371checked : Checked tree [1,5,3,10,7,7] := by
  refine ⟨plan6837,valid6837,t6_371choices,?_⟩
  exact check_of_frontier tree 2 t6_371root t6_371jobs t6_371frontier t6_371all
theorem t6_372choices : plan6838.choices=[1,5,3,10,10,7].map (options 6 4) := by rfl


theorem t6_372part0 : t6_372jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_372part1 : t6_372jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_372frontier : t6_372root.frontier 1=t6_372jobs := by rfl
theorem t6_372all : t6_372jobs.all (Job.check tree)=true := by
  simp only [t6_372jobs,List.all_append,List.all_nil,t6_372part0,t6_372part1,Bool.and_self]
theorem t6_372checked : Checked tree [1,5,3,10,10,7] := by
  refine ⟨plan6838,valid6838,t6_372choices,?_⟩
  exact check_of_frontier tree 1 t6_372root t6_372jobs t6_372frontier t6_372all
theorem t6_373choices : plan6839.choices=[1,5,3,10,10,10].map (options 6 4) := by rfl


theorem t6_373part0 : t6_373jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_373frontier : t6_373root.frontier 0=t6_373jobs := by rfl
theorem t6_373all : t6_373jobs.all (Job.check tree)=true := by
  simp only [t6_373jobs,List.all_append,List.all_nil,t6_373part0,Bool.and_self]
theorem t6_373checked : Checked tree [1,5,3,10,10,10] := by
  refine ⟨plan6839,valid6839,t6_373choices,?_⟩
  exact check_of_frontier tree 0 t6_373root t6_373jobs t6_373frontier t6_373all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks057 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_368checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_369checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_370checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_361checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_371checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_372checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_373checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_362checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_363checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_364checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_365checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_366checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_367checked⟩
