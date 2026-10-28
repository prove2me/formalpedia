-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks091
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:32:52.241993+00:00
-- url     : https://prove2.me/submissions/87f53132-c809-4f32-a2b7-4666b883eb4f

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks091
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks091
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
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























































theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid125 : plan125.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)






























































































































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





































































































































theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid548 : plan548.Valid := valid_step _ _ _ valid125 (by decide +kernel)





















theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)






























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

























































































































































theorem valid1517 : plan1517.Valid := valid_step _ _ _ valid547 (by decide +kernel)

theorem valid1518 : plan1518.Valid := valid_step _ _ _ valid548 (by decide +kernel)



























theorem valid1532 : plan1532.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1533 : plan1533.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1534 : plan1534.Valid := valid_step _ _ _ valid561 (by decide +kernel)




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



theorem valid3266 : plan3266.Valid := valid_step _ _ _ valid1517 (by decide +kernel)

theorem valid3267 : plan3267.Valid := valid_step _ _ _ valid1518 (by decide +kernel)













































































theorem valid3306 : plan3306.Valid := valid_step _ _ _ valid1532 (by decide +kernel)

theorem valid3307 : plan3307.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3308 : plan3308.Valid := valid_step _ _ _ valid1534 (by decide +kernel)








































































































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







































































theorem valid5412 : plan5412.Valid := valid_step _ _ _ valid3266 (by decide +kernel)

theorem valid5413 : plan5413.Valid := valid_step _ _ _ valid3267 (by decide +kernel)






















































































































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











































































































theorem valid5526 : plan5526.Valid := valid_step _ _ _ valid3306 (by decide +kernel)

theorem valid5527 : plan5527.Valid := valid_step _ _ _ valid3307 (by decide +kernel)

theorem valid5528 : plan5528.Valid := valid_step _ _ _ valid3308 (by decide +kernel)
















































































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



























































































































theorem valid6398 : plan6398.Valid := valid_step _ _ _ valid5412 (by decide +kernel)

theorem valid6399 : plan6399.Valid := valid_step _ _ _ valid5413 (by decide +kernel)


































































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













































































































































theorem valid6599 : plan6599.Valid := valid_step _ _ _ valid5526 (by decide +kernel)

theorem valid6600 : plan6600.Valid := valid_step _ _ _ valid5527 (by decide +kernel)

theorem valid6601 : plan6601.Valid := valid_step _ _ _ valid5528 (by decide +kernel)














































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
theorem t6_771choices : plan6398.choices=[2,9,3,3,3,7].map (options 6 2) := by rfl


theorem t6_771part0 : t6_771jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_771part1 : t6_771jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_771part2 : t6_771jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_771part3 : t6_771jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_771frontier : t6_771root.frontier 1=t6_771jobs := by rfl
theorem t6_771all : t6_771jobs.all (Job.check tree)=true := by
  simp only [t6_771jobs,List.all_append,List.all_nil,t6_771part0,t6_771part1,t6_771part2,t6_771part3,Bool.and_self]
theorem t6_771checked : Checked tree [2,9,3,3,3,7] := by
  refine ⟨plan6398,valid6398,t6_771choices,?_⟩
  exact check_of_frontier tree 1 t6_771root t6_771jobs t6_771frontier t6_771all
theorem t6_772choices : plan6399.choices=[2,9,3,3,3,10].map (options 6 2) := by rfl


theorem t6_772part0 : t6_772jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_772frontier : t6_772root.frontier 0=t6_772jobs := by rfl
theorem t6_772all : t6_772jobs.all (Job.check tree)=true := by
  simp only [t6_772jobs,List.all_append,List.all_nil,t6_772part0,Bool.and_self]
theorem t6_772checked : Checked tree [2,9,3,3,3,10] := by
  refine ⟨plan6399,valid6399,t6_772choices,?_⟩
  exact check_of_frontier tree 0 t6_772root t6_772jobs t6_772frontier t6_772all
theorem t6_773choices : plan6599.choices=[2,9,3,3,6,6].map (options 6 3) := by rfl


theorem t6_773part0 : t6_773jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_773part1 : t6_773jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_773frontier : t6_773root.frontier 1=t6_773jobs := by rfl
theorem t6_773all : t6_773jobs.all (Job.check tree)=true := by
  simp only [t6_773jobs,List.all_append,List.all_nil,t6_773part0,t6_773part1,Bool.and_self]
theorem t6_773checked : Checked tree [2,9,3,3,6,6] := by
  refine ⟨plan6599,valid6599,t6_773choices,?_⟩
  exact check_of_frontier tree 1 t6_773root t6_773jobs t6_773frontier t6_773all
theorem t6_774choices : plan6600.choices=[2,9,3,3,6,7].map (options 6 3) := by rfl


theorem t6_774part0 : t6_774jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_774part1 : t6_774jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_774part2 : t6_774jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_774part3 : t6_774jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_774part4 : t6_774jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_774part5 : t6_774jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_774part6 : t6_774jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_774frontier : t6_774root.frontier 2=t6_774jobs := by rfl
theorem t6_774all : t6_774jobs.all (Job.check tree)=true := by
  simp only [t6_774jobs,List.all_append,List.all_nil,t6_774part0,t6_774part1,t6_774part2,t6_774part3,t6_774part4,t6_774part5,t6_774part6,Bool.and_self]
theorem t6_774checked : Checked tree [2,9,3,3,6,7] := by
  refine ⟨plan6600,valid6600,t6_774choices,?_⟩
  exact check_of_frontier tree 2 t6_774root t6_774jobs t6_774frontier t6_774all
theorem t6_775choices : plan6601.choices=[2,9,3,3,6,10].map (options 6 3) := by rfl


theorem t6_775part0 : t6_775jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_775part1 : t6_775jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_775part2 : t6_775jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_775frontier : t6_775root.frontier 1=t6_775jobs := by rfl
theorem t6_775all : t6_775jobs.all (Job.check tree)=true := by
  simp only [t6_775jobs,List.all_append,List.all_nil,t6_775part0,t6_775part1,t6_775part2,Bool.and_self]
theorem t6_775checked : Checked tree [2,9,3,3,6,10] := by
  refine ⟨plan6601,valid6601,t6_775choices,?_⟩
  exact check_of_frontier tree 1 t6_775root t6_775jobs t6_775frontier t6_775all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks091 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_771checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_772checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_773checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_774checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_775checked⟩
