-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks064
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:25:50.215538+00:00
-- url     : https://prove2.me/submissions/c9e9fbc2-d722-4a93-8dc7-2c8fcd6f0c9e

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
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











































theorem valid118 : plan118.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid123 : plan123.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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

























































































































theorem valid541 : plan541.Valid := valid_step _ _ _ valid118 (by decide +kernel)









theorem valid546 : plan546.Valid := valid_step _ _ _ valid123 (by decide +kernel)

theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid548 : plan548.Valid := valid_step _ _ _ valid125 (by decide +kernel)





















theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)

theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)
























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

theorem valid1517 : plan1517.Valid := valid_step _ _ _ valid547 (by decide +kernel)

theorem valid1518 : plan1518.Valid := valid_step _ _ _ valid548 (by decide +kernel)



























theorem valid1532 : plan1532.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1533 : plan1533.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1534 : plan1534.Valid := valid_step _ _ _ valid561 (by decide +kernel)

theorem valid1535 : plan1535.Valid := valid_step _ _ _ valid562 (by decide +kernel)


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



































































































































































theorem valid3250 : plan3250.Valid := valid_step _ _ _ valid1508 (by decide +kernel)




























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

































theorem valid1553 : plan1553.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1554 : plan1554.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1555 : plan1555.Valid := valid_step _ _ _ valid564 (by decide +kernel)


























































































































































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





















theorem valid3275 : plan3275.Valid := valid_step _ _ _ valid1516 (by decide +kernel)

theorem valid3276 : plan3276.Valid := valid_step _ _ _ valid1517 (by decide +kernel)

theorem valid3277 : plan3277.Valid := valid_step _ _ _ valid1518 (by decide +kernel)



















































































theorem valid3319 : plan3319.Valid := valid_step _ _ _ valid1553 (by decide +kernel)

theorem valid3320 : plan3320.Valid := valid_step _ _ _ valid1554 (by decide +kernel)

theorem valid3321 : plan3321.Valid := valid_step _ _ _ valid1555 (by decide +kernel)









theorem valid3326 : plan3326.Valid := valid_step _ _ _ valid1532 (by decide +kernel)

theorem valid3327 : plan3327.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3328 : plan3328.Valid := valid_step _ _ _ valid1534 (by decide +kernel)

theorem valid3329 : plan3329.Valid := valid_step _ _ _ valid1535 (by decide +kernel)






























































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



















































































































































theorem valid5354 : plan5354.Valid := valid_step _ _ _ valid3250 (by decide +kernel)












































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





















theorem valid5387 : plan5387.Valid := valid_step _ _ _ valid3275 (by decide +kernel)

theorem valid5388 : plan5388.Valid := valid_step _ _ _ valid3276 (by decide +kernel)

theorem valid5389 : plan5389.Valid := valid_step _ _ _ valid3277 (by decide +kernel)













































































































































theorem valid5460 : plan5460.Valid := valid_step _ _ _ valid3319 (by decide +kernel)

theorem valid5461 : plan5461.Valid := valid_step _ _ _ valid3320 (by decide +kernel)

theorem valid5462 : plan5462.Valid := valid_step _ _ _ valid3321 (by decide +kernel)



theorem valid5464 : plan5464.Valid := valid_step _ _ _ valid3326 (by decide +kernel)

theorem valid5465 : plan5465.Valid := valid_step _ _ _ valid3327 (by decide +kernel)

theorem valid5466 : plan5466.Valid := valid_step _ _ _ valid3328 (by decide +kernel)

theorem valid5467 : plan5467.Valid := valid_step _ _ _ valid3329 (by decide +kernel)










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































































































































theorem valid6304 : plan6304.Valid := valid_step _ _ _ valid5354 (by decide +kernel)
































































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























































































theorem valid6380 : plan6380.Valid := valid_step _ _ _ valid5387 (by decide +kernel)

theorem valid6381 : plan6381.Valid := valid_step _ _ _ valid5388 (by decide +kernel)

theorem valid6382 : plan6382.Valid := valid_step _ _ _ valid5389 (by decide +kernel)




































































































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





























































theorem valid6559 : plan6559.Valid := valid_step _ _ _ valid5460 (by decide +kernel)

theorem valid6560 : plan6560.Valid := valid_step _ _ _ valid5461 (by decide +kernel)

theorem valid6561 : plan6561.Valid := valid_step _ _ _ valid5462 (by decide +kernel)

theorem valid6562 : plan6562.Valid := valid_step _ _ _ valid5464 (by decide +kernel)

theorem valid6563 : plan6563.Valid := valid_step _ _ _ valid5465 (by decide +kernel)

theorem valid6564 : plan6564.Valid := valid_step _ _ _ valid5466 (by decide +kernel)

theorem valid6565 : plan6565.Valid := valid_step _ _ _ valid5467 (by decide +kernel)






















































































































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
theorem t6_561choices : plan6559.choices=[2,2,3,10,7,7].map (options 6 3) := by rfl


theorem t6_561part0 : t6_561jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_561part1 : t6_561jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_561part2 : t6_561jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_561part3 : t6_561jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_561part4 : t6_561jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_561part5 : t6_561jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_561part6 : t6_561jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_561frontier : t6_561root.frontier 2=t6_561jobs := by rfl
theorem t6_561all : t6_561jobs.all (Job.check tree)=true := by
  simp only [t6_561jobs,List.all_append,List.all_nil,t6_561part0,t6_561part1,t6_561part2,t6_561part3,t6_561part4,t6_561part5,t6_561part6,Bool.and_self]
theorem t6_561checked : Checked tree [2,2,3,10,7,7] := by
  refine ⟨plan6559,valid6559,t6_561choices,?_⟩
  exact check_of_frontier tree 2 t6_561root t6_561jobs t6_561frontier t6_561all
theorem t6_562choices : plan6560.choices=[2,2,3,10,10,7].map (options 6 3) := by rfl


theorem t6_562part0 : t6_562jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_562part1 : t6_562jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_562part2 : t6_562jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_562part3 : t6_562jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_562frontier : t6_562root.frontier 1=t6_562jobs := by rfl
theorem t6_562all : t6_562jobs.all (Job.check tree)=true := by
  simp only [t6_562jobs,List.all_append,List.all_nil,t6_562part0,t6_562part1,t6_562part2,t6_562part3,Bool.and_self]
theorem t6_562checked : Checked tree [2,2,3,10,10,7] := by
  refine ⟨plan6560,valid6560,t6_562choices,?_⟩
  exact check_of_frontier tree 1 t6_562root t6_562jobs t6_562frontier t6_562all
theorem t6_563choices : plan6561.choices=[2,2,3,10,10,10].map (options 6 3) := by rfl


theorem t6_563part0 : t6_563jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_563frontier : t6_563root.frontier 0=t6_563jobs := by rfl
theorem t6_563all : t6_563jobs.all (Job.check tree)=true := by
  simp only [t6_563jobs,List.all_append,List.all_nil,t6_563part0,Bool.and_self]
theorem t6_563checked : Checked tree [2,2,3,10,10,10] := by
  refine ⟨plan6561,valid6561,t6_563choices,?_⟩
  exact check_of_frontier tree 0 t6_563root t6_563jobs t6_563frontier t6_563all
theorem t6_564choices : plan6304.choices=[2,2,5,3,3,3].map (options 6 1) := by rfl


theorem t6_564part0 : t6_564jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_564frontier : t6_564root.frontier 0=t6_564jobs := by rfl
theorem t6_564all : t6_564jobs.all (Job.check tree)=true := by
  simp only [t6_564jobs,List.all_append,List.all_nil,t6_564part0,Bool.and_self]
theorem t6_564checked : Checked tree [2,2,5,3,3,3] := by
  refine ⟨plan6304,valid6304,t6_564choices,?_⟩
  exact check_of_frontier tree 0 t6_564root t6_564jobs t6_564frontier t6_564all
theorem t6_565choices : plan6380.choices=[2,2,5,3,3,6].map (options 6 2) := by rfl


theorem t6_565part0 : t6_565jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_565frontier : t6_565root.frontier 0=t6_565jobs := by rfl
theorem t6_565all : t6_565jobs.all (Job.check tree)=true := by
  simp only [t6_565jobs,List.all_append,List.all_nil,t6_565part0,Bool.and_self]
theorem t6_565checked : Checked tree [2,2,5,3,3,6] := by
  refine ⟨plan6380,valid6380,t6_565choices,?_⟩
  exact check_of_frontier tree 0 t6_565root t6_565jobs t6_565frontier t6_565all
theorem t6_566choices : plan6381.choices=[2,2,5,3,3,7].map (options 6 2) := by rfl


theorem t6_566part0 : t6_566jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_566part1 : t6_566jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_566frontier : t6_566root.frontier 1=t6_566jobs := by rfl
theorem t6_566all : t6_566jobs.all (Job.check tree)=true := by
  simp only [t6_566jobs,List.all_append,List.all_nil,t6_566part0,t6_566part1,Bool.and_self]
theorem t6_566checked : Checked tree [2,2,5,3,3,7] := by
  refine ⟨plan6381,valid6381,t6_566choices,?_⟩
  exact check_of_frontier tree 1 t6_566root t6_566jobs t6_566frontier t6_566all
theorem t6_567choices : plan6382.choices=[2,2,5,3,3,10].map (options 6 2) := by rfl


theorem t6_567part0 : t6_567jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_567frontier : t6_567root.frontier 0=t6_567jobs := by rfl
theorem t6_567all : t6_567jobs.all (Job.check tree)=true := by
  simp only [t6_567jobs,List.all_append,List.all_nil,t6_567part0,Bool.and_self]
theorem t6_567checked : Checked tree [2,2,5,3,3,10] := by
  refine ⟨plan6382,valid6382,t6_567choices,?_⟩
  exact check_of_frontier tree 0 t6_567root t6_567jobs t6_567frontier t6_567all
theorem t6_568choices : plan6562.choices=[2,2,5,3,6,6].map (options 6 3) := by rfl


theorem t6_568part0 : t6_568jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_568frontier : t6_568root.frontier 0=t6_568jobs := by rfl
theorem t6_568all : t6_568jobs.all (Job.check tree)=true := by
  simp only [t6_568jobs,List.all_append,List.all_nil,t6_568part0,Bool.and_self]
theorem t6_568checked : Checked tree [2,2,5,3,6,6] := by
  refine ⟨plan6562,valid6562,t6_568choices,?_⟩
  exact check_of_frontier tree 0 t6_568root t6_568jobs t6_568frontier t6_568all
theorem t6_569choices : plan6563.choices=[2,2,5,3,6,7].map (options 6 3) := by rfl


theorem t6_569part0 : t6_569jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_569part1 : t6_569jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_569part2 : t6_569jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_569frontier : t6_569root.frontier 1=t6_569jobs := by rfl
theorem t6_569all : t6_569jobs.all (Job.check tree)=true := by
  simp only [t6_569jobs,List.all_append,List.all_nil,t6_569part0,t6_569part1,t6_569part2,Bool.and_self]
theorem t6_569checked : Checked tree [2,2,5,3,6,7] := by
  refine ⟨plan6563,valid6563,t6_569choices,?_⟩
  exact check_of_frontier tree 1 t6_569root t6_569jobs t6_569frontier t6_569all
theorem t6_570choices : plan6564.choices=[2,2,5,3,6,10].map (options 6 3) := by rfl


theorem t6_570part0 : t6_570jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_570frontier : t6_570root.frontier 0=t6_570jobs := by rfl
theorem t6_570all : t6_570jobs.all (Job.check tree)=true := by
  simp only [t6_570jobs,List.all_append,List.all_nil,t6_570part0,Bool.and_self]
theorem t6_570checked : Checked tree [2,2,5,3,6,10] := by
  refine ⟨plan6564,valid6564,t6_570choices,?_⟩
  exact check_of_frontier tree 0 t6_570root t6_570jobs t6_570frontier t6_570all
theorem t6_571choices : plan6565.choices=[2,2,5,3,7,7].map (options 6 3) := by rfl


theorem t6_571part0 : t6_571jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_571part1 : t6_571jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_571part2 : t6_571jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_571part3 : t6_571jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_571frontier : t6_571root.frontier 1=t6_571jobs := by rfl
theorem t6_571all : t6_571jobs.all (Job.check tree)=true := by
  simp only [t6_571jobs,List.all_append,List.all_nil,t6_571part0,t6_571part1,t6_571part2,t6_571part3,Bool.and_self]
theorem t6_571checked : Checked tree [2,2,5,3,7,7] := by
  refine ⟨plan6565,valid6565,t6_571choices,?_⟩
  exact check_of_frontier tree 1 t6_571root t6_571jobs t6_571frontier t6_571all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks064 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_569checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_570checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_571checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_561checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_562checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_563checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_564checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_565checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_566checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_567checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_568checked⟩
