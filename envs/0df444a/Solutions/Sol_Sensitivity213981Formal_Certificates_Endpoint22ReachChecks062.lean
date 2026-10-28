-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks062
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:13:31.81067+00:00
-- url     : https://prove2.me/submissions/6f5fb73c-06b3-4ad1-aff6-511012cb8590

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks062
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









































theorem valid117 : plan117.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid119 : plan119.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid120 : plan120.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid121 : plan121.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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























































































































theorem valid540 : plan540.Valid := valid_step _ _ _ valid117 (by decide +kernel)



theorem valid542 : plan542.Valid := valid_step _ _ _ valid119 (by decide +kernel)

theorem valid543 : plan543.Valid := valid_step _ _ _ valid120 (by decide +kernel)

theorem valid544 : plan544.Valid := valid_step _ _ _ valid121 (by decide +kernel)









theorem valid549 : plan549.Valid := valid_step _ _ _ valid123 (by decide +kernel)

theorem valid550 : plan550.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid551 : plan551.Valid := valid_step _ _ _ valid125 (by decide +kernel)

theorem valid552 : plan552.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid553 : plan553.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid554 : plan554.Valid := valid_step _ _ _ valid125 (by decide +kernel)









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



































































































































theorem valid1506 : plan1506.Valid := valid_step _ _ _ valid540 (by decide +kernel)





theorem valid1509 : plan1509.Valid := valid_step _ _ _ valid542 (by decide +kernel)

theorem valid1510 : plan1510.Valid := valid_step _ _ _ valid543 (by decide +kernel)

theorem valid1511 : plan1511.Valid := valid_step _ _ _ valid544 (by decide +kernel)















theorem valid1519 : plan1519.Valid := valid_step _ _ _ valid549 (by decide +kernel)

theorem valid1520 : plan1520.Valid := valid_step _ _ _ valid550 (by decide +kernel)

theorem valid1521 : plan1521.Valid := valid_step _ _ _ valid551 (by decide +kernel)

theorem valid1522 : plan1522.Valid := valid_step _ _ _ valid552 (by decide +kernel)

theorem valid1523 : plan1523.Valid := valid_step _ _ _ valid553 (by decide +kernel)

theorem valid1524 : plan1524.Valid := valid_step _ _ _ valid554 (by decide +kernel)
























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

















































































































































theorem valid3241 : plan3241.Valid := valid_step _ _ _ valid1506 (by decide +kernel)











theorem valid3247 : plan3247.Valid := valid_step _ _ _ valid1509 (by decide +kernel)

theorem valid3248 : plan3248.Valid := valid_step _ _ _ valid1510 (by decide +kernel)

theorem valid3249 : plan3249.Valid := valid_step _ _ _ valid1511 (by decide +kernel)






























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











theorem valid1542 : plan1542.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1543 : plan1543.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1544 : plan1544.Valid := valid_step _ _ _ valid561 (by decide +kernel)

















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







theorem valid3268 : plan3268.Valid := valid_step _ _ _ valid1519 (by decide +kernel)

theorem valid3269 : plan3269.Valid := valid_step _ _ _ valid1520 (by decide +kernel)

theorem valid3270 : plan3270.Valid := valid_step _ _ _ valid1521 (by decide +kernel)

theorem valid3271 : plan3271.Valid := valid_step _ _ _ valid1522 (by decide +kernel)

theorem valid3272 : plan3272.Valid := valid_step _ _ _ valid1523 (by decide +kernel)

theorem valid3273 : plan3273.Valid := valid_step _ _ _ valid1524 (by decide +kernel)





















































theorem valid3300 : plan3300.Valid := valid_step _ _ _ valid1553 (by decide +kernel)

theorem valid3301 : plan3301.Valid := valid_step _ _ _ valid1554 (by decide +kernel)

theorem valid3302 : plan3302.Valid := valid_step _ _ _ valid1555 (by decide +kernel)



















theorem valid3312 : plan3312.Valid := valid_step _ _ _ valid1542 (by decide +kernel)

theorem valid3313 : plan3313.Valid := valid_step _ _ _ valid1543 (by decide +kernel)

theorem valid3314 : plan3314.Valid := valid_step _ _ _ valid1544 (by decide +kernel)




























































































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





























































































































theorem valid5343 : plan5343.Valid := valid_step _ _ _ valid3241 (by decide +kernel)















theorem valid5351 : plan5351.Valid := valid_step _ _ _ valid3247 (by decide +kernel)

theorem valid5352 : plan5352.Valid := valid_step _ _ _ valid3248 (by decide +kernel)

theorem valid5353 : plan5353.Valid := valid_step _ _ _ valid3249 (by decide +kernel)














































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









theorem valid5381 : plan5381.Valid := valid_step _ _ _ valid3268 (by decide +kernel)

theorem valid5382 : plan5382.Valid := valid_step _ _ _ valid3269 (by decide +kernel)

theorem valid5383 : plan5383.Valid := valid_step _ _ _ valid3270 (by decide +kernel)

theorem valid5384 : plan5384.Valid := valid_step _ _ _ valid3271 (by decide +kernel)

theorem valid5385 : plan5385.Valid := valid_step _ _ _ valid3272 (by decide +kernel)

theorem valid5386 : plan5386.Valid := valid_step _ _ _ valid3273 (by decide +kernel)



















































































































theorem valid5444 : plan5444.Valid := valid_step _ _ _ valid3300 (by decide +kernel)

theorem valid5445 : plan5445.Valid := valid_step _ _ _ valid3301 (by decide +kernel)

theorem valid5446 : plan5446.Valid := valid_step _ _ _ valid3302 (by decide +kernel)













theorem valid5453 : plan5453.Valid := valid_step _ _ _ valid3312 (by decide +kernel)

theorem valid5454 : plan5454.Valid := valid_step _ _ _ valid3313 (by decide +kernel)

theorem valid5455 : plan5455.Valid := valid_step _ _ _ valid3314 (by decide +kernel)


































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















































































theorem valid6280 : plan6280.Valid := valid_step _ _ _ valid5343 (by decide +kernel)









































theorem valid6301 : plan6301.Valid := valid_step _ _ _ valid5351 (by decide +kernel)

theorem valid6302 : plan6302.Valid := valid_step _ _ _ valid5352 (by decide +kernel)

theorem valid6303 : plan6303.Valid := valid_step _ _ _ valid5353 (by decide +kernel)


































































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











































































theorem valid6374 : plan6374.Valid := valid_step _ _ _ valid5381 (by decide +kernel)

theorem valid6375 : plan6375.Valid := valid_step _ _ _ valid5382 (by decide +kernel)

theorem valid6376 : plan6376.Valid := valid_step _ _ _ valid5383 (by decide +kernel)

theorem valid6377 : plan6377.Valid := valid_step _ _ _ valid5384 (by decide +kernel)

theorem valid6378 : plan6378.Valid := valid_step _ _ _ valid5385 (by decide +kernel)

theorem valid6379 : plan6379.Valid := valid_step _ _ _ valid5386 (by decide +kernel)










































































































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









































theorem valid6549 : plan6549.Valid := valid_step _ _ _ valid5444 (by decide +kernel)

theorem valid6550 : plan6550.Valid := valid_step _ _ _ valid5445 (by decide +kernel)

theorem valid6551 : plan6551.Valid := valid_step _ _ _ valid5446 (by decide +kernel)

theorem valid6552 : plan6552.Valid := valid_step _ _ _ valid5453 (by decide +kernel)

theorem valid6553 : plan6553.Valid := valid_step _ _ _ valid5454 (by decide +kernel)

theorem valid6554 : plan6554.Valid := valid_step _ _ _ valid5455 (by decide +kernel)












































































































































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
theorem t6_541choices : plan6549.choices=[2,2,2,10,7,7].map (options 6 3) := by rfl


theorem t6_541part0 : t6_541jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_541frontier : t6_541root.frontier 0=t6_541jobs := by rfl
theorem t6_541all : t6_541jobs.all (Job.check tree)=true := by
  simp only [t6_541jobs,List.all_append,List.all_nil,t6_541part0,Bool.and_self]
theorem t6_541checked : Checked tree [2,2,2,10,7,7] := by
  refine ⟨plan6549,valid6549,t6_541choices,?_⟩
  exact check_of_frontier tree 0 t6_541root t6_541jobs t6_541frontier t6_541all
theorem t6_542choices : plan6550.choices=[2,2,2,10,10,7].map (options 6 3) := by rfl


theorem t6_542part0 : t6_542jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_542frontier : t6_542root.frontier 0=t6_542jobs := by rfl
theorem t6_542all : t6_542jobs.all (Job.check tree)=true := by
  simp only [t6_542jobs,List.all_append,List.all_nil,t6_542part0,Bool.and_self]
theorem t6_542checked : Checked tree [2,2,2,10,10,7] := by
  refine ⟨plan6550,valid6550,t6_542choices,?_⟩
  exact check_of_frontier tree 0 t6_542root t6_542jobs t6_542frontier t6_542all
theorem t6_543choices : plan6551.choices=[2,2,2,10,10,10].map (options 6 3) := by rfl


theorem t6_543part0 : t6_543jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_543frontier : t6_543root.frontier 0=t6_543jobs := by rfl
theorem t6_543all : t6_543jobs.all (Job.check tree)=true := by
  simp only [t6_543jobs,List.all_append,List.all_nil,t6_543part0,Bool.and_self]
theorem t6_543checked : Checked tree [2,2,2,10,10,10] := by
  refine ⟨plan6551,valid6551,t6_543choices,?_⟩
  exact check_of_frontier tree 0 t6_543root t6_543jobs t6_543frontier t6_543all
theorem t6_544choices : plan6280.choices=[2,2,3,3,3,3].map (options 6 0) := by rfl


theorem t6_544part0 : t6_544jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_544frontier : t6_544root.frontier 0=t6_544jobs := by rfl
theorem t6_544all : t6_544jobs.all (Job.check tree)=true := by
  simp only [t6_544jobs,List.all_append,List.all_nil,t6_544part0,Bool.and_self]
theorem t6_544checked : Checked tree [2,2,3,3,3,3] := by
  refine ⟨plan6280,valid6280,t6_544choices,?_⟩
  exact check_of_frontier tree 0 t6_544root t6_544jobs t6_544frontier t6_544all
theorem t6_545choices : plan6301.choices=[2,2,3,3,3,6].map (options 6 1) := by rfl


theorem t6_545part0 : t6_545jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_545frontier : t6_545root.frontier 0=t6_545jobs := by rfl
theorem t6_545all : t6_545jobs.all (Job.check tree)=true := by
  simp only [t6_545jobs,List.all_append,List.all_nil,t6_545part0,Bool.and_self]
theorem t6_545checked : Checked tree [2,2,3,3,3,6] := by
  refine ⟨plan6301,valid6301,t6_545choices,?_⟩
  exact check_of_frontier tree 0 t6_545root t6_545jobs t6_545frontier t6_545all
theorem t6_546choices : plan6302.choices=[2,2,3,3,3,7].map (options 6 1) := by rfl


theorem t6_546part0 : t6_546jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_546frontier : t6_546root.frontier 0=t6_546jobs := by rfl
theorem t6_546all : t6_546jobs.all (Job.check tree)=true := by
  simp only [t6_546jobs,List.all_append,List.all_nil,t6_546part0,Bool.and_self]
theorem t6_546checked : Checked tree [2,2,3,3,3,7] := by
  refine ⟨plan6302,valid6302,t6_546choices,?_⟩
  exact check_of_frontier tree 0 t6_546root t6_546jobs t6_546frontier t6_546all
theorem t6_547choices : plan6303.choices=[2,2,3,3,3,10].map (options 6 1) := by rfl


theorem t6_547part0 : t6_547jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_547frontier : t6_547root.frontier 0=t6_547jobs := by rfl
theorem t6_547all : t6_547jobs.all (Job.check tree)=true := by
  simp only [t6_547jobs,List.all_append,List.all_nil,t6_547part0,Bool.and_self]
theorem t6_547checked : Checked tree [2,2,3,3,3,10] := by
  refine ⟨plan6303,valid6303,t6_547choices,?_⟩
  exact check_of_frontier tree 0 t6_547root t6_547jobs t6_547frontier t6_547all
theorem t6_548choices : plan6374.choices=[2,2,3,3,6,6].map (options 6 2) := by rfl


theorem t6_548part0 : t6_548jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_548frontier : t6_548root.frontier 0=t6_548jobs := by rfl
theorem t6_548all : t6_548jobs.all (Job.check tree)=true := by
  simp only [t6_548jobs,List.all_append,List.all_nil,t6_548part0,Bool.and_self]
theorem t6_548checked : Checked tree [2,2,3,3,6,6] := by
  refine ⟨plan6374,valid6374,t6_548choices,?_⟩
  exact check_of_frontier tree 0 t6_548root t6_548jobs t6_548frontier t6_548all
theorem t6_549choices : plan6375.choices=[2,2,3,3,6,7].map (options 6 2) := by rfl


theorem t6_549part0 : t6_549jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_549part1 : t6_549jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_549part2 : t6_549jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_549frontier : t6_549root.frontier 1=t6_549jobs := by rfl
theorem t6_549all : t6_549jobs.all (Job.check tree)=true := by
  simp only [t6_549jobs,List.all_append,List.all_nil,t6_549part0,t6_549part1,t6_549part2,Bool.and_self]
theorem t6_549checked : Checked tree [2,2,3,3,6,7] := by
  refine ⟨plan6375,valid6375,t6_549choices,?_⟩
  exact check_of_frontier tree 1 t6_549root t6_549jobs t6_549frontier t6_549all
theorem t6_550choices : plan6376.choices=[2,2,3,3,6,10].map (options 6 2) := by rfl


theorem t6_550part0 : t6_550jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_550frontier : t6_550root.frontier 0=t6_550jobs := by rfl
theorem t6_550all : t6_550jobs.all (Job.check tree)=true := by
  simp only [t6_550jobs,List.all_append,List.all_nil,t6_550part0,Bool.and_self]
theorem t6_550checked : Checked tree [2,2,3,3,6,10] := by
  refine ⟨plan6376,valid6376,t6_550choices,?_⟩
  exact check_of_frontier tree 0 t6_550root t6_550jobs t6_550frontier t6_550all
theorem t6_551choices : plan6377.choices=[2,2,3,3,7,7].map (options 6 2) := by rfl


theorem t6_551part0 : t6_551jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_551part1 : t6_551jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_551part2 : t6_551jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_551frontier : t6_551root.frontier 1=t6_551jobs := by rfl
theorem t6_551all : t6_551jobs.all (Job.check tree)=true := by
  simp only [t6_551jobs,List.all_append,List.all_nil,t6_551part0,t6_551part1,t6_551part2,Bool.and_self]
theorem t6_551checked : Checked tree [2,2,3,3,7,7] := by
  refine ⟨plan6377,valid6377,t6_551choices,?_⟩
  exact check_of_frontier tree 1 t6_551root t6_551jobs t6_551frontier t6_551all
theorem t6_552choices : plan6378.choices=[2,2,3,3,10,7].map (options 6 2) := by rfl


theorem t6_552part0 : t6_552jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_552part1 : t6_552jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_552part2 : t6_552jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_552frontier : t6_552root.frontier 1=t6_552jobs := by rfl
theorem t6_552all : t6_552jobs.all (Job.check tree)=true := by
  simp only [t6_552jobs,List.all_append,List.all_nil,t6_552part0,t6_552part1,t6_552part2,Bool.and_self]
theorem t6_552checked : Checked tree [2,2,3,3,10,7] := by
  refine ⟨plan6378,valid6378,t6_552choices,?_⟩
  exact check_of_frontier tree 1 t6_552root t6_552jobs t6_552frontier t6_552all
theorem t6_553choices : plan6379.choices=[2,2,3,3,10,10].map (options 6 2) := by rfl


theorem t6_553part0 : t6_553jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_553frontier : t6_553root.frontier 0=t6_553jobs := by rfl
theorem t6_553all : t6_553jobs.all (Job.check tree)=true := by
  simp only [t6_553jobs,List.all_append,List.all_nil,t6_553part0,Bool.and_self]
theorem t6_553checked : Checked tree [2,2,3,3,10,10] := by
  refine ⟨plan6379,valid6379,t6_553choices,?_⟩
  exact check_of_frontier tree 0 t6_553root t6_553jobs t6_553frontier t6_553all
theorem t6_554choices : plan6552.choices=[2,2,3,6,6,6].map (options 6 3) := by rfl


theorem t6_554part0 : t6_554jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_554frontier : t6_554root.frontier 0=t6_554jobs := by rfl
theorem t6_554all : t6_554jobs.all (Job.check tree)=true := by
  simp only [t6_554jobs,List.all_append,List.all_nil,t6_554part0,Bool.and_self]
theorem t6_554checked : Checked tree [2,2,3,6,6,6] := by
  refine ⟨plan6552,valid6552,t6_554choices,?_⟩
  exact check_of_frontier tree 0 t6_554root t6_554jobs t6_554frontier t6_554all
theorem t6_555choices : plan6553.choices=[2,2,3,6,6,7].map (options 6 3) := by rfl


theorem t6_555part0 : t6_555jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_555part1 : t6_555jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_555part2 : t6_555jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_555part3 : t6_555jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_555frontier : t6_555root.frontier 1=t6_555jobs := by rfl
theorem t6_555all : t6_555jobs.all (Job.check tree)=true := by
  simp only [t6_555jobs,List.all_append,List.all_nil,t6_555part0,t6_555part1,t6_555part2,t6_555part3,Bool.and_self]
theorem t6_555checked : Checked tree [2,2,3,6,6,7] := by
  refine ⟨plan6553,valid6553,t6_555choices,?_⟩
  exact check_of_frontier tree 1 t6_555root t6_555jobs t6_555frontier t6_555all
theorem t6_556choices : plan6554.choices=[2,2,3,6,6,10].map (options 6 3) := by rfl


theorem t6_556part0 : t6_556jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_556part1 : t6_556jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_556frontier : t6_556root.frontier 1=t6_556jobs := by rfl
theorem t6_556all : t6_556jobs.all (Job.check tree)=true := by
  simp only [t6_556jobs,List.all_append,List.all_nil,t6_556part0,t6_556part1,Bool.and_self]
theorem t6_556checked : Checked tree [2,2,3,6,6,10] := by
  refine ⟨plan6554,valid6554,t6_556choices,?_⟩
  exact check_of_frontier tree 1 t6_556root t6_556jobs t6_556frontier t6_556all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks062 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_552checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_553checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_554checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_555checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_556checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_542checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_543checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_544checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_545checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_546checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_547checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_548checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_549checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_550checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_551checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_541checked⟩
