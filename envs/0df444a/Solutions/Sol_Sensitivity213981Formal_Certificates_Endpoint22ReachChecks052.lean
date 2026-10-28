-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks052
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:05:17.168807+00:00
-- url     : https://prove2.me/submissions/041a7f50-838e-4076-8de1-e09a941a8c2d

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks052
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks052
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
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

theorem valid1545 : plan1545.Valid := valid_step _ _ _ valid562 (by decide +kernel)



























































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







theorem valid3268 : plan3268.Valid := valid_step _ _ _ valid1519 (by decide +kernel)

theorem valid3269 : plan3269.Valid := valid_step _ _ _ valid1520 (by decide +kernel)

theorem valid3270 : plan3270.Valid := valid_step _ _ _ valid1521 (by decide +kernel)

theorem valid3271 : plan3271.Valid := valid_step _ _ _ valid1522 (by decide +kernel)

theorem valid3272 : plan3272.Valid := valid_step _ _ _ valid1523 (by decide +kernel)

theorem valid3273 : plan3273.Valid := valid_step _ _ _ valid1524 (by decide +kernel)













































































theorem valid3312 : plan3312.Valid := valid_step _ _ _ valid1542 (by decide +kernel)

theorem valid3313 : plan3313.Valid := valid_step _ _ _ valid1543 (by decide +kernel)

theorem valid3314 : plan3314.Valid := valid_step _ _ _ valid1544 (by decide +kernel)

theorem valid3315 : plan3315.Valid := valid_step _ _ _ valid1545 (by decide +kernel)


























































































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































































































































theorem valid5344 : plan5344.Valid := valid_step _ _ _ valid3241 (by decide +kernel)

























theorem valid5357 : plan5357.Valid := valid_step _ _ _ valid3247 (by decide +kernel)

theorem valid5358 : plan5358.Valid := valid_step _ _ _ valid3248 (by decide +kernel)

theorem valid5359 : plan5359.Valid := valid_step _ _ _ valid3249 (by decide +kernel)


































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







































theorem valid5396 : plan5396.Valid := valid_step _ _ _ valid3268 (by decide +kernel)

theorem valid5397 : plan5397.Valid := valid_step _ _ _ valid3269 (by decide +kernel)

theorem valid5398 : plan5398.Valid := valid_step _ _ _ valid3270 (by decide +kernel)

theorem valid5399 : plan5399.Valid := valid_step _ _ _ valid3271 (by decide +kernel)

theorem valid5400 : plan5400.Valid := valid_step _ _ _ valid3272 (by decide +kernel)

theorem valid5401 : plan5401.Valid := valid_step _ _ _ valid3273 (by decide +kernel)














































































































































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











































































theorem valid6278 : plan6278.Valid := valid_step _ _ _ valid5344 (by decide +kernel)



























theorem valid6292 : plan6292.Valid := valid_step _ _ _ valid5357 (by decide +kernel)

theorem valid6293 : plan6293.Valid := valid_step _ _ _ valid5358 (by decide +kernel)

theorem valid6294 : plan6294.Valid := valid_step _ _ _ valid5359 (by decide +kernel)




















































































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

















































































































































theorem valid3433 : plan3433.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3434 : plan3434.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3435 : plan3435.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3436 : plan3436.Valid := valid_step _ _ _ valid1582 (by decide +kernel)








































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



























theorem valid5486 : plan5486.Valid := valid_step _ _ _ valid3312 (by decide +kernel)

theorem valid5487 : plan5487.Valid := valid_step _ _ _ valid3313 (by decide +kernel)

theorem valid5488 : plan5488.Valid := valid_step _ _ _ valid3314 (by decide +kernel)

theorem valid5489 : plan5489.Valid := valid_step _ _ _ valid3315 (by decide +kernel)






























































































































































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













































































































































theorem valid6503 : plan6503.Valid := valid_step _ _ _ valid5486 (by decide +kernel)

theorem valid6504 : plan6504.Valid := valid_step _ _ _ valid5487 (by decide +kernel)

theorem valid6505 : plan6505.Valid := valid_step _ _ _ valid5488 (by decide +kernel)

theorem valid6506 : plan6506.Valid := valid_step _ _ _ valid5489 (by decide +kernel)












































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



































































































theorem valid5618 : plan5618.Valid := valid_step _ _ _ valid3433 (by decide +kernel)

theorem valid5619 : plan5619.Valid := valid_step _ _ _ valid3434 (by decide +kernel)

theorem valid5620 : plan5620.Valid := valid_step _ _ _ valid3435 (by decide +kernel)

theorem valid5621 : plan5621.Valid := valid_step _ _ _ valid3436 (by decide +kernel)






















































































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































































































































































theorem valid6800 : plan6800.Valid := valid_step _ _ _ valid5618 (by decide +kernel)

theorem valid6801 : plan6801.Valid := valid_step _ _ _ valid5619 (by decide +kernel)

theorem valid6802 : plan6802.Valid := valid_step _ _ _ valid5620 (by decide +kernel)

theorem valid6803 : plan6803.Valid := valid_step _ _ _ valid5621 (by decide +kernel)


























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

























theorem valid6349 : plan6349.Valid := valid_step _ _ _ valid5396 (by decide +kernel)

theorem valid6350 : plan6350.Valid := valid_step _ _ _ valid5397 (by decide +kernel)

theorem valid6351 : plan6351.Valid := valid_step _ _ _ valid5398 (by decide +kernel)

theorem valid6352 : plan6352.Valid := valid_step _ _ _ valid5399 (by decide +kernel)

theorem valid6353 : plan6353.Valid := valid_step _ _ _ valid5400 (by decide +kernel)

theorem valid6354 : plan6354.Valid := valid_step _ _ _ valid5401 (by decide +kernel)




























































































































































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
theorem t6_281choices : plan6800.choices=[1,2,10,7,7,7].map (options 6 4) := by rfl


theorem t6_281part0 : t6_281jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_281part1 : t6_281jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_281frontier : t6_281root.frontier 1=t6_281jobs := by rfl
theorem t6_281all : t6_281jobs.all (Job.check tree)=true := by
  simp only [t6_281jobs,List.all_append,List.all_nil,t6_281part0,t6_281part1,Bool.and_self]
theorem t6_281checked : Checked tree [1,2,10,7,7,7] := by
  refine ⟨plan6800,valid6800,t6_281choices,?_⟩
  exact check_of_frontier tree 1 t6_281root t6_281jobs t6_281frontier t6_281all
theorem t6_282choices : plan6801.choices=[1,2,10,10,7,7].map (options 6 4) := by rfl


theorem t6_282part0 : t6_282jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_282part1 : t6_282jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_282frontier : t6_282root.frontier 1=t6_282jobs := by rfl
theorem t6_282all : t6_282jobs.all (Job.check tree)=true := by
  simp only [t6_282jobs,List.all_append,List.all_nil,t6_282part0,t6_282part1,Bool.and_self]
theorem t6_282checked : Checked tree [1,2,10,10,7,7] := by
  refine ⟨plan6801,valid6801,t6_282choices,?_⟩
  exact check_of_frontier tree 1 t6_282root t6_282jobs t6_282frontier t6_282all
theorem t6_283choices : plan6802.choices=[1,2,10,10,10,7].map (options 6 4) := by rfl


theorem t6_283part0 : t6_283jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_283frontier : t6_283root.frontier 0=t6_283jobs := by rfl
theorem t6_283all : t6_283jobs.all (Job.check tree)=true := by
  simp only [t6_283jobs,List.all_append,List.all_nil,t6_283part0,Bool.and_self]
theorem t6_283checked : Checked tree [1,2,10,10,10,7] := by
  refine ⟨plan6802,valid6802,t6_283choices,?_⟩
  exact check_of_frontier tree 0 t6_283root t6_283jobs t6_283frontier t6_283all
theorem t6_284choices : plan6803.choices=[1,2,10,10,10,10].map (options 6 4) := by rfl


theorem t6_284part0 : t6_284jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_284frontier : t6_284root.frontier 0=t6_284jobs := by rfl
theorem t6_284all : t6_284jobs.all (Job.check tree)=true := by
  simp only [t6_284jobs,List.all_append,List.all_nil,t6_284part0,Bool.and_self]
theorem t6_284checked : Checked tree [1,2,10,10,10,10] := by
  refine ⟨plan6803,valid6803,t6_284choices,?_⟩
  exact check_of_frontier tree 0 t6_284root t6_284jobs t6_284frontier t6_284all
theorem t6_285choices : plan6278.choices=[1,3,3,3,3,3].map (options 6 0) := by rfl


theorem t6_285part0 : t6_285jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_285frontier : t6_285root.frontier 0=t6_285jobs := by rfl
theorem t6_285all : t6_285jobs.all (Job.check tree)=true := by
  simp only [t6_285jobs,List.all_append,List.all_nil,t6_285part0,Bool.and_self]
theorem t6_285checked : Checked tree [1,3,3,3,3,3] := by
  refine ⟨plan6278,valid6278,t6_285choices,?_⟩
  exact check_of_frontier tree 0 t6_285root t6_285jobs t6_285frontier t6_285all
theorem t6_286choices : plan6292.choices=[1,3,3,3,3,6].map (options 6 1) := by rfl


theorem t6_286part0 : t6_286jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_286frontier : t6_286root.frontier 0=t6_286jobs := by rfl
theorem t6_286all : t6_286jobs.all (Job.check tree)=true := by
  simp only [t6_286jobs,List.all_append,List.all_nil,t6_286part0,Bool.and_self]
theorem t6_286checked : Checked tree [1,3,3,3,3,6] := by
  refine ⟨plan6292,valid6292,t6_286choices,?_⟩
  exact check_of_frontier tree 0 t6_286root t6_286jobs t6_286frontier t6_286all
theorem t6_287choices : plan6293.choices=[1,3,3,3,3,7].map (options 6 1) := by rfl


theorem t6_287part0 : t6_287jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_287frontier : t6_287root.frontier 0=t6_287jobs := by rfl
theorem t6_287all : t6_287jobs.all (Job.check tree)=true := by
  simp only [t6_287jobs,List.all_append,List.all_nil,t6_287part0,Bool.and_self]
theorem t6_287checked : Checked tree [1,3,3,3,3,7] := by
  refine ⟨plan6293,valid6293,t6_287choices,?_⟩
  exact check_of_frontier tree 0 t6_287root t6_287jobs t6_287frontier t6_287all
theorem t6_288choices : plan6294.choices=[1,3,3,3,3,10].map (options 6 1) := by rfl


theorem t6_288part0 : t6_288jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_288frontier : t6_288root.frontier 0=t6_288jobs := by rfl
theorem t6_288all : t6_288jobs.all (Job.check tree)=true := by
  simp only [t6_288jobs,List.all_append,List.all_nil,t6_288part0,Bool.and_self]
theorem t6_288checked : Checked tree [1,3,3,3,3,10] := by
  refine ⟨plan6294,valid6294,t6_288choices,?_⟩
  exact check_of_frontier tree 0 t6_288root t6_288jobs t6_288frontier t6_288all
theorem t6_289choices : plan6349.choices=[1,3,3,3,6,6].map (options 6 2) := by rfl


theorem t6_289part0 : t6_289jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_289frontier : t6_289root.frontier 0=t6_289jobs := by rfl
theorem t6_289all : t6_289jobs.all (Job.check tree)=true := by
  simp only [t6_289jobs,List.all_append,List.all_nil,t6_289part0,Bool.and_self]
theorem t6_289checked : Checked tree [1,3,3,3,6,6] := by
  refine ⟨plan6349,valid6349,t6_289choices,?_⟩
  exact check_of_frontier tree 0 t6_289root t6_289jobs t6_289frontier t6_289all
theorem t6_290choices : plan6350.choices=[1,3,3,3,6,7].map (options 6 2) := by rfl


theorem t6_290part0 : t6_290jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_290part1 : t6_290jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_290frontier : t6_290root.frontier 1=t6_290jobs := by rfl
theorem t6_290all : t6_290jobs.all (Job.check tree)=true := by
  simp only [t6_290jobs,List.all_append,List.all_nil,t6_290part0,t6_290part1,Bool.and_self]
theorem t6_290checked : Checked tree [1,3,3,3,6,7] := by
  refine ⟨plan6350,valid6350,t6_290choices,?_⟩
  exact check_of_frontier tree 1 t6_290root t6_290jobs t6_290frontier t6_290all
theorem t6_291choices : plan6351.choices=[1,3,3,3,6,10].map (options 6 2) := by rfl


theorem t6_291part0 : t6_291jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_291frontier : t6_291root.frontier 0=t6_291jobs := by rfl
theorem t6_291all : t6_291jobs.all (Job.check tree)=true := by
  simp only [t6_291jobs,List.all_append,List.all_nil,t6_291part0,Bool.and_self]
theorem t6_291checked : Checked tree [1,3,3,3,6,10] := by
  refine ⟨plan6351,valid6351,t6_291choices,?_⟩
  exact check_of_frontier tree 0 t6_291root t6_291jobs t6_291frontier t6_291all
theorem t6_292choices : plan6352.choices=[1,3,3,3,7,7].map (options 6 2) := by rfl


theorem t6_292part0 : t6_292jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_292part1 : t6_292jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_292frontier : t6_292root.frontier 1=t6_292jobs := by rfl
theorem t6_292all : t6_292jobs.all (Job.check tree)=true := by
  simp only [t6_292jobs,List.all_append,List.all_nil,t6_292part0,t6_292part1,Bool.and_self]
theorem t6_292checked : Checked tree [1,3,3,3,7,7] := by
  refine ⟨plan6352,valid6352,t6_292choices,?_⟩
  exact check_of_frontier tree 1 t6_292root t6_292jobs t6_292frontier t6_292all
theorem t6_293choices : plan6353.choices=[1,3,3,3,10,7].map (options 6 2) := by rfl


theorem t6_293part0 : t6_293jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_293part1 : t6_293jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_293frontier : t6_293root.frontier 1=t6_293jobs := by rfl
theorem t6_293all : t6_293jobs.all (Job.check tree)=true := by
  simp only [t6_293jobs,List.all_append,List.all_nil,t6_293part0,t6_293part1,Bool.and_self]
theorem t6_293checked : Checked tree [1,3,3,3,10,7] := by
  refine ⟨plan6353,valid6353,t6_293choices,?_⟩
  exact check_of_frontier tree 1 t6_293root t6_293jobs t6_293frontier t6_293all
theorem t6_294choices : plan6354.choices=[1,3,3,3,10,10].map (options 6 2) := by rfl


theorem t6_294part0 : t6_294jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_294frontier : t6_294root.frontier 0=t6_294jobs := by rfl
theorem t6_294all : t6_294jobs.all (Job.check tree)=true := by
  simp only [t6_294jobs,List.all_append,List.all_nil,t6_294part0,Bool.and_self]
theorem t6_294checked : Checked tree [1,3,3,3,10,10] := by
  refine ⟨plan6354,valid6354,t6_294choices,?_⟩
  exact check_of_frontier tree 0 t6_294root t6_294jobs t6_294frontier t6_294all
theorem t6_295choices : plan6503.choices=[1,3,3,6,6,6].map (options 6 3) := by rfl


theorem t6_295part0 : t6_295jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_295frontier : t6_295root.frontier 0=t6_295jobs := by rfl
theorem t6_295all : t6_295jobs.all (Job.check tree)=true := by
  simp only [t6_295jobs,List.all_append,List.all_nil,t6_295part0,Bool.and_self]
theorem t6_295checked : Checked tree [1,3,3,6,6,6] := by
  refine ⟨plan6503,valid6503,t6_295choices,?_⟩
  exact check_of_frontier tree 0 t6_295root t6_295jobs t6_295frontier t6_295all
theorem t6_296choices : plan6504.choices=[1,3,3,6,6,7].map (options 6 3) := by rfl


theorem t6_296part0 : t6_296jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_296part1 : t6_296jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_296frontier : t6_296root.frontier 2=t6_296jobs := by rfl
theorem t6_296all : t6_296jobs.all (Job.check tree)=true := by
  simp only [t6_296jobs,List.all_append,List.all_nil,t6_296part0,t6_296part1,Bool.and_self]
theorem t6_296checked : Checked tree [1,3,3,6,6,7] := by
  refine ⟨plan6504,valid6504,t6_296choices,?_⟩
  exact check_of_frontier tree 2 t6_296root t6_296jobs t6_296frontier t6_296all
theorem t6_297choices : plan6505.choices=[1,3,3,6,6,10].map (options 6 3) := by rfl


theorem t6_297part0 : t6_297jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_297frontier : t6_297root.frontier 0=t6_297jobs := by rfl
theorem t6_297all : t6_297jobs.all (Job.check tree)=true := by
  simp only [t6_297jobs,List.all_append,List.all_nil,t6_297part0,Bool.and_self]
theorem t6_297checked : Checked tree [1,3,3,6,6,10] := by
  refine ⟨plan6505,valid6505,t6_297choices,?_⟩
  exact check_of_frontier tree 0 t6_297root t6_297jobs t6_297frontier t6_297all
theorem t6_298choices : plan6506.choices=[1,3,3,6,7,7].map (options 6 3) := by rfl


theorem t6_298part0 : t6_298jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_298part1 : t6_298jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_298part2 : t6_298jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_298part3 : t6_298jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_298frontier : t6_298root.frontier 2=t6_298jobs := by rfl
theorem t6_298all : t6_298jobs.all (Job.check tree)=true := by
  simp only [t6_298jobs,List.all_append,List.all_nil,t6_298part0,t6_298part1,t6_298part2,t6_298part3,Bool.and_self]
theorem t6_298checked : Checked tree [1,3,3,6,7,7] := by
  refine ⟨plan6506,valid6506,t6_298choices,?_⟩
  exact check_of_frontier tree 2 t6_298root t6_298jobs t6_298frontier t6_298all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks052 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_292checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_293checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_294checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_295checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_281checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_296checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_297checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_298checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_282checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_283checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_284checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_285checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_286checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_287checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_288checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_289checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_290checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_291checked⟩
