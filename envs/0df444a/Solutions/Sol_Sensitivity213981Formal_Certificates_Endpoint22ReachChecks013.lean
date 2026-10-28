-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks013
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:17.968027+00:00
-- url     : https://prove2.me/submissions/2bf9e0fe-98d4-451e-ab91-20bc8246ce55

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans048
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











theorem valid94 : plan94.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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

















theorem valid462 : plan462.Valid := valid_step _ _ _ valid94 (by decide +kernel)

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









theorem valid485 : plan485.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid486 : plan486.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid487 : plan487.Valid := valid_step _ _ _ valid105 (by decide +kernel)













theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)











theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)













theorem valid511 : plan511.Valid := valid_step _ _ _ valid109 (by decide +kernel)





theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)





theorem valid520 : plan520.Valid := valid_step _ _ _ valid109 (by decide +kernel)





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



































































theorem valid1298 : plan1298.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1299 : plan1299.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1300 : plan1300.Valid := valid_step _ _ _ valid465 (by decide +kernel)















theorem valid1308 : plan1308.Valid := valid_step _ _ _ valid462 (by decide +kernel)













theorem valid1315 : plan1315.Valid := valid_step _ _ _ valid462 (by decide +kernel)















































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

























































































































































theorem valid3725 : plan3725.Valid := valid_step _ _ _ valid2558 (by decide +kernel)






































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











theorem valid1350 : plan1350.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1351 : plan1351.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1352 : plan1352.Valid := valid_step _ _ _ valid487 (by decide +kernel)

















































theorem valid1377 : plan1377.Valid := valid_step _ _ _ valid486 (by decide +kernel)









theorem valid1382 : plan1382.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1383 : plan1383.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1384 : plan1384.Valid := valid_step _ _ _ valid487 (by decide +kernel)













































































theorem valid1423 : plan1423.Valid := valid_step _ _ _ valid511 (by decide +kernel)





theorem valid1426 : plan1426.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1427 : plan1427.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1428 : plan1428.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1429 : plan1429.Valid := valid_step _ _ _ valid517 (by decide +kernel)





theorem valid1432 : plan1432.Valid := valid_step _ _ _ valid520 (by decide +kernel)





theorem valid1435 : plan1435.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1436 : plan1436.Valid := valid_step _ _ _ valid524 (by decide +kernel)

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











































































































































theorem valid2662 : plan2662.Valid := valid_step _ _ _ valid1308 (by decide +kernel)

theorem valid2663 : plan2663.Valid := valid_step _ _ _ valid1315 (by decide +kernel)



theorem valid2665 : plan2665.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2666 : plan2666.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2667 : plan2667.Valid := valid_step _ _ _ valid1300 (by decide +kernel)










































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























































































































theorem valid2844 : plan2844.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2845 : plan2845.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2846 : plan2846.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2847 : plan2847.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2848 : plan2848.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2849 : plan2849.Valid := valid_step _ _ _ valid1344 (by decide +kernel)



theorem valid2851 : plan2851.Valid := valid_step _ _ _ valid1350 (by decide +kernel)

theorem valid2852 : plan2852.Valid := valid_step _ _ _ valid1351 (by decide +kernel)

theorem valid2853 : plan2853.Valid := valid_step _ _ _ valid1352 (by decide +kernel)

theorem valid2854 : plan2854.Valid := valid_step _ _ _ valid1377 (by decide +kernel)



theorem valid2856 : plan2856.Valid := valid_step _ _ _ valid1382 (by decide +kernel)

theorem valid2857 : plan2857.Valid := valid_step _ _ _ valid1383 (by decide +kernel)

theorem valid2858 : plan2858.Valid := valid_step _ _ _ valid1384 (by decide +kernel)







theorem valid2862 : plan2862.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2863 : plan2863.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2864 : plan2864.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2865 : plan2865.Valid := valid_step _ _ _ valid1342 (by decide +kernel)






























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



theorem valid1445 : plan1445.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1446 : plan1446.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1447 : plan1447.Valid := valid_step _ _ _ valid523 (by decide +kernel)







theorem valid1451 : plan1451.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1452 : plan1452.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1453 : plan1453.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1454 : plan1454.Valid := valid_step _ _ _ valid517 (by decide +kernel)





theorem valid1457 : plan1457.Valid := valid_step _ _ _ valid520 (by decide +kernel)





theorem valid1460 : plan1460.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1461 : plan1461.Valid := valid_step _ _ _ valid524 (by decide +kernel)

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









































































































































theorem valid3045 : plan3045.Valid := valid_step _ _ _ valid1423 (by decide +kernel)

theorem valid3046 : plan3046.Valid := valid_step _ _ _ valid1426 (by decide +kernel)

theorem valid3047 : plan3047.Valid := valid_step _ _ _ valid1427 (by decide +kernel)

theorem valid3048 : plan3048.Valid := valid_step _ _ _ valid1428 (by decide +kernel)

theorem valid3049 : plan3049.Valid := valid_step _ _ _ valid1429 (by decide +kernel)

theorem valid3050 : plan3050.Valid := valid_step _ _ _ valid1432 (by decide +kernel)

theorem valid3051 : plan3051.Valid := valid_step _ _ _ valid1435 (by decide +kernel)

theorem valid3052 : plan3052.Valid := valid_step _ _ _ valid1436 (by decide +kernel)

theorem valid3053 : plan3053.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid3054 : plan3054.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid3055 : plan3055.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid3056 : plan3056.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid3057 : plan3057.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid3058 : plan3058.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid3059 : plan3059.Valid := valid_step _ _ _ valid1443 (by decide +kernel)



theorem valid3061 : plan3061.Valid := valid_step _ _ _ valid1445 (by decide +kernel)

theorem valid3062 : plan3062.Valid := valid_step _ _ _ valid1446 (by decide +kernel)

theorem valid3063 : plan3063.Valid := valid_step _ _ _ valid1447 (by decide +kernel)







theorem valid3067 : plan3067.Valid := valid_step _ _ _ valid1451 (by decide +kernel)

theorem valid3068 : plan3068.Valid := valid_step _ _ _ valid1452 (by decide +kernel)

theorem valid3069 : plan3069.Valid := valid_step _ _ _ valid1453 (by decide +kernel)

theorem valid3070 : plan3070.Valid := valid_step _ _ _ valid1454 (by decide +kernel)

theorem valid3071 : plan3071.Valid := valid_step _ _ _ valid1457 (by decide +kernel)

theorem valid3072 : plan3072.Valid := valid_step _ _ _ valid1460 (by decide +kernel)
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

theorem valid3073 : plan3073.Valid := valid_step _ _ _ valid1461 (by decide +kernel)

theorem valid3074 : plan3074.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3075 : plan3075.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid3076 : plan3076.Valid := valid_step _ _ _ valid1464 (by decide +kernel)
























































































































































































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







































































































theorem valid3892 : plan3892.Valid := valid_step _ _ _ valid2662 (by decide +kernel)

theorem valid3893 : plan3893.Valid := valid_step _ _ _ valid2663 (by decide +kernel)

theorem valid3894 : plan3894.Valid := valid_step _ _ _ valid2665 (by decide +kernel)

theorem valid3895 : plan3895.Valid := valid_step _ _ _ valid2666 (by decide +kernel)

theorem valid3896 : plan3896.Valid := valid_step _ _ _ valid2667 (by decide +kernel)
















































































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





































































































































































theorem valid4211 : plan4211.Valid := valid_step _ _ _ valid2844 (by decide +kernel)

theorem valid4212 : plan4212.Valid := valid_step _ _ _ valid2845 (by decide +kernel)

theorem valid4213 : plan4213.Valid := valid_step _ _ _ valid2846 (by decide +kernel)

theorem valid4214 : plan4214.Valid := valid_step _ _ _ valid2847 (by decide +kernel)

theorem valid4215 : plan4215.Valid := valid_step _ _ _ valid2848 (by decide +kernel)

theorem valid4216 : plan4216.Valid := valid_step _ _ _ valid2849 (by decide +kernel)

theorem valid4217 : plan4217.Valid := valid_step _ _ _ valid2851 (by decide +kernel)

theorem valid4218 : plan4218.Valid := valid_step _ _ _ valid2852 (by decide +kernel)

theorem valid4219 : plan4219.Valid := valid_step _ _ _ valid2853 (by decide +kernel)

theorem valid4220 : plan4220.Valid := valid_step _ _ _ valid2854 (by decide +kernel)

theorem valid4221 : plan4221.Valid := valid_step _ _ _ valid2856 (by decide +kernel)

theorem valid4222 : plan4222.Valid := valid_step _ _ _ valid2857 (by decide +kernel)

theorem valid4223 : plan4223.Valid := valid_step _ _ _ valid2858 (by decide +kernel)

theorem valid4224 : plan4224.Valid := valid_step _ _ _ valid2862 (by decide +kernel)
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







theorem valid4612 : plan4612.Valid := valid_step _ _ _ valid3045 (by decide +kernel)

theorem valid4613 : plan4613.Valid := valid_step _ _ _ valid3046 (by decide +kernel)

theorem valid4614 : plan4614.Valid := valid_step _ _ _ valid3047 (by decide +kernel)

theorem valid4615 : plan4615.Valid := valid_step _ _ _ valid3048 (by decide +kernel)

theorem valid4616 : plan4616.Valid := valid_step _ _ _ valid3049 (by decide +kernel)

theorem valid4617 : plan4617.Valid := valid_step _ _ _ valid3050 (by decide +kernel)

theorem valid4618 : plan4618.Valid := valid_step _ _ _ valid3051 (by decide +kernel)

theorem valid4619 : plan4619.Valid := valid_step _ _ _ valid3052 (by decide +kernel)

theorem valid4620 : plan4620.Valid := valid_step _ _ _ valid3053 (by decide +kernel)

theorem valid4621 : plan4621.Valid := valid_step _ _ _ valid3054 (by decide +kernel)

theorem valid4622 : plan4622.Valid := valid_step _ _ _ valid3055 (by decide +kernel)

theorem valid4623 : plan4623.Valid := valid_step _ _ _ valid3056 (by decide +kernel)

theorem valid4624 : plan4624.Valid := valid_step _ _ _ valid3057 (by decide +kernel)

theorem valid4625 : plan4625.Valid := valid_step _ _ _ valid3058 (by decide +kernel)

theorem valid4626 : plan4626.Valid := valid_step _ _ _ valid3059 (by decide +kernel)

theorem valid4627 : plan4627.Valid := valid_step _ _ _ valid3061 (by decide +kernel)

theorem valid4628 : plan4628.Valid := valid_step _ _ _ valid3062 (by decide +kernel)

theorem valid4629 : plan4629.Valid := valid_step _ _ _ valid3063 (by decide +kernel)

theorem valid4630 : plan4630.Valid := valid_step _ _ _ valid3067 (by decide +kernel)

theorem valid4631 : plan4631.Valid := valid_step _ _ _ valid3068 (by decide +kernel)

theorem valid4632 : plan4632.Valid := valid_step _ _ _ valid3069 (by decide +kernel)

theorem valid4633 : plan4633.Valid := valid_step _ _ _ valid3070 (by decide +kernel)

theorem valid4634 : plan4634.Valid := valid_step _ _ _ valid3071 (by decide +kernel)

theorem valid4635 : plan4635.Valid := valid_step _ _ _ valid3072 (by decide +kernel)

theorem valid4636 : plan4636.Valid := valid_step _ _ _ valid3073 (by decide +kernel)

theorem valid4637 : plan4637.Valid := valid_step _ _ _ valid3074 (by decide +kernel)

theorem valid4638 : plan4638.Valid := valid_step _ _ _ valid3075 (by decide +kernel)

theorem valid4639 : plan4639.Valid := valid_step _ _ _ valid3076 (by decide +kernel)


































































































































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

theorem valid4225 : plan4225.Valid := valid_step _ _ _ valid2863 (by decide +kernel)

theorem valid4226 : plan4226.Valid := valid_step _ _ _ valid2864 (by decide +kernel)

theorem valid4227 : plan4227.Valid := valid_step _ _ _ valid2865 (by decide +kernel)


























































































































































































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
theorem t5_567choices : plan4211.choices=[1,8,3,6,6].map (options 5 3) := by rfl


theorem t5_567part0 : t5_567jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_567frontier : t5_567root.frontier 0=t5_567jobs := by rfl
theorem t5_567all : t5_567jobs.all (Job.check tree)=true := by
  simp only [t5_567jobs,List.all_append,List.all_nil,t5_567part0,Bool.and_self]
theorem t5_567checked : Checked tree [1,8,3,6,6] := by
  refine ⟨plan4211,valid4211,t5_567choices,?_⟩
  exact check_of_frontier tree 0 t5_567root t5_567jobs t5_567frontier t5_567all
theorem t5_568choices : plan4212.choices=[1,8,3,6,7].map (options 5 3) := by rfl


theorem t5_568part0 : t5_568jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_568frontier : t5_568root.frontier 0=t5_568jobs := by rfl
theorem t5_568all : t5_568jobs.all (Job.check tree)=true := by
  simp only [t5_568jobs,List.all_append,List.all_nil,t5_568part0,Bool.and_self]
theorem t5_568checked : Checked tree [1,8,3,6,7] := by
  refine ⟨plan4212,valid4212,t5_568choices,?_⟩
  exact check_of_frontier tree 0 t5_568root t5_568jobs t5_568frontier t5_568all
theorem t5_569choices : plan4213.choices=[1,8,3,6,10].map (options 5 3) := by rfl


theorem t5_569part0 : t5_569jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_569frontier : t5_569root.frontier 0=t5_569jobs := by rfl
theorem t5_569all : t5_569jobs.all (Job.check tree)=true := by
  simp only [t5_569jobs,List.all_append,List.all_nil,t5_569part0,Bool.and_self]
theorem t5_569checked : Checked tree [1,8,3,6,10] := by
  refine ⟨plan4213,valid4213,t5_569choices,?_⟩
  exact check_of_frontier tree 0 t5_569root t5_569jobs t5_569frontier t5_569all
theorem t5_570choices : plan4214.choices=[1,8,3,7,7].map (options 5 3) := by rfl


theorem t5_570part0 : t5_570jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_570frontier : t5_570root.frontier 0=t5_570jobs := by rfl
theorem t5_570all : t5_570jobs.all (Job.check tree)=true := by
  simp only [t5_570jobs,List.all_append,List.all_nil,t5_570part0,Bool.and_self]
theorem t5_570checked : Checked tree [1,8,3,7,7] := by
  refine ⟨plan4214,valid4214,t5_570choices,?_⟩
  exact check_of_frontier tree 0 t5_570root t5_570jobs t5_570frontier t5_570all
theorem t5_571choices : plan4215.choices=[1,8,3,10,7].map (options 5 3) := by rfl


theorem t5_571part0 : t5_571jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_571frontier : t5_571root.frontier 0=t5_571jobs := by rfl
theorem t5_571all : t5_571jobs.all (Job.check tree)=true := by
  simp only [t5_571jobs,List.all_append,List.all_nil,t5_571part0,Bool.and_self]
theorem t5_571checked : Checked tree [1,8,3,10,7] := by
  refine ⟨plan4215,valid4215,t5_571choices,?_⟩
  exact check_of_frontier tree 0 t5_571root t5_571jobs t5_571frontier t5_571all
theorem t5_572choices : plan4216.choices=[1,8,3,10,10].map (options 5 3) := by rfl


theorem t5_572part0 : t5_572jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_572frontier : t5_572root.frontier 0=t5_572jobs := by rfl
theorem t5_572all : t5_572jobs.all (Job.check tree)=true := by
  simp only [t5_572jobs,List.all_append,List.all_nil,t5_572part0,Bool.and_self]
theorem t5_572checked : Checked tree [1,8,3,10,10] := by
  refine ⟨plan4216,valid4216,t5_572choices,?_⟩
  exact check_of_frontier tree 0 t5_572root t5_572jobs t5_572frontier t5_572all
theorem t5_573choices : plan3892.choices=[1,8,5,3,3].map (options 5 2) := by rfl


theorem t5_573part0 : t5_573jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_573frontier : t5_573root.frontier 0=t5_573jobs := by rfl
theorem t5_573all : t5_573jobs.all (Job.check tree)=true := by
  simp only [t5_573jobs,List.all_append,List.all_nil,t5_573part0,Bool.and_self]
theorem t5_573checked : Checked tree [1,8,5,3,3] := by
  refine ⟨plan3892,valid3892,t5_573choices,?_⟩
  exact check_of_frontier tree 0 t5_573root t5_573jobs t5_573frontier t5_573all
theorem t5_574choices : plan4217.choices=[1,8,5,3,6].map (options 5 3) := by rfl


theorem t5_574part0 : t5_574jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_574frontier : t5_574root.frontier 0=t5_574jobs := by rfl
theorem t5_574all : t5_574jobs.all (Job.check tree)=true := by
  simp only [t5_574jobs,List.all_append,List.all_nil,t5_574part0,Bool.and_self]
theorem t5_574checked : Checked tree [1,8,5,3,6] := by
  refine ⟨plan4217,valid4217,t5_574choices,?_⟩
  exact check_of_frontier tree 0 t5_574root t5_574jobs t5_574frontier t5_574all
theorem t5_575choices : plan4218.choices=[1,8,5,3,7].map (options 5 3) := by rfl


theorem t5_575part0 : t5_575jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_575frontier : t5_575root.frontier 0=t5_575jobs := by rfl
theorem t5_575all : t5_575jobs.all (Job.check tree)=true := by
  simp only [t5_575jobs,List.all_append,List.all_nil,t5_575part0,Bool.and_self]
theorem t5_575checked : Checked tree [1,8,5,3,7] := by
  refine ⟨plan4218,valid4218,t5_575choices,?_⟩
  exact check_of_frontier tree 0 t5_575root t5_575jobs t5_575frontier t5_575all
theorem t5_576choices : plan4219.choices=[1,8,5,3,10].map (options 5 3) := by rfl


theorem t5_576part0 : t5_576jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_576frontier : t5_576root.frontier 0=t5_576jobs := by rfl
theorem t5_576all : t5_576jobs.all (Job.check tree)=true := by
  simp only [t5_576jobs,List.all_append,List.all_nil,t5_576part0,Bool.and_self]
theorem t5_576checked : Checked tree [1,8,5,3,10] := by
  refine ⟨plan4219,valid4219,t5_576choices,?_⟩
  exact check_of_frontier tree 0 t5_576root t5_576jobs t5_576frontier t5_576all
theorem t5_577choices : plan4612.choices=[1,8,5,5,7].map (options 5 4) := by rfl


theorem t5_577part0 : t5_577jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_577frontier : t5_577root.frontier 0=t5_577jobs := by rfl
theorem t5_577all : t5_577jobs.all (Job.check tree)=true := by
  simp only [t5_577jobs,List.all_append,List.all_nil,t5_577part0,Bool.and_self]
theorem t5_577checked : Checked tree [1,8,5,5,7] := by
  refine ⟨plan4612,valid4612,t5_577choices,?_⟩
  exact check_of_frontier tree 0 t5_577root t5_577jobs t5_577frontier t5_577all
theorem t5_578choices : plan4613.choices=[1,8,5,6,6].map (options 5 4) := by rfl


theorem t5_578part0 : t5_578jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_578frontier : t5_578root.frontier 0=t5_578jobs := by rfl
theorem t5_578all : t5_578jobs.all (Job.check tree)=true := by
  simp only [t5_578jobs,List.all_append,List.all_nil,t5_578part0,Bool.and_self]
theorem t5_578checked : Checked tree [1,8,5,6,6] := by
  refine ⟨plan4613,valid4613,t5_578choices,?_⟩
  exact check_of_frontier tree 0 t5_578root t5_578jobs t5_578frontier t5_578all
theorem t5_579choices : plan4614.choices=[1,8,5,6,7].map (options 5 4) := by rfl


theorem t5_579part0 : t5_579jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_579frontier : t5_579root.frontier 0=t5_579jobs := by rfl
theorem t5_579all : t5_579jobs.all (Job.check tree)=true := by
  simp only [t5_579jobs,List.all_append,List.all_nil,t5_579part0,Bool.and_self]
theorem t5_579checked : Checked tree [1,8,5,6,7] := by
  refine ⟨plan4614,valid4614,t5_579choices,?_⟩
  exact check_of_frontier tree 0 t5_579root t5_579jobs t5_579frontier t5_579all
theorem t5_580choices : plan4615.choices=[1,8,5,6,10].map (options 5 4) := by rfl


theorem t5_580part0 : t5_580jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_580frontier : t5_580root.frontier 0=t5_580jobs := by rfl
theorem t5_580all : t5_580jobs.all (Job.check tree)=true := by
  simp only [t5_580jobs,List.all_append,List.all_nil,t5_580part0,Bool.and_self]
theorem t5_580checked : Checked tree [1,8,5,6,10] := by
  refine ⟨plan4615,valid4615,t5_580choices,?_⟩
  exact check_of_frontier tree 0 t5_580root t5_580jobs t5_580frontier t5_580all
theorem t5_581choices : plan4616.choices=[1,8,5,7,7].map (options 5 4) := by rfl


theorem t5_581part0 : t5_581jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_581frontier : t5_581root.frontier 0=t5_581jobs := by rfl
theorem t5_581all : t5_581jobs.all (Job.check tree)=true := by
  simp only [t5_581jobs,List.all_append,List.all_nil,t5_581part0,Bool.and_self]
theorem t5_581checked : Checked tree [1,8,5,7,7] := by
  refine ⟨plan4616,valid4616,t5_581choices,?_⟩
  exact check_of_frontier tree 0 t5_581root t5_581jobs t5_581frontier t5_581all
theorem t5_582choices : plan4617.choices=[1,8,5,9,7].map (options 5 4) := by rfl


theorem t5_582part0 : t5_582jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_582frontier : t5_582root.frontier 0=t5_582jobs := by rfl
theorem t5_582all : t5_582jobs.all (Job.check tree)=true := by
  simp only [t5_582jobs,List.all_append,List.all_nil,t5_582part0,Bool.and_self]
theorem t5_582checked : Checked tree [1,8,5,9,7] := by
  refine ⟨plan4617,valid4617,t5_582choices,?_⟩
  exact check_of_frontier tree 0 t5_582root t5_582jobs t5_582frontier t5_582all
theorem t5_583choices : plan4618.choices=[1,8,5,10,7].map (options 5 4) := by rfl


theorem t5_583part0 : t5_583jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_583frontier : t5_583root.frontier 0=t5_583jobs := by rfl
theorem t5_583all : t5_583jobs.all (Job.check tree)=true := by
  simp only [t5_583jobs,List.all_append,List.all_nil,t5_583part0,Bool.and_self]
theorem t5_583checked : Checked tree [1,8,5,10,7] := by
  refine ⟨plan4618,valid4618,t5_583choices,?_⟩
  exact check_of_frontier tree 0 t5_583root t5_583jobs t5_583frontier t5_583all
theorem t5_584choices : plan4619.choices=[1,8,5,10,10].map (options 5 4) := by rfl


theorem t5_584part0 : t5_584jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_584frontier : t5_584root.frontier 0=t5_584jobs := by rfl
theorem t5_584all : t5_584jobs.all (Job.check tree)=true := by
  simp only [t5_584jobs,List.all_append,List.all_nil,t5_584part0,Bool.and_self]
theorem t5_584checked : Checked tree [1,8,5,10,10] := by
  refine ⟨plan4619,valid4619,t5_584choices,?_⟩
  exact check_of_frontier tree 0 t5_584root t5_584jobs t5_584frontier t5_584all
theorem t5_585choices : plan4620.choices=[1,8,6,6,6].map (options 5 4) := by rfl


theorem t5_585part0 : t5_585jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_585frontier : t5_585root.frontier 0=t5_585jobs := by rfl
theorem t5_585all : t5_585jobs.all (Job.check tree)=true := by
  simp only [t5_585jobs,List.all_append,List.all_nil,t5_585part0,Bool.and_self]
theorem t5_585checked : Checked tree [1,8,6,6,6] := by
  refine ⟨plan4620,valid4620,t5_585choices,?_⟩
  exact check_of_frontier tree 0 t5_585root t5_585jobs t5_585frontier t5_585all
theorem t5_586choices : plan4621.choices=[1,8,6,6,7].map (options 5 4) := by rfl


theorem t5_586part0 : t5_586jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_586frontier : t5_586root.frontier 0=t5_586jobs := by rfl
theorem t5_586all : t5_586jobs.all (Job.check tree)=true := by
  simp only [t5_586jobs,List.all_append,List.all_nil,t5_586part0,Bool.and_self]
theorem t5_586checked : Checked tree [1,8,6,6,7] := by
  refine ⟨plan4621,valid4621,t5_586choices,?_⟩
  exact check_of_frontier tree 0 t5_586root t5_586jobs t5_586frontier t5_586all
theorem t5_587choices : plan4622.choices=[1,8,6,6,10].map (options 5 4) := by rfl


theorem t5_587part0 : t5_587jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_587frontier : t5_587root.frontier 0=t5_587jobs := by rfl
theorem t5_587all : t5_587jobs.all (Job.check tree)=true := by
  simp only [t5_587jobs,List.all_append,List.all_nil,t5_587part0,Bool.and_self]
theorem t5_587checked : Checked tree [1,8,6,6,10] := by
  refine ⟨plan4622,valid4622,t5_587choices,?_⟩
  exact check_of_frontier tree 0 t5_587root t5_587jobs t5_587frontier t5_587all
theorem t5_588choices : plan4623.choices=[1,8,6,7,7].map (options 5 4) := by rfl


theorem t5_588part0 : t5_588jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_588frontier : t5_588root.frontier 0=t5_588jobs := by rfl
theorem t5_588all : t5_588jobs.all (Job.check tree)=true := by
  simp only [t5_588jobs,List.all_append,List.all_nil,t5_588part0,Bool.and_self]
theorem t5_588checked : Checked tree [1,8,6,7,7] := by
  refine ⟨plan4623,valid4623,t5_588choices,?_⟩
  exact check_of_frontier tree 0 t5_588root t5_588jobs t5_588frontier t5_588all
theorem t5_589choices : plan4624.choices=[1,8,6,10,7].map (options 5 4) := by rfl


theorem t5_589part0 : t5_589jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_589frontier : t5_589root.frontier 0=t5_589jobs := by rfl
theorem t5_589all : t5_589jobs.all (Job.check tree)=true := by
  simp only [t5_589jobs,List.all_append,List.all_nil,t5_589part0,Bool.and_self]
theorem t5_589checked : Checked tree [1,8,6,10,7] := by
  refine ⟨plan4624,valid4624,t5_589choices,?_⟩
  exact check_of_frontier tree 0 t5_589root t5_589jobs t5_589frontier t5_589all
theorem t5_590choices : plan4625.choices=[1,8,6,10,10].map (options 5 4) := by rfl


theorem t5_590part0 : t5_590jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_590frontier : t5_590root.frontier 0=t5_590jobs := by rfl
theorem t5_590all : t5_590jobs.all (Job.check tree)=true := by
  simp only [t5_590jobs,List.all_append,List.all_nil,t5_590part0,Bool.and_self]
theorem t5_590checked : Checked tree [1,8,6,10,10] := by
  refine ⟨plan4625,valid4625,t5_590choices,?_⟩
  exact check_of_frontier tree 0 t5_590root t5_590jobs t5_590frontier t5_590all
theorem t5_591choices : plan4626.choices=[1,8,7,7,7].map (options 5 4) := by rfl


theorem t5_591part0 : t5_591jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_591frontier : t5_591root.frontier 0=t5_591jobs := by rfl
theorem t5_591all : t5_591jobs.all (Job.check tree)=true := by
  simp only [t5_591jobs,List.all_append,List.all_nil,t5_591part0,Bool.and_self]
theorem t5_591checked : Checked tree [1,8,7,7,7] := by
  refine ⟨plan4626,valid4626,t5_591choices,?_⟩
  exact check_of_frontier tree 0 t5_591root t5_591jobs t5_591frontier t5_591all
theorem t5_592choices : plan4220.choices=[1,8,8,3,7].map (options 5 3) := by rfl


theorem t5_592part0 : t5_592jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_592frontier : t5_592root.frontier 0=t5_592jobs := by rfl
theorem t5_592all : t5_592jobs.all (Job.check tree)=true := by
  simp only [t5_592jobs,List.all_append,List.all_nil,t5_592part0,Bool.and_self]
theorem t5_592checked : Checked tree [1,8,8,3,7] := by
  refine ⟨plan4220,valid4220,t5_592choices,?_⟩
  exact check_of_frontier tree 0 t5_592root t5_592jobs t5_592frontier t5_592all
theorem t5_593choices : plan4627.choices=[1,8,8,6,7].map (options 5 4) := by rfl


theorem t5_593part0 : t5_593jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_593frontier : t5_593root.frontier 0=t5_593jobs := by rfl
theorem t5_593all : t5_593jobs.all (Job.check tree)=true := by
  simp only [t5_593jobs,List.all_append,List.all_nil,t5_593part0,Bool.and_self]
theorem t5_593checked : Checked tree [1,8,8,6,7] := by
  refine ⟨plan4627,valid4627,t5_593choices,?_⟩
  exact check_of_frontier tree 0 t5_593root t5_593jobs t5_593frontier t5_593all
theorem t5_594choices : plan4628.choices=[1,8,8,7,7].map (options 5 4) := by rfl


theorem t5_594part0 : t5_594jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_594frontier : t5_594root.frontier 0=t5_594jobs := by rfl
theorem t5_594all : t5_594jobs.all (Job.check tree)=true := by
  simp only [t5_594jobs,List.all_append,List.all_nil,t5_594part0,Bool.and_self]
theorem t5_594checked : Checked tree [1,8,8,7,7] := by
  refine ⟨plan4628,valid4628,t5_594choices,?_⟩
  exact check_of_frontier tree 0 t5_594root t5_594jobs t5_594frontier t5_594all
theorem t5_595choices : plan4629.choices=[1,8,8,10,7].map (options 5 4) := by rfl


theorem t5_595part0 : t5_595jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_595frontier : t5_595root.frontier 0=t5_595jobs := by rfl
theorem t5_595all : t5_595jobs.all (Job.check tree)=true := by
  simp only [t5_595jobs,List.all_append,List.all_nil,t5_595part0,Bool.and_self]
theorem t5_595checked : Checked tree [1,8,8,10,7] := by
  refine ⟨plan4629,valid4629,t5_595choices,?_⟩
  exact check_of_frontier tree 0 t5_595root t5_595jobs t5_595frontier t5_595all
theorem t5_596choices : plan3893.choices=[1,8,9,3,3].map (options 5 2) := by rfl


theorem t5_596part0 : t5_596jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_596frontier : t5_596root.frontier 0=t5_596jobs := by rfl
theorem t5_596all : t5_596jobs.all (Job.check tree)=true := by
  simp only [t5_596jobs,List.all_append,List.all_nil,t5_596part0,Bool.and_self]
theorem t5_596checked : Checked tree [1,8,9,3,3] := by
  refine ⟨plan3893,valid3893,t5_596choices,?_⟩
  exact check_of_frontier tree 0 t5_596root t5_596jobs t5_596frontier t5_596all
theorem t5_597choices : plan4221.choices=[1,8,9,3,6].map (options 5 3) := by rfl


theorem t5_597part0 : t5_597jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_597frontier : t5_597root.frontier 0=t5_597jobs := by rfl
theorem t5_597all : t5_597jobs.all (Job.check tree)=true := by
  simp only [t5_597jobs,List.all_append,List.all_nil,t5_597part0,Bool.and_self]
theorem t5_597checked : Checked tree [1,8,9,3,6] := by
  refine ⟨plan4221,valid4221,t5_597choices,?_⟩
  exact check_of_frontier tree 0 t5_597root t5_597jobs t5_597frontier t5_597all
theorem t5_598choices : plan4222.choices=[1,8,9,3,7].map (options 5 3) := by rfl


theorem t5_598part0 : t5_598jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_598frontier : t5_598root.frontier 0=t5_598jobs := by rfl
theorem t5_598all : t5_598jobs.all (Job.check tree)=true := by
  simp only [t5_598jobs,List.all_append,List.all_nil,t5_598part0,Bool.and_self]
theorem t5_598checked : Checked tree [1,8,9,3,7] := by
  refine ⟨plan4222,valid4222,t5_598choices,?_⟩
  exact check_of_frontier tree 0 t5_598root t5_598jobs t5_598frontier t5_598all
theorem t5_599choices : plan4223.choices=[1,8,9,3,10].map (options 5 3) := by rfl


theorem t5_599part0 : t5_599jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_599frontier : t5_599root.frontier 0=t5_599jobs := by rfl
theorem t5_599all : t5_599jobs.all (Job.check tree)=true := by
  simp only [t5_599jobs,List.all_append,List.all_nil,t5_599part0,Bool.and_self]
theorem t5_599checked : Checked tree [1,8,9,3,10] := by
  refine ⟨plan4223,valid4223,t5_599choices,?_⟩
  exact check_of_frontier tree 0 t5_599root t5_599jobs t5_599frontier t5_599all
theorem t5_600choices : plan4630.choices=[1,8,9,6,6].map (options 5 4) := by rfl


theorem t5_600part0 : t5_600jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_600frontier : t5_600root.frontier 0=t5_600jobs := by rfl
theorem t5_600all : t5_600jobs.all (Job.check tree)=true := by
  simp only [t5_600jobs,List.all_append,List.all_nil,t5_600part0,Bool.and_self]
theorem t5_600checked : Checked tree [1,8,9,6,6] := by
  refine ⟨plan4630,valid4630,t5_600choices,?_⟩
  exact check_of_frontier tree 0 t5_600root t5_600jobs t5_600frontier t5_600all
theorem t5_601choices : plan4631.choices=[1,8,9,6,7].map (options 5 4) := by rfl


theorem t5_601part0 : t5_601jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_601frontier : t5_601root.frontier 0=t5_601jobs := by rfl
theorem t5_601all : t5_601jobs.all (Job.check tree)=true := by
  simp only [t5_601jobs,List.all_append,List.all_nil,t5_601part0,Bool.and_self]
theorem t5_601checked : Checked tree [1,8,9,6,7] := by
  refine ⟨plan4631,valid4631,t5_601choices,?_⟩
  exact check_of_frontier tree 0 t5_601root t5_601jobs t5_601frontier t5_601all
theorem t5_602choices : plan4632.choices=[1,8,9,6,10].map (options 5 4) := by rfl


theorem t5_602part0 : t5_602jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_602frontier : t5_602root.frontier 0=t5_602jobs := by rfl
theorem t5_602all : t5_602jobs.all (Job.check tree)=true := by
  simp only [t5_602jobs,List.all_append,List.all_nil,t5_602part0,Bool.and_self]
theorem t5_602checked : Checked tree [1,8,9,6,10] := by
  refine ⟨plan4632,valid4632,t5_602choices,?_⟩
  exact check_of_frontier tree 0 t5_602root t5_602jobs t5_602frontier t5_602all
theorem t5_603choices : plan4633.choices=[1,8,9,7,7].map (options 5 4) := by rfl


theorem t5_603part0 : t5_603jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_603frontier : t5_603root.frontier 0=t5_603jobs := by rfl
theorem t5_603all : t5_603jobs.all (Job.check tree)=true := by
  simp only [t5_603jobs,List.all_append,List.all_nil,t5_603part0,Bool.and_self]
theorem t5_603checked : Checked tree [1,8,9,7,7] := by
  refine ⟨plan4633,valid4633,t5_603choices,?_⟩
  exact check_of_frontier tree 0 t5_603root t5_603jobs t5_603frontier t5_603all
theorem t5_604choices : plan4634.choices=[1,8,9,9,7].map (options 5 4) := by rfl


theorem t5_604part0 : t5_604jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_604frontier : t5_604root.frontier 0=t5_604jobs := by rfl
theorem t5_604all : t5_604jobs.all (Job.check tree)=true := by
  simp only [t5_604jobs,List.all_append,List.all_nil,t5_604part0,Bool.and_self]
theorem t5_604checked : Checked tree [1,8,9,9,7] := by
  refine ⟨plan4634,valid4634,t5_604choices,?_⟩
  exact check_of_frontier tree 0 t5_604root t5_604jobs t5_604frontier t5_604all
theorem t5_605choices : plan4635.choices=[1,8,9,10,7].map (options 5 4) := by rfl


theorem t5_605part0 : t5_605jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_605frontier : t5_605root.frontier 0=t5_605jobs := by rfl
theorem t5_605all : t5_605jobs.all (Job.check tree)=true := by
  simp only [t5_605jobs,List.all_append,List.all_nil,t5_605part0,Bool.and_self]
theorem t5_605checked : Checked tree [1,8,9,10,7] := by
  refine ⟨plan4635,valid4635,t5_605choices,?_⟩
  exact check_of_frontier tree 0 t5_605root t5_605jobs t5_605frontier t5_605all
theorem t5_606choices : plan4636.choices=[1,8,9,10,10].map (options 5 4) := by rfl


theorem t5_606part0 : t5_606jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_606frontier : t5_606root.frontier 0=t5_606jobs := by rfl
theorem t5_606all : t5_606jobs.all (Job.check tree)=true := by
  simp only [t5_606jobs,List.all_append,List.all_nil,t5_606part0,Bool.and_self]
theorem t5_606checked : Checked tree [1,8,9,10,10] := by
  refine ⟨plan4636,valid4636,t5_606choices,?_⟩
  exact check_of_frontier tree 0 t5_606root t5_606jobs t5_606frontier t5_606all
theorem t5_607choices : plan4637.choices=[1,8,10,7,7].map (options 5 4) := by rfl


theorem t5_607part0 : t5_607jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_607frontier : t5_607root.frontier 0=t5_607jobs := by rfl
theorem t5_607all : t5_607jobs.all (Job.check tree)=true := by
  simp only [t5_607jobs,List.all_append,List.all_nil,t5_607part0,Bool.and_self]
theorem t5_607checked : Checked tree [1,8,10,7,7] := by
  refine ⟨plan4637,valid4637,t5_607choices,?_⟩
  exact check_of_frontier tree 0 t5_607root t5_607jobs t5_607frontier t5_607all
theorem t5_608choices : plan4638.choices=[1,8,10,10,7].map (options 5 4) := by rfl


theorem t5_608part0 : t5_608jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_608frontier : t5_608root.frontier 0=t5_608jobs := by rfl
theorem t5_608all : t5_608jobs.all (Job.check tree)=true := by
  simp only [t5_608jobs,List.all_append,List.all_nil,t5_608part0,Bool.and_self]
theorem t5_608checked : Checked tree [1,8,10,10,7] := by
  refine ⟨plan4638,valid4638,t5_608choices,?_⟩
  exact check_of_frontier tree 0 t5_608root t5_608jobs t5_608frontier t5_608all
theorem t5_609choices : plan4639.choices=[1,8,10,10,10].map (options 5 4) := by rfl


theorem t5_609part0 : t5_609jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_609frontier : t5_609root.frontier 0=t5_609jobs := by rfl
theorem t5_609all : t5_609jobs.all (Job.check tree)=true := by
  simp only [t5_609jobs,List.all_append,List.all_nil,t5_609part0,Bool.and_self]
theorem t5_609checked : Checked tree [1,8,10,10,10] := by
  refine ⟨plan4639,valid4639,t5_609choices,?_⟩
  exact check_of_frontier tree 0 t5_609root t5_609jobs t5_609frontier t5_609all
theorem t5_610choices : plan3725.choices=[1,9,3,3,3].map (options 5 1) := by rfl


theorem t5_610part0 : t5_610jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_610frontier : t5_610root.frontier 0=t5_610jobs := by rfl
theorem t5_610all : t5_610jobs.all (Job.check tree)=true := by
  simp only [t5_610jobs,List.all_append,List.all_nil,t5_610part0,Bool.and_self]
theorem t5_610checked : Checked tree [1,9,3,3,3] := by
  refine ⟨plan3725,valid3725,t5_610choices,?_⟩
  exact check_of_frontier tree 0 t5_610root t5_610jobs t5_610frontier t5_610all
theorem t5_611choices : plan3894.choices=[1,9,3,3,6].map (options 5 2) := by rfl


theorem t5_611part0 : t5_611jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_611frontier : t5_611root.frontier 0=t5_611jobs := by rfl
theorem t5_611all : t5_611jobs.all (Job.check tree)=true := by
  simp only [t5_611jobs,List.all_append,List.all_nil,t5_611part0,Bool.and_self]
theorem t5_611checked : Checked tree [1,9,3,3,6] := by
  refine ⟨plan3894,valid3894,t5_611choices,?_⟩
  exact check_of_frontier tree 0 t5_611root t5_611jobs t5_611frontier t5_611all
theorem t5_612choices : plan3895.choices=[1,9,3,3,7].map (options 5 2) := by rfl


theorem t5_612part0 : t5_612jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_612frontier : t5_612root.frontier 0=t5_612jobs := by rfl
theorem t5_612all : t5_612jobs.all (Job.check tree)=true := by
  simp only [t5_612jobs,List.all_append,List.all_nil,t5_612part0,Bool.and_self]
theorem t5_612checked : Checked tree [1,9,3,3,7] := by
  refine ⟨plan3895,valid3895,t5_612choices,?_⟩
  exact check_of_frontier tree 0 t5_612root t5_612jobs t5_612frontier t5_612all
theorem t5_613choices : plan3896.choices=[1,9,3,3,10].map (options 5 2) := by rfl


theorem t5_613part0 : t5_613jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_613frontier : t5_613root.frontier 0=t5_613jobs := by rfl
theorem t5_613all : t5_613jobs.all (Job.check tree)=true := by
  simp only [t5_613jobs,List.all_append,List.all_nil,t5_613part0,Bool.and_self]
theorem t5_613checked : Checked tree [1,9,3,3,10] := by
  refine ⟨plan3896,valid3896,t5_613choices,?_⟩
  exact check_of_frontier tree 0 t5_613root t5_613jobs t5_613frontier t5_613all
theorem t5_614choices : plan4224.choices=[1,9,3,6,6].map (options 5 3) := by rfl


theorem t5_614part0 : t5_614jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_614frontier : t5_614root.frontier 0=t5_614jobs := by rfl
theorem t5_614all : t5_614jobs.all (Job.check tree)=true := by
  simp only [t5_614jobs,List.all_append,List.all_nil,t5_614part0,Bool.and_self]
theorem t5_614checked : Checked tree [1,9,3,6,6] := by
  refine ⟨plan4224,valid4224,t5_614choices,?_⟩
  exact check_of_frontier tree 0 t5_614root t5_614jobs t5_614frontier t5_614all
theorem t5_615choices : plan4225.choices=[1,9,3,6,7].map (options 5 3) := by rfl


theorem t5_615part0 : t5_615jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_615part1 : t5_615jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_615frontier : t5_615root.frontier 1=t5_615jobs := by rfl
theorem t5_615all : t5_615jobs.all (Job.check tree)=true := by
  simp only [t5_615jobs,List.all_append,List.all_nil,t5_615part0,t5_615part1,Bool.and_self]
theorem t5_615checked : Checked tree [1,9,3,6,7] := by
  refine ⟨plan4225,valid4225,t5_615choices,?_⟩
  exact check_of_frontier tree 1 t5_615root t5_615jobs t5_615frontier t5_615all
theorem t5_616choices : plan4226.choices=[1,9,3,6,10].map (options 5 3) := by rfl


theorem t5_616part0 : t5_616jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_616part1 : t5_616jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_616frontier : t5_616root.frontier 1=t5_616jobs := by rfl
theorem t5_616all : t5_616jobs.all (Job.check tree)=true := by
  simp only [t5_616jobs,List.all_append,List.all_nil,t5_616part0,t5_616part1,Bool.and_self]
theorem t5_616checked : Checked tree [1,9,3,6,10] := by
  refine ⟨plan4226,valid4226,t5_616choices,?_⟩
  exact check_of_frontier tree 1 t5_616root t5_616jobs t5_616frontier t5_616all
theorem t5_617choices : plan4227.choices=[1,9,3,7,7].map (options 5 3) := by rfl


theorem t5_617part0 : t5_617jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_617part1 : t5_617jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_617frontier : t5_617root.frontier 1=t5_617jobs := by rfl
theorem t5_617all : t5_617jobs.all (Job.check tree)=true := by
  simp only [t5_617jobs,List.all_append,List.all_nil,t5_617part0,t5_617part1,Bool.and_self]
theorem t5_617checked : Checked tree [1,9,3,7,7] := by
  refine ⟨plan4227,valid4227,t5_617choices,?_⟩
  exact check_of_frontier tree 1 t5_617root t5_617jobs t5_617frontier t5_617all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks013 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_567checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_580checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_581checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_582checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_583checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_584checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_585checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_586checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_587checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_588checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_589checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_568checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_590checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_591checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_592checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_593checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_594checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_595checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_596checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_597checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_598checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_599checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_569checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_600checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_601checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_602checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_603checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_604checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_605checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_606checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_607checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_608checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_609checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_570checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_610checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_611checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_612checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_613checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_614checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_615checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_616checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_617checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_571checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_572checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_573checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_574checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_575checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_576checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_577checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_578checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_579checked⟩
