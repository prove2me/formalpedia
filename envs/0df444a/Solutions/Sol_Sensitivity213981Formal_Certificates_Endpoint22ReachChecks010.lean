-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks010
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:46:07.593718+00:00
-- url     : https://prove2.me/submissions/55a7be7d-bf9d-41d7-8c73-1fe77d17afd5

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans047
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













theorem valid460 : plan460.Valid := valid_step _ _ _ valid97 (by decide +kernel)



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







theorem valid491 : plan491.Valid := valid_step _ _ _ valid103 (by decide +kernel)





theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)





theorem valid500 : plan500.Valid := valid_step _ _ _ valid103 (by decide +kernel)





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



















theorem valid1258 : plan1258.Valid := valid_step _ _ _ valid453 (by decide +kernel)











theorem valid1264 : plan1264.Valid := valid_step _ _ _ valid453 (by decide +kernel)



















theorem valid1274 : plan1274.Valid := valid_step _ _ _ valid460 (by decide +kernel)





theorem valid1277 : plan1277.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1278 : plan1278.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1279 : plan1279.Valid := valid_step _ _ _ valid465 (by decide +kernel)





































theorem valid1298 : plan1298.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1299 : plan1299.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1300 : plan1300.Valid := valid_step _ _ _ valid465 (by decide +kernel)















theorem valid1308 : plan1308.Valid := valid_step _ _ _ valid462 (by decide +kernel)

































theorem valid1325 : plan1325.Valid := valid_step _ _ _ valid491 (by decide +kernel)



theorem valid1327 : plan1327.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1328 : plan1328.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1329 : plan1329.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1330 : plan1330.Valid := valid_step _ _ _ valid497 (by decide +kernel)



theorem valid1332 : plan1332.Valid := valid_step _ _ _ valid500 (by decide +kernel)



theorem valid1334 : plan1334.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1335 : plan1335.Valid := valid_step _ _ _ valid504 (by decide +kernel)







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

















































































































theorem valid2553 : plan2553.Valid := valid_step _ _ _ valid1258 (by decide +kernel)

theorem valid2554 : plan2554.Valid := valid_step _ _ _ valid1264 (by decide +kernel)












































































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















































































































































theorem valid3720 : plan3720.Valid := valid_step _ _ _ valid2553 (by decide +kernel)

theorem valid3721 : plan3721.Valid := valid_step _ _ _ valid2554 (by decide +kernel)














































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

theorem valid1345 : plan1345.Valid := valid_step _ _ _ valid486 (by decide +kernel)









theorem valid1350 : plan1350.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1351 : plan1351.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1352 : plan1352.Valid := valid_step _ _ _ valid487 (by decide +kernel)











































theorem valid1374 : plan1374.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1375 : plan1375.Valid := valid_step _ _ _ valid504 (by decide +kernel)

theorem valid1376 : plan1376.Valid := valid_step _ _ _ valid497 (by decide +kernel)







































theorem valid1396 : plan1396.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1397 : plan1397.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1398 : plan1398.Valid := valid_step _ _ _ valid504 (by decide +kernel)































theorem valid1414 : plan1414.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1415 : plan1415.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1416 : plan1416.Valid := valid_step _ _ _ valid523 (by decide +kernel)













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























































































theorem valid2636 : plan2636.Valid := valid_step _ _ _ valid1274 (by decide +kernel)



theorem valid2638 : plan2638.Valid := valid_step _ _ _ valid1277 (by decide +kernel)

theorem valid2639 : plan2639.Valid := valid_step _ _ _ valid1278 (by decide +kernel)

theorem valid2640 : plan2640.Valid := valid_step _ _ _ valid1279 (by decide +kernel)



theorem valid2642 : plan2642.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2643 : plan2643.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2644 : plan2644.Valid := valid_step _ _ _ valid1300 (by decide +kernel)

theorem valid2645 : plan2645.Valid := valid_step _ _ _ valid1308 (by decide +kernel)






















































































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







































































































































































theorem valid2772 : plan2772.Valid := valid_step _ _ _ valid1374 (by decide +kernel)

theorem valid2773 : plan2773.Valid := valid_step _ _ _ valid1375 (by decide +kernel)

theorem valid2774 : plan2774.Valid := valid_step _ _ _ valid1376 (by decide +kernel)

theorem valid2775 : plan2775.Valid := valid_step _ _ _ valid1396 (by decide +kernel)

theorem valid2776 : plan2776.Valid := valid_step _ _ _ valid1397 (by decide +kernel)

theorem valid2777 : plan2777.Valid := valid_step _ _ _ valid1398 (by decide +kernel)









theorem valid2782 : plan2782.Valid := valid_step _ _ _ valid1325 (by decide +kernel)

theorem valid2783 : plan2783.Valid := valid_step _ _ _ valid1327 (by decide +kernel)

theorem valid2784 : plan2784.Valid := valid_step _ _ _ valid1328 (by decide +kernel)
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

theorem valid2785 : plan2785.Valid := valid_step _ _ _ valid1329 (by decide +kernel)

theorem valid2786 : plan2786.Valid := valid_step _ _ _ valid1330 (by decide +kernel)

theorem valid2787 : plan2787.Valid := valid_step _ _ _ valid1332 (by decide +kernel)

theorem valid2788 : plan2788.Valid := valid_step _ _ _ valid1334 (by decide +kernel)

theorem valid2789 : plan2789.Valid := valid_step _ _ _ valid1335 (by decide +kernel)







theorem valid2793 : plan2793.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2794 : plan2794.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2795 : plan2795.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2796 : plan2796.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2797 : plan2797.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2798 : plan2798.Valid := valid_step _ _ _ valid1344 (by decide +kernel)

theorem valid2799 : plan2799.Valid := valid_step _ _ _ valid1345 (by decide +kernel)



theorem valid2801 : plan2801.Valid := valid_step _ _ _ valid1350 (by decide +kernel)

theorem valid2802 : plan2802.Valid := valid_step _ _ _ valid1351 (by decide +kernel)

theorem valid2803 : plan2803.Valid := valid_step _ _ _ valid1352 (by decide +kernel)


























































































































































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

































































































theorem valid2929 : plan2929.Valid := valid_step _ _ _ valid1414 (by decide +kernel)

theorem valid2930 : plan2930.Valid := valid_step _ _ _ valid1415 (by decide +kernel)

theorem valid2931 : plan2931.Valid := valid_step _ _ _ valid1416 (by decide +kernel)







theorem valid2935 : plan2935.Valid := valid_step _ _ _ valid1423 (by decide +kernel)

theorem valid2936 : plan2936.Valid := valid_step _ _ _ valid1426 (by decide +kernel)

theorem valid2937 : plan2937.Valid := valid_step _ _ _ valid1427 (by decide +kernel)

theorem valid2938 : plan2938.Valid := valid_step _ _ _ valid1428 (by decide +kernel)

theorem valid2939 : plan2939.Valid := valid_step _ _ _ valid1429 (by decide +kernel)

theorem valid2940 : plan2940.Valid := valid_step _ _ _ valid1432 (by decide +kernel)

theorem valid2941 : plan2941.Valid := valid_step _ _ _ valid1435 (by decide +kernel)

theorem valid2942 : plan2942.Valid := valid_step _ _ _ valid1436 (by decide +kernel)

theorem valid2943 : plan2943.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid2944 : plan2944.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid2945 : plan2945.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid2946 : plan2946.Valid := valid_step _ _ _ valid1440 (by decide +kernel)




























































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





















































theorem valid4539 : plan4539.Valid := valid_step _ _ _ valid2929 (by decide +kernel)

theorem valid4540 : plan4540.Valid := valid_step _ _ _ valid2930 (by decide +kernel)

theorem valid4541 : plan4541.Valid := valid_step _ _ _ valid2931 (by decide +kernel)

theorem valid4542 : plan4542.Valid := valid_step _ _ _ valid2935 (by decide +kernel)

theorem valid4543 : plan4543.Valid := valid_step _ _ _ valid2936 (by decide +kernel)

theorem valid4544 : plan4544.Valid := valid_step _ _ _ valid2937 (by decide +kernel)

theorem valid4545 : plan4545.Valid := valid_step _ _ _ valid2938 (by decide +kernel)

theorem valid4546 : plan4546.Valid := valid_step _ _ _ valid2939 (by decide +kernel)

theorem valid4547 : plan4547.Valid := valid_step _ _ _ valid2940 (by decide +kernel)

theorem valid4548 : plan4548.Valid := valid_step _ _ _ valid2941 (by decide +kernel)

theorem valid4549 : plan4549.Valid := valid_step _ _ _ valid2942 (by decide +kernel)

theorem valid4550 : plan4550.Valid := valid_step _ _ _ valid2943 (by decide +kernel)

theorem valid4551 : plan4551.Valid := valid_step _ _ _ valid2944 (by decide +kernel)

theorem valid4552 : plan4552.Valid := valid_step _ _ _ valid2945 (by decide +kernel)

theorem valid4553 : plan4553.Valid := valid_step _ _ _ valid2946 (by decide +kernel)














































































































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





























































theorem valid3871 : plan3871.Valid := valid_step _ _ _ valid2636 (by decide +kernel)

theorem valid3872 : plan3872.Valid := valid_step _ _ _ valid2638 (by decide +kernel)

theorem valid3873 : plan3873.Valid := valid_step _ _ _ valid2639 (by decide +kernel)

theorem valid3874 : plan3874.Valid := valid_step _ _ _ valid2640 (by decide +kernel)

theorem valid3875 : plan3875.Valid := valid_step _ _ _ valid2642 (by decide +kernel)

theorem valid3876 : plan3876.Valid := valid_step _ _ _ valid2643 (by decide +kernel)

theorem valid3877 : plan3877.Valid := valid_step _ _ _ valid2644 (by decide +kernel)

theorem valid3878 : plan3878.Valid := valid_step _ _ _ valid2645 (by decide +kernel)




















































































































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































































theorem valid4160 : plan4160.Valid := valid_step _ _ _ valid2772 (by decide +kernel)

theorem valid4161 : plan4161.Valid := valid_step _ _ _ valid2773 (by decide +kernel)

theorem valid4162 : plan4162.Valid := valid_step _ _ _ valid2774 (by decide +kernel)

theorem valid4163 : plan4163.Valid := valid_step _ _ _ valid2775 (by decide +kernel)

theorem valid4164 : plan4164.Valid := valid_step _ _ _ valid2776 (by decide +kernel)

theorem valid4165 : plan4165.Valid := valid_step _ _ _ valid2777 (by decide +kernel)

theorem valid4166 : plan4166.Valid := valid_step _ _ _ valid2782 (by decide +kernel)

theorem valid4167 : plan4167.Valid := valid_step _ _ _ valid2783 (by decide +kernel)

theorem valid4168 : plan4168.Valid := valid_step _ _ _ valid2784 (by decide +kernel)

theorem valid4169 : plan4169.Valid := valid_step _ _ _ valid2785 (by decide +kernel)

theorem valid4170 : plan4170.Valid := valid_step _ _ _ valid2786 (by decide +kernel)

theorem valid4171 : plan4171.Valid := valid_step _ _ _ valid2787 (by decide +kernel)

theorem valid4172 : plan4172.Valid := valid_step _ _ _ valid2788 (by decide +kernel)

theorem valid4173 : plan4173.Valid := valid_step _ _ _ valid2789 (by decide +kernel)

theorem valid4174 : plan4174.Valid := valid_step _ _ _ valid2793 (by decide +kernel)

theorem valid4175 : plan4175.Valid := valid_step _ _ _ valid2794 (by decide +kernel)

theorem valid4176 : plan4176.Valid := valid_step _ _ _ valid2795 (by decide +kernel)

theorem valid4177 : plan4177.Valid := valid_step _ _ _ valid2796 (by decide +kernel)

theorem valid4178 : plan4178.Valid := valid_step _ _ _ valid2797 (by decide +kernel)

theorem valid4179 : plan4179.Valid := valid_step _ _ _ valid2798 (by decide +kernel)

theorem valid4180 : plan4180.Valid := valid_step _ _ _ valid2799 (by decide +kernel)

theorem valid4181 : plan4181.Valid := valid_step _ _ _ valid2801 (by decide +kernel)

theorem valid4182 : plan4182.Valid := valid_step _ _ _ valid2802 (by decide +kernel)

theorem valid4183 : plan4183.Valid := valid_step _ _ _ valid2803 (by decide +kernel)


















































































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
theorem t5_417choices : plan4160.choices=[1,3,6,10,7].map (options 5 3) := by rfl


theorem t5_417part0 : t5_417jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_417part1 : t5_417jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_417part2 : t5_417jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_417frontier : t5_417root.frontier 2=t5_417jobs := by rfl
theorem t5_417all : t5_417jobs.all (Job.check tree)=true := by
  simp only [t5_417jobs,List.all_append,List.all_nil,t5_417part0,t5_417part1,t5_417part2,Bool.and_self]
theorem t5_417checked : Checked tree [1,3,6,10,7] := by
  refine ⟨plan4160,valid4160,t5_417choices,?_⟩
  exact check_of_frontier tree 2 t5_417root t5_417jobs t5_417frontier t5_417all
theorem t5_418choices : plan4161.choices=[1,3,6,10,10].map (options 5 3) := by rfl


theorem t5_418part0 : t5_418jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_418part1 : t5_418jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_418frontier : t5_418root.frontier 1=t5_418jobs := by rfl
theorem t5_418all : t5_418jobs.all (Job.check tree)=true := by
  simp only [t5_418jobs,List.all_append,List.all_nil,t5_418part0,t5_418part1,Bool.and_self]
theorem t5_418checked : Checked tree [1,3,6,10,10] := by
  refine ⟨plan4161,valid4161,t5_418choices,?_⟩
  exact check_of_frontier tree 1 t5_418root t5_418jobs t5_418frontier t5_418all
theorem t5_419choices : plan4162.choices=[1,3,7,7,7].map (options 5 3) := by rfl


theorem t5_419part0 : t5_419jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_419frontier : t5_419root.frontier 0=t5_419jobs := by rfl
theorem t5_419all : t5_419jobs.all (Job.check tree)=true := by
  simp only [t5_419jobs,List.all_append,List.all_nil,t5_419part0,Bool.and_self]
theorem t5_419checked : Checked tree [1,3,7,7,7] := by
  refine ⟨plan4162,valid4162,t5_419choices,?_⟩
  exact check_of_frontier tree 0 t5_419root t5_419jobs t5_419frontier t5_419all
theorem t5_420choices : plan4163.choices=[1,3,10,7,7].map (options 5 3) := by rfl


theorem t5_420part0 : t5_420jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_420part1 : t5_420jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_420frontier : t5_420root.frontier 1=t5_420jobs := by rfl
theorem t5_420all : t5_420jobs.all (Job.check tree)=true := by
  simp only [t5_420jobs,List.all_append,List.all_nil,t5_420part0,t5_420part1,Bool.and_self]
theorem t5_420checked : Checked tree [1,3,10,7,7] := by
  refine ⟨plan4163,valid4163,t5_420choices,?_⟩
  exact check_of_frontier tree 1 t5_420root t5_420jobs t5_420frontier t5_420all
theorem t5_421choices : plan4164.choices=[1,3,10,10,7].map (options 5 3) := by rfl


theorem t5_421part0 : t5_421jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_421part1 : t5_421jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_421frontier : t5_421root.frontier 1=t5_421jobs := by rfl
theorem t5_421all : t5_421jobs.all (Job.check tree)=true := by
  simp only [t5_421jobs,List.all_append,List.all_nil,t5_421part0,t5_421part1,Bool.and_self]
theorem t5_421checked : Checked tree [1,3,10,10,7] := by
  refine ⟨plan4164,valid4164,t5_421choices,?_⟩
  exact check_of_frontier tree 1 t5_421root t5_421jobs t5_421frontier t5_421all
theorem t5_422choices : plan4165.choices=[1,3,10,10,10].map (options 5 3) := by rfl


theorem t5_422part0 : t5_422jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_422frontier : t5_422root.frontier 0=t5_422jobs := by rfl
theorem t5_422all : t5_422jobs.all (Job.check tree)=true := by
  simp only [t5_422jobs,List.all_append,List.all_nil,t5_422part0,Bool.and_self]
theorem t5_422checked : Checked tree [1,3,10,10,10] := by
  refine ⟨plan4165,valid4165,t5_422choices,?_⟩
  exact check_of_frontier tree 0 t5_422root t5_422jobs t5_422frontier t5_422all
theorem t5_423choices : plan3871.choices=[1,4,2,2,7].map (options 5 2) := by rfl


theorem t5_423part0 : t5_423jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_423frontier : t5_423root.frontier 0=t5_423jobs := by rfl
theorem t5_423all : t5_423jobs.all (Job.check tree)=true := by
  simp only [t5_423jobs,List.all_append,List.all_nil,t5_423part0,Bool.and_self]
theorem t5_423checked : Checked tree [1,4,2,2,7] := by
  refine ⟨plan3871,valid3871,t5_423choices,?_⟩
  exact check_of_frontier tree 0 t5_423root t5_423jobs t5_423frontier t5_423all
theorem t5_424choices : plan3720.choices=[1,4,2,3,3].map (options 5 1) := by rfl


theorem t5_424part0 : t5_424jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_424frontier : t5_424root.frontier 0=t5_424jobs := by rfl
theorem t5_424all : t5_424jobs.all (Job.check tree)=true := by
  simp only [t5_424jobs,List.all_append,List.all_nil,t5_424part0,Bool.and_self]
theorem t5_424checked : Checked tree [1,4,2,3,3] := by
  refine ⟨plan3720,valid3720,t5_424choices,?_⟩
  exact check_of_frontier tree 0 t5_424root t5_424jobs t5_424frontier t5_424all
theorem t5_425choices : plan3872.choices=[1,4,2,3,6].map (options 5 2) := by rfl


theorem t5_425part0 : t5_425jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_425frontier : t5_425root.frontier 0=t5_425jobs := by rfl
theorem t5_425all : t5_425jobs.all (Job.check tree)=true := by
  simp only [t5_425jobs,List.all_append,List.all_nil,t5_425part0,Bool.and_self]
theorem t5_425checked : Checked tree [1,4,2,3,6] := by
  refine ⟨plan3872,valid3872,t5_425choices,?_⟩
  exact check_of_frontier tree 0 t5_425root t5_425jobs t5_425frontier t5_425all
theorem t5_426choices : plan3873.choices=[1,4,2,3,7].map (options 5 2) := by rfl


theorem t5_426part0 : t5_426jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_426frontier : t5_426root.frontier 0=t5_426jobs := by rfl
theorem t5_426all : t5_426jobs.all (Job.check tree)=true := by
  simp only [t5_426jobs,List.all_append,List.all_nil,t5_426part0,Bool.and_self]
theorem t5_426checked : Checked tree [1,4,2,3,7] := by
  refine ⟨plan3873,valid3873,t5_426choices,?_⟩
  exact check_of_frontier tree 0 t5_426root t5_426jobs t5_426frontier t5_426all
theorem t5_427choices : plan3874.choices=[1,4,2,3,10].map (options 5 2) := by rfl


theorem t5_427part0 : t5_427jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_427frontier : t5_427root.frontier 0=t5_427jobs := by rfl
theorem t5_427all : t5_427jobs.all (Job.check tree)=true := by
  simp only [t5_427jobs,List.all_append,List.all_nil,t5_427part0,Bool.and_self]
theorem t5_427checked : Checked tree [1,4,2,3,10] := by
  refine ⟨plan3874,valid3874,t5_427choices,?_⟩
  exact check_of_frontier tree 0 t5_427root t5_427jobs t5_427frontier t5_427all
theorem t5_428choices : plan4166.choices=[1,4,2,5,7].map (options 5 3) := by rfl


theorem t5_428part0 : t5_428jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_428frontier : t5_428root.frontier 0=t5_428jobs := by rfl
theorem t5_428all : t5_428jobs.all (Job.check tree)=true := by
  simp only [t5_428jobs,List.all_append,List.all_nil,t5_428part0,Bool.and_self]
theorem t5_428checked : Checked tree [1,4,2,5,7] := by
  refine ⟨plan4166,valid4166,t5_428choices,?_⟩
  exact check_of_frontier tree 0 t5_428root t5_428jobs t5_428frontier t5_428all
theorem t5_429choices : plan4167.choices=[1,4,2,6,6].map (options 5 3) := by rfl


theorem t5_429part0 : t5_429jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_429frontier : t5_429root.frontier 0=t5_429jobs := by rfl
theorem t5_429all : t5_429jobs.all (Job.check tree)=true := by
  simp only [t5_429jobs,List.all_append,List.all_nil,t5_429part0,Bool.and_self]
theorem t5_429checked : Checked tree [1,4,2,6,6] := by
  refine ⟨plan4167,valid4167,t5_429choices,?_⟩
  exact check_of_frontier tree 0 t5_429root t5_429jobs t5_429frontier t5_429all
theorem t5_430choices : plan4168.choices=[1,4,2,6,7].map (options 5 3) := by rfl


theorem t5_430part0 : t5_430jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_430frontier : t5_430root.frontier 0=t5_430jobs := by rfl
theorem t5_430all : t5_430jobs.all (Job.check tree)=true := by
  simp only [t5_430jobs,List.all_append,List.all_nil,t5_430part0,Bool.and_self]
theorem t5_430checked : Checked tree [1,4,2,6,7] := by
  refine ⟨plan4168,valid4168,t5_430choices,?_⟩
  exact check_of_frontier tree 0 t5_430root t5_430jobs t5_430frontier t5_430all
theorem t5_431choices : plan4169.choices=[1,4,2,6,10].map (options 5 3) := by rfl


theorem t5_431part0 : t5_431jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_431frontier : t5_431root.frontier 0=t5_431jobs := by rfl
theorem t5_431all : t5_431jobs.all (Job.check tree)=true := by
  simp only [t5_431jobs,List.all_append,List.all_nil,t5_431part0,Bool.and_self]
theorem t5_431checked : Checked tree [1,4,2,6,10] := by
  refine ⟨plan4169,valid4169,t5_431choices,?_⟩
  exact check_of_frontier tree 0 t5_431root t5_431jobs t5_431frontier t5_431all
theorem t5_432choices : plan4170.choices=[1,4,2,7,7].map (options 5 3) := by rfl


theorem t5_432part0 : t5_432jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_432frontier : t5_432root.frontier 0=t5_432jobs := by rfl
theorem t5_432all : t5_432jobs.all (Job.check tree)=true := by
  simp only [t5_432jobs,List.all_append,List.all_nil,t5_432part0,Bool.and_self]
theorem t5_432checked : Checked tree [1,4,2,7,7] := by
  refine ⟨plan4170,valid4170,t5_432choices,?_⟩
  exact check_of_frontier tree 0 t5_432root t5_432jobs t5_432frontier t5_432all
theorem t5_433choices : plan4171.choices=[1,4,2,9,7].map (options 5 3) := by rfl


theorem t5_433part0 : t5_433jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_433frontier : t5_433root.frontier 0=t5_433jobs := by rfl
theorem t5_433all : t5_433jobs.all (Job.check tree)=true := by
  simp only [t5_433jobs,List.all_append,List.all_nil,t5_433part0,Bool.and_self]
theorem t5_433checked : Checked tree [1,4,2,9,7] := by
  refine ⟨plan4171,valid4171,t5_433choices,?_⟩
  exact check_of_frontier tree 0 t5_433root t5_433jobs t5_433frontier t5_433all
theorem t5_434choices : plan4172.choices=[1,4,2,10,7].map (options 5 3) := by rfl


theorem t5_434part0 : t5_434jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_434frontier : t5_434root.frontier 0=t5_434jobs := by rfl
theorem t5_434all : t5_434jobs.all (Job.check tree)=true := by
  simp only [t5_434jobs,List.all_append,List.all_nil,t5_434part0,Bool.and_self]
theorem t5_434checked : Checked tree [1,4,2,10,7] := by
  refine ⟨plan4172,valid4172,t5_434choices,?_⟩
  exact check_of_frontier tree 0 t5_434root t5_434jobs t5_434frontier t5_434all
theorem t5_435choices : plan4173.choices=[1,4,2,10,10].map (options 5 3) := by rfl


theorem t5_435part0 : t5_435jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_435frontier : t5_435root.frontier 0=t5_435jobs := by rfl
theorem t5_435all : t5_435jobs.all (Job.check tree)=true := by
  simp only [t5_435jobs,List.all_append,List.all_nil,t5_435part0,Bool.and_self]
theorem t5_435checked : Checked tree [1,4,2,10,10] := by
  refine ⟨plan4173,valid4173,t5_435choices,?_⟩
  exact check_of_frontier tree 0 t5_435root t5_435jobs t5_435frontier t5_435all
theorem t5_436choices : plan3721.choices=[1,4,3,3,3].map (options 5 1) := by rfl


theorem t5_436part0 : t5_436jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_436frontier : t5_436root.frontier 0=t5_436jobs := by rfl
theorem t5_436all : t5_436jobs.all (Job.check tree)=true := by
  simp only [t5_436jobs,List.all_append,List.all_nil,t5_436part0,Bool.and_self]
theorem t5_436checked : Checked tree [1,4,3,3,3] := by
  refine ⟨plan3721,valid3721,t5_436choices,?_⟩
  exact check_of_frontier tree 0 t5_436root t5_436jobs t5_436frontier t5_436all
theorem t5_437choices : plan3875.choices=[1,4,3,3,6].map (options 5 2) := by rfl


theorem t5_437part0 : t5_437jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_437frontier : t5_437root.frontier 0=t5_437jobs := by rfl
theorem t5_437all : t5_437jobs.all (Job.check tree)=true := by
  simp only [t5_437jobs,List.all_append,List.all_nil,t5_437part0,Bool.and_self]
theorem t5_437checked : Checked tree [1,4,3,3,6] := by
  refine ⟨plan3875,valid3875,t5_437choices,?_⟩
  exact check_of_frontier tree 0 t5_437root t5_437jobs t5_437frontier t5_437all
theorem t5_438choices : plan3876.choices=[1,4,3,3,7].map (options 5 2) := by rfl


theorem t5_438part0 : t5_438jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_438frontier : t5_438root.frontier 0=t5_438jobs := by rfl
theorem t5_438all : t5_438jobs.all (Job.check tree)=true := by
  simp only [t5_438jobs,List.all_append,List.all_nil,t5_438part0,Bool.and_self]
theorem t5_438checked : Checked tree [1,4,3,3,7] := by
  refine ⟨plan3876,valid3876,t5_438choices,?_⟩
  exact check_of_frontier tree 0 t5_438root t5_438jobs t5_438frontier t5_438all
theorem t5_439choices : plan3877.choices=[1,4,3,3,10].map (options 5 2) := by rfl


theorem t5_439part0 : t5_439jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_439frontier : t5_439root.frontier 0=t5_439jobs := by rfl
theorem t5_439all : t5_439jobs.all (Job.check tree)=true := by
  simp only [t5_439jobs,List.all_append,List.all_nil,t5_439part0,Bool.and_self]
theorem t5_439checked : Checked tree [1,4,3,3,10] := by
  refine ⟨plan3877,valid3877,t5_439choices,?_⟩
  exact check_of_frontier tree 0 t5_439root t5_439jobs t5_439frontier t5_439all
theorem t5_440choices : plan4174.choices=[1,4,3,6,6].map (options 5 3) := by rfl


theorem t5_440part0 : t5_440jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_440frontier : t5_440root.frontier 0=t5_440jobs := by rfl
theorem t5_440all : t5_440jobs.all (Job.check tree)=true := by
  simp only [t5_440jobs,List.all_append,List.all_nil,t5_440part0,Bool.and_self]
theorem t5_440checked : Checked tree [1,4,3,6,6] := by
  refine ⟨plan4174,valid4174,t5_440choices,?_⟩
  exact check_of_frontier tree 0 t5_440root t5_440jobs t5_440frontier t5_440all
theorem t5_441choices : plan4175.choices=[1,4,3,6,7].map (options 5 3) := by rfl


theorem t5_441part0 : t5_441jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_441frontier : t5_441root.frontier 0=t5_441jobs := by rfl
theorem t5_441all : t5_441jobs.all (Job.check tree)=true := by
  simp only [t5_441jobs,List.all_append,List.all_nil,t5_441part0,Bool.and_self]
theorem t5_441checked : Checked tree [1,4,3,6,7] := by
  refine ⟨plan4175,valid4175,t5_441choices,?_⟩
  exact check_of_frontier tree 0 t5_441root t5_441jobs t5_441frontier t5_441all
theorem t5_442choices : plan4176.choices=[1,4,3,6,10].map (options 5 3) := by rfl


theorem t5_442part0 : t5_442jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_442frontier : t5_442root.frontier 0=t5_442jobs := by rfl
theorem t5_442all : t5_442jobs.all (Job.check tree)=true := by
  simp only [t5_442jobs,List.all_append,List.all_nil,t5_442part0,Bool.and_self]
theorem t5_442checked : Checked tree [1,4,3,6,10] := by
  refine ⟨plan4176,valid4176,t5_442choices,?_⟩
  exact check_of_frontier tree 0 t5_442root t5_442jobs t5_442frontier t5_442all
theorem t5_443choices : plan4177.choices=[1,4,3,7,7].map (options 5 3) := by rfl


theorem t5_443part0 : t5_443jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_443frontier : t5_443root.frontier 0=t5_443jobs := by rfl
theorem t5_443all : t5_443jobs.all (Job.check tree)=true := by
  simp only [t5_443jobs,List.all_append,List.all_nil,t5_443part0,Bool.and_self]
theorem t5_443checked : Checked tree [1,4,3,7,7] := by
  refine ⟨plan4177,valid4177,t5_443choices,?_⟩
  exact check_of_frontier tree 0 t5_443root t5_443jobs t5_443frontier t5_443all
theorem t5_444choices : plan4178.choices=[1,4,3,10,7].map (options 5 3) := by rfl


theorem t5_444part0 : t5_444jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_444frontier : t5_444root.frontier 0=t5_444jobs := by rfl
theorem t5_444all : t5_444jobs.all (Job.check tree)=true := by
  simp only [t5_444jobs,List.all_append,List.all_nil,t5_444part0,Bool.and_self]
theorem t5_444checked : Checked tree [1,4,3,10,7] := by
  refine ⟨plan4178,valid4178,t5_444choices,?_⟩
  exact check_of_frontier tree 0 t5_444root t5_444jobs t5_444frontier t5_444all
theorem t5_445choices : plan4179.choices=[1,4,3,10,10].map (options 5 3) := by rfl


theorem t5_445part0 : t5_445jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_445frontier : t5_445root.frontier 0=t5_445jobs := by rfl
theorem t5_445all : t5_445jobs.all (Job.check tree)=true := by
  simp only [t5_445jobs,List.all_append,List.all_nil,t5_445part0,Bool.and_self]
theorem t5_445checked : Checked tree [1,4,3,10,10] := by
  refine ⟨plan4179,valid4179,t5_445choices,?_⟩
  exact check_of_frontier tree 0 t5_445root t5_445jobs t5_445frontier t5_445all
theorem t5_446choices : plan4180.choices=[1,4,4,3,7].map (options 5 3) := by rfl


theorem t5_446part0 : t5_446jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_446frontier : t5_446root.frontier 0=t5_446jobs := by rfl
theorem t5_446all : t5_446jobs.all (Job.check tree)=true := by
  simp only [t5_446jobs,List.all_append,List.all_nil,t5_446part0,Bool.and_self]
theorem t5_446checked : Checked tree [1,4,4,3,7] := by
  refine ⟨plan4180,valid4180,t5_446choices,?_⟩
  exact check_of_frontier tree 0 t5_446root t5_446jobs t5_446frontier t5_446all
theorem t5_447choices : plan4539.choices=[1,4,4,6,7].map (options 5 4) := by rfl


theorem t5_447part0 : t5_447jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_447frontier : t5_447root.frontier 0=t5_447jobs := by rfl
theorem t5_447all : t5_447jobs.all (Job.check tree)=true := by
  simp only [t5_447jobs,List.all_append,List.all_nil,t5_447part0,Bool.and_self]
theorem t5_447checked : Checked tree [1,4,4,6,7] := by
  refine ⟨plan4539,valid4539,t5_447choices,?_⟩
  exact check_of_frontier tree 0 t5_447root t5_447jobs t5_447frontier t5_447all
theorem t5_448choices : plan4540.choices=[1,4,4,7,7].map (options 5 4) := by rfl


theorem t5_448part0 : t5_448jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_448frontier : t5_448root.frontier 0=t5_448jobs := by rfl
theorem t5_448all : t5_448jobs.all (Job.check tree)=true := by
  simp only [t5_448jobs,List.all_append,List.all_nil,t5_448part0,Bool.and_self]
theorem t5_448checked : Checked tree [1,4,4,7,7] := by
  refine ⟨plan4540,valid4540,t5_448choices,?_⟩
  exact check_of_frontier tree 0 t5_448root t5_448jobs t5_448frontier t5_448all
theorem t5_449choices : plan4541.choices=[1,4,4,10,7].map (options 5 4) := by rfl


theorem t5_449part0 : t5_449jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_449frontier : t5_449root.frontier 0=t5_449jobs := by rfl
theorem t5_449all : t5_449jobs.all (Job.check tree)=true := by
  simp only [t5_449jobs,List.all_append,List.all_nil,t5_449part0,Bool.and_self]
theorem t5_449checked : Checked tree [1,4,4,10,7] := by
  refine ⟨plan4541,valid4541,t5_449choices,?_⟩
  exact check_of_frontier tree 0 t5_449root t5_449jobs t5_449frontier t5_449all
theorem t5_450choices : plan3878.choices=[1,4,5,3,3].map (options 5 2) := by rfl


theorem t5_450part0 : t5_450jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_450frontier : t5_450root.frontier 0=t5_450jobs := by rfl
theorem t5_450all : t5_450jobs.all (Job.check tree)=true := by
  simp only [t5_450jobs,List.all_append,List.all_nil,t5_450part0,Bool.and_self]
theorem t5_450checked : Checked tree [1,4,5,3,3] := by
  refine ⟨plan3878,valid3878,t5_450choices,?_⟩
  exact check_of_frontier tree 0 t5_450root t5_450jobs t5_450frontier t5_450all
theorem t5_451choices : plan4181.choices=[1,4,5,3,6].map (options 5 3) := by rfl


theorem t5_451part0 : t5_451jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_451frontier : t5_451root.frontier 0=t5_451jobs := by rfl
theorem t5_451all : t5_451jobs.all (Job.check tree)=true := by
  simp only [t5_451jobs,List.all_append,List.all_nil,t5_451part0,Bool.and_self]
theorem t5_451checked : Checked tree [1,4,5,3,6] := by
  refine ⟨plan4181,valid4181,t5_451choices,?_⟩
  exact check_of_frontier tree 0 t5_451root t5_451jobs t5_451frontier t5_451all
theorem t5_452choices : plan4182.choices=[1,4,5,3,7].map (options 5 3) := by rfl


theorem t5_452part0 : t5_452jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_452frontier : t5_452root.frontier 0=t5_452jobs := by rfl
theorem t5_452all : t5_452jobs.all (Job.check tree)=true := by
  simp only [t5_452jobs,List.all_append,List.all_nil,t5_452part0,Bool.and_self]
theorem t5_452checked : Checked tree [1,4,5,3,7] := by
  refine ⟨plan4182,valid4182,t5_452choices,?_⟩
  exact check_of_frontier tree 0 t5_452root t5_452jobs t5_452frontier t5_452all
theorem t5_453choices : plan4183.choices=[1,4,5,3,10].map (options 5 3) := by rfl


theorem t5_453part0 : t5_453jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_453frontier : t5_453root.frontier 0=t5_453jobs := by rfl
theorem t5_453all : t5_453jobs.all (Job.check tree)=true := by
  simp only [t5_453jobs,List.all_append,List.all_nil,t5_453part0,Bool.and_self]
theorem t5_453checked : Checked tree [1,4,5,3,10] := by
  refine ⟨plan4183,valid4183,t5_453choices,?_⟩
  exact check_of_frontier tree 0 t5_453root t5_453jobs t5_453frontier t5_453all
theorem t5_454choices : plan4542.choices=[1,4,5,5,7].map (options 5 4) := by rfl


theorem t5_454part0 : t5_454jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_454frontier : t5_454root.frontier 0=t5_454jobs := by rfl
theorem t5_454all : t5_454jobs.all (Job.check tree)=true := by
  simp only [t5_454jobs,List.all_append,List.all_nil,t5_454part0,Bool.and_self]
theorem t5_454checked : Checked tree [1,4,5,5,7] := by
  refine ⟨plan4542,valid4542,t5_454choices,?_⟩
  exact check_of_frontier tree 0 t5_454root t5_454jobs t5_454frontier t5_454all
theorem t5_455choices : plan4543.choices=[1,4,5,6,6].map (options 5 4) := by rfl


theorem t5_455part0 : t5_455jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_455frontier : t5_455root.frontier 0=t5_455jobs := by rfl
theorem t5_455all : t5_455jobs.all (Job.check tree)=true := by
  simp only [t5_455jobs,List.all_append,List.all_nil,t5_455part0,Bool.and_self]
theorem t5_455checked : Checked tree [1,4,5,6,6] := by
  refine ⟨plan4543,valid4543,t5_455choices,?_⟩
  exact check_of_frontier tree 0 t5_455root t5_455jobs t5_455frontier t5_455all
theorem t5_456choices : plan4544.choices=[1,4,5,6,7].map (options 5 4) := by rfl


theorem t5_456part0 : t5_456jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_456frontier : t5_456root.frontier 0=t5_456jobs := by rfl
theorem t5_456all : t5_456jobs.all (Job.check tree)=true := by
  simp only [t5_456jobs,List.all_append,List.all_nil,t5_456part0,Bool.and_self]
theorem t5_456checked : Checked tree [1,4,5,6,7] := by
  refine ⟨plan4544,valid4544,t5_456choices,?_⟩
  exact check_of_frontier tree 0 t5_456root t5_456jobs t5_456frontier t5_456all
theorem t5_457choices : plan4545.choices=[1,4,5,6,10].map (options 5 4) := by rfl


theorem t5_457part0 : t5_457jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_457frontier : t5_457root.frontier 0=t5_457jobs := by rfl
theorem t5_457all : t5_457jobs.all (Job.check tree)=true := by
  simp only [t5_457jobs,List.all_append,List.all_nil,t5_457part0,Bool.and_self]
theorem t5_457checked : Checked tree [1,4,5,6,10] := by
  refine ⟨plan4545,valid4545,t5_457choices,?_⟩
  exact check_of_frontier tree 0 t5_457root t5_457jobs t5_457frontier t5_457all
theorem t5_458choices : plan4546.choices=[1,4,5,7,7].map (options 5 4) := by rfl


theorem t5_458part0 : t5_458jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_458frontier : t5_458root.frontier 0=t5_458jobs := by rfl
theorem t5_458all : t5_458jobs.all (Job.check tree)=true := by
  simp only [t5_458jobs,List.all_append,List.all_nil,t5_458part0,Bool.and_self]
theorem t5_458checked : Checked tree [1,4,5,7,7] := by
  refine ⟨plan4546,valid4546,t5_458choices,?_⟩
  exact check_of_frontier tree 0 t5_458root t5_458jobs t5_458frontier t5_458all
theorem t5_459choices : plan4547.choices=[1,4,5,9,7].map (options 5 4) := by rfl


theorem t5_459part0 : t5_459jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_459frontier : t5_459root.frontier 0=t5_459jobs := by rfl
theorem t5_459all : t5_459jobs.all (Job.check tree)=true := by
  simp only [t5_459jobs,List.all_append,List.all_nil,t5_459part0,Bool.and_self]
theorem t5_459checked : Checked tree [1,4,5,9,7] := by
  refine ⟨plan4547,valid4547,t5_459choices,?_⟩
  exact check_of_frontier tree 0 t5_459root t5_459jobs t5_459frontier t5_459all
theorem t5_460choices : plan4548.choices=[1,4,5,10,7].map (options 5 4) := by rfl


theorem t5_460part0 : t5_460jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_460frontier : t5_460root.frontier 0=t5_460jobs := by rfl
theorem t5_460all : t5_460jobs.all (Job.check tree)=true := by
  simp only [t5_460jobs,List.all_append,List.all_nil,t5_460part0,Bool.and_self]
theorem t5_460checked : Checked tree [1,4,5,10,7] := by
  refine ⟨plan4548,valid4548,t5_460choices,?_⟩
  exact check_of_frontier tree 0 t5_460root t5_460jobs t5_460frontier t5_460all
theorem t5_461choices : plan4549.choices=[1,4,5,10,10].map (options 5 4) := by rfl


theorem t5_461part0 : t5_461jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_461frontier : t5_461root.frontier 0=t5_461jobs := by rfl
theorem t5_461all : t5_461jobs.all (Job.check tree)=true := by
  simp only [t5_461jobs,List.all_append,List.all_nil,t5_461part0,Bool.and_self]
theorem t5_461checked : Checked tree [1,4,5,10,10] := by
  refine ⟨plan4549,valid4549,t5_461choices,?_⟩
  exact check_of_frontier tree 0 t5_461root t5_461jobs t5_461frontier t5_461all
theorem t5_462choices : plan4550.choices=[1,4,6,6,6].map (options 5 4) := by rfl


theorem t5_462part0 : t5_462jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_462frontier : t5_462root.frontier 0=t5_462jobs := by rfl
theorem t5_462all : t5_462jobs.all (Job.check tree)=true := by
  simp only [t5_462jobs,List.all_append,List.all_nil,t5_462part0,Bool.and_self]
theorem t5_462checked : Checked tree [1,4,6,6,6] := by
  refine ⟨plan4550,valid4550,t5_462choices,?_⟩
  exact check_of_frontier tree 0 t5_462root t5_462jobs t5_462frontier t5_462all
theorem t5_463choices : plan4551.choices=[1,4,6,6,7].map (options 5 4) := by rfl


theorem t5_463part0 : t5_463jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_463frontier : t5_463root.frontier 0=t5_463jobs := by rfl
theorem t5_463all : t5_463jobs.all (Job.check tree)=true := by
  simp only [t5_463jobs,List.all_append,List.all_nil,t5_463part0,Bool.and_self]
theorem t5_463checked : Checked tree [1,4,6,6,7] := by
  refine ⟨plan4551,valid4551,t5_463choices,?_⟩
  exact check_of_frontier tree 0 t5_463root t5_463jobs t5_463frontier t5_463all
theorem t5_464choices : plan4552.choices=[1,4,6,6,10].map (options 5 4) := by rfl


theorem t5_464part0 : t5_464jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_464frontier : t5_464root.frontier 0=t5_464jobs := by rfl
theorem t5_464all : t5_464jobs.all (Job.check tree)=true := by
  simp only [t5_464jobs,List.all_append,List.all_nil,t5_464part0,Bool.and_self]
theorem t5_464checked : Checked tree [1,4,6,6,10] := by
  refine ⟨plan4552,valid4552,t5_464choices,?_⟩
  exact check_of_frontier tree 0 t5_464root t5_464jobs t5_464frontier t5_464all
theorem t5_465choices : plan4553.choices=[1,4,6,7,7].map (options 5 4) := by rfl


theorem t5_465part0 : t5_465jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_465frontier : t5_465root.frontier 0=t5_465jobs := by rfl
theorem t5_465all : t5_465jobs.all (Job.check tree)=true := by
  simp only [t5_465jobs,List.all_append,List.all_nil,t5_465part0,Bool.and_self]
theorem t5_465checked : Checked tree [1,4,6,7,7] := by
  refine ⟨plan4553,valid4553,t5_465choices,?_⟩
  exact check_of_frontier tree 0 t5_465root t5_465jobs t5_465frontier t5_465all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks010 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_426checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_427checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_428checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_429checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_430checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_431checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_432checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_433checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_434checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_435checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_436checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_437checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_438checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_439checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_440checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_441checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_442checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_443checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_444checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_445checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_446checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_447checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_448checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_449checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_450checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_417checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_451checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_452checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_453checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_454checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_455checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_456checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_457checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_458checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_459checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_460checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_461checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_462checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_463checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_464checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_418checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_465checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_419checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_420checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_421checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_422checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_423checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_424checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_425checked⟩
