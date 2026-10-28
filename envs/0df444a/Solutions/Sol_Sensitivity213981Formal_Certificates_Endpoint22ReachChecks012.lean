-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks012
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:56:19.388568+00:00
-- url     : https://prove2.me/submissions/31b65b53-cf24-460b-8a34-5a41391bce4a

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks012
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans047
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

theorem valid100 : plan100.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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

theorem valid498 : plan498.Valid := valid_step _ _ _ valid100 (by decide +kernel)



theorem valid500 : plan500.Valid := valid_step _ _ _ valid103 (by decide +kernel)





theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)



















theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)



theorem valid519 : plan519.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid520 : plan520.Valid := valid_step _ _ _ valid109 (by decide +kernel)



theorem valid522 : plan522.Valid := valid_step _ _ _ valid111 (by decide +kernel)

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





























theorem valid1315 : plan1315.Valid := valid_step _ _ _ valid462 (by decide +kernel)



















theorem valid1325 : plan1325.Valid := valid_step _ _ _ valid491 (by decide +kernel)



theorem valid1327 : plan1327.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1328 : plan1328.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1329 : plan1329.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1330 : plan1330.Valid := valid_step _ _ _ valid497 (by decide +kernel)



theorem valid1332 : plan1332.Valid := valid_step _ _ _ valid500 (by decide +kernel)



theorem valid1334 : plan1334.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1335 : plan1335.Valid := valid_step _ _ _ valid504 (by decide +kernel)


















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























































































































theorem valid2556 : plan2556.Valid := valid_step _ _ _ valid1258 (by decide +kernel)

theorem valid2557 : plan2557.Valid := valid_step _ _ _ valid1264 (by decide +kernel)






































































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





















































































































































theorem valid3723 : plan3723.Valid := valid_step _ _ _ valid2556 (by decide +kernel)

theorem valid3724 : plan3724.Valid := valid_step _ _ _ valid2557 (by decide +kernel)








































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











































































theorem valid1382 : plan1382.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1383 : plan1383.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1384 : plan1384.Valid := valid_step _ _ _ valid487 (by decide +kernel)









theorem valid1389 : plan1389.Valid := valid_step _ _ _ valid498 (by decide +kernel)































































































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























































































































theorem valid2652 : plan2652.Valid := valid_step _ _ _ valid1315 (by decide +kernel)

theorem valid2653 : plan2653.Valid := valid_step _ _ _ valid1274 (by decide +kernel)



theorem valid2655 : plan2655.Valid := valid_step _ _ _ valid1277 (by decide +kernel)

theorem valid2656 : plan2656.Valid := valid_step _ _ _ valid1278 (by decide +kernel)

theorem valid2657 : plan2657.Valid := valid_step _ _ _ valid1279 (by decide +kernel)



theorem valid2659 : plan2659.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2660 : plan2660.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2661 : plan2661.Valid := valid_step _ _ _ valid1300 (by decide +kernel)






















































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

















































































theorem valid2825 : plan2825.Valid := valid_step _ _ _ valid1382 (by decide +kernel)

theorem valid2826 : plan2826.Valid := valid_step _ _ _ valid1383 (by decide +kernel)

theorem valid2827 : plan2827.Valid := valid_step _ _ _ valid1384 (by decide +kernel)

theorem valid2828 : plan2828.Valid := valid_step _ _ _ valid1389 (by decide +kernel)









theorem valid2833 : plan2833.Valid := valid_step _ _ _ valid1325 (by decide +kernel)

theorem valid2834 : plan2834.Valid := valid_step _ _ _ valid1327 (by decide +kernel)

theorem valid2835 : plan2835.Valid := valid_step _ _ _ valid1328 (by decide +kernel)

theorem valid2836 : plan2836.Valid := valid_step _ _ _ valid1329 (by decide +kernel)

theorem valid2837 : plan2837.Valid := valid_step _ _ _ valid1330 (by decide +kernel)

theorem valid2838 : plan2838.Valid := valid_step _ _ _ valid1332 (by decide +kernel)

theorem valid2839 : plan2839.Valid := valid_step _ _ _ valid1334 (by decide +kernel)

theorem valid2840 : plan2840.Valid := valid_step _ _ _ valid1335 (by decide +kernel)
















































































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















theorem valid1451 : plan1451.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1452 : plan1452.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1453 : plan1453.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1454 : plan1454.Valid := valid_step _ _ _ valid517 (by decide +kernel)



theorem valid1456 : plan1456.Valid := valid_step _ _ _ valid519 (by decide +kernel)

theorem valid1457 : plan1457.Valid := valid_step _ _ _ valid520 (by decide +kernel)



theorem valid1459 : plan1459.Valid := valid_step _ _ _ valid522 (by decide +kernel)

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





































theorem valid2995 : plan2995.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid2996 : plan2996.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid2997 : plan2997.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid2998 : plan2998.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid2999 : plan2999.Valid := valid_step _ _ _ valid1443 (by decide +kernel)







theorem valid3003 : plan3003.Valid := valid_step _ _ _ valid1451 (by decide +kernel)

theorem valid3004 : plan3004.Valid := valid_step _ _ _ valid1452 (by decide +kernel)

theorem valid3005 : plan3005.Valid := valid_step _ _ _ valid1453 (by decide +kernel)

theorem valid3006 : plan3006.Valid := valid_step _ _ _ valid1454 (by decide +kernel)



theorem valid3008 : plan3008.Valid := valid_step _ _ _ valid1456 (by decide +kernel)

theorem valid3009 : plan3009.Valid := valid_step _ _ _ valid1457 (by decide +kernel)



theorem valid3011 : plan3011.Valid := valid_step _ _ _ valid1459 (by decide +kernel)

theorem valid3012 : plan3012.Valid := valid_step _ _ _ valid1460 (by decide +kernel)

theorem valid3013 : plan3013.Valid := valid_step _ _ _ valid1461 (by decide +kernel)

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















































































































































theorem valid4584 : plan4584.Valid := valid_step _ _ _ valid2995 (by decide +kernel)

theorem valid4585 : plan4585.Valid := valid_step _ _ _ valid2996 (by decide +kernel)

theorem valid4586 : plan4586.Valid := valid_step _ _ _ valid2997 (by decide +kernel)

theorem valid4587 : plan4587.Valid := valid_step _ _ _ valid2998 (by decide +kernel)

theorem valid4588 : plan4588.Valid := valid_step _ _ _ valid2999 (by decide +kernel)

theorem valid4589 : plan4589.Valid := valid_step _ _ _ valid3003 (by decide +kernel)

theorem valid4590 : plan4590.Valid := valid_step _ _ _ valid3004 (by decide +kernel)

theorem valid4591 : plan4591.Valid := valid_step _ _ _ valid3005 (by decide +kernel)

theorem valid4592 : plan4592.Valid := valid_step _ _ _ valid3006 (by decide +kernel)

theorem valid4593 : plan4593.Valid := valid_step _ _ _ valid3008 (by decide +kernel)

theorem valid4594 : plan4594.Valid := valid_step _ _ _ valid3009 (by decide +kernel)

theorem valid4595 : plan4595.Valid := valid_step _ _ _ valid3011 (by decide +kernel)

theorem valid4596 : plan4596.Valid := valid_step _ _ _ valid3012 (by decide +kernel)

theorem valid4597 : plan4597.Valid := valid_step _ _ _ valid3013 (by decide +kernel)

theorem valid4598 : plan4598.Valid := valid_step _ _ _ valid3014 (by decide +kernel)

theorem valid4599 : plan4599.Valid := valid_step _ _ _ valid3015 (by decide +kernel)

theorem valid4600 : plan4600.Valid := valid_step _ _ _ valid3016 (by decide +kernel)

theorem valid4601 : plan4601.Valid := valid_step _ _ _ valid3017 (by decide +kernel)

theorem valid4602 : plan4602.Valid := valid_step _ _ _ valid3018 (by decide +kernel)

theorem valid4603 : plan4603.Valid := valid_step _ _ _ valid3019 (by decide +kernel)

theorem valid4604 : plan4604.Valid := valid_step _ _ _ valid3020 (by decide +kernel)

theorem valid4605 : plan4605.Valid := valid_step _ _ _ valid3021 (by decide +kernel)

theorem valid4606 : plan4606.Valid := valid_step _ _ _ valid3022 (by decide +kernel)

theorem valid4607 : plan4607.Valid := valid_step _ _ _ valid3023 (by decide +kernel)

theorem valid4608 : plan4608.Valid := valid_step _ _ _ valid3024 (by decide +kernel)
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























































































theorem valid3884 : plan3884.Valid := valid_step _ _ _ valid2652 (by decide +kernel)

theorem valid3885 : plan3885.Valid := valid_step _ _ _ valid2653 (by decide +kernel)

theorem valid3886 : plan3886.Valid := valid_step _ _ _ valid2655 (by decide +kernel)

theorem valid3887 : plan3887.Valid := valid_step _ _ _ valid2656 (by decide +kernel)

theorem valid3888 : plan3888.Valid := valid_step _ _ _ valid2657 (by decide +kernel)

theorem valid3889 : plan3889.Valid := valid_step _ _ _ valid2659 (by decide +kernel)

theorem valid3890 : plan3890.Valid := valid_step _ _ _ valid2660 (by decide +kernel)

theorem valid3891 : plan3891.Valid := valid_step _ _ _ valid2661 (by decide +kernel)


























































































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













































































































































theorem valid4199 : plan4199.Valid := valid_step _ _ _ valid2825 (by decide +kernel)

theorem valid4200 : plan4200.Valid := valid_step _ _ _ valid2826 (by decide +kernel)

theorem valid4201 : plan4201.Valid := valid_step _ _ _ valid2827 (by decide +kernel)

theorem valid4202 : plan4202.Valid := valid_step _ _ _ valid2828 (by decide +kernel)

theorem valid4203 : plan4203.Valid := valid_step _ _ _ valid2833 (by decide +kernel)

theorem valid4204 : plan4204.Valid := valid_step _ _ _ valid2834 (by decide +kernel)

theorem valid4205 : plan4205.Valid := valid_step _ _ _ valid2835 (by decide +kernel)

theorem valid4206 : plan4206.Valid := valid_step _ _ _ valid2836 (by decide +kernel)

theorem valid4207 : plan4207.Valid := valid_step _ _ _ valid2837 (by decide +kernel)

theorem valid4208 : plan4208.Valid := valid_step _ _ _ valid2838 (by decide +kernel)

theorem valid4209 : plan4209.Valid := valid_step _ _ _ valid2839 (by decide +kernel)

theorem valid4210 : plan4210.Valid := valid_step _ _ _ valid2840 (by decide +kernel)




























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

theorem valid4609 : plan4609.Valid := valid_step _ _ _ valid3025 (by decide +kernel)

theorem valid4610 : plan4610.Valid := valid_step _ _ _ valid3026 (by decide +kernel)

theorem valid4611 : plan4611.Valid := valid_step _ _ _ valid3027 (by decide +kernel)


























































































































































































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
theorem t5_517choices : plan4584.choices=[1,5,6,6,10].map (options 5 4) := by rfl


theorem t5_517part0 : t5_517jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_517frontier : t5_517root.frontier 0=t5_517jobs := by rfl
theorem t5_517all : t5_517jobs.all (Job.check tree)=true := by
  simp only [t5_517jobs,List.all_append,List.all_nil,t5_517part0,Bool.and_self]
theorem t5_517checked : Checked tree [1,5,6,6,10] := by
  refine ⟨plan4584,valid4584,t5_517choices,?_⟩
  exact check_of_frontier tree 0 t5_517root t5_517jobs t5_517frontier t5_517all
theorem t5_518choices : plan4585.choices=[1,5,6,7,7].map (options 5 4) := by rfl


theorem t5_518part0 : t5_518jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_518frontier : t5_518root.frontier 0=t5_518jobs := by rfl
theorem t5_518all : t5_518jobs.all (Job.check tree)=true := by
  simp only [t5_518jobs,List.all_append,List.all_nil,t5_518part0,Bool.and_self]
theorem t5_518checked : Checked tree [1,5,6,7,7] := by
  refine ⟨plan4585,valid4585,t5_518choices,?_⟩
  exact check_of_frontier tree 0 t5_518root t5_518jobs t5_518frontier t5_518all
theorem t5_519choices : plan4586.choices=[1,5,6,10,7].map (options 5 4) := by rfl


theorem t5_519part0 : t5_519jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_519frontier : t5_519root.frontier 0=t5_519jobs := by rfl
theorem t5_519all : t5_519jobs.all (Job.check tree)=true := by
  simp only [t5_519jobs,List.all_append,List.all_nil,t5_519part0,Bool.and_self]
theorem t5_519checked : Checked tree [1,5,6,10,7] := by
  refine ⟨plan4586,valid4586,t5_519choices,?_⟩
  exact check_of_frontier tree 0 t5_519root t5_519jobs t5_519frontier t5_519all
theorem t5_520choices : plan4587.choices=[1,5,6,10,10].map (options 5 4) := by rfl


theorem t5_520part0 : t5_520jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_520frontier : t5_520root.frontier 0=t5_520jobs := by rfl
theorem t5_520all : t5_520jobs.all (Job.check tree)=true := by
  simp only [t5_520jobs,List.all_append,List.all_nil,t5_520part0,Bool.and_self]
theorem t5_520checked : Checked tree [1,5,6,10,10] := by
  refine ⟨plan4587,valid4587,t5_520choices,?_⟩
  exact check_of_frontier tree 0 t5_520root t5_520jobs t5_520frontier t5_520all
theorem t5_521choices : plan4588.choices=[1,5,7,7,7].map (options 5 4) := by rfl


theorem t5_521part0 : t5_521jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_521frontier : t5_521root.frontier 0=t5_521jobs := by rfl
theorem t5_521all : t5_521jobs.all (Job.check tree)=true := by
  simp only [t5_521jobs,List.all_append,List.all_nil,t5_521part0,Bool.and_self]
theorem t5_521checked : Checked tree [1,5,7,7,7] := by
  refine ⟨plan4588,valid4588,t5_521choices,?_⟩
  exact check_of_frontier tree 0 t5_521root t5_521jobs t5_521frontier t5_521all
theorem t5_522choices : plan3884.choices=[1,5,9,3,3].map (options 5 2) := by rfl


theorem t5_522part0 : t5_522jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_522frontier : t5_522root.frontier 0=t5_522jobs := by rfl
theorem t5_522all : t5_522jobs.all (Job.check tree)=true := by
  simp only [t5_522jobs,List.all_append,List.all_nil,t5_522part0,Bool.and_self]
theorem t5_522checked : Checked tree [1,5,9,3,3] := by
  refine ⟨plan3884,valid3884,t5_522choices,?_⟩
  exact check_of_frontier tree 0 t5_522root t5_522jobs t5_522frontier t5_522all
theorem t5_523choices : plan4199.choices=[1,5,9,3,6].map (options 5 3) := by rfl


theorem t5_523part0 : t5_523jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_523frontier : t5_523root.frontier 0=t5_523jobs := by rfl
theorem t5_523all : t5_523jobs.all (Job.check tree)=true := by
  simp only [t5_523jobs,List.all_append,List.all_nil,t5_523part0,Bool.and_self]
theorem t5_523checked : Checked tree [1,5,9,3,6] := by
  refine ⟨plan4199,valid4199,t5_523choices,?_⟩
  exact check_of_frontier tree 0 t5_523root t5_523jobs t5_523frontier t5_523all
theorem t5_524choices : plan4200.choices=[1,5,9,3,7].map (options 5 3) := by rfl


theorem t5_524part0 : t5_524jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_524part1 : t5_524jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_524frontier : t5_524root.frontier 1=t5_524jobs := by rfl
theorem t5_524all : t5_524jobs.all (Job.check tree)=true := by
  simp only [t5_524jobs,List.all_append,List.all_nil,t5_524part0,t5_524part1,Bool.and_self]
theorem t5_524checked : Checked tree [1,5,9,3,7] := by
  refine ⟨plan4200,valid4200,t5_524choices,?_⟩
  exact check_of_frontier tree 1 t5_524root t5_524jobs t5_524frontier t5_524all
theorem t5_525choices : plan4201.choices=[1,5,9,3,10].map (options 5 3) := by rfl


theorem t5_525part0 : t5_525jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_525frontier : t5_525root.frontier 0=t5_525jobs := by rfl
theorem t5_525all : t5_525jobs.all (Job.check tree)=true := by
  simp only [t5_525jobs,List.all_append,List.all_nil,t5_525part0,Bool.and_self]
theorem t5_525checked : Checked tree [1,5,9,3,10] := by
  refine ⟨plan4201,valid4201,t5_525choices,?_⟩
  exact check_of_frontier tree 0 t5_525root t5_525jobs t5_525frontier t5_525all
theorem t5_526choices : plan4589.choices=[1,5,9,6,6].map (options 5 4) := by rfl


theorem t5_526part0 : t5_526jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_526frontier : t5_526root.frontier 0=t5_526jobs := by rfl
theorem t5_526all : t5_526jobs.all (Job.check tree)=true := by
  simp only [t5_526jobs,List.all_append,List.all_nil,t5_526part0,Bool.and_self]
theorem t5_526checked : Checked tree [1,5,9,6,6] := by
  refine ⟨plan4589,valid4589,t5_526choices,?_⟩
  exact check_of_frontier tree 0 t5_526root t5_526jobs t5_526frontier t5_526all
theorem t5_527choices : plan4590.choices=[1,5,9,6,7].map (options 5 4) := by rfl


theorem t5_527part0 : t5_527jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_527frontier : t5_527root.frontier 0=t5_527jobs := by rfl
theorem t5_527all : t5_527jobs.all (Job.check tree)=true := by
  simp only [t5_527jobs,List.all_append,List.all_nil,t5_527part0,Bool.and_self]
theorem t5_527checked : Checked tree [1,5,9,6,7] := by
  refine ⟨plan4590,valid4590,t5_527choices,?_⟩
  exact check_of_frontier tree 0 t5_527root t5_527jobs t5_527frontier t5_527all
theorem t5_528choices : plan4591.choices=[1,5,9,6,10].map (options 5 4) := by rfl


theorem t5_528part0 : t5_528jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_528frontier : t5_528root.frontier 0=t5_528jobs := by rfl
theorem t5_528all : t5_528jobs.all (Job.check tree)=true := by
  simp only [t5_528jobs,List.all_append,List.all_nil,t5_528part0,Bool.and_self]
theorem t5_528checked : Checked tree [1,5,9,6,10] := by
  refine ⟨plan4591,valid4591,t5_528choices,?_⟩
  exact check_of_frontier tree 0 t5_528root t5_528jobs t5_528frontier t5_528all
theorem t5_529choices : plan4592.choices=[1,5,9,7,7].map (options 5 4) := by rfl


theorem t5_529part0 : t5_529jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_529frontier : t5_529root.frontier 0=t5_529jobs := by rfl
theorem t5_529all : t5_529jobs.all (Job.check tree)=true := by
  simp only [t5_529jobs,List.all_append,List.all_nil,t5_529part0,Bool.and_self]
theorem t5_529checked : Checked tree [1,5,9,7,7] := by
  refine ⟨plan4592,valid4592,t5_529choices,?_⟩
  exact check_of_frontier tree 0 t5_529root t5_529jobs t5_529frontier t5_529all
theorem t5_530choices : plan4202.choices=[1,5,9,9,3].map (options 5 3) := by rfl


theorem t5_530part0 : t5_530jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_530frontier : t5_530root.frontier 0=t5_530jobs := by rfl
theorem t5_530all : t5_530jobs.all (Job.check tree)=true := by
  simp only [t5_530jobs,List.all_append,List.all_nil,t5_530part0,Bool.and_self]
theorem t5_530checked : Checked tree [1,5,9,9,3] := by
  refine ⟨plan4202,valid4202,t5_530choices,?_⟩
  exact check_of_frontier tree 0 t5_530root t5_530jobs t5_530frontier t5_530all
theorem t5_531choices : plan4593.choices=[1,5,9,9,6].map (options 5 4) := by rfl


theorem t5_531part0 : t5_531jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_531frontier : t5_531root.frontier 0=t5_531jobs := by rfl
theorem t5_531all : t5_531jobs.all (Job.check tree)=true := by
  simp only [t5_531jobs,List.all_append,List.all_nil,t5_531part0,Bool.and_self]
theorem t5_531checked : Checked tree [1,5,9,9,6] := by
  refine ⟨plan4593,valid4593,t5_531choices,?_⟩
  exact check_of_frontier tree 0 t5_531root t5_531jobs t5_531frontier t5_531all
theorem t5_532choices : plan4594.choices=[1,5,9,9,7].map (options 5 4) := by rfl


theorem t5_532part0 : t5_532jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_532frontier : t5_532root.frontier 0=t5_532jobs := by rfl
theorem t5_532all : t5_532jobs.all (Job.check tree)=true := by
  simp only [t5_532jobs,List.all_append,List.all_nil,t5_532part0,Bool.and_self]
theorem t5_532checked : Checked tree [1,5,9,9,7] := by
  refine ⟨plan4594,valid4594,t5_532choices,?_⟩
  exact check_of_frontier tree 0 t5_532root t5_532jobs t5_532frontier t5_532all
theorem t5_533choices : plan4595.choices=[1,5,9,9,10].map (options 5 4) := by rfl


theorem t5_533part0 : t5_533jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_533frontier : t5_533root.frontier 0=t5_533jobs := by rfl
theorem t5_533all : t5_533jobs.all (Job.check tree)=true := by
  simp only [t5_533jobs,List.all_append,List.all_nil,t5_533part0,Bool.and_self]
theorem t5_533checked : Checked tree [1,5,9,9,10] := by
  refine ⟨plan4595,valid4595,t5_533choices,?_⟩
  exact check_of_frontier tree 0 t5_533root t5_533jobs t5_533frontier t5_533all
theorem t5_534choices : plan4596.choices=[1,5,9,10,7].map (options 5 4) := by rfl


theorem t5_534part0 : t5_534jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_534frontier : t5_534root.frontier 0=t5_534jobs := by rfl
theorem t5_534all : t5_534jobs.all (Job.check tree)=true := by
  simp only [t5_534jobs,List.all_append,List.all_nil,t5_534part0,Bool.and_self]
theorem t5_534checked : Checked tree [1,5,9,10,7] := by
  refine ⟨plan4596,valid4596,t5_534choices,?_⟩
  exact check_of_frontier tree 0 t5_534root t5_534jobs t5_534frontier t5_534all
theorem t5_535choices : plan4597.choices=[1,5,9,10,10].map (options 5 4) := by rfl


theorem t5_535part0 : t5_535jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_535frontier : t5_535root.frontier 0=t5_535jobs := by rfl
theorem t5_535all : t5_535jobs.all (Job.check tree)=true := by
  simp only [t5_535jobs,List.all_append,List.all_nil,t5_535part0,Bool.and_self]
theorem t5_535checked : Checked tree [1,5,9,10,10] := by
  refine ⟨plan4597,valid4597,t5_535choices,?_⟩
  exact check_of_frontier tree 0 t5_535root t5_535jobs t5_535frontier t5_535all
theorem t5_536choices : plan4598.choices=[1,5,10,7,7].map (options 5 4) := by rfl


theorem t5_536part0 : t5_536jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_536frontier : t5_536root.frontier 0=t5_536jobs := by rfl
theorem t5_536all : t5_536jobs.all (Job.check tree)=true := by
  simp only [t5_536jobs,List.all_append,List.all_nil,t5_536part0,Bool.and_self]
theorem t5_536checked : Checked tree [1,5,10,7,7] := by
  refine ⟨plan4598,valid4598,t5_536choices,?_⟩
  exact check_of_frontier tree 0 t5_536root t5_536jobs t5_536frontier t5_536all
theorem t5_537choices : plan4599.choices=[1,5,10,10,7].map (options 5 4) := by rfl


theorem t5_537part0 : t5_537jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_537frontier : t5_537root.frontier 0=t5_537jobs := by rfl
theorem t5_537all : t5_537jobs.all (Job.check tree)=true := by
  simp only [t5_537jobs,List.all_append,List.all_nil,t5_537part0,Bool.and_self]
theorem t5_537checked : Checked tree [1,5,10,10,7] := by
  refine ⟨plan4599,valid4599,t5_537choices,?_⟩
  exact check_of_frontier tree 0 t5_537root t5_537jobs t5_537frontier t5_537all
theorem t5_538choices : plan4600.choices=[1,5,10,10,10].map (options 5 4) := by rfl


theorem t5_538part0 : t5_538jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_538frontier : t5_538root.frontier 0=t5_538jobs := by rfl
theorem t5_538all : t5_538jobs.all (Job.check tree)=true := by
  simp only [t5_538jobs,List.all_append,List.all_nil,t5_538part0,Bool.and_self]
theorem t5_538checked : Checked tree [1,5,10,10,10] := by
  refine ⟨plan4600,valid4600,t5_538choices,?_⟩
  exact check_of_frontier tree 0 t5_538root t5_538jobs t5_538frontier t5_538all
theorem t5_539choices : plan4601.choices=[1,6,6,6,6].map (options 5 4) := by rfl


theorem t5_539part0 : t5_539jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_539frontier : t5_539root.frontier 0=t5_539jobs := by rfl
theorem t5_539all : t5_539jobs.all (Job.check tree)=true := by
  simp only [t5_539jobs,List.all_append,List.all_nil,t5_539part0,Bool.and_self]
theorem t5_539checked : Checked tree [1,6,6,6,6] := by
  refine ⟨plan4601,valid4601,t5_539choices,?_⟩
  exact check_of_frontier tree 0 t5_539root t5_539jobs t5_539frontier t5_539all
theorem t5_540choices : plan4602.choices=[1,6,6,6,7].map (options 5 4) := by rfl


theorem t5_540part0 : t5_540jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_540frontier : t5_540root.frontier 0=t5_540jobs := by rfl
theorem t5_540all : t5_540jobs.all (Job.check tree)=true := by
  simp only [t5_540jobs,List.all_append,List.all_nil,t5_540part0,Bool.and_self]
theorem t5_540checked : Checked tree [1,6,6,6,7] := by
  refine ⟨plan4602,valid4602,t5_540choices,?_⟩
  exact check_of_frontier tree 0 t5_540root t5_540jobs t5_540frontier t5_540all
theorem t5_541choices : plan4603.choices=[1,6,6,6,10].map (options 5 4) := by rfl


theorem t5_541part0 : t5_541jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_541frontier : t5_541root.frontier 0=t5_541jobs := by rfl
theorem t5_541all : t5_541jobs.all (Job.check tree)=true := by
  simp only [t5_541jobs,List.all_append,List.all_nil,t5_541part0,Bool.and_self]
theorem t5_541checked : Checked tree [1,6,6,6,10] := by
  refine ⟨plan4603,valid4603,t5_541choices,?_⟩
  exact check_of_frontier tree 0 t5_541root t5_541jobs t5_541frontier t5_541all
theorem t5_542choices : plan4604.choices=[1,6,6,7,7].map (options 5 4) := by rfl


theorem t5_542part0 : t5_542jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_542frontier : t5_542root.frontier 0=t5_542jobs := by rfl
theorem t5_542all : t5_542jobs.all (Job.check tree)=true := by
  simp only [t5_542jobs,List.all_append,List.all_nil,t5_542part0,Bool.and_self]
theorem t5_542checked : Checked tree [1,6,6,7,7] := by
  refine ⟨plan4604,valid4604,t5_542choices,?_⟩
  exact check_of_frontier tree 0 t5_542root t5_542jobs t5_542frontier t5_542all
theorem t5_543choices : plan4605.choices=[1,6,6,10,7].map (options 5 4) := by rfl


theorem t5_543part0 : t5_543jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_543frontier : t5_543root.frontier 0=t5_543jobs := by rfl
theorem t5_543all : t5_543jobs.all (Job.check tree)=true := by
  simp only [t5_543jobs,List.all_append,List.all_nil,t5_543part0,Bool.and_self]
theorem t5_543checked : Checked tree [1,6,6,10,7] := by
  refine ⟨plan4605,valid4605,t5_543choices,?_⟩
  exact check_of_frontier tree 0 t5_543root t5_543jobs t5_543frontier t5_543all
theorem t5_544choices : plan4606.choices=[1,6,6,10,10].map (options 5 4) := by rfl


theorem t5_544part0 : t5_544jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_544frontier : t5_544root.frontier 0=t5_544jobs := by rfl
theorem t5_544all : t5_544jobs.all (Job.check tree)=true := by
  simp only [t5_544jobs,List.all_append,List.all_nil,t5_544part0,Bool.and_self]
theorem t5_544checked : Checked tree [1,6,6,10,10] := by
  refine ⟨plan4606,valid4606,t5_544choices,?_⟩
  exact check_of_frontier tree 0 t5_544root t5_544jobs t5_544frontier t5_544all
theorem t5_545choices : plan4607.choices=[1,6,7,7,7].map (options 5 4) := by rfl


theorem t5_545part0 : t5_545jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_545frontier : t5_545root.frontier 0=t5_545jobs := by rfl
theorem t5_545all : t5_545jobs.all (Job.check tree)=true := by
  simp only [t5_545jobs,List.all_append,List.all_nil,t5_545part0,Bool.and_self]
theorem t5_545checked : Checked tree [1,6,7,7,7] := by
  refine ⟨plan4607,valid4607,t5_545choices,?_⟩
  exact check_of_frontier tree 0 t5_545root t5_545jobs t5_545frontier t5_545all
theorem t5_546choices : plan4608.choices=[1,6,10,7,7].map (options 5 4) := by rfl


theorem t5_546part0 : t5_546jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_546frontier : t5_546root.frontier 0=t5_546jobs := by rfl
theorem t5_546all : t5_546jobs.all (Job.check tree)=true := by
  simp only [t5_546jobs,List.all_append,List.all_nil,t5_546part0,Bool.and_self]
theorem t5_546checked : Checked tree [1,6,10,7,7] := by
  refine ⟨plan4608,valid4608,t5_546choices,?_⟩
  exact check_of_frontier tree 0 t5_546root t5_546jobs t5_546frontier t5_546all
theorem t5_547choices : plan4609.choices=[1,6,10,10,7].map (options 5 4) := by rfl


theorem t5_547part0 : t5_547jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_547frontier : t5_547root.frontier 0=t5_547jobs := by rfl
theorem t5_547all : t5_547jobs.all (Job.check tree)=true := by
  simp only [t5_547jobs,List.all_append,List.all_nil,t5_547part0,Bool.and_self]
theorem t5_547checked : Checked tree [1,6,10,10,7] := by
  refine ⟨plan4609,valid4609,t5_547choices,?_⟩
  exact check_of_frontier tree 0 t5_547root t5_547jobs t5_547frontier t5_547all
theorem t5_548choices : plan4610.choices=[1,6,10,10,10].map (options 5 4) := by rfl


theorem t5_548part0 : t5_548jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_548frontier : t5_548root.frontier 0=t5_548jobs := by rfl
theorem t5_548all : t5_548jobs.all (Job.check tree)=true := by
  simp only [t5_548jobs,List.all_append,List.all_nil,t5_548part0,Bool.and_self]
theorem t5_548checked : Checked tree [1,6,10,10,10] := by
  refine ⟨plan4610,valid4610,t5_548choices,?_⟩
  exact check_of_frontier tree 0 t5_548root t5_548jobs t5_548frontier t5_548all
theorem t5_549choices : plan4611.choices=[1,7,7,7,7].map (options 5 4) := by rfl


theorem t5_549part0 : t5_549jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_549frontier : t5_549root.frontier 0=t5_549jobs := by rfl
theorem t5_549all : t5_549jobs.all (Job.check tree)=true := by
  simp only [t5_549jobs,List.all_append,List.all_nil,t5_549part0,Bool.and_self]
theorem t5_549checked : Checked tree [1,7,7,7,7] := by
  refine ⟨plan4611,valid4611,t5_549choices,?_⟩
  exact check_of_frontier tree 0 t5_549root t5_549jobs t5_549frontier t5_549all
theorem t5_550choices : plan3885.choices=[1,8,2,2,7].map (options 5 2) := by rfl


theorem t5_550part0 : t5_550jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_550frontier : t5_550root.frontier 0=t5_550jobs := by rfl
theorem t5_550all : t5_550jobs.all (Job.check tree)=true := by
  simp only [t5_550jobs,List.all_append,List.all_nil,t5_550part0,Bool.and_self]
theorem t5_550checked : Checked tree [1,8,2,2,7] := by
  refine ⟨plan3885,valid3885,t5_550choices,?_⟩
  exact check_of_frontier tree 0 t5_550root t5_550jobs t5_550frontier t5_550all
theorem t5_551choices : plan3723.choices=[1,8,2,3,3].map (options 5 1) := by rfl


theorem t5_551part0 : t5_551jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_551frontier : t5_551root.frontier 0=t5_551jobs := by rfl
theorem t5_551all : t5_551jobs.all (Job.check tree)=true := by
  simp only [t5_551jobs,List.all_append,List.all_nil,t5_551part0,Bool.and_self]
theorem t5_551checked : Checked tree [1,8,2,3,3] := by
  refine ⟨plan3723,valid3723,t5_551choices,?_⟩
  exact check_of_frontier tree 0 t5_551root t5_551jobs t5_551frontier t5_551all
theorem t5_552choices : plan3886.choices=[1,8,2,3,6].map (options 5 2) := by rfl


theorem t5_552part0 : t5_552jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_552frontier : t5_552root.frontier 0=t5_552jobs := by rfl
theorem t5_552all : t5_552jobs.all (Job.check tree)=true := by
  simp only [t5_552jobs,List.all_append,List.all_nil,t5_552part0,Bool.and_self]
theorem t5_552checked : Checked tree [1,8,2,3,6] := by
  refine ⟨plan3886,valid3886,t5_552choices,?_⟩
  exact check_of_frontier tree 0 t5_552root t5_552jobs t5_552frontier t5_552all
theorem t5_553choices : plan3887.choices=[1,8,2,3,7].map (options 5 2) := by rfl


theorem t5_553part0 : t5_553jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_553frontier : t5_553root.frontier 0=t5_553jobs := by rfl
theorem t5_553all : t5_553jobs.all (Job.check tree)=true := by
  simp only [t5_553jobs,List.all_append,List.all_nil,t5_553part0,Bool.and_self]
theorem t5_553checked : Checked tree [1,8,2,3,7] := by
  refine ⟨plan3887,valid3887,t5_553choices,?_⟩
  exact check_of_frontier tree 0 t5_553root t5_553jobs t5_553frontier t5_553all
theorem t5_554choices : plan3888.choices=[1,8,2,3,10].map (options 5 2) := by rfl


theorem t5_554part0 : t5_554jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_554frontier : t5_554root.frontier 0=t5_554jobs := by rfl
theorem t5_554all : t5_554jobs.all (Job.check tree)=true := by
  simp only [t5_554jobs,List.all_append,List.all_nil,t5_554part0,Bool.and_self]
theorem t5_554checked : Checked tree [1,8,2,3,10] := by
  refine ⟨plan3888,valid3888,t5_554choices,?_⟩
  exact check_of_frontier tree 0 t5_554root t5_554jobs t5_554frontier t5_554all
theorem t5_555choices : plan4203.choices=[1,8,2,5,7].map (options 5 3) := by rfl


theorem t5_555part0 : t5_555jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_555frontier : t5_555root.frontier 0=t5_555jobs := by rfl
theorem t5_555all : t5_555jobs.all (Job.check tree)=true := by
  simp only [t5_555jobs,List.all_append,List.all_nil,t5_555part0,Bool.and_self]
theorem t5_555checked : Checked tree [1,8,2,5,7] := by
  refine ⟨plan4203,valid4203,t5_555choices,?_⟩
  exact check_of_frontier tree 0 t5_555root t5_555jobs t5_555frontier t5_555all
theorem t5_556choices : plan4204.choices=[1,8,2,6,6].map (options 5 3) := by rfl


theorem t5_556part0 : t5_556jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_556frontier : t5_556root.frontier 0=t5_556jobs := by rfl
theorem t5_556all : t5_556jobs.all (Job.check tree)=true := by
  simp only [t5_556jobs,List.all_append,List.all_nil,t5_556part0,Bool.and_self]
theorem t5_556checked : Checked tree [1,8,2,6,6] := by
  refine ⟨plan4204,valid4204,t5_556choices,?_⟩
  exact check_of_frontier tree 0 t5_556root t5_556jobs t5_556frontier t5_556all
theorem t5_557choices : plan4205.choices=[1,8,2,6,7].map (options 5 3) := by rfl


theorem t5_557part0 : t5_557jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_557frontier : t5_557root.frontier 0=t5_557jobs := by rfl
theorem t5_557all : t5_557jobs.all (Job.check tree)=true := by
  simp only [t5_557jobs,List.all_append,List.all_nil,t5_557part0,Bool.and_self]
theorem t5_557checked : Checked tree [1,8,2,6,7] := by
  refine ⟨plan4205,valid4205,t5_557choices,?_⟩
  exact check_of_frontier tree 0 t5_557root t5_557jobs t5_557frontier t5_557all
theorem t5_558choices : plan4206.choices=[1,8,2,6,10].map (options 5 3) := by rfl


theorem t5_558part0 : t5_558jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_558frontier : t5_558root.frontier 0=t5_558jobs := by rfl
theorem t5_558all : t5_558jobs.all (Job.check tree)=true := by
  simp only [t5_558jobs,List.all_append,List.all_nil,t5_558part0,Bool.and_self]
theorem t5_558checked : Checked tree [1,8,2,6,10] := by
  refine ⟨plan4206,valid4206,t5_558choices,?_⟩
  exact check_of_frontier tree 0 t5_558root t5_558jobs t5_558frontier t5_558all
theorem t5_559choices : plan4207.choices=[1,8,2,7,7].map (options 5 3) := by rfl


theorem t5_559part0 : t5_559jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_559frontier : t5_559root.frontier 0=t5_559jobs := by rfl
theorem t5_559all : t5_559jobs.all (Job.check tree)=true := by
  simp only [t5_559jobs,List.all_append,List.all_nil,t5_559part0,Bool.and_self]
theorem t5_559checked : Checked tree [1,8,2,7,7] := by
  refine ⟨plan4207,valid4207,t5_559choices,?_⟩
  exact check_of_frontier tree 0 t5_559root t5_559jobs t5_559frontier t5_559all
theorem t5_560choices : plan4208.choices=[1,8,2,9,7].map (options 5 3) := by rfl


theorem t5_560part0 : t5_560jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_560frontier : t5_560root.frontier 0=t5_560jobs := by rfl
theorem t5_560all : t5_560jobs.all (Job.check tree)=true := by
  simp only [t5_560jobs,List.all_append,List.all_nil,t5_560part0,Bool.and_self]
theorem t5_560checked : Checked tree [1,8,2,9,7] := by
  refine ⟨plan4208,valid4208,t5_560choices,?_⟩
  exact check_of_frontier tree 0 t5_560root t5_560jobs t5_560frontier t5_560all
theorem t5_561choices : plan4209.choices=[1,8,2,10,7].map (options 5 3) := by rfl


theorem t5_561part0 : t5_561jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_561frontier : t5_561root.frontier 0=t5_561jobs := by rfl
theorem t5_561all : t5_561jobs.all (Job.check tree)=true := by
  simp only [t5_561jobs,List.all_append,List.all_nil,t5_561part0,Bool.and_self]
theorem t5_561checked : Checked tree [1,8,2,10,7] := by
  refine ⟨plan4209,valid4209,t5_561choices,?_⟩
  exact check_of_frontier tree 0 t5_561root t5_561jobs t5_561frontier t5_561all
theorem t5_562choices : plan4210.choices=[1,8,2,10,10].map (options 5 3) := by rfl


theorem t5_562part0 : t5_562jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_562frontier : t5_562root.frontier 0=t5_562jobs := by rfl
theorem t5_562all : t5_562jobs.all (Job.check tree)=true := by
  simp only [t5_562jobs,List.all_append,List.all_nil,t5_562part0,Bool.and_self]
theorem t5_562checked : Checked tree [1,8,2,10,10] := by
  refine ⟨plan4210,valid4210,t5_562choices,?_⟩
  exact check_of_frontier tree 0 t5_562root t5_562jobs t5_562frontier t5_562all
theorem t5_563choices : plan3724.choices=[1,8,3,3,3].map (options 5 1) := by rfl


theorem t5_563part0 : t5_563jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_563frontier : t5_563root.frontier 0=t5_563jobs := by rfl
theorem t5_563all : t5_563jobs.all (Job.check tree)=true := by
  simp only [t5_563jobs,List.all_append,List.all_nil,t5_563part0,Bool.and_self]
theorem t5_563checked : Checked tree [1,8,3,3,3] := by
  refine ⟨plan3724,valid3724,t5_563choices,?_⟩
  exact check_of_frontier tree 0 t5_563root t5_563jobs t5_563frontier t5_563all
theorem t5_564choices : plan3889.choices=[1,8,3,3,6].map (options 5 2) := by rfl


theorem t5_564part0 : t5_564jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_564frontier : t5_564root.frontier 0=t5_564jobs := by rfl
theorem t5_564all : t5_564jobs.all (Job.check tree)=true := by
  simp only [t5_564jobs,List.all_append,List.all_nil,t5_564part0,Bool.and_self]
theorem t5_564checked : Checked tree [1,8,3,3,6] := by
  refine ⟨plan3889,valid3889,t5_564choices,?_⟩
  exact check_of_frontier tree 0 t5_564root t5_564jobs t5_564frontier t5_564all
theorem t5_565choices : plan3890.choices=[1,8,3,3,7].map (options 5 2) := by rfl


theorem t5_565part0 : t5_565jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_565frontier : t5_565root.frontier 0=t5_565jobs := by rfl
theorem t5_565all : t5_565jobs.all (Job.check tree)=true := by
  simp only [t5_565jobs,List.all_append,List.all_nil,t5_565part0,Bool.and_self]
theorem t5_565checked : Checked tree [1,8,3,3,7] := by
  refine ⟨plan3890,valid3890,t5_565choices,?_⟩
  exact check_of_frontier tree 0 t5_565root t5_565jobs t5_565frontier t5_565all
theorem t5_566choices : plan3891.choices=[1,8,3,3,10].map (options 5 2) := by rfl


theorem t5_566part0 : t5_566jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_566frontier : t5_566root.frontier 0=t5_566jobs := by rfl
theorem t5_566all : t5_566jobs.all (Job.check tree)=true := by
  simp only [t5_566jobs,List.all_append,List.all_nil,t5_566part0,Bool.and_self]
theorem t5_566checked : Checked tree [1,8,3,3,10] := by
  refine ⟨plan3891,valid3891,t5_566choices,?_⟩
  exact check_of_frontier tree 0 t5_566root t5_566jobs t5_566frontier t5_566all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks012 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_529checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_517checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_530checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_531checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_532checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_533checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_534checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_535checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_536checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_537checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_538checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_539checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_518checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_540checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_541checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_542checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_543checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_544checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_545checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_546checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_547checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_548checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_549checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_519checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_550checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_551checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_552checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_553checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_554checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_555checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_556checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_557checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_558checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_559checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_520checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_560checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_561checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_562checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_563checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_564checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_565checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_566checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_521checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_522checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_523checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_524checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_525checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_526checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_527checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_528checked⟩
