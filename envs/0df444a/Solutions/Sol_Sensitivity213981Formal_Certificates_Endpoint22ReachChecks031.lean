-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks031
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:26.11087+00:00
-- url     : https://prove2.me/submissions/aa07a1e2-0e80-4304-8307-1014c1593ca6

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks031
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans049
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

theorem valid488 : plan488.Valid := valid_step _ _ _ valid100 (by decide +kernel)











theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)







theorem valid498 : plan498.Valid := valid_step _ _ _ valid100 (by decide +kernel)























theorem valid510 : plan510.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid511 : plan511.Valid := valid_step _ _ _ valid109 (by decide +kernel)



theorem valid513 : plan513.Valid := valid_step _ _ _ valid111 (by decide +kernel)

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































theorem valid1264 : plan1264.Valid := valid_step _ _ _ valid453 (by decide +kernel)



































































theorem valid1298 : plan1298.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1299 : plan1299.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1300 : plan1300.Valid := valid_step _ _ _ valid465 (by decide +kernel)





























theorem valid1315 : plan1315.Valid := valid_step _ _ _ valid462 (by decide +kernel)















































theorem valid1339 : plan1339.Valid := valid_step _ _ _ valid494 (by decide +kernel)










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









































































































theorem valid2549 : plan2549.Valid := valid_step _ _ _ valid1264 (by decide +kernel)






















































































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

















theorem valid1353 : plan1353.Valid := valid_step _ _ _ valid488 (by decide +kernel)



















theorem valid1363 : plan1363.Valid := valid_step _ _ _ valid498 (by decide +kernel)





































theorem valid1382 : plan1382.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1383 : plan1383.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1384 : plan1384.Valid := valid_step _ _ _ valid487 (by decide +kernel)









theorem valid1389 : plan1389.Valid := valid_step _ _ _ valid498 (by decide +kernel)

































































theorem valid1422 : plan1422.Valid := valid_step _ _ _ valid510 (by decide +kernel)

theorem valid1423 : plan1423.Valid := valid_step _ _ _ valid511 (by decide +kernel)



theorem valid1425 : plan1425.Valid := valid_step _ _ _ valid513 (by decide +kernel)

theorem valid1426 : plan1426.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1427 : plan1427.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1428 : plan1428.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1429 : plan1429.Valid := valid_step _ _ _ valid517 (by decide +kernel)



theorem valid1431 : plan1431.Valid := valid_step _ _ _ valid519 (by decide +kernel)

theorem valid1432 : plan1432.Valid := valid_step _ _ _ valid520 (by decide +kernel)



theorem valid1434 : plan1434.Valid := valid_step _ _ _ valid522 (by decide +kernel)

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



























































theorem valid2622 : plan2622.Valid := valid_step _ _ _ valid1315 (by decide +kernel)









theorem valid2627 : plan2627.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2628 : plan2628.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2629 : plan2629.Valid := valid_step _ _ _ valid1300 (by decide +kernel)






















































































































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















theorem valid3752 : plan3752.Valid := valid_step _ _ _ valid2549 (by decide +kernel)
















































































































































































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

































































theorem valid2721 : plan2721.Valid := valid_step _ _ _ valid1353 (by decide +kernel)



















theorem valid2731 : plan2731.Valid := valid_step _ _ _ valid1363 (by decide +kernel)



























theorem valid2745 : plan2745.Valid := valid_step _ _ _ valid1382 (by decide +kernel)

theorem valid2746 : plan2746.Valid := valid_step _ _ _ valid1383 (by decide +kernel)

theorem valid2747 : plan2747.Valid := valid_step _ _ _ valid1384 (by decide +kernel)









theorem valid2752 : plan2752.Valid := valid_step _ _ _ valid1389 (by decide +kernel)



















theorem valid2762 : plan2762.Valid := valid_step _ _ _ valid1339 (by decide +kernel)












































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

















































theorem valid3961 : plan3961.Valid := valid_step _ _ _ valid2622 (by decide +kernel)

theorem valid3962 : plan3962.Valid := valid_step _ _ _ valid2627 (by decide +kernel)

theorem valid3963 : plan3963.Valid := valid_step _ _ _ valid2628 (by decide +kernel)

theorem valid3964 : plan3964.Valid := valid_step _ _ _ valid2629 (by decide +kernel)








































































































































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

















































































































































































theorem valid2873 : plan2873.Valid := valid_step _ _ _ valid1422 (by decide +kernel)

theorem valid2874 : plan2874.Valid := valid_step _ _ _ valid1423 (by decide +kernel)

theorem valid2875 : plan2875.Valid := valid_step _ _ _ valid1425 (by decide +kernel)

theorem valid2876 : plan2876.Valid := valid_step _ _ _ valid1426 (by decide +kernel)

theorem valid2877 : plan2877.Valid := valid_step _ _ _ valid1427 (by decide +kernel)

theorem valid2878 : plan2878.Valid := valid_step _ _ _ valid1428 (by decide +kernel)

theorem valid2879 : plan2879.Valid := valid_step _ _ _ valid1429 (by decide +kernel)

theorem valid2880 : plan2880.Valid := valid_step _ _ _ valid1431 (by decide +kernel)
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

theorem valid2881 : plan2881.Valid := valid_step _ _ _ valid1432 (by decide +kernel)

theorem valid2882 : plan2882.Valid := valid_step _ _ _ valid1434 (by decide +kernel)

theorem valid2883 : plan2883.Valid := valid_step _ _ _ valid1435 (by decide +kernel)

theorem valid2884 : plan2884.Valid := valid_step _ _ _ valid1436 (by decide +kernel)

theorem valid2885 : plan2885.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid2886 : plan2886.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid2887 : plan2887.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid2888 : plan2888.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid2889 : plan2889.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid2890 : plan2890.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid2891 : plan2891.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

theorem valid2892 : plan2892.Valid := valid_step _ _ _ valid1451 (by decide +kernel)

theorem valid2893 : plan2893.Valid := valid_step _ _ _ valid1452 (by decide +kernel)

theorem valid2894 : plan2894.Valid := valid_step _ _ _ valid1453 (by decide +kernel)

theorem valid2895 : plan2895.Valid := valid_step _ _ _ valid1454 (by decide +kernel)

theorem valid2896 : plan2896.Valid := valid_step _ _ _ valid1456 (by decide +kernel)

theorem valid2897 : plan2897.Valid := valid_step _ _ _ valid1457 (by decide +kernel)

theorem valid2898 : plan2898.Valid := valid_step _ _ _ valid1459 (by decide +kernel)

theorem valid2899 : plan2899.Valid := valid_step _ _ _ valid1460 (by decide +kernel)

theorem valid2900 : plan2900.Valid := valid_step _ _ _ valid1461 (by decide +kernel)

theorem valid2901 : plan2901.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid2902 : plan2902.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid2903 : plan2903.Valid := valid_step _ _ _ valid1464 (by decide +kernel)


















































































































































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























































































theorem valid4748 : plan4748.Valid := valid_step _ _ _ valid2873 (by decide +kernel)

theorem valid4749 : plan4749.Valid := valid_step _ _ _ valid2874 (by decide +kernel)

theorem valid4750 : plan4750.Valid := valid_step _ _ _ valid2875 (by decide +kernel)

theorem valid4751 : plan4751.Valid := valid_step _ _ _ valid2876 (by decide +kernel)

theorem valid4752 : plan4752.Valid := valid_step _ _ _ valid2877 (by decide +kernel)

theorem valid4753 : plan4753.Valid := valid_step _ _ _ valid2878 (by decide +kernel)

theorem valid4754 : plan4754.Valid := valid_step _ _ _ valid2879 (by decide +kernel)

theorem valid4755 : plan4755.Valid := valid_step _ _ _ valid2880 (by decide +kernel)

theorem valid4756 : plan4756.Valid := valid_step _ _ _ valid2881 (by decide +kernel)

theorem valid4757 : plan4757.Valid := valid_step _ _ _ valid2882 (by decide +kernel)

theorem valid4758 : plan4758.Valid := valid_step _ _ _ valid2883 (by decide +kernel)

theorem valid4759 : plan4759.Valid := valid_step _ _ _ valid2884 (by decide +kernel)

theorem valid4760 : plan4760.Valid := valid_step _ _ _ valid2885 (by decide +kernel)

theorem valid4761 : plan4761.Valid := valid_step _ _ _ valid2886 (by decide +kernel)

theorem valid4762 : plan4762.Valid := valid_step _ _ _ valid2887 (by decide +kernel)

theorem valid4763 : plan4763.Valid := valid_step _ _ _ valid2888 (by decide +kernel)

theorem valid4764 : plan4764.Valid := valid_step _ _ _ valid2889 (by decide +kernel)

theorem valid4765 : plan4765.Valid := valid_step _ _ _ valid2890 (by decide +kernel)

theorem valid4766 : plan4766.Valid := valid_step _ _ _ valid2891 (by decide +kernel)

theorem valid4767 : plan4767.Valid := valid_step _ _ _ valid2892 (by decide +kernel)

theorem valid4768 : plan4768.Valid := valid_step _ _ _ valid2893 (by decide +kernel)

theorem valid4769 : plan4769.Valid := valid_step _ _ _ valid2894 (by decide +kernel)

theorem valid4770 : plan4770.Valid := valid_step _ _ _ valid2895 (by decide +kernel)

theorem valid4771 : plan4771.Valid := valid_step _ _ _ valid2896 (by decide +kernel)

theorem valid4772 : plan4772.Valid := valid_step _ _ _ valid2897 (by decide +kernel)

theorem valid4773 : plan4773.Valid := valid_step _ _ _ valid2898 (by decide +kernel)

theorem valid4774 : plan4774.Valid := valid_step _ _ _ valid2899 (by decide +kernel)

theorem valid4775 : plan4775.Valid := valid_step _ _ _ valid2900 (by decide +kernel)

theorem valid4776 : plan4776.Valid := valid_step _ _ _ valid2901 (by decide +kernel)

theorem valid4777 : plan4777.Valid := valid_step _ _ _ valid2902 (by decide +kernel)

theorem valid4778 : plan4778.Valid := valid_step _ _ _ valid2903 (by decide +kernel)












































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





























theorem valid4335 : plan4335.Valid := valid_step _ _ _ valid2721 (by decide +kernel)

theorem valid4336 : plan4336.Valid := valid_step _ _ _ valid2731 (by decide +kernel)

theorem valid4337 : plan4337.Valid := valid_step _ _ _ valid2745 (by decide +kernel)

theorem valid4338 : plan4338.Valid := valid_step _ _ _ valid2746 (by decide +kernel)

theorem valid4339 : plan4339.Valid := valid_step _ _ _ valid2747 (by decide +kernel)

theorem valid4340 : plan4340.Valid := valid_step _ _ _ valid2752 (by decide +kernel)

theorem valid4341 : plan4341.Valid := valid_step _ _ _ valid2762 (by decide +kernel)






















































































































































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
theorem t5_929choices : plan4335.choices=[4,2,5,5,3].map (options 5 3) := by rfl


theorem t5_929part0 : t5_929jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_929frontier : t5_929root.frontier 0=t5_929jobs := by rfl
theorem t5_929all : t5_929jobs.all (Job.check tree)=true := by
  simp only [t5_929jobs,List.all_append,List.all_nil,t5_929part0,Bool.and_self]
theorem t5_929checked : Checked tree [4,2,5,5,3] := by
  refine ⟨plan4335,valid4335,t5_929choices,?_⟩
  exact check_of_frontier tree 0 t5_929root t5_929jobs t5_929frontier t5_929all
theorem t5_930choices : plan4748.choices=[4,2,5,5,6].map (options 5 4) := by rfl


theorem t5_930part0 : t5_930jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_930frontier : t5_930root.frontier 0=t5_930jobs := by rfl
theorem t5_930all : t5_930jobs.all (Job.check tree)=true := by
  simp only [t5_930jobs,List.all_append,List.all_nil,t5_930part0,Bool.and_self]
theorem t5_930checked : Checked tree [4,2,5,5,6] := by
  refine ⟨plan4748,valid4748,t5_930choices,?_⟩
  exact check_of_frontier tree 0 t5_930root t5_930jobs t5_930frontier t5_930all
theorem t5_931choices : plan4749.choices=[4,2,5,5,7].map (options 5 4) := by rfl


theorem t5_931part0 : t5_931jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_931frontier : t5_931root.frontier 0=t5_931jobs := by rfl
theorem t5_931all : t5_931jobs.all (Job.check tree)=true := by
  simp only [t5_931jobs,List.all_append,List.all_nil,t5_931part0,Bool.and_self]
theorem t5_931checked : Checked tree [4,2,5,5,7] := by
  refine ⟨plan4749,valid4749,t5_931choices,?_⟩
  exact check_of_frontier tree 0 t5_931root t5_931jobs t5_931frontier t5_931all
theorem t5_932choices : plan4750.choices=[4,2,5,5,10].map (options 5 4) := by rfl


theorem t5_932part0 : t5_932jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_932frontier : t5_932root.frontier 0=t5_932jobs := by rfl
theorem t5_932all : t5_932jobs.all (Job.check tree)=true := by
  simp only [t5_932jobs,List.all_append,List.all_nil,t5_932part0,Bool.and_self]
theorem t5_932checked : Checked tree [4,2,5,5,10] := by
  refine ⟨plan4750,valid4750,t5_932choices,?_⟩
  exact check_of_frontier tree 0 t5_932root t5_932jobs t5_932frontier t5_932all
theorem t5_933choices : plan4751.choices=[4,2,5,6,6].map (options 5 4) := by rfl


theorem t5_933part0 : t5_933jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_933frontier : t5_933root.frontier 0=t5_933jobs := by rfl
theorem t5_933all : t5_933jobs.all (Job.check tree)=true := by
  simp only [t5_933jobs,List.all_append,List.all_nil,t5_933part0,Bool.and_self]
theorem t5_933checked : Checked tree [4,2,5,6,6] := by
  refine ⟨plan4751,valid4751,t5_933choices,?_⟩
  exact check_of_frontier tree 0 t5_933root t5_933jobs t5_933frontier t5_933all
theorem t5_934choices : plan4752.choices=[4,2,5,6,7].map (options 5 4) := by rfl


theorem t5_934part0 : t5_934jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_934frontier : t5_934root.frontier 0=t5_934jobs := by rfl
theorem t5_934all : t5_934jobs.all (Job.check tree)=true := by
  simp only [t5_934jobs,List.all_append,List.all_nil,t5_934part0,Bool.and_self]
theorem t5_934checked : Checked tree [4,2,5,6,7] := by
  refine ⟨plan4752,valid4752,t5_934choices,?_⟩
  exact check_of_frontier tree 0 t5_934root t5_934jobs t5_934frontier t5_934all
theorem t5_935choices : plan4753.choices=[4,2,5,6,10].map (options 5 4) := by rfl


theorem t5_935part0 : t5_935jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_935frontier : t5_935root.frontier 0=t5_935jobs := by rfl
theorem t5_935all : t5_935jobs.all (Job.check tree)=true := by
  simp only [t5_935jobs,List.all_append,List.all_nil,t5_935part0,Bool.and_self]
theorem t5_935checked : Checked tree [4,2,5,6,10] := by
  refine ⟨plan4753,valid4753,t5_935choices,?_⟩
  exact check_of_frontier tree 0 t5_935root t5_935jobs t5_935frontier t5_935all
theorem t5_936choices : plan4754.choices=[4,2,5,7,7].map (options 5 4) := by rfl


theorem t5_936part0 : t5_936jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_936frontier : t5_936root.frontier 0=t5_936jobs := by rfl
theorem t5_936all : t5_936jobs.all (Job.check tree)=true := by
  simp only [t5_936jobs,List.all_append,List.all_nil,t5_936part0,Bool.and_self]
theorem t5_936checked : Checked tree [4,2,5,7,7] := by
  refine ⟨plan4754,valid4754,t5_936choices,?_⟩
  exact check_of_frontier tree 0 t5_936root t5_936jobs t5_936frontier t5_936all
theorem t5_937choices : plan4336.choices=[4,2,5,9,3].map (options 5 3) := by rfl


theorem t5_937part0 : t5_937jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_937frontier : t5_937root.frontier 0=t5_937jobs := by rfl
theorem t5_937all : t5_937jobs.all (Job.check tree)=true := by
  simp only [t5_937jobs,List.all_append,List.all_nil,t5_937part0,Bool.and_self]
theorem t5_937checked : Checked tree [4,2,5,9,3] := by
  refine ⟨plan4336,valid4336,t5_937choices,?_⟩
  exact check_of_frontier tree 0 t5_937root t5_937jobs t5_937frontier t5_937all
theorem t5_938choices : plan4755.choices=[4,2,5,9,6].map (options 5 4) := by rfl


theorem t5_938part0 : t5_938jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_938frontier : t5_938root.frontier 0=t5_938jobs := by rfl
theorem t5_938all : t5_938jobs.all (Job.check tree)=true := by
  simp only [t5_938jobs,List.all_append,List.all_nil,t5_938part0,Bool.and_self]
theorem t5_938checked : Checked tree [4,2,5,9,6] := by
  refine ⟨plan4755,valid4755,t5_938choices,?_⟩
  exact check_of_frontier tree 0 t5_938root t5_938jobs t5_938frontier t5_938all
theorem t5_939choices : plan4756.choices=[4,2,5,9,7].map (options 5 4) := by rfl


theorem t5_939part0 : t5_939jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_939frontier : t5_939root.frontier 0=t5_939jobs := by rfl
theorem t5_939all : t5_939jobs.all (Job.check tree)=true := by
  simp only [t5_939jobs,List.all_append,List.all_nil,t5_939part0,Bool.and_self]
theorem t5_939checked : Checked tree [4,2,5,9,7] := by
  refine ⟨plan4756,valid4756,t5_939choices,?_⟩
  exact check_of_frontier tree 0 t5_939root t5_939jobs t5_939frontier t5_939all
theorem t5_940choices : plan4757.choices=[4,2,5,9,10].map (options 5 4) := by rfl


theorem t5_940part0 : t5_940jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_940frontier : t5_940root.frontier 0=t5_940jobs := by rfl
theorem t5_940all : t5_940jobs.all (Job.check tree)=true := by
  simp only [t5_940jobs,List.all_append,List.all_nil,t5_940part0,Bool.and_self]
theorem t5_940checked : Checked tree [4,2,5,9,10] := by
  refine ⟨plan4757,valid4757,t5_940choices,?_⟩
  exact check_of_frontier tree 0 t5_940root t5_940jobs t5_940frontier t5_940all
theorem t5_941choices : plan4758.choices=[4,2,5,10,7].map (options 5 4) := by rfl


theorem t5_941part0 : t5_941jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_941frontier : t5_941root.frontier 0=t5_941jobs := by rfl
theorem t5_941all : t5_941jobs.all (Job.check tree)=true := by
  simp only [t5_941jobs,List.all_append,List.all_nil,t5_941part0,Bool.and_self]
theorem t5_941checked : Checked tree [4,2,5,10,7] := by
  refine ⟨plan4758,valid4758,t5_941choices,?_⟩
  exact check_of_frontier tree 0 t5_941root t5_941jobs t5_941frontier t5_941all
theorem t5_942choices : plan4759.choices=[4,2,5,10,10].map (options 5 4) := by rfl


theorem t5_942part0 : t5_942jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_942frontier : t5_942root.frontier 0=t5_942jobs := by rfl
theorem t5_942all : t5_942jobs.all (Job.check tree)=true := by
  simp only [t5_942jobs,List.all_append,List.all_nil,t5_942part0,Bool.and_self]
theorem t5_942checked : Checked tree [4,2,5,10,10] := by
  refine ⟨plan4759,valid4759,t5_942choices,?_⟩
  exact check_of_frontier tree 0 t5_942root t5_942jobs t5_942frontier t5_942all
theorem t5_943choices : plan4760.choices=[4,2,6,6,6].map (options 5 4) := by rfl


theorem t5_943part0 : t5_943jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_943frontier : t5_943root.frontier 0=t5_943jobs := by rfl
theorem t5_943all : t5_943jobs.all (Job.check tree)=true := by
  simp only [t5_943jobs,List.all_append,List.all_nil,t5_943part0,Bool.and_self]
theorem t5_943checked : Checked tree [4,2,6,6,6] := by
  refine ⟨plan4760,valid4760,t5_943choices,?_⟩
  exact check_of_frontier tree 0 t5_943root t5_943jobs t5_943frontier t5_943all
theorem t5_944choices : plan4761.choices=[4,2,6,6,7].map (options 5 4) := by rfl


theorem t5_944part0 : t5_944jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_944frontier : t5_944root.frontier 0=t5_944jobs := by rfl
theorem t5_944all : t5_944jobs.all (Job.check tree)=true := by
  simp only [t5_944jobs,List.all_append,List.all_nil,t5_944part0,Bool.and_self]
theorem t5_944checked : Checked tree [4,2,6,6,7] := by
  refine ⟨plan4761,valid4761,t5_944choices,?_⟩
  exact check_of_frontier tree 0 t5_944root t5_944jobs t5_944frontier t5_944all
theorem t5_945choices : plan4762.choices=[4,2,6,6,10].map (options 5 4) := by rfl


theorem t5_945part0 : t5_945jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_945frontier : t5_945root.frontier 0=t5_945jobs := by rfl
theorem t5_945all : t5_945jobs.all (Job.check tree)=true := by
  simp only [t5_945jobs,List.all_append,List.all_nil,t5_945part0,Bool.and_self]
theorem t5_945checked : Checked tree [4,2,6,6,10] := by
  refine ⟨plan4762,valid4762,t5_945choices,?_⟩
  exact check_of_frontier tree 0 t5_945root t5_945jobs t5_945frontier t5_945all
theorem t5_946choices : plan4763.choices=[4,2,6,7,7].map (options 5 4) := by rfl


theorem t5_946part0 : t5_946jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_946frontier : t5_946root.frontier 0=t5_946jobs := by rfl
theorem t5_946all : t5_946jobs.all (Job.check tree)=true := by
  simp only [t5_946jobs,List.all_append,List.all_nil,t5_946part0,Bool.and_self]
theorem t5_946checked : Checked tree [4,2,6,7,7] := by
  refine ⟨plan4763,valid4763,t5_946choices,?_⟩
  exact check_of_frontier tree 0 t5_946root t5_946jobs t5_946frontier t5_946all
theorem t5_947choices : plan4764.choices=[4,2,6,10,7].map (options 5 4) := by rfl


theorem t5_947part0 : t5_947jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_947frontier : t5_947root.frontier 0=t5_947jobs := by rfl
theorem t5_947all : t5_947jobs.all (Job.check tree)=true := by
  simp only [t5_947jobs,List.all_append,List.all_nil,t5_947part0,Bool.and_self]
theorem t5_947checked : Checked tree [4,2,6,10,7] := by
  refine ⟨plan4764,valid4764,t5_947choices,?_⟩
  exact check_of_frontier tree 0 t5_947root t5_947jobs t5_947frontier t5_947all
theorem t5_948choices : plan4765.choices=[4,2,6,10,10].map (options 5 4) := by rfl


theorem t5_948part0 : t5_948jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_948frontier : t5_948root.frontier 0=t5_948jobs := by rfl
theorem t5_948all : t5_948jobs.all (Job.check tree)=true := by
  simp only [t5_948jobs,List.all_append,List.all_nil,t5_948part0,Bool.and_self]
theorem t5_948checked : Checked tree [4,2,6,10,10] := by
  refine ⟨plan4765,valid4765,t5_948choices,?_⟩
  exact check_of_frontier tree 0 t5_948root t5_948jobs t5_948frontier t5_948all
theorem t5_949choices : plan4766.choices=[4,2,7,7,7].map (options 5 4) := by rfl


theorem t5_949part0 : t5_949jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_949frontier : t5_949root.frontier 0=t5_949jobs := by rfl
theorem t5_949all : t5_949jobs.all (Job.check tree)=true := by
  simp only [t5_949jobs,List.all_append,List.all_nil,t5_949part0,Bool.and_self]
theorem t5_949checked : Checked tree [4,2,7,7,7] := by
  refine ⟨plan4766,valid4766,t5_949choices,?_⟩
  exact check_of_frontier tree 0 t5_949root t5_949jobs t5_949frontier t5_949all
theorem t5_950choices : plan3961.choices=[4,2,9,3,3].map (options 5 2) := by rfl


theorem t5_950part0 : t5_950jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_950frontier : t5_950root.frontier 0=t5_950jobs := by rfl
theorem t5_950all : t5_950jobs.all (Job.check tree)=true := by
  simp only [t5_950jobs,List.all_append,List.all_nil,t5_950part0,Bool.and_self]
theorem t5_950checked : Checked tree [4,2,9,3,3] := by
  refine ⟨plan3961,valid3961,t5_950choices,?_⟩
  exact check_of_frontier tree 0 t5_950root t5_950jobs t5_950frontier t5_950all
theorem t5_951choices : plan4337.choices=[4,2,9,3,6].map (options 5 3) := by rfl


theorem t5_951part0 : t5_951jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_951frontier : t5_951root.frontier 0=t5_951jobs := by rfl
theorem t5_951all : t5_951jobs.all (Job.check tree)=true := by
  simp only [t5_951jobs,List.all_append,List.all_nil,t5_951part0,Bool.and_self]
theorem t5_951checked : Checked tree [4,2,9,3,6] := by
  refine ⟨plan4337,valid4337,t5_951choices,?_⟩
  exact check_of_frontier tree 0 t5_951root t5_951jobs t5_951frontier t5_951all
theorem t5_952choices : plan4338.choices=[4,2,9,3,7].map (options 5 3) := by rfl


theorem t5_952part0 : t5_952jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_952frontier : t5_952root.frontier 0=t5_952jobs := by rfl
theorem t5_952all : t5_952jobs.all (Job.check tree)=true := by
  simp only [t5_952jobs,List.all_append,List.all_nil,t5_952part0,Bool.and_self]
theorem t5_952checked : Checked tree [4,2,9,3,7] := by
  refine ⟨plan4338,valid4338,t5_952choices,?_⟩
  exact check_of_frontier tree 0 t5_952root t5_952jobs t5_952frontier t5_952all
theorem t5_953choices : plan4339.choices=[4,2,9,3,10].map (options 5 3) := by rfl


theorem t5_953part0 : t5_953jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_953frontier : t5_953root.frontier 0=t5_953jobs := by rfl
theorem t5_953all : t5_953jobs.all (Job.check tree)=true := by
  simp only [t5_953jobs,List.all_append,List.all_nil,t5_953part0,Bool.and_self]
theorem t5_953checked : Checked tree [4,2,9,3,10] := by
  refine ⟨plan4339,valid4339,t5_953choices,?_⟩
  exact check_of_frontier tree 0 t5_953root t5_953jobs t5_953frontier t5_953all
theorem t5_954choices : plan4767.choices=[4,2,9,6,6].map (options 5 4) := by rfl


theorem t5_954part0 : t5_954jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_954frontier : t5_954root.frontier 0=t5_954jobs := by rfl
theorem t5_954all : t5_954jobs.all (Job.check tree)=true := by
  simp only [t5_954jobs,List.all_append,List.all_nil,t5_954part0,Bool.and_self]
theorem t5_954checked : Checked tree [4,2,9,6,6] := by
  refine ⟨plan4767,valid4767,t5_954choices,?_⟩
  exact check_of_frontier tree 0 t5_954root t5_954jobs t5_954frontier t5_954all
theorem t5_955choices : plan4768.choices=[4,2,9,6,7].map (options 5 4) := by rfl


theorem t5_955part0 : t5_955jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_955frontier : t5_955root.frontier 0=t5_955jobs := by rfl
theorem t5_955all : t5_955jobs.all (Job.check tree)=true := by
  simp only [t5_955jobs,List.all_append,List.all_nil,t5_955part0,Bool.and_self]
theorem t5_955checked : Checked tree [4,2,9,6,7] := by
  refine ⟨plan4768,valid4768,t5_955choices,?_⟩
  exact check_of_frontier tree 0 t5_955root t5_955jobs t5_955frontier t5_955all
theorem t5_956choices : plan4769.choices=[4,2,9,6,10].map (options 5 4) := by rfl


theorem t5_956part0 : t5_956jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_956frontier : t5_956root.frontier 0=t5_956jobs := by rfl
theorem t5_956all : t5_956jobs.all (Job.check tree)=true := by
  simp only [t5_956jobs,List.all_append,List.all_nil,t5_956part0,Bool.and_self]
theorem t5_956checked : Checked tree [4,2,9,6,10] := by
  refine ⟨plan4769,valid4769,t5_956choices,?_⟩
  exact check_of_frontier tree 0 t5_956root t5_956jobs t5_956frontier t5_956all
theorem t5_957choices : plan4770.choices=[4,2,9,7,7].map (options 5 4) := by rfl


theorem t5_957part0 : t5_957jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_957frontier : t5_957root.frontier 0=t5_957jobs := by rfl
theorem t5_957all : t5_957jobs.all (Job.check tree)=true := by
  simp only [t5_957jobs,List.all_append,List.all_nil,t5_957part0,Bool.and_self]
theorem t5_957checked : Checked tree [4,2,9,7,7] := by
  refine ⟨plan4770,valid4770,t5_957choices,?_⟩
  exact check_of_frontier tree 0 t5_957root t5_957jobs t5_957frontier t5_957all
theorem t5_958choices : plan4340.choices=[4,2,9,9,3].map (options 5 3) := by rfl


theorem t5_958part0 : t5_958jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_958frontier : t5_958root.frontier 0=t5_958jobs := by rfl
theorem t5_958all : t5_958jobs.all (Job.check tree)=true := by
  simp only [t5_958jobs,List.all_append,List.all_nil,t5_958part0,Bool.and_self]
theorem t5_958checked : Checked tree [4,2,9,9,3] := by
  refine ⟨plan4340,valid4340,t5_958choices,?_⟩
  exact check_of_frontier tree 0 t5_958root t5_958jobs t5_958frontier t5_958all
theorem t5_959choices : plan4771.choices=[4,2,9,9,6].map (options 5 4) := by rfl


theorem t5_959part0 : t5_959jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_959frontier : t5_959root.frontier 0=t5_959jobs := by rfl
theorem t5_959all : t5_959jobs.all (Job.check tree)=true := by
  simp only [t5_959jobs,List.all_append,List.all_nil,t5_959part0,Bool.and_self]
theorem t5_959checked : Checked tree [4,2,9,9,6] := by
  refine ⟨plan4771,valid4771,t5_959choices,?_⟩
  exact check_of_frontier tree 0 t5_959root t5_959jobs t5_959frontier t5_959all
theorem t5_960choices : plan4772.choices=[4,2,9,9,7].map (options 5 4) := by rfl


theorem t5_960part0 : t5_960jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_960frontier : t5_960root.frontier 0=t5_960jobs := by rfl
theorem t5_960all : t5_960jobs.all (Job.check tree)=true := by
  simp only [t5_960jobs,List.all_append,List.all_nil,t5_960part0,Bool.and_self]
theorem t5_960checked : Checked tree [4,2,9,9,7] := by
  refine ⟨plan4772,valid4772,t5_960choices,?_⟩
  exact check_of_frontier tree 0 t5_960root t5_960jobs t5_960frontier t5_960all
theorem t5_961choices : plan4773.choices=[4,2,9,9,10].map (options 5 4) := by rfl


theorem t5_961part0 : t5_961jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_961frontier : t5_961root.frontier 0=t5_961jobs := by rfl
theorem t5_961all : t5_961jobs.all (Job.check tree)=true := by
  simp only [t5_961jobs,List.all_append,List.all_nil,t5_961part0,Bool.and_self]
theorem t5_961checked : Checked tree [4,2,9,9,10] := by
  refine ⟨plan4773,valid4773,t5_961choices,?_⟩
  exact check_of_frontier tree 0 t5_961root t5_961jobs t5_961frontier t5_961all
theorem t5_962choices : plan4774.choices=[4,2,9,10,7].map (options 5 4) := by rfl


theorem t5_962part0 : t5_962jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_962frontier : t5_962root.frontier 0=t5_962jobs := by rfl
theorem t5_962all : t5_962jobs.all (Job.check tree)=true := by
  simp only [t5_962jobs,List.all_append,List.all_nil,t5_962part0,Bool.and_self]
theorem t5_962checked : Checked tree [4,2,9,10,7] := by
  refine ⟨plan4774,valid4774,t5_962choices,?_⟩
  exact check_of_frontier tree 0 t5_962root t5_962jobs t5_962frontier t5_962all
theorem t5_963choices : plan4775.choices=[4,2,9,10,10].map (options 5 4) := by rfl


theorem t5_963part0 : t5_963jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_963frontier : t5_963root.frontier 0=t5_963jobs := by rfl
theorem t5_963all : t5_963jobs.all (Job.check tree)=true := by
  simp only [t5_963jobs,List.all_append,List.all_nil,t5_963part0,Bool.and_self]
theorem t5_963checked : Checked tree [4,2,9,10,10] := by
  refine ⟨plan4775,valid4775,t5_963choices,?_⟩
  exact check_of_frontier tree 0 t5_963root t5_963jobs t5_963frontier t5_963all
theorem t5_964choices : plan4776.choices=[4,2,10,7,7].map (options 5 4) := by rfl


theorem t5_964part0 : t5_964jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_964frontier : t5_964root.frontier 0=t5_964jobs := by rfl
theorem t5_964all : t5_964jobs.all (Job.check tree)=true := by
  simp only [t5_964jobs,List.all_append,List.all_nil,t5_964part0,Bool.and_self]
theorem t5_964checked : Checked tree [4,2,10,7,7] := by
  refine ⟨plan4776,valid4776,t5_964choices,?_⟩
  exact check_of_frontier tree 0 t5_964root t5_964jobs t5_964frontier t5_964all
theorem t5_965choices : plan4777.choices=[4,2,10,10,7].map (options 5 4) := by rfl


theorem t5_965part0 : t5_965jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_965frontier : t5_965root.frontier 0=t5_965jobs := by rfl
theorem t5_965all : t5_965jobs.all (Job.check tree)=true := by
  simp only [t5_965jobs,List.all_append,List.all_nil,t5_965part0,Bool.and_self]
theorem t5_965checked : Checked tree [4,2,10,10,7] := by
  refine ⟨plan4777,valid4777,t5_965choices,?_⟩
  exact check_of_frontier tree 0 t5_965root t5_965jobs t5_965frontier t5_965all
theorem t5_966choices : plan4778.choices=[4,2,10,10,10].map (options 5 4) := by rfl


theorem t5_966part0 : t5_966jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_966frontier : t5_966root.frontier 0=t5_966jobs := by rfl
theorem t5_966all : t5_966jobs.all (Job.check tree)=true := by
  simp only [t5_966jobs,List.all_append,List.all_nil,t5_966part0,Bool.and_self]
theorem t5_966checked : Checked tree [4,2,10,10,10] := by
  refine ⟨plan4778,valid4778,t5_966choices,?_⟩
  exact check_of_frontier tree 0 t5_966root t5_966jobs t5_966frontier t5_966all
theorem t5_967choices : plan3752.choices=[4,3,3,3,3].map (options 5 1) := by rfl


theorem t5_967part0 : t5_967jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_967frontier : t5_967root.frontier 0=t5_967jobs := by rfl
theorem t5_967all : t5_967jobs.all (Job.check tree)=true := by
  simp only [t5_967jobs,List.all_append,List.all_nil,t5_967part0,Bool.and_self]
theorem t5_967checked : Checked tree [4,3,3,3,3] := by
  refine ⟨plan3752,valid3752,t5_967choices,?_⟩
  exact check_of_frontier tree 0 t5_967root t5_967jobs t5_967frontier t5_967all
theorem t5_968choices : plan3962.choices=[4,3,3,3,6].map (options 5 2) := by rfl


theorem t5_968part0 : t5_968jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_968frontier : t5_968root.frontier 0=t5_968jobs := by rfl
theorem t5_968all : t5_968jobs.all (Job.check tree)=true := by
  simp only [t5_968jobs,List.all_append,List.all_nil,t5_968part0,Bool.and_self]
theorem t5_968checked : Checked tree [4,3,3,3,6] := by
  refine ⟨plan3962,valid3962,t5_968choices,?_⟩
  exact check_of_frontier tree 0 t5_968root t5_968jobs t5_968frontier t5_968all
theorem t5_969choices : plan3963.choices=[4,3,3,3,7].map (options 5 2) := by rfl


theorem t5_969part0 : t5_969jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_969frontier : t5_969root.frontier 0=t5_969jobs := by rfl
theorem t5_969all : t5_969jobs.all (Job.check tree)=true := by
  simp only [t5_969jobs,List.all_append,List.all_nil,t5_969part0,Bool.and_self]
theorem t5_969checked : Checked tree [4,3,3,3,7] := by
  refine ⟨plan3963,valid3963,t5_969choices,?_⟩
  exact check_of_frontier tree 0 t5_969root t5_969jobs t5_969frontier t5_969all
theorem t5_970choices : plan3964.choices=[4,3,3,3,10].map (options 5 2) := by rfl


theorem t5_970part0 : t5_970jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_970frontier : t5_970root.frontier 0=t5_970jobs := by rfl
theorem t5_970all : t5_970jobs.all (Job.check tree)=true := by
  simp only [t5_970jobs,List.all_append,List.all_nil,t5_970part0,Bool.and_self]
theorem t5_970checked : Checked tree [4,3,3,3,10] := by
  refine ⟨plan3964,valid3964,t5_970choices,?_⟩
  exact check_of_frontier tree 0 t5_970root t5_970jobs t5_970frontier t5_970all
theorem t5_971choices : plan4341.choices=[4,3,3,6,6].map (options 5 3) := by rfl


theorem t5_971part0 : t5_971jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_971frontier : t5_971root.frontier 0=t5_971jobs := by rfl
theorem t5_971all : t5_971jobs.all (Job.check tree)=true := by
  simp only [t5_971jobs,List.all_append,List.all_nil,t5_971part0,Bool.and_self]
theorem t5_971checked : Checked tree [4,3,3,6,6] := by
  refine ⟨plan4341,valid4341,t5_971choices,?_⟩
  exact check_of_frontier tree 0 t5_971root t5_971jobs t5_971frontier t5_971all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks031 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_942checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_943checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_944checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_945checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_946checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_947checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_948checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_949checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_950checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_951checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_930checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_952checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_953checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_954checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_955checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_956checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_957checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_958checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_959checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_960checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_961checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_931checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_962checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_963checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_964checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_965checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_966checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_967checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_968checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_969checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_970checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_971checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_932checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_933checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_934checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_935checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_936checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_937checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_938checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_939checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_940checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_941checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_929checked⟩
