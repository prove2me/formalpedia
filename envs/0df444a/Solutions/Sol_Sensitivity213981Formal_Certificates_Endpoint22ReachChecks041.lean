-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks041
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:01:18.727984+00:00
-- url     : https://prove2.me/submissions/5ce08043-3c3e-41d5-9f45-12275cdca210

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks041
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
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













theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)





theorem valid498 : plan498.Valid := valid_step _ _ _ valid100 (by decide +kernel)































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

theorem valid1340 : plan1340.Valid := valid_step _ _ _ valid495 (by decide +kernel)








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





































theorem valid1363 : plan1363.Valid := valid_step _ _ _ valid498 (by decide +kernel)





































theorem valid1382 : plan1382.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1383 : plan1383.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1384 : plan1384.Valid := valid_step _ _ _ valid487 (by decide +kernel)









theorem valid1389 : plan1389.Valid := valid_step _ _ _ valid498 (by decide +kernel)



















































































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

























theorem valid3757 : plan3757.Valid := valid_step _ _ _ valid2549 (by decide +kernel)






































































































































































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





















































































theorem valid2731 : plan2731.Valid := valid_step _ _ _ valid1363 (by decide +kernel)



























theorem valid2745 : plan2745.Valid := valid_step _ _ _ valid1382 (by decide +kernel)

theorem valid2746 : plan2746.Valid := valid_step _ _ _ valid1383 (by decide +kernel)

theorem valid2747 : plan2747.Valid := valid_step _ _ _ valid1384 (by decide +kernel)









theorem valid2752 : plan2752.Valid := valid_step _ _ _ valid1389 (by decide +kernel)



















theorem valid2762 : plan2762.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2763 : plan2763.Valid := valid_step _ _ _ valid1340 (by decide +kernel)










































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







































































































theorem valid3988 : plan3988.Valid := valid_step _ _ _ valid2622 (by decide +kernel)

theorem valid3989 : plan3989.Valid := valid_step _ _ _ valid2627 (by decide +kernel)

theorem valid3990 : plan3990.Valid := valid_step _ _ _ valid2628 (by decide +kernel)

theorem valid3991 : plan3991.Valid := valid_step _ _ _ valid2629 (by decide +kernel)


















































































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

theorem valid4417 : plan4417.Valid := valid_step _ _ _ valid2763 (by decide +kernel)






























































































































































































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





















































































































































































theorem valid4411 : plan4411.Valid := valid_step _ _ _ valid2731 (by decide +kernel)

theorem valid4412 : plan4412.Valid := valid_step _ _ _ valid2745 (by decide +kernel)

theorem valid4413 : plan4413.Valid := valid_step _ _ _ valid2746 (by decide +kernel)

theorem valid4414 : plan4414.Valid := valid_step _ _ _ valid2747 (by decide +kernel)

theorem valid4415 : plan4415.Valid := valid_step _ _ _ valid2752 (by decide +kernel)

theorem valid4416 : plan4416.Valid := valid_step _ _ _ valid2762 (by decide +kernel)
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





theorem valid4899 : plan4899.Valid := valid_step _ _ _ valid2880 (by decide +kernel)

theorem valid4900 : plan4900.Valid := valid_step _ _ _ valid2881 (by decide +kernel)

theorem valid4901 : plan4901.Valid := valid_step _ _ _ valid2882 (by decide +kernel)

theorem valid4902 : plan4902.Valid := valid_step _ _ _ valid2883 (by decide +kernel)

theorem valid4903 : plan4903.Valid := valid_step _ _ _ valid2884 (by decide +kernel)

theorem valid4904 : plan4904.Valid := valid_step _ _ _ valid2885 (by decide +kernel)

theorem valid4905 : plan4905.Valid := valid_step _ _ _ valid2886 (by decide +kernel)

theorem valid4906 : plan4906.Valid := valid_step _ _ _ valid2887 (by decide +kernel)

theorem valid4907 : plan4907.Valid := valid_step _ _ _ valid2888 (by decide +kernel)

theorem valid4908 : plan4908.Valid := valid_step _ _ _ valid2889 (by decide +kernel)

theorem valid4909 : plan4909.Valid := valid_step _ _ _ valid2890 (by decide +kernel)

theorem valid4910 : plan4910.Valid := valid_step _ _ _ valid2891 (by decide +kernel)

theorem valid4911 : plan4911.Valid := valid_step _ _ _ valid2892 (by decide +kernel)

theorem valid4912 : plan4912.Valid := valid_step _ _ _ valid2893 (by decide +kernel)

theorem valid4913 : plan4913.Valid := valid_step _ _ _ valid2894 (by decide +kernel)

theorem valid4914 : plan4914.Valid := valid_step _ _ _ valid2895 (by decide +kernel)

theorem valid4915 : plan4915.Valid := valid_step _ _ _ valid2896 (by decide +kernel)

theorem valid4916 : plan4916.Valid := valid_step _ _ _ valid2897 (by decide +kernel)

theorem valid4917 : plan4917.Valid := valid_step _ _ _ valid2898 (by decide +kernel)

theorem valid4918 : plan4918.Valid := valid_step _ _ _ valid2899 (by decide +kernel)

theorem valid4919 : plan4919.Valid := valid_step _ _ _ valid2900 (by decide +kernel)

theorem valid4920 : plan4920.Valid := valid_step _ _ _ valid2901 (by decide +kernel)

theorem valid4921 : plan4921.Valid := valid_step _ _ _ valid2902 (by decide +kernel)

theorem valid4922 : plan4922.Valid := valid_step _ _ _ valid2903 (by decide +kernel)












































































































































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
theorem t5_1398choices : plan4411.choices=[8,2,5,9,3].map (options 5 3) := by rfl


theorem t5_1398part0 : t5_1398jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1398frontier : t5_1398root.frontier 0=t5_1398jobs := by rfl
theorem t5_1398all : t5_1398jobs.all (Job.check tree)=true := by
  simp only [t5_1398jobs,List.all_append,List.all_nil,t5_1398part0,Bool.and_self]
theorem t5_1398checked : Checked tree [8,2,5,9,3] := by
  refine ⟨plan4411,valid4411,t5_1398choices,?_⟩
  exact check_of_frontier tree 0 t5_1398root t5_1398jobs t5_1398frontier t5_1398all
theorem t5_1399choices : plan4899.choices=[8,2,5,9,6].map (options 5 4) := by rfl


theorem t5_1399part0 : t5_1399jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1399frontier : t5_1399root.frontier 0=t5_1399jobs := by rfl
theorem t5_1399all : t5_1399jobs.all (Job.check tree)=true := by
  simp only [t5_1399jobs,List.all_append,List.all_nil,t5_1399part0,Bool.and_self]
theorem t5_1399checked : Checked tree [8,2,5,9,6] := by
  refine ⟨plan4899,valid4899,t5_1399choices,?_⟩
  exact check_of_frontier tree 0 t5_1399root t5_1399jobs t5_1399frontier t5_1399all
theorem t5_1400choices : plan4900.choices=[8,2,5,9,7].map (options 5 4) := by rfl


theorem t5_1400part0 : t5_1400jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1400frontier : t5_1400root.frontier 0=t5_1400jobs := by rfl
theorem t5_1400all : t5_1400jobs.all (Job.check tree)=true := by
  simp only [t5_1400jobs,List.all_append,List.all_nil,t5_1400part0,Bool.and_self]
theorem t5_1400checked : Checked tree [8,2,5,9,7] := by
  refine ⟨plan4900,valid4900,t5_1400choices,?_⟩
  exact check_of_frontier tree 0 t5_1400root t5_1400jobs t5_1400frontier t5_1400all
theorem t5_1401choices : plan4901.choices=[8,2,5,9,10].map (options 5 4) := by rfl


theorem t5_1401part0 : t5_1401jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1401frontier : t5_1401root.frontier 0=t5_1401jobs := by rfl
theorem t5_1401all : t5_1401jobs.all (Job.check tree)=true := by
  simp only [t5_1401jobs,List.all_append,List.all_nil,t5_1401part0,Bool.and_self]
theorem t5_1401checked : Checked tree [8,2,5,9,10] := by
  refine ⟨plan4901,valid4901,t5_1401choices,?_⟩
  exact check_of_frontier tree 0 t5_1401root t5_1401jobs t5_1401frontier t5_1401all
theorem t5_1402choices : plan4902.choices=[8,2,5,10,7].map (options 5 4) := by rfl


theorem t5_1402part0 : t5_1402jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1402frontier : t5_1402root.frontier 0=t5_1402jobs := by rfl
theorem t5_1402all : t5_1402jobs.all (Job.check tree)=true := by
  simp only [t5_1402jobs,List.all_append,List.all_nil,t5_1402part0,Bool.and_self]
theorem t5_1402checked : Checked tree [8,2,5,10,7] := by
  refine ⟨plan4902,valid4902,t5_1402choices,?_⟩
  exact check_of_frontier tree 0 t5_1402root t5_1402jobs t5_1402frontier t5_1402all
theorem t5_1403choices : plan4903.choices=[8,2,5,10,10].map (options 5 4) := by rfl


theorem t5_1403part0 : t5_1403jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1403frontier : t5_1403root.frontier 0=t5_1403jobs := by rfl
theorem t5_1403all : t5_1403jobs.all (Job.check tree)=true := by
  simp only [t5_1403jobs,List.all_append,List.all_nil,t5_1403part0,Bool.and_self]
theorem t5_1403checked : Checked tree [8,2,5,10,10] := by
  refine ⟨plan4903,valid4903,t5_1403choices,?_⟩
  exact check_of_frontier tree 0 t5_1403root t5_1403jobs t5_1403frontier t5_1403all
theorem t5_1404choices : plan4904.choices=[8,2,6,6,6].map (options 5 4) := by rfl


theorem t5_1404part0 : t5_1404jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1404frontier : t5_1404root.frontier 0=t5_1404jobs := by rfl
theorem t5_1404all : t5_1404jobs.all (Job.check tree)=true := by
  simp only [t5_1404jobs,List.all_append,List.all_nil,t5_1404part0,Bool.and_self]
theorem t5_1404checked : Checked tree [8,2,6,6,6] := by
  refine ⟨plan4904,valid4904,t5_1404choices,?_⟩
  exact check_of_frontier tree 0 t5_1404root t5_1404jobs t5_1404frontier t5_1404all
theorem t5_1405choices : plan4905.choices=[8,2,6,6,7].map (options 5 4) := by rfl


theorem t5_1405part0 : t5_1405jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1405frontier : t5_1405root.frontier 0=t5_1405jobs := by rfl
theorem t5_1405all : t5_1405jobs.all (Job.check tree)=true := by
  simp only [t5_1405jobs,List.all_append,List.all_nil,t5_1405part0,Bool.and_self]
theorem t5_1405checked : Checked tree [8,2,6,6,7] := by
  refine ⟨plan4905,valid4905,t5_1405choices,?_⟩
  exact check_of_frontier tree 0 t5_1405root t5_1405jobs t5_1405frontier t5_1405all
theorem t5_1406choices : plan4906.choices=[8,2,6,6,10].map (options 5 4) := by rfl


theorem t5_1406part0 : t5_1406jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1406frontier : t5_1406root.frontier 0=t5_1406jobs := by rfl
theorem t5_1406all : t5_1406jobs.all (Job.check tree)=true := by
  simp only [t5_1406jobs,List.all_append,List.all_nil,t5_1406part0,Bool.and_self]
theorem t5_1406checked : Checked tree [8,2,6,6,10] := by
  refine ⟨plan4906,valid4906,t5_1406choices,?_⟩
  exact check_of_frontier tree 0 t5_1406root t5_1406jobs t5_1406frontier t5_1406all
theorem t5_1407choices : plan4907.choices=[8,2,6,7,7].map (options 5 4) := by rfl


theorem t5_1407part0 : t5_1407jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1407frontier : t5_1407root.frontier 0=t5_1407jobs := by rfl
theorem t5_1407all : t5_1407jobs.all (Job.check tree)=true := by
  simp only [t5_1407jobs,List.all_append,List.all_nil,t5_1407part0,Bool.and_self]
theorem t5_1407checked : Checked tree [8,2,6,7,7] := by
  refine ⟨plan4907,valid4907,t5_1407choices,?_⟩
  exact check_of_frontier tree 0 t5_1407root t5_1407jobs t5_1407frontier t5_1407all
theorem t5_1408choices : plan4908.choices=[8,2,6,10,7].map (options 5 4) := by rfl


theorem t5_1408part0 : t5_1408jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1408frontier : t5_1408root.frontier 0=t5_1408jobs := by rfl
theorem t5_1408all : t5_1408jobs.all (Job.check tree)=true := by
  simp only [t5_1408jobs,List.all_append,List.all_nil,t5_1408part0,Bool.and_self]
theorem t5_1408checked : Checked tree [8,2,6,10,7] := by
  refine ⟨plan4908,valid4908,t5_1408choices,?_⟩
  exact check_of_frontier tree 0 t5_1408root t5_1408jobs t5_1408frontier t5_1408all
theorem t5_1409choices : plan4909.choices=[8,2,6,10,10].map (options 5 4) := by rfl


theorem t5_1409part0 : t5_1409jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1409frontier : t5_1409root.frontier 0=t5_1409jobs := by rfl
theorem t5_1409all : t5_1409jobs.all (Job.check tree)=true := by
  simp only [t5_1409jobs,List.all_append,List.all_nil,t5_1409part0,Bool.and_self]
theorem t5_1409checked : Checked tree [8,2,6,10,10] := by
  refine ⟨plan4909,valid4909,t5_1409choices,?_⟩
  exact check_of_frontier tree 0 t5_1409root t5_1409jobs t5_1409frontier t5_1409all
theorem t5_1410choices : plan4910.choices=[8,2,7,7,7].map (options 5 4) := by rfl


theorem t5_1410part0 : t5_1410jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1410frontier : t5_1410root.frontier 0=t5_1410jobs := by rfl
theorem t5_1410all : t5_1410jobs.all (Job.check tree)=true := by
  simp only [t5_1410jobs,List.all_append,List.all_nil,t5_1410part0,Bool.and_self]
theorem t5_1410checked : Checked tree [8,2,7,7,7] := by
  refine ⟨plan4910,valid4910,t5_1410choices,?_⟩
  exact check_of_frontier tree 0 t5_1410root t5_1410jobs t5_1410frontier t5_1410all
theorem t5_1411choices : plan3988.choices=[8,2,9,3,3].map (options 5 2) := by rfl


theorem t5_1411part0 : t5_1411jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1411frontier : t5_1411root.frontier 0=t5_1411jobs := by rfl
theorem t5_1411all : t5_1411jobs.all (Job.check tree)=true := by
  simp only [t5_1411jobs,List.all_append,List.all_nil,t5_1411part0,Bool.and_self]
theorem t5_1411checked : Checked tree [8,2,9,3,3] := by
  refine ⟨plan3988,valid3988,t5_1411choices,?_⟩
  exact check_of_frontier tree 0 t5_1411root t5_1411jobs t5_1411frontier t5_1411all
theorem t5_1412choices : plan4412.choices=[8,2,9,3,6].map (options 5 3) := by rfl


theorem t5_1412part0 : t5_1412jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1412frontier : t5_1412root.frontier 0=t5_1412jobs := by rfl
theorem t5_1412all : t5_1412jobs.all (Job.check tree)=true := by
  simp only [t5_1412jobs,List.all_append,List.all_nil,t5_1412part0,Bool.and_self]
theorem t5_1412checked : Checked tree [8,2,9,3,6] := by
  refine ⟨plan4412,valid4412,t5_1412choices,?_⟩
  exact check_of_frontier tree 0 t5_1412root t5_1412jobs t5_1412frontier t5_1412all
theorem t5_1413choices : plan4413.choices=[8,2,9,3,7].map (options 5 3) := by rfl


theorem t5_1413part0 : t5_1413jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1413frontier : t5_1413root.frontier 0=t5_1413jobs := by rfl
theorem t5_1413all : t5_1413jobs.all (Job.check tree)=true := by
  simp only [t5_1413jobs,List.all_append,List.all_nil,t5_1413part0,Bool.and_self]
theorem t5_1413checked : Checked tree [8,2,9,3,7] := by
  refine ⟨plan4413,valid4413,t5_1413choices,?_⟩
  exact check_of_frontier tree 0 t5_1413root t5_1413jobs t5_1413frontier t5_1413all
theorem t5_1414choices : plan4414.choices=[8,2,9,3,10].map (options 5 3) := by rfl


theorem t5_1414part0 : t5_1414jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1414frontier : t5_1414root.frontier 0=t5_1414jobs := by rfl
theorem t5_1414all : t5_1414jobs.all (Job.check tree)=true := by
  simp only [t5_1414jobs,List.all_append,List.all_nil,t5_1414part0,Bool.and_self]
theorem t5_1414checked : Checked tree [8,2,9,3,10] := by
  refine ⟨plan4414,valid4414,t5_1414choices,?_⟩
  exact check_of_frontier tree 0 t5_1414root t5_1414jobs t5_1414frontier t5_1414all
theorem t5_1415choices : plan4911.choices=[8,2,9,6,6].map (options 5 4) := by rfl


theorem t5_1415part0 : t5_1415jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1415frontier : t5_1415root.frontier 0=t5_1415jobs := by rfl
theorem t5_1415all : t5_1415jobs.all (Job.check tree)=true := by
  simp only [t5_1415jobs,List.all_append,List.all_nil,t5_1415part0,Bool.and_self]
theorem t5_1415checked : Checked tree [8,2,9,6,6] := by
  refine ⟨plan4911,valid4911,t5_1415choices,?_⟩
  exact check_of_frontier tree 0 t5_1415root t5_1415jobs t5_1415frontier t5_1415all
theorem t5_1416choices : plan4912.choices=[8,2,9,6,7].map (options 5 4) := by rfl


theorem t5_1416part0 : t5_1416jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1416frontier : t5_1416root.frontier 0=t5_1416jobs := by rfl
theorem t5_1416all : t5_1416jobs.all (Job.check tree)=true := by
  simp only [t5_1416jobs,List.all_append,List.all_nil,t5_1416part0,Bool.and_self]
theorem t5_1416checked : Checked tree [8,2,9,6,7] := by
  refine ⟨plan4912,valid4912,t5_1416choices,?_⟩
  exact check_of_frontier tree 0 t5_1416root t5_1416jobs t5_1416frontier t5_1416all
theorem t5_1417choices : plan4913.choices=[8,2,9,6,10].map (options 5 4) := by rfl


theorem t5_1417part0 : t5_1417jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1417frontier : t5_1417root.frontier 0=t5_1417jobs := by rfl
theorem t5_1417all : t5_1417jobs.all (Job.check tree)=true := by
  simp only [t5_1417jobs,List.all_append,List.all_nil,t5_1417part0,Bool.and_self]
theorem t5_1417checked : Checked tree [8,2,9,6,10] := by
  refine ⟨plan4913,valid4913,t5_1417choices,?_⟩
  exact check_of_frontier tree 0 t5_1417root t5_1417jobs t5_1417frontier t5_1417all
theorem t5_1418choices : plan4914.choices=[8,2,9,7,7].map (options 5 4) := by rfl


theorem t5_1418part0 : t5_1418jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1418frontier : t5_1418root.frontier 0=t5_1418jobs := by rfl
theorem t5_1418all : t5_1418jobs.all (Job.check tree)=true := by
  simp only [t5_1418jobs,List.all_append,List.all_nil,t5_1418part0,Bool.and_self]
theorem t5_1418checked : Checked tree [8,2,9,7,7] := by
  refine ⟨plan4914,valid4914,t5_1418choices,?_⟩
  exact check_of_frontier tree 0 t5_1418root t5_1418jobs t5_1418frontier t5_1418all
theorem t5_1419choices : plan4415.choices=[8,2,9,9,3].map (options 5 3) := by rfl


theorem t5_1419part0 : t5_1419jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1419frontier : t5_1419root.frontier 0=t5_1419jobs := by rfl
theorem t5_1419all : t5_1419jobs.all (Job.check tree)=true := by
  simp only [t5_1419jobs,List.all_append,List.all_nil,t5_1419part0,Bool.and_self]
theorem t5_1419checked : Checked tree [8,2,9,9,3] := by
  refine ⟨plan4415,valid4415,t5_1419choices,?_⟩
  exact check_of_frontier tree 0 t5_1419root t5_1419jobs t5_1419frontier t5_1419all
theorem t5_1420choices : plan4915.choices=[8,2,9,9,6].map (options 5 4) := by rfl


theorem t5_1420part0 : t5_1420jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1420frontier : t5_1420root.frontier 0=t5_1420jobs := by rfl
theorem t5_1420all : t5_1420jobs.all (Job.check tree)=true := by
  simp only [t5_1420jobs,List.all_append,List.all_nil,t5_1420part0,Bool.and_self]
theorem t5_1420checked : Checked tree [8,2,9,9,6] := by
  refine ⟨plan4915,valid4915,t5_1420choices,?_⟩
  exact check_of_frontier tree 0 t5_1420root t5_1420jobs t5_1420frontier t5_1420all
theorem t5_1421choices : plan4916.choices=[8,2,9,9,7].map (options 5 4) := by rfl


theorem t5_1421part0 : t5_1421jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1421frontier : t5_1421root.frontier 0=t5_1421jobs := by rfl
theorem t5_1421all : t5_1421jobs.all (Job.check tree)=true := by
  simp only [t5_1421jobs,List.all_append,List.all_nil,t5_1421part0,Bool.and_self]
theorem t5_1421checked : Checked tree [8,2,9,9,7] := by
  refine ⟨plan4916,valid4916,t5_1421choices,?_⟩
  exact check_of_frontier tree 0 t5_1421root t5_1421jobs t5_1421frontier t5_1421all
theorem t5_1422choices : plan4917.choices=[8,2,9,9,10].map (options 5 4) := by rfl


theorem t5_1422part0 : t5_1422jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1422frontier : t5_1422root.frontier 0=t5_1422jobs := by rfl
theorem t5_1422all : t5_1422jobs.all (Job.check tree)=true := by
  simp only [t5_1422jobs,List.all_append,List.all_nil,t5_1422part0,Bool.and_self]
theorem t5_1422checked : Checked tree [8,2,9,9,10] := by
  refine ⟨plan4917,valid4917,t5_1422choices,?_⟩
  exact check_of_frontier tree 0 t5_1422root t5_1422jobs t5_1422frontier t5_1422all
theorem t5_1423choices : plan4918.choices=[8,2,9,10,7].map (options 5 4) := by rfl


theorem t5_1423part0 : t5_1423jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1423frontier : t5_1423root.frontier 0=t5_1423jobs := by rfl
theorem t5_1423all : t5_1423jobs.all (Job.check tree)=true := by
  simp only [t5_1423jobs,List.all_append,List.all_nil,t5_1423part0,Bool.and_self]
theorem t5_1423checked : Checked tree [8,2,9,10,7] := by
  refine ⟨plan4918,valid4918,t5_1423choices,?_⟩
  exact check_of_frontier tree 0 t5_1423root t5_1423jobs t5_1423frontier t5_1423all
theorem t5_1424choices : plan4919.choices=[8,2,9,10,10].map (options 5 4) := by rfl


theorem t5_1424part0 : t5_1424jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1424frontier : t5_1424root.frontier 0=t5_1424jobs := by rfl
theorem t5_1424all : t5_1424jobs.all (Job.check tree)=true := by
  simp only [t5_1424jobs,List.all_append,List.all_nil,t5_1424part0,Bool.and_self]
theorem t5_1424checked : Checked tree [8,2,9,10,10] := by
  refine ⟨plan4919,valid4919,t5_1424choices,?_⟩
  exact check_of_frontier tree 0 t5_1424root t5_1424jobs t5_1424frontier t5_1424all
theorem t5_1425choices : plan4920.choices=[8,2,10,7,7].map (options 5 4) := by rfl


theorem t5_1425part0 : t5_1425jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1425frontier : t5_1425root.frontier 0=t5_1425jobs := by rfl
theorem t5_1425all : t5_1425jobs.all (Job.check tree)=true := by
  simp only [t5_1425jobs,List.all_append,List.all_nil,t5_1425part0,Bool.and_self]
theorem t5_1425checked : Checked tree [8,2,10,7,7] := by
  refine ⟨plan4920,valid4920,t5_1425choices,?_⟩
  exact check_of_frontier tree 0 t5_1425root t5_1425jobs t5_1425frontier t5_1425all
theorem t5_1426choices : plan4921.choices=[8,2,10,10,7].map (options 5 4) := by rfl


theorem t5_1426part0 : t5_1426jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1426frontier : t5_1426root.frontier 0=t5_1426jobs := by rfl
theorem t5_1426all : t5_1426jobs.all (Job.check tree)=true := by
  simp only [t5_1426jobs,List.all_append,List.all_nil,t5_1426part0,Bool.and_self]
theorem t5_1426checked : Checked tree [8,2,10,10,7] := by
  refine ⟨plan4921,valid4921,t5_1426choices,?_⟩
  exact check_of_frontier tree 0 t5_1426root t5_1426jobs t5_1426frontier t5_1426all
theorem t5_1427choices : plan4922.choices=[8,2,10,10,10].map (options 5 4) := by rfl


theorem t5_1427part0 : t5_1427jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1427frontier : t5_1427root.frontier 0=t5_1427jobs := by rfl
theorem t5_1427all : t5_1427jobs.all (Job.check tree)=true := by
  simp only [t5_1427jobs,List.all_append,List.all_nil,t5_1427part0,Bool.and_self]
theorem t5_1427checked : Checked tree [8,2,10,10,10] := by
  refine ⟨plan4922,valid4922,t5_1427choices,?_⟩
  exact check_of_frontier tree 0 t5_1427root t5_1427jobs t5_1427frontier t5_1427all
theorem t5_1428choices : plan3757.choices=[8,3,3,3,3].map (options 5 1) := by rfl


theorem t5_1428part0 : t5_1428jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1428frontier : t5_1428root.frontier 0=t5_1428jobs := by rfl
theorem t5_1428all : t5_1428jobs.all (Job.check tree)=true := by
  simp only [t5_1428jobs,List.all_append,List.all_nil,t5_1428part0,Bool.and_self]
theorem t5_1428checked : Checked tree [8,3,3,3,3] := by
  refine ⟨plan3757,valid3757,t5_1428choices,?_⟩
  exact check_of_frontier tree 0 t5_1428root t5_1428jobs t5_1428frontier t5_1428all
theorem t5_1429choices : plan3989.choices=[8,3,3,3,6].map (options 5 2) := by rfl


theorem t5_1429part0 : t5_1429jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1429frontier : t5_1429root.frontier 0=t5_1429jobs := by rfl
theorem t5_1429all : t5_1429jobs.all (Job.check tree)=true := by
  simp only [t5_1429jobs,List.all_append,List.all_nil,t5_1429part0,Bool.and_self]
theorem t5_1429checked : Checked tree [8,3,3,3,6] := by
  refine ⟨plan3989,valid3989,t5_1429choices,?_⟩
  exact check_of_frontier tree 0 t5_1429root t5_1429jobs t5_1429frontier t5_1429all
theorem t5_1430choices : plan3990.choices=[8,3,3,3,7].map (options 5 2) := by rfl


theorem t5_1430part0 : t5_1430jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1430frontier : t5_1430root.frontier 0=t5_1430jobs := by rfl
theorem t5_1430all : t5_1430jobs.all (Job.check tree)=true := by
  simp only [t5_1430jobs,List.all_append,List.all_nil,t5_1430part0,Bool.and_self]
theorem t5_1430checked : Checked tree [8,3,3,3,7] := by
  refine ⟨plan3990,valid3990,t5_1430choices,?_⟩
  exact check_of_frontier tree 0 t5_1430root t5_1430jobs t5_1430frontier t5_1430all
theorem t5_1431choices : plan3991.choices=[8,3,3,3,10].map (options 5 2) := by rfl


theorem t5_1431part0 : t5_1431jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1431frontier : t5_1431root.frontier 0=t5_1431jobs := by rfl
theorem t5_1431all : t5_1431jobs.all (Job.check tree)=true := by
  simp only [t5_1431jobs,List.all_append,List.all_nil,t5_1431part0,Bool.and_self]
theorem t5_1431checked : Checked tree [8,3,3,3,10] := by
  refine ⟨plan3991,valid3991,t5_1431choices,?_⟩
  exact check_of_frontier tree 0 t5_1431root t5_1431jobs t5_1431frontier t5_1431all
theorem t5_1432choices : plan4416.choices=[8,3,3,6,6].map (options 5 3) := by rfl


theorem t5_1432part0 : t5_1432jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1432frontier : t5_1432root.frontier 0=t5_1432jobs := by rfl
theorem t5_1432all : t5_1432jobs.all (Job.check tree)=true := by
  simp only [t5_1432jobs,List.all_append,List.all_nil,t5_1432part0,Bool.and_self]
theorem t5_1432checked : Checked tree [8,3,3,6,6] := by
  refine ⟨plan4416,valid4416,t5_1432choices,?_⟩
  exact check_of_frontier tree 0 t5_1432root t5_1432jobs t5_1432frontier t5_1432all
theorem t5_1433choices : plan4417.choices=[8,3,3,6,7].map (options 5 3) := by rfl


theorem t5_1433part0 : t5_1433jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1433part1 : t5_1433jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1433frontier : t5_1433root.frontier 1=t5_1433jobs := by rfl
theorem t5_1433all : t5_1433jobs.all (Job.check tree)=true := by
  simp only [t5_1433jobs,List.all_append,List.all_nil,t5_1433part0,t5_1433part1,Bool.and_self]
theorem t5_1433checked : Checked tree [8,3,3,6,7] := by
  refine ⟨plan4417,valid4417,t5_1433choices,?_⟩
  exact check_of_frontier tree 1 t5_1433root t5_1433jobs t5_1433frontier t5_1433all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks041 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1410checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1398checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1411checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1412checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1413checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1414checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1415checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1416checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1417checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1418checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1419checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1420checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1399checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1421checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1422checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1423checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1424checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1425checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1426checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1427checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1428checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1429checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1430checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1400checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1431checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1432checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1433checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1401checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1402checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1403checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1404checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1405checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1406checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1407checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1408checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1409checked⟩
