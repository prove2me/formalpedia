-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks040
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:01:09.200077+00:00
-- url     : https://prove2.me/submissions/2bcff558-1aea-4d1d-8bbb-bf1bcf581fc5

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks040
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
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

theorem valid466 : plan466.Valid := valid_step _ _ _ valid94 (by decide +kernel)



















theorem valid476 : plan476.Valid := valid_step _ _ _ valid94 (by decide +kernel)








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



theorem valid490 : plan490.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid491 : plan491.Valid := valid_step _ _ _ valid103 (by decide +kernel)



theorem valid493 : plan493.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)



theorem valid499 : plan499.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid500 : plan500.Valid := valid_step _ _ _ valid103 (by decide +kernel)



theorem valid502 : plan502.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)











theorem valid510 : plan510.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid511 : plan511.Valid := valid_step _ _ _ valid109 (by decide +kernel)



theorem valid513 : plan513.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)






















































































































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





























theorem valid1279 : plan1279.Valid := valid_step _ _ _ valid465 (by decide +kernel)

theorem valid1280 : plan1280.Valid := valid_step _ _ _ valid466 (by decide +kernel)



















theorem valid1290 : plan1290.Valid := valid_step _ _ _ valid476 (by decide +kernel)















theorem valid1298 : plan1298.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1299 : plan1299.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1300 : plan1300.Valid := valid_step _ _ _ valid465 (by decide +kernel)















theorem valid1308 : plan1308.Valid := valid_step _ _ _ valid462 (by decide +kernel)































theorem valid1324 : plan1324.Valid := valid_step _ _ _ valid490 (by decide +kernel)

theorem valid1325 : plan1325.Valid := valid_step _ _ _ valid491 (by decide +kernel)

theorem valid1326 : plan1326.Valid := valid_step _ _ _ valid493 (by decide +kernel)

theorem valid1327 : plan1327.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1328 : plan1328.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1329 : plan1329.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1330 : plan1330.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1331 : plan1331.Valid := valid_step _ _ _ valid499 (by decide +kernel)

theorem valid1332 : plan1332.Valid := valid_step _ _ _ valid500 (by decide +kernel)

theorem valid1333 : plan1333.Valid := valid_step _ _ _ valid502 (by decide +kernel)

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





























































































theorem valid2543 : plan2543.Valid := valid_step _ _ _ valid1264 (by decide +kernel)



























































































theorem valid2589 : plan2589.Valid := valid_step _ _ _ valid1279 (by decide +kernel)

theorem valid2590 : plan2590.Valid := valid_step _ _ _ valid1280 (by decide +kernel)




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

theorem valid1353 : plan1353.Valid := valid_step _ _ _ valid488 (by decide +kernel)









































































































































theorem valid1422 : plan1422.Valid := valid_step _ _ _ valid510 (by decide +kernel)

theorem valid1423 : plan1423.Valid := valid_step _ _ _ valid511 (by decide +kernel)



theorem valid1425 : plan1425.Valid := valid_step _ _ _ valid513 (by decide +kernel)

theorem valid1426 : plan1426.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1427 : plan1427.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1428 : plan1428.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1429 : plan1429.Valid := valid_step _ _ _ valid517 (by decide +kernel)






















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















theorem valid2600 : plan2600.Valid := valid_step _ _ _ valid1290 (by decide +kernel)













theorem valid2607 : plan2607.Valid := valid_step _ _ _ valid1298 (by decide +kernel)

theorem valid2608 : plan2608.Valid := valid_step _ _ _ valid1299 (by decide +kernel)

theorem valid2609 : plan2609.Valid := valid_step _ _ _ valid1300 (by decide +kernel)













theorem valid2616 : plan2616.Valid := valid_step _ _ _ valid1308 (by decide +kernel)
















































































































































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























theorem valid3756 : plan3756.Valid := valid_step _ _ _ valid2543 (by decide +kernel)








































































































































































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























theorem valid2700 : plan2700.Valid := valid_step _ _ _ valid1324 (by decide +kernel)

theorem valid2701 : plan2701.Valid := valid_step _ _ _ valid1325 (by decide +kernel)

theorem valid2702 : plan2702.Valid := valid_step _ _ _ valid1326 (by decide +kernel)

theorem valid2703 : plan2703.Valid := valid_step _ _ _ valid1327 (by decide +kernel)

theorem valid2704 : plan2704.Valid := valid_step _ _ _ valid1328 (by decide +kernel)

theorem valid2705 : plan2705.Valid := valid_step _ _ _ valid1329 (by decide +kernel)

theorem valid2706 : plan2706.Valid := valid_step _ _ _ valid1330 (by decide +kernel)

theorem valid2707 : plan2707.Valid := valid_step _ _ _ valid1331 (by decide +kernel)

theorem valid2708 : plan2708.Valid := valid_step _ _ _ valid1332 (by decide +kernel)

theorem valid2709 : plan2709.Valid := valid_step _ _ _ valid1333 (by decide +kernel)

theorem valid2710 : plan2710.Valid := valid_step _ _ _ valid1334 (by decide +kernel)

theorem valid2711 : plan2711.Valid := valid_step _ _ _ valid1335 (by decide +kernel)

theorem valid2712 : plan2712.Valid := valid_step _ _ _ valid1339 (by decide +kernel)

theorem valid2713 : plan2713.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2714 : plan2714.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2715 : plan2715.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2716 : plan2716.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2717 : plan2717.Valid := valid_step _ _ _ valid1344 (by decide +kernel)

theorem valid2718 : plan2718.Valid := valid_step _ _ _ valid1350 (by decide +kernel)

theorem valid2719 : plan2719.Valid := valid_step _ _ _ valid1351 (by decide +kernel)

theorem valid2720 : plan2720.Valid := valid_step _ _ _ valid1352 (by decide +kernel)

theorem valid2721 : plan2721.Valid := valid_step _ _ _ valid1353 (by decide +kernel)






























































































































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

























































































theorem valid3981 : plan3981.Valid := valid_step _ _ _ valid2589 (by decide +kernel)

theorem valid3982 : plan3982.Valid := valid_step _ _ _ valid2590 (by decide +kernel)

theorem valid3983 : plan3983.Valid := valid_step _ _ _ valid2600 (by decide +kernel)

theorem valid3984 : plan3984.Valid := valid_step _ _ _ valid2607 (by decide +kernel)

theorem valid3985 : plan3985.Valid := valid_step _ _ _ valid2608 (by decide +kernel)

theorem valid3986 : plan3986.Valid := valid_step _ _ _ valid2609 (by decide +kernel)

theorem valid3987 : plan3987.Valid := valid_step _ _ _ valid2616 (by decide +kernel)


























































































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









































































































































theorem valid4389 : plan4389.Valid := valid_step _ _ _ valid2700 (by decide +kernel)

theorem valid4390 : plan4390.Valid := valid_step _ _ _ valid2701 (by decide +kernel)

theorem valid4391 : plan4391.Valid := valid_step _ _ _ valid2702 (by decide +kernel)

theorem valid4392 : plan4392.Valid := valid_step _ _ _ valid2703 (by decide +kernel)

theorem valid4393 : plan4393.Valid := valid_step _ _ _ valid2704 (by decide +kernel)

theorem valid4394 : plan4394.Valid := valid_step _ _ _ valid2705 (by decide +kernel)

theorem valid4395 : plan4395.Valid := valid_step _ _ _ valid2706 (by decide +kernel)

theorem valid4396 : plan4396.Valid := valid_step _ _ _ valid2707 (by decide +kernel)

theorem valid4397 : plan4397.Valid := valid_step _ _ _ valid2708 (by decide +kernel)

theorem valid4398 : plan4398.Valid := valid_step _ _ _ valid2709 (by decide +kernel)

theorem valid4399 : plan4399.Valid := valid_step _ _ _ valid2710 (by decide +kernel)

theorem valid4400 : plan4400.Valid := valid_step _ _ _ valid2711 (by decide +kernel)

theorem valid4401 : plan4401.Valid := valid_step _ _ _ valid2712 (by decide +kernel)

theorem valid4402 : plan4402.Valid := valid_step _ _ _ valid2713 (by decide +kernel)

theorem valid4403 : plan4403.Valid := valid_step _ _ _ valid2714 (by decide +kernel)

theorem valid4404 : plan4404.Valid := valid_step _ _ _ valid2715 (by decide +kernel)

theorem valid4405 : plan4405.Valid := valid_step _ _ _ valid2716 (by decide +kernel)

theorem valid4406 : plan4406.Valid := valid_step _ _ _ valid2717 (by decide +kernel)

theorem valid4407 : plan4407.Valid := valid_step _ _ _ valid2718 (by decide +kernel)

theorem valid4408 : plan4408.Valid := valid_step _ _ _ valid2719 (by decide +kernel)

theorem valid4409 : plan4409.Valid := valid_step _ _ _ valid2720 (by decide +kernel)

theorem valid4410 : plan4410.Valid := valid_step _ _ _ valid2721 (by decide +kernel)












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























































































































































































theorem valid4892 : plan4892.Valid := valid_step _ _ _ valid2873 (by decide +kernel)

theorem valid4893 : plan4893.Valid := valid_step _ _ _ valid2874 (by decide +kernel)

theorem valid4894 : plan4894.Valid := valid_step _ _ _ valid2875 (by decide +kernel)

theorem valid4895 : plan4895.Valid := valid_step _ _ _ valid2876 (by decide +kernel)

theorem valid4896 : plan4896.Valid := valid_step _ _ _ valid2877 (by decide +kernel)
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

theorem valid4897 : plan4897.Valid := valid_step _ _ _ valid2878 (by decide +kernel)

theorem valid4898 : plan4898.Valid := valid_step _ _ _ valid2879 (by decide +kernel)




























































































































































































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
theorem t5_1361choices : plan3981.choices=[8,2,2,3,10].map (options 5 2) := by rfl


theorem t5_1361part0 : t5_1361jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1361frontier : t5_1361root.frontier 0=t5_1361jobs := by rfl
theorem t5_1361all : t5_1361jobs.all (Job.check tree)=true := by
  simp only [t5_1361jobs,List.all_append,List.all_nil,t5_1361part0,Bool.and_self]
theorem t5_1361checked : Checked tree [8,2,2,3,10] := by
  refine ⟨plan3981,valid3981,t5_1361choices,?_⟩
  exact check_of_frontier tree 0 t5_1361root t5_1361jobs t5_1361frontier t5_1361all
theorem t5_1362choices : plan3982.choices=[8,2,2,5,3].map (options 5 2) := by rfl


theorem t5_1362part0 : t5_1362jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1362frontier : t5_1362root.frontier 0=t5_1362jobs := by rfl
theorem t5_1362all : t5_1362jobs.all (Job.check tree)=true := by
  simp only [t5_1362jobs,List.all_append,List.all_nil,t5_1362part0,Bool.and_self]
theorem t5_1362checked : Checked tree [8,2,2,5,3] := by
  refine ⟨plan3982,valid3982,t5_1362choices,?_⟩
  exact check_of_frontier tree 0 t5_1362root t5_1362jobs t5_1362frontier t5_1362all
theorem t5_1363choices : plan4389.choices=[8,2,2,5,6].map (options 5 3) := by rfl


theorem t5_1363part0 : t5_1363jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1363frontier : t5_1363root.frontier 0=t5_1363jobs := by rfl
theorem t5_1363all : t5_1363jobs.all (Job.check tree)=true := by
  simp only [t5_1363jobs,List.all_append,List.all_nil,t5_1363part0,Bool.and_self]
theorem t5_1363checked : Checked tree [8,2,2,5,6] := by
  refine ⟨plan4389,valid4389,t5_1363choices,?_⟩
  exact check_of_frontier tree 0 t5_1363root t5_1363jobs t5_1363frontier t5_1363all
theorem t5_1364choices : plan4390.choices=[8,2,2,5,7].map (options 5 3) := by rfl


theorem t5_1364part0 : t5_1364jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1364frontier : t5_1364root.frontier 0=t5_1364jobs := by rfl
theorem t5_1364all : t5_1364jobs.all (Job.check tree)=true := by
  simp only [t5_1364jobs,List.all_append,List.all_nil,t5_1364part0,Bool.and_self]
theorem t5_1364checked : Checked tree [8,2,2,5,7] := by
  refine ⟨plan4390,valid4390,t5_1364choices,?_⟩
  exact check_of_frontier tree 0 t5_1364root t5_1364jobs t5_1364frontier t5_1364all
theorem t5_1365choices : plan4391.choices=[8,2,2,5,10].map (options 5 3) := by rfl


theorem t5_1365part0 : t5_1365jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1365frontier : t5_1365root.frontier 0=t5_1365jobs := by rfl
theorem t5_1365all : t5_1365jobs.all (Job.check tree)=true := by
  simp only [t5_1365jobs,List.all_append,List.all_nil,t5_1365part0,Bool.and_self]
theorem t5_1365checked : Checked tree [8,2,2,5,10] := by
  refine ⟨plan4391,valid4391,t5_1365choices,?_⟩
  exact check_of_frontier tree 0 t5_1365root t5_1365jobs t5_1365frontier t5_1365all
theorem t5_1366choices : plan4392.choices=[8,2,2,6,6].map (options 5 3) := by rfl


theorem t5_1366part0 : t5_1366jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1366frontier : t5_1366root.frontier 0=t5_1366jobs := by rfl
theorem t5_1366all : t5_1366jobs.all (Job.check tree)=true := by
  simp only [t5_1366jobs,List.all_append,List.all_nil,t5_1366part0,Bool.and_self]
theorem t5_1366checked : Checked tree [8,2,2,6,6] := by
  refine ⟨plan4392,valid4392,t5_1366choices,?_⟩
  exact check_of_frontier tree 0 t5_1366root t5_1366jobs t5_1366frontier t5_1366all
theorem t5_1367choices : plan4393.choices=[8,2,2,6,7].map (options 5 3) := by rfl


theorem t5_1367part0 : t5_1367jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1367frontier : t5_1367root.frontier 0=t5_1367jobs := by rfl
theorem t5_1367all : t5_1367jobs.all (Job.check tree)=true := by
  simp only [t5_1367jobs,List.all_append,List.all_nil,t5_1367part0,Bool.and_self]
theorem t5_1367checked : Checked tree [8,2,2,6,7] := by
  refine ⟨plan4393,valid4393,t5_1367choices,?_⟩
  exact check_of_frontier tree 0 t5_1367root t5_1367jobs t5_1367frontier t5_1367all
theorem t5_1368choices : plan4394.choices=[8,2,2,6,10].map (options 5 3) := by rfl


theorem t5_1368part0 : t5_1368jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1368frontier : t5_1368root.frontier 0=t5_1368jobs := by rfl
theorem t5_1368all : t5_1368jobs.all (Job.check tree)=true := by
  simp only [t5_1368jobs,List.all_append,List.all_nil,t5_1368part0,Bool.and_self]
theorem t5_1368checked : Checked tree [8,2,2,6,10] := by
  refine ⟨plan4394,valid4394,t5_1368choices,?_⟩
  exact check_of_frontier tree 0 t5_1368root t5_1368jobs t5_1368frontier t5_1368all
theorem t5_1369choices : plan4395.choices=[8,2,2,7,7].map (options 5 3) := by rfl


theorem t5_1369part0 : t5_1369jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1369frontier : t5_1369root.frontier 0=t5_1369jobs := by rfl
theorem t5_1369all : t5_1369jobs.all (Job.check tree)=true := by
  simp only [t5_1369jobs,List.all_append,List.all_nil,t5_1369part0,Bool.and_self]
theorem t5_1369checked : Checked tree [8,2,2,7,7] := by
  refine ⟨plan4395,valid4395,t5_1369choices,?_⟩
  exact check_of_frontier tree 0 t5_1369root t5_1369jobs t5_1369frontier t5_1369all
theorem t5_1370choices : plan3983.choices=[8,2,2,9,3].map (options 5 2) := by rfl


theorem t5_1370part0 : t5_1370jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1370frontier : t5_1370root.frontier 0=t5_1370jobs := by rfl
theorem t5_1370all : t5_1370jobs.all (Job.check tree)=true := by
  simp only [t5_1370jobs,List.all_append,List.all_nil,t5_1370part0,Bool.and_self]
theorem t5_1370checked : Checked tree [8,2,2,9,3] := by
  refine ⟨plan3983,valid3983,t5_1370choices,?_⟩
  exact check_of_frontier tree 0 t5_1370root t5_1370jobs t5_1370frontier t5_1370all
theorem t5_1371choices : plan4396.choices=[8,2,2,9,6].map (options 5 3) := by rfl


theorem t5_1371part0 : t5_1371jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1371frontier : t5_1371root.frontier 0=t5_1371jobs := by rfl
theorem t5_1371all : t5_1371jobs.all (Job.check tree)=true := by
  simp only [t5_1371jobs,List.all_append,List.all_nil,t5_1371part0,Bool.and_self]
theorem t5_1371checked : Checked tree [8,2,2,9,6] := by
  refine ⟨plan4396,valid4396,t5_1371choices,?_⟩
  exact check_of_frontier tree 0 t5_1371root t5_1371jobs t5_1371frontier t5_1371all
theorem t5_1372choices : plan4397.choices=[8,2,2,9,7].map (options 5 3) := by rfl


theorem t5_1372part0 : t5_1372jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1372frontier : t5_1372root.frontier 0=t5_1372jobs := by rfl
theorem t5_1372all : t5_1372jobs.all (Job.check tree)=true := by
  simp only [t5_1372jobs,List.all_append,List.all_nil,t5_1372part0,Bool.and_self]
theorem t5_1372checked : Checked tree [8,2,2,9,7] := by
  refine ⟨plan4397,valid4397,t5_1372choices,?_⟩
  exact check_of_frontier tree 0 t5_1372root t5_1372jobs t5_1372frontier t5_1372all
theorem t5_1373choices : plan4398.choices=[8,2,2,9,10].map (options 5 3) := by rfl


theorem t5_1373part0 : t5_1373jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1373frontier : t5_1373root.frontier 0=t5_1373jobs := by rfl
theorem t5_1373all : t5_1373jobs.all (Job.check tree)=true := by
  simp only [t5_1373jobs,List.all_append,List.all_nil,t5_1373part0,Bool.and_self]
theorem t5_1373checked : Checked tree [8,2,2,9,10] := by
  refine ⟨plan4398,valid4398,t5_1373choices,?_⟩
  exact check_of_frontier tree 0 t5_1373root t5_1373jobs t5_1373frontier t5_1373all
theorem t5_1374choices : plan4399.choices=[8,2,2,10,7].map (options 5 3) := by rfl


theorem t5_1374part0 : t5_1374jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1374frontier : t5_1374root.frontier 0=t5_1374jobs := by rfl
theorem t5_1374all : t5_1374jobs.all (Job.check tree)=true := by
  simp only [t5_1374jobs,List.all_append,List.all_nil,t5_1374part0,Bool.and_self]
theorem t5_1374checked : Checked tree [8,2,2,10,7] := by
  refine ⟨plan4399,valid4399,t5_1374choices,?_⟩
  exact check_of_frontier tree 0 t5_1374root t5_1374jobs t5_1374frontier t5_1374all
theorem t5_1375choices : plan4400.choices=[8,2,2,10,10].map (options 5 3) := by rfl


theorem t5_1375part0 : t5_1375jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1375frontier : t5_1375root.frontier 0=t5_1375jobs := by rfl
theorem t5_1375all : t5_1375jobs.all (Job.check tree)=true := by
  simp only [t5_1375jobs,List.all_append,List.all_nil,t5_1375part0,Bool.and_self]
theorem t5_1375checked : Checked tree [8,2,2,10,10] := by
  refine ⟨plan4400,valid4400,t5_1375choices,?_⟩
  exact check_of_frontier tree 0 t5_1375root t5_1375jobs t5_1375frontier t5_1375all
theorem t5_1376choices : plan3756.choices=[8,2,3,3,3].map (options 5 1) := by rfl


theorem t5_1376part0 : t5_1376jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1376frontier : t5_1376root.frontier 0=t5_1376jobs := by rfl
theorem t5_1376all : t5_1376jobs.all (Job.check tree)=true := by
  simp only [t5_1376jobs,List.all_append,List.all_nil,t5_1376part0,Bool.and_self]
theorem t5_1376checked : Checked tree [8,2,3,3,3] := by
  refine ⟨plan3756,valid3756,t5_1376choices,?_⟩
  exact check_of_frontier tree 0 t5_1376root t5_1376jobs t5_1376frontier t5_1376all
theorem t5_1377choices : plan3984.choices=[8,2,3,3,6].map (options 5 2) := by rfl


theorem t5_1377part0 : t5_1377jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1377frontier : t5_1377root.frontier 0=t5_1377jobs := by rfl
theorem t5_1377all : t5_1377jobs.all (Job.check tree)=true := by
  simp only [t5_1377jobs,List.all_append,List.all_nil,t5_1377part0,Bool.and_self]
theorem t5_1377checked : Checked tree [8,2,3,3,6] := by
  refine ⟨plan3984,valid3984,t5_1377choices,?_⟩
  exact check_of_frontier tree 0 t5_1377root t5_1377jobs t5_1377frontier t5_1377all
theorem t5_1378choices : plan3985.choices=[8,2,3,3,7].map (options 5 2) := by rfl


theorem t5_1378part0 : t5_1378jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1378part1 : t5_1378jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1378frontier : t5_1378root.frontier 1=t5_1378jobs := by rfl
theorem t5_1378all : t5_1378jobs.all (Job.check tree)=true := by
  simp only [t5_1378jobs,List.all_append,List.all_nil,t5_1378part0,t5_1378part1,Bool.and_self]
theorem t5_1378checked : Checked tree [8,2,3,3,7] := by
  refine ⟨plan3985,valid3985,t5_1378choices,?_⟩
  exact check_of_frontier tree 1 t5_1378root t5_1378jobs t5_1378frontier t5_1378all
theorem t5_1379choices : plan3986.choices=[8,2,3,3,10].map (options 5 2) := by rfl


theorem t5_1379part0 : t5_1379jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1379frontier : t5_1379root.frontier 0=t5_1379jobs := by rfl
theorem t5_1379all : t5_1379jobs.all (Job.check tree)=true := by
  simp only [t5_1379jobs,List.all_append,List.all_nil,t5_1379part0,Bool.and_self]
theorem t5_1379checked : Checked tree [8,2,3,3,10] := by
  refine ⟨plan3986,valid3986,t5_1379choices,?_⟩
  exact check_of_frontier tree 0 t5_1379root t5_1379jobs t5_1379frontier t5_1379all
theorem t5_1380choices : plan4401.choices=[8,2,3,6,6].map (options 5 3) := by rfl


theorem t5_1380part0 : t5_1380jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1380frontier : t5_1380root.frontier 0=t5_1380jobs := by rfl
theorem t5_1380all : t5_1380jobs.all (Job.check tree)=true := by
  simp only [t5_1380jobs,List.all_append,List.all_nil,t5_1380part0,Bool.and_self]
theorem t5_1380checked : Checked tree [8,2,3,6,6] := by
  refine ⟨plan4401,valid4401,t5_1380choices,?_⟩
  exact check_of_frontier tree 0 t5_1380root t5_1380jobs t5_1380frontier t5_1380all
theorem t5_1381choices : plan4402.choices=[8,2,3,6,7].map (options 5 3) := by rfl


theorem t5_1381part0 : t5_1381jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1381part1 : t5_1381jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1381frontier : t5_1381root.frontier 1=t5_1381jobs := by rfl
theorem t5_1381all : t5_1381jobs.all (Job.check tree)=true := by
  simp only [t5_1381jobs,List.all_append,List.all_nil,t5_1381part0,t5_1381part1,Bool.and_self]
theorem t5_1381checked : Checked tree [8,2,3,6,7] := by
  refine ⟨plan4402,valid4402,t5_1381choices,?_⟩
  exact check_of_frontier tree 1 t5_1381root t5_1381jobs t5_1381frontier t5_1381all
theorem t5_1382choices : plan4403.choices=[8,2,3,6,10].map (options 5 3) := by rfl


theorem t5_1382part0 : t5_1382jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1382part1 : t5_1382jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1382frontier : t5_1382root.frontier 1=t5_1382jobs := by rfl
theorem t5_1382all : t5_1382jobs.all (Job.check tree)=true := by
  simp only [t5_1382jobs,List.all_append,List.all_nil,t5_1382part0,t5_1382part1,Bool.and_self]
theorem t5_1382checked : Checked tree [8,2,3,6,10] := by
  refine ⟨plan4403,valid4403,t5_1382choices,?_⟩
  exact check_of_frontier tree 1 t5_1382root t5_1382jobs t5_1382frontier t5_1382all
theorem t5_1383choices : plan4404.choices=[8,2,3,7,7].map (options 5 3) := by rfl


theorem t5_1383part0 : t5_1383jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1383frontier : t5_1383root.frontier 0=t5_1383jobs := by rfl
theorem t5_1383all : t5_1383jobs.all (Job.check tree)=true := by
  simp only [t5_1383jobs,List.all_append,List.all_nil,t5_1383part0,Bool.and_self]
theorem t5_1383checked : Checked tree [8,2,3,7,7] := by
  refine ⟨plan4404,valid4404,t5_1383choices,?_⟩
  exact check_of_frontier tree 0 t5_1383root t5_1383jobs t5_1383frontier t5_1383all
theorem t5_1384choices : plan4405.choices=[8,2,3,10,7].map (options 5 3) := by rfl


theorem t5_1384part0 : t5_1384jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1384part1 : t5_1384jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1384frontier : t5_1384root.frontier 1=t5_1384jobs := by rfl
theorem t5_1384all : t5_1384jobs.all (Job.check tree)=true := by
  simp only [t5_1384jobs,List.all_append,List.all_nil,t5_1384part0,t5_1384part1,Bool.and_self]
theorem t5_1384checked : Checked tree [8,2,3,10,7] := by
  refine ⟨plan4405,valid4405,t5_1384choices,?_⟩
  exact check_of_frontier tree 1 t5_1384root t5_1384jobs t5_1384frontier t5_1384all
theorem t5_1385choices : plan4406.choices=[8,2,3,10,10].map (options 5 3) := by rfl


theorem t5_1385part0 : t5_1385jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1385frontier : t5_1385root.frontier 0=t5_1385jobs := by rfl
theorem t5_1385all : t5_1385jobs.all (Job.check tree)=true := by
  simp only [t5_1385jobs,List.all_append,List.all_nil,t5_1385part0,Bool.and_self]
theorem t5_1385checked : Checked tree [8,2,3,10,10] := by
  refine ⟨plan4406,valid4406,t5_1385choices,?_⟩
  exact check_of_frontier tree 0 t5_1385root t5_1385jobs t5_1385frontier t5_1385all
theorem t5_1386choices : plan3987.choices=[8,2,5,3,3].map (options 5 2) := by rfl


theorem t5_1386part0 : t5_1386jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1386frontier : t5_1386root.frontier 0=t5_1386jobs := by rfl
theorem t5_1386all : t5_1386jobs.all (Job.check tree)=true := by
  simp only [t5_1386jobs,List.all_append,List.all_nil,t5_1386part0,Bool.and_self]
theorem t5_1386checked : Checked tree [8,2,5,3,3] := by
  refine ⟨plan3987,valid3987,t5_1386choices,?_⟩
  exact check_of_frontier tree 0 t5_1386root t5_1386jobs t5_1386frontier t5_1386all
theorem t5_1387choices : plan4407.choices=[8,2,5,3,6].map (options 5 3) := by rfl


theorem t5_1387part0 : t5_1387jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1387frontier : t5_1387root.frontier 0=t5_1387jobs := by rfl
theorem t5_1387all : t5_1387jobs.all (Job.check tree)=true := by
  simp only [t5_1387jobs,List.all_append,List.all_nil,t5_1387part0,Bool.and_self]
theorem t5_1387checked : Checked tree [8,2,5,3,6] := by
  refine ⟨plan4407,valid4407,t5_1387choices,?_⟩
  exact check_of_frontier tree 0 t5_1387root t5_1387jobs t5_1387frontier t5_1387all
theorem t5_1388choices : plan4408.choices=[8,2,5,3,7].map (options 5 3) := by rfl


theorem t5_1388part0 : t5_1388jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1388frontier : t5_1388root.frontier 0=t5_1388jobs := by rfl
theorem t5_1388all : t5_1388jobs.all (Job.check tree)=true := by
  simp only [t5_1388jobs,List.all_append,List.all_nil,t5_1388part0,Bool.and_self]
theorem t5_1388checked : Checked tree [8,2,5,3,7] := by
  refine ⟨plan4408,valid4408,t5_1388choices,?_⟩
  exact check_of_frontier tree 0 t5_1388root t5_1388jobs t5_1388frontier t5_1388all
theorem t5_1389choices : plan4409.choices=[8,2,5,3,10].map (options 5 3) := by rfl


theorem t5_1389part0 : t5_1389jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1389frontier : t5_1389root.frontier 0=t5_1389jobs := by rfl
theorem t5_1389all : t5_1389jobs.all (Job.check tree)=true := by
  simp only [t5_1389jobs,List.all_append,List.all_nil,t5_1389part0,Bool.and_self]
theorem t5_1389checked : Checked tree [8,2,5,3,10] := by
  refine ⟨plan4409,valid4409,t5_1389choices,?_⟩
  exact check_of_frontier tree 0 t5_1389root t5_1389jobs t5_1389frontier t5_1389all
theorem t5_1390choices : plan4410.choices=[8,2,5,5,3].map (options 5 3) := by rfl


theorem t5_1390part0 : t5_1390jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1390frontier : t5_1390root.frontier 0=t5_1390jobs := by rfl
theorem t5_1390all : t5_1390jobs.all (Job.check tree)=true := by
  simp only [t5_1390jobs,List.all_append,List.all_nil,t5_1390part0,Bool.and_self]
theorem t5_1390checked : Checked tree [8,2,5,5,3] := by
  refine ⟨plan4410,valid4410,t5_1390choices,?_⟩
  exact check_of_frontier tree 0 t5_1390root t5_1390jobs t5_1390frontier t5_1390all
theorem t5_1391choices : plan4892.choices=[8,2,5,5,6].map (options 5 4) := by rfl


theorem t5_1391part0 : t5_1391jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1391frontier : t5_1391root.frontier 0=t5_1391jobs := by rfl
theorem t5_1391all : t5_1391jobs.all (Job.check tree)=true := by
  simp only [t5_1391jobs,List.all_append,List.all_nil,t5_1391part0,Bool.and_self]
theorem t5_1391checked : Checked tree [8,2,5,5,6] := by
  refine ⟨plan4892,valid4892,t5_1391choices,?_⟩
  exact check_of_frontier tree 0 t5_1391root t5_1391jobs t5_1391frontier t5_1391all
theorem t5_1392choices : plan4893.choices=[8,2,5,5,7].map (options 5 4) := by rfl


theorem t5_1392part0 : t5_1392jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1392frontier : t5_1392root.frontier 0=t5_1392jobs := by rfl
theorem t5_1392all : t5_1392jobs.all (Job.check tree)=true := by
  simp only [t5_1392jobs,List.all_append,List.all_nil,t5_1392part0,Bool.and_self]
theorem t5_1392checked : Checked tree [8,2,5,5,7] := by
  refine ⟨plan4893,valid4893,t5_1392choices,?_⟩
  exact check_of_frontier tree 0 t5_1392root t5_1392jobs t5_1392frontier t5_1392all
theorem t5_1393choices : plan4894.choices=[8,2,5,5,10].map (options 5 4) := by rfl


theorem t5_1393part0 : t5_1393jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1393frontier : t5_1393root.frontier 0=t5_1393jobs := by rfl
theorem t5_1393all : t5_1393jobs.all (Job.check tree)=true := by
  simp only [t5_1393jobs,List.all_append,List.all_nil,t5_1393part0,Bool.and_self]
theorem t5_1393checked : Checked tree [8,2,5,5,10] := by
  refine ⟨plan4894,valid4894,t5_1393choices,?_⟩
  exact check_of_frontier tree 0 t5_1393root t5_1393jobs t5_1393frontier t5_1393all
theorem t5_1394choices : plan4895.choices=[8,2,5,6,6].map (options 5 4) := by rfl


theorem t5_1394part0 : t5_1394jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1394frontier : t5_1394root.frontier 0=t5_1394jobs := by rfl
theorem t5_1394all : t5_1394jobs.all (Job.check tree)=true := by
  simp only [t5_1394jobs,List.all_append,List.all_nil,t5_1394part0,Bool.and_self]
theorem t5_1394checked : Checked tree [8,2,5,6,6] := by
  refine ⟨plan4895,valid4895,t5_1394choices,?_⟩
  exact check_of_frontier tree 0 t5_1394root t5_1394jobs t5_1394frontier t5_1394all
theorem t5_1395choices : plan4896.choices=[8,2,5,6,7].map (options 5 4) := by rfl


theorem t5_1395part0 : t5_1395jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1395frontier : t5_1395root.frontier 0=t5_1395jobs := by rfl
theorem t5_1395all : t5_1395jobs.all (Job.check tree)=true := by
  simp only [t5_1395jobs,List.all_append,List.all_nil,t5_1395part0,Bool.and_self]
theorem t5_1395checked : Checked tree [8,2,5,6,7] := by
  refine ⟨plan4896,valid4896,t5_1395choices,?_⟩
  exact check_of_frontier tree 0 t5_1395root t5_1395jobs t5_1395frontier t5_1395all
theorem t5_1396choices : plan4897.choices=[8,2,5,6,10].map (options 5 4) := by rfl


theorem t5_1396part0 : t5_1396jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1396frontier : t5_1396root.frontier 0=t5_1396jobs := by rfl
theorem t5_1396all : t5_1396jobs.all (Job.check tree)=true := by
  simp only [t5_1396jobs,List.all_append,List.all_nil,t5_1396part0,Bool.and_self]
theorem t5_1396checked : Checked tree [8,2,5,6,10] := by
  refine ⟨plan4897,valid4897,t5_1396choices,?_⟩
  exact check_of_frontier tree 0 t5_1396root t5_1396jobs t5_1396frontier t5_1396all
theorem t5_1397choices : plan4898.choices=[8,2,5,7,7].map (options 5 4) := by rfl


theorem t5_1397part0 : t5_1397jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1397frontier : t5_1397root.frontier 0=t5_1397jobs := by rfl
theorem t5_1397all : t5_1397jobs.all (Job.check tree)=true := by
  simp only [t5_1397jobs,List.all_append,List.all_nil,t5_1397part0,Bool.and_self]
theorem t5_1397checked : Checked tree [8,2,5,7,7] := by
  refine ⟨plan4898,valid4898,t5_1397choices,?_⟩
  exact check_of_frontier tree 0 t5_1397root t5_1397jobs t5_1397frontier t5_1397all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks040 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1373checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1361checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1374checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1375checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1376checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1377checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1378checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1379checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1380checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1381checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1382checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1362checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1383checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1384checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1385checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1386checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1387checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1388checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1389checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1390checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1391checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1363checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1392checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1393checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1394checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1395checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1396checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1397checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1364checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1365checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1366checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1367checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1368checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1369checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1370checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1371checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1372checked⟩
