-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks008
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:46:06.957699+00:00
-- url     : https://prove2.me/submissions/500f59b4-6a68-4b0a-91c2-7de9ecb14f0e

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks008
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans042
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans043
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

theorem valid481 : plan481.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid482 : plan482.Valid := valid_step _ _ _ valid99 (by decide +kernel)















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







































theorem valid1268 : plan1268.Valid := valid_step _ _ _ valid453 (by decide +kernel)

theorem valid1269 : plan1269.Valid := valid_step _ _ _ valid453 (by decide +kernel)







































































theorem valid1305 : plan1305.Valid := valid_step _ _ _ valid481 (by decide +kernel)

theorem valid1306 : plan1306.Valid := valid_step _ _ _ valid482 (by decide +kernel)





theorem valid1309 : plan1309.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1310 : plan1310.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1311 : plan1311.Valid := valid_step _ _ _ valid465 (by decide +kernel)

theorem valid1312 : plan1312.Valid := valid_step _ _ _ valid466 (by decide +kernel)

theorem valid1313 : plan1313.Valid := valid_step _ _ _ valid476 (by decide +kernel)





theorem valid1316 : plan1316.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1317 : plan1317.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1318 : plan1318.Valid := valid_step _ _ _ valid465 (by decide +kernel)




















































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





































































































theorem valid2547 : plan2547.Valid := valid_step _ _ _ valid1268 (by decide +kernel)

theorem valid2548 : plan2548.Valid := valid_step _ _ _ valid1269 (by decide +kernel)
























































































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





































































































































theorem valid3715 : plan3715.Valid := valid_step _ _ _ valid2547 (by decide +kernel)

theorem valid3716 : plan3716.Valid := valid_step _ _ _ valid2548 (by decide +kernel)
























































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





















theorem valid1355 : plan1355.Valid := valid_step _ _ _ valid490 (by decide +kernel)

theorem valid1356 : plan1356.Valid := valid_step _ _ _ valid491 (by decide +kernel)



theorem valid1358 : plan1358.Valid := valid_step _ _ _ valid493 (by decide +kernel)

theorem valid1359 : plan1359.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1360 : plan1360.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1361 : plan1361.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1362 : plan1362.Valid := valid_step _ _ _ valid497 (by decide +kernel)



theorem valid1364 : plan1364.Valid := valid_step _ _ _ valid499 (by decide +kernel)

theorem valid1365 : plan1365.Valid := valid_step _ _ _ valid500 (by decide +kernel)



theorem valid1367 : plan1367.Valid := valid_step _ _ _ valid502 (by decide +kernel)

theorem valid1368 : plan1368.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1369 : plan1369.Valid := valid_step _ _ _ valid504 (by decide +kernel)

theorem valid1370 : plan1370.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1371 : plan1371.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1372 : plan1372.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1373 : plan1373.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1374 : plan1374.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1375 : plan1375.Valid := valid_step _ _ _ valid504 (by decide +kernel)

theorem valid1376 : plan1376.Valid := valid_step _ _ _ valid497 (by decide +kernel)

















theorem valid1385 : plan1385.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1386 : plan1386.Valid := valid_step _ _ _ valid495 (by decide +kernel)












































































































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











































theorem valid2614 : plan2614.Valid := valid_step _ _ _ valid1305 (by decide +kernel)

theorem valid2615 : plan2615.Valid := valid_step _ _ _ valid1306 (by decide +kernel)



theorem valid2617 : plan2617.Valid := valid_step _ _ _ valid1309 (by decide +kernel)

theorem valid2618 : plan2618.Valid := valid_step _ _ _ valid1310 (by decide +kernel)

theorem valid2619 : plan2619.Valid := valid_step _ _ _ valid1311 (by decide +kernel)

theorem valid2620 : plan2620.Valid := valid_step _ _ _ valid1312 (by decide +kernel)

theorem valid2621 : plan2621.Valid := valid_step _ _ _ valid1313 (by decide +kernel)



theorem valid2623 : plan2623.Valid := valid_step _ _ _ valid1316 (by decide +kernel)

theorem valid2624 : plan2624.Valid := valid_step _ _ _ valid1317 (by decide +kernel)

theorem valid2625 : plan2625.Valid := valid_step _ _ _ valid1318 (by decide +kernel)






























































































































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





































































theorem valid2723 : plan2723.Valid := valid_step _ _ _ valid1355 (by decide +kernel)

theorem valid2724 : plan2724.Valid := valid_step _ _ _ valid1356 (by decide +kernel)



theorem valid2726 : plan2726.Valid := valid_step _ _ _ valid1358 (by decide +kernel)

theorem valid2727 : plan2727.Valid := valid_step _ _ _ valid1359 (by decide +kernel)

theorem valid2728 : plan2728.Valid := valid_step _ _ _ valid1360 (by decide +kernel)

theorem valid2729 : plan2729.Valid := valid_step _ _ _ valid1361 (by decide +kernel)

theorem valid2730 : plan2730.Valid := valid_step _ _ _ valid1362 (by decide +kernel)



theorem valid2732 : plan2732.Valid := valid_step _ _ _ valid1364 (by decide +kernel)

theorem valid2733 : plan2733.Valid := valid_step _ _ _ valid1365 (by decide +kernel)



theorem valid2735 : plan2735.Valid := valid_step _ _ _ valid1367 (by decide +kernel)

theorem valid2736 : plan2736.Valid := valid_step _ _ _ valid1368 (by decide +kernel)

theorem valid2737 : plan2737.Valid := valid_step _ _ _ valid1369 (by decide +kernel)

theorem valid2738 : plan2738.Valid := valid_step _ _ _ valid1370 (by decide +kernel)

theorem valid2739 : plan2739.Valid := valid_step _ _ _ valid1371 (by decide +kernel)

theorem valid2740 : plan2740.Valid := valid_step _ _ _ valid1372 (by decide +kernel)

theorem valid2741 : plan2741.Valid := valid_step _ _ _ valid1373 (by decide +kernel)

theorem valid2742 : plan2742.Valid := valid_step _ _ _ valid1374 (by decide +kernel)

theorem valid2743 : plan2743.Valid := valid_step _ _ _ valid1375 (by decide +kernel)

theorem valid2744 : plan2744.Valid := valid_step _ _ _ valid1376 (by decide +kernel)







theorem valid2748 : plan2748.Valid := valid_step _ _ _ valid1385 (by decide +kernel)

theorem valid2749 : plan2749.Valid := valid_step _ _ _ valid1386 (by decide +kernel)






































































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

























































































































































































theorem valid4125 : plan4125.Valid := valid_step _ _ _ valid2723 (by decide +kernel)

theorem valid4126 : plan4126.Valid := valid_step _ _ _ valid2724 (by decide +kernel)

theorem valid4127 : plan4127.Valid := valid_step _ _ _ valid2726 (by decide +kernel)

theorem valid4128 : plan4128.Valid := valid_step _ _ _ valid2727 (by decide +kernel)
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



























theorem valid3854 : plan3854.Valid := valid_step _ _ _ valid2614 (by decide +kernel)

theorem valid3855 : plan3855.Valid := valid_step _ _ _ valid2615 (by decide +kernel)

theorem valid3856 : plan3856.Valid := valid_step _ _ _ valid2617 (by decide +kernel)

theorem valid3857 : plan3857.Valid := valid_step _ _ _ valid2618 (by decide +kernel)

theorem valid3858 : plan3858.Valid := valid_step _ _ _ valid2619 (by decide +kernel)

theorem valid3859 : plan3859.Valid := valid_step _ _ _ valid2620 (by decide +kernel)

theorem valid3860 : plan3860.Valid := valid_step _ _ _ valid2621 (by decide +kernel)

theorem valid3861 : plan3861.Valid := valid_step _ _ _ valid2623 (by decide +kernel)

theorem valid3862 : plan3862.Valid := valid_step _ _ _ valid2624 (by decide +kernel)

theorem valid3863 : plan3863.Valid := valid_step _ _ _ valid2625 (by decide +kernel)


















































































































































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

theorem valid4129 : plan4129.Valid := valid_step _ _ _ valid2728 (by decide +kernel)

theorem valid4130 : plan4130.Valid := valid_step _ _ _ valid2729 (by decide +kernel)

theorem valid4131 : plan4131.Valid := valid_step _ _ _ valid2730 (by decide +kernel)

theorem valid4132 : plan4132.Valid := valid_step _ _ _ valid2732 (by decide +kernel)

theorem valid4133 : plan4133.Valid := valid_step _ _ _ valid2733 (by decide +kernel)

theorem valid4134 : plan4134.Valid := valid_step _ _ _ valid2735 (by decide +kernel)

theorem valid4135 : plan4135.Valid := valid_step _ _ _ valid2736 (by decide +kernel)

theorem valid4136 : plan4136.Valid := valid_step _ _ _ valid2737 (by decide +kernel)

theorem valid4137 : plan4137.Valid := valid_step _ _ _ valid2738 (by decide +kernel)

theorem valid4138 : plan4138.Valid := valid_step _ _ _ valid2739 (by decide +kernel)

theorem valid4139 : plan4139.Valid := valid_step _ _ _ valid2740 (by decide +kernel)

theorem valid4140 : plan4140.Valid := valid_step _ _ _ valid2741 (by decide +kernel)

theorem valid4141 : plan4141.Valid := valid_step _ _ _ valid2742 (by decide +kernel)

theorem valid4142 : plan4142.Valid := valid_step _ _ _ valid2743 (by decide +kernel)

theorem valid4143 : plan4143.Valid := valid_step _ _ _ valid2744 (by decide +kernel)

theorem valid4144 : plan4144.Valid := valid_step _ _ _ valid2748 (by decide +kernel)

theorem valid4145 : plan4145.Valid := valid_step _ _ _ valid2749 (by decide +kernel)






























































































































































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
theorem t5_359choices : plan3854.choices=[1,2,3,10,7].map (options 5 2) := by rfl


theorem t5_359part0 : t5_359jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_359part1 : t5_359jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_359frontier : t5_359root.frontier 1=t5_359jobs := by rfl
theorem t5_359all : t5_359jobs.all (Job.check tree)=true := by
  simp only [t5_359jobs,List.all_append,List.all_nil,t5_359part0,t5_359part1,Bool.and_self]
theorem t5_359checked : Checked tree [1,2,3,10,7] := by
  refine ⟨plan3854,valid3854,t5_359choices,?_⟩
  exact check_of_frontier tree 1 t5_359root t5_359jobs t5_359frontier t5_359all
theorem t5_360choices : plan3855.choices=[1,2,3,10,10].map (options 5 2) := by rfl


theorem t5_360part0 : t5_360jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_360frontier : t5_360root.frontier 0=t5_360jobs := by rfl
theorem t5_360all : t5_360jobs.all (Job.check tree)=true := by
  simp only [t5_360jobs,List.all_append,List.all_nil,t5_360part0,Bool.and_self]
theorem t5_360checked : Checked tree [1,2,3,10,10] := by
  refine ⟨plan3855,valid3855,t5_360choices,?_⟩
  exact check_of_frontier tree 0 t5_360root t5_360jobs t5_360frontier t5_360all
theorem t5_361choices : plan3715.choices=[1,2,5,3,3].map (options 5 1) := by rfl


theorem t5_361part0 : t5_361jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_361frontier : t5_361root.frontier 0=t5_361jobs := by rfl
theorem t5_361all : t5_361jobs.all (Job.check tree)=true := by
  simp only [t5_361jobs,List.all_append,List.all_nil,t5_361part0,Bool.and_self]
theorem t5_361checked : Checked tree [1,2,5,3,3] := by
  refine ⟨plan3715,valid3715,t5_361choices,?_⟩
  exact check_of_frontier tree 0 t5_361root t5_361jobs t5_361frontier t5_361all
theorem t5_362choices : plan3856.choices=[1,2,5,3,6].map (options 5 2) := by rfl


theorem t5_362part0 : t5_362jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_362frontier : t5_362root.frontier 0=t5_362jobs := by rfl
theorem t5_362all : t5_362jobs.all (Job.check tree)=true := by
  simp only [t5_362jobs,List.all_append,List.all_nil,t5_362part0,Bool.and_self]
theorem t5_362checked : Checked tree [1,2,5,3,6] := by
  refine ⟨plan3856,valid3856,t5_362choices,?_⟩
  exact check_of_frontier tree 0 t5_362root t5_362jobs t5_362frontier t5_362all
theorem t5_363choices : plan3857.choices=[1,2,5,3,7].map (options 5 2) := by rfl


theorem t5_363part0 : t5_363jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_363frontier : t5_363root.frontier 0=t5_363jobs := by rfl
theorem t5_363all : t5_363jobs.all (Job.check tree)=true := by
  simp only [t5_363jobs,List.all_append,List.all_nil,t5_363part0,Bool.and_self]
theorem t5_363checked : Checked tree [1,2,5,3,7] := by
  refine ⟨plan3857,valid3857,t5_363choices,?_⟩
  exact check_of_frontier tree 0 t5_363root t5_363jobs t5_363frontier t5_363all
theorem t5_364choices : plan3858.choices=[1,2,5,3,10].map (options 5 2) := by rfl


theorem t5_364part0 : t5_364jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_364frontier : t5_364root.frontier 0=t5_364jobs := by rfl
theorem t5_364all : t5_364jobs.all (Job.check tree)=true := by
  simp only [t5_364jobs,List.all_append,List.all_nil,t5_364part0,Bool.and_self]
theorem t5_364checked : Checked tree [1,2,5,3,10] := by
  refine ⟨plan3858,valid3858,t5_364choices,?_⟩
  exact check_of_frontier tree 0 t5_364root t5_364jobs t5_364frontier t5_364all
theorem t5_365choices : plan3859.choices=[1,2,5,5,3].map (options 5 2) := by rfl


theorem t5_365part0 : t5_365jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_365frontier : t5_365root.frontier 0=t5_365jobs := by rfl
theorem t5_365all : t5_365jobs.all (Job.check tree)=true := by
  simp only [t5_365jobs,List.all_append,List.all_nil,t5_365part0,Bool.and_self]
theorem t5_365checked : Checked tree [1,2,5,5,3] := by
  refine ⟨plan3859,valid3859,t5_365choices,?_⟩
  exact check_of_frontier tree 0 t5_365root t5_365jobs t5_365frontier t5_365all
theorem t5_366choices : plan4125.choices=[1,2,5,5,6].map (options 5 3) := by rfl


theorem t5_366part0 : t5_366jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_366frontier : t5_366root.frontier 0=t5_366jobs := by rfl
theorem t5_366all : t5_366jobs.all (Job.check tree)=true := by
  simp only [t5_366jobs,List.all_append,List.all_nil,t5_366part0,Bool.and_self]
theorem t5_366checked : Checked tree [1,2,5,5,6] := by
  refine ⟨plan4125,valid4125,t5_366choices,?_⟩
  exact check_of_frontier tree 0 t5_366root t5_366jobs t5_366frontier t5_366all
theorem t5_367choices : plan4126.choices=[1,2,5,5,7].map (options 5 3) := by rfl


theorem t5_367part0 : t5_367jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_367frontier : t5_367root.frontier 0=t5_367jobs := by rfl
theorem t5_367all : t5_367jobs.all (Job.check tree)=true := by
  simp only [t5_367jobs,List.all_append,List.all_nil,t5_367part0,Bool.and_self]
theorem t5_367checked : Checked tree [1,2,5,5,7] := by
  refine ⟨plan4126,valid4126,t5_367choices,?_⟩
  exact check_of_frontier tree 0 t5_367root t5_367jobs t5_367frontier t5_367all
theorem t5_368choices : plan4127.choices=[1,2,5,5,10].map (options 5 3) := by rfl


theorem t5_368part0 : t5_368jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_368frontier : t5_368root.frontier 0=t5_368jobs := by rfl
theorem t5_368all : t5_368jobs.all (Job.check tree)=true := by
  simp only [t5_368jobs,List.all_append,List.all_nil,t5_368part0,Bool.and_self]
theorem t5_368checked : Checked tree [1,2,5,5,10] := by
  refine ⟨plan4127,valid4127,t5_368choices,?_⟩
  exact check_of_frontier tree 0 t5_368root t5_368jobs t5_368frontier t5_368all
theorem t5_369choices : plan4128.choices=[1,2,5,6,6].map (options 5 3) := by rfl


theorem t5_369part0 : t5_369jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_369frontier : t5_369root.frontier 0=t5_369jobs := by rfl
theorem t5_369all : t5_369jobs.all (Job.check tree)=true := by
  simp only [t5_369jobs,List.all_append,List.all_nil,t5_369part0,Bool.and_self]
theorem t5_369checked : Checked tree [1,2,5,6,6] := by
  refine ⟨plan4128,valid4128,t5_369choices,?_⟩
  exact check_of_frontier tree 0 t5_369root t5_369jobs t5_369frontier t5_369all
theorem t5_370choices : plan4129.choices=[1,2,5,6,7].map (options 5 3) := by rfl


theorem t5_370part0 : t5_370jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_370frontier : t5_370root.frontier 0=t5_370jobs := by rfl
theorem t5_370all : t5_370jobs.all (Job.check tree)=true := by
  simp only [t5_370jobs,List.all_append,List.all_nil,t5_370part0,Bool.and_self]
theorem t5_370checked : Checked tree [1,2,5,6,7] := by
  refine ⟨plan4129,valid4129,t5_370choices,?_⟩
  exact check_of_frontier tree 0 t5_370root t5_370jobs t5_370frontier t5_370all
theorem t5_371choices : plan4130.choices=[1,2,5,6,10].map (options 5 3) := by rfl


theorem t5_371part0 : t5_371jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_371frontier : t5_371root.frontier 0=t5_371jobs := by rfl
theorem t5_371all : t5_371jobs.all (Job.check tree)=true := by
  simp only [t5_371jobs,List.all_append,List.all_nil,t5_371part0,Bool.and_self]
theorem t5_371checked : Checked tree [1,2,5,6,10] := by
  refine ⟨plan4130,valid4130,t5_371choices,?_⟩
  exact check_of_frontier tree 0 t5_371root t5_371jobs t5_371frontier t5_371all
theorem t5_372choices : plan4131.choices=[1,2,5,7,7].map (options 5 3) := by rfl


theorem t5_372part0 : t5_372jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_372frontier : t5_372root.frontier 0=t5_372jobs := by rfl
theorem t5_372all : t5_372jobs.all (Job.check tree)=true := by
  simp only [t5_372jobs,List.all_append,List.all_nil,t5_372part0,Bool.and_self]
theorem t5_372checked : Checked tree [1,2,5,7,7] := by
  refine ⟨plan4131,valid4131,t5_372choices,?_⟩
  exact check_of_frontier tree 0 t5_372root t5_372jobs t5_372frontier t5_372all
theorem t5_373choices : plan3860.choices=[1,2,5,9,3].map (options 5 2) := by rfl


theorem t5_373part0 : t5_373jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_373frontier : t5_373root.frontier 0=t5_373jobs := by rfl
theorem t5_373all : t5_373jobs.all (Job.check tree)=true := by
  simp only [t5_373jobs,List.all_append,List.all_nil,t5_373part0,Bool.and_self]
theorem t5_373checked : Checked tree [1,2,5,9,3] := by
  refine ⟨plan3860,valid3860,t5_373choices,?_⟩
  exact check_of_frontier tree 0 t5_373root t5_373jobs t5_373frontier t5_373all
theorem t5_374choices : plan4132.choices=[1,2,5,9,6].map (options 5 3) := by rfl


theorem t5_374part0 : t5_374jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_374frontier : t5_374root.frontier 0=t5_374jobs := by rfl
theorem t5_374all : t5_374jobs.all (Job.check tree)=true := by
  simp only [t5_374jobs,List.all_append,List.all_nil,t5_374part0,Bool.and_self]
theorem t5_374checked : Checked tree [1,2,5,9,6] := by
  refine ⟨plan4132,valid4132,t5_374choices,?_⟩
  exact check_of_frontier tree 0 t5_374root t5_374jobs t5_374frontier t5_374all
theorem t5_375choices : plan4133.choices=[1,2,5,9,7].map (options 5 3) := by rfl


theorem t5_375part0 : t5_375jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_375frontier : t5_375root.frontier 0=t5_375jobs := by rfl
theorem t5_375all : t5_375jobs.all (Job.check tree)=true := by
  simp only [t5_375jobs,List.all_append,List.all_nil,t5_375part0,Bool.and_self]
theorem t5_375checked : Checked tree [1,2,5,9,7] := by
  refine ⟨plan4133,valid4133,t5_375choices,?_⟩
  exact check_of_frontier tree 0 t5_375root t5_375jobs t5_375frontier t5_375all
theorem t5_376choices : plan4134.choices=[1,2,5,9,10].map (options 5 3) := by rfl


theorem t5_376part0 : t5_376jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_376frontier : t5_376root.frontier 0=t5_376jobs := by rfl
theorem t5_376all : t5_376jobs.all (Job.check tree)=true := by
  simp only [t5_376jobs,List.all_append,List.all_nil,t5_376part0,Bool.and_self]
theorem t5_376checked : Checked tree [1,2,5,9,10] := by
  refine ⟨plan4134,valid4134,t5_376choices,?_⟩
  exact check_of_frontier tree 0 t5_376root t5_376jobs t5_376frontier t5_376all
theorem t5_377choices : plan4135.choices=[1,2,5,10,7].map (options 5 3) := by rfl


theorem t5_377part0 : t5_377jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_377frontier : t5_377root.frontier 0=t5_377jobs := by rfl
theorem t5_377all : t5_377jobs.all (Job.check tree)=true := by
  simp only [t5_377jobs,List.all_append,List.all_nil,t5_377part0,Bool.and_self]
theorem t5_377checked : Checked tree [1,2,5,10,7] := by
  refine ⟨plan4135,valid4135,t5_377choices,?_⟩
  exact check_of_frontier tree 0 t5_377root t5_377jobs t5_377frontier t5_377all
theorem t5_378choices : plan4136.choices=[1,2,5,10,10].map (options 5 3) := by rfl


theorem t5_378part0 : t5_378jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_378frontier : t5_378root.frontier 0=t5_378jobs := by rfl
theorem t5_378all : t5_378jobs.all (Job.check tree)=true := by
  simp only [t5_378jobs,List.all_append,List.all_nil,t5_378part0,Bool.and_self]
theorem t5_378checked : Checked tree [1,2,5,10,10] := by
  refine ⟨plan4136,valid4136,t5_378choices,?_⟩
  exact check_of_frontier tree 0 t5_378root t5_378jobs t5_378frontier t5_378all
theorem t5_379choices : plan4137.choices=[1,2,6,6,6].map (options 5 3) := by rfl


theorem t5_379part0 : t5_379jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_379frontier : t5_379root.frontier 0=t5_379jobs := by rfl
theorem t5_379all : t5_379jobs.all (Job.check tree)=true := by
  simp only [t5_379jobs,List.all_append,List.all_nil,t5_379part0,Bool.and_self]
theorem t5_379checked : Checked tree [1,2,6,6,6] := by
  refine ⟨plan4137,valid4137,t5_379choices,?_⟩
  exact check_of_frontier tree 0 t5_379root t5_379jobs t5_379frontier t5_379all
theorem t5_380choices : plan4138.choices=[1,2,6,6,7].map (options 5 3) := by rfl


theorem t5_380part0 : t5_380jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_380frontier : t5_380root.frontier 0=t5_380jobs := by rfl
theorem t5_380all : t5_380jobs.all (Job.check tree)=true := by
  simp only [t5_380jobs,List.all_append,List.all_nil,t5_380part0,Bool.and_self]
theorem t5_380checked : Checked tree [1,2,6,6,7] := by
  refine ⟨plan4138,valid4138,t5_380choices,?_⟩
  exact check_of_frontier tree 0 t5_380root t5_380jobs t5_380frontier t5_380all
theorem t5_381choices : plan4139.choices=[1,2,6,6,10].map (options 5 3) := by rfl


theorem t5_381part0 : t5_381jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_381frontier : t5_381root.frontier 0=t5_381jobs := by rfl
theorem t5_381all : t5_381jobs.all (Job.check tree)=true := by
  simp only [t5_381jobs,List.all_append,List.all_nil,t5_381part0,Bool.and_self]
theorem t5_381checked : Checked tree [1,2,6,6,10] := by
  refine ⟨plan4139,valid4139,t5_381choices,?_⟩
  exact check_of_frontier tree 0 t5_381root t5_381jobs t5_381frontier t5_381all
theorem t5_382choices : plan4140.choices=[1,2,6,7,7].map (options 5 3) := by rfl


theorem t5_382part0 : t5_382jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_382frontier : t5_382root.frontier 0=t5_382jobs := by rfl
theorem t5_382all : t5_382jobs.all (Job.check tree)=true := by
  simp only [t5_382jobs,List.all_append,List.all_nil,t5_382part0,Bool.and_self]
theorem t5_382checked : Checked tree [1,2,6,7,7] := by
  refine ⟨plan4140,valid4140,t5_382choices,?_⟩
  exact check_of_frontier tree 0 t5_382root t5_382jobs t5_382frontier t5_382all
theorem t5_383choices : plan4141.choices=[1,2,6,10,7].map (options 5 3) := by rfl


theorem t5_383part0 : t5_383jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_383part1 : t5_383jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_383frontier : t5_383root.frontier 1=t5_383jobs := by rfl
theorem t5_383all : t5_383jobs.all (Job.check tree)=true := by
  simp only [t5_383jobs,List.all_append,List.all_nil,t5_383part0,t5_383part1,Bool.and_self]
theorem t5_383checked : Checked tree [1,2,6,10,7] := by
  refine ⟨plan4141,valid4141,t5_383choices,?_⟩
  exact check_of_frontier tree 1 t5_383root t5_383jobs t5_383frontier t5_383all
theorem t5_384choices : plan4142.choices=[1,2,6,10,10].map (options 5 3) := by rfl


theorem t5_384part0 : t5_384jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_384frontier : t5_384root.frontier 0=t5_384jobs := by rfl
theorem t5_384all : t5_384jobs.all (Job.check tree)=true := by
  simp only [t5_384jobs,List.all_append,List.all_nil,t5_384part0,Bool.and_self]
theorem t5_384checked : Checked tree [1,2,6,10,10] := by
  refine ⟨plan4142,valid4142,t5_384choices,?_⟩
  exact check_of_frontier tree 0 t5_384root t5_384jobs t5_384frontier t5_384all
theorem t5_385choices : plan4143.choices=[1,2,7,7,7].map (options 5 3) := by rfl


theorem t5_385part0 : t5_385jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_385frontier : t5_385root.frontier 0=t5_385jobs := by rfl
theorem t5_385all : t5_385jobs.all (Job.check tree)=true := by
  simp only [t5_385jobs,List.all_append,List.all_nil,t5_385part0,Bool.and_self]
theorem t5_385checked : Checked tree [1,2,7,7,7] := by
  refine ⟨plan4143,valid4143,t5_385choices,?_⟩
  exact check_of_frontier tree 0 t5_385root t5_385jobs t5_385frontier t5_385all
theorem t5_386choices : plan3716.choices=[1,2,9,3,3].map (options 5 1) := by rfl


theorem t5_386part0 : t5_386jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_386frontier : t5_386root.frontier 0=t5_386jobs := by rfl
theorem t5_386all : t5_386jobs.all (Job.check tree)=true := by
  simp only [t5_386jobs,List.all_append,List.all_nil,t5_386part0,Bool.and_self]
theorem t5_386checked : Checked tree [1,2,9,3,3] := by
  refine ⟨plan3716,valid3716,t5_386choices,?_⟩
  exact check_of_frontier tree 0 t5_386root t5_386jobs t5_386frontier t5_386all
theorem t5_387choices : plan3861.choices=[1,2,9,3,6].map (options 5 2) := by rfl


theorem t5_387part0 : t5_387jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_387frontier : t5_387root.frontier 0=t5_387jobs := by rfl
theorem t5_387all : t5_387jobs.all (Job.check tree)=true := by
  simp only [t5_387jobs,List.all_append,List.all_nil,t5_387part0,Bool.and_self]
theorem t5_387checked : Checked tree [1,2,9,3,6] := by
  refine ⟨plan3861,valid3861,t5_387choices,?_⟩
  exact check_of_frontier tree 0 t5_387root t5_387jobs t5_387frontier t5_387all
theorem t5_388choices : plan3862.choices=[1,2,9,3,7].map (options 5 2) := by rfl


theorem t5_388part0 : t5_388jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_388frontier : t5_388root.frontier 0=t5_388jobs := by rfl
theorem t5_388all : t5_388jobs.all (Job.check tree)=true := by
  simp only [t5_388jobs,List.all_append,List.all_nil,t5_388part0,Bool.and_self]
theorem t5_388checked : Checked tree [1,2,9,3,7] := by
  refine ⟨plan3862,valid3862,t5_388choices,?_⟩
  exact check_of_frontier tree 0 t5_388root t5_388jobs t5_388frontier t5_388all
theorem t5_389choices : plan3863.choices=[1,2,9,3,10].map (options 5 2) := by rfl


theorem t5_389part0 : t5_389jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_389frontier : t5_389root.frontier 0=t5_389jobs := by rfl
theorem t5_389all : t5_389jobs.all (Job.check tree)=true := by
  simp only [t5_389jobs,List.all_append,List.all_nil,t5_389part0,Bool.and_self]
theorem t5_389checked : Checked tree [1,2,9,3,10] := by
  refine ⟨plan3863,valid3863,t5_389choices,?_⟩
  exact check_of_frontier tree 0 t5_389root t5_389jobs t5_389frontier t5_389all
theorem t5_390choices : plan4144.choices=[1,2,9,6,6].map (options 5 3) := by rfl


theorem t5_390part0 : t5_390jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_390frontier : t5_390root.frontier 0=t5_390jobs := by rfl
theorem t5_390all : t5_390jobs.all (Job.check tree)=true := by
  simp only [t5_390jobs,List.all_append,List.all_nil,t5_390part0,Bool.and_self]
theorem t5_390checked : Checked tree [1,2,9,6,6] := by
  refine ⟨plan4144,valid4144,t5_390choices,?_⟩
  exact check_of_frontier tree 0 t5_390root t5_390jobs t5_390frontier t5_390all
theorem t5_391choices : plan4145.choices=[1,2,9,6,7].map (options 5 3) := by rfl


theorem t5_391part0 : t5_391jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_391frontier : t5_391root.frontier 0=t5_391jobs := by rfl
theorem t5_391all : t5_391jobs.all (Job.check tree)=true := by
  simp only [t5_391jobs,List.all_append,List.all_nil,t5_391part0,Bool.and_self]
theorem t5_391checked : Checked tree [1,2,9,6,7] := by
  refine ⟨plan4145,valid4145,t5_391choices,?_⟩
  exact check_of_frontier tree 0 t5_391root t5_391jobs t5_391frontier t5_391all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks008 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_371checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_372checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_373checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_374checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_359checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_375checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_376checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_377checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_378checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_379checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_380checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_381checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_382checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_383checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_384checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_360checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_385checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_386checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_387checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_388checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_389checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_390checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_391checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_361checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_362checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_363checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_364checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_365checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_366checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_367checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_368checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_369checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_370checked⟩
