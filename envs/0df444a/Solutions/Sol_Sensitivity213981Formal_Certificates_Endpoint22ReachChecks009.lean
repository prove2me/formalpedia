-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks009
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:44:50.912263+00:00
-- url     : https://prove2.me/submissions/27815288-234c-4cb0-ad73-7e0d9b65dd4b

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks009
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













































































































































































theorem valid87 : plan87.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid90 : plan90.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid91 : plan91.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid93 : plan93.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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



























































































































theorem valid446 : plan446.Valid := valid_step _ _ _ valid87 (by decide +kernel)















theorem valid454 : plan454.Valid := valid_step _ _ _ valid90 (by decide +kernel)

theorem valid455 : plan455.Valid := valid_step _ _ _ valid91 (by decide +kernel)

theorem valid456 : plan456.Valid := valid_step _ _ _ valid93 (by decide +kernel)































theorem valid472 : plan472.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid473 : plan473.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid474 : plan474.Valid := valid_step _ _ _ valid99 (by decide +kernel)

theorem valid475 : plan475.Valid := valid_step _ _ _ valid97 (by decide +kernel)

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



theorem valid1250 : plan1250.Valid := valid_step _ _ _ valid446 (by decide +kernel)





























theorem valid1265 : plan1265.Valid := valid_step _ _ _ valid454 (by decide +kernel)

theorem valid1266 : plan1266.Valid := valid_step _ _ _ valid455 (by decide +kernel)

theorem valid1267 : plan1267.Valid := valid_step _ _ _ valid456 (by decide +kernel)



































































theorem valid1301 : plan1301.Valid := valid_step _ _ _ valid472 (by decide +kernel)

theorem valid1302 : plan1302.Valid := valid_step _ _ _ valid473 (by decide +kernel)

theorem valid1303 : plan1303.Valid := valid_step _ _ _ valid474 (by decide +kernel)

theorem valid1304 : plan1304.Valid := valid_step _ _ _ valid475 (by decide +kernel)

theorem valid1305 : plan1305.Valid := valid_step _ _ _ valid481 (by decide +kernel)

theorem valid1306 : plan1306.Valid := valid_step _ _ _ valid482 (by decide +kernel)

























theorem valid1319 : plan1319.Valid := valid_step _ _ _ valid476 (by decide +kernel)


















































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















































theorem valid2520 : plan2520.Valid := valid_step _ _ _ valid1250 (by decide +kernel)



























































theorem valid2550 : plan2550.Valid := valid_step _ _ _ valid1265 (by decide +kernel)

theorem valid2551 : plan2551.Valid := valid_step _ _ _ valid1266 (by decide +kernel)

theorem valid2552 : plan2552.Valid := valid_step _ _ _ valid1267 (by decide +kernel)
















































































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





































theorem valid3667 : plan3667.Valid := valid_step _ _ _ valid2520 (by decide +kernel)



































































































theorem valid3717 : plan3717.Valid := valid_step _ _ _ valid2550 (by decide +kernel)

theorem valid3718 : plan3718.Valid := valid_step _ _ _ valid2551 (by decide +kernel)

theorem valid3719 : plan3719.Valid := valid_step _ _ _ valid2552 (by decide +kernel)


















































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



















































theorem valid1370 : plan1370.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1371 : plan1371.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1372 : plan1372.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1373 : plan1373.Valid := valid_step _ _ _ valid497 (by decide +kernel)



























theorem valid1387 : plan1387.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1388 : plan1388.Valid := valid_step _ _ _ valid497 (by decide +kernel)



theorem valid1390 : plan1390.Valid := valid_step _ _ _ valid499 (by decide +kernel)

theorem valid1391 : plan1391.Valid := valid_step _ _ _ valid500 (by decide +kernel)



theorem valid1393 : plan1393.Valid := valid_step _ _ _ valid502 (by decide +kernel)

theorem valid1394 : plan1394.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1395 : plan1395.Valid := valid_step _ _ _ valid504 (by decide +kernel)

theorem valid1396 : plan1396.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1397 : plan1397.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1398 : plan1398.Valid := valid_step _ _ _ valid504 (by decide +kernel)




















































































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



































































theorem valid2626 : plan2626.Valid := valid_step _ _ _ valid1319 (by decide +kernel)







theorem valid2630 : plan2630.Valid := valid_step _ _ _ valid1301 (by decide +kernel)

theorem valid2631 : plan2631.Valid := valid_step _ _ _ valid1302 (by decide +kernel)

theorem valid2632 : plan2632.Valid := valid_step _ _ _ valid1303 (by decide +kernel)

theorem valid2633 : plan2633.Valid := valid_step _ _ _ valid1304 (by decide +kernel)

theorem valid2634 : plan2634.Valid := valid_step _ _ _ valid1305 (by decide +kernel)

theorem valid2635 : plan2635.Valid := valid_step _ _ _ valid1306 (by decide +kernel)










































































































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



























































































































theorem valid2750 : plan2750.Valid := valid_step _ _ _ valid1387 (by decide +kernel)

theorem valid2751 : plan2751.Valid := valid_step _ _ _ valid1388 (by decide +kernel)



theorem valid2753 : plan2753.Valid := valid_step _ _ _ valid1390 (by decide +kernel)

theorem valid2754 : plan2754.Valid := valid_step _ _ _ valid1391 (by decide +kernel)



theorem valid2756 : plan2756.Valid := valid_step _ _ _ valid1393 (by decide +kernel)

theorem valid2757 : plan2757.Valid := valid_step _ _ _ valid1394 (by decide +kernel)

theorem valid2758 : plan2758.Valid := valid_step _ _ _ valid1395 (by decide +kernel)

theorem valid2759 : plan2759.Valid := valid_step _ _ _ valid1396 (by decide +kernel)

theorem valid2760 : plan2760.Valid := valid_step _ _ _ valid1397 (by decide +kernel)

theorem valid2761 : plan2761.Valid := valid_step _ _ _ valid1398 (by decide +kernel)













theorem valid2768 : plan2768.Valid := valid_step _ _ _ valid1370 (by decide +kernel)

theorem valid2769 : plan2769.Valid := valid_step _ _ _ valid1371 (by decide +kernel)

theorem valid2770 : plan2770.Valid := valid_step _ _ _ valid1372 (by decide +kernel)

theorem valid2771 : plan2771.Valid := valid_step _ _ _ valid1373 (by decide +kernel)


























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















































theorem valid3864 : plan3864.Valid := valid_step _ _ _ valid2626 (by decide +kernel)

theorem valid3865 : plan3865.Valid := valid_step _ _ _ valid2630 (by decide +kernel)

theorem valid3866 : plan3866.Valid := valid_step _ _ _ valid2631 (by decide +kernel)

theorem valid3867 : plan3867.Valid := valid_step _ _ _ valid2632 (by decide +kernel)

theorem valid3868 : plan3868.Valid := valid_step _ _ _ valid2633 (by decide +kernel)

theorem valid3869 : plan3869.Valid := valid_step _ _ _ valid2634 (by decide +kernel)

theorem valid3870 : plan3870.Valid := valid_step _ _ _ valid2635 (by decide +kernel)




































































































































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



































theorem valid4146 : plan4146.Valid := valid_step _ _ _ valid2750 (by decide +kernel)

theorem valid4147 : plan4147.Valid := valid_step _ _ _ valid2751 (by decide +kernel)

theorem valid4148 : plan4148.Valid := valid_step _ _ _ valid2753 (by decide +kernel)

theorem valid4149 : plan4149.Valid := valid_step _ _ _ valid2754 (by decide +kernel)

theorem valid4150 : plan4150.Valid := valid_step _ _ _ valid2756 (by decide +kernel)

theorem valid4151 : plan4151.Valid := valid_step _ _ _ valid2757 (by decide +kernel)

theorem valid4152 : plan4152.Valid := valid_step _ _ _ valid2758 (by decide +kernel)

theorem valid4153 : plan4153.Valid := valid_step _ _ _ valid2759 (by decide +kernel)

theorem valid4154 : plan4154.Valid := valid_step _ _ _ valid2760 (by decide +kernel)

theorem valid4155 : plan4155.Valid := valid_step _ _ _ valid2761 (by decide +kernel)

theorem valid4156 : plan4156.Valid := valid_step _ _ _ valid2768 (by decide +kernel)

theorem valid4157 : plan4157.Valid := valid_step _ _ _ valid2769 (by decide +kernel)

theorem valid4158 : plan4158.Valid := valid_step _ _ _ valid2770 (by decide +kernel)

theorem valid4159 : plan4159.Valid := valid_step _ _ _ valid2771 (by decide +kernel)


































































































































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
theorem t5_392choices : plan4146.choices=[1,2,9,6,10].map (options 5 3) := by rfl


theorem t5_392part0 : t5_392jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_392frontier : t5_392root.frontier 0=t5_392jobs := by rfl
theorem t5_392all : t5_392jobs.all (Job.check tree)=true := by
  simp only [t5_392jobs,List.all_append,List.all_nil,t5_392part0,Bool.and_self]
theorem t5_392checked : Checked tree [1,2,9,6,10] := by
  refine ⟨plan4146,valid4146,t5_392choices,?_⟩
  exact check_of_frontier tree 0 t5_392root t5_392jobs t5_392frontier t5_392all
theorem t5_393choices : plan4147.choices=[1,2,9,7,7].map (options 5 3) := by rfl


theorem t5_393part0 : t5_393jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_393frontier : t5_393root.frontier 0=t5_393jobs := by rfl
theorem t5_393all : t5_393jobs.all (Job.check tree)=true := by
  simp only [t5_393jobs,List.all_append,List.all_nil,t5_393part0,Bool.and_self]
theorem t5_393checked : Checked tree [1,2,9,7,7] := by
  refine ⟨plan4147,valid4147,t5_393choices,?_⟩
  exact check_of_frontier tree 0 t5_393root t5_393jobs t5_393frontier t5_393all
theorem t5_394choices : plan3864.choices=[1,2,9,9,3].map (options 5 2) := by rfl


theorem t5_394part0 : t5_394jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_394frontier : t5_394root.frontier 0=t5_394jobs := by rfl
theorem t5_394all : t5_394jobs.all (Job.check tree)=true := by
  simp only [t5_394jobs,List.all_append,List.all_nil,t5_394part0,Bool.and_self]
theorem t5_394checked : Checked tree [1,2,9,9,3] := by
  refine ⟨plan3864,valid3864,t5_394choices,?_⟩
  exact check_of_frontier tree 0 t5_394root t5_394jobs t5_394frontier t5_394all
theorem t5_395choices : plan4148.choices=[1,2,9,9,6].map (options 5 3) := by rfl


theorem t5_395part0 : t5_395jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_395frontier : t5_395root.frontier 0=t5_395jobs := by rfl
theorem t5_395all : t5_395jobs.all (Job.check tree)=true := by
  simp only [t5_395jobs,List.all_append,List.all_nil,t5_395part0,Bool.and_self]
theorem t5_395checked : Checked tree [1,2,9,9,6] := by
  refine ⟨plan4148,valid4148,t5_395choices,?_⟩
  exact check_of_frontier tree 0 t5_395root t5_395jobs t5_395frontier t5_395all
theorem t5_396choices : plan4149.choices=[1,2,9,9,7].map (options 5 3) := by rfl


theorem t5_396part0 : t5_396jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_396frontier : t5_396root.frontier 0=t5_396jobs := by rfl
theorem t5_396all : t5_396jobs.all (Job.check tree)=true := by
  simp only [t5_396jobs,List.all_append,List.all_nil,t5_396part0,Bool.and_self]
theorem t5_396checked : Checked tree [1,2,9,9,7] := by
  refine ⟨plan4149,valid4149,t5_396choices,?_⟩
  exact check_of_frontier tree 0 t5_396root t5_396jobs t5_396frontier t5_396all
theorem t5_397choices : plan4150.choices=[1,2,9,9,10].map (options 5 3) := by rfl


theorem t5_397part0 : t5_397jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_397frontier : t5_397root.frontier 0=t5_397jobs := by rfl
theorem t5_397all : t5_397jobs.all (Job.check tree)=true := by
  simp only [t5_397jobs,List.all_append,List.all_nil,t5_397part0,Bool.and_self]
theorem t5_397checked : Checked tree [1,2,9,9,10] := by
  refine ⟨plan4150,valid4150,t5_397choices,?_⟩
  exact check_of_frontier tree 0 t5_397root t5_397jobs t5_397frontier t5_397all
theorem t5_398choices : plan4151.choices=[1,2,9,10,7].map (options 5 3) := by rfl


theorem t5_398part0 : t5_398jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_398frontier : t5_398root.frontier 0=t5_398jobs := by rfl
theorem t5_398all : t5_398jobs.all (Job.check tree)=true := by
  simp only [t5_398jobs,List.all_append,List.all_nil,t5_398part0,Bool.and_self]
theorem t5_398checked : Checked tree [1,2,9,10,7] := by
  refine ⟨plan4151,valid4151,t5_398choices,?_⟩
  exact check_of_frontier tree 0 t5_398root t5_398jobs t5_398frontier t5_398all
theorem t5_399choices : plan4152.choices=[1,2,9,10,10].map (options 5 3) := by rfl


theorem t5_399part0 : t5_399jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_399frontier : t5_399root.frontier 0=t5_399jobs := by rfl
theorem t5_399all : t5_399jobs.all (Job.check tree)=true := by
  simp only [t5_399jobs,List.all_append,List.all_nil,t5_399part0,Bool.and_self]
theorem t5_399checked : Checked tree [1,2,9,10,10] := by
  refine ⟨plan4152,valid4152,t5_399choices,?_⟩
  exact check_of_frontier tree 0 t5_399root t5_399jobs t5_399frontier t5_399all
theorem t5_400choices : plan4153.choices=[1,2,10,7,7].map (options 5 3) := by rfl


theorem t5_400part0 : t5_400jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_400frontier : t5_400root.frontier 0=t5_400jobs := by rfl
theorem t5_400all : t5_400jobs.all (Job.check tree)=true := by
  simp only [t5_400jobs,List.all_append,List.all_nil,t5_400part0,Bool.and_self]
theorem t5_400checked : Checked tree [1,2,10,7,7] := by
  refine ⟨plan4153,valid4153,t5_400choices,?_⟩
  exact check_of_frontier tree 0 t5_400root t5_400jobs t5_400frontier t5_400all
theorem t5_401choices : plan4154.choices=[1,2,10,10,7].map (options 5 3) := by rfl


theorem t5_401part0 : t5_401jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_401frontier : t5_401root.frontier 0=t5_401jobs := by rfl
theorem t5_401all : t5_401jobs.all (Job.check tree)=true := by
  simp only [t5_401jobs,List.all_append,List.all_nil,t5_401part0,Bool.and_self]
theorem t5_401checked : Checked tree [1,2,10,10,7] := by
  refine ⟨plan4154,valid4154,t5_401choices,?_⟩
  exact check_of_frontier tree 0 t5_401root t5_401jobs t5_401frontier t5_401all
theorem t5_402choices : plan4155.choices=[1,2,10,10,10].map (options 5 3) := by rfl


theorem t5_402part0 : t5_402jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_402frontier : t5_402root.frontier 0=t5_402jobs := by rfl
theorem t5_402all : t5_402jobs.all (Job.check tree)=true := by
  simp only [t5_402jobs,List.all_append,List.all_nil,t5_402part0,Bool.and_self]
theorem t5_402checked : Checked tree [1,2,10,10,10] := by
  refine ⟨plan4155,valid4155,t5_402choices,?_⟩
  exact check_of_frontier tree 0 t5_402root t5_402jobs t5_402frontier t5_402all
theorem t5_403choices : plan3667.choices=[1,3,3,3,3].map (options 5 0) := by rfl


theorem t5_403part0 : t5_403jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_403frontier : t5_403root.frontier 0=t5_403jobs := by rfl
theorem t5_403all : t5_403jobs.all (Job.check tree)=true := by
  simp only [t5_403jobs,List.all_append,List.all_nil,t5_403part0,Bool.and_self]
theorem t5_403checked : Checked tree [1,3,3,3,3] := by
  refine ⟨plan3667,valid3667,t5_403choices,?_⟩
  exact check_of_frontier tree 0 t5_403root t5_403jobs t5_403frontier t5_403all
theorem t5_404choices : plan3717.choices=[1,3,3,3,6].map (options 5 1) := by rfl


theorem t5_404part0 : t5_404jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_404frontier : t5_404root.frontier 0=t5_404jobs := by rfl
theorem t5_404all : t5_404jobs.all (Job.check tree)=true := by
  simp only [t5_404jobs,List.all_append,List.all_nil,t5_404part0,Bool.and_self]
theorem t5_404checked : Checked tree [1,3,3,3,6] := by
  refine ⟨plan3717,valid3717,t5_404choices,?_⟩
  exact check_of_frontier tree 0 t5_404root t5_404jobs t5_404frontier t5_404all
theorem t5_405choices : plan3718.choices=[1,3,3,3,7].map (options 5 1) := by rfl


theorem t5_405part0 : t5_405jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_405frontier : t5_405root.frontier 0=t5_405jobs := by rfl
theorem t5_405all : t5_405jobs.all (Job.check tree)=true := by
  simp only [t5_405jobs,List.all_append,List.all_nil,t5_405part0,Bool.and_self]
theorem t5_405checked : Checked tree [1,3,3,3,7] := by
  refine ⟨plan3718,valid3718,t5_405choices,?_⟩
  exact check_of_frontier tree 0 t5_405root t5_405jobs t5_405frontier t5_405all
theorem t5_406choices : plan3719.choices=[1,3,3,3,10].map (options 5 1) := by rfl


theorem t5_406part0 : t5_406jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_406frontier : t5_406root.frontier 0=t5_406jobs := by rfl
theorem t5_406all : t5_406jobs.all (Job.check tree)=true := by
  simp only [t5_406jobs,List.all_append,List.all_nil,t5_406part0,Bool.and_self]
theorem t5_406checked : Checked tree [1,3,3,3,10] := by
  refine ⟨plan3719,valid3719,t5_406choices,?_⟩
  exact check_of_frontier tree 0 t5_406root t5_406jobs t5_406frontier t5_406all
theorem t5_407choices : plan3865.choices=[1,3,3,6,6].map (options 5 2) := by rfl


theorem t5_407part0 : t5_407jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_407frontier : t5_407root.frontier 0=t5_407jobs := by rfl
theorem t5_407all : t5_407jobs.all (Job.check tree)=true := by
  simp only [t5_407jobs,List.all_append,List.all_nil,t5_407part0,Bool.and_self]
theorem t5_407checked : Checked tree [1,3,3,6,6] := by
  refine ⟨plan3865,valid3865,t5_407choices,?_⟩
  exact check_of_frontier tree 0 t5_407root t5_407jobs t5_407frontier t5_407all
theorem t5_408choices : plan3866.choices=[1,3,3,6,7].map (options 5 2) := by rfl


theorem t5_408part0 : t5_408jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_408part1 : t5_408jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_408frontier : t5_408root.frontier 1=t5_408jobs := by rfl
theorem t5_408all : t5_408jobs.all (Job.check tree)=true := by
  simp only [t5_408jobs,List.all_append,List.all_nil,t5_408part0,t5_408part1,Bool.and_self]
theorem t5_408checked : Checked tree [1,3,3,6,7] := by
  refine ⟨plan3866,valid3866,t5_408choices,?_⟩
  exact check_of_frontier tree 1 t5_408root t5_408jobs t5_408frontier t5_408all
theorem t5_409choices : plan3867.choices=[1,3,3,6,10].map (options 5 2) := by rfl


theorem t5_409part0 : t5_409jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_409frontier : t5_409root.frontier 0=t5_409jobs := by rfl
theorem t5_409all : t5_409jobs.all (Job.check tree)=true := by
  simp only [t5_409jobs,List.all_append,List.all_nil,t5_409part0,Bool.and_self]
theorem t5_409checked : Checked tree [1,3,3,6,10] := by
  refine ⟨plan3867,valid3867,t5_409choices,?_⟩
  exact check_of_frontier tree 0 t5_409root t5_409jobs t5_409frontier t5_409all
theorem t5_410choices : plan3868.choices=[1,3,3,7,7].map (options 5 2) := by rfl


theorem t5_410part0 : t5_410jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_410frontier : t5_410root.frontier 0=t5_410jobs := by rfl
theorem t5_410all : t5_410jobs.all (Job.check tree)=true := by
  simp only [t5_410jobs,List.all_append,List.all_nil,t5_410part0,Bool.and_self]
theorem t5_410checked : Checked tree [1,3,3,7,7] := by
  refine ⟨plan3868,valid3868,t5_410choices,?_⟩
  exact check_of_frontier tree 0 t5_410root t5_410jobs t5_410frontier t5_410all
theorem t5_411choices : plan3869.choices=[1,3,3,10,7].map (options 5 2) := by rfl


theorem t5_411part0 : t5_411jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_411part1 : t5_411jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_411frontier : t5_411root.frontier 1=t5_411jobs := by rfl
theorem t5_411all : t5_411jobs.all (Job.check tree)=true := by
  simp only [t5_411jobs,List.all_append,List.all_nil,t5_411part0,t5_411part1,Bool.and_self]
theorem t5_411checked : Checked tree [1,3,3,10,7] := by
  refine ⟨plan3869,valid3869,t5_411choices,?_⟩
  exact check_of_frontier tree 1 t5_411root t5_411jobs t5_411frontier t5_411all
theorem t5_412choices : plan3870.choices=[1,3,3,10,10].map (options 5 2) := by rfl


theorem t5_412part0 : t5_412jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_412frontier : t5_412root.frontier 0=t5_412jobs := by rfl
theorem t5_412all : t5_412jobs.all (Job.check tree)=true := by
  simp only [t5_412jobs,List.all_append,List.all_nil,t5_412part0,Bool.and_self]
theorem t5_412checked : Checked tree [1,3,3,10,10] := by
  refine ⟨plan3870,valid3870,t5_412choices,?_⟩
  exact check_of_frontier tree 0 t5_412root t5_412jobs t5_412frontier t5_412all
theorem t5_413choices : plan4156.choices=[1,3,6,6,6].map (options 5 3) := by rfl


theorem t5_413part0 : t5_413jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_413frontier : t5_413root.frontier 0=t5_413jobs := by rfl
theorem t5_413all : t5_413jobs.all (Job.check tree)=true := by
  simp only [t5_413jobs,List.all_append,List.all_nil,t5_413part0,Bool.and_self]
theorem t5_413checked : Checked tree [1,3,6,6,6] := by
  refine ⟨plan4156,valid4156,t5_413choices,?_⟩
  exact check_of_frontier tree 0 t5_413root t5_413jobs t5_413frontier t5_413all
theorem t5_414choices : plan4157.choices=[1,3,6,6,7].map (options 5 3) := by rfl


theorem t5_414part0 : t5_414jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_414part1 : t5_414jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_414frontier : t5_414root.frontier 1=t5_414jobs := by rfl
theorem t5_414all : t5_414jobs.all (Job.check tree)=true := by
  simp only [t5_414jobs,List.all_append,List.all_nil,t5_414part0,t5_414part1,Bool.and_self]
theorem t5_414checked : Checked tree [1,3,6,6,7] := by
  refine ⟨plan4157,valid4157,t5_414choices,?_⟩
  exact check_of_frontier tree 1 t5_414root t5_414jobs t5_414frontier t5_414all
theorem t5_415choices : plan4158.choices=[1,3,6,6,10].map (options 5 3) := by rfl


theorem t5_415part0 : t5_415jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_415part1 : t5_415jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_415frontier : t5_415root.frontier 1=t5_415jobs := by rfl
theorem t5_415all : t5_415jobs.all (Job.check tree)=true := by
  simp only [t5_415jobs,List.all_append,List.all_nil,t5_415part0,t5_415part1,Bool.and_self]
theorem t5_415checked : Checked tree [1,3,6,6,10] := by
  refine ⟨plan4158,valid4158,t5_415choices,?_⟩
  exact check_of_frontier tree 1 t5_415root t5_415jobs t5_415frontier t5_415all
theorem t5_416choices : plan4159.choices=[1,3,6,7,7].map (options 5 3) := by rfl


theorem t5_416part0 : t5_416jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_416part1 : t5_416jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_416frontier : t5_416root.frontier 1=t5_416jobs := by rfl
theorem t5_416all : t5_416jobs.all (Job.check tree)=true := by
  simp only [t5_416jobs,List.all_append,List.all_nil,t5_416part0,t5_416part1,Bool.and_self]
theorem t5_416checked : Checked tree [1,3,6,7,7] := by
  refine ⟨plan4159,valid4159,t5_416choices,?_⟩
  exact check_of_frontier tree 1 t5_416root t5_416jobs t5_416frontier t5_416all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks009 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_405checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_406checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_407checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_408checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_409checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_410checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_411checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_412checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_393checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_413checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_414checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_415checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_416checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_394checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_395checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_396checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_397checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_398checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_399checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_400checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_401checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_402checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_403checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_392checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_404checked⟩
