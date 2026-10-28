-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks030
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:16:51.872079+00:00
-- url     : https://prove2.me/submissions/e09af5ce-9e28-4124-a29b-5f5cf1d1ce07

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks030
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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





theorem valid102 : plan102.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid105 : plan105.Valid := valid_step _ _ _ valid0 (by decide +kernel)











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





























































































































theorem valid447 : plan447.Valid := valid_step _ _ _ valid88 (by decide +kernel)











theorem valid453 : plan453.Valid := valid_step _ _ _ valid88 (by decide +kernel)











theorem valid459 : plan459.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid460 : plan460.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid461 : plan461.Valid := valid_step _ _ _ valid99 (by decide +kernel)

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







theorem valid1252 : plan1252.Valid := valid_step _ _ _ valid447 (by decide +kernel)











theorem valid1258 : plan1258.Valid := valid_step _ _ _ valid453 (by decide +kernel)











theorem valid1264 : plan1264.Valid := valid_step _ _ _ valid453 (by decide +kernel)

















theorem valid1273 : plan1273.Valid := valid_step _ _ _ valid459 (by decide +kernel)

theorem valid1274 : plan1274.Valid := valid_step _ _ _ valid460 (by decide +kernel)

theorem valid1275 : plan1275.Valid := valid_step _ _ _ valid461 (by decide +kernel)



theorem valid1277 : plan1277.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1278 : plan1278.Valid := valid_step _ _ _ valid464 (by decide +kernel)

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





































































theorem valid2531 : plan2531.Valid := valid_step _ _ _ valid1252 (by decide +kernel)











theorem valid2537 : plan2537.Valid := valid_step _ _ _ valid1258 (by decide +kernel)











theorem valid2543 : plan2543.Valid := valid_step _ _ _ valid1264 (by decide +kernel)

















































































theorem valid2584 : plan2584.Valid := valid_step _ _ _ valid1273 (by decide +kernel)

theorem valid2585 : plan2585.Valid := valid_step _ _ _ valid1274 (by decide +kernel)

theorem valid2586 : plan2586.Valid := valid_step _ _ _ valid1275 (by decide +kernel)

theorem valid2587 : plan2587.Valid := valid_step _ _ _ valid1277 (by decide +kernel)

theorem valid2588 : plan2588.Valid := valid_step _ _ _ valid1278 (by decide +kernel)

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









theorem valid3749 : plan3749.Valid := valid_step _ _ _ valid2531 (by decide +kernel)

theorem valid3750 : plan3750.Valid := valid_step _ _ _ valid2537 (by decide +kernel)

theorem valid3751 : plan3751.Valid := valid_step _ _ _ valid2543 (by decide +kernel)


















































































































































































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

























theorem valid3949 : plan3949.Valid := valid_step _ _ _ valid2584 (by decide +kernel)

theorem valid3950 : plan3950.Valid := valid_step _ _ _ valid2585 (by decide +kernel)

theorem valid3951 : plan3951.Valid := valid_step _ _ _ valid2586 (by decide +kernel)

theorem valid3952 : plan3952.Valid := valid_step _ _ _ valid2587 (by decide +kernel)

theorem valid3953 : plan3953.Valid := valid_step _ _ _ valid2588 (by decide +kernel)

theorem valid3954 : plan3954.Valid := valid_step _ _ _ valid2589 (by decide +kernel)

theorem valid3955 : plan3955.Valid := valid_step _ _ _ valid2590 (by decide +kernel)

theorem valid3956 : plan3956.Valid := valid_step _ _ _ valid2600 (by decide +kernel)

theorem valid3957 : plan3957.Valid := valid_step _ _ _ valid2607 (by decide +kernel)

theorem valid3958 : plan3958.Valid := valid_step _ _ _ valid2608 (by decide +kernel)

theorem valid3959 : plan3959.Valid := valid_step _ _ _ valid2609 (by decide +kernel)

theorem valid3960 : plan3960.Valid := valid_step _ _ _ valid2616 (by decide +kernel)
















































































































































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











































































theorem valid3110 : plan3110.Valid := valid_step _ _ _ valid1464 (by decide +kernel)




















































































































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



















































































































































































theorem valid4314 : plan4314.Valid := valid_step _ _ _ valid2700 (by decide +kernel)

theorem valid4315 : plan4315.Valid := valid_step _ _ _ valid2701 (by decide +kernel)

theorem valid4316 : plan4316.Valid := valid_step _ _ _ valid2702 (by decide +kernel)

theorem valid4317 : plan4317.Valid := valid_step _ _ _ valid2703 (by decide +kernel)

theorem valid4318 : plan4318.Valid := valid_step _ _ _ valid2704 (by decide +kernel)

theorem valid4319 : plan4319.Valid := valid_step _ _ _ valid2705 (by decide +kernel)

theorem valid4320 : plan4320.Valid := valid_step _ _ _ valid2706 (by decide +kernel)
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





















































































theorem valid4747 : plan4747.Valid := valid_step _ _ _ valid3110 (by decide +kernel)










































































































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

theorem valid4321 : plan4321.Valid := valid_step _ _ _ valid2707 (by decide +kernel)

theorem valid4322 : plan4322.Valid := valid_step _ _ _ valid2708 (by decide +kernel)

theorem valid4323 : plan4323.Valid := valid_step _ _ _ valid2709 (by decide +kernel)

theorem valid4324 : plan4324.Valid := valid_step _ _ _ valid2710 (by decide +kernel)

theorem valid4325 : plan4325.Valid := valid_step _ _ _ valid2711 (by decide +kernel)

theorem valid4326 : plan4326.Valid := valid_step _ _ _ valid2712 (by decide +kernel)

theorem valid4327 : plan4327.Valid := valid_step _ _ _ valid2713 (by decide +kernel)

theorem valid4328 : plan4328.Valid := valid_step _ _ _ valid2714 (by decide +kernel)

theorem valid4329 : plan4329.Valid := valid_step _ _ _ valid2715 (by decide +kernel)

theorem valid4330 : plan4330.Valid := valid_step _ _ _ valid2716 (by decide +kernel)

theorem valid4331 : plan4331.Valid := valid_step _ _ _ valid2717 (by decide +kernel)

theorem valid4332 : plan4332.Valid := valid_step _ _ _ valid2718 (by decide +kernel)

theorem valid4333 : plan4333.Valid := valid_step _ _ _ valid2719 (by decide +kernel)

theorem valid4334 : plan4334.Valid := valid_step _ _ _ valid2720 (by decide +kernel)




































































































































































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
theorem t5_892choices : plan4747.choices=[3,10,10,10,10].map (options 5 4) := by rfl


theorem t5_892part0 : t5_892jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_892frontier : t5_892root.frontier 0=t5_892jobs := by rfl
theorem t5_892all : t5_892jobs.all (Job.check tree)=true := by
  simp only [t5_892jobs,List.all_append,List.all_nil,t5_892part0,Bool.and_self]
theorem t5_892checked : Checked tree [3,10,10,10,10] := by
  refine ⟨plan4747,valid4747,t5_892choices,?_⟩
  exact check_of_frontier tree 0 t5_892root t5_892jobs t5_892frontier t5_892all
theorem t5_893choices : plan3749.choices=[4,2,2,2,3].map (options 5 1) := by rfl


theorem t5_893part0 : t5_893jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_893frontier : t5_893root.frontier 0=t5_893jobs := by rfl
theorem t5_893all : t5_893jobs.all (Job.check tree)=true := by
  simp only [t5_893jobs,List.all_append,List.all_nil,t5_893part0,Bool.and_self]
theorem t5_893checked : Checked tree [4,2,2,2,3] := by
  refine ⟨plan3749,valid3749,t5_893choices,?_⟩
  exact check_of_frontier tree 0 t5_893root t5_893jobs t5_893frontier t5_893all
theorem t5_894choices : plan3949.choices=[4,2,2,2,6].map (options 5 2) := by rfl


theorem t5_894part0 : t5_894jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_894frontier : t5_894root.frontier 0=t5_894jobs := by rfl
theorem t5_894all : t5_894jobs.all (Job.check tree)=true := by
  simp only [t5_894jobs,List.all_append,List.all_nil,t5_894part0,Bool.and_self]
theorem t5_894checked : Checked tree [4,2,2,2,6] := by
  refine ⟨plan3949,valid3949,t5_894choices,?_⟩
  exact check_of_frontier tree 0 t5_894root t5_894jobs t5_894frontier t5_894all
theorem t5_895choices : plan3950.choices=[4,2,2,2,7].map (options 5 2) := by rfl


theorem t5_895part0 : t5_895jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_895frontier : t5_895root.frontier 0=t5_895jobs := by rfl
theorem t5_895all : t5_895jobs.all (Job.check tree)=true := by
  simp only [t5_895jobs,List.all_append,List.all_nil,t5_895part0,Bool.and_self]
theorem t5_895checked : Checked tree [4,2,2,2,7] := by
  refine ⟨plan3950,valid3950,t5_895choices,?_⟩
  exact check_of_frontier tree 0 t5_895root t5_895jobs t5_895frontier t5_895all
theorem t5_896choices : plan3951.choices=[4,2,2,2,10].map (options 5 2) := by rfl


theorem t5_896part0 : t5_896jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_896frontier : t5_896root.frontier 0=t5_896jobs := by rfl
theorem t5_896all : t5_896jobs.all (Job.check tree)=true := by
  simp only [t5_896jobs,List.all_append,List.all_nil,t5_896part0,Bool.and_self]
theorem t5_896checked : Checked tree [4,2,2,2,10] := by
  refine ⟨plan3951,valid3951,t5_896choices,?_⟩
  exact check_of_frontier tree 0 t5_896root t5_896jobs t5_896frontier t5_896all
theorem t5_897choices : plan3750.choices=[4,2,2,3,3].map (options 5 1) := by rfl


theorem t5_897part0 : t5_897jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_897frontier : t5_897root.frontier 0=t5_897jobs := by rfl
theorem t5_897all : t5_897jobs.all (Job.check tree)=true := by
  simp only [t5_897jobs,List.all_append,List.all_nil,t5_897part0,Bool.and_self]
theorem t5_897checked : Checked tree [4,2,2,3,3] := by
  refine ⟨plan3750,valid3750,t5_897choices,?_⟩
  exact check_of_frontier tree 0 t5_897root t5_897jobs t5_897frontier t5_897all
theorem t5_898choices : plan3952.choices=[4,2,2,3,6].map (options 5 2) := by rfl


theorem t5_898part0 : t5_898jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_898frontier : t5_898root.frontier 0=t5_898jobs := by rfl
theorem t5_898all : t5_898jobs.all (Job.check tree)=true := by
  simp only [t5_898jobs,List.all_append,List.all_nil,t5_898part0,Bool.and_self]
theorem t5_898checked : Checked tree [4,2,2,3,6] := by
  refine ⟨plan3952,valid3952,t5_898choices,?_⟩
  exact check_of_frontier tree 0 t5_898root t5_898jobs t5_898frontier t5_898all
theorem t5_899choices : plan3953.choices=[4,2,2,3,7].map (options 5 2) := by rfl


theorem t5_899part0 : t5_899jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_899frontier : t5_899root.frontier 0=t5_899jobs := by rfl
theorem t5_899all : t5_899jobs.all (Job.check tree)=true := by
  simp only [t5_899jobs,List.all_append,List.all_nil,t5_899part0,Bool.and_self]
theorem t5_899checked : Checked tree [4,2,2,3,7] := by
  refine ⟨plan3953,valid3953,t5_899choices,?_⟩
  exact check_of_frontier tree 0 t5_899root t5_899jobs t5_899frontier t5_899all
theorem t5_900choices : plan3954.choices=[4,2,2,3,10].map (options 5 2) := by rfl


theorem t5_900part0 : t5_900jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_900frontier : t5_900root.frontier 0=t5_900jobs := by rfl
theorem t5_900all : t5_900jobs.all (Job.check tree)=true := by
  simp only [t5_900jobs,List.all_append,List.all_nil,t5_900part0,Bool.and_self]
theorem t5_900checked : Checked tree [4,2,2,3,10] := by
  refine ⟨plan3954,valid3954,t5_900choices,?_⟩
  exact check_of_frontier tree 0 t5_900root t5_900jobs t5_900frontier t5_900all
theorem t5_901choices : plan3955.choices=[4,2,2,5,3].map (options 5 2) := by rfl


theorem t5_901part0 : t5_901jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_901frontier : t5_901root.frontier 0=t5_901jobs := by rfl
theorem t5_901all : t5_901jobs.all (Job.check tree)=true := by
  simp only [t5_901jobs,List.all_append,List.all_nil,t5_901part0,Bool.and_self]
theorem t5_901checked : Checked tree [4,2,2,5,3] := by
  refine ⟨plan3955,valid3955,t5_901choices,?_⟩
  exact check_of_frontier tree 0 t5_901root t5_901jobs t5_901frontier t5_901all
theorem t5_902choices : plan4314.choices=[4,2,2,5,6].map (options 5 3) := by rfl


theorem t5_902part0 : t5_902jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_902frontier : t5_902root.frontier 0=t5_902jobs := by rfl
theorem t5_902all : t5_902jobs.all (Job.check tree)=true := by
  simp only [t5_902jobs,List.all_append,List.all_nil,t5_902part0,Bool.and_self]
theorem t5_902checked : Checked tree [4,2,2,5,6] := by
  refine ⟨plan4314,valid4314,t5_902choices,?_⟩
  exact check_of_frontier tree 0 t5_902root t5_902jobs t5_902frontier t5_902all
theorem t5_903choices : plan4315.choices=[4,2,2,5,7].map (options 5 3) := by rfl


theorem t5_903part0 : t5_903jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_903frontier : t5_903root.frontier 0=t5_903jobs := by rfl
theorem t5_903all : t5_903jobs.all (Job.check tree)=true := by
  simp only [t5_903jobs,List.all_append,List.all_nil,t5_903part0,Bool.and_self]
theorem t5_903checked : Checked tree [4,2,2,5,7] := by
  refine ⟨plan4315,valid4315,t5_903choices,?_⟩
  exact check_of_frontier tree 0 t5_903root t5_903jobs t5_903frontier t5_903all
theorem t5_904choices : plan4316.choices=[4,2,2,5,10].map (options 5 3) := by rfl


theorem t5_904part0 : t5_904jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_904frontier : t5_904root.frontier 0=t5_904jobs := by rfl
theorem t5_904all : t5_904jobs.all (Job.check tree)=true := by
  simp only [t5_904jobs,List.all_append,List.all_nil,t5_904part0,Bool.and_self]
theorem t5_904checked : Checked tree [4,2,2,5,10] := by
  refine ⟨plan4316,valid4316,t5_904choices,?_⟩
  exact check_of_frontier tree 0 t5_904root t5_904jobs t5_904frontier t5_904all
theorem t5_905choices : plan4317.choices=[4,2,2,6,6].map (options 5 3) := by rfl


theorem t5_905part0 : t5_905jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_905frontier : t5_905root.frontier 0=t5_905jobs := by rfl
theorem t5_905all : t5_905jobs.all (Job.check tree)=true := by
  simp only [t5_905jobs,List.all_append,List.all_nil,t5_905part0,Bool.and_self]
theorem t5_905checked : Checked tree [4,2,2,6,6] := by
  refine ⟨plan4317,valid4317,t5_905choices,?_⟩
  exact check_of_frontier tree 0 t5_905root t5_905jobs t5_905frontier t5_905all
theorem t5_906choices : plan4318.choices=[4,2,2,6,7].map (options 5 3) := by rfl


theorem t5_906part0 : t5_906jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_906frontier : t5_906root.frontier 0=t5_906jobs := by rfl
theorem t5_906all : t5_906jobs.all (Job.check tree)=true := by
  simp only [t5_906jobs,List.all_append,List.all_nil,t5_906part0,Bool.and_self]
theorem t5_906checked : Checked tree [4,2,2,6,7] := by
  refine ⟨plan4318,valid4318,t5_906choices,?_⟩
  exact check_of_frontier tree 0 t5_906root t5_906jobs t5_906frontier t5_906all
theorem t5_907choices : plan4319.choices=[4,2,2,6,10].map (options 5 3) := by rfl


theorem t5_907part0 : t5_907jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_907frontier : t5_907root.frontier 0=t5_907jobs := by rfl
theorem t5_907all : t5_907jobs.all (Job.check tree)=true := by
  simp only [t5_907jobs,List.all_append,List.all_nil,t5_907part0,Bool.and_self]
theorem t5_907checked : Checked tree [4,2,2,6,10] := by
  refine ⟨plan4319,valid4319,t5_907choices,?_⟩
  exact check_of_frontier tree 0 t5_907root t5_907jobs t5_907frontier t5_907all
theorem t5_908choices : plan4320.choices=[4,2,2,7,7].map (options 5 3) := by rfl


theorem t5_908part0 : t5_908jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_908frontier : t5_908root.frontier 0=t5_908jobs := by rfl
theorem t5_908all : t5_908jobs.all (Job.check tree)=true := by
  simp only [t5_908jobs,List.all_append,List.all_nil,t5_908part0,Bool.and_self]
theorem t5_908checked : Checked tree [4,2,2,7,7] := by
  refine ⟨plan4320,valid4320,t5_908choices,?_⟩
  exact check_of_frontier tree 0 t5_908root t5_908jobs t5_908frontier t5_908all
theorem t5_909choices : plan3956.choices=[4,2,2,9,3].map (options 5 2) := by rfl


theorem t5_909part0 : t5_909jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_909frontier : t5_909root.frontier 0=t5_909jobs := by rfl
theorem t5_909all : t5_909jobs.all (Job.check tree)=true := by
  simp only [t5_909jobs,List.all_append,List.all_nil,t5_909part0,Bool.and_self]
theorem t5_909checked : Checked tree [4,2,2,9,3] := by
  refine ⟨plan3956,valid3956,t5_909choices,?_⟩
  exact check_of_frontier tree 0 t5_909root t5_909jobs t5_909frontier t5_909all
theorem t5_910choices : plan4321.choices=[4,2,2,9,6].map (options 5 3) := by rfl


theorem t5_910part0 : t5_910jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_910frontier : t5_910root.frontier 0=t5_910jobs := by rfl
theorem t5_910all : t5_910jobs.all (Job.check tree)=true := by
  simp only [t5_910jobs,List.all_append,List.all_nil,t5_910part0,Bool.and_self]
theorem t5_910checked : Checked tree [4,2,2,9,6] := by
  refine ⟨plan4321,valid4321,t5_910choices,?_⟩
  exact check_of_frontier tree 0 t5_910root t5_910jobs t5_910frontier t5_910all
theorem t5_911choices : plan4322.choices=[4,2,2,9,7].map (options 5 3) := by rfl


theorem t5_911part0 : t5_911jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_911frontier : t5_911root.frontier 0=t5_911jobs := by rfl
theorem t5_911all : t5_911jobs.all (Job.check tree)=true := by
  simp only [t5_911jobs,List.all_append,List.all_nil,t5_911part0,Bool.and_self]
theorem t5_911checked : Checked tree [4,2,2,9,7] := by
  refine ⟨plan4322,valid4322,t5_911choices,?_⟩
  exact check_of_frontier tree 0 t5_911root t5_911jobs t5_911frontier t5_911all
theorem t5_912choices : plan4323.choices=[4,2,2,9,10].map (options 5 3) := by rfl


theorem t5_912part0 : t5_912jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_912frontier : t5_912root.frontier 0=t5_912jobs := by rfl
theorem t5_912all : t5_912jobs.all (Job.check tree)=true := by
  simp only [t5_912jobs,List.all_append,List.all_nil,t5_912part0,Bool.and_self]
theorem t5_912checked : Checked tree [4,2,2,9,10] := by
  refine ⟨plan4323,valid4323,t5_912choices,?_⟩
  exact check_of_frontier tree 0 t5_912root t5_912jobs t5_912frontier t5_912all
theorem t5_913choices : plan4324.choices=[4,2,2,10,7].map (options 5 3) := by rfl


theorem t5_913part0 : t5_913jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_913frontier : t5_913root.frontier 0=t5_913jobs := by rfl
theorem t5_913all : t5_913jobs.all (Job.check tree)=true := by
  simp only [t5_913jobs,List.all_append,List.all_nil,t5_913part0,Bool.and_self]
theorem t5_913checked : Checked tree [4,2,2,10,7] := by
  refine ⟨plan4324,valid4324,t5_913choices,?_⟩
  exact check_of_frontier tree 0 t5_913root t5_913jobs t5_913frontier t5_913all
theorem t5_914choices : plan4325.choices=[4,2,2,10,10].map (options 5 3) := by rfl


theorem t5_914part0 : t5_914jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_914frontier : t5_914root.frontier 0=t5_914jobs := by rfl
theorem t5_914all : t5_914jobs.all (Job.check tree)=true := by
  simp only [t5_914jobs,List.all_append,List.all_nil,t5_914part0,Bool.and_self]
theorem t5_914checked : Checked tree [4,2,2,10,10] := by
  refine ⟨plan4325,valid4325,t5_914choices,?_⟩
  exact check_of_frontier tree 0 t5_914root t5_914jobs t5_914frontier t5_914all
theorem t5_915choices : plan3751.choices=[4,2,3,3,3].map (options 5 1) := by rfl


theorem t5_915part0 : t5_915jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_915frontier : t5_915root.frontier 0=t5_915jobs := by rfl
theorem t5_915all : t5_915jobs.all (Job.check tree)=true := by
  simp only [t5_915jobs,List.all_append,List.all_nil,t5_915part0,Bool.and_self]
theorem t5_915checked : Checked tree [4,2,3,3,3] := by
  refine ⟨plan3751,valid3751,t5_915choices,?_⟩
  exact check_of_frontier tree 0 t5_915root t5_915jobs t5_915frontier t5_915all
theorem t5_916choices : plan3957.choices=[4,2,3,3,6].map (options 5 2) := by rfl


theorem t5_916part0 : t5_916jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_916frontier : t5_916root.frontier 0=t5_916jobs := by rfl
theorem t5_916all : t5_916jobs.all (Job.check tree)=true := by
  simp only [t5_916jobs,List.all_append,List.all_nil,t5_916part0,Bool.and_self]
theorem t5_916checked : Checked tree [4,2,3,3,6] := by
  refine ⟨plan3957,valid3957,t5_916choices,?_⟩
  exact check_of_frontier tree 0 t5_916root t5_916jobs t5_916frontier t5_916all
theorem t5_917choices : plan3958.choices=[4,2,3,3,7].map (options 5 2) := by rfl


theorem t5_917part0 : t5_917jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_917part1 : t5_917jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_917frontier : t5_917root.frontier 1=t5_917jobs := by rfl
theorem t5_917all : t5_917jobs.all (Job.check tree)=true := by
  simp only [t5_917jobs,List.all_append,List.all_nil,t5_917part0,t5_917part1,Bool.and_self]
theorem t5_917checked : Checked tree [4,2,3,3,7] := by
  refine ⟨plan3958,valid3958,t5_917choices,?_⟩
  exact check_of_frontier tree 1 t5_917root t5_917jobs t5_917frontier t5_917all
theorem t5_918choices : plan3959.choices=[4,2,3,3,10].map (options 5 2) := by rfl


theorem t5_918part0 : t5_918jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_918frontier : t5_918root.frontier 0=t5_918jobs := by rfl
theorem t5_918all : t5_918jobs.all (Job.check tree)=true := by
  simp only [t5_918jobs,List.all_append,List.all_nil,t5_918part0,Bool.and_self]
theorem t5_918checked : Checked tree [4,2,3,3,10] := by
  refine ⟨plan3959,valid3959,t5_918choices,?_⟩
  exact check_of_frontier tree 0 t5_918root t5_918jobs t5_918frontier t5_918all
theorem t5_919choices : plan4326.choices=[4,2,3,6,6].map (options 5 3) := by rfl


theorem t5_919part0 : t5_919jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_919frontier : t5_919root.frontier 0=t5_919jobs := by rfl
theorem t5_919all : t5_919jobs.all (Job.check tree)=true := by
  simp only [t5_919jobs,List.all_append,List.all_nil,t5_919part0,Bool.and_self]
theorem t5_919checked : Checked tree [4,2,3,6,6] := by
  refine ⟨plan4326,valid4326,t5_919choices,?_⟩
  exact check_of_frontier tree 0 t5_919root t5_919jobs t5_919frontier t5_919all
theorem t5_920choices : plan4327.choices=[4,2,3,6,7].map (options 5 3) := by rfl


theorem t5_920part0 : t5_920jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_920part1 : t5_920jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_920frontier : t5_920root.frontier 1=t5_920jobs := by rfl
theorem t5_920all : t5_920jobs.all (Job.check tree)=true := by
  simp only [t5_920jobs,List.all_append,List.all_nil,t5_920part0,t5_920part1,Bool.and_self]
theorem t5_920checked : Checked tree [4,2,3,6,7] := by
  refine ⟨plan4327,valid4327,t5_920choices,?_⟩
  exact check_of_frontier tree 1 t5_920root t5_920jobs t5_920frontier t5_920all
theorem t5_921choices : plan4328.choices=[4,2,3,6,10].map (options 5 3) := by rfl


theorem t5_921part0 : t5_921jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_921part1 : t5_921jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_921frontier : t5_921root.frontier 1=t5_921jobs := by rfl
theorem t5_921all : t5_921jobs.all (Job.check tree)=true := by
  simp only [t5_921jobs,List.all_append,List.all_nil,t5_921part0,t5_921part1,Bool.and_self]
theorem t5_921checked : Checked tree [4,2,3,6,10] := by
  refine ⟨plan4328,valid4328,t5_921choices,?_⟩
  exact check_of_frontier tree 1 t5_921root t5_921jobs t5_921frontier t5_921all
theorem t5_922choices : plan4329.choices=[4,2,3,7,7].map (options 5 3) := by rfl


theorem t5_922part0 : t5_922jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_922frontier : t5_922root.frontier 0=t5_922jobs := by rfl
theorem t5_922all : t5_922jobs.all (Job.check tree)=true := by
  simp only [t5_922jobs,List.all_append,List.all_nil,t5_922part0,Bool.and_self]
theorem t5_922checked : Checked tree [4,2,3,7,7] := by
  refine ⟨plan4329,valid4329,t5_922choices,?_⟩
  exact check_of_frontier tree 0 t5_922root t5_922jobs t5_922frontier t5_922all
theorem t5_923choices : plan4330.choices=[4,2,3,10,7].map (options 5 3) := by rfl


theorem t5_923part0 : t5_923jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_923part1 : t5_923jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_923frontier : t5_923root.frontier 1=t5_923jobs := by rfl
theorem t5_923all : t5_923jobs.all (Job.check tree)=true := by
  simp only [t5_923jobs,List.all_append,List.all_nil,t5_923part0,t5_923part1,Bool.and_self]
theorem t5_923checked : Checked tree [4,2,3,10,7] := by
  refine ⟨plan4330,valid4330,t5_923choices,?_⟩
  exact check_of_frontier tree 1 t5_923root t5_923jobs t5_923frontier t5_923all
theorem t5_924choices : plan4331.choices=[4,2,3,10,10].map (options 5 3) := by rfl


theorem t5_924part0 : t5_924jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_924frontier : t5_924root.frontier 0=t5_924jobs := by rfl
theorem t5_924all : t5_924jobs.all (Job.check tree)=true := by
  simp only [t5_924jobs,List.all_append,List.all_nil,t5_924part0,Bool.and_self]
theorem t5_924checked : Checked tree [4,2,3,10,10] := by
  refine ⟨plan4331,valid4331,t5_924choices,?_⟩
  exact check_of_frontier tree 0 t5_924root t5_924jobs t5_924frontier t5_924all
theorem t5_925choices : plan3960.choices=[4,2,5,3,3].map (options 5 2) := by rfl


theorem t5_925part0 : t5_925jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_925frontier : t5_925root.frontier 0=t5_925jobs := by rfl
theorem t5_925all : t5_925jobs.all (Job.check tree)=true := by
  simp only [t5_925jobs,List.all_append,List.all_nil,t5_925part0,Bool.and_self]
theorem t5_925checked : Checked tree [4,2,5,3,3] := by
  refine ⟨plan3960,valid3960,t5_925choices,?_⟩
  exact check_of_frontier tree 0 t5_925root t5_925jobs t5_925frontier t5_925all
theorem t5_926choices : plan4332.choices=[4,2,5,3,6].map (options 5 3) := by rfl


theorem t5_926part0 : t5_926jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_926frontier : t5_926root.frontier 0=t5_926jobs := by rfl
theorem t5_926all : t5_926jobs.all (Job.check tree)=true := by
  simp only [t5_926jobs,List.all_append,List.all_nil,t5_926part0,Bool.and_self]
theorem t5_926checked : Checked tree [4,2,5,3,6] := by
  refine ⟨plan4332,valid4332,t5_926choices,?_⟩
  exact check_of_frontier tree 0 t5_926root t5_926jobs t5_926frontier t5_926all
theorem t5_927choices : plan4333.choices=[4,2,5,3,7].map (options 5 3) := by rfl


theorem t5_927part0 : t5_927jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_927frontier : t5_927root.frontier 0=t5_927jobs := by rfl
theorem t5_927all : t5_927jobs.all (Job.check tree)=true := by
  simp only [t5_927jobs,List.all_append,List.all_nil,t5_927part0,Bool.and_self]
theorem t5_927checked : Checked tree [4,2,5,3,7] := by
  refine ⟨plan4333,valid4333,t5_927choices,?_⟩
  exact check_of_frontier tree 0 t5_927root t5_927jobs t5_927frontier t5_927all
theorem t5_928choices : plan4334.choices=[4,2,5,3,10].map (options 5 3) := by rfl


theorem t5_928part0 : t5_928jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_928frontier : t5_928root.frontier 0=t5_928jobs := by rfl
theorem t5_928all : t5_928jobs.all (Job.check tree)=true := by
  simp only [t5_928jobs,List.all_append,List.all_nil,t5_928part0,Bool.and_self]
theorem t5_928checked : Checked tree [4,2,5,3,10] := by
  refine ⟨plan4334,valid4334,t5_928choices,?_⟩
  exact check_of_frontier tree 0 t5_928root t5_928jobs t5_928frontier t5_928all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks030 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_892checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_905checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_906checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_907checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_908checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_909checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_910checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_911checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_912checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_913checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_914checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_893checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_915checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_916checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_917checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_918checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_919checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_920checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_921checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_922checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_923checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_894checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_924checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_925checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_926checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_927checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_928checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_895checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_896checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_897checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_898checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_899checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_900checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_901checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_902checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_903checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_904checked⟩
