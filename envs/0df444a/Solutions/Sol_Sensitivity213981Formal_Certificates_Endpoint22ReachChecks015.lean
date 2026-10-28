-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks015
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:19.191739+00:00
-- url     : https://prove2.me/submissions/d09a0058-9e37-48c4-8c51-0ed532d993e3

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks015
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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



theorem valid101 : plan101.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid102 : plan102.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid104 : plan104.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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



theorem valid455 : plan455.Valid := valid_step _ _ _ valid91 (by decide +kernel)

theorem valid456 : plan456.Valid := valid_step _ _ _ valid93 (by decide +kernel)













theorem valid463 : plan463.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid464 : plan464.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid465 : plan465.Valid := valid_step _ _ _ valid99 (by decide +kernel)

theorem valid466 : plan466.Valid := valid_step _ _ _ valid94 (by decide +kernel)











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













theorem valid489 : plan489.Valid := valid_step _ _ _ valid101 (by decide +kernel)

theorem valid490 : plan490.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid491 : plan491.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid492 : plan492.Valid := valid_step _ _ _ valid104 (by decide +kernel)

theorem valid493 : plan493.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)






























































































































































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



































theorem valid1266 : plan1266.Valid := valid_step _ _ _ valid455 (by decide +kernel)

theorem valid1267 : plan1267.Valid := valid_step _ _ _ valid456 (by decide +kernel)

theorem valid1268 : plan1268.Valid := valid_step _ _ _ valid453 (by decide +kernel)

































































theorem valid1301 : plan1301.Valid := valid_step _ _ _ valid472 (by decide +kernel)

theorem valid1302 : plan1302.Valid := valid_step _ _ _ valid473 (by decide +kernel)

theorem valid1303 : plan1303.Valid := valid_step _ _ _ valid474 (by decide +kernel)

theorem valid1304 : plan1304.Valid := valid_step _ _ _ valid475 (by decide +kernel)

theorem valid1305 : plan1305.Valid := valid_step _ _ _ valid481 (by decide +kernel)

theorem valid1306 : plan1306.Valid := valid_step _ _ _ valid482 (by decide +kernel)





theorem valid1309 : plan1309.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1310 : plan1310.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1311 : plan1311.Valid := valid_step _ _ _ valid465 (by decide +kernel)

theorem valid1312 : plan1312.Valid := valid_step _ _ _ valid466 (by decide +kernel)

theorem valid1313 : plan1313.Valid := valid_step _ _ _ valid476 (by decide +kernel)






























































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

































































































theorem valid2545 : plan2545.Valid := valid_step _ _ _ valid1266 (by decide +kernel)

theorem valid2546 : plan2546.Valid := valid_step _ _ _ valid1267 (by decide +kernel)

theorem valid2547 : plan2547.Valid := valid_step _ _ _ valid1268 (by decide +kernel)


























































































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

















































































































































































theorem valid3737 : plan3737.Valid := valid_step _ _ _ valid2545 (by decide +kernel)

theorem valid3738 : plan3738.Valid := valid_step _ _ _ valid2546 (by decide +kernel)

theorem valid3739 : plan3739.Valid := valid_step _ _ _ valid2547 (by decide +kernel)










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



















theorem valid1354 : plan1354.Valid := valid_step _ _ _ valid489 (by decide +kernel)

theorem valid1355 : plan1355.Valid := valid_step _ _ _ valid490 (by decide +kernel)

theorem valid1356 : plan1356.Valid := valid_step _ _ _ valid491 (by decide +kernel)

theorem valid1357 : plan1357.Valid := valid_step _ _ _ valid492 (by decide +kernel)

theorem valid1358 : plan1358.Valid := valid_step _ _ _ valid493 (by decide +kernel)

theorem valid1359 : plan1359.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1360 : plan1360.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1361 : plan1361.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1362 : plan1362.Valid := valid_step _ _ _ valid497 (by decide +kernel)




























































































































































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



































theorem valid2610 : plan2610.Valid := valid_step _ _ _ valid1301 (by decide +kernel)

theorem valid2611 : plan2611.Valid := valid_step _ _ _ valid1302 (by decide +kernel)

theorem valid2612 : plan2612.Valid := valid_step _ _ _ valid1303 (by decide +kernel)

theorem valid2613 : plan2613.Valid := valid_step _ _ _ valid1304 (by decide +kernel)

theorem valid2614 : plan2614.Valid := valid_step _ _ _ valid1305 (by decide +kernel)

theorem valid2615 : plan2615.Valid := valid_step _ _ _ valid1306 (by decide +kernel)



theorem valid2617 : plan2617.Valid := valid_step _ _ _ valid1309 (by decide +kernel)

theorem valid2618 : plan2618.Valid := valid_step _ _ _ valid1310 (by decide +kernel)

theorem valid2619 : plan2619.Valid := valid_step _ _ _ valid1311 (by decide +kernel)

theorem valid2620 : plan2620.Valid := valid_step _ _ _ valid1312 (by decide +kernel)

theorem valid2621 : plan2621.Valid := valid_step _ _ _ valid1313 (by decide +kernel)






































































































































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



































































theorem valid2722 : plan2722.Valid := valid_step _ _ _ valid1354 (by decide +kernel)

theorem valid2723 : plan2723.Valid := valid_step _ _ _ valid1355 (by decide +kernel)

theorem valid2724 : plan2724.Valid := valid_step _ _ _ valid1356 (by decide +kernel)

theorem valid2725 : plan2725.Valid := valid_step _ _ _ valid1357 (by decide +kernel)

theorem valid2726 : plan2726.Valid := valid_step _ _ _ valid1358 (by decide +kernel)

theorem valid2727 : plan2727.Valid := valid_step _ _ _ valid1359 (by decide +kernel)

theorem valid2728 : plan2728.Valid := valid_step _ _ _ valid1360 (by decide +kernel)

theorem valid2729 : plan2729.Valid := valid_step _ _ _ valid1361 (by decide +kernel)

theorem valid2730 : plan2730.Valid := valid_step _ _ _ valid1362 (by decide +kernel)












































































































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

















































































































































theorem valid3913 : plan3913.Valid := valid_step _ _ _ valid2610 (by decide +kernel)

theorem valid3914 : plan3914.Valid := valid_step _ _ _ valid2611 (by decide +kernel)

theorem valid3915 : plan3915.Valid := valid_step _ _ _ valid2612 (by decide +kernel)

theorem valid3916 : plan3916.Valid := valid_step _ _ _ valid2613 (by decide +kernel)

theorem valid3917 : plan3917.Valid := valid_step _ _ _ valid2614 (by decide +kernel)

theorem valid3918 : plan3918.Valid := valid_step _ _ _ valid2615 (by decide +kernel)

theorem valid3919 : plan3919.Valid := valid_step _ _ _ valid2617 (by decide +kernel)

theorem valid3920 : plan3920.Valid := valid_step _ _ _ valid2618 (by decide +kernel)

theorem valid3921 : plan3921.Valid := valid_step _ _ _ valid2619 (by decide +kernel)

theorem valid3922 : plan3922.Valid := valid_step _ _ _ valid2620 (by decide +kernel)

theorem valid3923 : plan3923.Valid := valid_step _ _ _ valid2621 (by decide +kernel)


























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



















theorem valid4234 : plan4234.Valid := valid_step _ _ _ valid2722 (by decide +kernel)

theorem valid4235 : plan4235.Valid := valid_step _ _ _ valid2723 (by decide +kernel)

theorem valid4236 : plan4236.Valid := valid_step _ _ _ valid2724 (by decide +kernel)

theorem valid4237 : plan4237.Valid := valid_step _ _ _ valid2725 (by decide +kernel)

theorem valid4238 : plan4238.Valid := valid_step _ _ _ valid2726 (by decide +kernel)

theorem valid4239 : plan4239.Valid := valid_step _ _ _ valid2727 (by decide +kernel)

theorem valid4240 : plan4240.Valid := valid_step _ _ _ valid2728 (by decide +kernel)

theorem valid4241 : plan4241.Valid := valid_step _ _ _ valid2729 (by decide +kernel)

theorem valid4242 : plan4242.Valid := valid_step _ _ _ valid2730 (by decide +kernel)




























































































































































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
theorem t5_678choices : plan3737.choices=[2,2,3,3,7].map (options 5 1) := by rfl


theorem t5_678part0 : t5_678jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_678frontier : t5_678root.frontier 0=t5_678jobs := by rfl
theorem t5_678all : t5_678jobs.all (Job.check tree)=true := by
  simp only [t5_678jobs,List.all_append,List.all_nil,t5_678part0,Bool.and_self]
theorem t5_678checked : Checked tree [2,2,3,3,7] := by
  refine ⟨plan3737,valid3737,t5_678choices,?_⟩
  exact check_of_frontier tree 0 t5_678root t5_678jobs t5_678frontier t5_678all
theorem t5_679choices : plan3738.choices=[2,2,3,3,10].map (options 5 1) := by rfl


theorem t5_679part0 : t5_679jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_679frontier : t5_679root.frontier 0=t5_679jobs := by rfl
theorem t5_679all : t5_679jobs.all (Job.check tree)=true := by
  simp only [t5_679jobs,List.all_append,List.all_nil,t5_679part0,Bool.and_self]
theorem t5_679checked : Checked tree [2,2,3,3,10] := by
  refine ⟨plan3738,valid3738,t5_679choices,?_⟩
  exact check_of_frontier tree 0 t5_679root t5_679jobs t5_679frontier t5_679all
theorem t5_680choices : plan3913.choices=[2,2,3,6,6].map (options 5 2) := by rfl


theorem t5_680part0 : t5_680jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_680frontier : t5_680root.frontier 0=t5_680jobs := by rfl
theorem t5_680all : t5_680jobs.all (Job.check tree)=true := by
  simp only [t5_680jobs,List.all_append,List.all_nil,t5_680part0,Bool.and_self]
theorem t5_680checked : Checked tree [2,2,3,6,6] := by
  refine ⟨plan3913,valid3913,t5_680choices,?_⟩
  exact check_of_frontier tree 0 t5_680root t5_680jobs t5_680frontier t5_680all
theorem t5_681choices : plan3914.choices=[2,2,3,6,7].map (options 5 2) := by rfl


theorem t5_681part0 : t5_681jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_681part1 : t5_681jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_681part2 : t5_681jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_681frontier : t5_681root.frontier 1=t5_681jobs := by rfl
theorem t5_681all : t5_681jobs.all (Job.check tree)=true := by
  simp only [t5_681jobs,List.all_append,List.all_nil,t5_681part0,t5_681part1,t5_681part2,Bool.and_self]
theorem t5_681checked : Checked tree [2,2,3,6,7] := by
  refine ⟨plan3914,valid3914,t5_681choices,?_⟩
  exact check_of_frontier tree 1 t5_681root t5_681jobs t5_681frontier t5_681all
theorem t5_682choices : plan3915.choices=[2,2,3,6,10].map (options 5 2) := by rfl


theorem t5_682part0 : t5_682jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_682part1 : t5_682jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_682frontier : t5_682root.frontier 1=t5_682jobs := by rfl
theorem t5_682all : t5_682jobs.all (Job.check tree)=true := by
  simp only [t5_682jobs,List.all_append,List.all_nil,t5_682part0,t5_682part1,Bool.and_self]
theorem t5_682checked : Checked tree [2,2,3,6,10] := by
  refine ⟨plan3915,valid3915,t5_682choices,?_⟩
  exact check_of_frontier tree 1 t5_682root t5_682jobs t5_682frontier t5_682all
theorem t5_683choices : plan3916.choices=[2,2,3,7,7].map (options 5 2) := by rfl


theorem t5_683part0 : t5_683jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_683part1 : t5_683jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_683frontier : t5_683root.frontier 1=t5_683jobs := by rfl
theorem t5_683all : t5_683jobs.all (Job.check tree)=true := by
  simp only [t5_683jobs,List.all_append,List.all_nil,t5_683part0,t5_683part1,Bool.and_self]
theorem t5_683checked : Checked tree [2,2,3,7,7] := by
  refine ⟨plan3916,valid3916,t5_683choices,?_⟩
  exact check_of_frontier tree 1 t5_683root t5_683jobs t5_683frontier t5_683all
theorem t5_684choices : plan3917.choices=[2,2,3,10,7].map (options 5 2) := by rfl


theorem t5_684part0 : t5_684jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_684part1 : t5_684jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_684part2 : t5_684jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_684frontier : t5_684root.frontier 1=t5_684jobs := by rfl
theorem t5_684all : t5_684jobs.all (Job.check tree)=true := by
  simp only [t5_684jobs,List.all_append,List.all_nil,t5_684part0,t5_684part1,t5_684part2,Bool.and_self]
theorem t5_684checked : Checked tree [2,2,3,10,7] := by
  refine ⟨plan3917,valid3917,t5_684choices,?_⟩
  exact check_of_frontier tree 1 t5_684root t5_684jobs t5_684frontier t5_684all
theorem t5_685choices : plan3918.choices=[2,2,3,10,10].map (options 5 2) := by rfl


theorem t5_685part0 : t5_685jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_685frontier : t5_685root.frontier 0=t5_685jobs := by rfl
theorem t5_685all : t5_685jobs.all (Job.check tree)=true := by
  simp only [t5_685jobs,List.all_append,List.all_nil,t5_685part0,Bool.and_self]
theorem t5_685checked : Checked tree [2,2,3,10,10] := by
  refine ⟨plan3918,valid3918,t5_685choices,?_⟩
  exact check_of_frontier tree 0 t5_685root t5_685jobs t5_685frontier t5_685all
theorem t5_686choices : plan3739.choices=[2,2,5,3,3].map (options 5 1) := by rfl


theorem t5_686part0 : t5_686jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_686frontier : t5_686root.frontier 0=t5_686jobs := by rfl
theorem t5_686all : t5_686jobs.all (Job.check tree)=true := by
  simp only [t5_686jobs,List.all_append,List.all_nil,t5_686part0,Bool.and_self]
theorem t5_686checked : Checked tree [2,2,5,3,3] := by
  refine ⟨plan3739,valid3739,t5_686choices,?_⟩
  exact check_of_frontier tree 0 t5_686root t5_686jobs t5_686frontier t5_686all
theorem t5_687choices : plan3919.choices=[2,2,5,3,6].map (options 5 2) := by rfl


theorem t5_687part0 : t5_687jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_687frontier : t5_687root.frontier 0=t5_687jobs := by rfl
theorem t5_687all : t5_687jobs.all (Job.check tree)=true := by
  simp only [t5_687jobs,List.all_append,List.all_nil,t5_687part0,Bool.and_self]
theorem t5_687checked : Checked tree [2,2,5,3,6] := by
  refine ⟨plan3919,valid3919,t5_687choices,?_⟩
  exact check_of_frontier tree 0 t5_687root t5_687jobs t5_687frontier t5_687all
theorem t5_688choices : plan3920.choices=[2,2,5,3,7].map (options 5 2) := by rfl


theorem t5_688part0 : t5_688jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_688part1 : t5_688jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_688frontier : t5_688root.frontier 1=t5_688jobs := by rfl
theorem t5_688all : t5_688jobs.all (Job.check tree)=true := by
  simp only [t5_688jobs,List.all_append,List.all_nil,t5_688part0,t5_688part1,Bool.and_self]
theorem t5_688checked : Checked tree [2,2,5,3,7] := by
  refine ⟨plan3920,valid3920,t5_688choices,?_⟩
  exact check_of_frontier tree 1 t5_688root t5_688jobs t5_688frontier t5_688all
theorem t5_689choices : plan3921.choices=[2,2,5,3,10].map (options 5 2) := by rfl


theorem t5_689part0 : t5_689jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_689frontier : t5_689root.frontier 0=t5_689jobs := by rfl
theorem t5_689all : t5_689jobs.all (Job.check tree)=true := by
  simp only [t5_689jobs,List.all_append,List.all_nil,t5_689part0,Bool.and_self]
theorem t5_689checked : Checked tree [2,2,5,3,10] := by
  refine ⟨plan3921,valid3921,t5_689choices,?_⟩
  exact check_of_frontier tree 0 t5_689root t5_689jobs t5_689frontier t5_689all
theorem t5_690choices : plan3922.choices=[2,2,5,5,3].map (options 5 2) := by rfl


theorem t5_690part0 : t5_690jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_690frontier : t5_690root.frontier 0=t5_690jobs := by rfl
theorem t5_690all : t5_690jobs.all (Job.check tree)=true := by
  simp only [t5_690jobs,List.all_append,List.all_nil,t5_690part0,Bool.and_self]
theorem t5_690checked : Checked tree [2,2,5,5,3] := by
  refine ⟨plan3922,valid3922,t5_690choices,?_⟩
  exact check_of_frontier tree 0 t5_690root t5_690jobs t5_690frontier t5_690all
theorem t5_691choices : plan4234.choices=[2,2,5,5,5].map (options 5 3) := by rfl


theorem t5_691part0 : t5_691jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_691frontier : t5_691root.frontier 0=t5_691jobs := by rfl
theorem t5_691all : t5_691jobs.all (Job.check tree)=true := by
  simp only [t5_691jobs,List.all_append,List.all_nil,t5_691part0,Bool.and_self]
theorem t5_691checked : Checked tree [2,2,5,5,5] := by
  refine ⟨plan4234,valid4234,t5_691choices,?_⟩
  exact check_of_frontier tree 0 t5_691root t5_691jobs t5_691frontier t5_691all
theorem t5_692choices : plan4235.choices=[2,2,5,5,6].map (options 5 3) := by rfl


theorem t5_692part0 : t5_692jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_692frontier : t5_692root.frontier 0=t5_692jobs := by rfl
theorem t5_692all : t5_692jobs.all (Job.check tree)=true := by
  simp only [t5_692jobs,List.all_append,List.all_nil,t5_692part0,Bool.and_self]
theorem t5_692checked : Checked tree [2,2,5,5,6] := by
  refine ⟨plan4235,valid4235,t5_692choices,?_⟩
  exact check_of_frontier tree 0 t5_692root t5_692jobs t5_692frontier t5_692all
theorem t5_693choices : plan4236.choices=[2,2,5,5,7].map (options 5 3) := by rfl


theorem t5_693part0 : t5_693jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_693frontier : t5_693root.frontier 0=t5_693jobs := by rfl
theorem t5_693all : t5_693jobs.all (Job.check tree)=true := by
  simp only [t5_693jobs,List.all_append,List.all_nil,t5_693part0,Bool.and_self]
theorem t5_693checked : Checked tree [2,2,5,5,7] := by
  refine ⟨plan4236,valid4236,t5_693choices,?_⟩
  exact check_of_frontier tree 0 t5_693root t5_693jobs t5_693frontier t5_693all
theorem t5_694choices : plan4237.choices=[2,2,5,5,9].map (options 5 3) := by rfl


theorem t5_694part0 : t5_694jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_694frontier : t5_694root.frontier 0=t5_694jobs := by rfl
theorem t5_694all : t5_694jobs.all (Job.check tree)=true := by
  simp only [t5_694jobs,List.all_append,List.all_nil,t5_694part0,Bool.and_self]
theorem t5_694checked : Checked tree [2,2,5,5,9] := by
  refine ⟨plan4237,valid4237,t5_694choices,?_⟩
  exact check_of_frontier tree 0 t5_694root t5_694jobs t5_694frontier t5_694all
theorem t5_695choices : plan4238.choices=[2,2,5,5,10].map (options 5 3) := by rfl


theorem t5_695part0 : t5_695jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_695frontier : t5_695root.frontier 0=t5_695jobs := by rfl
theorem t5_695all : t5_695jobs.all (Job.check tree)=true := by
  simp only [t5_695jobs,List.all_append,List.all_nil,t5_695part0,Bool.and_self]
theorem t5_695checked : Checked tree [2,2,5,5,10] := by
  refine ⟨plan4238,valid4238,t5_695choices,?_⟩
  exact check_of_frontier tree 0 t5_695root t5_695jobs t5_695frontier t5_695all
theorem t5_696choices : plan4239.choices=[2,2,5,6,6].map (options 5 3) := by rfl


theorem t5_696part0 : t5_696jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_696frontier : t5_696root.frontier 0=t5_696jobs := by rfl
theorem t5_696all : t5_696jobs.all (Job.check tree)=true := by
  simp only [t5_696jobs,List.all_append,List.all_nil,t5_696part0,Bool.and_self]
theorem t5_696checked : Checked tree [2,2,5,6,6] := by
  refine ⟨plan4239,valid4239,t5_696choices,?_⟩
  exact check_of_frontier tree 0 t5_696root t5_696jobs t5_696frontier t5_696all
theorem t5_697choices : plan4240.choices=[2,2,5,6,7].map (options 5 3) := by rfl


theorem t5_697part0 : t5_697jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_697frontier : t5_697root.frontier 0=t5_697jobs := by rfl
theorem t5_697all : t5_697jobs.all (Job.check tree)=true := by
  simp only [t5_697jobs,List.all_append,List.all_nil,t5_697part0,Bool.and_self]
theorem t5_697checked : Checked tree [2,2,5,6,7] := by
  refine ⟨plan4240,valid4240,t5_697choices,?_⟩
  exact check_of_frontier tree 0 t5_697root t5_697jobs t5_697frontier t5_697all
theorem t5_698choices : plan4241.choices=[2,2,5,6,10].map (options 5 3) := by rfl


theorem t5_698part0 : t5_698jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_698frontier : t5_698root.frontier 0=t5_698jobs := by rfl
theorem t5_698all : t5_698jobs.all (Job.check tree)=true := by
  simp only [t5_698jobs,List.all_append,List.all_nil,t5_698part0,Bool.and_self]
theorem t5_698checked : Checked tree [2,2,5,6,10] := by
  refine ⟨plan4241,valid4241,t5_698choices,?_⟩
  exact check_of_frontier tree 0 t5_698root t5_698jobs t5_698frontier t5_698all
theorem t5_699choices : plan4242.choices=[2,2,5,7,7].map (options 5 3) := by rfl


theorem t5_699part0 : t5_699jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_699frontier : t5_699root.frontier 0=t5_699jobs := by rfl
theorem t5_699all : t5_699jobs.all (Job.check tree)=true := by
  simp only [t5_699jobs,List.all_append,List.all_nil,t5_699part0,Bool.and_self]
theorem t5_699checked : Checked tree [2,2,5,7,7] := by
  refine ⟨plan4242,valid4242,t5_699choices,?_⟩
  exact check_of_frontier tree 0 t5_699root t5_699jobs t5_699frontier t5_699all
theorem t5_700choices : plan3923.choices=[2,2,5,9,3].map (options 5 2) := by rfl


theorem t5_700part0 : t5_700jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_700frontier : t5_700root.frontier 0=t5_700jobs := by rfl
theorem t5_700all : t5_700jobs.all (Job.check tree)=true := by
  simp only [t5_700jobs,List.all_append,List.all_nil,t5_700part0,Bool.and_self]
theorem t5_700checked : Checked tree [2,2,5,9,3] := by
  refine ⟨plan3923,valid3923,t5_700choices,?_⟩
  exact check_of_frontier tree 0 t5_700root t5_700jobs t5_700frontier t5_700all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks015 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_688checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_689checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_690checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_691checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_692checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_693checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_694checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_695checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_696checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_679checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_697checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_698checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_699checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_700checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_680checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_681checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_682checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_683checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_684checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_685checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_686checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_678checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_687checked⟩
