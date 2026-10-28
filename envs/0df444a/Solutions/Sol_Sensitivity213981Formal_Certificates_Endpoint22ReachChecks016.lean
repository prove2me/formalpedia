-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks016
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:47:11.042496+00:00
-- url     : https://prove2.me/submissions/45055b9d-40ce-4117-85b8-a5254f07a67a

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks016
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



















theorem valid463 : plan463.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid464 : plan464.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid465 : plan465.Valid := valid_step _ _ _ valid99 (by decide +kernel)





















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



























theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)



theorem valid499 : plan499.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid500 : plan500.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid501 : plan501.Valid := valid_step _ _ _ valid104 (by decide +kernel)

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









































theorem valid1269 : plan1269.Valid := valid_step _ _ _ valid453 (by decide +kernel)





























































































theorem valid1316 : plan1316.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1317 : plan1317.Valid := valid_step _ _ _ valid464 (by decide +kernel)

theorem valid1318 : plan1318.Valid := valid_step _ _ _ valid465 (by decide +kernel)

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























































































































































































theorem valid3740 : plan3740.Valid := valid_step _ _ _ valid2548 (by decide +kernel)








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







































theorem valid1364 : plan1364.Valid := valid_step _ _ _ valid499 (by decide +kernel)

theorem valid1365 : plan1365.Valid := valid_step _ _ _ valid500 (by decide +kernel)

theorem valid1366 : plan1366.Valid := valid_step _ _ _ valid501 (by decide +kernel)

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

theorem valid1387 : plan1387.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1388 : plan1388.Valid := valid_step _ _ _ valid497 (by decide +kernel)



theorem valid1390 : plan1390.Valid := valid_step _ _ _ valid499 (by decide +kernel)

theorem valid1391 : plan1391.Valid := valid_step _ _ _ valid500 (by decide +kernel)

theorem valid1392 : plan1392.Valid := valid_step _ _ _ valid501 (by decide +kernel)

theorem valid1393 : plan1393.Valid := valid_step _ _ _ valid502 (by decide +kernel)

theorem valid1394 : plan1394.Valid := valid_step _ _ _ valid503 (by decide +kernel)




























































































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





























































theorem valid2623 : plan2623.Valid := valid_step _ _ _ valid1316 (by decide +kernel)

theorem valid2624 : plan2624.Valid := valid_step _ _ _ valid1317 (by decide +kernel)

theorem valid2625 : plan2625.Valid := valid_step _ _ _ valid1318 (by decide +kernel)

theorem valid2626 : plan2626.Valid := valid_step _ _ _ valid1319 (by decide +kernel)




























































































































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























































































theorem valid2732 : plan2732.Valid := valid_step _ _ _ valid1364 (by decide +kernel)

theorem valid2733 : plan2733.Valid := valid_step _ _ _ valid1365 (by decide +kernel)

theorem valid2734 : plan2734.Valid := valid_step _ _ _ valid1366 (by decide +kernel)

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

theorem valid2750 : plan2750.Valid := valid_step _ _ _ valid1387 (by decide +kernel)

theorem valid2751 : plan2751.Valid := valid_step _ _ _ valid1388 (by decide +kernel)



theorem valid2753 : plan2753.Valid := valid_step _ _ _ valid1390 (by decide +kernel)

theorem valid2754 : plan2754.Valid := valid_step _ _ _ valid1391 (by decide +kernel)

theorem valid2755 : plan2755.Valid := valid_step _ _ _ valid1392 (by decide +kernel)

theorem valid2756 : plan2756.Valid := valid_step _ _ _ valid1393 (by decide +kernel)

theorem valid2757 : plan2757.Valid := valid_step _ _ _ valid1394 (by decide +kernel)






















































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







































































































































































theorem valid3924 : plan3924.Valid := valid_step _ _ _ valid2623 (by decide +kernel)

theorem valid3925 : plan3925.Valid := valid_step _ _ _ valid2624 (by decide +kernel)

theorem valid3926 : plan3926.Valid := valid_step _ _ _ valid2625 (by decide +kernel)

theorem valid3927 : plan3927.Valid := valid_step _ _ _ valid2626 (by decide +kernel)


















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





































theorem valid4243 : plan4243.Valid := valid_step _ _ _ valid2732 (by decide +kernel)

theorem valid4244 : plan4244.Valid := valid_step _ _ _ valid2733 (by decide +kernel)

theorem valid4245 : plan4245.Valid := valid_step _ _ _ valid2734 (by decide +kernel)

theorem valid4246 : plan4246.Valid := valid_step _ _ _ valid2735 (by decide +kernel)

theorem valid4247 : plan4247.Valid := valid_step _ _ _ valid2736 (by decide +kernel)

theorem valid4248 : plan4248.Valid := valid_step _ _ _ valid2737 (by decide +kernel)

theorem valid4249 : plan4249.Valid := valid_step _ _ _ valid2738 (by decide +kernel)

theorem valid4250 : plan4250.Valid := valid_step _ _ _ valid2739 (by decide +kernel)

theorem valid4251 : plan4251.Valid := valid_step _ _ _ valid2740 (by decide +kernel)

theorem valid4252 : plan4252.Valid := valid_step _ _ _ valid2741 (by decide +kernel)

theorem valid4253 : plan4253.Valid := valid_step _ _ _ valid2742 (by decide +kernel)

theorem valid4254 : plan4254.Valid := valid_step _ _ _ valid2743 (by decide +kernel)

theorem valid4255 : plan4255.Valid := valid_step _ _ _ valid2744 (by decide +kernel)

theorem valid4256 : plan4256.Valid := valid_step _ _ _ valid2748 (by decide +kernel)

theorem valid4257 : plan4257.Valid := valid_step _ _ _ valid2749 (by decide +kernel)

theorem valid4258 : plan4258.Valid := valid_step _ _ _ valid2750 (by decide +kernel)

theorem valid4259 : plan4259.Valid := valid_step _ _ _ valid2751 (by decide +kernel)

theorem valid4260 : plan4260.Valid := valid_step _ _ _ valid2753 (by decide +kernel)

theorem valid4261 : plan4261.Valid := valid_step _ _ _ valid2754 (by decide +kernel)

theorem valid4262 : plan4262.Valid := valid_step _ _ _ valid2755 (by decide +kernel)

theorem valid4263 : plan4263.Valid := valid_step _ _ _ valid2756 (by decide +kernel)

theorem valid4264 : plan4264.Valid := valid_step _ _ _ valid2757 (by decide +kernel)
















































































































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
theorem t5_701choices : plan4243.choices=[2,2,5,9,6].map (options 5 3) := by rfl


theorem t5_701part0 : t5_701jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_701frontier : t5_701root.frontier 0=t5_701jobs := by rfl
theorem t5_701all : t5_701jobs.all (Job.check tree)=true := by
  simp only [t5_701jobs,List.all_append,List.all_nil,t5_701part0,Bool.and_self]
theorem t5_701checked : Checked tree [2,2,5,9,6] := by
  refine ⟨plan4243,valid4243,t5_701choices,?_⟩
  exact check_of_frontier tree 0 t5_701root t5_701jobs t5_701frontier t5_701all
theorem t5_702choices : plan4244.choices=[2,2,5,9,7].map (options 5 3) := by rfl


theorem t5_702part0 : t5_702jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_702frontier : t5_702root.frontier 0=t5_702jobs := by rfl
theorem t5_702all : t5_702jobs.all (Job.check tree)=true := by
  simp only [t5_702jobs,List.all_append,List.all_nil,t5_702part0,Bool.and_self]
theorem t5_702checked : Checked tree [2,2,5,9,7] := by
  refine ⟨plan4244,valid4244,t5_702choices,?_⟩
  exact check_of_frontier tree 0 t5_702root t5_702jobs t5_702frontier t5_702all
theorem t5_703choices : plan4245.choices=[2,2,5,9,9].map (options 5 3) := by rfl


theorem t5_703part0 : t5_703jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_703frontier : t5_703root.frontier 0=t5_703jobs := by rfl
theorem t5_703all : t5_703jobs.all (Job.check tree)=true := by
  simp only [t5_703jobs,List.all_append,List.all_nil,t5_703part0,Bool.and_self]
theorem t5_703checked : Checked tree [2,2,5,9,9] := by
  refine ⟨plan4245,valid4245,t5_703choices,?_⟩
  exact check_of_frontier tree 0 t5_703root t5_703jobs t5_703frontier t5_703all
theorem t5_704choices : plan4246.choices=[2,2,5,9,10].map (options 5 3) := by rfl


theorem t5_704part0 : t5_704jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_704frontier : t5_704root.frontier 0=t5_704jobs := by rfl
theorem t5_704all : t5_704jobs.all (Job.check tree)=true := by
  simp only [t5_704jobs,List.all_append,List.all_nil,t5_704part0,Bool.and_self]
theorem t5_704checked : Checked tree [2,2,5,9,10] := by
  refine ⟨plan4246,valid4246,t5_704choices,?_⟩
  exact check_of_frontier tree 0 t5_704root t5_704jobs t5_704frontier t5_704all
theorem t5_705choices : plan4247.choices=[2,2,5,10,7].map (options 5 3) := by rfl


theorem t5_705part0 : t5_705jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_705frontier : t5_705root.frontier 0=t5_705jobs := by rfl
theorem t5_705all : t5_705jobs.all (Job.check tree)=true := by
  simp only [t5_705jobs,List.all_append,List.all_nil,t5_705part0,Bool.and_self]
theorem t5_705checked : Checked tree [2,2,5,10,7] := by
  refine ⟨plan4247,valid4247,t5_705choices,?_⟩
  exact check_of_frontier tree 0 t5_705root t5_705jobs t5_705frontier t5_705all
theorem t5_706choices : plan4248.choices=[2,2,5,10,10].map (options 5 3) := by rfl


theorem t5_706part0 : t5_706jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_706frontier : t5_706root.frontier 0=t5_706jobs := by rfl
theorem t5_706all : t5_706jobs.all (Job.check tree)=true := by
  simp only [t5_706jobs,List.all_append,List.all_nil,t5_706part0,Bool.and_self]
theorem t5_706checked : Checked tree [2,2,5,10,10] := by
  refine ⟨plan4248,valid4248,t5_706choices,?_⟩
  exact check_of_frontier tree 0 t5_706root t5_706jobs t5_706frontier t5_706all
theorem t5_707choices : plan4249.choices=[2,2,6,6,6].map (options 5 3) := by rfl


theorem t5_707part0 : t5_707jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_707frontier : t5_707root.frontier 0=t5_707jobs := by rfl
theorem t5_707all : t5_707jobs.all (Job.check tree)=true := by
  simp only [t5_707jobs,List.all_append,List.all_nil,t5_707part0,Bool.and_self]
theorem t5_707checked : Checked tree [2,2,6,6,6] := by
  refine ⟨plan4249,valid4249,t5_707choices,?_⟩
  exact check_of_frontier tree 0 t5_707root t5_707jobs t5_707frontier t5_707all
theorem t5_708choices : plan4250.choices=[2,2,6,6,7].map (options 5 3) := by rfl


theorem t5_708part0 : t5_708jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_708frontier : t5_708root.frontier 0=t5_708jobs := by rfl
theorem t5_708all : t5_708jobs.all (Job.check tree)=true := by
  simp only [t5_708jobs,List.all_append,List.all_nil,t5_708part0,Bool.and_self]
theorem t5_708checked : Checked tree [2,2,6,6,7] := by
  refine ⟨plan4250,valid4250,t5_708choices,?_⟩
  exact check_of_frontier tree 0 t5_708root t5_708jobs t5_708frontier t5_708all
theorem t5_709choices : plan4251.choices=[2,2,6,6,10].map (options 5 3) := by rfl


theorem t5_709part0 : t5_709jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_709frontier : t5_709root.frontier 0=t5_709jobs := by rfl
theorem t5_709all : t5_709jobs.all (Job.check tree)=true := by
  simp only [t5_709jobs,List.all_append,List.all_nil,t5_709part0,Bool.and_self]
theorem t5_709checked : Checked tree [2,2,6,6,10] := by
  refine ⟨plan4251,valid4251,t5_709choices,?_⟩
  exact check_of_frontier tree 0 t5_709root t5_709jobs t5_709frontier t5_709all
theorem t5_710choices : plan4252.choices=[2,2,6,7,7].map (options 5 3) := by rfl


theorem t5_710part0 : t5_710jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_710frontier : t5_710root.frontier 0=t5_710jobs := by rfl
theorem t5_710all : t5_710jobs.all (Job.check tree)=true := by
  simp only [t5_710jobs,List.all_append,List.all_nil,t5_710part0,Bool.and_self]
theorem t5_710checked : Checked tree [2,2,6,7,7] := by
  refine ⟨plan4252,valid4252,t5_710choices,?_⟩
  exact check_of_frontier tree 0 t5_710root t5_710jobs t5_710frontier t5_710all
theorem t5_711choices : plan4253.choices=[2,2,6,10,7].map (options 5 3) := by rfl


theorem t5_711part0 : t5_711jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_711part1 : t5_711jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_711frontier : t5_711root.frontier 1=t5_711jobs := by rfl
theorem t5_711all : t5_711jobs.all (Job.check tree)=true := by
  simp only [t5_711jobs,List.all_append,List.all_nil,t5_711part0,t5_711part1,Bool.and_self]
theorem t5_711checked : Checked tree [2,2,6,10,7] := by
  refine ⟨plan4253,valid4253,t5_711choices,?_⟩
  exact check_of_frontier tree 1 t5_711root t5_711jobs t5_711frontier t5_711all
theorem t5_712choices : plan4254.choices=[2,2,6,10,10].map (options 5 3) := by rfl


theorem t5_712part0 : t5_712jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_712frontier : t5_712root.frontier 0=t5_712jobs := by rfl
theorem t5_712all : t5_712jobs.all (Job.check tree)=true := by
  simp only [t5_712jobs,List.all_append,List.all_nil,t5_712part0,Bool.and_self]
theorem t5_712checked : Checked tree [2,2,6,10,10] := by
  refine ⟨plan4254,valid4254,t5_712choices,?_⟩
  exact check_of_frontier tree 0 t5_712root t5_712jobs t5_712frontier t5_712all
theorem t5_713choices : plan4255.choices=[2,2,7,7,7].map (options 5 3) := by rfl


theorem t5_713part0 : t5_713jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_713frontier : t5_713root.frontier 0=t5_713jobs := by rfl
theorem t5_713all : t5_713jobs.all (Job.check tree)=true := by
  simp only [t5_713jobs,List.all_append,List.all_nil,t5_713part0,Bool.and_self]
theorem t5_713checked : Checked tree [2,2,7,7,7] := by
  refine ⟨plan4255,valid4255,t5_713choices,?_⟩
  exact check_of_frontier tree 0 t5_713root t5_713jobs t5_713frontier t5_713all
theorem t5_714choices : plan3740.choices=[2,2,9,3,3].map (options 5 1) := by rfl


theorem t5_714part0 : t5_714jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_714frontier : t5_714root.frontier 0=t5_714jobs := by rfl
theorem t5_714all : t5_714jobs.all (Job.check tree)=true := by
  simp only [t5_714jobs,List.all_append,List.all_nil,t5_714part0,Bool.and_self]
theorem t5_714checked : Checked tree [2,2,9,3,3] := by
  refine ⟨plan3740,valid3740,t5_714choices,?_⟩
  exact check_of_frontier tree 0 t5_714root t5_714jobs t5_714frontier t5_714all
theorem t5_715choices : plan3924.choices=[2,2,9,3,6].map (options 5 2) := by rfl


theorem t5_715part0 : t5_715jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_715frontier : t5_715root.frontier 0=t5_715jobs := by rfl
theorem t5_715all : t5_715jobs.all (Job.check tree)=true := by
  simp only [t5_715jobs,List.all_append,List.all_nil,t5_715part0,Bool.and_self]
theorem t5_715checked : Checked tree [2,2,9,3,6] := by
  refine ⟨plan3924,valid3924,t5_715choices,?_⟩
  exact check_of_frontier tree 0 t5_715root t5_715jobs t5_715frontier t5_715all
theorem t5_716choices : plan3925.choices=[2,2,9,3,7].map (options 5 2) := by rfl


theorem t5_716part0 : t5_716jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_716part1 : t5_716jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_716frontier : t5_716root.frontier 1=t5_716jobs := by rfl
theorem t5_716all : t5_716jobs.all (Job.check tree)=true := by
  simp only [t5_716jobs,List.all_append,List.all_nil,t5_716part0,t5_716part1,Bool.and_self]
theorem t5_716checked : Checked tree [2,2,9,3,7] := by
  refine ⟨plan3925,valid3925,t5_716choices,?_⟩
  exact check_of_frontier tree 1 t5_716root t5_716jobs t5_716frontier t5_716all
theorem t5_717choices : plan3926.choices=[2,2,9,3,10].map (options 5 2) := by rfl


theorem t5_717part0 : t5_717jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_717frontier : t5_717root.frontier 0=t5_717jobs := by rfl
theorem t5_717all : t5_717jobs.all (Job.check tree)=true := by
  simp only [t5_717jobs,List.all_append,List.all_nil,t5_717part0,Bool.and_self]
theorem t5_717checked : Checked tree [2,2,9,3,10] := by
  refine ⟨plan3926,valid3926,t5_717choices,?_⟩
  exact check_of_frontier tree 0 t5_717root t5_717jobs t5_717frontier t5_717all
theorem t5_718choices : plan4256.choices=[2,2,9,6,6].map (options 5 3) := by rfl


theorem t5_718part0 : t5_718jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_718frontier : t5_718root.frontier 0=t5_718jobs := by rfl
theorem t5_718all : t5_718jobs.all (Job.check tree)=true := by
  simp only [t5_718jobs,List.all_append,List.all_nil,t5_718part0,Bool.and_self]
theorem t5_718checked : Checked tree [2,2,9,6,6] := by
  refine ⟨plan4256,valid4256,t5_718choices,?_⟩
  exact check_of_frontier tree 0 t5_718root t5_718jobs t5_718frontier t5_718all
theorem t5_719choices : plan4257.choices=[2,2,9,6,7].map (options 5 3) := by rfl


theorem t5_719part0 : t5_719jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_719frontier : t5_719root.frontier 0=t5_719jobs := by rfl
theorem t5_719all : t5_719jobs.all (Job.check tree)=true := by
  simp only [t5_719jobs,List.all_append,List.all_nil,t5_719part0,Bool.and_self]
theorem t5_719checked : Checked tree [2,2,9,6,7] := by
  refine ⟨plan4257,valid4257,t5_719choices,?_⟩
  exact check_of_frontier tree 0 t5_719root t5_719jobs t5_719frontier t5_719all
theorem t5_720choices : plan4258.choices=[2,2,9,6,10].map (options 5 3) := by rfl


theorem t5_720part0 : t5_720jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_720frontier : t5_720root.frontier 0=t5_720jobs := by rfl
theorem t5_720all : t5_720jobs.all (Job.check tree)=true := by
  simp only [t5_720jobs,List.all_append,List.all_nil,t5_720part0,Bool.and_self]
theorem t5_720checked : Checked tree [2,2,9,6,10] := by
  refine ⟨plan4258,valid4258,t5_720choices,?_⟩
  exact check_of_frontier tree 0 t5_720root t5_720jobs t5_720frontier t5_720all
theorem t5_721choices : plan4259.choices=[2,2,9,7,7].map (options 5 3) := by rfl


theorem t5_721part0 : t5_721jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_721frontier : t5_721root.frontier 0=t5_721jobs := by rfl
theorem t5_721all : t5_721jobs.all (Job.check tree)=true := by
  simp only [t5_721jobs,List.all_append,List.all_nil,t5_721part0,Bool.and_self]
theorem t5_721checked : Checked tree [2,2,9,7,7] := by
  refine ⟨plan4259,valid4259,t5_721choices,?_⟩
  exact check_of_frontier tree 0 t5_721root t5_721jobs t5_721frontier t5_721all
theorem t5_722choices : plan3927.choices=[2,2,9,9,3].map (options 5 2) := by rfl


theorem t5_722part0 : t5_722jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_722frontier : t5_722root.frontier 0=t5_722jobs := by rfl
theorem t5_722all : t5_722jobs.all (Job.check tree)=true := by
  simp only [t5_722jobs,List.all_append,List.all_nil,t5_722part0,Bool.and_self]
theorem t5_722checked : Checked tree [2,2,9,9,3] := by
  refine ⟨plan3927,valid3927,t5_722choices,?_⟩
  exact check_of_frontier tree 0 t5_722root t5_722jobs t5_722frontier t5_722all
theorem t5_723choices : plan4260.choices=[2,2,9,9,6].map (options 5 3) := by rfl


theorem t5_723part0 : t5_723jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_723frontier : t5_723root.frontier 0=t5_723jobs := by rfl
theorem t5_723all : t5_723jobs.all (Job.check tree)=true := by
  simp only [t5_723jobs,List.all_append,List.all_nil,t5_723part0,Bool.and_self]
theorem t5_723checked : Checked tree [2,2,9,9,6] := by
  refine ⟨plan4260,valid4260,t5_723choices,?_⟩
  exact check_of_frontier tree 0 t5_723root t5_723jobs t5_723frontier t5_723all
theorem t5_724choices : plan4261.choices=[2,2,9,9,7].map (options 5 3) := by rfl


theorem t5_724part0 : t5_724jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_724frontier : t5_724root.frontier 0=t5_724jobs := by rfl
theorem t5_724all : t5_724jobs.all (Job.check tree)=true := by
  simp only [t5_724jobs,List.all_append,List.all_nil,t5_724part0,Bool.and_self]
theorem t5_724checked : Checked tree [2,2,9,9,7] := by
  refine ⟨plan4261,valid4261,t5_724choices,?_⟩
  exact check_of_frontier tree 0 t5_724root t5_724jobs t5_724frontier t5_724all
theorem t5_725choices : plan4262.choices=[2,2,9,9,9].map (options 5 3) := by rfl


theorem t5_725part0 : t5_725jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_725frontier : t5_725root.frontier 0=t5_725jobs := by rfl
theorem t5_725all : t5_725jobs.all (Job.check tree)=true := by
  simp only [t5_725jobs,List.all_append,List.all_nil,t5_725part0,Bool.and_self]
theorem t5_725checked : Checked tree [2,2,9,9,9] := by
  refine ⟨plan4262,valid4262,t5_725choices,?_⟩
  exact check_of_frontier tree 0 t5_725root t5_725jobs t5_725frontier t5_725all
theorem t5_726choices : plan4263.choices=[2,2,9,9,10].map (options 5 3) := by rfl


theorem t5_726part0 : t5_726jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_726frontier : t5_726root.frontier 0=t5_726jobs := by rfl
theorem t5_726all : t5_726jobs.all (Job.check tree)=true := by
  simp only [t5_726jobs,List.all_append,List.all_nil,t5_726part0,Bool.and_self]
theorem t5_726checked : Checked tree [2,2,9,9,10] := by
  refine ⟨plan4263,valid4263,t5_726choices,?_⟩
  exact check_of_frontier tree 0 t5_726root t5_726jobs t5_726frontier t5_726all
theorem t5_727choices : plan4264.choices=[2,2,9,10,7].map (options 5 3) := by rfl


theorem t5_727part0 : t5_727jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_727frontier : t5_727root.frontier 0=t5_727jobs := by rfl
theorem t5_727all : t5_727jobs.all (Job.check tree)=true := by
  simp only [t5_727jobs,List.all_append,List.all_nil,t5_727part0,Bool.and_self]
theorem t5_727checked : Checked tree [2,2,9,10,7] := by
  refine ⟨plan4264,valid4264,t5_727choices,?_⟩
  exact check_of_frontier tree 0 t5_727root t5_727jobs t5_727frontier t5_727all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks016 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_713checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_714checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_715checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_716checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_717checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_718checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_719checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_720checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_721checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_702checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_722checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_723checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_724checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_725checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_726checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_727checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_703checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_704checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_705checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_706checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_707checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_708checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_709checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_710checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_711checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_712checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_701checked⟩
