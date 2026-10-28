-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks132
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:48:34.759892+00:00
-- url     : https://prove2.me/submissions/ebabedae-8282-4276-8b78-00c45f487221

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks132
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks132
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
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



















































theorem valid122 : plan122.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid133 : plan133.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid134 : plan134.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid135 : plan135.Valid := valid_step _ _ _ valid0 (by decide +kernel)


















































































































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

theorem valid577 : plan577.Valid := valid_step _ _ _ valid135 (by decide +kernel)



theorem valid579 : plan579.Valid := valid_step _ _ _ valid134 (by decide +kernel)

theorem valid580 : plan580.Valid := valid_step _ _ _ valid135 (by decide +kernel)
























































































































































































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

































































































































theorem valid545 : plan545.Valid := valid_step _ _ _ valid122 (by decide +kernel)





















theorem valid556 : plan556.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid557 : plan557.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid558 : plan558.Valid := valid_step _ _ _ valid129 (by decide +kernel)



















theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)

theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid573 : plan573.Valid := valid_step _ _ _ valid132 (by decide +kernel)



theorem valid575 : plan575.Valid := valid_step _ _ _ valid133 (by decide +kernel)

theorem valid576 : plan576.Valid := valid_step _ _ _ valid134 (by decide +kernel)
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





















































































































































theorem valid1515 : plan1515.Valid := valid_step _ _ _ valid545 (by decide +kernel)



























theorem valid1529 : plan1529.Valid := valid_step _ _ _ valid556 (by decide +kernel)

theorem valid1530 : plan1530.Valid := valid_step _ _ _ valid557 (by decide +kernel)

theorem valid1531 : plan1531.Valid := valid_step _ _ _ valid558 (by decide +kernel)










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































































































































































































theorem valid3264 : plan3264.Valid := valid_step _ _ _ valid1515 (by decide +kernel)
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













































theorem valid1559 : plan1559.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1561 : plan1561.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1564 : plan1564.Valid := valid_step _ _ _ valid573 (by decide +kernel)

























































theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)



















theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1606 : plan1606.Valid := valid_step _ _ _ valid580 (by decide +kernel)




















































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













































































theorem valid3303 : plan3303.Valid := valid_step _ _ _ valid1529 (by decide +kernel)

theorem valid3304 : plan3304.Valid := valid_step _ _ _ valid1530 (by decide +kernel)

theorem valid3305 : plan3305.Valid := valid_step _ _ _ valid1531 (by decide +kernel)

































































































theorem valid3354 : plan3354.Valid := valid_step _ _ _ valid1559 (by decide +kernel)

theorem valid3355 : plan3355.Valid := valid_step _ _ _ valid1560 (by decide +kernel)

theorem valid3356 : plan3356.Valid := valid_step _ _ _ valid1561 (by decide +kernel)

theorem valid3357 : plan3357.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3358 : plan3358.Valid := valid_step _ _ _ valid1563 (by decide +kernel)

theorem valid3359 : plan3359.Valid := valid_step _ _ _ valid1564 (by decide +kernel)


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





















































theorem valid5403 : plan5403.Valid := valid_step _ _ _ valid3264 (by decide +kernel)










































































































































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































































































































































theorem valid3440 : plan3440.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3441 : plan3441.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3442 : plan3442.Valid := valid_step _ _ _ valid1595 (by decide +kernel)




























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

























































theorem valid5501 : plan5501.Valid := valid_step _ _ _ valid3303 (by decide +kernel)

theorem valid5502 : plan5502.Valid := valid_step _ _ _ valid3304 (by decide +kernel)

theorem valid5503 : plan5503.Valid := valid_step _ _ _ valid3305 (by decide +kernel)


































































































































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



























































































































































































theorem valid5662 : plan5662.Valid := valid_step _ _ _ valid3354 (by decide +kernel)

theorem valid5663 : plan5663.Valid := valid_step _ _ _ valid3355 (by decide +kernel)

theorem valid5664 : plan5664.Valid := valid_step _ _ _ valid3356 (by decide +kernel)
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



















































theorem valid6650 : plan6650.Valid := valid_step _ _ _ valid5501 (by decide +kernel)

theorem valid6651 : plan6651.Valid := valid_step _ _ _ valid5502 (by decide +kernel)

theorem valid6652 : plan6652.Valid := valid_step _ _ _ valid5503 (by decide +kernel)








































































































































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









































































































theorem valid3509 : plan3509.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3510 : plan3510.Valid := valid_step _ _ _ valid1606 (by decide +kernel)




















































































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

theorem valid5665 : plan5665.Valid := valid_step _ _ _ valid3357 (by decide +kernel)

theorem valid5666 : plan5666.Valid := valid_step _ _ _ valid3358 (by decide +kernel)

theorem valid5667 : plan5667.Valid := valid_step _ _ _ valid3359 (by decide +kernel)


























































































































































































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













































theorem valid5783 : plan5783.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5784 : plan5784.Valid := valid_step _ _ _ valid3510 (by decide +kernel)



























































theorem valid5814 : plan5814.Valid := valid_step _ _ _ valid3440 (by decide +kernel)

theorem valid5815 : plan5815.Valid := valid_step _ _ _ valid3441 (by decide +kernel)

theorem valid5816 : plan5816.Valid := valid_step _ _ _ valid3442 (by decide +kernel)
















































































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





































































































































































theorem valid6419 : plan6419.Valid := valid_step _ _ _ valid5403 (by decide +kernel)


























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

























































































theorem valid7053 : plan7053.Valid := valid_step _ _ _ valid5662 (by decide +kernel)

theorem valid7054 : plan7054.Valid := valid_step _ _ _ valid5663 (by decide +kernel)

theorem valid7055 : plan7055.Valid := valid_step _ _ _ valid5664 (by decide +kernel)

theorem valid7056 : plan7056.Valid := valid_step _ _ _ valid5665 (by decide +kernel)

theorem valid7057 : plan7057.Valid := valid_step _ _ _ valid5666 (by decide +kernel)

theorem valid7058 : plan7058.Valid := valid_step _ _ _ valid5667 (by decide +kernel)




























































































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













































































































theorem valid7543 : plan7543.Valid := valid_step _ _ _ valid5783 (by decide +kernel)

theorem valid7544 : plan7544.Valid := valid_step _ _ _ valid5784 (by decide +kernel)

theorem valid7545 : plan7545.Valid := valid_step _ _ _ valid5814 (by decide +kernel)

theorem valid7546 : plan7546.Valid := valid_step _ _ _ valid5815 (by decide +kernel)

theorem valid7547 : plan7547.Valid := valid_step _ _ _ valid5816 (by decide +kernel)










































































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
theorem t6_1220choices : plan7543.choices=[5,3,10,10,10,7].map (options 6 5) := by rfl


theorem t6_1220part0 : t6_1220jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1220part1 : t6_1220jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1220frontier : t6_1220root.frontier 1=t6_1220jobs := by rfl
theorem t6_1220all : t6_1220jobs.all (Job.check tree)=true := by
  simp only [t6_1220jobs,List.all_append,List.all_nil,t6_1220part0,t6_1220part1,Bool.and_self]
theorem t6_1220checked : Checked tree [5,3,10,10,10,7] := by
  refine ⟨plan7543,valid7543,t6_1220choices,?_⟩
  exact check_of_frontier tree 1 t6_1220root t6_1220jobs t6_1220frontier t6_1220all
theorem t6_1221choices : plan7544.choices=[5,3,10,10,10,10].map (options 6 5) := by rfl


theorem t6_1221part0 : t6_1221jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1221frontier : t6_1221root.frontier 0=t6_1221jobs := by rfl
theorem t6_1221all : t6_1221jobs.all (Job.check tree)=true := by
  simp only [t6_1221jobs,List.all_append,List.all_nil,t6_1221part0,Bool.and_self]
theorem t6_1221checked : Checked tree [5,3,10,10,10,10] := by
  refine ⟨plan7544,valid7544,t6_1221choices,?_⟩
  exact check_of_frontier tree 0 t6_1221root t6_1221jobs t6_1221frontier t6_1221all
theorem t6_1222choices : plan6419.choices=[5,5,3,3,3,3].map (options 6 2) := by rfl


theorem t6_1222part0 : t6_1222jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1222frontier : t6_1222root.frontier 0=t6_1222jobs := by rfl
theorem t6_1222all : t6_1222jobs.all (Job.check tree)=true := by
  simp only [t6_1222jobs,List.all_append,List.all_nil,t6_1222part0,Bool.and_self]
theorem t6_1222checked : Checked tree [5,5,3,3,3,3] := by
  refine ⟨plan6419,valid6419,t6_1222choices,?_⟩
  exact check_of_frontier tree 0 t6_1222root t6_1222jobs t6_1222frontier t6_1222all
theorem t6_1223choices : plan6650.choices=[5,5,3,3,3,6].map (options 6 3) := by rfl


theorem t6_1223part0 : t6_1223jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1223frontier : t6_1223root.frontier 0=t6_1223jobs := by rfl
theorem t6_1223all : t6_1223jobs.all (Job.check tree)=true := by
  simp only [t6_1223jobs,List.all_append,List.all_nil,t6_1223part0,Bool.and_self]
theorem t6_1223checked : Checked tree [5,5,3,3,3,6] := by
  refine ⟨plan6650,valid6650,t6_1223choices,?_⟩
  exact check_of_frontier tree 0 t6_1223root t6_1223jobs t6_1223frontier t6_1223all
theorem t6_1224choices : plan6651.choices=[5,5,3,3,3,7].map (options 6 3) := by rfl


theorem t6_1224part0 : t6_1224jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1224part1 : t6_1224jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1224frontier : t6_1224root.frontier 1=t6_1224jobs := by rfl
theorem t6_1224all : t6_1224jobs.all (Job.check tree)=true := by
  simp only [t6_1224jobs,List.all_append,List.all_nil,t6_1224part0,t6_1224part1,Bool.and_self]
theorem t6_1224checked : Checked tree [5,5,3,3,3,7] := by
  refine ⟨plan6651,valid6651,t6_1224choices,?_⟩
  exact check_of_frontier tree 1 t6_1224root t6_1224jobs t6_1224frontier t6_1224all
theorem t6_1225choices : plan6652.choices=[5,5,3,3,3,10].map (options 6 3) := by rfl


theorem t6_1225part0 : t6_1225jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1225frontier : t6_1225root.frontier 0=t6_1225jobs := by rfl
theorem t6_1225all : t6_1225jobs.all (Job.check tree)=true := by
  simp only [t6_1225jobs,List.all_append,List.all_nil,t6_1225part0,Bool.and_self]
theorem t6_1225checked : Checked tree [5,5,3,3,3,10] := by
  refine ⟨plan6652,valid6652,t6_1225choices,?_⟩
  exact check_of_frontier tree 0 t6_1225root t6_1225jobs t6_1225frontier t6_1225all
theorem t6_1226choices : plan7053.choices=[5,5,3,3,6,6].map (options 6 4) := by rfl


theorem t6_1226part0 : t6_1226jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1226frontier : t6_1226root.frontier 0=t6_1226jobs := by rfl
theorem t6_1226all : t6_1226jobs.all (Job.check tree)=true := by
  simp only [t6_1226jobs,List.all_append,List.all_nil,t6_1226part0,Bool.and_self]
theorem t6_1226checked : Checked tree [5,5,3,3,6,6] := by
  refine ⟨plan7053,valid7053,t6_1226choices,?_⟩
  exact check_of_frontier tree 0 t6_1226root t6_1226jobs t6_1226frontier t6_1226all
theorem t6_1227choices : plan7054.choices=[5,5,3,3,6,7].map (options 6 4) := by rfl


theorem t6_1227part0 : t6_1227jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1227part1 : t6_1227jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1227part2 : t6_1227jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1227frontier : t6_1227root.frontier 1=t6_1227jobs := by rfl
theorem t6_1227all : t6_1227jobs.all (Job.check tree)=true := by
  simp only [t6_1227jobs,List.all_append,List.all_nil,t6_1227part0,t6_1227part1,t6_1227part2,Bool.and_self]
theorem t6_1227checked : Checked tree [5,5,3,3,6,7] := by
  refine ⟨plan7054,valid7054,t6_1227choices,?_⟩
  exact check_of_frontier tree 1 t6_1227root t6_1227jobs t6_1227frontier t6_1227all
theorem t6_1228choices : plan7055.choices=[5,5,3,3,6,10].map (options 6 4) := by rfl


theorem t6_1228part0 : t6_1228jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1228frontier : t6_1228root.frontier 0=t6_1228jobs := by rfl
theorem t6_1228all : t6_1228jobs.all (Job.check tree)=true := by
  simp only [t6_1228jobs,List.all_append,List.all_nil,t6_1228part0,Bool.and_self]
theorem t6_1228checked : Checked tree [5,5,3,3,6,10] := by
  refine ⟨plan7055,valid7055,t6_1228choices,?_⟩
  exact check_of_frontier tree 0 t6_1228root t6_1228jobs t6_1228frontier t6_1228all
theorem t6_1229choices : plan7056.choices=[5,5,3,3,7,7].map (options 6 4) := by rfl


theorem t6_1229part0 : t6_1229jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1229part1 : t6_1229jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1229part2 : t6_1229jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1229part3 : t6_1229jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1229frontier : t6_1229root.frontier 1=t6_1229jobs := by rfl
theorem t6_1229all : t6_1229jobs.all (Job.check tree)=true := by
  simp only [t6_1229jobs,List.all_append,List.all_nil,t6_1229part0,t6_1229part1,t6_1229part2,t6_1229part3,Bool.and_self]
theorem t6_1229checked : Checked tree [5,5,3,3,7,7] := by
  refine ⟨plan7056,valid7056,t6_1229choices,?_⟩
  exact check_of_frontier tree 1 t6_1229root t6_1229jobs t6_1229frontier t6_1229all
theorem t6_1230choices : plan7057.choices=[5,5,3,3,10,7].map (options 6 4) := by rfl


theorem t6_1230part0 : t6_1230jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1230part1 : t6_1230jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1230part2 : t6_1230jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1230frontier : t6_1230root.frontier 1=t6_1230jobs := by rfl
theorem t6_1230all : t6_1230jobs.all (Job.check tree)=true := by
  simp only [t6_1230jobs,List.all_append,List.all_nil,t6_1230part0,t6_1230part1,t6_1230part2,Bool.and_self]
theorem t6_1230checked : Checked tree [5,5,3,3,10,7] := by
  refine ⟨plan7057,valid7057,t6_1230choices,?_⟩
  exact check_of_frontier tree 1 t6_1230root t6_1230jobs t6_1230frontier t6_1230all
theorem t6_1231choices : plan7058.choices=[5,5,3,3,10,10].map (options 6 4) := by rfl


theorem t6_1231part0 : t6_1231jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1231frontier : t6_1231root.frontier 0=t6_1231jobs := by rfl
theorem t6_1231all : t6_1231jobs.all (Job.check tree)=true := by
  simp only [t6_1231jobs,List.all_append,List.all_nil,t6_1231part0,Bool.and_self]
theorem t6_1231checked : Checked tree [5,5,3,3,10,10] := by
  refine ⟨plan7058,valid7058,t6_1231choices,?_⟩
  exact check_of_frontier tree 0 t6_1231root t6_1231jobs t6_1231frontier t6_1231all
theorem t6_1232choices : plan7545.choices=[5,5,3,6,6,6].map (options 6 5) := by rfl


theorem t6_1232part0 : t6_1232jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1232frontier : t6_1232root.frontier 0=t6_1232jobs := by rfl
theorem t6_1232all : t6_1232jobs.all (Job.check tree)=true := by
  simp only [t6_1232jobs,List.all_append,List.all_nil,t6_1232part0,Bool.and_self]
theorem t6_1232checked : Checked tree [5,5,3,6,6,6] := by
  refine ⟨plan7545,valid7545,t6_1232choices,?_⟩
  exact check_of_frontier tree 0 t6_1232root t6_1232jobs t6_1232frontier t6_1232all
theorem t6_1233choices : plan7546.choices=[5,5,3,6,6,7].map (options 6 5) := by rfl


theorem t6_1233part0 : t6_1233jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1233part1 : t6_1233jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1233frontier : t6_1233root.frontier 1=t6_1233jobs := by rfl
theorem t6_1233all : t6_1233jobs.all (Job.check tree)=true := by
  simp only [t6_1233jobs,List.all_append,List.all_nil,t6_1233part0,t6_1233part1,Bool.and_self]
theorem t6_1233checked : Checked tree [5,5,3,6,6,7] := by
  refine ⟨plan7546,valid7546,t6_1233choices,?_⟩
  exact check_of_frontier tree 1 t6_1233root t6_1233jobs t6_1233frontier t6_1233all
theorem t6_1234choices : plan7547.choices=[5,5,3,6,6,10].map (options 6 5) := by rfl


theorem t6_1234part0 : t6_1234jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1234frontier : t6_1234root.frontier 0=t6_1234jobs := by rfl
theorem t6_1234all : t6_1234jobs.all (Job.check tree)=true := by
  simp only [t6_1234jobs,List.all_append,List.all_nil,t6_1234part0,Bool.and_self]
theorem t6_1234checked : Checked tree [5,5,3,6,6,10] := by
  refine ⟨plan7547,valid7547,t6_1234choices,?_⟩
  exact check_of_frontier tree 0 t6_1234root t6_1234jobs t6_1234frontier t6_1234all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks132 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1229checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1230checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1231checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1232checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1233checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1220checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1234checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1221checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1222checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1223checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1224checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1225checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1226checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1227checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1228checked⟩
