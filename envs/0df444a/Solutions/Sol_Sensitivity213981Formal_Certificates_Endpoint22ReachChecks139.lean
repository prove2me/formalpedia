-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks139
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:52:34.248992+00:00
-- url     : https://prove2.me/submissions/af67db66-81cc-4eaa-a1e1-20e63116651c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks139
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks139
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
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































































theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)





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

theorem valid578 : plan578.Valid := valid_step _ _ _ valid134 (by decide +kernel)

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

























































































































































theorem valid557 : plan557.Valid := valid_step _ _ _ valid128 (by decide +kernel)























theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)



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



















































































































































































theorem valid1530 : plan1530.Valid := valid_step _ _ _ valid557 (by decide +kernel)












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















































theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)



theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)



















theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)

theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)









theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1582 : plan1582.Valid := valid_step _ _ _ valid573 (by decide +kernel)

















theorem valid1591 : plan1591.Valid := valid_step _ _ _ valid578 (by decide +kernel)



theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)





theorem valid1602 : plan1602.Valid := valid_step _ _ _ valid578 (by decide +kernel)



theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

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























































































































theorem valid3324 : plan3324.Valid := valid_step _ _ _ valid1530 (by decide +kernel)








































































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













































































































































































theorem valid5463 : plan5463.Valid := valid_step _ _ _ valid3324 (by decide +kernel)


















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







theorem valid3364 : plan3364.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3365 : plan3365.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3366 : plan3366.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3367 : plan3367.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3368 : plan3368.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3369 : plan3369.Valid := valid_step _ _ _ valid1582 (by decide +kernel)











theorem valid3375 : plan3375.Valid := valid_step _ _ _ valid1560 (by decide +kernel)



theorem valid3377 : plan3377.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3378 : plan3378.Valid := valid_step _ _ _ valid1563 (by decide +kernel)




























































































































































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



























































































































































































theorem valid5566 : plan5566.Valid := valid_step _ _ _ valid3364 (by decide +kernel)

theorem valid5567 : plan5567.Valid := valid_step _ _ _ valid3365 (by decide +kernel)

theorem valid5568 : plan5568.Valid := valid_step _ _ _ valid3366 (by decide +kernel)
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

theorem valid5569 : plan5569.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5570 : plan5570.Valid := valid_step _ _ _ valid3368 (by decide +kernel)

theorem valid5571 : plan5571.Valid := valid_step _ _ _ valid3369 (by decide +kernel)

theorem valid5572 : plan5572.Valid := valid_step _ _ _ valid3375 (by decide +kernel)

theorem valid5573 : plan5573.Valid := valid_step _ _ _ valid3377 (by decide +kernel)

theorem valid5574 : plan5574.Valid := valid_step _ _ _ valid3378 (by decide +kernel)




















































































































































































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

























































































theorem valid6669 : plan6669.Valid := valid_step _ _ _ valid5463 (by decide +kernel)






































































































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





theorem valid3459 : plan3459.Valid := valid_step _ _ _ valid1591 (by decide +kernel)





theorem valid3462 : plan3462.Valid := valid_step _ _ _ valid1594 (by decide +kernel)



theorem valid3464 : plan3464.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3465 : plan3465.Valid := valid_step _ _ _ valid1597 (by decide +kernel)



theorem valid3467 : plan3467.Valid := valid_step _ _ _ valid1599 (by decide +kernel)





theorem valid3470 : plan3470.Valid := valid_step _ _ _ valid1602 (by decide +kernel)



theorem valid3472 : plan3472.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3473 : plan3473.Valid := valid_step _ _ _ valid1605 (by decide +kernel)



theorem valid3475 : plan3475.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3477 : plan3477.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)








































































































































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























































































































































theorem valid5740 : plan5740.Valid := valid_step _ _ _ valid3459 (by decide +kernel)

theorem valid5741 : plan5741.Valid := valid_step _ _ _ valid3462 (by decide +kernel)

theorem valid5742 : plan5742.Valid := valid_step _ _ _ valid3464 (by decide +kernel)

theorem valid5743 : plan5743.Valid := valid_step _ _ _ valid3465 (by decide +kernel)

theorem valid5744 : plan5744.Valid := valid_step _ _ _ valid3467 (by decide +kernel)

theorem valid5745 : plan5745.Valid := valid_step _ _ _ valid3470 (by decide +kernel)

theorem valid5746 : plan5746.Valid := valid_step _ _ _ valid3472 (by decide +kernel)

theorem valid5747 : plan5747.Valid := valid_step _ _ _ valid3473 (by decide +kernel)

theorem valid5748 : plan5748.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5749 : plan5749.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5750 : plan5750.Valid := valid_step _ _ _ valid3477 (by decide +kernel)

theorem valid5751 : plan5751.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5752 : plan5752.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5753 : plan5753.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5754 : plan5754.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5755 : plan5755.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5756 : plan5756.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5757 : plan5757.Valid := valid_step _ _ _ valid3484 (by decide +kernel)






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



























































































































































theorem valid7086 : plan7086.Valid := valid_step _ _ _ valid5566 (by decide +kernel)

theorem valid7087 : plan7087.Valid := valid_step _ _ _ valid5567 (by decide +kernel)

theorem valid7088 : plan7088.Valid := valid_step _ _ _ valid5568 (by decide +kernel)

theorem valid7089 : plan7089.Valid := valid_step _ _ _ valid5569 (by decide +kernel)

theorem valid7090 : plan7090.Valid := valid_step _ _ _ valid5570 (by decide +kernel)

theorem valid7091 : plan7091.Valid := valid_step _ _ _ valid5571 (by decide +kernel)

theorem valid7092 : plan7092.Valid := valid_step _ _ _ valid5572 (by decide +kernel)

theorem valid7093 : plan7093.Valid := valid_step _ _ _ valid5573 (by decide +kernel)

theorem valid7094 : plan7094.Valid := valid_step _ _ _ valid5574 (by decide +kernel)




















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





theorem valid7587 : plan7587.Valid := valid_step _ _ _ valid5740 (by decide +kernel)

theorem valid7588 : plan7588.Valid := valid_step _ _ _ valid5741 (by decide +kernel)

theorem valid7589 : plan7589.Valid := valid_step _ _ _ valid5742 (by decide +kernel)

theorem valid7590 : plan7590.Valid := valid_step _ _ _ valid5743 (by decide +kernel)

theorem valid7591 : plan7591.Valid := valid_step _ _ _ valid5744 (by decide +kernel)

theorem valid7592 : plan7592.Valid := valid_step _ _ _ valid5745 (by decide +kernel)

theorem valid7593 : plan7593.Valid := valid_step _ _ _ valid5746 (by decide +kernel)

theorem valid7594 : plan7594.Valid := valid_step _ _ _ valid5747 (by decide +kernel)

theorem valid7595 : plan7595.Valid := valid_step _ _ _ valid5748 (by decide +kernel)

theorem valid7596 : plan7596.Valid := valid_step _ _ _ valid5749 (by decide +kernel)

theorem valid7597 : plan7597.Valid := valid_step _ _ _ valid5750 (by decide +kernel)

theorem valid7598 : plan7598.Valid := valid_step _ _ _ valid5751 (by decide +kernel)

theorem valid7599 : plan7599.Valid := valid_step _ _ _ valid5752 (by decide +kernel)

theorem valid7600 : plan7600.Valid := valid_step _ _ _ valid5753 (by decide +kernel)

theorem valid7601 : plan7601.Valid := valid_step _ _ _ valid5754 (by decide +kernel)

theorem valid7602 : plan7602.Valid := valid_step _ _ _ valid5755 (by decide +kernel)

theorem valid7603 : plan7603.Valid := valid_step _ _ _ valid5756 (by decide +kernel)

theorem valid7604 : plan7604.Valid := valid_step _ _ _ valid5757 (by decide +kernel)
























































































































































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
theorem t6_1438choices : plan7086.choices=[8,2,3,6,10,7].map (options 6 4) := by rfl


theorem t6_1438part0 : t6_1438jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1438part1 : t6_1438jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1438frontier : t6_1438root.frontier 1=t6_1438jobs := by rfl
theorem t6_1438all : t6_1438jobs.all (Job.check tree)=true := by
  simp only [t6_1438jobs,List.all_append,List.all_nil,t6_1438part0,t6_1438part1,Bool.and_self]
theorem t6_1438checked : Checked tree [8,2,3,6,10,7] := by
  refine ⟨plan7086,valid7086,t6_1438choices,?_⟩
  exact check_of_frontier tree 1 t6_1438root t6_1438jobs t6_1438frontier t6_1438all
theorem t6_1439choices : plan7087.choices=[8,2,3,6,10,10].map (options 6 4) := by rfl


theorem t6_1439part0 : t6_1439jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1439frontier : t6_1439root.frontier 0=t6_1439jobs := by rfl
theorem t6_1439all : t6_1439jobs.all (Job.check tree)=true := by
  simp only [t6_1439jobs,List.all_append,List.all_nil,t6_1439part0,Bool.and_self]
theorem t6_1439checked : Checked tree [8,2,3,6,10,10] := by
  refine ⟨plan7087,valid7087,t6_1439choices,?_⟩
  exact check_of_frontier tree 0 t6_1439root t6_1439jobs t6_1439frontier t6_1439all
theorem t6_1440choices : plan7088.choices=[8,2,3,7,7,7].map (options 6 4) := by rfl


theorem t6_1440part0 : t6_1440jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1440part1 : t6_1440jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1440frontier : t6_1440root.frontier 1=t6_1440jobs := by rfl
theorem t6_1440all : t6_1440jobs.all (Job.check tree)=true := by
  simp only [t6_1440jobs,List.all_append,List.all_nil,t6_1440part0,t6_1440part1,Bool.and_self]
theorem t6_1440checked : Checked tree [8,2,3,7,7,7] := by
  refine ⟨plan7088,valid7088,t6_1440choices,?_⟩
  exact check_of_frontier tree 1 t6_1440root t6_1440jobs t6_1440frontier t6_1440all
theorem t6_1441choices : plan7089.choices=[8,2,3,10,7,7].map (options 6 4) := by rfl


theorem t6_1441part0 : t6_1441jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1441part1 : t6_1441jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1441part2 : t6_1441jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1441frontier : t6_1441root.frontier 2=t6_1441jobs := by rfl
theorem t6_1441all : t6_1441jobs.all (Job.check tree)=true := by
  simp only [t6_1441jobs,List.all_append,List.all_nil,t6_1441part0,t6_1441part1,t6_1441part2,Bool.and_self]
theorem t6_1441checked : Checked tree [8,2,3,10,7,7] := by
  refine ⟨plan7089,valid7089,t6_1441choices,?_⟩
  exact check_of_frontier tree 2 t6_1441root t6_1441jobs t6_1441frontier t6_1441all
theorem t6_1442choices : plan7090.choices=[8,2,3,10,10,7].map (options 6 4) := by rfl


theorem t6_1442part0 : t6_1442jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1442part1 : t6_1442jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1442frontier : t6_1442root.frontier 1=t6_1442jobs := by rfl
theorem t6_1442all : t6_1442jobs.all (Job.check tree)=true := by
  simp only [t6_1442jobs,List.all_append,List.all_nil,t6_1442part0,t6_1442part1,Bool.and_self]
theorem t6_1442checked : Checked tree [8,2,3,10,10,7] := by
  refine ⟨plan7090,valid7090,t6_1442choices,?_⟩
  exact check_of_frontier tree 1 t6_1442root t6_1442jobs t6_1442frontier t6_1442all
theorem t6_1443choices : plan7091.choices=[8,2,3,10,10,10].map (options 6 4) := by rfl


theorem t6_1443part0 : t6_1443jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1443frontier : t6_1443root.frontier 0=t6_1443jobs := by rfl
theorem t6_1443all : t6_1443jobs.all (Job.check tree)=true := by
  simp only [t6_1443jobs,List.all_append,List.all_nil,t6_1443part0,Bool.and_self]
theorem t6_1443checked : Checked tree [8,2,3,10,10,10] := by
  refine ⟨plan7091,valid7091,t6_1443choices,?_⟩
  exact check_of_frontier tree 0 t6_1443root t6_1443jobs t6_1443frontier t6_1443all
theorem t6_1444choices : plan6669.choices=[8,2,5,3,3,7].map (options 6 3) := by rfl


theorem t6_1444part0 : t6_1444jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1444frontier : t6_1444root.frontier 0=t6_1444jobs := by rfl
theorem t6_1444all : t6_1444jobs.all (Job.check tree)=true := by
  simp only [t6_1444jobs,List.all_append,List.all_nil,t6_1444part0,Bool.and_self]
theorem t6_1444checked : Checked tree [8,2,5,3,3,7] := by
  refine ⟨plan6669,valid6669,t6_1444choices,?_⟩
  exact check_of_frontier tree 0 t6_1444root t6_1444jobs t6_1444frontier t6_1444all
theorem t6_1445choices : plan7092.choices=[8,2,5,3,6,7].map (options 6 4) := by rfl


theorem t6_1445part0 : t6_1445jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1445frontier : t6_1445root.frontier 0=t6_1445jobs := by rfl
theorem t6_1445all : t6_1445jobs.all (Job.check tree)=true := by
  simp only [t6_1445jobs,List.all_append,List.all_nil,t6_1445part0,Bool.and_self]
theorem t6_1445checked : Checked tree [8,2,5,3,6,7] := by
  refine ⟨plan7092,valid7092,t6_1445choices,?_⟩
  exact check_of_frontier tree 0 t6_1445root t6_1445jobs t6_1445frontier t6_1445all
theorem t6_1446choices : plan7093.choices=[8,2,5,3,7,7].map (options 6 4) := by rfl


theorem t6_1446part0 : t6_1446jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1446part1 : t6_1446jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1446frontier : t6_1446root.frontier 1=t6_1446jobs := by rfl
theorem t6_1446all : t6_1446jobs.all (Job.check tree)=true := by
  simp only [t6_1446jobs,List.all_append,List.all_nil,t6_1446part0,t6_1446part1,Bool.and_self]
theorem t6_1446checked : Checked tree [8,2,5,3,7,7] := by
  refine ⟨plan7093,valid7093,t6_1446choices,?_⟩
  exact check_of_frontier tree 1 t6_1446root t6_1446jobs t6_1446frontier t6_1446all
theorem t6_1447choices : plan7094.choices=[8,2,5,3,10,7].map (options 6 4) := by rfl


theorem t6_1447part0 : t6_1447jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1447frontier : t6_1447root.frontier 0=t6_1447jobs := by rfl
theorem t6_1447all : t6_1447jobs.all (Job.check tree)=true := by
  simp only [t6_1447jobs,List.all_append,List.all_nil,t6_1447part0,Bool.and_self]
theorem t6_1447checked : Checked tree [8,2,5,3,10,7] := by
  refine ⟨plan7094,valid7094,t6_1447choices,?_⟩
  exact check_of_frontier tree 0 t6_1447root t6_1447jobs t6_1447frontier t6_1447all
theorem t6_1448choices : plan7587.choices=[8,2,5,5,7,7].map (options 6 5) := by rfl


theorem t6_1448part0 : t6_1448jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1448frontier : t6_1448root.frontier 0=t6_1448jobs := by rfl
theorem t6_1448all : t6_1448jobs.all (Job.check tree)=true := by
  simp only [t6_1448jobs,List.all_append,List.all_nil,t6_1448part0,Bool.and_self]
theorem t6_1448checked : Checked tree [8,2,5,5,7,7] := by
  refine ⟨plan7587,valid7587,t6_1448choices,?_⟩
  exact check_of_frontier tree 0 t6_1448root t6_1448jobs t6_1448frontier t6_1448all
theorem t6_1449choices : plan7588.choices=[8,2,5,6,6,7].map (options 6 5) := by rfl


theorem t6_1449part0 : t6_1449jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1449frontier : t6_1449root.frontier 0=t6_1449jobs := by rfl
theorem t6_1449all : t6_1449jobs.all (Job.check tree)=true := by
  simp only [t6_1449jobs,List.all_append,List.all_nil,t6_1449part0,Bool.and_self]
theorem t6_1449checked : Checked tree [8,2,5,6,6,7] := by
  refine ⟨plan7588,valid7588,t6_1449choices,?_⟩
  exact check_of_frontier tree 0 t6_1449root t6_1449jobs t6_1449frontier t6_1449all
theorem t6_1450choices : plan7589.choices=[8,2,5,6,7,7].map (options 6 5) := by rfl


theorem t6_1450part0 : t6_1450jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1450frontier : t6_1450root.frontier 0=t6_1450jobs := by rfl
theorem t6_1450all : t6_1450jobs.all (Job.check tree)=true := by
  simp only [t6_1450jobs,List.all_append,List.all_nil,t6_1450part0,Bool.and_self]
theorem t6_1450checked : Checked tree [8,2,5,6,7,7] := by
  refine ⟨plan7589,valid7589,t6_1450choices,?_⟩
  exact check_of_frontier tree 0 t6_1450root t6_1450jobs t6_1450frontier t6_1450all
theorem t6_1451choices : plan7590.choices=[8,2,5,6,10,7].map (options 6 5) := by rfl


theorem t6_1451part0 : t6_1451jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1451frontier : t6_1451root.frontier 0=t6_1451jobs := by rfl
theorem t6_1451all : t6_1451jobs.all (Job.check tree)=true := by
  simp only [t6_1451jobs,List.all_append,List.all_nil,t6_1451part0,Bool.and_self]
theorem t6_1451checked : Checked tree [8,2,5,6,10,7] := by
  refine ⟨plan7590,valid7590,t6_1451choices,?_⟩
  exact check_of_frontier tree 0 t6_1451root t6_1451jobs t6_1451frontier t6_1451all
theorem t6_1452choices : plan7591.choices=[8,2,5,7,7,7].map (options 6 5) := by rfl


theorem t6_1452part0 : t6_1452jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1452frontier : t6_1452root.frontier 0=t6_1452jobs := by rfl
theorem t6_1452all : t6_1452jobs.all (Job.check tree)=true := by
  simp only [t6_1452jobs,List.all_append,List.all_nil,t6_1452part0,Bool.and_self]
theorem t6_1452checked : Checked tree [8,2,5,7,7,7] := by
  refine ⟨plan7591,valid7591,t6_1452choices,?_⟩
  exact check_of_frontier tree 0 t6_1452root t6_1452jobs t6_1452frontier t6_1452all
theorem t6_1453choices : plan7592.choices=[8,2,5,9,7,7].map (options 6 5) := by rfl


theorem t6_1453part0 : t6_1453jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1453frontier : t6_1453root.frontier 0=t6_1453jobs := by rfl
theorem t6_1453all : t6_1453jobs.all (Job.check tree)=true := by
  simp only [t6_1453jobs,List.all_append,List.all_nil,t6_1453part0,Bool.and_self]
theorem t6_1453checked : Checked tree [8,2,5,9,7,7] := by
  refine ⟨plan7592,valid7592,t6_1453choices,?_⟩
  exact check_of_frontier tree 0 t6_1453root t6_1453jobs t6_1453frontier t6_1453all
theorem t6_1454choices : plan7593.choices=[8,2,5,10,7,7].map (options 6 5) := by rfl


theorem t6_1454part0 : t6_1454jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1454frontier : t6_1454root.frontier 0=t6_1454jobs := by rfl
theorem t6_1454all : t6_1454jobs.all (Job.check tree)=true := by
  simp only [t6_1454jobs,List.all_append,List.all_nil,t6_1454part0,Bool.and_self]
theorem t6_1454checked : Checked tree [8,2,5,10,7,7] := by
  refine ⟨plan7593,valid7593,t6_1454choices,?_⟩
  exact check_of_frontier tree 0 t6_1454root t6_1454jobs t6_1454frontier t6_1454all
theorem t6_1455choices : plan7594.choices=[8,2,5,10,10,7].map (options 6 5) := by rfl


theorem t6_1455part0 : t6_1455jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1455frontier : t6_1455root.frontier 0=t6_1455jobs := by rfl
theorem t6_1455all : t6_1455jobs.all (Job.check tree)=true := by
  simp only [t6_1455jobs,List.all_append,List.all_nil,t6_1455part0,Bool.and_self]
theorem t6_1455checked : Checked tree [8,2,5,10,10,7] := by
  refine ⟨plan7594,valid7594,t6_1455choices,?_⟩
  exact check_of_frontier tree 0 t6_1455root t6_1455jobs t6_1455frontier t6_1455all
theorem t6_1456choices : plan7595.choices=[8,2,6,6,6,6].map (options 6 5) := by rfl


theorem t6_1456part0 : t6_1456jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1456frontier : t6_1456root.frontier 0=t6_1456jobs := by rfl
theorem t6_1456all : t6_1456jobs.all (Job.check tree)=true := by
  simp only [t6_1456jobs,List.all_append,List.all_nil,t6_1456part0,Bool.and_self]
theorem t6_1456checked : Checked tree [8,2,6,6,6,6] := by
  refine ⟨plan7595,valid7595,t6_1456choices,?_⟩
  exact check_of_frontier tree 0 t6_1456root t6_1456jobs t6_1456frontier t6_1456all
theorem t6_1457choices : plan7596.choices=[8,2,6,6,6,7].map (options 6 5) := by rfl


theorem t6_1457part0 : t6_1457jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1457frontier : t6_1457root.frontier 0=t6_1457jobs := by rfl
theorem t6_1457all : t6_1457jobs.all (Job.check tree)=true := by
  simp only [t6_1457jobs,List.all_append,List.all_nil,t6_1457part0,Bool.and_self]
theorem t6_1457checked : Checked tree [8,2,6,6,6,7] := by
  refine ⟨plan7596,valid7596,t6_1457choices,?_⟩
  exact check_of_frontier tree 0 t6_1457root t6_1457jobs t6_1457frontier t6_1457all
theorem t6_1458choices : plan7597.choices=[8,2,6,6,6,10].map (options 6 5) := by rfl


theorem t6_1458part0 : t6_1458jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1458frontier : t6_1458root.frontier 0=t6_1458jobs := by rfl
theorem t6_1458all : t6_1458jobs.all (Job.check tree)=true := by
  simp only [t6_1458jobs,List.all_append,List.all_nil,t6_1458part0,Bool.and_self]
theorem t6_1458checked : Checked tree [8,2,6,6,6,10] := by
  refine ⟨plan7597,valid7597,t6_1458choices,?_⟩
  exact check_of_frontier tree 0 t6_1458root t6_1458jobs t6_1458frontier t6_1458all
theorem t6_1459choices : plan7598.choices=[8,2,6,6,7,7].map (options 6 5) := by rfl


theorem t6_1459part0 : t6_1459jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1459frontier : t6_1459root.frontier 0=t6_1459jobs := by rfl
theorem t6_1459all : t6_1459jobs.all (Job.check tree)=true := by
  simp only [t6_1459jobs,List.all_append,List.all_nil,t6_1459part0,Bool.and_self]
theorem t6_1459checked : Checked tree [8,2,6,6,7,7] := by
  refine ⟨plan7598,valid7598,t6_1459choices,?_⟩
  exact check_of_frontier tree 0 t6_1459root t6_1459jobs t6_1459frontier t6_1459all
theorem t6_1460choices : plan7599.choices=[8,2,6,6,10,7].map (options 6 5) := by rfl


theorem t6_1460part0 : t6_1460jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1460frontier : t6_1460root.frontier 0=t6_1460jobs := by rfl
theorem t6_1460all : t6_1460jobs.all (Job.check tree)=true := by
  simp only [t6_1460jobs,List.all_append,List.all_nil,t6_1460part0,Bool.and_self]
theorem t6_1460checked : Checked tree [8,2,6,6,10,7] := by
  refine ⟨plan7599,valid7599,t6_1460choices,?_⟩
  exact check_of_frontier tree 0 t6_1460root t6_1460jobs t6_1460frontier t6_1460all
theorem t6_1461choices : plan7600.choices=[8,2,6,6,10,10].map (options 6 5) := by rfl


theorem t6_1461part0 : t6_1461jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1461frontier : t6_1461root.frontier 0=t6_1461jobs := by rfl
theorem t6_1461all : t6_1461jobs.all (Job.check tree)=true := by
  simp only [t6_1461jobs,List.all_append,List.all_nil,t6_1461part0,Bool.and_self]
theorem t6_1461checked : Checked tree [8,2,6,6,10,10] := by
  refine ⟨plan7600,valid7600,t6_1461choices,?_⟩
  exact check_of_frontier tree 0 t6_1461root t6_1461jobs t6_1461frontier t6_1461all
theorem t6_1462choices : plan7601.choices=[8,2,6,7,7,7].map (options 6 5) := by rfl


theorem t6_1462part0 : t6_1462jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1462frontier : t6_1462root.frontier 0=t6_1462jobs := by rfl
theorem t6_1462all : t6_1462jobs.all (Job.check tree)=true := by
  simp only [t6_1462jobs,List.all_append,List.all_nil,t6_1462part0,Bool.and_self]
theorem t6_1462checked : Checked tree [8,2,6,7,7,7] := by
  refine ⟨plan7601,valid7601,t6_1462choices,?_⟩
  exact check_of_frontier tree 0 t6_1462root t6_1462jobs t6_1462frontier t6_1462all
theorem t6_1463choices : plan7602.choices=[8,2,6,10,7,7].map (options 6 5) := by rfl


theorem t6_1463part0 : t6_1463jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1463part1 : t6_1463jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1463frontier : t6_1463root.frontier 1=t6_1463jobs := by rfl
theorem t6_1463all : t6_1463jobs.all (Job.check tree)=true := by
  simp only [t6_1463jobs,List.all_append,List.all_nil,t6_1463part0,t6_1463part1,Bool.and_self]
theorem t6_1463checked : Checked tree [8,2,6,10,7,7] := by
  refine ⟨plan7602,valid7602,t6_1463choices,?_⟩
  exact check_of_frontier tree 1 t6_1463root t6_1463jobs t6_1463frontier t6_1463all
theorem t6_1464choices : plan7603.choices=[8,2,6,10,10,7].map (options 6 5) := by rfl


theorem t6_1464part0 : t6_1464jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1464frontier : t6_1464root.frontier 0=t6_1464jobs := by rfl
theorem t6_1464all : t6_1464jobs.all (Job.check tree)=true := by
  simp only [t6_1464jobs,List.all_append,List.all_nil,t6_1464part0,Bool.and_self]
theorem t6_1464checked : Checked tree [8,2,6,10,10,7] := by
  refine ⟨plan7603,valid7603,t6_1464choices,?_⟩
  exact check_of_frontier tree 0 t6_1464root t6_1464jobs t6_1464frontier t6_1464all
theorem t6_1465choices : plan7604.choices=[8,2,6,10,10,10].map (options 6 5) := by rfl


theorem t6_1465part0 : t6_1465jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1465frontier : t6_1465root.frontier 0=t6_1465jobs := by rfl
theorem t6_1465all : t6_1465jobs.all (Job.check tree)=true := by
  simp only [t6_1465jobs,List.all_append,List.all_nil,t6_1465part0,Bool.and_self]
theorem t6_1465checked : Checked tree [8,2,6,10,10,10] := by
  refine ⟨plan7604,valid7604,t6_1465choices,?_⟩
  exact check_of_frontier tree 0 t6_1465root t6_1465jobs t6_1465frontier t6_1465all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks139 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1447checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1448checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1449checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1450checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1438checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1451checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1452checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1453checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1454checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1455checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1456checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1457checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1458checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1459checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1460checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1439checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1461checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1462checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1463checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1464checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1465checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1440checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1441checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1442checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1443checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1444checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1445checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1446checked⟩
