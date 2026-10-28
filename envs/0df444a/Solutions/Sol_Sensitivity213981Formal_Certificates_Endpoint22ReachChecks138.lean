-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks138
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:51:30.726233+00:00
-- url     : https://prove2.me/submissions/a9447453-a621-47fb-9be1-7357264eb9a9

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks138
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks138
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans082
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











































theorem valid118 : plan118.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid123 : plan123.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid125 : plan125.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid137 : plan137.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid138 : plan138.Valid := valid_step _ _ _ valid0 (by decide +kernel)












































































































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















theorem valid584 : plan584.Valid := valid_step _ _ _ valid137 (by decide +kernel)

theorem valid585 : plan585.Valid := valid_step _ _ _ valid137 (by decide +kernel)

theorem valid586 : plan586.Valid := valid_step _ _ _ valid138 (by decide +kernel)












































































































































































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

























































































































theorem valid541 : plan541.Valid := valid_step _ _ _ valid118 (by decide +kernel)









theorem valid546 : plan546.Valid := valid_step _ _ _ valid123 (by decide +kernel)

theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid548 : plan548.Valid := valid_step _ _ _ valid125 (by decide +kernel)





















theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)

theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)

theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)








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







































































































































theorem valid1508 : plan1508.Valid := valid_step _ _ _ valid541 (by decide +kernel)















theorem valid1516 : plan1516.Valid := valid_step _ _ _ valid546 (by decide +kernel)

theorem valid1517 : plan1517.Valid := valid_step _ _ _ valid547 (by decide +kernel)

theorem valid1518 : plan1518.Valid := valid_step _ _ _ valid548 (by decide +kernel)

















theorem valid1527 : plan1527.Valid := valid_step _ _ _ valid562 (by decide +kernel)









theorem valid1532 : plan1532.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1533 : plan1533.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1534 : plan1534.Valid := valid_step _ _ _ valid561 (by decide +kernel)

theorem valid1535 : plan1535.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1536 : plan1536.Valid := valid_step _ _ _ valid563 (by decide +kernel)
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



























































































































































theorem valid3246 : plan3246.Valid := valid_step _ _ _ valid1508 (by decide +kernel)

















theorem valid3255 : plan3255.Valid := valid_step _ _ _ valid1517 (by decide +kernel)


















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

theorem valid1537 : plan1537.Valid := valid_step _ _ _ valid564 (by decide +kernel)



























































theorem valid1567 : plan1567.Valid := valid_step _ _ _ valid571 (by decide +kernel)



theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)



theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)





theorem valid1578 : plan1578.Valid := valid_step _ _ _ valid571 (by decide +kernel)



theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)





































































theorem valid1616 : plan1616.Valid := valid_step _ _ _ valid584 (by decide +kernel)







theorem valid1620 : plan1620.Valid := valid_step _ _ _ valid584 (by decide +kernel)

theorem valid1621 : plan1621.Valid := valid_step _ _ _ valid585 (by decide +kernel)

theorem valid1622 : plan1622.Valid := valid_step _ _ _ valid586 (by decide +kernel)




















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

theorem valid3265 : plan3265.Valid := valid_step _ _ _ valid1516 (by decide +kernel)

theorem valid3266 : plan3266.Valid := valid_step _ _ _ valid1517 (by decide +kernel)

theorem valid3267 : plan3267.Valid := valid_step _ _ _ valid1518 (by decide +kernel)































theorem valid3283 : plan3283.Valid := valid_step _ _ _ valid1527 (by decide +kernel)

theorem valid3284 : plan3284.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3285 : plan3285.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3286 : plan3286.Valid := valid_step _ _ _ valid1536 (by decide +kernel)







































theorem valid3306 : plan3306.Valid := valid_step _ _ _ valid1532 (by decide +kernel)

theorem valid3307 : plan3307.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3308 : plan3308.Valid := valid_step _ _ _ valid1534 (by decide +kernel)

theorem valid3309 : plan3309.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3310 : plan3310.Valid := valid_step _ _ _ valid1536 (by decide +kernel)

theorem valid3311 : plan3311.Valid := valid_step _ _ _ valid1537 (by decide +kernel)





































































theorem valid3346 : plan3346.Valid := valid_step _ _ _ valid1567 (by decide +kernel)

theorem valid3347 : plan3347.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3348 : plan3348.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3349 : plan3349.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3350 : plan3350.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3351 : plan3351.Valid := valid_step _ _ _ valid1578 (by decide +kernel)

theorem valid3352 : plan3352.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3353 : plan3353.Valid := valid_step _ _ _ valid1581 (by decide +kernel)













theorem valid3360 : plan3360.Valid := valid_step _ _ _ valid1569 (by decide +kernel)
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











































































































































theorem valid5350 : plan5350.Valid := valid_step _ _ _ valid3246 (by decide +kernel)





































theorem valid5369 : plan5369.Valid := valid_step _ _ _ valid3255 (by decide +kernel)














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

theorem valid3553 : plan3553.Valid := valid_step _ _ _ valid1616 (by decide +kernel)

theorem valid3554 : plan3554.Valid := valid_step _ _ _ valid1620 (by decide +kernel)

theorem valid3555 : plan3555.Valid := valid_step _ _ _ valid1621 (by decide +kernel)

theorem valid3556 : plan3556.Valid := valid_step _ _ _ valid1622 (by decide +kernel)
























































































































































































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



theorem valid5378 : plan5378.Valid := valid_step _ _ _ valid3265 (by decide +kernel)

theorem valid5379 : plan5379.Valid := valid_step _ _ _ valid3266 (by decide +kernel)

theorem valid5380 : plan5380.Valid := valid_step _ _ _ valid3267 (by decide +kernel)





























































































theorem valid5427 : plan5427.Valid := valid_step _ _ _ valid3283 (by decide +kernel)

theorem valid5428 : plan5428.Valid := valid_step _ _ _ valid3284 (by decide +kernel)

theorem valid5429 : plan5429.Valid := valid_step _ _ _ valid3285 (by decide +kernel)

theorem valid5430 : plan5430.Valid := valid_step _ _ _ valid3286 (by decide +kernel)

































theorem valid5447 : plan5447.Valid := valid_step _ _ _ valid3306 (by decide +kernel)

theorem valid5448 : plan5448.Valid := valid_step _ _ _ valid3307 (by decide +kernel)

theorem valid5449 : plan5449.Valid := valid_step _ _ _ valid3308 (by decide +kernel)

theorem valid5450 : plan5450.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5451 : plan5451.Valid := valid_step _ _ _ valid3310 (by decide +kernel)

theorem valid5452 : plan5452.Valid := valid_step _ _ _ valid3311 (by decide +kernel)








































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

























































































































































theorem valid6317 : plan6317.Valid := valid_step _ _ _ valid5350 (by decide +kernel)






































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

theorem valid3361 : plan3361.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3362 : plan3362.Valid := valid_step _ _ _ valid1571 (by decide +kernel)

theorem valid3363 : plan3363.Valid := valid_step _ _ _ valid1572 (by decide +kernel)


























































































































































































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



































































































































































theorem valid5554 : plan5554.Valid := valid_step _ _ _ valid3346 (by decide +kernel)

theorem valid5555 : plan5555.Valid := valid_step _ _ _ valid3347 (by decide +kernel)

theorem valid5556 : plan5556.Valid := valid_step _ _ _ valid3348 (by decide +kernel)

theorem valid5557 : plan5557.Valid := valid_step _ _ _ valid3349 (by decide +kernel)

theorem valid5558 : plan5558.Valid := valid_step _ _ _ valid3350 (by decide +kernel)

theorem valid5559 : plan5559.Valid := valid_step _ _ _ valid3351 (by decide +kernel)

theorem valid5560 : plan5560.Valid := valid_step _ _ _ valid3352 (by decide +kernel)

theorem valid5561 : plan5561.Valid := valid_step _ _ _ valid3353 (by decide +kernel)

theorem valid5562 : plan5562.Valid := valid_step _ _ _ valid3360 (by decide +kernel)

theorem valid5563 : plan5563.Valid := valid_step _ _ _ valid3361 (by decide +kernel)

theorem valid5564 : plan5564.Valid := valid_step _ _ _ valid3362 (by decide +kernel)

theorem valid5565 : plan5565.Valid := valid_step _ _ _ valid3363 (by decide +kernel)






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





































































theorem valid6659 : plan6659.Valid := valid_step _ _ _ valid5427 (by decide +kernel)

theorem valid6660 : plan6660.Valid := valid_step _ _ _ valid5428 (by decide +kernel)

theorem valid6661 : plan6661.Valid := valid_step _ _ _ valid5429 (by decide +kernel)

theorem valid6662 : plan6662.Valid := valid_step _ _ _ valid5430 (by decide +kernel)

theorem valid6663 : plan6663.Valid := valid_step _ _ _ valid5447 (by decide +kernel)

theorem valid6664 : plan6664.Valid := valid_step _ _ _ valid5448 (by decide +kernel)

theorem valid6665 : plan6665.Valid := valid_step _ _ _ valid5449 (by decide +kernel)

theorem valid6666 : plan6666.Valid := valid_step _ _ _ valid5450 (by decide +kernel)

theorem valid6667 : plan6667.Valid := valid_step _ _ _ valid5451 (by decide +kernel)

theorem valid6668 : plan6668.Valid := valid_step _ _ _ valid5452 (by decide +kernel)








































































































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



































































































































































theorem valid3538 : plan3538.Valid := valid_step _ _ _ valid1616 (by decide +kernel)




























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









































































































































































theorem valid6421 : plan6421.Valid := valid_step _ _ _ valid5369 (by decide +kernel)

theorem valid6422 : plan6422.Valid := valid_step _ _ _ valid5378 (by decide +kernel)

theorem valid6423 : plan6423.Valid := valid_step _ _ _ valid5379 (by decide +kernel)

theorem valid6424 : plan6424.Valid := valid_step _ _ _ valid5380 (by decide +kernel)
















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



































































































































theorem valid7074 : plan7074.Valid := valid_step _ _ _ valid5554 (by decide +kernel)

theorem valid7075 : plan7075.Valid := valid_step _ _ _ valid5555 (by decide +kernel)

theorem valid7076 : plan7076.Valid := valid_step _ _ _ valid5556 (by decide +kernel)

theorem valid7077 : plan7077.Valid := valid_step _ _ _ valid5557 (by decide +kernel)

theorem valid7078 : plan7078.Valid := valid_step _ _ _ valid5558 (by decide +kernel)

theorem valid7079 : plan7079.Valid := valid_step _ _ _ valid5559 (by decide +kernel)

theorem valid7080 : plan7080.Valid := valid_step _ _ _ valid5560 (by decide +kernel)

theorem valid7081 : plan7081.Valid := valid_step _ _ _ valid5561 (by decide +kernel)

theorem valid7082 : plan7082.Valid := valid_step _ _ _ valid5562 (by decide +kernel)

theorem valid7083 : plan7083.Valid := valid_step _ _ _ valid5563 (by decide +kernel)

theorem valid7084 : plan7084.Valid := valid_step _ _ _ valid5564 (by decide +kernel)

theorem valid7085 : plan7085.Valid := valid_step _ _ _ valid5565 (by decide +kernel)






































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











theorem valid6054 : plan6054.Valid := valid_step _ _ _ valid3538 (by decide +kernel)





























































































theorem valid6101 : plan6101.Valid := valid_step _ _ _ valid3553 (by decide +kernel)

theorem valid6102 : plan6102.Valid := valid_step _ _ _ valid3554 (by decide +kernel)

theorem valid6103 : plan6103.Valid := valid_step _ _ _ valid3555 (by decide +kernel)

theorem valid6104 : plan6104.Valid := valid_step _ _ _ valid3556 (by decide +kernel)
















































































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



































































































theorem valid7922 : plan7922.Valid := valid_step _ _ _ valid6101 (by decide +kernel)

theorem valid7923 : plan7923.Valid := valid_step _ _ _ valid6102 (by decide +kernel)

theorem valid7924 : plan7924.Valid := valid_step _ _ _ valid6103 (by decide +kernel)

theorem valid7925 : plan7925.Valid := valid_step _ _ _ valid6104 (by decide +kernel)

theorem valid7926 : plan7926.Valid := valid_step _ _ _ valid6054 (by decide +kernel)




















































































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
theorem t6_1406choices : plan7922.choices=[6,10,10,7,7,7].map (options 6 6) := by rfl


theorem t6_1406part0 : t6_1406jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1406frontier : t6_1406root.frontier 0=t6_1406jobs := by rfl
theorem t6_1406all : t6_1406jobs.all (Job.check tree)=true := by
  simp only [t6_1406jobs,List.all_append,List.all_nil,t6_1406part0,Bool.and_self]
theorem t6_1406checked : Checked tree [6,10,10,7,7,7] := by
  refine ⟨plan7922,valid7922,t6_1406choices,?_⟩
  exact check_of_frontier tree 0 t6_1406root t6_1406jobs t6_1406frontier t6_1406all
theorem t6_1407choices : plan7923.choices=[6,10,10,10,7,7].map (options 6 6) := by rfl


theorem t6_1407part0 : t6_1407jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1407frontier : t6_1407root.frontier 0=t6_1407jobs := by rfl
theorem t6_1407all : t6_1407jobs.all (Job.check tree)=true := by
  simp only [t6_1407jobs,List.all_append,List.all_nil,t6_1407part0,Bool.and_self]
theorem t6_1407checked : Checked tree [6,10,10,10,7,7] := by
  refine ⟨plan7923,valid7923,t6_1407choices,?_⟩
  exact check_of_frontier tree 0 t6_1407root t6_1407jobs t6_1407frontier t6_1407all
theorem t6_1408choices : plan7924.choices=[6,10,10,10,10,7].map (options 6 6) := by rfl


theorem t6_1408part0 : t6_1408jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1408frontier : t6_1408root.frontier 0=t6_1408jobs := by rfl
theorem t6_1408all : t6_1408jobs.all (Job.check tree)=true := by
  simp only [t6_1408jobs,List.all_append,List.all_nil,t6_1408part0,Bool.and_self]
theorem t6_1408checked : Checked tree [6,10,10,10,10,7] := by
  refine ⟨plan7924,valid7924,t6_1408choices,?_⟩
  exact check_of_frontier tree 0 t6_1408root t6_1408jobs t6_1408frontier t6_1408all
theorem t6_1409choices : plan7925.choices=[6,10,10,10,10,10].map (options 6 6) := by rfl


theorem t6_1409part0 : t6_1409jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1409frontier : t6_1409root.frontier 0=t6_1409jobs := by rfl
theorem t6_1409all : t6_1409jobs.all (Job.check tree)=true := by
  simp only [t6_1409jobs,List.all_append,List.all_nil,t6_1409part0,Bool.and_self]
theorem t6_1409checked : Checked tree [6,10,10,10,10,10] := by
  refine ⟨plan7925,valid7925,t6_1409choices,?_⟩
  exact check_of_frontier tree 0 t6_1409root t6_1409jobs t6_1409frontier t6_1409all
theorem t6_1410choices : plan7926.choices=[7,7,7,7,7,7].map (options 6 6) := by rfl


theorem t6_1410part0 : t6_1410jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1410frontier : t6_1410root.frontier 0=t6_1410jobs := by rfl
theorem t6_1410all : t6_1410jobs.all (Job.check tree)=true := by
  simp only [t6_1410jobs,List.all_append,List.all_nil,t6_1410part0,Bool.and_self]
theorem t6_1410checked : Checked tree [7,7,7,7,7,7] := by
  refine ⟨plan7926,valid7926,t6_1410choices,?_⟩
  exact check_of_frontier tree 0 t6_1410root t6_1410jobs t6_1410frontier t6_1410all
theorem t6_1411choices : plan6659.choices=[8,2,2,2,7,7].map (options 6 3) := by rfl


theorem t6_1411part0 : t6_1411jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1411frontier : t6_1411root.frontier 0=t6_1411jobs := by rfl
theorem t6_1411all : t6_1411jobs.all (Job.check tree)=true := by
  simp only [t6_1411jobs,List.all_append,List.all_nil,t6_1411part0,Bool.and_self]
theorem t6_1411checked : Checked tree [8,2,2,2,7,7] := by
  refine ⟨plan6659,valid6659,t6_1411choices,?_⟩
  exact check_of_frontier tree 0 t6_1411root t6_1411jobs t6_1411frontier t6_1411all
theorem t6_1412choices : plan6421.choices=[8,2,2,3,3,7].map (options 6 2) := by rfl


theorem t6_1412part0 : t6_1412jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1412frontier : t6_1412root.frontier 0=t6_1412jobs := by rfl
theorem t6_1412all : t6_1412jobs.all (Job.check tree)=true := by
  simp only [t6_1412jobs,List.all_append,List.all_nil,t6_1412part0,Bool.and_self]
theorem t6_1412checked : Checked tree [8,2,2,3,3,7] := by
  refine ⟨plan6421,valid6421,t6_1412choices,?_⟩
  exact check_of_frontier tree 0 t6_1412root t6_1412jobs t6_1412frontier t6_1412all
theorem t6_1413choices : plan6660.choices=[8,2,2,3,6,7].map (options 6 3) := by rfl


theorem t6_1413part0 : t6_1413jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1413frontier : t6_1413root.frontier 0=t6_1413jobs := by rfl
theorem t6_1413all : t6_1413jobs.all (Job.check tree)=true := by
  simp only [t6_1413jobs,List.all_append,List.all_nil,t6_1413part0,Bool.and_self]
theorem t6_1413checked : Checked tree [8,2,2,3,6,7] := by
  refine ⟨plan6660,valid6660,t6_1413choices,?_⟩
  exact check_of_frontier tree 0 t6_1413root t6_1413jobs t6_1413frontier t6_1413all
theorem t6_1414choices : plan6661.choices=[8,2,2,3,7,7].map (options 6 3) := by rfl


theorem t6_1414part0 : t6_1414jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1414frontier : t6_1414root.frontier 0=t6_1414jobs := by rfl
theorem t6_1414all : t6_1414jobs.all (Job.check tree)=true := by
  simp only [t6_1414jobs,List.all_append,List.all_nil,t6_1414part0,Bool.and_self]
theorem t6_1414checked : Checked tree [8,2,2,3,7,7] := by
  refine ⟨plan6661,valid6661,t6_1414choices,?_⟩
  exact check_of_frontier tree 0 t6_1414root t6_1414jobs t6_1414frontier t6_1414all
theorem t6_1415choices : plan6662.choices=[8,2,2,3,10,7].map (options 6 3) := by rfl


theorem t6_1415part0 : t6_1415jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1415frontier : t6_1415root.frontier 0=t6_1415jobs := by rfl
theorem t6_1415all : t6_1415jobs.all (Job.check tree)=true := by
  simp only [t6_1415jobs,List.all_append,List.all_nil,t6_1415part0,Bool.and_self]
theorem t6_1415checked : Checked tree [8,2,2,3,10,7] := by
  refine ⟨plan6662,valid6662,t6_1415choices,?_⟩
  exact check_of_frontier tree 0 t6_1415root t6_1415jobs t6_1415frontier t6_1415all
theorem t6_1416choices : plan7074.choices=[8,2,2,5,7,7].map (options 6 4) := by rfl


theorem t6_1416part0 : t6_1416jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1416frontier : t6_1416root.frontier 0=t6_1416jobs := by rfl
theorem t6_1416all : t6_1416jobs.all (Job.check tree)=true := by
  simp only [t6_1416jobs,List.all_append,List.all_nil,t6_1416part0,Bool.and_self]
theorem t6_1416checked : Checked tree [8,2,2,5,7,7] := by
  refine ⟨plan7074,valid7074,t6_1416choices,?_⟩
  exact check_of_frontier tree 0 t6_1416root t6_1416jobs t6_1416frontier t6_1416all
theorem t6_1417choices : plan7075.choices=[8,2,2,6,6,7].map (options 6 4) := by rfl


theorem t6_1417part0 : t6_1417jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1417frontier : t6_1417root.frontier 0=t6_1417jobs := by rfl
theorem t6_1417all : t6_1417jobs.all (Job.check tree)=true := by
  simp only [t6_1417jobs,List.all_append,List.all_nil,t6_1417part0,Bool.and_self]
theorem t6_1417checked : Checked tree [8,2,2,6,6,7] := by
  refine ⟨plan7075,valid7075,t6_1417choices,?_⟩
  exact check_of_frontier tree 0 t6_1417root t6_1417jobs t6_1417frontier t6_1417all
theorem t6_1418choices : plan7076.choices=[8,2,2,6,7,7].map (options 6 4) := by rfl


theorem t6_1418part0 : t6_1418jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1418frontier : t6_1418root.frontier 0=t6_1418jobs := by rfl
theorem t6_1418all : t6_1418jobs.all (Job.check tree)=true := by
  simp only [t6_1418jobs,List.all_append,List.all_nil,t6_1418part0,Bool.and_self]
theorem t6_1418checked : Checked tree [8,2,2,6,7,7] := by
  refine ⟨plan7076,valid7076,t6_1418choices,?_⟩
  exact check_of_frontier tree 0 t6_1418root t6_1418jobs t6_1418frontier t6_1418all
theorem t6_1419choices : plan7077.choices=[8,2,2,6,10,7].map (options 6 4) := by rfl


theorem t6_1419part0 : t6_1419jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1419frontier : t6_1419root.frontier 0=t6_1419jobs := by rfl
theorem t6_1419all : t6_1419jobs.all (Job.check tree)=true := by
  simp only [t6_1419jobs,List.all_append,List.all_nil,t6_1419part0,Bool.and_self]
theorem t6_1419checked : Checked tree [8,2,2,6,10,7] := by
  refine ⟨plan7077,valid7077,t6_1419choices,?_⟩
  exact check_of_frontier tree 0 t6_1419root t6_1419jobs t6_1419frontier t6_1419all
theorem t6_1420choices : plan7078.choices=[8,2,2,7,7,7].map (options 6 4) := by rfl


theorem t6_1420part0 : t6_1420jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1420frontier : t6_1420root.frontier 0=t6_1420jobs := by rfl
theorem t6_1420all : t6_1420jobs.all (Job.check tree)=true := by
  simp only [t6_1420jobs,List.all_append,List.all_nil,t6_1420part0,Bool.and_self]
theorem t6_1420checked : Checked tree [8,2,2,7,7,7] := by
  refine ⟨plan7078,valid7078,t6_1420choices,?_⟩
  exact check_of_frontier tree 0 t6_1420root t6_1420jobs t6_1420frontier t6_1420all
theorem t6_1421choices : plan7079.choices=[8,2,2,9,7,7].map (options 6 4) := by rfl


theorem t6_1421part0 : t6_1421jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1421frontier : t6_1421root.frontier 0=t6_1421jobs := by rfl
theorem t6_1421all : t6_1421jobs.all (Job.check tree)=true := by
  simp only [t6_1421jobs,List.all_append,List.all_nil,t6_1421part0,Bool.and_self]
theorem t6_1421checked : Checked tree [8,2,2,9,7,7] := by
  refine ⟨plan7079,valid7079,t6_1421choices,?_⟩
  exact check_of_frontier tree 0 t6_1421root t6_1421jobs t6_1421frontier t6_1421all
theorem t6_1422choices : plan7080.choices=[8,2,2,10,7,7].map (options 6 4) := by rfl


theorem t6_1422part0 : t6_1422jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1422frontier : t6_1422root.frontier 0=t6_1422jobs := by rfl
theorem t6_1422all : t6_1422jobs.all (Job.check tree)=true := by
  simp only [t6_1422jobs,List.all_append,List.all_nil,t6_1422part0,Bool.and_self]
theorem t6_1422checked : Checked tree [8,2,2,10,7,7] := by
  refine ⟨plan7080,valid7080,t6_1422choices,?_⟩
  exact check_of_frontier tree 0 t6_1422root t6_1422jobs t6_1422frontier t6_1422all
theorem t6_1423choices : plan7081.choices=[8,2,2,10,10,7].map (options 6 4) := by rfl


theorem t6_1423part0 : t6_1423jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1423frontier : t6_1423root.frontier 0=t6_1423jobs := by rfl
theorem t6_1423all : t6_1423jobs.all (Job.check tree)=true := by
  simp only [t6_1423jobs,List.all_append,List.all_nil,t6_1423part0,Bool.and_self]
theorem t6_1423checked : Checked tree [8,2,2,10,10,7] := by
  refine ⟨plan7081,valid7081,t6_1423choices,?_⟩
  exact check_of_frontier tree 0 t6_1423root t6_1423jobs t6_1423frontier t6_1423all
theorem t6_1424choices : plan6317.choices=[8,2,3,3,3,3].map (options 6 1) := by rfl


theorem t6_1424part0 : t6_1424jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1424frontier : t6_1424root.frontier 0=t6_1424jobs := by rfl
theorem t6_1424all : t6_1424jobs.all (Job.check tree)=true := by
  simp only [t6_1424jobs,List.all_append,List.all_nil,t6_1424part0,Bool.and_self]
theorem t6_1424checked : Checked tree [8,2,3,3,3,3] := by
  refine ⟨plan6317,valid6317,t6_1424choices,?_⟩
  exact check_of_frontier tree 0 t6_1424root t6_1424jobs t6_1424frontier t6_1424all
theorem t6_1425choices : plan6422.choices=[8,2,3,3,3,6].map (options 6 2) := by rfl


theorem t6_1425part0 : t6_1425jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1425frontier : t6_1425root.frontier 0=t6_1425jobs := by rfl
theorem t6_1425all : t6_1425jobs.all (Job.check tree)=true := by
  simp only [t6_1425jobs,List.all_append,List.all_nil,t6_1425part0,Bool.and_self]
theorem t6_1425checked : Checked tree [8,2,3,3,3,6] := by
  refine ⟨plan6422,valid6422,t6_1425choices,?_⟩
  exact check_of_frontier tree 0 t6_1425root t6_1425jobs t6_1425frontier t6_1425all
theorem t6_1426choices : plan6423.choices=[8,2,3,3,3,7].map (options 6 2) := by rfl


theorem t6_1426part0 : t6_1426jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1426frontier : t6_1426root.frontier 0=t6_1426jobs := by rfl
theorem t6_1426all : t6_1426jobs.all (Job.check tree)=true := by
  simp only [t6_1426jobs,List.all_append,List.all_nil,t6_1426part0,Bool.and_self]
theorem t6_1426checked : Checked tree [8,2,3,3,3,7] := by
  refine ⟨plan6423,valid6423,t6_1426choices,?_⟩
  exact check_of_frontier tree 0 t6_1426root t6_1426jobs t6_1426frontier t6_1426all
theorem t6_1427choices : plan6424.choices=[8,2,3,3,3,10].map (options 6 2) := by rfl


theorem t6_1427part0 : t6_1427jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1427frontier : t6_1427root.frontier 0=t6_1427jobs := by rfl
theorem t6_1427all : t6_1427jobs.all (Job.check tree)=true := by
  simp only [t6_1427jobs,List.all_append,List.all_nil,t6_1427part0,Bool.and_self]
theorem t6_1427checked : Checked tree [8,2,3,3,3,10] := by
  refine ⟨plan6424,valid6424,t6_1427choices,?_⟩
  exact check_of_frontier tree 0 t6_1427root t6_1427jobs t6_1427frontier t6_1427all
theorem t6_1428choices : plan6663.choices=[8,2,3,3,6,6].map (options 6 3) := by rfl


theorem t6_1428part0 : t6_1428jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1428frontier : t6_1428root.frontier 0=t6_1428jobs := by rfl
theorem t6_1428all : t6_1428jobs.all (Job.check tree)=true := by
  simp only [t6_1428jobs,List.all_append,List.all_nil,t6_1428part0,Bool.and_self]
theorem t6_1428checked : Checked tree [8,2,3,3,6,6] := by
  refine ⟨plan6663,valid6663,t6_1428choices,?_⟩
  exact check_of_frontier tree 0 t6_1428root t6_1428jobs t6_1428frontier t6_1428all
theorem t6_1429choices : plan6664.choices=[8,2,3,3,6,7].map (options 6 3) := by rfl


theorem t6_1429part0 : t6_1429jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1429part1 : t6_1429jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1429frontier : t6_1429root.frontier 1=t6_1429jobs := by rfl
theorem t6_1429all : t6_1429jobs.all (Job.check tree)=true := by
  simp only [t6_1429jobs,List.all_append,List.all_nil,t6_1429part0,t6_1429part1,Bool.and_self]
theorem t6_1429checked : Checked tree [8,2,3,3,6,7] := by
  refine ⟨plan6664,valid6664,t6_1429choices,?_⟩
  exact check_of_frontier tree 1 t6_1429root t6_1429jobs t6_1429frontier t6_1429all
theorem t6_1430choices : plan6665.choices=[8,2,3,3,6,10].map (options 6 3) := by rfl


theorem t6_1430part0 : t6_1430jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1430frontier : t6_1430root.frontier 0=t6_1430jobs := by rfl
theorem t6_1430all : t6_1430jobs.all (Job.check tree)=true := by
  simp only [t6_1430jobs,List.all_append,List.all_nil,t6_1430part0,Bool.and_self]
theorem t6_1430checked : Checked tree [8,2,3,3,6,10] := by
  refine ⟨plan6665,valid6665,t6_1430choices,?_⟩
  exact check_of_frontier tree 0 t6_1430root t6_1430jobs t6_1430frontier t6_1430all
theorem t6_1431choices : plan6666.choices=[8,2,3,3,7,7].map (options 6 3) := by rfl


theorem t6_1431part0 : t6_1431jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1431part1 : t6_1431jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1431part2 : t6_1431jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1431frontier : t6_1431root.frontier 1=t6_1431jobs := by rfl
theorem t6_1431all : t6_1431jobs.all (Job.check tree)=true := by
  simp only [t6_1431jobs,List.all_append,List.all_nil,t6_1431part0,t6_1431part1,t6_1431part2,Bool.and_self]
theorem t6_1431checked : Checked tree [8,2,3,3,7,7] := by
  refine ⟨plan6666,valid6666,t6_1431choices,?_⟩
  exact check_of_frontier tree 1 t6_1431root t6_1431jobs t6_1431frontier t6_1431all
theorem t6_1432choices : plan6667.choices=[8,2,3,3,10,7].map (options 6 3) := by rfl


theorem t6_1432part0 : t6_1432jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1432part1 : t6_1432jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1432frontier : t6_1432root.frontier 1=t6_1432jobs := by rfl
theorem t6_1432all : t6_1432jobs.all (Job.check tree)=true := by
  simp only [t6_1432jobs,List.all_append,List.all_nil,t6_1432part0,t6_1432part1,Bool.and_self]
theorem t6_1432checked : Checked tree [8,2,3,3,10,7] := by
  refine ⟨plan6667,valid6667,t6_1432choices,?_⟩
  exact check_of_frontier tree 1 t6_1432root t6_1432jobs t6_1432frontier t6_1432all
theorem t6_1433choices : plan6668.choices=[8,2,3,3,10,10].map (options 6 3) := by rfl


theorem t6_1433part0 : t6_1433jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1433frontier : t6_1433root.frontier 0=t6_1433jobs := by rfl
theorem t6_1433all : t6_1433jobs.all (Job.check tree)=true := by
  simp only [t6_1433jobs,List.all_append,List.all_nil,t6_1433part0,Bool.and_self]
theorem t6_1433checked : Checked tree [8,2,3,3,10,10] := by
  refine ⟨plan6668,valid6668,t6_1433choices,?_⟩
  exact check_of_frontier tree 0 t6_1433root t6_1433jobs t6_1433frontier t6_1433all
theorem t6_1434choices : plan7082.choices=[8,2,3,6,6,6].map (options 6 4) := by rfl


theorem t6_1434part0 : t6_1434jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1434frontier : t6_1434root.frontier 0=t6_1434jobs := by rfl
theorem t6_1434all : t6_1434jobs.all (Job.check tree)=true := by
  simp only [t6_1434jobs,List.all_append,List.all_nil,t6_1434part0,Bool.and_self]
theorem t6_1434checked : Checked tree [8,2,3,6,6,6] := by
  refine ⟨plan7082,valid7082,t6_1434choices,?_⟩
  exact check_of_frontier tree 0 t6_1434root t6_1434jobs t6_1434frontier t6_1434all
theorem t6_1435choices : plan7083.choices=[8,2,3,6,6,7].map (options 6 4) := by rfl


theorem t6_1435part0 : t6_1435jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1435part1 : t6_1435jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1435frontier : t6_1435root.frontier 1=t6_1435jobs := by rfl
theorem t6_1435all : t6_1435jobs.all (Job.check tree)=true := by
  simp only [t6_1435jobs,List.all_append,List.all_nil,t6_1435part0,t6_1435part1,Bool.and_self]
theorem t6_1435checked : Checked tree [8,2,3,6,6,7] := by
  refine ⟨plan7083,valid7083,t6_1435choices,?_⟩
  exact check_of_frontier tree 1 t6_1435root t6_1435jobs t6_1435frontier t6_1435all
theorem t6_1436choices : plan7084.choices=[8,2,3,6,6,10].map (options 6 4) := by rfl


theorem t6_1436part0 : t6_1436jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1436frontier : t6_1436root.frontier 0=t6_1436jobs := by rfl
theorem t6_1436all : t6_1436jobs.all (Job.check tree)=true := by
  simp only [t6_1436jobs,List.all_append,List.all_nil,t6_1436part0,Bool.and_self]
theorem t6_1436checked : Checked tree [8,2,3,6,6,10] := by
  refine ⟨plan7084,valid7084,t6_1436choices,?_⟩
  exact check_of_frontier tree 0 t6_1436root t6_1436jobs t6_1436frontier t6_1436all
theorem t6_1437choices : plan7085.choices=[8,2,3,6,7,7].map (options 6 4) := by rfl


theorem t6_1437part0 : t6_1437jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1437part1 : t6_1437jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1437part2 : t6_1437jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1437frontier : t6_1437root.frontier 2=t6_1437jobs := by rfl
theorem t6_1437all : t6_1437jobs.all (Job.check tree)=true := by
  simp only [t6_1437jobs,List.all_append,List.all_nil,t6_1437part0,t6_1437part1,t6_1437part2,Bool.and_self]
theorem t6_1437checked : Checked tree [8,2,3,6,7,7] := by
  refine ⟨plan7085,valid7085,t6_1437choices,?_⟩
  exact check_of_frontier tree 2 t6_1437root t6_1437jobs t6_1437frontier t6_1437all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks138 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1418checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1406checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1419checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1420checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1421checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1422checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1423checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1424checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1425checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1426checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1427checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1428checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1407checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1429checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1430checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1431checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1432checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1433checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1434checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1435checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1436checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1408checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1437checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1409checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1410checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1411checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1412checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1413checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1414checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1415checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1416checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1417checked⟩
