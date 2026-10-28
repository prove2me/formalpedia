-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks056
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:07:13.441973+00:00
-- url     : https://prove2.me/submissions/c1ad2391-2a90-4bdd-91eb-263183bb9498

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks056
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans075
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



theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid134 : plan134.Valid := valid_step _ _ _ valid0 (by decide +kernel)




















































































































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



theorem valid578 : plan578.Valid := valid_step _ _ _ valid134 (by decide +kernel)

theorem valid579 : plan579.Valid := valid_step _ _ _ valid134 (by decide +kernel)


























































































































































































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











theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)



theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid573 : plan573.Valid := valid_step _ _ _ valid132 (by decide +kernel)





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







































































































































theorem valid1508 : plan1508.Valid := valid_step _ _ _ valid541 (by decide +kernel)















theorem valid1516 : plan1516.Valid := valid_step _ _ _ valid546 (by decide +kernel)

theorem valid1517 : plan1517.Valid := valid_step _ _ _ valid547 (by decide +kernel)

theorem valid1518 : plan1518.Valid := valid_step _ _ _ valid548 (by decide +kernel)



























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



















































theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)















theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)



theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)



theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)









theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1582 : plan1582.Valid := valid_step _ _ _ valid573 (by decide +kernel)























theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)



theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)



theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)









theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)






















































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



































theorem valid3285 : plan3285.Valid := valid_step _ _ _ valid1535 (by decide +kernel)









































theorem valid3306 : plan3306.Valid := valid_step _ _ _ valid1532 (by decide +kernel)

theorem valid3307 : plan3307.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3308 : plan3308.Valid := valid_step _ _ _ valid1534 (by decide +kernel)

theorem valid3309 : plan3309.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3310 : plan3310.Valid := valid_step _ _ _ valid1536 (by decide +kernel)











































































theorem valid3348 : plan3348.Valid := valid_step _ _ _ valid1572 (by decide +kernel)



theorem valid3350 : plan3350.Valid := valid_step _ _ _ valid1575 (by decide +kernel)



theorem valid3352 : plan3352.Valid := valid_step _ _ _ valid1580 (by decide +kernel)
















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































































































































































theorem valid5360 : plan5360.Valid := valid_step _ _ _ valid3246 (by decide +kernel)
































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



















































theorem valid5402 : plan5402.Valid := valid_step _ _ _ valid3266 (by decide +kernel)



theorem valid5404 : plan5404.Valid := valid_step _ _ _ valid3265 (by decide +kernel)

theorem valid5405 : plan5405.Valid := valid_step _ _ _ valid3266 (by decide +kernel)

theorem valid5406 : plan5406.Valid := valid_step _ _ _ valid3267 (by decide +kernel)




































































































































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













































































































theorem valid6295 : plan6295.Valid := valid_step _ _ _ valid5360 (by decide +kernel)


















































































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



theorem valid3363 : plan3363.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3364 : plan3364.Valid := valid_step _ _ _ valid1573 (by decide +kernel)



theorem valid3366 : plan3366.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3367 : plan3367.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3368 : plan3368.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

















theorem valid3377 : plan3377.Valid := valid_step _ _ _ valid1562 (by decide +kernel)













































































theorem valid3416 : plan3416.Valid := valid_step _ _ _ valid1562 (by decide +kernel)



































theorem valid3434 : plan3434.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3435 : plan3435.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3436 : plan3436.Valid := valid_step _ _ _ valid1582 (by decide +kernel)



























theorem valid3450 : plan3450.Valid := valid_step _ _ _ valid1599 (by decide +kernel)












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















































theorem valid5496 : plan5496.Valid := valid_step _ _ _ valid3285 (by decide +kernel)



theorem valid5498 : plan5498.Valid := valid_step _ _ _ valid3307 (by decide +kernel)

theorem valid5499 : plan5499.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5500 : plan5500.Valid := valid_step _ _ _ valid3310 (by decide +kernel)







theorem valid5504 : plan5504.Valid := valid_step _ _ _ valid3306 (by decide +kernel)

theorem valid5505 : plan5505.Valid := valid_step _ _ _ valid3307 (by decide +kernel)

theorem valid5506 : plan5506.Valid := valid_step _ _ _ valid3308 (by decide +kernel)




























































































































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

































































































































































theorem valid6513 : plan6513.Valid := valid_step _ _ _ valid5496 (by decide +kernel)

theorem valid6514 : plan6514.Valid := valid_step _ _ _ valid5498 (by decide +kernel)

theorem valid6515 : plan6515.Valid := valid_step _ _ _ valid5499 (by decide +kernel)

theorem valid6516 : plan6516.Valid := valid_step _ _ _ valid5500 (by decide +kernel)

theorem valid6517 : plan6517.Valid := valid_step _ _ _ valid5504 (by decide +kernel)

theorem valid6518 : plan6518.Valid := valid_step _ _ _ valid5505 (by decide +kernel)

theorem valid6519 : plan6519.Valid := valid_step _ _ _ valid5506 (by decide +kernel)


















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























































































































































theorem valid5644 : plan5644.Valid := valid_step _ _ _ valid3434 (by decide +kernel)

theorem valid5645 : plan5645.Valid := valid_step _ _ _ valid3435 (by decide +kernel)

theorem valid5646 : plan5646.Valid := valid_step _ _ _ valid3436 (by decide +kernel)



theorem valid5648 : plan5648.Valid := valid_step _ _ _ valid3348 (by decide +kernel)

theorem valid5649 : plan5649.Valid := valid_step _ _ _ valid3350 (by decide +kernel)

theorem valid5650 : plan5650.Valid := valid_step _ _ _ valid3352 (by decide +kernel)







theorem valid5654 : plan5654.Valid := valid_step _ _ _ valid3361 (by decide +kernel)

theorem valid5655 : plan5655.Valid := valid_step _ _ _ valid3363 (by decide +kernel)

theorem valid5656 : plan5656.Valid := valid_step _ _ _ valid3364 (by decide +kernel)

theorem valid5657 : plan5657.Valid := valid_step _ _ _ valid3366 (by decide +kernel)

theorem valid5658 : plan5658.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5659 : plan5659.Valid := valid_step _ _ _ valid3368 (by decide +kernel)

theorem valid5660 : plan5660.Valid := valid_step _ _ _ valid3377 (by decide +kernel)

theorem valid5661 : plan5661.Valid := valid_step _ _ _ valid3416 (by decide +kernel)






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















theorem valid3464 : plan3464.Valid := valid_step _ _ _ valid1596 (by decide +kernel)





theorem valid3467 : plan3467.Valid := valid_step _ _ _ valid1599 (by decide +kernel)









theorem valid3472 : plan3472.Valid := valid_step _ _ _ valid1604 (by decide +kernel)







theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)



theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)



theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)



theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3486 : plan3486.Valid := valid_step _ _ _ valid1599 (by decide +kernel)



















theorem valid3496 : plan3496.Valid := valid_step _ _ _ valid1596 (by decide +kernel)





theorem valid3499 : plan3499.Valid := valid_step _ _ _ valid1599 (by decide +kernel)









theorem valid3504 : plan3504.Valid := valid_step _ _ _ valid1604 (by decide +kernel)





theorem valid3507 : plan3507.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3508 : plan3508.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3509 : plan3509.Valid := valid_step _ _ _ valid1605 (by decide +kernel)






















































































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































































































































































































theorem valid6816 : plan6816.Valid := valid_step _ _ _ valid5644 (by decide +kernel)
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



































































theorem valid5794 : plan5794.Valid := valid_step _ _ _ valid3450 (by decide +kernel)



theorem valid5796 : plan5796.Valid := valid_step _ _ _ valid3464 (by decide +kernel)

theorem valid5797 : plan5797.Valid := valid_step _ _ _ valid3467 (by decide +kernel)

theorem valid5798 : plan5798.Valid := valid_step _ _ _ valid3472 (by decide +kernel)

theorem valid5799 : plan5799.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5800 : plan5800.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5801 : plan5801.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5802 : plan5802.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5803 : plan5803.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5804 : plan5804.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5805 : plan5805.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

theorem valid5806 : plan5806.Valid := valid_step _ _ _ valid3486 (by decide +kernel)



theorem valid5808 : plan5808.Valid := valid_step _ _ _ valid3496 (by decide +kernel)

theorem valid5809 : plan5809.Valid := valid_step _ _ _ valid3499 (by decide +kernel)

theorem valid5810 : plan5810.Valid := valid_step _ _ _ valid3504 (by decide +kernel)

theorem valid5811 : plan5811.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5812 : plan5812.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5813 : plan5813.Valid := valid_step _ _ _ valid3509 (by decide +kernel)






















































































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





































theorem valid6355 : plan6355.Valid := valid_step _ _ _ valid5402 (by decide +kernel)

theorem valid6356 : plan6356.Valid := valid_step _ _ _ valid5404 (by decide +kernel)

theorem valid6357 : plan6357.Valid := valid_step _ _ _ valid5405 (by decide +kernel)

theorem valid6358 : plan6358.Valid := valid_step _ _ _ valid5406 (by decide +kernel)




















































































































































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























theorem valid7212 : plan7212.Valid := valid_step _ _ _ valid5794 (by decide +kernel)

theorem valid7213 : plan7213.Valid := valid_step _ _ _ valid5796 (by decide +kernel)

theorem valid7214 : plan7214.Valid := valid_step _ _ _ valid5797 (by decide +kernel)

theorem valid7215 : plan7215.Valid := valid_step _ _ _ valid5798 (by decide +kernel)

theorem valid7216 : plan7216.Valid := valid_step _ _ _ valid5799 (by decide +kernel)

theorem valid7217 : plan7217.Valid := valid_step _ _ _ valid5800 (by decide +kernel)

theorem valid7218 : plan7218.Valid := valid_step _ _ _ valid5801 (by decide +kernel)

theorem valid7219 : plan7219.Valid := valid_step _ _ _ valid5802 (by decide +kernel)

theorem valid7220 : plan7220.Valid := valid_step _ _ _ valid5803 (by decide +kernel)

theorem valid7221 : plan7221.Valid := valid_step _ _ _ valid5804 (by decide +kernel)

theorem valid7222 : plan7222.Valid := valid_step _ _ _ valid5805 (by decide +kernel)

theorem valid7223 : plan7223.Valid := valid_step _ _ _ valid5806 (by decide +kernel)

theorem valid7224 : plan7224.Valid := valid_step _ _ _ valid5808 (by decide +kernel)

theorem valid7225 : plan7225.Valid := valid_step _ _ _ valid5809 (by decide +kernel)

theorem valid7226 : plan7226.Valid := valid_step _ _ _ valid5810 (by decide +kernel)

theorem valid7227 : plan7227.Valid := valid_step _ _ _ valid5811 (by decide +kernel)

theorem valid7228 : plan7228.Valid := valid_step _ _ _ valid5812 (by decide +kernel)

theorem valid7229 : plan7229.Valid := valid_step _ _ _ valid5813 (by decide +kernel)






































































































































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

theorem valid6817 : plan6817.Valid := valid_step _ _ _ valid5645 (by decide +kernel)

theorem valid6818 : plan6818.Valid := valid_step _ _ _ valid5646 (by decide +kernel)

theorem valid6819 : plan6819.Valid := valid_step _ _ _ valid5648 (by decide +kernel)

theorem valid6820 : plan6820.Valid := valid_step _ _ _ valid5649 (by decide +kernel)

theorem valid6821 : plan6821.Valid := valid_step _ _ _ valid5650 (by decide +kernel)

theorem valid6822 : plan6822.Valid := valid_step _ _ _ valid5654 (by decide +kernel)

theorem valid6823 : plan6823.Valid := valid_step _ _ _ valid5655 (by decide +kernel)

theorem valid6824 : plan6824.Valid := valid_step _ _ _ valid5656 (by decide +kernel)

theorem valid6825 : plan6825.Valid := valid_step _ _ _ valid5657 (by decide +kernel)

theorem valid6826 : plan6826.Valid := valid_step _ _ _ valid5658 (by decide +kernel)

theorem valid6827 : plan6827.Valid := valid_step _ _ _ valid5659 (by decide +kernel)

theorem valid6828 : plan6828.Valid := valid_step _ _ _ valid5660 (by decide +kernel)

theorem valid6829 : plan6829.Valid := valid_step _ _ _ valid5661 (by decide +kernel)






































































































































































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
theorem t6_317choices : plan6816.choices=[1,3,10,10,7,7].map (options 6 4) := by rfl


theorem t6_317part0 : t6_317jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_317part1 : t6_317jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_317part2 : t6_317jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_317part3 : t6_317jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_317frontier : t6_317root.frontier 2=t6_317jobs := by rfl
theorem t6_317all : t6_317jobs.all (Job.check tree)=true := by
  simp only [t6_317jobs,List.all_append,List.all_nil,t6_317part0,t6_317part1,t6_317part2,t6_317part3,Bool.and_self]
theorem t6_317checked : Checked tree [1,3,10,10,7,7] := by
  refine ⟨plan6816,valid6816,t6_317choices,?_⟩
  exact check_of_frontier tree 2 t6_317root t6_317jobs t6_317frontier t6_317all
theorem t6_318choices : plan6817.choices=[1,3,10,10,10,7].map (options 6 4) := by rfl


theorem t6_318part0 : t6_318jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_318part1 : t6_318jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_318frontier : t6_318root.frontier 1=t6_318jobs := by rfl
theorem t6_318all : t6_318jobs.all (Job.check tree)=true := by
  simp only [t6_318jobs,List.all_append,List.all_nil,t6_318part0,t6_318part1,Bool.and_self]
theorem t6_318checked : Checked tree [1,3,10,10,10,7] := by
  refine ⟨plan6817,valid6817,t6_318choices,?_⟩
  exact check_of_frontier tree 1 t6_318root t6_318jobs t6_318frontier t6_318all
theorem t6_319choices : plan6818.choices=[1,3,10,10,10,10].map (options 6 4) := by rfl


theorem t6_319part0 : t6_319jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_319frontier : t6_319root.frontier 0=t6_319jobs := by rfl
theorem t6_319all : t6_319jobs.all (Job.check tree)=true := by
  simp only [t6_319jobs,List.all_append,List.all_nil,t6_319part0,Bool.and_self]
theorem t6_319checked : Checked tree [1,3,10,10,10,10] := by
  refine ⟨plan6818,valid6818,t6_319choices,?_⟩
  exact check_of_frontier tree 0 t6_319root t6_319jobs t6_319frontier t6_319all
theorem t6_320choices : plan6513.choices=[1,4,2,3,7,7].map (options 6 3) := by rfl


theorem t6_320part0 : t6_320jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_320frontier : t6_320root.frontier 0=t6_320jobs := by rfl
theorem t6_320all : t6_320jobs.all (Job.check tree)=true := by
  simp only [t6_320jobs,List.all_append,List.all_nil,t6_320part0,Bool.and_self]
theorem t6_320checked : Checked tree [1,4,2,3,7,7] := by
  refine ⟨plan6513,valid6513,t6_320choices,?_⟩
  exact check_of_frontier tree 0 t6_320root t6_320jobs t6_320frontier t6_320all
theorem t6_321choices : plan6819.choices=[1,4,2,6,7,7].map (options 6 4) := by rfl


theorem t6_321part0 : t6_321jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_321frontier : t6_321root.frontier 0=t6_321jobs := by rfl
theorem t6_321all : t6_321jobs.all (Job.check tree)=true := by
  simp only [t6_321jobs,List.all_append,List.all_nil,t6_321part0,Bool.and_self]
theorem t6_321checked : Checked tree [1,4,2,6,7,7] := by
  refine ⟨plan6819,valid6819,t6_321choices,?_⟩
  exact check_of_frontier tree 0 t6_321root t6_321jobs t6_321frontier t6_321all
theorem t6_322choices : plan6820.choices=[1,4,2,7,7,7].map (options 6 4) := by rfl


theorem t6_322part0 : t6_322jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_322frontier : t6_322root.frontier 0=t6_322jobs := by rfl
theorem t6_322all : t6_322jobs.all (Job.check tree)=true := by
  simp only [t6_322jobs,List.all_append,List.all_nil,t6_322part0,Bool.and_self]
theorem t6_322checked : Checked tree [1,4,2,7,7,7] := by
  refine ⟨plan6820,valid6820,t6_322choices,?_⟩
  exact check_of_frontier tree 0 t6_322root t6_322jobs t6_322frontier t6_322all
theorem t6_323choices : plan6821.choices=[1,4,2,10,7,7].map (options 6 4) := by rfl


theorem t6_323part0 : t6_323jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_323frontier : t6_323root.frontier 0=t6_323jobs := by rfl
theorem t6_323all : t6_323jobs.all (Job.check tree)=true := by
  simp only [t6_323jobs,List.all_append,List.all_nil,t6_323part0,Bool.and_self]
theorem t6_323checked : Checked tree [1,4,2,10,7,7] := by
  refine ⟨plan6821,valid6821,t6_323choices,?_⟩
  exact check_of_frontier tree 0 t6_323root t6_323jobs t6_323frontier t6_323all
theorem t6_324choices : plan6355.choices=[1,4,3,3,3,7].map (options 6 2) := by rfl


theorem t6_324part0 : t6_324jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_324frontier : t6_324root.frontier 0=t6_324jobs := by rfl
theorem t6_324all : t6_324jobs.all (Job.check tree)=true := by
  simp only [t6_324jobs,List.all_append,List.all_nil,t6_324part0,Bool.and_self]
theorem t6_324checked : Checked tree [1,4,3,3,3,7] := by
  refine ⟨plan6355,valid6355,t6_324choices,?_⟩
  exact check_of_frontier tree 0 t6_324root t6_324jobs t6_324frontier t6_324all
theorem t6_325choices : plan6514.choices=[1,4,3,3,6,7].map (options 6 3) := by rfl


theorem t6_325part0 : t6_325jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_325frontier : t6_325root.frontier 0=t6_325jobs := by rfl
theorem t6_325all : t6_325jobs.all (Job.check tree)=true := by
  simp only [t6_325jobs,List.all_append,List.all_nil,t6_325part0,Bool.and_self]
theorem t6_325checked : Checked tree [1,4,3,3,6,7] := by
  refine ⟨plan6514,valid6514,t6_325choices,?_⟩
  exact check_of_frontier tree 0 t6_325root t6_325jobs t6_325frontier t6_325all
theorem t6_326choices : plan6515.choices=[1,4,3,3,7,7].map (options 6 3) := by rfl


theorem t6_326part0 : t6_326jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_326frontier : t6_326root.frontier 0=t6_326jobs := by rfl
theorem t6_326all : t6_326jobs.all (Job.check tree)=true := by
  simp only [t6_326jobs,List.all_append,List.all_nil,t6_326part0,Bool.and_self]
theorem t6_326checked : Checked tree [1,4,3,3,7,7] := by
  refine ⟨plan6515,valid6515,t6_326choices,?_⟩
  exact check_of_frontier tree 0 t6_326root t6_326jobs t6_326frontier t6_326all
theorem t6_327choices : plan6516.choices=[1,4,3,3,10,7].map (options 6 3) := by rfl


theorem t6_327part0 : t6_327jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_327frontier : t6_327root.frontier 0=t6_327jobs := by rfl
theorem t6_327all : t6_327jobs.all (Job.check tree)=true := by
  simp only [t6_327jobs,List.all_append,List.all_nil,t6_327part0,Bool.and_self]
theorem t6_327checked : Checked tree [1,4,3,3,10,7] := by
  refine ⟨plan6516,valid6516,t6_327choices,?_⟩
  exact check_of_frontier tree 0 t6_327root t6_327jobs t6_327frontier t6_327all
theorem t6_328choices : plan6822.choices=[1,4,3,6,6,7].map (options 6 4) := by rfl


theorem t6_328part0 : t6_328jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_328frontier : t6_328root.frontier 0=t6_328jobs := by rfl
theorem t6_328all : t6_328jobs.all (Job.check tree)=true := by
  simp only [t6_328jobs,List.all_append,List.all_nil,t6_328part0,Bool.and_self]
theorem t6_328checked : Checked tree [1,4,3,6,6,7] := by
  refine ⟨plan6822,valid6822,t6_328choices,?_⟩
  exact check_of_frontier tree 0 t6_328root t6_328jobs t6_328frontier t6_328all
theorem t6_329choices : plan6823.choices=[1,4,3,6,7,7].map (options 6 4) := by rfl


theorem t6_329part0 : t6_329jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_329frontier : t6_329root.frontier 0=t6_329jobs := by rfl
theorem t6_329all : t6_329jobs.all (Job.check tree)=true := by
  simp only [t6_329jobs,List.all_append,List.all_nil,t6_329part0,Bool.and_self]
theorem t6_329checked : Checked tree [1,4,3,6,7,7] := by
  refine ⟨plan6823,valid6823,t6_329choices,?_⟩
  exact check_of_frontier tree 0 t6_329root t6_329jobs t6_329frontier t6_329all
theorem t6_330choices : plan6824.choices=[1,4,3,6,10,7].map (options 6 4) := by rfl


theorem t6_330part0 : t6_330jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_330frontier : t6_330root.frontier 0=t6_330jobs := by rfl
theorem t6_330all : t6_330jobs.all (Job.check tree)=true := by
  simp only [t6_330jobs,List.all_append,List.all_nil,t6_330part0,Bool.and_self]
theorem t6_330checked : Checked tree [1,4,3,6,10,7] := by
  refine ⟨plan6824,valid6824,t6_330choices,?_⟩
  exact check_of_frontier tree 0 t6_330root t6_330jobs t6_330frontier t6_330all
theorem t6_331choices : plan6825.choices=[1,4,3,7,7,7].map (options 6 4) := by rfl


theorem t6_331part0 : t6_331jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_331frontier : t6_331root.frontier 0=t6_331jobs := by rfl
theorem t6_331all : t6_331jobs.all (Job.check tree)=true := by
  simp only [t6_331jobs,List.all_append,List.all_nil,t6_331part0,Bool.and_self]
theorem t6_331checked : Checked tree [1,4,3,7,7,7] := by
  refine ⟨plan6825,valid6825,t6_331choices,?_⟩
  exact check_of_frontier tree 0 t6_331root t6_331jobs t6_331frontier t6_331all
theorem t6_332choices : plan6826.choices=[1,4,3,10,7,7].map (options 6 4) := by rfl


theorem t6_332part0 : t6_332jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_332frontier : t6_332root.frontier 0=t6_332jobs := by rfl
theorem t6_332all : t6_332jobs.all (Job.check tree)=true := by
  simp only [t6_332jobs,List.all_append,List.all_nil,t6_332part0,Bool.and_self]
theorem t6_332checked : Checked tree [1,4,3,10,7,7] := by
  refine ⟨plan6826,valid6826,t6_332choices,?_⟩
  exact check_of_frontier tree 0 t6_332root t6_332jobs t6_332frontier t6_332all
theorem t6_333choices : plan6827.choices=[1,4,3,10,10,7].map (options 6 4) := by rfl


theorem t6_333part0 : t6_333jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_333frontier : t6_333root.frontier 0=t6_333jobs := by rfl
theorem t6_333all : t6_333jobs.all (Job.check tree)=true := by
  simp only [t6_333jobs,List.all_append,List.all_nil,t6_333part0,Bool.and_self]
theorem t6_333checked : Checked tree [1,4,3,10,10,7] := by
  refine ⟨plan6827,valid6827,t6_333choices,?_⟩
  exact check_of_frontier tree 0 t6_333root t6_333jobs t6_333frontier t6_333all
theorem t6_334choices : plan7212.choices=[1,4,4,7,7,7].map (options 6 5) := by rfl


theorem t6_334part0 : t6_334jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_334frontier : t6_334root.frontier 0=t6_334jobs := by rfl
theorem t6_334all : t6_334jobs.all (Job.check tree)=true := by
  simp only [t6_334jobs,List.all_append,List.all_nil,t6_334part0,Bool.and_self]
theorem t6_334checked : Checked tree [1,4,4,7,7,7] := by
  refine ⟨plan7212,valid7212,t6_334choices,?_⟩
  exact check_of_frontier tree 0 t6_334root t6_334jobs t6_334frontier t6_334all
theorem t6_335choices : plan6828.choices=[1,4,5,3,7,7].map (options 6 4) := by rfl


theorem t6_335part0 : t6_335jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_335frontier : t6_335root.frontier 0=t6_335jobs := by rfl
theorem t6_335all : t6_335jobs.all (Job.check tree)=true := by
  simp only [t6_335jobs,List.all_append,List.all_nil,t6_335part0,Bool.and_self]
theorem t6_335checked : Checked tree [1,4,5,3,7,7] := by
  refine ⟨plan6828,valid6828,t6_335choices,?_⟩
  exact check_of_frontier tree 0 t6_335root t6_335jobs t6_335frontier t6_335all
theorem t6_336choices : plan7213.choices=[1,4,5,6,7,7].map (options 6 5) := by rfl


theorem t6_336part0 : t6_336jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_336frontier : t6_336root.frontier 0=t6_336jobs := by rfl
theorem t6_336all : t6_336jobs.all (Job.check tree)=true := by
  simp only [t6_336jobs,List.all_append,List.all_nil,t6_336part0,Bool.and_self]
theorem t6_336checked : Checked tree [1,4,5,6,7,7] := by
  refine ⟨plan7213,valid7213,t6_336choices,?_⟩
  exact check_of_frontier tree 0 t6_336root t6_336jobs t6_336frontier t6_336all
theorem t6_337choices : plan7214.choices=[1,4,5,7,7,7].map (options 6 5) := by rfl


theorem t6_337part0 : t6_337jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_337frontier : t6_337root.frontier 0=t6_337jobs := by rfl
theorem t6_337all : t6_337jobs.all (Job.check tree)=true := by
  simp only [t6_337jobs,List.all_append,List.all_nil,t6_337part0,Bool.and_self]
theorem t6_337checked : Checked tree [1,4,5,7,7,7] := by
  refine ⟨plan7214,valid7214,t6_337choices,?_⟩
  exact check_of_frontier tree 0 t6_337root t6_337jobs t6_337frontier t6_337all
theorem t6_338choices : plan7215.choices=[1,4,5,10,7,7].map (options 6 5) := by rfl


theorem t6_338part0 : t6_338jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_338frontier : t6_338root.frontier 0=t6_338jobs := by rfl
theorem t6_338all : t6_338jobs.all (Job.check tree)=true := by
  simp only [t6_338jobs,List.all_append,List.all_nil,t6_338part0,Bool.and_self]
theorem t6_338checked : Checked tree [1,4,5,10,7,7] := by
  refine ⟨plan7215,valid7215,t6_338choices,?_⟩
  exact check_of_frontier tree 0 t6_338root t6_338jobs t6_338frontier t6_338all
theorem t6_339choices : plan7216.choices=[1,4,6,6,6,7].map (options 6 5) := by rfl


theorem t6_339part0 : t6_339jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_339frontier : t6_339root.frontier 0=t6_339jobs := by rfl
theorem t6_339all : t6_339jobs.all (Job.check tree)=true := by
  simp only [t6_339jobs,List.all_append,List.all_nil,t6_339part0,Bool.and_self]
theorem t6_339checked : Checked tree [1,4,6,6,6,7] := by
  refine ⟨plan7216,valid7216,t6_339choices,?_⟩
  exact check_of_frontier tree 0 t6_339root t6_339jobs t6_339frontier t6_339all
theorem t6_340choices : plan7217.choices=[1,4,6,6,7,7].map (options 6 5) := by rfl


theorem t6_340part0 : t6_340jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_340frontier : t6_340root.frontier 0=t6_340jobs := by rfl
theorem t6_340all : t6_340jobs.all (Job.check tree)=true := by
  simp only [t6_340jobs,List.all_append,List.all_nil,t6_340part0,Bool.and_self]
theorem t6_340checked : Checked tree [1,4,6,6,7,7] := by
  refine ⟨plan7217,valid7217,t6_340choices,?_⟩
  exact check_of_frontier tree 0 t6_340root t6_340jobs t6_340frontier t6_340all
theorem t6_341choices : plan7218.choices=[1,4,6,6,10,7].map (options 6 5) := by rfl


theorem t6_341part0 : t6_341jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_341frontier : t6_341root.frontier 0=t6_341jobs := by rfl
theorem t6_341all : t6_341jobs.all (Job.check tree)=true := by
  simp only [t6_341jobs,List.all_append,List.all_nil,t6_341part0,Bool.and_self]
theorem t6_341checked : Checked tree [1,4,6,6,10,7] := by
  refine ⟨plan7218,valid7218,t6_341choices,?_⟩
  exact check_of_frontier tree 0 t6_341root t6_341jobs t6_341frontier t6_341all
theorem t6_342choices : plan7219.choices=[1,4,6,7,7,7].map (options 6 5) := by rfl


theorem t6_342part0 : t6_342jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_342frontier : t6_342root.frontier 0=t6_342jobs := by rfl
theorem t6_342all : t6_342jobs.all (Job.check tree)=true := by
  simp only [t6_342jobs,List.all_append,List.all_nil,t6_342part0,Bool.and_self]
theorem t6_342checked : Checked tree [1,4,6,7,7,7] := by
  refine ⟨plan7219,valid7219,t6_342choices,?_⟩
  exact check_of_frontier tree 0 t6_342root t6_342jobs t6_342frontier t6_342all
theorem t6_343choices : plan7220.choices=[1,4,6,10,7,7].map (options 6 5) := by rfl


theorem t6_343part0 : t6_343jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_343frontier : t6_343root.frontier 0=t6_343jobs := by rfl
theorem t6_343all : t6_343jobs.all (Job.check tree)=true := by
  simp only [t6_343jobs,List.all_append,List.all_nil,t6_343part0,Bool.and_self]
theorem t6_343checked : Checked tree [1,4,6,10,7,7] := by
  refine ⟨plan7220,valid7220,t6_343choices,?_⟩
  exact check_of_frontier tree 0 t6_343root t6_343jobs t6_343frontier t6_343all
theorem t6_344choices : plan7221.choices=[1,4,6,10,10,7].map (options 6 5) := by rfl


theorem t6_344part0 : t6_344jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_344frontier : t6_344root.frontier 0=t6_344jobs := by rfl
theorem t6_344all : t6_344jobs.all (Job.check tree)=true := by
  simp only [t6_344jobs,List.all_append,List.all_nil,t6_344part0,Bool.and_self]
theorem t6_344checked : Checked tree [1,4,6,10,10,7] := by
  refine ⟨plan7221,valid7221,t6_344choices,?_⟩
  exact check_of_frontier tree 0 t6_344root t6_344jobs t6_344frontier t6_344all
theorem t6_345choices : plan7222.choices=[1,4,7,7,7,7].map (options 6 5) := by rfl


theorem t6_345part0 : t6_345jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_345frontier : t6_345root.frontier 0=t6_345jobs := by rfl
theorem t6_345all : t6_345jobs.all (Job.check tree)=true := by
  simp only [t6_345jobs,List.all_append,List.all_nil,t6_345part0,Bool.and_self]
theorem t6_345checked : Checked tree [1,4,7,7,7,7] := by
  refine ⟨plan7222,valid7222,t6_345choices,?_⟩
  exact check_of_frontier tree 0 t6_345root t6_345jobs t6_345frontier t6_345all
theorem t6_346choices : plan7223.choices=[1,4,8,7,7,7].map (options 6 5) := by rfl


theorem t6_346part0 : t6_346jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_346frontier : t6_346root.frontier 0=t6_346jobs := by rfl
theorem t6_346all : t6_346jobs.all (Job.check tree)=true := by
  simp only [t6_346jobs,List.all_append,List.all_nil,t6_346part0,Bool.and_self]
theorem t6_346checked : Checked tree [1,4,8,7,7,7] := by
  refine ⟨plan7223,valid7223,t6_346choices,?_⟩
  exact check_of_frontier tree 0 t6_346root t6_346jobs t6_346frontier t6_346all
theorem t6_347choices : plan6829.choices=[1,4,9,3,7,7].map (options 6 4) := by rfl


theorem t6_347part0 : t6_347jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_347frontier : t6_347root.frontier 0=t6_347jobs := by rfl
theorem t6_347all : t6_347jobs.all (Job.check tree)=true := by
  simp only [t6_347jobs,List.all_append,List.all_nil,t6_347part0,Bool.and_self]
theorem t6_347checked : Checked tree [1,4,9,3,7,7] := by
  refine ⟨plan6829,valid6829,t6_347choices,?_⟩
  exact check_of_frontier tree 0 t6_347root t6_347jobs t6_347frontier t6_347all
theorem t6_348choices : plan7224.choices=[1,4,9,6,7,7].map (options 6 5) := by rfl


theorem t6_348part0 : t6_348jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_348frontier : t6_348root.frontier 0=t6_348jobs := by rfl
theorem t6_348all : t6_348jobs.all (Job.check tree)=true := by
  simp only [t6_348jobs,List.all_append,List.all_nil,t6_348part0,Bool.and_self]
theorem t6_348checked : Checked tree [1,4,9,6,7,7] := by
  refine ⟨plan7224,valid7224,t6_348choices,?_⟩
  exact check_of_frontier tree 0 t6_348root t6_348jobs t6_348frontier t6_348all
theorem t6_349choices : plan7225.choices=[1,4,9,7,7,7].map (options 6 5) := by rfl


theorem t6_349part0 : t6_349jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_349frontier : t6_349root.frontier 0=t6_349jobs := by rfl
theorem t6_349all : t6_349jobs.all (Job.check tree)=true := by
  simp only [t6_349jobs,List.all_append,List.all_nil,t6_349part0,Bool.and_self]
theorem t6_349checked : Checked tree [1,4,9,7,7,7] := by
  refine ⟨plan7225,valid7225,t6_349choices,?_⟩
  exact check_of_frontier tree 0 t6_349root t6_349jobs t6_349frontier t6_349all
theorem t6_350choices : plan7226.choices=[1,4,9,10,7,7].map (options 6 5) := by rfl


theorem t6_350part0 : t6_350jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_350frontier : t6_350root.frontier 0=t6_350jobs := by rfl
theorem t6_350all : t6_350jobs.all (Job.check tree)=true := by
  simp only [t6_350jobs,List.all_append,List.all_nil,t6_350part0,Bool.and_self]
theorem t6_350checked : Checked tree [1,4,9,10,7,7] := by
  refine ⟨plan7226,valid7226,t6_350choices,?_⟩
  exact check_of_frontier tree 0 t6_350root t6_350jobs t6_350frontier t6_350all
theorem t6_351choices : plan7227.choices=[1,4,10,7,7,7].map (options 6 5) := by rfl


theorem t6_351part0 : t6_351jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_351frontier : t6_351root.frontier 0=t6_351jobs := by rfl
theorem t6_351all : t6_351jobs.all (Job.check tree)=true := by
  simp only [t6_351jobs,List.all_append,List.all_nil,t6_351part0,Bool.and_self]
theorem t6_351checked : Checked tree [1,4,10,7,7,7] := by
  refine ⟨plan7227,valid7227,t6_351choices,?_⟩
  exact check_of_frontier tree 0 t6_351root t6_351jobs t6_351frontier t6_351all
theorem t6_352choices : plan7228.choices=[1,4,10,10,7,7].map (options 6 5) := by rfl


theorem t6_352part0 : t6_352jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_352frontier : t6_352root.frontier 0=t6_352jobs := by rfl
theorem t6_352all : t6_352jobs.all (Job.check tree)=true := by
  simp only [t6_352jobs,List.all_append,List.all_nil,t6_352part0,Bool.and_self]
theorem t6_352checked : Checked tree [1,4,10,10,7,7] := by
  refine ⟨plan7228,valid7228,t6_352choices,?_⟩
  exact check_of_frontier tree 0 t6_352root t6_352jobs t6_352frontier t6_352all
theorem t6_353choices : plan7229.choices=[1,4,10,10,10,7].map (options 6 5) := by rfl


theorem t6_353part0 : t6_353jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_353frontier : t6_353root.frontier 0=t6_353jobs := by rfl
theorem t6_353all : t6_353jobs.all (Job.check tree)=true := by
  simp only [t6_353jobs,List.all_append,List.all_nil,t6_353part0,Bool.and_self]
theorem t6_353checked : Checked tree [1,4,10,10,10,7] := by
  refine ⟨plan7229,valid7229,t6_353choices,?_⟩
  exact check_of_frontier tree 0 t6_353root t6_353jobs t6_353frontier t6_353all
theorem t6_354choices : plan6295.choices=[1,5,3,3,3,3].map (options 6 1) := by rfl


theorem t6_354part0 : t6_354jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_354frontier : t6_354root.frontier 0=t6_354jobs := by rfl
theorem t6_354all : t6_354jobs.all (Job.check tree)=true := by
  simp only [t6_354jobs,List.all_append,List.all_nil,t6_354part0,Bool.and_self]
theorem t6_354checked : Checked tree [1,5,3,3,3,3] := by
  refine ⟨plan6295,valid6295,t6_354choices,?_⟩
  exact check_of_frontier tree 0 t6_354root t6_354jobs t6_354frontier t6_354all
theorem t6_355choices : plan6356.choices=[1,5,3,3,3,6].map (options 6 2) := by rfl


theorem t6_355part0 : t6_355jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_355frontier : t6_355root.frontier 0=t6_355jobs := by rfl
theorem t6_355all : t6_355jobs.all (Job.check tree)=true := by
  simp only [t6_355jobs,List.all_append,List.all_nil,t6_355part0,Bool.and_self]
theorem t6_355checked : Checked tree [1,5,3,3,3,6] := by
  refine ⟨plan6356,valid6356,t6_355choices,?_⟩
  exact check_of_frontier tree 0 t6_355root t6_355jobs t6_355frontier t6_355all
theorem t6_356choices : plan6357.choices=[1,5,3,3,3,7].map (options 6 2) := by rfl


theorem t6_356part0 : t6_356jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_356frontier : t6_356root.frontier 0=t6_356jobs := by rfl
theorem t6_356all : t6_356jobs.all (Job.check tree)=true := by
  simp only [t6_356jobs,List.all_append,List.all_nil,t6_356part0,Bool.and_self]
theorem t6_356checked : Checked tree [1,5,3,3,3,7] := by
  refine ⟨plan6357,valid6357,t6_356choices,?_⟩
  exact check_of_frontier tree 0 t6_356root t6_356jobs t6_356frontier t6_356all
theorem t6_357choices : plan6358.choices=[1,5,3,3,3,10].map (options 6 2) := by rfl


theorem t6_357part0 : t6_357jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_357frontier : t6_357root.frontier 0=t6_357jobs := by rfl
theorem t6_357all : t6_357jobs.all (Job.check tree)=true := by
  simp only [t6_357jobs,List.all_append,List.all_nil,t6_357part0,Bool.and_self]
theorem t6_357checked : Checked tree [1,5,3,3,3,10] := by
  refine ⟨plan6358,valid6358,t6_357choices,?_⟩
  exact check_of_frontier tree 0 t6_357root t6_357jobs t6_357frontier t6_357all
theorem t6_358choices : plan6517.choices=[1,5,3,3,6,6].map (options 6 3) := by rfl


theorem t6_358part0 : t6_358jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_358frontier : t6_358root.frontier 0=t6_358jobs := by rfl
theorem t6_358all : t6_358jobs.all (Job.check tree)=true := by
  simp only [t6_358jobs,List.all_append,List.all_nil,t6_358part0,Bool.and_self]
theorem t6_358checked : Checked tree [1,5,3,3,6,6] := by
  refine ⟨plan6517,valid6517,t6_358choices,?_⟩
  exact check_of_frontier tree 0 t6_358root t6_358jobs t6_358frontier t6_358all
theorem t6_359choices : plan6518.choices=[1,5,3,3,6,7].map (options 6 3) := by rfl


theorem t6_359part0 : t6_359jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_359part1 : t6_359jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_359frontier : t6_359root.frontier 1=t6_359jobs := by rfl
theorem t6_359all : t6_359jobs.all (Job.check tree)=true := by
  simp only [t6_359jobs,List.all_append,List.all_nil,t6_359part0,t6_359part1,Bool.and_self]
theorem t6_359checked : Checked tree [1,5,3,3,6,7] := by
  refine ⟨plan6518,valid6518,t6_359choices,?_⟩
  exact check_of_frontier tree 1 t6_359root t6_359jobs t6_359frontier t6_359all
theorem t6_360choices : plan6519.choices=[1,5,3,3,6,10].map (options 6 3) := by rfl


theorem t6_360part0 : t6_360jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_360frontier : t6_360root.frontier 0=t6_360jobs := by rfl
theorem t6_360all : t6_360jobs.all (Job.check tree)=true := by
  simp only [t6_360jobs,List.all_append,List.all_nil,t6_360part0,Bool.and_self]
theorem t6_360checked : Checked tree [1,5,3,3,6,10] := by
  refine ⟨plan6519,valid6519,t6_360choices,?_⟩
  exact check_of_frontier tree 0 t6_360root t6_360jobs t6_360frontier t6_360all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks056 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_327checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_328checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_329checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_330checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_331checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_332checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_333checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_334checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_335checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_336checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_337checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_338checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_339checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_340checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_341checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_342checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_343checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_344checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_345checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_346checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_347checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_348checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_349checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_350checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_351checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_352checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_353checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_317checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_354checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_355checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_356checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_357checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_358checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_359checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_360checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_318checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_319checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_320checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_321checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_322checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_323checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_324checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_325checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_326checked⟩
