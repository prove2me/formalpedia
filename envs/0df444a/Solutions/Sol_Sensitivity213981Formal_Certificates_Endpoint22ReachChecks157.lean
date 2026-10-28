-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks157
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:20:33.093015+00:00
-- url     : https://prove2.me/submissions/2e11d182-6f42-47e9-9ad4-114a285152c4

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks157
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks157
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans086
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans091
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































































































theorem valid144 : plan144.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid147 : plan147.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid150 : plan150.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid153 : plan153.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid156 : plan156.Valid := valid_step _ _ _ valid0 (by decide +kernel)








































































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





































theorem valid595 : plan595.Valid := valid_step _ _ _ valid144 (by decide +kernel)











theorem valid601 : plan601.Valid := valid_step _ _ _ valid147 (by decide +kernel)











theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)











theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)











theorem valid619 : plan619.Valid := valid_step _ _ _ valid156 (by decide +kernel)










































































































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















theorem valid1640 : plan1640.Valid := valid_step _ _ _ valid601 (by decide +kernel)





theorem valid1643 : plan1643.Valid := valid_step _ _ _ valid601 (by decide +kernel)

theorem valid1644 : plan1644.Valid := valid_step _ _ _ valid601 (by decide +kernel)













theorem valid1651 : plan1651.Valid := valid_step _ _ _ valid607 (by decide +kernel)





theorem valid1654 : plan1654.Valid := valid_step _ _ _ valid607 (by decide +kernel)



















theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)











theorem valid1671 : plan1671.Valid := valid_step _ _ _ valid619 (by decide +kernel)





theorem valid1674 : plan1674.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1675 : plan1675.Valid := valid_step _ _ _ valid619 (by decide +kernel)










































































































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





























































































































































































theorem valid1631 : plan1631.Valid := valid_step _ _ _ valid595 (by decide +kernel)


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

























theorem valid3565 : plan3565.Valid := valid_step _ _ _ valid1631 (by decide +kernel)

















theorem valid3574 : plan3574.Valid := valid_step _ _ _ valid1640 (by decide +kernel)





theorem valid3577 : plan3577.Valid := valid_step _ _ _ valid1643 (by decide +kernel)

theorem valid3578 : plan3578.Valid := valid_step _ _ _ valid1644 (by decide +kernel)













theorem valid3585 : plan3585.Valid := valid_step _ _ _ valid1654 (by decide +kernel)











theorem valid3591 : plan3591.Valid := valid_step _ _ _ valid1651 (by decide +kernel)





theorem valid3594 : plan3594.Valid := valid_step _ _ _ valid1654 (by decide +kernel)







theorem valid3598 : plan3598.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

theorem valid3599 : plan3599.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

























theorem valid3612 : plan3612.Valid := valid_step _ _ _ valid1664 (by decide +kernel)







theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3617 : plan3617.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3618 : plan3618.Valid := valid_step _ _ _ valid1665 (by decide +kernel)













theorem valid3625 : plan3625.Valid := valid_step _ _ _ valid1671 (by decide +kernel)





theorem valid3628 : plan3628.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3629 : plan3629.Valid := valid_step _ _ _ valid1675 (by decide +kernel)





theorem valid3632 : plan3632.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3633 : plan3633.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3634 : plan3634.Valid := valid_step _ _ _ valid1675 (by decide +kernel)




























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

































































































































theorem valid6113 : plan6113.Valid := valid_step _ _ _ valid3565 (by decide +kernel)





theorem valid6116 : plan6116.Valid := valid_step _ _ _ valid3577 (by decide +kernel)













theorem valid6123 : plan6123.Valid := valid_step _ _ _ valid3574 (by decide +kernel)





theorem valid6126 : plan6126.Valid := valid_step _ _ _ valid3577 (by decide +kernel)

theorem valid6127 : plan6127.Valid := valid_step _ _ _ valid3578 (by decide +kernel)





theorem valid6130 : plan6130.Valid := valid_step _ _ _ valid3594 (by decide +kernel)

theorem valid6131 : plan6131.Valid := valid_step _ _ _ valid3598 (by decide +kernel)

theorem valid6132 : plan6132.Valid := valid_step _ _ _ valid3599 (by decide +kernel)









theorem valid6137 : plan6137.Valid := valid_step _ _ _ valid3585 (by decide +kernel)











theorem valid6143 : plan6143.Valid := valid_step _ _ _ valid3591 (by decide +kernel)


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







































theorem valid6164 : plan6164.Valid := valid_step _ _ _ valid3612 (by decide +kernel)





theorem valid6167 : plan6167.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6168 : plan6168.Valid := valid_step _ _ _ valid3617 (by decide +kernel)

























































theorem valid6197 : plan6197.Valid := valid_step _ _ _ valid3618 (by decide +kernel)





















theorem valid6208 : plan6208.Valid := valid_step _ _ _ valid3632 (by decide +kernel)









theorem valid6213 : plan6213.Valid := valid_step _ _ _ valid3625 (by decide +kernel)





theorem valid6216 : plan6216.Valid := valid_step _ _ _ valid3628 (by decide +kernel)

theorem valid6217 : plan6217.Valid := valid_step _ _ _ valid3629 (by decide +kernel)





theorem valid6220 : plan6220.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6221 : plan6221.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6222 : plan6222.Valid := valid_step _ _ _ valid3634 (by decide +kernel)





theorem valid6225 : plan6225.Valid := valid_step _ _ _ valid3632 (by decide +kernel)





theorem valid6228 : plan6228.Valid := valid_step _ _ _ valid3632 (by decide +kernel)



theorem valid6230 : plan6230.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6231 : plan6231.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6232 : plan6232.Valid := valid_step _ _ _ valid3634 (by decide +kernel)
















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























theorem valid8076 : plan8076.Valid := valid_step _ _ _ valid6113 (by decide +kernel)















theorem valid8084 : plan8084.Valid := valid_step _ _ _ valid6116 (by decide +kernel)

theorem valid8085 : plan8085.Valid := valid_step _ _ _ valid6123 (by decide +kernel)

theorem valid8086 : plan8086.Valid := valid_step _ _ _ valid6126 (by decide +kernel)

theorem valid8087 : plan8087.Valid := valid_step _ _ _ valid6127 (by decide +kernel)

































theorem valid8104 : plan8104.Valid := valid_step _ _ _ valid6130 (by decide +kernel)

theorem valid8105 : plan8105.Valid := valid_step _ _ _ valid6131 (by decide +kernel)

theorem valid8106 : plan8106.Valid := valid_step _ _ _ valid6132 (by decide +kernel)



theorem valid8108 : plan8108.Valid := valid_step _ _ _ valid6143 (by decide +kernel)





























































theorem valid8139 : plan8139.Valid := valid_step _ _ _ valid6137 (by decide +kernel)







theorem valid8143 : plan8143.Valid := valid_step _ _ _ valid6137 (by decide +kernel)


































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



































































































































theorem valid8418 : plan8418.Valid := valid_step _ _ _ valid8076 (by decide +kernel)

































theorem valid8435 : plan8435.Valid := valid_step _ _ _ valid8084 (by decide +kernel)

theorem valid8436 : plan8436.Valid := valid_step _ _ _ valid8085 (by decide +kernel)

theorem valid8437 : plan8437.Valid := valid_step _ _ _ valid8086 (by decide +kernel)

theorem valid8438 : plan8438.Valid := valid_step _ _ _ valid8087 (by decide +kernel)




















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































































theorem valid8480 : plan8480.Valid := valid_step _ _ _ valid8139 (by decide +kernel)

theorem valid8481 : plan8481.Valid := valid_step _ _ _ valid8143 (by decide +kernel)

theorem valid8482 : plan8482.Valid := valid_step _ _ _ valid8104 (by decide +kernel)

theorem valid8483 : plan8483.Valid := valid_step _ _ _ valid8105 (by decide +kernel)

theorem valid8484 : plan8484.Valid := valid_step _ _ _ valid8106 (by decide +kernel)

theorem valid8485 : plan8485.Valid := valid_step _ _ _ valid8108 (by decide +kernel)






















































































































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







































































theorem valid8196 : plan8196.Valid := valid_step _ _ _ valid6197 (by decide +kernel)





theorem valid8199 : plan8199.Valid := valid_step _ _ _ valid6167 (by decide +kernel)









theorem valid8204 : plan8204.Valid := valid_step _ _ _ valid6164 (by decide +kernel)



theorem valid8206 : plan8206.Valid := valid_step _ _ _ valid6167 (by decide +kernel)

theorem valid8207 : plan8207.Valid := valid_step _ _ _ valid6168 (by decide +kernel)







theorem valid8211 : plan8211.Valid := valid_step _ _ _ valid6167 (by decide +kernel)









theorem valid8216 : plan8216.Valid := valid_step _ _ _ valid6164 (by decide +kernel)



theorem valid8218 : plan8218.Valid := valid_step _ _ _ valid6167 (by decide +kernel)

theorem valid8219 : plan8219.Valid := valid_step _ _ _ valid6168 (by decide +kernel)





















































theorem valid8246 : plan8246.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8247 : plan8247.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8248 : plan8248.Valid := valid_step _ _ _ valid6230 (by decide +kernel)
















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





































































theorem valid8579 : plan8579.Valid := valid_step _ _ _ valid8196 (by decide +kernel)

theorem valid8580 : plan8580.Valid := valid_step _ _ _ valid8199 (by decide +kernel)

theorem valid8581 : plan8581.Valid := valid_step _ _ _ valid8204 (by decide +kernel)

theorem valid8582 : plan8582.Valid := valid_step _ _ _ valid8206 (by decide +kernel)

theorem valid8583 : plan8583.Valid := valid_step _ _ _ valid8207 (by decide +kernel)

theorem valid8584 : plan8584.Valid := valid_step _ _ _ valid8211 (by decide +kernel)

theorem valid8585 : plan8585.Valid := valid_step _ _ _ valid8216 (by decide +kernel)

theorem valid8586 : plan8586.Valid := valid_step _ _ _ valid8218 (by decide +kernel)

theorem valid8587 : plan8587.Valid := valid_step _ _ _ valid8219 (by decide +kernel)










































































































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

theorem valid8257 : plan8257.Valid := valid_step _ _ _ valid6208 (by decide +kernel)





theorem valid8260 : plan8260.Valid := valid_step _ _ _ valid6216 (by decide +kernel)



theorem valid8262 : plan8262.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8263 : plan8263.Valid := valid_step _ _ _ valid6221 (by decide +kernel)



theorem valid8265 : plan8265.Valid := valid_step _ _ _ valid6225 (by decide +kernel)





theorem valid8268 : plan8268.Valid := valid_step _ _ _ valid6228 (by decide +kernel)



theorem valid8270 : plan8270.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8271 : plan8271.Valid := valid_step _ _ _ valid6231 (by decide +kernel)









theorem valid8276 : plan8276.Valid := valid_step _ _ _ valid6213 (by decide +kernel)





theorem valid8279 : plan8279.Valid := valid_step _ _ _ valid6216 (by decide +kernel)

theorem valid8280 : plan8280.Valid := valid_step _ _ _ valid6217 (by decide +kernel)





theorem valid8283 : plan8283.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8284 : plan8284.Valid := valid_step _ _ _ valid6221 (by decide +kernel)

theorem valid8285 : plan8285.Valid := valid_step _ _ _ valid6222 (by decide +kernel)





theorem valid8288 : plan8288.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8289 : plan8289.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8290 : plan8290.Valid := valid_step _ _ _ valid6231 (by decide +kernel)

theorem valid8291 : plan8291.Valid := valid_step _ _ _ valid6232 (by decide +kernel)





theorem valid8294 : plan8294.Valid := valid_step _ _ _ valid6225 (by decide +kernel)



theorem valid8296 : plan8296.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8297 : plan8297.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8298 : plan8298.Valid := valid_step _ _ _ valid6230 (by decide +kernel)















theorem valid8306 : plan8306.Valid := valid_step _ _ _ valid6216 (by decide +kernel)



theorem valid8308 : plan8308.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8309 : plan8309.Valid := valid_step _ _ _ valid6221 (by decide +kernel)



theorem valid8311 : plan8311.Valid := valid_step _ _ _ valid6225 (by decide +kernel)





theorem valid8314 : plan8314.Valid := valid_step _ _ _ valid6228 (by decide +kernel)



theorem valid8316 : plan8316.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8317 : plan8317.Valid := valid_step _ _ _ valid6231 (by decide +kernel)



theorem valid8319 : plan8319.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8320 : plan8320.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8321 : plan8321.Valid := valid_step _ _ _ valid6231 (by decide +kernel)

theorem valid8322 : plan8322.Valid := valid_step _ _ _ valid6232 (by decide +kernel)




























































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











































































































































































theorem valid8726 : plan8726.Valid := valid_step _ _ _ valid8246 (by decide +kernel)

theorem valid8727 : plan8727.Valid := valid_step _ _ _ valid8247 (by decide +kernel)

theorem valid8728 : plan8728.Valid := valid_step _ _ _ valid8248 (by decide +kernel)

theorem valid8729 : plan8729.Valid := valid_step _ _ _ valid8257 (by decide +kernel)

theorem valid8730 : plan8730.Valid := valid_step _ _ _ valid8260 (by decide +kernel)

theorem valid8731 : plan8731.Valid := valid_step _ _ _ valid8262 (by decide +kernel)

theorem valid8732 : plan8732.Valid := valid_step _ _ _ valid8263 (by decide +kernel)

theorem valid8733 : plan8733.Valid := valid_step _ _ _ valid8265 (by decide +kernel)

theorem valid8734 : plan8734.Valid := valid_step _ _ _ valid8268 (by decide +kernel)

theorem valid8735 : plan8735.Valid := valid_step _ _ _ valid8270 (by decide +kernel)

theorem valid8736 : plan8736.Valid := valid_step _ _ _ valid8271 (by decide +kernel)
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

theorem valid8737 : plan8737.Valid := valid_step _ _ _ valid8276 (by decide +kernel)

theorem valid8738 : plan8738.Valid := valid_step _ _ _ valid8279 (by decide +kernel)

theorem valid8739 : plan8739.Valid := valid_step _ _ _ valid8280 (by decide +kernel)

theorem valid8740 : plan8740.Valid := valid_step _ _ _ valid8283 (by decide +kernel)

theorem valid8741 : plan8741.Valid := valid_step _ _ _ valid8284 (by decide +kernel)

theorem valid8742 : plan8742.Valid := valid_step _ _ _ valid8285 (by decide +kernel)

theorem valid8743 : plan8743.Valid := valid_step _ _ _ valid8288 (by decide +kernel)

theorem valid8744 : plan8744.Valid := valid_step _ _ _ valid8289 (by decide +kernel)

theorem valid8745 : plan8745.Valid := valid_step _ _ _ valid8290 (by decide +kernel)

theorem valid8746 : plan8746.Valid := valid_step _ _ _ valid8291 (by decide +kernel)

theorem valid8747 : plan8747.Valid := valid_step _ _ _ valid8294 (by decide +kernel)

theorem valid8748 : plan8748.Valid := valid_step _ _ _ valid8296 (by decide +kernel)

theorem valid8749 : plan8749.Valid := valid_step _ _ _ valid8297 (by decide +kernel)

theorem valid8750 : plan8750.Valid := valid_step _ _ _ valid8298 (by decide +kernel)

theorem valid8751 : plan8751.Valid := valid_step _ _ _ valid8306 (by decide +kernel)

theorem valid8752 : plan8752.Valid := valid_step _ _ _ valid8308 (by decide +kernel)

theorem valid8753 : plan8753.Valid := valid_step _ _ _ valid8309 (by decide +kernel)

theorem valid8754 : plan8754.Valid := valid_step _ _ _ valid8311 (by decide +kernel)

theorem valid8755 : plan8755.Valid := valid_step _ _ _ valid8314 (by decide +kernel)

theorem valid8756 : plan8756.Valid := valid_step _ _ _ valid8316 (by decide +kernel)

theorem valid8757 : plan8757.Valid := valid_step _ _ _ valid8317 (by decide +kernel)

theorem valid8758 : plan8758.Valid := valid_step _ _ _ valid8319 (by decide +kernel)

theorem valid8759 : plan8759.Valid := valid_step _ _ _ valid8320 (by decide +kernel)

theorem valid8760 : plan8760.Valid := valid_step _ _ _ valid8321 (by decide +kernel)

theorem valid8761 : plan8761.Valid := valid_step _ _ _ valid8322 (by decide +kernel)














































































































































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
theorem t7_71choices : plan8579.choices=[1,3,10,10,10,7,7].map (options 7 5) := by rfl


theorem t7_71part0 : t7_71jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_71frontier : t7_71root.frontier 0=t7_71jobs := by rfl
theorem t7_71all : t7_71jobs.all (Job.check tree)=true := by
  simp only [t7_71jobs,List.all_append,List.all_nil,t7_71part0,Bool.and_self]
theorem t7_71checked : Checked tree [1,3,10,10,10,7,7] := by
  refine ⟨plan8579,valid8579,t7_71choices,?_⟩
  exact check_of_frontier tree 0 t7_71root t7_71jobs t7_71frontier t7_71all
theorem t7_72choices : plan8580.choices=[1,4,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_72part0 : t7_72jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_72frontier : t7_72root.frontier 0=t7_72jobs := by rfl
theorem t7_72all : t7_72jobs.all (Job.check tree)=true := by
  simp only [t7_72jobs,List.all_append,List.all_nil,t7_72part0,Bool.and_self]
theorem t7_72checked : Checked tree [1,4,3,7,7,7,7] := by
  refine ⟨plan8580,valid8580,t7_72choices,?_⟩
  exact check_of_frontier tree 0 t7_72root t7_72jobs t7_72frontier t7_72all
theorem t7_73choices : plan8726.choices=[1,4,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_73part0 : t7_73jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_73frontier : t7_73root.frontier 0=t7_73jobs := by rfl
theorem t7_73all : t7_73jobs.all (Job.check tree)=true := by
  simp only [t7_73jobs,List.all_append,List.all_nil,t7_73part0,Bool.and_self]
theorem t7_73checked : Checked tree [1,4,6,7,7,7,7] := by
  refine ⟨plan8726,valid8726,t7_73choices,?_⟩
  exact check_of_frontier tree 0 t7_73root t7_73jobs t7_73frontier t7_73all
theorem t7_74choices : plan8727.choices=[1,4,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_74part0 : t7_74jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_74frontier : t7_74root.frontier 0=t7_74jobs := by rfl
theorem t7_74all : t7_74jobs.all (Job.check tree)=true := by
  simp only [t7_74jobs,List.all_append,List.all_nil,t7_74part0,Bool.and_self]
theorem t7_74checked : Checked tree [1,4,7,7,7,7,7] := by
  refine ⟨plan8727,valid8727,t7_74choices,?_⟩
  exact check_of_frontier tree 0 t7_74root t7_74jobs t7_74frontier t7_74all
theorem t7_75choices : plan8728.choices=[1,4,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_75part0 : t7_75jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_75frontier : t7_75root.frontier 0=t7_75jobs := by rfl
theorem t7_75all : t7_75jobs.all (Job.check tree)=true := by
  simp only [t7_75jobs,List.all_append,List.all_nil,t7_75part0,Bool.and_self]
theorem t7_75checked : Checked tree [1,4,10,7,7,7,7] := by
  refine ⟨plan8728,valid8728,t7_75choices,?_⟩
  exact check_of_frontier tree 0 t7_75root t7_75jobs t7_75frontier t7_75all
theorem t7_76choices : plan8480.choices=[1,5,3,3,7,7,7].map (options 7 4) := by rfl


theorem t7_76part0 : t7_76jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_76frontier : t7_76root.frontier 0=t7_76jobs := by rfl
theorem t7_76all : t7_76jobs.all (Job.check tree)=true := by
  simp only [t7_76jobs,List.all_append,List.all_nil,t7_76part0,Bool.and_self]
theorem t7_76checked : Checked tree [1,5,3,3,7,7,7] := by
  refine ⟨plan8480,valid8480,t7_76choices,?_⟩
  exact check_of_frontier tree 0 t7_76root t7_76jobs t7_76frontier t7_76all
theorem t7_77choices : plan8581.choices=[1,5,3,6,7,7,7].map (options 7 5) := by rfl


theorem t7_77part0 : t7_77jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_77frontier : t7_77root.frontier 0=t7_77jobs := by rfl
theorem t7_77all : t7_77jobs.all (Job.check tree)=true := by
  simp only [t7_77jobs,List.all_append,List.all_nil,t7_77part0,Bool.and_self]
theorem t7_77checked : Checked tree [1,5,3,6,7,7,7] := by
  refine ⟨plan8581,valid8581,t7_77choices,?_⟩
  exact check_of_frontier tree 0 t7_77root t7_77jobs t7_77frontier t7_77all
theorem t7_78choices : plan8582.choices=[1,5,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_78part0 : t7_78jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_78frontier : t7_78root.frontier 0=t7_78jobs := by rfl
theorem t7_78all : t7_78jobs.all (Job.check tree)=true := by
  simp only [t7_78jobs,List.all_append,List.all_nil,t7_78part0,Bool.and_self]
theorem t7_78checked : Checked tree [1,5,3,7,7,7,7] := by
  refine ⟨plan8582,valid8582,t7_78choices,?_⟩
  exact check_of_frontier tree 0 t7_78root t7_78jobs t7_78frontier t7_78all
theorem t7_79choices : plan8583.choices=[1,5,3,10,7,7,7].map (options 7 5) := by rfl


theorem t7_79part0 : t7_79jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_79frontier : t7_79root.frontier 0=t7_79jobs := by rfl
theorem t7_79all : t7_79jobs.all (Job.check tree)=true := by
  simp only [t7_79jobs,List.all_append,List.all_nil,t7_79part0,Bool.and_self]
theorem t7_79checked : Checked tree [1,5,3,10,7,7,7] := by
  refine ⟨plan8583,valid8583,t7_79choices,?_⟩
  exact check_of_frontier tree 0 t7_79root t7_79jobs t7_79frontier t7_79all
theorem t7_80choices : plan8729.choices=[1,5,5,7,7,7,7].map (options 7 6) := by rfl


theorem t7_80part0 : t7_80jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_80frontier : t7_80root.frontier 0=t7_80jobs := by rfl
theorem t7_80all : t7_80jobs.all (Job.check tree)=true := by
  simp only [t7_80jobs,List.all_append,List.all_nil,t7_80part0,Bool.and_self]
theorem t7_80checked : Checked tree [1,5,5,7,7,7,7] := by
  refine ⟨plan8729,valid8729,t7_80choices,?_⟩
  exact check_of_frontier tree 0 t7_80root t7_80jobs t7_80frontier t7_80all
theorem t7_81choices : plan8730.choices=[1,5,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_81part0 : t7_81jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_81frontier : t7_81root.frontier 0=t7_81jobs := by rfl
theorem t7_81all : t7_81jobs.all (Job.check tree)=true := by
  simp only [t7_81jobs,List.all_append,List.all_nil,t7_81part0,Bool.and_self]
theorem t7_81checked : Checked tree [1,5,6,6,7,7,7] := by
  refine ⟨plan8730,valid8730,t7_81choices,?_⟩
  exact check_of_frontier tree 0 t7_81root t7_81jobs t7_81frontier t7_81all
theorem t7_82choices : plan8731.choices=[1,5,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_82part0 : t7_82jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_82frontier : t7_82root.frontier 0=t7_82jobs := by rfl
theorem t7_82all : t7_82jobs.all (Job.check tree)=true := by
  simp only [t7_82jobs,List.all_append,List.all_nil,t7_82part0,Bool.and_self]
theorem t7_82checked : Checked tree [1,5,6,7,7,7,7] := by
  refine ⟨plan8731,valid8731,t7_82choices,?_⟩
  exact check_of_frontier tree 0 t7_82root t7_82jobs t7_82frontier t7_82all
theorem t7_83choices : plan8732.choices=[1,5,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_83part0 : t7_83jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_83frontier : t7_83root.frontier 0=t7_83jobs := by rfl
theorem t7_83all : t7_83jobs.all (Job.check tree)=true := by
  simp only [t7_83jobs,List.all_append,List.all_nil,t7_83part0,Bool.and_self]
theorem t7_83checked : Checked tree [1,5,6,10,7,7,7] := by
  refine ⟨plan8732,valid8732,t7_83choices,?_⟩
  exact check_of_frontier tree 0 t7_83root t7_83jobs t7_83frontier t7_83all
theorem t7_84choices : plan8733.choices=[1,5,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_84part0 : t7_84jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_84frontier : t7_84root.frontier 0=t7_84jobs := by rfl
theorem t7_84all : t7_84jobs.all (Job.check tree)=true := by
  simp only [t7_84jobs,List.all_append,List.all_nil,t7_84part0,Bool.and_self]
theorem t7_84checked : Checked tree [1,5,7,7,7,7,7] := by
  refine ⟨plan8733,valid8733,t7_84choices,?_⟩
  exact check_of_frontier tree 0 t7_84root t7_84jobs t7_84frontier t7_84all
theorem t7_85choices : plan8734.choices=[1,5,9,7,7,7,7].map (options 7 6) := by rfl


theorem t7_85part0 : t7_85jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_85frontier : t7_85root.frontier 0=t7_85jobs := by rfl
theorem t7_85all : t7_85jobs.all (Job.check tree)=true := by
  simp only [t7_85jobs,List.all_append,List.all_nil,t7_85part0,Bool.and_self]
theorem t7_85checked : Checked tree [1,5,9,7,7,7,7] := by
  refine ⟨plan8734,valid8734,t7_85choices,?_⟩
  exact check_of_frontier tree 0 t7_85root t7_85jobs t7_85frontier t7_85all
theorem t7_86choices : plan8735.choices=[1,5,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_86part0 : t7_86jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_86frontier : t7_86root.frontier 0=t7_86jobs := by rfl
theorem t7_86all : t7_86jobs.all (Job.check tree)=true := by
  simp only [t7_86jobs,List.all_append,List.all_nil,t7_86part0,Bool.and_self]
theorem t7_86checked : Checked tree [1,5,10,7,7,7,7] := by
  refine ⟨plan8735,valid8735,t7_86choices,?_⟩
  exact check_of_frontier tree 0 t7_86root t7_86jobs t7_86frontier t7_86all
theorem t7_87choices : plan8736.choices=[1,5,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_87part0 : t7_87jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_87frontier : t7_87root.frontier 0=t7_87jobs := by rfl
theorem t7_87all : t7_87jobs.all (Job.check tree)=true := by
  simp only [t7_87jobs,List.all_append,List.all_nil,t7_87part0,Bool.and_self]
theorem t7_87checked : Checked tree [1,5,10,10,7,7,7] := by
  refine ⟨plan8736,valid8736,t7_87choices,?_⟩
  exact check_of_frontier tree 0 t7_87root t7_87jobs t7_87frontier t7_87all
theorem t7_88choices : plan8737.choices=[1,6,6,6,6,7,7].map (options 7 6) := by rfl


theorem t7_88part0 : t7_88jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_88frontier : t7_88root.frontier 0=t7_88jobs := by rfl
theorem t7_88all : t7_88jobs.all (Job.check tree)=true := by
  simp only [t7_88jobs,List.all_append,List.all_nil,t7_88part0,Bool.and_self]
theorem t7_88checked : Checked tree [1,6,6,6,6,7,7] := by
  refine ⟨plan8737,valid8737,t7_88choices,?_⟩
  exact check_of_frontier tree 0 t7_88root t7_88jobs t7_88frontier t7_88all
theorem t7_89choices : plan8738.choices=[1,6,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_89part0 : t7_89jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_89frontier : t7_89root.frontier 0=t7_89jobs := by rfl
theorem t7_89all : t7_89jobs.all (Job.check tree)=true := by
  simp only [t7_89jobs,List.all_append,List.all_nil,t7_89part0,Bool.and_self]
theorem t7_89checked : Checked tree [1,6,6,6,7,7,7] := by
  refine ⟨plan8738,valid8738,t7_89choices,?_⟩
  exact check_of_frontier tree 0 t7_89root t7_89jobs t7_89frontier t7_89all
theorem t7_90choices : plan8739.choices=[1,6,6,6,10,7,7].map (options 7 6) := by rfl


theorem t7_90part0 : t7_90jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_90frontier : t7_90root.frontier 0=t7_90jobs := by rfl
theorem t7_90all : t7_90jobs.all (Job.check tree)=true := by
  simp only [t7_90jobs,List.all_append,List.all_nil,t7_90part0,Bool.and_self]
theorem t7_90checked : Checked tree [1,6,6,6,10,7,7] := by
  refine ⟨plan8739,valid8739,t7_90choices,?_⟩
  exact check_of_frontier tree 0 t7_90root t7_90jobs t7_90frontier t7_90all
theorem t7_91choices : plan8740.choices=[1,6,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_91part0 : t7_91jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_91frontier : t7_91root.frontier 0=t7_91jobs := by rfl
theorem t7_91all : t7_91jobs.all (Job.check tree)=true := by
  simp only [t7_91jobs,List.all_append,List.all_nil,t7_91part0,Bool.and_self]
theorem t7_91checked : Checked tree [1,6,6,7,7,7,7] := by
  refine ⟨plan8740,valid8740,t7_91choices,?_⟩
  exact check_of_frontier tree 0 t7_91root t7_91jobs t7_91frontier t7_91all
theorem t7_92choices : plan8741.choices=[1,6,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_92part0 : t7_92jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_92frontier : t7_92root.frontier 0=t7_92jobs := by rfl
theorem t7_92all : t7_92jobs.all (Job.check tree)=true := by
  simp only [t7_92jobs,List.all_append,List.all_nil,t7_92part0,Bool.and_self]
theorem t7_92checked : Checked tree [1,6,6,10,7,7,7] := by
  refine ⟨plan8741,valid8741,t7_92choices,?_⟩
  exact check_of_frontier tree 0 t7_92root t7_92jobs t7_92frontier t7_92all
theorem t7_93choices : plan8742.choices=[1,6,6,10,10,7,7].map (options 7 6) := by rfl


theorem t7_93part0 : t7_93jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_93frontier : t7_93root.frontier 0=t7_93jobs := by rfl
theorem t7_93all : t7_93jobs.all (Job.check tree)=true := by
  simp only [t7_93jobs,List.all_append,List.all_nil,t7_93part0,Bool.and_self]
theorem t7_93checked : Checked tree [1,6,6,10,10,7,7] := by
  refine ⟨plan8742,valid8742,t7_93choices,?_⟩
  exact check_of_frontier tree 0 t7_93root t7_93jobs t7_93frontier t7_93all
theorem t7_94choices : plan8743.choices=[1,6,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_94part0 : t7_94jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_94frontier : t7_94root.frontier 0=t7_94jobs := by rfl
theorem t7_94all : t7_94jobs.all (Job.check tree)=true := by
  simp only [t7_94jobs,List.all_append,List.all_nil,t7_94part0,Bool.and_self]
theorem t7_94checked : Checked tree [1,6,7,7,7,7,7] := by
  refine ⟨plan8743,valid8743,t7_94choices,?_⟩
  exact check_of_frontier tree 0 t7_94root t7_94jobs t7_94frontier t7_94all
theorem t7_95choices : plan8744.choices=[1,6,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_95part0 : t7_95jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_95frontier : t7_95root.frontier 0=t7_95jobs := by rfl
theorem t7_95all : t7_95jobs.all (Job.check tree)=true := by
  simp only [t7_95jobs,List.all_append,List.all_nil,t7_95part0,Bool.and_self]
theorem t7_95checked : Checked tree [1,6,10,7,7,7,7] := by
  refine ⟨plan8744,valid8744,t7_95choices,?_⟩
  exact check_of_frontier tree 0 t7_95root t7_95jobs t7_95frontier t7_95all
theorem t7_96choices : plan8745.choices=[1,6,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_96part0 : t7_96jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_96frontier : t7_96root.frontier 0=t7_96jobs := by rfl
theorem t7_96all : t7_96jobs.all (Job.check tree)=true := by
  simp only [t7_96jobs,List.all_append,List.all_nil,t7_96part0,Bool.and_self]
theorem t7_96checked : Checked tree [1,6,10,10,7,7,7] := by
  refine ⟨plan8745,valid8745,t7_96choices,?_⟩
  exact check_of_frontier tree 0 t7_96root t7_96jobs t7_96frontier t7_96all
theorem t7_97choices : plan8746.choices=[1,6,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_97part0 : t7_97jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_97frontier : t7_97root.frontier 0=t7_97jobs := by rfl
theorem t7_97all : t7_97jobs.all (Job.check tree)=true := by
  simp only [t7_97jobs,List.all_append,List.all_nil,t7_97part0,Bool.and_self]
theorem t7_97checked : Checked tree [1,6,10,10,10,7,7] := by
  refine ⟨plan8746,valid8746,t7_97choices,?_⟩
  exact check_of_frontier tree 0 t7_97root t7_97jobs t7_97frontier t7_97all
theorem t7_98choices : plan8747.choices=[1,7,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_98part0 : t7_98jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_98frontier : t7_98root.frontier 0=t7_98jobs := by rfl
theorem t7_98all : t7_98jobs.all (Job.check tree)=true := by
  simp only [t7_98jobs,List.all_append,List.all_nil,t7_98part0,Bool.and_self]
theorem t7_98checked : Checked tree [1,7,7,7,7,7,7] := by
  refine ⟨plan8747,valid8747,t7_98choices,?_⟩
  exact check_of_frontier tree 0 t7_98root t7_98jobs t7_98frontier t7_98all
theorem t7_99choices : plan8584.choices=[1,8,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_99part0 : t7_99jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_99frontier : t7_99root.frontier 0=t7_99jobs := by rfl
theorem t7_99all : t7_99jobs.all (Job.check tree)=true := by
  simp only [t7_99jobs,List.all_append,List.all_nil,t7_99part0,Bool.and_self]
theorem t7_99checked : Checked tree [1,8,3,7,7,7,7] := by
  refine ⟨plan8584,valid8584,t7_99choices,?_⟩
  exact check_of_frontier tree 0 t7_99root t7_99jobs t7_99frontier t7_99all
theorem t7_100choices : plan8748.choices=[1,8,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_100part0 : t7_100jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_100frontier : t7_100root.frontier 0=t7_100jobs := by rfl
theorem t7_100all : t7_100jobs.all (Job.check tree)=true := by
  simp only [t7_100jobs,List.all_append,List.all_nil,t7_100part0,Bool.and_self]
theorem t7_100checked : Checked tree [1,8,6,7,7,7,7] := by
  refine ⟨plan8748,valid8748,t7_100choices,?_⟩
  exact check_of_frontier tree 0 t7_100root t7_100jobs t7_100frontier t7_100all
theorem t7_101choices : plan8749.choices=[1,8,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_101part0 : t7_101jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_101frontier : t7_101root.frontier 0=t7_101jobs := by rfl
theorem t7_101all : t7_101jobs.all (Job.check tree)=true := by
  simp only [t7_101jobs,List.all_append,List.all_nil,t7_101part0,Bool.and_self]
theorem t7_101checked : Checked tree [1,8,7,7,7,7,7] := by
  refine ⟨plan8749,valid8749,t7_101choices,?_⟩
  exact check_of_frontier tree 0 t7_101root t7_101jobs t7_101frontier t7_101all
theorem t7_102choices : plan8750.choices=[1,8,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_102part0 : t7_102jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_102frontier : t7_102root.frontier 0=t7_102jobs := by rfl
theorem t7_102all : t7_102jobs.all (Job.check tree)=true := by
  simp only [t7_102jobs,List.all_append,List.all_nil,t7_102part0,Bool.and_self]
theorem t7_102checked : Checked tree [1,8,10,7,7,7,7] := by
  refine ⟨plan8750,valid8750,t7_102choices,?_⟩
  exact check_of_frontier tree 0 t7_102root t7_102jobs t7_102frontier t7_102all
theorem t7_103choices : plan8481.choices=[1,9,3,3,7,7,7].map (options 7 4) := by rfl


theorem t7_103part0 : t7_103jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_103frontier : t7_103root.frontier 0=t7_103jobs := by rfl
theorem t7_103all : t7_103jobs.all (Job.check tree)=true := by
  simp only [t7_103jobs,List.all_append,List.all_nil,t7_103part0,Bool.and_self]
theorem t7_103checked : Checked tree [1,9,3,3,7,7,7] := by
  refine ⟨plan8481,valid8481,t7_103choices,?_⟩
  exact check_of_frontier tree 0 t7_103root t7_103jobs t7_103frontier t7_103all
theorem t7_104choices : plan8585.choices=[1,9,3,6,7,7,7].map (options 7 5) := by rfl


theorem t7_104part0 : t7_104jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_104frontier : t7_104root.frontier 0=t7_104jobs := by rfl
theorem t7_104all : t7_104jobs.all (Job.check tree)=true := by
  simp only [t7_104jobs,List.all_append,List.all_nil,t7_104part0,Bool.and_self]
theorem t7_104checked : Checked tree [1,9,3,6,7,7,7] := by
  refine ⟨plan8585,valid8585,t7_104choices,?_⟩
  exact check_of_frontier tree 0 t7_104root t7_104jobs t7_104frontier t7_104all
theorem t7_105choices : plan8586.choices=[1,9,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_105part0 : t7_105jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_105frontier : t7_105root.frontier 0=t7_105jobs := by rfl
theorem t7_105all : t7_105jobs.all (Job.check tree)=true := by
  simp only [t7_105jobs,List.all_append,List.all_nil,t7_105part0,Bool.and_self]
theorem t7_105checked : Checked tree [1,9,3,7,7,7,7] := by
  refine ⟨plan8586,valid8586,t7_105choices,?_⟩
  exact check_of_frontier tree 0 t7_105root t7_105jobs t7_105frontier t7_105all
theorem t7_106choices : plan8587.choices=[1,9,3,10,7,7,7].map (options 7 5) := by rfl


theorem t7_106part0 : t7_106jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_106frontier : t7_106root.frontier 0=t7_106jobs := by rfl
theorem t7_106all : t7_106jobs.all (Job.check tree)=true := by
  simp only [t7_106jobs,List.all_append,List.all_nil,t7_106part0,Bool.and_self]
theorem t7_106checked : Checked tree [1,9,3,10,7,7,7] := by
  refine ⟨plan8587,valid8587,t7_106choices,?_⟩
  exact check_of_frontier tree 0 t7_106root t7_106jobs t7_106frontier t7_106all
theorem t7_107choices : plan8751.choices=[1,9,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_107part0 : t7_107jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_107frontier : t7_107root.frontier 0=t7_107jobs := by rfl
theorem t7_107all : t7_107jobs.all (Job.check tree)=true := by
  simp only [t7_107jobs,List.all_append,List.all_nil,t7_107part0,Bool.and_self]
theorem t7_107checked : Checked tree [1,9,6,6,7,7,7] := by
  refine ⟨plan8751,valid8751,t7_107choices,?_⟩
  exact check_of_frontier tree 0 t7_107root t7_107jobs t7_107frontier t7_107all
theorem t7_108choices : plan8752.choices=[1,9,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_108part0 : t7_108jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_108frontier : t7_108root.frontier 0=t7_108jobs := by rfl
theorem t7_108all : t7_108jobs.all (Job.check tree)=true := by
  simp only [t7_108jobs,List.all_append,List.all_nil,t7_108part0,Bool.and_self]
theorem t7_108checked : Checked tree [1,9,6,7,7,7,7] := by
  refine ⟨plan8752,valid8752,t7_108choices,?_⟩
  exact check_of_frontier tree 0 t7_108root t7_108jobs t7_108frontier t7_108all
theorem t7_109choices : plan8753.choices=[1,9,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_109part0 : t7_109jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_109frontier : t7_109root.frontier 0=t7_109jobs := by rfl
theorem t7_109all : t7_109jobs.all (Job.check tree)=true := by
  simp only [t7_109jobs,List.all_append,List.all_nil,t7_109part0,Bool.and_self]
theorem t7_109checked : Checked tree [1,9,6,10,7,7,7] := by
  refine ⟨plan8753,valid8753,t7_109choices,?_⟩
  exact check_of_frontier tree 0 t7_109root t7_109jobs t7_109frontier t7_109all
theorem t7_110choices : plan8754.choices=[1,9,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_110part0 : t7_110jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_110frontier : t7_110root.frontier 0=t7_110jobs := by rfl
theorem t7_110all : t7_110jobs.all (Job.check tree)=true := by
  simp only [t7_110jobs,List.all_append,List.all_nil,t7_110part0,Bool.and_self]
theorem t7_110checked : Checked tree [1,9,7,7,7,7,7] := by
  refine ⟨plan8754,valid8754,t7_110choices,?_⟩
  exact check_of_frontier tree 0 t7_110root t7_110jobs t7_110frontier t7_110all
theorem t7_111choices : plan8755.choices=[1,9,9,7,7,7,7].map (options 7 6) := by rfl


theorem t7_111part0 : t7_111jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_111frontier : t7_111root.frontier 0=t7_111jobs := by rfl
theorem t7_111all : t7_111jobs.all (Job.check tree)=true := by
  simp only [t7_111jobs,List.all_append,List.all_nil,t7_111part0,Bool.and_self]
theorem t7_111checked : Checked tree [1,9,9,7,7,7,7] := by
  refine ⟨plan8755,valid8755,t7_111choices,?_⟩
  exact check_of_frontier tree 0 t7_111root t7_111jobs t7_111frontier t7_111all
theorem t7_112choices : plan8756.choices=[1,9,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_112part0 : t7_112jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_112frontier : t7_112root.frontier 0=t7_112jobs := by rfl
theorem t7_112all : t7_112jobs.all (Job.check tree)=true := by
  simp only [t7_112jobs,List.all_append,List.all_nil,t7_112part0,Bool.and_self]
theorem t7_112checked : Checked tree [1,9,10,7,7,7,7] := by
  refine ⟨plan8756,valid8756,t7_112choices,?_⟩
  exact check_of_frontier tree 0 t7_112root t7_112jobs t7_112frontier t7_112all
theorem t7_113choices : plan8757.choices=[1,9,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_113part0 : t7_113jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_113frontier : t7_113root.frontier 0=t7_113jobs := by rfl
theorem t7_113all : t7_113jobs.all (Job.check tree)=true := by
  simp only [t7_113jobs,List.all_append,List.all_nil,t7_113part0,Bool.and_self]
theorem t7_113checked : Checked tree [1,9,10,10,7,7,7] := by
  refine ⟨plan8757,valid8757,t7_113choices,?_⟩
  exact check_of_frontier tree 0 t7_113root t7_113jobs t7_113frontier t7_113all
theorem t7_114choices : plan8758.choices=[1,10,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_114part0 : t7_114jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_114frontier : t7_114root.frontier 0=t7_114jobs := by rfl
theorem t7_114all : t7_114jobs.all (Job.check tree)=true := by
  simp only [t7_114jobs,List.all_append,List.all_nil,t7_114part0,Bool.and_self]
theorem t7_114checked : Checked tree [1,10,7,7,7,7,7] := by
  refine ⟨plan8758,valid8758,t7_114choices,?_⟩
  exact check_of_frontier tree 0 t7_114root t7_114jobs t7_114frontier t7_114all
theorem t7_115choices : plan8759.choices=[1,10,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_115part0 : t7_115jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_115frontier : t7_115root.frontier 0=t7_115jobs := by rfl
theorem t7_115all : t7_115jobs.all (Job.check tree)=true := by
  simp only [t7_115jobs,List.all_append,List.all_nil,t7_115part0,Bool.and_self]
theorem t7_115checked : Checked tree [1,10,10,7,7,7,7] := by
  refine ⟨plan8759,valid8759,t7_115choices,?_⟩
  exact check_of_frontier tree 0 t7_115root t7_115jobs t7_115frontier t7_115all
theorem t7_116choices : plan8760.choices=[1,10,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_116part0 : t7_116jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_116frontier : t7_116root.frontier 0=t7_116jobs := by rfl
theorem t7_116all : t7_116jobs.all (Job.check tree)=true := by
  simp only [t7_116jobs,List.all_append,List.all_nil,t7_116part0,Bool.and_self]
theorem t7_116checked : Checked tree [1,10,10,10,7,7,7] := by
  refine ⟨plan8760,valid8760,t7_116choices,?_⟩
  exact check_of_frontier tree 0 t7_116root t7_116jobs t7_116frontier t7_116all
theorem t7_117choices : plan8761.choices=[1,10,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_117part0 : t7_117jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_117frontier : t7_117root.frontier 0=t7_117jobs := by rfl
theorem t7_117all : t7_117jobs.all (Job.check tree)=true := by
  simp only [t7_117jobs,List.all_append,List.all_nil,t7_117part0,Bool.and_self]
theorem t7_117checked : Checked tree [1,10,10,10,10,7,7] := by
  refine ⟨plan8761,valid8761,t7_117choices,?_⟩
  exact check_of_frontier tree 0 t7_117root t7_117jobs t7_117frontier t7_117all
theorem t7_118choices : plan8435.choices=[2,2,2,3,7,7,7].map (options 7 3) := by rfl


theorem t7_118part0 : t7_118jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_118frontier : t7_118root.frontier 0=t7_118jobs := by rfl
theorem t7_118all : t7_118jobs.all (Job.check tree)=true := by
  simp only [t7_118jobs,List.all_append,List.all_nil,t7_118part0,Bool.and_self]
theorem t7_118checked : Checked tree [2,2,2,3,7,7,7] := by
  refine ⟨plan8435,valid8435,t7_118choices,?_⟩
  exact check_of_frontier tree 0 t7_118root t7_118jobs t7_118frontier t7_118all
theorem t7_119choices : plan8482.choices=[2,2,2,6,7,7,7].map (options 7 4) := by rfl


theorem t7_119part0 : t7_119jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_119frontier : t7_119root.frontier 0=t7_119jobs := by rfl
theorem t7_119all : t7_119jobs.all (Job.check tree)=true := by
  simp only [t7_119jobs,List.all_append,List.all_nil,t7_119part0,Bool.and_self]
theorem t7_119checked : Checked tree [2,2,2,6,7,7,7] := by
  refine ⟨plan8482,valid8482,t7_119choices,?_⟩
  exact check_of_frontier tree 0 t7_119root t7_119jobs t7_119frontier t7_119all
theorem t7_120choices : plan8483.choices=[2,2,2,7,7,7,7].map (options 7 4) := by rfl


theorem t7_120part0 : t7_120jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_120frontier : t7_120root.frontier 0=t7_120jobs := by rfl
theorem t7_120all : t7_120jobs.all (Job.check tree)=true := by
  simp only [t7_120jobs,List.all_append,List.all_nil,t7_120part0,Bool.and_self]
theorem t7_120checked : Checked tree [2,2,2,7,7,7,7] := by
  refine ⟨plan8483,valid8483,t7_120choices,?_⟩
  exact check_of_frontier tree 0 t7_120root t7_120jobs t7_120frontier t7_120all
theorem t7_121choices : plan8484.choices=[2,2,2,10,7,7,7].map (options 7 4) := by rfl


theorem t7_121part0 : t7_121jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_121frontier : t7_121root.frontier 0=t7_121jobs := by rfl
theorem t7_121all : t7_121jobs.all (Job.check tree)=true := by
  simp only [t7_121jobs,List.all_append,List.all_nil,t7_121part0,Bool.and_self]
theorem t7_121checked : Checked tree [2,2,2,10,7,7,7] := by
  refine ⟨plan8484,valid8484,t7_121choices,?_⟩
  exact check_of_frontier tree 0 t7_121root t7_121jobs t7_121frontier t7_121all
theorem t7_122choices : plan8418.choices=[2,2,3,3,3,7,7].map (options 7 2) := by rfl


theorem t7_122part0 : t7_122jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_122frontier : t7_122root.frontier 0=t7_122jobs := by rfl
theorem t7_122all : t7_122jobs.all (Job.check tree)=true := by
  simp only [t7_122jobs,List.all_append,List.all_nil,t7_122part0,Bool.and_self]
theorem t7_122checked : Checked tree [2,2,3,3,3,7,7] := by
  refine ⟨plan8418,valid8418,t7_122choices,?_⟩
  exact check_of_frontier tree 0 t7_122root t7_122jobs t7_122frontier t7_122all
theorem t7_123choices : plan8436.choices=[2,2,3,3,6,7,7].map (options 7 3) := by rfl


theorem t7_123part0 : t7_123jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_123frontier : t7_123root.frontier 0=t7_123jobs := by rfl
theorem t7_123all : t7_123jobs.all (Job.check tree)=true := by
  simp only [t7_123jobs,List.all_append,List.all_nil,t7_123part0,Bool.and_self]
theorem t7_123checked : Checked tree [2,2,3,3,6,7,7] := by
  refine ⟨plan8436,valid8436,t7_123choices,?_⟩
  exact check_of_frontier tree 0 t7_123root t7_123jobs t7_123frontier t7_123all
theorem t7_124choices : plan8437.choices=[2,2,3,3,7,7,7].map (options 7 3) := by rfl


theorem t7_124part0 : t7_124jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_124part1 : t7_124jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_124frontier : t7_124root.frontier 1=t7_124jobs := by rfl
theorem t7_124all : t7_124jobs.all (Job.check tree)=true := by
  simp only [t7_124jobs,List.all_append,List.all_nil,t7_124part0,t7_124part1,Bool.and_self]
theorem t7_124checked : Checked tree [2,2,3,3,7,7,7] := by
  refine ⟨plan8437,valid8437,t7_124choices,?_⟩
  exact check_of_frontier tree 1 t7_124root t7_124jobs t7_124frontier t7_124all
theorem t7_125choices : plan8438.choices=[2,2,3,3,10,7,7].map (options 7 3) := by rfl


theorem t7_125part0 : t7_125jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_125frontier : t7_125root.frontier 0=t7_125jobs := by rfl
theorem t7_125all : t7_125jobs.all (Job.check tree)=true := by
  simp only [t7_125jobs,List.all_append,List.all_nil,t7_125part0,Bool.and_self]
theorem t7_125checked : Checked tree [2,2,3,3,10,7,7] := by
  refine ⟨plan8438,valid8438,t7_125choices,?_⟩
  exact check_of_frontier tree 0 t7_125root t7_125jobs t7_125frontier t7_125all
theorem t7_126choices : plan8485.choices=[2,2,3,6,6,7,7].map (options 7 4) := by rfl


theorem t7_126part0 : t7_126jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_126frontier : t7_126root.frontier 0=t7_126jobs := by rfl
theorem t7_126all : t7_126jobs.all (Job.check tree)=true := by
  simp only [t7_126jobs,List.all_append,List.all_nil,t7_126part0,Bool.and_self]
theorem t7_126checked : Checked tree [2,2,3,6,6,7,7] := by
  refine ⟨plan8485,valid8485,t7_126choices,?_⟩
  exact check_of_frontier tree 0 t7_126root t7_126jobs t7_126frontier t7_126all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks157 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_71checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_84checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_85checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_86checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_87checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_88checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_89checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_90checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_91checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_92checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_93checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_72checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_94checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_95checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_96checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_97checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_98checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_99checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_100checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_101checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_102checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_103checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_73checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_104checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_105checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_106checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_107checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_108checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_109checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_110checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_111checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_112checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_113checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_74checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_114checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_115checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_116checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_117checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_118checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_119checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_120checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_121checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_122checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_75checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_123checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_124checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_125checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_126checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_76checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_77checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_78checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_79checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_80checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_81checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_82checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_83checked⟩
