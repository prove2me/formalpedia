-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks193
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:20:00.631048+00:00
-- url     : https://prove2.me/submissions/15412af7-5a13-4416-b840-dd26de60b8ca

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks193
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks193
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans086
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans093
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans094
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans095
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











































































































theorem valid150 : plan150.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid153 : plan153.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid156 : plan156.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid159 : plan159.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid160 : plan160.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid162 : plan162.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid163 : plan163.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid164 : plan164.Valid := valid_step _ _ _ valid0 (by decide +kernel)
























































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





























































theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)











theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)











theorem valid619 : plan619.Valid := valid_step _ _ _ valid156 (by decide +kernel)

theorem valid620 : plan620.Valid := valid_step _ _ _ valid156 (by decide +kernel)





theorem valid623 : plan623.Valid := valid_step _ _ _ valid159 (by decide +kernel)



theorem valid625 : plan625.Valid := valid_step _ _ _ valid159 (by decide +kernel)

theorem valid626 : plan626.Valid := valid_step _ _ _ valid159 (by decide +kernel)

theorem valid627 : plan627.Valid := valid_step _ _ _ valid160 (by decide +kernel)



theorem valid629 : plan629.Valid := valid_step _ _ _ valid162 (by decide +kernel)

theorem valid630 : plan630.Valid := valid_step _ _ _ valid163 (by decide +kernel)

theorem valid631 : plan631.Valid := valid_step _ _ _ valid164 (by decide +kernel)


















































































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





























theorem valid1647 : plan1647.Valid := valid_step _ _ _ valid607 (by decide +kernel)



























theorem valid1661 : plan1661.Valid := valid_step _ _ _ valid613 (by decide +kernel)





theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)











theorem valid1671 : plan1671.Valid := valid_step _ _ _ valid619 (by decide +kernel)





theorem valid1674 : plan1674.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1675 : plan1675.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1676 : plan1676.Valid := valid_step _ _ _ valid620 (by decide +kernel)





theorem valid1679 : plan1679.Valid := valid_step _ _ _ valid623 (by decide +kernel)



theorem valid1681 : plan1681.Valid := valid_step _ _ _ valid625 (by decide +kernel)

theorem valid1682 : plan1682.Valid := valid_step _ _ _ valid626 (by decide +kernel)



theorem valid1684 : plan1684.Valid := valid_step _ _ _ valid625 (by decide +kernel)

theorem valid1685 : plan1685.Valid := valid_step _ _ _ valid625 (by decide +kernel)

theorem valid1686 : plan1686.Valid := valid_step _ _ _ valid626 (by decide +kernel)

theorem valid1687 : plan1687.Valid := valid_step _ _ _ valid627 (by decide +kernel)



theorem valid1689 : plan1689.Valid := valid_step _ _ _ valid629 (by decide +kernel)

theorem valid1690 : plan1690.Valid := valid_step _ _ _ valid630 (by decide +kernel)

theorem valid1691 : plan1691.Valid := valid_step _ _ _ valid631 (by decide +kernel)










































































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

theorem valid3649 : plan3649.Valid := valid_step _ _ _ valid1685 (by decide +kernel)

theorem valid3650 : plan3650.Valid := valid_step _ _ _ valid1686 (by decide +kernel)

theorem valid3651 : plan3651.Valid := valid_step _ _ _ valid1687 (by decide +kernel)



theorem valid3653 : plan3653.Valid := valid_step _ _ _ valid1689 (by decide +kernel)

theorem valid3654 : plan3654.Valid := valid_step _ _ _ valid1690 (by decide +kernel)

theorem valid3655 : plan3655.Valid := valid_step _ _ _ valid1691 (by decide +kernel)


















































































































































































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

























































theorem valid3581 : plan3581.Valid := valid_step _ _ _ valid1647 (by decide +kernel)











































theorem valid3603 : plan3603.Valid := valid_step _ _ _ valid1661 (by decide +kernel)

theorem valid3604 : plan3604.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3605 : plan3605.Valid := valid_step _ _ _ valid1665 (by decide +kernel)































theorem valid3621 : plan3621.Valid := valid_step _ _ _ valid1674 (by decide +kernel)







theorem valid3625 : plan3625.Valid := valid_step _ _ _ valid1671 (by decide +kernel)





theorem valid3628 : plan3628.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3629 : plan3629.Valid := valid_step _ _ _ valid1675 (by decide +kernel)





theorem valid3632 : plan3632.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3633 : plan3633.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3634 : plan3634.Valid := valid_step _ _ _ valid1675 (by decide +kernel)

theorem valid3635 : plan3635.Valid := valid_step _ _ _ valid1676 (by decide +kernel)





theorem valid3638 : plan3638.Valid := valid_step _ _ _ valid1679 (by decide +kernel)



theorem valid3640 : plan3640.Valid := valid_step _ _ _ valid1681 (by decide +kernel)

theorem valid3641 : plan3641.Valid := valid_step _ _ _ valid1682 (by decide +kernel)



theorem valid3643 : plan3643.Valid := valid_step _ _ _ valid1684 (by decide +kernel)

theorem valid3644 : plan3644.Valid := valid_step _ _ _ valid1685 (by decide +kernel)

theorem valid3645 : plan3645.Valid := valid_step _ _ _ valid1686 (by decide +kernel)



theorem valid3647 : plan3647.Valid := valid_step _ _ _ valid1684 (by decide +kernel)

theorem valid3648 : plan3648.Valid := valid_step _ _ _ valid1684 (by decide +kernel)
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

theorem valid6241 : plan6241.Valid := valid_step _ _ _ valid3640 (by decide +kernel)

theorem valid6242 : plan6242.Valid := valid_step _ _ _ valid3641 (by decide +kernel)



theorem valid6244 : plan6244.Valid := valid_step _ _ _ valid3643 (by decide +kernel)

theorem valid6245 : plan6245.Valid := valid_step _ _ _ valid3644 (by decide +kernel)

theorem valid6246 : plan6246.Valid := valid_step _ _ _ valid3645 (by decide +kernel)



theorem valid6248 : plan6248.Valid := valid_step _ _ _ valid3647 (by decide +kernel)

theorem valid6249 : plan6249.Valid := valid_step _ _ _ valid3648 (by decide +kernel)

theorem valid6250 : plan6250.Valid := valid_step _ _ _ valid3649 (by decide +kernel)

theorem valid6251 : plan6251.Valid := valid_step _ _ _ valid3650 (by decide +kernel)



theorem valid6253 : plan6253.Valid := valid_step _ _ _ valid3647 (by decide +kernel)

theorem valid6254 : plan6254.Valid := valid_step _ _ _ valid3643 (by decide +kernel)

theorem valid6255 : plan6255.Valid := valid_step _ _ _ valid3647 (by decide +kernel)

theorem valid6256 : plan6256.Valid := valid_step _ _ _ valid3648 (by decide +kernel)

theorem valid6257 : plan6257.Valid := valid_step _ _ _ valid3647 (by decide +kernel)

theorem valid6258 : plan6258.Valid := valid_step _ _ _ valid3648 (by decide +kernel)

theorem valid6259 : plan6259.Valid := valid_step _ _ _ valid3649 (by decide +kernel)

theorem valid6260 : plan6260.Valid := valid_step _ _ _ valid3650 (by decide +kernel)

theorem valid6261 : plan6261.Valid := valid_step _ _ _ valid3651 (by decide +kernel)





theorem valid6264 : plan6264.Valid := valid_step _ _ _ valid3653 (by decide +kernel)





theorem valid6267 : plan6267.Valid := valid_step _ _ _ valid3654 (by decide +kernel)





theorem valid6270 : plan6270.Valid := valid_step _ _ _ valid3655 (by decide +kernel)




































































































































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









































































































































































theorem valid6133 : plan6133.Valid := valid_step _ _ _ valid3581 (by decide +kernel)






















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



























theorem valid6158 : plan6158.Valid := valid_step _ _ _ valid3603 (by decide +kernel)

theorem valid6159 : plan6159.Valid := valid_step _ _ _ valid3604 (by decide +kernel)

theorem valid6160 : plan6160.Valid := valid_step _ _ _ valid3605 (by decide +kernel)















































































theorem valid6200 : plan6200.Valid := valid_step _ _ _ valid3625 (by decide +kernel)

theorem valid6201 : plan6201.Valid := valid_step _ _ _ valid3628 (by decide +kernel)

theorem valid6202 : plan6202.Valid := valid_step _ _ _ valid3629 (by decide +kernel)

theorem valid6203 : plan6203.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6204 : plan6204.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6205 : plan6205.Valid := valid_step _ _ _ valid3634 (by decide +kernel)







































theorem valid6225 : plan6225.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6226 : plan6226.Valid := valid_step _ _ _ valid3621 (by decide +kernel)







theorem valid6230 : plan6230.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6231 : plan6231.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6232 : plan6232.Valid := valid_step _ _ _ valid3634 (by decide +kernel)

theorem valid6233 : plan6233.Valid := valid_step _ _ _ valid3635 (by decide +kernel)











theorem valid6239 : plan6239.Valid := valid_step _ _ _ valid3638 (by decide +kernel)


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

























































































































































theorem valid8141 : plan8141.Valid := valid_step _ _ _ valid6133 (by decide +kernel)






































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



theorem valid8354 : plan8354.Valid := valid_step _ _ _ valid6248 (by decide +kernel)

theorem valid8355 : plan8355.Valid := valid_step _ _ _ valid6249 (by decide +kernel)

theorem valid8356 : plan8356.Valid := valid_step _ _ _ valid6250 (by decide +kernel)

theorem valid8357 : plan8357.Valid := valid_step _ _ _ valid6251 (by decide +kernel)



theorem valid8359 : plan8359.Valid := valid_step _ _ _ valid6253 (by decide +kernel)

theorem valid8360 : plan8360.Valid := valid_step _ _ _ valid6257 (by decide +kernel)

theorem valid8361 : plan8361.Valid := valid_step _ _ _ valid6258 (by decide +kernel)

theorem valid8362 : plan8362.Valid := valid_step _ _ _ valid6259 (by decide +kernel)

theorem valid8363 : plan8363.Valid := valid_step _ _ _ valid6260 (by decide +kernel)



theorem valid8365 : plan8365.Valid := valid_step _ _ _ valid6253 (by decide +kernel)







theorem valid8369 : plan8369.Valid := valid_step _ _ _ valid6241 (by decide +kernel)

theorem valid8370 : plan8370.Valid := valid_step _ _ _ valid6244 (by decide +kernel)

theorem valid8371 : plan8371.Valid := valid_step _ _ _ valid6245 (by decide +kernel)

theorem valid8372 : plan8372.Valid := valid_step _ _ _ valid6248 (by decide +kernel)

theorem valid8373 : plan8373.Valid := valid_step _ _ _ valid6249 (by decide +kernel)

theorem valid8374 : plan8374.Valid := valid_step _ _ _ valid6250 (by decide +kernel)

theorem valid8375 : plan8375.Valid := valid_step _ _ _ valid6253 (by decide +kernel)

theorem valid8376 : plan8376.Valid := valid_step _ _ _ valid6254 (by decide +kernel)

theorem valid8377 : plan8377.Valid := valid_step _ _ _ valid6255 (by decide +kernel)

theorem valid8378 : plan8378.Valid := valid_step _ _ _ valid6256 (by decide +kernel)

theorem valid8379 : plan8379.Valid := valid_step _ _ _ valid6257 (by decide +kernel)

theorem valid8380 : plan8380.Valid := valid_step _ _ _ valid6258 (by decide +kernel)

theorem valid8381 : plan8381.Valid := valid_step _ _ _ valid6259 (by decide +kernel)

theorem valid8382 : plan8382.Valid := valid_step _ _ _ valid6253 (by decide +kernel)

theorem valid8383 : plan8383.Valid := valid_step _ _ _ valid6257 (by decide +kernel)

theorem valid8384 : plan8384.Valid := valid_step _ _ _ valid6258 (by decide +kernel)

theorem valid8385 : plan8385.Valid := valid_step _ _ _ valid6259 (by decide +kernel)

theorem valid8386 : plan8386.Valid := valid_step _ _ _ valid6260 (by decide +kernel)

theorem valid8387 : plan8387.Valid := valid_step _ _ _ valid6261 (by decide +kernel)





theorem valid8390 : plan8390.Valid := valid_step _ _ _ valid6264 (by decide +kernel)







theorem valid8394 : plan8394.Valid := valid_step _ _ _ valid6267 (by decide +kernel)



theorem valid8396 : plan8396.Valid := valid_step _ _ _ valid6267 (by decide +kernel)

theorem valid8397 : plan8397.Valid := valid_step _ _ _ valid6267 (by decide +kernel)









theorem valid8402 : plan8402.Valid := valid_step _ _ _ valid6270 (by decide +kernel)




























































































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







































































































theorem valid8212 : plan8212.Valid := valid_step _ _ _ valid6158 (by decide +kernel)

theorem valid8213 : plan8213.Valid := valid_step _ _ _ valid6159 (by decide +kernel)

theorem valid8214 : plan8214.Valid := valid_step _ _ _ valid6160 (by decide +kernel)



















































theorem valid8240 : plan8240.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8241 : plan8241.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8242 : plan8242.Valid := valid_step _ _ _ valid6231 (by decide +kernel)

theorem valid8243 : plan8243.Valid := valid_step _ _ _ valid6232 (by decide +kernel)

theorem valid8244 : plan8244.Valid := valid_step _ _ _ valid6233 (by decide +kernel)
























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



theorem valid8546 : plan8546.Valid := valid_step _ _ _ valid8141 (by decide +kernel)




























































































































































































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





















































































theorem valid8299 : plan8299.Valid := valid_step _ _ _ valid6200 (by decide +kernel)

theorem valid8300 : plan8300.Valid := valid_step _ _ _ valid6201 (by decide +kernel)

theorem valid8301 : plan8301.Valid := valid_step _ _ _ valid6202 (by decide +kernel)

theorem valid8302 : plan8302.Valid := valid_step _ _ _ valid6203 (by decide +kernel)

theorem valid8303 : plan8303.Valid := valid_step _ _ _ valid6204 (by decide +kernel)

theorem valid8304 : plan8304.Valid := valid_step _ _ _ valid6205 (by decide +kernel)















theorem valid8312 : plan8312.Valid := valid_step _ _ _ valid6226 (by decide +kernel)

































































theorem valid8345 : plan8345.Valid := valid_step _ _ _ valid6239 (by decide +kernel)



theorem valid8347 : plan8347.Valid := valid_step _ _ _ valid6241 (by decide +kernel)

theorem valid8348 : plan8348.Valid := valid_step _ _ _ valid6242 (by decide +kernel)



theorem valid8350 : plan8350.Valid := valid_step _ _ _ valid6244 (by decide +kernel)

theorem valid8351 : plan8351.Valid := valid_step _ _ _ valid6245 (by decide +kernel)

theorem valid8352 : plan8352.Valid := valid_step _ _ _ valid6246 (by decide +kernel)
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

































































































































theorem valid8705 : plan8705.Valid := valid_step _ _ _ valid8212 (by decide +kernel)

theorem valid8706 : plan8706.Valid := valid_step _ _ _ valid8213 (by decide +kernel)

theorem valid8707 : plan8707.Valid := valid_step _ _ _ valid8214 (by decide +kernel)


























































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





theorem valid8931 : plan8931.Valid := valid_step _ _ _ valid8240 (by decide +kernel)

theorem valid8932 : plan8932.Valid := valid_step _ _ _ valid8241 (by decide +kernel)

theorem valid8933 : plan8933.Valid := valid_step _ _ _ valid8242 (by decide +kernel)

theorem valid8934 : plan8934.Valid := valid_step _ _ _ valid8243 (by decide +kernel)

theorem valid8935 : plan8935.Valid := valid_step _ _ _ valid8244 (by decide +kernel)

theorem valid8936 : plan8936.Valid := valid_step _ _ _ valid8299 (by decide +kernel)

theorem valid8937 : plan8937.Valid := valid_step _ _ _ valid8300 (by decide +kernel)

theorem valid8938 : plan8938.Valid := valid_step _ _ _ valid8301 (by decide +kernel)

theorem valid8939 : plan8939.Valid := valid_step _ _ _ valid8302 (by decide +kernel)

theorem valid8940 : plan8940.Valid := valid_step _ _ _ valid8303 (by decide +kernel)

theorem valid8941 : plan8941.Valid := valid_step _ _ _ valid8304 (by decide +kernel)

theorem valid8942 : plan8942.Valid := valid_step _ _ _ valid8312 (by decide +kernel)




































































































































































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





































































































































theorem valid9091 : plan9091.Valid := valid_step _ _ _ valid8345 (by decide +kernel)

theorem valid9092 : plan9092.Valid := valid_step _ _ _ valid8347 (by decide +kernel)

theorem valid9093 : plan9093.Valid := valid_step _ _ _ valid8348 (by decide +kernel)

theorem valid9094 : plan9094.Valid := valid_step _ _ _ valid8350 (by decide +kernel)

theorem valid9095 : plan9095.Valid := valid_step _ _ _ valid8351 (by decide +kernel)

theorem valid9096 : plan9096.Valid := valid_step _ _ _ valid8352 (by decide +kernel)

theorem valid9097 : plan9097.Valid := valid_step _ _ _ valid8354 (by decide +kernel)

theorem valid9098 : plan9098.Valid := valid_step _ _ _ valid8355 (by decide +kernel)

theorem valid9099 : plan9099.Valid := valid_step _ _ _ valid8356 (by decide +kernel)

theorem valid9100 : plan9100.Valid := valid_step _ _ _ valid8357 (by decide +kernel)

theorem valid9101 : plan9101.Valid := valid_step _ _ _ valid8359 (by decide +kernel)

theorem valid9102 : plan9102.Valid := valid_step _ _ _ valid8360 (by decide +kernel)

theorem valid9103 : plan9103.Valid := valid_step _ _ _ valid8361 (by decide +kernel)

theorem valid9104 : plan9104.Valid := valid_step _ _ _ valid8362 (by decide +kernel)

theorem valid9105 : plan9105.Valid := valid_step _ _ _ valid8363 (by decide +kernel)

theorem valid9106 : plan9106.Valid := valid_step _ _ _ valid8365 (by decide +kernel)

theorem valid9107 : plan9107.Valid := valid_step _ _ _ valid8369 (by decide +kernel)

theorem valid9108 : plan9108.Valid := valid_step _ _ _ valid8370 (by decide +kernel)

theorem valid9109 : plan9109.Valid := valid_step _ _ _ valid8371 (by decide +kernel)

theorem valid9110 : plan9110.Valid := valid_step _ _ _ valid8372 (by decide +kernel)

theorem valid9111 : plan9111.Valid := valid_step _ _ _ valid8373 (by decide +kernel)

theorem valid9112 : plan9112.Valid := valid_step _ _ _ valid8374 (by decide +kernel)

theorem valid9113 : plan9113.Valid := valid_step _ _ _ valid8375 (by decide +kernel)

theorem valid9114 : plan9114.Valid := valid_step _ _ _ valid8376 (by decide +kernel)

theorem valid9115 : plan9115.Valid := valid_step _ _ _ valid8377 (by decide +kernel)

theorem valid9116 : plan9116.Valid := valid_step _ _ _ valid8378 (by decide +kernel)

theorem valid9117 : plan9117.Valid := valid_step _ _ _ valid8379 (by decide +kernel)

theorem valid9118 : plan9118.Valid := valid_step _ _ _ valid8380 (by decide +kernel)

theorem valid9119 : plan9119.Valid := valid_step _ _ _ valid8381 (by decide +kernel)

theorem valid9120 : plan9120.Valid := valid_step _ _ _ valid8382 (by decide +kernel)
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

theorem valid9121 : plan9121.Valid := valid_step _ _ _ valid8383 (by decide +kernel)

theorem valid9122 : plan9122.Valid := valid_step _ _ _ valid8384 (by decide +kernel)

theorem valid9123 : plan9123.Valid := valid_step _ _ _ valid8385 (by decide +kernel)

theorem valid9124 : plan9124.Valid := valid_step _ _ _ valid8386 (by decide +kernel)

theorem valid9125 : plan9125.Valid := valid_step _ _ _ valid8365 (by decide +kernel)

theorem valid9126 : plan9126.Valid := valid_step _ _ _ valid8382 (by decide +kernel)

theorem valid9127 : plan9127.Valid := valid_step _ _ _ valid8383 (by decide +kernel)

theorem valid9128 : plan9128.Valid := valid_step _ _ _ valid8384 (by decide +kernel)

theorem valid9129 : plan9129.Valid := valid_step _ _ _ valid8385 (by decide +kernel)

theorem valid9130 : plan9130.Valid := valid_step _ _ _ valid8386 (by decide +kernel)

theorem valid9131 : plan9131.Valid := valid_step _ _ _ valid8387 (by decide +kernel)





theorem valid9134 : plan9134.Valid := valid_step _ _ _ valid8390 (by decide +kernel)



theorem valid9136 : plan9136.Valid := valid_step _ _ _ valid8396 (by decide +kernel)





theorem valid9139 : plan9139.Valid := valid_step _ _ _ valid8394 (by decide +kernel)



theorem valid9141 : plan9141.Valid := valid_step _ _ _ valid8396 (by decide +kernel)

theorem valid9142 : plan9142.Valid := valid_step _ _ _ valid8397 (by decide +kernel)

















theorem valid9151 : plan9151.Valid := valid_step _ _ _ valid8402 (by decide +kernel)





theorem valid9154 : plan9154.Valid := valid_step _ _ _ valid8402 (by decide +kernel)



theorem valid9156 : plan9156.Valid := valid_step _ _ _ valid8402 (by decide +kernel)

































theorem valid9173 : plan9173.Valid := valid_step _ _ _ valid9134 (by decide +kernel)







theorem valid9177 : plan9177.Valid := valid_step _ _ _ valid9141 (by decide +kernel)

theorem valid9178 : plan9178.Valid := valid_step _ _ _ valid9136 (by decide +kernel)

theorem valid9179 : plan9179.Valid := valid_step _ _ _ valid9139 (by decide +kernel)

theorem valid9180 : plan9180.Valid := valid_step _ _ _ valid9141 (by decide +kernel)

theorem valid9181 : plan9181.Valid := valid_step _ _ _ valid9142 (by decide +kernel)

















theorem valid9190 : plan9190.Valid := valid_step _ _ _ valid9154 (by decide +kernel)

theorem valid9191 : plan9191.Valid := valid_step _ _ _ valid9151 (by decide +kernel)

theorem valid9192 : plan9192.Valid := valid_step _ _ _ valid9154 (by decide +kernel)

theorem valid9193 : plan9193.Valid := valid_step _ _ _ valid9156 (by decide +kernel)














































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
theorem t7_663choices : plan8931.choices=[9,3,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_663part0 : t7_663jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_663part1 : t7_663jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_663part2 : t7_663jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_663frontier : t7_663root.frontier 1=t7_663jobs := by rfl
theorem t7_663all : t7_663jobs.all (Job.check tree)=true := by
  simp only [t7_663jobs,List.all_append,List.all_nil,t7_663part0,t7_663part1,t7_663part2,Bool.and_self]
theorem t7_663checked : Checked tree [9,3,7,7,7,7,7] := by
  refine ⟨plan8931,valid8931,t7_663choices,?_⟩
  exact check_of_frontier tree 1 t7_663root t7_663jobs t7_663frontier t7_663all
theorem t7_664choices : plan8932.choices=[9,3,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_664part0 : t7_664jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_664part1 : t7_664jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_664part2 : t7_664jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_664frontier : t7_664root.frontier 1=t7_664jobs := by rfl
theorem t7_664all : t7_664jobs.all (Job.check tree)=true := by
  simp only [t7_664jobs,List.all_append,List.all_nil,t7_664part0,t7_664part1,t7_664part2,Bool.and_self]
theorem t7_664checked : Checked tree [9,3,10,7,7,7,7] := by
  refine ⟨plan8932,valid8932,t7_664choices,?_⟩
  exact check_of_frontier tree 1 t7_664root t7_664jobs t7_664frontier t7_664all
theorem t7_665choices : plan8933.choices=[9,3,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_665part0 : t7_665jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_665part1 : t7_665jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_665frontier : t7_665root.frontier 1=t7_665jobs := by rfl
theorem t7_665all : t7_665jobs.all (Job.check tree)=true := by
  simp only [t7_665jobs,List.all_append,List.all_nil,t7_665part0,t7_665part1,Bool.and_self]
theorem t7_665checked : Checked tree [9,3,10,10,7,7,7] := by
  refine ⟨plan8933,valid8933,t7_665choices,?_⟩
  exact check_of_frontier tree 1 t7_665root t7_665jobs t7_665frontier t7_665all
theorem t7_666choices : plan8934.choices=[9,3,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_666part0 : t7_666jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_666frontier : t7_666root.frontier 0=t7_666jobs := by rfl
theorem t7_666all : t7_666jobs.all (Job.check tree)=true := by
  simp only [t7_666jobs,List.all_append,List.all_nil,t7_666part0,Bool.and_self]
theorem t7_666checked : Checked tree [9,3,10,10,10,7,7] := by
  refine ⟨plan8934,valid8934,t7_666choices,?_⟩
  exact check_of_frontier tree 0 t7_666root t7_666jobs t7_666frontier t7_666all
theorem t7_667choices : plan8935.choices=[9,3,10,10,10,10,7].map (options 7 6) := by rfl


theorem t7_667part0 : t7_667jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_667frontier : t7_667root.frontier 0=t7_667jobs := by rfl
theorem t7_667all : t7_667jobs.all (Job.check tree)=true := by
  simp only [t7_667jobs,List.all_append,List.all_nil,t7_667part0,Bool.and_self]
theorem t7_667checked : Checked tree [9,3,10,10,10,10,7] := by
  refine ⟨plan8935,valid8935,t7_667choices,?_⟩
  exact check_of_frontier tree 0 t7_667root t7_667jobs t7_667frontier t7_667all
theorem t7_668choices : plan9091.choices=[9,6,6,6,6,6,7].map (options 7 7) := by rfl


theorem t7_668part0 : t7_668jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_668frontier : t7_668root.frontier 0=t7_668jobs := by rfl
theorem t7_668all : t7_668jobs.all (Job.check tree)=true := by
  simp only [t7_668jobs,List.all_append,List.all_nil,t7_668part0,Bool.and_self]
theorem t7_668checked : Checked tree [9,6,6,6,6,6,7] := by
  refine ⟨plan9091,valid9091,t7_668choices,?_⟩
  exact check_of_frontier tree 0 t7_668root t7_668jobs t7_668frontier t7_668all
theorem t7_669choices : plan9092.choices=[9,6,6,6,6,7,7].map (options 7 7) := by rfl


theorem t7_669part0 : t7_669jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_669frontier : t7_669root.frontier 0=t7_669jobs := by rfl
theorem t7_669all : t7_669jobs.all (Job.check tree)=true := by
  simp only [t7_669jobs,List.all_append,List.all_nil,t7_669part0,Bool.and_self]
theorem t7_669checked : Checked tree [9,6,6,6,6,7,7] := by
  refine ⟨plan9092,valid9092,t7_669choices,?_⟩
  exact check_of_frontier tree 0 t7_669root t7_669jobs t7_669frontier t7_669all
theorem t7_670choices : plan9093.choices=[9,6,6,6,6,10,7].map (options 7 7) := by rfl


theorem t7_670part0 : t7_670jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_670frontier : t7_670root.frontier 0=t7_670jobs := by rfl
theorem t7_670all : t7_670jobs.all (Job.check tree)=true := by
  simp only [t7_670jobs,List.all_append,List.all_nil,t7_670part0,Bool.and_self]
theorem t7_670checked : Checked tree [9,6,6,6,6,10,7] := by
  refine ⟨plan9093,valid9093,t7_670choices,?_⟩
  exact check_of_frontier tree 0 t7_670root t7_670jobs t7_670frontier t7_670all
theorem t7_671choices : plan9094.choices=[9,6,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_671part0 : t7_671jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_671frontier : t7_671root.frontier 0=t7_671jobs := by rfl
theorem t7_671all : t7_671jobs.all (Job.check tree)=true := by
  simp only [t7_671jobs,List.all_append,List.all_nil,t7_671part0,Bool.and_self]
theorem t7_671checked : Checked tree [9,6,6,6,7,7,7] := by
  refine ⟨plan9094,valid9094,t7_671choices,?_⟩
  exact check_of_frontier tree 0 t7_671root t7_671jobs t7_671frontier t7_671all
theorem t7_672choices : plan9095.choices=[9,6,6,6,10,7,7].map (options 7 7) := by rfl


theorem t7_672part0 : t7_672jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_672frontier : t7_672root.frontier 0=t7_672jobs := by rfl
theorem t7_672all : t7_672jobs.all (Job.check tree)=true := by
  simp only [t7_672jobs,List.all_append,List.all_nil,t7_672part0,Bool.and_self]
theorem t7_672checked : Checked tree [9,6,6,6,10,7,7] := by
  refine ⟨plan9095,valid9095,t7_672choices,?_⟩
  exact check_of_frontier tree 0 t7_672root t7_672jobs t7_672frontier t7_672all
theorem t7_673choices : plan9096.choices=[9,6,6,6,10,10,7].map (options 7 7) := by rfl


theorem t7_673part0 : t7_673jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_673frontier : t7_673root.frontier 0=t7_673jobs := by rfl
theorem t7_673all : t7_673jobs.all (Job.check tree)=true := by
  simp only [t7_673jobs,List.all_append,List.all_nil,t7_673part0,Bool.and_self]
theorem t7_673checked : Checked tree [9,6,6,6,10,10,7] := by
  refine ⟨plan9096,valid9096,t7_673choices,?_⟩
  exact check_of_frontier tree 0 t7_673root t7_673jobs t7_673frontier t7_673all
theorem t7_674choices : plan9097.choices=[9,6,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_674part0 : t7_674jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_674frontier : t7_674root.frontier 0=t7_674jobs := by rfl
theorem t7_674all : t7_674jobs.all (Job.check tree)=true := by
  simp only [t7_674jobs,List.all_append,List.all_nil,t7_674part0,Bool.and_self]
theorem t7_674checked : Checked tree [9,6,6,7,7,7,7] := by
  refine ⟨plan9097,valid9097,t7_674choices,?_⟩
  exact check_of_frontier tree 0 t7_674root t7_674jobs t7_674frontier t7_674all
theorem t7_675choices : plan9098.choices=[9,6,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_675part0 : t7_675jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_675frontier : t7_675root.frontier 0=t7_675jobs := by rfl
theorem t7_675all : t7_675jobs.all (Job.check tree)=true := by
  simp only [t7_675jobs,List.all_append,List.all_nil,t7_675part0,Bool.and_self]
theorem t7_675checked : Checked tree [9,6,6,10,7,7,7] := by
  refine ⟨plan9098,valid9098,t7_675choices,?_⟩
  exact check_of_frontier tree 0 t7_675root t7_675jobs t7_675frontier t7_675all
theorem t7_676choices : plan9099.choices=[9,6,6,10,10,7,7].map (options 7 7) := by rfl


theorem t7_676part0 : t7_676jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_676frontier : t7_676root.frontier 0=t7_676jobs := by rfl
theorem t7_676all : t7_676jobs.all (Job.check tree)=true := by
  simp only [t7_676jobs,List.all_append,List.all_nil,t7_676part0,Bool.and_self]
theorem t7_676checked : Checked tree [9,6,6,10,10,7,7] := by
  refine ⟨plan9099,valid9099,t7_676choices,?_⟩
  exact check_of_frontier tree 0 t7_676root t7_676jobs t7_676frontier t7_676all
theorem t7_677choices : plan9100.choices=[9,6,6,10,10,10,7].map (options 7 7) := by rfl


theorem t7_677part0 : t7_677jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_677frontier : t7_677root.frontier 0=t7_677jobs := by rfl
theorem t7_677all : t7_677jobs.all (Job.check tree)=true := by
  simp only [t7_677jobs,List.all_append,List.all_nil,t7_677part0,Bool.and_self]
theorem t7_677checked : Checked tree [9,6,6,10,10,10,7] := by
  refine ⟨plan9100,valid9100,t7_677choices,?_⟩
  exact check_of_frontier tree 0 t7_677root t7_677jobs t7_677frontier t7_677all
theorem t7_678choices : plan9101.choices=[9,6,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_678part0 : t7_678jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_678frontier : t7_678root.frontier 0=t7_678jobs := by rfl
theorem t7_678all : t7_678jobs.all (Job.check tree)=true := by
  simp only [t7_678jobs,List.all_append,List.all_nil,t7_678part0,Bool.and_self]
theorem t7_678checked : Checked tree [9,6,7,7,7,7,7] := by
  refine ⟨plan9101,valid9101,t7_678choices,?_⟩
  exact check_of_frontier tree 0 t7_678root t7_678jobs t7_678frontier t7_678all
theorem t7_679choices : plan9102.choices=[9,6,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_679part0 : t7_679jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_679frontier : t7_679root.frontier 0=t7_679jobs := by rfl
theorem t7_679all : t7_679jobs.all (Job.check tree)=true := by
  simp only [t7_679jobs,List.all_append,List.all_nil,t7_679part0,Bool.and_self]
theorem t7_679checked : Checked tree [9,6,10,7,7,7,7] := by
  refine ⟨plan9102,valid9102,t7_679choices,?_⟩
  exact check_of_frontier tree 0 t7_679root t7_679jobs t7_679frontier t7_679all
theorem t7_680choices : plan9103.choices=[9,6,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_680part0 : t7_680jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_680frontier : t7_680root.frontier 0=t7_680jobs := by rfl
theorem t7_680all : t7_680jobs.all (Job.check tree)=true := by
  simp only [t7_680jobs,List.all_append,List.all_nil,t7_680part0,Bool.and_self]
theorem t7_680checked : Checked tree [9,6,10,10,7,7,7] := by
  refine ⟨plan9103,valid9103,t7_680choices,?_⟩
  exact check_of_frontier tree 0 t7_680root t7_680jobs t7_680frontier t7_680all
theorem t7_681choices : plan9104.choices=[9,6,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_681part0 : t7_681jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_681frontier : t7_681root.frontier 0=t7_681jobs := by rfl
theorem t7_681all : t7_681jobs.all (Job.check tree)=true := by
  simp only [t7_681jobs,List.all_append,List.all_nil,t7_681part0,Bool.and_self]
theorem t7_681checked : Checked tree [9,6,10,10,10,7,7] := by
  refine ⟨plan9104,valid9104,t7_681choices,?_⟩
  exact check_of_frontier tree 0 t7_681root t7_681jobs t7_681frontier t7_681all
theorem t7_682choices : plan9105.choices=[9,6,10,10,10,10,7].map (options 7 7) := by rfl


theorem t7_682part0 : t7_682jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_682frontier : t7_682root.frontier 0=t7_682jobs := by rfl
theorem t7_682all : t7_682jobs.all (Job.check tree)=true := by
  simp only [t7_682jobs,List.all_append,List.all_nil,t7_682part0,Bool.and_self]
theorem t7_682checked : Checked tree [9,6,10,10,10,10,7] := by
  refine ⟨plan9105,valid9105,t7_682choices,?_⟩
  exact check_of_frontier tree 0 t7_682root t7_682jobs t7_682frontier t7_682all
theorem t7_683choices : plan9106.choices=[9,7,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_683part0 : t7_683jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_683frontier : t7_683root.frontier 0=t7_683jobs := by rfl
theorem t7_683all : t7_683jobs.all (Job.check tree)=true := by
  simp only [t7_683jobs,List.all_append,List.all_nil,t7_683part0,Bool.and_self]
theorem t7_683checked : Checked tree [9,7,7,7,7,7,7] := by
  refine ⟨plan9106,valid9106,t7_683choices,?_⟩
  exact check_of_frontier tree 0 t7_683root t7_683jobs t7_683frontier t7_683all
theorem t7_684choices : plan8546.choices=[9,9,3,3,3,7,7].map (options 7 4) := by rfl


theorem t7_684part0 : t7_684jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_684frontier : t7_684root.frontier 0=t7_684jobs := by rfl
theorem t7_684all : t7_684jobs.all (Job.check tree)=true := by
  simp only [t7_684jobs,List.all_append,List.all_nil,t7_684part0,Bool.and_self]
theorem t7_684checked : Checked tree [9,9,3,3,3,7,7] := by
  refine ⟨plan8546,valid8546,t7_684choices,?_⟩
  exact check_of_frontier tree 0 t7_684root t7_684jobs t7_684frontier t7_684all
theorem t7_685choices : plan8705.choices=[9,9,3,3,6,7,7].map (options 7 5) := by rfl


theorem t7_685part0 : t7_685jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_685frontier : t7_685root.frontier 0=t7_685jobs := by rfl
theorem t7_685all : t7_685jobs.all (Job.check tree)=true := by
  simp only [t7_685jobs,List.all_append,List.all_nil,t7_685part0,Bool.and_self]
theorem t7_685checked : Checked tree [9,9,3,3,6,7,7] := by
  refine ⟨plan8705,valid8705,t7_685choices,?_⟩
  exact check_of_frontier tree 0 t7_685root t7_685jobs t7_685frontier t7_685all
theorem t7_686choices : plan8706.choices=[9,9,3,3,7,7,7].map (options 7 5) := by rfl


theorem t7_686part0 : t7_686jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_686frontier : t7_686root.frontier 0=t7_686jobs := by rfl
theorem t7_686all : t7_686jobs.all (Job.check tree)=true := by
  simp only [t7_686jobs,List.all_append,List.all_nil,t7_686part0,Bool.and_self]
theorem t7_686checked : Checked tree [9,9,3,3,7,7,7] := by
  refine ⟨plan8706,valid8706,t7_686choices,?_⟩
  exact check_of_frontier tree 0 t7_686root t7_686jobs t7_686frontier t7_686all
theorem t7_687choices : plan8707.choices=[9,9,3,3,10,7,7].map (options 7 5) := by rfl


theorem t7_687part0 : t7_687jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_687frontier : t7_687root.frontier 0=t7_687jobs := by rfl
theorem t7_687all : t7_687jobs.all (Job.check tree)=true := by
  simp only [t7_687jobs,List.all_append,List.all_nil,t7_687part0,Bool.and_self]
theorem t7_687checked : Checked tree [9,9,3,3,10,7,7] := by
  refine ⟨plan8707,valid8707,t7_687choices,?_⟩
  exact check_of_frontier tree 0 t7_687root t7_687jobs t7_687frontier t7_687all
theorem t7_688choices : plan8936.choices=[9,9,3,6,6,7,7].map (options 7 6) := by rfl


theorem t7_688part0 : t7_688jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_688frontier : t7_688root.frontier 0=t7_688jobs := by rfl
theorem t7_688all : t7_688jobs.all (Job.check tree)=true := by
  simp only [t7_688jobs,List.all_append,List.all_nil,t7_688part0,Bool.and_self]
theorem t7_688checked : Checked tree [9,9,3,6,6,7,7] := by
  refine ⟨plan8936,valid8936,t7_688choices,?_⟩
  exact check_of_frontier tree 0 t7_688root t7_688jobs t7_688frontier t7_688all
theorem t7_689choices : plan8937.choices=[9,9,3,6,7,7,7].map (options 7 6) := by rfl


theorem t7_689part0 : t7_689jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_689frontier : t7_689root.frontier 0=t7_689jobs := by rfl
theorem t7_689all : t7_689jobs.all (Job.check tree)=true := by
  simp only [t7_689jobs,List.all_append,List.all_nil,t7_689part0,Bool.and_self]
theorem t7_689checked : Checked tree [9,9,3,6,7,7,7] := by
  refine ⟨plan8937,valid8937,t7_689choices,?_⟩
  exact check_of_frontier tree 0 t7_689root t7_689jobs t7_689frontier t7_689all
theorem t7_690choices : plan8938.choices=[9,9,3,6,10,7,7].map (options 7 6) := by rfl


theorem t7_690part0 : t7_690jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_690frontier : t7_690root.frontier 0=t7_690jobs := by rfl
theorem t7_690all : t7_690jobs.all (Job.check tree)=true := by
  simp only [t7_690jobs,List.all_append,List.all_nil,t7_690part0,Bool.and_self]
theorem t7_690checked : Checked tree [9,9,3,6,10,7,7] := by
  refine ⟨plan8938,valid8938,t7_690choices,?_⟩
  exact check_of_frontier tree 0 t7_690root t7_690jobs t7_690frontier t7_690all
theorem t7_691choices : plan8939.choices=[9,9,3,7,7,7,7].map (options 7 6) := by rfl


theorem t7_691part0 : t7_691jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_691frontier : t7_691root.frontier 0=t7_691jobs := by rfl
theorem t7_691all : t7_691jobs.all (Job.check tree)=true := by
  simp only [t7_691jobs,List.all_append,List.all_nil,t7_691part0,Bool.and_self]
theorem t7_691checked : Checked tree [9,9,3,7,7,7,7] := by
  refine ⟨plan8939,valid8939,t7_691choices,?_⟩
  exact check_of_frontier tree 0 t7_691root t7_691jobs t7_691frontier t7_691all
theorem t7_692choices : plan8940.choices=[9,9,3,10,7,7,7].map (options 7 6) := by rfl


theorem t7_692part0 : t7_692jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_692frontier : t7_692root.frontier 0=t7_692jobs := by rfl
theorem t7_692all : t7_692jobs.all (Job.check tree)=true := by
  simp only [t7_692jobs,List.all_append,List.all_nil,t7_692part0,Bool.and_self]
theorem t7_692checked : Checked tree [9,9,3,10,7,7,7] := by
  refine ⟨plan8940,valid8940,t7_692choices,?_⟩
  exact check_of_frontier tree 0 t7_692root t7_692jobs t7_692frontier t7_692all
theorem t7_693choices : plan8941.choices=[9,9,3,10,10,7,7].map (options 7 6) := by rfl


theorem t7_693part0 : t7_693jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_693frontier : t7_693root.frontier 0=t7_693jobs := by rfl
theorem t7_693all : t7_693jobs.all (Job.check tree)=true := by
  simp only [t7_693jobs,List.all_append,List.all_nil,t7_693part0,Bool.and_self]
theorem t7_693checked : Checked tree [9,9,3,10,10,7,7] := by
  refine ⟨plan8941,valid8941,t7_693choices,?_⟩
  exact check_of_frontier tree 0 t7_693root t7_693jobs t7_693frontier t7_693all
theorem t7_694choices : plan9107.choices=[9,9,6,6,6,7,7].map (options 7 7) := by rfl


theorem t7_694part0 : t7_694jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_694frontier : t7_694root.frontier 0=t7_694jobs := by rfl
theorem t7_694all : t7_694jobs.all (Job.check tree)=true := by
  simp only [t7_694jobs,List.all_append,List.all_nil,t7_694part0,Bool.and_self]
theorem t7_694checked : Checked tree [9,9,6,6,6,7,7] := by
  refine ⟨plan9107,valid9107,t7_694choices,?_⟩
  exact check_of_frontier tree 0 t7_694root t7_694jobs t7_694frontier t7_694all
theorem t7_695choices : plan9108.choices=[9,9,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_695part0 : t7_695jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_695frontier : t7_695root.frontier 0=t7_695jobs := by rfl
theorem t7_695all : t7_695jobs.all (Job.check tree)=true := by
  simp only [t7_695jobs,List.all_append,List.all_nil,t7_695part0,Bool.and_self]
theorem t7_695checked : Checked tree [9,9,6,6,7,7,7] := by
  refine ⟨plan9108,valid9108,t7_695choices,?_⟩
  exact check_of_frontier tree 0 t7_695root t7_695jobs t7_695frontier t7_695all
theorem t7_696choices : plan9109.choices=[9,9,6,6,10,7,7].map (options 7 7) := by rfl


theorem t7_696part0 : t7_696jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_696frontier : t7_696root.frontier 0=t7_696jobs := by rfl
theorem t7_696all : t7_696jobs.all (Job.check tree)=true := by
  simp only [t7_696jobs,List.all_append,List.all_nil,t7_696part0,Bool.and_self]
theorem t7_696checked : Checked tree [9,9,6,6,10,7,7] := by
  refine ⟨plan9109,valid9109,t7_696choices,?_⟩
  exact check_of_frontier tree 0 t7_696root t7_696jobs t7_696frontier t7_696all
theorem t7_697choices : plan9110.choices=[9,9,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_697part0 : t7_697jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_697frontier : t7_697root.frontier 0=t7_697jobs := by rfl
theorem t7_697all : t7_697jobs.all (Job.check tree)=true := by
  simp only [t7_697jobs,List.all_append,List.all_nil,t7_697part0,Bool.and_self]
theorem t7_697checked : Checked tree [9,9,6,7,7,7,7] := by
  refine ⟨plan9110,valid9110,t7_697choices,?_⟩
  exact check_of_frontier tree 0 t7_697root t7_697jobs t7_697frontier t7_697all
theorem t7_698choices : plan9111.choices=[9,9,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_698part0 : t7_698jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_698frontier : t7_698root.frontier 0=t7_698jobs := by rfl
theorem t7_698all : t7_698jobs.all (Job.check tree)=true := by
  simp only [t7_698jobs,List.all_append,List.all_nil,t7_698part0,Bool.and_self]
theorem t7_698checked : Checked tree [9,9,6,10,7,7,7] := by
  refine ⟨plan9111,valid9111,t7_698choices,?_⟩
  exact check_of_frontier tree 0 t7_698root t7_698jobs t7_698frontier t7_698all
theorem t7_699choices : plan9112.choices=[9,9,6,10,10,7,7].map (options 7 7) := by rfl


theorem t7_699part0 : t7_699jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_699frontier : t7_699root.frontier 0=t7_699jobs := by rfl
theorem t7_699all : t7_699jobs.all (Job.check tree)=true := by
  simp only [t7_699jobs,List.all_append,List.all_nil,t7_699part0,Bool.and_self]
theorem t7_699checked : Checked tree [9,9,6,10,10,7,7] := by
  refine ⟨plan9112,valid9112,t7_699choices,?_⟩
  exact check_of_frontier tree 0 t7_699root t7_699jobs t7_699frontier t7_699all
theorem t7_700choices : plan9113.choices=[9,9,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_700part0 : t7_700jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_700frontier : t7_700root.frontier 0=t7_700jobs := by rfl
theorem t7_700all : t7_700jobs.all (Job.check tree)=true := by
  simp only [t7_700jobs,List.all_append,List.all_nil,t7_700part0,Bool.and_self]
theorem t7_700checked : Checked tree [9,9,7,7,7,7,7] := by
  refine ⟨plan9113,valid9113,t7_700choices,?_⟩
  exact check_of_frontier tree 0 t7_700root t7_700jobs t7_700frontier t7_700all
theorem t7_701choices : plan8942.choices=[9,9,9,3,7,7,7].map (options 7 6) := by rfl


theorem t7_701part0 : t7_701jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_701frontier : t7_701root.frontier 0=t7_701jobs := by rfl
theorem t7_701all : t7_701jobs.all (Job.check tree)=true := by
  simp only [t7_701jobs,List.all_append,List.all_nil,t7_701part0,Bool.and_self]
theorem t7_701checked : Checked tree [9,9,9,3,7,7,7] := by
  refine ⟨plan8942,valid8942,t7_701choices,?_⟩
  exact check_of_frontier tree 0 t7_701root t7_701jobs t7_701frontier t7_701all
theorem t7_702choices : plan9114.choices=[9,9,9,6,7,7,7].map (options 7 7) := by rfl


theorem t7_702part0 : t7_702jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_702frontier : t7_702root.frontier 0=t7_702jobs := by rfl
theorem t7_702all : t7_702jobs.all (Job.check tree)=true := by
  simp only [t7_702jobs,List.all_append,List.all_nil,t7_702part0,Bool.and_self]
theorem t7_702checked : Checked tree [9,9,9,6,7,7,7] := by
  refine ⟨plan9114,valid9114,t7_702choices,?_⟩
  exact check_of_frontier tree 0 t7_702root t7_702jobs t7_702frontier t7_702all
theorem t7_703choices : plan9115.choices=[9,9,9,7,7,7,7].map (options 7 7) := by rfl


theorem t7_703part0 : t7_703jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_703frontier : t7_703root.frontier 0=t7_703jobs := by rfl
theorem t7_703all : t7_703jobs.all (Job.check tree)=true := by
  simp only [t7_703jobs,List.all_append,List.all_nil,t7_703part0,Bool.and_self]
theorem t7_703checked : Checked tree [9,9,9,7,7,7,7] := by
  refine ⟨plan9115,valid9115,t7_703choices,?_⟩
  exact check_of_frontier tree 0 t7_703root t7_703jobs t7_703frontier t7_703all
theorem t7_704choices : plan9116.choices=[9,9,9,10,7,7,7].map (options 7 7) := by rfl


theorem t7_704part0 : t7_704jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_704frontier : t7_704root.frontier 0=t7_704jobs := by rfl
theorem t7_704all : t7_704jobs.all (Job.check tree)=true := by
  simp only [t7_704jobs,List.all_append,List.all_nil,t7_704part0,Bool.and_self]
theorem t7_704checked : Checked tree [9,9,9,10,7,7,7] := by
  refine ⟨plan9116,valid9116,t7_704choices,?_⟩
  exact check_of_frontier tree 0 t7_704root t7_704jobs t7_704frontier t7_704all
theorem t7_705choices : plan9117.choices=[9,9,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_705part0 : t7_705jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_705frontier : t7_705root.frontier 0=t7_705jobs := by rfl
theorem t7_705all : t7_705jobs.all (Job.check tree)=true := by
  simp only [t7_705jobs,List.all_append,List.all_nil,t7_705part0,Bool.and_self]
theorem t7_705checked : Checked tree [9,9,10,7,7,7,7] := by
  refine ⟨plan9117,valid9117,t7_705choices,?_⟩
  exact check_of_frontier tree 0 t7_705root t7_705jobs t7_705frontier t7_705all
theorem t7_706choices : plan9118.choices=[9,9,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_706part0 : t7_706jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_706frontier : t7_706root.frontier 0=t7_706jobs := by rfl
theorem t7_706all : t7_706jobs.all (Job.check tree)=true := by
  simp only [t7_706jobs,List.all_append,List.all_nil,t7_706part0,Bool.and_self]
theorem t7_706checked : Checked tree [9,9,10,10,7,7,7] := by
  refine ⟨plan9118,valid9118,t7_706choices,?_⟩
  exact check_of_frontier tree 0 t7_706root t7_706jobs t7_706frontier t7_706all
theorem t7_707choices : plan9119.choices=[9,9,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_707part0 : t7_707jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_707frontier : t7_707root.frontier 0=t7_707jobs := by rfl
theorem t7_707all : t7_707jobs.all (Job.check tree)=true := by
  simp only [t7_707jobs,List.all_append,List.all_nil,t7_707part0,Bool.and_self]
theorem t7_707checked : Checked tree [9,9,10,10,10,7,7] := by
  refine ⟨plan9119,valid9119,t7_707choices,?_⟩
  exact check_of_frontier tree 0 t7_707root t7_707jobs t7_707frontier t7_707all
theorem t7_708choices : plan9120.choices=[9,10,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_708part0 : t7_708jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_708frontier : t7_708root.frontier 0=t7_708jobs := by rfl
theorem t7_708all : t7_708jobs.all (Job.check tree)=true := by
  simp only [t7_708jobs,List.all_append,List.all_nil,t7_708part0,Bool.and_self]
theorem t7_708checked : Checked tree [9,10,7,7,7,7,7] := by
  refine ⟨plan9120,valid9120,t7_708choices,?_⟩
  exact check_of_frontier tree 0 t7_708root t7_708jobs t7_708frontier t7_708all
theorem t7_709choices : plan9121.choices=[9,10,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_709part0 : t7_709jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_709frontier : t7_709root.frontier 0=t7_709jobs := by rfl
theorem t7_709all : t7_709jobs.all (Job.check tree)=true := by
  simp only [t7_709jobs,List.all_append,List.all_nil,t7_709part0,Bool.and_self]
theorem t7_709checked : Checked tree [9,10,10,7,7,7,7] := by
  refine ⟨plan9121,valid9121,t7_709choices,?_⟩
  exact check_of_frontier tree 0 t7_709root t7_709jobs t7_709frontier t7_709all
theorem t7_710choices : plan9122.choices=[9,10,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_710part0 : t7_710jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_710frontier : t7_710root.frontier 0=t7_710jobs := by rfl
theorem t7_710all : t7_710jobs.all (Job.check tree)=true := by
  simp only [t7_710jobs,List.all_append,List.all_nil,t7_710part0,Bool.and_self]
theorem t7_710checked : Checked tree [9,10,10,10,7,7,7] := by
  refine ⟨plan9122,valid9122,t7_710choices,?_⟩
  exact check_of_frontier tree 0 t7_710root t7_710jobs t7_710frontier t7_710all
theorem t7_711choices : plan9123.choices=[9,10,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_711part0 : t7_711jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_711frontier : t7_711root.frontier 0=t7_711jobs := by rfl
theorem t7_711all : t7_711jobs.all (Job.check tree)=true := by
  simp only [t7_711jobs,List.all_append,List.all_nil,t7_711part0,Bool.and_self]
theorem t7_711checked : Checked tree [9,10,10,10,10,7,7] := by
  refine ⟨plan9123,valid9123,t7_711choices,?_⟩
  exact check_of_frontier tree 0 t7_711root t7_711jobs t7_711frontier t7_711all
theorem t7_712choices : plan9124.choices=[9,10,10,10,10,10,7].map (options 7 7) := by rfl


theorem t7_712part0 : t7_712jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_712frontier : t7_712root.frontier 0=t7_712jobs := by rfl
theorem t7_712all : t7_712jobs.all (Job.check tree)=true := by
  simp only [t7_712jobs,List.all_append,List.all_nil,t7_712part0,Bool.and_self]
theorem t7_712checked : Checked tree [9,10,10,10,10,10,7] := by
  refine ⟨plan9124,valid9124,t7_712choices,?_⟩
  exact check_of_frontier tree 0 t7_712root t7_712jobs t7_712frontier t7_712all
theorem t7_713choices : plan9125.choices=[10,7,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_713part0 : t7_713jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_713frontier : t7_713root.frontier 0=t7_713jobs := by rfl
theorem t7_713all : t7_713jobs.all (Job.check tree)=true := by
  simp only [t7_713jobs,List.all_append,List.all_nil,t7_713part0,Bool.and_self]
theorem t7_713checked : Checked tree [10,7,7,7,7,7,7] := by
  refine ⟨plan9125,valid9125,t7_713choices,?_⟩
  exact check_of_frontier tree 0 t7_713root t7_713jobs t7_713frontier t7_713all
theorem t7_714choices : plan9126.choices=[10,10,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_714part0 : t7_714jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_714frontier : t7_714root.frontier 0=t7_714jobs := by rfl
theorem t7_714all : t7_714jobs.all (Job.check tree)=true := by
  simp only [t7_714jobs,List.all_append,List.all_nil,t7_714part0,Bool.and_self]
theorem t7_714checked : Checked tree [10,10,7,7,7,7,7] := by
  refine ⟨plan9126,valid9126,t7_714choices,?_⟩
  exact check_of_frontier tree 0 t7_714root t7_714jobs t7_714frontier t7_714all
theorem t7_715choices : plan9127.choices=[10,10,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_715part0 : t7_715jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_715frontier : t7_715root.frontier 0=t7_715jobs := by rfl
theorem t7_715all : t7_715jobs.all (Job.check tree)=true := by
  simp only [t7_715jobs,List.all_append,List.all_nil,t7_715part0,Bool.and_self]
theorem t7_715checked : Checked tree [10,10,10,7,7,7,7] := by
  refine ⟨plan9127,valid9127,t7_715choices,?_⟩
  exact check_of_frontier tree 0 t7_715root t7_715jobs t7_715frontier t7_715all
theorem t7_716choices : plan9128.choices=[10,10,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_716part0 : t7_716jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_716frontier : t7_716root.frontier 0=t7_716jobs := by rfl
theorem t7_716all : t7_716jobs.all (Job.check tree)=true := by
  simp only [t7_716jobs,List.all_append,List.all_nil,t7_716part0,Bool.and_self]
theorem t7_716checked : Checked tree [10,10,10,10,7,7,7] := by
  refine ⟨plan9128,valid9128,t7_716choices,?_⟩
  exact check_of_frontier tree 0 t7_716root t7_716jobs t7_716frontier t7_716all
theorem t7_717choices : plan9129.choices=[10,10,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_717part0 : t7_717jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_717frontier : t7_717root.frontier 0=t7_717jobs := by rfl
theorem t7_717all : t7_717jobs.all (Job.check tree)=true := by
  simp only [t7_717jobs,List.all_append,List.all_nil,t7_717part0,Bool.and_self]
theorem t7_717checked : Checked tree [10,10,10,10,10,7,7] := by
  refine ⟨plan9129,valid9129,t7_717choices,?_⟩
  exact check_of_frontier tree 0 t7_717root t7_717jobs t7_717frontier t7_717all
theorem t7_718choices : plan9130.choices=[10,10,10,10,10,10,7].map (options 7 7) := by rfl


theorem t7_718part0 : t7_718jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_718frontier : t7_718root.frontier 0=t7_718jobs := by rfl
theorem t7_718all : t7_718jobs.all (Job.check tree)=true := by
  simp only [t7_718jobs,List.all_append,List.all_nil,t7_718part0,Bool.and_self]
theorem t7_718checked : Checked tree [10,10,10,10,10,10,7] := by
  refine ⟨plan9130,valid9130,t7_718choices,?_⟩
  exact check_of_frontier tree 0 t7_718root t7_718jobs t7_718frontier t7_718all
theorem t7_719choices : plan9131.choices=[10,10,10,10,10,10,10].map (options 7 7) := by rfl


theorem t7_719part0 : t7_719jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_719frontier : t7_719root.frontier 0=t7_719jobs := by rfl
theorem t7_719all : t7_719jobs.all (Job.check tree)=true := by
  simp only [t7_719jobs,List.all_append,List.all_nil,t7_719part0,Bool.and_self]
theorem t7_719checked : Checked tree [10,10,10,10,10,10,10] := by
  refine ⟨plan9131,valid9131,t7_719choices,?_⟩
  exact check_of_frontier tree 0 t7_719root t7_719jobs t7_719frontier t7_719all
theorem t8_0choices : plan9190.choices=[0,7,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_0part0 : t8_0jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_0frontier : t8_0root.frontier 0=t8_0jobs := by rfl
theorem t8_0all : t8_0jobs.all (Job.check tree)=true := by
  simp only [t8_0jobs,List.all_append,List.all_nil,t8_0part0,Bool.and_self]
theorem t8_0checked : Checked tree [0,7,7,7,7,7,7,7] := by
  refine ⟨plan9190,valid9190,t8_0choices,?_⟩
  exact check_of_frontier tree 0 t8_0root t8_0jobs t8_0frontier t8_0all
theorem t8_1choices : plan9177.choices=[1,3,7,7,7,7,7,7].map (options 8 6) := by rfl


theorem t8_1part0 : t8_1jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_1frontier : t8_1root.frontier 0=t8_1jobs := by rfl
theorem t8_1all : t8_1jobs.all (Job.check tree)=true := by
  simp only [t8_1jobs,List.all_append,List.all_nil,t8_1part0,Bool.and_self]
theorem t8_1checked : Checked tree [1,3,7,7,7,7,7,7] := by
  refine ⟨plan9177,valid9177,t8_1choices,?_⟩
  exact check_of_frontier tree 0 t8_1root t8_1jobs t8_1frontier t8_1all
theorem t8_2choices : plan9191.choices=[1,6,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_2part0 : t8_2jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_2frontier : t8_2root.frontier 0=t8_2jobs := by rfl
theorem t8_2all : t8_2jobs.all (Job.check tree)=true := by
  simp only [t8_2jobs,List.all_append,List.all_nil,t8_2part0,Bool.and_self]
theorem t8_2checked : Checked tree [1,6,7,7,7,7,7,7] := by
  refine ⟨plan9191,valid9191,t8_2choices,?_⟩
  exact check_of_frontier tree 0 t8_2root t8_2jobs t8_2frontier t8_2all
theorem t8_3choices : plan9192.choices=[1,7,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_3part0 : t8_3jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_3frontier : t8_3root.frontier 0=t8_3jobs := by rfl
theorem t8_3all : t8_3jobs.all (Job.check tree)=true := by
  simp only [t8_3jobs,List.all_append,List.all_nil,t8_3part0,Bool.and_self]
theorem t8_3checked : Checked tree [1,7,7,7,7,7,7,7] := by
  refine ⟨plan9192,valid9192,t8_3choices,?_⟩
  exact check_of_frontier tree 0 t8_3root t8_3jobs t8_3frontier t8_3all
theorem t8_4choices : plan9193.choices=[1,10,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_4part0 : t8_4jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_4frontier : t8_4root.frontier 0=t8_4jobs := by rfl
theorem t8_4all : t8_4jobs.all (Job.check tree)=true := by
  simp only [t8_4jobs,List.all_append,List.all_nil,t8_4part0,Bool.and_self]
theorem t8_4checked : Checked tree [1,10,7,7,7,7,7,7] := by
  refine ⟨plan9193,valid9193,t8_4choices,?_⟩
  exact check_of_frontier tree 0 t8_4root t8_4jobs t8_4frontier t8_4all
theorem t8_5choices : plan9178.choices=[2,2,7,7,7,7,7,7].map (options 8 6) := by rfl


theorem t8_5part0 : t8_5jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_5frontier : t8_5root.frontier 0=t8_5jobs := by rfl
theorem t8_5all : t8_5jobs.all (Job.check tree)=true := by
  simp only [t8_5jobs,List.all_append,List.all_nil,t8_5part0,Bool.and_self]
theorem t8_5checked : Checked tree [2,2,7,7,7,7,7,7] := by
  refine ⟨plan9178,valid9178,t8_5choices,?_⟩
  exact check_of_frontier tree 0 t8_5root t8_5jobs t8_5frontier t8_5all
theorem t8_6choices : plan9173.choices=[2,3,3,7,7,7,7,7].map (options 8 5) := by rfl


theorem t8_6part0 : t8_6jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_6frontier : t8_6root.frontier 0=t8_6jobs := by rfl
theorem t8_6all : t8_6jobs.all (Job.check tree)=true := by
  simp only [t8_6jobs,List.all_append,List.all_nil,t8_6part0,Bool.and_self]
theorem t8_6checked : Checked tree [2,3,3,7,7,7,7,7] := by
  refine ⟨plan9173,valid9173,t8_6choices,?_⟩
  exact check_of_frontier tree 0 t8_6root t8_6jobs t8_6frontier t8_6all
theorem t8_7choices : plan9179.choices=[2,3,6,7,7,7,7,7].map (options 8 6) := by rfl


theorem t8_7part0 : t8_7jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_7frontier : t8_7root.frontier 0=t8_7jobs := by rfl
theorem t8_7all : t8_7jobs.all (Job.check tree)=true := by
  simp only [t8_7jobs,List.all_append,List.all_nil,t8_7part0,Bool.and_self]
theorem t8_7checked : Checked tree [2,3,6,7,7,7,7,7] := by
  refine ⟨plan9179,valid9179,t8_7choices,?_⟩
  exact check_of_frontier tree 0 t8_7root t8_7jobs t8_7frontier t8_7all
theorem t8_8choices : plan9180.choices=[2,3,7,7,7,7,7,7].map (options 8 6) := by rfl


theorem t8_8part0 : t8_8jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_8frontier : t8_8root.frontier 0=t8_8jobs := by rfl
theorem t8_8all : t8_8jobs.all (Job.check tree)=true := by
  simp only [t8_8jobs,List.all_append,List.all_nil,t8_8part0,Bool.and_self]
theorem t8_8checked : Checked tree [2,3,7,7,7,7,7,7] := by
  refine ⟨plan9180,valid9180,t8_8choices,?_⟩
  exact check_of_frontier tree 0 t8_8root t8_8jobs t8_8frontier t8_8all
theorem t8_9choices : plan9181.choices=[2,3,10,7,7,7,7,7].map (options 8 6) := by rfl


theorem t8_9part0 : t8_9jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_9frontier : t8_9root.frontier 0=t8_9jobs := by rfl
theorem t8_9all : t8_9jobs.all (Job.check tree)=true := by
  simp only [t8_9jobs,List.all_append,List.all_nil,t8_9part0,Bool.and_self]
theorem t8_9checked : Checked tree [2,3,10,7,7,7,7,7] := by
  refine ⟨plan9181,valid9181,t8_9choices,?_⟩
  exact check_of_frontier tree 0 t8_9root t8_9jobs t8_9frontier t8_9all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks193 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_674checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_675checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_676checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_677checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_678checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_679checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_680checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_663checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_681checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_682checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_683checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_684checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_685checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_686checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_687checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_688checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_689checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_690checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_691checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_692checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_693checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_694checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_695checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_696checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_697checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_698checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_664checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_699checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_700checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_701checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_702checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_703checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_704checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_705checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_706checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_707checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_708checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_709checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_710checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_711checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_712checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_713checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_714checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_665checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_715checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_716checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_717checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_718checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_719checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_0checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_1checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_2checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_3checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_4checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_666checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_5checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_6checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_7checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_8checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_9checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_667checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_668checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_669checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_670checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_671checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_672checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_673checked⟩
