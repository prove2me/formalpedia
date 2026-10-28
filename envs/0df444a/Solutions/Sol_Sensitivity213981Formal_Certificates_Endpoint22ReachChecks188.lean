-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks188
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:18:50.409827+00:00
-- url     : https://prove2.me/submissions/a6c06e3a-92c0-46ee-bf7c-1cf29fc456b2

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks188
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks188
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans092
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans093
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans094
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



theorem valid158 : plan158.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid159 : plan159.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid160 : plan160.Valid := valid_step _ _ _ valid0 (by decide +kernel)
































































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





theorem valid622 : plan622.Valid := valid_step _ _ _ valid158 (by decide +kernel)

theorem valid623 : plan623.Valid := valid_step _ _ _ valid159 (by decide +kernel)

theorem valid624 : plan624.Valid := valid_step _ _ _ valid160 (by decide +kernel)

theorem valid625 : plan625.Valid := valid_step _ _ _ valid159 (by decide +kernel)

theorem valid626 : plan626.Valid := valid_step _ _ _ valid159 (by decide +kernel)

theorem valid627 : plan627.Valid := valid_step _ _ _ valid160 (by decide +kernel)


























































































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













theorem valid1654 : plan1654.Valid := valid_step _ _ _ valid607 (by decide +kernel)













theorem valid1661 : plan1661.Valid := valid_step _ _ _ valid613 (by decide +kernel)





theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)











theorem valid1671 : plan1671.Valid := valid_step _ _ _ valid619 (by decide +kernel)





theorem valid1674 : plan1674.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1675 : plan1675.Valid := valid_step _ _ _ valid619 (by decide +kernel)





theorem valid1678 : plan1678.Valid := valid_step _ _ _ valid622 (by decide +kernel)

theorem valid1679 : plan1679.Valid := valid_step _ _ _ valid623 (by decide +kernel)

theorem valid1680 : plan1680.Valid := valid_step _ _ _ valid624 (by decide +kernel)

theorem valid1681 : plan1681.Valid := valid_step _ _ _ valid625 (by decide +kernel)

theorem valid1682 : plan1682.Valid := valid_step _ _ _ valid626 (by decide +kernel)

theorem valid1683 : plan1683.Valid := valid_step _ _ _ valid627 (by decide +kernel)

theorem valid1684 : plan1684.Valid := valid_step _ _ _ valid625 (by decide +kernel)

theorem valid1685 : plan1685.Valid := valid_step _ _ _ valid625 (by decide +kernel)

theorem valid1686 : plan1686.Valid := valid_step _ _ _ valid626 (by decide +kernel)

theorem valid1687 : plan1687.Valid := valid_step _ _ _ valid627 (by decide +kernel)


















































































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







theorem valid3585 : plan3585.Valid := valid_step _ _ _ valid1654 (by decide +kernel)



































theorem valid3603 : plan3603.Valid := valid_step _ _ _ valid1661 (by decide +kernel)

theorem valid3604 : plan3604.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3605 : plan3605.Valid := valid_step _ _ _ valid1665 (by decide +kernel)





















theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)









theorem valid3621 : plan3621.Valid := valid_step _ _ _ valid1674 (by decide +kernel)







theorem valid3625 : plan3625.Valid := valid_step _ _ _ valid1671 (by decide +kernel)





theorem valid3628 : plan3628.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3629 : plan3629.Valid := valid_step _ _ _ valid1675 (by decide +kernel)





theorem valid3632 : plan3632.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3633 : plan3633.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3634 : plan3634.Valid := valid_step _ _ _ valid1675 (by decide +kernel)





theorem valid3637 : plan3637.Valid := valid_step _ _ _ valid1678 (by decide +kernel)

theorem valid3638 : plan3638.Valid := valid_step _ _ _ valid1679 (by decide +kernel)

theorem valid3639 : plan3639.Valid := valid_step _ _ _ valid1680 (by decide +kernel)

theorem valid3640 : plan3640.Valid := valid_step _ _ _ valid1681 (by decide +kernel)

theorem valid3641 : plan3641.Valid := valid_step _ _ _ valid1682 (by decide +kernel)

theorem valid3642 : plan3642.Valid := valid_step _ _ _ valid1683 (by decide +kernel)

theorem valid3643 : plan3643.Valid := valid_step _ _ _ valid1684 (by decide +kernel)

theorem valid3644 : plan3644.Valid := valid_step _ _ _ valid1685 (by decide +kernel)

theorem valid3645 : plan3645.Valid := valid_step _ _ _ valid1686 (by decide +kernel)

theorem valid3646 : plan3646.Valid := valid_step _ _ _ valid1687 (by decide +kernel)

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

theorem valid6243 : plan6243.Valid := valid_step _ _ _ valid3642 (by decide +kernel)

theorem valid6244 : plan6244.Valid := valid_step _ _ _ valid3643 (by decide +kernel)

theorem valid6245 : plan6245.Valid := valid_step _ _ _ valid3644 (by decide +kernel)

theorem valid6246 : plan6246.Valid := valid_step _ _ _ valid3645 (by decide +kernel)

theorem valid6247 : plan6247.Valid := valid_step _ _ _ valid3646 (by decide +kernel)

theorem valid6248 : plan6248.Valid := valid_step _ _ _ valid3647 (by decide +kernel)

theorem valid6249 : plan6249.Valid := valid_step _ _ _ valid3648 (by decide +kernel)

theorem valid6250 : plan6250.Valid := valid_step _ _ _ valid3649 (by decide +kernel)

theorem valid6251 : plan6251.Valid := valid_step _ _ _ valid3650 (by decide +kernel)

theorem valid6252 : plan6252.Valid := valid_step _ _ _ valid3651 (by decide +kernel)

theorem valid6253 : plan6253.Valid := valid_step _ _ _ valid3647 (by decide +kernel)

theorem valid6254 : plan6254.Valid := valid_step _ _ _ valid3643 (by decide +kernel)

theorem valid6255 : plan6255.Valid := valid_step _ _ _ valid3647 (by decide +kernel)

theorem valid6256 : plan6256.Valid := valid_step _ _ _ valid3648 (by decide +kernel)

theorem valid6257 : plan6257.Valid := valid_step _ _ _ valid3647 (by decide +kernel)

theorem valid6258 : plan6258.Valid := valid_step _ _ _ valid3648 (by decide +kernel)

theorem valid6259 : plan6259.Valid := valid_step _ _ _ valid3649 (by decide +kernel)

theorem valid6260 : plan6260.Valid := valid_step _ _ _ valid3650 (by decide +kernel)

theorem valid6261 : plan6261.Valid := valid_step _ _ _ valid3651 (by decide +kernel)






















































































































































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







theorem valid6137 : plan6137.Valid := valid_step _ _ _ valid3585 (by decide +kernel)














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

























theorem valid6157 : plan6157.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6158 : plan6158.Valid := valid_step _ _ _ valid3603 (by decide +kernel)

theorem valid6159 : plan6159.Valid := valid_step _ _ _ valid3604 (by decide +kernel)

theorem valid6160 : plan6160.Valid := valid_step _ _ _ valid3605 (by decide +kernel)















































































theorem valid6200 : plan6200.Valid := valid_step _ _ _ valid3625 (by decide +kernel)

theorem valid6201 : plan6201.Valid := valid_step _ _ _ valid3628 (by decide +kernel)

theorem valid6202 : plan6202.Valid := valid_step _ _ _ valid3629 (by decide +kernel)

theorem valid6203 : plan6203.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6204 : plan6204.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6205 : plan6205.Valid := valid_step _ _ _ valid3634 (by decide +kernel)

theorem valid6206 : plan6206.Valid := valid_step _ _ _ valid3621 (by decide +kernel)







































theorem valid6226 : plan6226.Valid := valid_step _ _ _ valid3621 (by decide +kernel)

















theorem valid6235 : plan6235.Valid := valid_step _ _ _ valid3643 (by decide +kernel)

theorem valid6236 : plan6236.Valid := valid_step _ _ _ valid3647 (by decide +kernel)

theorem valid6237 : plan6237.Valid := valid_step _ _ _ valid3648 (by decide +kernel)

theorem valid6238 : plan6238.Valid := valid_step _ _ _ valid3637 (by decide +kernel)

theorem valid6239 : plan6239.Valid := valid_step _ _ _ valid3638 (by decide +kernel)

theorem valid6240 : plan6240.Valid := valid_step _ _ _ valid3639 (by decide +kernel)
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





















































































theorem valid8107 : plan8107.Valid := valid_step _ _ _ valid6137 (by decide +kernel)



































































theorem valid8141 : plan8141.Valid := valid_step _ _ _ valid6133 (by decide +kernel)













theorem valid8148 : plan8148.Valid := valid_step _ _ _ valid6157 (by decide +kernel)
























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

theorem valid8353 : plan8353.Valid := valid_step _ _ _ valid6247 (by decide +kernel)

theorem valid8354 : plan8354.Valid := valid_step _ _ _ valid6248 (by decide +kernel)

theorem valid8355 : plan8355.Valid := valid_step _ _ _ valid6249 (by decide +kernel)

theorem valid8356 : plan8356.Valid := valid_step _ _ _ valid6250 (by decide +kernel)

theorem valid8357 : plan8357.Valid := valid_step _ _ _ valid6251 (by decide +kernel)

theorem valid8358 : plan8358.Valid := valid_step _ _ _ valid6252 (by decide +kernel)

theorem valid8359 : plan8359.Valid := valid_step _ _ _ valid6253 (by decide +kernel)

theorem valid8360 : plan8360.Valid := valid_step _ _ _ valid6257 (by decide +kernel)

theorem valid8361 : plan8361.Valid := valid_step _ _ _ valid6258 (by decide +kernel)

theorem valid8362 : plan8362.Valid := valid_step _ _ _ valid6259 (by decide +kernel)

theorem valid8363 : plan8363.Valid := valid_step _ _ _ valid6260 (by decide +kernel)

theorem valid8364 : plan8364.Valid := valid_step _ _ _ valid6261 (by decide +kernel)

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













































































































































































theorem valid8535 : plan8535.Valid := valid_step _ _ _ valid8141 (by decide +kernel)

theorem valid8536 : plan8536.Valid := valid_step _ _ _ valid8107 (by decide +kernel)
















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











































































theorem valid8252 : plan8252.Valid := valid_step _ _ _ valid6203 (by decide +kernel)

theorem valid8253 : plan8253.Valid := valid_step _ _ _ valid6204 (by decide +kernel)

theorem valid8254 : plan8254.Valid := valid_step _ _ _ valid6205 (by decide +kernel)

theorem valid8255 : plan8255.Valid := valid_step _ _ _ valid6206 (by decide +kernel)


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



















theorem valid8266 : plan8266.Valid := valid_step _ _ _ valid6226 (by decide +kernel)

































































theorem valid8299 : plan8299.Valid := valid_step _ _ _ valid6200 (by decide +kernel)

theorem valid8300 : plan8300.Valid := valid_step _ _ _ valid6201 (by decide +kernel)

theorem valid8301 : plan8301.Valid := valid_step _ _ _ valid6202 (by decide +kernel)

theorem valid8302 : plan8302.Valid := valid_step _ _ _ valid6203 (by decide +kernel)

theorem valid8303 : plan8303.Valid := valid_step _ _ _ valid6204 (by decide +kernel)

theorem valid8304 : plan8304.Valid := valid_step _ _ _ valid6205 (by decide +kernel)















theorem valid8312 : plan8312.Valid := valid_step _ _ _ valid6226 (by decide +kernel)































theorem valid8328 : plan8328.Valid := valid_step _ _ _ valid6235 (by decide +kernel)

theorem valid8329 : plan8329.Valid := valid_step _ _ _ valid6236 (by decide +kernel)

theorem valid8330 : plan8330.Valid := valid_step _ _ _ valid6237 (by decide +kernel)

theorem valid8331 : plan8331.Valid := valid_step _ _ _ valid6241 (by decide +kernel)

theorem valid8332 : plan8332.Valid := valid_step _ _ _ valid6244 (by decide +kernel)

theorem valid8333 : plan8333.Valid := valid_step _ _ _ valid6245 (by decide +kernel)

theorem valid8334 : plan8334.Valid := valid_step _ _ _ valid6248 (by decide +kernel)

theorem valid8335 : plan8335.Valid := valid_step _ _ _ valid6249 (by decide +kernel)

theorem valid8336 : plan8336.Valid := valid_step _ _ _ valid6250 (by decide +kernel)

theorem valid8337 : plan8337.Valid := valid_step _ _ _ valid6253 (by decide +kernel)

theorem valid8338 : plan8338.Valid := valid_step _ _ _ valid6254 (by decide +kernel)

theorem valid8339 : plan8339.Valid := valid_step _ _ _ valid6255 (by decide +kernel)

theorem valid8340 : plan8340.Valid := valid_step _ _ _ valid6256 (by decide +kernel)

theorem valid8341 : plan8341.Valid := valid_step _ _ _ valid6257 (by decide +kernel)

theorem valid8342 : plan8342.Valid := valid_step _ _ _ valid6258 (by decide +kernel)

theorem valid8343 : plan8343.Valid := valid_step _ _ _ valid6259 (by decide +kernel)

theorem valid8344 : plan8344.Valid := valid_step _ _ _ valid6238 (by decide +kernel)

theorem valid8345 : plan8345.Valid := valid_step _ _ _ valid6239 (by decide +kernel)

theorem valid8346 : plan8346.Valid := valid_step _ _ _ valid6240 (by decide +kernel)

theorem valid8347 : plan8347.Valid := valid_step _ _ _ valid6241 (by decide +kernel)

theorem valid8348 : plan8348.Valid := valid_step _ _ _ valid6242 (by decide +kernel)

theorem valid8349 : plan8349.Valid := valid_step _ _ _ valid6243 (by decide +kernel)

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















































































theorem valid8680 : plan8680.Valid := valid_step _ _ _ valid8212 (by decide +kernel)

theorem valid8681 : plan8681.Valid := valid_step _ _ _ valid8213 (by decide +kernel)

theorem valid8682 : plan8682.Valid := valid_step _ _ _ valid8214 (by decide +kernel)

theorem valid8683 : plan8683.Valid := valid_step _ _ _ valid8148 (by decide +kernel)










































































































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







































































































theorem valid8884 : plan8884.Valid := valid_step _ _ _ valid8252 (by decide +kernel)

theorem valid8885 : plan8885.Valid := valid_step _ _ _ valid8253 (by decide +kernel)

theorem valid8886 : plan8886.Valid := valid_step _ _ _ valid8254 (by decide +kernel)

theorem valid8887 : plan8887.Valid := valid_step _ _ _ valid8255 (by decide +kernel)

theorem valid8888 : plan8888.Valid := valid_step _ _ _ valid8266 (by decide +kernel)

theorem valid8889 : plan8889.Valid := valid_step _ _ _ valid8299 (by decide +kernel)

theorem valid8890 : plan8890.Valid := valid_step _ _ _ valid8300 (by decide +kernel)

theorem valid8891 : plan8891.Valid := valid_step _ _ _ valid8301 (by decide +kernel)

theorem valid8892 : plan8892.Valid := valid_step _ _ _ valid8302 (by decide +kernel)

theorem valid8893 : plan8893.Valid := valid_step _ _ _ valid8303 (by decide +kernel)

theorem valid8894 : plan8894.Valid := valid_step _ _ _ valid8304 (by decide +kernel)

theorem valid8895 : plan8895.Valid := valid_step _ _ _ valid8312 (by decide +kernel)


































































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





































































































theorem valid8979 : plan8979.Valid := valid_step _ _ _ valid8328 (by decide +kernel)

theorem valid8980 : plan8980.Valid := valid_step _ _ _ valid8329 (by decide +kernel)

theorem valid8981 : plan8981.Valid := valid_step _ _ _ valid8330 (by decide +kernel)

theorem valid8982 : plan8982.Valid := valid_step _ _ _ valid8331 (by decide +kernel)

theorem valid8983 : plan8983.Valid := valid_step _ _ _ valid8332 (by decide +kernel)

theorem valid8984 : plan8984.Valid := valid_step _ _ _ valid8333 (by decide +kernel)

theorem valid8985 : plan8985.Valid := valid_step _ _ _ valid8334 (by decide +kernel)

theorem valid8986 : plan8986.Valid := valid_step _ _ _ valid8335 (by decide +kernel)

theorem valid8987 : plan8987.Valid := valid_step _ _ _ valid8336 (by decide +kernel)

theorem valid8988 : plan8988.Valid := valid_step _ _ _ valid8337 (by decide +kernel)

theorem valid8989 : plan8989.Valid := valid_step _ _ _ valid8338 (by decide +kernel)

theorem valid8990 : plan8990.Valid := valid_step _ _ _ valid8339 (by decide +kernel)

theorem valid8991 : plan8991.Valid := valid_step _ _ _ valid8340 (by decide +kernel)

theorem valid8992 : plan8992.Valid := valid_step _ _ _ valid8341 (by decide +kernel)

theorem valid8993 : plan8993.Valid := valid_step _ _ _ valid8342 (by decide +kernel)

theorem valid8994 : plan8994.Valid := valid_step _ _ _ valid8343 (by decide +kernel)

theorem valid8995 : plan8995.Valid := valid_step _ _ _ valid8345 (by decide +kernel)

theorem valid8996 : plan8996.Valid := valid_step _ _ _ valid8347 (by decide +kernel)

theorem valid8997 : plan8997.Valid := valid_step _ _ _ valid8348 (by decide +kernel)

theorem valid8998 : plan8998.Valid := valid_step _ _ _ valid8350 (by decide +kernel)

theorem valid8999 : plan8999.Valid := valid_step _ _ _ valid8351 (by decide +kernel)

theorem valid9000 : plan9000.Valid := valid_step _ _ _ valid8352 (by decide +kernel)

theorem valid9001 : plan9001.Valid := valid_step _ _ _ valid8354 (by decide +kernel)

theorem valid9002 : plan9002.Valid := valid_step _ _ _ valid8355 (by decide +kernel)

theorem valid9003 : plan9003.Valid := valid_step _ _ _ valid8356 (by decide +kernel)

theorem valid9004 : plan9004.Valid := valid_step _ _ _ valid8357 (by decide +kernel)

theorem valid9005 : plan9005.Valid := valid_step _ _ _ valid8359 (by decide +kernel)

theorem valid9006 : plan9006.Valid := valid_step _ _ _ valid8360 (by decide +kernel)

theorem valid9007 : plan9007.Valid := valid_step _ _ _ valid8361 (by decide +kernel)

theorem valid9008 : plan9008.Valid := valid_step _ _ _ valid8362 (by decide +kernel)

theorem valid9009 : plan9009.Valid := valid_step _ _ _ valid8363 (by decide +kernel)

theorem valid9010 : plan9010.Valid := valid_step _ _ _ valid8365 (by decide +kernel)

theorem valid9011 : plan9011.Valid := valid_step _ _ _ valid8369 (by decide +kernel)

theorem valid9012 : plan9012.Valid := valid_step _ _ _ valid8370 (by decide +kernel)

theorem valid9013 : plan9013.Valid := valid_step _ _ _ valid8371 (by decide +kernel)

theorem valid9014 : plan9014.Valid := valid_step _ _ _ valid8372 (by decide +kernel)

theorem valid9015 : plan9015.Valid := valid_step _ _ _ valid8373 (by decide +kernel)

theorem valid9016 : plan9016.Valid := valid_step _ _ _ valid8374 (by decide +kernel)

theorem valid9017 : plan9017.Valid := valid_step _ _ _ valid8375 (by decide +kernel)

theorem valid9018 : plan9018.Valid := valid_step _ _ _ valid8376 (by decide +kernel)

theorem valid9019 : plan9019.Valid := valid_step _ _ _ valid8377 (by decide +kernel)

theorem valid9020 : plan9020.Valid := valid_step _ _ _ valid8378 (by decide +kernel)

theorem valid9021 : plan9021.Valid := valid_step _ _ _ valid8379 (by decide +kernel)

theorem valid9022 : plan9022.Valid := valid_step _ _ _ valid8380 (by decide +kernel)

theorem valid9023 : plan9023.Valid := valid_step _ _ _ valid8381 (by decide +kernel)

theorem valid9024 : plan9024.Valid := valid_step _ _ _ valid8382 (by decide +kernel)
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

theorem valid9025 : plan9025.Valid := valid_step _ _ _ valid8383 (by decide +kernel)

theorem valid9026 : plan9026.Valid := valid_step _ _ _ valid8384 (by decide +kernel)

theorem valid9027 : plan9027.Valid := valid_step _ _ _ valid8385 (by decide +kernel)

theorem valid9028 : plan9028.Valid := valid_step _ _ _ valid8386 (by decide +kernel)

theorem valid9029 : plan9029.Valid := valid_step _ _ _ valid8344 (by decide +kernel)

theorem valid9030 : plan9030.Valid := valid_step _ _ _ valid8345 (by decide +kernel)

theorem valid9031 : plan9031.Valid := valid_step _ _ _ valid8346 (by decide +kernel)

theorem valid9032 : plan9032.Valid := valid_step _ _ _ valid8347 (by decide +kernel)

theorem valid9033 : plan9033.Valid := valid_step _ _ _ valid8348 (by decide +kernel)

theorem valid9034 : plan9034.Valid := valid_step _ _ _ valid8349 (by decide +kernel)

theorem valid9035 : plan9035.Valid := valid_step _ _ _ valid8350 (by decide +kernel)

theorem valid9036 : plan9036.Valid := valid_step _ _ _ valid8351 (by decide +kernel)

theorem valid9037 : plan9037.Valid := valid_step _ _ _ valid8352 (by decide +kernel)

theorem valid9038 : plan9038.Valid := valid_step _ _ _ valid8353 (by decide +kernel)

theorem valid9039 : plan9039.Valid := valid_step _ _ _ valid8354 (by decide +kernel)

theorem valid9040 : plan9040.Valid := valid_step _ _ _ valid8355 (by decide +kernel)

theorem valid9041 : plan9041.Valid := valid_step _ _ _ valid8356 (by decide +kernel)

theorem valid9042 : plan9042.Valid := valid_step _ _ _ valid8357 (by decide +kernel)

theorem valid9043 : plan9043.Valid := valid_step _ _ _ valid8358 (by decide +kernel)

theorem valid9044 : plan9044.Valid := valid_step _ _ _ valid8359 (by decide +kernel)

theorem valid9045 : plan9045.Valid := valid_step _ _ _ valid8360 (by decide +kernel)

theorem valid9046 : plan9046.Valid := valid_step _ _ _ valid8361 (by decide +kernel)

theorem valid9047 : plan9047.Valid := valid_step _ _ _ valid8362 (by decide +kernel)

theorem valid9048 : plan9048.Valid := valid_step _ _ _ valid8363 (by decide +kernel)

theorem valid9049 : plan9049.Valid := valid_step _ _ _ valid8364 (by decide +kernel)

theorem valid9050 : plan9050.Valid := valid_step _ _ _ valid8365 (by decide +kernel)

theorem valid9051 : plan9051.Valid := valid_step _ _ _ valid8382 (by decide +kernel)

theorem valid9052 : plan9052.Valid := valid_step _ _ _ valid8383 (by decide +kernel)

theorem valid9053 : plan9053.Valid := valid_step _ _ _ valid8384 (by decide +kernel)

theorem valid9054 : plan9054.Valid := valid_step _ _ _ valid8385 (by decide +kernel)

theorem valid9055 : plan9055.Valid := valid_step _ _ _ valid8386 (by decide +kernel)

theorem valid9056 : plan9056.Valid := valid_step _ _ _ valid8387 (by decide +kernel)

theorem valid9057 : plan9057.Valid := valid_step _ _ _ valid8365 (by decide +kernel)






























































































































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
theorem t7_463choices : plan8884.choices=[5,5,3,7,7,7,7].map (options 7 6) := by rfl


theorem t7_463part0 : t7_463jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_463frontier : t7_463root.frontier 0=t7_463jobs := by rfl
theorem t7_463all : t7_463jobs.all (Job.check tree)=true := by
  simp only [t7_463jobs,List.all_append,List.all_nil,t7_463part0,Bool.and_self]
theorem t7_463checked : Checked tree [5,5,3,7,7,7,7] := by
  refine ⟨plan8884,valid8884,t7_463choices,?_⟩
  exact check_of_frontier tree 0 t7_463root t7_463jobs t7_463frontier t7_463all
theorem t7_464choices : plan8885.choices=[5,5,3,10,7,7,7].map (options 7 6) := by rfl


theorem t7_464part0 : t7_464jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_464frontier : t7_464root.frontier 0=t7_464jobs := by rfl
theorem t7_464all : t7_464jobs.all (Job.check tree)=true := by
  simp only [t7_464jobs,List.all_append,List.all_nil,t7_464part0,Bool.and_self]
theorem t7_464checked : Checked tree [5,5,3,10,7,7,7] := by
  refine ⟨plan8885,valid8885,t7_464choices,?_⟩
  exact check_of_frontier tree 0 t7_464root t7_464jobs t7_464frontier t7_464all
theorem t7_465choices : plan8886.choices=[5,5,3,10,10,7,7].map (options 7 6) := by rfl


theorem t7_465part0 : t7_465jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_465frontier : t7_465root.frontier 0=t7_465jobs := by rfl
theorem t7_465all : t7_465jobs.all (Job.check tree)=true := by
  simp only [t7_465jobs,List.all_append,List.all_nil,t7_465part0,Bool.and_self]
theorem t7_465checked : Checked tree [5,5,3,10,10,7,7] := by
  refine ⟨plan8886,valid8886,t7_465choices,?_⟩
  exact check_of_frontier tree 0 t7_465root t7_465jobs t7_465frontier t7_465all
theorem t7_466choices : plan8887.choices=[5,5,5,3,7,7,7].map (options 7 6) := by rfl


theorem t7_466part0 : t7_466jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_466frontier : t7_466root.frontier 0=t7_466jobs := by rfl
theorem t7_466all : t7_466jobs.all (Job.check tree)=true := by
  simp only [t7_466jobs,List.all_append,List.all_nil,t7_466part0,Bool.and_self]
theorem t7_466checked : Checked tree [5,5,5,3,7,7,7] := by
  refine ⟨plan8887,valid8887,t7_466choices,?_⟩
  exact check_of_frontier tree 0 t7_466root t7_466jobs t7_466frontier t7_466all
theorem t7_467choices : plan8979.choices=[5,5,5,6,7,7,7].map (options 7 7) := by rfl


theorem t7_467part0 : t7_467jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_467frontier : t7_467root.frontier 0=t7_467jobs := by rfl
theorem t7_467all : t7_467jobs.all (Job.check tree)=true := by
  simp only [t7_467jobs,List.all_append,List.all_nil,t7_467part0,Bool.and_self]
theorem t7_467checked : Checked tree [5,5,5,6,7,7,7] := by
  refine ⟨plan8979,valid8979,t7_467choices,?_⟩
  exact check_of_frontier tree 0 t7_467root t7_467jobs t7_467frontier t7_467all
theorem t7_468choices : plan8980.choices=[5,5,5,7,7,7,7].map (options 7 7) := by rfl


theorem t7_468part0 : t7_468jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_468frontier : t7_468root.frontier 0=t7_468jobs := by rfl
theorem t7_468all : t7_468jobs.all (Job.check tree)=true := by
  simp only [t7_468jobs,List.all_append,List.all_nil,t7_468part0,Bool.and_self]
theorem t7_468checked : Checked tree [5,5,5,7,7,7,7] := by
  refine ⟨plan8980,valid8980,t7_468choices,?_⟩
  exact check_of_frontier tree 0 t7_468root t7_468jobs t7_468frontier t7_468all
theorem t7_469choices : plan8981.choices=[5,5,5,10,7,7,7].map (options 7 7) := by rfl


theorem t7_469part0 : t7_469jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_469frontier : t7_469root.frontier 0=t7_469jobs := by rfl
theorem t7_469all : t7_469jobs.all (Job.check tree)=true := by
  simp only [t7_469jobs,List.all_append,List.all_nil,t7_469part0,Bool.and_self]
theorem t7_469checked : Checked tree [5,5,5,10,7,7,7] := by
  refine ⟨plan8981,valid8981,t7_469choices,?_⟩
  exact check_of_frontier tree 0 t7_469root t7_469jobs t7_469frontier t7_469all
theorem t7_470choices : plan8982.choices=[5,5,6,6,6,7,7].map (options 7 7) := by rfl


theorem t7_470part0 : t7_470jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_470frontier : t7_470root.frontier 0=t7_470jobs := by rfl
theorem t7_470all : t7_470jobs.all (Job.check tree)=true := by
  simp only [t7_470jobs,List.all_append,List.all_nil,t7_470part0,Bool.and_self]
theorem t7_470checked : Checked tree [5,5,6,6,6,7,7] := by
  refine ⟨plan8982,valid8982,t7_470choices,?_⟩
  exact check_of_frontier tree 0 t7_470root t7_470jobs t7_470frontier t7_470all
theorem t7_471choices : plan8983.choices=[5,5,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_471part0 : t7_471jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_471frontier : t7_471root.frontier 0=t7_471jobs := by rfl
theorem t7_471all : t7_471jobs.all (Job.check tree)=true := by
  simp only [t7_471jobs,List.all_append,List.all_nil,t7_471part0,Bool.and_self]
theorem t7_471checked : Checked tree [5,5,6,6,7,7,7] := by
  refine ⟨plan8983,valid8983,t7_471choices,?_⟩
  exact check_of_frontier tree 0 t7_471root t7_471jobs t7_471frontier t7_471all
theorem t7_472choices : plan8984.choices=[5,5,6,6,10,7,7].map (options 7 7) := by rfl


theorem t7_472part0 : t7_472jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_472frontier : t7_472root.frontier 0=t7_472jobs := by rfl
theorem t7_472all : t7_472jobs.all (Job.check tree)=true := by
  simp only [t7_472jobs,List.all_append,List.all_nil,t7_472part0,Bool.and_self]
theorem t7_472checked : Checked tree [5,5,6,6,10,7,7] := by
  refine ⟨plan8984,valid8984,t7_472choices,?_⟩
  exact check_of_frontier tree 0 t7_472root t7_472jobs t7_472frontier t7_472all
theorem t7_473choices : plan8985.choices=[5,5,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_473part0 : t7_473jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_473frontier : t7_473root.frontier 0=t7_473jobs := by rfl
theorem t7_473all : t7_473jobs.all (Job.check tree)=true := by
  simp only [t7_473jobs,List.all_append,List.all_nil,t7_473part0,Bool.and_self]
theorem t7_473checked : Checked tree [5,5,6,7,7,7,7] := by
  refine ⟨plan8985,valid8985,t7_473choices,?_⟩
  exact check_of_frontier tree 0 t7_473root t7_473jobs t7_473frontier t7_473all
theorem t7_474choices : plan8986.choices=[5,5,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_474part0 : t7_474jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_474frontier : t7_474root.frontier 0=t7_474jobs := by rfl
theorem t7_474all : t7_474jobs.all (Job.check tree)=true := by
  simp only [t7_474jobs,List.all_append,List.all_nil,t7_474part0,Bool.and_self]
theorem t7_474checked : Checked tree [5,5,6,10,7,7,7] := by
  refine ⟨plan8986,valid8986,t7_474choices,?_⟩
  exact check_of_frontier tree 0 t7_474root t7_474jobs t7_474frontier t7_474all
theorem t7_475choices : plan8987.choices=[5,5,6,10,10,7,7].map (options 7 7) := by rfl


theorem t7_475part0 : t7_475jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_475frontier : t7_475root.frontier 0=t7_475jobs := by rfl
theorem t7_475all : t7_475jobs.all (Job.check tree)=true := by
  simp only [t7_475jobs,List.all_append,List.all_nil,t7_475part0,Bool.and_self]
theorem t7_475checked : Checked tree [5,5,6,10,10,7,7] := by
  refine ⟨plan8987,valid8987,t7_475choices,?_⟩
  exact check_of_frontier tree 0 t7_475root t7_475jobs t7_475frontier t7_475all
theorem t7_476choices : plan8988.choices=[5,5,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_476part0 : t7_476jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_476frontier : t7_476root.frontier 0=t7_476jobs := by rfl
theorem t7_476all : t7_476jobs.all (Job.check tree)=true := by
  simp only [t7_476jobs,List.all_append,List.all_nil,t7_476part0,Bool.and_self]
theorem t7_476checked : Checked tree [5,5,7,7,7,7,7] := by
  refine ⟨plan8988,valid8988,t7_476choices,?_⟩
  exact check_of_frontier tree 0 t7_476root t7_476jobs t7_476frontier t7_476all
theorem t7_477choices : plan8888.choices=[5,5,9,3,7,7,7].map (options 7 6) := by rfl


theorem t7_477part0 : t7_477jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_477frontier : t7_477root.frontier 0=t7_477jobs := by rfl
theorem t7_477all : t7_477jobs.all (Job.check tree)=true := by
  simp only [t7_477jobs,List.all_append,List.all_nil,t7_477part0,Bool.and_self]
theorem t7_477checked : Checked tree [5,5,9,3,7,7,7] := by
  refine ⟨plan8888,valid8888,t7_477choices,?_⟩
  exact check_of_frontier tree 0 t7_477root t7_477jobs t7_477frontier t7_477all
theorem t7_478choices : plan8989.choices=[5,5,9,6,7,7,7].map (options 7 7) := by rfl


theorem t7_478part0 : t7_478jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_478frontier : t7_478root.frontier 0=t7_478jobs := by rfl
theorem t7_478all : t7_478jobs.all (Job.check tree)=true := by
  simp only [t7_478jobs,List.all_append,List.all_nil,t7_478part0,Bool.and_self]
theorem t7_478checked : Checked tree [5,5,9,6,7,7,7] := by
  refine ⟨plan8989,valid8989,t7_478choices,?_⟩
  exact check_of_frontier tree 0 t7_478root t7_478jobs t7_478frontier t7_478all
theorem t7_479choices : plan8990.choices=[5,5,9,7,7,7,7].map (options 7 7) := by rfl


theorem t7_479part0 : t7_479jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_479frontier : t7_479root.frontier 0=t7_479jobs := by rfl
theorem t7_479all : t7_479jobs.all (Job.check tree)=true := by
  simp only [t7_479jobs,List.all_append,List.all_nil,t7_479part0,Bool.and_self]
theorem t7_479checked : Checked tree [5,5,9,7,7,7,7] := by
  refine ⟨plan8990,valid8990,t7_479choices,?_⟩
  exact check_of_frontier tree 0 t7_479root t7_479jobs t7_479frontier t7_479all
theorem t7_480choices : plan8991.choices=[5,5,9,10,7,7,7].map (options 7 7) := by rfl


theorem t7_480part0 : t7_480jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_480frontier : t7_480root.frontier 0=t7_480jobs := by rfl
theorem t7_480all : t7_480jobs.all (Job.check tree)=true := by
  simp only [t7_480jobs,List.all_append,List.all_nil,t7_480part0,Bool.and_self]
theorem t7_480checked : Checked tree [5,5,9,10,7,7,7] := by
  refine ⟨plan8991,valid8991,t7_480choices,?_⟩
  exact check_of_frontier tree 0 t7_480root t7_480jobs t7_480frontier t7_480all
theorem t7_481choices : plan8992.choices=[5,5,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_481part0 : t7_481jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_481frontier : t7_481root.frontier 0=t7_481jobs := by rfl
theorem t7_481all : t7_481jobs.all (Job.check tree)=true := by
  simp only [t7_481jobs,List.all_append,List.all_nil,t7_481part0,Bool.and_self]
theorem t7_481checked : Checked tree [5,5,10,7,7,7,7] := by
  refine ⟨plan8992,valid8992,t7_481choices,?_⟩
  exact check_of_frontier tree 0 t7_481root t7_481jobs t7_481frontier t7_481all
theorem t7_482choices : plan8993.choices=[5,5,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_482part0 : t7_482jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_482frontier : t7_482root.frontier 0=t7_482jobs := by rfl
theorem t7_482all : t7_482jobs.all (Job.check tree)=true := by
  simp only [t7_482jobs,List.all_append,List.all_nil,t7_482part0,Bool.and_self]
theorem t7_482checked : Checked tree [5,5,10,10,7,7,7] := by
  refine ⟨plan8993,valid8993,t7_482choices,?_⟩
  exact check_of_frontier tree 0 t7_482root t7_482jobs t7_482frontier t7_482all
theorem t7_483choices : plan8994.choices=[5,5,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_483part0 : t7_483jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_483frontier : t7_483root.frontier 0=t7_483jobs := by rfl
theorem t7_483all : t7_483jobs.all (Job.check tree)=true := by
  simp only [t7_483jobs,List.all_append,List.all_nil,t7_483part0,Bool.and_self]
theorem t7_483checked : Checked tree [5,5,10,10,10,7,7] := by
  refine ⟨plan8994,valid8994,t7_483choices,?_⟩
  exact check_of_frontier tree 0 t7_483root t7_483jobs t7_483frontier t7_483all
theorem t7_484choices : plan8995.choices=[5,6,6,6,6,6,7].map (options 7 7) := by rfl


theorem t7_484part0 : t7_484jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_484frontier : t7_484root.frontier 0=t7_484jobs := by rfl
theorem t7_484all : t7_484jobs.all (Job.check tree)=true := by
  simp only [t7_484jobs,List.all_append,List.all_nil,t7_484part0,Bool.and_self]
theorem t7_484checked : Checked tree [5,6,6,6,6,6,7] := by
  refine ⟨plan8995,valid8995,t7_484choices,?_⟩
  exact check_of_frontier tree 0 t7_484root t7_484jobs t7_484frontier t7_484all
theorem t7_485choices : plan8996.choices=[5,6,6,6,6,7,7].map (options 7 7) := by rfl


theorem t7_485part0 : t7_485jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_485frontier : t7_485root.frontier 0=t7_485jobs := by rfl
theorem t7_485all : t7_485jobs.all (Job.check tree)=true := by
  simp only [t7_485jobs,List.all_append,List.all_nil,t7_485part0,Bool.and_self]
theorem t7_485checked : Checked tree [5,6,6,6,6,7,7] := by
  refine ⟨plan8996,valid8996,t7_485choices,?_⟩
  exact check_of_frontier tree 0 t7_485root t7_485jobs t7_485frontier t7_485all
theorem t7_486choices : plan8997.choices=[5,6,6,6,6,10,7].map (options 7 7) := by rfl


theorem t7_486part0 : t7_486jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_486frontier : t7_486root.frontier 0=t7_486jobs := by rfl
theorem t7_486all : t7_486jobs.all (Job.check tree)=true := by
  simp only [t7_486jobs,List.all_append,List.all_nil,t7_486part0,Bool.and_self]
theorem t7_486checked : Checked tree [5,6,6,6,6,10,7] := by
  refine ⟨plan8997,valid8997,t7_486choices,?_⟩
  exact check_of_frontier tree 0 t7_486root t7_486jobs t7_486frontier t7_486all
theorem t7_487choices : plan8998.choices=[5,6,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_487part0 : t7_487jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_487frontier : t7_487root.frontier 0=t7_487jobs := by rfl
theorem t7_487all : t7_487jobs.all (Job.check tree)=true := by
  simp only [t7_487jobs,List.all_append,List.all_nil,t7_487part0,Bool.and_self]
theorem t7_487checked : Checked tree [5,6,6,6,7,7,7] := by
  refine ⟨plan8998,valid8998,t7_487choices,?_⟩
  exact check_of_frontier tree 0 t7_487root t7_487jobs t7_487frontier t7_487all
theorem t7_488choices : plan8999.choices=[5,6,6,6,10,7,7].map (options 7 7) := by rfl


theorem t7_488part0 : t7_488jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_488frontier : t7_488root.frontier 0=t7_488jobs := by rfl
theorem t7_488all : t7_488jobs.all (Job.check tree)=true := by
  simp only [t7_488jobs,List.all_append,List.all_nil,t7_488part0,Bool.and_self]
theorem t7_488checked : Checked tree [5,6,6,6,10,7,7] := by
  refine ⟨plan8999,valid8999,t7_488choices,?_⟩
  exact check_of_frontier tree 0 t7_488root t7_488jobs t7_488frontier t7_488all
theorem t7_489choices : plan9000.choices=[5,6,6,6,10,10,7].map (options 7 7) := by rfl


theorem t7_489part0 : t7_489jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_489frontier : t7_489root.frontier 0=t7_489jobs := by rfl
theorem t7_489all : t7_489jobs.all (Job.check tree)=true := by
  simp only [t7_489jobs,List.all_append,List.all_nil,t7_489part0,Bool.and_self]
theorem t7_489checked : Checked tree [5,6,6,6,10,10,7] := by
  refine ⟨plan9000,valid9000,t7_489choices,?_⟩
  exact check_of_frontier tree 0 t7_489root t7_489jobs t7_489frontier t7_489all
theorem t7_490choices : plan9001.choices=[5,6,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_490part0 : t7_490jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_490frontier : t7_490root.frontier 0=t7_490jobs := by rfl
theorem t7_490all : t7_490jobs.all (Job.check tree)=true := by
  simp only [t7_490jobs,List.all_append,List.all_nil,t7_490part0,Bool.and_self]
theorem t7_490checked : Checked tree [5,6,6,7,7,7,7] := by
  refine ⟨plan9001,valid9001,t7_490choices,?_⟩
  exact check_of_frontier tree 0 t7_490root t7_490jobs t7_490frontier t7_490all
theorem t7_491choices : plan9002.choices=[5,6,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_491part0 : t7_491jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_491frontier : t7_491root.frontier 0=t7_491jobs := by rfl
theorem t7_491all : t7_491jobs.all (Job.check tree)=true := by
  simp only [t7_491jobs,List.all_append,List.all_nil,t7_491part0,Bool.and_self]
theorem t7_491checked : Checked tree [5,6,6,10,7,7,7] := by
  refine ⟨plan9002,valid9002,t7_491choices,?_⟩
  exact check_of_frontier tree 0 t7_491root t7_491jobs t7_491frontier t7_491all
theorem t7_492choices : plan9003.choices=[5,6,6,10,10,7,7].map (options 7 7) := by rfl


theorem t7_492part0 : t7_492jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_492frontier : t7_492root.frontier 0=t7_492jobs := by rfl
theorem t7_492all : t7_492jobs.all (Job.check tree)=true := by
  simp only [t7_492jobs,List.all_append,List.all_nil,t7_492part0,Bool.and_self]
theorem t7_492checked : Checked tree [5,6,6,10,10,7,7] := by
  refine ⟨plan9003,valid9003,t7_492choices,?_⟩
  exact check_of_frontier tree 0 t7_492root t7_492jobs t7_492frontier t7_492all
theorem t7_493choices : plan9004.choices=[5,6,6,10,10,10,7].map (options 7 7) := by rfl


theorem t7_493part0 : t7_493jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_493frontier : t7_493root.frontier 0=t7_493jobs := by rfl
theorem t7_493all : t7_493jobs.all (Job.check tree)=true := by
  simp only [t7_493jobs,List.all_append,List.all_nil,t7_493part0,Bool.and_self]
theorem t7_493checked : Checked tree [5,6,6,10,10,10,7] := by
  refine ⟨plan9004,valid9004,t7_493choices,?_⟩
  exact check_of_frontier tree 0 t7_493root t7_493jobs t7_493frontier t7_493all
theorem t7_494choices : plan9005.choices=[5,6,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_494part0 : t7_494jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_494frontier : t7_494root.frontier 0=t7_494jobs := by rfl
theorem t7_494all : t7_494jobs.all (Job.check tree)=true := by
  simp only [t7_494jobs,List.all_append,List.all_nil,t7_494part0,Bool.and_self]
theorem t7_494checked : Checked tree [5,6,7,7,7,7,7] := by
  refine ⟨plan9005,valid9005,t7_494choices,?_⟩
  exact check_of_frontier tree 0 t7_494root t7_494jobs t7_494frontier t7_494all
theorem t7_495choices : plan9006.choices=[5,6,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_495part0 : t7_495jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_495frontier : t7_495root.frontier 0=t7_495jobs := by rfl
theorem t7_495all : t7_495jobs.all (Job.check tree)=true := by
  simp only [t7_495jobs,List.all_append,List.all_nil,t7_495part0,Bool.and_self]
theorem t7_495checked : Checked tree [5,6,10,7,7,7,7] := by
  refine ⟨plan9006,valid9006,t7_495choices,?_⟩
  exact check_of_frontier tree 0 t7_495root t7_495jobs t7_495frontier t7_495all
theorem t7_496choices : plan9007.choices=[5,6,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_496part0 : t7_496jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_496frontier : t7_496root.frontier 0=t7_496jobs := by rfl
theorem t7_496all : t7_496jobs.all (Job.check tree)=true := by
  simp only [t7_496jobs,List.all_append,List.all_nil,t7_496part0,Bool.and_self]
theorem t7_496checked : Checked tree [5,6,10,10,7,7,7] := by
  refine ⟨plan9007,valid9007,t7_496choices,?_⟩
  exact check_of_frontier tree 0 t7_496root t7_496jobs t7_496frontier t7_496all
theorem t7_497choices : plan9008.choices=[5,6,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_497part0 : t7_497jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_497frontier : t7_497root.frontier 0=t7_497jobs := by rfl
theorem t7_497all : t7_497jobs.all (Job.check tree)=true := by
  simp only [t7_497jobs,List.all_append,List.all_nil,t7_497part0,Bool.and_self]
theorem t7_497checked : Checked tree [5,6,10,10,10,7,7] := by
  refine ⟨plan9008,valid9008,t7_497choices,?_⟩
  exact check_of_frontier tree 0 t7_497root t7_497jobs t7_497frontier t7_497all
theorem t7_498choices : plan9009.choices=[5,6,10,10,10,10,7].map (options 7 7) := by rfl


theorem t7_498part0 : t7_498jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_498frontier : t7_498root.frontier 0=t7_498jobs := by rfl
theorem t7_498all : t7_498jobs.all (Job.check tree)=true := by
  simp only [t7_498jobs,List.all_append,List.all_nil,t7_498part0,Bool.and_self]
theorem t7_498checked : Checked tree [5,6,10,10,10,10,7] := by
  refine ⟨plan9009,valid9009,t7_498choices,?_⟩
  exact check_of_frontier tree 0 t7_498root t7_498jobs t7_498frontier t7_498all
theorem t7_499choices : plan9010.choices=[5,7,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_499part0 : t7_499jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_499frontier : t7_499root.frontier 0=t7_499jobs := by rfl
theorem t7_499all : t7_499jobs.all (Job.check tree)=true := by
  simp only [t7_499jobs,List.all_append,List.all_nil,t7_499part0,Bool.and_self]
theorem t7_499checked : Checked tree [5,7,7,7,7,7,7] := by
  refine ⟨plan9010,valid9010,t7_499choices,?_⟩
  exact check_of_frontier tree 0 t7_499root t7_499jobs t7_499frontier t7_499all
theorem t7_500choices : plan8535.choices=[5,9,3,3,3,7,7].map (options 7 4) := by rfl


theorem t7_500part0 : t7_500jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_500frontier : t7_500root.frontier 0=t7_500jobs := by rfl
theorem t7_500all : t7_500jobs.all (Job.check tree)=true := by
  simp only [t7_500jobs,List.all_append,List.all_nil,t7_500part0,Bool.and_self]
theorem t7_500checked : Checked tree [5,9,3,3,3,7,7] := by
  refine ⟨plan8535,valid8535,t7_500choices,?_⟩
  exact check_of_frontier tree 0 t7_500root t7_500jobs t7_500frontier t7_500all
theorem t7_501choices : plan8680.choices=[5,9,3,3,6,7,7].map (options 7 5) := by rfl


theorem t7_501part0 : t7_501jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_501frontier : t7_501root.frontier 0=t7_501jobs := by rfl
theorem t7_501all : t7_501jobs.all (Job.check tree)=true := by
  simp only [t7_501jobs,List.all_append,List.all_nil,t7_501part0,Bool.and_self]
theorem t7_501checked : Checked tree [5,9,3,3,6,7,7] := by
  refine ⟨plan8680,valid8680,t7_501choices,?_⟩
  exact check_of_frontier tree 0 t7_501root t7_501jobs t7_501frontier t7_501all
theorem t7_502choices : plan8681.choices=[5,9,3,3,7,7,7].map (options 7 5) := by rfl


theorem t7_502part0 : t7_502jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_502part1 : t7_502jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_502frontier : t7_502root.frontier 1=t7_502jobs := by rfl
theorem t7_502all : t7_502jobs.all (Job.check tree)=true := by
  simp only [t7_502jobs,List.all_append,List.all_nil,t7_502part0,t7_502part1,Bool.and_self]
theorem t7_502checked : Checked tree [5,9,3,3,7,7,7] := by
  refine ⟨plan8681,valid8681,t7_502choices,?_⟩
  exact check_of_frontier tree 1 t7_502root t7_502jobs t7_502frontier t7_502all
theorem t7_503choices : plan8682.choices=[5,9,3,3,10,7,7].map (options 7 5) := by rfl


theorem t7_503part0 : t7_503jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_503frontier : t7_503root.frontier 0=t7_503jobs := by rfl
theorem t7_503all : t7_503jobs.all (Job.check tree)=true := by
  simp only [t7_503jobs,List.all_append,List.all_nil,t7_503part0,Bool.and_self]
theorem t7_503checked : Checked tree [5,9,3,3,10,7,7] := by
  refine ⟨plan8682,valid8682,t7_503choices,?_⟩
  exact check_of_frontier tree 0 t7_503root t7_503jobs t7_503frontier t7_503all
theorem t7_504choices : plan8889.choices=[5,9,3,6,6,7,7].map (options 7 6) := by rfl


theorem t7_504part0 : t7_504jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_504frontier : t7_504root.frontier 0=t7_504jobs := by rfl
theorem t7_504all : t7_504jobs.all (Job.check tree)=true := by
  simp only [t7_504jobs,List.all_append,List.all_nil,t7_504part0,Bool.and_self]
theorem t7_504checked : Checked tree [5,9,3,6,6,7,7] := by
  refine ⟨plan8889,valid8889,t7_504choices,?_⟩
  exact check_of_frontier tree 0 t7_504root t7_504jobs t7_504frontier t7_504all
theorem t7_505choices : plan8890.choices=[5,9,3,6,7,7,7].map (options 7 6) := by rfl


theorem t7_505part0 : t7_505jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_505frontier : t7_505root.frontier 0=t7_505jobs := by rfl
theorem t7_505all : t7_505jobs.all (Job.check tree)=true := by
  simp only [t7_505jobs,List.all_append,List.all_nil,t7_505part0,Bool.and_self]
theorem t7_505checked : Checked tree [5,9,3,6,7,7,7] := by
  refine ⟨plan8890,valid8890,t7_505choices,?_⟩
  exact check_of_frontier tree 0 t7_505root t7_505jobs t7_505frontier t7_505all
theorem t7_506choices : plan8891.choices=[5,9,3,6,10,7,7].map (options 7 6) := by rfl


theorem t7_506part0 : t7_506jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_506frontier : t7_506root.frontier 0=t7_506jobs := by rfl
theorem t7_506all : t7_506jobs.all (Job.check tree)=true := by
  simp only [t7_506jobs,List.all_append,List.all_nil,t7_506part0,Bool.and_self]
theorem t7_506checked : Checked tree [5,9,3,6,10,7,7] := by
  refine ⟨plan8891,valid8891,t7_506choices,?_⟩
  exact check_of_frontier tree 0 t7_506root t7_506jobs t7_506frontier t7_506all
theorem t7_507choices : plan8892.choices=[5,9,3,7,7,7,7].map (options 7 6) := by rfl


theorem t7_507part0 : t7_507jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_507part1 : t7_507jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_507frontier : t7_507root.frontier 1=t7_507jobs := by rfl
theorem t7_507all : t7_507jobs.all (Job.check tree)=true := by
  simp only [t7_507jobs,List.all_append,List.all_nil,t7_507part0,t7_507part1,Bool.and_self]
theorem t7_507checked : Checked tree [5,9,3,7,7,7,7] := by
  refine ⟨plan8892,valid8892,t7_507choices,?_⟩
  exact check_of_frontier tree 1 t7_507root t7_507jobs t7_507frontier t7_507all
theorem t7_508choices : plan8893.choices=[5,9,3,10,7,7,7].map (options 7 6) := by rfl


theorem t7_508part0 : t7_508jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_508frontier : t7_508root.frontier 0=t7_508jobs := by rfl
theorem t7_508all : t7_508jobs.all (Job.check tree)=true := by
  simp only [t7_508jobs,List.all_append,List.all_nil,t7_508part0,Bool.and_self]
theorem t7_508checked : Checked tree [5,9,3,10,7,7,7] := by
  refine ⟨plan8893,valid8893,t7_508choices,?_⟩
  exact check_of_frontier tree 0 t7_508root t7_508jobs t7_508frontier t7_508all
theorem t7_509choices : plan8894.choices=[5,9,3,10,10,7,7].map (options 7 6) := by rfl


theorem t7_509part0 : t7_509jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_509frontier : t7_509root.frontier 0=t7_509jobs := by rfl
theorem t7_509all : t7_509jobs.all (Job.check tree)=true := by
  simp only [t7_509jobs,List.all_append,List.all_nil,t7_509part0,Bool.and_self]
theorem t7_509checked : Checked tree [5,9,3,10,10,7,7] := by
  refine ⟨plan8894,valid8894,t7_509choices,?_⟩
  exact check_of_frontier tree 0 t7_509root t7_509jobs t7_509frontier t7_509all
theorem t7_510choices : plan9011.choices=[5,9,6,6,6,7,7].map (options 7 7) := by rfl


theorem t7_510part0 : t7_510jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_510frontier : t7_510root.frontier 0=t7_510jobs := by rfl
theorem t7_510all : t7_510jobs.all (Job.check tree)=true := by
  simp only [t7_510jobs,List.all_append,List.all_nil,t7_510part0,Bool.and_self]
theorem t7_510checked : Checked tree [5,9,6,6,6,7,7] := by
  refine ⟨plan9011,valid9011,t7_510choices,?_⟩
  exact check_of_frontier tree 0 t7_510root t7_510jobs t7_510frontier t7_510all
theorem t7_511choices : plan9012.choices=[5,9,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_511part0 : t7_511jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_511frontier : t7_511root.frontier 0=t7_511jobs := by rfl
theorem t7_511all : t7_511jobs.all (Job.check tree)=true := by
  simp only [t7_511jobs,List.all_append,List.all_nil,t7_511part0,Bool.and_self]
theorem t7_511checked : Checked tree [5,9,6,6,7,7,7] := by
  refine ⟨plan9012,valid9012,t7_511choices,?_⟩
  exact check_of_frontier tree 0 t7_511root t7_511jobs t7_511frontier t7_511all
theorem t7_512choices : plan9013.choices=[5,9,6,6,10,7,7].map (options 7 7) := by rfl


theorem t7_512part0 : t7_512jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_512frontier : t7_512root.frontier 0=t7_512jobs := by rfl
theorem t7_512all : t7_512jobs.all (Job.check tree)=true := by
  simp only [t7_512jobs,List.all_append,List.all_nil,t7_512part0,Bool.and_self]
theorem t7_512checked : Checked tree [5,9,6,6,10,7,7] := by
  refine ⟨plan9013,valid9013,t7_512choices,?_⟩
  exact check_of_frontier tree 0 t7_512root t7_512jobs t7_512frontier t7_512all
theorem t7_513choices : plan9014.choices=[5,9,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_513part0 : t7_513jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_513frontier : t7_513root.frontier 0=t7_513jobs := by rfl
theorem t7_513all : t7_513jobs.all (Job.check tree)=true := by
  simp only [t7_513jobs,List.all_append,List.all_nil,t7_513part0,Bool.and_self]
theorem t7_513checked : Checked tree [5,9,6,7,7,7,7] := by
  refine ⟨plan9014,valid9014,t7_513choices,?_⟩
  exact check_of_frontier tree 0 t7_513root t7_513jobs t7_513frontier t7_513all
theorem t7_514choices : plan9015.choices=[5,9,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_514part0 : t7_514jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_514frontier : t7_514root.frontier 0=t7_514jobs := by rfl
theorem t7_514all : t7_514jobs.all (Job.check tree)=true := by
  simp only [t7_514jobs,List.all_append,List.all_nil,t7_514part0,Bool.and_self]
theorem t7_514checked : Checked tree [5,9,6,10,7,7,7] := by
  refine ⟨plan9015,valid9015,t7_514choices,?_⟩
  exact check_of_frontier tree 0 t7_514root t7_514jobs t7_514frontier t7_514all
theorem t7_515choices : plan9016.choices=[5,9,6,10,10,7,7].map (options 7 7) := by rfl


theorem t7_515part0 : t7_515jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_515frontier : t7_515root.frontier 0=t7_515jobs := by rfl
theorem t7_515all : t7_515jobs.all (Job.check tree)=true := by
  simp only [t7_515jobs,List.all_append,List.all_nil,t7_515part0,Bool.and_self]
theorem t7_515checked : Checked tree [5,9,6,10,10,7,7] := by
  refine ⟨plan9016,valid9016,t7_515choices,?_⟩
  exact check_of_frontier tree 0 t7_515root t7_515jobs t7_515frontier t7_515all
theorem t7_516choices : plan9017.choices=[5,9,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_516part0 : t7_516jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_516frontier : t7_516root.frontier 0=t7_516jobs := by rfl
theorem t7_516all : t7_516jobs.all (Job.check tree)=true := by
  simp only [t7_516jobs,List.all_append,List.all_nil,t7_516part0,Bool.and_self]
theorem t7_516checked : Checked tree [5,9,7,7,7,7,7] := by
  refine ⟨plan9017,valid9017,t7_516choices,?_⟩
  exact check_of_frontier tree 0 t7_516root t7_516jobs t7_516frontier t7_516all
theorem t7_517choices : plan8895.choices=[5,9,9,3,7,7,7].map (options 7 6) := by rfl


theorem t7_517part0 : t7_517jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_517frontier : t7_517root.frontier 0=t7_517jobs := by rfl
theorem t7_517all : t7_517jobs.all (Job.check tree)=true := by
  simp only [t7_517jobs,List.all_append,List.all_nil,t7_517part0,Bool.and_self]
theorem t7_517checked : Checked tree [5,9,9,3,7,7,7] := by
  refine ⟨plan8895,valid8895,t7_517choices,?_⟩
  exact check_of_frontier tree 0 t7_517root t7_517jobs t7_517frontier t7_517all
theorem t7_518choices : plan9018.choices=[5,9,9,6,7,7,7].map (options 7 7) := by rfl


theorem t7_518part0 : t7_518jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_518frontier : t7_518root.frontier 0=t7_518jobs := by rfl
theorem t7_518all : t7_518jobs.all (Job.check tree)=true := by
  simp only [t7_518jobs,List.all_append,List.all_nil,t7_518part0,Bool.and_self]
theorem t7_518checked : Checked tree [5,9,9,6,7,7,7] := by
  refine ⟨plan9018,valid9018,t7_518choices,?_⟩
  exact check_of_frontier tree 0 t7_518root t7_518jobs t7_518frontier t7_518all
theorem t7_519choices : plan9019.choices=[5,9,9,7,7,7,7].map (options 7 7) := by rfl


theorem t7_519part0 : t7_519jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_519frontier : t7_519root.frontier 0=t7_519jobs := by rfl
theorem t7_519all : t7_519jobs.all (Job.check tree)=true := by
  simp only [t7_519jobs,List.all_append,List.all_nil,t7_519part0,Bool.and_self]
theorem t7_519checked : Checked tree [5,9,9,7,7,7,7] := by
  refine ⟨plan9019,valid9019,t7_519choices,?_⟩
  exact check_of_frontier tree 0 t7_519root t7_519jobs t7_519frontier t7_519all
theorem t7_520choices : plan9020.choices=[5,9,9,10,7,7,7].map (options 7 7) := by rfl


theorem t7_520part0 : t7_520jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_520frontier : t7_520root.frontier 0=t7_520jobs := by rfl
theorem t7_520all : t7_520jobs.all (Job.check tree)=true := by
  simp only [t7_520jobs,List.all_append,List.all_nil,t7_520part0,Bool.and_self]
theorem t7_520checked : Checked tree [5,9,9,10,7,7,7] := by
  refine ⟨plan9020,valid9020,t7_520choices,?_⟩
  exact check_of_frontier tree 0 t7_520root t7_520jobs t7_520frontier t7_520all
theorem t7_521choices : plan9021.choices=[5,9,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_521part0 : t7_521jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_521frontier : t7_521root.frontier 0=t7_521jobs := by rfl
theorem t7_521all : t7_521jobs.all (Job.check tree)=true := by
  simp only [t7_521jobs,List.all_append,List.all_nil,t7_521part0,Bool.and_self]
theorem t7_521checked : Checked tree [5,9,10,7,7,7,7] := by
  refine ⟨plan9021,valid9021,t7_521choices,?_⟩
  exact check_of_frontier tree 0 t7_521root t7_521jobs t7_521frontier t7_521all
theorem t7_522choices : plan9022.choices=[5,9,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_522part0 : t7_522jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_522frontier : t7_522root.frontier 0=t7_522jobs := by rfl
theorem t7_522all : t7_522jobs.all (Job.check tree)=true := by
  simp only [t7_522jobs,List.all_append,List.all_nil,t7_522part0,Bool.and_self]
theorem t7_522checked : Checked tree [5,9,10,10,7,7,7] := by
  refine ⟨plan9022,valid9022,t7_522choices,?_⟩
  exact check_of_frontier tree 0 t7_522root t7_522jobs t7_522frontier t7_522all
theorem t7_523choices : plan9023.choices=[5,9,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_523part0 : t7_523jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_523frontier : t7_523root.frontier 0=t7_523jobs := by rfl
theorem t7_523all : t7_523jobs.all (Job.check tree)=true := by
  simp only [t7_523jobs,List.all_append,List.all_nil,t7_523part0,Bool.and_self]
theorem t7_523checked : Checked tree [5,9,10,10,10,7,7] := by
  refine ⟨plan9023,valid9023,t7_523choices,?_⟩
  exact check_of_frontier tree 0 t7_523root t7_523jobs t7_523frontier t7_523all
theorem t7_524choices : plan9024.choices=[5,10,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_524part0 : t7_524jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_524frontier : t7_524root.frontier 0=t7_524jobs := by rfl
theorem t7_524all : t7_524jobs.all (Job.check tree)=true := by
  simp only [t7_524jobs,List.all_append,List.all_nil,t7_524part0,Bool.and_self]
theorem t7_524checked : Checked tree [5,10,7,7,7,7,7] := by
  refine ⟨plan9024,valid9024,t7_524choices,?_⟩
  exact check_of_frontier tree 0 t7_524root t7_524jobs t7_524frontier t7_524all
theorem t7_525choices : plan9025.choices=[5,10,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_525part0 : t7_525jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_525frontier : t7_525root.frontier 0=t7_525jobs := by rfl
theorem t7_525all : t7_525jobs.all (Job.check tree)=true := by
  simp only [t7_525jobs,List.all_append,List.all_nil,t7_525part0,Bool.and_self]
theorem t7_525checked : Checked tree [5,10,10,7,7,7,7] := by
  refine ⟨plan9025,valid9025,t7_525choices,?_⟩
  exact check_of_frontier tree 0 t7_525root t7_525jobs t7_525frontier t7_525all
theorem t7_526choices : plan9026.choices=[5,10,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_526part0 : t7_526jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_526frontier : t7_526root.frontier 0=t7_526jobs := by rfl
theorem t7_526all : t7_526jobs.all (Job.check tree)=true := by
  simp only [t7_526jobs,List.all_append,List.all_nil,t7_526part0,Bool.and_self]
theorem t7_526checked : Checked tree [5,10,10,10,7,7,7] := by
  refine ⟨plan9026,valid9026,t7_526choices,?_⟩
  exact check_of_frontier tree 0 t7_526root t7_526jobs t7_526frontier t7_526all
theorem t7_527choices : plan9027.choices=[5,10,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_527part0 : t7_527jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_527frontier : t7_527root.frontier 0=t7_527jobs := by rfl
theorem t7_527all : t7_527jobs.all (Job.check tree)=true := by
  simp only [t7_527jobs,List.all_append,List.all_nil,t7_527part0,Bool.and_self]
theorem t7_527checked : Checked tree [5,10,10,10,10,7,7] := by
  refine ⟨plan9027,valid9027,t7_527choices,?_⟩
  exact check_of_frontier tree 0 t7_527root t7_527jobs t7_527frontier t7_527all
theorem t7_528choices : plan9028.choices=[5,10,10,10,10,10,7].map (options 7 7) := by rfl


theorem t7_528part0 : t7_528jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_528frontier : t7_528root.frontier 0=t7_528jobs := by rfl
theorem t7_528all : t7_528jobs.all (Job.check tree)=true := by
  simp only [t7_528jobs,List.all_append,List.all_nil,t7_528part0,Bool.and_self]
theorem t7_528checked : Checked tree [5,10,10,10,10,10,7] := by
  refine ⟨plan9028,valid9028,t7_528choices,?_⟩
  exact check_of_frontier tree 0 t7_528root t7_528jobs t7_528frontier t7_528all
theorem t7_529choices : plan9029.choices=[6,6,6,6,6,6,6].map (options 7 7) := by rfl


theorem t7_529part0 : t7_529jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_529frontier : t7_529root.frontier 0=t7_529jobs := by rfl
theorem t7_529all : t7_529jobs.all (Job.check tree)=true := by
  simp only [t7_529jobs,List.all_append,List.all_nil,t7_529part0,Bool.and_self]
theorem t7_529checked : Checked tree [6,6,6,6,6,6,6] := by
  refine ⟨plan9029,valid9029,t7_529choices,?_⟩
  exact check_of_frontier tree 0 t7_529root t7_529jobs t7_529frontier t7_529all
theorem t7_530choices : plan9030.choices=[6,6,6,6,6,6,7].map (options 7 7) := by rfl


theorem t7_530part0 : t7_530jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_530frontier : t7_530root.frontier 0=t7_530jobs := by rfl
theorem t7_530all : t7_530jobs.all (Job.check tree)=true := by
  simp only [t7_530jobs,List.all_append,List.all_nil,t7_530part0,Bool.and_self]
theorem t7_530checked : Checked tree [6,6,6,6,6,6,7] := by
  refine ⟨plan9030,valid9030,t7_530choices,?_⟩
  exact check_of_frontier tree 0 t7_530root t7_530jobs t7_530frontier t7_530all
theorem t7_531choices : plan9031.choices=[6,6,6,6,6,6,10].map (options 7 7) := by rfl


theorem t7_531part0 : t7_531jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_531frontier : t7_531root.frontier 0=t7_531jobs := by rfl
theorem t7_531all : t7_531jobs.all (Job.check tree)=true := by
  simp only [t7_531jobs,List.all_append,List.all_nil,t7_531part0,Bool.and_self]
theorem t7_531checked : Checked tree [6,6,6,6,6,6,10] := by
  refine ⟨plan9031,valid9031,t7_531choices,?_⟩
  exact check_of_frontier tree 0 t7_531root t7_531jobs t7_531frontier t7_531all
theorem t7_532choices : plan9032.choices=[6,6,6,6,6,7,7].map (options 7 7) := by rfl


theorem t7_532part0 : t7_532jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_532frontier : t7_532root.frontier 0=t7_532jobs := by rfl
theorem t7_532all : t7_532jobs.all (Job.check tree)=true := by
  simp only [t7_532jobs,List.all_append,List.all_nil,t7_532part0,Bool.and_self]
theorem t7_532checked : Checked tree [6,6,6,6,6,7,7] := by
  refine ⟨plan9032,valid9032,t7_532choices,?_⟩
  exact check_of_frontier tree 0 t7_532root t7_532jobs t7_532frontier t7_532all
theorem t7_533choices : plan9033.choices=[6,6,6,6,6,10,7].map (options 7 7) := by rfl


theorem t7_533part0 : t7_533jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_533frontier : t7_533root.frontier 0=t7_533jobs := by rfl
theorem t7_533all : t7_533jobs.all (Job.check tree)=true := by
  simp only [t7_533jobs,List.all_append,List.all_nil,t7_533part0,Bool.and_self]
theorem t7_533checked : Checked tree [6,6,6,6,6,10,7] := by
  refine ⟨plan9033,valid9033,t7_533choices,?_⟩
  exact check_of_frontier tree 0 t7_533root t7_533jobs t7_533frontier t7_533all
theorem t7_534choices : plan9034.choices=[6,6,6,6,6,10,10].map (options 7 7) := by rfl


theorem t7_534part0 : t7_534jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_534frontier : t7_534root.frontier 0=t7_534jobs := by rfl
theorem t7_534all : t7_534jobs.all (Job.check tree)=true := by
  simp only [t7_534jobs,List.all_append,List.all_nil,t7_534part0,Bool.and_self]
theorem t7_534checked : Checked tree [6,6,6,6,6,10,10] := by
  refine ⟨plan9034,valid9034,t7_534choices,?_⟩
  exact check_of_frontier tree 0 t7_534root t7_534jobs t7_534frontier t7_534all
theorem t7_535choices : plan9035.choices=[6,6,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_535part0 : t7_535jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_535frontier : t7_535root.frontier 0=t7_535jobs := by rfl
theorem t7_535all : t7_535jobs.all (Job.check tree)=true := by
  simp only [t7_535jobs,List.all_append,List.all_nil,t7_535part0,Bool.and_self]
theorem t7_535checked : Checked tree [6,6,6,6,7,7,7] := by
  refine ⟨plan9035,valid9035,t7_535choices,?_⟩
  exact check_of_frontier tree 0 t7_535root t7_535jobs t7_535frontier t7_535all
theorem t7_536choices : plan9036.choices=[6,6,6,6,10,7,7].map (options 7 7) := by rfl


theorem t7_536part0 : t7_536jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_536frontier : t7_536root.frontier 0=t7_536jobs := by rfl
theorem t7_536all : t7_536jobs.all (Job.check tree)=true := by
  simp only [t7_536jobs,List.all_append,List.all_nil,t7_536part0,Bool.and_self]
theorem t7_536checked : Checked tree [6,6,6,6,10,7,7] := by
  refine ⟨plan9036,valid9036,t7_536choices,?_⟩
  exact check_of_frontier tree 0 t7_536root t7_536jobs t7_536frontier t7_536all
theorem t7_537choices : plan9037.choices=[6,6,6,6,10,10,7].map (options 7 7) := by rfl


theorem t7_537part0 : t7_537jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_537frontier : t7_537root.frontier 0=t7_537jobs := by rfl
theorem t7_537all : t7_537jobs.all (Job.check tree)=true := by
  simp only [t7_537jobs,List.all_append,List.all_nil,t7_537part0,Bool.and_self]
theorem t7_537checked : Checked tree [6,6,6,6,10,10,7] := by
  refine ⟨plan9037,valid9037,t7_537choices,?_⟩
  exact check_of_frontier tree 0 t7_537root t7_537jobs t7_537frontier t7_537all
theorem t7_538choices : plan9038.choices=[6,6,6,6,10,10,10].map (options 7 7) := by rfl


theorem t7_538part0 : t7_538jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_538frontier : t7_538root.frontier 0=t7_538jobs := by rfl
theorem t7_538all : t7_538jobs.all (Job.check tree)=true := by
  simp only [t7_538jobs,List.all_append,List.all_nil,t7_538part0,Bool.and_self]
theorem t7_538checked : Checked tree [6,6,6,6,10,10,10] := by
  refine ⟨plan9038,valid9038,t7_538choices,?_⟩
  exact check_of_frontier tree 0 t7_538root t7_538jobs t7_538frontier t7_538all
theorem t7_539choices : plan9039.choices=[6,6,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_539part0 : t7_539jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_539frontier : t7_539root.frontier 0=t7_539jobs := by rfl
theorem t7_539all : t7_539jobs.all (Job.check tree)=true := by
  simp only [t7_539jobs,List.all_append,List.all_nil,t7_539part0,Bool.and_self]
theorem t7_539checked : Checked tree [6,6,6,7,7,7,7] := by
  refine ⟨plan9039,valid9039,t7_539choices,?_⟩
  exact check_of_frontier tree 0 t7_539root t7_539jobs t7_539frontier t7_539all
theorem t7_540choices : plan9040.choices=[6,6,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_540part0 : t7_540jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_540frontier : t7_540root.frontier 0=t7_540jobs := by rfl
theorem t7_540all : t7_540jobs.all (Job.check tree)=true := by
  simp only [t7_540jobs,List.all_append,List.all_nil,t7_540part0,Bool.and_self]
theorem t7_540checked : Checked tree [6,6,6,10,7,7,7] := by
  refine ⟨plan9040,valid9040,t7_540choices,?_⟩
  exact check_of_frontier tree 0 t7_540root t7_540jobs t7_540frontier t7_540all
theorem t7_541choices : plan9041.choices=[6,6,6,10,10,7,7].map (options 7 7) := by rfl


theorem t7_541part0 : t7_541jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_541frontier : t7_541root.frontier 0=t7_541jobs := by rfl
theorem t7_541all : t7_541jobs.all (Job.check tree)=true := by
  simp only [t7_541jobs,List.all_append,List.all_nil,t7_541part0,Bool.and_self]
theorem t7_541checked : Checked tree [6,6,6,10,10,7,7] := by
  refine ⟨plan9041,valid9041,t7_541choices,?_⟩
  exact check_of_frontier tree 0 t7_541root t7_541jobs t7_541frontier t7_541all
theorem t7_542choices : plan9042.choices=[6,6,6,10,10,10,7].map (options 7 7) := by rfl


theorem t7_542part0 : t7_542jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_542frontier : t7_542root.frontier 0=t7_542jobs := by rfl
theorem t7_542all : t7_542jobs.all (Job.check tree)=true := by
  simp only [t7_542jobs,List.all_append,List.all_nil,t7_542part0,Bool.and_self]
theorem t7_542checked : Checked tree [6,6,6,10,10,10,7] := by
  refine ⟨plan9042,valid9042,t7_542choices,?_⟩
  exact check_of_frontier tree 0 t7_542root t7_542jobs t7_542frontier t7_542all
theorem t7_543choices : plan9043.choices=[6,6,6,10,10,10,10].map (options 7 7) := by rfl


theorem t7_543part0 : t7_543jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_543frontier : t7_543root.frontier 0=t7_543jobs := by rfl
theorem t7_543all : t7_543jobs.all (Job.check tree)=true := by
  simp only [t7_543jobs,List.all_append,List.all_nil,t7_543part0,Bool.and_self]
theorem t7_543checked : Checked tree [6,6,6,10,10,10,10] := by
  refine ⟨plan9043,valid9043,t7_543choices,?_⟩
  exact check_of_frontier tree 0 t7_543root t7_543jobs t7_543frontier t7_543all
theorem t7_544choices : plan9044.choices=[6,6,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_544part0 : t7_544jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_544frontier : t7_544root.frontier 0=t7_544jobs := by rfl
theorem t7_544all : t7_544jobs.all (Job.check tree)=true := by
  simp only [t7_544jobs,List.all_append,List.all_nil,t7_544part0,Bool.and_self]
theorem t7_544checked : Checked tree [6,6,7,7,7,7,7] := by
  refine ⟨plan9044,valid9044,t7_544choices,?_⟩
  exact check_of_frontier tree 0 t7_544root t7_544jobs t7_544frontier t7_544all
theorem t7_545choices : plan9045.choices=[6,6,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_545part0 : t7_545jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_545frontier : t7_545root.frontier 0=t7_545jobs := by rfl
theorem t7_545all : t7_545jobs.all (Job.check tree)=true := by
  simp only [t7_545jobs,List.all_append,List.all_nil,t7_545part0,Bool.and_self]
theorem t7_545checked : Checked tree [6,6,10,7,7,7,7] := by
  refine ⟨plan9045,valid9045,t7_545choices,?_⟩
  exact check_of_frontier tree 0 t7_545root t7_545jobs t7_545frontier t7_545all
theorem t7_546choices : plan9046.choices=[6,6,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_546part0 : t7_546jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_546frontier : t7_546root.frontier 0=t7_546jobs := by rfl
theorem t7_546all : t7_546jobs.all (Job.check tree)=true := by
  simp only [t7_546jobs,List.all_append,List.all_nil,t7_546part0,Bool.and_self]
theorem t7_546checked : Checked tree [6,6,10,10,7,7,7] := by
  refine ⟨plan9046,valid9046,t7_546choices,?_⟩
  exact check_of_frontier tree 0 t7_546root t7_546jobs t7_546frontier t7_546all
theorem t7_547choices : plan9047.choices=[6,6,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_547part0 : t7_547jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_547frontier : t7_547root.frontier 0=t7_547jobs := by rfl
theorem t7_547all : t7_547jobs.all (Job.check tree)=true := by
  simp only [t7_547jobs,List.all_append,List.all_nil,t7_547part0,Bool.and_self]
theorem t7_547checked : Checked tree [6,6,10,10,10,7,7] := by
  refine ⟨plan9047,valid9047,t7_547choices,?_⟩
  exact check_of_frontier tree 0 t7_547root t7_547jobs t7_547frontier t7_547all
theorem t7_548choices : plan9048.choices=[6,6,10,10,10,10,7].map (options 7 7) := by rfl


theorem t7_548part0 : t7_548jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_548frontier : t7_548root.frontier 0=t7_548jobs := by rfl
theorem t7_548all : t7_548jobs.all (Job.check tree)=true := by
  simp only [t7_548jobs,List.all_append,List.all_nil,t7_548part0,Bool.and_self]
theorem t7_548checked : Checked tree [6,6,10,10,10,10,7] := by
  refine ⟨plan9048,valid9048,t7_548choices,?_⟩
  exact check_of_frontier tree 0 t7_548root t7_548jobs t7_548frontier t7_548all
theorem t7_549choices : plan9049.choices=[6,6,10,10,10,10,10].map (options 7 7) := by rfl


theorem t7_549part0 : t7_549jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_549frontier : t7_549root.frontier 0=t7_549jobs := by rfl
theorem t7_549all : t7_549jobs.all (Job.check tree)=true := by
  simp only [t7_549jobs,List.all_append,List.all_nil,t7_549part0,Bool.and_self]
theorem t7_549checked : Checked tree [6,6,10,10,10,10,10] := by
  refine ⟨plan9049,valid9049,t7_549choices,?_⟩
  exact check_of_frontier tree 0 t7_549root t7_549jobs t7_549frontier t7_549all
theorem t7_550choices : plan9050.choices=[6,7,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_550part0 : t7_550jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_550frontier : t7_550root.frontier 0=t7_550jobs := by rfl
theorem t7_550all : t7_550jobs.all (Job.check tree)=true := by
  simp only [t7_550jobs,List.all_append,List.all_nil,t7_550part0,Bool.and_self]
theorem t7_550checked : Checked tree [6,7,7,7,7,7,7] := by
  refine ⟨plan9050,valid9050,t7_550choices,?_⟩
  exact check_of_frontier tree 0 t7_550root t7_550jobs t7_550frontier t7_550all
theorem t7_551choices : plan9051.choices=[6,10,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_551part0 : t7_551jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_551frontier : t7_551root.frontier 0=t7_551jobs := by rfl
theorem t7_551all : t7_551jobs.all (Job.check tree)=true := by
  simp only [t7_551jobs,List.all_append,List.all_nil,t7_551part0,Bool.and_self]
theorem t7_551checked : Checked tree [6,10,7,7,7,7,7] := by
  refine ⟨plan9051,valid9051,t7_551choices,?_⟩
  exact check_of_frontier tree 0 t7_551root t7_551jobs t7_551frontier t7_551all
theorem t7_552choices : plan9052.choices=[6,10,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_552part0 : t7_552jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_552frontier : t7_552root.frontier 0=t7_552jobs := by rfl
theorem t7_552all : t7_552jobs.all (Job.check tree)=true := by
  simp only [t7_552jobs,List.all_append,List.all_nil,t7_552part0,Bool.and_self]
theorem t7_552checked : Checked tree [6,10,10,7,7,7,7] := by
  refine ⟨plan9052,valid9052,t7_552choices,?_⟩
  exact check_of_frontier tree 0 t7_552root t7_552jobs t7_552frontier t7_552all
theorem t7_553choices : plan9053.choices=[6,10,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_553part0 : t7_553jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_553frontier : t7_553root.frontier 0=t7_553jobs := by rfl
theorem t7_553all : t7_553jobs.all (Job.check tree)=true := by
  simp only [t7_553jobs,List.all_append,List.all_nil,t7_553part0,Bool.and_self]
theorem t7_553checked : Checked tree [6,10,10,10,7,7,7] := by
  refine ⟨plan9053,valid9053,t7_553choices,?_⟩
  exact check_of_frontier tree 0 t7_553root t7_553jobs t7_553frontier t7_553all
theorem t7_554choices : plan9054.choices=[6,10,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_554part0 : t7_554jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_554frontier : t7_554root.frontier 0=t7_554jobs := by rfl
theorem t7_554all : t7_554jobs.all (Job.check tree)=true := by
  simp only [t7_554jobs,List.all_append,List.all_nil,t7_554part0,Bool.and_self]
theorem t7_554checked : Checked tree [6,10,10,10,10,7,7] := by
  refine ⟨plan9054,valid9054,t7_554choices,?_⟩
  exact check_of_frontier tree 0 t7_554root t7_554jobs t7_554frontier t7_554all
theorem t7_555choices : plan9055.choices=[6,10,10,10,10,10,7].map (options 7 7) := by rfl


theorem t7_555part0 : t7_555jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_555frontier : t7_555root.frontier 0=t7_555jobs := by rfl
theorem t7_555all : t7_555jobs.all (Job.check tree)=true := by
  simp only [t7_555jobs,List.all_append,List.all_nil,t7_555part0,Bool.and_self]
theorem t7_555checked : Checked tree [6,10,10,10,10,10,7] := by
  refine ⟨plan9055,valid9055,t7_555choices,?_⟩
  exact check_of_frontier tree 0 t7_555root t7_555jobs t7_555frontier t7_555all
theorem t7_556choices : plan9056.choices=[6,10,10,10,10,10,10].map (options 7 7) := by rfl


theorem t7_556part0 : t7_556jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_556frontier : t7_556root.frontier 0=t7_556jobs := by rfl
theorem t7_556all : t7_556jobs.all (Job.check tree)=true := by
  simp only [t7_556jobs,List.all_append,List.all_nil,t7_556part0,Bool.and_self]
theorem t7_556checked : Checked tree [6,10,10,10,10,10,10] := by
  refine ⟨plan9056,valid9056,t7_556choices,?_⟩
  exact check_of_frontier tree 0 t7_556root t7_556jobs t7_556frontier t7_556all
theorem t7_557choices : plan9057.choices=[7,7,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_557part0 : t7_557jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_557frontier : t7_557root.frontier 0=t7_557jobs := by rfl
theorem t7_557all : t7_557jobs.all (Job.check tree)=true := by
  simp only [t7_557jobs,List.all_append,List.all_nil,t7_557part0,Bool.and_self]
theorem t7_557checked : Checked tree [7,7,7,7,7,7,7] := by
  refine ⟨plan9057,valid9057,t7_557choices,?_⟩
  exact check_of_frontier tree 0 t7_557root t7_557jobs t7_557frontier t7_557all
theorem t7_558choices : plan8683.choices=[8,2,2,7,7,7,7].map (options 7 5) := by rfl


theorem t7_558part0 : t7_558jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_558frontier : t7_558root.frontier 0=t7_558jobs := by rfl
theorem t7_558all : t7_558jobs.all (Job.check tree)=true := by
  simp only [t7_558jobs,List.all_append,List.all_nil,t7_558part0,Bool.and_self]
theorem t7_558checked : Checked tree [8,2,2,7,7,7,7] := by
  refine ⟨plan8683,valid8683,t7_558choices,?_⟩
  exact check_of_frontier tree 0 t7_558root t7_558jobs t7_558frontier t7_558all
theorem t7_559choices : plan8536.choices=[8,2,3,3,7,7,7].map (options 7 4) := by rfl


theorem t7_559part0 : t7_559jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_559frontier : t7_559root.frontier 0=t7_559jobs := by rfl
theorem t7_559all : t7_559jobs.all (Job.check tree)=true := by
  simp only [t7_559jobs,List.all_append,List.all_nil,t7_559part0,Bool.and_self]
theorem t7_559checked : Checked tree [8,2,3,3,7,7,7] := by
  refine ⟨plan8536,valid8536,t7_559choices,?_⟩
  exact check_of_frontier tree 0 t7_559root t7_559jobs t7_559frontier t7_559all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks188 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_463checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_476checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_477checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_478checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_479checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_480checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_481checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_482checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_483checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_484checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_485checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_464checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_486checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_487checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_488checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_489checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_490checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_491checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_492checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_493checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_494checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_495checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_465checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_496checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_497checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_498checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_499checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_500checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_501checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_502checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_503checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_504checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_466checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_505checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_506checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_507checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_508checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_509checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_510checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_511checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_512checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_513checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_514checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_467checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_515checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_516checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_517checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_518checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_519checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_520checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_521checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_522checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_523checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_524checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_468checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_525checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_526checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_527checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_528checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_529checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_530checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_531checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_532checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_533checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_534checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_469checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_535checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_536checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_537checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_538checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_539checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_540checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_541checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_542checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_543checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_544checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_470checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_545checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_546checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_547checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_548checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_549checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_550checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_551checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_552checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_553checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_554checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_471checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_555checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_556checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_557checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_558checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_559checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_472checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_473checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_474checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_475checked⟩
