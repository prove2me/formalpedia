-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks184
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:14:29.124131+00:00
-- url     : https://prove2.me/submissions/cc689cf6-a20d-43ff-ae23-93dfbabe2c61

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks184
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks184
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
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





theorem valid159 : plan159.Valid := valid_step _ _ _ valid0 (by decide +kernel)


































































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





























theorem valid591 : plan591.Valid := valid_step _ _ _ valid144 (by decide +kernel)















theorem valid599 : plan599.Valid := valid_step _ _ _ valid147 (by decide +kernel)



theorem valid601 : plan601.Valid := valid_step _ _ _ valid147 (by decide +kernel)

theorem valid602 : plan602.Valid := valid_step _ _ _ valid147 (by decide +kernel)





theorem valid605 : plan605.Valid := valid_step _ _ _ valid150 (by decide +kernel)



theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)











theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)











theorem valid619 : plan619.Valid := valid_step _ _ _ valid156 (by decide +kernel)











theorem valid625 : plan625.Valid := valid_step _ _ _ valid159 (by decide +kernel)






























































































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



theorem valid1634 : plan1634.Valid := valid_step _ _ _ valid599 (by decide +kernel)

theorem valid1635 : plan1635.Valid := valid_step _ _ _ valid601 (by decide +kernel)

theorem valid1636 : plan1636.Valid := valid_step _ _ _ valid602 (by decide +kernel)

























theorem valid1649 : plan1649.Valid := valid_step _ _ _ valid605 (by decide +kernel)



theorem valid1651 : plan1651.Valid := valid_step _ _ _ valid607 (by decide +kernel)

























theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)











theorem valid1671 : plan1671.Valid := valid_step _ _ _ valid619 (by decide +kernel)





theorem valid1674 : plan1674.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1675 : plan1675.Valid := valid_step _ _ _ valid619 (by decide +kernel)











theorem valid1681 : plan1681.Valid := valid_step _ _ _ valid625 (by decide +kernel)





theorem valid1684 : plan1684.Valid := valid_step _ _ _ valid625 (by decide +kernel)

theorem valid1685 : plan1685.Valid := valid_step _ _ _ valid625 (by decide +kernel)






















































































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





















































































































































































theorem valid1627 : plan1627.Valid := valid_step _ _ _ valid591 (by decide +kernel)










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

















theorem valid3561 : plan3561.Valid := valid_step _ _ _ valid1627 (by decide +kernel)













theorem valid3568 : plan3568.Valid := valid_step _ _ _ valid1634 (by decide +kernel)

theorem valid3569 : plan3569.Valid := valid_step _ _ _ valid1635 (by decide +kernel)

theorem valid3570 : plan3570.Valid := valid_step _ _ _ valid1636 (by decide +kernel)























theorem valid3582 : plan3582.Valid := valid_step _ _ _ valid1649 (by decide +kernel)

theorem valid3583 : plan3583.Valid := valid_step _ _ _ valid1651 (by decide +kernel)









































theorem valid3604 : plan3604.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

























theorem valid3617 : plan3617.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3618 : plan3618.Valid := valid_step _ _ _ valid1665 (by decide +kernel)













theorem valid3625 : plan3625.Valid := valid_step _ _ _ valid1671 (by decide +kernel)





theorem valid3628 : plan3628.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3629 : plan3629.Valid := valid_step _ _ _ valid1675 (by decide +kernel)





theorem valid3632 : plan3632.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3633 : plan3633.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3634 : plan3634.Valid := valid_step _ _ _ valid1675 (by decide +kernel)











theorem valid3640 : plan3640.Valid := valid_step _ _ _ valid1681 (by decide +kernel)





theorem valid3643 : plan3643.Valid := valid_step _ _ _ valid1684 (by decide +kernel)

theorem valid3644 : plan3644.Valid := valid_step _ _ _ valid1685 (by decide +kernel)





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





theorem valid6244 : plan6244.Valid := valid_step _ _ _ valid3643 (by decide +kernel)

theorem valid6245 : plan6245.Valid := valid_step _ _ _ valid3644 (by decide +kernel)





theorem valid6248 : plan6248.Valid := valid_step _ _ _ valid3647 (by decide +kernel)

theorem valid6249 : plan6249.Valid := valid_step _ _ _ valid3648 (by decide +kernel)

theorem valid6250 : plan6250.Valid := valid_step _ _ _ valid3649 (by decide +kernel)





theorem valid6253 : plan6253.Valid := valid_step _ _ _ valid3647 (by decide +kernel)



theorem valid6255 : plan6255.Valid := valid_step _ _ _ valid3647 (by decide +kernel)



theorem valid6257 : plan6257.Valid := valid_step _ _ _ valid3647 (by decide +kernel)

theorem valid6258 : plan6258.Valid := valid_step _ _ _ valid3648 (by decide +kernel)

theorem valid6259 : plan6259.Valid := valid_step _ _ _ valid3649 (by decide +kernel)


























































































































































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

























































































































theorem valid6109 : plan6109.Valid := valid_step _ _ _ valid3561 (by decide +kernel)















theorem valid6117 : plan6117.Valid := valid_step _ _ _ valid3568 (by decide +kernel)

theorem valid6118 : plan6118.Valid := valid_step _ _ _ valid3569 (by decide +kernel)

theorem valid6119 : plan6119.Valid := valid_step _ _ _ valid3570 (by decide +kernel)





























theorem valid6134 : plan6134.Valid := valid_step _ _ _ valid3582 (by decide +kernel)

theorem valid6135 : plan6135.Valid := valid_step _ _ _ valid3583 (by decide +kernel)


















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





























theorem valid6159 : plan6159.Valid := valid_step _ _ _ valid3604 (by decide +kernel)

















theorem valid6168 : plan6168.Valid := valid_step _ _ _ valid3617 (by decide +kernel)

theorem valid6169 : plan6169.Valid := valid_step _ _ _ valid3618 (by decide +kernel)































































theorem valid6201 : plan6201.Valid := valid_step _ _ _ valid3628 (by decide +kernel)



theorem valid6203 : plan6203.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6204 : plan6204.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

















theorem valid6213 : plan6213.Valid := valid_step _ _ _ valid3625 (by decide +kernel)





theorem valid6216 : plan6216.Valid := valid_step _ _ _ valid3628 (by decide +kernel)

theorem valid6217 : plan6217.Valid := valid_step _ _ _ valid3629 (by decide +kernel)





theorem valid6220 : plan6220.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6221 : plan6221.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6222 : plan6222.Valid := valid_step _ _ _ valid3634 (by decide +kernel)





theorem valid6225 : plan6225.Valid := valid_step _ _ _ valid3632 (by decide +kernel)









theorem valid6230 : plan6230.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6231 : plan6231.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6232 : plan6232.Valid := valid_step _ _ _ valid3634 (by decide +kernel)







theorem valid6236 : plan6236.Valid := valid_step _ _ _ valid3647 (by decide +kernel)








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

























theorem valid8077 : plan8077.Valid := valid_step _ _ _ valid6109 (by decide +kernel)





















theorem valid8088 : plan8088.Valid := valid_step _ _ _ valid6117 (by decide +kernel)

theorem valid8089 : plan8089.Valid := valid_step _ _ _ valid6118 (by decide +kernel)

theorem valid8090 : plan8090.Valid := valid_step _ _ _ valid6119 (by decide +kernel)



















































theorem valid8116 : plan8116.Valid := valid_step _ _ _ valid6134 (by decide +kernel)

theorem valid8117 : plan8117.Valid := valid_step _ _ _ valid6135 (by decide +kernel)






















































































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





theorem valid8359 : plan8359.Valid := valid_step _ _ _ valid6253 (by decide +kernel)

theorem valid8360 : plan8360.Valid := valid_step _ _ _ valid6257 (by decide +kernel)

theorem valid8361 : plan8361.Valid := valid_step _ _ _ valid6258 (by decide +kernel)

theorem valid8362 : plan8362.Valid := valid_step _ _ _ valid6259 (by decide +kernel)





theorem valid8365 : plan8365.Valid := valid_step _ _ _ valid6253 (by decide +kernel)

theorem valid8366 : plan8366.Valid := valid_step _ _ _ valid6248 (by decide +kernel)

theorem valid8367 : plan8367.Valid := valid_step _ _ _ valid6253 (by decide +kernel)

theorem valid8368 : plan8368.Valid := valid_step _ _ _ valid6257 (by decide +kernel)



theorem valid8370 : plan8370.Valid := valid_step _ _ _ valid6244 (by decide +kernel)



theorem valid8372 : plan8372.Valid := valid_step _ _ _ valid6248 (by decide +kernel)

theorem valid8373 : plan8373.Valid := valid_step _ _ _ valid6249 (by decide +kernel)



theorem valid8375 : plan8375.Valid := valid_step _ _ _ valid6253 (by decide +kernel)



theorem valid8377 : plan8377.Valid := valid_step _ _ _ valid6255 (by decide +kernel)



theorem valid8379 : plan8379.Valid := valid_step _ _ _ valid6257 (by decide +kernel)

theorem valid8380 : plan8380.Valid := valid_step _ _ _ valid6258 (by decide +kernel)



theorem valid8382 : plan8382.Valid := valid_step _ _ _ valid6253 (by decide +kernel)

theorem valid8383 : plan8383.Valid := valid_step _ _ _ valid6257 (by decide +kernel)

theorem valid8384 : plan8384.Valid := valid_step _ _ _ valid6258 (by decide +kernel)

theorem valid8385 : plan8385.Valid := valid_step _ _ _ valid6259 (by decide +kernel)





















































































theorem valid8428 : plan8428.Valid := valid_step _ _ _ valid8077 (by decide +kernel)








































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



















theorem valid8458 : plan8458.Valid := valid_step _ _ _ valid8088 (by decide +kernel)

theorem valid8459 : plan8459.Valid := valid_step _ _ _ valid8089 (by decide +kernel)

theorem valid8460 : plan8460.Valid := valid_step _ _ _ valid8090 (by decide +kernel)







































































































































theorem valid8528 : plan8528.Valid := valid_step _ _ _ valid8116 (by decide +kernel)

theorem valid8529 : plan8529.Valid := valid_step _ _ _ valid8117 (by decide +kernel)






























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





























theorem valid8175 : plan8175.Valid := valid_step _ _ _ valid6168 (by decide +kernel)

theorem valid8176 : plan8176.Valid := valid_step _ _ _ valid6169 (by decide +kernel)

















































theorem valid8201 : plan8201.Valid := valid_step _ _ _ valid6159 (by decide +kernel)























theorem valid8213 : plan8213.Valid := valid_step _ _ _ valid6159 (by decide +kernel)



































theorem valid8231 : plan8231.Valid := valid_step _ _ _ valid6213 (by decide +kernel)



theorem valid8233 : plan8233.Valid := valid_step _ _ _ valid6216 (by decide +kernel)

theorem valid8234 : plan8234.Valid := valid_step _ _ _ valid6217 (by decide +kernel)



theorem valid8236 : plan8236.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8237 : plan8237.Valid := valid_step _ _ _ valid6221 (by decide +kernel)

theorem valid8238 : plan8238.Valid := valid_step _ _ _ valid6222 (by decide +kernel)



theorem valid8240 : plan8240.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8241 : plan8241.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8242 : plan8242.Valid := valid_step _ _ _ valid6231 (by decide +kernel)

theorem valid8243 : plan8243.Valid := valid_step _ _ _ valid6232 (by decide +kernel)



theorem valid8245 : plan8245.Valid := valid_step _ _ _ valid6203 (by decide +kernel)









theorem valid8250 : plan8250.Valid := valid_step _ _ _ valid6201 (by decide +kernel)



theorem valid8252 : plan8252.Valid := valid_step _ _ _ valid6203 (by decide +kernel)

theorem valid8253 : plan8253.Valid := valid_step _ _ _ valid6204 (by decide +kernel)






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













































































theorem valid8295 : plan8295.Valid := valid_step _ _ _ valid6203 (by decide +kernel)









theorem valid8300 : plan8300.Valid := valid_step _ _ _ valid6201 (by decide +kernel)



theorem valid8302 : plan8302.Valid := valid_step _ _ _ valid6203 (by decide +kernel)

theorem valid8303 : plan8303.Valid := valid_step _ _ _ valid6204 (by decide +kernel)











































theorem valid8325 : plan8325.Valid := valid_step _ _ _ valid6248 (by decide +kernel)

theorem valid8326 : plan8326.Valid := valid_step _ _ _ valid6253 (by decide +kernel)

theorem valid8327 : plan8327.Valid := valid_step _ _ _ valid6257 (by decide +kernel)



theorem valid8329 : plan8329.Valid := valid_step _ _ _ valid6236 (by decide +kernel)





theorem valid8332 : plan8332.Valid := valid_step _ _ _ valid6244 (by decide +kernel)



theorem valid8334 : plan8334.Valid := valid_step _ _ _ valid6248 (by decide +kernel)

theorem valid8335 : plan8335.Valid := valid_step _ _ _ valid6249 (by decide +kernel)



theorem valid8337 : plan8337.Valid := valid_step _ _ _ valid6253 (by decide +kernel)



theorem valid8339 : plan8339.Valid := valid_step _ _ _ valid6255 (by decide +kernel)



theorem valid8341 : plan8341.Valid := valid_step _ _ _ valid6257 (by decide +kernel)

theorem valid8342 : plan8342.Valid := valid_step _ _ _ valid6258 (by decide +kernel)









theorem valid8347 : plan8347.Valid := valid_step _ _ _ valid6241 (by decide +kernel)





theorem valid8350 : plan8350.Valid := valid_step _ _ _ valid6244 (by decide +kernel)

theorem valid8351 : plan8351.Valid := valid_step _ _ _ valid6245 (by decide +kernel)


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













































theorem valid8663 : plan8663.Valid := valid_step _ _ _ valid8175 (by decide +kernel)

theorem valid8664 : plan8664.Valid := valid_step _ _ _ valid8176 (by decide +kernel)

theorem valid8665 : plan8665.Valid := valid_step _ _ _ valid8201 (by decide +kernel)

theorem valid8666 : plan8666.Valid := valid_step _ _ _ valid8213 (by decide +kernel)












































































































































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































theorem valid8848 : plan8848.Valid := valid_step _ _ _ valid8231 (by decide +kernel)

theorem valid8849 : plan8849.Valid := valid_step _ _ _ valid8233 (by decide +kernel)

theorem valid8850 : plan8850.Valid := valid_step _ _ _ valid8234 (by decide +kernel)

theorem valid8851 : plan8851.Valid := valid_step _ _ _ valid8236 (by decide +kernel)

theorem valid8852 : plan8852.Valid := valid_step _ _ _ valid8237 (by decide +kernel)

theorem valid8853 : plan8853.Valid := valid_step _ _ _ valid8238 (by decide +kernel)

theorem valid8854 : plan8854.Valid := valid_step _ _ _ valid8240 (by decide +kernel)

theorem valid8855 : plan8855.Valid := valid_step _ _ _ valid8241 (by decide +kernel)

theorem valid8856 : plan8856.Valid := valid_step _ _ _ valid8242 (by decide +kernel)

theorem valid8857 : plan8857.Valid := valid_step _ _ _ valid8243 (by decide +kernel)

theorem valid8858 : plan8858.Valid := valid_step _ _ _ valid8245 (by decide +kernel)

theorem valid8859 : plan8859.Valid := valid_step _ _ _ valid8250 (by decide +kernel)

theorem valid8860 : plan8860.Valid := valid_step _ _ _ valid8252 (by decide +kernel)

theorem valid8861 : plan8861.Valid := valid_step _ _ _ valid8253 (by decide +kernel)

theorem valid8862 : plan8862.Valid := valid_step _ _ _ valid8295 (by decide +kernel)

theorem valid8863 : plan8863.Valid := valid_step _ _ _ valid8300 (by decide +kernel)

theorem valid8864 : plan8864.Valid := valid_step _ _ _ valid8302 (by decide +kernel)

theorem valid8865 : plan8865.Valid := valid_step _ _ _ valid8303 (by decide +kernel)






























































































































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





























theorem valid8943 : plan8943.Valid := valid_step _ _ _ valid8325 (by decide +kernel)

theorem valid8944 : plan8944.Valid := valid_step _ _ _ valid8326 (by decide +kernel)

theorem valid8945 : plan8945.Valid := valid_step _ _ _ valid8327 (by decide +kernel)

theorem valid8946 : plan8946.Valid := valid_step _ _ _ valid8329 (by decide +kernel)

theorem valid8947 : plan8947.Valid := valid_step _ _ _ valid8332 (by decide +kernel)

theorem valid8948 : plan8948.Valid := valid_step _ _ _ valid8334 (by decide +kernel)

theorem valid8949 : plan8949.Valid := valid_step _ _ _ valid8335 (by decide +kernel)

theorem valid8950 : plan8950.Valid := valid_step _ _ _ valid8337 (by decide +kernel)

theorem valid8951 : plan8951.Valid := valid_step _ _ _ valid8339 (by decide +kernel)

theorem valid8952 : plan8952.Valid := valid_step _ _ _ valid8341 (by decide +kernel)

theorem valid8953 : plan8953.Valid := valid_step _ _ _ valid8342 (by decide +kernel)

theorem valid8954 : plan8954.Valid := valid_step _ _ _ valid8347 (by decide +kernel)

theorem valid8955 : plan8955.Valid := valid_step _ _ _ valid8350 (by decide +kernel)

theorem valid8956 : plan8956.Valid := valid_step _ _ _ valid8351 (by decide +kernel)

theorem valid8957 : plan8957.Valid := valid_step _ _ _ valid8354 (by decide +kernel)

theorem valid8958 : plan8958.Valid := valid_step _ _ _ valid8355 (by decide +kernel)

theorem valid8959 : plan8959.Valid := valid_step _ _ _ valid8356 (by decide +kernel)

theorem valid8960 : plan8960.Valid := valid_step _ _ _ valid8359 (by decide +kernel)

theorem valid8961 : plan8961.Valid := valid_step _ _ _ valid8360 (by decide +kernel)

theorem valid8962 : plan8962.Valid := valid_step _ _ _ valid8361 (by decide +kernel)

theorem valid8963 : plan8963.Valid := valid_step _ _ _ valid8362 (by decide +kernel)

theorem valid8964 : plan8964.Valid := valid_step _ _ _ valid8365 (by decide +kernel)

theorem valid8965 : plan8965.Valid := valid_step _ _ _ valid8366 (by decide +kernel)

theorem valid8966 : plan8966.Valid := valid_step _ _ _ valid8367 (by decide +kernel)

theorem valid8967 : plan8967.Valid := valid_step _ _ _ valid8368 (by decide +kernel)

theorem valid8968 : plan8968.Valid := valid_step _ _ _ valid8370 (by decide +kernel)

theorem valid8969 : plan8969.Valid := valid_step _ _ _ valid8372 (by decide +kernel)

theorem valid8970 : plan8970.Valid := valid_step _ _ _ valid8373 (by decide +kernel)

theorem valid8971 : plan8971.Valid := valid_step _ _ _ valid8375 (by decide +kernel)

theorem valid8972 : plan8972.Valid := valid_step _ _ _ valid8377 (by decide +kernel)

theorem valid8973 : plan8973.Valid := valid_step _ _ _ valid8379 (by decide +kernel)

theorem valid8974 : plan8974.Valid := valid_step _ _ _ valid8380 (by decide +kernel)

theorem valid8975 : plan8975.Valid := valid_step _ _ _ valid8382 (by decide +kernel)

theorem valid8976 : plan8976.Valid := valid_step _ _ _ valid8383 (by decide +kernel)

theorem valid8977 : plan8977.Valid := valid_step _ _ _ valid8384 (by decide +kernel)

theorem valid8978 : plan8978.Valid := valid_step _ _ _ valid8385 (by decide +kernel)




























































































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
theorem t7_363choices : plan8663.choices=[4,3,3,10,7,7,7].map (options 7 5) := by rfl


theorem t7_363part0 : t7_363jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_363frontier : t7_363root.frontier 0=t7_363jobs := by rfl
theorem t7_363all : t7_363jobs.all (Job.check tree)=true := by
  simp only [t7_363jobs,List.all_append,List.all_nil,t7_363part0,Bool.and_self]
theorem t7_363checked : Checked tree [4,3,3,10,7,7,7] := by
  refine ⟨plan8663,valid8663,t7_363choices,?_⟩
  exact check_of_frontier tree 0 t7_363root t7_363jobs t7_363frontier t7_363all
theorem t7_364choices : plan8664.choices=[4,3,3,10,10,7,7].map (options 7 5) := by rfl


theorem t7_364part0 : t7_364jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_364frontier : t7_364root.frontier 0=t7_364jobs := by rfl
theorem t7_364all : t7_364jobs.all (Job.check tree)=true := by
  simp only [t7_364jobs,List.all_append,List.all_nil,t7_364part0,Bool.and_self]
theorem t7_364checked : Checked tree [4,3,3,10,10,7,7] := by
  refine ⟨plan8664,valid8664,t7_364choices,?_⟩
  exact check_of_frontier tree 0 t7_364root t7_364jobs t7_364frontier t7_364all
theorem t7_365choices : plan8848.choices=[4,3,6,6,6,7,7].map (options 7 6) := by rfl


theorem t7_365part0 : t7_365jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_365frontier : t7_365root.frontier 0=t7_365jobs := by rfl
theorem t7_365all : t7_365jobs.all (Job.check tree)=true := by
  simp only [t7_365jobs,List.all_append,List.all_nil,t7_365part0,Bool.and_self]
theorem t7_365checked : Checked tree [4,3,6,6,6,7,7] := by
  refine ⟨plan8848,valid8848,t7_365choices,?_⟩
  exact check_of_frontier tree 0 t7_365root t7_365jobs t7_365frontier t7_365all
theorem t7_366choices : plan8849.choices=[4,3,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_366part0 : t7_366jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_366frontier : t7_366root.frontier 0=t7_366jobs := by rfl
theorem t7_366all : t7_366jobs.all (Job.check tree)=true := by
  simp only [t7_366jobs,List.all_append,List.all_nil,t7_366part0,Bool.and_self]
theorem t7_366checked : Checked tree [4,3,6,6,7,7,7] := by
  refine ⟨plan8849,valid8849,t7_366choices,?_⟩
  exact check_of_frontier tree 0 t7_366root t7_366jobs t7_366frontier t7_366all
theorem t7_367choices : plan8850.choices=[4,3,6,6,10,7,7].map (options 7 6) := by rfl


theorem t7_367part0 : t7_367jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_367frontier : t7_367root.frontier 0=t7_367jobs := by rfl
theorem t7_367all : t7_367jobs.all (Job.check tree)=true := by
  simp only [t7_367jobs,List.all_append,List.all_nil,t7_367part0,Bool.and_self]
theorem t7_367checked : Checked tree [4,3,6,6,10,7,7] := by
  refine ⟨plan8850,valid8850,t7_367choices,?_⟩
  exact check_of_frontier tree 0 t7_367root t7_367jobs t7_367frontier t7_367all
theorem t7_368choices : plan8851.choices=[4,3,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_368part0 : t7_368jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_368frontier : t7_368root.frontier 0=t7_368jobs := by rfl
theorem t7_368all : t7_368jobs.all (Job.check tree)=true := by
  simp only [t7_368jobs,List.all_append,List.all_nil,t7_368part0,Bool.and_self]
theorem t7_368checked : Checked tree [4,3,6,7,7,7,7] := by
  refine ⟨plan8851,valid8851,t7_368choices,?_⟩
  exact check_of_frontier tree 0 t7_368root t7_368jobs t7_368frontier t7_368all
theorem t7_369choices : plan8852.choices=[4,3,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_369part0 : t7_369jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_369frontier : t7_369root.frontier 0=t7_369jobs := by rfl
theorem t7_369all : t7_369jobs.all (Job.check tree)=true := by
  simp only [t7_369jobs,List.all_append,List.all_nil,t7_369part0,Bool.and_self]
theorem t7_369checked : Checked tree [4,3,6,10,7,7,7] := by
  refine ⟨plan8852,valid8852,t7_369choices,?_⟩
  exact check_of_frontier tree 0 t7_369root t7_369jobs t7_369frontier t7_369all
theorem t7_370choices : plan8853.choices=[4,3,6,10,10,7,7].map (options 7 6) := by rfl


theorem t7_370part0 : t7_370jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_370frontier : t7_370root.frontier 0=t7_370jobs := by rfl
theorem t7_370all : t7_370jobs.all (Job.check tree)=true := by
  simp only [t7_370jobs,List.all_append,List.all_nil,t7_370part0,Bool.and_self]
theorem t7_370checked : Checked tree [4,3,6,10,10,7,7] := by
  refine ⟨plan8853,valid8853,t7_370choices,?_⟩
  exact check_of_frontier tree 0 t7_370root t7_370jobs t7_370frontier t7_370all
theorem t7_371choices : plan8854.choices=[4,3,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_371part0 : t7_371jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_371frontier : t7_371root.frontier 0=t7_371jobs := by rfl
theorem t7_371all : t7_371jobs.all (Job.check tree)=true := by
  simp only [t7_371jobs,List.all_append,List.all_nil,t7_371part0,Bool.and_self]
theorem t7_371checked : Checked tree [4,3,7,7,7,7,7] := by
  refine ⟨plan8854,valid8854,t7_371choices,?_⟩
  exact check_of_frontier tree 0 t7_371root t7_371jobs t7_371frontier t7_371all
theorem t7_372choices : plan8855.choices=[4,3,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_372part0 : t7_372jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_372frontier : t7_372root.frontier 0=t7_372jobs := by rfl
theorem t7_372all : t7_372jobs.all (Job.check tree)=true := by
  simp only [t7_372jobs,List.all_append,List.all_nil,t7_372part0,Bool.and_self]
theorem t7_372checked : Checked tree [4,3,10,7,7,7,7] := by
  refine ⟨plan8855,valid8855,t7_372choices,?_⟩
  exact check_of_frontier tree 0 t7_372root t7_372jobs t7_372frontier t7_372all
theorem t7_373choices : plan8856.choices=[4,3,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_373part0 : t7_373jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_373frontier : t7_373root.frontier 0=t7_373jobs := by rfl
theorem t7_373all : t7_373jobs.all (Job.check tree)=true := by
  simp only [t7_373jobs,List.all_append,List.all_nil,t7_373part0,Bool.and_self]
theorem t7_373checked : Checked tree [4,3,10,10,7,7,7] := by
  refine ⟨plan8856,valid8856,t7_373choices,?_⟩
  exact check_of_frontier tree 0 t7_373root t7_373jobs t7_373frontier t7_373all
theorem t7_374choices : plan8857.choices=[4,3,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_374part0 : t7_374jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_374frontier : t7_374root.frontier 0=t7_374jobs := by rfl
theorem t7_374all : t7_374jobs.all (Job.check tree)=true := by
  simp only [t7_374jobs,List.all_append,List.all_nil,t7_374part0,Bool.and_self]
theorem t7_374checked : Checked tree [4,3,10,10,10,7,7] := by
  refine ⟨plan8857,valid8857,t7_374choices,?_⟩
  exact check_of_frontier tree 0 t7_374root t7_374jobs t7_374frontier t7_374all
theorem t7_375choices : plan8858.choices=[4,4,3,7,7,7,7].map (options 7 6) := by rfl


theorem t7_375part0 : t7_375jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_375frontier : t7_375root.frontier 0=t7_375jobs := by rfl
theorem t7_375all : t7_375jobs.all (Job.check tree)=true := by
  simp only [t7_375jobs,List.all_append,List.all_nil,t7_375part0,Bool.and_self]
theorem t7_375checked : Checked tree [4,4,3,7,7,7,7] := by
  refine ⟨plan8858,valid8858,t7_375choices,?_⟩
  exact check_of_frontier tree 0 t7_375root t7_375jobs t7_375frontier t7_375all
theorem t7_376choices : plan8943.choices=[4,4,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_376part0 : t7_376jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_376frontier : t7_376root.frontier 0=t7_376jobs := by rfl
theorem t7_376all : t7_376jobs.all (Job.check tree)=true := by
  simp only [t7_376jobs,List.all_append,List.all_nil,t7_376part0,Bool.and_self]
theorem t7_376checked : Checked tree [4,4,6,7,7,7,7] := by
  refine ⟨plan8943,valid8943,t7_376choices,?_⟩
  exact check_of_frontier tree 0 t7_376root t7_376jobs t7_376frontier t7_376all
theorem t7_377choices : plan8944.choices=[4,4,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_377part0 : t7_377jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_377frontier : t7_377root.frontier 0=t7_377jobs := by rfl
theorem t7_377all : t7_377jobs.all (Job.check tree)=true := by
  simp only [t7_377jobs,List.all_append,List.all_nil,t7_377part0,Bool.and_self]
theorem t7_377checked : Checked tree [4,4,7,7,7,7,7] := by
  refine ⟨plan8944,valid8944,t7_377choices,?_⟩
  exact check_of_frontier tree 0 t7_377root t7_377jobs t7_377frontier t7_377all
theorem t7_378choices : plan8945.choices=[4,4,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_378part0 : t7_378jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_378frontier : t7_378root.frontier 0=t7_378jobs := by rfl
theorem t7_378all : t7_378jobs.all (Job.check tree)=true := by
  simp only [t7_378jobs,List.all_append,List.all_nil,t7_378part0,Bool.and_self]
theorem t7_378checked : Checked tree [4,4,10,7,7,7,7] := by
  refine ⟨plan8945,valid8945,t7_378choices,?_⟩
  exact check_of_frontier tree 0 t7_378root t7_378jobs t7_378frontier t7_378all
theorem t7_379choices : plan8665.choices=[4,5,3,3,7,7,7].map (options 7 5) := by rfl


theorem t7_379part0 : t7_379jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_379frontier : t7_379root.frontier 0=t7_379jobs := by rfl
theorem t7_379all : t7_379jobs.all (Job.check tree)=true := by
  simp only [t7_379jobs,List.all_append,List.all_nil,t7_379part0,Bool.and_self]
theorem t7_379checked : Checked tree [4,5,3,3,7,7,7] := by
  refine ⟨plan8665,valid8665,t7_379choices,?_⟩
  exact check_of_frontier tree 0 t7_379root t7_379jobs t7_379frontier t7_379all
theorem t7_380choices : plan8859.choices=[4,5,3,6,7,7,7].map (options 7 6) := by rfl


theorem t7_380part0 : t7_380jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_380frontier : t7_380root.frontier 0=t7_380jobs := by rfl
theorem t7_380all : t7_380jobs.all (Job.check tree)=true := by
  simp only [t7_380jobs,List.all_append,List.all_nil,t7_380part0,Bool.and_self]
theorem t7_380checked : Checked tree [4,5,3,6,7,7,7] := by
  refine ⟨plan8859,valid8859,t7_380choices,?_⟩
  exact check_of_frontier tree 0 t7_380root t7_380jobs t7_380frontier t7_380all
theorem t7_381choices : plan8860.choices=[4,5,3,7,7,7,7].map (options 7 6) := by rfl


theorem t7_381part0 : t7_381jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_381frontier : t7_381root.frontier 0=t7_381jobs := by rfl
theorem t7_381all : t7_381jobs.all (Job.check tree)=true := by
  simp only [t7_381jobs,List.all_append,List.all_nil,t7_381part0,Bool.and_self]
theorem t7_381checked : Checked tree [4,5,3,7,7,7,7] := by
  refine ⟨plan8860,valid8860,t7_381choices,?_⟩
  exact check_of_frontier tree 0 t7_381root t7_381jobs t7_381frontier t7_381all
theorem t7_382choices : plan8861.choices=[4,5,3,10,7,7,7].map (options 7 6) := by rfl


theorem t7_382part0 : t7_382jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_382frontier : t7_382root.frontier 0=t7_382jobs := by rfl
theorem t7_382all : t7_382jobs.all (Job.check tree)=true := by
  simp only [t7_382jobs,List.all_append,List.all_nil,t7_382part0,Bool.and_self]
theorem t7_382checked : Checked tree [4,5,3,10,7,7,7] := by
  refine ⟨plan8861,valid8861,t7_382choices,?_⟩
  exact check_of_frontier tree 0 t7_382root t7_382jobs t7_382frontier t7_382all
theorem t7_383choices : plan8946.choices=[4,5,5,7,7,7,7].map (options 7 7) := by rfl


theorem t7_383part0 : t7_383jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_383frontier : t7_383root.frontier 0=t7_383jobs := by rfl
theorem t7_383all : t7_383jobs.all (Job.check tree)=true := by
  simp only [t7_383jobs,List.all_append,List.all_nil,t7_383part0,Bool.and_self]
theorem t7_383checked : Checked tree [4,5,5,7,7,7,7] := by
  refine ⟨plan8946,valid8946,t7_383choices,?_⟩
  exact check_of_frontier tree 0 t7_383root t7_383jobs t7_383frontier t7_383all
theorem t7_384choices : plan8947.choices=[4,5,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_384part0 : t7_384jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_384frontier : t7_384root.frontier 0=t7_384jobs := by rfl
theorem t7_384all : t7_384jobs.all (Job.check tree)=true := by
  simp only [t7_384jobs,List.all_append,List.all_nil,t7_384part0,Bool.and_self]
theorem t7_384checked : Checked tree [4,5,6,6,7,7,7] := by
  refine ⟨plan8947,valid8947,t7_384choices,?_⟩
  exact check_of_frontier tree 0 t7_384root t7_384jobs t7_384frontier t7_384all
theorem t7_385choices : plan8948.choices=[4,5,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_385part0 : t7_385jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_385frontier : t7_385root.frontier 0=t7_385jobs := by rfl
theorem t7_385all : t7_385jobs.all (Job.check tree)=true := by
  simp only [t7_385jobs,List.all_append,List.all_nil,t7_385part0,Bool.and_self]
theorem t7_385checked : Checked tree [4,5,6,7,7,7,7] := by
  refine ⟨plan8948,valid8948,t7_385choices,?_⟩
  exact check_of_frontier tree 0 t7_385root t7_385jobs t7_385frontier t7_385all
theorem t7_386choices : plan8949.choices=[4,5,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_386part0 : t7_386jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_386frontier : t7_386root.frontier 0=t7_386jobs := by rfl
theorem t7_386all : t7_386jobs.all (Job.check tree)=true := by
  simp only [t7_386jobs,List.all_append,List.all_nil,t7_386part0,Bool.and_self]
theorem t7_386checked : Checked tree [4,5,6,10,7,7,7] := by
  refine ⟨plan8949,valid8949,t7_386choices,?_⟩
  exact check_of_frontier tree 0 t7_386root t7_386jobs t7_386frontier t7_386all
theorem t7_387choices : plan8950.choices=[4,5,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_387part0 : t7_387jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_387frontier : t7_387root.frontier 0=t7_387jobs := by rfl
theorem t7_387all : t7_387jobs.all (Job.check tree)=true := by
  simp only [t7_387jobs,List.all_append,List.all_nil,t7_387part0,Bool.and_self]
theorem t7_387checked : Checked tree [4,5,7,7,7,7,7] := by
  refine ⟨plan8950,valid8950,t7_387choices,?_⟩
  exact check_of_frontier tree 0 t7_387root t7_387jobs t7_387frontier t7_387all
theorem t7_388choices : plan8951.choices=[4,5,9,7,7,7,7].map (options 7 7) := by rfl


theorem t7_388part0 : t7_388jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_388frontier : t7_388root.frontier 0=t7_388jobs := by rfl
theorem t7_388all : t7_388jobs.all (Job.check tree)=true := by
  simp only [t7_388jobs,List.all_append,List.all_nil,t7_388part0,Bool.and_self]
theorem t7_388checked : Checked tree [4,5,9,7,7,7,7] := by
  refine ⟨plan8951,valid8951,t7_388choices,?_⟩
  exact check_of_frontier tree 0 t7_388root t7_388jobs t7_388frontier t7_388all
theorem t7_389choices : plan8952.choices=[4,5,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_389part0 : t7_389jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_389frontier : t7_389root.frontier 0=t7_389jobs := by rfl
theorem t7_389all : t7_389jobs.all (Job.check tree)=true := by
  simp only [t7_389jobs,List.all_append,List.all_nil,t7_389part0,Bool.and_self]
theorem t7_389checked : Checked tree [4,5,10,7,7,7,7] := by
  refine ⟨plan8952,valid8952,t7_389choices,?_⟩
  exact check_of_frontier tree 0 t7_389root t7_389jobs t7_389frontier t7_389all
theorem t7_390choices : plan8953.choices=[4,5,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_390part0 : t7_390jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_390frontier : t7_390root.frontier 0=t7_390jobs := by rfl
theorem t7_390all : t7_390jobs.all (Job.check tree)=true := by
  simp only [t7_390jobs,List.all_append,List.all_nil,t7_390part0,Bool.and_self]
theorem t7_390checked : Checked tree [4,5,10,10,7,7,7] := by
  refine ⟨plan8953,valid8953,t7_390choices,?_⟩
  exact check_of_frontier tree 0 t7_390root t7_390jobs t7_390frontier t7_390all
theorem t7_391choices : plan8954.choices=[4,6,6,6,6,7,7].map (options 7 7) := by rfl


theorem t7_391part0 : t7_391jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_391frontier : t7_391root.frontier 0=t7_391jobs := by rfl
theorem t7_391all : t7_391jobs.all (Job.check tree)=true := by
  simp only [t7_391jobs,List.all_append,List.all_nil,t7_391part0,Bool.and_self]
theorem t7_391checked : Checked tree [4,6,6,6,6,7,7] := by
  refine ⟨plan8954,valid8954,t7_391choices,?_⟩
  exact check_of_frontier tree 0 t7_391root t7_391jobs t7_391frontier t7_391all
theorem t7_392choices : plan8955.choices=[4,6,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_392part0 : t7_392jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_392frontier : t7_392root.frontier 0=t7_392jobs := by rfl
theorem t7_392all : t7_392jobs.all (Job.check tree)=true := by
  simp only [t7_392jobs,List.all_append,List.all_nil,t7_392part0,Bool.and_self]
theorem t7_392checked : Checked tree [4,6,6,6,7,7,7] := by
  refine ⟨plan8955,valid8955,t7_392choices,?_⟩
  exact check_of_frontier tree 0 t7_392root t7_392jobs t7_392frontier t7_392all
theorem t7_393choices : plan8956.choices=[4,6,6,6,10,7,7].map (options 7 7) := by rfl


theorem t7_393part0 : t7_393jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_393frontier : t7_393root.frontier 0=t7_393jobs := by rfl
theorem t7_393all : t7_393jobs.all (Job.check tree)=true := by
  simp only [t7_393jobs,List.all_append,List.all_nil,t7_393part0,Bool.and_self]
theorem t7_393checked : Checked tree [4,6,6,6,10,7,7] := by
  refine ⟨plan8956,valid8956,t7_393choices,?_⟩
  exact check_of_frontier tree 0 t7_393root t7_393jobs t7_393frontier t7_393all
theorem t7_394choices : plan8957.choices=[4,6,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_394part0 : t7_394jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_394frontier : t7_394root.frontier 0=t7_394jobs := by rfl
theorem t7_394all : t7_394jobs.all (Job.check tree)=true := by
  simp only [t7_394jobs,List.all_append,List.all_nil,t7_394part0,Bool.and_self]
theorem t7_394checked : Checked tree [4,6,6,7,7,7,7] := by
  refine ⟨plan8957,valid8957,t7_394choices,?_⟩
  exact check_of_frontier tree 0 t7_394root t7_394jobs t7_394frontier t7_394all
theorem t7_395choices : plan8958.choices=[4,6,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_395part0 : t7_395jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_395frontier : t7_395root.frontier 0=t7_395jobs := by rfl
theorem t7_395all : t7_395jobs.all (Job.check tree)=true := by
  simp only [t7_395jobs,List.all_append,List.all_nil,t7_395part0,Bool.and_self]
theorem t7_395checked : Checked tree [4,6,6,10,7,7,7] := by
  refine ⟨plan8958,valid8958,t7_395choices,?_⟩
  exact check_of_frontier tree 0 t7_395root t7_395jobs t7_395frontier t7_395all
theorem t7_396choices : plan8959.choices=[4,6,6,10,10,7,7].map (options 7 7) := by rfl


theorem t7_396part0 : t7_396jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_396frontier : t7_396root.frontier 0=t7_396jobs := by rfl
theorem t7_396all : t7_396jobs.all (Job.check tree)=true := by
  simp only [t7_396jobs,List.all_append,List.all_nil,t7_396part0,Bool.and_self]
theorem t7_396checked : Checked tree [4,6,6,10,10,7,7] := by
  refine ⟨plan8959,valid8959,t7_396choices,?_⟩
  exact check_of_frontier tree 0 t7_396root t7_396jobs t7_396frontier t7_396all
theorem t7_397choices : plan8960.choices=[4,6,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_397part0 : t7_397jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_397frontier : t7_397root.frontier 0=t7_397jobs := by rfl
theorem t7_397all : t7_397jobs.all (Job.check tree)=true := by
  simp only [t7_397jobs,List.all_append,List.all_nil,t7_397part0,Bool.and_self]
theorem t7_397checked : Checked tree [4,6,7,7,7,7,7] := by
  refine ⟨plan8960,valid8960,t7_397choices,?_⟩
  exact check_of_frontier tree 0 t7_397root t7_397jobs t7_397frontier t7_397all
theorem t7_398choices : plan8961.choices=[4,6,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_398part0 : t7_398jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_398frontier : t7_398root.frontier 0=t7_398jobs := by rfl
theorem t7_398all : t7_398jobs.all (Job.check tree)=true := by
  simp only [t7_398jobs,List.all_append,List.all_nil,t7_398part0,Bool.and_self]
theorem t7_398checked : Checked tree [4,6,10,7,7,7,7] := by
  refine ⟨plan8961,valid8961,t7_398choices,?_⟩
  exact check_of_frontier tree 0 t7_398root t7_398jobs t7_398frontier t7_398all
theorem t7_399choices : plan8962.choices=[4,6,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_399part0 : t7_399jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_399frontier : t7_399root.frontier 0=t7_399jobs := by rfl
theorem t7_399all : t7_399jobs.all (Job.check tree)=true := by
  simp only [t7_399jobs,List.all_append,List.all_nil,t7_399part0,Bool.and_self]
theorem t7_399checked : Checked tree [4,6,10,10,7,7,7] := by
  refine ⟨plan8962,valid8962,t7_399choices,?_⟩
  exact check_of_frontier tree 0 t7_399root t7_399jobs t7_399frontier t7_399all
theorem t7_400choices : plan8963.choices=[4,6,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_400part0 : t7_400jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_400frontier : t7_400root.frontier 0=t7_400jobs := by rfl
theorem t7_400all : t7_400jobs.all (Job.check tree)=true := by
  simp only [t7_400jobs,List.all_append,List.all_nil,t7_400part0,Bool.and_self]
theorem t7_400checked : Checked tree [4,6,10,10,10,7,7] := by
  refine ⟨plan8963,valid8963,t7_400choices,?_⟩
  exact check_of_frontier tree 0 t7_400root t7_400jobs t7_400frontier t7_400all
theorem t7_401choices : plan8964.choices=[4,7,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_401part0 : t7_401jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_401frontier : t7_401root.frontier 0=t7_401jobs := by rfl
theorem t7_401all : t7_401jobs.all (Job.check tree)=true := by
  simp only [t7_401jobs,List.all_append,List.all_nil,t7_401part0,Bool.and_self]
theorem t7_401checked : Checked tree [4,7,7,7,7,7,7] := by
  refine ⟨plan8964,valid8964,t7_401choices,?_⟩
  exact check_of_frontier tree 0 t7_401root t7_401jobs t7_401frontier t7_401all
theorem t7_402choices : plan8862.choices=[4,8,3,7,7,7,7].map (options 7 6) := by rfl


theorem t7_402part0 : t7_402jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_402frontier : t7_402root.frontier 0=t7_402jobs := by rfl
theorem t7_402all : t7_402jobs.all (Job.check tree)=true := by
  simp only [t7_402jobs,List.all_append,List.all_nil,t7_402part0,Bool.and_self]
theorem t7_402checked : Checked tree [4,8,3,7,7,7,7] := by
  refine ⟨plan8862,valid8862,t7_402choices,?_⟩
  exact check_of_frontier tree 0 t7_402root t7_402jobs t7_402frontier t7_402all
theorem t7_403choices : plan8965.choices=[4,8,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_403part0 : t7_403jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_403frontier : t7_403root.frontier 0=t7_403jobs := by rfl
theorem t7_403all : t7_403jobs.all (Job.check tree)=true := by
  simp only [t7_403jobs,List.all_append,List.all_nil,t7_403part0,Bool.and_self]
theorem t7_403checked : Checked tree [4,8,6,7,7,7,7] := by
  refine ⟨plan8965,valid8965,t7_403choices,?_⟩
  exact check_of_frontier tree 0 t7_403root t7_403jobs t7_403frontier t7_403all
theorem t7_404choices : plan8966.choices=[4,8,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_404part0 : t7_404jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_404frontier : t7_404root.frontier 0=t7_404jobs := by rfl
theorem t7_404all : t7_404jobs.all (Job.check tree)=true := by
  simp only [t7_404jobs,List.all_append,List.all_nil,t7_404part0,Bool.and_self]
theorem t7_404checked : Checked tree [4,8,7,7,7,7,7] := by
  refine ⟨plan8966,valid8966,t7_404choices,?_⟩
  exact check_of_frontier tree 0 t7_404root t7_404jobs t7_404frontier t7_404all
theorem t7_405choices : plan8967.choices=[4,8,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_405part0 : t7_405jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_405frontier : t7_405root.frontier 0=t7_405jobs := by rfl
theorem t7_405all : t7_405jobs.all (Job.check tree)=true := by
  simp only [t7_405jobs,List.all_append,List.all_nil,t7_405part0,Bool.and_self]
theorem t7_405checked : Checked tree [4,8,10,7,7,7,7] := by
  refine ⟨plan8967,valid8967,t7_405choices,?_⟩
  exact check_of_frontier tree 0 t7_405root t7_405jobs t7_405frontier t7_405all
theorem t7_406choices : plan8666.choices=[4,9,3,3,7,7,7].map (options 7 5) := by rfl


theorem t7_406part0 : t7_406jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_406frontier : t7_406root.frontier 0=t7_406jobs := by rfl
theorem t7_406all : t7_406jobs.all (Job.check tree)=true := by
  simp only [t7_406jobs,List.all_append,List.all_nil,t7_406part0,Bool.and_self]
theorem t7_406checked : Checked tree [4,9,3,3,7,7,7] := by
  refine ⟨plan8666,valid8666,t7_406choices,?_⟩
  exact check_of_frontier tree 0 t7_406root t7_406jobs t7_406frontier t7_406all
theorem t7_407choices : plan8863.choices=[4,9,3,6,7,7,7].map (options 7 6) := by rfl


theorem t7_407part0 : t7_407jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_407frontier : t7_407root.frontier 0=t7_407jobs := by rfl
theorem t7_407all : t7_407jobs.all (Job.check tree)=true := by
  simp only [t7_407jobs,List.all_append,List.all_nil,t7_407part0,Bool.and_self]
theorem t7_407checked : Checked tree [4,9,3,6,7,7,7] := by
  refine ⟨plan8863,valid8863,t7_407choices,?_⟩
  exact check_of_frontier tree 0 t7_407root t7_407jobs t7_407frontier t7_407all
theorem t7_408choices : plan8864.choices=[4,9,3,7,7,7,7].map (options 7 6) := by rfl


theorem t7_408part0 : t7_408jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_408frontier : t7_408root.frontier 0=t7_408jobs := by rfl
theorem t7_408all : t7_408jobs.all (Job.check tree)=true := by
  simp only [t7_408jobs,List.all_append,List.all_nil,t7_408part0,Bool.and_self]
theorem t7_408checked : Checked tree [4,9,3,7,7,7,7] := by
  refine ⟨plan8864,valid8864,t7_408choices,?_⟩
  exact check_of_frontier tree 0 t7_408root t7_408jobs t7_408frontier t7_408all
theorem t7_409choices : plan8865.choices=[4,9,3,10,7,7,7].map (options 7 6) := by rfl


theorem t7_409part0 : t7_409jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_409frontier : t7_409root.frontier 0=t7_409jobs := by rfl
theorem t7_409all : t7_409jobs.all (Job.check tree)=true := by
  simp only [t7_409jobs,List.all_append,List.all_nil,t7_409part0,Bool.and_self]
theorem t7_409checked : Checked tree [4,9,3,10,7,7,7] := by
  refine ⟨plan8865,valid8865,t7_409choices,?_⟩
  exact check_of_frontier tree 0 t7_409root t7_409jobs t7_409frontier t7_409all
theorem t7_410choices : plan8968.choices=[4,9,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_410part0 : t7_410jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_410frontier : t7_410root.frontier 0=t7_410jobs := by rfl
theorem t7_410all : t7_410jobs.all (Job.check tree)=true := by
  simp only [t7_410jobs,List.all_append,List.all_nil,t7_410part0,Bool.and_self]
theorem t7_410checked : Checked tree [4,9,6,6,7,7,7] := by
  refine ⟨plan8968,valid8968,t7_410choices,?_⟩
  exact check_of_frontier tree 0 t7_410root t7_410jobs t7_410frontier t7_410all
theorem t7_411choices : plan8969.choices=[4,9,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_411part0 : t7_411jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_411frontier : t7_411root.frontier 0=t7_411jobs := by rfl
theorem t7_411all : t7_411jobs.all (Job.check tree)=true := by
  simp only [t7_411jobs,List.all_append,List.all_nil,t7_411part0,Bool.and_self]
theorem t7_411checked : Checked tree [4,9,6,7,7,7,7] := by
  refine ⟨plan8969,valid8969,t7_411choices,?_⟩
  exact check_of_frontier tree 0 t7_411root t7_411jobs t7_411frontier t7_411all
theorem t7_412choices : plan8970.choices=[4,9,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_412part0 : t7_412jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_412frontier : t7_412root.frontier 0=t7_412jobs := by rfl
theorem t7_412all : t7_412jobs.all (Job.check tree)=true := by
  simp only [t7_412jobs,List.all_append,List.all_nil,t7_412part0,Bool.and_self]
theorem t7_412checked : Checked tree [4,9,6,10,7,7,7] := by
  refine ⟨plan8970,valid8970,t7_412choices,?_⟩
  exact check_of_frontier tree 0 t7_412root t7_412jobs t7_412frontier t7_412all
theorem t7_413choices : plan8971.choices=[4,9,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_413part0 : t7_413jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_413frontier : t7_413root.frontier 0=t7_413jobs := by rfl
theorem t7_413all : t7_413jobs.all (Job.check tree)=true := by
  simp only [t7_413jobs,List.all_append,List.all_nil,t7_413part0,Bool.and_self]
theorem t7_413checked : Checked tree [4,9,7,7,7,7,7] := by
  refine ⟨plan8971,valid8971,t7_413choices,?_⟩
  exact check_of_frontier tree 0 t7_413root t7_413jobs t7_413frontier t7_413all
theorem t7_414choices : plan8972.choices=[4,9,9,7,7,7,7].map (options 7 7) := by rfl


theorem t7_414part0 : t7_414jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_414frontier : t7_414root.frontier 0=t7_414jobs := by rfl
theorem t7_414all : t7_414jobs.all (Job.check tree)=true := by
  simp only [t7_414jobs,List.all_append,List.all_nil,t7_414part0,Bool.and_self]
theorem t7_414checked : Checked tree [4,9,9,7,7,7,7] := by
  refine ⟨plan8972,valid8972,t7_414choices,?_⟩
  exact check_of_frontier tree 0 t7_414root t7_414jobs t7_414frontier t7_414all
theorem t7_415choices : plan8973.choices=[4,9,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_415part0 : t7_415jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_415frontier : t7_415root.frontier 0=t7_415jobs := by rfl
theorem t7_415all : t7_415jobs.all (Job.check tree)=true := by
  simp only [t7_415jobs,List.all_append,List.all_nil,t7_415part0,Bool.and_self]
theorem t7_415checked : Checked tree [4,9,10,7,7,7,7] := by
  refine ⟨plan8973,valid8973,t7_415choices,?_⟩
  exact check_of_frontier tree 0 t7_415root t7_415jobs t7_415frontier t7_415all
theorem t7_416choices : plan8974.choices=[4,9,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_416part0 : t7_416jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_416frontier : t7_416root.frontier 0=t7_416jobs := by rfl
theorem t7_416all : t7_416jobs.all (Job.check tree)=true := by
  simp only [t7_416jobs,List.all_append,List.all_nil,t7_416part0,Bool.and_self]
theorem t7_416checked : Checked tree [4,9,10,10,7,7,7] := by
  refine ⟨plan8974,valid8974,t7_416choices,?_⟩
  exact check_of_frontier tree 0 t7_416root t7_416jobs t7_416frontier t7_416all
theorem t7_417choices : plan8975.choices=[4,10,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_417part0 : t7_417jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_417frontier : t7_417root.frontier 0=t7_417jobs := by rfl
theorem t7_417all : t7_417jobs.all (Job.check tree)=true := by
  simp only [t7_417jobs,List.all_append,List.all_nil,t7_417part0,Bool.and_self]
theorem t7_417checked : Checked tree [4,10,7,7,7,7,7] := by
  refine ⟨plan8975,valid8975,t7_417choices,?_⟩
  exact check_of_frontier tree 0 t7_417root t7_417jobs t7_417frontier t7_417all
theorem t7_418choices : plan8976.choices=[4,10,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_418part0 : t7_418jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_418frontier : t7_418root.frontier 0=t7_418jobs := by rfl
theorem t7_418all : t7_418jobs.all (Job.check tree)=true := by
  simp only [t7_418jobs,List.all_append,List.all_nil,t7_418part0,Bool.and_self]
theorem t7_418checked : Checked tree [4,10,10,7,7,7,7] := by
  refine ⟨plan8976,valid8976,t7_418choices,?_⟩
  exact check_of_frontier tree 0 t7_418root t7_418jobs t7_418frontier t7_418all
theorem t7_419choices : plan8977.choices=[4,10,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_419part0 : t7_419jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_419frontier : t7_419root.frontier 0=t7_419jobs := by rfl
theorem t7_419all : t7_419jobs.all (Job.check tree)=true := by
  simp only [t7_419jobs,List.all_append,List.all_nil,t7_419part0,Bool.and_self]
theorem t7_419checked : Checked tree [4,10,10,10,7,7,7] := by
  refine ⟨plan8977,valid8977,t7_419choices,?_⟩
  exact check_of_frontier tree 0 t7_419root t7_419jobs t7_419frontier t7_419all
theorem t7_420choices : plan8978.choices=[4,10,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_420part0 : t7_420jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_420frontier : t7_420root.frontier 0=t7_420jobs := by rfl
theorem t7_420all : t7_420jobs.all (Job.check tree)=true := by
  simp only [t7_420jobs,List.all_append,List.all_nil,t7_420part0,Bool.and_self]
theorem t7_420checked : Checked tree [4,10,10,10,10,7,7] := by
  refine ⟨plan8978,valid8978,t7_420choices,?_⟩
  exact check_of_frontier tree 0 t7_420root t7_420jobs t7_420frontier t7_420all
theorem t7_421choices : plan8428.choices=[5,3,3,3,3,3,7].map (options 7 2) := by rfl


theorem t7_421part0 : t7_421jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_421frontier : t7_421root.frontier 0=t7_421jobs := by rfl
theorem t7_421all : t7_421jobs.all (Job.check tree)=true := by
  simp only [t7_421jobs,List.all_append,List.all_nil,t7_421part0,Bool.and_self]
theorem t7_421checked : Checked tree [5,3,3,3,3,3,7] := by
  refine ⟨plan8428,valid8428,t7_421choices,?_⟩
  exact check_of_frontier tree 0 t7_421root t7_421jobs t7_421frontier t7_421all
theorem t7_422choices : plan8458.choices=[5,3,3,3,3,6,7].map (options 7 3) := by rfl


theorem t7_422part0 : t7_422jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_422frontier : t7_422root.frontier 0=t7_422jobs := by rfl
theorem t7_422all : t7_422jobs.all (Job.check tree)=true := by
  simp only [t7_422jobs,List.all_append,List.all_nil,t7_422part0,Bool.and_self]
theorem t7_422checked : Checked tree [5,3,3,3,3,6,7] := by
  refine ⟨plan8458,valid8458,t7_422choices,?_⟩
  exact check_of_frontier tree 0 t7_422root t7_422jobs t7_422frontier t7_422all
theorem t7_423choices : plan8459.choices=[5,3,3,3,3,7,7].map (options 7 3) := by rfl


theorem t7_423part0 : t7_423jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_423part1 : t7_423jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_423frontier : t7_423root.frontier 1=t7_423jobs := by rfl
theorem t7_423all : t7_423jobs.all (Job.check tree)=true := by
  simp only [t7_423jobs,List.all_append,List.all_nil,t7_423part0,t7_423part1,Bool.and_self]
theorem t7_423checked : Checked tree [5,3,3,3,3,7,7] := by
  refine ⟨plan8459,valid8459,t7_423choices,?_⟩
  exact check_of_frontier tree 1 t7_423root t7_423jobs t7_423frontier t7_423all
theorem t7_424choices : plan8460.choices=[5,3,3,3,3,10,7].map (options 7 3) := by rfl


theorem t7_424part0 : t7_424jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_424frontier : t7_424root.frontier 0=t7_424jobs := by rfl
theorem t7_424all : t7_424jobs.all (Job.check tree)=true := by
  simp only [t7_424jobs,List.all_append,List.all_nil,t7_424part0,Bool.and_self]
theorem t7_424checked : Checked tree [5,3,3,3,3,10,7] := by
  refine ⟨plan8460,valid8460,t7_424choices,?_⟩
  exact check_of_frontier tree 0 t7_424root t7_424jobs t7_424frontier t7_424all
theorem t7_425choices : plan8528.choices=[5,3,3,3,6,6,7].map (options 7 4) := by rfl


theorem t7_425part0 : t7_425jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_425frontier : t7_425root.frontier 0=t7_425jobs := by rfl
theorem t7_425all : t7_425jobs.all (Job.check tree)=true := by
  simp only [t7_425jobs,List.all_append,List.all_nil,t7_425part0,Bool.and_self]
theorem t7_425checked : Checked tree [5,3,3,3,6,6,7] := by
  refine ⟨plan8528,valid8528,t7_425choices,?_⟩
  exact check_of_frontier tree 0 t7_425root t7_425jobs t7_425frontier t7_425all
theorem t7_426choices : plan8529.choices=[5,3,3,3,6,7,7].map (options 7 4) := by rfl


theorem t7_426part0 : t7_426jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_426part1 : t7_426jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_426part2 : t7_426jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_426frontier : t7_426root.frontier 1=t7_426jobs := by rfl
theorem t7_426all : t7_426jobs.all (Job.check tree)=true := by
  simp only [t7_426jobs,List.all_append,List.all_nil,t7_426part0,t7_426part1,t7_426part2,Bool.and_self]
theorem t7_426checked : Checked tree [5,3,3,3,6,7,7] := by
  refine ⟨plan8529,valid8529,t7_426choices,?_⟩
  exact check_of_frontier tree 1 t7_426root t7_426jobs t7_426frontier t7_426all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks184 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_363checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_376checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_377checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_378checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_379checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_380checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_381checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_382checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_383checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_384checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_385checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_364checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_386checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_387checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_388checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_389checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_390checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_391checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_392checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_393checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_394checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_395checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_365checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_396checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_397checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_398checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_399checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_400checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_401checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_402checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_403checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_404checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_405checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_366checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_406checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_407checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_408checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_409checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_410checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_411checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_412checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_413checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_414checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_415checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_367checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_416checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_417checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_418checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_419checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_420checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_421checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_422checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_423checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_424checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_368checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_425checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_426checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_369checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_370checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_371checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_372checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_373checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_374checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_375checked⟩
