-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks189
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:19:15.826482+00:00
-- url     : https://prove2.me/submissions/d84358a4-041a-4576-b85c-d502ee9811d0

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks189
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks189
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

















































theorem valid601 : plan601.Valid := valid_step _ _ _ valid147 (by decide +kernel)











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





theorem valid1635 : plan1635.Valid := valid_step _ _ _ valid601 (by decide +kernel)































theorem valid1651 : plan1651.Valid := valid_step _ _ _ valid607 (by decide +kernel)





theorem valid1654 : plan1654.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1655 : plan1655.Valid := valid_step _ _ _ valid607 (by decide +kernel)











theorem valid1661 : plan1661.Valid := valid_step _ _ _ valid613 (by decide +kernel)





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

































theorem valid3569 : plan3569.Valid := valid_step _ _ _ valid1635 (by decide +kernel)



























theorem valid3583 : plan3583.Valid := valid_step _ _ _ valid1651 (by decide +kernel)



theorem valid3585 : plan3585.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

theorem valid3586 : plan3586.Valid := valid_step _ _ _ valid1655 (by decide +kernel)



































theorem valid3604 : plan3604.Valid := valid_step _ _ _ valid1664 (by decide +kernel)









theorem valid3609 : plan3609.Valid := valid_step _ _ _ valid1661 (by decide +kernel)





theorem valid3612 : plan3612.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3613 : plan3613.Valid := valid_step _ _ _ valid1665 (by decide +kernel)





theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

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











































































































































theorem valid6118 : plan6118.Valid := valid_step _ _ _ valid3569 (by decide +kernel)

































theorem valid6135 : plan6135.Valid := valid_step _ _ _ valid3583 (by decide +kernel)



theorem valid6137 : plan6137.Valid := valid_step _ _ _ valid3585 (by decide +kernel)

theorem valid6138 : plan6138.Valid := valid_step _ _ _ valid3586 (by decide +kernel)












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





theorem valid6162 : plan6162.Valid := valid_step _ _ _ valid3609 (by decide +kernel)



theorem valid6164 : plan6164.Valid := valid_step _ _ _ valid3612 (by decide +kernel)

theorem valid6165 : plan6165.Valid := valid_step _ _ _ valid3613 (by decide +kernel)



theorem valid6167 : plan6167.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6168 : plan6168.Valid := valid_step _ _ _ valid3617 (by decide +kernel)

theorem valid6169 : plan6169.Valid := valid_step _ _ _ valid3618 (by decide +kernel)































































theorem valid6201 : plan6201.Valid := valid_step _ _ _ valid3628 (by decide +kernel)



theorem valid6203 : plan6203.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6204 : plan6204.Valid := valid_step _ _ _ valid3633 (by decide +kernel)







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

















































theorem valid8089 : plan8089.Valid := valid_step _ _ _ valid6118 (by decide +kernel)























































theorem valid8117 : plan8117.Valid := valid_step _ _ _ valid6135 (by decide +kernel)



theorem valid8119 : plan8119.Valid := valid_step _ _ _ valid6137 (by decide +kernel)

theorem valid8120 : plan8120.Valid := valid_step _ _ _ valid6138 (by decide +kernel)

























































theorem valid8149 : plan8149.Valid := valid_step _ _ _ valid6164 (by decide +kernel)

theorem valid8150 : plan8150.Valid := valid_step _ _ _ valid6167 (by decide +kernel)

theorem valid8151 : plan8151.Valid := valid_step _ _ _ valid6168 (by decide +kernel)


















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

























theorem valid8461 : plan8461.Valid := valid_step _ _ _ valid8089 (by decide +kernel)























































































































































theorem valid8537 : plan8537.Valid := valid_step _ _ _ valid8117 (by decide +kernel)

theorem valid8538 : plan8538.Valid := valid_step _ _ _ valid8119 (by decide +kernel)

theorem valid8539 : plan8539.Valid := valid_step _ _ _ valid8120 (by decide +kernel)










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

















theorem valid8169 : plan8169.Valid := valid_step _ _ _ valid6162 (by decide +kernel)



theorem valid8171 : plan8171.Valid := valid_step _ _ _ valid6164 (by decide +kernel)

theorem valid8172 : plan8172.Valid := valid_step _ _ _ valid6165 (by decide +kernel)



theorem valid8174 : plan8174.Valid := valid_step _ _ _ valid6167 (by decide +kernel)

theorem valid8175 : plan8175.Valid := valid_step _ _ _ valid6168 (by decide +kernel)

theorem valid8176 : plan8176.Valid := valid_step _ _ _ valid6169 (by decide +kernel)

















































theorem valid8201 : plan8201.Valid := valid_step _ _ _ valid6159 (by decide +kernel)























theorem valid8213 : plan8213.Valid := valid_step _ _ _ valid6159 (by decide +kernel)

















theorem valid8222 : plan8222.Valid := valid_step _ _ _ valid6208 (by decide +kernel)

theorem valid8223 : plan8223.Valid := valid_step _ _ _ valid6216 (by decide +kernel)

theorem valid8224 : plan8224.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8225 : plan8225.Valid := valid_step _ _ _ valid6221 (by decide +kernel)

theorem valid8226 : plan8226.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8227 : plan8227.Valid := valid_step _ _ _ valid6228 (by decide +kernel)

theorem valid8228 : plan8228.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8229 : plan8229.Valid := valid_step _ _ _ valid6231 (by decide +kernel)



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























































































theorem valid8684 : plan8684.Valid := valid_step _ _ _ valid8149 (by decide +kernel)

theorem valid8685 : plan8685.Valid := valid_step _ _ _ valid8150 (by decide +kernel)

theorem valid8686 : plan8686.Valid := valid_step _ _ _ valid8151 (by decide +kernel)

theorem valid8687 : plan8687.Valid := valid_step _ _ _ valid8169 (by decide +kernel)

theorem valid8688 : plan8688.Valid := valid_step _ _ _ valid8171 (by decide +kernel)

theorem valid8689 : plan8689.Valid := valid_step _ _ _ valid8172 (by decide +kernel)

theorem valid8690 : plan8690.Valid := valid_step _ _ _ valid8174 (by decide +kernel)

theorem valid8691 : plan8691.Valid := valid_step _ _ _ valid8175 (by decide +kernel)

theorem valid8692 : plan8692.Valid := valid_step _ _ _ valid8176 (by decide +kernel)

theorem valid8693 : plan8693.Valid := valid_step _ _ _ valid8201 (by decide +kernel)

theorem valid8694 : plan8694.Valid := valid_step _ _ _ valid8213 (by decide +kernel)




















































































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































































































































theorem valid8896 : plan8896.Valid := valid_step _ _ _ valid8222 (by decide +kernel)

theorem valid8897 : plan8897.Valid := valid_step _ _ _ valid8223 (by decide +kernel)

theorem valid8898 : plan8898.Valid := valid_step _ _ _ valid8224 (by decide +kernel)

theorem valid8899 : plan8899.Valid := valid_step _ _ _ valid8225 (by decide +kernel)

theorem valid8900 : plan8900.Valid := valid_step _ _ _ valid8226 (by decide +kernel)

theorem valid8901 : plan8901.Valid := valid_step _ _ _ valid8227 (by decide +kernel)

theorem valid8902 : plan8902.Valid := valid_step _ _ _ valid8228 (by decide +kernel)

theorem valid8903 : plan8903.Valid := valid_step _ _ _ valid8229 (by decide +kernel)

theorem valid8904 : plan8904.Valid := valid_step _ _ _ valid8231 (by decide +kernel)

theorem valid8905 : plan8905.Valid := valid_step _ _ _ valid8233 (by decide +kernel)

theorem valid8906 : plan8906.Valid := valid_step _ _ _ valid8234 (by decide +kernel)

theorem valid8907 : plan8907.Valid := valid_step _ _ _ valid8236 (by decide +kernel)

theorem valid8908 : plan8908.Valid := valid_step _ _ _ valid8237 (by decide +kernel)

theorem valid8909 : plan8909.Valid := valid_step _ _ _ valid8238 (by decide +kernel)

theorem valid8910 : plan8910.Valid := valid_step _ _ _ valid8240 (by decide +kernel)

theorem valid8911 : plan8911.Valid := valid_step _ _ _ valid8241 (by decide +kernel)

theorem valid8912 : plan8912.Valid := valid_step _ _ _ valid8242 (by decide +kernel)

theorem valid8913 : plan8913.Valid := valid_step _ _ _ valid8243 (by decide +kernel)

theorem valid8914 : plan8914.Valid := valid_step _ _ _ valid8250 (by decide +kernel)

theorem valid8915 : plan8915.Valid := valid_step _ _ _ valid8252 (by decide +kernel)

theorem valid8916 : plan8916.Valid := valid_step _ _ _ valid8253 (by decide +kernel)

theorem valid8917 : plan8917.Valid := valid_step _ _ _ valid8295 (by decide +kernel)

theorem valid8918 : plan8918.Valid := valid_step _ _ _ valid8300 (by decide +kernel)

theorem valid8919 : plan8919.Valid := valid_step _ _ _ valid8302 (by decide +kernel)

theorem valid8920 : plan8920.Valid := valid_step _ _ _ valid8303 (by decide +kernel)
















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



































































theorem valid9058 : plan9058.Valid := valid_step _ _ _ valid8329 (by decide +kernel)

theorem valid9059 : plan9059.Valid := valid_step _ _ _ valid8332 (by decide +kernel)

theorem valid9060 : plan9060.Valid := valid_step _ _ _ valid8334 (by decide +kernel)

theorem valid9061 : plan9061.Valid := valid_step _ _ _ valid8335 (by decide +kernel)

theorem valid9062 : plan9062.Valid := valid_step _ _ _ valid8337 (by decide +kernel)

theorem valid9063 : plan9063.Valid := valid_step _ _ _ valid8339 (by decide +kernel)

theorem valid9064 : plan9064.Valid := valid_step _ _ _ valid8341 (by decide +kernel)

theorem valid9065 : plan9065.Valid := valid_step _ _ _ valid8342 (by decide +kernel)

theorem valid9066 : plan9066.Valid := valid_step _ _ _ valid8347 (by decide +kernel)

theorem valid9067 : plan9067.Valid := valid_step _ _ _ valid8350 (by decide +kernel)

theorem valid9068 : plan9068.Valid := valid_step _ _ _ valid8351 (by decide +kernel)

theorem valid9069 : plan9069.Valid := valid_step _ _ _ valid8354 (by decide +kernel)

theorem valid9070 : plan9070.Valid := valid_step _ _ _ valid8355 (by decide +kernel)

theorem valid9071 : plan9071.Valid := valid_step _ _ _ valid8356 (by decide +kernel)

theorem valid9072 : plan9072.Valid := valid_step _ _ _ valid8359 (by decide +kernel)

theorem valid9073 : plan9073.Valid := valid_step _ _ _ valid8360 (by decide +kernel)

theorem valid9074 : plan9074.Valid := valid_step _ _ _ valid8361 (by decide +kernel)

theorem valid9075 : plan9075.Valid := valid_step _ _ _ valid8362 (by decide +kernel)

theorem valid9076 : plan9076.Valid := valid_step _ _ _ valid8365 (by decide +kernel)

theorem valid9077 : plan9077.Valid := valid_step _ _ _ valid8366 (by decide +kernel)

theorem valid9078 : plan9078.Valid := valid_step _ _ _ valid8367 (by decide +kernel)

theorem valid9079 : plan9079.Valid := valid_step _ _ _ valid8368 (by decide +kernel)

theorem valid9080 : plan9080.Valid := valid_step _ _ _ valid8370 (by decide +kernel)

theorem valid9081 : plan9081.Valid := valid_step _ _ _ valid8372 (by decide +kernel)

theorem valid9082 : plan9082.Valid := valid_step _ _ _ valid8373 (by decide +kernel)

theorem valid9083 : plan9083.Valid := valid_step _ _ _ valid8375 (by decide +kernel)

theorem valid9084 : plan9084.Valid := valid_step _ _ _ valid8377 (by decide +kernel)

theorem valid9085 : plan9085.Valid := valid_step _ _ _ valid8379 (by decide +kernel)

theorem valid9086 : plan9086.Valid := valid_step _ _ _ valid8380 (by decide +kernel)

theorem valid9087 : plan9087.Valid := valid_step _ _ _ valid8382 (by decide +kernel)

theorem valid9088 : plan9088.Valid := valid_step _ _ _ valid8383 (by decide +kernel)

theorem valid9089 : plan9089.Valid := valid_step _ _ _ valid8384 (by decide +kernel)

theorem valid9090 : plan9090.Valid := valid_step _ _ _ valid8385 (by decide +kernel)




























































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
theorem t7_560choices : plan8684.choices=[8,2,3,6,7,7,7].map (options 7 5) := by rfl


theorem t7_560part0 : t7_560jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_560frontier : t7_560root.frontier 0=t7_560jobs := by rfl
theorem t7_560all : t7_560jobs.all (Job.check tree)=true := by
  simp only [t7_560jobs,List.all_append,List.all_nil,t7_560part0,Bool.and_self]
theorem t7_560checked : Checked tree [8,2,3,6,7,7,7] := by
  refine ⟨plan8684,valid8684,t7_560choices,?_⟩
  exact check_of_frontier tree 0 t7_560root t7_560jobs t7_560frontier t7_560all
theorem t7_561choices : plan8685.choices=[8,2,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_561part0 : t7_561jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_561frontier : t7_561root.frontier 0=t7_561jobs := by rfl
theorem t7_561all : t7_561jobs.all (Job.check tree)=true := by
  simp only [t7_561jobs,List.all_append,List.all_nil,t7_561part0,Bool.and_self]
theorem t7_561checked : Checked tree [8,2,3,7,7,7,7] := by
  refine ⟨plan8685,valid8685,t7_561choices,?_⟩
  exact check_of_frontier tree 0 t7_561root t7_561jobs t7_561frontier t7_561all
theorem t7_562choices : plan8686.choices=[8,2,3,10,7,7,7].map (options 7 5) := by rfl


theorem t7_562part0 : t7_562jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_562frontier : t7_562root.frontier 0=t7_562jobs := by rfl
theorem t7_562all : t7_562jobs.all (Job.check tree)=true := by
  simp only [t7_562jobs,List.all_append,List.all_nil,t7_562part0,Bool.and_self]
theorem t7_562checked : Checked tree [8,2,3,10,7,7,7] := by
  refine ⟨plan8686,valid8686,t7_562choices,?_⟩
  exact check_of_frontier tree 0 t7_562root t7_562jobs t7_562frontier t7_562all
theorem t7_563choices : plan8896.choices=[8,2,5,7,7,7,7].map (options 7 6) := by rfl


theorem t7_563part0 : t7_563jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_563frontier : t7_563root.frontier 0=t7_563jobs := by rfl
theorem t7_563all : t7_563jobs.all (Job.check tree)=true := by
  simp only [t7_563jobs,List.all_append,List.all_nil,t7_563part0,Bool.and_self]
theorem t7_563checked : Checked tree [8,2,5,7,7,7,7] := by
  refine ⟨plan8896,valid8896,t7_563choices,?_⟩
  exact check_of_frontier tree 0 t7_563root t7_563jobs t7_563frontier t7_563all
theorem t7_564choices : plan8897.choices=[8,2,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_564part0 : t7_564jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_564frontier : t7_564root.frontier 0=t7_564jobs := by rfl
theorem t7_564all : t7_564jobs.all (Job.check tree)=true := by
  simp only [t7_564jobs,List.all_append,List.all_nil,t7_564part0,Bool.and_self]
theorem t7_564checked : Checked tree [8,2,6,6,7,7,7] := by
  refine ⟨plan8897,valid8897,t7_564choices,?_⟩
  exact check_of_frontier tree 0 t7_564root t7_564jobs t7_564frontier t7_564all
theorem t7_565choices : plan8898.choices=[8,2,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_565part0 : t7_565jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_565frontier : t7_565root.frontier 0=t7_565jobs := by rfl
theorem t7_565all : t7_565jobs.all (Job.check tree)=true := by
  simp only [t7_565jobs,List.all_append,List.all_nil,t7_565part0,Bool.and_self]
theorem t7_565checked : Checked tree [8,2,6,7,7,7,7] := by
  refine ⟨plan8898,valid8898,t7_565choices,?_⟩
  exact check_of_frontier tree 0 t7_565root t7_565jobs t7_565frontier t7_565all
theorem t7_566choices : plan8899.choices=[8,2,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_566part0 : t7_566jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_566frontier : t7_566root.frontier 0=t7_566jobs := by rfl
theorem t7_566all : t7_566jobs.all (Job.check tree)=true := by
  simp only [t7_566jobs,List.all_append,List.all_nil,t7_566part0,Bool.and_self]
theorem t7_566checked : Checked tree [8,2,6,10,7,7,7] := by
  refine ⟨plan8899,valid8899,t7_566choices,?_⟩
  exact check_of_frontier tree 0 t7_566root t7_566jobs t7_566frontier t7_566all
theorem t7_567choices : plan8900.choices=[8,2,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_567part0 : t7_567jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_567frontier : t7_567root.frontier 0=t7_567jobs := by rfl
theorem t7_567all : t7_567jobs.all (Job.check tree)=true := by
  simp only [t7_567jobs,List.all_append,List.all_nil,t7_567part0,Bool.and_self]
theorem t7_567checked : Checked tree [8,2,7,7,7,7,7] := by
  refine ⟨plan8900,valid8900,t7_567choices,?_⟩
  exact check_of_frontier tree 0 t7_567root t7_567jobs t7_567frontier t7_567all
theorem t7_568choices : plan8901.choices=[8,2,9,7,7,7,7].map (options 7 6) := by rfl


theorem t7_568part0 : t7_568jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_568frontier : t7_568root.frontier 0=t7_568jobs := by rfl
theorem t7_568all : t7_568jobs.all (Job.check tree)=true := by
  simp only [t7_568jobs,List.all_append,List.all_nil,t7_568part0,Bool.and_self]
theorem t7_568checked : Checked tree [8,2,9,7,7,7,7] := by
  refine ⟨plan8901,valid8901,t7_568choices,?_⟩
  exact check_of_frontier tree 0 t7_568root t7_568jobs t7_568frontier t7_568all
theorem t7_569choices : plan8902.choices=[8,2,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_569part0 : t7_569jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_569frontier : t7_569root.frontier 0=t7_569jobs := by rfl
theorem t7_569all : t7_569jobs.all (Job.check tree)=true := by
  simp only [t7_569jobs,List.all_append,List.all_nil,t7_569part0,Bool.and_self]
theorem t7_569checked : Checked tree [8,2,10,7,7,7,7] := by
  refine ⟨plan8902,valid8902,t7_569choices,?_⟩
  exact check_of_frontier tree 0 t7_569root t7_569jobs t7_569frontier t7_569all
theorem t7_570choices : plan8903.choices=[8,2,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_570part0 : t7_570jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_570frontier : t7_570root.frontier 0=t7_570jobs := by rfl
theorem t7_570all : t7_570jobs.all (Job.check tree)=true := by
  simp only [t7_570jobs,List.all_append,List.all_nil,t7_570part0,Bool.and_self]
theorem t7_570checked : Checked tree [8,2,10,10,7,7,7] := by
  refine ⟨plan8903,valid8903,t7_570choices,?_⟩
  exact check_of_frontier tree 0 t7_570root t7_570jobs t7_570frontier t7_570all
theorem t7_571choices : plan8461.choices=[8,3,3,3,3,7,7].map (options 7 3) := by rfl


theorem t7_571part0 : t7_571jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_571frontier : t7_571root.frontier 0=t7_571jobs := by rfl
theorem t7_571all : t7_571jobs.all (Job.check tree)=true := by
  simp only [t7_571jobs,List.all_append,List.all_nil,t7_571part0,Bool.and_self]
theorem t7_571checked : Checked tree [8,3,3,3,3,7,7] := by
  refine ⟨plan8461,valid8461,t7_571choices,?_⟩
  exact check_of_frontier tree 0 t7_571root t7_571jobs t7_571frontier t7_571all
theorem t7_572choices : plan8537.choices=[8,3,3,3,6,7,7].map (options 7 4) := by rfl


theorem t7_572part0 : t7_572jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_572frontier : t7_572root.frontier 0=t7_572jobs := by rfl
theorem t7_572all : t7_572jobs.all (Job.check tree)=true := by
  simp only [t7_572jobs,List.all_append,List.all_nil,t7_572part0,Bool.and_self]
theorem t7_572checked : Checked tree [8,3,3,3,6,7,7] := by
  refine ⟨plan8537,valid8537,t7_572choices,?_⟩
  exact check_of_frontier tree 0 t7_572root t7_572jobs t7_572frontier t7_572all
theorem t7_573choices : plan8538.choices=[8,3,3,3,7,7,7].map (options 7 4) := by rfl


theorem t7_573part0 : t7_573jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_573frontier : t7_573root.frontier 0=t7_573jobs := by rfl
theorem t7_573all : t7_573jobs.all (Job.check tree)=true := by
  simp only [t7_573jobs,List.all_append,List.all_nil,t7_573part0,Bool.and_self]
theorem t7_573checked : Checked tree [8,3,3,3,7,7,7] := by
  refine ⟨plan8538,valid8538,t7_573choices,?_⟩
  exact check_of_frontier tree 0 t7_573root t7_573jobs t7_573frontier t7_573all
theorem t7_574choices : plan8539.choices=[8,3,3,3,10,7,7].map (options 7 4) := by rfl


theorem t7_574part0 : t7_574jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_574frontier : t7_574root.frontier 0=t7_574jobs := by rfl
theorem t7_574all : t7_574jobs.all (Job.check tree)=true := by
  simp only [t7_574jobs,List.all_append,List.all_nil,t7_574part0,Bool.and_self]
theorem t7_574checked : Checked tree [8,3,3,3,10,7,7] := by
  refine ⟨plan8539,valid8539,t7_574choices,?_⟩
  exact check_of_frontier tree 0 t7_574root t7_574jobs t7_574frontier t7_574all
theorem t7_575choices : plan8687.choices=[8,3,3,6,6,7,7].map (options 7 5) := by rfl


theorem t7_575part0 : t7_575jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_575frontier : t7_575root.frontier 0=t7_575jobs := by rfl
theorem t7_575all : t7_575jobs.all (Job.check tree)=true := by
  simp only [t7_575jobs,List.all_append,List.all_nil,t7_575part0,Bool.and_self]
theorem t7_575checked : Checked tree [8,3,3,6,6,7,7] := by
  refine ⟨plan8687,valid8687,t7_575choices,?_⟩
  exact check_of_frontier tree 0 t7_575root t7_575jobs t7_575frontier t7_575all
theorem t7_576choices : plan8688.choices=[8,3,3,6,7,7,7].map (options 7 5) := by rfl


theorem t7_576part0 : t7_576jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_576frontier : t7_576root.frontier 0=t7_576jobs := by rfl
theorem t7_576all : t7_576jobs.all (Job.check tree)=true := by
  simp only [t7_576jobs,List.all_append,List.all_nil,t7_576part0,Bool.and_self]
theorem t7_576checked : Checked tree [8,3,3,6,7,7,7] := by
  refine ⟨plan8688,valid8688,t7_576choices,?_⟩
  exact check_of_frontier tree 0 t7_576root t7_576jobs t7_576frontier t7_576all
theorem t7_577choices : plan8689.choices=[8,3,3,6,10,7,7].map (options 7 5) := by rfl


theorem t7_577part0 : t7_577jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_577frontier : t7_577root.frontier 0=t7_577jobs := by rfl
theorem t7_577all : t7_577jobs.all (Job.check tree)=true := by
  simp only [t7_577jobs,List.all_append,List.all_nil,t7_577part0,Bool.and_self]
theorem t7_577checked : Checked tree [8,3,3,6,10,7,7] := by
  refine ⟨plan8689,valid8689,t7_577choices,?_⟩
  exact check_of_frontier tree 0 t7_577root t7_577jobs t7_577frontier t7_577all
theorem t7_578choices : plan8690.choices=[8,3,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_578part0 : t7_578jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_578frontier : t7_578root.frontier 0=t7_578jobs := by rfl
theorem t7_578all : t7_578jobs.all (Job.check tree)=true := by
  simp only [t7_578jobs,List.all_append,List.all_nil,t7_578part0,Bool.and_self]
theorem t7_578checked : Checked tree [8,3,3,7,7,7,7] := by
  refine ⟨plan8690,valid8690,t7_578choices,?_⟩
  exact check_of_frontier tree 0 t7_578root t7_578jobs t7_578frontier t7_578all
theorem t7_579choices : plan8691.choices=[8,3,3,10,7,7,7].map (options 7 5) := by rfl


theorem t7_579part0 : t7_579jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_579frontier : t7_579root.frontier 0=t7_579jobs := by rfl
theorem t7_579all : t7_579jobs.all (Job.check tree)=true := by
  simp only [t7_579jobs,List.all_append,List.all_nil,t7_579part0,Bool.and_self]
theorem t7_579checked : Checked tree [8,3,3,10,7,7,7] := by
  refine ⟨plan8691,valid8691,t7_579choices,?_⟩
  exact check_of_frontier tree 0 t7_579root t7_579jobs t7_579frontier t7_579all
theorem t7_580choices : plan8692.choices=[8,3,3,10,10,7,7].map (options 7 5) := by rfl


theorem t7_580part0 : t7_580jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_580frontier : t7_580root.frontier 0=t7_580jobs := by rfl
theorem t7_580all : t7_580jobs.all (Job.check tree)=true := by
  simp only [t7_580jobs,List.all_append,List.all_nil,t7_580part0,Bool.and_self]
theorem t7_580checked : Checked tree [8,3,3,10,10,7,7] := by
  refine ⟨plan8692,valid8692,t7_580choices,?_⟩
  exact check_of_frontier tree 0 t7_580root t7_580jobs t7_580frontier t7_580all
theorem t7_581choices : plan8904.choices=[8,3,6,6,6,7,7].map (options 7 6) := by rfl


theorem t7_581part0 : t7_581jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_581frontier : t7_581root.frontier 0=t7_581jobs := by rfl
theorem t7_581all : t7_581jobs.all (Job.check tree)=true := by
  simp only [t7_581jobs,List.all_append,List.all_nil,t7_581part0,Bool.and_self]
theorem t7_581checked : Checked tree [8,3,6,6,6,7,7] := by
  refine ⟨plan8904,valid8904,t7_581choices,?_⟩
  exact check_of_frontier tree 0 t7_581root t7_581jobs t7_581frontier t7_581all
theorem t7_582choices : plan8905.choices=[8,3,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_582part0 : t7_582jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_582frontier : t7_582root.frontier 0=t7_582jobs := by rfl
theorem t7_582all : t7_582jobs.all (Job.check tree)=true := by
  simp only [t7_582jobs,List.all_append,List.all_nil,t7_582part0,Bool.and_self]
theorem t7_582checked : Checked tree [8,3,6,6,7,7,7] := by
  refine ⟨plan8905,valid8905,t7_582choices,?_⟩
  exact check_of_frontier tree 0 t7_582root t7_582jobs t7_582frontier t7_582all
theorem t7_583choices : plan8906.choices=[8,3,6,6,10,7,7].map (options 7 6) := by rfl


theorem t7_583part0 : t7_583jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_583frontier : t7_583root.frontier 0=t7_583jobs := by rfl
theorem t7_583all : t7_583jobs.all (Job.check tree)=true := by
  simp only [t7_583jobs,List.all_append,List.all_nil,t7_583part0,Bool.and_self]
theorem t7_583checked : Checked tree [8,3,6,6,10,7,7] := by
  refine ⟨plan8906,valid8906,t7_583choices,?_⟩
  exact check_of_frontier tree 0 t7_583root t7_583jobs t7_583frontier t7_583all
theorem t7_584choices : plan8907.choices=[8,3,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_584part0 : t7_584jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_584frontier : t7_584root.frontier 0=t7_584jobs := by rfl
theorem t7_584all : t7_584jobs.all (Job.check tree)=true := by
  simp only [t7_584jobs,List.all_append,List.all_nil,t7_584part0,Bool.and_self]
theorem t7_584checked : Checked tree [8,3,6,7,7,7,7] := by
  refine ⟨plan8907,valid8907,t7_584choices,?_⟩
  exact check_of_frontier tree 0 t7_584root t7_584jobs t7_584frontier t7_584all
theorem t7_585choices : plan8908.choices=[8,3,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_585part0 : t7_585jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_585frontier : t7_585root.frontier 0=t7_585jobs := by rfl
theorem t7_585all : t7_585jobs.all (Job.check tree)=true := by
  simp only [t7_585jobs,List.all_append,List.all_nil,t7_585part0,Bool.and_self]
theorem t7_585checked : Checked tree [8,3,6,10,7,7,7] := by
  refine ⟨plan8908,valid8908,t7_585choices,?_⟩
  exact check_of_frontier tree 0 t7_585root t7_585jobs t7_585frontier t7_585all
theorem t7_586choices : plan8909.choices=[8,3,6,10,10,7,7].map (options 7 6) := by rfl


theorem t7_586part0 : t7_586jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_586frontier : t7_586root.frontier 0=t7_586jobs := by rfl
theorem t7_586all : t7_586jobs.all (Job.check tree)=true := by
  simp only [t7_586jobs,List.all_append,List.all_nil,t7_586part0,Bool.and_self]
theorem t7_586checked : Checked tree [8,3,6,10,10,7,7] := by
  refine ⟨plan8909,valid8909,t7_586choices,?_⟩
  exact check_of_frontier tree 0 t7_586root t7_586jobs t7_586frontier t7_586all
theorem t7_587choices : plan8910.choices=[8,3,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_587part0 : t7_587jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_587frontier : t7_587root.frontier 0=t7_587jobs := by rfl
theorem t7_587all : t7_587jobs.all (Job.check tree)=true := by
  simp only [t7_587jobs,List.all_append,List.all_nil,t7_587part0,Bool.and_self]
theorem t7_587checked : Checked tree [8,3,7,7,7,7,7] := by
  refine ⟨plan8910,valid8910,t7_587choices,?_⟩
  exact check_of_frontier tree 0 t7_587root t7_587jobs t7_587frontier t7_587all
theorem t7_588choices : plan8911.choices=[8,3,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_588part0 : t7_588jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_588frontier : t7_588root.frontier 0=t7_588jobs := by rfl
theorem t7_588all : t7_588jobs.all (Job.check tree)=true := by
  simp only [t7_588jobs,List.all_append,List.all_nil,t7_588part0,Bool.and_self]
theorem t7_588checked : Checked tree [8,3,10,7,7,7,7] := by
  refine ⟨plan8911,valid8911,t7_588choices,?_⟩
  exact check_of_frontier tree 0 t7_588root t7_588jobs t7_588frontier t7_588all
theorem t7_589choices : plan8912.choices=[8,3,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_589part0 : t7_589jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_589frontier : t7_589root.frontier 0=t7_589jobs := by rfl
theorem t7_589all : t7_589jobs.all (Job.check tree)=true := by
  simp only [t7_589jobs,List.all_append,List.all_nil,t7_589part0,Bool.and_self]
theorem t7_589checked : Checked tree [8,3,10,10,7,7,7] := by
  refine ⟨plan8912,valid8912,t7_589choices,?_⟩
  exact check_of_frontier tree 0 t7_589root t7_589jobs t7_589frontier t7_589all
theorem t7_590choices : plan8913.choices=[8,3,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_590part0 : t7_590jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_590frontier : t7_590root.frontier 0=t7_590jobs := by rfl
theorem t7_590all : t7_590jobs.all (Job.check tree)=true := by
  simp only [t7_590jobs,List.all_append,List.all_nil,t7_590part0,Bool.and_self]
theorem t7_590checked : Checked tree [8,3,10,10,10,7,7] := by
  refine ⟨plan8913,valid8913,t7_590choices,?_⟩
  exact check_of_frontier tree 0 t7_590root t7_590jobs t7_590frontier t7_590all
theorem t7_591choices : plan8693.choices=[8,5,3,3,7,7,7].map (options 7 5) := by rfl


theorem t7_591part0 : t7_591jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_591frontier : t7_591root.frontier 0=t7_591jobs := by rfl
theorem t7_591all : t7_591jobs.all (Job.check tree)=true := by
  simp only [t7_591jobs,List.all_append,List.all_nil,t7_591part0,Bool.and_self]
theorem t7_591checked : Checked tree [8,5,3,3,7,7,7] := by
  refine ⟨plan8693,valid8693,t7_591choices,?_⟩
  exact check_of_frontier tree 0 t7_591root t7_591jobs t7_591frontier t7_591all
theorem t7_592choices : plan8914.choices=[8,5,3,6,7,7,7].map (options 7 6) := by rfl


theorem t7_592part0 : t7_592jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_592frontier : t7_592root.frontier 0=t7_592jobs := by rfl
theorem t7_592all : t7_592jobs.all (Job.check tree)=true := by
  simp only [t7_592jobs,List.all_append,List.all_nil,t7_592part0,Bool.and_self]
theorem t7_592checked : Checked tree [8,5,3,6,7,7,7] := by
  refine ⟨plan8914,valid8914,t7_592choices,?_⟩
  exact check_of_frontier tree 0 t7_592root t7_592jobs t7_592frontier t7_592all
theorem t7_593choices : plan8915.choices=[8,5,3,7,7,7,7].map (options 7 6) := by rfl


theorem t7_593part0 : t7_593jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_593frontier : t7_593root.frontier 0=t7_593jobs := by rfl
theorem t7_593all : t7_593jobs.all (Job.check tree)=true := by
  simp only [t7_593jobs,List.all_append,List.all_nil,t7_593part0,Bool.and_self]
theorem t7_593checked : Checked tree [8,5,3,7,7,7,7] := by
  refine ⟨plan8915,valid8915,t7_593choices,?_⟩
  exact check_of_frontier tree 0 t7_593root t7_593jobs t7_593frontier t7_593all
theorem t7_594choices : plan8916.choices=[8,5,3,10,7,7,7].map (options 7 6) := by rfl


theorem t7_594part0 : t7_594jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_594frontier : t7_594root.frontier 0=t7_594jobs := by rfl
theorem t7_594all : t7_594jobs.all (Job.check tree)=true := by
  simp only [t7_594jobs,List.all_append,List.all_nil,t7_594part0,Bool.and_self]
theorem t7_594checked : Checked tree [8,5,3,10,7,7,7] := by
  refine ⟨plan8916,valid8916,t7_594choices,?_⟩
  exact check_of_frontier tree 0 t7_594root t7_594jobs t7_594frontier t7_594all
theorem t7_595choices : plan9058.choices=[8,5,5,7,7,7,7].map (options 7 7) := by rfl


theorem t7_595part0 : t7_595jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_595frontier : t7_595root.frontier 0=t7_595jobs := by rfl
theorem t7_595all : t7_595jobs.all (Job.check tree)=true := by
  simp only [t7_595jobs,List.all_append,List.all_nil,t7_595part0,Bool.and_self]
theorem t7_595checked : Checked tree [8,5,5,7,7,7,7] := by
  refine ⟨plan9058,valid9058,t7_595choices,?_⟩
  exact check_of_frontier tree 0 t7_595root t7_595jobs t7_595frontier t7_595all
theorem t7_596choices : plan9059.choices=[8,5,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_596part0 : t7_596jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_596frontier : t7_596root.frontier 0=t7_596jobs := by rfl
theorem t7_596all : t7_596jobs.all (Job.check tree)=true := by
  simp only [t7_596jobs,List.all_append,List.all_nil,t7_596part0,Bool.and_self]
theorem t7_596checked : Checked tree [8,5,6,6,7,7,7] := by
  refine ⟨plan9059,valid9059,t7_596choices,?_⟩
  exact check_of_frontier tree 0 t7_596root t7_596jobs t7_596frontier t7_596all
theorem t7_597choices : plan9060.choices=[8,5,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_597part0 : t7_597jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_597frontier : t7_597root.frontier 0=t7_597jobs := by rfl
theorem t7_597all : t7_597jobs.all (Job.check tree)=true := by
  simp only [t7_597jobs,List.all_append,List.all_nil,t7_597part0,Bool.and_self]
theorem t7_597checked : Checked tree [8,5,6,7,7,7,7] := by
  refine ⟨plan9060,valid9060,t7_597choices,?_⟩
  exact check_of_frontier tree 0 t7_597root t7_597jobs t7_597frontier t7_597all
theorem t7_598choices : plan9061.choices=[8,5,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_598part0 : t7_598jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_598frontier : t7_598root.frontier 0=t7_598jobs := by rfl
theorem t7_598all : t7_598jobs.all (Job.check tree)=true := by
  simp only [t7_598jobs,List.all_append,List.all_nil,t7_598part0,Bool.and_self]
theorem t7_598checked : Checked tree [8,5,6,10,7,7,7] := by
  refine ⟨plan9061,valid9061,t7_598choices,?_⟩
  exact check_of_frontier tree 0 t7_598root t7_598jobs t7_598frontier t7_598all
theorem t7_599choices : plan9062.choices=[8,5,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_599part0 : t7_599jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_599frontier : t7_599root.frontier 0=t7_599jobs := by rfl
theorem t7_599all : t7_599jobs.all (Job.check tree)=true := by
  simp only [t7_599jobs,List.all_append,List.all_nil,t7_599part0,Bool.and_self]
theorem t7_599checked : Checked tree [8,5,7,7,7,7,7] := by
  refine ⟨plan9062,valid9062,t7_599choices,?_⟩
  exact check_of_frontier tree 0 t7_599root t7_599jobs t7_599frontier t7_599all
theorem t7_600choices : plan9063.choices=[8,5,9,7,7,7,7].map (options 7 7) := by rfl


theorem t7_600part0 : t7_600jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_600frontier : t7_600root.frontier 0=t7_600jobs := by rfl
theorem t7_600all : t7_600jobs.all (Job.check tree)=true := by
  simp only [t7_600jobs,List.all_append,List.all_nil,t7_600part0,Bool.and_self]
theorem t7_600checked : Checked tree [8,5,9,7,7,7,7] := by
  refine ⟨plan9063,valid9063,t7_600choices,?_⟩
  exact check_of_frontier tree 0 t7_600root t7_600jobs t7_600frontier t7_600all
theorem t7_601choices : plan9064.choices=[8,5,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_601part0 : t7_601jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_601frontier : t7_601root.frontier 0=t7_601jobs := by rfl
theorem t7_601all : t7_601jobs.all (Job.check tree)=true := by
  simp only [t7_601jobs,List.all_append,List.all_nil,t7_601part0,Bool.and_self]
theorem t7_601checked : Checked tree [8,5,10,7,7,7,7] := by
  refine ⟨plan9064,valid9064,t7_601choices,?_⟩
  exact check_of_frontier tree 0 t7_601root t7_601jobs t7_601frontier t7_601all
theorem t7_602choices : plan9065.choices=[8,5,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_602part0 : t7_602jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_602frontier : t7_602root.frontier 0=t7_602jobs := by rfl
theorem t7_602all : t7_602jobs.all (Job.check tree)=true := by
  simp only [t7_602jobs,List.all_append,List.all_nil,t7_602part0,Bool.and_self]
theorem t7_602checked : Checked tree [8,5,10,10,7,7,7] := by
  refine ⟨plan9065,valid9065,t7_602choices,?_⟩
  exact check_of_frontier tree 0 t7_602root t7_602jobs t7_602frontier t7_602all
theorem t7_603choices : plan9066.choices=[8,6,6,6,6,7,7].map (options 7 7) := by rfl


theorem t7_603part0 : t7_603jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_603frontier : t7_603root.frontier 0=t7_603jobs := by rfl
theorem t7_603all : t7_603jobs.all (Job.check tree)=true := by
  simp only [t7_603jobs,List.all_append,List.all_nil,t7_603part0,Bool.and_self]
theorem t7_603checked : Checked tree [8,6,6,6,6,7,7] := by
  refine ⟨plan9066,valid9066,t7_603choices,?_⟩
  exact check_of_frontier tree 0 t7_603root t7_603jobs t7_603frontier t7_603all
theorem t7_604choices : plan9067.choices=[8,6,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_604part0 : t7_604jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_604frontier : t7_604root.frontier 0=t7_604jobs := by rfl
theorem t7_604all : t7_604jobs.all (Job.check tree)=true := by
  simp only [t7_604jobs,List.all_append,List.all_nil,t7_604part0,Bool.and_self]
theorem t7_604checked : Checked tree [8,6,6,6,7,7,7] := by
  refine ⟨plan9067,valid9067,t7_604choices,?_⟩
  exact check_of_frontier tree 0 t7_604root t7_604jobs t7_604frontier t7_604all
theorem t7_605choices : plan9068.choices=[8,6,6,6,10,7,7].map (options 7 7) := by rfl


theorem t7_605part0 : t7_605jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_605frontier : t7_605root.frontier 0=t7_605jobs := by rfl
theorem t7_605all : t7_605jobs.all (Job.check tree)=true := by
  simp only [t7_605jobs,List.all_append,List.all_nil,t7_605part0,Bool.and_self]
theorem t7_605checked : Checked tree [8,6,6,6,10,7,7] := by
  refine ⟨plan9068,valid9068,t7_605choices,?_⟩
  exact check_of_frontier tree 0 t7_605root t7_605jobs t7_605frontier t7_605all
theorem t7_606choices : plan9069.choices=[8,6,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_606part0 : t7_606jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_606frontier : t7_606root.frontier 0=t7_606jobs := by rfl
theorem t7_606all : t7_606jobs.all (Job.check tree)=true := by
  simp only [t7_606jobs,List.all_append,List.all_nil,t7_606part0,Bool.and_self]
theorem t7_606checked : Checked tree [8,6,6,7,7,7,7] := by
  refine ⟨plan9069,valid9069,t7_606choices,?_⟩
  exact check_of_frontier tree 0 t7_606root t7_606jobs t7_606frontier t7_606all
theorem t7_607choices : plan9070.choices=[8,6,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_607part0 : t7_607jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_607frontier : t7_607root.frontier 0=t7_607jobs := by rfl
theorem t7_607all : t7_607jobs.all (Job.check tree)=true := by
  simp only [t7_607jobs,List.all_append,List.all_nil,t7_607part0,Bool.and_self]
theorem t7_607checked : Checked tree [8,6,6,10,7,7,7] := by
  refine ⟨plan9070,valid9070,t7_607choices,?_⟩
  exact check_of_frontier tree 0 t7_607root t7_607jobs t7_607frontier t7_607all
theorem t7_608choices : plan9071.choices=[8,6,6,10,10,7,7].map (options 7 7) := by rfl


theorem t7_608part0 : t7_608jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_608frontier : t7_608root.frontier 0=t7_608jobs := by rfl
theorem t7_608all : t7_608jobs.all (Job.check tree)=true := by
  simp only [t7_608jobs,List.all_append,List.all_nil,t7_608part0,Bool.and_self]
theorem t7_608checked : Checked tree [8,6,6,10,10,7,7] := by
  refine ⟨plan9071,valid9071,t7_608choices,?_⟩
  exact check_of_frontier tree 0 t7_608root t7_608jobs t7_608frontier t7_608all
theorem t7_609choices : plan9072.choices=[8,6,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_609part0 : t7_609jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_609frontier : t7_609root.frontier 0=t7_609jobs := by rfl
theorem t7_609all : t7_609jobs.all (Job.check tree)=true := by
  simp only [t7_609jobs,List.all_append,List.all_nil,t7_609part0,Bool.and_self]
theorem t7_609checked : Checked tree [8,6,7,7,7,7,7] := by
  refine ⟨plan9072,valid9072,t7_609choices,?_⟩
  exact check_of_frontier tree 0 t7_609root t7_609jobs t7_609frontier t7_609all
theorem t7_610choices : plan9073.choices=[8,6,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_610part0 : t7_610jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_610frontier : t7_610root.frontier 0=t7_610jobs := by rfl
theorem t7_610all : t7_610jobs.all (Job.check tree)=true := by
  simp only [t7_610jobs,List.all_append,List.all_nil,t7_610part0,Bool.and_self]
theorem t7_610checked : Checked tree [8,6,10,7,7,7,7] := by
  refine ⟨plan9073,valid9073,t7_610choices,?_⟩
  exact check_of_frontier tree 0 t7_610root t7_610jobs t7_610frontier t7_610all
theorem t7_611choices : plan9074.choices=[8,6,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_611part0 : t7_611jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_611frontier : t7_611root.frontier 0=t7_611jobs := by rfl
theorem t7_611all : t7_611jobs.all (Job.check tree)=true := by
  simp only [t7_611jobs,List.all_append,List.all_nil,t7_611part0,Bool.and_self]
theorem t7_611checked : Checked tree [8,6,10,10,7,7,7] := by
  refine ⟨plan9074,valid9074,t7_611choices,?_⟩
  exact check_of_frontier tree 0 t7_611root t7_611jobs t7_611frontier t7_611all
theorem t7_612choices : plan9075.choices=[8,6,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_612part0 : t7_612jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_612frontier : t7_612root.frontier 0=t7_612jobs := by rfl
theorem t7_612all : t7_612jobs.all (Job.check tree)=true := by
  simp only [t7_612jobs,List.all_append,List.all_nil,t7_612part0,Bool.and_self]
theorem t7_612checked : Checked tree [8,6,10,10,10,7,7] := by
  refine ⟨plan9075,valid9075,t7_612choices,?_⟩
  exact check_of_frontier tree 0 t7_612root t7_612jobs t7_612frontier t7_612all
theorem t7_613choices : plan9076.choices=[8,7,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_613part0 : t7_613jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_613frontier : t7_613root.frontier 0=t7_613jobs := by rfl
theorem t7_613all : t7_613jobs.all (Job.check tree)=true := by
  simp only [t7_613jobs,List.all_append,List.all_nil,t7_613part0,Bool.and_self]
theorem t7_613checked : Checked tree [8,7,7,7,7,7,7] := by
  refine ⟨plan9076,valid9076,t7_613choices,?_⟩
  exact check_of_frontier tree 0 t7_613root t7_613jobs t7_613frontier t7_613all
theorem t7_614choices : plan8917.choices=[8,8,3,7,7,7,7].map (options 7 6) := by rfl


theorem t7_614part0 : t7_614jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_614frontier : t7_614root.frontier 0=t7_614jobs := by rfl
theorem t7_614all : t7_614jobs.all (Job.check tree)=true := by
  simp only [t7_614jobs,List.all_append,List.all_nil,t7_614part0,Bool.and_self]
theorem t7_614checked : Checked tree [8,8,3,7,7,7,7] := by
  refine ⟨plan8917,valid8917,t7_614choices,?_⟩
  exact check_of_frontier tree 0 t7_614root t7_614jobs t7_614frontier t7_614all
theorem t7_615choices : plan9077.choices=[8,8,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_615part0 : t7_615jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_615frontier : t7_615root.frontier 0=t7_615jobs := by rfl
theorem t7_615all : t7_615jobs.all (Job.check tree)=true := by
  simp only [t7_615jobs,List.all_append,List.all_nil,t7_615part0,Bool.and_self]
theorem t7_615checked : Checked tree [8,8,6,7,7,7,7] := by
  refine ⟨plan9077,valid9077,t7_615choices,?_⟩
  exact check_of_frontier tree 0 t7_615root t7_615jobs t7_615frontier t7_615all
theorem t7_616choices : plan9078.choices=[8,8,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_616part0 : t7_616jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_616frontier : t7_616root.frontier 0=t7_616jobs := by rfl
theorem t7_616all : t7_616jobs.all (Job.check tree)=true := by
  simp only [t7_616jobs,List.all_append,List.all_nil,t7_616part0,Bool.and_self]
theorem t7_616checked : Checked tree [8,8,7,7,7,7,7] := by
  refine ⟨plan9078,valid9078,t7_616choices,?_⟩
  exact check_of_frontier tree 0 t7_616root t7_616jobs t7_616frontier t7_616all
theorem t7_617choices : plan9079.choices=[8,8,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_617part0 : t7_617jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_617frontier : t7_617root.frontier 0=t7_617jobs := by rfl
theorem t7_617all : t7_617jobs.all (Job.check tree)=true := by
  simp only [t7_617jobs,List.all_append,List.all_nil,t7_617part0,Bool.and_self]
theorem t7_617checked : Checked tree [8,8,10,7,7,7,7] := by
  refine ⟨plan9079,valid9079,t7_617choices,?_⟩
  exact check_of_frontier tree 0 t7_617root t7_617jobs t7_617frontier t7_617all
theorem t7_618choices : plan8694.choices=[8,9,3,3,7,7,7].map (options 7 5) := by rfl


theorem t7_618part0 : t7_618jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_618frontier : t7_618root.frontier 0=t7_618jobs := by rfl
theorem t7_618all : t7_618jobs.all (Job.check tree)=true := by
  simp only [t7_618jobs,List.all_append,List.all_nil,t7_618part0,Bool.and_self]
theorem t7_618checked : Checked tree [8,9,3,3,7,7,7] := by
  refine ⟨plan8694,valid8694,t7_618choices,?_⟩
  exact check_of_frontier tree 0 t7_618root t7_618jobs t7_618frontier t7_618all
theorem t7_619choices : plan8918.choices=[8,9,3,6,7,7,7].map (options 7 6) := by rfl


theorem t7_619part0 : t7_619jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_619frontier : t7_619root.frontier 0=t7_619jobs := by rfl
theorem t7_619all : t7_619jobs.all (Job.check tree)=true := by
  simp only [t7_619jobs,List.all_append,List.all_nil,t7_619part0,Bool.and_self]
theorem t7_619checked : Checked tree [8,9,3,6,7,7,7] := by
  refine ⟨plan8918,valid8918,t7_619choices,?_⟩
  exact check_of_frontier tree 0 t7_619root t7_619jobs t7_619frontier t7_619all
theorem t7_620choices : plan8919.choices=[8,9,3,7,7,7,7].map (options 7 6) := by rfl


theorem t7_620part0 : t7_620jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_620frontier : t7_620root.frontier 0=t7_620jobs := by rfl
theorem t7_620all : t7_620jobs.all (Job.check tree)=true := by
  simp only [t7_620jobs,List.all_append,List.all_nil,t7_620part0,Bool.and_self]
theorem t7_620checked : Checked tree [8,9,3,7,7,7,7] := by
  refine ⟨plan8919,valid8919,t7_620choices,?_⟩
  exact check_of_frontier tree 0 t7_620root t7_620jobs t7_620frontier t7_620all
theorem t7_621choices : plan8920.choices=[8,9,3,10,7,7,7].map (options 7 6) := by rfl


theorem t7_621part0 : t7_621jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_621frontier : t7_621root.frontier 0=t7_621jobs := by rfl
theorem t7_621all : t7_621jobs.all (Job.check tree)=true := by
  simp only [t7_621jobs,List.all_append,List.all_nil,t7_621part0,Bool.and_self]
theorem t7_621checked : Checked tree [8,9,3,10,7,7,7] := by
  refine ⟨plan8920,valid8920,t7_621choices,?_⟩
  exact check_of_frontier tree 0 t7_621root t7_621jobs t7_621frontier t7_621all
theorem t7_622choices : plan9080.choices=[8,9,6,6,7,7,7].map (options 7 7) := by rfl


theorem t7_622part0 : t7_622jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_622frontier : t7_622root.frontier 0=t7_622jobs := by rfl
theorem t7_622all : t7_622jobs.all (Job.check tree)=true := by
  simp only [t7_622jobs,List.all_append,List.all_nil,t7_622part0,Bool.and_self]
theorem t7_622checked : Checked tree [8,9,6,6,7,7,7] := by
  refine ⟨plan9080,valid9080,t7_622choices,?_⟩
  exact check_of_frontier tree 0 t7_622root t7_622jobs t7_622frontier t7_622all
theorem t7_623choices : plan9081.choices=[8,9,6,7,7,7,7].map (options 7 7) := by rfl


theorem t7_623part0 : t7_623jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_623frontier : t7_623root.frontier 0=t7_623jobs := by rfl
theorem t7_623all : t7_623jobs.all (Job.check tree)=true := by
  simp only [t7_623jobs,List.all_append,List.all_nil,t7_623part0,Bool.and_self]
theorem t7_623checked : Checked tree [8,9,6,7,7,7,7] := by
  refine ⟨plan9081,valid9081,t7_623choices,?_⟩
  exact check_of_frontier tree 0 t7_623root t7_623jobs t7_623frontier t7_623all
theorem t7_624choices : plan9082.choices=[8,9,6,10,7,7,7].map (options 7 7) := by rfl


theorem t7_624part0 : t7_624jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_624frontier : t7_624root.frontier 0=t7_624jobs := by rfl
theorem t7_624all : t7_624jobs.all (Job.check tree)=true := by
  simp only [t7_624jobs,List.all_append,List.all_nil,t7_624part0,Bool.and_self]
theorem t7_624checked : Checked tree [8,9,6,10,7,7,7] := by
  refine ⟨plan9082,valid9082,t7_624choices,?_⟩
  exact check_of_frontier tree 0 t7_624root t7_624jobs t7_624frontier t7_624all
theorem t7_625choices : plan9083.choices=[8,9,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_625part0 : t7_625jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_625frontier : t7_625root.frontier 0=t7_625jobs := by rfl
theorem t7_625all : t7_625jobs.all (Job.check tree)=true := by
  simp only [t7_625jobs,List.all_append,List.all_nil,t7_625part0,Bool.and_self]
theorem t7_625checked : Checked tree [8,9,7,7,7,7,7] := by
  refine ⟨plan9083,valid9083,t7_625choices,?_⟩
  exact check_of_frontier tree 0 t7_625root t7_625jobs t7_625frontier t7_625all
theorem t7_626choices : plan9084.choices=[8,9,9,7,7,7,7].map (options 7 7) := by rfl


theorem t7_626part0 : t7_626jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_626frontier : t7_626root.frontier 0=t7_626jobs := by rfl
theorem t7_626all : t7_626jobs.all (Job.check tree)=true := by
  simp only [t7_626jobs,List.all_append,List.all_nil,t7_626part0,Bool.and_self]
theorem t7_626checked : Checked tree [8,9,9,7,7,7,7] := by
  refine ⟨plan9084,valid9084,t7_626choices,?_⟩
  exact check_of_frontier tree 0 t7_626root t7_626jobs t7_626frontier t7_626all
theorem t7_627choices : plan9085.choices=[8,9,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_627part0 : t7_627jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_627frontier : t7_627root.frontier 0=t7_627jobs := by rfl
theorem t7_627all : t7_627jobs.all (Job.check tree)=true := by
  simp only [t7_627jobs,List.all_append,List.all_nil,t7_627part0,Bool.and_self]
theorem t7_627checked : Checked tree [8,9,10,7,7,7,7] := by
  refine ⟨plan9085,valid9085,t7_627choices,?_⟩
  exact check_of_frontier tree 0 t7_627root t7_627jobs t7_627frontier t7_627all
theorem t7_628choices : plan9086.choices=[8,9,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_628part0 : t7_628jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_628frontier : t7_628root.frontier 0=t7_628jobs := by rfl
theorem t7_628all : t7_628jobs.all (Job.check tree)=true := by
  simp only [t7_628jobs,List.all_append,List.all_nil,t7_628part0,Bool.and_self]
theorem t7_628checked : Checked tree [8,9,10,10,7,7,7] := by
  refine ⟨plan9086,valid9086,t7_628choices,?_⟩
  exact check_of_frontier tree 0 t7_628root t7_628jobs t7_628frontier t7_628all
theorem t7_629choices : plan9087.choices=[8,10,7,7,7,7,7].map (options 7 7) := by rfl


theorem t7_629part0 : t7_629jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_629frontier : t7_629root.frontier 0=t7_629jobs := by rfl
theorem t7_629all : t7_629jobs.all (Job.check tree)=true := by
  simp only [t7_629jobs,List.all_append,List.all_nil,t7_629part0,Bool.and_self]
theorem t7_629checked : Checked tree [8,10,7,7,7,7,7] := by
  refine ⟨plan9087,valid9087,t7_629choices,?_⟩
  exact check_of_frontier tree 0 t7_629root t7_629jobs t7_629frontier t7_629all
theorem t7_630choices : plan9088.choices=[8,10,10,7,7,7,7].map (options 7 7) := by rfl


theorem t7_630part0 : t7_630jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_630frontier : t7_630root.frontier 0=t7_630jobs := by rfl
theorem t7_630all : t7_630jobs.all (Job.check tree)=true := by
  simp only [t7_630jobs,List.all_append,List.all_nil,t7_630part0,Bool.and_self]
theorem t7_630checked : Checked tree [8,10,10,7,7,7,7] := by
  refine ⟨plan9088,valid9088,t7_630choices,?_⟩
  exact check_of_frontier tree 0 t7_630root t7_630jobs t7_630frontier t7_630all
theorem t7_631choices : plan9089.choices=[8,10,10,10,7,7,7].map (options 7 7) := by rfl


theorem t7_631part0 : t7_631jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_631frontier : t7_631root.frontier 0=t7_631jobs := by rfl
theorem t7_631all : t7_631jobs.all (Job.check tree)=true := by
  simp only [t7_631jobs,List.all_append,List.all_nil,t7_631part0,Bool.and_self]
theorem t7_631checked : Checked tree [8,10,10,10,7,7,7] := by
  refine ⟨plan9089,valid9089,t7_631choices,?_⟩
  exact check_of_frontier tree 0 t7_631root t7_631jobs t7_631frontier t7_631all
theorem t7_632choices : plan9090.choices=[8,10,10,10,10,7,7].map (options 7 7) := by rfl


theorem t7_632part0 : t7_632jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_632frontier : t7_632root.frontier 0=t7_632jobs := by rfl
theorem t7_632all : t7_632jobs.all (Job.check tree)=true := by
  simp only [t7_632jobs,List.all_append,List.all_nil,t7_632part0,Bool.and_self]
theorem t7_632checked : Checked tree [8,10,10,10,10,7,7] := by
  refine ⟨plan9090,valid9090,t7_632choices,?_⟩
  exact check_of_frontier tree 0 t7_632root t7_632jobs t7_632frontier t7_632all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks189 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_573checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_574checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_575checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_576checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_577checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_578checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_579checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_580checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_581checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_582checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_561checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_583checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_584checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_585checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_586checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_587checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_588checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_589checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_590checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_591checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_592checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_562checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_593checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_594checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_595checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_596checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_597checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_598checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_599checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_600checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_601checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_602checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_563checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_603checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_604checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_605checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_606checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_607checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_608checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_609checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_610checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_611checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_612checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_564checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_613checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_614checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_615checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_616checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_617checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_618checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_619checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_620checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_621checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_565checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_622checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_623checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_624checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_625checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_626checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_627checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_628checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_629checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_630checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_631checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_566checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_632checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_567checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_568checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_569checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_570checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_571checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_572checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_560checked⟩
