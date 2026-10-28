-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks039
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:01:08.553042+00:00
-- url     : https://prove2.me/submissions/3a4b8867-c2b9-4994-a84a-5e05c0eed47c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans053
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans054
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

theorem valid100 : plan100.Valid := valid_step _ _ _ valid0 (by decide +kernel)











theorem valid106 : plan106.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid108 : plan108.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid109 : plan109.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid111 : plan111.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid113 : plan113.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid114 : plan114.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid115 : plan115.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid116 : plan116.Valid := valid_step _ _ _ valid0 (by decide +kernel)
























































































































































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





























































































































theorem valid447 : plan447.Valid := valid_step _ _ _ valid88 (by decide +kernel)











theorem valid453 : plan453.Valid := valid_step _ _ _ valid88 (by decide +kernel)











theorem valid459 : plan459.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid460 : plan460.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid461 : plan461.Valid := valid_step _ _ _ valid99 (by decide +kernel)



theorem valid463 : plan463.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid464 : plan464.Valid := valid_step _ _ _ valid97 (by decide +kernel)
































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







theorem valid484 : plan484.Valid := valid_step _ _ _ valid100 (by decide +kernel)









































theorem valid505 : plan505.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid506 : plan506.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid507 : plan507.Valid := valid_step _ _ _ valid111 (by decide +kernel)





















theorem valid518 : plan518.Valid := valid_step _ _ _ valid106 (by decide +kernel)









theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid524 : plan524.Valid := valid_step _ _ _ valid111 (by decide +kernel)











theorem valid530 : plan530.Valid := valid_step _ _ _ valid113 (by decide +kernel)

theorem valid531 : plan531.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid532 : plan532.Valid := valid_step _ _ _ valid116 (by decide +kernel)

theorem valid533 : plan533.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid534 : plan534.Valid := valid_step _ _ _ valid113 (by decide +kernel)

theorem valid535 : plan535.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid536 : plan536.Valid := valid_step _ _ _ valid115 (by decide +kernel)

theorem valid537 : plan537.Valid := valid_step _ _ _ valid116 (by decide +kernel)

theorem valid538 : plan538.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid539 : plan539.Valid := valid_step _ _ _ valid116 (by decide +kernel)










































































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







theorem valid1252 : plan1252.Valid := valid_step _ _ _ valid447 (by decide +kernel)











theorem valid1258 : plan1258.Valid := valid_step _ _ _ valid453 (by decide +kernel)





























theorem valid1273 : plan1273.Valid := valid_step _ _ _ valid459 (by decide +kernel)

theorem valid1274 : plan1274.Valid := valid_step _ _ _ valid460 (by decide +kernel)

theorem valid1275 : plan1275.Valid := valid_step _ _ _ valid461 (by decide +kernel)



theorem valid1277 : plan1277.Valid := valid_step _ _ _ valid463 (by decide +kernel)

theorem valid1278 : plan1278.Valid := valid_step _ _ _ valid464 (by decide +kernel)




































































































































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





































































theorem valid2531 : plan2531.Valid := valid_step _ _ _ valid1252 (by decide +kernel)











theorem valid2537 : plan2537.Valid := valid_step _ _ _ valid1258 (by decide +kernel)





























































































theorem valid2584 : plan2584.Valid := valid_step _ _ _ valid1273 (by decide +kernel)

theorem valid2585 : plan2585.Valid := valid_step _ _ _ valid1274 (by decide +kernel)

theorem valid2586 : plan2586.Valid := valid_step _ _ _ valid1275 (by decide +kernel)

theorem valid2587 : plan2587.Valid := valid_step _ _ _ valid1277 (by decide +kernel)

theorem valid2588 : plan2588.Valid := valid_step _ _ _ valid1278 (by decide +kernel)








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









































































theorem valid1381 : plan1381.Valid := valid_step _ _ _ valid484 (by decide +kernel)



























































theorem valid1411 : plan1411.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1412 : plan1412.Valid := valid_step _ _ _ valid524 (by decide +kernel)
























































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



















theorem valid3754 : plan3754.Valid := valid_step _ _ _ valid2531 (by decide +kernel)

theorem valid3755 : plan3755.Valid := valid_step _ _ _ valid2537 (by decide +kernel)










































































































































































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















































































theorem valid3976 : plan3976.Valid := valid_step _ _ _ valid2584 (by decide +kernel)

theorem valid3977 : plan3977.Valid := valid_step _ _ _ valid2585 (by decide +kernel)

theorem valid3978 : plan3978.Valid := valid_step _ _ _ valid2586 (by decide +kernel)

theorem valid3979 : plan3979.Valid := valid_step _ _ _ valid2587 (by decide +kernel)

theorem valid3980 : plan3980.Valid := valid_step _ _ _ valid2588 (by decide +kernel)








































































































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







































































































































































theorem valid2868 : plan2868.Valid := valid_step _ _ _ valid1381 (by decide +kernel)
























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















theorem valid1448 : plan1448.Valid := valid_step _ _ _ valid505 (by decide +kernel)

theorem valid1449 : plan1449.Valid := valid_step _ _ _ valid506 (by decide +kernel)

theorem valid1450 : plan1450.Valid := valid_step _ _ _ valid507 (by decide +kernel)









theorem valid1455 : plan1455.Valid := valid_step _ _ _ valid518 (by decide +kernel)























































theorem valid1483 : plan1483.Valid := valid_step _ _ _ valid530 (by decide +kernel)

theorem valid1484 : plan1484.Valid := valid_step _ _ _ valid531 (by decide +kernel)

theorem valid1485 : plan1485.Valid := valid_step _ _ _ valid532 (by decide +kernel)

theorem valid1486 : plan1486.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1487 : plan1487.Valid := valid_step _ _ _ valid538 (by decide +kernel)

theorem valid1488 : plan1488.Valid := valid_step _ _ _ valid539 (by decide +kernel)

theorem valid1489 : plan1489.Valid := valid_step _ _ _ valid533 (by decide +kernel)







theorem valid1493 : plan1493.Valid := valid_step _ _ _ valid530 (by decide +kernel)

theorem valid1494 : plan1494.Valid := valid_step _ _ _ valid531 (by decide +kernel)

theorem valid1495 : plan1495.Valid := valid_step _ _ _ valid532 (by decide +kernel)

theorem valid1496 : plan1496.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1497 : plan1497.Valid := valid_step _ _ _ valid534 (by decide +kernel)

theorem valid1498 : plan1498.Valid := valid_step _ _ _ valid535 (by decide +kernel)

theorem valid1499 : plan1499.Valid := valid_step _ _ _ valid536 (by decide +kernel)

theorem valid1500 : plan1500.Valid := valid_step _ _ _ valid537 (by decide +kernel)

theorem valid1501 : plan1501.Valid := valid_step _ _ _ valid538 (by decide +kernel)

theorem valid1502 : plan1502.Valid := valid_step _ _ _ valid539 (by decide +kernel)

theorem valid1503 : plan1503.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1504 : plan1504.Valid := valid_step _ _ _ valid538 (by decide +kernel)

theorem valid1505 : plan1505.Valid := valid_step _ _ _ valid539 (by decide +kernel)






























































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

















theorem valid3081 : plan3081.Valid := valid_step _ _ _ valid1411 (by decide +kernel)

theorem valid3082 : plan3082.Valid := valid_step _ _ _ valid1412 (by decide +kernel)















theorem valid3090 : plan3090.Valid := valid_step _ _ _ valid1448 (by decide +kernel)

theorem valid3091 : plan3091.Valid := valid_step _ _ _ valid1449 (by decide +kernel)

theorem valid3092 : plan3092.Valid := valid_step _ _ _ valid1450 (by decide +kernel)









theorem valid3097 : plan3097.Valid := valid_step _ _ _ valid1455 (by decide +kernel)














































































































































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







































































































































theorem valid4388 : plan4388.Valid := valid_step _ _ _ valid2868 (by decide +kernel)
























































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











































































































































































theorem valid4886 : plan4886.Valid := valid_step _ _ _ valid3081 (by decide +kernel)

theorem valid4887 : plan4887.Valid := valid_step _ _ _ valid3082 (by decide +kernel)

theorem valid4888 : plan4888.Valid := valid_step _ _ _ valid3090 (by decide +kernel)

theorem valid4889 : plan4889.Valid := valid_step _ _ _ valid3091 (by decide +kernel)

theorem valid4890 : plan4890.Valid := valid_step _ _ _ valid3092 (by decide +kernel)

theorem valid4891 : plan4891.Valid := valid_step _ _ _ valid3097 (by decide +kernel)










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

















theorem valid3177 : plan3177.Valid := valid_step _ _ _ valid1483 (by decide +kernel)

theorem valid3178 : plan3178.Valid := valid_step _ _ _ valid1484 (by decide +kernel)

theorem valid3179 : plan3179.Valid := valid_step _ _ _ valid1485 (by decide +kernel)

theorem valid3180 : plan3180.Valid := valid_step _ _ _ valid1486 (by decide +kernel)

theorem valid3181 : plan3181.Valid := valid_step _ _ _ valid1487 (by decide +kernel)

theorem valid3182 : plan3182.Valid := valid_step _ _ _ valid1488 (by decide +kernel)

theorem valid3183 : plan3183.Valid := valid_step _ _ _ valid1489 (by decide +kernel)

theorem valid3184 : plan3184.Valid := valid_step _ _ _ valid1503 (by decide +kernel)

theorem valid3185 : plan3185.Valid := valid_step _ _ _ valid1504 (by decide +kernel)

theorem valid3186 : plan3186.Valid := valid_step _ _ _ valid1505 (by decide +kernel)

theorem valid3187 : plan3187.Valid := valid_step _ _ _ valid1489 (by decide +kernel)

























































theorem valid3216 : plan3216.Valid := valid_step _ _ _ valid1483 (by decide +kernel)

theorem valid3217 : plan3217.Valid := valid_step _ _ _ valid1484 (by decide +kernel)

theorem valid3218 : plan3218.Valid := valid_step _ _ _ valid1485 (by decide +kernel)

theorem valid3219 : plan3219.Valid := valid_step _ _ _ valid1486 (by decide +kernel)

theorem valid3220 : plan3220.Valid := valid_step _ _ _ valid1487 (by decide +kernel)

theorem valid3221 : plan3221.Valid := valid_step _ _ _ valid1488 (by decide +kernel)

theorem valid3222 : plan3222.Valid := valid_step _ _ _ valid1489 (by decide +kernel)

theorem valid3223 : plan3223.Valid := valid_step _ _ _ valid1493 (by decide +kernel)

theorem valid3224 : plan3224.Valid := valid_step _ _ _ valid1494 (by decide +kernel)

theorem valid3225 : plan3225.Valid := valid_step _ _ _ valid1495 (by decide +kernel)

theorem valid3226 : plan3226.Valid := valid_step _ _ _ valid1496 (by decide +kernel)

theorem valid3227 : plan3227.Valid := valid_step _ _ _ valid1497 (by decide +kernel)

theorem valid3228 : plan3228.Valid := valid_step _ _ _ valid1498 (by decide +kernel)

theorem valid3229 : plan3229.Valid := valid_step _ _ _ valid1499 (by decide +kernel)

theorem valid3230 : plan3230.Valid := valid_step _ _ _ valid1500 (by decide +kernel)

theorem valid3231 : plan3231.Valid := valid_step _ _ _ valid1501 (by decide +kernel)

theorem valid3232 : plan3232.Valid := valid_step _ _ _ valid1502 (by decide +kernel)

theorem valid3233 : plan3233.Valid := valid_step _ _ _ valid1503 (by decide +kernel)

theorem valid3234 : plan3234.Valid := valid_step _ _ _ valid1504 (by decide +kernel)

theorem valid3235 : plan3235.Valid := valid_step _ _ _ valid1505 (by decide +kernel)

theorem valid3236 : plan3236.Valid := valid_step _ _ _ valid1489 (by decide +kernel)

theorem valid3237 : plan3237.Valid := valid_step _ _ _ valid1503 (by decide +kernel)

theorem valid3238 : plan3238.Valid := valid_step _ _ _ valid1504 (by decide +kernel)

theorem valid3239 : plan3239.Valid := valid_step _ _ _ valid1505 (by decide +kernel)


















































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

































































































































































theorem valid5169 : plan5169.Valid := valid_step _ _ _ valid3216 (by decide +kernel)

theorem valid5170 : plan5170.Valid := valid_step _ _ _ valid3217 (by decide +kernel)

theorem valid5171 : plan5171.Valid := valid_step _ _ _ valid3218 (by decide +kernel)

theorem valid5172 : plan5172.Valid := valid_step _ _ _ valid3219 (by decide +kernel)

theorem valid5173 : plan5173.Valid := valid_step _ _ _ valid3220 (by decide +kernel)

theorem valid5174 : plan5174.Valid := valid_step _ _ _ valid3221 (by decide +kernel)

theorem valid5175 : plan5175.Valid := valid_step _ _ _ valid3222 (by decide +kernel)

theorem valid5176 : plan5176.Valid := valid_step _ _ _ valid3223 (by decide +kernel)

theorem valid5177 : plan5177.Valid := valid_step _ _ _ valid3224 (by decide +kernel)

theorem valid5178 : plan5178.Valid := valid_step _ _ _ valid3225 (by decide +kernel)

theorem valid5179 : plan5179.Valid := valid_step _ _ _ valid3226 (by decide +kernel)

theorem valid5180 : plan5180.Valid := valid_step _ _ _ valid3227 (by decide +kernel)

theorem valid5181 : plan5181.Valid := valid_step _ _ _ valid3228 (by decide +kernel)

theorem valid5182 : plan5182.Valid := valid_step _ _ _ valid3229 (by decide +kernel)

theorem valid5183 : plan5183.Valid := valid_step _ _ _ valid3230 (by decide +kernel)

theorem valid5184 : plan5184.Valid := valid_step _ _ _ valid3231 (by decide +kernel)
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

theorem valid5185 : plan5185.Valid := valid_step _ _ _ valid3232 (by decide +kernel)

theorem valid5186 : plan5186.Valid := valid_step _ _ _ valid3233 (by decide +kernel)

theorem valid5187 : plan5187.Valid := valid_step _ _ _ valid3234 (by decide +kernel)

theorem valid5188 : plan5188.Valid := valid_step _ _ _ valid3235 (by decide +kernel)

theorem valid5189 : plan5189.Valid := valid_step _ _ _ valid3236 (by decide +kernel)

theorem valid5190 : plan5190.Valid := valid_step _ _ _ valid3237 (by decide +kernel)

theorem valid5191 : plan5191.Valid := valid_step _ _ _ valid3238 (by decide +kernel)

theorem valid5192 : plan5192.Valid := valid_step _ _ _ valid3239 (by decide +kernel)

theorem valid5193 : plan5193.Valid := valid_step _ _ _ valid3177 (by decide +kernel)

theorem valid5194 : plan5194.Valid := valid_step _ _ _ valid3178 (by decide +kernel)

theorem valid5195 : plan5195.Valid := valid_step _ _ _ valid3179 (by decide +kernel)

theorem valid5196 : plan5196.Valid := valid_step _ _ _ valid3180 (by decide +kernel)

theorem valid5197 : plan5197.Valid := valid_step _ _ _ valid3181 (by decide +kernel)

theorem valid5198 : plan5198.Valid := valid_step _ _ _ valid3182 (by decide +kernel)

theorem valid5199 : plan5199.Valid := valid_step _ _ _ valid3183 (by decide +kernel)

theorem valid5200 : plan5200.Valid := valid_step _ _ _ valid3184 (by decide +kernel)

theorem valid5201 : plan5201.Valid := valid_step _ _ _ valid3185 (by decide +kernel)

theorem valid5202 : plan5202.Valid := valid_step _ _ _ valid3186 (by decide +kernel)

theorem valid5203 : plan5203.Valid := valid_step _ _ _ valid3187 (by decide +kernel)

theorem valid5204 : plan5204.Valid := valid_step _ _ _ valid3236 (by decide +kernel)

theorem valid5205 : plan5205.Valid := valid_step _ _ _ valid3237 (by decide +kernel)

theorem valid5206 : plan5206.Valid := valid_step _ _ _ valid3238 (by decide +kernel)

theorem valid5207 : plan5207.Valid := valid_step _ _ _ valid3239 (by decide +kernel)

theorem valid5208 : plan5208.Valid := valid_step _ _ _ valid3187 (by decide +kernel)
















































































































































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
theorem t5_1307choices : plan4886.choices=[5,9,3,10,7].map (options 5 4) := by rfl


theorem t5_1307part0 : t5_1307jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1307part1 : t5_1307jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1307part2 : t5_1307jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1307frontier : t5_1307root.frontier 1=t5_1307jobs := by rfl
theorem t5_1307all : t5_1307jobs.all (Job.check tree)=true := by
  simp only [t5_1307jobs,List.all_append,List.all_nil,t5_1307part0,t5_1307part1,t5_1307part2,Bool.and_self]
theorem t5_1307checked : Checked tree [5,9,3,10,7] := by
  refine ⟨plan4886,valid4886,t5_1307choices,?_⟩
  exact check_of_frontier tree 1 t5_1307root t5_1307jobs t5_1307frontier t5_1307all
theorem t5_1308choices : plan4887.choices=[5,9,3,10,10].map (options 5 4) := by rfl


theorem t5_1308part0 : t5_1308jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1308frontier : t5_1308root.frontier 0=t5_1308jobs := by rfl
theorem t5_1308all : t5_1308jobs.all (Job.check tree)=true := by
  simp only [t5_1308jobs,List.all_append,List.all_nil,t5_1308part0,Bool.and_self]
theorem t5_1308checked : Checked tree [5,9,3,10,10] := by
  refine ⟨plan4887,valid4887,t5_1308choices,?_⟩
  exact check_of_frontier tree 0 t5_1308root t5_1308jobs t5_1308frontier t5_1308all
theorem t5_1309choices : plan5169.choices=[5,9,6,6,6].map (options 5 5) := by rfl


theorem t5_1309part0 : t5_1309jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1309frontier : t5_1309root.frontier 0=t5_1309jobs := by rfl
theorem t5_1309all : t5_1309jobs.all (Job.check tree)=true := by
  simp only [t5_1309jobs,List.all_append,List.all_nil,t5_1309part0,Bool.and_self]
theorem t5_1309checked : Checked tree [5,9,6,6,6] := by
  refine ⟨plan5169,valid5169,t5_1309choices,?_⟩
  exact check_of_frontier tree 0 t5_1309root t5_1309jobs t5_1309frontier t5_1309all
theorem t5_1310choices : plan5170.choices=[5,9,6,6,7].map (options 5 5) := by rfl


theorem t5_1310part0 : t5_1310jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1310frontier : t5_1310root.frontier 0=t5_1310jobs := by rfl
theorem t5_1310all : t5_1310jobs.all (Job.check tree)=true := by
  simp only [t5_1310jobs,List.all_append,List.all_nil,t5_1310part0,Bool.and_self]
theorem t5_1310checked : Checked tree [5,9,6,6,7] := by
  refine ⟨plan5170,valid5170,t5_1310choices,?_⟩
  exact check_of_frontier tree 0 t5_1310root t5_1310jobs t5_1310frontier t5_1310all
theorem t5_1311choices : plan5171.choices=[5,9,6,6,10].map (options 5 5) := by rfl


theorem t5_1311part0 : t5_1311jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1311frontier : t5_1311root.frontier 0=t5_1311jobs := by rfl
theorem t5_1311all : t5_1311jobs.all (Job.check tree)=true := by
  simp only [t5_1311jobs,List.all_append,List.all_nil,t5_1311part0,Bool.and_self]
theorem t5_1311checked : Checked tree [5,9,6,6,10] := by
  refine ⟨plan5171,valid5171,t5_1311choices,?_⟩
  exact check_of_frontier tree 0 t5_1311root t5_1311jobs t5_1311frontier t5_1311all
theorem t5_1312choices : plan5172.choices=[5,9,6,7,7].map (options 5 5) := by rfl


theorem t5_1312part0 : t5_1312jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1312frontier : t5_1312root.frontier 0=t5_1312jobs := by rfl
theorem t5_1312all : t5_1312jobs.all (Job.check tree)=true := by
  simp only [t5_1312jobs,List.all_append,List.all_nil,t5_1312part0,Bool.and_self]
theorem t5_1312checked : Checked tree [5,9,6,7,7] := by
  refine ⟨plan5172,valid5172,t5_1312choices,?_⟩
  exact check_of_frontier tree 0 t5_1312root t5_1312jobs t5_1312frontier t5_1312all
theorem t5_1313choices : plan5173.choices=[5,9,6,10,7].map (options 5 5) := by rfl


theorem t5_1313part0 : t5_1313jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1313frontier : t5_1313root.frontier 0=t5_1313jobs := by rfl
theorem t5_1313all : t5_1313jobs.all (Job.check tree)=true := by
  simp only [t5_1313jobs,List.all_append,List.all_nil,t5_1313part0,Bool.and_self]
theorem t5_1313checked : Checked tree [5,9,6,10,7] := by
  refine ⟨plan5173,valid5173,t5_1313choices,?_⟩
  exact check_of_frontier tree 0 t5_1313root t5_1313jobs t5_1313frontier t5_1313all
theorem t5_1314choices : plan5174.choices=[5,9,6,10,10].map (options 5 5) := by rfl


theorem t5_1314part0 : t5_1314jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1314frontier : t5_1314root.frontier 0=t5_1314jobs := by rfl
theorem t5_1314all : t5_1314jobs.all (Job.check tree)=true := by
  simp only [t5_1314jobs,List.all_append,List.all_nil,t5_1314part0,Bool.and_self]
theorem t5_1314checked : Checked tree [5,9,6,10,10] := by
  refine ⟨plan5174,valid5174,t5_1314choices,?_⟩
  exact check_of_frontier tree 0 t5_1314root t5_1314jobs t5_1314frontier t5_1314all
theorem t5_1315choices : plan5175.choices=[5,9,7,7,7].map (options 5 5) := by rfl


theorem t5_1315part0 : t5_1315jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1315frontier : t5_1315root.frontier 0=t5_1315jobs := by rfl
theorem t5_1315all : t5_1315jobs.all (Job.check tree)=true := by
  simp only [t5_1315jobs,List.all_append,List.all_nil,t5_1315part0,Bool.and_self]
theorem t5_1315checked : Checked tree [5,9,7,7,7] := by
  refine ⟨plan5175,valid5175,t5_1315choices,?_⟩
  exact check_of_frontier tree 0 t5_1315root t5_1315jobs t5_1315frontier t5_1315all
theorem t5_1316choices : plan4388.choices=[5,9,9,3,3].map (options 5 3) := by rfl


theorem t5_1316part0 : t5_1316jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1316frontier : t5_1316root.frontier 0=t5_1316jobs := by rfl
theorem t5_1316all : t5_1316jobs.all (Job.check tree)=true := by
  simp only [t5_1316jobs,List.all_append,List.all_nil,t5_1316part0,Bool.and_self]
theorem t5_1316checked : Checked tree [5,9,9,3,3] := by
  refine ⟨plan4388,valid4388,t5_1316choices,?_⟩
  exact check_of_frontier tree 0 t5_1316root t5_1316jobs t5_1316frontier t5_1316all
theorem t5_1317choices : plan4888.choices=[5,9,9,3,6].map (options 5 4) := by rfl


theorem t5_1317part0 : t5_1317jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1317frontier : t5_1317root.frontier 0=t5_1317jobs := by rfl
theorem t5_1317all : t5_1317jobs.all (Job.check tree)=true := by
  simp only [t5_1317jobs,List.all_append,List.all_nil,t5_1317part0,Bool.and_self]
theorem t5_1317checked : Checked tree [5,9,9,3,6] := by
  refine ⟨plan4888,valid4888,t5_1317choices,?_⟩
  exact check_of_frontier tree 0 t5_1317root t5_1317jobs t5_1317frontier t5_1317all
theorem t5_1318choices : plan4889.choices=[5,9,9,3,7].map (options 5 4) := by rfl


theorem t5_1318part0 : t5_1318jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1318frontier : t5_1318root.frontier 0=t5_1318jobs := by rfl
theorem t5_1318all : t5_1318jobs.all (Job.check tree)=true := by
  simp only [t5_1318jobs,List.all_append,List.all_nil,t5_1318part0,Bool.and_self]
theorem t5_1318checked : Checked tree [5,9,9,3,7] := by
  refine ⟨plan4889,valid4889,t5_1318choices,?_⟩
  exact check_of_frontier tree 0 t5_1318root t5_1318jobs t5_1318frontier t5_1318all
theorem t5_1319choices : plan4890.choices=[5,9,9,3,10].map (options 5 4) := by rfl


theorem t5_1319part0 : t5_1319jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1319frontier : t5_1319root.frontier 0=t5_1319jobs := by rfl
theorem t5_1319all : t5_1319jobs.all (Job.check tree)=true := by
  simp only [t5_1319jobs,List.all_append,List.all_nil,t5_1319part0,Bool.and_self]
theorem t5_1319checked : Checked tree [5,9,9,3,10] := by
  refine ⟨plan4890,valid4890,t5_1319choices,?_⟩
  exact check_of_frontier tree 0 t5_1319root t5_1319jobs t5_1319frontier t5_1319all
theorem t5_1320choices : plan5176.choices=[5,9,9,6,6].map (options 5 5) := by rfl


theorem t5_1320part0 : t5_1320jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1320frontier : t5_1320root.frontier 0=t5_1320jobs := by rfl
theorem t5_1320all : t5_1320jobs.all (Job.check tree)=true := by
  simp only [t5_1320jobs,List.all_append,List.all_nil,t5_1320part0,Bool.and_self]
theorem t5_1320checked : Checked tree [5,9,9,6,6] := by
  refine ⟨plan5176,valid5176,t5_1320choices,?_⟩
  exact check_of_frontier tree 0 t5_1320root t5_1320jobs t5_1320frontier t5_1320all
theorem t5_1321choices : plan5177.choices=[5,9,9,6,7].map (options 5 5) := by rfl


theorem t5_1321part0 : t5_1321jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1321frontier : t5_1321root.frontier 0=t5_1321jobs := by rfl
theorem t5_1321all : t5_1321jobs.all (Job.check tree)=true := by
  simp only [t5_1321jobs,List.all_append,List.all_nil,t5_1321part0,Bool.and_self]
theorem t5_1321checked : Checked tree [5,9,9,6,7] := by
  refine ⟨plan5177,valid5177,t5_1321choices,?_⟩
  exact check_of_frontier tree 0 t5_1321root t5_1321jobs t5_1321frontier t5_1321all
theorem t5_1322choices : plan5178.choices=[5,9,9,6,10].map (options 5 5) := by rfl


theorem t5_1322part0 : t5_1322jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1322frontier : t5_1322root.frontier 0=t5_1322jobs := by rfl
theorem t5_1322all : t5_1322jobs.all (Job.check tree)=true := by
  simp only [t5_1322jobs,List.all_append,List.all_nil,t5_1322part0,Bool.and_self]
theorem t5_1322checked : Checked tree [5,9,9,6,10] := by
  refine ⟨plan5178,valid5178,t5_1322choices,?_⟩
  exact check_of_frontier tree 0 t5_1322root t5_1322jobs t5_1322frontier t5_1322all
theorem t5_1323choices : plan5179.choices=[5,9,9,7,7].map (options 5 5) := by rfl


theorem t5_1323part0 : t5_1323jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1323frontier : t5_1323root.frontier 0=t5_1323jobs := by rfl
theorem t5_1323all : t5_1323jobs.all (Job.check tree)=true := by
  simp only [t5_1323jobs,List.all_append,List.all_nil,t5_1323part0,Bool.and_self]
theorem t5_1323checked : Checked tree [5,9,9,7,7] := by
  refine ⟨plan5179,valid5179,t5_1323choices,?_⟩
  exact check_of_frontier tree 0 t5_1323root t5_1323jobs t5_1323frontier t5_1323all
theorem t5_1324choices : plan4891.choices=[5,9,9,9,3].map (options 5 4) := by rfl


theorem t5_1324part0 : t5_1324jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1324frontier : t5_1324root.frontier 0=t5_1324jobs := by rfl
theorem t5_1324all : t5_1324jobs.all (Job.check tree)=true := by
  simp only [t5_1324jobs,List.all_append,List.all_nil,t5_1324part0,Bool.and_self]
theorem t5_1324checked : Checked tree [5,9,9,9,3] := by
  refine ⟨plan4891,valid4891,t5_1324choices,?_⟩
  exact check_of_frontier tree 0 t5_1324root t5_1324jobs t5_1324frontier t5_1324all
theorem t5_1325choices : plan5180.choices=[5,9,9,9,6].map (options 5 5) := by rfl


theorem t5_1325part0 : t5_1325jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1325frontier : t5_1325root.frontier 0=t5_1325jobs := by rfl
theorem t5_1325all : t5_1325jobs.all (Job.check tree)=true := by
  simp only [t5_1325jobs,List.all_append,List.all_nil,t5_1325part0,Bool.and_self]
theorem t5_1325checked : Checked tree [5,9,9,9,6] := by
  refine ⟨plan5180,valid5180,t5_1325choices,?_⟩
  exact check_of_frontier tree 0 t5_1325root t5_1325jobs t5_1325frontier t5_1325all
theorem t5_1326choices : plan5181.choices=[5,9,9,9,7].map (options 5 5) := by rfl


theorem t5_1326part0 : t5_1326jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1326frontier : t5_1326root.frontier 0=t5_1326jobs := by rfl
theorem t5_1326all : t5_1326jobs.all (Job.check tree)=true := by
  simp only [t5_1326jobs,List.all_append,List.all_nil,t5_1326part0,Bool.and_self]
theorem t5_1326checked : Checked tree [5,9,9,9,7] := by
  refine ⟨plan5181,valid5181,t5_1326choices,?_⟩
  exact check_of_frontier tree 0 t5_1326root t5_1326jobs t5_1326frontier t5_1326all
theorem t5_1327choices : plan5182.choices=[5,9,9,9,9].map (options 5 5) := by rfl


theorem t5_1327part0 : t5_1327jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1327frontier : t5_1327root.frontier 0=t5_1327jobs := by rfl
theorem t5_1327all : t5_1327jobs.all (Job.check tree)=true := by
  simp only [t5_1327jobs,List.all_append,List.all_nil,t5_1327part0,Bool.and_self]
theorem t5_1327checked : Checked tree [5,9,9,9,9] := by
  refine ⟨plan5182,valid5182,t5_1327choices,?_⟩
  exact check_of_frontier tree 0 t5_1327root t5_1327jobs t5_1327frontier t5_1327all
theorem t5_1328choices : plan5183.choices=[5,9,9,9,10].map (options 5 5) := by rfl


theorem t5_1328part0 : t5_1328jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1328frontier : t5_1328root.frontier 0=t5_1328jobs := by rfl
theorem t5_1328all : t5_1328jobs.all (Job.check tree)=true := by
  simp only [t5_1328jobs,List.all_append,List.all_nil,t5_1328part0,Bool.and_self]
theorem t5_1328checked : Checked tree [5,9,9,9,10] := by
  refine ⟨plan5183,valid5183,t5_1328choices,?_⟩
  exact check_of_frontier tree 0 t5_1328root t5_1328jobs t5_1328frontier t5_1328all
theorem t5_1329choices : plan5184.choices=[5,9,9,10,7].map (options 5 5) := by rfl


theorem t5_1329part0 : t5_1329jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1329frontier : t5_1329root.frontier 0=t5_1329jobs := by rfl
theorem t5_1329all : t5_1329jobs.all (Job.check tree)=true := by
  simp only [t5_1329jobs,List.all_append,List.all_nil,t5_1329part0,Bool.and_self]
theorem t5_1329checked : Checked tree [5,9,9,10,7] := by
  refine ⟨plan5184,valid5184,t5_1329choices,?_⟩
  exact check_of_frontier tree 0 t5_1329root t5_1329jobs t5_1329frontier t5_1329all
theorem t5_1330choices : plan5185.choices=[5,9,9,10,10].map (options 5 5) := by rfl


theorem t5_1330part0 : t5_1330jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1330frontier : t5_1330root.frontier 0=t5_1330jobs := by rfl
theorem t5_1330all : t5_1330jobs.all (Job.check tree)=true := by
  simp only [t5_1330jobs,List.all_append,List.all_nil,t5_1330part0,Bool.and_self]
theorem t5_1330checked : Checked tree [5,9,9,10,10] := by
  refine ⟨plan5185,valid5185,t5_1330choices,?_⟩
  exact check_of_frontier tree 0 t5_1330root t5_1330jobs t5_1330frontier t5_1330all
theorem t5_1331choices : plan5186.choices=[5,9,10,7,7].map (options 5 5) := by rfl


theorem t5_1331part0 : t5_1331jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1331frontier : t5_1331root.frontier 0=t5_1331jobs := by rfl
theorem t5_1331all : t5_1331jobs.all (Job.check tree)=true := by
  simp only [t5_1331jobs,List.all_append,List.all_nil,t5_1331part0,Bool.and_self]
theorem t5_1331checked : Checked tree [5,9,10,7,7] := by
  refine ⟨plan5186,valid5186,t5_1331choices,?_⟩
  exact check_of_frontier tree 0 t5_1331root t5_1331jobs t5_1331frontier t5_1331all
theorem t5_1332choices : plan5187.choices=[5,9,10,10,7].map (options 5 5) := by rfl


theorem t5_1332part0 : t5_1332jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1332frontier : t5_1332root.frontier 0=t5_1332jobs := by rfl
theorem t5_1332all : t5_1332jobs.all (Job.check tree)=true := by
  simp only [t5_1332jobs,List.all_append,List.all_nil,t5_1332part0,Bool.and_self]
theorem t5_1332checked : Checked tree [5,9,10,10,7] := by
  refine ⟨plan5187,valid5187,t5_1332choices,?_⟩
  exact check_of_frontier tree 0 t5_1332root t5_1332jobs t5_1332frontier t5_1332all
theorem t5_1333choices : plan5188.choices=[5,9,10,10,10].map (options 5 5) := by rfl


theorem t5_1333part0 : t5_1333jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1333frontier : t5_1333root.frontier 0=t5_1333jobs := by rfl
theorem t5_1333all : t5_1333jobs.all (Job.check tree)=true := by
  simp only [t5_1333jobs,List.all_append,List.all_nil,t5_1333part0,Bool.and_self]
theorem t5_1333checked : Checked tree [5,9,10,10,10] := by
  refine ⟨plan5188,valid5188,t5_1333choices,?_⟩
  exact check_of_frontier tree 0 t5_1333root t5_1333jobs t5_1333frontier t5_1333all
theorem t5_1334choices : plan5189.choices=[5,10,7,7,7].map (options 5 5) := by rfl


theorem t5_1334part0 : t5_1334jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1334frontier : t5_1334root.frontier 0=t5_1334jobs := by rfl
theorem t5_1334all : t5_1334jobs.all (Job.check tree)=true := by
  simp only [t5_1334jobs,List.all_append,List.all_nil,t5_1334part0,Bool.and_self]
theorem t5_1334checked : Checked tree [5,10,7,7,7] := by
  refine ⟨plan5189,valid5189,t5_1334choices,?_⟩
  exact check_of_frontier tree 0 t5_1334root t5_1334jobs t5_1334frontier t5_1334all
theorem t5_1335choices : plan5190.choices=[5,10,10,7,7].map (options 5 5) := by rfl


theorem t5_1335part0 : t5_1335jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1335frontier : t5_1335root.frontier 0=t5_1335jobs := by rfl
theorem t5_1335all : t5_1335jobs.all (Job.check tree)=true := by
  simp only [t5_1335jobs,List.all_append,List.all_nil,t5_1335part0,Bool.and_self]
theorem t5_1335checked : Checked tree [5,10,10,7,7] := by
  refine ⟨plan5190,valid5190,t5_1335choices,?_⟩
  exact check_of_frontier tree 0 t5_1335root t5_1335jobs t5_1335frontier t5_1335all
theorem t5_1336choices : plan5191.choices=[5,10,10,10,7].map (options 5 5) := by rfl


theorem t5_1336part0 : t5_1336jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1336frontier : t5_1336root.frontier 0=t5_1336jobs := by rfl
theorem t5_1336all : t5_1336jobs.all (Job.check tree)=true := by
  simp only [t5_1336jobs,List.all_append,List.all_nil,t5_1336part0,Bool.and_self]
theorem t5_1336checked : Checked tree [5,10,10,10,7] := by
  refine ⟨plan5191,valid5191,t5_1336choices,?_⟩
  exact check_of_frontier tree 0 t5_1336root t5_1336jobs t5_1336frontier t5_1336all
theorem t5_1337choices : plan5192.choices=[5,10,10,10,10].map (options 5 5) := by rfl


theorem t5_1337part0 : t5_1337jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1337frontier : t5_1337root.frontier 0=t5_1337jobs := by rfl
theorem t5_1337all : t5_1337jobs.all (Job.check tree)=true := by
  simp only [t5_1337jobs,List.all_append,List.all_nil,t5_1337part0,Bool.and_self]
theorem t5_1337checked : Checked tree [5,10,10,10,10] := by
  refine ⟨plan5192,valid5192,t5_1337choices,?_⟩
  exact check_of_frontier tree 0 t5_1337root t5_1337jobs t5_1337frontier t5_1337all
theorem t5_1338choices : plan5193.choices=[6,6,6,6,6].map (options 5 5) := by rfl


theorem t5_1338part0 : t5_1338jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1338frontier : t5_1338root.frontier 0=t5_1338jobs := by rfl
theorem t5_1338all : t5_1338jobs.all (Job.check tree)=true := by
  simp only [t5_1338jobs,List.all_append,List.all_nil,t5_1338part0,Bool.and_self]
theorem t5_1338checked : Checked tree [6,6,6,6,6] := by
  refine ⟨plan5193,valid5193,t5_1338choices,?_⟩
  exact check_of_frontier tree 0 t5_1338root t5_1338jobs t5_1338frontier t5_1338all
theorem t5_1339choices : plan5194.choices=[6,6,6,6,7].map (options 5 5) := by rfl


theorem t5_1339part0 : t5_1339jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1339frontier : t5_1339root.frontier 0=t5_1339jobs := by rfl
theorem t5_1339all : t5_1339jobs.all (Job.check tree)=true := by
  simp only [t5_1339jobs,List.all_append,List.all_nil,t5_1339part0,Bool.and_self]
theorem t5_1339checked : Checked tree [6,6,6,6,7] := by
  refine ⟨plan5194,valid5194,t5_1339choices,?_⟩
  exact check_of_frontier tree 0 t5_1339root t5_1339jobs t5_1339frontier t5_1339all
theorem t5_1340choices : plan5195.choices=[6,6,6,6,10].map (options 5 5) := by rfl


theorem t5_1340part0 : t5_1340jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1340frontier : t5_1340root.frontier 0=t5_1340jobs := by rfl
theorem t5_1340all : t5_1340jobs.all (Job.check tree)=true := by
  simp only [t5_1340jobs,List.all_append,List.all_nil,t5_1340part0,Bool.and_self]
theorem t5_1340checked : Checked tree [6,6,6,6,10] := by
  refine ⟨plan5195,valid5195,t5_1340choices,?_⟩
  exact check_of_frontier tree 0 t5_1340root t5_1340jobs t5_1340frontier t5_1340all
theorem t5_1341choices : plan5196.choices=[6,6,6,7,7].map (options 5 5) := by rfl


theorem t5_1341part0 : t5_1341jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1341frontier : t5_1341root.frontier 0=t5_1341jobs := by rfl
theorem t5_1341all : t5_1341jobs.all (Job.check tree)=true := by
  simp only [t5_1341jobs,List.all_append,List.all_nil,t5_1341part0,Bool.and_self]
theorem t5_1341checked : Checked tree [6,6,6,7,7] := by
  refine ⟨plan5196,valid5196,t5_1341choices,?_⟩
  exact check_of_frontier tree 0 t5_1341root t5_1341jobs t5_1341frontier t5_1341all
theorem t5_1342choices : plan5197.choices=[6,6,6,10,7].map (options 5 5) := by rfl


theorem t5_1342part0 : t5_1342jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1342frontier : t5_1342root.frontier 0=t5_1342jobs := by rfl
theorem t5_1342all : t5_1342jobs.all (Job.check tree)=true := by
  simp only [t5_1342jobs,List.all_append,List.all_nil,t5_1342part0,Bool.and_self]
theorem t5_1342checked : Checked tree [6,6,6,10,7] := by
  refine ⟨plan5197,valid5197,t5_1342choices,?_⟩
  exact check_of_frontier tree 0 t5_1342root t5_1342jobs t5_1342frontier t5_1342all
theorem t5_1343choices : plan5198.choices=[6,6,6,10,10].map (options 5 5) := by rfl


theorem t5_1343part0 : t5_1343jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1343frontier : t5_1343root.frontier 0=t5_1343jobs := by rfl
theorem t5_1343all : t5_1343jobs.all (Job.check tree)=true := by
  simp only [t5_1343jobs,List.all_append,List.all_nil,t5_1343part0,Bool.and_self]
theorem t5_1343checked : Checked tree [6,6,6,10,10] := by
  refine ⟨plan5198,valid5198,t5_1343choices,?_⟩
  exact check_of_frontier tree 0 t5_1343root t5_1343jobs t5_1343frontier t5_1343all
theorem t5_1344choices : plan5199.choices=[6,6,7,7,7].map (options 5 5) := by rfl


theorem t5_1344part0 : t5_1344jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1344frontier : t5_1344root.frontier 0=t5_1344jobs := by rfl
theorem t5_1344all : t5_1344jobs.all (Job.check tree)=true := by
  simp only [t5_1344jobs,List.all_append,List.all_nil,t5_1344part0,Bool.and_self]
theorem t5_1344checked : Checked tree [6,6,7,7,7] := by
  refine ⟨plan5199,valid5199,t5_1344choices,?_⟩
  exact check_of_frontier tree 0 t5_1344root t5_1344jobs t5_1344frontier t5_1344all
theorem t5_1345choices : plan5200.choices=[6,6,10,7,7].map (options 5 5) := by rfl


theorem t5_1345part0 : t5_1345jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1345frontier : t5_1345root.frontier 0=t5_1345jobs := by rfl
theorem t5_1345all : t5_1345jobs.all (Job.check tree)=true := by
  simp only [t5_1345jobs,List.all_append,List.all_nil,t5_1345part0,Bool.and_self]
theorem t5_1345checked : Checked tree [6,6,10,7,7] := by
  refine ⟨plan5200,valid5200,t5_1345choices,?_⟩
  exact check_of_frontier tree 0 t5_1345root t5_1345jobs t5_1345frontier t5_1345all
theorem t5_1346choices : plan5201.choices=[6,6,10,10,7].map (options 5 5) := by rfl


theorem t5_1346part0 : t5_1346jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1346frontier : t5_1346root.frontier 0=t5_1346jobs := by rfl
theorem t5_1346all : t5_1346jobs.all (Job.check tree)=true := by
  simp only [t5_1346jobs,List.all_append,List.all_nil,t5_1346part0,Bool.and_self]
theorem t5_1346checked : Checked tree [6,6,10,10,7] := by
  refine ⟨plan5201,valid5201,t5_1346choices,?_⟩
  exact check_of_frontier tree 0 t5_1346root t5_1346jobs t5_1346frontier t5_1346all
theorem t5_1347choices : plan5202.choices=[6,6,10,10,10].map (options 5 5) := by rfl


theorem t5_1347part0 : t5_1347jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1347frontier : t5_1347root.frontier 0=t5_1347jobs := by rfl
theorem t5_1347all : t5_1347jobs.all (Job.check tree)=true := by
  simp only [t5_1347jobs,List.all_append,List.all_nil,t5_1347part0,Bool.and_self]
theorem t5_1347checked : Checked tree [6,6,10,10,10] := by
  refine ⟨plan5202,valid5202,t5_1347choices,?_⟩
  exact check_of_frontier tree 0 t5_1347root t5_1347jobs t5_1347frontier t5_1347all
theorem t5_1348choices : plan5203.choices=[6,7,7,7,7].map (options 5 5) := by rfl


theorem t5_1348part0 : t5_1348jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1348frontier : t5_1348root.frontier 0=t5_1348jobs := by rfl
theorem t5_1348all : t5_1348jobs.all (Job.check tree)=true := by
  simp only [t5_1348jobs,List.all_append,List.all_nil,t5_1348part0,Bool.and_self]
theorem t5_1348checked : Checked tree [6,7,7,7,7] := by
  refine ⟨plan5203,valid5203,t5_1348choices,?_⟩
  exact check_of_frontier tree 0 t5_1348root t5_1348jobs t5_1348frontier t5_1348all
theorem t5_1349choices : plan5204.choices=[6,10,7,7,7].map (options 5 5) := by rfl


theorem t5_1349part0 : t5_1349jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1349frontier : t5_1349root.frontier 0=t5_1349jobs := by rfl
theorem t5_1349all : t5_1349jobs.all (Job.check tree)=true := by
  simp only [t5_1349jobs,List.all_append,List.all_nil,t5_1349part0,Bool.and_self]
theorem t5_1349checked : Checked tree [6,10,7,7,7] := by
  refine ⟨plan5204,valid5204,t5_1349choices,?_⟩
  exact check_of_frontier tree 0 t5_1349root t5_1349jobs t5_1349frontier t5_1349all
theorem t5_1350choices : plan5205.choices=[6,10,10,7,7].map (options 5 5) := by rfl


theorem t5_1350part0 : t5_1350jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1350frontier : t5_1350root.frontier 0=t5_1350jobs := by rfl
theorem t5_1350all : t5_1350jobs.all (Job.check tree)=true := by
  simp only [t5_1350jobs,List.all_append,List.all_nil,t5_1350part0,Bool.and_self]
theorem t5_1350checked : Checked tree [6,10,10,7,7] := by
  refine ⟨plan5205,valid5205,t5_1350choices,?_⟩
  exact check_of_frontier tree 0 t5_1350root t5_1350jobs t5_1350frontier t5_1350all
theorem t5_1351choices : plan5206.choices=[6,10,10,10,7].map (options 5 5) := by rfl


theorem t5_1351part0 : t5_1351jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1351frontier : t5_1351root.frontier 0=t5_1351jobs := by rfl
theorem t5_1351all : t5_1351jobs.all (Job.check tree)=true := by
  simp only [t5_1351jobs,List.all_append,List.all_nil,t5_1351part0,Bool.and_self]
theorem t5_1351checked : Checked tree [6,10,10,10,7] := by
  refine ⟨plan5206,valid5206,t5_1351choices,?_⟩
  exact check_of_frontier tree 0 t5_1351root t5_1351jobs t5_1351frontier t5_1351all
theorem t5_1352choices : plan5207.choices=[6,10,10,10,10].map (options 5 5) := by rfl


theorem t5_1352part0 : t5_1352jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1352frontier : t5_1352root.frontier 0=t5_1352jobs := by rfl
theorem t5_1352all : t5_1352jobs.all (Job.check tree)=true := by
  simp only [t5_1352jobs,List.all_append,List.all_nil,t5_1352part0,Bool.and_self]
theorem t5_1352checked : Checked tree [6,10,10,10,10] := by
  refine ⟨plan5207,valid5207,t5_1352choices,?_⟩
  exact check_of_frontier tree 0 t5_1352root t5_1352jobs t5_1352frontier t5_1352all
theorem t5_1353choices : plan5208.choices=[7,7,7,7,7].map (options 5 5) := by rfl


theorem t5_1353part0 : t5_1353jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1353frontier : t5_1353root.frontier 0=t5_1353jobs := by rfl
theorem t5_1353all : t5_1353jobs.all (Job.check tree)=true := by
  simp only [t5_1353jobs,List.all_append,List.all_nil,t5_1353part0,Bool.and_self]
theorem t5_1353checked : Checked tree [7,7,7,7,7] := by
  refine ⟨plan5208,valid5208,t5_1353choices,?_⟩
  exact check_of_frontier tree 0 t5_1353root t5_1353jobs t5_1353frontier t5_1353all
theorem t5_1354choices : plan3754.choices=[8,2,2,2,3].map (options 5 1) := by rfl


theorem t5_1354part0 : t5_1354jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1354frontier : t5_1354root.frontier 0=t5_1354jobs := by rfl
theorem t5_1354all : t5_1354jobs.all (Job.check tree)=true := by
  simp only [t5_1354jobs,List.all_append,List.all_nil,t5_1354part0,Bool.and_self]
theorem t5_1354checked : Checked tree [8,2,2,2,3] := by
  refine ⟨plan3754,valid3754,t5_1354choices,?_⟩
  exact check_of_frontier tree 0 t5_1354root t5_1354jobs t5_1354frontier t5_1354all
theorem t5_1355choices : plan3976.choices=[8,2,2,2,6].map (options 5 2) := by rfl


theorem t5_1355part0 : t5_1355jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1355frontier : t5_1355root.frontier 0=t5_1355jobs := by rfl
theorem t5_1355all : t5_1355jobs.all (Job.check tree)=true := by
  simp only [t5_1355jobs,List.all_append,List.all_nil,t5_1355part0,Bool.and_self]
theorem t5_1355checked : Checked tree [8,2,2,2,6] := by
  refine ⟨plan3976,valid3976,t5_1355choices,?_⟩
  exact check_of_frontier tree 0 t5_1355root t5_1355jobs t5_1355frontier t5_1355all
theorem t5_1356choices : plan3977.choices=[8,2,2,2,7].map (options 5 2) := by rfl


theorem t5_1356part0 : t5_1356jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1356frontier : t5_1356root.frontier 0=t5_1356jobs := by rfl
theorem t5_1356all : t5_1356jobs.all (Job.check tree)=true := by
  simp only [t5_1356jobs,List.all_append,List.all_nil,t5_1356part0,Bool.and_self]
theorem t5_1356checked : Checked tree [8,2,2,2,7] := by
  refine ⟨plan3977,valid3977,t5_1356choices,?_⟩
  exact check_of_frontier tree 0 t5_1356root t5_1356jobs t5_1356frontier t5_1356all
theorem t5_1357choices : plan3978.choices=[8,2,2,2,10].map (options 5 2) := by rfl


theorem t5_1357part0 : t5_1357jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1357frontier : t5_1357root.frontier 0=t5_1357jobs := by rfl
theorem t5_1357all : t5_1357jobs.all (Job.check tree)=true := by
  simp only [t5_1357jobs,List.all_append,List.all_nil,t5_1357part0,Bool.and_self]
theorem t5_1357checked : Checked tree [8,2,2,2,10] := by
  refine ⟨plan3978,valid3978,t5_1357choices,?_⟩
  exact check_of_frontier tree 0 t5_1357root t5_1357jobs t5_1357frontier t5_1357all
theorem t5_1358choices : plan3755.choices=[8,2,2,3,3].map (options 5 1) := by rfl


theorem t5_1358part0 : t5_1358jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1358frontier : t5_1358root.frontier 0=t5_1358jobs := by rfl
theorem t5_1358all : t5_1358jobs.all (Job.check tree)=true := by
  simp only [t5_1358jobs,List.all_append,List.all_nil,t5_1358part0,Bool.and_self]
theorem t5_1358checked : Checked tree [8,2,2,3,3] := by
  refine ⟨plan3755,valid3755,t5_1358choices,?_⟩
  exact check_of_frontier tree 0 t5_1358root t5_1358jobs t5_1358frontier t5_1358all
theorem t5_1359choices : plan3979.choices=[8,2,2,3,6].map (options 5 2) := by rfl


theorem t5_1359part0 : t5_1359jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1359frontier : t5_1359root.frontier 0=t5_1359jobs := by rfl
theorem t5_1359all : t5_1359jobs.all (Job.check tree)=true := by
  simp only [t5_1359jobs,List.all_append,List.all_nil,t5_1359part0,Bool.and_self]
theorem t5_1359checked : Checked tree [8,2,2,3,6] := by
  refine ⟨plan3979,valid3979,t5_1359choices,?_⟩
  exact check_of_frontier tree 0 t5_1359root t5_1359jobs t5_1359frontier t5_1359all
theorem t5_1360choices : plan3980.choices=[8,2,2,3,7].map (options 5 2) := by rfl


theorem t5_1360part0 : t5_1360jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1360frontier : t5_1360root.frontier 0=t5_1360jobs := by rfl
theorem t5_1360all : t5_1360jobs.all (Job.check tree)=true := by
  simp only [t5_1360jobs,List.all_append,List.all_nil,t5_1360part0,Bool.and_self]
theorem t5_1360checked : Checked tree [8,2,2,3,7] := by
  refine ⟨plan3980,valid3980,t5_1360choices,?_⟩
  exact check_of_frontier tree 0 t5_1360root t5_1360jobs t5_1360frontier t5_1360all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks039 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1319checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1320checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1321checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1322checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1323checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1324checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1325checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1326checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1307checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1327checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1328checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1329checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1330checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1331checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1332checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1333checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1334checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1335checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1336checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1308checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1337checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1338checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1339checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1340checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1341checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1342checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1343checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1344checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1345checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1346checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1309checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1347checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1348checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1349checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1350checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1351checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1352checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1353checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1354checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1355checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1356checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1310checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1357checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1358checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1359checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1360checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1311checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1312checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1313checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1314checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1315checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1316checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1317checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1318checked⟩
