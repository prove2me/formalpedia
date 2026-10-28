-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks169
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:07:05.199979+00:00
-- url     : https://prove2.me/submissions/f2328963-b705-49e8-9901-bb65c858618f

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks169
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks169
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans086
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
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





















































































theorem valid139 : plan139.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid140 : plan140.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid141 : plan141.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid142 : plan142.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid143 : plan143.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid144 : plan144.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid145 : plan145.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid146 : plan146.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid147 : plan147.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid148 : plan148.Valid := valid_step _ _ _ valid0 (by decide +kernel)















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





















theorem valid587 : plan587.Valid := valid_step _ _ _ valid139 (by decide +kernel)

theorem valid588 : plan588.Valid := valid_step _ _ _ valid140 (by decide +kernel)

theorem valid589 : plan589.Valid := valid_step _ _ _ valid141 (by decide +kernel)

theorem valid590 : plan590.Valid := valid_step _ _ _ valid142 (by decide +kernel)



theorem valid592 : plan592.Valid := valid_step _ _ _ valid143 (by decide +kernel)

theorem valid593 : plan593.Valid := valid_step _ _ _ valid144 (by decide +kernel)

theorem valid594 : plan594.Valid := valid_step _ _ _ valid145 (by decide +kernel)

theorem valid595 : plan595.Valid := valid_step _ _ _ valid144 (by decide +kernel)

theorem valid596 : plan596.Valid := valid_step _ _ _ valid144 (by decide +kernel)

theorem valid597 : plan597.Valid := valid_step _ _ _ valid145 (by decide +kernel)

theorem valid598 : plan598.Valid := valid_step _ _ _ valid146 (by decide +kernel)

theorem valid599 : plan599.Valid := valid_step _ _ _ valid147 (by decide +kernel)

theorem valid600 : plan600.Valid := valid_step _ _ _ valid148 (by decide +kernel)

theorem valid601 : plan601.Valid := valid_step _ _ _ valid147 (by decide +kernel)

theorem valid602 : plan602.Valid := valid_step _ _ _ valid147 (by decide +kernel)

theorem valid603 : plan603.Valid := valid_step _ _ _ valid148 (by decide +kernel)































theorem valid619 : plan619.Valid := valid_step _ _ _ valid156 (by decide +kernel)

theorem valid620 : plan620.Valid := valid_step _ _ _ valid156 (by decide +kernel)








































































































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

theorem valid1633 : plan1633.Valid := valid_step _ _ _ valid597 (by decide +kernel)







theorem valid1637 : plan1637.Valid := valid_step _ _ _ valid598 (by decide +kernel)

theorem valid1638 : plan1638.Valid := valid_step _ _ _ valid599 (by decide +kernel)

theorem valid1639 : plan1639.Valid := valid_step _ _ _ valid600 (by decide +kernel)

theorem valid1640 : plan1640.Valid := valid_step _ _ _ valid601 (by decide +kernel)

theorem valid1641 : plan1641.Valid := valid_step _ _ _ valid602 (by decide +kernel)

theorem valid1642 : plan1642.Valid := valid_step _ _ _ valid603 (by decide +kernel)































































theorem valid1674 : plan1674.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1675 : plan1675.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1676 : plan1676.Valid := valid_step _ _ _ valid620 (by decide +kernel)








































































































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













































































































































































theorem valid1623 : plan1623.Valid := valid_step _ _ _ valid587 (by decide +kernel)

theorem valid1624 : plan1624.Valid := valid_step _ _ _ valid588 (by decide +kernel)

theorem valid1625 : plan1625.Valid := valid_step _ _ _ valid589 (by decide +kernel)

theorem valid1626 : plan1626.Valid := valid_step _ _ _ valid590 (by decide +kernel)



theorem valid1628 : plan1628.Valid := valid_step _ _ _ valid592 (by decide +kernel)

theorem valid1629 : plan1629.Valid := valid_step _ _ _ valid593 (by decide +kernel)

theorem valid1630 : plan1630.Valid := valid_step _ _ _ valid594 (by decide +kernel)

theorem valid1631 : plan1631.Valid := valid_step _ _ _ valid595 (by decide +kernel)

theorem valid1632 : plan1632.Valid := valid_step _ _ _ valid596 (by decide +kernel)
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









theorem valid3557 : plan3557.Valid := valid_step _ _ _ valid1623 (by decide +kernel)

theorem valid3558 : plan3558.Valid := valid_step _ _ _ valid1624 (by decide +kernel)

theorem valid3559 : plan3559.Valid := valid_step _ _ _ valid1625 (by decide +kernel)

theorem valid3560 : plan3560.Valid := valid_step _ _ _ valid1626 (by decide +kernel)



theorem valid3562 : plan3562.Valid := valid_step _ _ _ valid1628 (by decide +kernel)

theorem valid3563 : plan3563.Valid := valid_step _ _ _ valid1629 (by decide +kernel)

theorem valid3564 : plan3564.Valid := valid_step _ _ _ valid1630 (by decide +kernel)

theorem valid3565 : plan3565.Valid := valid_step _ _ _ valid1631 (by decide +kernel)

theorem valid3566 : plan3566.Valid := valid_step _ _ _ valid1632 (by decide +kernel)

theorem valid3567 : plan3567.Valid := valid_step _ _ _ valid1633 (by decide +kernel)







theorem valid3571 : plan3571.Valid := valid_step _ _ _ valid1637 (by decide +kernel)

theorem valid3572 : plan3572.Valid := valid_step _ _ _ valid1638 (by decide +kernel)

theorem valid3573 : plan3573.Valid := valid_step _ _ _ valid1639 (by decide +kernel)

theorem valid3574 : plan3574.Valid := valid_step _ _ _ valid1640 (by decide +kernel)

theorem valid3575 : plan3575.Valid := valid_step _ _ _ valid1641 (by decide +kernel)

theorem valid3576 : plan3576.Valid := valid_step _ _ _ valid1642 (by decide +kernel)















































































































theorem valid3632 : plan3632.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3633 : plan3633.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3634 : plan3634.Valid := valid_step _ _ _ valid1675 (by decide +kernel)

theorem valid3635 : plan3635.Valid := valid_step _ _ _ valid1676 (by decide +kernel)


























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

















































































































theorem valid6105 : plan6105.Valid := valid_step _ _ _ valid3557 (by decide +kernel)

theorem valid6106 : plan6106.Valid := valid_step _ _ _ valid3558 (by decide +kernel)

theorem valid6107 : plan6107.Valid := valid_step _ _ _ valid3559 (by decide +kernel)

theorem valid6108 : plan6108.Valid := valid_step _ _ _ valid3560 (by decide +kernel)



theorem valid6110 : plan6110.Valid := valid_step _ _ _ valid3562 (by decide +kernel)

theorem valid6111 : plan6111.Valid := valid_step _ _ _ valid3563 (by decide +kernel)

theorem valid6112 : plan6112.Valid := valid_step _ _ _ valid3564 (by decide +kernel)

theorem valid6113 : plan6113.Valid := valid_step _ _ _ valid3565 (by decide +kernel)

theorem valid6114 : plan6114.Valid := valid_step _ _ _ valid3566 (by decide +kernel)

theorem valid6115 : plan6115.Valid := valid_step _ _ _ valid3567 (by decide +kernel)









theorem valid6120 : plan6120.Valid := valid_step _ _ _ valid3571 (by decide +kernel)

theorem valid6121 : plan6121.Valid := valid_step _ _ _ valid3572 (by decide +kernel)

theorem valid6122 : plan6122.Valid := valid_step _ _ _ valid3573 (by decide +kernel)

theorem valid6123 : plan6123.Valid := valid_step _ _ _ valid3574 (by decide +kernel)

theorem valid6124 : plan6124.Valid := valid_step _ _ _ valid3575 (by decide +kernel)

theorem valid6125 : plan6125.Valid := valid_step _ _ _ valid3576 (by decide +kernel)






































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

































































































































































theorem valid6225 : plan6225.Valid := valid_step _ _ _ valid3632 (by decide +kernel)





theorem valid6228 : plan6228.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6229 : plan6229.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6230 : plan6230.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6231 : plan6231.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6232 : plan6232.Valid := valid_step _ _ _ valid3634 (by decide +kernel)

theorem valid6233 : plan6233.Valid := valid_step _ _ _ valid3635 (by decide +kernel)














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















theorem valid8072 : plan8072.Valid := valid_step _ _ _ valid6105 (by decide +kernel)

theorem valid8073 : plan8073.Valid := valid_step _ _ _ valid6106 (by decide +kernel)

theorem valid8074 : plan8074.Valid := valid_step _ _ _ valid6107 (by decide +kernel)

theorem valid8075 : plan8075.Valid := valid_step _ _ _ valid6108 (by decide +kernel)





theorem valid8078 : plan8078.Valid := valid_step _ _ _ valid6110 (by decide +kernel)

theorem valid8079 : plan8079.Valid := valid_step _ _ _ valid6111 (by decide +kernel)

theorem valid8080 : plan8080.Valid := valid_step _ _ _ valid6112 (by decide +kernel)

theorem valid8081 : plan8081.Valid := valid_step _ _ _ valid6113 (by decide +kernel)

theorem valid8082 : plan8082.Valid := valid_step _ _ _ valid6114 (by decide +kernel)

theorem valid8083 : plan8083.Valid := valid_step _ _ _ valid6115 (by decide +kernel)















theorem valid8091 : plan8091.Valid := valid_step _ _ _ valid6120 (by decide +kernel)

theorem valid8092 : plan8092.Valid := valid_step _ _ _ valid6121 (by decide +kernel)

theorem valid8093 : plan8093.Valid := valid_step _ _ _ valid6122 (by decide +kernel)

theorem valid8094 : plan8094.Valid := valid_step _ _ _ valid6123 (by decide +kernel)

theorem valid8095 : plan8095.Valid := valid_step _ _ _ valid6124 (by decide +kernel)

theorem valid8096 : plan8096.Valid := valid_step _ _ _ valid6125 (by decide +kernel)
































































































































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























































































































theorem valid8412 : plan8412.Valid := valid_step _ _ _ valid8072 (by decide +kernel)



theorem valid8414 : plan8414.Valid := valid_step _ _ _ valid8073 (by decide +kernel)

theorem valid8415 : plan8415.Valid := valid_step _ _ _ valid8074 (by decide +kernel)

theorem valid8416 : plan8416.Valid := valid_step _ _ _ valid8075 (by decide +kernel)











theorem valid8422 : plan8422.Valid := valid_step _ _ _ valid8078 (by decide +kernel)

theorem valid8423 : plan8423.Valid := valid_step _ _ _ valid8079 (by decide +kernel)

theorem valid8424 : plan8424.Valid := valid_step _ _ _ valid8080 (by decide +kernel)

theorem valid8425 : plan8425.Valid := valid_step _ _ _ valid8081 (by decide +kernel)

theorem valid8426 : plan8426.Valid := valid_step _ _ _ valid8082 (by decide +kernel)

theorem valid8427 : plan8427.Valid := valid_step _ _ _ valid8083 (by decide +kernel)







































theorem valid8447 : plan8447.Valid := valid_step _ _ _ valid8091 (by decide +kernel)

theorem valid8448 : plan8448.Valid := valid_step _ _ _ valid8092 (by decide +kernel)
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

theorem valid8449 : plan8449.Valid := valid_step _ _ _ valid8093 (by decide +kernel)

theorem valid8450 : plan8450.Valid := valid_step _ _ _ valid8094 (by decide +kernel)

theorem valid8451 : plan8451.Valid := valid_step _ _ _ valid8095 (by decide +kernel)

theorem valid8452 : plan8452.Valid := valid_step _ _ _ valid8096 (by decide +kernel)
























































































































































































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



















































































































theorem valid8314 : plan8314.Valid := valid_step _ _ _ valid6228 (by decide +kernel)

theorem valid8315 : plan8315.Valid := valid_step _ _ _ valid6229 (by decide +kernel)

theorem valid8316 : plan8316.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8317 : plan8317.Valid := valid_step _ _ _ valid6231 (by decide +kernel)

theorem valid8318 : plan8318.Valid := valid_step _ _ _ valid6232 (by decide +kernel)

theorem valid8319 : plan8319.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8320 : plan8320.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8321 : plan8321.Valid := valid_step _ _ _ valid6231 (by decide +kernel)

theorem valid8322 : plan8322.Valid := valid_step _ _ _ valid6232 (by decide +kernel)

theorem valid8323 : plan8323.Valid := valid_step _ _ _ valid6233 (by decide +kernel)


























































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



































































































































theorem valid8802 : plan8802.Valid := valid_step _ _ _ valid8314 (by decide +kernel)

theorem valid8803 : plan8803.Valid := valid_step _ _ _ valid8315 (by decide +kernel)

theorem valid8804 : plan8804.Valid := valid_step _ _ _ valid8316 (by decide +kernel)

theorem valid8805 : plan8805.Valid := valid_step _ _ _ valid8317 (by decide +kernel)

theorem valid8806 : plan8806.Valid := valid_step _ _ _ valid8318 (by decide +kernel)

theorem valid8807 : plan8807.Valid := valid_step _ _ _ valid8319 (by decide +kernel)

theorem valid8808 : plan8808.Valid := valid_step _ _ _ valid8320 (by decide +kernel)

theorem valid8809 : plan8809.Valid := valid_step _ _ _ valid8321 (by decide +kernel)

theorem valid8810 : plan8810.Valid := valid_step _ _ _ valid8322 (by decide +kernel)

theorem valid8811 : plan8811.Valid := valid_step _ _ _ valid8323 (by decide +kernel)










































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
theorem t7_248choices : plan8802.choices=[2,9,9,7,7,7,7].map (options 7 6) := by rfl


theorem t7_248part0 : t7_248jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_248frontier : t7_248root.frontier 0=t7_248jobs := by rfl
theorem t7_248all : t7_248jobs.all (Job.check tree)=true := by
  simp only [t7_248jobs,List.all_append,List.all_nil,t7_248part0,Bool.and_self]
theorem t7_248checked : Checked tree [2,9,9,7,7,7,7] := by
  refine ⟨plan8802,valid8802,t7_248choices,?_⟩
  exact check_of_frontier tree 0 t7_248root t7_248jobs t7_248frontier t7_248all
theorem t7_249choices : plan8803.choices=[2,9,9,10,7,7,7].map (options 7 6) := by rfl


theorem t7_249part0 : t7_249jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_249frontier : t7_249root.frontier 0=t7_249jobs := by rfl
theorem t7_249all : t7_249jobs.all (Job.check tree)=true := by
  simp only [t7_249jobs,List.all_append,List.all_nil,t7_249part0,Bool.and_self]
theorem t7_249checked : Checked tree [2,9,9,10,7,7,7] := by
  refine ⟨plan8803,valid8803,t7_249choices,?_⟩
  exact check_of_frontier tree 0 t7_249root t7_249jobs t7_249frontier t7_249all
theorem t7_250choices : plan8804.choices=[2,9,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_250part0 : t7_250jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_250frontier : t7_250root.frontier 0=t7_250jobs := by rfl
theorem t7_250all : t7_250jobs.all (Job.check tree)=true := by
  simp only [t7_250jobs,List.all_append,List.all_nil,t7_250part0,Bool.and_self]
theorem t7_250checked : Checked tree [2,9,10,7,7,7,7] := by
  refine ⟨plan8804,valid8804,t7_250choices,?_⟩
  exact check_of_frontier tree 0 t7_250root t7_250jobs t7_250frontier t7_250all
theorem t7_251choices : plan8805.choices=[2,9,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_251part0 : t7_251jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_251frontier : t7_251root.frontier 0=t7_251jobs := by rfl
theorem t7_251all : t7_251jobs.all (Job.check tree)=true := by
  simp only [t7_251jobs,List.all_append,List.all_nil,t7_251part0,Bool.and_self]
theorem t7_251checked : Checked tree [2,9,10,10,7,7,7] := by
  refine ⟨plan8805,valid8805,t7_251choices,?_⟩
  exact check_of_frontier tree 0 t7_251root t7_251jobs t7_251frontier t7_251all
theorem t7_252choices : plan8806.choices=[2,9,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_252part0 : t7_252jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_252frontier : t7_252root.frontier 0=t7_252jobs := by rfl
theorem t7_252all : t7_252jobs.all (Job.check tree)=true := by
  simp only [t7_252jobs,List.all_append,List.all_nil,t7_252part0,Bool.and_self]
theorem t7_252checked : Checked tree [2,9,10,10,10,7,7] := by
  refine ⟨plan8806,valid8806,t7_252choices,?_⟩
  exact check_of_frontier tree 0 t7_252root t7_252jobs t7_252frontier t7_252all
theorem t7_253choices : plan8807.choices=[2,10,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_253part0 : t7_253jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_253part1 : t7_253jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_253frontier : t7_253root.frontier 1=t7_253jobs := by rfl
theorem t7_253all : t7_253jobs.all (Job.check tree)=true := by
  simp only [t7_253jobs,List.all_append,List.all_nil,t7_253part0,t7_253part1,Bool.and_self]
theorem t7_253checked : Checked tree [2,10,7,7,7,7,7] := by
  refine ⟨plan8807,valid8807,t7_253choices,?_⟩
  exact check_of_frontier tree 1 t7_253root t7_253jobs t7_253frontier t7_253all
theorem t7_254choices : plan8808.choices=[2,10,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_254part0 : t7_254jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_254part1 : t7_254jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_254frontier : t7_254root.frontier 1=t7_254jobs := by rfl
theorem t7_254all : t7_254jobs.all (Job.check tree)=true := by
  simp only [t7_254jobs,List.all_append,List.all_nil,t7_254part0,t7_254part1,Bool.and_self]
theorem t7_254checked : Checked tree [2,10,10,7,7,7,7] := by
  refine ⟨plan8808,valid8808,t7_254choices,?_⟩
  exact check_of_frontier tree 1 t7_254root t7_254jobs t7_254frontier t7_254all
theorem t7_255choices : plan8809.choices=[2,10,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_255part0 : t7_255jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_255frontier : t7_255root.frontier 0=t7_255jobs := by rfl
theorem t7_255all : t7_255jobs.all (Job.check tree)=true := by
  simp only [t7_255jobs,List.all_append,List.all_nil,t7_255part0,Bool.and_self]
theorem t7_255checked : Checked tree [2,10,10,10,7,7,7] := by
  refine ⟨plan8809,valid8809,t7_255choices,?_⟩
  exact check_of_frontier tree 0 t7_255root t7_255jobs t7_255frontier t7_255all
theorem t7_256choices : plan8810.choices=[2,10,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_256part0 : t7_256jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_256frontier : t7_256root.frontier 0=t7_256jobs := by rfl
theorem t7_256all : t7_256jobs.all (Job.check tree)=true := by
  simp only [t7_256jobs,List.all_append,List.all_nil,t7_256part0,Bool.and_self]
theorem t7_256checked : Checked tree [2,10,10,10,10,7,7] := by
  refine ⟨plan8810,valid8810,t7_256choices,?_⟩
  exact check_of_frontier tree 0 t7_256root t7_256jobs t7_256frontier t7_256all
theorem t7_257choices : plan8811.choices=[2,10,10,10,10,10,7].map (options 7 6) := by rfl


theorem t7_257part0 : t7_257jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_257frontier : t7_257root.frontier 0=t7_257jobs := by rfl
theorem t7_257all : t7_257jobs.all (Job.check tree)=true := by
  simp only [t7_257jobs,List.all_append,List.all_nil,t7_257part0,Bool.and_self]
theorem t7_257checked : Checked tree [2,10,10,10,10,10,7] := by
  refine ⟨plan8811,valid8811,t7_257choices,?_⟩
  exact check_of_frontier tree 0 t7_257root t7_257jobs t7_257frontier t7_257all
theorem t7_258choices : plan8412.choices=[3,3,3,3,3,3,3].map (options 7 0) := by rfl


theorem t7_258part0 : t7_258jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_258frontier : t7_258root.frontier 0=t7_258jobs := by rfl
theorem t7_258all : t7_258jobs.all (Job.check tree)=true := by
  simp only [t7_258jobs,List.all_append,List.all_nil,t7_258part0,Bool.and_self]
theorem t7_258checked : Checked tree [3,3,3,3,3,3,3] := by
  refine ⟨plan8412,valid8412,t7_258choices,?_⟩
  exact check_of_frontier tree 0 t7_258root t7_258jobs t7_258frontier t7_258all
theorem t7_259choices : plan8414.choices=[3,3,3,3,3,3,6].map (options 7 1) := by rfl


theorem t7_259part0 : t7_259jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_259frontier : t7_259root.frontier 0=t7_259jobs := by rfl
theorem t7_259all : t7_259jobs.all (Job.check tree)=true := by
  simp only [t7_259jobs,List.all_append,List.all_nil,t7_259part0,Bool.and_self]
theorem t7_259checked : Checked tree [3,3,3,3,3,3,6] := by
  refine ⟨plan8414,valid8414,t7_259choices,?_⟩
  exact check_of_frontier tree 0 t7_259root t7_259jobs t7_259frontier t7_259all
theorem t7_260choices : plan8415.choices=[3,3,3,3,3,3,7].map (options 7 1) := by rfl


theorem t7_260part0 : t7_260jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_260frontier : t7_260root.frontier 0=t7_260jobs := by rfl
theorem t7_260all : t7_260jobs.all (Job.check tree)=true := by
  simp only [t7_260jobs,List.all_append,List.all_nil,t7_260part0,Bool.and_self]
theorem t7_260checked : Checked tree [3,3,3,3,3,3,7] := by
  refine ⟨plan8415,valid8415,t7_260choices,?_⟩
  exact check_of_frontier tree 0 t7_260root t7_260jobs t7_260frontier t7_260all
theorem t7_261choices : plan8416.choices=[3,3,3,3,3,3,10].map (options 7 1) := by rfl


theorem t7_261part0 : t7_261jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_261frontier : t7_261root.frontier 0=t7_261jobs := by rfl
theorem t7_261all : t7_261jobs.all (Job.check tree)=true := by
  simp only [t7_261jobs,List.all_append,List.all_nil,t7_261part0,Bool.and_self]
theorem t7_261checked : Checked tree [3,3,3,3,3,3,10] := by
  refine ⟨plan8416,valid8416,t7_261choices,?_⟩
  exact check_of_frontier tree 0 t7_261root t7_261jobs t7_261frontier t7_261all
theorem t7_262choices : plan8422.choices=[3,3,3,3,3,6,6].map (options 7 2) := by rfl


theorem t7_262part0 : t7_262jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_262frontier : t7_262root.frontier 0=t7_262jobs := by rfl
theorem t7_262all : t7_262jobs.all (Job.check tree)=true := by
  simp only [t7_262jobs,List.all_append,List.all_nil,t7_262part0,Bool.and_self]
theorem t7_262checked : Checked tree [3,3,3,3,3,6,6] := by
  refine ⟨plan8422,valid8422,t7_262choices,?_⟩
  exact check_of_frontier tree 0 t7_262root t7_262jobs t7_262frontier t7_262all
theorem t7_263choices : plan8423.choices=[3,3,3,3,3,6,7].map (options 7 2) := by rfl


theorem t7_263part0 : t7_263jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_263frontier : t7_263root.frontier 0=t7_263jobs := by rfl
theorem t7_263all : t7_263jobs.all (Job.check tree)=true := by
  simp only [t7_263jobs,List.all_append,List.all_nil,t7_263part0,Bool.and_self]
theorem t7_263checked : Checked tree [3,3,3,3,3,6,7] := by
  refine ⟨plan8423,valid8423,t7_263choices,?_⟩
  exact check_of_frontier tree 0 t7_263root t7_263jobs t7_263frontier t7_263all
theorem t7_264choices : plan8424.choices=[3,3,3,3,3,6,10].map (options 7 2) := by rfl


theorem t7_264part0 : t7_264jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_264frontier : t7_264root.frontier 0=t7_264jobs := by rfl
theorem t7_264all : t7_264jobs.all (Job.check tree)=true := by
  simp only [t7_264jobs,List.all_append,List.all_nil,t7_264part0,Bool.and_self]
theorem t7_264checked : Checked tree [3,3,3,3,3,6,10] := by
  refine ⟨plan8424,valid8424,t7_264choices,?_⟩
  exact check_of_frontier tree 0 t7_264root t7_264jobs t7_264frontier t7_264all
theorem t7_265choices : plan8425.choices=[3,3,3,3,3,7,7].map (options 7 2) := by rfl


theorem t7_265part0 : t7_265jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_265frontier : t7_265root.frontier 0=t7_265jobs := by rfl
theorem t7_265all : t7_265jobs.all (Job.check tree)=true := by
  simp only [t7_265jobs,List.all_append,List.all_nil,t7_265part0,Bool.and_self]
theorem t7_265checked : Checked tree [3,3,3,3,3,7,7] := by
  refine ⟨plan8425,valid8425,t7_265choices,?_⟩
  exact check_of_frontier tree 0 t7_265root t7_265jobs t7_265frontier t7_265all
theorem t7_266choices : plan8426.choices=[3,3,3,3,3,10,7].map (options 7 2) := by rfl


theorem t7_266part0 : t7_266jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_266frontier : t7_266root.frontier 0=t7_266jobs := by rfl
theorem t7_266all : t7_266jobs.all (Job.check tree)=true := by
  simp only [t7_266jobs,List.all_append,List.all_nil,t7_266part0,Bool.and_self]
theorem t7_266checked : Checked tree [3,3,3,3,3,10,7] := by
  refine ⟨plan8426,valid8426,t7_266choices,?_⟩
  exact check_of_frontier tree 0 t7_266root t7_266jobs t7_266frontier t7_266all
theorem t7_267choices : plan8427.choices=[3,3,3,3,3,10,10].map (options 7 2) := by rfl


theorem t7_267part0 : t7_267jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_267frontier : t7_267root.frontier 0=t7_267jobs := by rfl
theorem t7_267all : t7_267jobs.all (Job.check tree)=true := by
  simp only [t7_267jobs,List.all_append,List.all_nil,t7_267part0,Bool.and_self]
theorem t7_267checked : Checked tree [3,3,3,3,3,10,10] := by
  refine ⟨plan8427,valid8427,t7_267choices,?_⟩
  exact check_of_frontier tree 0 t7_267root t7_267jobs t7_267frontier t7_267all
theorem t7_268choices : plan8447.choices=[3,3,3,3,6,6,6].map (options 7 3) := by rfl


theorem t7_268part0 : t7_268jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_268frontier : t7_268root.frontier 0=t7_268jobs := by rfl
theorem t7_268all : t7_268jobs.all (Job.check tree)=true := by
  simp only [t7_268jobs,List.all_append,List.all_nil,t7_268part0,Bool.and_self]
theorem t7_268checked : Checked tree [3,3,3,3,6,6,6] := by
  refine ⟨plan8447,valid8447,t7_268choices,?_⟩
  exact check_of_frontier tree 0 t7_268root t7_268jobs t7_268frontier t7_268all
theorem t7_269choices : plan8448.choices=[3,3,3,3,6,6,7].map (options 7 3) := by rfl


theorem t7_269part0 : t7_269jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_269part1 : t7_269jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_269frontier : t7_269root.frontier 1=t7_269jobs := by rfl
theorem t7_269all : t7_269jobs.all (Job.check tree)=true := by
  simp only [t7_269jobs,List.all_append,List.all_nil,t7_269part0,t7_269part1,Bool.and_self]
theorem t7_269checked : Checked tree [3,3,3,3,6,6,7] := by
  refine ⟨plan8448,valid8448,t7_269choices,?_⟩
  exact check_of_frontier tree 1 t7_269root t7_269jobs t7_269frontier t7_269all
theorem t7_270choices : plan8449.choices=[3,3,3,3,6,6,10].map (options 7 3) := by rfl


theorem t7_270part0 : t7_270jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_270frontier : t7_270root.frontier 0=t7_270jobs := by rfl
theorem t7_270all : t7_270jobs.all (Job.check tree)=true := by
  simp only [t7_270jobs,List.all_append,List.all_nil,t7_270part0,Bool.and_self]
theorem t7_270checked : Checked tree [3,3,3,3,6,6,10] := by
  refine ⟨plan8449,valid8449,t7_270choices,?_⟩
  exact check_of_frontier tree 0 t7_270root t7_270jobs t7_270frontier t7_270all
theorem t7_271choices : plan8450.choices=[3,3,3,3,6,7,7].map (options 7 3) := by rfl


theorem t7_271part0 : t7_271jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_271part1 : t7_271jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_271part2 : t7_271jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_271part3 : t7_271jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_271part4 : t7_271jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_271part5 : t7_271jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_271frontier : t7_271root.frontier 1=t7_271jobs := by rfl
theorem t7_271all : t7_271jobs.all (Job.check tree)=true := by
  simp only [t7_271jobs,List.all_append,List.all_nil,t7_271part0,t7_271part1,t7_271part2,t7_271part3,t7_271part4,t7_271part5,Bool.and_self]
theorem t7_271checked : Checked tree [3,3,3,3,6,7,7] := by
  refine ⟨plan8450,valid8450,t7_271choices,?_⟩
  exact check_of_frontier tree 1 t7_271root t7_271jobs t7_271frontier t7_271all
theorem t7_272choices : plan8451.choices=[3,3,3,3,6,10,7].map (options 7 3) := by rfl


theorem t7_272part0 : t7_272jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_272part1 : t7_272jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_272part2 : t7_272jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_272part3 : t7_272jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_272frontier : t7_272root.frontier 1=t7_272jobs := by rfl
theorem t7_272all : t7_272jobs.all (Job.check tree)=true := by
  simp only [t7_272jobs,List.all_append,List.all_nil,t7_272part0,t7_272part1,t7_272part2,t7_272part3,Bool.and_self]
theorem t7_272checked : Checked tree [3,3,3,3,6,10,7] := by
  refine ⟨plan8451,valid8451,t7_272choices,?_⟩
  exact check_of_frontier tree 1 t7_272root t7_272jobs t7_272frontier t7_272all
theorem t7_273choices : plan8452.choices=[3,3,3,3,6,10,10].map (options 7 3) := by rfl


theorem t7_273part0 : t7_273jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_273frontier : t7_273root.frontier 0=t7_273jobs := by rfl
theorem t7_273all : t7_273jobs.all (Job.check tree)=true := by
  simp only [t7_273jobs,List.all_append,List.all_nil,t7_273part0,Bool.and_self]
theorem t7_273checked : Checked tree [3,3,3,3,6,10,10] := by
  refine ⟨plan8452,valid8452,t7_273choices,?_⟩
  exact check_of_frontier tree 0 t7_273root t7_273jobs t7_273frontier t7_273all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks169 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_260checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_261checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_262checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_263checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_264checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_265checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_266checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_267checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_268checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_249checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_269checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_270checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_271checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_272checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_273checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_250checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_251checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_252checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_253checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_254checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_255checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_256checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_257checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_258checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_248checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_259checked⟩
