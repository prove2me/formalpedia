-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks097
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:34:57.658008+00:00
-- url     : https://prove2.me/submissions/a3df0437-2296-4178-81b4-37a533d57237

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks097
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks097
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
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











































































































































































theorem valid566 : plan566.Valid := valid_step _ _ _ valid131 (by decide +kernel)









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



















































theorem valid1562 : plan1562.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1563 : plan1563.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1564 : plan1564.Valid := valid_step _ _ _ valid573 (by decide +kernel)























theorem valid1576 : plan1576.Valid := valid_step _ _ _ valid566 (by decide +kernel)

































theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)



theorem valid1601 : plan1601.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1602 : plan1602.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1603 : plan1603.Valid := valid_step _ _ _ valid579 (by decide +kernel)

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















































































































theorem valid3416 : plan3416.Valid := valid_step _ _ _ valid1562 (by decide +kernel)

theorem valid3417 : plan3417.Valid := valid_step _ _ _ valid1563 (by decide +kernel)

theorem valid3418 : plan3418.Valid := valid_step _ _ _ valid1564 (by decide +kernel)















theorem valid3426 : plan3426.Valid := valid_step _ _ _ valid1576 (by decide +kernel)




























































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

























































theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)















theorem valid3493 : plan3493.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3494 : plan3494.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3495 : plan3495.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3496 : plan3496.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3497 : plan3497.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3498 : plan3498.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3499 : plan3499.Valid := valid_step _ _ _ valid1599 (by decide +kernel)



theorem valid3501 : plan3501.Valid := valid_step _ _ _ valid1601 (by decide +kernel)

theorem valid3502 : plan3502.Valid := valid_step _ _ _ valid1602 (by decide +kernel)

theorem valid3503 : plan3503.Valid := valid_step _ _ _ valid1603 (by decide +kernel)

theorem valid3504 : plan3504.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3505 : plan3505.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3506 : plan3506.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3507 : plan3507.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3508 : plan3508.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3509 : plan3509.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3510 : plan3510.Valid := valid_step _ _ _ valid1606 (by decide +kernel)




















































































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















































































































































theorem valid5736 : plan5736.Valid := valid_step _ _ _ valid3416 (by decide +kernel)

theorem valid5737 : plan5737.Valid := valid_step _ _ _ valid3417 (by decide +kernel)

theorem valid5738 : plan5738.Valid := valid_step _ _ _ valid3418 (by decide +kernel)

theorem valid5739 : plan5739.Valid := valid_step _ _ _ valid3426 (by decide +kernel)










































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



theorem valid5954 : plan5954.Valid := valid_step _ _ _ valid3493 (by decide +kernel)

theorem valid5955 : plan5955.Valid := valid_step _ _ _ valid3494 (by decide +kernel)

theorem valid5956 : plan5956.Valid := valid_step _ _ _ valid3495 (by decide +kernel)

theorem valid5957 : plan5957.Valid := valid_step _ _ _ valid3496 (by decide +kernel)

theorem valid5958 : plan5958.Valid := valid_step _ _ _ valid3497 (by decide +kernel)

theorem valid5959 : plan5959.Valid := valid_step _ _ _ valid3498 (by decide +kernel)

theorem valid5960 : plan5960.Valid := valid_step _ _ _ valid3499 (by decide +kernel)



theorem valid5962 : plan5962.Valid := valid_step _ _ _ valid3501 (by decide +kernel)

theorem valid5963 : plan5963.Valid := valid_step _ _ _ valid3502 (by decide +kernel)

theorem valid5964 : plan5964.Valid := valid_step _ _ _ valid3503 (by decide +kernel)

theorem valid5965 : plan5965.Valid := valid_step _ _ _ valid3504 (by decide +kernel)

theorem valid5966 : plan5966.Valid := valid_step _ _ _ valid3505 (by decide +kernel)

theorem valid5967 : plan5967.Valid := valid_step _ _ _ valid3506 (by decide +kernel)

theorem valid5968 : plan5968.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5969 : plan5969.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5970 : plan5970.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5971 : plan5971.Valid := valid_step _ _ _ valid3510 (by decide +kernel)

theorem valid5972 : plan5972.Valid := valid_step _ _ _ valid3485 (by decide +kernel)
























































































































































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





























































































































































































theorem valid7391 : plan7391.Valid := valid_step _ _ _ valid5954 (by decide +kernel)

theorem valid7392 : plan7392.Valid := valid_step _ _ _ valid5955 (by decide +kernel)
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













































































































theorem valid6967 : plan6967.Valid := valid_step _ _ _ valid5736 (by decide +kernel)

theorem valid6968 : plan6968.Valid := valid_step _ _ _ valid5737 (by decide +kernel)

theorem valid6969 : plan6969.Valid := valid_step _ _ _ valid5738 (by decide +kernel)

theorem valid6970 : plan6970.Valid := valid_step _ _ _ valid5739 (by decide +kernel)












































































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

theorem valid7393 : plan7393.Valid := valid_step _ _ _ valid5956 (by decide +kernel)

theorem valid7394 : plan7394.Valid := valid_step _ _ _ valid5957 (by decide +kernel)

theorem valid7395 : plan7395.Valid := valid_step _ _ _ valid5958 (by decide +kernel)

theorem valid7396 : plan7396.Valid := valid_step _ _ _ valid5959 (by decide +kernel)

theorem valid7397 : plan7397.Valid := valid_step _ _ _ valid5960 (by decide +kernel)

theorem valid7398 : plan7398.Valid := valid_step _ _ _ valid5962 (by decide +kernel)

theorem valid7399 : plan7399.Valid := valid_step _ _ _ valid5963 (by decide +kernel)

theorem valid7400 : plan7400.Valid := valid_step _ _ _ valid5964 (by decide +kernel)

theorem valid7401 : plan7401.Valid := valid_step _ _ _ valid5965 (by decide +kernel)

theorem valid7402 : plan7402.Valid := valid_step _ _ _ valid5966 (by decide +kernel)

theorem valid7403 : plan7403.Valid := valid_step _ _ _ valid5967 (by decide +kernel)

theorem valid7404 : plan7404.Valid := valid_step _ _ _ valid5968 (by decide +kernel)

theorem valid7405 : plan7405.Valid := valid_step _ _ _ valid5969 (by decide +kernel)

theorem valid7406 : plan7406.Valid := valid_step _ _ _ valid5970 (by decide +kernel)

theorem valid7407 : plan7407.Valid := valid_step _ _ _ valid5971 (by decide +kernel)

theorem valid7408 : plan7408.Valid := valid_step _ _ _ valid5972 (by decide +kernel)
































































































































































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
theorem t6_807choices : plan6967.choices=[2,9,9,3,7,7].map (options 6 4) := by rfl


theorem t6_807part0 : t6_807jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_807part1 : t6_807jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_807part2 : t6_807jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_807frontier : t6_807root.frontier 1=t6_807jobs := by rfl
theorem t6_807all : t6_807jobs.all (Job.check tree)=true := by
  simp only [t6_807jobs,List.all_append,List.all_nil,t6_807part0,t6_807part1,t6_807part2,Bool.and_self]
theorem t6_807checked : Checked tree [2,9,9,3,7,7] := by
  refine ⟨plan6967,valid6967,t6_807choices,?_⟩
  exact check_of_frontier tree 1 t6_807root t6_807jobs t6_807frontier t6_807all
theorem t6_808choices : plan6968.choices=[2,9,9,3,10,7].map (options 6 4) := by rfl


theorem t6_808part0 : t6_808jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_808part1 : t6_808jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_808part2 : t6_808jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_808frontier : t6_808root.frontier 1=t6_808jobs := by rfl
theorem t6_808all : t6_808jobs.all (Job.check tree)=true := by
  simp only [t6_808jobs,List.all_append,List.all_nil,t6_808part0,t6_808part1,t6_808part2,Bool.and_self]
theorem t6_808checked : Checked tree [2,9,9,3,10,7] := by
  refine ⟨plan6968,valid6968,t6_808choices,?_⟩
  exact check_of_frontier tree 1 t6_808root t6_808jobs t6_808frontier t6_808all
theorem t6_809choices : plan6969.choices=[2,9,9,3,10,10].map (options 6 4) := by rfl


theorem t6_809part0 : t6_809jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_809frontier : t6_809root.frontier 0=t6_809jobs := by rfl
theorem t6_809all : t6_809jobs.all (Job.check tree)=true := by
  simp only [t6_809jobs,List.all_append,List.all_nil,t6_809part0,Bool.and_self]
theorem t6_809checked : Checked tree [2,9,9,3,10,10] := by
  refine ⟨plan6969,valid6969,t6_809choices,?_⟩
  exact check_of_frontier tree 0 t6_809root t6_809jobs t6_809frontier t6_809all
theorem t6_810choices : plan7391.choices=[2,9,9,6,6,6].map (options 6 5) := by rfl


theorem t6_810part0 : t6_810jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_810frontier : t6_810root.frontier 0=t6_810jobs := by rfl
theorem t6_810all : t6_810jobs.all (Job.check tree)=true := by
  simp only [t6_810jobs,List.all_append,List.all_nil,t6_810part0,Bool.and_self]
theorem t6_810checked : Checked tree [2,9,9,6,6,6] := by
  refine ⟨plan7391,valid7391,t6_810choices,?_⟩
  exact check_of_frontier tree 0 t6_810root t6_810jobs t6_810frontier t6_810all
theorem t6_811choices : plan7392.choices=[2,9,9,6,6,7].map (options 6 5) := by rfl


theorem t6_811part0 : t6_811jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_811frontier : t6_811root.frontier 0=t6_811jobs := by rfl
theorem t6_811all : t6_811jobs.all (Job.check tree)=true := by
  simp only [t6_811jobs,List.all_append,List.all_nil,t6_811part0,Bool.and_self]
theorem t6_811checked : Checked tree [2,9,9,6,6,7] := by
  refine ⟨plan7392,valid7392,t6_811choices,?_⟩
  exact check_of_frontier tree 0 t6_811root t6_811jobs t6_811frontier t6_811all
theorem t6_812choices : plan7393.choices=[2,9,9,6,6,10].map (options 6 5) := by rfl


theorem t6_812part0 : t6_812jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_812frontier : t6_812root.frontier 0=t6_812jobs := by rfl
theorem t6_812all : t6_812jobs.all (Job.check tree)=true := by
  simp only [t6_812jobs,List.all_append,List.all_nil,t6_812part0,Bool.and_self]
theorem t6_812checked : Checked tree [2,9,9,6,6,10] := by
  refine ⟨plan7393,valid7393,t6_812choices,?_⟩
  exact check_of_frontier tree 0 t6_812root t6_812jobs t6_812frontier t6_812all
theorem t6_813choices : plan7394.choices=[2,9,9,6,7,7].map (options 6 5) := by rfl


theorem t6_813part0 : t6_813jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_813frontier : t6_813root.frontier 0=t6_813jobs := by rfl
theorem t6_813all : t6_813jobs.all (Job.check tree)=true := by
  simp only [t6_813jobs,List.all_append,List.all_nil,t6_813part0,Bool.and_self]
theorem t6_813checked : Checked tree [2,9,9,6,7,7] := by
  refine ⟨plan7394,valid7394,t6_813choices,?_⟩
  exact check_of_frontier tree 0 t6_813root t6_813jobs t6_813frontier t6_813all
theorem t6_814choices : plan7395.choices=[2,9,9,6,10,7].map (options 6 5) := by rfl


theorem t6_814part0 : t6_814jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_814frontier : t6_814root.frontier 0=t6_814jobs := by rfl
theorem t6_814all : t6_814jobs.all (Job.check tree)=true := by
  simp only [t6_814jobs,List.all_append,List.all_nil,t6_814part0,Bool.and_self]
theorem t6_814checked : Checked tree [2,9,9,6,10,7] := by
  refine ⟨plan7395,valid7395,t6_814choices,?_⟩
  exact check_of_frontier tree 0 t6_814root t6_814jobs t6_814frontier t6_814all
theorem t6_815choices : plan7396.choices=[2,9,9,6,10,10].map (options 6 5) := by rfl


theorem t6_815part0 : t6_815jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_815frontier : t6_815root.frontier 0=t6_815jobs := by rfl
theorem t6_815all : t6_815jobs.all (Job.check tree)=true := by
  simp only [t6_815jobs,List.all_append,List.all_nil,t6_815part0,Bool.and_self]
theorem t6_815checked : Checked tree [2,9,9,6,10,10] := by
  refine ⟨plan7396,valid7396,t6_815choices,?_⟩
  exact check_of_frontier tree 0 t6_815root t6_815jobs t6_815frontier t6_815all
theorem t6_816choices : plan7397.choices=[2,9,9,7,7,7].map (options 6 5) := by rfl


theorem t6_816part0 : t6_816jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_816frontier : t6_816root.frontier 0=t6_816jobs := by rfl
theorem t6_816all : t6_816jobs.all (Job.check tree)=true := by
  simp only [t6_816jobs,List.all_append,List.all_nil,t6_816part0,Bool.and_self]
theorem t6_816checked : Checked tree [2,9,9,7,7,7] := by
  refine ⟨plan7397,valid7397,t6_816choices,?_⟩
  exact check_of_frontier tree 0 t6_816root t6_816jobs t6_816frontier t6_816all
theorem t6_817choices : plan6970.choices=[2,9,9,9,3,7].map (options 6 4) := by rfl


theorem t6_817part0 : t6_817jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_817frontier : t6_817root.frontier 0=t6_817jobs := by rfl
theorem t6_817all : t6_817jobs.all (Job.check tree)=true := by
  simp only [t6_817jobs,List.all_append,List.all_nil,t6_817part0,Bool.and_self]
theorem t6_817checked : Checked tree [2,9,9,9,3,7] := by
  refine ⟨plan6970,valid6970,t6_817choices,?_⟩
  exact check_of_frontier tree 0 t6_817root t6_817jobs t6_817frontier t6_817all
theorem t6_818choices : plan7398.choices=[2,9,9,9,6,7].map (options 6 5) := by rfl


theorem t6_818part0 : t6_818jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_818frontier : t6_818root.frontier 0=t6_818jobs := by rfl
theorem t6_818all : t6_818jobs.all (Job.check tree)=true := by
  simp only [t6_818jobs,List.all_append,List.all_nil,t6_818part0,Bool.and_self]
theorem t6_818checked : Checked tree [2,9,9,9,6,7] := by
  refine ⟨plan7398,valid7398,t6_818choices,?_⟩
  exact check_of_frontier tree 0 t6_818root t6_818jobs t6_818frontier t6_818all
theorem t6_819choices : plan7399.choices=[2,9,9,9,7,7].map (options 6 5) := by rfl


theorem t6_819part0 : t6_819jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_819frontier : t6_819root.frontier 0=t6_819jobs := by rfl
theorem t6_819all : t6_819jobs.all (Job.check tree)=true := by
  simp only [t6_819jobs,List.all_append,List.all_nil,t6_819part0,Bool.and_self]
theorem t6_819checked : Checked tree [2,9,9,9,7,7] := by
  refine ⟨plan7399,valid7399,t6_819choices,?_⟩
  exact check_of_frontier tree 0 t6_819root t6_819jobs t6_819frontier t6_819all
theorem t6_820choices : plan7400.choices=[2,9,9,9,10,7].map (options 6 5) := by rfl


theorem t6_820part0 : t6_820jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_820frontier : t6_820root.frontier 0=t6_820jobs := by rfl
theorem t6_820all : t6_820jobs.all (Job.check tree)=true := by
  simp only [t6_820jobs,List.all_append,List.all_nil,t6_820part0,Bool.and_self]
theorem t6_820checked : Checked tree [2,9,9,9,10,7] := by
  refine ⟨plan7400,valid7400,t6_820choices,?_⟩
  exact check_of_frontier tree 0 t6_820root t6_820jobs t6_820frontier t6_820all
theorem t6_821choices : plan7401.choices=[2,9,9,10,7,7].map (options 6 5) := by rfl


theorem t6_821part0 : t6_821jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_821frontier : t6_821root.frontier 0=t6_821jobs := by rfl
theorem t6_821all : t6_821jobs.all (Job.check tree)=true := by
  simp only [t6_821jobs,List.all_append,List.all_nil,t6_821part0,Bool.and_self]
theorem t6_821checked : Checked tree [2,9,9,10,7,7] := by
  refine ⟨plan7401,valid7401,t6_821choices,?_⟩
  exact check_of_frontier tree 0 t6_821root t6_821jobs t6_821frontier t6_821all
theorem t6_822choices : plan7402.choices=[2,9,9,10,10,7].map (options 6 5) := by rfl


theorem t6_822part0 : t6_822jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_822frontier : t6_822root.frontier 0=t6_822jobs := by rfl
theorem t6_822all : t6_822jobs.all (Job.check tree)=true := by
  simp only [t6_822jobs,List.all_append,List.all_nil,t6_822part0,Bool.and_self]
theorem t6_822checked : Checked tree [2,9,9,10,10,7] := by
  refine ⟨plan7402,valid7402,t6_822choices,?_⟩
  exact check_of_frontier tree 0 t6_822root t6_822jobs t6_822frontier t6_822all
theorem t6_823choices : plan7403.choices=[2,9,9,10,10,10].map (options 6 5) := by rfl


theorem t6_823part0 : t6_823jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_823frontier : t6_823root.frontier 0=t6_823jobs := by rfl
theorem t6_823all : t6_823jobs.all (Job.check tree)=true := by
  simp only [t6_823jobs,List.all_append,List.all_nil,t6_823part0,Bool.and_self]
theorem t6_823checked : Checked tree [2,9,9,10,10,10] := by
  refine ⟨plan7403,valid7403,t6_823choices,?_⟩
  exact check_of_frontier tree 0 t6_823root t6_823jobs t6_823frontier t6_823all
theorem t6_824choices : plan7404.choices=[2,9,10,7,7,7].map (options 6 5) := by rfl


theorem t6_824part0 : t6_824jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_824part1 : t6_824jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_824part2 : t6_824jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_824frontier : t6_824root.frontier 2=t6_824jobs := by rfl
theorem t6_824all : t6_824jobs.all (Job.check tree)=true := by
  simp only [t6_824jobs,List.all_append,List.all_nil,t6_824part0,t6_824part1,t6_824part2,Bool.and_self]
theorem t6_824checked : Checked tree [2,9,10,7,7,7] := by
  refine ⟨plan7404,valid7404,t6_824choices,?_⟩
  exact check_of_frontier tree 2 t6_824root t6_824jobs t6_824frontier t6_824all
theorem t6_825choices : plan7405.choices=[2,9,10,10,7,7].map (options 6 5) := by rfl


theorem t6_825part0 : t6_825jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_825part1 : t6_825jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_825frontier : t6_825root.frontier 2=t6_825jobs := by rfl
theorem t6_825all : t6_825jobs.all (Job.check tree)=true := by
  simp only [t6_825jobs,List.all_append,List.all_nil,t6_825part0,t6_825part1,Bool.and_self]
theorem t6_825checked : Checked tree [2,9,10,10,7,7] := by
  refine ⟨plan7405,valid7405,t6_825choices,?_⟩
  exact check_of_frontier tree 2 t6_825root t6_825jobs t6_825frontier t6_825all
theorem t6_826choices : plan7406.choices=[2,9,10,10,10,7].map (options 6 5) := by rfl


theorem t6_826part0 : t6_826jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_826frontier : t6_826root.frontier 0=t6_826jobs := by rfl
theorem t6_826all : t6_826jobs.all (Job.check tree)=true := by
  simp only [t6_826jobs,List.all_append,List.all_nil,t6_826part0,Bool.and_self]
theorem t6_826checked : Checked tree [2,9,10,10,10,7] := by
  refine ⟨plan7406,valid7406,t6_826choices,?_⟩
  exact check_of_frontier tree 0 t6_826root t6_826jobs t6_826frontier t6_826all
theorem t6_827choices : plan7407.choices=[2,9,10,10,10,10].map (options 6 5) := by rfl


theorem t6_827part0 : t6_827jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_827frontier : t6_827root.frontier 0=t6_827jobs := by rfl
theorem t6_827all : t6_827jobs.all (Job.check tree)=true := by
  simp only [t6_827jobs,List.all_append,List.all_nil,t6_827part0,Bool.and_self]
theorem t6_827checked : Checked tree [2,9,10,10,10,10] := by
  refine ⟨plan7407,valid7407,t6_827choices,?_⟩
  exact check_of_frontier tree 0 t6_827root t6_827jobs t6_827frontier t6_827all
theorem t6_828choices : plan7408.choices=[2,10,7,7,7,7].map (options 6 5) := by rfl


theorem t6_828part0 : t6_828jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_828part1 : t6_828jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_828part2 : t6_828jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_828frontier : t6_828root.frontier 2=t6_828jobs := by rfl
theorem t6_828all : t6_828jobs.all (Job.check tree)=true := by
  simp only [t6_828jobs,List.all_append,List.all_nil,t6_828part0,t6_828part1,t6_828part2,Bool.and_self]
theorem t6_828checked : Checked tree [2,10,7,7,7,7] := by
  refine ⟨plan7408,valid7408,t6_828choices,?_⟩
  exact check_of_frontier tree 2 t6_828root t6_828jobs t6_828frontier t6_828all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks097 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_818checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_819checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_820checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_821checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_822checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_823checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_807checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_824checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_825checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_826checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_827checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_828checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_808checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_809checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_810checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_811checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_812checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_813checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_814checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_815checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_816checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_817checked⟩
