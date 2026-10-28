-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks087
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:31:34.027359+00:00
-- url     : https://prove2.me/submissions/74826819-6a27-4700-b0ad-63410bedb569

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
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



















































theorem valid122 : plan122.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)





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

































































































































theorem valid545 : plan545.Valid := valid_step _ _ _ valid122 (by decide +kernel)





















theorem valid556 : plan556.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid557 : plan557.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid558 : plan558.Valid := valid_step _ _ _ valid129 (by decide +kernel)



















theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)














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





















































































































































theorem valid1515 : plan1515.Valid := valid_step _ _ _ valid545 (by decide +kernel)



























theorem valid1529 : plan1529.Valid := valid_step _ _ _ valid556 (by decide +kernel)

theorem valid1530 : plan1530.Valid := valid_step _ _ _ valid557 (by decide +kernel)

theorem valid1531 : plan1531.Valid := valid_step _ _ _ valid558 (by decide +kernel)










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













































theorem valid1559 : plan1559.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)











































































theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)









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



























theorem valid3278 : plan3278.Valid := valid_step _ _ _ valid1515 (by decide +kernel)

















































































































theorem valid3335 : plan3335.Valid := valid_step _ _ _ valid1529 (by decide +kernel)

theorem valid3336 : plan3336.Valid := valid_step _ _ _ valid1530 (by decide +kernel)

theorem valid3337 : plan3337.Valid := valid_step _ _ _ valid1531 (by decide +kernel)














































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































































theorem valid5408 : plan5408.Valid := valid_step _ _ _ valid3278 (by decide +kernel)
































































































































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









































































































theorem valid3413 : plan3413.Valid := valid_step _ _ _ valid1559 (by decide +kernel)

theorem valid3414 : plan3414.Valid := valid_step _ _ _ valid1560 (by decide +kernel)




















































































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





















































































theorem valid5515 : plan5515.Valid := valid_step _ _ _ valid3335 (by decide +kernel)

theorem valid5516 : plan5516.Valid := valid_step _ _ _ valid3336 (by decide +kernel)

theorem valid5517 : plan5517.Valid := valid_step _ _ _ valid3337 (by decide +kernel)






































































































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















































theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)






































































































































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























































theorem valid5692 : plan5692.Valid := valid_step _ _ _ valid3413 (by decide +kernel)

theorem valid5693 : plan5693.Valid := valid_step _ _ _ valid3414 (by decide +kernel)






































































































































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

























































































































































































theorem valid5853 : plan5853.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5854 : plan5854.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5855 : plan5855.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5856 : plan5856.Valid := valid_step _ _ _ valid3483 (by decide +kernel)
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

theorem valid5857 : plan5857.Valid := valid_step _ _ _ valid3484 (by decide +kernel)

theorem valid5858 : plan5858.Valid := valid_step _ _ _ valid3485 (by decide +kernel)




























































































































































































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























































































































theorem valid6396 : plan6396.Valid := valid_step _ _ _ valid5408 (by decide +kernel)








































































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







































































































































theorem valid6596 : plan6596.Valid := valid_step _ _ _ valid5515 (by decide +kernel)

theorem valid6597 : plan6597.Valid := valid_step _ _ _ valid5516 (by decide +kernel)

theorem valid6598 : plan6598.Valid := valid_step _ _ _ valid5517 (by decide +kernel)




















































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

























































































theorem valid7341 : plan7341.Valid := valid_step _ _ _ valid5853 (by decide +kernel)

theorem valid7342 : plan7342.Valid := valid_step _ _ _ valid5854 (by decide +kernel)

theorem valid7343 : plan7343.Valid := valid_step _ _ _ valid5855 (by decide +kernel)

theorem valid7344 : plan7344.Valid := valid_step _ _ _ valid5856 (by decide +kernel)

theorem valid7345 : plan7345.Valid := valid_step _ _ _ valid5857 (by decide +kernel)

theorem valid7346 : plan7346.Valid := valid_step _ _ _ valid5858 (by decide +kernel)




























































































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





































































theorem valid6947 : plan6947.Valid := valid_step _ _ _ valid5692 (by decide +kernel)

theorem valid6948 : plan6948.Valid := valid_step _ _ _ valid5693 (by decide +kernel)
























































































































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
theorem t6_719choices : plan7341.choices=[2,5,6,6,10,10].map (options 6 5) := by rfl


theorem t6_719part0 : t6_719jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_719frontier : t6_719root.frontier 0=t6_719jobs := by rfl
theorem t6_719all : t6_719jobs.all (Job.check tree)=true := by
  simp only [t6_719jobs,List.all_append,List.all_nil,t6_719part0,Bool.and_self]
theorem t6_719checked : Checked tree [2,5,6,6,10,10] := by
  refine ⟨plan7341,valid7341,t6_719choices,?_⟩
  exact check_of_frontier tree 0 t6_719root t6_719jobs t6_719frontier t6_719all
theorem t6_720choices : plan7342.choices=[2,5,6,7,7,7].map (options 6 5) := by rfl


theorem t6_720part0 : t6_720jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_720part1 : t6_720jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_720part2 : t6_720jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_720frontier : t6_720root.frontier 2=t6_720jobs := by rfl
theorem t6_720all : t6_720jobs.all (Job.check tree)=true := by
  simp only [t6_720jobs,List.all_append,List.all_nil,t6_720part0,t6_720part1,t6_720part2,Bool.and_self]
theorem t6_720checked : Checked tree [2,5,6,7,7,7] := by
  refine ⟨plan7342,valid7342,t6_720choices,?_⟩
  exact check_of_frontier tree 2 t6_720root t6_720jobs t6_720frontier t6_720all
theorem t6_721choices : plan7343.choices=[2,5,6,10,7,7].map (options 6 5) := by rfl


theorem t6_721part0 : t6_721jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_721part1 : t6_721jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_721part2 : t6_721jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_721part3 : t6_721jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_721frontier : t6_721root.frontier 2=t6_721jobs := by rfl
theorem t6_721all : t6_721jobs.all (Job.check tree)=true := by
  simp only [t6_721jobs,List.all_append,List.all_nil,t6_721part0,t6_721part1,t6_721part2,t6_721part3,Bool.and_self]
theorem t6_721checked : Checked tree [2,5,6,10,7,7] := by
  refine ⟨plan7343,valid7343,t6_721choices,?_⟩
  exact check_of_frontier tree 2 t6_721root t6_721jobs t6_721frontier t6_721all
theorem t6_722choices : plan7344.choices=[2,5,6,10,10,7].map (options 6 5) := by rfl


theorem t6_722part0 : t6_722jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_722part1 : t6_722jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_722frontier : t6_722root.frontier 2=t6_722jobs := by rfl
theorem t6_722all : t6_722jobs.all (Job.check tree)=true := by
  simp only [t6_722jobs,List.all_append,List.all_nil,t6_722part0,t6_722part1,Bool.and_self]
theorem t6_722checked : Checked tree [2,5,6,10,10,7] := by
  refine ⟨plan7344,valid7344,t6_722choices,?_⟩
  exact check_of_frontier tree 2 t6_722root t6_722jobs t6_722frontier t6_722all
theorem t6_723choices : plan7345.choices=[2,5,6,10,10,10].map (options 6 5) := by rfl


theorem t6_723part0 : t6_723jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_723frontier : t6_723root.frontier 0=t6_723jobs := by rfl
theorem t6_723all : t6_723jobs.all (Job.check tree)=true := by
  simp only [t6_723jobs,List.all_append,List.all_nil,t6_723part0,Bool.and_self]
theorem t6_723checked : Checked tree [2,5,6,10,10,10] := by
  refine ⟨plan7345,valid7345,t6_723choices,?_⟩
  exact check_of_frontier tree 0 t6_723root t6_723jobs t6_723frontier t6_723all
theorem t6_724choices : plan7346.choices=[2,5,7,7,7,7].map (options 6 5) := by rfl


theorem t6_724part0 : t6_724jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_724part1 : t6_724jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_724frontier : t6_724root.frontier 1=t6_724jobs := by rfl
theorem t6_724all : t6_724jobs.all (Job.check tree)=true := by
  simp only [t6_724jobs,List.all_append,List.all_nil,t6_724part0,t6_724part1,Bool.and_self]
theorem t6_724checked : Checked tree [2,5,7,7,7,7] := by
  refine ⟨plan7346,valid7346,t6_724choices,?_⟩
  exact check_of_frontier tree 1 t6_724root t6_724jobs t6_724frontier t6_724all
theorem t6_725choices : plan6396.choices=[2,5,9,3,3,3].map (options 6 2) := by rfl


theorem t6_725part0 : t6_725jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_725frontier : t6_725root.frontier 0=t6_725jobs := by rfl
theorem t6_725all : t6_725jobs.all (Job.check tree)=true := by
  simp only [t6_725jobs,List.all_append,List.all_nil,t6_725part0,Bool.and_self]
theorem t6_725checked : Checked tree [2,5,9,3,3,3] := by
  refine ⟨plan6396,valid6396,t6_725choices,?_⟩
  exact check_of_frontier tree 0 t6_725root t6_725jobs t6_725frontier t6_725all
theorem t6_726choices : plan6596.choices=[2,5,9,3,3,6].map (options 6 3) := by rfl


theorem t6_726part0 : t6_726jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_726frontier : t6_726root.frontier 0=t6_726jobs := by rfl
theorem t6_726all : t6_726jobs.all (Job.check tree)=true := by
  simp only [t6_726jobs,List.all_append,List.all_nil,t6_726part0,Bool.and_self]
theorem t6_726checked : Checked tree [2,5,9,3,3,6] := by
  refine ⟨plan6596,valid6596,t6_726choices,?_⟩
  exact check_of_frontier tree 0 t6_726root t6_726jobs t6_726frontier t6_726all
theorem t6_727choices : plan6597.choices=[2,5,9,3,3,7].map (options 6 3) := by rfl


theorem t6_727part0 : t6_727jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_727part1 : t6_727jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_727part2 : t6_727jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_727frontier : t6_727root.frontier 1=t6_727jobs := by rfl
theorem t6_727all : t6_727jobs.all (Job.check tree)=true := by
  simp only [t6_727jobs,List.all_append,List.all_nil,t6_727part0,t6_727part1,t6_727part2,Bool.and_self]
theorem t6_727checked : Checked tree [2,5,9,3,3,7] := by
  refine ⟨plan6597,valid6597,t6_727choices,?_⟩
  exact check_of_frontier tree 1 t6_727root t6_727jobs t6_727frontier t6_727all
theorem t6_728choices : plan6598.choices=[2,5,9,3,3,10].map (options 6 3) := by rfl


theorem t6_728part0 : t6_728jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_728frontier : t6_728root.frontier 0=t6_728jobs := by rfl
theorem t6_728all : t6_728jobs.all (Job.check tree)=true := by
  simp only [t6_728jobs,List.all_append,List.all_nil,t6_728part0,Bool.and_self]
theorem t6_728checked : Checked tree [2,5,9,3,3,10] := by
  refine ⟨plan6598,valid6598,t6_728choices,?_⟩
  exact check_of_frontier tree 0 t6_728root t6_728jobs t6_728frontier t6_728all
theorem t6_729choices : plan6947.choices=[2,5,9,3,6,6].map (options 6 4) := by rfl


theorem t6_729part0 : t6_729jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_729frontier : t6_729root.frontier 0=t6_729jobs := by rfl
theorem t6_729all : t6_729jobs.all (Job.check tree)=true := by
  simp only [t6_729jobs,List.all_append,List.all_nil,t6_729part0,Bool.and_self]
theorem t6_729checked : Checked tree [2,5,9,3,6,6] := by
  refine ⟨plan6947,valid6947,t6_729choices,?_⟩
  exact check_of_frontier tree 0 t6_729root t6_729jobs t6_729frontier t6_729all
theorem t6_730choices : plan6948.choices=[2,5,9,3,6,7].map (options 6 4) := by rfl


theorem t6_730part0 : t6_730jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_730part1 : t6_730jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_730part2 : t6_730jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_730part3 : t6_730jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_730frontier : t6_730root.frontier 2=t6_730jobs := by rfl
theorem t6_730all : t6_730jobs.all (Job.check tree)=true := by
  simp only [t6_730jobs,List.all_append,List.all_nil,t6_730part0,t6_730part1,t6_730part2,t6_730part3,Bool.and_self]
theorem t6_730checked : Checked tree [2,5,9,3,6,7] := by
  refine ⟨plan6948,valid6948,t6_730choices,?_⟩
  exact check_of_frontier tree 2 t6_730root t6_730jobs t6_730frontier t6_730all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks087 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_726checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_727checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_728checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_729checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_730checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_720checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_721checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_722checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_723checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_724checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_725checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_719checked⟩
