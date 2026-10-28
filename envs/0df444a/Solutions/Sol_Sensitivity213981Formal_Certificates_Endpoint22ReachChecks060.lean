-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks060
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:13:39.588436+00:00
-- url     : https://prove2.me/submissions/633be281-c05b-4872-a504-54c1eb599889

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans075
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































































theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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





































































































































































theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)

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

theorem valid1537 : plan1537.Valid := valid_step _ _ _ valid564 (by decide +kernel)































































theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)

theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)









theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1582 : plan1582.Valid := valid_step _ _ _ valid573 (by decide +kernel)





















theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)




































































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



























































































theorem valid3310 : plan3310.Valid := valid_step _ _ _ valid1536 (by decide +kernel)

theorem valid3311 : plan3311.Valid := valid_step _ _ _ valid1537 (by decide +kernel)

































































































theorem valid3360 : plan3360.Valid := valid_step _ _ _ valid1569 (by decide +kernel)
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

theorem valid3362 : plan3362.Valid := valid_step _ _ _ valid1571 (by decide +kernel)

theorem valid3363 : plan3363.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3364 : plan3364.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3365 : plan3365.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3366 : plan3366.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3367 : plan3367.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3368 : plan3368.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3369 : plan3369.Valid := valid_step _ _ _ valid1582 (by decide +kernel)














































































































































































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



















































































































theorem valid5530 : plan5530.Valid := valid_step _ _ _ valid3310 (by decide +kernel)

theorem valid5531 : plan5531.Valid := valid_step _ _ _ valid3311 (by decide +kernel)










































































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





































theorem valid3475 : plan3475.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3477 : plan3477.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)
















































































































































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















































































































theorem valid5720 : plan5720.Valid := valid_step _ _ _ valid3360 (by decide +kernel)

theorem valid5721 : plan5721.Valid := valid_step _ _ _ valid3361 (by decide +kernel)

theorem valid5722 : plan5722.Valid := valid_step _ _ _ valid3362 (by decide +kernel)

theorem valid5723 : plan5723.Valid := valid_step _ _ _ valid3363 (by decide +kernel)

theorem valid5724 : plan5724.Valid := valid_step _ _ _ valid3364 (by decide +kernel)

theorem valid5725 : plan5725.Valid := valid_step _ _ _ valid3365 (by decide +kernel)

theorem valid5726 : plan5726.Valid := valid_step _ _ _ valid3366 (by decide +kernel)

theorem valid5727 : plan5727.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5728 : plan5728.Valid := valid_step _ _ _ valid3368 (by decide +kernel)

theorem valid5729 : plan5729.Valid := valid_step _ _ _ valid3369 (by decide +kernel)






























































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

































































































































































theorem valid5937 : plan5937.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5938 : plan5938.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5939 : plan5939.Valid := valid_step _ _ _ valid3477 (by decide +kernel)

theorem valid5940 : plan5940.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5941 : plan5941.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5942 : plan5942.Valid := valid_step _ _ _ valid3480 (by decide +kernel)




















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

























































































































































































theorem valid7293 : plan7293.Valid := valid_step _ _ _ valid5937 (by decide +kernel)

theorem valid7294 : plan7294.Valid := valid_step _ _ _ valid5938 (by decide +kernel)

theorem valid7295 : plan7295.Valid := valid_step _ _ _ valid5939 (by decide +kernel)

theorem valid7296 : plan7296.Valid := valid_step _ _ _ valid5940 (by decide +kernel)
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

















































































theorem valid6857 : plan6857.Valid := valid_step _ _ _ valid5720 (by decide +kernel)

theorem valid6858 : plan6858.Valid := valid_step _ _ _ valid5721 (by decide +kernel)

theorem valid6859 : plan6859.Valid := valid_step _ _ _ valid5722 (by decide +kernel)

theorem valid6860 : plan6860.Valid := valid_step _ _ _ valid5723 (by decide +kernel)

theorem valid6861 : plan6861.Valid := valid_step _ _ _ valid5724 (by decide +kernel)

theorem valid6862 : plan6862.Valid := valid_step _ _ _ valid5725 (by decide +kernel)

theorem valid6863 : plan6863.Valid := valid_step _ _ _ valid5726 (by decide +kernel)

theorem valid6864 : plan6864.Valid := valid_step _ _ _ valid5727 (by decide +kernel)

theorem valid6865 : plan6865.Valid := valid_step _ _ _ valid5728 (by decide +kernel)

theorem valid6866 : plan6866.Valid := valid_step _ _ _ valid5729 (by decide +kernel)




























































































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









theorem valid6533 : plan6533.Valid := valid_step _ _ _ valid5530 (by decide +kernel)

theorem valid6534 : plan6534.Valid := valid_step _ _ _ valid5531 (by decide +kernel)




















































































































































































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

theorem valid7297 : plan7297.Valid := valid_step _ _ _ valid5941 (by decide +kernel)

theorem valid7298 : plan7298.Valid := valid_step _ _ _ valid5942 (by decide +kernel)




























































































































































































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
theorem t6_469choices : plan6533.choices=[1,9,3,3,10,7].map (options 6 3) := by rfl


theorem t6_469part0 : t6_469jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_469part1 : t6_469jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_469frontier : t6_469root.frontier 1=t6_469jobs := by rfl
theorem t6_469all : t6_469jobs.all (Job.check tree)=true := by
  simp only [t6_469jobs,List.all_append,List.all_nil,t6_469part0,t6_469part1,Bool.and_self]
theorem t6_469checked : Checked tree [1,9,3,3,10,7] := by
  refine ⟨plan6533,valid6533,t6_469choices,?_⟩
  exact check_of_frontier tree 1 t6_469root t6_469jobs t6_469frontier t6_469all
theorem t6_470choices : plan6534.choices=[1,9,3,3,10,10].map (options 6 3) := by rfl


theorem t6_470part0 : t6_470jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_470frontier : t6_470root.frontier 0=t6_470jobs := by rfl
theorem t6_470all : t6_470jobs.all (Job.check tree)=true := by
  simp only [t6_470jobs,List.all_append,List.all_nil,t6_470part0,Bool.and_self]
theorem t6_470checked : Checked tree [1,9,3,3,10,10] := by
  refine ⟨plan6534,valid6534,t6_470choices,?_⟩
  exact check_of_frontier tree 0 t6_470root t6_470jobs t6_470frontier t6_470all
theorem t6_471choices : plan6857.choices=[1,9,3,6,6,6].map (options 6 4) := by rfl


theorem t6_471part0 : t6_471jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_471frontier : t6_471root.frontier 0=t6_471jobs := by rfl
theorem t6_471all : t6_471jobs.all (Job.check tree)=true := by
  simp only [t6_471jobs,List.all_append,List.all_nil,t6_471part0,Bool.and_self]
theorem t6_471checked : Checked tree [1,9,3,6,6,6] := by
  refine ⟨plan6857,valid6857,t6_471choices,?_⟩
  exact check_of_frontier tree 0 t6_471root t6_471jobs t6_471frontier t6_471all
theorem t6_472choices : plan6858.choices=[1,9,3,6,6,7].map (options 6 4) := by rfl


theorem t6_472part0 : t6_472jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_472part1 : t6_472jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_472frontier : t6_472root.frontier 1=t6_472jobs := by rfl
theorem t6_472all : t6_472jobs.all (Job.check tree)=true := by
  simp only [t6_472jobs,List.all_append,List.all_nil,t6_472part0,t6_472part1,Bool.and_self]
theorem t6_472checked : Checked tree [1,9,3,6,6,7] := by
  refine ⟨plan6858,valid6858,t6_472choices,?_⟩
  exact check_of_frontier tree 1 t6_472root t6_472jobs t6_472frontier t6_472all
theorem t6_473choices : plan6859.choices=[1,9,3,6,6,10].map (options 6 4) := by rfl


theorem t6_473part0 : t6_473jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_473frontier : t6_473root.frontier 0=t6_473jobs := by rfl
theorem t6_473all : t6_473jobs.all (Job.check tree)=true := by
  simp only [t6_473jobs,List.all_append,List.all_nil,t6_473part0,Bool.and_self]
theorem t6_473checked : Checked tree [1,9,3,6,6,10] := by
  refine ⟨plan6859,valid6859,t6_473choices,?_⟩
  exact check_of_frontier tree 0 t6_473root t6_473jobs t6_473frontier t6_473all
theorem t6_474choices : plan6860.choices=[1,9,3,6,7,7].map (options 6 4) := by rfl


theorem t6_474part0 : t6_474jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_474part1 : t6_474jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_474part2 : t6_474jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_474frontier : t6_474root.frontier 2=t6_474jobs := by rfl
theorem t6_474all : t6_474jobs.all (Job.check tree)=true := by
  simp only [t6_474jobs,List.all_append,List.all_nil,t6_474part0,t6_474part1,t6_474part2,Bool.and_self]
theorem t6_474checked : Checked tree [1,9,3,6,7,7] := by
  refine ⟨plan6860,valid6860,t6_474choices,?_⟩
  exact check_of_frontier tree 2 t6_474root t6_474jobs t6_474frontier t6_474all
theorem t6_475choices : plan6861.choices=[1,9,3,6,10,7].map (options 6 4) := by rfl


theorem t6_475part0 : t6_475jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_475part1 : t6_475jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_475part2 : t6_475jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_475frontier : t6_475root.frontier 2=t6_475jobs := by rfl
theorem t6_475all : t6_475jobs.all (Job.check tree)=true := by
  simp only [t6_475jobs,List.all_append,List.all_nil,t6_475part0,t6_475part1,t6_475part2,Bool.and_self]
theorem t6_475checked : Checked tree [1,9,3,6,10,7] := by
  refine ⟨plan6861,valid6861,t6_475choices,?_⟩
  exact check_of_frontier tree 2 t6_475root t6_475jobs t6_475frontier t6_475all
theorem t6_476choices : plan6862.choices=[1,9,3,6,10,10].map (options 6 4) := by rfl


theorem t6_476part0 : t6_476jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_476frontier : t6_476root.frontier 0=t6_476jobs := by rfl
theorem t6_476all : t6_476jobs.all (Job.check tree)=true := by
  simp only [t6_476jobs,List.all_append,List.all_nil,t6_476part0,Bool.and_self]
theorem t6_476checked : Checked tree [1,9,3,6,10,10] := by
  refine ⟨plan6862,valid6862,t6_476choices,?_⟩
  exact check_of_frontier tree 0 t6_476root t6_476jobs t6_476frontier t6_476all
theorem t6_477choices : plan6863.choices=[1,9,3,7,7,7].map (options 6 4) := by rfl


theorem t6_477part0 : t6_477jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_477part1 : t6_477jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_477part2 : t6_477jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_477frontier : t6_477root.frontier 1=t6_477jobs := by rfl
theorem t6_477all : t6_477jobs.all (Job.check tree)=true := by
  simp only [t6_477jobs,List.all_append,List.all_nil,t6_477part0,t6_477part1,t6_477part2,Bool.and_self]
theorem t6_477checked : Checked tree [1,9,3,7,7,7] := by
  refine ⟨plan6863,valid6863,t6_477choices,?_⟩
  exact check_of_frontier tree 1 t6_477root t6_477jobs t6_477frontier t6_477all
theorem t6_478choices : plan6864.choices=[1,9,3,10,7,7].map (options 6 4) := by rfl


theorem t6_478part0 : t6_478jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_478part1 : t6_478jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_478part2 : t6_478jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_478frontier : t6_478root.frontier 2=t6_478jobs := by rfl
theorem t6_478all : t6_478jobs.all (Job.check tree)=true := by
  simp only [t6_478jobs,List.all_append,List.all_nil,t6_478part0,t6_478part1,t6_478part2,Bool.and_self]
theorem t6_478checked : Checked tree [1,9,3,10,7,7] := by
  refine ⟨plan6864,valid6864,t6_478choices,?_⟩
  exact check_of_frontier tree 2 t6_478root t6_478jobs t6_478frontier t6_478all
theorem t6_479choices : plan6865.choices=[1,9,3,10,10,7].map (options 6 4) := by rfl


theorem t6_479part0 : t6_479jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_479part1 : t6_479jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_479frontier : t6_479root.frontier 1=t6_479jobs := by rfl
theorem t6_479all : t6_479jobs.all (Job.check tree)=true := by
  simp only [t6_479jobs,List.all_append,List.all_nil,t6_479part0,t6_479part1,Bool.and_self]
theorem t6_479checked : Checked tree [1,9,3,10,10,7] := by
  refine ⟨plan6865,valid6865,t6_479choices,?_⟩
  exact check_of_frontier tree 1 t6_479root t6_479jobs t6_479frontier t6_479all
theorem t6_480choices : plan6866.choices=[1,9,3,10,10,10].map (options 6 4) := by rfl


theorem t6_480part0 : t6_480jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_480frontier : t6_480root.frontier 0=t6_480jobs := by rfl
theorem t6_480all : t6_480jobs.all (Job.check tree)=true := by
  simp only [t6_480jobs,List.all_append,List.all_nil,t6_480part0,Bool.and_self]
theorem t6_480checked : Checked tree [1,9,3,10,10,10] := by
  refine ⟨plan6866,valid6866,t6_480choices,?_⟩
  exact check_of_frontier tree 0 t6_480root t6_480jobs t6_480frontier t6_480all
theorem t6_481choices : plan7293.choices=[1,9,6,6,6,6].map (options 6 5) := by rfl


theorem t6_481part0 : t6_481jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_481frontier : t6_481root.frontier 0=t6_481jobs := by rfl
theorem t6_481all : t6_481jobs.all (Job.check tree)=true := by
  simp only [t6_481jobs,List.all_append,List.all_nil,t6_481part0,Bool.and_self]
theorem t6_481checked : Checked tree [1,9,6,6,6,6] := by
  refine ⟨plan7293,valid7293,t6_481choices,?_⟩
  exact check_of_frontier tree 0 t6_481root t6_481jobs t6_481frontier t6_481all
theorem t6_482choices : plan7294.choices=[1,9,6,6,6,7].map (options 6 5) := by rfl


theorem t6_482part0 : t6_482jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_482frontier : t6_482root.frontier 0=t6_482jobs := by rfl
theorem t6_482all : t6_482jobs.all (Job.check tree)=true := by
  simp only [t6_482jobs,List.all_append,List.all_nil,t6_482part0,Bool.and_self]
theorem t6_482checked : Checked tree [1,9,6,6,6,7] := by
  refine ⟨plan7294,valid7294,t6_482choices,?_⟩
  exact check_of_frontier tree 0 t6_482root t6_482jobs t6_482frontier t6_482all
theorem t6_483choices : plan7295.choices=[1,9,6,6,6,10].map (options 6 5) := by rfl


theorem t6_483part0 : t6_483jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_483frontier : t6_483root.frontier 0=t6_483jobs := by rfl
theorem t6_483all : t6_483jobs.all (Job.check tree)=true := by
  simp only [t6_483jobs,List.all_append,List.all_nil,t6_483part0,Bool.and_self]
theorem t6_483checked : Checked tree [1,9,6,6,6,10] := by
  refine ⟨plan7295,valid7295,t6_483choices,?_⟩
  exact check_of_frontier tree 0 t6_483root t6_483jobs t6_483frontier t6_483all
theorem t6_484choices : plan7296.choices=[1,9,6,6,7,7].map (options 6 5) := by rfl


theorem t6_484part0 : t6_484jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_484frontier : t6_484root.frontier 0=t6_484jobs := by rfl
theorem t6_484all : t6_484jobs.all (Job.check tree)=true := by
  simp only [t6_484jobs,List.all_append,List.all_nil,t6_484part0,Bool.and_self]
theorem t6_484checked : Checked tree [1,9,6,6,7,7] := by
  refine ⟨plan7296,valid7296,t6_484choices,?_⟩
  exact check_of_frontier tree 0 t6_484root t6_484jobs t6_484frontier t6_484all
theorem t6_485choices : plan7297.choices=[1,9,6,6,10,7].map (options 6 5) := by rfl


theorem t6_485part0 : t6_485jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_485frontier : t6_485root.frontier 0=t6_485jobs := by rfl
theorem t6_485all : t6_485jobs.all (Job.check tree)=true := by
  simp only [t6_485jobs,List.all_append,List.all_nil,t6_485part0,Bool.and_self]
theorem t6_485checked : Checked tree [1,9,6,6,10,7] := by
  refine ⟨plan7297,valid7297,t6_485choices,?_⟩
  exact check_of_frontier tree 0 t6_485root t6_485jobs t6_485frontier t6_485all
theorem t6_486choices : plan7298.choices=[1,9,6,6,10,10].map (options 6 5) := by rfl


theorem t6_486part0 : t6_486jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_486frontier : t6_486root.frontier 0=t6_486jobs := by rfl
theorem t6_486all : t6_486jobs.all (Job.check tree)=true := by
  simp only [t6_486jobs,List.all_append,List.all_nil,t6_486part0,Bool.and_self]
theorem t6_486checked : Checked tree [1,9,6,6,10,10] := by
  refine ⟨plan7298,valid7298,t6_486choices,?_⟩
  exact check_of_frontier tree 0 t6_486root t6_486jobs t6_486frontier t6_486all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks060 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_477checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_469checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_478checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_479checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_480checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_481checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_482checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_483checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_484checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_485checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_486checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_470checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_471checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_472checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_473checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_474checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_475checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_476checked⟩
