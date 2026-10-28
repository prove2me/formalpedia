-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks067
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:15:24.450674+00:00
-- url     : https://prove2.me/submissions/51f77775-4ec5-4eb0-a23c-045a21d19722

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
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

























































































































































theorem valid557 : plan557.Valid := valid_step _ _ _ valid128 (by decide +kernel)









theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)

theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid573 : plan573.Valid := valid_step _ _ _ valid132 (by decide +kernel)






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





























































































































































































theorem valid1535 : plan1535.Valid := valid_step _ _ _ valid562 (by decide +kernel)

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























theorem valid1549 : plan1549.Valid := valid_step _ _ _ valid557 (by decide +kernel)







































theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)

theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)



theorem valid1577 : plan1577.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1578 : plan1578.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1579 : plan1579.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1582 : plan1582.Valid := valid_step _ _ _ valid573 (by decide +kernel)




































































































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

























































































































































theorem valid3341 : plan3341.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3342 : plan3342.Valid := valid_step _ _ _ valid1536 (by decide +kernel)

theorem valid3343 : plan3343.Valid := valid_step _ _ _ valid1537 (by decide +kernel)

theorem valid3344 : plan3344.Valid := valid_step _ _ _ valid1549 (by decide +kernel)
































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





















































































































theorem valid3419 : plan3419.Valid := valid_step _ _ _ valid1569 (by decide +kernel)

theorem valid3420 : plan3420.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3421 : plan3421.Valid := valid_step _ _ _ valid1571 (by decide +kernel)

theorem valid3422 : plan3422.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3423 : plan3423.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3424 : plan3424.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3425 : plan3425.Valid := valid_step _ _ _ valid1575 (by decide +kernel)



theorem valid3427 : plan3427.Valid := valid_step _ _ _ valid1577 (by decide +kernel)

theorem valid3428 : plan3428.Valid := valid_step _ _ _ valid1578 (by decide +kernel)

theorem valid3429 : plan3429.Valid := valid_step _ _ _ valid1579 (by decide +kernel)

theorem valid3430 : plan3430.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3431 : plan3431.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3432 : plan3432.Valid := valid_step _ _ _ valid1582 (by decide +kernel)

theorem valid3433 : plan3433.Valid := valid_step _ _ _ valid1575 (by decide +kernel)














































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







theorem valid5476 : plan5476.Valid := valid_step _ _ _ valid3341 (by decide +kernel)

theorem valid5477 : plan5477.Valid := valid_step _ _ _ valid3342 (by decide +kernel)

theorem valid5478 : plan5478.Valid := valid_step _ _ _ valid3343 (by decide +kernel)

theorem valid5479 : plan5479.Valid := valid_step _ _ _ valid3344 (by decide +kernel)


















































































































































































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









































































theorem valid5605 : plan5605.Valid := valid_step _ _ _ valid3419 (by decide +kernel)

theorem valid5606 : plan5606.Valid := valid_step _ _ _ valid3420 (by decide +kernel)

theorem valid5607 : plan5607.Valid := valid_step _ _ _ valid3421 (by decide +kernel)

theorem valid5608 : plan5608.Valid := valid_step _ _ _ valid3422 (by decide +kernel)

theorem valid5609 : plan5609.Valid := valid_step _ _ _ valid3423 (by decide +kernel)

theorem valid5610 : plan5610.Valid := valid_step _ _ _ valid3424 (by decide +kernel)

theorem valid5611 : plan5611.Valid := valid_step _ _ _ valid3425 (by decide +kernel)

theorem valid5612 : plan5612.Valid := valid_step _ _ _ valid3427 (by decide +kernel)

theorem valid5613 : plan5613.Valid := valid_step _ _ _ valid3428 (by decide +kernel)

theorem valid5614 : plan5614.Valid := valid_step _ _ _ valid3429 (by decide +kernel)

theorem valid5615 : plan5615.Valid := valid_step _ _ _ valid3430 (by decide +kernel)

theorem valid5616 : plan5616.Valid := valid_step _ _ _ valid3431 (by decide +kernel)

theorem valid5617 : plan5617.Valid := valid_step _ _ _ valid3432 (by decide +kernel)

theorem valid5618 : plan5618.Valid := valid_step _ _ _ valid3433 (by decide +kernel)




























































































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

































































































































































theorem valid6897 : plan6897.Valid := valid_step _ _ _ valid5605 (by decide +kernel)

theorem valid6898 : plan6898.Valid := valid_step _ _ _ valid5606 (by decide +kernel)

theorem valid6899 : plan6899.Valid := valid_step _ _ _ valid5607 (by decide +kernel)

theorem valid6900 : plan6900.Valid := valid_step _ _ _ valid5608 (by decide +kernel)

theorem valid6901 : plan6901.Valid := valid_step _ _ _ valid5609 (by decide +kernel)

theorem valid6902 : plan6902.Valid := valid_step _ _ _ valid5610 (by decide +kernel)

theorem valid6903 : plan6903.Valid := valid_step _ _ _ valid5611 (by decide +kernel)

theorem valid6904 : plan6904.Valid := valid_step _ _ _ valid5612 (by decide +kernel)

theorem valid6905 : plan6905.Valid := valid_step _ _ _ valid5613 (by decide +kernel)

theorem valid6906 : plan6906.Valid := valid_step _ _ _ valid5614 (by decide +kernel)

theorem valid6907 : plan6907.Valid := valid_step _ _ _ valid5615 (by decide +kernel)

theorem valid6908 : plan6908.Valid := valid_step _ _ _ valid5616 (by decide +kernel)

theorem valid6909 : plan6909.Valid := valid_step _ _ _ valid5617 (by decide +kernel)

theorem valid6910 : plan6910.Valid := valid_step _ _ _ valid5618 (by decide +kernel)




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

























































































theorem valid6573 : plan6573.Valid := valid_step _ _ _ valid5476 (by decide +kernel)

theorem valid6574 : plan6574.Valid := valid_step _ _ _ valid5477 (by decide +kernel)

theorem valid6575 : plan6575.Valid := valid_step _ _ _ valid5478 (by decide +kernel)

theorem valid6576 : plan6576.Valid := valid_step _ _ _ valid5479 (by decide +kernel)
































































































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
theorem t6_610choices : plan6573.choices=[2,2,9,3,7,7].map (options 6 3) := by rfl


theorem t6_610part0 : t6_610jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_610part1 : t6_610jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_610part2 : t6_610jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_610part3 : t6_610jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_610frontier : t6_610root.frontier 1=t6_610jobs := by rfl
theorem t6_610all : t6_610jobs.all (Job.check tree)=true := by
  simp only [t6_610jobs,List.all_append,List.all_nil,t6_610part0,t6_610part1,t6_610part2,t6_610part3,Bool.and_self]
theorem t6_610checked : Checked tree [2,2,9,3,7,7] := by
  refine ⟨plan6573,valid6573,t6_610choices,?_⟩
  exact check_of_frontier tree 1 t6_610root t6_610jobs t6_610frontier t6_610all
theorem t6_611choices : plan6574.choices=[2,2,9,3,10,7].map (options 6 3) := by rfl


theorem t6_611part0 : t6_611jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_611part1 : t6_611jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_611part2 : t6_611jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_611frontier : t6_611root.frontier 1=t6_611jobs := by rfl
theorem t6_611all : t6_611jobs.all (Job.check tree)=true := by
  simp only [t6_611jobs,List.all_append,List.all_nil,t6_611part0,t6_611part1,t6_611part2,Bool.and_self]
theorem t6_611checked : Checked tree [2,2,9,3,10,7] := by
  refine ⟨plan6574,valid6574,t6_611choices,?_⟩
  exact check_of_frontier tree 1 t6_611root t6_611jobs t6_611frontier t6_611all
theorem t6_612choices : plan6575.choices=[2,2,9,3,10,10].map (options 6 3) := by rfl


theorem t6_612part0 : t6_612jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_612frontier : t6_612root.frontier 0=t6_612jobs := by rfl
theorem t6_612all : t6_612jobs.all (Job.check tree)=true := by
  simp only [t6_612jobs,List.all_append,List.all_nil,t6_612part0,Bool.and_self]
theorem t6_612checked : Checked tree [2,2,9,3,10,10] := by
  refine ⟨plan6575,valid6575,t6_612choices,?_⟩
  exact check_of_frontier tree 0 t6_612root t6_612jobs t6_612frontier t6_612all
theorem t6_613choices : plan6897.choices=[2,2,9,6,6,6].map (options 6 4) := by rfl


theorem t6_613part0 : t6_613jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_613frontier : t6_613root.frontier 0=t6_613jobs := by rfl
theorem t6_613all : t6_613jobs.all (Job.check tree)=true := by
  simp only [t6_613jobs,List.all_append,List.all_nil,t6_613part0,Bool.and_self]
theorem t6_613checked : Checked tree [2,2,9,6,6,6] := by
  refine ⟨plan6897,valid6897,t6_613choices,?_⟩
  exact check_of_frontier tree 0 t6_613root t6_613jobs t6_613frontier t6_613all
theorem t6_614choices : plan6898.choices=[2,2,9,6,6,7].map (options 6 4) := by rfl


theorem t6_614part0 : t6_614jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_614frontier : t6_614root.frontier 0=t6_614jobs := by rfl
theorem t6_614all : t6_614jobs.all (Job.check tree)=true := by
  simp only [t6_614jobs,List.all_append,List.all_nil,t6_614part0,Bool.and_self]
theorem t6_614checked : Checked tree [2,2,9,6,6,7] := by
  refine ⟨plan6898,valid6898,t6_614choices,?_⟩
  exact check_of_frontier tree 0 t6_614root t6_614jobs t6_614frontier t6_614all
theorem t6_615choices : plan6899.choices=[2,2,9,6,6,10].map (options 6 4) := by rfl


theorem t6_615part0 : t6_615jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_615frontier : t6_615root.frontier 0=t6_615jobs := by rfl
theorem t6_615all : t6_615jobs.all (Job.check tree)=true := by
  simp only [t6_615jobs,List.all_append,List.all_nil,t6_615part0,Bool.and_self]
theorem t6_615checked : Checked tree [2,2,9,6,6,10] := by
  refine ⟨plan6899,valid6899,t6_615choices,?_⟩
  exact check_of_frontier tree 0 t6_615root t6_615jobs t6_615frontier t6_615all
theorem t6_616choices : plan6900.choices=[2,2,9,6,7,7].map (options 6 4) := by rfl


theorem t6_616part0 : t6_616jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_616part1 : t6_616jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_616frontier : t6_616root.frontier 1=t6_616jobs := by rfl
theorem t6_616all : t6_616jobs.all (Job.check tree)=true := by
  simp only [t6_616jobs,List.all_append,List.all_nil,t6_616part0,t6_616part1,Bool.and_self]
theorem t6_616checked : Checked tree [2,2,9,6,7,7] := by
  refine ⟨plan6900,valid6900,t6_616choices,?_⟩
  exact check_of_frontier tree 1 t6_616root t6_616jobs t6_616frontier t6_616all
theorem t6_617choices : plan6901.choices=[2,2,9,6,10,7].map (options 6 4) := by rfl


theorem t6_617part0 : t6_617jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_617part1 : t6_617jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_617frontier : t6_617root.frontier 1=t6_617jobs := by rfl
theorem t6_617all : t6_617jobs.all (Job.check tree)=true := by
  simp only [t6_617jobs,List.all_append,List.all_nil,t6_617part0,t6_617part1,Bool.and_self]
theorem t6_617checked : Checked tree [2,2,9,6,10,7] := by
  refine ⟨plan6901,valid6901,t6_617choices,?_⟩
  exact check_of_frontier tree 1 t6_617root t6_617jobs t6_617frontier t6_617all
theorem t6_618choices : plan6902.choices=[2,2,9,6,10,10].map (options 6 4) := by rfl


theorem t6_618part0 : t6_618jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_618frontier : t6_618root.frontier 0=t6_618jobs := by rfl
theorem t6_618all : t6_618jobs.all (Job.check tree)=true := by
  simp only [t6_618jobs,List.all_append,List.all_nil,t6_618part0,Bool.and_self]
theorem t6_618checked : Checked tree [2,2,9,6,10,10] := by
  refine ⟨plan6902,valid6902,t6_618choices,?_⟩
  exact check_of_frontier tree 0 t6_618root t6_618jobs t6_618frontier t6_618all
theorem t6_619choices : plan6903.choices=[2,2,9,7,7,7].map (options 6 4) := by rfl


theorem t6_619part0 : t6_619jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_619part1 : t6_619jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_619frontier : t6_619root.frontier 1=t6_619jobs := by rfl
theorem t6_619all : t6_619jobs.all (Job.check tree)=true := by
  simp only [t6_619jobs,List.all_append,List.all_nil,t6_619part0,t6_619part1,Bool.and_self]
theorem t6_619checked : Checked tree [2,2,9,7,7,7] := by
  refine ⟨plan6903,valid6903,t6_619choices,?_⟩
  exact check_of_frontier tree 1 t6_619root t6_619jobs t6_619frontier t6_619all
theorem t6_620choices : plan6576.choices=[2,2,9,9,3,7].map (options 6 3) := by rfl


theorem t6_620part0 : t6_620jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_620frontier : t6_620root.frontier 0=t6_620jobs := by rfl
theorem t6_620all : t6_620jobs.all (Job.check tree)=true := by
  simp only [t6_620jobs,List.all_append,List.all_nil,t6_620part0,Bool.and_self]
theorem t6_620checked : Checked tree [2,2,9,9,3,7] := by
  refine ⟨plan6576,valid6576,t6_620choices,?_⟩
  exact check_of_frontier tree 0 t6_620root t6_620jobs t6_620frontier t6_620all
theorem t6_621choices : plan6904.choices=[2,2,9,9,6,7].map (options 6 4) := by rfl


theorem t6_621part0 : t6_621jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_621frontier : t6_621root.frontier 0=t6_621jobs := by rfl
theorem t6_621all : t6_621jobs.all (Job.check tree)=true := by
  simp only [t6_621jobs,List.all_append,List.all_nil,t6_621part0,Bool.and_self]
theorem t6_621checked : Checked tree [2,2,9,9,6,7] := by
  refine ⟨plan6904,valid6904,t6_621choices,?_⟩
  exact check_of_frontier tree 0 t6_621root t6_621jobs t6_621frontier t6_621all
theorem t6_622choices : plan6905.choices=[2,2,9,9,7,7].map (options 6 4) := by rfl


theorem t6_622part0 : t6_622jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_622frontier : t6_622root.frontier 0=t6_622jobs := by rfl
theorem t6_622all : t6_622jobs.all (Job.check tree)=true := by
  simp only [t6_622jobs,List.all_append,List.all_nil,t6_622part0,Bool.and_self]
theorem t6_622checked : Checked tree [2,2,9,9,7,7] := by
  refine ⟨plan6905,valid6905,t6_622choices,?_⟩
  exact check_of_frontier tree 0 t6_622root t6_622jobs t6_622frontier t6_622all
theorem t6_623choices : plan6906.choices=[2,2,9,9,10,7].map (options 6 4) := by rfl


theorem t6_623part0 : t6_623jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_623frontier : t6_623root.frontier 0=t6_623jobs := by rfl
theorem t6_623all : t6_623jobs.all (Job.check tree)=true := by
  simp only [t6_623jobs,List.all_append,List.all_nil,t6_623part0,Bool.and_self]
theorem t6_623checked : Checked tree [2,2,9,9,10,7] := by
  refine ⟨plan6906,valid6906,t6_623choices,?_⟩
  exact check_of_frontier tree 0 t6_623root t6_623jobs t6_623frontier t6_623all
theorem t6_624choices : plan6907.choices=[2,2,9,10,7,7].map (options 6 4) := by rfl


theorem t6_624part0 : t6_624jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_624part1 : t6_624jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_624frontier : t6_624root.frontier 1=t6_624jobs := by rfl
theorem t6_624all : t6_624jobs.all (Job.check tree)=true := by
  simp only [t6_624jobs,List.all_append,List.all_nil,t6_624part0,t6_624part1,Bool.and_self]
theorem t6_624checked : Checked tree [2,2,9,10,7,7] := by
  refine ⟨plan6907,valid6907,t6_624choices,?_⟩
  exact check_of_frontier tree 1 t6_624root t6_624jobs t6_624frontier t6_624all
theorem t6_625choices : plan6908.choices=[2,2,9,10,10,7].map (options 6 4) := by rfl


theorem t6_625part0 : t6_625jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_625frontier : t6_625root.frontier 0=t6_625jobs := by rfl
theorem t6_625all : t6_625jobs.all (Job.check tree)=true := by
  simp only [t6_625jobs,List.all_append,List.all_nil,t6_625part0,Bool.and_self]
theorem t6_625checked : Checked tree [2,2,9,10,10,7] := by
  refine ⟨plan6908,valid6908,t6_625choices,?_⟩
  exact check_of_frontier tree 0 t6_625root t6_625jobs t6_625frontier t6_625all
theorem t6_626choices : plan6909.choices=[2,2,9,10,10,10].map (options 6 4) := by rfl


theorem t6_626part0 : t6_626jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_626frontier : t6_626root.frontier 0=t6_626jobs := by rfl
theorem t6_626all : t6_626jobs.all (Job.check tree)=true := by
  simp only [t6_626jobs,List.all_append,List.all_nil,t6_626part0,Bool.and_self]
theorem t6_626checked : Checked tree [2,2,9,10,10,10] := by
  refine ⟨plan6909,valid6909,t6_626choices,?_⟩
  exact check_of_frontier tree 0 t6_626root t6_626jobs t6_626frontier t6_626all
theorem t6_627choices : plan6910.choices=[2,2,10,7,7,7].map (options 6 4) := by rfl


theorem t6_627part0 : t6_627jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_627part1 : t6_627jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_627part2 : t6_627jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_627frontier : t6_627root.frontier 1=t6_627jobs := by rfl
theorem t6_627all : t6_627jobs.all (Job.check tree)=true := by
  simp only [t6_627jobs,List.all_append,List.all_nil,t6_627part0,t6_627part1,t6_627part2,Bool.and_self]
theorem t6_627checked : Checked tree [2,2,10,7,7,7] := by
  refine ⟨plan6910,valid6910,t6_627choices,?_⟩
  exact check_of_frontier tree 1 t6_627root t6_627jobs t6_627frontier t6_627all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks067 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_619checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_620checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_621checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_622checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_623checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_624checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_625checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_626checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_610checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_627checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_611checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_612checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_613checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_614checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_615checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_616checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_617checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_618checked⟩
