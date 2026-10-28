-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks051
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:05:16.576232+00:00
-- url     : https://prove2.me/submissions/18c36a2b-e741-4194-8504-ed5f22053ea4

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks051
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks051
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
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























































theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)







theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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





































































































































theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)

























theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)



theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)









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

























































































































































theorem valid1517 : plan1517.Valid := valid_step _ _ _ valid547 (by decide +kernel)































theorem valid1533 : plan1533.Valid := valid_step _ _ _ valid560 (by decide +kernel)



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

































































theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)

theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)

theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)





theorem valid1578 : plan1578.Valid := valid_step _ _ _ valid571 (by decide +kernel)



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































theorem valid3280 : plan3280.Valid := valid_step _ _ _ valid1517 (by decide +kernel)





















































































































theorem valid3339 : plan3339.Valid := valid_step _ _ _ valid1533 (by decide +kernel)



theorem valid3341 : plan3341.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3342 : plan3342.Valid := valid_step _ _ _ valid1536 (by decide +kernel)




































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





























theorem valid5391 : plan5391.Valid := valid_step _ _ _ valid3280 (by decide +kernel)


































































































































































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





































































theorem valid3395 : plan3395.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3396 : plan3396.Valid := valid_step _ _ _ valid1581 (by decide +kernel)



theorem valid3398 : plan3398.Valid := valid_step _ _ _ valid1569 (by decide +kernel)

theorem valid3399 : plan3399.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3400 : plan3400.Valid := valid_step _ _ _ valid1571 (by decide +kernel)

theorem valid3401 : plan3401.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3402 : plan3402.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3403 : plan3403.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3404 : plan3404.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3405 : plan3405.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3406 : plan3406.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3407 : plan3407.Valid := valid_step _ _ _ valid1582 (by decide +kernel)

theorem valid3408 : plan3408.Valid := valid_step _ _ _ valid1575 (by decide +kernel)























theorem valid3420 : plan3420.Valid := valid_step _ _ _ valid1570 (by decide +kernel)



theorem valid3422 : plan3422.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3423 : plan3423.Valid := valid_step _ _ _ valid1573 (by decide +kernel)



theorem valid3425 : plan3425.Valid := valid_step _ _ _ valid1575 (by decide +kernel)





theorem valid3428 : plan3428.Valid := valid_step _ _ _ valid1578 (by decide +kernel)



theorem valid3430 : plan3430.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3431 : plan3431.Valid := valid_step _ _ _ valid1581 (by decide +kernel)


















































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



theorem valid5474 : plan5474.Valid := valid_step _ _ _ valid3339 (by decide +kernel)



theorem valid5476 : plan5476.Valid := valid_step _ _ _ valid3341 (by decide +kernel)

theorem valid5477 : plan5477.Valid := valid_step _ _ _ valid3342 (by decide +kernel)






















































































































































































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







































































































































theorem valid6500 : plan6500.Valid := valid_step _ _ _ valid5474 (by decide +kernel)

theorem valid6501 : plan6501.Valid := valid_step _ _ _ valid5476 (by decide +kernel)

theorem valid6502 : plan6502.Valid := valid_step _ _ _ valid5477 (by decide +kernel)




















































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







































theorem valid5588 : plan5588.Valid := valid_step _ _ _ valid3395 (by decide +kernel)

theorem valid5589 : plan5589.Valid := valid_step _ _ _ valid3396 (by decide +kernel)



theorem valid5591 : plan5591.Valid := valid_step _ _ _ valid3398 (by decide +kernel)

theorem valid5592 : plan5592.Valid := valid_step _ _ _ valid3399 (by decide +kernel)

theorem valid5593 : plan5593.Valid := valid_step _ _ _ valid3400 (by decide +kernel)

theorem valid5594 : plan5594.Valid := valid_step _ _ _ valid3401 (by decide +kernel)

theorem valid5595 : plan5595.Valid := valid_step _ _ _ valid3402 (by decide +kernel)

theorem valid5596 : plan5596.Valid := valid_step _ _ _ valid3403 (by decide +kernel)

theorem valid5597 : plan5597.Valid := valid_step _ _ _ valid3404 (by decide +kernel)

theorem valid5598 : plan5598.Valid := valid_step _ _ _ valid3405 (by decide +kernel)

theorem valid5599 : plan5599.Valid := valid_step _ _ _ valid3406 (by decide +kernel)

theorem valid5600 : plan5600.Valid := valid_step _ _ _ valid3407 (by decide +kernel)

theorem valid5601 : plan5601.Valid := valid_step _ _ _ valid3408 (by decide +kernel)









theorem valid5606 : plan5606.Valid := valid_step _ _ _ valid3420 (by decide +kernel)



theorem valid5608 : plan5608.Valid := valid_step _ _ _ valid3422 (by decide +kernel)

theorem valid5609 : plan5609.Valid := valid_step _ _ _ valid3423 (by decide +kernel)



theorem valid5611 : plan5611.Valid := valid_step _ _ _ valid3425 (by decide +kernel)



theorem valid5613 : plan5613.Valid := valid_step _ _ _ valid3428 (by decide +kernel)



theorem valid5615 : plan5615.Valid := valid_step _ _ _ valid3430 (by decide +kernel)

theorem valid5616 : plan5616.Valid := valid_step _ _ _ valid3431 (by decide +kernel)
































































































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























































































































theorem valid6780 : plan6780.Valid := valid_step _ _ _ valid5588 (by decide +kernel)

theorem valid6781 : plan6781.Valid := valid_step _ _ _ valid5589 (by decide +kernel)

theorem valid6782 : plan6782.Valid := valid_step _ _ _ valid5591 (by decide +kernel)

theorem valid6783 : plan6783.Valid := valid_step _ _ _ valid5592 (by decide +kernel)

theorem valid6784 : plan6784.Valid := valid_step _ _ _ valid5593 (by decide +kernel)

theorem valid6785 : plan6785.Valid := valid_step _ _ _ valid5594 (by decide +kernel)

theorem valid6786 : plan6786.Valid := valid_step _ _ _ valid5595 (by decide +kernel)

theorem valid6787 : plan6787.Valid := valid_step _ _ _ valid5596 (by decide +kernel)

theorem valid6788 : plan6788.Valid := valid_step _ _ _ valid5597 (by decide +kernel)

theorem valid6789 : plan6789.Valid := valid_step _ _ _ valid5598 (by decide +kernel)

theorem valid6790 : plan6790.Valid := valid_step _ _ _ valid5599 (by decide +kernel)

theorem valid6791 : plan6791.Valid := valid_step _ _ _ valid5600 (by decide +kernel)

theorem valid6792 : plan6792.Valid := valid_step _ _ _ valid5601 (by decide +kernel)

theorem valid6793 : plan6793.Valid := valid_step _ _ _ valid5606 (by decide +kernel)

theorem valid6794 : plan6794.Valid := valid_step _ _ _ valid5608 (by decide +kernel)

theorem valid6795 : plan6795.Valid := valid_step _ _ _ valid5609 (by decide +kernel)

theorem valid6796 : plan6796.Valid := valid_step _ _ _ valid5611 (by decide +kernel)

theorem valid6797 : plan6797.Valid := valid_step _ _ _ valid5613 (by decide +kernel)

theorem valid6798 : plan6798.Valid := valid_step _ _ _ valid5615 (by decide +kernel)

theorem valid6799 : plan6799.Valid := valid_step _ _ _ valid5616 (by decide +kernel)


































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























theorem valid6348 : plan6348.Valid := valid_step _ _ _ valid5391 (by decide +kernel)








































































































































































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
theorem t6_257choices : plan6780.choices=[1,2,5,10,7,7].map (options 6 4) := by rfl


theorem t6_257part0 : t6_257jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_257frontier : t6_257root.frontier 0=t6_257jobs := by rfl
theorem t6_257all : t6_257jobs.all (Job.check tree)=true := by
  simp only [t6_257jobs,List.all_append,List.all_nil,t6_257part0,Bool.and_self]
theorem t6_257checked : Checked tree [1,2,5,10,7,7] := by
  refine ⟨plan6780,valid6780,t6_257choices,?_⟩
  exact check_of_frontier tree 0 t6_257root t6_257jobs t6_257frontier t6_257all
theorem t6_258choices : plan6781.choices=[1,2,5,10,10,7].map (options 6 4) := by rfl


theorem t6_258part0 : t6_258jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_258frontier : t6_258root.frontier 0=t6_258jobs := by rfl
theorem t6_258all : t6_258jobs.all (Job.check tree)=true := by
  simp only [t6_258jobs,List.all_append,List.all_nil,t6_258part0,Bool.and_self]
theorem t6_258checked : Checked tree [1,2,5,10,10,7] := by
  refine ⟨plan6781,valid6781,t6_258choices,?_⟩
  exact check_of_frontier tree 0 t6_258root t6_258jobs t6_258frontier t6_258all
theorem t6_259choices : plan6782.choices=[1,2,6,6,6,6].map (options 6 4) := by rfl


theorem t6_259part0 : t6_259jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_259frontier : t6_259root.frontier 0=t6_259jobs := by rfl
theorem t6_259all : t6_259jobs.all (Job.check tree)=true := by
  simp only [t6_259jobs,List.all_append,List.all_nil,t6_259part0,Bool.and_self]
theorem t6_259checked : Checked tree [1,2,6,6,6,6] := by
  refine ⟨plan6782,valid6782,t6_259choices,?_⟩
  exact check_of_frontier tree 0 t6_259root t6_259jobs t6_259frontier t6_259all
theorem t6_260choices : plan6783.choices=[1,2,6,6,6,7].map (options 6 4) := by rfl


theorem t6_260part0 : t6_260jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_260frontier : t6_260root.frontier 0=t6_260jobs := by rfl
theorem t6_260all : t6_260jobs.all (Job.check tree)=true := by
  simp only [t6_260jobs,List.all_append,List.all_nil,t6_260part0,Bool.and_self]
theorem t6_260checked : Checked tree [1,2,6,6,6,7] := by
  refine ⟨plan6783,valid6783,t6_260choices,?_⟩
  exact check_of_frontier tree 0 t6_260root t6_260jobs t6_260frontier t6_260all
theorem t6_261choices : plan6784.choices=[1,2,6,6,6,10].map (options 6 4) := by rfl


theorem t6_261part0 : t6_261jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_261frontier : t6_261root.frontier 0=t6_261jobs := by rfl
theorem t6_261all : t6_261jobs.all (Job.check tree)=true := by
  simp only [t6_261jobs,List.all_append,List.all_nil,t6_261part0,Bool.and_self]
theorem t6_261checked : Checked tree [1,2,6,6,6,10] := by
  refine ⟨plan6784,valid6784,t6_261choices,?_⟩
  exact check_of_frontier tree 0 t6_261root t6_261jobs t6_261frontier t6_261all
theorem t6_262choices : plan6785.choices=[1,2,6,6,7,7].map (options 6 4) := by rfl


theorem t6_262part0 : t6_262jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_262part1 : t6_262jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_262frontier : t6_262root.frontier 1=t6_262jobs := by rfl
theorem t6_262all : t6_262jobs.all (Job.check tree)=true := by
  simp only [t6_262jobs,List.all_append,List.all_nil,t6_262part0,t6_262part1,Bool.and_self]
theorem t6_262checked : Checked tree [1,2,6,6,7,7] := by
  refine ⟨plan6785,valid6785,t6_262choices,?_⟩
  exact check_of_frontier tree 1 t6_262root t6_262jobs t6_262frontier t6_262all
theorem t6_263choices : plan6786.choices=[1,2,6,6,10,7].map (options 6 4) := by rfl


theorem t6_263part0 : t6_263jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_263frontier : t6_263root.frontier 0=t6_263jobs := by rfl
theorem t6_263all : t6_263jobs.all (Job.check tree)=true := by
  simp only [t6_263jobs,List.all_append,List.all_nil,t6_263part0,Bool.and_self]
theorem t6_263checked : Checked tree [1,2,6,6,10,7] := by
  refine ⟨plan6786,valid6786,t6_263choices,?_⟩
  exact check_of_frontier tree 0 t6_263root t6_263jobs t6_263frontier t6_263all
theorem t6_264choices : plan6787.choices=[1,2,6,6,10,10].map (options 6 4) := by rfl


theorem t6_264part0 : t6_264jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_264frontier : t6_264root.frontier 0=t6_264jobs := by rfl
theorem t6_264all : t6_264jobs.all (Job.check tree)=true := by
  simp only [t6_264jobs,List.all_append,List.all_nil,t6_264part0,Bool.and_self]
theorem t6_264checked : Checked tree [1,2,6,6,10,10] := by
  refine ⟨plan6787,valid6787,t6_264choices,?_⟩
  exact check_of_frontier tree 0 t6_264root t6_264jobs t6_264frontier t6_264all
theorem t6_265choices : plan6788.choices=[1,2,6,7,7,7].map (options 6 4) := by rfl


theorem t6_265part0 : t6_265jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_265part1 : t6_265jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_265frontier : t6_265root.frontier 1=t6_265jobs := by rfl
theorem t6_265all : t6_265jobs.all (Job.check tree)=true := by
  simp only [t6_265jobs,List.all_append,List.all_nil,t6_265part0,t6_265part1,Bool.and_self]
theorem t6_265checked : Checked tree [1,2,6,7,7,7] := by
  refine ⟨plan6788,valid6788,t6_265choices,?_⟩
  exact check_of_frontier tree 1 t6_265root t6_265jobs t6_265frontier t6_265all
theorem t6_266choices : plan6789.choices=[1,2,6,10,7,7].map (options 6 4) := by rfl


theorem t6_266part0 : t6_266jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_266part1 : t6_266jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_266part2 : t6_266jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_266frontier : t6_266root.frontier 1=t6_266jobs := by rfl
theorem t6_266all : t6_266jobs.all (Job.check tree)=true := by
  simp only [t6_266jobs,List.all_append,List.all_nil,t6_266part0,t6_266part1,t6_266part2,Bool.and_self]
theorem t6_266checked : Checked tree [1,2,6,10,7,7] := by
  refine ⟨plan6789,valid6789,t6_266choices,?_⟩
  exact check_of_frontier tree 1 t6_266root t6_266jobs t6_266frontier t6_266all
theorem t6_267choices : plan6790.choices=[1,2,6,10,10,7].map (options 6 4) := by rfl


theorem t6_267part0 : t6_267jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_267frontier : t6_267root.frontier 0=t6_267jobs := by rfl
theorem t6_267all : t6_267jobs.all (Job.check tree)=true := by
  simp only [t6_267jobs,List.all_append,List.all_nil,t6_267part0,Bool.and_self]
theorem t6_267checked : Checked tree [1,2,6,10,10,7] := by
  refine ⟨plan6790,valid6790,t6_267choices,?_⟩
  exact check_of_frontier tree 0 t6_267root t6_267jobs t6_267frontier t6_267all
theorem t6_268choices : plan6791.choices=[1,2,6,10,10,10].map (options 6 4) := by rfl


theorem t6_268part0 : t6_268jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_268frontier : t6_268root.frontier 0=t6_268jobs := by rfl
theorem t6_268all : t6_268jobs.all (Job.check tree)=true := by
  simp only [t6_268jobs,List.all_append,List.all_nil,t6_268part0,Bool.and_self]
theorem t6_268checked : Checked tree [1,2,6,10,10,10] := by
  refine ⟨plan6791,valid6791,t6_268choices,?_⟩
  exact check_of_frontier tree 0 t6_268root t6_268jobs t6_268frontier t6_268all
theorem t6_269choices : plan6792.choices=[1,2,7,7,7,7].map (options 6 4) := by rfl


theorem t6_269part0 : t6_269jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_269frontier : t6_269root.frontier 0=t6_269jobs := by rfl
theorem t6_269all : t6_269jobs.all (Job.check tree)=true := by
  simp only [t6_269jobs,List.all_append,List.all_nil,t6_269part0,Bool.and_self]
theorem t6_269checked : Checked tree [1,2,7,7,7,7] := by
  refine ⟨plan6792,valid6792,t6_269choices,?_⟩
  exact check_of_frontier tree 0 t6_269root t6_269jobs t6_269frontier t6_269all
theorem t6_270choices : plan6348.choices=[1,2,9,3,3,7].map (options 6 2) := by rfl


theorem t6_270part0 : t6_270jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_270frontier : t6_270root.frontier 0=t6_270jobs := by rfl
theorem t6_270all : t6_270jobs.all (Job.check tree)=true := by
  simp only [t6_270jobs,List.all_append,List.all_nil,t6_270part0,Bool.and_self]
theorem t6_270checked : Checked tree [1,2,9,3,3,7] := by
  refine ⟨plan6348,valid6348,t6_270choices,?_⟩
  exact check_of_frontier tree 0 t6_270root t6_270jobs t6_270frontier t6_270all
theorem t6_271choices : plan6500.choices=[1,2,9,3,6,7].map (options 6 3) := by rfl


theorem t6_271part0 : t6_271jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_271frontier : t6_271root.frontier 0=t6_271jobs := by rfl
theorem t6_271all : t6_271jobs.all (Job.check tree)=true := by
  simp only [t6_271jobs,List.all_append,List.all_nil,t6_271part0,Bool.and_self]
theorem t6_271checked : Checked tree [1,2,9,3,6,7] := by
  refine ⟨plan6500,valid6500,t6_271choices,?_⟩
  exact check_of_frontier tree 0 t6_271root t6_271jobs t6_271frontier t6_271all
theorem t6_272choices : plan6501.choices=[1,2,9,3,7,7].map (options 6 3) := by rfl


theorem t6_272part0 : t6_272jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_272part1 : t6_272jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_272frontier : t6_272root.frontier 1=t6_272jobs := by rfl
theorem t6_272all : t6_272jobs.all (Job.check tree)=true := by
  simp only [t6_272jobs,List.all_append,List.all_nil,t6_272part0,t6_272part1,Bool.and_self]
theorem t6_272checked : Checked tree [1,2,9,3,7,7] := by
  refine ⟨plan6501,valid6501,t6_272choices,?_⟩
  exact check_of_frontier tree 1 t6_272root t6_272jobs t6_272frontier t6_272all
theorem t6_273choices : plan6502.choices=[1,2,9,3,10,7].map (options 6 3) := by rfl


theorem t6_273part0 : t6_273jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_273frontier : t6_273root.frontier 0=t6_273jobs := by rfl
theorem t6_273all : t6_273jobs.all (Job.check tree)=true := by
  simp only [t6_273jobs,List.all_append,List.all_nil,t6_273part0,Bool.and_self]
theorem t6_273checked : Checked tree [1,2,9,3,10,7] := by
  refine ⟨plan6502,valid6502,t6_273choices,?_⟩
  exact check_of_frontier tree 0 t6_273root t6_273jobs t6_273frontier t6_273all
theorem t6_274choices : plan6793.choices=[1,2,9,6,6,7].map (options 6 4) := by rfl


theorem t6_274part0 : t6_274jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_274frontier : t6_274root.frontier 0=t6_274jobs := by rfl
theorem t6_274all : t6_274jobs.all (Job.check tree)=true := by
  simp only [t6_274jobs,List.all_append,List.all_nil,t6_274part0,Bool.and_self]
theorem t6_274checked : Checked tree [1,2,9,6,6,7] := by
  refine ⟨plan6793,valid6793,t6_274choices,?_⟩
  exact check_of_frontier tree 0 t6_274root t6_274jobs t6_274frontier t6_274all
theorem t6_275choices : plan6794.choices=[1,2,9,6,7,7].map (options 6 4) := by rfl


theorem t6_275part0 : t6_275jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_275frontier : t6_275root.frontier 0=t6_275jobs := by rfl
theorem t6_275all : t6_275jobs.all (Job.check tree)=true := by
  simp only [t6_275jobs,List.all_append,List.all_nil,t6_275part0,Bool.and_self]
theorem t6_275checked : Checked tree [1,2,9,6,7,7] := by
  refine ⟨plan6794,valid6794,t6_275choices,?_⟩
  exact check_of_frontier tree 0 t6_275root t6_275jobs t6_275frontier t6_275all
theorem t6_276choices : plan6795.choices=[1,2,9,6,10,7].map (options 6 4) := by rfl


theorem t6_276part0 : t6_276jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_276frontier : t6_276root.frontier 0=t6_276jobs := by rfl
theorem t6_276all : t6_276jobs.all (Job.check tree)=true := by
  simp only [t6_276jobs,List.all_append,List.all_nil,t6_276part0,Bool.and_self]
theorem t6_276checked : Checked tree [1,2,9,6,10,7] := by
  refine ⟨plan6795,valid6795,t6_276choices,?_⟩
  exact check_of_frontier tree 0 t6_276root t6_276jobs t6_276frontier t6_276all
theorem t6_277choices : plan6796.choices=[1,2,9,7,7,7].map (options 6 4) := by rfl


theorem t6_277part0 : t6_277jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_277frontier : t6_277root.frontier 0=t6_277jobs := by rfl
theorem t6_277all : t6_277jobs.all (Job.check tree)=true := by
  simp only [t6_277jobs,List.all_append,List.all_nil,t6_277part0,Bool.and_self]
theorem t6_277checked : Checked tree [1,2,9,7,7,7] := by
  refine ⟨plan6796,valid6796,t6_277choices,?_⟩
  exact check_of_frontier tree 0 t6_277root t6_277jobs t6_277frontier t6_277all
theorem t6_278choices : plan6797.choices=[1,2,9,9,7,7].map (options 6 4) := by rfl


theorem t6_278part0 : t6_278jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_278frontier : t6_278root.frontier 0=t6_278jobs := by rfl
theorem t6_278all : t6_278jobs.all (Job.check tree)=true := by
  simp only [t6_278jobs,List.all_append,List.all_nil,t6_278part0,Bool.and_self]
theorem t6_278checked : Checked tree [1,2,9,9,7,7] := by
  refine ⟨plan6797,valid6797,t6_278choices,?_⟩
  exact check_of_frontier tree 0 t6_278root t6_278jobs t6_278frontier t6_278all
theorem t6_279choices : plan6798.choices=[1,2,9,10,7,7].map (options 6 4) := by rfl


theorem t6_279part0 : t6_279jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_279frontier : t6_279root.frontier 0=t6_279jobs := by rfl
theorem t6_279all : t6_279jobs.all (Job.check tree)=true := by
  simp only [t6_279jobs,List.all_append,List.all_nil,t6_279part0,Bool.and_self]
theorem t6_279checked : Checked tree [1,2,9,10,7,7] := by
  refine ⟨plan6798,valid6798,t6_279choices,?_⟩
  exact check_of_frontier tree 0 t6_279root t6_279jobs t6_279frontier t6_279all
theorem t6_280choices : plan6799.choices=[1,2,9,10,10,7].map (options 6 4) := by rfl


theorem t6_280part0 : t6_280jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_280frontier : t6_280root.frontier 0=t6_280jobs := by rfl
theorem t6_280all : t6_280jobs.all (Job.check tree)=true := by
  simp only [t6_280jobs,List.all_append,List.all_nil,t6_280part0,Bool.and_self]
theorem t6_280checked : Checked tree [1,2,9,10,10,7] := by
  refine ⟨plan6799,valid6799,t6_280choices,?_⟩
  exact check_of_frontier tree 0 t6_280root t6_280jobs t6_280frontier t6_280all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks051 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_268checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_269checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_270checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_271checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_272checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_273checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_274checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_275checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_276checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_258checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_277checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_278checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_279checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_280checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_259checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_260checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_261checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_262checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_263checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_264checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_265checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_266checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_267checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_257checked⟩
