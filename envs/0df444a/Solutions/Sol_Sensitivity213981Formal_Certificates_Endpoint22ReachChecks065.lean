-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks065
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:14:53.312989+00:00
-- url     : https://prove2.me/submissions/2765d454-98d7-4d9f-8f17-a0e0e609c806

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
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

theorem valid1538 : plan1538.Valid := valid_step _ _ _ valid557 (by decide +kernel)





















theorem valid1549 : plan1549.Valid := valid_step _ _ _ valid557 (by decide +kernel)

































theorem valid1566 : plan1566.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1567 : plan1567.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1568 : plan1568.Valid := valid_step _ _ _ valid572 (by decide +kernel)

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



































































































































theorem valid3330 : plan3330.Valid := valid_step _ _ _ valid1536 (by decide +kernel)

theorem valid3331 : plan3331.Valid := valid_step _ _ _ valid1537 (by decide +kernel)

theorem valid3332 : plan3332.Valid := valid_step _ _ _ valid1538 (by decide +kernel)

theorem valid3333 : plan3333.Valid := valid_step _ _ _ valid1549 (by decide +kernel)






















































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























































































































































































theorem valid5468 : plan5468.Valid := valid_step _ _ _ valid3330 (by decide +kernel)

theorem valid5469 : plan5469.Valid := valid_step _ _ _ valid3331 (by decide +kernel)

theorem valid5470 : plan5470.Valid := valid_step _ _ _ valid3332 (by decide +kernel)

theorem valid5471 : plan5471.Valid := valid_step _ _ _ valid3333 (by decide +kernel)


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









































theorem valid3381 : plan3381.Valid := valid_step _ _ _ valid1566 (by decide +kernel)

theorem valid3382 : plan3382.Valid := valid_step _ _ _ valid1567 (by decide +kernel)

theorem valid3383 : plan3383.Valid := valid_step _ _ _ valid1568 (by decide +kernel)

theorem valid3384 : plan3384.Valid := valid_step _ _ _ valid1569 (by decide +kernel)

theorem valid3385 : plan3385.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3386 : plan3386.Valid := valid_step _ _ _ valid1571 (by decide +kernel)

theorem valid3387 : plan3387.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3388 : plan3388.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3389 : plan3389.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3390 : plan3390.Valid := valid_step _ _ _ valid1575 (by decide +kernel)



theorem valid3392 : plan3392.Valid := valid_step _ _ _ valid1577 (by decide +kernel)

theorem valid3393 : plan3393.Valid := valid_step _ _ _ valid1578 (by decide +kernel)

theorem valid3394 : plan3394.Valid := valid_step _ _ _ valid1579 (by decide +kernel)

theorem valid3395 : plan3395.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3396 : plan3396.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3397 : plan3397.Valid := valid_step _ _ _ valid1582 (by decide +kernel)

theorem valid3398 : plan3398.Valid := valid_step _ _ _ valid1569 (by decide +kernel)

theorem valid3399 : plan3399.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3400 : plan3400.Valid := valid_step _ _ _ valid1571 (by decide +kernel)

theorem valid3401 : plan3401.Valid := valid_step _ _ _ valid1572 (by decide +kernel)














































































































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













theorem valid5575 : plan5575.Valid := valid_step _ _ _ valid3381 (by decide +kernel)

theorem valid5576 : plan5576.Valid := valid_step _ _ _ valid3382 (by decide +kernel)

theorem valid5577 : plan5577.Valid := valid_step _ _ _ valid3383 (by decide +kernel)

theorem valid5578 : plan5578.Valid := valid_step _ _ _ valid3384 (by decide +kernel)

theorem valid5579 : plan5579.Valid := valid_step _ _ _ valid3385 (by decide +kernel)

theorem valid5580 : plan5580.Valid := valid_step _ _ _ valid3386 (by decide +kernel)

theorem valid5581 : plan5581.Valid := valid_step _ _ _ valid3387 (by decide +kernel)

theorem valid5582 : plan5582.Valid := valid_step _ _ _ valid3388 (by decide +kernel)

theorem valid5583 : plan5583.Valid := valid_step _ _ _ valid3389 (by decide +kernel)

theorem valid5584 : plan5584.Valid := valid_step _ _ _ valid3390 (by decide +kernel)

theorem valid5585 : plan5585.Valid := valid_step _ _ _ valid3392 (by decide +kernel)

theorem valid5586 : plan5586.Valid := valid_step _ _ _ valid3393 (by decide +kernel)

theorem valid5587 : plan5587.Valid := valid_step _ _ _ valid3394 (by decide +kernel)

theorem valid5588 : plan5588.Valid := valid_step _ _ _ valid3395 (by decide +kernel)

theorem valid5589 : plan5589.Valid := valid_step _ _ _ valid3396 (by decide +kernel)

theorem valid5590 : plan5590.Valid := valid_step _ _ _ valid3397 (by decide +kernel)

theorem valid5591 : plan5591.Valid := valid_step _ _ _ valid3398 (by decide +kernel)

theorem valid5592 : plan5592.Valid := valid_step _ _ _ valid3399 (by decide +kernel)

theorem valid5593 : plan5593.Valid := valid_step _ _ _ valid3400 (by decide +kernel)

theorem valid5594 : plan5594.Valid := valid_step _ _ _ valid3401 (by decide +kernel)












































































































































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











































































































theorem valid6870 : plan6870.Valid := valid_step _ _ _ valid5575 (by decide +kernel)

theorem valid6871 : plan6871.Valid := valid_step _ _ _ valid5576 (by decide +kernel)

theorem valid6872 : plan6872.Valid := valid_step _ _ _ valid5577 (by decide +kernel)

theorem valid6873 : plan6873.Valid := valid_step _ _ _ valid5578 (by decide +kernel)

theorem valid6874 : plan6874.Valid := valid_step _ _ _ valid5579 (by decide +kernel)

theorem valid6875 : plan6875.Valid := valid_step _ _ _ valid5580 (by decide +kernel)

theorem valid6876 : plan6876.Valid := valid_step _ _ _ valid5581 (by decide +kernel)

theorem valid6877 : plan6877.Valid := valid_step _ _ _ valid5582 (by decide +kernel)

theorem valid6878 : plan6878.Valid := valid_step _ _ _ valid5583 (by decide +kernel)

theorem valid6879 : plan6879.Valid := valid_step _ _ _ valid5584 (by decide +kernel)

theorem valid6880 : plan6880.Valid := valid_step _ _ _ valid5585 (by decide +kernel)

theorem valid6881 : plan6881.Valid := valid_step _ _ _ valid5586 (by decide +kernel)

theorem valid6882 : plan6882.Valid := valid_step _ _ _ valid5587 (by decide +kernel)

theorem valid6883 : plan6883.Valid := valid_step _ _ _ valid5588 (by decide +kernel)

theorem valid6884 : plan6884.Valid := valid_step _ _ _ valid5589 (by decide +kernel)

theorem valid6885 : plan6885.Valid := valid_step _ _ _ valid5590 (by decide +kernel)

theorem valid6886 : plan6886.Valid := valid_step _ _ _ valid5591 (by decide +kernel)

theorem valid6887 : plan6887.Valid := valid_step _ _ _ valid5592 (by decide +kernel)

theorem valid6888 : plan6888.Valid := valid_step _ _ _ valid5593 (by decide +kernel)

theorem valid6889 : plan6889.Valid := valid_step _ _ _ valid5594 (by decide +kernel)














































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











































































theorem valid6566 : plan6566.Valid := valid_step _ _ _ valid5468 (by decide +kernel)

theorem valid6567 : plan6567.Valid := valid_step _ _ _ valid5469 (by decide +kernel)

theorem valid6568 : plan6568.Valid := valid_step _ _ _ valid5470 (by decide +kernel)

theorem valid6569 : plan6569.Valid := valid_step _ _ _ valid5471 (by decide +kernel)














































































































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
theorem t6_572choices : plan6566.choices=[2,2,5,3,10,7].map (options 6 3) := by rfl


theorem t6_572part0 : t6_572jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_572part1 : t6_572jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_572part2 : t6_572jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_572frontier : t6_572root.frontier 1=t6_572jobs := by rfl
theorem t6_572all : t6_572jobs.all (Job.check tree)=true := by
  simp only [t6_572jobs,List.all_append,List.all_nil,t6_572part0,t6_572part1,t6_572part2,Bool.and_self]
theorem t6_572checked : Checked tree [2,2,5,3,10,7] := by
  refine ⟨plan6566,valid6566,t6_572choices,?_⟩
  exact check_of_frontier tree 1 t6_572root t6_572jobs t6_572frontier t6_572all
theorem t6_573choices : plan6567.choices=[2,2,5,3,10,10].map (options 6 3) := by rfl


theorem t6_573part0 : t6_573jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_573frontier : t6_573root.frontier 0=t6_573jobs := by rfl
theorem t6_573all : t6_573jobs.all (Job.check tree)=true := by
  simp only [t6_573jobs,List.all_append,List.all_nil,t6_573part0,Bool.and_self]
theorem t6_573checked : Checked tree [2,2,5,3,10,10] := by
  refine ⟨plan6567,valid6567,t6_573choices,?_⟩
  exact check_of_frontier tree 0 t6_573root t6_573jobs t6_573frontier t6_573all
theorem t6_574choices : plan6568.choices=[2,2,5,5,3,7].map (options 6 3) := by rfl


theorem t6_574part0 : t6_574jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_574frontier : t6_574root.frontier 0=t6_574jobs := by rfl
theorem t6_574all : t6_574jobs.all (Job.check tree)=true := by
  simp only [t6_574jobs,List.all_append,List.all_nil,t6_574part0,Bool.and_self]
theorem t6_574checked : Checked tree [2,2,5,5,3,7] := by
  refine ⟨plan6568,valid6568,t6_574choices,?_⟩
  exact check_of_frontier tree 0 t6_574root t6_574jobs t6_574frontier t6_574all
theorem t6_575choices : plan6870.choices=[2,2,5,5,6,7].map (options 6 4) := by rfl


theorem t6_575part0 : t6_575jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_575frontier : t6_575root.frontier 0=t6_575jobs := by rfl
theorem t6_575all : t6_575jobs.all (Job.check tree)=true := by
  simp only [t6_575jobs,List.all_append,List.all_nil,t6_575part0,Bool.and_self]
theorem t6_575checked : Checked tree [2,2,5,5,6,7] := by
  refine ⟨plan6870,valid6870,t6_575choices,?_⟩
  exact check_of_frontier tree 0 t6_575root t6_575jobs t6_575frontier t6_575all
theorem t6_576choices : plan6871.choices=[2,2,5,5,7,7].map (options 6 4) := by rfl


theorem t6_576part0 : t6_576jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_576frontier : t6_576root.frontier 0=t6_576jobs := by rfl
theorem t6_576all : t6_576jobs.all (Job.check tree)=true := by
  simp only [t6_576jobs,List.all_append,List.all_nil,t6_576part0,Bool.and_self]
theorem t6_576checked : Checked tree [2,2,5,5,7,7] := by
  refine ⟨plan6871,valid6871,t6_576choices,?_⟩
  exact check_of_frontier tree 0 t6_576root t6_576jobs t6_576frontier t6_576all
theorem t6_577choices : plan6872.choices=[2,2,5,5,10,7].map (options 6 4) := by rfl


theorem t6_577part0 : t6_577jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_577frontier : t6_577root.frontier 0=t6_577jobs := by rfl
theorem t6_577all : t6_577jobs.all (Job.check tree)=true := by
  simp only [t6_577jobs,List.all_append,List.all_nil,t6_577part0,Bool.and_self]
theorem t6_577checked : Checked tree [2,2,5,5,10,7] := by
  refine ⟨plan6872,valid6872,t6_577choices,?_⟩
  exact check_of_frontier tree 0 t6_577root t6_577jobs t6_577frontier t6_577all
theorem t6_578choices : plan6873.choices=[2,2,5,6,6,6].map (options 6 4) := by rfl


theorem t6_578part0 : t6_578jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_578frontier : t6_578root.frontier 0=t6_578jobs := by rfl
theorem t6_578all : t6_578jobs.all (Job.check tree)=true := by
  simp only [t6_578jobs,List.all_append,List.all_nil,t6_578part0,Bool.and_self]
theorem t6_578checked : Checked tree [2,2,5,6,6,6] := by
  refine ⟨plan6873,valid6873,t6_578choices,?_⟩
  exact check_of_frontier tree 0 t6_578root t6_578jobs t6_578frontier t6_578all
theorem t6_579choices : plan6874.choices=[2,2,5,6,6,7].map (options 6 4) := by rfl


theorem t6_579part0 : t6_579jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_579frontier : t6_579root.frontier 0=t6_579jobs := by rfl
theorem t6_579all : t6_579jobs.all (Job.check tree)=true := by
  simp only [t6_579jobs,List.all_append,List.all_nil,t6_579part0,Bool.and_self]
theorem t6_579checked : Checked tree [2,2,5,6,6,7] := by
  refine ⟨plan6874,valid6874,t6_579choices,?_⟩
  exact check_of_frontier tree 0 t6_579root t6_579jobs t6_579frontier t6_579all
theorem t6_580choices : plan6875.choices=[2,2,5,6,6,10].map (options 6 4) := by rfl


theorem t6_580part0 : t6_580jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_580frontier : t6_580root.frontier 0=t6_580jobs := by rfl
theorem t6_580all : t6_580jobs.all (Job.check tree)=true := by
  simp only [t6_580jobs,List.all_append,List.all_nil,t6_580part0,Bool.and_self]
theorem t6_580checked : Checked tree [2,2,5,6,6,10] := by
  refine ⟨plan6875,valid6875,t6_580choices,?_⟩
  exact check_of_frontier tree 0 t6_580root t6_580jobs t6_580frontier t6_580all
theorem t6_581choices : plan6876.choices=[2,2,5,6,7,7].map (options 6 4) := by rfl


theorem t6_581part0 : t6_581jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_581part1 : t6_581jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_581frontier : t6_581root.frontier 1=t6_581jobs := by rfl
theorem t6_581all : t6_581jobs.all (Job.check tree)=true := by
  simp only [t6_581jobs,List.all_append,List.all_nil,t6_581part0,t6_581part1,Bool.and_self]
theorem t6_581checked : Checked tree [2,2,5,6,7,7] := by
  refine ⟨plan6876,valid6876,t6_581choices,?_⟩
  exact check_of_frontier tree 1 t6_581root t6_581jobs t6_581frontier t6_581all
theorem t6_582choices : plan6877.choices=[2,2,5,6,10,7].map (options 6 4) := by rfl


theorem t6_582part0 : t6_582jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_582part1 : t6_582jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_582frontier : t6_582root.frontier 1=t6_582jobs := by rfl
theorem t6_582all : t6_582jobs.all (Job.check tree)=true := by
  simp only [t6_582jobs,List.all_append,List.all_nil,t6_582part0,t6_582part1,Bool.and_self]
theorem t6_582checked : Checked tree [2,2,5,6,10,7] := by
  refine ⟨plan6877,valid6877,t6_582choices,?_⟩
  exact check_of_frontier tree 1 t6_582root t6_582jobs t6_582frontier t6_582all
theorem t6_583choices : plan6878.choices=[2,2,5,6,10,10].map (options 6 4) := by rfl


theorem t6_583part0 : t6_583jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_583frontier : t6_583root.frontier 0=t6_583jobs := by rfl
theorem t6_583all : t6_583jobs.all (Job.check tree)=true := by
  simp only [t6_583jobs,List.all_append,List.all_nil,t6_583part0,Bool.and_self]
theorem t6_583checked : Checked tree [2,2,5,6,10,10] := by
  refine ⟨plan6878,valid6878,t6_583choices,?_⟩
  exact check_of_frontier tree 0 t6_583root t6_583jobs t6_583frontier t6_583all
theorem t6_584choices : plan6879.choices=[2,2,5,7,7,7].map (options 6 4) := by rfl


theorem t6_584part0 : t6_584jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_584part1 : t6_584jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_584frontier : t6_584root.frontier 1=t6_584jobs := by rfl
theorem t6_584all : t6_584jobs.all (Job.check tree)=true := by
  simp only [t6_584jobs,List.all_append,List.all_nil,t6_584part0,t6_584part1,Bool.and_self]
theorem t6_584checked : Checked tree [2,2,5,7,7,7] := by
  refine ⟨plan6879,valid6879,t6_584choices,?_⟩
  exact check_of_frontier tree 1 t6_584root t6_584jobs t6_584frontier t6_584all
theorem t6_585choices : plan6569.choices=[2,2,5,9,3,7].map (options 6 3) := by rfl


theorem t6_585part0 : t6_585jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_585frontier : t6_585root.frontier 0=t6_585jobs := by rfl
theorem t6_585all : t6_585jobs.all (Job.check tree)=true := by
  simp only [t6_585jobs,List.all_append,List.all_nil,t6_585part0,Bool.and_self]
theorem t6_585checked : Checked tree [2,2,5,9,3,7] := by
  refine ⟨plan6569,valid6569,t6_585choices,?_⟩
  exact check_of_frontier tree 0 t6_585root t6_585jobs t6_585frontier t6_585all
theorem t6_586choices : plan6880.choices=[2,2,5,9,6,7].map (options 6 4) := by rfl


theorem t6_586part0 : t6_586jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_586frontier : t6_586root.frontier 0=t6_586jobs := by rfl
theorem t6_586all : t6_586jobs.all (Job.check tree)=true := by
  simp only [t6_586jobs,List.all_append,List.all_nil,t6_586part0,Bool.and_self]
theorem t6_586checked : Checked tree [2,2,5,9,6,7] := by
  refine ⟨plan6880,valid6880,t6_586choices,?_⟩
  exact check_of_frontier tree 0 t6_586root t6_586jobs t6_586frontier t6_586all
theorem t6_587choices : plan6881.choices=[2,2,5,9,7,7].map (options 6 4) := by rfl


theorem t6_587part0 : t6_587jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_587frontier : t6_587root.frontier 0=t6_587jobs := by rfl
theorem t6_587all : t6_587jobs.all (Job.check tree)=true := by
  simp only [t6_587jobs,List.all_append,List.all_nil,t6_587part0,Bool.and_self]
theorem t6_587checked : Checked tree [2,2,5,9,7,7] := by
  refine ⟨plan6881,valid6881,t6_587choices,?_⟩
  exact check_of_frontier tree 0 t6_587root t6_587jobs t6_587frontier t6_587all
theorem t6_588choices : plan6882.choices=[2,2,5,9,10,7].map (options 6 4) := by rfl


theorem t6_588part0 : t6_588jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_588frontier : t6_588root.frontier 0=t6_588jobs := by rfl
theorem t6_588all : t6_588jobs.all (Job.check tree)=true := by
  simp only [t6_588jobs,List.all_append,List.all_nil,t6_588part0,Bool.and_self]
theorem t6_588checked : Checked tree [2,2,5,9,10,7] := by
  refine ⟨plan6882,valid6882,t6_588choices,?_⟩
  exact check_of_frontier tree 0 t6_588root t6_588jobs t6_588frontier t6_588all
theorem t6_589choices : plan6883.choices=[2,2,5,10,7,7].map (options 6 4) := by rfl


theorem t6_589part0 : t6_589jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_589part1 : t6_589jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_589frontier : t6_589root.frontier 1=t6_589jobs := by rfl
theorem t6_589all : t6_589jobs.all (Job.check tree)=true := by
  simp only [t6_589jobs,List.all_append,List.all_nil,t6_589part0,t6_589part1,Bool.and_self]
theorem t6_589checked : Checked tree [2,2,5,10,7,7] := by
  refine ⟨plan6883,valid6883,t6_589choices,?_⟩
  exact check_of_frontier tree 1 t6_589root t6_589jobs t6_589frontier t6_589all
theorem t6_590choices : plan6884.choices=[2,2,5,10,10,7].map (options 6 4) := by rfl


theorem t6_590part0 : t6_590jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_590frontier : t6_590root.frontier 0=t6_590jobs := by rfl
theorem t6_590all : t6_590jobs.all (Job.check tree)=true := by
  simp only [t6_590jobs,List.all_append,List.all_nil,t6_590part0,Bool.and_self]
theorem t6_590checked : Checked tree [2,2,5,10,10,7] := by
  refine ⟨plan6884,valid6884,t6_590choices,?_⟩
  exact check_of_frontier tree 0 t6_590root t6_590jobs t6_590frontier t6_590all
theorem t6_591choices : plan6885.choices=[2,2,5,10,10,10].map (options 6 4) := by rfl


theorem t6_591part0 : t6_591jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_591frontier : t6_591root.frontier 0=t6_591jobs := by rfl
theorem t6_591all : t6_591jobs.all (Job.check tree)=true := by
  simp only [t6_591jobs,List.all_append,List.all_nil,t6_591part0,Bool.and_self]
theorem t6_591checked : Checked tree [2,2,5,10,10,10] := by
  refine ⟨plan6885,valid6885,t6_591choices,?_⟩
  exact check_of_frontier tree 0 t6_591root t6_591jobs t6_591frontier t6_591all
theorem t6_592choices : plan6886.choices=[2,2,6,6,6,6].map (options 6 4) := by rfl


theorem t6_592part0 : t6_592jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_592frontier : t6_592root.frontier 0=t6_592jobs := by rfl
theorem t6_592all : t6_592jobs.all (Job.check tree)=true := by
  simp only [t6_592jobs,List.all_append,List.all_nil,t6_592part0,Bool.and_self]
theorem t6_592checked : Checked tree [2,2,6,6,6,6] := by
  refine ⟨plan6886,valid6886,t6_592choices,?_⟩
  exact check_of_frontier tree 0 t6_592root t6_592jobs t6_592frontier t6_592all
theorem t6_593choices : plan6887.choices=[2,2,6,6,6,7].map (options 6 4) := by rfl


theorem t6_593part0 : t6_593jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_593frontier : t6_593root.frontier 0=t6_593jobs := by rfl
theorem t6_593all : t6_593jobs.all (Job.check tree)=true := by
  simp only [t6_593jobs,List.all_append,List.all_nil,t6_593part0,Bool.and_self]
theorem t6_593checked : Checked tree [2,2,6,6,6,7] := by
  refine ⟨plan6887,valid6887,t6_593choices,?_⟩
  exact check_of_frontier tree 0 t6_593root t6_593jobs t6_593frontier t6_593all
theorem t6_594choices : plan6888.choices=[2,2,6,6,6,10].map (options 6 4) := by rfl


theorem t6_594part0 : t6_594jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_594frontier : t6_594root.frontier 0=t6_594jobs := by rfl
theorem t6_594all : t6_594jobs.all (Job.check tree)=true := by
  simp only [t6_594jobs,List.all_append,List.all_nil,t6_594part0,Bool.and_self]
theorem t6_594checked : Checked tree [2,2,6,6,6,10] := by
  refine ⟨plan6888,valid6888,t6_594choices,?_⟩
  exact check_of_frontier tree 0 t6_594root t6_594jobs t6_594frontier t6_594all
theorem t6_595choices : plan6889.choices=[2,2,6,6,7,7].map (options 6 4) := by rfl


theorem t6_595part0 : t6_595jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_595part1 : t6_595jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_595frontier : t6_595root.frontier 1=t6_595jobs := by rfl
theorem t6_595all : t6_595jobs.all (Job.check tree)=true := by
  simp only [t6_595jobs,List.all_append,List.all_nil,t6_595part0,t6_595part1,Bool.and_self]
theorem t6_595checked : Checked tree [2,2,6,6,7,7] := by
  refine ⟨plan6889,valid6889,t6_595choices,?_⟩
  exact check_of_frontier tree 1 t6_595root t6_595jobs t6_595frontier t6_595all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks065 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_583checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_584checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_585checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_586checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_587checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_588checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_572checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_589checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_590checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_591checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_592checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_593checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_594checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_595checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_573checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_574checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_575checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_576checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_577checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_578checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_579checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_580checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_581checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_582checked⟩
