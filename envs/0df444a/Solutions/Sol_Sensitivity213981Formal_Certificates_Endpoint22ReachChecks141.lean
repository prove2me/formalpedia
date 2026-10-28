-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks141
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:53:27.142543+00:00
-- url     : https://prove2.me/submissions/b603c825-6c4f-4062-96bd-0a57615420aa

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks141
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks141
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
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













































































































theorem valid5623 : plan5623.Valid := valid_step _ _ _ valid3361 (by decide +kernel)

theorem valid5624 : plan5624.Valid := valid_step _ _ _ valid3362 (by decide +kernel)

theorem valid5625 : plan5625.Valid := valid_step _ _ _ valid3363 (by decide +kernel)

theorem valid5626 : plan5626.Valid := valid_step _ _ _ valid3364 (by decide +kernel)

theorem valid5627 : plan5627.Valid := valid_step _ _ _ valid3365 (by decide +kernel)

theorem valid5628 : plan5628.Valid := valid_step _ _ _ valid3366 (by decide +kernel)

theorem valid5629 : plan5629.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5630 : plan5630.Valid := valid_step _ _ _ valid3368 (by decide +kernel)

theorem valid5631 : plan5631.Valid := valid_step _ _ _ valid3369 (by decide +kernel)


































































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



















theorem valid5770 : plan5770.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5771 : plan5771.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5772 : plan5772.Valid := valid_step _ _ _ valid3477 (by decide +kernel)








































































































































































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

theorem valid7105 : plan7105.Valid := valid_step _ _ _ valid5629 (by decide +kernel)

theorem valid7106 : plan7106.Valid := valid_step _ _ _ valid5630 (by decide +kernel)

theorem valid7107 : plan7107.Valid := valid_step _ _ _ valid5631 (by decide +kernel)


























































































































































































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





















































































































































































theorem valid7099 : plan7099.Valid := valid_step _ _ _ valid5623 (by decide +kernel)

theorem valid7100 : plan7100.Valid := valid_step _ _ _ valid5624 (by decide +kernel)

theorem valid7101 : plan7101.Valid := valid_step _ _ _ valid5625 (by decide +kernel)

theorem valid7102 : plan7102.Valid := valid_step _ _ _ valid5626 (by decide +kernel)

theorem valid7103 : plan7103.Valid := valid_step _ _ _ valid5627 (by decide +kernel)

theorem valid7104 : plan7104.Valid := valid_step _ _ _ valid5628 (by decide +kernel)
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

































































theorem valid7617 : plan7617.Valid := valid_step _ _ _ valid5770 (by decide +kernel)

theorem valid7618 : plan7618.Valid := valid_step _ _ _ valid5771 (by decide +kernel)

theorem valid7619 : plan7619.Valid := valid_step _ _ _ valid5772 (by decide +kernel)


























































































































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
theorem t6_1493choices : plan7099.choices=[8,3,3,6,6,7].map (options 6 4) := by rfl


theorem t6_1493part0 : t6_1493jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1493part1 : t6_1493jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1493frontier : t6_1493root.frontier 1=t6_1493jobs := by rfl
theorem t6_1493all : t6_1493jobs.all (Job.check tree)=true := by
  simp only [t6_1493jobs,List.all_append,List.all_nil,t6_1493part0,t6_1493part1,Bool.and_self]
theorem t6_1493checked : Checked tree [8,3,3,6,6,7] := by
  refine ⟨plan7099,valid7099,t6_1493choices,?_⟩
  exact check_of_frontier tree 1 t6_1493root t6_1493jobs t6_1493frontier t6_1493all
theorem t6_1494choices : plan7100.choices=[8,3,3,6,6,10].map (options 6 4) := by rfl


theorem t6_1494part0 : t6_1494jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1494frontier : t6_1494root.frontier 0=t6_1494jobs := by rfl
theorem t6_1494all : t6_1494jobs.all (Job.check tree)=true := by
  simp only [t6_1494jobs,List.all_append,List.all_nil,t6_1494part0,Bool.and_self]
theorem t6_1494checked : Checked tree [8,3,3,6,6,10] := by
  refine ⟨plan7100,valid7100,t6_1494choices,?_⟩
  exact check_of_frontier tree 0 t6_1494root t6_1494jobs t6_1494frontier t6_1494all
theorem t6_1495choices : plan7101.choices=[8,3,3,6,7,7].map (options 6 4) := by rfl


theorem t6_1495part0 : t6_1495jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1495part1 : t6_1495jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1495part2 : t6_1495jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1495frontier : t6_1495root.frontier 2=t6_1495jobs := by rfl
theorem t6_1495all : t6_1495jobs.all (Job.check tree)=true := by
  simp only [t6_1495jobs,List.all_append,List.all_nil,t6_1495part0,t6_1495part1,t6_1495part2,Bool.and_self]
theorem t6_1495checked : Checked tree [8,3,3,6,7,7] := by
  refine ⟨plan7101,valid7101,t6_1495choices,?_⟩
  exact check_of_frontier tree 2 t6_1495root t6_1495jobs t6_1495frontier t6_1495all
theorem t6_1496choices : plan7102.choices=[8,3,3,6,10,7].map (options 6 4) := by rfl


theorem t6_1496part0 : t6_1496jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1496part1 : t6_1496jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1496part2 : t6_1496jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1496frontier : t6_1496root.frontier 2=t6_1496jobs := by rfl
theorem t6_1496all : t6_1496jobs.all (Job.check tree)=true := by
  simp only [t6_1496jobs,List.all_append,List.all_nil,t6_1496part0,t6_1496part1,t6_1496part2,Bool.and_self]
theorem t6_1496checked : Checked tree [8,3,3,6,10,7] := by
  refine ⟨plan7102,valid7102,t6_1496choices,?_⟩
  exact check_of_frontier tree 2 t6_1496root t6_1496jobs t6_1496frontier t6_1496all
theorem t6_1497choices : plan7103.choices=[8,3,3,6,10,10].map (options 6 4) := by rfl


theorem t6_1497part0 : t6_1497jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1497frontier : t6_1497root.frontier 0=t6_1497jobs := by rfl
theorem t6_1497all : t6_1497jobs.all (Job.check tree)=true := by
  simp only [t6_1497jobs,List.all_append,List.all_nil,t6_1497part0,Bool.and_self]
theorem t6_1497checked : Checked tree [8,3,3,6,10,10] := by
  refine ⟨plan7103,valid7103,t6_1497choices,?_⟩
  exact check_of_frontier tree 0 t6_1497root t6_1497jobs t6_1497frontier t6_1497all
theorem t6_1498choices : plan7104.choices=[8,3,3,7,7,7].map (options 6 4) := by rfl


theorem t6_1498part0 : t6_1498jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1498part1 : t6_1498jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1498part2 : t6_1498jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1498frontier : t6_1498root.frontier 1=t6_1498jobs := by rfl
theorem t6_1498all : t6_1498jobs.all (Job.check tree)=true := by
  simp only [t6_1498jobs,List.all_append,List.all_nil,t6_1498part0,t6_1498part1,t6_1498part2,Bool.and_self]
theorem t6_1498checked : Checked tree [8,3,3,7,7,7] := by
  refine ⟨plan7104,valid7104,t6_1498choices,?_⟩
  exact check_of_frontier tree 1 t6_1498root t6_1498jobs t6_1498frontier t6_1498all
theorem t6_1499choices : plan7105.choices=[8,3,3,10,7,7].map (options 6 4) := by rfl


theorem t6_1499part0 : t6_1499jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1499part1 : t6_1499jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1499part2 : t6_1499jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1499frontier : t6_1499root.frontier 2=t6_1499jobs := by rfl
theorem t6_1499all : t6_1499jobs.all (Job.check tree)=true := by
  simp only [t6_1499jobs,List.all_append,List.all_nil,t6_1499part0,t6_1499part1,t6_1499part2,Bool.and_self]
theorem t6_1499checked : Checked tree [8,3,3,10,7,7] := by
  refine ⟨plan7105,valid7105,t6_1499choices,?_⟩
  exact check_of_frontier tree 2 t6_1499root t6_1499jobs t6_1499frontier t6_1499all
theorem t6_1500choices : plan7106.choices=[8,3,3,10,10,7].map (options 6 4) := by rfl


theorem t6_1500part0 : t6_1500jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1500part1 : t6_1500jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1500frontier : t6_1500root.frontier 1=t6_1500jobs := by rfl
theorem t6_1500all : t6_1500jobs.all (Job.check tree)=true := by
  simp only [t6_1500jobs,List.all_append,List.all_nil,t6_1500part0,t6_1500part1,Bool.and_self]
theorem t6_1500checked : Checked tree [8,3,3,10,10,7] := by
  refine ⟨plan7106,valid7106,t6_1500choices,?_⟩
  exact check_of_frontier tree 1 t6_1500root t6_1500jobs t6_1500frontier t6_1500all
theorem t6_1501choices : plan7107.choices=[8,3,3,10,10,10].map (options 6 4) := by rfl


theorem t6_1501part0 : t6_1501jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1501frontier : t6_1501root.frontier 0=t6_1501jobs := by rfl
theorem t6_1501all : t6_1501jobs.all (Job.check tree)=true := by
  simp only [t6_1501jobs,List.all_append,List.all_nil,t6_1501part0,Bool.and_self]
theorem t6_1501checked : Checked tree [8,3,3,10,10,10] := by
  refine ⟨plan7107,valid7107,t6_1501choices,?_⟩
  exact check_of_frontier tree 0 t6_1501root t6_1501jobs t6_1501frontier t6_1501all
theorem t6_1502choices : plan7617.choices=[8,3,6,6,6,6].map (options 6 5) := by rfl


theorem t6_1502part0 : t6_1502jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1502frontier : t6_1502root.frontier 0=t6_1502jobs := by rfl
theorem t6_1502all : t6_1502jobs.all (Job.check tree)=true := by
  simp only [t6_1502jobs,List.all_append,List.all_nil,t6_1502part0,Bool.and_self]
theorem t6_1502checked : Checked tree [8,3,6,6,6,6] := by
  refine ⟨plan7617,valid7617,t6_1502choices,?_⟩
  exact check_of_frontier tree 0 t6_1502root t6_1502jobs t6_1502frontier t6_1502all
theorem t6_1503choices : plan7618.choices=[8,3,6,6,6,7].map (options 6 5) := by rfl


theorem t6_1503part0 : t6_1503jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1503frontier : t6_1503root.frontier 0=t6_1503jobs := by rfl
theorem t6_1503all : t6_1503jobs.all (Job.check tree)=true := by
  simp only [t6_1503jobs,List.all_append,List.all_nil,t6_1503part0,Bool.and_self]
theorem t6_1503checked : Checked tree [8,3,6,6,6,7] := by
  refine ⟨plan7618,valid7618,t6_1503choices,?_⟩
  exact check_of_frontier tree 0 t6_1503root t6_1503jobs t6_1503frontier t6_1503all
theorem t6_1504choices : plan7619.choices=[8,3,6,6,6,10].map (options 6 5) := by rfl


theorem t6_1504part0 : t6_1504jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1504frontier : t6_1504root.frontier 0=t6_1504jobs := by rfl
theorem t6_1504all : t6_1504jobs.all (Job.check tree)=true := by
  simp only [t6_1504jobs,List.all_append,List.all_nil,t6_1504part0,Bool.and_self]
theorem t6_1504checked : Checked tree [8,3,6,6,6,10] := by
  refine ⟨plan7619,valid7619,t6_1504choices,?_⟩
  exact check_of_frontier tree 0 t6_1504root t6_1504jobs t6_1504frontier t6_1504all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks141 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1499checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1493checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1500checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1501checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1502checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1503checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1504checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1494checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1495checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1496checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1497checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1498checked⟩
