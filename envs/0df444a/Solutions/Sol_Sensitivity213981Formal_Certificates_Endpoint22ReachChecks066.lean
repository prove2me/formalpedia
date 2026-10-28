-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks066
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:14:27.302317+00:00
-- url     : https://prove2.me/submissions/87206ebb-690f-4365-b05b-60a957de06e2

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
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











































theorem valid118 : plan118.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid123 : plan123.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid125 : plan125.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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

























































































































theorem valid541 : plan541.Valid := valid_step _ _ _ valid118 (by decide +kernel)









theorem valid546 : plan546.Valid := valid_step _ _ _ valid123 (by decide +kernel)

theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid548 : plan548.Valid := valid_step _ _ _ valid125 (by decide +kernel)





















theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)



















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







































































































































theorem valid1508 : plan1508.Valid := valid_step _ _ _ valid541 (by decide +kernel)















theorem valid1516 : plan1516.Valid := valid_step _ _ _ valid546 (by decide +kernel)

theorem valid1517 : plan1517.Valid := valid_step _ _ _ valid547 (by decide +kernel)

theorem valid1518 : plan1518.Valid := valid_step _ _ _ valid548 (by decide +kernel)



























theorem valid1532 : plan1532.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1533 : plan1533.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1534 : plan1534.Valid := valid_step _ _ _ valid561 (by decide +kernel)




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





































































































































































theorem valid3251 : plan3251.Valid := valid_step _ _ _ valid1508 (by decide +kernel)


























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









































































theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)

theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)









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





























theorem valid3279 : plan3279.Valid := valid_step _ _ _ valid1516 (by decide +kernel)

theorem valid3280 : plan3280.Valid := valid_step _ _ _ valid1517 (by decide +kernel)

theorem valid3281 : plan3281.Valid := valid_step _ _ _ valid1518 (by decide +kernel)

















































































































theorem valid3338 : plan3338.Valid := valid_step _ _ _ valid1532 (by decide +kernel)

theorem valid3339 : plan3339.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3340 : plan3340.Valid := valid_step _ _ _ valid1534 (by decide +kernel)








































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





















































































































































theorem valid5355 : plan5355.Valid := valid_step _ _ _ valid3251 (by decide +kernel)










































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



























theorem valid5390 : plan5390.Valid := valid_step _ _ _ valid3279 (by decide +kernel)

theorem valid5391 : plan5391.Valid := valid_step _ _ _ valid3280 (by decide +kernel)

theorem valid5392 : plan5392.Valid := valid_step _ _ _ valid3281 (by decide +kernel)
































































































































































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

































































































































theorem valid6305 : plan6305.Valid := valid_step _ _ _ valid5355 (by decide +kernel)






























































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



















































































theorem valid3402 : plan3402.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3403 : plan3403.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3404 : plan3404.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3405 : plan3405.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3406 : plan3406.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3407 : plan3407.Valid := valid_step _ _ _ valid1582 (by decide +kernel)

theorem valid3408 : plan3408.Valid := valid_step _ _ _ valid1575 (by decide +kernel)
































































































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

theorem valid5473 : plan5473.Valid := valid_step _ _ _ valid3338 (by decide +kernel)

theorem valid5474 : plan5474.Valid := valid_step _ _ _ valid3339 (by decide +kernel)

theorem valid5475 : plan5475.Valid := valid_step _ _ _ valid3340 (by decide +kernel)


























































































































































































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





















































theorem valid5595 : plan5595.Valid := valid_step _ _ _ valid3402 (by decide +kernel)

theorem valid5596 : plan5596.Valid := valid_step _ _ _ valid3403 (by decide +kernel)

theorem valid5597 : plan5597.Valid := valid_step _ _ _ valid3404 (by decide +kernel)

theorem valid5598 : plan5598.Valid := valid_step _ _ _ valid3405 (by decide +kernel)

theorem valid5599 : plan5599.Valid := valid_step _ _ _ valid3406 (by decide +kernel)

theorem valid5600 : plan5600.Valid := valid_step _ _ _ valid3407 (by decide +kernel)

theorem valid5601 : plan5601.Valid := valid_step _ _ _ valid3408 (by decide +kernel)






























































































































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





























































































theorem valid6383 : plan6383.Valid := valid_step _ _ _ valid5390 (by decide +kernel)

theorem valid6384 : plan6384.Valid := valid_step _ _ _ valid5391 (by decide +kernel)

theorem valid6385 : plan6385.Valid := valid_step _ _ _ valid5392 (by decide +kernel)






























































































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



















































































































































theorem valid6890 : plan6890.Valid := valid_step _ _ _ valid5595 (by decide +kernel)

theorem valid6891 : plan6891.Valid := valid_step _ _ _ valid5596 (by decide +kernel)

theorem valid6892 : plan6892.Valid := valid_step _ _ _ valid5597 (by decide +kernel)

theorem valid6893 : plan6893.Valid := valid_step _ _ _ valid5598 (by decide +kernel)

theorem valid6894 : plan6894.Valid := valid_step _ _ _ valid5599 (by decide +kernel)

theorem valid6895 : plan6895.Valid := valid_step _ _ _ valid5600 (by decide +kernel)

theorem valid6896 : plan6896.Valid := valid_step _ _ _ valid5601 (by decide +kernel)
































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



















































































theorem valid6570 : plan6570.Valid := valid_step _ _ _ valid5473 (by decide +kernel)

theorem valid6571 : plan6571.Valid := valid_step _ _ _ valid5474 (by decide +kernel)

theorem valid6572 : plan6572.Valid := valid_step _ _ _ valid5475 (by decide +kernel)








































































































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
theorem t6_596choices : plan6890.choices=[2,2,6,6,10,7].map (options 6 4) := by rfl


theorem t6_596part0 : t6_596jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_596part1 : t6_596jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_596frontier : t6_596root.frontier 3=t6_596jobs := by rfl
theorem t6_596all : t6_596jobs.all (Job.check tree)=true := by
  simp only [t6_596jobs,List.all_append,List.all_nil,t6_596part0,t6_596part1,Bool.and_self]
theorem t6_596checked : Checked tree [2,2,6,6,10,7] := by
  refine ⟨plan6890,valid6890,t6_596choices,?_⟩
  exact check_of_frontier tree 3 t6_596root t6_596jobs t6_596frontier t6_596all
theorem t6_597choices : plan6891.choices=[2,2,6,6,10,10].map (options 6 4) := by rfl


theorem t6_597part0 : t6_597jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_597frontier : t6_597root.frontier 0=t6_597jobs := by rfl
theorem t6_597all : t6_597jobs.all (Job.check tree)=true := by
  simp only [t6_597jobs,List.all_append,List.all_nil,t6_597part0,Bool.and_self]
theorem t6_597checked : Checked tree [2,2,6,6,10,10] := by
  refine ⟨plan6891,valid6891,t6_597choices,?_⟩
  exact check_of_frontier tree 0 t6_597root t6_597jobs t6_597frontier t6_597all
theorem t6_598choices : plan6892.choices=[2,2,6,7,7,7].map (options 6 4) := by rfl


theorem t6_598part0 : t6_598jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_598part1 : t6_598jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_598part2 : t6_598jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_598frontier : t6_598root.frontier 1=t6_598jobs := by rfl
theorem t6_598all : t6_598jobs.all (Job.check tree)=true := by
  simp only [t6_598jobs,List.all_append,List.all_nil,t6_598part0,t6_598part1,t6_598part2,Bool.and_self]
theorem t6_598checked : Checked tree [2,2,6,7,7,7] := by
  refine ⟨plan6892,valid6892,t6_598choices,?_⟩
  exact check_of_frontier tree 1 t6_598root t6_598jobs t6_598frontier t6_598all
theorem t6_599choices : plan6893.choices=[2,2,6,10,7,7].map (options 6 4) := by rfl


theorem t6_599part0 : t6_599jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_599part1 : t6_599jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_599part2 : t6_599jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_599part3 : t6_599jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_599frontier : t6_599root.frontier 3=t6_599jobs := by rfl
theorem t6_599all : t6_599jobs.all (Job.check tree)=true := by
  simp only [t6_599jobs,List.all_append,List.all_nil,t6_599part0,t6_599part1,t6_599part2,t6_599part3,Bool.and_self]
theorem t6_599checked : Checked tree [2,2,6,10,7,7] := by
  refine ⟨plan6893,valid6893,t6_599choices,?_⟩
  exact check_of_frontier tree 3 t6_599root t6_599jobs t6_599frontier t6_599all
theorem t6_600choices : plan6894.choices=[2,2,6,10,10,7].map (options 6 4) := by rfl


theorem t6_600part0 : t6_600jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_600part1 : t6_600jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_600frontier : t6_600root.frontier 3=t6_600jobs := by rfl
theorem t6_600all : t6_600jobs.all (Job.check tree)=true := by
  simp only [t6_600jobs,List.all_append,List.all_nil,t6_600part0,t6_600part1,Bool.and_self]
theorem t6_600checked : Checked tree [2,2,6,10,10,7] := by
  refine ⟨plan6894,valid6894,t6_600choices,?_⟩
  exact check_of_frontier tree 3 t6_600root t6_600jobs t6_600frontier t6_600all
theorem t6_601choices : plan6895.choices=[2,2,6,10,10,10].map (options 6 4) := by rfl


theorem t6_601part0 : t6_601jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_601frontier : t6_601root.frontier 0=t6_601jobs := by rfl
theorem t6_601all : t6_601jobs.all (Job.check tree)=true := by
  simp only [t6_601jobs,List.all_append,List.all_nil,t6_601part0,Bool.and_self]
theorem t6_601checked : Checked tree [2,2,6,10,10,10] := by
  refine ⟨plan6895,valid6895,t6_601choices,?_⟩
  exact check_of_frontier tree 0 t6_601root t6_601jobs t6_601frontier t6_601all
theorem t6_602choices : plan6896.choices=[2,2,7,7,7,7].map (options 6 4) := by rfl


theorem t6_602part0 : t6_602jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_602part1 : t6_602jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_602frontier : t6_602root.frontier 1=t6_602jobs := by rfl
theorem t6_602all : t6_602jobs.all (Job.check tree)=true := by
  simp only [t6_602jobs,List.all_append,List.all_nil,t6_602part0,t6_602part1,Bool.and_self]
theorem t6_602checked : Checked tree [2,2,7,7,7,7] := by
  refine ⟨plan6896,valid6896,t6_602choices,?_⟩
  exact check_of_frontier tree 1 t6_602root t6_602jobs t6_602frontier t6_602all
theorem t6_603choices : plan6305.choices=[2,2,9,3,3,3].map (options 6 1) := by rfl


theorem t6_603part0 : t6_603jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_603frontier : t6_603root.frontier 0=t6_603jobs := by rfl
theorem t6_603all : t6_603jobs.all (Job.check tree)=true := by
  simp only [t6_603jobs,List.all_append,List.all_nil,t6_603part0,Bool.and_self]
theorem t6_603checked : Checked tree [2,2,9,3,3,3] := by
  refine ⟨plan6305,valid6305,t6_603choices,?_⟩
  exact check_of_frontier tree 0 t6_603root t6_603jobs t6_603frontier t6_603all
theorem t6_604choices : plan6383.choices=[2,2,9,3,3,6].map (options 6 2) := by rfl


theorem t6_604part0 : t6_604jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_604frontier : t6_604root.frontier 0=t6_604jobs := by rfl
theorem t6_604all : t6_604jobs.all (Job.check tree)=true := by
  simp only [t6_604jobs,List.all_append,List.all_nil,t6_604part0,Bool.and_self]
theorem t6_604checked : Checked tree [2,2,9,3,3,6] := by
  refine ⟨plan6383,valid6383,t6_604choices,?_⟩
  exact check_of_frontier tree 0 t6_604root t6_604jobs t6_604frontier t6_604all
theorem t6_605choices : plan6384.choices=[2,2,9,3,3,7].map (options 6 2) := by rfl


theorem t6_605part0 : t6_605jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_605part1 : t6_605jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_605frontier : t6_605root.frontier 1=t6_605jobs := by rfl
theorem t6_605all : t6_605jobs.all (Job.check tree)=true := by
  simp only [t6_605jobs,List.all_append,List.all_nil,t6_605part0,t6_605part1,Bool.and_self]
theorem t6_605checked : Checked tree [2,2,9,3,3,7] := by
  refine ⟨plan6384,valid6384,t6_605choices,?_⟩
  exact check_of_frontier tree 1 t6_605root t6_605jobs t6_605frontier t6_605all
theorem t6_606choices : plan6385.choices=[2,2,9,3,3,10].map (options 6 2) := by rfl


theorem t6_606part0 : t6_606jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_606frontier : t6_606root.frontier 0=t6_606jobs := by rfl
theorem t6_606all : t6_606jobs.all (Job.check tree)=true := by
  simp only [t6_606jobs,List.all_append,List.all_nil,t6_606part0,Bool.and_self]
theorem t6_606checked : Checked tree [2,2,9,3,3,10] := by
  refine ⟨plan6385,valid6385,t6_606choices,?_⟩
  exact check_of_frontier tree 0 t6_606root t6_606jobs t6_606frontier t6_606all
theorem t6_607choices : plan6570.choices=[2,2,9,3,6,6].map (options 6 3) := by rfl


theorem t6_607part0 : t6_607jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_607frontier : t6_607root.frontier 0=t6_607jobs := by rfl
theorem t6_607all : t6_607jobs.all (Job.check tree)=true := by
  simp only [t6_607jobs,List.all_append,List.all_nil,t6_607part0,Bool.and_self]
theorem t6_607checked : Checked tree [2,2,9,3,6,6] := by
  refine ⟨plan6570,valid6570,t6_607choices,?_⟩
  exact check_of_frontier tree 0 t6_607root t6_607jobs t6_607frontier t6_607all
theorem t6_608choices : plan6571.choices=[2,2,9,3,6,7].map (options 6 3) := by rfl


theorem t6_608part0 : t6_608jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_608part1 : t6_608jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_608part2 : t6_608jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_608frontier : t6_608root.frontier 1=t6_608jobs := by rfl
theorem t6_608all : t6_608jobs.all (Job.check tree)=true := by
  simp only [t6_608jobs,List.all_append,List.all_nil,t6_608part0,t6_608part1,t6_608part2,Bool.and_self]
theorem t6_608checked : Checked tree [2,2,9,3,6,7] := by
  refine ⟨plan6571,valid6571,t6_608choices,?_⟩
  exact check_of_frontier tree 1 t6_608root t6_608jobs t6_608frontier t6_608all
theorem t6_609choices : plan6572.choices=[2,2,9,3,6,10].map (options 6 3) := by rfl


theorem t6_609part0 : t6_609jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_609frontier : t6_609root.frontier 0=t6_609jobs := by rfl
theorem t6_609all : t6_609jobs.all (Job.check tree)=true := by
  simp only [t6_609jobs,List.all_append,List.all_nil,t6_609part0,Bool.and_self]
theorem t6_609checked : Checked tree [2,2,9,3,6,10] := by
  refine ⟨plan6572,valid6572,t6_609choices,?_⟩
  exact check_of_frontier tree 0 t6_609root t6_609jobs t6_609frontier t6_609all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks066 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_599checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_600checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_601checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_602checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_603checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_604checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_605checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_606checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_607checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_608checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_609checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_596checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_597checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_598checked⟩
