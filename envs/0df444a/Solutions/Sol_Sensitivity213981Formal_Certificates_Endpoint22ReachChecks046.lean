-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks046
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:07:02.417004+00:00
-- url     : https://prove2.me/submissions/bb4af2ca-d041-42fb-9e63-13c15d6efb55

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
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



























































































































































































theorem valid94 : plan94.Valid := valid_step _ _ _ valid0 (by decide +kernel)




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











theorem valid102 : plan102.Valid := valid_step _ _ _ valid0 (by decide +kernel)













theorem valid109 : plan109.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid111 : plan111.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid113 : plan113.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid114 : plan114.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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



























































































































































theorem valid462 : plan462.Valid := valid_step _ _ _ valid94 (by decide +kernel)




































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









theorem valid485 : plan485.Valid := valid_step _ _ _ valid102 (by decide +kernel)































































theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)











theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid524 : plan524.Valid := valid_step _ _ _ valid111 (by decide +kernel)











theorem valid530 : plan530.Valid := valid_step _ _ _ valid113 (by decide +kernel)

theorem valid531 : plan531.Valid := valid_step _ _ _ valid114 (by decide +kernel)

theorem valid532 : plan532.Valid := valid_step _ _ _ valid116 (by decide +kernel)

theorem valid533 : plan533.Valid := valid_step _ _ _ valid114 (by decide +kernel)









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

































































































theorem valid1297 : plan1297.Valid := valid_step _ _ _ valid462 (by decide +kernel)













































































theorem valid1336 : plan1336.Valid := valid_step _ _ _ valid485 (by decide +kernel)
















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















































































































































theorem valid2664 : plan2664.Valid := valid_step _ _ _ valid1297 (by decide +kernel)
















































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





























































































































theorem valid3999 : plan3999.Valid := valid_step _ _ _ valid2664 (by decide +kernel)


































































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





















































































































































theorem valid2859 : plan2859.Valid := valid_step _ _ _ valid1336 (by decide +kernel)










































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

theorem valid1441 : plan1441.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1442 : plan1442.Valid := valid_step _ _ _ valid524 (by decide +kernel)

theorem valid1443 : plan1443.Valid := valid_step _ _ _ valid517 (by decide +kernel)





































theorem valid1462 : plan1462.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1463 : plan1463.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1464 : plan1464.Valid := valid_step _ _ _ valid524 (by decide +kernel)





































theorem valid1483 : plan1483.Valid := valid_step _ _ _ valid530 (by decide +kernel)

theorem valid1484 : plan1484.Valid := valid_step _ _ _ valid531 (by decide +kernel)

theorem valid1485 : plan1485.Valid := valid_step _ _ _ valid532 (by decide +kernel)

theorem valid1486 : plan1486.Valid := valid_step _ _ _ valid533 (by decide +kernel)

theorem valid1487 : plan1487.Valid := valid_step _ _ _ valid538 (by decide +kernel)

theorem valid1488 : plan1488.Valid := valid_step _ _ _ valid539 (by decide +kernel)

theorem valid1489 : plan1489.Valid := valid_step _ _ _ valid533 (by decide +kernel)



























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























































theorem valid2908 : plan2908.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid2909 : plan2909.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid2910 : plan2910.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

theorem valid2911 : plan2911.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid2912 : plan2912.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid2913 : plan2913.Valid := valid_step _ _ _ valid1464 (by decide +kernel)






























































































































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



























































theorem valid4446 : plan4446.Valid := valid_step _ _ _ valid2859 (by decide +kernel)




































































































































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













































































































































































theorem valid4983 : plan4983.Valid := valid_step _ _ _ valid2908 (by decide +kernel)

theorem valid4984 : plan4984.Valid := valid_step _ _ _ valid2909 (by decide +kernel)

theorem valid4985 : plan4985.Valid := valid_step _ _ _ valid2910 (by decide +kernel)

theorem valid4986 : plan4986.Valid := valid_step _ _ _ valid2911 (by decide +kernel)

theorem valid4987 : plan4987.Valid := valid_step _ _ _ valid2912 (by decide +kernel)

theorem valid4988 : plan4988.Valid := valid_step _ _ _ valid2913 (by decide +kernel)








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











































theorem valid5302 : plan5302.Valid := valid_step _ _ _ valid3177 (by decide +kernel)

theorem valid5303 : plan5303.Valid := valid_step _ _ _ valid3178 (by decide +kernel)

theorem valid5304 : plan5304.Valid := valid_step _ _ _ valid3179 (by decide +kernel)

theorem valid5305 : plan5305.Valid := valid_step _ _ _ valid3180 (by decide +kernel)

theorem valid5306 : plan5306.Valid := valid_step _ _ _ valid3181 (by decide +kernel)

theorem valid5307 : plan5307.Valid := valid_step _ _ _ valid3182 (by decide +kernel)

theorem valid5308 : plan5308.Valid := valid_step _ _ _ valid3183 (by decide +kernel)

theorem valid5309 : plan5309.Valid := valid_step _ _ _ valid3184 (by decide +kernel)

theorem valid5310 : plan5310.Valid := valid_step _ _ _ valid3185 (by decide +kernel)

theorem valid5311 : plan5311.Valid := valid_step _ _ _ valid3186 (by decide +kernel)

theorem valid5312 : plan5312.Valid := valid_step _ _ _ valid3187 (by decide +kernel)
































































































































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
theorem t5_1623choices : plan4983.choices=[9,3,6,10,7].map (options 5 4) := by rfl


theorem t5_1623part0 : t5_1623jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1623part1 : t5_1623jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1623part2 : t5_1623jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1623part3 : t5_1623jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_1623part4 : t5_1623jobs4.all (Job.check tree)=true := by decide +kernel

theorem t5_1623frontier : t5_1623root.frontier 1=t5_1623jobs := by rfl
theorem t5_1623all : t5_1623jobs.all (Job.check tree)=true := by
  simp only [t5_1623jobs,List.all_append,List.all_nil,t5_1623part0,t5_1623part1,t5_1623part2,t5_1623part3,t5_1623part4,Bool.and_self]
theorem t5_1623checked : Checked tree [9,3,6,10,7] := by
  refine ⟨plan4983,valid4983,t5_1623choices,?_⟩
  exact check_of_frontier tree 1 t5_1623root t5_1623jobs t5_1623frontier t5_1623all
theorem t5_1624choices : plan4984.choices=[9,3,6,10,10].map (options 5 4) := by rfl


theorem t5_1624part0 : t5_1624jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1624part1 : t5_1624jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1624frontier : t5_1624root.frontier 1=t5_1624jobs := by rfl
theorem t5_1624all : t5_1624jobs.all (Job.check tree)=true := by
  simp only [t5_1624jobs,List.all_append,List.all_nil,t5_1624part0,t5_1624part1,Bool.and_self]
theorem t5_1624checked : Checked tree [9,3,6,10,10] := by
  refine ⟨plan4984,valid4984,t5_1624choices,?_⟩
  exact check_of_frontier tree 1 t5_1624root t5_1624jobs t5_1624frontier t5_1624all
theorem t5_1625choices : plan4985.choices=[9,3,7,7,7].map (options 5 4) := by rfl


theorem t5_1625part0 : t5_1625jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1625part1 : t5_1625jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1625frontier : t5_1625root.frontier 1=t5_1625jobs := by rfl
theorem t5_1625all : t5_1625jobs.all (Job.check tree)=true := by
  simp only [t5_1625jobs,List.all_append,List.all_nil,t5_1625part0,t5_1625part1,Bool.and_self]
theorem t5_1625checked : Checked tree [9,3,7,7,7] := by
  refine ⟨plan4985,valid4985,t5_1625choices,?_⟩
  exact check_of_frontier tree 1 t5_1625root t5_1625jobs t5_1625frontier t5_1625all
theorem t5_1626choices : plan4986.choices=[9,3,10,7,7].map (options 5 4) := by rfl


theorem t5_1626part0 : t5_1626jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1626part1 : t5_1626jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1626part2 : t5_1626jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1626frontier : t5_1626root.frontier 1=t5_1626jobs := by rfl
theorem t5_1626all : t5_1626jobs.all (Job.check tree)=true := by
  simp only [t5_1626jobs,List.all_append,List.all_nil,t5_1626part0,t5_1626part1,t5_1626part2,Bool.and_self]
theorem t5_1626checked : Checked tree [9,3,10,7,7] := by
  refine ⟨plan4986,valid4986,t5_1626choices,?_⟩
  exact check_of_frontier tree 1 t5_1626root t5_1626jobs t5_1626frontier t5_1626all
theorem t5_1627choices : plan4987.choices=[9,3,10,10,7].map (options 5 4) := by rfl


theorem t5_1627part0 : t5_1627jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1627part1 : t5_1627jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1627frontier : t5_1627root.frontier 1=t5_1627jobs := by rfl
theorem t5_1627all : t5_1627jobs.all (Job.check tree)=true := by
  simp only [t5_1627jobs,List.all_append,List.all_nil,t5_1627part0,t5_1627part1,Bool.and_self]
theorem t5_1627checked : Checked tree [9,3,10,10,7] := by
  refine ⟨plan4987,valid4987,t5_1627choices,?_⟩
  exact check_of_frontier tree 1 t5_1627root t5_1627jobs t5_1627frontier t5_1627all
theorem t5_1628choices : plan4988.choices=[9,3,10,10,10].map (options 5 4) := by rfl


theorem t5_1628part0 : t5_1628jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1628frontier : t5_1628root.frontier 0=t5_1628jobs := by rfl
theorem t5_1628all : t5_1628jobs.all (Job.check tree)=true := by
  simp only [t5_1628jobs,List.all_append,List.all_nil,t5_1628part0,Bool.and_self]
theorem t5_1628checked : Checked tree [9,3,10,10,10] := by
  refine ⟨plan4988,valid4988,t5_1628choices,?_⟩
  exact check_of_frontier tree 0 t5_1628root t5_1628jobs t5_1628frontier t5_1628all
theorem t5_1629choices : plan5302.choices=[9,6,6,6,6].map (options 5 5) := by rfl


theorem t5_1629part0 : t5_1629jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1629frontier : t5_1629root.frontier 0=t5_1629jobs := by rfl
theorem t5_1629all : t5_1629jobs.all (Job.check tree)=true := by
  simp only [t5_1629jobs,List.all_append,List.all_nil,t5_1629part0,Bool.and_self]
theorem t5_1629checked : Checked tree [9,6,6,6,6] := by
  refine ⟨plan5302,valid5302,t5_1629choices,?_⟩
  exact check_of_frontier tree 0 t5_1629root t5_1629jobs t5_1629frontier t5_1629all
theorem t5_1630choices : plan5303.choices=[9,6,6,6,7].map (options 5 5) := by rfl


theorem t5_1630part0 : t5_1630jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1630frontier : t5_1630root.frontier 0=t5_1630jobs := by rfl
theorem t5_1630all : t5_1630jobs.all (Job.check tree)=true := by
  simp only [t5_1630jobs,List.all_append,List.all_nil,t5_1630part0,Bool.and_self]
theorem t5_1630checked : Checked tree [9,6,6,6,7] := by
  refine ⟨plan5303,valid5303,t5_1630choices,?_⟩
  exact check_of_frontier tree 0 t5_1630root t5_1630jobs t5_1630frontier t5_1630all
theorem t5_1631choices : plan5304.choices=[9,6,6,6,10].map (options 5 5) := by rfl


theorem t5_1631part0 : t5_1631jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1631frontier : t5_1631root.frontier 0=t5_1631jobs := by rfl
theorem t5_1631all : t5_1631jobs.all (Job.check tree)=true := by
  simp only [t5_1631jobs,List.all_append,List.all_nil,t5_1631part0,Bool.and_self]
theorem t5_1631checked : Checked tree [9,6,6,6,10] := by
  refine ⟨plan5304,valid5304,t5_1631choices,?_⟩
  exact check_of_frontier tree 0 t5_1631root t5_1631jobs t5_1631frontier t5_1631all
theorem t5_1632choices : plan5305.choices=[9,6,6,7,7].map (options 5 5) := by rfl


theorem t5_1632part0 : t5_1632jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1632frontier : t5_1632root.frontier 0=t5_1632jobs := by rfl
theorem t5_1632all : t5_1632jobs.all (Job.check tree)=true := by
  simp only [t5_1632jobs,List.all_append,List.all_nil,t5_1632part0,Bool.and_self]
theorem t5_1632checked : Checked tree [9,6,6,7,7] := by
  refine ⟨plan5305,valid5305,t5_1632choices,?_⟩
  exact check_of_frontier tree 0 t5_1632root t5_1632jobs t5_1632frontier t5_1632all
theorem t5_1633choices : plan5306.choices=[9,6,6,10,7].map (options 5 5) := by rfl


theorem t5_1633part0 : t5_1633jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1633frontier : t5_1633root.frontier 0=t5_1633jobs := by rfl
theorem t5_1633all : t5_1633jobs.all (Job.check tree)=true := by
  simp only [t5_1633jobs,List.all_append,List.all_nil,t5_1633part0,Bool.and_self]
theorem t5_1633checked : Checked tree [9,6,6,10,7] := by
  refine ⟨plan5306,valid5306,t5_1633choices,?_⟩
  exact check_of_frontier tree 0 t5_1633root t5_1633jobs t5_1633frontier t5_1633all
theorem t5_1634choices : plan5307.choices=[9,6,6,10,10].map (options 5 5) := by rfl


theorem t5_1634part0 : t5_1634jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1634frontier : t5_1634root.frontier 0=t5_1634jobs := by rfl
theorem t5_1634all : t5_1634jobs.all (Job.check tree)=true := by
  simp only [t5_1634jobs,List.all_append,List.all_nil,t5_1634part0,Bool.and_self]
theorem t5_1634checked : Checked tree [9,6,6,10,10] := by
  refine ⟨plan5307,valid5307,t5_1634choices,?_⟩
  exact check_of_frontier tree 0 t5_1634root t5_1634jobs t5_1634frontier t5_1634all
theorem t5_1635choices : plan5308.choices=[9,6,7,7,7].map (options 5 5) := by rfl


theorem t5_1635part0 : t5_1635jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1635frontier : t5_1635root.frontier 0=t5_1635jobs := by rfl
theorem t5_1635all : t5_1635jobs.all (Job.check tree)=true := by
  simp only [t5_1635jobs,List.all_append,List.all_nil,t5_1635part0,Bool.and_self]
theorem t5_1635checked : Checked tree [9,6,7,7,7] := by
  refine ⟨plan5308,valid5308,t5_1635choices,?_⟩
  exact check_of_frontier tree 0 t5_1635root t5_1635jobs t5_1635frontier t5_1635all
theorem t5_1636choices : plan5309.choices=[9,6,10,7,7].map (options 5 5) := by rfl


theorem t5_1636part0 : t5_1636jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1636frontier : t5_1636root.frontier 0=t5_1636jobs := by rfl
theorem t5_1636all : t5_1636jobs.all (Job.check tree)=true := by
  simp only [t5_1636jobs,List.all_append,List.all_nil,t5_1636part0,Bool.and_self]
theorem t5_1636checked : Checked tree [9,6,10,7,7] := by
  refine ⟨plan5309,valid5309,t5_1636choices,?_⟩
  exact check_of_frontier tree 0 t5_1636root t5_1636jobs t5_1636frontier t5_1636all
theorem t5_1637choices : plan5310.choices=[9,6,10,10,7].map (options 5 5) := by rfl


theorem t5_1637part0 : t5_1637jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1637frontier : t5_1637root.frontier 0=t5_1637jobs := by rfl
theorem t5_1637all : t5_1637jobs.all (Job.check tree)=true := by
  simp only [t5_1637jobs,List.all_append,List.all_nil,t5_1637part0,Bool.and_self]
theorem t5_1637checked : Checked tree [9,6,10,10,7] := by
  refine ⟨plan5310,valid5310,t5_1637choices,?_⟩
  exact check_of_frontier tree 0 t5_1637root t5_1637jobs t5_1637frontier t5_1637all
theorem t5_1638choices : plan5311.choices=[9,6,10,10,10].map (options 5 5) := by rfl


theorem t5_1638part0 : t5_1638jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1638frontier : t5_1638root.frontier 0=t5_1638jobs := by rfl
theorem t5_1638all : t5_1638jobs.all (Job.check tree)=true := by
  simp only [t5_1638jobs,List.all_append,List.all_nil,t5_1638part0,Bool.and_self]
theorem t5_1638checked : Checked tree [9,6,10,10,10] := by
  refine ⟨plan5311,valid5311,t5_1638choices,?_⟩
  exact check_of_frontier tree 0 t5_1638root t5_1638jobs t5_1638frontier t5_1638all
theorem t5_1639choices : plan5312.choices=[9,7,7,7,7].map (options 5 5) := by rfl


theorem t5_1639part0 : t5_1639jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1639frontier : t5_1639root.frontier 0=t5_1639jobs := by rfl
theorem t5_1639all : t5_1639jobs.all (Job.check tree)=true := by
  simp only [t5_1639jobs,List.all_append,List.all_nil,t5_1639part0,Bool.and_self]
theorem t5_1639checked : Checked tree [9,7,7,7,7] := by
  refine ⟨plan5312,valid5312,t5_1639choices,?_⟩
  exact check_of_frontier tree 0 t5_1639root t5_1639jobs t5_1639frontier t5_1639all
theorem t5_1640choices : plan3999.choices=[9,9,3,3,3].map (options 5 2) := by rfl


theorem t5_1640part0 : t5_1640jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1640frontier : t5_1640root.frontier 0=t5_1640jobs := by rfl
theorem t5_1640all : t5_1640jobs.all (Job.check tree)=true := by
  simp only [t5_1640jobs,List.all_append,List.all_nil,t5_1640part0,Bool.and_self]
theorem t5_1640checked : Checked tree [9,9,3,3,3] := by
  refine ⟨plan3999,valid3999,t5_1640choices,?_⟩
  exact check_of_frontier tree 0 t5_1640root t5_1640jobs t5_1640frontier t5_1640all
theorem t5_1641choices : plan4446.choices=[9,9,3,3,6].map (options 5 3) := by rfl


theorem t5_1641part0 : t5_1641jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1641frontier : t5_1641root.frontier 0=t5_1641jobs := by rfl
theorem t5_1641all : t5_1641jobs.all (Job.check tree)=true := by
  simp only [t5_1641jobs,List.all_append,List.all_nil,t5_1641part0,Bool.and_self]
theorem t5_1641checked : Checked tree [9,9,3,3,6] := by
  refine ⟨plan4446,valid4446,t5_1641choices,?_⟩
  exact check_of_frontier tree 0 t5_1641root t5_1641jobs t5_1641frontier t5_1641all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks046 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1632checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1633checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1634checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1635checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1636checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1637checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1638checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1639checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1640checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1641checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1623checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1624checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1625checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1626checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1627checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1628checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1629checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1630checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1631checked⟩
