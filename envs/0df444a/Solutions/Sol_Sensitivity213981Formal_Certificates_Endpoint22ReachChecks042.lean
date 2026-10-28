-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks042
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:06:40.829345+00:00
-- url     : https://prove2.me/submissions/0b89d0bd-9076-4307-8d8e-8784a7928578

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks042
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks042
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
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

theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid105 : plan105.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid108 : plan108.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid109 : plan109.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid111 : plan111.Valid := valid_step _ _ _ valid0 (by decide +kernel)


































































































































































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

theorem valid486 : plan486.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid487 : plan487.Valid := valid_step _ _ _ valid105 (by decide +kernel)

















theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)











theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)



















theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)











theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid524 : plan524.Valid := valid_step _ _ _ valid111 (by decide +kernel)








































































































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

theorem valid1337 : plan1337.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1338 : plan1338.Valid := valid_step _ _ _ valid487 (by decide +kernel)





theorem valid1341 : plan1341.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1342 : plan1342.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1343 : plan1343.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1344 : plan1344.Valid := valid_step _ _ _ valid504 (by decide +kernel)
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





























































































































theorem valid1407 : plan1407.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1408 : plan1408.Valid := valid_step _ _ _ valid515 (by decide +kernel)

























































theorem valid1437 : plan1437.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1438 : plan1438.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1439 : plan1439.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1440 : plan1440.Valid := valid_step _ _ _ valid517 (by decide +kernel)
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













































































































theorem valid2647 : plan2647.Valid := valid_step _ _ _ valid1297 (by decide +kernel)


















































































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























































































































































theorem valid2764 : plan2764.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2765 : plan2765.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2766 : plan2766.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2767 : plan2767.Valid := valid_step _ _ _ valid1344 (by decide +kernel)


































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















































































































theorem valid3992 : plan3992.Valid := valid_step _ _ _ valid2647 (by decide +kernel)
















































































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

















































theorem valid2809 : plan2809.Valid := valid_step _ _ _ valid1336 (by decide +kernel)

theorem valid2810 : plan2810.Valid := valid_step _ _ _ valid1337 (by decide +kernel)

theorem valid2811 : plan2811.Valid := valid_step _ _ _ valid1338 (by decide +kernel)










































































































































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















































theorem valid2904 : plan2904.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid2905 : plan2905.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid2906 : plan2906.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid2907 : plan2907.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid2908 : plan2908.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid2909 : plan2909.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid2910 : plan2910.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

theorem valid2911 : plan2911.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid2912 : plan2912.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid2913 : plan2913.Valid := valid_step _ _ _ valid1464 (by decide +kernel)











































































































theorem valid2967 : plan2967.Valid := valid_step _ _ _ valid1407 (by decide +kernel)

theorem valid2968 : plan2968.Valid := valid_step _ _ _ valid1408 (by decide +kernel)
















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



theorem valid4418 : plan4418.Valid := valid_step _ _ _ valid2764 (by decide +kernel)

theorem valid4419 : plan4419.Valid := valid_step _ _ _ valid2765 (by decide +kernel)

theorem valid4420 : plan4420.Valid := valid_step _ _ _ valid2766 (by decide +kernel)

theorem valid4421 : plan4421.Valid := valid_step _ _ _ valid2767 (by decide +kernel)

theorem valid4422 : plan4422.Valid := valid_step _ _ _ valid2809 (by decide +kernel)

theorem valid4423 : plan4423.Valid := valid_step _ _ _ valid2810 (by decide +kernel)

theorem valid4424 : plan4424.Valid := valid_step _ _ _ valid2811 (by decide +kernel)
















































































































































































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





















































theorem valid4923 : plan4923.Valid := valid_step _ _ _ valid2904 (by decide +kernel)

theorem valid4924 : plan4924.Valid := valid_step _ _ _ valid2905 (by decide +kernel)

theorem valid4925 : plan4925.Valid := valid_step _ _ _ valid2906 (by decide +kernel)

theorem valid4926 : plan4926.Valid := valid_step _ _ _ valid2907 (by decide +kernel)

theorem valid4927 : plan4927.Valid := valid_step _ _ _ valid2908 (by decide +kernel)

theorem valid4928 : plan4928.Valid := valid_step _ _ _ valid2909 (by decide +kernel)

theorem valid4929 : plan4929.Valid := valid_step _ _ _ valid2910 (by decide +kernel)

theorem valid4930 : plan4930.Valid := valid_step _ _ _ valid2911 (by decide +kernel)

theorem valid4931 : plan4931.Valid := valid_step _ _ _ valid2912 (by decide +kernel)

theorem valid4932 : plan4932.Valid := valid_step _ _ _ valid2913 (by decide +kernel)

theorem valid4933 : plan4933.Valid := valid_step _ _ _ valid2967 (by decide +kernel)

theorem valid4934 : plan4934.Valid := valid_step _ _ _ valid2968 (by decide +kernel)




















































































































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
theorem t5_1434choices : plan4418.choices=[8,3,3,6,10].map (options 5 3) := by rfl


theorem t5_1434part0 : t5_1434jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1434frontier : t5_1434root.frontier 0=t5_1434jobs := by rfl
theorem t5_1434all : t5_1434jobs.all (Job.check tree)=true := by
  simp only [t5_1434jobs,List.all_append,List.all_nil,t5_1434part0,Bool.and_self]
theorem t5_1434checked : Checked tree [8,3,3,6,10] := by
  refine ⟨plan4418,valid4418,t5_1434choices,?_⟩
  exact check_of_frontier tree 0 t5_1434root t5_1434jobs t5_1434frontier t5_1434all
theorem t5_1435choices : plan4419.choices=[8,3,3,7,7].map (options 5 3) := by rfl


theorem t5_1435part0 : t5_1435jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1435frontier : t5_1435root.frontier 0=t5_1435jobs := by rfl
theorem t5_1435all : t5_1435jobs.all (Job.check tree)=true := by
  simp only [t5_1435jobs,List.all_append,List.all_nil,t5_1435part0,Bool.and_self]
theorem t5_1435checked : Checked tree [8,3,3,7,7] := by
  refine ⟨plan4419,valid4419,t5_1435choices,?_⟩
  exact check_of_frontier tree 0 t5_1435root t5_1435jobs t5_1435frontier t5_1435all
theorem t5_1436choices : plan4420.choices=[8,3,3,10,7].map (options 5 3) := by rfl


theorem t5_1436part0 : t5_1436jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1436part1 : t5_1436jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1436frontier : t5_1436root.frontier 1=t5_1436jobs := by rfl
theorem t5_1436all : t5_1436jobs.all (Job.check tree)=true := by
  simp only [t5_1436jobs,List.all_append,List.all_nil,t5_1436part0,t5_1436part1,Bool.and_self]
theorem t5_1436checked : Checked tree [8,3,3,10,7] := by
  refine ⟨plan4420,valid4420,t5_1436choices,?_⟩
  exact check_of_frontier tree 1 t5_1436root t5_1436jobs t5_1436frontier t5_1436all
theorem t5_1437choices : plan4421.choices=[8,3,3,10,10].map (options 5 3) := by rfl


theorem t5_1437part0 : t5_1437jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1437frontier : t5_1437root.frontier 0=t5_1437jobs := by rfl
theorem t5_1437all : t5_1437jobs.all (Job.check tree)=true := by
  simp only [t5_1437jobs,List.all_append,List.all_nil,t5_1437part0,Bool.and_self]
theorem t5_1437checked : Checked tree [8,3,3,10,10] := by
  refine ⟨plan4421,valid4421,t5_1437choices,?_⟩
  exact check_of_frontier tree 0 t5_1437root t5_1437jobs t5_1437frontier t5_1437all
theorem t5_1438choices : plan4923.choices=[8,3,6,6,6].map (options 5 4) := by rfl


theorem t5_1438part0 : t5_1438jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1438frontier : t5_1438root.frontier 0=t5_1438jobs := by rfl
theorem t5_1438all : t5_1438jobs.all (Job.check tree)=true := by
  simp only [t5_1438jobs,List.all_append,List.all_nil,t5_1438part0,Bool.and_self]
theorem t5_1438checked : Checked tree [8,3,6,6,6] := by
  refine ⟨plan4923,valid4923,t5_1438choices,?_⟩
  exact check_of_frontier tree 0 t5_1438root t5_1438jobs t5_1438frontier t5_1438all
theorem t5_1439choices : plan4924.choices=[8,3,6,6,7].map (options 5 4) := by rfl


theorem t5_1439part0 : t5_1439jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1439frontier : t5_1439root.frontier 0=t5_1439jobs := by rfl
theorem t5_1439all : t5_1439jobs.all (Job.check tree)=true := by
  simp only [t5_1439jobs,List.all_append,List.all_nil,t5_1439part0,Bool.and_self]
theorem t5_1439checked : Checked tree [8,3,6,6,7] := by
  refine ⟨plan4924,valid4924,t5_1439choices,?_⟩
  exact check_of_frontier tree 0 t5_1439root t5_1439jobs t5_1439frontier t5_1439all
theorem t5_1440choices : plan4925.choices=[8,3,6,6,10].map (options 5 4) := by rfl


theorem t5_1440part0 : t5_1440jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1440frontier : t5_1440root.frontier 0=t5_1440jobs := by rfl
theorem t5_1440all : t5_1440jobs.all (Job.check tree)=true := by
  simp only [t5_1440jobs,List.all_append,List.all_nil,t5_1440part0,Bool.and_self]
theorem t5_1440checked : Checked tree [8,3,6,6,10] := by
  refine ⟨plan4925,valid4925,t5_1440choices,?_⟩
  exact check_of_frontier tree 0 t5_1440root t5_1440jobs t5_1440frontier t5_1440all
theorem t5_1441choices : plan4926.choices=[8,3,6,7,7].map (options 5 4) := by rfl


theorem t5_1441part0 : t5_1441jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1441part1 : t5_1441jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1441frontier : t5_1441root.frontier 1=t5_1441jobs := by rfl
theorem t5_1441all : t5_1441jobs.all (Job.check tree)=true := by
  simp only [t5_1441jobs,List.all_append,List.all_nil,t5_1441part0,t5_1441part1,Bool.and_self]
theorem t5_1441checked : Checked tree [8,3,6,7,7] := by
  refine ⟨plan4926,valid4926,t5_1441choices,?_⟩
  exact check_of_frontier tree 1 t5_1441root t5_1441jobs t5_1441frontier t5_1441all
theorem t5_1442choices : plan4927.choices=[8,3,6,10,7].map (options 5 4) := by rfl


theorem t5_1442part0 : t5_1442jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1442part1 : t5_1442jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1442part2 : t5_1442jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1442frontier : t5_1442root.frontier 1=t5_1442jobs := by rfl
theorem t5_1442all : t5_1442jobs.all (Job.check tree)=true := by
  simp only [t5_1442jobs,List.all_append,List.all_nil,t5_1442part0,t5_1442part1,t5_1442part2,Bool.and_self]
theorem t5_1442checked : Checked tree [8,3,6,10,7] := by
  refine ⟨plan4927,valid4927,t5_1442choices,?_⟩
  exact check_of_frontier tree 1 t5_1442root t5_1442jobs t5_1442frontier t5_1442all
theorem t5_1443choices : plan4928.choices=[8,3,6,10,10].map (options 5 4) := by rfl


theorem t5_1443part0 : t5_1443jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1443frontier : t5_1443root.frontier 0=t5_1443jobs := by rfl
theorem t5_1443all : t5_1443jobs.all (Job.check tree)=true := by
  simp only [t5_1443jobs,List.all_append,List.all_nil,t5_1443part0,Bool.and_self]
theorem t5_1443checked : Checked tree [8,3,6,10,10] := by
  refine ⟨plan4928,valid4928,t5_1443choices,?_⟩
  exact check_of_frontier tree 0 t5_1443root t5_1443jobs t5_1443frontier t5_1443all
theorem t5_1444choices : plan4929.choices=[8,3,7,7,7].map (options 5 4) := by rfl


theorem t5_1444part0 : t5_1444jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1444frontier : t5_1444root.frontier 0=t5_1444jobs := by rfl
theorem t5_1444all : t5_1444jobs.all (Job.check tree)=true := by
  simp only [t5_1444jobs,List.all_append,List.all_nil,t5_1444part0,Bool.and_self]
theorem t5_1444checked : Checked tree [8,3,7,7,7] := by
  refine ⟨plan4929,valid4929,t5_1444choices,?_⟩
  exact check_of_frontier tree 0 t5_1444root t5_1444jobs t5_1444frontier t5_1444all
theorem t5_1445choices : plan4930.choices=[8,3,10,7,7].map (options 5 4) := by rfl


theorem t5_1445part0 : t5_1445jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1445part1 : t5_1445jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1445frontier : t5_1445root.frontier 1=t5_1445jobs := by rfl
theorem t5_1445all : t5_1445jobs.all (Job.check tree)=true := by
  simp only [t5_1445jobs,List.all_append,List.all_nil,t5_1445part0,t5_1445part1,Bool.and_self]
theorem t5_1445checked : Checked tree [8,3,10,7,7] := by
  refine ⟨plan4930,valid4930,t5_1445choices,?_⟩
  exact check_of_frontier tree 1 t5_1445root t5_1445jobs t5_1445frontier t5_1445all
theorem t5_1446choices : plan4931.choices=[8,3,10,10,7].map (options 5 4) := by rfl


theorem t5_1446part0 : t5_1446jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1446frontier : t5_1446root.frontier 0=t5_1446jobs := by rfl
theorem t5_1446all : t5_1446jobs.all (Job.check tree)=true := by
  simp only [t5_1446jobs,List.all_append,List.all_nil,t5_1446part0,Bool.and_self]
theorem t5_1446checked : Checked tree [8,3,10,10,7] := by
  refine ⟨plan4931,valid4931,t5_1446choices,?_⟩
  exact check_of_frontier tree 0 t5_1446root t5_1446jobs t5_1446frontier t5_1446all
theorem t5_1447choices : plan4932.choices=[8,3,10,10,10].map (options 5 4) := by rfl


theorem t5_1447part0 : t5_1447jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1447frontier : t5_1447root.frontier 0=t5_1447jobs := by rfl
theorem t5_1447all : t5_1447jobs.all (Job.check tree)=true := by
  simp only [t5_1447jobs,List.all_append,List.all_nil,t5_1447part0,Bool.and_self]
theorem t5_1447checked : Checked tree [8,3,10,10,10] := by
  refine ⟨plan4932,valid4932,t5_1447choices,?_⟩
  exact check_of_frontier tree 0 t5_1447root t5_1447jobs t5_1447frontier t5_1447all
theorem t5_1448choices : plan3992.choices=[8,5,3,3,3].map (options 5 2) := by rfl


theorem t5_1448part0 : t5_1448jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1448frontier : t5_1448root.frontier 0=t5_1448jobs := by rfl
theorem t5_1448all : t5_1448jobs.all (Job.check tree)=true := by
  simp only [t5_1448jobs,List.all_append,List.all_nil,t5_1448part0,Bool.and_self]
theorem t5_1448checked : Checked tree [8,5,3,3,3] := by
  refine ⟨plan3992,valid3992,t5_1448choices,?_⟩
  exact check_of_frontier tree 0 t5_1448root t5_1448jobs t5_1448frontier t5_1448all
theorem t5_1449choices : plan4422.choices=[8,5,3,3,6].map (options 5 3) := by rfl


theorem t5_1449part0 : t5_1449jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1449frontier : t5_1449root.frontier 0=t5_1449jobs := by rfl
theorem t5_1449all : t5_1449jobs.all (Job.check tree)=true := by
  simp only [t5_1449jobs,List.all_append,List.all_nil,t5_1449part0,Bool.and_self]
theorem t5_1449checked : Checked tree [8,5,3,3,6] := by
  refine ⟨plan4422,valid4422,t5_1449choices,?_⟩
  exact check_of_frontier tree 0 t5_1449root t5_1449jobs t5_1449frontier t5_1449all
theorem t5_1450choices : plan4423.choices=[8,5,3,3,7].map (options 5 3) := by rfl


theorem t5_1450part0 : t5_1450jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1450frontier : t5_1450root.frontier 0=t5_1450jobs := by rfl
theorem t5_1450all : t5_1450jobs.all (Job.check tree)=true := by
  simp only [t5_1450jobs,List.all_append,List.all_nil,t5_1450part0,Bool.and_self]
theorem t5_1450checked : Checked tree [8,5,3,3,7] := by
  refine ⟨plan4423,valid4423,t5_1450choices,?_⟩
  exact check_of_frontier tree 0 t5_1450root t5_1450jobs t5_1450frontier t5_1450all
theorem t5_1451choices : plan4424.choices=[8,5,3,3,10].map (options 5 3) := by rfl


theorem t5_1451part0 : t5_1451jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1451frontier : t5_1451root.frontier 0=t5_1451jobs := by rfl
theorem t5_1451all : t5_1451jobs.all (Job.check tree)=true := by
  simp only [t5_1451jobs,List.all_append,List.all_nil,t5_1451part0,Bool.and_self]
theorem t5_1451checked : Checked tree [8,5,3,3,10] := by
  refine ⟨plan4424,valid4424,t5_1451choices,?_⟩
  exact check_of_frontier tree 0 t5_1451root t5_1451jobs t5_1451frontier t5_1451all
theorem t5_1452choices : plan4933.choices=[8,5,3,6,6].map (options 5 4) := by rfl


theorem t5_1452part0 : t5_1452jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1452frontier : t5_1452root.frontier 0=t5_1452jobs := by rfl
theorem t5_1452all : t5_1452jobs.all (Job.check tree)=true := by
  simp only [t5_1452jobs,List.all_append,List.all_nil,t5_1452part0,Bool.and_self]
theorem t5_1452checked : Checked tree [8,5,3,6,6] := by
  refine ⟨plan4933,valid4933,t5_1452choices,?_⟩
  exact check_of_frontier tree 0 t5_1452root t5_1452jobs t5_1452frontier t5_1452all
theorem t5_1453choices : plan4934.choices=[8,5,3,6,7].map (options 5 4) := by rfl


theorem t5_1453part0 : t5_1453jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1453frontier : t5_1453root.frontier 0=t5_1453jobs := by rfl
theorem t5_1453all : t5_1453jobs.all (Job.check tree)=true := by
  simp only [t5_1453jobs,List.all_append,List.all_nil,t5_1453part0,Bool.and_self]
theorem t5_1453checked : Checked tree [8,5,3,6,7] := by
  refine ⟨plan4934,valid4934,t5_1453choices,?_⟩
  exact check_of_frontier tree 0 t5_1453root t5_1453jobs t5_1453frontier t5_1453all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks042 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1445checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1446checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1447checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1448checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1449checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1450checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1451checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1452checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1453checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1435checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1436checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1437checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1438checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1439checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1440checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1441checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1442checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1443checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1444checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1434checked⟩
