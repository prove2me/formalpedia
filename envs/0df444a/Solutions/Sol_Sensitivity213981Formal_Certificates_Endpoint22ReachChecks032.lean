-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks032
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:26.744004+00:00
-- url     : https://prove2.me/submissions/5cd5d328-c9ca-4271-bc97-7575cb23c2ca

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks032
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans049
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





theorem valid483 : plan483.Valid := valid_step _ _ _ valid103 (by decide +kernel)



theorem valid485 : plan485.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid486 : plan486.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid487 : plan487.Valid := valid_step _ _ _ valid105 (by decide +kernel)















theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)











theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)













theorem valid511 : plan511.Valid := valid_step _ _ _ valid109 (by decide +kernel)





theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)





theorem valid520 : plan520.Valid := valid_step _ _ _ valid109 (by decide +kernel)





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























































theorem valid1276 : plan1276.Valid := valid_step _ _ _ valid462 (by decide +kernel)









































theorem valid1297 : plan1297.Valid := valid_step _ _ _ valid462 (by decide +kernel)













































theorem valid1320 : plan1320.Valid := valid_step _ _ _ valid483 (by decide +kernel)

theorem valid1321 : plan1321.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1322 : plan1322.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1323 : plan1323.Valid := valid_step _ _ _ valid487 (by decide +kernel)

























theorem valid1336 : plan1336.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1337 : plan1337.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1338 : plan1338.Valid := valid_step _ _ _ valid487 (by decide +kernel)



theorem valid1340 : plan1340.Valid := valid_step _ _ _ valid495 (by decide +kernel)

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













































































































theorem valid1399 : plan1399.Valid := valid_step _ _ _ valid511 (by decide +kernel)

theorem valid1400 : plan1400.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1401 : plan1401.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1402 : plan1402.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1403 : plan1403.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1404 : plan1404.Valid := valid_step _ _ _ valid520 (by decide +kernel)

theorem valid1405 : plan1405.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1406 : plan1406.Valid := valid_step _ _ _ valid524 (by decide +kernel)

theorem valid1407 : plan1407.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1408 : plan1408.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1409 : plan1409.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1410 : plan1410.Valid := valid_step _ _ _ valid517 (by decide +kernel)





















































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

























































































theorem valid2637 : plan2637.Valid := valid_step _ _ _ valid1276 (by decide +kernel)







theorem valid2641 : plan2641.Valid := valid_step _ _ _ valid1297 (by decide +kernel)






























































































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





















































































































































theorem valid2763 : plan2763.Valid := valid_step _ _ _ valid1340 (by decide +kernel)

theorem valid2764 : plan2764.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2765 : plan2765.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2766 : plan2766.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2767 : plan2767.Valid := valid_step _ _ _ valid1344 (by decide +kernel)





















theorem valid2778 : plan2778.Valid := valid_step _ _ _ valid1320 (by decide +kernel)

theorem valid2779 : plan2779.Valid := valid_step _ _ _ valid1321 (by decide +kernel)

theorem valid2780 : plan2780.Valid := valid_step _ _ _ valid1322 (by decide +kernel)

theorem valid2781 : plan2781.Valid := valid_step _ _ _ valid1323 (by decide +kernel)






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

























































theorem valid3965 : plan3965.Valid := valid_step _ _ _ valid2637 (by decide +kernel)

theorem valid3966 : plan3966.Valid := valid_step _ _ _ valid2641 (by decide +kernel)




































































































































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











theorem valid2790 : plan2790.Valid := valid_step _ _ _ valid1336 (by decide +kernel)

theorem valid2791 : plan2791.Valid := valid_step _ _ _ valid1337 (by decide +kernel)

theorem valid2792 : plan2792.Valid := valid_step _ _ _ valid1338 (by decide +kernel)
















































































































































































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

theorem valid2914 : plan2914.Valid := valid_step _ _ _ valid1399 (by decide +kernel)

theorem valid2915 : plan2915.Valid := valid_step _ _ _ valid1400 (by decide +kernel)

theorem valid2916 : plan2916.Valid := valid_step _ _ _ valid1401 (by decide +kernel)

theorem valid2917 : plan2917.Valid := valid_step _ _ _ valid1402 (by decide +kernel)

theorem valid2918 : plan2918.Valid := valid_step _ _ _ valid1403 (by decide +kernel)

theorem valid2919 : plan2919.Valid := valid_step _ _ _ valid1404 (by decide +kernel)

theorem valid2920 : plan2920.Valid := valid_step _ _ _ valid1405 (by decide +kernel)

theorem valid2921 : plan2921.Valid := valid_step _ _ _ valid1406 (by decide +kernel)

theorem valid2922 : plan2922.Valid := valid_step _ _ _ valid1407 (by decide +kernel)

theorem valid2923 : plan2923.Valid := valid_step _ _ _ valid1408 (by decide +kernel)

theorem valid2924 : plan2924.Valid := valid_step _ _ _ valid1409 (by decide +kernel)

theorem valid2925 : plan2925.Valid := valid_step _ _ _ valid1410 (by decide +kernel)






































































































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





















































































































































theorem valid4779 : plan4779.Valid := valid_step _ _ _ valid2904 (by decide +kernel)

theorem valid4780 : plan4780.Valid := valid_step _ _ _ valid2905 (by decide +kernel)

theorem valid4781 : plan4781.Valid := valid_step _ _ _ valid2906 (by decide +kernel)

theorem valid4782 : plan4782.Valid := valid_step _ _ _ valid2907 (by decide +kernel)

theorem valid4783 : plan4783.Valid := valid_step _ _ _ valid2908 (by decide +kernel)

theorem valid4784 : plan4784.Valid := valid_step _ _ _ valid2909 (by decide +kernel)

theorem valid4785 : plan4785.Valid := valid_step _ _ _ valid2910 (by decide +kernel)

theorem valid4786 : plan4786.Valid := valid_step _ _ _ valid2911 (by decide +kernel)

theorem valid4787 : plan4787.Valid := valid_step _ _ _ valid2912 (by decide +kernel)

theorem valid4788 : plan4788.Valid := valid_step _ _ _ valid2913 (by decide +kernel)

theorem valid4789 : plan4789.Valid := valid_step _ _ _ valid2914 (by decide +kernel)

theorem valid4790 : plan4790.Valid := valid_step _ _ _ valid2915 (by decide +kernel)

theorem valid4791 : plan4791.Valid := valid_step _ _ _ valid2916 (by decide +kernel)

theorem valid4792 : plan4792.Valid := valid_step _ _ _ valid2917 (by decide +kernel)

theorem valid4793 : plan4793.Valid := valid_step _ _ _ valid2918 (by decide +kernel)

theorem valid4794 : plan4794.Valid := valid_step _ _ _ valid2919 (by decide +kernel)

theorem valid4795 : plan4795.Valid := valid_step _ _ _ valid2920 (by decide +kernel)

theorem valid4796 : plan4796.Valid := valid_step _ _ _ valid2921 (by decide +kernel)

theorem valid4797 : plan4797.Valid := valid_step _ _ _ valid2922 (by decide +kernel)

theorem valid4798 : plan4798.Valid := valid_step _ _ _ valid2923 (by decide +kernel)

theorem valid4799 : plan4799.Valid := valid_step _ _ _ valid2924 (by decide +kernel)

theorem valid4800 : plan4800.Valid := valid_step _ _ _ valid2925 (by decide +kernel)
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











































theorem valid4342 : plan4342.Valid := valid_step _ _ _ valid2763 (by decide +kernel)

theorem valid4343 : plan4343.Valid := valid_step _ _ _ valid2764 (by decide +kernel)

theorem valid4344 : plan4344.Valid := valid_step _ _ _ valid2765 (by decide +kernel)

theorem valid4345 : plan4345.Valid := valid_step _ _ _ valid2766 (by decide +kernel)

theorem valid4346 : plan4346.Valid := valid_step _ _ _ valid2767 (by decide +kernel)

theorem valid4347 : plan4347.Valid := valid_step _ _ _ valid2778 (by decide +kernel)

theorem valid4348 : plan4348.Valid := valid_step _ _ _ valid2779 (by decide +kernel)

theorem valid4349 : plan4349.Valid := valid_step _ _ _ valid2780 (by decide +kernel)

theorem valid4350 : plan4350.Valid := valid_step _ _ _ valid2781 (by decide +kernel)

theorem valid4351 : plan4351.Valid := valid_step _ _ _ valid2790 (by decide +kernel)

theorem valid4352 : plan4352.Valid := valid_step _ _ _ valid2791 (by decide +kernel)

theorem valid4353 : plan4353.Valid := valid_step _ _ _ valid2792 (by decide +kernel)






























































































































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
theorem t5_972choices : plan4342.choices=[4,3,3,6,7].map (options 5 3) := by rfl


theorem t5_972part0 : t5_972jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_972part1 : t5_972jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_972frontier : t5_972root.frontier 1=t5_972jobs := by rfl
theorem t5_972all : t5_972jobs.all (Job.check tree)=true := by
  simp only [t5_972jobs,List.all_append,List.all_nil,t5_972part0,t5_972part1,Bool.and_self]
theorem t5_972checked : Checked tree [4,3,3,6,7] := by
  refine ⟨plan4342,valid4342,t5_972choices,?_⟩
  exact check_of_frontier tree 1 t5_972root t5_972jobs t5_972frontier t5_972all
theorem t5_973choices : plan4343.choices=[4,3,3,6,10].map (options 5 3) := by rfl


theorem t5_973part0 : t5_973jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_973frontier : t5_973root.frontier 0=t5_973jobs := by rfl
theorem t5_973all : t5_973jobs.all (Job.check tree)=true := by
  simp only [t5_973jobs,List.all_append,List.all_nil,t5_973part0,Bool.and_self]
theorem t5_973checked : Checked tree [4,3,3,6,10] := by
  refine ⟨plan4343,valid4343,t5_973choices,?_⟩
  exact check_of_frontier tree 0 t5_973root t5_973jobs t5_973frontier t5_973all
theorem t5_974choices : plan4344.choices=[4,3,3,7,7].map (options 5 3) := by rfl


theorem t5_974part0 : t5_974jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_974frontier : t5_974root.frontier 0=t5_974jobs := by rfl
theorem t5_974all : t5_974jobs.all (Job.check tree)=true := by
  simp only [t5_974jobs,List.all_append,List.all_nil,t5_974part0,Bool.and_self]
theorem t5_974checked : Checked tree [4,3,3,7,7] := by
  refine ⟨plan4344,valid4344,t5_974choices,?_⟩
  exact check_of_frontier tree 0 t5_974root t5_974jobs t5_974frontier t5_974all
theorem t5_975choices : plan4345.choices=[4,3,3,10,7].map (options 5 3) := by rfl


theorem t5_975part0 : t5_975jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_975part1 : t5_975jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_975frontier : t5_975root.frontier 1=t5_975jobs := by rfl
theorem t5_975all : t5_975jobs.all (Job.check tree)=true := by
  simp only [t5_975jobs,List.all_append,List.all_nil,t5_975part0,t5_975part1,Bool.and_self]
theorem t5_975checked : Checked tree [4,3,3,10,7] := by
  refine ⟨plan4345,valid4345,t5_975choices,?_⟩
  exact check_of_frontier tree 1 t5_975root t5_975jobs t5_975frontier t5_975all
theorem t5_976choices : plan4346.choices=[4,3,3,10,10].map (options 5 3) := by rfl


theorem t5_976part0 : t5_976jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_976frontier : t5_976root.frontier 0=t5_976jobs := by rfl
theorem t5_976all : t5_976jobs.all (Job.check tree)=true := by
  simp only [t5_976jobs,List.all_append,List.all_nil,t5_976part0,Bool.and_self]
theorem t5_976checked : Checked tree [4,3,3,10,10] := by
  refine ⟨plan4346,valid4346,t5_976choices,?_⟩
  exact check_of_frontier tree 0 t5_976root t5_976jobs t5_976frontier t5_976all
theorem t5_977choices : plan4779.choices=[4,3,6,6,6].map (options 5 4) := by rfl


theorem t5_977part0 : t5_977jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_977frontier : t5_977root.frontier 0=t5_977jobs := by rfl
theorem t5_977all : t5_977jobs.all (Job.check tree)=true := by
  simp only [t5_977jobs,List.all_append,List.all_nil,t5_977part0,Bool.and_self]
theorem t5_977checked : Checked tree [4,3,6,6,6] := by
  refine ⟨plan4779,valid4779,t5_977choices,?_⟩
  exact check_of_frontier tree 0 t5_977root t5_977jobs t5_977frontier t5_977all
theorem t5_978choices : plan4780.choices=[4,3,6,6,7].map (options 5 4) := by rfl


theorem t5_978part0 : t5_978jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_978frontier : t5_978root.frontier 0=t5_978jobs := by rfl
theorem t5_978all : t5_978jobs.all (Job.check tree)=true := by
  simp only [t5_978jobs,List.all_append,List.all_nil,t5_978part0,Bool.and_self]
theorem t5_978checked : Checked tree [4,3,6,6,7] := by
  refine ⟨plan4780,valid4780,t5_978choices,?_⟩
  exact check_of_frontier tree 0 t5_978root t5_978jobs t5_978frontier t5_978all
theorem t5_979choices : plan4781.choices=[4,3,6,6,10].map (options 5 4) := by rfl


theorem t5_979part0 : t5_979jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_979frontier : t5_979root.frontier 0=t5_979jobs := by rfl
theorem t5_979all : t5_979jobs.all (Job.check tree)=true := by
  simp only [t5_979jobs,List.all_append,List.all_nil,t5_979part0,Bool.and_self]
theorem t5_979checked : Checked tree [4,3,6,6,10] := by
  refine ⟨plan4781,valid4781,t5_979choices,?_⟩
  exact check_of_frontier tree 0 t5_979root t5_979jobs t5_979frontier t5_979all
theorem t5_980choices : plan4782.choices=[4,3,6,7,7].map (options 5 4) := by rfl


theorem t5_980part0 : t5_980jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_980part1 : t5_980jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_980frontier : t5_980root.frontier 1=t5_980jobs := by rfl
theorem t5_980all : t5_980jobs.all (Job.check tree)=true := by
  simp only [t5_980jobs,List.all_append,List.all_nil,t5_980part0,t5_980part1,Bool.and_self]
theorem t5_980checked : Checked tree [4,3,6,7,7] := by
  refine ⟨plan4782,valid4782,t5_980choices,?_⟩
  exact check_of_frontier tree 1 t5_980root t5_980jobs t5_980frontier t5_980all
theorem t5_981choices : plan4783.choices=[4,3,6,10,7].map (options 5 4) := by rfl


theorem t5_981part0 : t5_981jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_981part1 : t5_981jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_981part2 : t5_981jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_981frontier : t5_981root.frontier 1=t5_981jobs := by rfl
theorem t5_981all : t5_981jobs.all (Job.check tree)=true := by
  simp only [t5_981jobs,List.all_append,List.all_nil,t5_981part0,t5_981part1,t5_981part2,Bool.and_self]
theorem t5_981checked : Checked tree [4,3,6,10,7] := by
  refine ⟨plan4783,valid4783,t5_981choices,?_⟩
  exact check_of_frontier tree 1 t5_981root t5_981jobs t5_981frontier t5_981all
theorem t5_982choices : plan4784.choices=[4,3,6,10,10].map (options 5 4) := by rfl


theorem t5_982part0 : t5_982jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_982frontier : t5_982root.frontier 0=t5_982jobs := by rfl
theorem t5_982all : t5_982jobs.all (Job.check tree)=true := by
  simp only [t5_982jobs,List.all_append,List.all_nil,t5_982part0,Bool.and_self]
theorem t5_982checked : Checked tree [4,3,6,10,10] := by
  refine ⟨plan4784,valid4784,t5_982choices,?_⟩
  exact check_of_frontier tree 0 t5_982root t5_982jobs t5_982frontier t5_982all
theorem t5_983choices : plan4785.choices=[4,3,7,7,7].map (options 5 4) := by rfl


theorem t5_983part0 : t5_983jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_983frontier : t5_983root.frontier 0=t5_983jobs := by rfl
theorem t5_983all : t5_983jobs.all (Job.check tree)=true := by
  simp only [t5_983jobs,List.all_append,List.all_nil,t5_983part0,Bool.and_self]
theorem t5_983checked : Checked tree [4,3,7,7,7] := by
  refine ⟨plan4785,valid4785,t5_983choices,?_⟩
  exact check_of_frontier tree 0 t5_983root t5_983jobs t5_983frontier t5_983all
theorem t5_984choices : plan4786.choices=[4,3,10,7,7].map (options 5 4) := by rfl


theorem t5_984part0 : t5_984jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_984part1 : t5_984jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_984frontier : t5_984root.frontier 1=t5_984jobs := by rfl
theorem t5_984all : t5_984jobs.all (Job.check tree)=true := by
  simp only [t5_984jobs,List.all_append,List.all_nil,t5_984part0,t5_984part1,Bool.and_self]
theorem t5_984checked : Checked tree [4,3,10,7,7] := by
  refine ⟨plan4786,valid4786,t5_984choices,?_⟩
  exact check_of_frontier tree 1 t5_984root t5_984jobs t5_984frontier t5_984all
theorem t5_985choices : plan4787.choices=[4,3,10,10,7].map (options 5 4) := by rfl


theorem t5_985part0 : t5_985jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_985frontier : t5_985root.frontier 0=t5_985jobs := by rfl
theorem t5_985all : t5_985jobs.all (Job.check tree)=true := by
  simp only [t5_985jobs,List.all_append,List.all_nil,t5_985part0,Bool.and_self]
theorem t5_985checked : Checked tree [4,3,10,10,7] := by
  refine ⟨plan4787,valid4787,t5_985choices,?_⟩
  exact check_of_frontier tree 0 t5_985root t5_985jobs t5_985frontier t5_985all
theorem t5_986choices : plan4788.choices=[4,3,10,10,10].map (options 5 4) := by rfl


theorem t5_986part0 : t5_986jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_986frontier : t5_986root.frontier 0=t5_986jobs := by rfl
theorem t5_986all : t5_986jobs.all (Job.check tree)=true := by
  simp only [t5_986jobs,List.all_append,List.all_nil,t5_986part0,Bool.and_self]
theorem t5_986checked : Checked tree [4,3,10,10,10] := by
  refine ⟨plan4788,valid4788,t5_986choices,?_⟩
  exact check_of_frontier tree 0 t5_986root t5_986jobs t5_986frontier t5_986all
theorem t5_987choices : plan4347.choices=[4,4,2,2,7].map (options 5 3) := by rfl


theorem t5_987part0 : t5_987jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_987frontier : t5_987root.frontier 0=t5_987jobs := by rfl
theorem t5_987all : t5_987jobs.all (Job.check tree)=true := by
  simp only [t5_987jobs,List.all_append,List.all_nil,t5_987part0,Bool.and_self]
theorem t5_987checked : Checked tree [4,4,2,2,7] := by
  refine ⟨plan4347,valid4347,t5_987choices,?_⟩
  exact check_of_frontier tree 0 t5_987root t5_987jobs t5_987frontier t5_987all
theorem t5_988choices : plan3965.choices=[4,4,2,3,3].map (options 5 2) := by rfl


theorem t5_988part0 : t5_988jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_988frontier : t5_988root.frontier 0=t5_988jobs := by rfl
theorem t5_988all : t5_988jobs.all (Job.check tree)=true := by
  simp only [t5_988jobs,List.all_append,List.all_nil,t5_988part0,Bool.and_self]
theorem t5_988checked : Checked tree [4,4,2,3,3] := by
  refine ⟨plan3965,valid3965,t5_988choices,?_⟩
  exact check_of_frontier tree 0 t5_988root t5_988jobs t5_988frontier t5_988all
theorem t5_989choices : plan4348.choices=[4,4,2,3,6].map (options 5 3) := by rfl


theorem t5_989part0 : t5_989jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_989frontier : t5_989root.frontier 0=t5_989jobs := by rfl
theorem t5_989all : t5_989jobs.all (Job.check tree)=true := by
  simp only [t5_989jobs,List.all_append,List.all_nil,t5_989part0,Bool.and_self]
theorem t5_989checked : Checked tree [4,4,2,3,6] := by
  refine ⟨plan4348,valid4348,t5_989choices,?_⟩
  exact check_of_frontier tree 0 t5_989root t5_989jobs t5_989frontier t5_989all
theorem t5_990choices : plan4349.choices=[4,4,2,3,7].map (options 5 3) := by rfl


theorem t5_990part0 : t5_990jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_990frontier : t5_990root.frontier 0=t5_990jobs := by rfl
theorem t5_990all : t5_990jobs.all (Job.check tree)=true := by
  simp only [t5_990jobs,List.all_append,List.all_nil,t5_990part0,Bool.and_self]
theorem t5_990checked : Checked tree [4,4,2,3,7] := by
  refine ⟨plan4349,valid4349,t5_990choices,?_⟩
  exact check_of_frontier tree 0 t5_990root t5_990jobs t5_990frontier t5_990all
theorem t5_991choices : plan4350.choices=[4,4,2,3,10].map (options 5 3) := by rfl


theorem t5_991part0 : t5_991jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_991frontier : t5_991root.frontier 0=t5_991jobs := by rfl
theorem t5_991all : t5_991jobs.all (Job.check tree)=true := by
  simp only [t5_991jobs,List.all_append,List.all_nil,t5_991part0,Bool.and_self]
theorem t5_991checked : Checked tree [4,4,2,3,10] := by
  refine ⟨plan4350,valid4350,t5_991choices,?_⟩
  exact check_of_frontier tree 0 t5_991root t5_991jobs t5_991frontier t5_991all
theorem t5_992choices : plan4789.choices=[4,4,2,5,7].map (options 5 4) := by rfl


theorem t5_992part0 : t5_992jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_992frontier : t5_992root.frontier 0=t5_992jobs := by rfl
theorem t5_992all : t5_992jobs.all (Job.check tree)=true := by
  simp only [t5_992jobs,List.all_append,List.all_nil,t5_992part0,Bool.and_self]
theorem t5_992checked : Checked tree [4,4,2,5,7] := by
  refine ⟨plan4789,valid4789,t5_992choices,?_⟩
  exact check_of_frontier tree 0 t5_992root t5_992jobs t5_992frontier t5_992all
theorem t5_993choices : plan4790.choices=[4,4,2,6,6].map (options 5 4) := by rfl


theorem t5_993part0 : t5_993jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_993frontier : t5_993root.frontier 0=t5_993jobs := by rfl
theorem t5_993all : t5_993jobs.all (Job.check tree)=true := by
  simp only [t5_993jobs,List.all_append,List.all_nil,t5_993part0,Bool.and_self]
theorem t5_993checked : Checked tree [4,4,2,6,6] := by
  refine ⟨plan4790,valid4790,t5_993choices,?_⟩
  exact check_of_frontier tree 0 t5_993root t5_993jobs t5_993frontier t5_993all
theorem t5_994choices : plan4791.choices=[4,4,2,6,7].map (options 5 4) := by rfl


theorem t5_994part0 : t5_994jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_994frontier : t5_994root.frontier 0=t5_994jobs := by rfl
theorem t5_994all : t5_994jobs.all (Job.check tree)=true := by
  simp only [t5_994jobs,List.all_append,List.all_nil,t5_994part0,Bool.and_self]
theorem t5_994checked : Checked tree [4,4,2,6,7] := by
  refine ⟨plan4791,valid4791,t5_994choices,?_⟩
  exact check_of_frontier tree 0 t5_994root t5_994jobs t5_994frontier t5_994all
theorem t5_995choices : plan4792.choices=[4,4,2,6,10].map (options 5 4) := by rfl


theorem t5_995part0 : t5_995jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_995frontier : t5_995root.frontier 0=t5_995jobs := by rfl
theorem t5_995all : t5_995jobs.all (Job.check tree)=true := by
  simp only [t5_995jobs,List.all_append,List.all_nil,t5_995part0,Bool.and_self]
theorem t5_995checked : Checked tree [4,4,2,6,10] := by
  refine ⟨plan4792,valid4792,t5_995choices,?_⟩
  exact check_of_frontier tree 0 t5_995root t5_995jobs t5_995frontier t5_995all
theorem t5_996choices : plan4793.choices=[4,4,2,7,7].map (options 5 4) := by rfl


theorem t5_996part0 : t5_996jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_996frontier : t5_996root.frontier 0=t5_996jobs := by rfl
theorem t5_996all : t5_996jobs.all (Job.check tree)=true := by
  simp only [t5_996jobs,List.all_append,List.all_nil,t5_996part0,Bool.and_self]
theorem t5_996checked : Checked tree [4,4,2,7,7] := by
  refine ⟨plan4793,valid4793,t5_996choices,?_⟩
  exact check_of_frontier tree 0 t5_996root t5_996jobs t5_996frontier t5_996all
theorem t5_997choices : plan4794.choices=[4,4,2,9,7].map (options 5 4) := by rfl


theorem t5_997part0 : t5_997jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_997frontier : t5_997root.frontier 0=t5_997jobs := by rfl
theorem t5_997all : t5_997jobs.all (Job.check tree)=true := by
  simp only [t5_997jobs,List.all_append,List.all_nil,t5_997part0,Bool.and_self]
theorem t5_997checked : Checked tree [4,4,2,9,7] := by
  refine ⟨plan4794,valid4794,t5_997choices,?_⟩
  exact check_of_frontier tree 0 t5_997root t5_997jobs t5_997frontier t5_997all
theorem t5_998choices : plan4795.choices=[4,4,2,10,7].map (options 5 4) := by rfl


theorem t5_998part0 : t5_998jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_998frontier : t5_998root.frontier 0=t5_998jobs := by rfl
theorem t5_998all : t5_998jobs.all (Job.check tree)=true := by
  simp only [t5_998jobs,List.all_append,List.all_nil,t5_998part0,Bool.and_self]
theorem t5_998checked : Checked tree [4,4,2,10,7] := by
  refine ⟨plan4795,valid4795,t5_998choices,?_⟩
  exact check_of_frontier tree 0 t5_998root t5_998jobs t5_998frontier t5_998all
theorem t5_999choices : plan4796.choices=[4,4,2,10,10].map (options 5 4) := by rfl


theorem t5_999part0 : t5_999jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_999frontier : t5_999root.frontier 0=t5_999jobs := by rfl
theorem t5_999all : t5_999jobs.all (Job.check tree)=true := by
  simp only [t5_999jobs,List.all_append,List.all_nil,t5_999part0,Bool.and_self]
theorem t5_999checked : Checked tree [4,4,2,10,10] := by
  refine ⟨plan4796,valid4796,t5_999choices,?_⟩
  exact check_of_frontier tree 0 t5_999root t5_999jobs t5_999frontier t5_999all
theorem t5_1000choices : plan3966.choices=[4,4,3,3,3].map (options 5 2) := by rfl


theorem t5_1000part0 : t5_1000jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1000frontier : t5_1000root.frontier 0=t5_1000jobs := by rfl
theorem t5_1000all : t5_1000jobs.all (Job.check tree)=true := by
  simp only [t5_1000jobs,List.all_append,List.all_nil,t5_1000part0,Bool.and_self]
theorem t5_1000checked : Checked tree [4,4,3,3,3] := by
  refine ⟨plan3966,valid3966,t5_1000choices,?_⟩
  exact check_of_frontier tree 0 t5_1000root t5_1000jobs t5_1000frontier t5_1000all
theorem t5_1001choices : plan4351.choices=[4,4,3,3,6].map (options 5 3) := by rfl


theorem t5_1001part0 : t5_1001jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1001frontier : t5_1001root.frontier 0=t5_1001jobs := by rfl
theorem t5_1001all : t5_1001jobs.all (Job.check tree)=true := by
  simp only [t5_1001jobs,List.all_append,List.all_nil,t5_1001part0,Bool.and_self]
theorem t5_1001checked : Checked tree [4,4,3,3,6] := by
  refine ⟨plan4351,valid4351,t5_1001choices,?_⟩
  exact check_of_frontier tree 0 t5_1001root t5_1001jobs t5_1001frontier t5_1001all
theorem t5_1002choices : plan4352.choices=[4,4,3,3,7].map (options 5 3) := by rfl


theorem t5_1002part0 : t5_1002jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1002frontier : t5_1002root.frontier 0=t5_1002jobs := by rfl
theorem t5_1002all : t5_1002jobs.all (Job.check tree)=true := by
  simp only [t5_1002jobs,List.all_append,List.all_nil,t5_1002part0,Bool.and_self]
theorem t5_1002checked : Checked tree [4,4,3,3,7] := by
  refine ⟨plan4352,valid4352,t5_1002choices,?_⟩
  exact check_of_frontier tree 0 t5_1002root t5_1002jobs t5_1002frontier t5_1002all
theorem t5_1003choices : plan4353.choices=[4,4,3,3,10].map (options 5 3) := by rfl


theorem t5_1003part0 : t5_1003jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1003frontier : t5_1003root.frontier 0=t5_1003jobs := by rfl
theorem t5_1003all : t5_1003jobs.all (Job.check tree)=true := by
  simp only [t5_1003jobs,List.all_append,List.all_nil,t5_1003part0,Bool.and_self]
theorem t5_1003checked : Checked tree [4,4,3,3,10] := by
  refine ⟨plan4353,valid4353,t5_1003choices,?_⟩
  exact check_of_frontier tree 0 t5_1003root t5_1003jobs t5_1003frontier t5_1003all
theorem t5_1004choices : plan4797.choices=[4,4,3,6,6].map (options 5 4) := by rfl


theorem t5_1004part0 : t5_1004jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1004frontier : t5_1004root.frontier 0=t5_1004jobs := by rfl
theorem t5_1004all : t5_1004jobs.all (Job.check tree)=true := by
  simp only [t5_1004jobs,List.all_append,List.all_nil,t5_1004part0,Bool.and_self]
theorem t5_1004checked : Checked tree [4,4,3,6,6] := by
  refine ⟨plan4797,valid4797,t5_1004choices,?_⟩
  exact check_of_frontier tree 0 t5_1004root t5_1004jobs t5_1004frontier t5_1004all
theorem t5_1005choices : plan4798.choices=[4,4,3,6,7].map (options 5 4) := by rfl


theorem t5_1005part0 : t5_1005jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1005frontier : t5_1005root.frontier 0=t5_1005jobs := by rfl
theorem t5_1005all : t5_1005jobs.all (Job.check tree)=true := by
  simp only [t5_1005jobs,List.all_append,List.all_nil,t5_1005part0,Bool.and_self]
theorem t5_1005checked : Checked tree [4,4,3,6,7] := by
  refine ⟨plan4798,valid4798,t5_1005choices,?_⟩
  exact check_of_frontier tree 0 t5_1005root t5_1005jobs t5_1005frontier t5_1005all
theorem t5_1006choices : plan4799.choices=[4,4,3,6,10].map (options 5 4) := by rfl


theorem t5_1006part0 : t5_1006jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1006frontier : t5_1006root.frontier 0=t5_1006jobs := by rfl
theorem t5_1006all : t5_1006jobs.all (Job.check tree)=true := by
  simp only [t5_1006jobs,List.all_append,List.all_nil,t5_1006part0,Bool.and_self]
theorem t5_1006checked : Checked tree [4,4,3,6,10] := by
  refine ⟨plan4799,valid4799,t5_1006choices,?_⟩
  exact check_of_frontier tree 0 t5_1006root t5_1006jobs t5_1006frontier t5_1006all
theorem t5_1007choices : plan4800.choices=[4,4,3,7,7].map (options 5 4) := by rfl


theorem t5_1007part0 : t5_1007jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1007frontier : t5_1007root.frontier 0=t5_1007jobs := by rfl
theorem t5_1007all : t5_1007jobs.all (Job.check tree)=true := by
  simp only [t5_1007jobs,List.all_append,List.all_nil,t5_1007part0,Bool.and_self]
theorem t5_1007checked : Checked tree [4,4,3,7,7] := by
  refine ⟨plan4800,valid4800,t5_1007choices,?_⟩
  exact check_of_frontier tree 0 t5_1007root t5_1007jobs t5_1007frontier t5_1007all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks032 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_983checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_984checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_985checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_972checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_986checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_987checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_988checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_989checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_990checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_991checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_992checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_993checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_994checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_995checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_973checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_996checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_997checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_998checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_999checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1000checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1001checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1002checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1003checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1004checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1005checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_974checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1006checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1007checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_975checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_976checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_977checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_978checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_979checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_980checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_981checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_982checked⟩
