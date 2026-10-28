-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks025
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:59:33.590985+00:00
-- url     : https://prove2.me/submissions/fb719404-6de2-4344-b6d2-eb50c5e6a4c8

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks025
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks025
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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









theorem valid485 : plan485.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid486 : plan486.Valid := valid_step _ _ _ valid103 (by decide +kernel)

































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





































































































































theorem valid1315 : plan1315.Valid := valid_step _ _ _ valid462 (by decide +kernel)























































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











































































theorem valid1382 : plan1382.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1383 : plan1383.Valid := valid_step _ _ _ valid486 (by decide +kernel)











































































































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























































































































































theorem valid2668 : plan2668.Valid := valid_step _ _ _ valid1315 (by decide +kernel)








































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











theorem valid3942 : plan3942.Valid := valid_step _ _ _ valid2668 (by decide +kernel)




















































































































































































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



































































































































































theorem valid2866 : plan2866.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2867 : plan2867.Valid := valid_step _ _ _ valid1344 (by decide +kernel)



theorem valid2869 : plan2869.Valid := valid_step _ _ _ valid1382 (by decide +kernel)

theorem valid2870 : plan2870.Valid := valid_step _ _ _ valid1383 (by decide +kernel)




















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





















theorem valid3083 : plan3083.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid3084 : plan3084.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid3085 : plan3085.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid3086 : plan3086.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid3087 : plan3087.Valid := valid_step _ _ _ valid1441 (by decide +kernel)

theorem valid3088 : plan3088.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid3089 : plan3089.Valid := valid_step _ _ _ valid1443 (by decide +kernel)






























































































































































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



















































































































































theorem valid4298 : plan4298.Valid := valid_step _ _ _ valid2866 (by decide +kernel)

theorem valid4299 : plan4299.Valid := valid_step _ _ _ valid2867 (by decide +kernel)

theorem valid4300 : plan4300.Valid := valid_step _ _ _ valid2869 (by decide +kernel)

theorem valid4301 : plan4301.Valid := valid_step _ _ _ valid2870 (by decide +kernel)






































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









theorem valid4709 : plan4709.Valid := valid_step _ _ _ valid3083 (by decide +kernel)

theorem valid4710 : plan4710.Valid := valid_step _ _ _ valid3084 (by decide +kernel)

theorem valid4711 : plan4711.Valid := valid_step _ _ _ valid3085 (by decide +kernel)

theorem valid4712 : plan4712.Valid := valid_step _ _ _ valid3086 (by decide +kernel)

theorem valid4713 : plan4713.Valid := valid_step _ _ _ valid3087 (by decide +kernel)

theorem valid4714 : plan4714.Valid := valid_step _ _ _ valid3088 (by decide +kernel)

theorem valid4715 : plan4715.Valid := valid_step _ _ _ valid3089 (by decide +kernel)










































































































































































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
theorem t5_827choices : plan4298.choices=[2,9,3,10,7].map (options 5 3) := by rfl


theorem t5_827part0 : t5_827jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_827part1 : t5_827jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_827part2 : t5_827jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_827part3 : t5_827jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_827frontier : t5_827root.frontier 1=t5_827jobs := by rfl
theorem t5_827all : t5_827jobs.all (Job.check tree)=true := by
  simp only [t5_827jobs,List.all_append,List.all_nil,t5_827part0,t5_827part1,t5_827part2,t5_827part3,Bool.and_self]
theorem t5_827checked : Checked tree [2,9,3,10,7] := by
  refine ⟨plan4298,valid4298,t5_827choices,?_⟩
  exact check_of_frontier tree 1 t5_827root t5_827jobs t5_827frontier t5_827all
theorem t5_828choices : plan4299.choices=[2,9,3,10,10].map (options 5 3) := by rfl


theorem t5_828part0 : t5_828jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_828part1 : t5_828jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_828frontier : t5_828root.frontier 1=t5_828jobs := by rfl
theorem t5_828all : t5_828jobs.all (Job.check tree)=true := by
  simp only [t5_828jobs,List.all_append,List.all_nil,t5_828part0,t5_828part1,Bool.and_self]
theorem t5_828checked : Checked tree [2,9,3,10,10] := by
  refine ⟨plan4299,valid4299,t5_828choices,?_⟩
  exact check_of_frontier tree 1 t5_828root t5_828jobs t5_828frontier t5_828all
theorem t5_829choices : plan4709.choices=[2,9,6,6,6].map (options 5 4) := by rfl


theorem t5_829part0 : t5_829jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_829frontier : t5_829root.frontier 0=t5_829jobs := by rfl
theorem t5_829all : t5_829jobs.all (Job.check tree)=true := by
  simp only [t5_829jobs,List.all_append,List.all_nil,t5_829part0,Bool.and_self]
theorem t5_829checked : Checked tree [2,9,6,6,6] := by
  refine ⟨plan4709,valid4709,t5_829choices,?_⟩
  exact check_of_frontier tree 0 t5_829root t5_829jobs t5_829frontier t5_829all
theorem t5_830choices : plan4710.choices=[2,9,6,6,7].map (options 5 4) := by rfl


theorem t5_830part0 : t5_830jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_830part1 : t5_830jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_830frontier : t5_830root.frontier 1=t5_830jobs := by rfl
theorem t5_830all : t5_830jobs.all (Job.check tree)=true := by
  simp only [t5_830jobs,List.all_append,List.all_nil,t5_830part0,t5_830part1,Bool.and_self]
theorem t5_830checked : Checked tree [2,9,6,6,7] := by
  refine ⟨plan4710,valid4710,t5_830choices,?_⟩
  exact check_of_frontier tree 1 t5_830root t5_830jobs t5_830frontier t5_830all
theorem t5_831choices : plan4711.choices=[2,9,6,6,10].map (options 5 4) := by rfl


theorem t5_831part0 : t5_831jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_831frontier : t5_831root.frontier 0=t5_831jobs := by rfl
theorem t5_831all : t5_831jobs.all (Job.check tree)=true := by
  simp only [t5_831jobs,List.all_append,List.all_nil,t5_831part0,Bool.and_self]
theorem t5_831checked : Checked tree [2,9,6,6,10] := by
  refine ⟨plan4711,valid4711,t5_831choices,?_⟩
  exact check_of_frontier tree 0 t5_831root t5_831jobs t5_831frontier t5_831all
theorem t5_832choices : plan4712.choices=[2,9,6,7,7].map (options 5 4) := by rfl


theorem t5_832part0 : t5_832jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_832part1 : t5_832jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_832frontier : t5_832root.frontier 1=t5_832jobs := by rfl
theorem t5_832all : t5_832jobs.all (Job.check tree)=true := by
  simp only [t5_832jobs,List.all_append,List.all_nil,t5_832part0,t5_832part1,Bool.and_self]
theorem t5_832checked : Checked tree [2,9,6,7,7] := by
  refine ⟨plan4712,valid4712,t5_832choices,?_⟩
  exact check_of_frontier tree 1 t5_832root t5_832jobs t5_832frontier t5_832all
theorem t5_833choices : plan4713.choices=[2,9,6,10,7].map (options 5 4) := by rfl


theorem t5_833part0 : t5_833jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_833part1 : t5_833jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_833part2 : t5_833jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_833frontier : t5_833root.frontier 2=t5_833jobs := by rfl
theorem t5_833all : t5_833jobs.all (Job.check tree)=true := by
  simp only [t5_833jobs,List.all_append,List.all_nil,t5_833part0,t5_833part1,t5_833part2,Bool.and_self]
theorem t5_833checked : Checked tree [2,9,6,10,7] := by
  refine ⟨plan4713,valid4713,t5_833choices,?_⟩
  exact check_of_frontier tree 2 t5_833root t5_833jobs t5_833frontier t5_833all
theorem t5_834choices : plan4714.choices=[2,9,6,10,10].map (options 5 4) := by rfl


theorem t5_834part0 : t5_834jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_834frontier : t5_834root.frontier 0=t5_834jobs := by rfl
theorem t5_834all : t5_834jobs.all (Job.check tree)=true := by
  simp only [t5_834jobs,List.all_append,List.all_nil,t5_834part0,Bool.and_self]
theorem t5_834checked : Checked tree [2,9,6,10,10] := by
  refine ⟨plan4714,valid4714,t5_834choices,?_⟩
  exact check_of_frontier tree 0 t5_834root t5_834jobs t5_834frontier t5_834all
theorem t5_835choices : plan4715.choices=[2,9,7,7,7].map (options 5 4) := by rfl


theorem t5_835part0 : t5_835jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_835frontier : t5_835root.frontier 0=t5_835jobs := by rfl
theorem t5_835all : t5_835jobs.all (Job.check tree)=true := by
  simp only [t5_835jobs,List.all_append,List.all_nil,t5_835part0,Bool.and_self]
theorem t5_835checked : Checked tree [2,9,7,7,7] := by
  refine ⟨plan4715,valid4715,t5_835choices,?_⟩
  exact check_of_frontier tree 0 t5_835root t5_835jobs t5_835frontier t5_835all
theorem t5_836choices : plan3942.choices=[2,9,9,3,3].map (options 5 2) := by rfl


theorem t5_836part0 : t5_836jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_836frontier : t5_836root.frontier 0=t5_836jobs := by rfl
theorem t5_836all : t5_836jobs.all (Job.check tree)=true := by
  simp only [t5_836jobs,List.all_append,List.all_nil,t5_836part0,Bool.and_self]
theorem t5_836checked : Checked tree [2,9,9,3,3] := by
  refine ⟨plan3942,valid3942,t5_836choices,?_⟩
  exact check_of_frontier tree 0 t5_836root t5_836jobs t5_836frontier t5_836all
theorem t5_837choices : plan4300.choices=[2,9,9,3,6].map (options 5 3) := by rfl


theorem t5_837part0 : t5_837jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_837frontier : t5_837root.frontier 0=t5_837jobs := by rfl
theorem t5_837all : t5_837jobs.all (Job.check tree)=true := by
  simp only [t5_837jobs,List.all_append,List.all_nil,t5_837part0,Bool.and_self]
theorem t5_837checked : Checked tree [2,9,9,3,6] := by
  refine ⟨plan4300,valid4300,t5_837choices,?_⟩
  exact check_of_frontier tree 0 t5_837root t5_837jobs t5_837frontier t5_837all
theorem t5_838choices : plan4301.choices=[2,9,9,3,7].map (options 5 3) := by rfl


theorem t5_838part0 : t5_838jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_838part1 : t5_838jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_838frontier : t5_838root.frontier 1=t5_838jobs := by rfl
theorem t5_838all : t5_838jobs.all (Job.check tree)=true := by
  simp only [t5_838jobs,List.all_append,List.all_nil,t5_838part0,t5_838part1,Bool.and_self]
theorem t5_838checked : Checked tree [2,9,9,3,7] := by
  refine ⟨plan4301,valid4301,t5_838choices,?_⟩
  exact check_of_frontier tree 1 t5_838root t5_838jobs t5_838frontier t5_838all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks025 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_836checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_837checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_838checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_827checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_828checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_829checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_830checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_831checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_832checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_833checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_834checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_835checked⟩
