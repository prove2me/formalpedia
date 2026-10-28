-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks022
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:20.506624+00:00
-- url     : https://prove2.me/submissions/6276a8c1-d6d3-4f6b-a3ce-bee2e779d588

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks022
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks022
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans048
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







theorem valid100 : plan100.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid102 : plan102.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid105 : plan105.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid108 : plan108.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid109 : plan109.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid110 : plan110.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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





















theorem valid498 : plan498.Valid := valid_step _ _ _ valid100 (by decide +kernel)































theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)



theorem valid519 : plan519.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid520 : plan520.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid521 : plan521.Valid := valid_step _ _ _ valid110 (by decide +kernel)

theorem valid522 : plan522.Valid := valid_step _ _ _ valid111 (by decide +kernel)

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

theorem valid1384 : plan1384.Valid := valid_step _ _ _ valid487 (by decide +kernel)









theorem valid1389 : plan1389.Valid := valid_step _ _ _ valid498 (by decide +kernel)






































































































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























































































































theorem valid2652 : plan2652.Valid := valid_step _ _ _ valid1315 (by decide +kernel)








































































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



theorem valid3938 : plan3938.Valid := valid_step _ _ _ valid2652 (by decide +kernel)




























































































































































































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

















































































theorem valid2825 : plan2825.Valid := valid_step _ _ _ valid1382 (by decide +kernel)

theorem valid2826 : plan2826.Valid := valid_step _ _ _ valid1383 (by decide +kernel)

theorem valid2827 : plan2827.Valid := valid_step _ _ _ valid1384 (by decide +kernel)

theorem valid2828 : plan2828.Valid := valid_step _ _ _ valid1389 (by decide +kernel)








































































































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



theorem valid1442 : plan1442.Valid := valid_step _ _ _ valid524 (by decide +kernel)

theorem valid1443 : plan1443.Valid := valid_step _ _ _ valid517 (by decide +kernel)















theorem valid1451 : plan1451.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1452 : plan1452.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1453 : plan1453.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1454 : plan1454.Valid := valid_step _ _ _ valid517 (by decide +kernel)



theorem valid1456 : plan1456.Valid := valid_step _ _ _ valid519 (by decide +kernel)

theorem valid1457 : plan1457.Valid := valid_step _ _ _ valid520 (by decide +kernel)

theorem valid1458 : plan1458.Valid := valid_step _ _ _ valid521 (by decide +kernel)

theorem valid1459 : plan1459.Valid := valid_step _ _ _ valid522 (by decide +kernel)

theorem valid1460 : plan1460.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1461 : plan1461.Valid := valid_step _ _ _ valid524 (by decide +kernel)






















































































































































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











































theorem valid2998 : plan2998.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid2999 : plan2999.Valid := valid_step _ _ _ valid1443 (by decide +kernel)







theorem valid3003 : plan3003.Valid := valid_step _ _ _ valid1451 (by decide +kernel)

theorem valid3004 : plan3004.Valid := valid_step _ _ _ valid1452 (by decide +kernel)

theorem valid3005 : plan3005.Valid := valid_step _ _ _ valid1453 (by decide +kernel)

theorem valid3006 : plan3006.Valid := valid_step _ _ _ valid1454 (by decide +kernel)



theorem valid3008 : plan3008.Valid := valid_step _ _ _ valid1456 (by decide +kernel)

theorem valid3009 : plan3009.Valid := valid_step _ _ _ valid1457 (by decide +kernel)

theorem valid3010 : plan3010.Valid := valid_step _ _ _ valid1458 (by decide +kernel)

theorem valid3011 : plan3011.Valid := valid_step _ _ _ valid1459 (by decide +kernel)

theorem valid3012 : plan3012.Valid := valid_step _ _ _ valid1460 (by decide +kernel)

theorem valid3013 : plan3013.Valid := valid_step _ _ _ valid1461 (by decide +kernel)






















































































































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





















































































































































theorem valid4683 : plan4683.Valid := valid_step _ _ _ valid2998 (by decide +kernel)

theorem valid4684 : plan4684.Valid := valid_step _ _ _ valid2999 (by decide +kernel)

theorem valid4685 : plan4685.Valid := valid_step _ _ _ valid3003 (by decide +kernel)

theorem valid4686 : plan4686.Valid := valid_step _ _ _ valid3004 (by decide +kernel)

theorem valid4687 : plan4687.Valid := valid_step _ _ _ valid3005 (by decide +kernel)

theorem valid4688 : plan4688.Valid := valid_step _ _ _ valid3006 (by decide +kernel)

theorem valid4689 : plan4689.Valid := valid_step _ _ _ valid3008 (by decide +kernel)

theorem valid4690 : plan4690.Valid := valid_step _ _ _ valid3009 (by decide +kernel)

theorem valid4691 : plan4691.Valid := valid_step _ _ _ valid3010 (by decide +kernel)

theorem valid4692 : plan4692.Valid := valid_step _ _ _ valid3011 (by decide +kernel)

theorem valid4693 : plan4693.Valid := valid_step _ _ _ valid3012 (by decide +kernel)

theorem valid4694 : plan4694.Valid := valid_step _ _ _ valid3013 (by decide +kernel)




















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



































































































































theorem valid4290 : plan4290.Valid := valid_step _ _ _ valid2825 (by decide +kernel)

theorem valid4291 : plan4291.Valid := valid_step _ _ _ valid2826 (by decide +kernel)

theorem valid4292 : plan4292.Valid := valid_step _ _ _ valid2827 (by decide +kernel)

theorem valid4293 : plan4293.Valid := valid_step _ _ _ valid2828 (by decide +kernel)






















































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
theorem t5_788choices : plan4683.choices=[2,5,6,10,10].map (options 5 4) := by rfl


theorem t5_788part0 : t5_788jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_788frontier : t5_788root.frontier 0=t5_788jobs := by rfl
theorem t5_788all : t5_788jobs.all (Job.check tree)=true := by
  simp only [t5_788jobs,List.all_append,List.all_nil,t5_788part0,Bool.and_self]
theorem t5_788checked : Checked tree [2,5,6,10,10] := by
  refine ⟨plan4683,valid4683,t5_788choices,?_⟩
  exact check_of_frontier tree 0 t5_788root t5_788jobs t5_788frontier t5_788all
theorem t5_789choices : plan4684.choices=[2,5,7,7,7].map (options 5 4) := by rfl


theorem t5_789part0 : t5_789jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_789frontier : t5_789root.frontier 0=t5_789jobs := by rfl
theorem t5_789all : t5_789jobs.all (Job.check tree)=true := by
  simp only [t5_789jobs,List.all_append,List.all_nil,t5_789part0,Bool.and_self]
theorem t5_789checked : Checked tree [2,5,7,7,7] := by
  refine ⟨plan4684,valid4684,t5_789choices,?_⟩
  exact check_of_frontier tree 0 t5_789root t5_789jobs t5_789frontier t5_789all
theorem t5_790choices : plan3938.choices=[2,5,9,3,3].map (options 5 2) := by rfl


theorem t5_790part0 : t5_790jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_790frontier : t5_790root.frontier 0=t5_790jobs := by rfl
theorem t5_790all : t5_790jobs.all (Job.check tree)=true := by
  simp only [t5_790jobs,List.all_append,List.all_nil,t5_790part0,Bool.and_self]
theorem t5_790checked : Checked tree [2,5,9,3,3] := by
  refine ⟨plan3938,valid3938,t5_790choices,?_⟩
  exact check_of_frontier tree 0 t5_790root t5_790jobs t5_790frontier t5_790all
theorem t5_791choices : plan4290.choices=[2,5,9,3,6].map (options 5 3) := by rfl


theorem t5_791part0 : t5_791jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_791part1 : t5_791jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_791part2 : t5_791jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_791frontier : t5_791root.frontier 1=t5_791jobs := by rfl
theorem t5_791all : t5_791jobs.all (Job.check tree)=true := by
  simp only [t5_791jobs,List.all_append,List.all_nil,t5_791part0,t5_791part1,t5_791part2,Bool.and_self]
theorem t5_791checked : Checked tree [2,5,9,3,6] := by
  refine ⟨plan4290,valid4290,t5_791choices,?_⟩
  exact check_of_frontier tree 1 t5_791root t5_791jobs t5_791frontier t5_791all
theorem t5_792choices : plan4291.choices=[2,5,9,3,7].map (options 5 3) := by rfl


theorem t5_792part0 : t5_792jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_792part1 : t5_792jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_792part2 : t5_792jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_792part3 : t5_792jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_792frontier : t5_792root.frontier 1=t5_792jobs := by rfl
theorem t5_792all : t5_792jobs.all (Job.check tree)=true := by
  simp only [t5_792jobs,List.all_append,List.all_nil,t5_792part0,t5_792part1,t5_792part2,t5_792part3,Bool.and_self]
theorem t5_792checked : Checked tree [2,5,9,3,7] := by
  refine ⟨plan4291,valid4291,t5_792choices,?_⟩
  exact check_of_frontier tree 1 t5_792root t5_792jobs t5_792frontier t5_792all
theorem t5_793choices : plan4292.choices=[2,5,9,3,10].map (options 5 3) := by rfl


theorem t5_793part0 : t5_793jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_793part1 : t5_793jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_793part2 : t5_793jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_793frontier : t5_793root.frontier 1=t5_793jobs := by rfl
theorem t5_793all : t5_793jobs.all (Job.check tree)=true := by
  simp only [t5_793jobs,List.all_append,List.all_nil,t5_793part0,t5_793part1,t5_793part2,Bool.and_self]
theorem t5_793checked : Checked tree [2,5,9,3,10] := by
  refine ⟨plan4292,valid4292,t5_793choices,?_⟩
  exact check_of_frontier tree 1 t5_793root t5_793jobs t5_793frontier t5_793all
theorem t5_794choices : plan4685.choices=[2,5,9,6,6].map (options 5 4) := by rfl


theorem t5_794part0 : t5_794jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_794frontier : t5_794root.frontier 0=t5_794jobs := by rfl
theorem t5_794all : t5_794jobs.all (Job.check tree)=true := by
  simp only [t5_794jobs,List.all_append,List.all_nil,t5_794part0,Bool.and_self]
theorem t5_794checked : Checked tree [2,5,9,6,6] := by
  refine ⟨plan4685,valid4685,t5_794choices,?_⟩
  exact check_of_frontier tree 0 t5_794root t5_794jobs t5_794frontier t5_794all
theorem t5_795choices : plan4686.choices=[2,5,9,6,7].map (options 5 4) := by rfl


theorem t5_795part0 : t5_795jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_795part1 : t5_795jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_795frontier : t5_795root.frontier 1=t5_795jobs := by rfl
theorem t5_795all : t5_795jobs.all (Job.check tree)=true := by
  simp only [t5_795jobs,List.all_append,List.all_nil,t5_795part0,t5_795part1,Bool.and_self]
theorem t5_795checked : Checked tree [2,5,9,6,7] := by
  refine ⟨plan4686,valid4686,t5_795choices,?_⟩
  exact check_of_frontier tree 1 t5_795root t5_795jobs t5_795frontier t5_795all
theorem t5_796choices : plan4687.choices=[2,5,9,6,10].map (options 5 4) := by rfl


theorem t5_796part0 : t5_796jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_796frontier : t5_796root.frontier 0=t5_796jobs := by rfl
theorem t5_796all : t5_796jobs.all (Job.check tree)=true := by
  simp only [t5_796jobs,List.all_append,List.all_nil,t5_796part0,Bool.and_self]
theorem t5_796checked : Checked tree [2,5,9,6,10] := by
  refine ⟨plan4687,valid4687,t5_796choices,?_⟩
  exact check_of_frontier tree 0 t5_796root t5_796jobs t5_796frontier t5_796all
theorem t5_797choices : plan4688.choices=[2,5,9,7,7].map (options 5 4) := by rfl


theorem t5_797part0 : t5_797jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_797frontier : t5_797root.frontier 0=t5_797jobs := by rfl
theorem t5_797all : t5_797jobs.all (Job.check tree)=true := by
  simp only [t5_797jobs,List.all_append,List.all_nil,t5_797part0,Bool.and_self]
theorem t5_797checked : Checked tree [2,5,9,7,7] := by
  refine ⟨plan4688,valid4688,t5_797choices,?_⟩
  exact check_of_frontier tree 0 t5_797root t5_797jobs t5_797frontier t5_797all
theorem t5_798choices : plan4293.choices=[2,5,9,9,3].map (options 5 3) := by rfl


theorem t5_798part0 : t5_798jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_798frontier : t5_798root.frontier 0=t5_798jobs := by rfl
theorem t5_798all : t5_798jobs.all (Job.check tree)=true := by
  simp only [t5_798jobs,List.all_append,List.all_nil,t5_798part0,Bool.and_self]
theorem t5_798checked : Checked tree [2,5,9,9,3] := by
  refine ⟨plan4293,valid4293,t5_798choices,?_⟩
  exact check_of_frontier tree 0 t5_798root t5_798jobs t5_798frontier t5_798all
theorem t5_799choices : plan4689.choices=[2,5,9,9,6].map (options 5 4) := by rfl


theorem t5_799part0 : t5_799jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_799frontier : t5_799root.frontier 0=t5_799jobs := by rfl
theorem t5_799all : t5_799jobs.all (Job.check tree)=true := by
  simp only [t5_799jobs,List.all_append,List.all_nil,t5_799part0,Bool.and_self]
theorem t5_799checked : Checked tree [2,5,9,9,6] := by
  refine ⟨plan4689,valid4689,t5_799choices,?_⟩
  exact check_of_frontier tree 0 t5_799root t5_799jobs t5_799frontier t5_799all
theorem t5_800choices : plan4690.choices=[2,5,9,9,7].map (options 5 4) := by rfl


theorem t5_800part0 : t5_800jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_800frontier : t5_800root.frontier 0=t5_800jobs := by rfl
theorem t5_800all : t5_800jobs.all (Job.check tree)=true := by
  simp only [t5_800jobs,List.all_append,List.all_nil,t5_800part0,Bool.and_self]
theorem t5_800checked : Checked tree [2,5,9,9,7] := by
  refine ⟨plan4690,valid4690,t5_800choices,?_⟩
  exact check_of_frontier tree 0 t5_800root t5_800jobs t5_800frontier t5_800all
theorem t5_801choices : plan4691.choices=[2,5,9,9,9].map (options 5 4) := by rfl


theorem t5_801part0 : t5_801jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_801frontier : t5_801root.frontier 0=t5_801jobs := by rfl
theorem t5_801all : t5_801jobs.all (Job.check tree)=true := by
  simp only [t5_801jobs,List.all_append,List.all_nil,t5_801part0,Bool.and_self]
theorem t5_801checked : Checked tree [2,5,9,9,9] := by
  refine ⟨plan4691,valid4691,t5_801choices,?_⟩
  exact check_of_frontier tree 0 t5_801root t5_801jobs t5_801frontier t5_801all
theorem t5_802choices : plan4692.choices=[2,5,9,9,10].map (options 5 4) := by rfl


theorem t5_802part0 : t5_802jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_802frontier : t5_802root.frontier 0=t5_802jobs := by rfl
theorem t5_802all : t5_802jobs.all (Job.check tree)=true := by
  simp only [t5_802jobs,List.all_append,List.all_nil,t5_802part0,Bool.and_self]
theorem t5_802checked : Checked tree [2,5,9,9,10] := by
  refine ⟨plan4692,valid4692,t5_802choices,?_⟩
  exact check_of_frontier tree 0 t5_802root t5_802jobs t5_802frontier t5_802all
theorem t5_803choices : plan4693.choices=[2,5,9,10,7].map (options 5 4) := by rfl


theorem t5_803part0 : t5_803jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_803part1 : t5_803jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_803frontier : t5_803root.frontier 1=t5_803jobs := by rfl
theorem t5_803all : t5_803jobs.all (Job.check tree)=true := by
  simp only [t5_803jobs,List.all_append,List.all_nil,t5_803part0,t5_803part1,Bool.and_self]
theorem t5_803checked : Checked tree [2,5,9,10,7] := by
  refine ⟨plan4693,valid4693,t5_803choices,?_⟩
  exact check_of_frontier tree 1 t5_803root t5_803jobs t5_803frontier t5_803all
theorem t5_804choices : plan4694.choices=[2,5,9,10,10].map (options 5 4) := by rfl


theorem t5_804part0 : t5_804jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_804frontier : t5_804root.frontier 0=t5_804jobs := by rfl
theorem t5_804all : t5_804jobs.all (Job.check tree)=true := by
  simp only [t5_804jobs,List.all_append,List.all_nil,t5_804part0,Bool.and_self]
theorem t5_804checked : Checked tree [2,5,9,10,10] := by
  refine ⟨plan4694,valid4694,t5_804choices,?_⟩
  exact check_of_frontier tree 0 t5_804root t5_804jobs t5_804frontier t5_804all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks022 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_798checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_799checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_800checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_801checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_802checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_803checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_804checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_789checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_790checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_791checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_792checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_793checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_794checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_795checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_796checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_788checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_797checked⟩
