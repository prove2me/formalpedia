-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks026
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:23.015996+00:00
-- url     : https://prove2.me/submissions/a6cf2aa3-4eba-4176-a7c8-ffc3d09f6653

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
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













































































































































































theorem valid87 : plan87.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid90 : plan90.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid91 : plan91.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid93 : plan93.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid96 : plan96.Valid := valid_step _ _ _ valid0 (by decide +kernel)
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

theorem valid97 : plan97.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid99 : plan99.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid100 : plan100.Valid := valid_step _ _ _ valid0 (by decide +kernel)









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



























































































































theorem valid446 : plan446.Valid := valid_step _ _ _ valid87 (by decide +kernel)















theorem valid454 : plan454.Valid := valid_step _ _ _ valid90 (by decide +kernel)

theorem valid455 : plan455.Valid := valid_step _ _ _ valid91 (by decide +kernel)

theorem valid456 : plan456.Valid := valid_step _ _ _ valid93 (by decide +kernel)































theorem valid472 : plan472.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid473 : plan473.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid474 : plan474.Valid := valid_step _ _ _ valid99 (by decide +kernel)












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



theorem valid1250 : plan1250.Valid := valid_step _ _ _ valid446 (by decide +kernel)





























theorem valid1265 : plan1265.Valid := valid_step _ _ _ valid454 (by decide +kernel)

theorem valid1266 : plan1266.Valid := valid_step _ _ _ valid455 (by decide +kernel)

theorem valid1267 : plan1267.Valid := valid_step _ _ _ valid456 (by decide +kernel)



































































theorem valid1301 : plan1301.Valid := valid_step _ _ _ valid472 (by decide +kernel)

theorem valid1302 : plan1302.Valid := valid_step _ _ _ valid473 (by decide +kernel)

theorem valid1303 : plan1303.Valid := valid_step _ _ _ valid474 (by decide +kernel)


















































































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















































theorem valid2520 : plan2520.Valid := valid_step _ _ _ valid1250 (by decide +kernel)



























































theorem valid2550 : plan2550.Valid := valid_step _ _ _ valid1265 (by decide +kernel)

theorem valid2551 : plan2551.Valid := valid_step _ _ _ valid1266 (by decide +kernel)

theorem valid2552 : plan2552.Valid := valid_step _ _ _ valid1267 (by decide +kernel)
















































































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

















































theorem valid3673 : plan3673.Valid := valid_step _ _ _ valid2520 (by decide +kernel)














































































































































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











































































theorem valid2630 : plan2630.Valid := valid_step _ _ _ valid1301 (by decide +kernel)

theorem valid2631 : plan2631.Valid := valid_step _ _ _ valid1302 (by decide +kernel)

theorem valid2632 : plan2632.Valid := valid_step _ _ _ valid1303 (by decide +kernel)
















































































































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



theorem valid3746 : plan3746.Valid := valid_step _ _ _ valid2550 (by decide +kernel)

theorem valid3747 : plan3747.Valid := valid_step _ _ _ valid2551 (by decide +kernel)

theorem valid3748 : plan3748.Valid := valid_step _ _ _ valid2552 (by decide +kernel)
























































































































































































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













theorem valid3943 : plan3943.Valid := valid_step _ _ _ valid2630 (by decide +kernel)

theorem valid3944 : plan3944.Valid := valid_step _ _ _ valid2631 (by decide +kernel)

theorem valid3945 : plan3945.Valid := valid_step _ _ _ valid2632 (by decide +kernel)














































































































































































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













































































































































































theorem valid2871 : plan2871.Valid := valid_step _ _ _ valid1384 (by decide +kernel)

theorem valid2872 : plan2872.Valid := valid_step _ _ _ valid1389 (by decide +kernel)
















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









































theorem valid3093 : plan3093.Valid := valid_step _ _ _ valid1451 (by decide +kernel)

theorem valid3094 : plan3094.Valid := valid_step _ _ _ valid1452 (by decide +kernel)

theorem valid3095 : plan3095.Valid := valid_step _ _ _ valid1453 (by decide +kernel)

theorem valid3096 : plan3096.Valid := valid_step _ _ _ valid1454 (by decide +kernel)



theorem valid3098 : plan3098.Valid := valid_step _ _ _ valid1456 (by decide +kernel)

theorem valid3099 : plan3099.Valid := valid_step _ _ _ valid1457 (by decide +kernel)

theorem valid3100 : plan3100.Valid := valid_step _ _ _ valid1458 (by decide +kernel)

theorem valid3101 : plan3101.Valid := valid_step _ _ _ valid1459 (by decide +kernel)

theorem valid3102 : plan3102.Valid := valid_step _ _ _ valid1460 (by decide +kernel)

theorem valid3103 : plan3103.Valid := valid_step _ _ _ valid1461 (by decide +kernel)

theorem valid3104 : plan3104.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3105 : plan3105.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid3106 : plan3106.Valid := valid_step _ _ _ valid1464 (by decide +kernel)

theorem valid3107 : plan3107.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

theorem valid3108 : plan3108.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3109 : plan3109.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid3110 : plan3110.Valid := valid_step _ _ _ valid1464 (by decide +kernel)




















































































































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



























































































































































theorem valid4302 : plan4302.Valid := valid_step _ _ _ valid2871 (by decide +kernel)

theorem valid4303 : plan4303.Valid := valid_step _ _ _ valid2872 (by decide +kernel)


































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























theorem valid4716 : plan4716.Valid := valid_step _ _ _ valid3093 (by decide +kernel)

theorem valid4717 : plan4717.Valid := valid_step _ _ _ valid3094 (by decide +kernel)

theorem valid4718 : plan4718.Valid := valid_step _ _ _ valid3095 (by decide +kernel)

theorem valid4719 : plan4719.Valid := valid_step _ _ _ valid3096 (by decide +kernel)

theorem valid4720 : plan4720.Valid := valid_step _ _ _ valid3098 (by decide +kernel)

theorem valid4721 : plan4721.Valid := valid_step _ _ _ valid3099 (by decide +kernel)

theorem valid4722 : plan4722.Valid := valid_step _ _ _ valid3100 (by decide +kernel)

theorem valid4723 : plan4723.Valid := valid_step _ _ _ valid3101 (by decide +kernel)

theorem valid4724 : plan4724.Valid := valid_step _ _ _ valid3102 (by decide +kernel)

theorem valid4725 : plan4725.Valid := valid_step _ _ _ valid3103 (by decide +kernel)

theorem valid4726 : plan4726.Valid := valid_step _ _ _ valid3104 (by decide +kernel)

theorem valid4727 : plan4727.Valid := valid_step _ _ _ valid3105 (by decide +kernel)

theorem valid4728 : plan4728.Valid := valid_step _ _ _ valid3106 (by decide +kernel)

theorem valid4729 : plan4729.Valid := valid_step _ _ _ valid3107 (by decide +kernel)

theorem valid4730 : plan4730.Valid := valid_step _ _ _ valid3108 (by decide +kernel)

theorem valid4731 : plan4731.Valid := valid_step _ _ _ valid3109 (by decide +kernel)

theorem valid4732 : plan4732.Valid := valid_step _ _ _ valid3110 (by decide +kernel)








































































































































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
theorem t5_839choices : plan4302.choices=[2,9,9,3,10].map (options 5 3) := by rfl


theorem t5_839part0 : t5_839jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_839frontier : t5_839root.frontier 0=t5_839jobs := by rfl
theorem t5_839all : t5_839jobs.all (Job.check tree)=true := by
  simp only [t5_839jobs,List.all_append,List.all_nil,t5_839part0,Bool.and_self]
theorem t5_839checked : Checked tree [2,9,9,3,10] := by
  refine ⟨plan4302,valid4302,t5_839choices,?_⟩
  exact check_of_frontier tree 0 t5_839root t5_839jobs t5_839frontier t5_839all
theorem t5_840choices : plan4716.choices=[2,9,9,6,6].map (options 5 4) := by rfl


theorem t5_840part0 : t5_840jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_840frontier : t5_840root.frontier 0=t5_840jobs := by rfl
theorem t5_840all : t5_840jobs.all (Job.check tree)=true := by
  simp only [t5_840jobs,List.all_append,List.all_nil,t5_840part0,Bool.and_self]
theorem t5_840checked : Checked tree [2,9,9,6,6] := by
  refine ⟨plan4716,valid4716,t5_840choices,?_⟩
  exact check_of_frontier tree 0 t5_840root t5_840jobs t5_840frontier t5_840all
theorem t5_841choices : plan4717.choices=[2,9,9,6,7].map (options 5 4) := by rfl


theorem t5_841part0 : t5_841jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_841frontier : t5_841root.frontier 0=t5_841jobs := by rfl
theorem t5_841all : t5_841jobs.all (Job.check tree)=true := by
  simp only [t5_841jobs,List.all_append,List.all_nil,t5_841part0,Bool.and_self]
theorem t5_841checked : Checked tree [2,9,9,6,7] := by
  refine ⟨plan4717,valid4717,t5_841choices,?_⟩
  exact check_of_frontier tree 0 t5_841root t5_841jobs t5_841frontier t5_841all
theorem t5_842choices : plan4718.choices=[2,9,9,6,10].map (options 5 4) := by rfl


theorem t5_842part0 : t5_842jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_842frontier : t5_842root.frontier 0=t5_842jobs := by rfl
theorem t5_842all : t5_842jobs.all (Job.check tree)=true := by
  simp only [t5_842jobs,List.all_append,List.all_nil,t5_842part0,Bool.and_self]
theorem t5_842checked : Checked tree [2,9,9,6,10] := by
  refine ⟨plan4718,valid4718,t5_842choices,?_⟩
  exact check_of_frontier tree 0 t5_842root t5_842jobs t5_842frontier t5_842all
theorem t5_843choices : plan4719.choices=[2,9,9,7,7].map (options 5 4) := by rfl


theorem t5_843part0 : t5_843jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_843frontier : t5_843root.frontier 0=t5_843jobs := by rfl
theorem t5_843all : t5_843jobs.all (Job.check tree)=true := by
  simp only [t5_843jobs,List.all_append,List.all_nil,t5_843part0,Bool.and_self]
theorem t5_843checked : Checked tree [2,9,9,7,7] := by
  refine ⟨plan4719,valid4719,t5_843choices,?_⟩
  exact check_of_frontier tree 0 t5_843root t5_843jobs t5_843frontier t5_843all
theorem t5_844choices : plan4303.choices=[2,9,9,9,3].map (options 5 3) := by rfl


theorem t5_844part0 : t5_844jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_844frontier : t5_844root.frontier 0=t5_844jobs := by rfl
theorem t5_844all : t5_844jobs.all (Job.check tree)=true := by
  simp only [t5_844jobs,List.all_append,List.all_nil,t5_844part0,Bool.and_self]
theorem t5_844checked : Checked tree [2,9,9,9,3] := by
  refine ⟨plan4303,valid4303,t5_844choices,?_⟩
  exact check_of_frontier tree 0 t5_844root t5_844jobs t5_844frontier t5_844all
theorem t5_845choices : plan4720.choices=[2,9,9,9,6].map (options 5 4) := by rfl


theorem t5_845part0 : t5_845jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_845frontier : t5_845root.frontier 0=t5_845jobs := by rfl
theorem t5_845all : t5_845jobs.all (Job.check tree)=true := by
  simp only [t5_845jobs,List.all_append,List.all_nil,t5_845part0,Bool.and_self]
theorem t5_845checked : Checked tree [2,9,9,9,6] := by
  refine ⟨plan4720,valid4720,t5_845choices,?_⟩
  exact check_of_frontier tree 0 t5_845root t5_845jobs t5_845frontier t5_845all
theorem t5_846choices : plan4721.choices=[2,9,9,9,7].map (options 5 4) := by rfl


theorem t5_846part0 : t5_846jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_846frontier : t5_846root.frontier 0=t5_846jobs := by rfl
theorem t5_846all : t5_846jobs.all (Job.check tree)=true := by
  simp only [t5_846jobs,List.all_append,List.all_nil,t5_846part0,Bool.and_self]
theorem t5_846checked : Checked tree [2,9,9,9,7] := by
  refine ⟨plan4721,valid4721,t5_846choices,?_⟩
  exact check_of_frontier tree 0 t5_846root t5_846jobs t5_846frontier t5_846all
theorem t5_847choices : plan4722.choices=[2,9,9,9,9].map (options 5 4) := by rfl


theorem t5_847part0 : t5_847jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_847frontier : t5_847root.frontier 0=t5_847jobs := by rfl
theorem t5_847all : t5_847jobs.all (Job.check tree)=true := by
  simp only [t5_847jobs,List.all_append,List.all_nil,t5_847part0,Bool.and_self]
theorem t5_847checked : Checked tree [2,9,9,9,9] := by
  refine ⟨plan4722,valid4722,t5_847choices,?_⟩
  exact check_of_frontier tree 0 t5_847root t5_847jobs t5_847frontier t5_847all
theorem t5_848choices : plan4723.choices=[2,9,9,9,10].map (options 5 4) := by rfl


theorem t5_848part0 : t5_848jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_848frontier : t5_848root.frontier 0=t5_848jobs := by rfl
theorem t5_848all : t5_848jobs.all (Job.check tree)=true := by
  simp only [t5_848jobs,List.all_append,List.all_nil,t5_848part0,Bool.and_self]
theorem t5_848checked : Checked tree [2,9,9,9,10] := by
  refine ⟨plan4723,valid4723,t5_848choices,?_⟩
  exact check_of_frontier tree 0 t5_848root t5_848jobs t5_848frontier t5_848all
theorem t5_849choices : plan4724.choices=[2,9,9,10,7].map (options 5 4) := by rfl


theorem t5_849part0 : t5_849jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_849frontier : t5_849root.frontier 0=t5_849jobs := by rfl
theorem t5_849all : t5_849jobs.all (Job.check tree)=true := by
  simp only [t5_849jobs,List.all_append,List.all_nil,t5_849part0,Bool.and_self]
theorem t5_849checked : Checked tree [2,9,9,10,7] := by
  refine ⟨plan4724,valid4724,t5_849choices,?_⟩
  exact check_of_frontier tree 0 t5_849root t5_849jobs t5_849frontier t5_849all
theorem t5_850choices : plan4725.choices=[2,9,9,10,10].map (options 5 4) := by rfl


theorem t5_850part0 : t5_850jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_850frontier : t5_850root.frontier 0=t5_850jobs := by rfl
theorem t5_850all : t5_850jobs.all (Job.check tree)=true := by
  simp only [t5_850jobs,List.all_append,List.all_nil,t5_850part0,Bool.and_self]
theorem t5_850checked : Checked tree [2,9,9,10,10] := by
  refine ⟨plan4725,valid4725,t5_850choices,?_⟩
  exact check_of_frontier tree 0 t5_850root t5_850jobs t5_850frontier t5_850all
theorem t5_851choices : plan4726.choices=[2,9,10,7,7].map (options 5 4) := by rfl


theorem t5_851part0 : t5_851jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_851part1 : t5_851jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_851frontier : t5_851root.frontier 1=t5_851jobs := by rfl
theorem t5_851all : t5_851jobs.all (Job.check tree)=true := by
  simp only [t5_851jobs,List.all_append,List.all_nil,t5_851part0,t5_851part1,Bool.and_self]
theorem t5_851checked : Checked tree [2,9,10,7,7] := by
  refine ⟨plan4726,valid4726,t5_851choices,?_⟩
  exact check_of_frontier tree 1 t5_851root t5_851jobs t5_851frontier t5_851all
theorem t5_852choices : plan4727.choices=[2,9,10,10,7].map (options 5 4) := by rfl


theorem t5_852part0 : t5_852jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_852part1 : t5_852jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_852frontier : t5_852root.frontier 1=t5_852jobs := by rfl
theorem t5_852all : t5_852jobs.all (Job.check tree)=true := by
  simp only [t5_852jobs,List.all_append,List.all_nil,t5_852part0,t5_852part1,Bool.and_self]
theorem t5_852checked : Checked tree [2,9,10,10,7] := by
  refine ⟨plan4727,valid4727,t5_852choices,?_⟩
  exact check_of_frontier tree 1 t5_852root t5_852jobs t5_852frontier t5_852all
theorem t5_853choices : plan4728.choices=[2,9,10,10,10].map (options 5 4) := by rfl


theorem t5_853part0 : t5_853jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_853frontier : t5_853root.frontier 0=t5_853jobs := by rfl
theorem t5_853all : t5_853jobs.all (Job.check tree)=true := by
  simp only [t5_853jobs,List.all_append,List.all_nil,t5_853part0,Bool.and_self]
theorem t5_853checked : Checked tree [2,9,10,10,10] := by
  refine ⟨plan4728,valid4728,t5_853choices,?_⟩
  exact check_of_frontier tree 0 t5_853root t5_853jobs t5_853frontier t5_853all
theorem t5_854choices : plan4729.choices=[2,10,7,7,7].map (options 5 4) := by rfl


theorem t5_854part0 : t5_854jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_854part1 : t5_854jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_854frontier : t5_854root.frontier 1=t5_854jobs := by rfl
theorem t5_854all : t5_854jobs.all (Job.check tree)=true := by
  simp only [t5_854jobs,List.all_append,List.all_nil,t5_854part0,t5_854part1,Bool.and_self]
theorem t5_854checked : Checked tree [2,10,7,7,7] := by
  refine ⟨plan4729,valid4729,t5_854choices,?_⟩
  exact check_of_frontier tree 1 t5_854root t5_854jobs t5_854frontier t5_854all
theorem t5_855choices : plan4730.choices=[2,10,10,7,7].map (options 5 4) := by rfl


theorem t5_855part0 : t5_855jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_855part1 : t5_855jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_855frontier : t5_855root.frontier 1=t5_855jobs := by rfl
theorem t5_855all : t5_855jobs.all (Job.check tree)=true := by
  simp only [t5_855jobs,List.all_append,List.all_nil,t5_855part0,t5_855part1,Bool.and_self]
theorem t5_855checked : Checked tree [2,10,10,7,7] := by
  refine ⟨plan4730,valid4730,t5_855choices,?_⟩
  exact check_of_frontier tree 1 t5_855root t5_855jobs t5_855frontier t5_855all
theorem t5_856choices : plan4731.choices=[2,10,10,10,7].map (options 5 4) := by rfl


theorem t5_856part0 : t5_856jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_856frontier : t5_856root.frontier 0=t5_856jobs := by rfl
theorem t5_856all : t5_856jobs.all (Job.check tree)=true := by
  simp only [t5_856jobs,List.all_append,List.all_nil,t5_856part0,Bool.and_self]
theorem t5_856checked : Checked tree [2,10,10,10,7] := by
  refine ⟨plan4731,valid4731,t5_856choices,?_⟩
  exact check_of_frontier tree 0 t5_856root t5_856jobs t5_856frontier t5_856all
theorem t5_857choices : plan4732.choices=[2,10,10,10,10].map (options 5 4) := by rfl


theorem t5_857part0 : t5_857jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_857frontier : t5_857root.frontier 0=t5_857jobs := by rfl
theorem t5_857all : t5_857jobs.all (Job.check tree)=true := by
  simp only [t5_857jobs,List.all_append,List.all_nil,t5_857part0,Bool.and_self]
theorem t5_857checked : Checked tree [2,10,10,10,10] := by
  refine ⟨plan4732,valid4732,t5_857choices,?_⟩
  exact check_of_frontier tree 0 t5_857root t5_857jobs t5_857frontier t5_857all
theorem t5_858choices : plan3673.choices=[3,3,3,3,3].map (options 5 0) := by rfl


theorem t5_858part0 : t5_858jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_858frontier : t5_858root.frontier 0=t5_858jobs := by rfl
theorem t5_858all : t5_858jobs.all (Job.check tree)=true := by
  simp only [t5_858jobs,List.all_append,List.all_nil,t5_858part0,Bool.and_self]
theorem t5_858checked : Checked tree [3,3,3,3,3] := by
  refine ⟨plan3673,valid3673,t5_858choices,?_⟩
  exact check_of_frontier tree 0 t5_858root t5_858jobs t5_858frontier t5_858all
theorem t5_859choices : plan3746.choices=[3,3,3,3,6].map (options 5 1) := by rfl


theorem t5_859part0 : t5_859jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_859frontier : t5_859root.frontier 0=t5_859jobs := by rfl
theorem t5_859all : t5_859jobs.all (Job.check tree)=true := by
  simp only [t5_859jobs,List.all_append,List.all_nil,t5_859part0,Bool.and_self]
theorem t5_859checked : Checked tree [3,3,3,3,6] := by
  refine ⟨plan3746,valid3746,t5_859choices,?_⟩
  exact check_of_frontier tree 0 t5_859root t5_859jobs t5_859frontier t5_859all
theorem t5_860choices : plan3747.choices=[3,3,3,3,7].map (options 5 1) := by rfl


theorem t5_860part0 : t5_860jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_860frontier : t5_860root.frontier 0=t5_860jobs := by rfl
theorem t5_860all : t5_860jobs.all (Job.check tree)=true := by
  simp only [t5_860jobs,List.all_append,List.all_nil,t5_860part0,Bool.and_self]
theorem t5_860checked : Checked tree [3,3,3,3,7] := by
  refine ⟨plan3747,valid3747,t5_860choices,?_⟩
  exact check_of_frontier tree 0 t5_860root t5_860jobs t5_860frontier t5_860all
theorem t5_861choices : plan3748.choices=[3,3,3,3,10].map (options 5 1) := by rfl


theorem t5_861part0 : t5_861jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_861frontier : t5_861root.frontier 0=t5_861jobs := by rfl
theorem t5_861all : t5_861jobs.all (Job.check tree)=true := by
  simp only [t5_861jobs,List.all_append,List.all_nil,t5_861part0,Bool.and_self]
theorem t5_861checked : Checked tree [3,3,3,3,10] := by
  refine ⟨plan3748,valid3748,t5_861choices,?_⟩
  exact check_of_frontier tree 0 t5_861root t5_861jobs t5_861frontier t5_861all
theorem t5_862choices : plan3943.choices=[3,3,3,6,6].map (options 5 2) := by rfl


theorem t5_862part0 : t5_862jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_862frontier : t5_862root.frontier 0=t5_862jobs := by rfl
theorem t5_862all : t5_862jobs.all (Job.check tree)=true := by
  simp only [t5_862jobs,List.all_append,List.all_nil,t5_862part0,Bool.and_self]
theorem t5_862checked : Checked tree [3,3,3,6,6] := by
  refine ⟨plan3943,valid3943,t5_862choices,?_⟩
  exact check_of_frontier tree 0 t5_862root t5_862jobs t5_862frontier t5_862all
theorem t5_863choices : plan3944.choices=[3,3,3,6,7].map (options 5 2) := by rfl


theorem t5_863part0 : t5_863jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_863part1 : t5_863jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_863frontier : t5_863root.frontier 1=t5_863jobs := by rfl
theorem t5_863all : t5_863jobs.all (Job.check tree)=true := by
  simp only [t5_863jobs,List.all_append,List.all_nil,t5_863part0,t5_863part1,Bool.and_self]
theorem t5_863checked : Checked tree [3,3,3,6,7] := by
  refine ⟨plan3944,valid3944,t5_863choices,?_⟩
  exact check_of_frontier tree 1 t5_863root t5_863jobs t5_863frontier t5_863all
theorem t5_864choices : plan3945.choices=[3,3,3,6,10].map (options 5 2) := by rfl


theorem t5_864part0 : t5_864jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_864part1 : t5_864jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_864frontier : t5_864root.frontier 1=t5_864jobs := by rfl
theorem t5_864all : t5_864jobs.all (Job.check tree)=true := by
  simp only [t5_864jobs,List.all_append,List.all_nil,t5_864part0,t5_864part1,Bool.and_self]
theorem t5_864checked : Checked tree [3,3,3,6,10] := by
  refine ⟨plan3945,valid3945,t5_864choices,?_⟩
  exact check_of_frontier tree 1 t5_864root t5_864jobs t5_864frontier t5_864all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks026 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_851checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_839checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_852checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_853checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_854checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_855checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_856checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_857checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_858checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_859checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_840checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_860checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_861checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_862checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_863checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_864checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_841checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_842checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_843checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_844checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_845checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_846checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_847checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_848checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_849checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_850checked⟩
