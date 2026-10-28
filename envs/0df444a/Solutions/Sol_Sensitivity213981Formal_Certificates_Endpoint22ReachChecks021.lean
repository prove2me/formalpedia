-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks021
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:47:19.478915+00:00
-- url     : https://prove2.me/submissions/739ad870-0a59-43f4-b6f2-0829f3afd19c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks021
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks021
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



theorem valid107 : plan107.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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

theorem valid488 : plan488.Valid := valid_step _ _ _ valid100 (by decide +kernel)



















theorem valid498 : plan498.Valid := valid_step _ _ _ valid100 (by decide +kernel)











theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)









theorem valid509 : plan509.Valid := valid_step _ _ _ valid107 (by decide +kernel)

theorem valid510 : plan510.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid511 : plan511.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid512 : plan512.Valid := valid_step _ _ _ valid110 (by decide +kernel)

theorem valid513 : plan513.Valid := valid_step _ _ _ valid111 (by decide +kernel)

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























































































































theorem valid1308 : plan1308.Valid := valid_step _ _ _ valid462 (by decide +kernel)







































































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











theorem valid1350 : plan1350.Valid := valid_step _ _ _ valid485 (by decide +kernel)

theorem valid1351 : plan1351.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1352 : plan1352.Valid := valid_step _ _ _ valid487 (by decide +kernel)

theorem valid1353 : plan1353.Valid := valid_step _ _ _ valid488 (by decide +kernel)



















theorem valid1363 : plan1363.Valid := valid_step _ _ _ valid498 (by decide +kernel)



















































































































theorem valid1421 : plan1421.Valid := valid_step _ _ _ valid509 (by decide +kernel)

theorem valid1422 : plan1422.Valid := valid_step _ _ _ valid510 (by decide +kernel)

theorem valid1423 : plan1423.Valid := valid_step _ _ _ valid511 (by decide +kernel)

theorem valid1424 : plan1424.Valid := valid_step _ _ _ valid512 (by decide +kernel)

theorem valid1425 : plan1425.Valid := valid_step _ _ _ valid513 (by decide +kernel)

theorem valid1426 : plan1426.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1427 : plan1427.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1428 : plan1428.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1429 : plan1429.Valid := valid_step _ _ _ valid517 (by decide +kernel)



theorem valid1431 : plan1431.Valid := valid_step _ _ _ valid519 (by decide +kernel)

theorem valid1432 : plan1432.Valid := valid_step _ _ _ valid520 (by decide +kernel)

theorem valid1433 : plan1433.Valid := valid_step _ _ _ valid521 (by decide +kernel)

theorem valid1434 : plan1434.Valid := valid_step _ _ _ valid522 (by decide +kernel)

theorem valid1435 : plan1435.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1436 : plan1436.Valid := valid_step _ _ _ valid524 (by decide +kernel)

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





















































































































theorem valid2651 : plan2651.Valid := valid_step _ _ _ valid1308 (by decide +kernel)










































































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

theorem valid3937 : plan3937.Valid := valid_step _ _ _ valid2651 (by decide +kernel)






























































































































































































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

































































theorem valid2817 : plan2817.Valid := valid_step _ _ _ valid1344 (by decide +kernel)



theorem valid2819 : plan2819.Valid := valid_step _ _ _ valid1350 (by decide +kernel)

theorem valid2820 : plan2820.Valid := valid_step _ _ _ valid1351 (by decide +kernel)

theorem valid2821 : plan2821.Valid := valid_step _ _ _ valid1352 (by decide +kernel)

theorem valid2822 : plan2822.Valid := valid_step _ _ _ valid1353 (by decide +kernel)

theorem valid2823 : plan2823.Valid := valid_step _ _ _ valid1363 (by decide +kernel)


















































































































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

theorem valid2977 : plan2977.Valid := valid_step _ _ _ valid1421 (by decide +kernel)

theorem valid2978 : plan2978.Valid := valid_step _ _ _ valid1422 (by decide +kernel)

theorem valid2979 : plan2979.Valid := valid_step _ _ _ valid1423 (by decide +kernel)

theorem valid2980 : plan2980.Valid := valid_step _ _ _ valid1424 (by decide +kernel)

theorem valid2981 : plan2981.Valid := valid_step _ _ _ valid1425 (by decide +kernel)

theorem valid2982 : plan2982.Valid := valid_step _ _ _ valid1426 (by decide +kernel)

theorem valid2983 : plan2983.Valid := valid_step _ _ _ valid1427 (by decide +kernel)

theorem valid2984 : plan2984.Valid := valid_step _ _ _ valid1428 (by decide +kernel)

theorem valid2985 : plan2985.Valid := valid_step _ _ _ valid1429 (by decide +kernel)



theorem valid2987 : plan2987.Valid := valid_step _ _ _ valid1431 (by decide +kernel)

theorem valid2988 : plan2988.Valid := valid_step _ _ _ valid1432 (by decide +kernel)

theorem valid2989 : plan2989.Valid := valid_step _ _ _ valid1433 (by decide +kernel)

theorem valid2990 : plan2990.Valid := valid_step _ _ _ valid1434 (by decide +kernel)

theorem valid2991 : plan2991.Valid := valid_step _ _ _ valid1435 (by decide +kernel)

theorem valid2992 : plan2992.Valid := valid_step _ _ _ valid1436 (by decide +kernel)

theorem valid2993 : plan2993.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid2994 : plan2994.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid2995 : plan2995.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid2996 : plan2996.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid2997 : plan2997.Valid := valid_step _ _ _ valid1441 (by decide +kernel)






















































































































































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













































































































theorem valid4663 : plan4663.Valid := valid_step _ _ _ valid2977 (by decide +kernel)

theorem valid4664 : plan4664.Valid := valid_step _ _ _ valid2978 (by decide +kernel)

theorem valid4665 : plan4665.Valid := valid_step _ _ _ valid2979 (by decide +kernel)

theorem valid4666 : plan4666.Valid := valid_step _ _ _ valid2980 (by decide +kernel)

theorem valid4667 : plan4667.Valid := valid_step _ _ _ valid2981 (by decide +kernel)

theorem valid4668 : plan4668.Valid := valid_step _ _ _ valid2982 (by decide +kernel)

theorem valid4669 : plan4669.Valid := valid_step _ _ _ valid2983 (by decide +kernel)

theorem valid4670 : plan4670.Valid := valid_step _ _ _ valid2984 (by decide +kernel)

theorem valid4671 : plan4671.Valid := valid_step _ _ _ valid2985 (by decide +kernel)

theorem valid4672 : plan4672.Valid := valid_step _ _ _ valid2987 (by decide +kernel)

theorem valid4673 : plan4673.Valid := valid_step _ _ _ valid2988 (by decide +kernel)

theorem valid4674 : plan4674.Valid := valid_step _ _ _ valid2989 (by decide +kernel)

theorem valid4675 : plan4675.Valid := valid_step _ _ _ valid2990 (by decide +kernel)

theorem valid4676 : plan4676.Valid := valid_step _ _ _ valid2991 (by decide +kernel)

theorem valid4677 : plan4677.Valid := valid_step _ _ _ valid2992 (by decide +kernel)

theorem valid4678 : plan4678.Valid := valid_step _ _ _ valid2993 (by decide +kernel)

theorem valid4679 : plan4679.Valid := valid_step _ _ _ valid2994 (by decide +kernel)

theorem valid4680 : plan4680.Valid := valid_step _ _ _ valid2995 (by decide +kernel)

theorem valid4681 : plan4681.Valid := valid_step _ _ _ valid2996 (by decide +kernel)

theorem valid4682 : plan4682.Valid := valid_step _ _ _ valid2997 (by decide +kernel)












































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























































































































theorem valid4284 : plan4284.Valid := valid_step _ _ _ valid2817 (by decide +kernel)

theorem valid4285 : plan4285.Valid := valid_step _ _ _ valid2819 (by decide +kernel)

theorem valid4286 : plan4286.Valid := valid_step _ _ _ valid2820 (by decide +kernel)

theorem valid4287 : plan4287.Valid := valid_step _ _ _ valid2821 (by decide +kernel)

theorem valid4288 : plan4288.Valid := valid_step _ _ _ valid2822 (by decide +kernel)

theorem valid4289 : plan4289.Valid := valid_step _ _ _ valid2823 (by decide +kernel)






























































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
theorem t5_761choices : plan4284.choices=[2,5,3,10,10].map (options 5 3) := by rfl


theorem t5_761part0 : t5_761jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_761part1 : t5_761jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_761frontier : t5_761root.frontier 1=t5_761jobs := by rfl
theorem t5_761all : t5_761jobs.all (Job.check tree)=true := by
  simp only [t5_761jobs,List.all_append,List.all_nil,t5_761part0,t5_761part1,Bool.and_self]
theorem t5_761checked : Checked tree [2,5,3,10,10] := by
  refine ⟨plan4284,valid4284,t5_761choices,?_⟩
  exact check_of_frontier tree 1 t5_761root t5_761jobs t5_761frontier t5_761all
theorem t5_762choices : plan3937.choices=[2,5,5,3,3].map (options 5 2) := by rfl


theorem t5_762part0 : t5_762jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_762frontier : t5_762root.frontier 0=t5_762jobs := by rfl
theorem t5_762all : t5_762jobs.all (Job.check tree)=true := by
  simp only [t5_762jobs,List.all_append,List.all_nil,t5_762part0,Bool.and_self]
theorem t5_762checked : Checked tree [2,5,5,3,3] := by
  refine ⟨plan3937,valid3937,t5_762choices,?_⟩
  exact check_of_frontier tree 0 t5_762root t5_762jobs t5_762frontier t5_762all
theorem t5_763choices : plan4285.choices=[2,5,5,3,6].map (options 5 3) := by rfl


theorem t5_763part0 : t5_763jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_763frontier : t5_763root.frontier 0=t5_763jobs := by rfl
theorem t5_763all : t5_763jobs.all (Job.check tree)=true := by
  simp only [t5_763jobs,List.all_append,List.all_nil,t5_763part0,Bool.and_self]
theorem t5_763checked : Checked tree [2,5,5,3,6] := by
  refine ⟨plan4285,valid4285,t5_763choices,?_⟩
  exact check_of_frontier tree 0 t5_763root t5_763jobs t5_763frontier t5_763all
theorem t5_764choices : plan4286.choices=[2,5,5,3,7].map (options 5 3) := by rfl


theorem t5_764part0 : t5_764jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_764part1 : t5_764jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_764frontier : t5_764root.frontier 1=t5_764jobs := by rfl
theorem t5_764all : t5_764jobs.all (Job.check tree)=true := by
  simp only [t5_764jobs,List.all_append,List.all_nil,t5_764part0,t5_764part1,Bool.and_self]
theorem t5_764checked : Checked tree [2,5,5,3,7] := by
  refine ⟨plan4286,valid4286,t5_764choices,?_⟩
  exact check_of_frontier tree 1 t5_764root t5_764jobs t5_764frontier t5_764all
theorem t5_765choices : plan4287.choices=[2,5,5,3,10].map (options 5 3) := by rfl


theorem t5_765part0 : t5_765jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_765frontier : t5_765root.frontier 0=t5_765jobs := by rfl
theorem t5_765all : t5_765jobs.all (Job.check tree)=true := by
  simp only [t5_765jobs,List.all_append,List.all_nil,t5_765part0,Bool.and_self]
theorem t5_765checked : Checked tree [2,5,5,3,10] := by
  refine ⟨plan4287,valid4287,t5_765choices,?_⟩
  exact check_of_frontier tree 0 t5_765root t5_765jobs t5_765frontier t5_765all
theorem t5_766choices : plan4288.choices=[2,5,5,5,3].map (options 5 3) := by rfl


theorem t5_766part0 : t5_766jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_766frontier : t5_766root.frontier 0=t5_766jobs := by rfl
theorem t5_766all : t5_766jobs.all (Job.check tree)=true := by
  simp only [t5_766jobs,List.all_append,List.all_nil,t5_766part0,Bool.and_self]
theorem t5_766checked : Checked tree [2,5,5,5,3] := by
  refine ⟨plan4288,valid4288,t5_766choices,?_⟩
  exact check_of_frontier tree 0 t5_766root t5_766jobs t5_766frontier t5_766all
theorem t5_767choices : plan4663.choices=[2,5,5,5,5].map (options 5 4) := by rfl


theorem t5_767part0 : t5_767jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_767frontier : t5_767root.frontier 0=t5_767jobs := by rfl
theorem t5_767all : t5_767jobs.all (Job.check tree)=true := by
  simp only [t5_767jobs,List.all_append,List.all_nil,t5_767part0,Bool.and_self]
theorem t5_767checked : Checked tree [2,5,5,5,5] := by
  refine ⟨plan4663,valid4663,t5_767choices,?_⟩
  exact check_of_frontier tree 0 t5_767root t5_767jobs t5_767frontier t5_767all
theorem t5_768choices : plan4664.choices=[2,5,5,5,6].map (options 5 4) := by rfl


theorem t5_768part0 : t5_768jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_768frontier : t5_768root.frontier 0=t5_768jobs := by rfl
theorem t5_768all : t5_768jobs.all (Job.check tree)=true := by
  simp only [t5_768jobs,List.all_append,List.all_nil,t5_768part0,Bool.and_self]
theorem t5_768checked : Checked tree [2,5,5,5,6] := by
  refine ⟨plan4664,valid4664,t5_768choices,?_⟩
  exact check_of_frontier tree 0 t5_768root t5_768jobs t5_768frontier t5_768all
theorem t5_769choices : plan4665.choices=[2,5,5,5,7].map (options 5 4) := by rfl


theorem t5_769part0 : t5_769jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_769frontier : t5_769root.frontier 0=t5_769jobs := by rfl
theorem t5_769all : t5_769jobs.all (Job.check tree)=true := by
  simp only [t5_769jobs,List.all_append,List.all_nil,t5_769part0,Bool.and_self]
theorem t5_769checked : Checked tree [2,5,5,5,7] := by
  refine ⟨plan4665,valid4665,t5_769choices,?_⟩
  exact check_of_frontier tree 0 t5_769root t5_769jobs t5_769frontier t5_769all
theorem t5_770choices : plan4666.choices=[2,5,5,5,9].map (options 5 4) := by rfl


theorem t5_770part0 : t5_770jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_770frontier : t5_770root.frontier 0=t5_770jobs := by rfl
theorem t5_770all : t5_770jobs.all (Job.check tree)=true := by
  simp only [t5_770jobs,List.all_append,List.all_nil,t5_770part0,Bool.and_self]
theorem t5_770checked : Checked tree [2,5,5,5,9] := by
  refine ⟨plan4666,valid4666,t5_770choices,?_⟩
  exact check_of_frontier tree 0 t5_770root t5_770jobs t5_770frontier t5_770all
theorem t5_771choices : plan4667.choices=[2,5,5,5,10].map (options 5 4) := by rfl


theorem t5_771part0 : t5_771jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_771frontier : t5_771root.frontier 0=t5_771jobs := by rfl
theorem t5_771all : t5_771jobs.all (Job.check tree)=true := by
  simp only [t5_771jobs,List.all_append,List.all_nil,t5_771part0,Bool.and_self]
theorem t5_771checked : Checked tree [2,5,5,5,10] := by
  refine ⟨plan4667,valid4667,t5_771choices,?_⟩
  exact check_of_frontier tree 0 t5_771root t5_771jobs t5_771frontier t5_771all
theorem t5_772choices : plan4668.choices=[2,5,5,6,6].map (options 5 4) := by rfl


theorem t5_772part0 : t5_772jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_772frontier : t5_772root.frontier 0=t5_772jobs := by rfl
theorem t5_772all : t5_772jobs.all (Job.check tree)=true := by
  simp only [t5_772jobs,List.all_append,List.all_nil,t5_772part0,Bool.and_self]
theorem t5_772checked : Checked tree [2,5,5,6,6] := by
  refine ⟨plan4668,valid4668,t5_772choices,?_⟩
  exact check_of_frontier tree 0 t5_772root t5_772jobs t5_772frontier t5_772all
theorem t5_773choices : plan4669.choices=[2,5,5,6,7].map (options 5 4) := by rfl


theorem t5_773part0 : t5_773jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_773frontier : t5_773root.frontier 0=t5_773jobs := by rfl
theorem t5_773all : t5_773jobs.all (Job.check tree)=true := by
  simp only [t5_773jobs,List.all_append,List.all_nil,t5_773part0,Bool.and_self]
theorem t5_773checked : Checked tree [2,5,5,6,7] := by
  refine ⟨plan4669,valid4669,t5_773choices,?_⟩
  exact check_of_frontier tree 0 t5_773root t5_773jobs t5_773frontier t5_773all
theorem t5_774choices : plan4670.choices=[2,5,5,6,10].map (options 5 4) := by rfl


theorem t5_774part0 : t5_774jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_774frontier : t5_774root.frontier 0=t5_774jobs := by rfl
theorem t5_774all : t5_774jobs.all (Job.check tree)=true := by
  simp only [t5_774jobs,List.all_append,List.all_nil,t5_774part0,Bool.and_self]
theorem t5_774checked : Checked tree [2,5,5,6,10] := by
  refine ⟨plan4670,valid4670,t5_774choices,?_⟩
  exact check_of_frontier tree 0 t5_774root t5_774jobs t5_774frontier t5_774all
theorem t5_775choices : plan4671.choices=[2,5,5,7,7].map (options 5 4) := by rfl


theorem t5_775part0 : t5_775jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_775frontier : t5_775root.frontier 0=t5_775jobs := by rfl
theorem t5_775all : t5_775jobs.all (Job.check tree)=true := by
  simp only [t5_775jobs,List.all_append,List.all_nil,t5_775part0,Bool.and_self]
theorem t5_775checked : Checked tree [2,5,5,7,7] := by
  refine ⟨plan4671,valid4671,t5_775choices,?_⟩
  exact check_of_frontier tree 0 t5_775root t5_775jobs t5_775frontier t5_775all
theorem t5_776choices : plan4289.choices=[2,5,5,9,3].map (options 5 3) := by rfl


theorem t5_776part0 : t5_776jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_776frontier : t5_776root.frontier 0=t5_776jobs := by rfl
theorem t5_776all : t5_776jobs.all (Job.check tree)=true := by
  simp only [t5_776jobs,List.all_append,List.all_nil,t5_776part0,Bool.and_self]
theorem t5_776checked : Checked tree [2,5,5,9,3] := by
  refine ⟨plan4289,valid4289,t5_776choices,?_⟩
  exact check_of_frontier tree 0 t5_776root t5_776jobs t5_776frontier t5_776all
theorem t5_777choices : plan4672.choices=[2,5,5,9,6].map (options 5 4) := by rfl


theorem t5_777part0 : t5_777jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_777frontier : t5_777root.frontier 0=t5_777jobs := by rfl
theorem t5_777all : t5_777jobs.all (Job.check tree)=true := by
  simp only [t5_777jobs,List.all_append,List.all_nil,t5_777part0,Bool.and_self]
theorem t5_777checked : Checked tree [2,5,5,9,6] := by
  refine ⟨plan4672,valid4672,t5_777choices,?_⟩
  exact check_of_frontier tree 0 t5_777root t5_777jobs t5_777frontier t5_777all
theorem t5_778choices : plan4673.choices=[2,5,5,9,7].map (options 5 4) := by rfl


theorem t5_778part0 : t5_778jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_778frontier : t5_778root.frontier 0=t5_778jobs := by rfl
theorem t5_778all : t5_778jobs.all (Job.check tree)=true := by
  simp only [t5_778jobs,List.all_append,List.all_nil,t5_778part0,Bool.and_self]
theorem t5_778checked : Checked tree [2,5,5,9,7] := by
  refine ⟨plan4673,valid4673,t5_778choices,?_⟩
  exact check_of_frontier tree 0 t5_778root t5_778jobs t5_778frontier t5_778all
theorem t5_779choices : plan4674.choices=[2,5,5,9,9].map (options 5 4) := by rfl


theorem t5_779part0 : t5_779jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_779frontier : t5_779root.frontier 0=t5_779jobs := by rfl
theorem t5_779all : t5_779jobs.all (Job.check tree)=true := by
  simp only [t5_779jobs,List.all_append,List.all_nil,t5_779part0,Bool.and_self]
theorem t5_779checked : Checked tree [2,5,5,9,9] := by
  refine ⟨plan4674,valid4674,t5_779choices,?_⟩
  exact check_of_frontier tree 0 t5_779root t5_779jobs t5_779frontier t5_779all
theorem t5_780choices : plan4675.choices=[2,5,5,9,10].map (options 5 4) := by rfl


theorem t5_780part0 : t5_780jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_780frontier : t5_780root.frontier 0=t5_780jobs := by rfl
theorem t5_780all : t5_780jobs.all (Job.check tree)=true := by
  simp only [t5_780jobs,List.all_append,List.all_nil,t5_780part0,Bool.and_self]
theorem t5_780checked : Checked tree [2,5,5,9,10] := by
  refine ⟨plan4675,valid4675,t5_780choices,?_⟩
  exact check_of_frontier tree 0 t5_780root t5_780jobs t5_780frontier t5_780all
theorem t5_781choices : plan4676.choices=[2,5,5,10,7].map (options 5 4) := by rfl


theorem t5_781part0 : t5_781jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_781frontier : t5_781root.frontier 0=t5_781jobs := by rfl
theorem t5_781all : t5_781jobs.all (Job.check tree)=true := by
  simp only [t5_781jobs,List.all_append,List.all_nil,t5_781part0,Bool.and_self]
theorem t5_781checked : Checked tree [2,5,5,10,7] := by
  refine ⟨plan4676,valid4676,t5_781choices,?_⟩
  exact check_of_frontier tree 0 t5_781root t5_781jobs t5_781frontier t5_781all
theorem t5_782choices : plan4677.choices=[2,5,5,10,10].map (options 5 4) := by rfl


theorem t5_782part0 : t5_782jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_782frontier : t5_782root.frontier 0=t5_782jobs := by rfl
theorem t5_782all : t5_782jobs.all (Job.check tree)=true := by
  simp only [t5_782jobs,List.all_append,List.all_nil,t5_782part0,Bool.and_self]
theorem t5_782checked : Checked tree [2,5,5,10,10] := by
  refine ⟨plan4677,valid4677,t5_782choices,?_⟩
  exact check_of_frontier tree 0 t5_782root t5_782jobs t5_782frontier t5_782all
theorem t5_783choices : plan4678.choices=[2,5,6,6,6].map (options 5 4) := by rfl


theorem t5_783part0 : t5_783jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_783frontier : t5_783root.frontier 0=t5_783jobs := by rfl
theorem t5_783all : t5_783jobs.all (Job.check tree)=true := by
  simp only [t5_783jobs,List.all_append,List.all_nil,t5_783part0,Bool.and_self]
theorem t5_783checked : Checked tree [2,5,6,6,6] := by
  refine ⟨plan4678,valid4678,t5_783choices,?_⟩
  exact check_of_frontier tree 0 t5_783root t5_783jobs t5_783frontier t5_783all
theorem t5_784choices : plan4679.choices=[2,5,6,6,7].map (options 5 4) := by rfl


theorem t5_784part0 : t5_784jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_784part1 : t5_784jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_784frontier : t5_784root.frontier 1=t5_784jobs := by rfl
theorem t5_784all : t5_784jobs.all (Job.check tree)=true := by
  simp only [t5_784jobs,List.all_append,List.all_nil,t5_784part0,t5_784part1,Bool.and_self]
theorem t5_784checked : Checked tree [2,5,6,6,7] := by
  refine ⟨plan4679,valid4679,t5_784choices,?_⟩
  exact check_of_frontier tree 1 t5_784root t5_784jobs t5_784frontier t5_784all
theorem t5_785choices : plan4680.choices=[2,5,6,6,10].map (options 5 4) := by rfl


theorem t5_785part0 : t5_785jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_785frontier : t5_785root.frontier 0=t5_785jobs := by rfl
theorem t5_785all : t5_785jobs.all (Job.check tree)=true := by
  simp only [t5_785jobs,List.all_append,List.all_nil,t5_785part0,Bool.and_self]
theorem t5_785checked : Checked tree [2,5,6,6,10] := by
  refine ⟨plan4680,valid4680,t5_785choices,?_⟩
  exact check_of_frontier tree 0 t5_785root t5_785jobs t5_785frontier t5_785all
theorem t5_786choices : plan4681.choices=[2,5,6,7,7].map (options 5 4) := by rfl


theorem t5_786part0 : t5_786jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_786part1 : t5_786jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_786frontier : t5_786root.frontier 1=t5_786jobs := by rfl
theorem t5_786all : t5_786jobs.all (Job.check tree)=true := by
  simp only [t5_786jobs,List.all_append,List.all_nil,t5_786part0,t5_786part1,Bool.and_self]
theorem t5_786checked : Checked tree [2,5,6,7,7] := by
  refine ⟨plan4681,valid4681,t5_786choices,?_⟩
  exact check_of_frontier tree 1 t5_786root t5_786jobs t5_786frontier t5_786all
theorem t5_787choices : plan4682.choices=[2,5,6,10,7].map (options 5 4) := by rfl


theorem t5_787part0 : t5_787jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_787part1 : t5_787jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_787part2 : t5_787jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_787frontier : t5_787root.frontier 2=t5_787jobs := by rfl
theorem t5_787all : t5_787jobs.all (Job.check tree)=true := by
  simp only [t5_787jobs,List.all_append,List.all_nil,t5_787part0,t5_787part1,t5_787part2,Bool.and_self]
theorem t5_787checked : Checked tree [2,5,6,10,7] := by
  refine ⟨plan4682,valid4682,t5_787choices,?_⟩
  exact check_of_frontier tree 2 t5_787root t5_787jobs t5_787frontier t5_787all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks021 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_773checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_774checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_775checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_776checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_777checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_761checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_778checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_779checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_780checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_781checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_782checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_783checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_784checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_785checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_786checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_762checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_787checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_763checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_764checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_765checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_766checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_767checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_768checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_769checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_770checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_771checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_772checked⟩
