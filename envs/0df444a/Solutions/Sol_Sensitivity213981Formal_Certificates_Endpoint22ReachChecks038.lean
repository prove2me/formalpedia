-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks038
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:01:07.286993+00:00
-- url     : https://prove2.me/submissions/5b592f92-aa2c-44f2-90fb-4757498ef14a

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks038
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans050
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans053
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

theorem valid486 : plan486.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid487 : plan487.Valid := valid_step _ _ _ valid105 (by decide +kernel)





















































theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)





























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

theorem valid1337 : plan1337.Valid := valid_step _ _ _ valid486 (by decide +kernel)

theorem valid1338 : plan1338.Valid := valid_step _ _ _ valid487 (by decide +kernel)












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

theorem valid1409 : plan1409.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1410 : plan1410.Valid := valid_step _ _ _ valid517 (by decide +kernel)




























































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













































































theorem valid3975 : plan3975.Valid := valid_step _ _ _ valid2664 (by decide +kernel)


















































































































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

theorem valid2860 : plan2860.Valid := valid_step _ _ _ valid1337 (by decide +kernel)

theorem valid2861 : plan2861.Valid := valid_step _ _ _ valid1338 (by decide +kernel)






































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









theorem valid3077 : plan3077.Valid := valid_step _ _ _ valid1407 (by decide +kernel)

theorem valid3078 : plan3078.Valid := valid_step _ _ _ valid1408 (by decide +kernel)

theorem valid3079 : plan3079.Valid := valid_step _ _ _ valid1409 (by decide +kernel)

theorem valid3080 : plan3080.Valid := valid_step _ _ _ valid1410 (by decide +kernel)
















































































































































































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

































































































































theorem valid4385 : plan4385.Valid := valid_step _ _ _ valid2859 (by decide +kernel)

theorem valid4386 : plan4386.Valid := valid_step _ _ _ valid2860 (by decide +kernel)

theorem valid4387 : plan4387.Valid := valid_step _ _ _ valid2861 (by decide +kernel)


























































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



































































































































































theorem valid4882 : plan4882.Valid := valid_step _ _ _ valid3077 (by decide +kernel)

theorem valid4883 : plan4883.Valid := valid_step _ _ _ valid3078 (by decide +kernel)

theorem valid4884 : plan4884.Valid := valid_step _ _ _ valid3079 (by decide +kernel)

theorem valid4885 : plan4885.Valid := valid_step _ _ _ valid3080 (by decide +kernel)






















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















































































































































theorem valid5160 : plan5160.Valid := valid_step _ _ _ valid3179 (by decide +kernel)

theorem valid5161 : plan5161.Valid := valid_step _ _ _ valid3180 (by decide +kernel)

theorem valid5162 : plan5162.Valid := valid_step _ _ _ valid3181 (by decide +kernel)

theorem valid5163 : plan5163.Valid := valid_step _ _ _ valid3182 (by decide +kernel)

theorem valid5164 : plan5164.Valid := valid_step _ _ _ valid3183 (by decide +kernel)

theorem valid5165 : plan5165.Valid := valid_step _ _ _ valid3184 (by decide +kernel)

theorem valid5166 : plan5166.Valid := valid_step _ _ _ valid3185 (by decide +kernel)

theorem valid5167 : plan5167.Valid := valid_step _ _ _ valid3186 (by decide +kernel)

theorem valid5168 : plan5168.Valid := valid_step _ _ _ valid3187 (by decide +kernel)
































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
theorem t5_1290choices : plan5160.choices=[5,6,6,6,10].map (options 5 5) := by rfl


theorem t5_1290part0 : t5_1290jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1290frontier : t5_1290root.frontier 0=t5_1290jobs := by rfl
theorem t5_1290all : t5_1290jobs.all (Job.check tree)=true := by
  simp only [t5_1290jobs,List.all_append,List.all_nil,t5_1290part0,Bool.and_self]
theorem t5_1290checked : Checked tree [5,6,6,6,10] := by
  refine ⟨plan5160,valid5160,t5_1290choices,?_⟩
  exact check_of_frontier tree 0 t5_1290root t5_1290jobs t5_1290frontier t5_1290all
theorem t5_1291choices : plan5161.choices=[5,6,6,7,7].map (options 5 5) := by rfl


theorem t5_1291part0 : t5_1291jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1291frontier : t5_1291root.frontier 0=t5_1291jobs := by rfl
theorem t5_1291all : t5_1291jobs.all (Job.check tree)=true := by
  simp only [t5_1291jobs,List.all_append,List.all_nil,t5_1291part0,Bool.and_self]
theorem t5_1291checked : Checked tree [5,6,6,7,7] := by
  refine ⟨plan5161,valid5161,t5_1291choices,?_⟩
  exact check_of_frontier tree 0 t5_1291root t5_1291jobs t5_1291frontier t5_1291all
theorem t5_1292choices : plan5162.choices=[5,6,6,10,7].map (options 5 5) := by rfl


theorem t5_1292part0 : t5_1292jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1292frontier : t5_1292root.frontier 0=t5_1292jobs := by rfl
theorem t5_1292all : t5_1292jobs.all (Job.check tree)=true := by
  simp only [t5_1292jobs,List.all_append,List.all_nil,t5_1292part0,Bool.and_self]
theorem t5_1292checked : Checked tree [5,6,6,10,7] := by
  refine ⟨plan5162,valid5162,t5_1292choices,?_⟩
  exact check_of_frontier tree 0 t5_1292root t5_1292jobs t5_1292frontier t5_1292all
theorem t5_1293choices : plan5163.choices=[5,6,6,10,10].map (options 5 5) := by rfl


theorem t5_1293part0 : t5_1293jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1293frontier : t5_1293root.frontier 0=t5_1293jobs := by rfl
theorem t5_1293all : t5_1293jobs.all (Job.check tree)=true := by
  simp only [t5_1293jobs,List.all_append,List.all_nil,t5_1293part0,Bool.and_self]
theorem t5_1293checked : Checked tree [5,6,6,10,10] := by
  refine ⟨plan5163,valid5163,t5_1293choices,?_⟩
  exact check_of_frontier tree 0 t5_1293root t5_1293jobs t5_1293frontier t5_1293all
theorem t5_1294choices : plan5164.choices=[5,6,7,7,7].map (options 5 5) := by rfl


theorem t5_1294part0 : t5_1294jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1294frontier : t5_1294root.frontier 0=t5_1294jobs := by rfl
theorem t5_1294all : t5_1294jobs.all (Job.check tree)=true := by
  simp only [t5_1294jobs,List.all_append,List.all_nil,t5_1294part0,Bool.and_self]
theorem t5_1294checked : Checked tree [5,6,7,7,7] := by
  refine ⟨plan5164,valid5164,t5_1294choices,?_⟩
  exact check_of_frontier tree 0 t5_1294root t5_1294jobs t5_1294frontier t5_1294all
theorem t5_1295choices : plan5165.choices=[5,6,10,7,7].map (options 5 5) := by rfl


theorem t5_1295part0 : t5_1295jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1295frontier : t5_1295root.frontier 0=t5_1295jobs := by rfl
theorem t5_1295all : t5_1295jobs.all (Job.check tree)=true := by
  simp only [t5_1295jobs,List.all_append,List.all_nil,t5_1295part0,Bool.and_self]
theorem t5_1295checked : Checked tree [5,6,10,7,7] := by
  refine ⟨plan5165,valid5165,t5_1295choices,?_⟩
  exact check_of_frontier tree 0 t5_1295root t5_1295jobs t5_1295frontier t5_1295all
theorem t5_1296choices : plan5166.choices=[5,6,10,10,7].map (options 5 5) := by rfl


theorem t5_1296part0 : t5_1296jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1296frontier : t5_1296root.frontier 0=t5_1296jobs := by rfl
theorem t5_1296all : t5_1296jobs.all (Job.check tree)=true := by
  simp only [t5_1296jobs,List.all_append,List.all_nil,t5_1296part0,Bool.and_self]
theorem t5_1296checked : Checked tree [5,6,10,10,7] := by
  refine ⟨plan5166,valid5166,t5_1296choices,?_⟩
  exact check_of_frontier tree 0 t5_1296root t5_1296jobs t5_1296frontier t5_1296all
theorem t5_1297choices : plan5167.choices=[5,6,10,10,10].map (options 5 5) := by rfl


theorem t5_1297part0 : t5_1297jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1297frontier : t5_1297root.frontier 0=t5_1297jobs := by rfl
theorem t5_1297all : t5_1297jobs.all (Job.check tree)=true := by
  simp only [t5_1297jobs,List.all_append,List.all_nil,t5_1297part0,Bool.and_self]
theorem t5_1297checked : Checked tree [5,6,10,10,10] := by
  refine ⟨plan5167,valid5167,t5_1297choices,?_⟩
  exact check_of_frontier tree 0 t5_1297root t5_1297jobs t5_1297frontier t5_1297all
theorem t5_1298choices : plan5168.choices=[5,7,7,7,7].map (options 5 5) := by rfl


theorem t5_1298part0 : t5_1298jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1298frontier : t5_1298root.frontier 0=t5_1298jobs := by rfl
theorem t5_1298all : t5_1298jobs.all (Job.check tree)=true := by
  simp only [t5_1298jobs,List.all_append,List.all_nil,t5_1298part0,Bool.and_self]
theorem t5_1298checked : Checked tree [5,7,7,7,7] := by
  refine ⟨plan5168,valid5168,t5_1298choices,?_⟩
  exact check_of_frontier tree 0 t5_1298root t5_1298jobs t5_1298frontier t5_1298all
theorem t5_1299choices : plan3975.choices=[5,9,3,3,3].map (options 5 2) := by rfl


theorem t5_1299part0 : t5_1299jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1299frontier : t5_1299root.frontier 0=t5_1299jobs := by rfl
theorem t5_1299all : t5_1299jobs.all (Job.check tree)=true := by
  simp only [t5_1299jobs,List.all_append,List.all_nil,t5_1299part0,Bool.and_self]
theorem t5_1299checked : Checked tree [5,9,3,3,3] := by
  refine ⟨plan3975,valid3975,t5_1299choices,?_⟩
  exact check_of_frontier tree 0 t5_1299root t5_1299jobs t5_1299frontier t5_1299all
theorem t5_1300choices : plan4385.choices=[5,9,3,3,6].map (options 5 3) := by rfl


theorem t5_1300part0 : t5_1300jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1300part1 : t5_1300jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1300frontier : t5_1300root.frontier 1=t5_1300jobs := by rfl
theorem t5_1300all : t5_1300jobs.all (Job.check tree)=true := by
  simp only [t5_1300jobs,List.all_append,List.all_nil,t5_1300part0,t5_1300part1,Bool.and_self]
theorem t5_1300checked : Checked tree [5,9,3,3,6] := by
  refine ⟨plan4385,valid4385,t5_1300choices,?_⟩
  exact check_of_frontier tree 1 t5_1300root t5_1300jobs t5_1300frontier t5_1300all
theorem t5_1301choices : plan4386.choices=[5,9,3,3,7].map (options 5 3) := by rfl


theorem t5_1301part0 : t5_1301jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1301part1 : t5_1301jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1301part2 : t5_1301jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1301frontier : t5_1301root.frontier 1=t5_1301jobs := by rfl
theorem t5_1301all : t5_1301jobs.all (Job.check tree)=true := by
  simp only [t5_1301jobs,List.all_append,List.all_nil,t5_1301part0,t5_1301part1,t5_1301part2,Bool.and_self]
theorem t5_1301checked : Checked tree [5,9,3,3,7] := by
  refine ⟨plan4386,valid4386,t5_1301choices,?_⟩
  exact check_of_frontier tree 1 t5_1301root t5_1301jobs t5_1301frontier t5_1301all
theorem t5_1302choices : plan4387.choices=[5,9,3,3,10].map (options 5 3) := by rfl


theorem t5_1302part0 : t5_1302jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1302part1 : t5_1302jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1302frontier : t5_1302root.frontier 1=t5_1302jobs := by rfl
theorem t5_1302all : t5_1302jobs.all (Job.check tree)=true := by
  simp only [t5_1302jobs,List.all_append,List.all_nil,t5_1302part0,t5_1302part1,Bool.and_self]
theorem t5_1302checked : Checked tree [5,9,3,3,10] := by
  refine ⟨plan4387,valid4387,t5_1302choices,?_⟩
  exact check_of_frontier tree 1 t5_1302root t5_1302jobs t5_1302frontier t5_1302all
theorem t5_1303choices : plan4882.choices=[5,9,3,6,6].map (options 5 4) := by rfl


theorem t5_1303part0 : t5_1303jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1303frontier : t5_1303root.frontier 0=t5_1303jobs := by rfl
theorem t5_1303all : t5_1303jobs.all (Job.check tree)=true := by
  simp only [t5_1303jobs,List.all_append,List.all_nil,t5_1303part0,Bool.and_self]
theorem t5_1303checked : Checked tree [5,9,3,6,6] := by
  refine ⟨plan4882,valid4882,t5_1303choices,?_⟩
  exact check_of_frontier tree 0 t5_1303root t5_1303jobs t5_1303frontier t5_1303all
theorem t5_1304choices : plan4883.choices=[5,9,3,6,7].map (options 5 4) := by rfl


theorem t5_1304part0 : t5_1304jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1304part1 : t5_1304jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1304part2 : t5_1304jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1304frontier : t5_1304root.frontier 1=t5_1304jobs := by rfl
theorem t5_1304all : t5_1304jobs.all (Job.check tree)=true := by
  simp only [t5_1304jobs,List.all_append,List.all_nil,t5_1304part0,t5_1304part1,t5_1304part2,Bool.and_self]
theorem t5_1304checked : Checked tree [5,9,3,6,7] := by
  refine ⟨plan4883,valid4883,t5_1304choices,?_⟩
  exact check_of_frontier tree 1 t5_1304root t5_1304jobs t5_1304frontier t5_1304all
theorem t5_1305choices : plan4884.choices=[5,9,3,6,10].map (options 5 4) := by rfl


theorem t5_1305part0 : t5_1305jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1305part1 : t5_1305jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1305frontier : t5_1305root.frontier 1=t5_1305jobs := by rfl
theorem t5_1305all : t5_1305jobs.all (Job.check tree)=true := by
  simp only [t5_1305jobs,List.all_append,List.all_nil,t5_1305part0,t5_1305part1,Bool.and_self]
theorem t5_1305checked : Checked tree [5,9,3,6,10] := by
  refine ⟨plan4884,valid4884,t5_1305choices,?_⟩
  exact check_of_frontier tree 1 t5_1305root t5_1305jobs t5_1305frontier t5_1305all
theorem t5_1306choices : plan4885.choices=[5,9,3,7,7].map (options 5 4) := by rfl


theorem t5_1306part0 : t5_1306jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1306part1 : t5_1306jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1306frontier : t5_1306root.frontier 1=t5_1306jobs := by rfl
theorem t5_1306all : t5_1306jobs.all (Job.check tree)=true := by
  simp only [t5_1306jobs,List.all_append,List.all_nil,t5_1306part0,t5_1306part1,Bool.and_self]
theorem t5_1306checked : Checked tree [5,9,3,7,7] := by
  refine ⟨plan4885,valid4885,t5_1306choices,?_⟩
  exact check_of_frontier tree 1 t5_1306root t5_1306jobs t5_1306frontier t5_1306all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks038 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1290checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1301checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1302checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1303checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1304checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1305checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1306checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1291checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1292checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1293checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1294checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1295checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1296checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1297checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1298checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1299checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1300checked⟩
