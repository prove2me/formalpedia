-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks136
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:50:18.500697+00:00
-- url     : https://prove2.me/submissions/3d4f8670-87ed-4ff8-992b-c63157252952

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks136
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks136
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans078
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

theorem valid578 : plan578.Valid := valid_step _ _ _ valid134 (by decide +kernel)

theorem valid579 : plan579.Valid := valid_step _ _ _ valid134 (by decide +kernel)

theorem valid580 : plan580.Valid := valid_step _ _ _ valid135 (by decide +kernel)
























































































































































































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



















































































































theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)









theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)
























































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

































































































































































theorem valid3441 : plan3441.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3442 : plan3442.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3443 : plan3443.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3444 : plan3444.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3445 : plan3445.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3446 : plan3446.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3447 : plan3447.Valid := valid_step _ _ _ valid1604 (by decide +kernel)


















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















































































































































theorem valid5928 : plan5928.Valid := valid_step _ _ _ valid3441 (by decide +kernel)

theorem valid5929 : plan5929.Valid := valid_step _ _ _ valid3442 (by decide +kernel)

theorem valid5930 : plan5930.Valid := valid_step _ _ _ valid3443 (by decide +kernel)

theorem valid5931 : plan5931.Valid := valid_step _ _ _ valid3444 (by decide +kernel)

theorem valid5932 : plan5932.Valid := valid_step _ _ _ valid3445 (by decide +kernel)

theorem valid5933 : plan5933.Valid := valid_step _ _ _ valid3446 (by decide +kernel)

theorem valid5934 : plan5934.Valid := valid_step _ _ _ valid3447 (by decide +kernel)




































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





































































































































































theorem valid7571 : plan7571.Valid := valid_step _ _ _ valid5928 (by decide +kernel)

theorem valid7572 : plan7572.Valid := valid_step _ _ _ valid5929 (by decide +kernel)

theorem valid7573 : plan7573.Valid := valid_step _ _ _ valid5930 (by decide +kernel)

theorem valid7574 : plan7574.Valid := valid_step _ _ _ valid5931 (by decide +kernel)

theorem valid7575 : plan7575.Valid := valid_step _ _ _ valid5932 (by decide +kernel)

theorem valid7576 : plan7576.Valid := valid_step _ _ _ valid5933 (by decide +kernel)

theorem valid7577 : plan7577.Valid := valid_step _ _ _ valid5934 (by decide +kernel)














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
theorem t6_1336choices : plan7571.choices=[5,9,3,6,6,7].map (options 6 5) := by rfl


theorem t6_1336part0 : t6_1336jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1336part1 : t6_1336jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1336part2 : t6_1336jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1336frontier : t6_1336root.frontier 1=t6_1336jobs := by rfl
theorem t6_1336all : t6_1336jobs.all (Job.check tree)=true := by
  simp only [t6_1336jobs,List.all_append,List.all_nil,t6_1336part0,t6_1336part1,t6_1336part2,Bool.and_self]
theorem t6_1336checked : Checked tree [5,9,3,6,6,7] := by
  refine ⟨plan7571,valid7571,t6_1336choices,?_⟩
  exact check_of_frontier tree 1 t6_1336root t6_1336jobs t6_1336frontier t6_1336all
theorem t6_1337choices : plan7572.choices=[5,9,3,6,6,10].map (options 6 5) := by rfl


theorem t6_1337part0 : t6_1337jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1337frontier : t6_1337root.frontier 0=t6_1337jobs := by rfl
theorem t6_1337all : t6_1337jobs.all (Job.check tree)=true := by
  simp only [t6_1337jobs,List.all_append,List.all_nil,t6_1337part0,Bool.and_self]
theorem t6_1337checked : Checked tree [5,9,3,6,6,10] := by
  refine ⟨plan7572,valid7572,t6_1337choices,?_⟩
  exact check_of_frontier tree 0 t6_1337root t6_1337jobs t6_1337frontier t6_1337all
theorem t6_1338choices : plan7573.choices=[5,9,3,6,7,7].map (options 6 5) := by rfl


theorem t6_1338part0 : t6_1338jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1338part1 : t6_1338jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1338part2 : t6_1338jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1338part3 : t6_1338jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1338frontier : t6_1338root.frontier 2=t6_1338jobs := by rfl
theorem t6_1338all : t6_1338jobs.all (Job.check tree)=true := by
  simp only [t6_1338jobs,List.all_append,List.all_nil,t6_1338part0,t6_1338part1,t6_1338part2,t6_1338part3,Bool.and_self]
theorem t6_1338checked : Checked tree [5,9,3,6,7,7] := by
  refine ⟨plan7573,valid7573,t6_1338choices,?_⟩
  exact check_of_frontier tree 2 t6_1338root t6_1338jobs t6_1338frontier t6_1338all
theorem t6_1339choices : plan7574.choices=[5,9,3,6,10,7].map (options 6 5) := by rfl


theorem t6_1339part0 : t6_1339jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1339part1 : t6_1339jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1339part2 : t6_1339jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1339frontier : t6_1339root.frontier 1=t6_1339jobs := by rfl
theorem t6_1339all : t6_1339jobs.all (Job.check tree)=true := by
  simp only [t6_1339jobs,List.all_append,List.all_nil,t6_1339part0,t6_1339part1,t6_1339part2,Bool.and_self]
theorem t6_1339checked : Checked tree [5,9,3,6,10,7] := by
  refine ⟨plan7574,valid7574,t6_1339choices,?_⟩
  exact check_of_frontier tree 1 t6_1339root t6_1339jobs t6_1339frontier t6_1339all
theorem t6_1340choices : plan7575.choices=[5,9,3,6,10,10].map (options 6 5) := by rfl


theorem t6_1340part0 : t6_1340jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1340frontier : t6_1340root.frontier 0=t6_1340jobs := by rfl
theorem t6_1340all : t6_1340jobs.all (Job.check tree)=true := by
  simp only [t6_1340jobs,List.all_append,List.all_nil,t6_1340part0,Bool.and_self]
theorem t6_1340checked : Checked tree [5,9,3,6,10,10] := by
  refine ⟨plan7575,valid7575,t6_1340choices,?_⟩
  exact check_of_frontier tree 0 t6_1340root t6_1340jobs t6_1340frontier t6_1340all
theorem t6_1341choices : plan7576.choices=[5,9,3,7,7,7].map (options 6 5) := by rfl


theorem t6_1341part0 : t6_1341jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1341part1 : t6_1341jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1341part2 : t6_1341jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1341part3 : t6_1341jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1341frontier : t6_1341root.frontier 1=t6_1341jobs := by rfl
theorem t6_1341all : t6_1341jobs.all (Job.check tree)=true := by
  simp only [t6_1341jobs,List.all_append,List.all_nil,t6_1341part0,t6_1341part1,t6_1341part2,t6_1341part3,Bool.and_self]
theorem t6_1341checked : Checked tree [5,9,3,7,7,7] := by
  refine ⟨plan7576,valid7576,t6_1341choices,?_⟩
  exact check_of_frontier tree 1 t6_1341root t6_1341jobs t6_1341frontier t6_1341all
theorem t6_1342choices : plan7577.choices=[5,9,3,10,7,7].map (options 6 5) := by rfl


theorem t6_1342part0 : t6_1342jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1342part1 : t6_1342jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1342part2 : t6_1342jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1342part3 : t6_1342jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1342frontier : t6_1342root.frontier 2=t6_1342jobs := by rfl
theorem t6_1342all : t6_1342jobs.all (Job.check tree)=true := by
  simp only [t6_1342jobs,List.all_append,List.all_nil,t6_1342part0,t6_1342part1,t6_1342part2,t6_1342part3,Bool.and_self]
theorem t6_1342checked : Checked tree [5,9,3,10,7,7] := by
  refine ⟨plan7577,valid7577,t6_1342choices,?_⟩
  exact check_of_frontier tree 2 t6_1342root t6_1342jobs t6_1342frontier t6_1342all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks136 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1342checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1336checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1337checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1338checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1339checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1340checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1341checked⟩
