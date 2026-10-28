-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks129
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:48:27.269893+00:00
-- url     : https://prove2.me/submissions/163a8576-0605-4e8a-887b-dd846a5e3ceb

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks129
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks129
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
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





































































theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid133 : plan133.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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























































































































































































theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid573 : plan573.Valid := valid_step _ _ _ valid132 (by decide +kernel)



theorem valid575 : plan575.Valid := valid_step _ _ _ valid133 (by decide +kernel)

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

























































































theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1582 : plan1582.Valid := valid_step _ _ _ valid573 (by decide +kernel)





















theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)








































































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















theorem valid3368 : plan3368.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3369 : plan3369.Valid := valid_step _ _ _ valid1582 (by decide +kernel)














































































































































































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



























































































































theorem valid5630 : plan5630.Valid := valid_step _ _ _ valid3368 (by decide +kernel)

theorem valid5631 : plan5631.Valid := valid_step _ _ _ valid3369 (by decide +kernel)


































































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





































theorem valid3475 : plan3475.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3477 : plan3477.Valid := valid_step _ _ _ valid1595 (by decide +kernel)

theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)




















































































































































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



















theorem valid5770 : plan5770.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5771 : plan5771.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5772 : plan5772.Valid := valid_step _ _ _ valid3477 (by decide +kernel)

theorem valid5773 : plan5773.Valid := valid_step _ _ _ valid3478 (by decide +kernel)






































































































































































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





















































































theorem valid7051 : plan7051.Valid := valid_step _ _ _ valid5630 (by decide +kernel)

theorem valid7052 : plan7052.Valid := valid_step _ _ _ valid5631 (by decide +kernel)








































































































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



















































































theorem valid7530 : plan7530.Valid := valid_step _ _ _ valid5770 (by decide +kernel)

theorem valid7531 : plan7531.Valid := valid_step _ _ _ valid5771 (by decide +kernel)

theorem valid7532 : plan7532.Valid := valid_step _ _ _ valid5772 (by decide +kernel)

theorem valid7533 : plan7533.Valid := valid_step _ _ _ valid5773 (by decide +kernel)






































































































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
theorem t6_1205choices : plan7051.choices=[5,3,3,10,10,7].map (options 6 4) := by rfl


theorem t6_1205part0 : t6_1205jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1205part1 : t6_1205jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1205part2 : t6_1205jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1205part3 : t6_1205jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1205part4 : t6_1205jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1205part5 : t6_1205jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1205frontier : t6_1205root.frontier 2=t6_1205jobs := by rfl
theorem t6_1205all : t6_1205jobs.all (Job.check tree)=true := by
  simp only [t6_1205jobs,List.all_append,List.all_nil,t6_1205part0,t6_1205part1,t6_1205part2,t6_1205part3,t6_1205part4,t6_1205part5,Bool.and_self]
theorem t6_1205checked : Checked tree [5,3,3,10,10,7] := by
  refine ⟨plan7051,valid7051,t6_1205choices,?_⟩
  exact check_of_frontier tree 2 t6_1205root t6_1205jobs t6_1205frontier t6_1205all
theorem t6_1206choices : plan7052.choices=[5,3,3,10,10,10].map (options 6 4) := by rfl


theorem t6_1206part0 : t6_1206jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1206part1 : t6_1206jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1206frontier : t6_1206root.frontier 1=t6_1206jobs := by rfl
theorem t6_1206all : t6_1206jobs.all (Job.check tree)=true := by
  simp only [t6_1206jobs,List.all_append,List.all_nil,t6_1206part0,t6_1206part1,Bool.and_self]
theorem t6_1206checked : Checked tree [5,3,3,10,10,10] := by
  refine ⟨plan7052,valid7052,t6_1206choices,?_⟩
  exact check_of_frontier tree 1 t6_1206root t6_1206jobs t6_1206frontier t6_1206all
theorem t6_1207choices : plan7530.choices=[5,3,6,6,6,6].map (options 6 5) := by rfl


theorem t6_1207part0 : t6_1207jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1207frontier : t6_1207root.frontier 0=t6_1207jobs := by rfl
theorem t6_1207all : t6_1207jobs.all (Job.check tree)=true := by
  simp only [t6_1207jobs,List.all_append,List.all_nil,t6_1207part0,Bool.and_self]
theorem t6_1207checked : Checked tree [5,3,6,6,6,6] := by
  refine ⟨plan7530,valid7530,t6_1207choices,?_⟩
  exact check_of_frontier tree 0 t6_1207root t6_1207jobs t6_1207frontier t6_1207all
theorem t6_1208choices : plan7531.choices=[5,3,6,6,6,7].map (options 6 5) := by rfl


theorem t6_1208part0 : t6_1208jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1208part1 : t6_1208jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1208frontier : t6_1208root.frontier 1=t6_1208jobs := by rfl
theorem t6_1208all : t6_1208jobs.all (Job.check tree)=true := by
  simp only [t6_1208jobs,List.all_append,List.all_nil,t6_1208part0,t6_1208part1,Bool.and_self]
theorem t6_1208checked : Checked tree [5,3,6,6,6,7] := by
  refine ⟨plan7531,valid7531,t6_1208choices,?_⟩
  exact check_of_frontier tree 1 t6_1208root t6_1208jobs t6_1208frontier t6_1208all
theorem t6_1209choices : plan7532.choices=[5,3,6,6,6,10].map (options 6 5) := by rfl


theorem t6_1209part0 : t6_1209jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1209frontier : t6_1209root.frontier 0=t6_1209jobs := by rfl
theorem t6_1209all : t6_1209jobs.all (Job.check tree)=true := by
  simp only [t6_1209jobs,List.all_append,List.all_nil,t6_1209part0,Bool.and_self]
theorem t6_1209checked : Checked tree [5,3,6,6,6,10] := by
  refine ⟨plan7532,valid7532,t6_1209choices,?_⟩
  exact check_of_frontier tree 0 t6_1209root t6_1209jobs t6_1209frontier t6_1209all
theorem t6_1210choices : plan7533.choices=[5,3,6,6,7,7].map (options 6 5) := by rfl


theorem t6_1210part0 : t6_1210jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1210part1 : t6_1210jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1210part2 : t6_1210jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1210part3 : t6_1210jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1210part4 : t6_1210jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1210frontier : t6_1210root.frontier 2=t6_1210jobs := by rfl
theorem t6_1210all : t6_1210jobs.all (Job.check tree)=true := by
  simp only [t6_1210jobs,List.all_append,List.all_nil,t6_1210part0,t6_1210part1,t6_1210part2,t6_1210part3,t6_1210part4,Bool.and_self]
theorem t6_1210checked : Checked tree [5,3,6,6,7,7] := by
  refine ⟨plan7533,valid7533,t6_1210choices,?_⟩
  exact check_of_frontier tree 2 t6_1210root t6_1210jobs t6_1210frontier t6_1210all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks129 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1210checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1205checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1206checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1207checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1208checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1209checked⟩
