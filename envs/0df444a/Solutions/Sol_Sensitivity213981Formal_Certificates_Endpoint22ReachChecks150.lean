-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks150
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:57:45.573006+00:00
-- url     : https://prove2.me/submissions/344f1ded-cac6-4774-81c9-3db7a2a30077

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks150
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks150
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans079
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





























































theorem valid7135 : plan7135.Valid := valid_step _ _ _ valid5630 (by decide +kernel)

theorem valid7136 : plan7136.Valid := valid_step _ _ _ valid5631 (by decide +kernel)
































































































































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















































































































































































theorem valid7672 : plan7672.Valid := valid_step _ _ _ valid5770 (by decide +kernel)

theorem valid7673 : plan7673.Valid := valid_step _ _ _ valid5771 (by decide +kernel)

theorem valid7674 : plan7674.Valid := valid_step _ _ _ valid5772 (by decide +kernel)

theorem valid7675 : plan7675.Valid := valid_step _ _ _ valid5773 (by decide +kernel)










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
theorem t6_1693choices : plan7135.choices=[9,3,3,10,10,7].map (options 6 4) := by rfl


theorem t6_1693part0 : t6_1693jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1693part1 : t6_1693jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1693part2 : t6_1693jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1693part3 : t6_1693jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1693part4 : t6_1693jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1693part5 : t6_1693jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1693frontier : t6_1693root.frontier 2=t6_1693jobs := by rfl
theorem t6_1693all : t6_1693jobs.all (Job.check tree)=true := by
  simp only [t6_1693jobs,List.all_append,List.all_nil,t6_1693part0,t6_1693part1,t6_1693part2,t6_1693part3,t6_1693part4,t6_1693part5,Bool.and_self]
theorem t6_1693checked : Checked tree [9,3,3,10,10,7] := by
  refine ⟨plan7135,valid7135,t6_1693choices,?_⟩
  exact check_of_frontier tree 2 t6_1693root t6_1693jobs t6_1693frontier t6_1693all
theorem t6_1694choices : plan7136.choices=[9,3,3,10,10,10].map (options 6 4) := by rfl


theorem t6_1694part0 : t6_1694jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1694part1 : t6_1694jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1694frontier : t6_1694root.frontier 1=t6_1694jobs := by rfl
theorem t6_1694all : t6_1694jobs.all (Job.check tree)=true := by
  simp only [t6_1694jobs,List.all_append,List.all_nil,t6_1694part0,t6_1694part1,Bool.and_self]
theorem t6_1694checked : Checked tree [9,3,3,10,10,10] := by
  refine ⟨plan7136,valid7136,t6_1694choices,?_⟩
  exact check_of_frontier tree 1 t6_1694root t6_1694jobs t6_1694frontier t6_1694all
theorem t6_1695choices : plan7672.choices=[9,3,6,6,6,6].map (options 6 5) := by rfl


theorem t6_1695part0 : t6_1695jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1695frontier : t6_1695root.frontier 0=t6_1695jobs := by rfl
theorem t6_1695all : t6_1695jobs.all (Job.check tree)=true := by
  simp only [t6_1695jobs,List.all_append,List.all_nil,t6_1695part0,Bool.and_self]
theorem t6_1695checked : Checked tree [9,3,6,6,6,6] := by
  refine ⟨plan7672,valid7672,t6_1695choices,?_⟩
  exact check_of_frontier tree 0 t6_1695root t6_1695jobs t6_1695frontier t6_1695all
theorem t6_1696choices : plan7673.choices=[9,3,6,6,6,7].map (options 6 5) := by rfl


theorem t6_1696part0 : t6_1696jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1696part1 : t6_1696jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1696frontier : t6_1696root.frontier 1=t6_1696jobs := by rfl
theorem t6_1696all : t6_1696jobs.all (Job.check tree)=true := by
  simp only [t6_1696jobs,List.all_append,List.all_nil,t6_1696part0,t6_1696part1,Bool.and_self]
theorem t6_1696checked : Checked tree [9,3,6,6,6,7] := by
  refine ⟨plan7673,valid7673,t6_1696choices,?_⟩
  exact check_of_frontier tree 1 t6_1696root t6_1696jobs t6_1696frontier t6_1696all
theorem t6_1697choices : plan7674.choices=[9,3,6,6,6,10].map (options 6 5) := by rfl


theorem t6_1697part0 : t6_1697jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1697frontier : t6_1697root.frontier 0=t6_1697jobs := by rfl
theorem t6_1697all : t6_1697jobs.all (Job.check tree)=true := by
  simp only [t6_1697jobs,List.all_append,List.all_nil,t6_1697part0,Bool.and_self]
theorem t6_1697checked : Checked tree [9,3,6,6,6,10] := by
  refine ⟨plan7674,valid7674,t6_1697choices,?_⟩
  exact check_of_frontier tree 0 t6_1697root t6_1697jobs t6_1697frontier t6_1697all
theorem t6_1698choices : plan7675.choices=[9,3,6,6,7,7].map (options 6 5) := by rfl


theorem t6_1698part0 : t6_1698jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1698part1 : t6_1698jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1698part2 : t6_1698jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1698part3 : t6_1698jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1698part4 : t6_1698jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1698frontier : t6_1698root.frontier 2=t6_1698jobs := by rfl
theorem t6_1698all : t6_1698jobs.all (Job.check tree)=true := by
  simp only [t6_1698jobs,List.all_append,List.all_nil,t6_1698part0,t6_1698part1,t6_1698part2,t6_1698part3,t6_1698part4,Bool.and_self]
theorem t6_1698checked : Checked tree [9,3,6,6,7,7] := by
  refine ⟨plan7675,valid7675,t6_1698choices,?_⟩
  exact check_of_frontier tree 2 t6_1698root t6_1698jobs t6_1698frontier t6_1698all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks150 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1698checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1693checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1694checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1695checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1696checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1697checked⟩
