-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks069
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:16:53.241596+00:00
-- url     : https://prove2.me/submissions/41e81e74-87de-44f5-97f7-88b033a2afb0

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
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























































theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid125 : plan125.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)
































































































































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

















































































































































theorem valid553 : plan553.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid554 : plan554.Valid := valid_step _ _ _ valid125 (by decide +kernel)









theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)
































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





































































































































































theorem valid1523 : plan1523.Valid := valid_step _ _ _ valid553 (by decide +kernel)

theorem valid1524 : plan1524.Valid := valid_step _ _ _ valid554 (by decide +kernel)
























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











theorem valid1542 : plan1542.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1543 : plan1543.Valid := valid_step _ _ _ valid560 (by decide +kernel)


















































































































































































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















theorem valid3272 : plan3272.Valid := valid_step _ _ _ valid1523 (by decide +kernel)

theorem valid3273 : plan3273.Valid := valid_step _ _ _ valid1524 (by decide +kernel)













































































theorem valid3312 : plan3312.Valid := valid_step _ _ _ valid1542 (by decide +kernel)

theorem valid3313 : plan3313.Valid := valid_step _ _ _ valid1543 (by decide +kernel)






























































































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















































theorem valid5400 : plan5400.Valid := valid_step _ _ _ valid3272 (by decide +kernel)

theorem valid5401 : plan5401.Valid := valid_step _ _ _ valid3273 (by decide +kernel)














































































































































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



























theorem valid5486 : plan5486.Valid := valid_step _ _ _ valid3312 (by decide +kernel)

theorem valid5487 : plan5487.Valid := valid_step _ _ _ valid3313 (by decide +kernel)


































































































































































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











































































































theorem valid6390 : plan6390.Valid := valid_step _ _ _ valid5400 (by decide +kernel)

theorem valid6391 : plan6391.Valid := valid_step _ _ _ valid5401 (by decide +kernel)


















































































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

































































































theorem valid6577 : plan6577.Valid := valid_step _ _ _ valid5486 (by decide +kernel)

theorem valid6578 : plan6578.Valid := valid_step _ _ _ valid5487 (by decide +kernel)




























































































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
theorem t6_639choices : plan6390.choices=[2,3,3,3,10,7].map (options 6 2) := by rfl


theorem t6_639part0 : t6_639jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_639part1 : t6_639jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_639part2 : t6_639jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_639part3 : t6_639jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_639part4 : t6_639jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_639frontier : t6_639root.frontier 1=t6_639jobs := by rfl
theorem t6_639all : t6_639jobs.all (Job.check tree)=true := by
  simp only [t6_639jobs,List.all_append,List.all_nil,t6_639part0,t6_639part1,t6_639part2,t6_639part3,t6_639part4,Bool.and_self]
theorem t6_639checked : Checked tree [2,3,3,3,10,7] := by
  refine ⟨plan6390,valid6390,t6_639choices,?_⟩
  exact check_of_frontier tree 1 t6_639root t6_639jobs t6_639frontier t6_639all
theorem t6_640choices : plan6391.choices=[2,3,3,3,10,10].map (options 6 2) := by rfl


theorem t6_640part0 : t6_640jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_640part1 : t6_640jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_640frontier : t6_640root.frontier 1=t6_640jobs := by rfl
theorem t6_640all : t6_640jobs.all (Job.check tree)=true := by
  simp only [t6_640jobs,List.all_append,List.all_nil,t6_640part0,t6_640part1,Bool.and_self]
theorem t6_640checked : Checked tree [2,3,3,3,10,10] := by
  refine ⟨plan6391,valid6391,t6_640choices,?_⟩
  exact check_of_frontier tree 1 t6_640root t6_640jobs t6_640frontier t6_640all
theorem t6_641choices : plan6577.choices=[2,3,3,6,6,6].map (options 6 3) := by rfl


theorem t6_641part0 : t6_641jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_641part1 : t6_641jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_641frontier : t6_641root.frontier 1=t6_641jobs := by rfl
theorem t6_641all : t6_641jobs.all (Job.check tree)=true := by
  simp only [t6_641jobs,List.all_append,List.all_nil,t6_641part0,t6_641part1,Bool.and_self]
theorem t6_641checked : Checked tree [2,3,3,6,6,6] := by
  refine ⟨plan6577,valid6577,t6_641choices,?_⟩
  exact check_of_frontier tree 1 t6_641root t6_641jobs t6_641frontier t6_641all
theorem t6_642choices : plan6578.choices=[2,3,3,6,6,7].map (options 6 3) := by rfl


theorem t6_642part0 : t6_642jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_642part1 : t6_642jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_642part2 : t6_642jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_642part3 : t6_642jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_642part4 : t6_642jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_642part5 : t6_642jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_642part6 : t6_642jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_642part7 : t6_642jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_642frontier : t6_642root.frontier 2=t6_642jobs := by rfl
theorem t6_642all : t6_642jobs.all (Job.check tree)=true := by
  simp only [t6_642jobs,List.all_append,List.all_nil,t6_642part0,t6_642part1,t6_642part2,t6_642part3,t6_642part4,t6_642part5,t6_642part6,t6_642part7,Bool.and_self]
theorem t6_642checked : Checked tree [2,3,3,6,6,7] := by
  refine ⟨plan6578,valid6578,t6_642choices,?_⟩
  exact check_of_frontier tree 2 t6_642root t6_642jobs t6_642frontier t6_642all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks069 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_642checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_639checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_640checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_641checked⟩
