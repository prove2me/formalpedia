-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks124
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:48:08.062453+00:00
-- url     : https://prove2.me/submissions/8db5d1cc-321e-4608-96b5-62a374aa8c83

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks124
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks124
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
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































































theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)






























































































































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































































































































































theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)

theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)




























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

























































































































































































theorem valid1533 : plan1533.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1534 : plan1534.Valid := valid_step _ _ _ valid561 (by decide +kernel)

theorem valid1535 : plan1535.Valid := valid_step _ _ _ valid562 (by decide +kernel)


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





















































































theorem valid3307 : plan3307.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3308 : plan3308.Valid := valid_step _ _ _ valid1534 (by decide +kernel)

theorem valid3309 : plan3309.Valid := valid_step _ _ _ valid1535 (by decide +kernel)






































































































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

















theorem valid5481 : plan5481.Valid := valid_step _ _ _ valid3307 (by decide +kernel)

theorem valid5482 : plan5482.Valid := valid_step _ _ _ valid3308 (by decide +kernel)

theorem valid5483 : plan5483.Valid := valid_step _ _ _ valid3309 (by decide +kernel)










































































































































































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









































theorem valid6645 : plan6645.Valid := valid_step _ _ _ valid5481 (by decide +kernel)

theorem valid6646 : plan6646.Valid := valid_step _ _ _ valid5482 (by decide +kernel)

theorem valid6647 : plan6647.Valid := valid_step _ _ _ valid5483 (by decide +kernel)


















































































































































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
theorem t6_1192choices : plan6645.choices=[5,3,3,3,6,7].map (options 6 3) := by rfl


theorem t6_1192part0 : t6_1192jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1192part1 : t6_1192jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1192part2 : t6_1192jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1192part3 : t6_1192jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1192part4 : t6_1192jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1192part5 : t6_1192jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1192frontier : t6_1192root.frontier 2=t6_1192jobs := by rfl
theorem t6_1192all : t6_1192jobs.all (Job.check tree)=true := by
  simp only [t6_1192jobs,List.all_append,List.all_nil,t6_1192part0,t6_1192part1,t6_1192part2,t6_1192part3,t6_1192part4,t6_1192part5,Bool.and_self]
theorem t6_1192checked : Checked tree [5,3,3,3,6,7] := by
  refine ⟨plan6645,valid6645,t6_1192choices,?_⟩
  exact check_of_frontier tree 2 t6_1192root t6_1192jobs t6_1192frontier t6_1192all
theorem t6_1193choices : plan6646.choices=[5,3,3,3,6,10].map (options 6 3) := by rfl


theorem t6_1193part0 : t6_1193jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1193part1 : t6_1193jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1193part2 : t6_1193jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1193part3 : t6_1193jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1193frontier : t6_1193root.frontier 1=t6_1193jobs := by rfl
theorem t6_1193all : t6_1193jobs.all (Job.check tree)=true := by
  simp only [t6_1193jobs,List.all_append,List.all_nil,t6_1193part0,t6_1193part1,t6_1193part2,t6_1193part3,Bool.and_self]
theorem t6_1193checked : Checked tree [5,3,3,3,6,10] := by
  refine ⟨plan6646,valid6646,t6_1193choices,?_⟩
  exact check_of_frontier tree 1 t6_1193root t6_1193jobs t6_1193frontier t6_1193all
theorem t6_1194choices : plan6647.choices=[5,3,3,3,7,7].map (options 6 3) := by rfl


theorem t6_1194part0 : t6_1194jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1194part1 : t6_1194jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1194part2 : t6_1194jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1194part3 : t6_1194jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1194part4 : t6_1194jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1194frontier : t6_1194root.frontier 2=t6_1194jobs := by rfl
theorem t6_1194all : t6_1194jobs.all (Job.check tree)=true := by
  simp only [t6_1194jobs,List.all_append,List.all_nil,t6_1194part0,t6_1194part1,t6_1194part2,t6_1194part3,t6_1194part4,Bool.and_self]
theorem t6_1194checked : Checked tree [5,3,3,3,7,7] := by
  refine ⟨plan6647,valid6647,t6_1194choices,?_⟩
  exact check_of_frontier tree 2 t6_1194root t6_1194jobs t6_1194frontier t6_1194all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks124 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1194checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1192checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1193checked⟩
