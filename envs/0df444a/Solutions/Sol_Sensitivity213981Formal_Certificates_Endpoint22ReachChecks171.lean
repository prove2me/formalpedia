-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks171
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:08:09.447993+00:00
-- url     : https://prove2.me/submissions/256cb3a0-45c3-4792-8950-7db1cc2e1cb2

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks171
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks171
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
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











































































































theorem valid150 : plan150.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid151 : plan151.Valid := valid_step _ _ _ valid0 (by decide +kernel)


















































































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





























































theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)

theorem valid608 : plan608.Valid := valid_step _ _ _ valid150 (by decide +kernel)

theorem valid609 : plan609.Valid := valid_step _ _ _ valid151 (by decide +kernel)






























































































































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





































theorem valid1651 : plan1651.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1652 : plan1652.Valid := valid_step _ _ _ valid608 (by decide +kernel)

theorem valid1653 : plan1653.Valid := valid_step _ _ _ valid609 (by decide +kernel)






















































































































































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













































































theorem valid3591 : plan3591.Valid := valid_step _ _ _ valid1651 (by decide +kernel)

theorem valid3592 : plan3592.Valid := valid_step _ _ _ valid1652 (by decide +kernel)

theorem valid3593 : plan3593.Valid := valid_step _ _ _ valid1653 (by decide +kernel)














































































































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





























































































































































































theorem valid6143 : plan6143.Valid := valid_step _ _ _ valid3591 (by decide +kernel)

theorem valid6144 : plan6144.Valid := valid_step _ _ _ valid3592 (by decide +kernel)
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

theorem valid6145 : plan6145.Valid := valid_step _ _ _ valid3593 (by decide +kernel)






























































































































































































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

























































































































theorem valid8125 : plan8125.Valid := valid_step _ _ _ valid6143 (by decide +kernel)

theorem valid8126 : plan8126.Valid := valid_step _ _ _ valid6144 (by decide +kernel)

theorem valid8127 : plan8127.Valid := valid_step _ _ _ valid6145 (by decide +kernel)


































































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































































































































theorem valid8512 : plan8512.Valid := valid_step _ _ _ valid8125 (by decide +kernel)

theorem valid8513 : plan8513.Valid := valid_step _ _ _ valid8126 (by decide +kernel)

theorem valid8514 : plan8514.Valid := valid_step _ _ _ valid8127 (by decide +kernel)




























































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
theorem t7_281choices : plan8512.choices=[3,3,3,6,6,7,7].map (options 7 4) := by rfl


theorem t7_281part0 : t7_281jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_281part1 : t7_281jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_281part2 : t7_281jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_281part3 : t7_281jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_281part4 : t7_281jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_281part5 : t7_281jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_281frontier : t7_281root.frontier 4=t7_281jobs := by rfl
theorem t7_281all : t7_281jobs.all (Job.check tree)=true := by
  simp only [t7_281jobs,List.all_append,List.all_nil,t7_281part0,t7_281part1,t7_281part2,t7_281part3,t7_281part4,t7_281part5,Bool.and_self]
theorem t7_281checked : Checked tree [3,3,3,6,6,7,7] := by
  refine ⟨plan8512,valid8512,t7_281choices,?_⟩
  exact check_of_frontier tree 4 t7_281root t7_281jobs t7_281frontier t7_281all
theorem t7_282choices : plan8513.choices=[3,3,3,6,6,10,7].map (options 7 4) := by rfl


theorem t7_282part0 : t7_282jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_282part1 : t7_282jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_282part2 : t7_282jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_282part3 : t7_282jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_282frontier : t7_282root.frontier 4=t7_282jobs := by rfl
theorem t7_282all : t7_282jobs.all (Job.check tree)=true := by
  simp only [t7_282jobs,List.all_append,List.all_nil,t7_282part0,t7_282part1,t7_282part2,t7_282part3,Bool.and_self]
theorem t7_282checked : Checked tree [3,3,3,6,6,10,7] := by
  refine ⟨plan8513,valid8513,t7_282choices,?_⟩
  exact check_of_frontier tree 4 t7_282root t7_282jobs t7_282frontier t7_282all
theorem t7_283choices : plan8514.choices=[3,3,3,6,6,10,10].map (options 7 4) := by rfl


theorem t7_283part0 : t7_283jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_283frontier : t7_283root.frontier 0=t7_283jobs := by rfl
theorem t7_283all : t7_283jobs.all (Job.check tree)=true := by
  simp only [t7_283jobs,List.all_append,List.all_nil,t7_283part0,Bool.and_self]
theorem t7_283checked : Checked tree [3,3,3,6,6,10,10] := by
  refine ⟨plan8514,valid8514,t7_283choices,?_⟩
  exact check_of_frontier tree 0 t7_283root t7_283jobs t7_283frontier t7_283all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks171 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_281checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_282checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_283checked⟩
