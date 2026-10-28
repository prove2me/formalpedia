-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks180
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:11:49.930117+00:00
-- url     : https://prove2.me/submissions/078d1124-79de-45cd-ad2e-c98117945522

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks180
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks180
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
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

















































































































theorem valid153 : plan153.Valid := valid_step _ _ _ valid0 (by decide +kernel)














































































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









































































theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)






















































































































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































































theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)
































































































































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































































































































theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3617 : plan3617.Valid := valid_step _ _ _ valid1664 (by decide +kernel)






























































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





































































































theorem valid6195 : plan6195.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6196 : plan6196.Valid := valid_step _ _ _ valid3617 (by decide +kernel)
























































































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



































































theorem valid8194 : plan8194.Valid := valid_step _ _ _ valid6195 (by decide +kernel)

theorem valid8195 : plan8195.Valid := valid_step _ _ _ valid6196 (by decide +kernel)


























































































































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



















theorem valid8650 : plan8650.Valid := valid_step _ _ _ valid8194 (by decide +kernel)

theorem valid8651 : plan8651.Valid := valid_step _ _ _ valid8195 (by decide +kernel)










































































































































































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
theorem t7_309choices : plan8650.choices=[3,3,10,7,7,7,7].map (options 7 5) := by rfl


theorem t7_309part0 : t7_309jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_309part1 : t7_309jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_309part2 : t7_309jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_309part3 : t7_309jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_309part4 : t7_309jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_309part5 : t7_309jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_309part6 : t7_309jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_309part7 : t7_309jobs7.all (Job.check tree)=true := by decide +kernel

theorem t7_309part8 : t7_309jobs8.all (Job.check tree)=true := by decide +kernel

theorem t7_309part9 : t7_309jobs9.all (Job.check tree)=true := by decide +kernel

theorem t7_309frontier : t7_309root.frontier 3=t7_309jobs := by rfl
theorem t7_309all : t7_309jobs.all (Job.check tree)=true := by
  simp only [t7_309jobs,List.all_append,List.all_nil,t7_309part0,t7_309part1,t7_309part2,t7_309part3,t7_309part4,t7_309part5,t7_309part6,t7_309part7,t7_309part8,t7_309part9,Bool.and_self]
theorem t7_309checked : Checked tree [3,3,10,7,7,7,7] := by
  refine ⟨plan8650,valid8650,t7_309choices,?_⟩
  exact check_of_frontier tree 3 t7_309root t7_309jobs t7_309frontier t7_309all
theorem t7_310choices : plan8651.choices=[3,3,10,10,7,7,7].map (options 7 5) := by rfl


theorem t7_310part0 : t7_310jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_310part1 : t7_310jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_310part2 : t7_310jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_310part3 : t7_310jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_310part4 : t7_310jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_310part5 : t7_310jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_310part6 : t7_310jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_310frontier : t7_310root.frontier 3=t7_310jobs := by rfl
theorem t7_310all : t7_310jobs.all (Job.check tree)=true := by
  simp only [t7_310jobs,List.all_append,List.all_nil,t7_310part0,t7_310part1,t7_310part2,t7_310part3,t7_310part4,t7_310part5,t7_310part6,Bool.and_self]
theorem t7_310checked : Checked tree [3,3,10,10,7,7,7] := by
  refine ⟨plan8651,valid8651,t7_310choices,?_⟩
  exact check_of_frontier tree 3 t7_310root t7_310jobs t7_310frontier t7_310all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks180 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_309checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_310checked⟩
