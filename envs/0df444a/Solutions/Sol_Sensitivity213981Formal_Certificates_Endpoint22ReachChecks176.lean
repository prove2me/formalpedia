-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks176
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:10:25.841204+00:00
-- url     : https://prove2.me/submissions/b3a3d4ed-3fd6-44cd-9668-3dfa99a74253

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks176
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks176
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
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

theorem valid154 : plan154.Valid := valid_step _ _ _ valid0 (by decide +kernel)












































































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

theorem valid614 : plan614.Valid := valid_step _ _ _ valid153 (by decide +kernel)

theorem valid615 : plan615.Valid := valid_step _ _ _ valid154 (by decide +kernel)


















































































































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

theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1666 : plan1666.Valid := valid_step _ _ _ valid614 (by decide +kernel)

theorem valid1667 : plan1667.Valid := valid_step _ _ _ valid615 (by decide +kernel)


























































































































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























































































































theorem valid3612 : plan3612.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3613 : plan3613.Valid := valid_step _ _ _ valid1665 (by decide +kernel)

theorem valid3614 : plan3614.Valid := valid_step _ _ _ valid1666 (by decide +kernel)

theorem valid3615 : plan3615.Valid := valid_step _ _ _ valid1667 (by decide +kernel)


































































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









































































theorem valid6181 : plan6181.Valid := valid_step _ _ _ valid3612 (by decide +kernel)

theorem valid6182 : plan6182.Valid := valid_step _ _ _ valid3613 (by decide +kernel)

theorem valid6183 : plan6183.Valid := valid_step _ _ _ valid3614 (by decide +kernel)

theorem valid6184 : plan6184.Valid := valid_step _ _ _ valid3615 (by decide +kernel)
















































































































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















































theorem valid8184 : plan8184.Valid := valid_step _ _ _ valid6181 (by decide +kernel)

theorem valid8185 : plan8185.Valid := valid_step _ _ _ valid6182 (by decide +kernel)

theorem valid8186 : plan8186.Valid := valid_step _ _ _ valid6183 (by decide +kernel)

theorem valid8187 : plan8187.Valid := valid_step _ _ _ valid6184 (by decide +kernel)










































































































































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































































































































































































theorem valid8640 : plan8640.Valid := valid_step _ _ _ valid8184 (by decide +kernel)
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

theorem valid8641 : plan8641.Valid := valid_step _ _ _ valid8185 (by decide +kernel)

theorem valid8642 : plan8642.Valid := valid_step _ _ _ valid8186 (by decide +kernel)

theorem valid8643 : plan8643.Valid := valid_step _ _ _ valid8187 (by decide +kernel)


























































































































































































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
theorem t7_299choices : plan8640.choices=[3,3,6,6,7,7,7].map (options 7 5) := by rfl


theorem t7_299part0 : t7_299jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_299part1 : t7_299jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_299part2 : t7_299jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_299part3 : t7_299jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_299part4 : t7_299jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_299part5 : t7_299jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_299part6 : t7_299jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_299frontier : t7_299root.frontier 3=t7_299jobs := by rfl
theorem t7_299all : t7_299jobs.all (Job.check tree)=true := by
  simp only [t7_299jobs,List.all_append,List.all_nil,t7_299part0,t7_299part1,t7_299part2,t7_299part3,t7_299part4,t7_299part5,t7_299part6,Bool.and_self]
theorem t7_299checked : Checked tree [3,3,6,6,7,7,7] := by
  refine ⟨plan8640,valid8640,t7_299choices,?_⟩
  exact check_of_frontier tree 3 t7_299root t7_299jobs t7_299frontier t7_299all
theorem t7_300choices : plan8641.choices=[3,3,6,6,10,7,7].map (options 7 5) := by rfl


theorem t7_300part0 : t7_300jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_300part1 : t7_300jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_300part2 : t7_300jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_300part3 : t7_300jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_300part4 : t7_300jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_300part5 : t7_300jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_300part6 : t7_300jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_300frontier : t7_300root.frontier 3=t7_300jobs := by rfl
theorem t7_300all : t7_300jobs.all (Job.check tree)=true := by
  simp only [t7_300jobs,List.all_append,List.all_nil,t7_300part0,t7_300part1,t7_300part2,t7_300part3,t7_300part4,t7_300part5,t7_300part6,Bool.and_self]
theorem t7_300checked : Checked tree [3,3,6,6,10,7,7] := by
  refine ⟨plan8641,valid8641,t7_300choices,?_⟩
  exact check_of_frontier tree 3 t7_300root t7_300jobs t7_300frontier t7_300all
theorem t7_301choices : plan8642.choices=[3,3,6,6,10,10,7].map (options 7 5) := by rfl


theorem t7_301part0 : t7_301jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_301part1 : t7_301jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_301part2 : t7_301jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_301frontier : t7_301root.frontier 3=t7_301jobs := by rfl
theorem t7_301all : t7_301jobs.all (Job.check tree)=true := by
  simp only [t7_301jobs,List.all_append,List.all_nil,t7_301part0,t7_301part1,t7_301part2,Bool.and_self]
theorem t7_301checked : Checked tree [3,3,6,6,10,10,7] := by
  refine ⟨plan8642,valid8642,t7_301choices,?_⟩
  exact check_of_frontier tree 3 t7_301root t7_301jobs t7_301frontier t7_301all
theorem t7_302choices : plan8643.choices=[3,3,6,6,10,10,10].map (options 7 5) := by rfl


theorem t7_302part0 : t7_302jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_302frontier : t7_302root.frontier 0=t7_302jobs := by rfl
theorem t7_302all : t7_302jobs.all (Job.check tree)=true := by
  simp only [t7_302jobs,List.all_append,List.all_nil,t7_302part0,Bool.and_self]
theorem t7_302checked : Checked tree [3,3,6,6,10,10,10] := by
  refine ⟨plan8643,valid8643,t7_302choices,?_⟩
  exact check_of_frontier tree 0 t7_302root t7_302jobs t7_302frontier t7_302all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks176 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_300checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_301checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_302checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_299checked⟩
