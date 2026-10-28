-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks111
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:39:30.917983+00:00
-- url     : https://prove2.me/submissions/a193ace4-e389-489a-8f3f-6f4e7322e49f

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks111
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks111
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
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























































































































theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)


































































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











































theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)

theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)














































































































































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



























































theorem valid5886 : plan5886.Valid := valid_step _ _ _ valid3478 (by decide +kernel)

theorem valid5887 : plan5887.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5888 : plan5888.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5889 : plan5889.Valid := valid_step _ _ _ valid3481 (by decide +kernel)






























































































































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















































theorem valid7416 : plan7416.Valid := valid_step _ _ _ valid5886 (by decide +kernel)

theorem valid7417 : plan7417.Valid := valid_step _ _ _ valid5887 (by decide +kernel)

theorem valid7418 : plan7418.Valid := valid_step _ _ _ valid5888 (by decide +kernel)

theorem valid7419 : plan7419.Valid := valid_step _ _ _ valid5889 (by decide +kernel)










































































































































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
theorem t6_871choices : plan7416.choices=[3,6,6,6,7,7].map (options 6 5) := by rfl


theorem t6_871part0 : t6_871jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_871part1 : t6_871jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_871part2 : t6_871jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_871part3 : t6_871jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_871frontier : t6_871root.frontier 2=t6_871jobs := by rfl
theorem t6_871all : t6_871jobs.all (Job.check tree)=true := by
  simp only [t6_871jobs,List.all_append,List.all_nil,t6_871part0,t6_871part1,t6_871part2,t6_871part3,Bool.and_self]
theorem t6_871checked : Checked tree [3,6,6,6,7,7] := by
  refine ⟨plan7416,valid7416,t6_871choices,?_⟩
  exact check_of_frontier tree 2 t6_871root t6_871jobs t6_871frontier t6_871all
theorem t6_872choices : plan7417.choices=[3,6,6,6,10,7].map (options 6 5) := by rfl


theorem t6_872part0 : t6_872jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_872part1 : t6_872jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_872part2 : t6_872jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_872part3 : t6_872jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_872frontier : t6_872root.frontier 2=t6_872jobs := by rfl
theorem t6_872all : t6_872jobs.all (Job.check tree)=true := by
  simp only [t6_872jobs,List.all_append,List.all_nil,t6_872part0,t6_872part1,t6_872part2,t6_872part3,Bool.and_self]
theorem t6_872checked : Checked tree [3,6,6,6,10,7] := by
  refine ⟨plan7417,valid7417,t6_872choices,?_⟩
  exact check_of_frontier tree 2 t6_872root t6_872jobs t6_872frontier t6_872all
theorem t6_873choices : plan7418.choices=[3,6,6,6,10,10].map (options 6 5) := by rfl


theorem t6_873part0 : t6_873jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_873frontier : t6_873root.frontier 0=t6_873jobs := by rfl
theorem t6_873all : t6_873jobs.all (Job.check tree)=true := by
  simp only [t6_873jobs,List.all_append,List.all_nil,t6_873part0,Bool.and_self]
theorem t6_873checked : Checked tree [3,6,6,6,10,10] := by
  refine ⟨plan7418,valid7418,t6_873choices,?_⟩
  exact check_of_frontier tree 0 t6_873root t6_873jobs t6_873frontier t6_873all
theorem t6_874choices : plan7419.choices=[3,6,6,7,7,7].map (options 6 5) := by rfl


theorem t6_874part0 : t6_874jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_874part1 : t6_874jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_874part2 : t6_874jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_874part3 : t6_874jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_874part4 : t6_874jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_874part5 : t6_874jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_874frontier : t6_874root.frontier 2=t6_874jobs := by rfl
theorem t6_874all : t6_874jobs.all (Job.check tree)=true := by
  simp only [t6_874jobs,List.all_append,List.all_nil,t6_874part0,t6_874part1,t6_874part2,t6_874part3,t6_874part4,t6_874part5,Bool.and_self]
theorem t6_874checked : Checked tree [3,6,6,7,7,7] := by
  refine ⟨plan7419,valid7419,t6_874choices,?_⟩
  exact check_of_frontier tree 2 t6_874root t6_874jobs t6_874frontier t6_874all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks111 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_874checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_871checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_872checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_873checked⟩
