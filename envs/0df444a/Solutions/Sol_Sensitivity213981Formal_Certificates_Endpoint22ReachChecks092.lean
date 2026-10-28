-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks092
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:33:40.387486+00:00
-- url     : https://prove2.me/submissions/ce277a3f-5bac-4169-aaeb-b66b013e719c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks092
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks092
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)




























































































































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



































































































































































theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)
















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





























































































































































































theorem valid1535 : plan1535.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1536 : plan1536.Valid := valid_step _ _ _ valid563 (by decide +kernel)
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

theorem valid1537 : plan1537.Valid := valid_step _ _ _ valid564 (by decide +kernel)































































theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)






























































































































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

























































































theorem valid3309 : plan3309.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3310 : plan3310.Valid := valid_step _ _ _ valid1536 (by decide +kernel)

theorem valid3311 : plan3311.Valid := valid_step _ _ _ valid1537 (by decide +kernel)

































































































theorem valid3360 : plan3360.Valid := valid_step _ _ _ valid1569 (by decide +kernel)
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

















































































































theorem valid5529 : plan5529.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5530 : plan5530.Valid := valid_step _ _ _ valid3310 (by decide +kernel)

theorem valid5531 : plan5531.Valid := valid_step _ _ _ valid3311 (by decide +kernel)










































































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















































































































theorem valid5720 : plan5720.Valid := valid_step _ _ _ valid3360 (by decide +kernel)
















































































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



















































































































































theorem valid6602 : plan6602.Valid := valid_step _ _ _ valid5529 (by decide +kernel)

theorem valid6603 : plan6603.Valid := valid_step _ _ _ valid5530 (by decide +kernel)

theorem valid6604 : plan6604.Valid := valid_step _ _ _ valid5531 (by decide +kernel)








































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



















































































theorem valid6954 : plan6954.Valid := valid_step _ _ _ valid5720 (by decide +kernel)












































































































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
theorem t6_776choices : plan6602.choices=[2,9,3,3,7,7].map (options 6 3) := by rfl


theorem t6_776part0 : t6_776jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_776part1 : t6_776jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_776part2 : t6_776jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_776part3 : t6_776jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_776part4 : t6_776jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_776part5 : t6_776jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_776part6 : t6_776jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_776frontier : t6_776root.frontier 2=t6_776jobs := by rfl
theorem t6_776all : t6_776jobs.all (Job.check tree)=true := by
  simp only [t6_776jobs,List.all_append,List.all_nil,t6_776part0,t6_776part1,t6_776part2,t6_776part3,t6_776part4,t6_776part5,t6_776part6,Bool.and_self]
theorem t6_776checked : Checked tree [2,9,3,3,7,7] := by
  refine ⟨plan6602,valid6602,t6_776choices,?_⟩
  exact check_of_frontier tree 2 t6_776root t6_776jobs t6_776frontier t6_776all
theorem t6_777choices : plan6603.choices=[2,9,3,3,10,7].map (options 6 3) := by rfl


theorem t6_777part0 : t6_777jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_777part1 : t6_777jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_777part2 : t6_777jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_777part3 : t6_777jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_777part4 : t6_777jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_777part5 : t6_777jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_777part6 : t6_777jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_777frontier : t6_777root.frontier 2=t6_777jobs := by rfl
theorem t6_777all : t6_777jobs.all (Job.check tree)=true := by
  simp only [t6_777jobs,List.all_append,List.all_nil,t6_777part0,t6_777part1,t6_777part2,t6_777part3,t6_777part4,t6_777part5,t6_777part6,Bool.and_self]
theorem t6_777checked : Checked tree [2,9,3,3,10,7] := by
  refine ⟨plan6603,valid6603,t6_777choices,?_⟩
  exact check_of_frontier tree 2 t6_777root t6_777jobs t6_777frontier t6_777all
theorem t6_778choices : plan6604.choices=[2,9,3,3,10,10].map (options 6 3) := by rfl


theorem t6_778part0 : t6_778jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_778part1 : t6_778jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_778frontier : t6_778root.frontier 1=t6_778jobs := by rfl
theorem t6_778all : t6_778jobs.all (Job.check tree)=true := by
  simp only [t6_778jobs,List.all_append,List.all_nil,t6_778part0,t6_778part1,Bool.and_self]
theorem t6_778checked : Checked tree [2,9,3,3,10,10] := by
  refine ⟨plan6604,valid6604,t6_778choices,?_⟩
  exact check_of_frontier tree 1 t6_778root t6_778jobs t6_778frontier t6_778all
theorem t6_779choices : plan6954.choices=[2,9,3,6,6,6].map (options 6 4) := by rfl


theorem t6_779part0 : t6_779jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_779frontier : t6_779root.frontier 0=t6_779jobs := by rfl
theorem t6_779all : t6_779jobs.all (Job.check tree)=true := by
  simp only [t6_779jobs,List.all_append,List.all_nil,t6_779part0,Bool.and_self]
theorem t6_779checked : Checked tree [2,9,3,6,6,6] := by
  refine ⟨plan6954,valid6954,t6_779choices,?_⟩
  exact check_of_frontier tree 0 t6_779root t6_779jobs t6_779frontier t6_779all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks092 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_779checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_776checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_777checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_778checked⟩
