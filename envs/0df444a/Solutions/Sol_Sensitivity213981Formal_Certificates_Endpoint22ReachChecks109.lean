-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks109
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:39:50.845163+00:00
-- url     : https://prove2.me/submissions/10702007-04e2-4f06-9abc-4a5c45897ebf

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks109
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks109
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
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





































































theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)


























































































































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





















































































































































































theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)










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













































































theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)


















































































































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































































































theorem valid3408 : plan3408.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

















































theorem valid3433 : plan3433.Valid := valid_step _ _ _ valid1575 (by decide +kernel)














































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



















































































































































theorem valid5642 : plan5642.Valid := valid_step _ _ _ valid3408 (by decide +kernel)

theorem valid5643 : plan5643.Valid := valid_step _ _ _ valid3433 (by decide +kernel)










































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









































































































































theorem valid6981 : plan6981.Valid := valid_step _ _ _ valid5642 (by decide +kernel)

theorem valid6982 : plan6982.Valid := valid_step _ _ _ valid5643 (by decide +kernel)




















































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
theorem t6_863choices : plan6981.choices=[3,3,7,7,7,7].map (options 6 4) := by rfl


theorem t6_863part0 : t6_863jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_863part1 : t6_863jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_863part2 : t6_863jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_863part3 : t6_863jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_863part4 : t6_863jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_863part5 : t6_863jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_863frontier : t6_863root.frontier 2=t6_863jobs := by rfl
theorem t6_863all : t6_863jobs.all (Job.check tree)=true := by
  simp only [t6_863jobs,List.all_append,List.all_nil,t6_863part0,t6_863part1,t6_863part2,t6_863part3,t6_863part4,t6_863part5,Bool.and_self]
theorem t6_863checked : Checked tree [3,3,7,7,7,7] := by
  refine ⟨plan6981,valid6981,t6_863choices,?_⟩
  exact check_of_frontier tree 2 t6_863root t6_863jobs t6_863frontier t6_863all
theorem t6_864choices : plan6982.choices=[3,3,10,7,7,7].map (options 6 4) := by rfl


theorem t6_864part0 : t6_864jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_864part1 : t6_864jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_864part2 : t6_864jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_864part3 : t6_864jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_864part4 : t6_864jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_864part5 : t6_864jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_864part6 : t6_864jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_864part7 : t6_864jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_864part8 : t6_864jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_864part9 : t6_864jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_864frontier : t6_864root.frontier 3=t6_864jobs := by rfl
theorem t6_864all : t6_864jobs.all (Job.check tree)=true := by
  simp only [t6_864jobs,List.all_append,List.all_nil,t6_864part0,t6_864part1,t6_864part2,t6_864part3,t6_864part4,t6_864part5,t6_864part6,t6_864part7,t6_864part8,t6_864part9,Bool.and_self]
theorem t6_864checked : Checked tree [3,3,10,7,7,7] := by
  refine ⟨plan6982,valid6982,t6_864choices,?_⟩
  exact check_of_frontier tree 3 t6_864root t6_864jobs t6_864frontier t6_864all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks109 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_864checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_863checked⟩
