-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks128
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:49:30.140135+00:00
-- url     : https://prove2.me/submissions/efd73967-7658-4a65-80c5-75dbff54602b

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks128
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks128
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
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









theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)








































































































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











theorem valid3366 : plan3366.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

theorem valid3367 : plan3367.Valid := valid_step _ _ _ valid1580 (by decide +kernel)


















































































































































































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























































































































theorem valid5628 : plan5628.Valid := valid_step _ _ _ valid3366 (by decide +kernel)

theorem valid5629 : plan5629.Valid := valid_step _ _ _ valid3367 (by decide +kernel)






































































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

















































































theorem valid7049 : plan7049.Valid := valid_step _ _ _ valid5628 (by decide +kernel)

theorem valid7050 : plan7050.Valid := valid_step _ _ _ valid5629 (by decide +kernel)












































































































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
theorem t6_1203choices : plan7049.choices=[5,3,3,7,7,7].map (options 6 4) := by rfl


theorem t6_1203part0 : t6_1203jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1203part1 : t6_1203jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1203part2 : t6_1203jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1203part3 : t6_1203jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1203part4 : t6_1203jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1203part5 : t6_1203jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1203frontier : t6_1203root.frontier 2=t6_1203jobs := by rfl
theorem t6_1203all : t6_1203jobs.all (Job.check tree)=true := by
  simp only [t6_1203jobs,List.all_append,List.all_nil,t6_1203part0,t6_1203part1,t6_1203part2,t6_1203part3,t6_1203part4,t6_1203part5,Bool.and_self]
theorem t6_1203checked : Checked tree [5,3,3,7,7,7] := by
  refine ⟨plan7049,valid7049,t6_1203choices,?_⟩
  exact check_of_frontier tree 2 t6_1203root t6_1203jobs t6_1203frontier t6_1203all
theorem t6_1204choices : plan7050.choices=[5,3,3,10,7,7].map (options 6 4) := by rfl


theorem t6_1204part0 : t6_1204jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1204part1 : t6_1204jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1204part2 : t6_1204jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1204part3 : t6_1204jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1204part4 : t6_1204jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1204part5 : t6_1204jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1204part6 : t6_1204jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_1204part7 : t6_1204jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_1204part8 : t6_1204jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_1204part9 : t6_1204jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_1204frontier : t6_1204root.frontier 2=t6_1204jobs := by rfl
theorem t6_1204all : t6_1204jobs.all (Job.check tree)=true := by
  simp only [t6_1204jobs,List.all_append,List.all_nil,t6_1204part0,t6_1204part1,t6_1204part2,t6_1204part3,t6_1204part4,t6_1204part5,t6_1204part6,t6_1204part7,t6_1204part8,t6_1204part9,Bool.and_self]
theorem t6_1204checked : Checked tree [5,3,3,10,7,7] := by
  refine ⟨plan7050,valid7050,t6_1204choices,?_⟩
  exact check_of_frontier tree 2 t6_1204root t6_1204jobs t6_1204frontier t6_1204all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks128 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1203checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1204checked⟩
