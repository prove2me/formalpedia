-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks108
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:38:48.356311+00:00
-- url     : https://prove2.me/submissions/f7691023-75fd-406a-8a71-74348371e1b8

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks108
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks108
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

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)
























































































































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



























































































theorem valid3406 : plan3406.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3407 : plan3407.Valid := valid_step _ _ _ valid1582 (by decide +kernel)


































































































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















































































































































theorem valid5640 : plan5640.Valid := valid_step _ _ _ valid3406 (by decide +kernel)

theorem valid5641 : plan5641.Valid := valid_step _ _ _ valid3407 (by decide +kernel)














































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





































































































































theorem valid6979 : plan6979.Valid := valid_step _ _ _ valid5640 (by decide +kernel)

theorem valid6980 : plan6980.Valid := valid_step _ _ _ valid5641 (by decide +kernel)
























































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
theorem t6_861choices : plan6979.choices=[3,3,6,10,10,7].map (options 6 4) := by rfl


theorem t6_861part0 : t6_861jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_861part1 : t6_861jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_861part2 : t6_861jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_861part3 : t6_861jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_861part4 : t6_861jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_861part5 : t6_861jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_861part6 : t6_861jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_861part7 : t6_861jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_861part8 : t6_861jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_861part9 : t6_861jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_861part10 : t6_861jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_861part11 : t6_861jobs11.all (Job.check tree)=true := by decide +kernel

theorem t6_861frontier : t6_861root.frontier 3=t6_861jobs := by rfl
theorem t6_861all : t6_861jobs.all (Job.check tree)=true := by
  simp only [t6_861jobs,List.all_append,List.all_nil,t6_861part0,t6_861part1,t6_861part2,t6_861part3,t6_861part4,t6_861part5,t6_861part6,t6_861part7,t6_861part8,t6_861part9,t6_861part10,t6_861part11,Bool.and_self]
theorem t6_861checked : Checked tree [3,3,6,10,10,7] := by
  refine ⟨plan6979,valid6979,t6_861choices,?_⟩
  exact check_of_frontier tree 3 t6_861root t6_861jobs t6_861frontier t6_861all
theorem t6_862choices : plan6980.choices=[3,3,6,10,10,10].map (options 6 4) := by rfl


theorem t6_862part0 : t6_862jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_862part1 : t6_862jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_862part2 : t6_862jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_862part3 : t6_862jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_862frontier : t6_862root.frontier 1=t6_862jobs := by rfl
theorem t6_862all : t6_862jobs.all (Job.check tree)=true := by
  simp only [t6_862jobs,List.all_append,List.all_nil,t6_862part0,t6_862part1,t6_862part2,t6_862part3,Bool.and_self]
theorem t6_862checked : Checked tree [3,3,6,10,10,10] := by
  refine ⟨plan6980,valid6980,t6_862choices,?_⟩
  exact check_of_frontier tree 1 t6_862root t6_862jobs t6_862frontier t6_862all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks108 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_861checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_862checked⟩
