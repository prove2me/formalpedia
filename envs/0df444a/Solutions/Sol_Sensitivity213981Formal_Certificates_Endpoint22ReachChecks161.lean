-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks161
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:01:22.445046+00:00
-- url     : https://prove2.me/submissions/89b4ba0a-04b0-4d5d-9cd1-4c0bdeded587

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks161
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks161
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
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











































theorem valid1654 : plan1654.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1655 : plan1655.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1656 : plan1656.Valid := valid_step _ _ _ valid608 (by decide +kernel)
















































































































































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





















































































theorem valid3595 : plan3595.Valid := valid_step _ _ _ valid1655 (by decide +kernel)

theorem valid3596 : plan3596.Valid := valid_step _ _ _ valid1656 (by decide +kernel)



theorem valid3598 : plan3598.Valid := valid_step _ _ _ valid1654 (by decide +kernel)




































































































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





theorem valid6147 : plan6147.Valid := valid_step _ _ _ valid3595 (by decide +kernel)

theorem valid6148 : plan6148.Valid := valid_step _ _ _ valid3596 (by decide +kernel)



theorem valid6150 : plan6150.Valid := valid_step _ _ _ valid3598 (by decide +kernel)




















































































































































































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

































































































































theorem valid8129 : plan8129.Valid := valid_step _ _ _ valid6147 (by decide +kernel)

theorem valid8130 : plan8130.Valid := valid_step _ _ _ valid6148 (by decide +kernel)



theorem valid8132 : plan8132.Valid := valid_step _ _ _ valid6150 (by decide +kernel)
























































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

































































































theorem valid8497 : plan8497.Valid := valid_step _ _ _ valid8129 (by decide +kernel)

theorem valid8498 : plan8498.Valid := valid_step _ _ _ valid8130 (by decide +kernel)

theorem valid8499 : plan8499.Valid := valid_step _ _ _ valid8132 (by decide +kernel)


























































































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
theorem t7_164choices : plan8497.choices=[2,3,3,6,10,7,7].map (options 7 4) := by rfl


theorem t7_164part0 : t7_164jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_164part1 : t7_164jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_164part2 : t7_164jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_164part3 : t7_164jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_164part4 : t7_164jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_164part5 : t7_164jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_164part6 : t7_164jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_164part7 : t7_164jobs7.all (Job.check tree)=true := by decide +kernel

theorem t7_164frontier : t7_164root.frontier 2=t7_164jobs := by rfl
theorem t7_164all : t7_164jobs.all (Job.check tree)=true := by
  simp only [t7_164jobs,List.all_append,List.all_nil,t7_164part0,t7_164part1,t7_164part2,t7_164part3,t7_164part4,t7_164part5,t7_164part6,t7_164part7,Bool.and_self]
theorem t7_164checked : Checked tree [2,3,3,6,10,7,7] := by
  refine ⟨plan8497,valid8497,t7_164choices,?_⟩
  exact check_of_frontier tree 2 t7_164root t7_164jobs t7_164frontier t7_164all
theorem t7_165choices : plan8498.choices=[2,3,3,6,10,10,7].map (options 7 4) := by rfl


theorem t7_165part0 : t7_165jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_165part1 : t7_165jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_165part2 : t7_165jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_165frontier : t7_165root.frontier 1=t7_165jobs := by rfl
theorem t7_165all : t7_165jobs.all (Job.check tree)=true := by
  simp only [t7_165jobs,List.all_append,List.all_nil,t7_165part0,t7_165part1,t7_165part2,Bool.and_self]
theorem t7_165checked : Checked tree [2,3,3,6,10,10,7] := by
  refine ⟨plan8498,valid8498,t7_165choices,?_⟩
  exact check_of_frontier tree 1 t7_165root t7_165jobs t7_165frontier t7_165all
theorem t7_166choices : plan8499.choices=[2,3,3,7,7,7,7].map (options 7 4) := by rfl


theorem t7_166part0 : t7_166jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_166part1 : t7_166jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_166part2 : t7_166jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_166part3 : t7_166jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_166part4 : t7_166jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_166part5 : t7_166jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_166part6 : t7_166jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_166frontier : t7_166root.frontier 2=t7_166jobs := by rfl
theorem t7_166all : t7_166jobs.all (Job.check tree)=true := by
  simp only [t7_166jobs,List.all_append,List.all_nil,t7_166part0,t7_166part1,t7_166part2,t7_166part3,t7_166part4,t7_166part5,t7_166part6,Bool.and_self]
theorem t7_166checked : Checked tree [2,3,3,7,7,7,7] := by
  refine ⟨plan8499,valid8499,t7_166choices,?_⟩
  exact check_of_frontier tree 2 t7_166root t7_166jobs t7_166frontier t7_166all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks161 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_166checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_164checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_165checked⟩
