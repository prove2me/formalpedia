-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks094
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:34:13.43348+00:00
-- url     : https://prove2.me/submissions/497feeba-80e2-4e57-b6a3-ce64f38fd12f

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks094
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks094
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
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





















































































































































































theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

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









































































theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)

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







theorem valid3364 : plan3364.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3365 : plan3365.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3366 : plan3366.Valid := valid_step _ _ _ valid1575 (by decide +kernel)




















































































































































































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























































































































theorem valid5724 : plan5724.Valid := valid_step _ _ _ valid3364 (by decide +kernel)

theorem valid5725 : plan5725.Valid := valid_step _ _ _ valid3365 (by decide +kernel)

theorem valid5726 : plan5726.Valid := valid_step _ _ _ valid3366 (by decide +kernel)




































































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



























































































theorem valid6958 : plan6958.Valid := valid_step _ _ _ valid5724 (by decide +kernel)

theorem valid6959 : plan6959.Valid := valid_step _ _ _ valid5725 (by decide +kernel)

theorem valid6960 : plan6960.Valid := valid_step _ _ _ valid5726 (by decide +kernel)
































































































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
theorem t6_783choices : plan6958.choices=[2,9,3,6,10,7].map (options 6 4) := by rfl


theorem t6_783part0 : t6_783jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_783part1 : t6_783jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_783part2 : t6_783jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_783part3 : t6_783jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_783part4 : t6_783jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_783part5 : t6_783jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_783part6 : t6_783jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_783part7 : t6_783jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_783part8 : t6_783jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_783part9 : t6_783jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_783part10 : t6_783jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_783frontier : t6_783root.frontier 2=t6_783jobs := by rfl
theorem t6_783all : t6_783jobs.all (Job.check tree)=true := by
  simp only [t6_783jobs,List.all_append,List.all_nil,t6_783part0,t6_783part1,t6_783part2,t6_783part3,t6_783part4,t6_783part5,t6_783part6,t6_783part7,t6_783part8,t6_783part9,t6_783part10,Bool.and_self]
theorem t6_783checked : Checked tree [2,9,3,6,10,7] := by
  refine ⟨plan6958,valid6958,t6_783choices,?_⟩
  exact check_of_frontier tree 2 t6_783root t6_783jobs t6_783frontier t6_783all
theorem t6_784choices : plan6959.choices=[2,9,3,6,10,10].map (options 6 4) := by rfl


theorem t6_784part0 : t6_784jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_784part1 : t6_784jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_784frontier : t6_784root.frontier 1=t6_784jobs := by rfl
theorem t6_784all : t6_784jobs.all (Job.check tree)=true := by
  simp only [t6_784jobs,List.all_append,List.all_nil,t6_784part0,t6_784part1,Bool.and_self]
theorem t6_784checked : Checked tree [2,9,3,6,10,10] := by
  refine ⟨plan6959,valid6959,t6_784choices,?_⟩
  exact check_of_frontier tree 1 t6_784root t6_784jobs t6_784frontier t6_784all
theorem t6_785choices : plan6960.choices=[2,9,3,7,7,7].map (options 6 4) := by rfl


theorem t6_785part0 : t6_785jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_785part1 : t6_785jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_785part2 : t6_785jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_785part3 : t6_785jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_785part4 : t6_785jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_785part5 : t6_785jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_785frontier : t6_785root.frontier 2=t6_785jobs := by rfl
theorem t6_785all : t6_785jobs.all (Job.check tree)=true := by
  simp only [t6_785jobs,List.all_append,List.all_nil,t6_785part0,t6_785part1,t6_785part2,t6_785part3,t6_785part4,t6_785part5,Bool.and_self]
theorem t6_785checked : Checked tree [2,9,3,7,7,7] := by
  refine ⟨plan6960,valid6960,t6_785choices,?_⟩
  exact check_of_frontier tree 2 t6_785root t6_785jobs t6_785frontier t6_785all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks094 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_783checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_784checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_785checked⟩
