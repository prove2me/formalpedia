-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks127
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:48:21.162988+00:00
-- url     : https://prove2.me/submissions/62332a09-f238-491f-98b4-4936d99dc425

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks127
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks127
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









































































theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)




















































































































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



















































































































theorem valid5626 : plan5626.Valid := valid_step _ _ _ valid3364 (by decide +kernel)

theorem valid5627 : plan5627.Valid := valid_step _ _ _ valid3365 (by decide +kernel)










































































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













































































theorem valid7047 : plan7047.Valid := valid_step _ _ _ valid5626 (by decide +kernel)

theorem valid7048 : plan7048.Valid := valid_step _ _ _ valid5627 (by decide +kernel)
















































































































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
theorem t6_1201choices : plan7047.choices=[5,3,3,6,10,7].map (options 6 4) := by rfl


theorem t6_1201part0 : t6_1201jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part1 : t6_1201jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part2 : t6_1201jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part3 : t6_1201jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part4 : t6_1201jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part5 : t6_1201jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part6 : t6_1201jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part7 : t6_1201jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part8 : t6_1201jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part9 : t6_1201jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part10 : t6_1201jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part11 : t6_1201jobs11.all (Job.check tree)=true := by decide +kernel

theorem t6_1201part12 : t6_1201jobs12.all (Job.check tree)=true := by decide +kernel

theorem t6_1201frontier : t6_1201root.frontier 2=t6_1201jobs := by rfl
theorem t6_1201all : t6_1201jobs.all (Job.check tree)=true := by
  simp only [t6_1201jobs,List.all_append,List.all_nil,t6_1201part0,t6_1201part1,t6_1201part2,t6_1201part3,t6_1201part4,t6_1201part5,t6_1201part6,t6_1201part7,t6_1201part8,t6_1201part9,t6_1201part10,t6_1201part11,t6_1201part12,Bool.and_self]
theorem t6_1201checked : Checked tree [5,3,3,6,10,7] := by
  refine ⟨plan7047,valid7047,t6_1201choices,?_⟩
  exact check_of_frontier tree 2 t6_1201root t6_1201jobs t6_1201frontier t6_1201all
theorem t6_1202choices : plan7048.choices=[5,3,3,6,10,10].map (options 6 4) := by rfl


theorem t6_1202part0 : t6_1202jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1202part1 : t6_1202jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1202part2 : t6_1202jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1202part3 : t6_1202jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1202frontier : t6_1202root.frontier 1=t6_1202jobs := by rfl
theorem t6_1202all : t6_1202jobs.all (Job.check tree)=true := by
  simp only [t6_1202jobs,List.all_append,List.all_nil,t6_1202part0,t6_1202part1,t6_1202part2,t6_1202part3,Bool.and_self]
theorem t6_1202checked : Checked tree [5,3,3,6,10,10] := by
  refine ⟨plan7048,valid7048,t6_1202choices,?_⟩
  exact check_of_frontier tree 1 t6_1202root t6_1202jobs t6_1202frontier t6_1202all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks127 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1201checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1202checked⟩
