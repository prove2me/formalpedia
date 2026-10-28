-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks148
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:57:36.585481+00:00
-- url     : https://prove2.me/submissions/ba298011-0dc9-46fb-8ac9-8f46988aede1

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks148
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks148
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
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





















































theorem valid7131 : plan7131.Valid := valid_step _ _ _ valid5626 (by decide +kernel)

theorem valid7132 : plan7132.Valid := valid_step _ _ _ valid5627 (by decide +kernel)








































































































































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
theorem t6_1689choices : plan7131.choices=[9,3,3,6,10,7].map (options 6 4) := by rfl


theorem t6_1689part0 : t6_1689jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part1 : t6_1689jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part2 : t6_1689jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part3 : t6_1689jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part4 : t6_1689jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part5 : t6_1689jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part6 : t6_1689jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part7 : t6_1689jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part8 : t6_1689jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part9 : t6_1689jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part10 : t6_1689jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part11 : t6_1689jobs11.all (Job.check tree)=true := by decide +kernel

theorem t6_1689part12 : t6_1689jobs12.all (Job.check tree)=true := by decide +kernel

theorem t6_1689frontier : t6_1689root.frontier 2=t6_1689jobs := by rfl
theorem t6_1689all : t6_1689jobs.all (Job.check tree)=true := by
  simp only [t6_1689jobs,List.all_append,List.all_nil,t6_1689part0,t6_1689part1,t6_1689part2,t6_1689part3,t6_1689part4,t6_1689part5,t6_1689part6,t6_1689part7,t6_1689part8,t6_1689part9,t6_1689part10,t6_1689part11,t6_1689part12,Bool.and_self]
theorem t6_1689checked : Checked tree [9,3,3,6,10,7] := by
  refine ⟨plan7131,valid7131,t6_1689choices,?_⟩
  exact check_of_frontier tree 2 t6_1689root t6_1689jobs t6_1689frontier t6_1689all
theorem t6_1690choices : plan7132.choices=[9,3,3,6,10,10].map (options 6 4) := by rfl


theorem t6_1690part0 : t6_1690jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1690part1 : t6_1690jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1690part2 : t6_1690jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1690part3 : t6_1690jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1690frontier : t6_1690root.frontier 1=t6_1690jobs := by rfl
theorem t6_1690all : t6_1690jobs.all (Job.check tree)=true := by
  simp only [t6_1690jobs,List.all_append,List.all_nil,t6_1690part0,t6_1690part1,t6_1690part2,t6_1690part3,Bool.and_self]
theorem t6_1690checked : Checked tree [9,3,3,6,10,10] := by
  refine ⟨plan7132,valid7132,t6_1690choices,?_⟩
  exact check_of_frontier tree 1 t6_1690root t6_1690jobs t6_1690frontier t6_1690all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks148 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1689checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1690checked⟩
