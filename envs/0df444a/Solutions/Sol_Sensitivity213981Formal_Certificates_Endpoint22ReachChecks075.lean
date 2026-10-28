-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks075
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:22:32.167015+00:00
-- url     : https://prove2.me/submissions/b378d799-8d3c-44fb-9df8-35abaa039293

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks075
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks075
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



















































































theorem valid3402 : plan3402.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3403 : plan3403.Valid := valid_step _ _ _ valid1574 (by decide +kernel)










































































































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







































































































































theorem valid5636 : plan5636.Valid := valid_step _ _ _ valid3402 (by decide +kernel)

theorem valid5637 : plan5637.Valid := valid_step _ _ _ valid3403 (by decide +kernel)






















































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











theorem valid6918 : plan6918.Valid := valid_step _ _ _ valid5636 (by decide +kernel)

theorem valid6919 : plan6919.Valid := valid_step _ _ _ valid5637 (by decide +kernel)


















































































































































































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
theorem t6_655choices : plan6918.choices=[2,3,6,6,10,7].map (options 6 4) := by rfl


theorem t6_655part0 : t6_655jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_655part1 : t6_655jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_655part2 : t6_655jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_655part3 : t6_655jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_655part4 : t6_655jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_655part5 : t6_655jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_655part6 : t6_655jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_655part7 : t6_655jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_655part8 : t6_655jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_655part9 : t6_655jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_655part10 : t6_655jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_655frontier : t6_655root.frontier 3=t6_655jobs := by rfl
theorem t6_655all : t6_655jobs.all (Job.check tree)=true := by
  simp only [t6_655jobs,List.all_append,List.all_nil,t6_655part0,t6_655part1,t6_655part2,t6_655part3,t6_655part4,t6_655part5,t6_655part6,t6_655part7,t6_655part8,t6_655part9,t6_655part10,Bool.and_self]
theorem t6_655checked : Checked tree [2,3,6,6,10,7] := by
  refine ⟨plan6918,valid6918,t6_655choices,?_⟩
  exact check_of_frontier tree 3 t6_655root t6_655jobs t6_655frontier t6_655all
theorem t6_656choices : plan6919.choices=[2,3,6,6,10,10].map (options 6 4) := by rfl


theorem t6_656part0 : t6_656jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_656part1 : t6_656jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_656part2 : t6_656jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_656frontier : t6_656root.frontier 1=t6_656jobs := by rfl
theorem t6_656all : t6_656jobs.all (Job.check tree)=true := by
  simp only [t6_656jobs,List.all_append,List.all_nil,t6_656part0,t6_656part1,t6_656part2,Bool.and_self]
theorem t6_656checked : Checked tree [2,3,6,6,10,10] := by
  refine ⟨plan6919,valid6919,t6_656choices,?_⟩
  exact check_of_frontier tree 1 t6_656root t6_656jobs t6_656frontier t6_656all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks075 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_655checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_656checked⟩
