-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks112
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:39:43.600455+00:00
-- url     : https://prove2.me/submissions/11878c49-6253-4fc4-abd7-8bf5467615c2

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks112
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks112
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







































































































































theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1606 : plan1606.Valid := valid_step _ _ _ valid580 (by decide +kernel)




















































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



















































theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)








































































































































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



































































theorem valid5890 : plan5890.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5891 : plan5891.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5892 : plan5892.Valid := valid_step _ _ _ valid3484 (by decide +kernel)
























































































































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























































theorem valid7420 : plan7420.Valid := valid_step _ _ _ valid5890 (by decide +kernel)

theorem valid7421 : plan7421.Valid := valid_step _ _ _ valid5891 (by decide +kernel)

theorem valid7422 : plan7422.Valid := valid_step _ _ _ valid5892 (by decide +kernel)




































































































































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
theorem t6_875choices : plan7420.choices=[3,6,6,10,7,7].map (options 6 5) := by rfl


theorem t6_875part0 : t6_875jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_875part1 : t6_875jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_875part2 : t6_875jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_875part3 : t6_875jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_875part4 : t6_875jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_875part5 : t6_875jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_875part6 : t6_875jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_875part7 : t6_875jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_875part8 : t6_875jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_875frontier : t6_875root.frontier 2=t6_875jobs := by rfl
theorem t6_875all : t6_875jobs.all (Job.check tree)=true := by
  simp only [t6_875jobs,List.all_append,List.all_nil,t6_875part0,t6_875part1,t6_875part2,t6_875part3,t6_875part4,t6_875part5,t6_875part6,t6_875part7,t6_875part8,Bool.and_self]
theorem t6_875checked : Checked tree [3,6,6,10,7,7] := by
  refine ⟨plan7420,valid7420,t6_875choices,?_⟩
  exact check_of_frontier tree 2 t6_875root t6_875jobs t6_875frontier t6_875all
theorem t6_876choices : plan7421.choices=[3,6,6,10,10,7].map (options 6 5) := by rfl


theorem t6_876part0 : t6_876jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_876part1 : t6_876jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_876part2 : t6_876jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_876part3 : t6_876jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_876part4 : t6_876jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_876frontier : t6_876root.frontier 2=t6_876jobs := by rfl
theorem t6_876all : t6_876jobs.all (Job.check tree)=true := by
  simp only [t6_876jobs,List.all_append,List.all_nil,t6_876part0,t6_876part1,t6_876part2,t6_876part3,t6_876part4,Bool.and_self]
theorem t6_876checked : Checked tree [3,6,6,10,10,7] := by
  refine ⟨plan7421,valid7421,t6_876choices,?_⟩
  exact check_of_frontier tree 2 t6_876root t6_876jobs t6_876frontier t6_876all
theorem t6_877choices : plan7422.choices=[3,6,6,10,10,10].map (options 6 5) := by rfl


theorem t6_877part0 : t6_877jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_877part1 : t6_877jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_877frontier : t6_877root.frontier 1=t6_877jobs := by rfl
theorem t6_877all : t6_877jobs.all (Job.check tree)=true := by
  simp only [t6_877jobs,List.all_append,List.all_nil,t6_877part0,t6_877part1,Bool.and_self]
theorem t6_877checked : Checked tree [3,6,6,10,10,10] := by
  refine ⟨plan7422,valid7422,t6_877choices,?_⟩
  exact check_of_frontier tree 1 t6_877root t6_877jobs t6_877frontier t6_877all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks112 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_875checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_876checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_877checked⟩
