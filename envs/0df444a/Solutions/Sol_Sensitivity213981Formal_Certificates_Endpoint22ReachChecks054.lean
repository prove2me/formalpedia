-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks054
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:05:18.340376+00:00
-- url     : https://prove2.me/submissions/f64b6c20-39f5-401d-831f-04fe0c9d6981

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks054
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks054
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
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







































































theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

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

















































































theorem valid3401 : plan3401.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3402 : plan3402.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3403 : plan3403.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3404 : plan3404.Valid := valid_step _ _ _ valid1575 (by decide +kernel)








































































































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





































































































































theorem valid5635 : plan5635.Valid := valid_step _ _ _ valid3401 (by decide +kernel)

theorem valid5636 : plan5636.Valid := valid_step _ _ _ valid3402 (by decide +kernel)

theorem valid5637 : plan5637.Valid := valid_step _ _ _ valid3403 (by decide +kernel)

theorem valid5638 : plan5638.Valid := valid_step _ _ _ valid3404 (by decide +kernel)




















































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













































































































































































theorem valid6807 : plan6807.Valid := valid_step _ _ _ valid5635 (by decide +kernel)

theorem valid6808 : plan6808.Valid := valid_step _ _ _ valid5636 (by decide +kernel)

theorem valid6809 : plan6809.Valid := valid_step _ _ _ valid5637 (by decide +kernel)

theorem valid6810 : plan6810.Valid := valid_step _ _ _ valid5638 (by decide +kernel)












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
theorem t6_308choices : plan6807.choices=[1,3,6,6,7,7].map (options 6 4) := by rfl


theorem t6_308part0 : t6_308jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_308part1 : t6_308jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_308part2 : t6_308jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_308part3 : t6_308jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_308frontier : t6_308root.frontier 2=t6_308jobs := by rfl
theorem t6_308all : t6_308jobs.all (Job.check tree)=true := by
  simp only [t6_308jobs,List.all_append,List.all_nil,t6_308part0,t6_308part1,t6_308part2,t6_308part3,Bool.and_self]
theorem t6_308checked : Checked tree [1,3,6,6,7,7] := by
  refine ⟨plan6807,valid6807,t6_308choices,?_⟩
  exact check_of_frontier tree 2 t6_308root t6_308jobs t6_308frontier t6_308all
theorem t6_309choices : plan6808.choices=[1,3,6,6,10,7].map (options 6 4) := by rfl


theorem t6_309part0 : t6_309jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_309part1 : t6_309jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_309part2 : t6_309jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_309part3 : t6_309jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_309frontier : t6_309root.frontier 3=t6_309jobs := by rfl
theorem t6_309all : t6_309jobs.all (Job.check tree)=true := by
  simp only [t6_309jobs,List.all_append,List.all_nil,t6_309part0,t6_309part1,t6_309part2,t6_309part3,Bool.and_self]
theorem t6_309checked : Checked tree [1,3,6,6,10,7] := by
  refine ⟨plan6808,valid6808,t6_309choices,?_⟩
  exact check_of_frontier tree 3 t6_309root t6_309jobs t6_309frontier t6_309all
theorem t6_310choices : plan6809.choices=[1,3,6,6,10,10].map (options 6 4) := by rfl


theorem t6_310part0 : t6_310jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_310frontier : t6_310root.frontier 0=t6_310jobs := by rfl
theorem t6_310all : t6_310jobs.all (Job.check tree)=true := by
  simp only [t6_310jobs,List.all_append,List.all_nil,t6_310part0,Bool.and_self]
theorem t6_310checked : Checked tree [1,3,6,6,10,10] := by
  refine ⟨plan6809,valid6809,t6_310choices,?_⟩
  exact check_of_frontier tree 0 t6_310root t6_310jobs t6_310frontier t6_310all
theorem t6_311choices : plan6810.choices=[1,3,6,7,7,7].map (options 6 4) := by rfl


theorem t6_311part0 : t6_311jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_311part1 : t6_311jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_311part2 : t6_311jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_311part3 : t6_311jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_311part4 : t6_311jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_311frontier : t6_311root.frontier 2=t6_311jobs := by rfl
theorem t6_311all : t6_311jobs.all (Job.check tree)=true := by
  simp only [t6_311jobs,List.all_append,List.all_nil,t6_311part0,t6_311part1,t6_311part2,t6_311part3,t6_311part4,Bool.and_self]
theorem t6_311checked : Checked tree [1,3,6,7,7,7] := by
  refine ⟨plan6810,valid6810,t6_311choices,?_⟩
  exact check_of_frontier tree 2 t6_311root t6_311jobs t6_311frontier t6_311all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks054 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_309checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_310checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_311checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_308checked⟩
