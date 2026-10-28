-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks179
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:12:08.769993+00:00
-- url     : https://prove2.me/submissions/9bcba2af-9706-4612-b794-9dae07684609

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks179
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks179
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
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

















































































































theorem valid153 : plan153.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid154 : plan154.Valid := valid_step _ _ _ valid0 (by decide +kernel)












































































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









































































theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)

theorem valid614 : plan614.Valid := valid_step _ _ _ valid153 (by decide +kernel)

theorem valid615 : plan615.Valid := valid_step _ _ _ valid154 (by decide +kernel)


















































































































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































































theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1666 : plan1666.Valid := valid_step _ _ _ valid614 (by decide +kernel)

theorem valid1667 : plan1667.Valid := valid_step _ _ _ valid615 (by decide +kernel)


























































































































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































































































































theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)



theorem valid3618 : plan3618.Valid := valid_step _ _ _ valid1665 (by decide +kernel)

theorem valid3619 : plan3619.Valid := valid_step _ _ _ valid1666 (by decide +kernel)

theorem valid3620 : plan3620.Valid := valid_step _ _ _ valid1667 (by decide +kernel)
























































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





















































































theorem valid6187 : plan6187.Valid := valid_step _ _ _ valid3618 (by decide +kernel)

theorem valid6188 : plan6188.Valid := valid_step _ _ _ valid3619 (by decide +kernel)

theorem valid6189 : plan6189.Valid := valid_step _ _ _ valid3620 (by decide +kernel)

theorem valid6190 : plan6190.Valid := valid_step _ _ _ valid3616 (by decide +kernel)




































































































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



























































theorem valid8190 : plan8190.Valid := valid_step _ _ _ valid6187 (by decide +kernel)

theorem valid8191 : plan8191.Valid := valid_step _ _ _ valid6188 (by decide +kernel)

theorem valid8192 : plan8192.Valid := valid_step _ _ _ valid6189 (by decide +kernel)

theorem valid8193 : plan8193.Valid := valid_step _ _ _ valid6190 (by decide +kernel)






























































































































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











theorem valid8646 : plan8646.Valid := valid_step _ _ _ valid8190 (by decide +kernel)

theorem valid8647 : plan8647.Valid := valid_step _ _ _ valid8191 (by decide +kernel)

theorem valid8648 : plan8648.Valid := valid_step _ _ _ valid8192 (by decide +kernel)

theorem valid8649 : plan8649.Valid := valid_step _ _ _ valid8193 (by decide +kernel)














































































































































































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
theorem t7_305choices : plan8646.choices=[3,3,6,10,10,7,7].map (options 7 5) := by rfl


theorem t7_305part0 : t7_305jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_305part1 : t7_305jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_305part2 : t7_305jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_305part3 : t7_305jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_305part4 : t7_305jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_305part5 : t7_305jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_305part6 : t7_305jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_305frontier : t7_305root.frontier 3=t7_305jobs := by rfl
theorem t7_305all : t7_305jobs.all (Job.check tree)=true := by
  simp only [t7_305jobs,List.all_append,List.all_nil,t7_305part0,t7_305part1,t7_305part2,t7_305part3,t7_305part4,t7_305part5,t7_305part6,Bool.and_self]
theorem t7_305checked : Checked tree [3,3,6,10,10,7,7] := by
  refine ⟨plan8646,valid8646,t7_305choices,?_⟩
  exact check_of_frontier tree 3 t7_305root t7_305jobs t7_305frontier t7_305all
theorem t7_306choices : plan8647.choices=[3,3,6,10,10,10,7].map (options 7 5) := by rfl


theorem t7_306part0 : t7_306jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_306part1 : t7_306jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_306frontier : t7_306root.frontier 3=t7_306jobs := by rfl
theorem t7_306all : t7_306jobs.all (Job.check tree)=true := by
  simp only [t7_306jobs,List.all_append,List.all_nil,t7_306part0,t7_306part1,Bool.and_self]
theorem t7_306checked : Checked tree [3,3,6,10,10,10,7] := by
  refine ⟨plan8647,valid8647,t7_306choices,?_⟩
  exact check_of_frontier tree 3 t7_306root t7_306jobs t7_306frontier t7_306all
theorem t7_307choices : plan8648.choices=[3,3,6,10,10,10,10].map (options 7 5) := by rfl


theorem t7_307part0 : t7_307jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_307frontier : t7_307root.frontier 0=t7_307jobs := by rfl
theorem t7_307all : t7_307jobs.all (Job.check tree)=true := by
  simp only [t7_307jobs,List.all_append,List.all_nil,t7_307part0,Bool.and_self]
theorem t7_307checked : Checked tree [3,3,6,10,10,10,10] := by
  refine ⟨plan8648,valid8648,t7_307choices,?_⟩
  exact check_of_frontier tree 0 t7_307root t7_307jobs t7_307frontier t7_307all
theorem t7_308choices : plan8649.choices=[3,3,7,7,7,7,7].map (options 7 5) := by rfl


theorem t7_308part0 : t7_308jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_308part1 : t7_308jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_308part2 : t7_308jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_308part3 : t7_308jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_308part4 : t7_308jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_308part5 : t7_308jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_308frontier : t7_308root.frontier 3=t7_308jobs := by rfl
theorem t7_308all : t7_308jobs.all (Job.check tree)=true := by
  simp only [t7_308jobs,List.all_append,List.all_nil,t7_308part0,t7_308part1,t7_308part2,t7_308part3,t7_308part4,t7_308part5,Bool.and_self]
theorem t7_308checked : Checked tree [3,3,7,7,7,7,7] := by
  refine ⟨plan8649,valid8649,t7_308choices,?_⟩
  exact check_of_frontier tree 3 t7_308root t7_308jobs t7_308frontier t7_308all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks179 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_307checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_308checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_305checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_306checked⟩
