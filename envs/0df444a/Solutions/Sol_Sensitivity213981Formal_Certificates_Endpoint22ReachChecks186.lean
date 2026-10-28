-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks186
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:14:35.450987+00:00
-- url     : https://prove2.me/submissions/8cf95038-2e0e-48d3-b1c5-e955948358bd

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks186
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks186
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans092
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





theorem valid156 : plan156.Valid := valid_step _ _ _ valid0 (by decide +kernel)








































































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





theorem valid617 : plan617.Valid := valid_step _ _ _ valid156 (by decide +kernel)



theorem valid619 : plan619.Valid := valid_step _ _ _ valid156 (by decide +kernel)

theorem valid620 : plan620.Valid := valid_step _ _ _ valid156 (by decide +kernel)








































































































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





theorem valid1669 : plan1669.Valid := valid_step _ _ _ valid617 (by decide +kernel)



theorem valid1671 : plan1671.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1672 : plan1672.Valid := valid_step _ _ _ valid620 (by decide +kernel)



theorem valid1674 : plan1674.Valid := valid_step _ _ _ valid619 (by decide +kernel)












































































































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

























































































































theorem valid3613 : plan3613.Valid := valid_step _ _ _ valid1665 (by decide +kernel)

theorem valid3614 : plan3614.Valid := valid_step _ _ _ valid1666 (by decide +kernel)



theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3617 : plan3617.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3618 : plan3618.Valid := valid_step _ _ _ valid1665 (by decide +kernel)

theorem valid3619 : plan3619.Valid := valid_step _ _ _ valid1666 (by decide +kernel)







theorem valid3623 : plan3623.Valid := valid_step _ _ _ valid1669 (by decide +kernel)



theorem valid3625 : plan3625.Valid := valid_step _ _ _ valid1671 (by decide +kernel)

theorem valid3626 : plan3626.Valid := valid_step _ _ _ valid1672 (by decide +kernel)



theorem valid3628 : plan3628.Valid := valid_step _ _ _ valid1674 (by decide +kernel)








































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









































theorem valid6165 : plan6165.Valid := valid_step _ _ _ valid3613 (by decide +kernel)

theorem valid6166 : plan6166.Valid := valid_step _ _ _ valid3614 (by decide +kernel)

theorem valid6167 : plan6167.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6168 : plan6168.Valid := valid_step _ _ _ valid3617 (by decide +kernel)

theorem valid6169 : plan6169.Valid := valid_step _ _ _ valid3618 (by decide +kernel)

theorem valid6170 : plan6170.Valid := valid_step _ _ _ valid3619 (by decide +kernel)

















































































theorem valid6211 : plan6211.Valid := valid_step _ _ _ valid3623 (by decide +kernel)



theorem valid6213 : plan6213.Valid := valid_step _ _ _ valid3625 (by decide +kernel)

theorem valid6214 : plan6214.Valid := valid_step _ _ _ valid3626 (by decide +kernel)



theorem valid6216 : plan6216.Valid := valid_step _ _ _ valid3628 (by decide +kernel)
















































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























theorem valid8172 : plan8172.Valid := valid_step _ _ _ valid6165 (by decide +kernel)

theorem valid8173 : plan8173.Valid := valid_step _ _ _ valid6166 (by decide +kernel)

theorem valid8174 : plan8174.Valid := valid_step _ _ _ valid6167 (by decide +kernel)

theorem valid8175 : plan8175.Valid := valid_step _ _ _ valid6168 (by decide +kernel)

theorem valid8176 : plan8176.Valid := valid_step _ _ _ valid6169 (by decide +kernel)

theorem valid8177 : plan8177.Valid := valid_step _ _ _ valid6170 (by decide +kernel)









































































































theorem valid8230 : plan8230.Valid := valid_step _ _ _ valid6211 (by decide +kernel)

theorem valid8231 : plan8231.Valid := valid_step _ _ _ valid6213 (by decide +kernel)

theorem valid8232 : plan8232.Valid := valid_step _ _ _ valid6214 (by decide +kernel)

theorem valid8233 : plan8233.Valid := valid_step _ _ _ valid6216 (by decide +kernel)














































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





























































theorem valid8671 : plan8671.Valid := valid_step _ _ _ valid8172 (by decide +kernel)

theorem valid8672 : plan8672.Valid := valid_step _ _ _ valid8173 (by decide +kernel)

theorem valid8673 : plan8673.Valid := valid_step _ _ _ valid8174 (by decide +kernel)

theorem valid8674 : plan8674.Valid := valid_step _ _ _ valid8175 (by decide +kernel)

theorem valid8675 : plan8675.Valid := valid_step _ _ _ valid8176 (by decide +kernel)

theorem valid8676 : plan8676.Valid := valid_step _ _ _ valid8177 (by decide +kernel)
























































































































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



































































theorem valid8866 : plan8866.Valid := valid_step _ _ _ valid8230 (by decide +kernel)

theorem valid8867 : plan8867.Valid := valid_step _ _ _ valid8231 (by decide +kernel)

theorem valid8868 : plan8868.Valid := valid_step _ _ _ valid8232 (by decide +kernel)

theorem valid8869 : plan8869.Valid := valid_step _ _ _ valid8233 (by decide +kernel)






















































































































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
theorem t7_435choices : plan8671.choices=[5,3,3,6,10,7,7].map (options 7 5) := by rfl


theorem t7_435part0 : t7_435jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_435part1 : t7_435jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_435part2 : t7_435jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_435part3 : t7_435jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_435frontier : t7_435root.frontier 1=t7_435jobs := by rfl
theorem t7_435all : t7_435jobs.all (Job.check tree)=true := by
  simp only [t7_435jobs,List.all_append,List.all_nil,t7_435part0,t7_435part1,t7_435part2,t7_435part3,Bool.and_self]
theorem t7_435checked : Checked tree [5,3,3,6,10,7,7] := by
  refine ⟨plan8671,valid8671,t7_435choices,?_⟩
  exact check_of_frontier tree 1 t7_435root t7_435jobs t7_435frontier t7_435all
theorem t7_436choices : plan8672.choices=[5,3,3,6,10,10,7].map (options 7 5) := by rfl


theorem t7_436part0 : t7_436jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_436frontier : t7_436root.frontier 0=t7_436jobs := by rfl
theorem t7_436all : t7_436jobs.all (Job.check tree)=true := by
  simp only [t7_436jobs,List.all_append,List.all_nil,t7_436part0,Bool.and_self]
theorem t7_436checked : Checked tree [5,3,3,6,10,10,7] := by
  refine ⟨plan8672,valid8672,t7_436choices,?_⟩
  exact check_of_frontier tree 0 t7_436root t7_436jobs t7_436frontier t7_436all
theorem t7_437choices : plan8673.choices=[5,3,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_437part0 : t7_437jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_437part1 : t7_437jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_437part2 : t7_437jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_437part3 : t7_437jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_437frontier : t7_437root.frontier 2=t7_437jobs := by rfl
theorem t7_437all : t7_437jobs.all (Job.check tree)=true := by
  simp only [t7_437jobs,List.all_append,List.all_nil,t7_437part0,t7_437part1,t7_437part2,t7_437part3,Bool.and_self]
theorem t7_437checked : Checked tree [5,3,3,7,7,7,7] := by
  refine ⟨plan8673,valid8673,t7_437choices,?_⟩
  exact check_of_frontier tree 2 t7_437root t7_437jobs t7_437frontier t7_437all
theorem t7_438choices : plan8674.choices=[5,3,3,10,7,7,7].map (options 7 5) := by rfl


theorem t7_438part0 : t7_438jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_438part1 : t7_438jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_438part2 : t7_438jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_438part3 : t7_438jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_438part4 : t7_438jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_438part5 : t7_438jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_438frontier : t7_438root.frontier 2=t7_438jobs := by rfl
theorem t7_438all : t7_438jobs.all (Job.check tree)=true := by
  simp only [t7_438jobs,List.all_append,List.all_nil,t7_438part0,t7_438part1,t7_438part2,t7_438part3,t7_438part4,t7_438part5,Bool.and_self]
theorem t7_438checked : Checked tree [5,3,3,10,7,7,7] := by
  refine ⟨plan8674,valid8674,t7_438choices,?_⟩
  exact check_of_frontier tree 2 t7_438root t7_438jobs t7_438frontier t7_438all
theorem t7_439choices : plan8675.choices=[5,3,3,10,10,7,7].map (options 7 5) := by rfl


theorem t7_439part0 : t7_439jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_439part1 : t7_439jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_439part2 : t7_439jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_439frontier : t7_439root.frontier 1=t7_439jobs := by rfl
theorem t7_439all : t7_439jobs.all (Job.check tree)=true := by
  simp only [t7_439jobs,List.all_append,List.all_nil,t7_439part0,t7_439part1,t7_439part2,Bool.and_self]
theorem t7_439checked : Checked tree [5,3,3,10,10,7,7] := by
  refine ⟨plan8675,valid8675,t7_439choices,?_⟩
  exact check_of_frontier tree 1 t7_439root t7_439jobs t7_439frontier t7_439all
theorem t7_440choices : plan8676.choices=[5,3,3,10,10,10,7].map (options 7 5) := by rfl


theorem t7_440part0 : t7_440jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_440frontier : t7_440root.frontier 0=t7_440jobs := by rfl
theorem t7_440all : t7_440jobs.all (Job.check tree)=true := by
  simp only [t7_440jobs,List.all_append,List.all_nil,t7_440part0,Bool.and_self]
theorem t7_440checked : Checked tree [5,3,3,10,10,10,7] := by
  refine ⟨plan8676,valid8676,t7_440choices,?_⟩
  exact check_of_frontier tree 0 t7_440root t7_440jobs t7_440frontier t7_440all
theorem t7_441choices : plan8866.choices=[5,3,6,6,6,6,7].map (options 7 6) := by rfl


theorem t7_441part0 : t7_441jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_441frontier : t7_441root.frontier 0=t7_441jobs := by rfl
theorem t7_441all : t7_441jobs.all (Job.check tree)=true := by
  simp only [t7_441jobs,List.all_append,List.all_nil,t7_441part0,Bool.and_self]
theorem t7_441checked : Checked tree [5,3,6,6,6,6,7] := by
  refine ⟨plan8866,valid8866,t7_441choices,?_⟩
  exact check_of_frontier tree 0 t7_441root t7_441jobs t7_441frontier t7_441all
theorem t7_442choices : plan8867.choices=[5,3,6,6,6,7,7].map (options 7 6) := by rfl


theorem t7_442part0 : t7_442jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_442frontier : t7_442root.frontier 0=t7_442jobs := by rfl
theorem t7_442all : t7_442jobs.all (Job.check tree)=true := by
  simp only [t7_442jobs,List.all_append,List.all_nil,t7_442part0,Bool.and_self]
theorem t7_442checked : Checked tree [5,3,6,6,6,7,7] := by
  refine ⟨plan8867,valid8867,t7_442choices,?_⟩
  exact check_of_frontier tree 0 t7_442root t7_442jobs t7_442frontier t7_442all
theorem t7_443choices : plan8868.choices=[5,3,6,6,6,10,7].map (options 7 6) := by rfl


theorem t7_443part0 : t7_443jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_443frontier : t7_443root.frontier 0=t7_443jobs := by rfl
theorem t7_443all : t7_443jobs.all (Job.check tree)=true := by
  simp only [t7_443jobs,List.all_append,List.all_nil,t7_443part0,Bool.and_self]
theorem t7_443checked : Checked tree [5,3,6,6,6,10,7] := by
  refine ⟨plan8868,valid8868,t7_443choices,?_⟩
  exact check_of_frontier tree 0 t7_443root t7_443jobs t7_443frontier t7_443all
theorem t7_444choices : plan8869.choices=[5,3,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_444part0 : t7_444jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_444part1 : t7_444jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_444frontier : t7_444root.frontier 1=t7_444jobs := by rfl
theorem t7_444all : t7_444jobs.all (Job.check tree)=true := by
  simp only [t7_444jobs,List.all_append,List.all_nil,t7_444part0,t7_444part1,Bool.and_self]
theorem t7_444checked : Checked tree [5,3,6,6,7,7,7] := by
  refine ⟨plan8869,valid8869,t7_444choices,?_⟩
  exact check_of_frontier tree 1 t7_444root t7_444jobs t7_444frontier t7_444all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks186 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_438checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_439checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_440checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_441checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_442checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_443checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_444checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_435checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_436checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_437checked⟩
