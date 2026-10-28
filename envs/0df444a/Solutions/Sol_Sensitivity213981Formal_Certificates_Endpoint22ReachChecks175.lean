-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks175
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:09:14.314991+00:00
-- url     : https://prove2.me/submissions/54376c75-f07c-4b54-9e44-08c1e6ced99f

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks175
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks175
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
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

theorem valid151 : plan151.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid152 : plan152.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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





























































theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)

theorem valid608 : plan608.Valid := valid_step _ _ _ valid150 (by decide +kernel)

theorem valid609 : plan609.Valid := valid_step _ _ _ valid151 (by decide +kernel)

theorem valid610 : plan610.Valid := valid_step _ _ _ valid152 (by decide +kernel)

theorem valid611 : plan611.Valid := valid_step _ _ _ valid153 (by decide +kernel)

theorem valid612 : plan612.Valid := valid_step _ _ _ valid154 (by decide +kernel)

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













































theorem valid1655 : plan1655.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1656 : plan1656.Valid := valid_step _ _ _ valid608 (by decide +kernel)

theorem valid1657 : plan1657.Valid := valid_step _ _ _ valid609 (by decide +kernel)

theorem valid1658 : plan1658.Valid := valid_step _ _ _ valid610 (by decide +kernel)

theorem valid1659 : plan1659.Valid := valid_step _ _ _ valid611 (by decide +kernel)

theorem valid1660 : plan1660.Valid := valid_step _ _ _ valid612 (by decide +kernel)

theorem valid1661 : plan1661.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1662 : plan1662.Valid := valid_step _ _ _ valid614 (by decide +kernel)

theorem valid1663 : plan1663.Valid := valid_step _ _ _ valid615 (by decide +kernel)


































































































































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































































































theorem valid3600 : plan3600.Valid := valid_step _ _ _ valid1655 (by decide +kernel)

theorem valid3601 : plan3601.Valid := valid_step _ _ _ valid1656 (by decide +kernel)

theorem valid3602 : plan3602.Valid := valid_step _ _ _ valid1657 (by decide +kernel)







theorem valid3606 : plan3606.Valid := valid_step _ _ _ valid1658 (by decide +kernel)

theorem valid3607 : plan3607.Valid := valid_step _ _ _ valid1659 (by decide +kernel)

theorem valid3608 : plan3608.Valid := valid_step _ _ _ valid1660 (by decide +kernel)

theorem valid3609 : plan3609.Valid := valid_step _ _ _ valid1661 (by decide +kernel)

theorem valid3610 : plan3610.Valid := valid_step _ _ _ valid1662 (by decide +kernel)

theorem valid3611 : plan3611.Valid := valid_step _ _ _ valid1663 (by decide +kernel)










































































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















theorem valid6152 : plan6152.Valid := valid_step _ _ _ valid3600 (by decide +kernel)

theorem valid6153 : plan6153.Valid := valid_step _ _ _ valid3601 (by decide +kernel)

theorem valid6154 : plan6154.Valid := valid_step _ _ _ valid3602 (by decide +kernel)









































theorem valid6175 : plan6175.Valid := valid_step _ _ _ valid3606 (by decide +kernel)

theorem valid6176 : plan6176.Valid := valid_step _ _ _ valid3607 (by decide +kernel)

theorem valid6177 : plan6177.Valid := valid_step _ _ _ valid3608 (by decide +kernel)

theorem valid6178 : plan6178.Valid := valid_step _ _ _ valid3609 (by decide +kernel)

theorem valid6179 : plan6179.Valid := valid_step _ _ _ valid3610 (by decide +kernel)

theorem valid6180 : plan6180.Valid := valid_step _ _ _ valid3611 (by decide +kernel)
























































































































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











































































































































theorem valid8134 : plan8134.Valid := valid_step _ _ _ valid6152 (by decide +kernel)

theorem valid8135 : plan8135.Valid := valid_step _ _ _ valid6153 (by decide +kernel)

theorem valid8136 : plan8136.Valid := valid_step _ _ _ valid6154 (by decide +kernel)
















































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

















































































































































theorem valid8521 : plan8521.Valid := valid_step _ _ _ valid8134 (by decide +kernel)

theorem valid8522 : plan8522.Valid := valid_step _ _ _ valid8135 (by decide +kernel)

theorem valid8523 : plan8523.Valid := valid_step _ _ _ valid8136 (by decide +kernel)










































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



































theorem valid8178 : plan8178.Valid := valid_step _ _ _ valid6175 (by decide +kernel)

theorem valid8179 : plan8179.Valid := valid_step _ _ _ valid6176 (by decide +kernel)

theorem valid8180 : plan8180.Valid := valid_step _ _ _ valid6177 (by decide +kernel)

theorem valid8181 : plan8181.Valid := valid_step _ _ _ valid6178 (by decide +kernel)

theorem valid8182 : plan8182.Valid := valid_step _ _ _ valid6179 (by decide +kernel)

theorem valid8183 : plan8183.Valid := valid_step _ _ _ valid6180 (by decide +kernel)


















































































































































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



















































































































































































theorem valid8634 : plan8634.Valid := valid_step _ _ _ valid8178 (by decide +kernel)

theorem valid8635 : plan8635.Valid := valid_step _ _ _ valid8179 (by decide +kernel)

theorem valid8636 : plan8636.Valid := valid_step _ _ _ valid8180 (by decide +kernel)

theorem valid8637 : plan8637.Valid := valid_step _ _ _ valid8181 (by decide +kernel)

theorem valid8638 : plan8638.Valid := valid_step _ _ _ valid8182 (by decide +kernel)

theorem valid8639 : plan8639.Valid := valid_step _ _ _ valid8183 (by decide +kernel)


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
theorem t7_290choices : plan8521.choices=[3,3,3,10,10,7,7].map (options 7 4) := by rfl


theorem t7_290part0 : t7_290jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_290part1 : t7_290jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_290part2 : t7_290jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_290part3 : t7_290jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_290part4 : t7_290jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_290part5 : t7_290jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_290frontier : t7_290root.frontier 4=t7_290jobs := by rfl
theorem t7_290all : t7_290jobs.all (Job.check tree)=true := by
  simp only [t7_290jobs,List.all_append,List.all_nil,t7_290part0,t7_290part1,t7_290part2,t7_290part3,t7_290part4,t7_290part5,Bool.and_self]
theorem t7_290checked : Checked tree [3,3,3,10,10,7,7] := by
  refine ⟨plan8521,valid8521,t7_290choices,?_⟩
  exact check_of_frontier tree 4 t7_290root t7_290jobs t7_290frontier t7_290all
theorem t7_291choices : plan8522.choices=[3,3,3,10,10,10,7].map (options 7 4) := by rfl


theorem t7_291part0 : t7_291jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_291part1 : t7_291jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_291frontier : t7_291root.frontier 1=t7_291jobs := by rfl
theorem t7_291all : t7_291jobs.all (Job.check tree)=true := by
  simp only [t7_291jobs,List.all_append,List.all_nil,t7_291part0,t7_291part1,Bool.and_self]
theorem t7_291checked : Checked tree [3,3,3,10,10,10,7] := by
  refine ⟨plan8522,valid8522,t7_291choices,?_⟩
  exact check_of_frontier tree 1 t7_291root t7_291jobs t7_291frontier t7_291all
theorem t7_292choices : plan8523.choices=[3,3,3,10,10,10,10].map (options 7 4) := by rfl


theorem t7_292part0 : t7_292jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_292frontier : t7_292root.frontier 0=t7_292jobs := by rfl
theorem t7_292all : t7_292jobs.all (Job.check tree)=true := by
  simp only [t7_292jobs,List.all_append,List.all_nil,t7_292part0,Bool.and_self]
theorem t7_292checked : Checked tree [3,3,3,10,10,10,10] := by
  refine ⟨plan8523,valid8523,t7_292choices,?_⟩
  exact check_of_frontier tree 0 t7_292root t7_292jobs t7_292frontier t7_292all
theorem t7_293choices : plan8634.choices=[3,3,6,6,6,6,6].map (options 7 5) := by rfl


theorem t7_293part0 : t7_293jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_293frontier : t7_293root.frontier 0=t7_293jobs := by rfl
theorem t7_293all : t7_293jobs.all (Job.check tree)=true := by
  simp only [t7_293jobs,List.all_append,List.all_nil,t7_293part0,Bool.and_self]
theorem t7_293checked : Checked tree [3,3,6,6,6,6,6] := by
  refine ⟨plan8634,valid8634,t7_293choices,?_⟩
  exact check_of_frontier tree 0 t7_293root t7_293jobs t7_293frontier t7_293all
theorem t7_294choices : plan8635.choices=[3,3,6,6,6,6,7].map (options 7 5) := by rfl


theorem t7_294part0 : t7_294jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_294frontier : t7_294root.frontier 0=t7_294jobs := by rfl
theorem t7_294all : t7_294jobs.all (Job.check tree)=true := by
  simp only [t7_294jobs,List.all_append,List.all_nil,t7_294part0,Bool.and_self]
theorem t7_294checked : Checked tree [3,3,6,6,6,6,7] := by
  refine ⟨plan8635,valid8635,t7_294choices,?_⟩
  exact check_of_frontier tree 0 t7_294root t7_294jobs t7_294frontier t7_294all
theorem t7_295choices : plan8636.choices=[3,3,6,6,6,6,10].map (options 7 5) := by rfl


theorem t7_295part0 : t7_295jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_295frontier : t7_295root.frontier 0=t7_295jobs := by rfl
theorem t7_295all : t7_295jobs.all (Job.check tree)=true := by
  simp only [t7_295jobs,List.all_append,List.all_nil,t7_295part0,Bool.and_self]
theorem t7_295checked : Checked tree [3,3,6,6,6,6,10] := by
  refine ⟨plan8636,valid8636,t7_295choices,?_⟩
  exact check_of_frontier tree 0 t7_295root t7_295jobs t7_295frontier t7_295all
theorem t7_296choices : plan8637.choices=[3,3,6,6,6,7,7].map (options 7 5) := by rfl


theorem t7_296part0 : t7_296jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_296part1 : t7_296jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_296part2 : t7_296jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_296frontier : t7_296root.frontier 3=t7_296jobs := by rfl
theorem t7_296all : t7_296jobs.all (Job.check tree)=true := by
  simp only [t7_296jobs,List.all_append,List.all_nil,t7_296part0,t7_296part1,t7_296part2,Bool.and_self]
theorem t7_296checked : Checked tree [3,3,6,6,6,7,7] := by
  refine ⟨plan8637,valid8637,t7_296choices,?_⟩
  exact check_of_frontier tree 3 t7_296root t7_296jobs t7_296frontier t7_296all
theorem t7_297choices : plan8638.choices=[3,3,6,6,6,10,7].map (options 7 5) := by rfl


theorem t7_297part0 : t7_297jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_297part1 : t7_297jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_297frontier : t7_297root.frontier 3=t7_297jobs := by rfl
theorem t7_297all : t7_297jobs.all (Job.check tree)=true := by
  simp only [t7_297jobs,List.all_append,List.all_nil,t7_297part0,t7_297part1,Bool.and_self]
theorem t7_297checked : Checked tree [3,3,6,6,6,10,7] := by
  refine ⟨plan8638,valid8638,t7_297choices,?_⟩
  exact check_of_frontier tree 3 t7_297root t7_297jobs t7_297frontier t7_297all
theorem t7_298choices : plan8639.choices=[3,3,6,6,6,10,10].map (options 7 5) := by rfl


theorem t7_298part0 : t7_298jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_298frontier : t7_298root.frontier 0=t7_298jobs := by rfl
theorem t7_298all : t7_298jobs.all (Job.check tree)=true := by
  simp only [t7_298jobs,List.all_append,List.all_nil,t7_298part0,Bool.and_self]
theorem t7_298checked : Checked tree [3,3,6,6,6,10,10] := by
  refine ⟨plan8639,valid8639,t7_298choices,?_⟩
  exact check_of_frontier tree 0 t7_298root t7_298jobs t7_298frontier t7_298all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks175 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_290checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_291checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_292checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_293checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_294checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_295checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_296checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_297checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_298checked⟩
