-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks163
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:04:28.855307+00:00
-- url     : https://prove2.me/submissions/a09851ad-e21d-47dd-b41e-c07f0b5c852e

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks163
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks163
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
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

















































































































theorem valid153 : plan153.Valid := valid_step _ _ _ valid0 (by decide +kernel)














































































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























































































































theorem valid3612 : plan3612.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3613 : plan3613.Valid := valid_step _ _ _ valid1665 (by decide +kernel)

theorem valid3614 : plan3614.Valid := valid_step _ _ _ valid1666 (by decide +kernel)



theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)
































































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









































































theorem valid6181 : plan6181.Valid := valid_step _ _ _ valid3612 (by decide +kernel)

theorem valid6182 : plan6182.Valid := valid_step _ _ _ valid3613 (by decide +kernel)

theorem valid6183 : plan6183.Valid := valid_step _ _ _ valid3614 (by decide +kernel)



theorem valid6185 : plan6185.Valid := valid_step _ _ _ valid3616 (by decide +kernel)














































































































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















































theorem valid8184 : plan8184.Valid := valid_step _ _ _ valid6181 (by decide +kernel)

theorem valid8185 : plan8185.Valid := valid_step _ _ _ valid6182 (by decide +kernel)

theorem valid8186 : plan8186.Valid := valid_step _ _ _ valid6183 (by decide +kernel)



theorem valid8188 : plan8188.Valid := valid_step _ _ _ valid6185 (by decide +kernel)








































































































































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





























































































































theorem valid8607 : plan8607.Valid := valid_step _ _ _ valid8184 (by decide +kernel)

theorem valid8608 : plan8608.Valid := valid_step _ _ _ valid8185 (by decide +kernel)

theorem valid8609 : plan8609.Valid := valid_step _ _ _ valid8186 (by decide +kernel)

theorem valid8610 : plan8610.Valid := valid_step _ _ _ valid8188 (by decide +kernel)




























































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
theorem t7_173choices : plan8607.choices=[2,3,6,6,7,7,7].map (options 7 5) := by rfl


theorem t7_173part0 : t7_173jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_173part1 : t7_173jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_173part2 : t7_173jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_173part3 : t7_173jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_173part4 : t7_173jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_173frontier : t7_173root.frontier 3=t7_173jobs := by rfl
theorem t7_173all : t7_173jobs.all (Job.check tree)=true := by
  simp only [t7_173jobs,List.all_append,List.all_nil,t7_173part0,t7_173part1,t7_173part2,t7_173part3,t7_173part4,Bool.and_self]
theorem t7_173checked : Checked tree [2,3,6,6,7,7,7] := by
  refine ⟨plan8607,valid8607,t7_173choices,?_⟩
  exact check_of_frontier tree 3 t7_173root t7_173jobs t7_173frontier t7_173all
theorem t7_174choices : plan8608.choices=[2,3,6,6,10,7,7].map (options 7 5) := by rfl


theorem t7_174part0 : t7_174jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_174part1 : t7_174jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_174part2 : t7_174jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_174part3 : t7_174jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_174frontier : t7_174root.frontier 3=t7_174jobs := by rfl
theorem t7_174all : t7_174jobs.all (Job.check tree)=true := by
  simp only [t7_174jobs,List.all_append,List.all_nil,t7_174part0,t7_174part1,t7_174part2,t7_174part3,Bool.and_self]
theorem t7_174checked : Checked tree [2,3,6,6,10,7,7] := by
  refine ⟨plan8608,valid8608,t7_174choices,?_⟩
  exact check_of_frontier tree 3 t7_174root t7_174jobs t7_174frontier t7_174all
theorem t7_175choices : plan8609.choices=[2,3,6,6,10,10,7].map (options 7 5) := by rfl


theorem t7_175part0 : t7_175jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_175frontier : t7_175root.frontier 0=t7_175jobs := by rfl
theorem t7_175all : t7_175jobs.all (Job.check tree)=true := by
  simp only [t7_175jobs,List.all_append,List.all_nil,t7_175part0,Bool.and_self]
theorem t7_175checked : Checked tree [2,3,6,6,10,10,7] := by
  refine ⟨plan8609,valid8609,t7_175choices,?_⟩
  exact check_of_frontier tree 0 t7_175root t7_175jobs t7_175frontier t7_175all
theorem t7_176choices : plan8610.choices=[2,3,6,7,7,7,7].map (options 7 5) := by rfl


theorem t7_176part0 : t7_176jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_176part1 : t7_176jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_176part2 : t7_176jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_176part3 : t7_176jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_176part4 : t7_176jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_176part5 : t7_176jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_176part6 : t7_176jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_176part7 : t7_176jobs7.all (Job.check tree)=true := by decide +kernel

theorem t7_176frontier : t7_176root.frontier 3=t7_176jobs := by rfl
theorem t7_176all : t7_176jobs.all (Job.check tree)=true := by
  simp only [t7_176jobs,List.all_append,List.all_nil,t7_176part0,t7_176part1,t7_176part2,t7_176part3,t7_176part4,t7_176part5,t7_176part6,t7_176part7,Bool.and_self]
theorem t7_176checked : Checked tree [2,3,6,7,7,7,7] := by
  refine ⟨plan8610,valid8610,t7_176choices,?_⟩
  exact check_of_frontier tree 3 t7_176root t7_176jobs t7_176frontier t7_176all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks163 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_173checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_174checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_175checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_176checked⟩
