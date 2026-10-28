-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks191
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:17:15.361811+00:00
-- url     : https://prove2.me/submissions/39c3af6e-8bea-4136-9a33-c67bff813fdf

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks191
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks191
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



























































theorem valid1662 : plan1662.Valid := valid_step _ _ _ valid614 (by decide +kernel)



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



















































































































theorem valid3610 : plan3610.Valid := valid_step _ _ _ valid1662 (by decide +kernel)



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





































theorem valid6163 : plan6163.Valid := valid_step _ _ _ valid3610 (by decide +kernel)

theorem valid6164 : plan6164.Valid := valid_step _ _ _ valid3612 (by decide +kernel)

theorem valid6165 : plan6165.Valid := valid_step _ _ _ valid3613 (by decide +kernel)

theorem valid6166 : plan6166.Valid := valid_step _ _ _ valid3614 (by decide +kernel)

theorem valid6167 : plan6167.Valid := valid_step _ _ _ valid3616 (by decide +kernel)


















































































































































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



















theorem valid8170 : plan8170.Valid := valid_step _ _ _ valid6163 (by decide +kernel)

theorem valid8171 : plan8171.Valid := valid_step _ _ _ valid6164 (by decide +kernel)

theorem valid8172 : plan8172.Valid := valid_step _ _ _ valid6165 (by decide +kernel)

theorem valid8173 : plan8173.Valid := valid_step _ _ _ valid6166 (by decide +kernel)

theorem valid8174 : plan8174.Valid := valid_step _ _ _ valid6167 (by decide +kernel)




































































































































































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

















































































































theorem valid8697 : plan8697.Valid := valid_step _ _ _ valid8170 (by decide +kernel)

theorem valid8698 : plan8698.Valid := valid_step _ _ _ valid8171 (by decide +kernel)

theorem valid8699 : plan8699.Valid := valid_step _ _ _ valid8172 (by decide +kernel)

theorem valid8700 : plan8700.Valid := valid_step _ _ _ valid8173 (by decide +kernel)

theorem valid8701 : plan8701.Valid := valid_step _ _ _ valid8174 (by decide +kernel)






































































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
theorem t7_645choices : plan8697.choices=[9,3,3,6,6,10,7].map (options 7 5) := by rfl


theorem t7_645part0 : t7_645jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_645frontier : t7_645root.frontier 0=t7_645jobs := by rfl
theorem t7_645all : t7_645jobs.all (Job.check tree)=true := by
  simp only [t7_645jobs,List.all_append,List.all_nil,t7_645part0,Bool.and_self]
theorem t7_645checked : Checked tree [9,3,3,6,6,10,7] := by
  refine ⟨plan8697,valid8697,t7_645choices,?_⟩
  exact check_of_frontier tree 0 t7_645root t7_645jobs t7_645frontier t7_645all
theorem t7_646choices : plan8698.choices=[9,3,3,6,7,7,7].map (options 7 5) := by rfl


theorem t7_646part0 : t7_646jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_646part1 : t7_646jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_646part2 : t7_646jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_646part3 : t7_646jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_646part4 : t7_646jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_646part5 : t7_646jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_646frontier : t7_646root.frontier 2=t7_646jobs := by rfl
theorem t7_646all : t7_646jobs.all (Job.check tree)=true := by
  simp only [t7_646jobs,List.all_append,List.all_nil,t7_646part0,t7_646part1,t7_646part2,t7_646part3,t7_646part4,t7_646part5,Bool.and_self]
theorem t7_646checked : Checked tree [9,3,3,6,7,7,7] := by
  refine ⟨plan8698,valid8698,t7_646choices,?_⟩
  exact check_of_frontier tree 2 t7_646root t7_646jobs t7_646frontier t7_646all
theorem t7_647choices : plan8699.choices=[9,3,3,6,10,7,7].map (options 7 5) := by rfl


theorem t7_647part0 : t7_647jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_647part1 : t7_647jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_647part2 : t7_647jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_647part3 : t7_647jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_647frontier : t7_647root.frontier 1=t7_647jobs := by rfl
theorem t7_647all : t7_647jobs.all (Job.check tree)=true := by
  simp only [t7_647jobs,List.all_append,List.all_nil,t7_647part0,t7_647part1,t7_647part2,t7_647part3,Bool.and_self]
theorem t7_647checked : Checked tree [9,3,3,6,10,7,7] := by
  refine ⟨plan8699,valid8699,t7_647choices,?_⟩
  exact check_of_frontier tree 1 t7_647root t7_647jobs t7_647frontier t7_647all
theorem t7_648choices : plan8700.choices=[9,3,3,6,10,10,7].map (options 7 5) := by rfl


theorem t7_648part0 : t7_648jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_648frontier : t7_648root.frontier 0=t7_648jobs := by rfl
theorem t7_648all : t7_648jobs.all (Job.check tree)=true := by
  simp only [t7_648jobs,List.all_append,List.all_nil,t7_648part0,Bool.and_self]
theorem t7_648checked : Checked tree [9,3,3,6,10,10,7] := by
  refine ⟨plan8700,valid8700,t7_648choices,?_⟩
  exact check_of_frontier tree 0 t7_648root t7_648jobs t7_648frontier t7_648all
theorem t7_649choices : plan8701.choices=[9,3,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_649part0 : t7_649jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_649part1 : t7_649jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_649part2 : t7_649jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_649part3 : t7_649jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_649frontier : t7_649root.frontier 2=t7_649jobs := by rfl
theorem t7_649all : t7_649jobs.all (Job.check tree)=true := by
  simp only [t7_649jobs,List.all_append,List.all_nil,t7_649part0,t7_649part1,t7_649part2,t7_649part3,Bool.and_self]
theorem t7_649checked : Checked tree [9,3,3,7,7,7,7] := by
  refine ⟨plan8701,valid8701,t7_649choices,?_⟩
  exact check_of_frontier tree 2 t7_649root t7_649jobs t7_649frontier t7_649all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks191 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_649checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_646checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_647checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_648checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_645checked⟩
