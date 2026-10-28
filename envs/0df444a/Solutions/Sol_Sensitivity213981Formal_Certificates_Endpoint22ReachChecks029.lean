-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks029
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:24.770422+00:00
-- url     : https://prove2.me/submissions/f0ec0a47-206a-418e-94c7-cf5d23e84911

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans049
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

























theorem valid109 : plan109.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid111 : plan111.Valid := valid_step _ _ _ valid0 (by decide +kernel)


































































































































































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









































































theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)











theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid524 : plan524.Valid := valid_step _ _ _ valid111 (by decide +kernel)








































































































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



theorem valid1442 : plan1442.Valid := valid_step _ _ _ valid524 (by decide +kernel)

theorem valid1443 : plan1443.Valid := valid_step _ _ _ valid517 (by decide +kernel)





































theorem valid1462 : plan1462.Valid := valid_step _ _ _ valid517 (by decide +kernel)

theorem valid1463 : plan1463.Valid := valid_step _ _ _ valid523 (by decide +kernel)

theorem valid1464 : plan1464.Valid := valid_step _ _ _ valid524 (by decide +kernel)
















































































































































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



























































































theorem valid3022 : plan3022.Valid := valid_step _ _ _ valid1442 (by decide +kernel)

theorem valid3023 : plan3023.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

theorem valid3024 : plan3024.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3025 : plan3025.Valid := valid_step _ _ _ valid1463 (by decide +kernel)

theorem valid3026 : plan3026.Valid := valid_step _ _ _ valid1464 (by decide +kernel)

theorem valid3027 : plan3027.Valid := valid_step _ _ _ valid1443 (by decide +kernel)


























































































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





































































theorem valid3107 : plan3107.Valid := valid_step _ _ _ valid1443 (by decide +kernel)

theorem valid3108 : plan3108.Valid := valid_step _ _ _ valid1462 (by decide +kernel)

theorem valid3109 : plan3109.Valid := valid_step _ _ _ valid1463 (by decide +kernel)






















































































































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



































































theorem valid4738 : plan4738.Valid := valid_step _ _ _ valid3022 (by decide +kernel)

theorem valid4739 : plan4739.Valid := valid_step _ _ _ valid3023 (by decide +kernel)

theorem valid4740 : plan4740.Valid := valid_step _ _ _ valid3024 (by decide +kernel)

theorem valid4741 : plan4741.Valid := valid_step _ _ _ valid3025 (by decide +kernel)

theorem valid4742 : plan4742.Valid := valid_step _ _ _ valid3026 (by decide +kernel)

theorem valid4743 : plan4743.Valid := valid_step _ _ _ valid3027 (by decide +kernel)

theorem valid4744 : plan4744.Valid := valid_step _ _ _ valid3107 (by decide +kernel)

theorem valid4745 : plan4745.Valid := valid_step _ _ _ valid3108 (by decide +kernel)

theorem valid4746 : plan4746.Valid := valid_step _ _ _ valid3109 (by decide +kernel)












































































































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
theorem t5_883choices : plan4738.choices=[3,6,6,10,10].map (options 5 4) := by rfl


theorem t5_883part0 : t5_883jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_883part1 : t5_883jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_883frontier : t5_883root.frontier 1=t5_883jobs := by rfl
theorem t5_883all : t5_883jobs.all (Job.check tree)=true := by
  simp only [t5_883jobs,List.all_append,List.all_nil,t5_883part0,t5_883part1,Bool.and_self]
theorem t5_883checked : Checked tree [3,6,6,10,10] := by
  refine ⟨plan4738,valid4738,t5_883choices,?_⟩
  exact check_of_frontier tree 1 t5_883root t5_883jobs t5_883frontier t5_883all
theorem t5_884choices : plan4739.choices=[3,6,7,7,7].map (options 5 4) := by rfl


theorem t5_884part0 : t5_884jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_884part1 : t5_884jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_884part2 : t5_884jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_884frontier : t5_884root.frontier 1=t5_884jobs := by rfl
theorem t5_884all : t5_884jobs.all (Job.check tree)=true := by
  simp only [t5_884jobs,List.all_append,List.all_nil,t5_884part0,t5_884part1,t5_884part2,Bool.and_self]
theorem t5_884checked : Checked tree [3,6,7,7,7] := by
  refine ⟨plan4739,valid4739,t5_884choices,?_⟩
  exact check_of_frontier tree 1 t5_884root t5_884jobs t5_884frontier t5_884all
theorem t5_885choices : plan4740.choices=[3,6,10,7,7].map (options 5 4) := by rfl


theorem t5_885part0 : t5_885jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_885part1 : t5_885jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_885part2 : t5_885jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_885part3 : t5_885jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_885frontier : t5_885root.frontier 2=t5_885jobs := by rfl
theorem t5_885all : t5_885jobs.all (Job.check tree)=true := by
  simp only [t5_885jobs,List.all_append,List.all_nil,t5_885part0,t5_885part1,t5_885part2,t5_885part3,Bool.and_self]
theorem t5_885checked : Checked tree [3,6,10,7,7] := by
  refine ⟨plan4740,valid4740,t5_885choices,?_⟩
  exact check_of_frontier tree 2 t5_885root t5_885jobs t5_885frontier t5_885all
theorem t5_886choices : plan4741.choices=[3,6,10,10,7].map (options 5 4) := by rfl


theorem t5_886part0 : t5_886jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_886part1 : t5_886jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_886part2 : t5_886jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_886frontier : t5_886root.frontier 2=t5_886jobs := by rfl
theorem t5_886all : t5_886jobs.all (Job.check tree)=true := by
  simp only [t5_886jobs,List.all_append,List.all_nil,t5_886part0,t5_886part1,t5_886part2,Bool.and_self]
theorem t5_886checked : Checked tree [3,6,10,10,7] := by
  refine ⟨plan4741,valid4741,t5_886choices,?_⟩
  exact check_of_frontier tree 2 t5_886root t5_886jobs t5_886frontier t5_886all
theorem t5_887choices : plan4742.choices=[3,6,10,10,10].map (options 5 4) := by rfl


theorem t5_887part0 : t5_887jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_887part1 : t5_887jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_887frontier : t5_887root.frontier 1=t5_887jobs := by rfl
theorem t5_887all : t5_887jobs.all (Job.check tree)=true := by
  simp only [t5_887jobs,List.all_append,List.all_nil,t5_887part0,t5_887part1,Bool.and_self]
theorem t5_887checked : Checked tree [3,6,10,10,10] := by
  refine ⟨plan4742,valid4742,t5_887choices,?_⟩
  exact check_of_frontier tree 1 t5_887root t5_887jobs t5_887frontier t5_887all
theorem t5_888choices : plan4743.choices=[3,7,7,7,7].map (options 5 4) := by rfl


theorem t5_888part0 : t5_888jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_888frontier : t5_888root.frontier 0=t5_888jobs := by rfl
theorem t5_888all : t5_888jobs.all (Job.check tree)=true := by
  simp only [t5_888jobs,List.all_append,List.all_nil,t5_888part0,Bool.and_self]
theorem t5_888checked : Checked tree [3,7,7,7,7] := by
  refine ⟨plan4743,valid4743,t5_888choices,?_⟩
  exact check_of_frontier tree 0 t5_888root t5_888jobs t5_888frontier t5_888all
theorem t5_889choices : plan4744.choices=[3,10,7,7,7].map (options 5 4) := by rfl


theorem t5_889part0 : t5_889jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_889part1 : t5_889jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_889part2 : t5_889jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_889frontier : t5_889root.frontier 1=t5_889jobs := by rfl
theorem t5_889all : t5_889jobs.all (Job.check tree)=true := by
  simp only [t5_889jobs,List.all_append,List.all_nil,t5_889part0,t5_889part1,t5_889part2,Bool.and_self]
theorem t5_889checked : Checked tree [3,10,7,7,7] := by
  refine ⟨plan4744,valid4744,t5_889choices,?_⟩
  exact check_of_frontier tree 1 t5_889root t5_889jobs t5_889frontier t5_889all
theorem t5_890choices : plan4745.choices=[3,10,10,7,7].map (options 5 4) := by rfl


theorem t5_890part0 : t5_890jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_890part1 : t5_890jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_890part2 : t5_890jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_890frontier : t5_890root.frontier 1=t5_890jobs := by rfl
theorem t5_890all : t5_890jobs.all (Job.check tree)=true := by
  simp only [t5_890jobs,List.all_append,List.all_nil,t5_890part0,t5_890part1,t5_890part2,Bool.and_self]
theorem t5_890checked : Checked tree [3,10,10,7,7] := by
  refine ⟨plan4745,valid4745,t5_890choices,?_⟩
  exact check_of_frontier tree 1 t5_890root t5_890jobs t5_890frontier t5_890all
theorem t5_891choices : plan4746.choices=[3,10,10,10,7].map (options 5 4) := by rfl


theorem t5_891part0 : t5_891jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_891part1 : t5_891jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_891frontier : t5_891root.frontier 1=t5_891jobs := by rfl
theorem t5_891all : t5_891jobs.all (Job.check tree)=true := by
  simp only [t5_891jobs,List.all_append,List.all_nil,t5_891part0,t5_891part1,Bool.and_self]
theorem t5_891checked : Checked tree [3,10,10,10,7] := by
  refine ⟨plan4746,valid4746,t5_891choices,?_⟩
  exact check_of_frontier tree 1 t5_891root t5_891jobs t5_891frontier t5_891all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks029 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_888checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_889checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_883checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_890checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_891checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_884checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_885checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_886checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_887checked⟩
