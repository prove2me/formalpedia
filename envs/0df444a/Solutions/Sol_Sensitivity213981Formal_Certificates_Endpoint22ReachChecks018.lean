-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks018
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:56:28.148517+00:00
-- url     : https://prove2.me/submissions/ebd3d366-865f-4d28-9e92-0d0bd5ca9dc8

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks018
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks018
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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











theorem valid102 : plan102.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid105 : plan105.Valid := valid_step _ _ _ valid0 (by decide +kernel)














































































































































































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



























theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)











theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)


















































































































































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



















































theorem valid1370 : plan1370.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1371 : plan1371.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1372 : plan1372.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1373 : plan1373.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1374 : plan1374.Valid := valid_step _ _ _ valid503 (by decide +kernel)




































































































































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































































































































































theorem valid2768 : plan2768.Valid := valid_step _ _ _ valid1370 (by decide +kernel)

theorem valid2769 : plan2769.Valid := valid_step _ _ _ valid1371 (by decide +kernel)

theorem valid2770 : plan2770.Valid := valid_step _ _ _ valid1372 (by decide +kernel)

theorem valid2771 : plan2771.Valid := valid_step _ _ _ valid1373 (by decide +kernel)

theorem valid2772 : plan2772.Valid := valid_step _ _ _ valid1374 (by decide +kernel)
























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

























































































theorem valid4269 : plan4269.Valid := valid_step _ _ _ valid2768 (by decide +kernel)

theorem valid4270 : plan4270.Valid := valid_step _ _ _ valid2769 (by decide +kernel)

theorem valid4271 : plan4271.Valid := valid_step _ _ _ valid2770 (by decide +kernel)

theorem valid4272 : plan4272.Valid := valid_step _ _ _ valid2771 (by decide +kernel)

theorem valid4273 : plan4273.Valid := valid_step _ _ _ valid2772 (by decide +kernel)






























































































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
theorem t5_742choices : plan4269.choices=[2,3,6,6,6].map (options 5 3) := by rfl


theorem t5_742part0 : t5_742jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_742part1 : t5_742jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_742frontier : t5_742root.frontier 1=t5_742jobs := by rfl
theorem t5_742all : t5_742jobs.all (Job.check tree)=true := by
  simp only [t5_742jobs,List.all_append,List.all_nil,t5_742part0,t5_742part1,Bool.and_self]
theorem t5_742checked : Checked tree [2,3,6,6,6] := by
  refine ⟨plan4269,valid4269,t5_742choices,?_⟩
  exact check_of_frontier tree 1 t5_742root t5_742jobs t5_742frontier t5_742all
theorem t5_743choices : plan4270.choices=[2,3,6,6,7].map (options 5 3) := by rfl


theorem t5_743part0 : t5_743jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_743part1 : t5_743jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_743part2 : t5_743jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_743part3 : t5_743jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_743frontier : t5_743root.frontier 1=t5_743jobs := by rfl
theorem t5_743all : t5_743jobs.all (Job.check tree)=true := by
  simp only [t5_743jobs,List.all_append,List.all_nil,t5_743part0,t5_743part1,t5_743part2,t5_743part3,Bool.and_self]
theorem t5_743checked : Checked tree [2,3,6,6,7] := by
  refine ⟨plan4270,valid4270,t5_743choices,?_⟩
  exact check_of_frontier tree 1 t5_743root t5_743jobs t5_743frontier t5_743all
theorem t5_744choices : plan4271.choices=[2,3,6,6,10].map (options 5 3) := by rfl


theorem t5_744part0 : t5_744jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_744part1 : t5_744jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_744part2 : t5_744jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_744frontier : t5_744root.frontier 1=t5_744jobs := by rfl
theorem t5_744all : t5_744jobs.all (Job.check tree)=true := by
  simp only [t5_744jobs,List.all_append,List.all_nil,t5_744part0,t5_744part1,t5_744part2,Bool.and_self]
theorem t5_744checked : Checked tree [2,3,6,6,10] := by
  refine ⟨plan4271,valid4271,t5_744choices,?_⟩
  exact check_of_frontier tree 1 t5_744root t5_744jobs t5_744frontier t5_744all
theorem t5_745choices : plan4272.choices=[2,3,6,7,7].map (options 5 3) := by rfl


theorem t5_745part0 : t5_745jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_745part1 : t5_745jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_745part2 : t5_745jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_745part3 : t5_745jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_745frontier : t5_745root.frontier 1=t5_745jobs := by rfl
theorem t5_745all : t5_745jobs.all (Job.check tree)=true := by
  simp only [t5_745jobs,List.all_append,List.all_nil,t5_745part0,t5_745part1,t5_745part2,t5_745part3,Bool.and_self]
theorem t5_745checked : Checked tree [2,3,6,7,7] := by
  refine ⟨plan4272,valid4272,t5_745choices,?_⟩
  exact check_of_frontier tree 1 t5_745root t5_745jobs t5_745frontier t5_745all
theorem t5_746choices : plan4273.choices=[2,3,6,10,7].map (options 5 3) := by rfl


theorem t5_746part0 : t5_746jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_746part1 : t5_746jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_746part2 : t5_746jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_746part3 : t5_746jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_746part4 : t5_746jobs4.all (Job.check tree)=true := by decide +kernel

theorem t5_746part5 : t5_746jobs5.all (Job.check tree)=true := by decide +kernel

theorem t5_746frontier : t5_746root.frontier 2=t5_746jobs := by rfl
theorem t5_746all : t5_746jobs.all (Job.check tree)=true := by
  simp only [t5_746jobs,List.all_append,List.all_nil,t5_746part0,t5_746part1,t5_746part2,t5_746part3,t5_746part4,t5_746part5,Bool.and_self]
theorem t5_746checked : Checked tree [2,3,6,10,7] := by
  refine ⟨plan4273,valid4273,t5_746choices,?_⟩
  exact check_of_frontier tree 2 t5_746root t5_746jobs t5_746frontier t5_746all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks018 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_742checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_743checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_744checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_745checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_746checked⟩
