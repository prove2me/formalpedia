-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks055
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:07:12.670597+00:00
-- url     : https://prove2.me/submissions/df4abeb2-58a0-4a34-a665-7f81c0cd9152

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks055
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













































































theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)









theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1582 : plan1582.Valid := valid_step _ _ _ valid573 (by decide +kernel)




































































































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

























































































theorem valid3405 : plan3405.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3406 : plan3406.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3407 : plan3407.Valid := valid_step _ _ _ valid1582 (by decide +kernel)

theorem valid3408 : plan3408.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

















































theorem valid3433 : plan3433.Valid := valid_step _ _ _ valid1575 (by decide +kernel)














































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













































































































































theorem valid5639 : plan5639.Valid := valid_step _ _ _ valid3405 (by decide +kernel)

theorem valid5640 : plan5640.Valid := valid_step _ _ _ valid3406 (by decide +kernel)

theorem valid5641 : plan5641.Valid := valid_step _ _ _ valid3407 (by decide +kernel)

theorem valid5642 : plan5642.Valid := valid_step _ _ _ valid3408 (by decide +kernel)

theorem valid5643 : plan5643.Valid := valid_step _ _ _ valid3433 (by decide +kernel)










































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





















































































































































































theorem valid6811 : plan6811.Valid := valid_step _ _ _ valid5639 (by decide +kernel)

theorem valid6812 : plan6812.Valid := valid_step _ _ _ valid5640 (by decide +kernel)

theorem valid6813 : plan6813.Valid := valid_step _ _ _ valid5641 (by decide +kernel)

theorem valid6814 : plan6814.Valid := valid_step _ _ _ valid5642 (by decide +kernel)

theorem valid6815 : plan6815.Valid := valid_step _ _ _ valid5643 (by decide +kernel)


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
theorem t6_312choices : plan6811.choices=[1,3,6,10,7,7].map (options 6 4) := by rfl


theorem t6_312part0 : t6_312jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_312part1 : t6_312jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_312part2 : t6_312jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_312part3 : t6_312jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_312part4 : t6_312jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_312part5 : t6_312jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_312frontier : t6_312root.frontier 3=t6_312jobs := by rfl
theorem t6_312all : t6_312jobs.all (Job.check tree)=true := by
  simp only [t6_312jobs,List.all_append,List.all_nil,t6_312part0,t6_312part1,t6_312part2,t6_312part3,t6_312part4,t6_312part5,Bool.and_self]
theorem t6_312checked : Checked tree [1,3,6,10,7,7] := by
  refine ⟨plan6811,valid6811,t6_312choices,?_⟩
  exact check_of_frontier tree 3 t6_312root t6_312jobs t6_312frontier t6_312all
theorem t6_313choices : plan6812.choices=[1,3,6,10,10,7].map (options 6 4) := by rfl


theorem t6_313part0 : t6_313jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_313part1 : t6_313jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_313part2 : t6_313jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_313part3 : t6_313jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_313frontier : t6_313root.frontier 3=t6_313jobs := by rfl
theorem t6_313all : t6_313jobs.all (Job.check tree)=true := by
  simp only [t6_313jobs,List.all_append,List.all_nil,t6_313part0,t6_313part1,t6_313part2,t6_313part3,Bool.and_self]
theorem t6_313checked : Checked tree [1,3,6,10,10,7] := by
  refine ⟨plan6812,valid6812,t6_313choices,?_⟩
  exact check_of_frontier tree 3 t6_313root t6_313jobs t6_313frontier t6_313all
theorem t6_314choices : plan6813.choices=[1,3,6,10,10,10].map (options 6 4) := by rfl


theorem t6_314part0 : t6_314jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_314frontier : t6_314root.frontier 0=t6_314jobs := by rfl
theorem t6_314all : t6_314jobs.all (Job.check tree)=true := by
  simp only [t6_314jobs,List.all_append,List.all_nil,t6_314part0,Bool.and_self]
theorem t6_314checked : Checked tree [1,3,6,10,10,10] := by
  refine ⟨plan6813,valid6813,t6_314choices,?_⟩
  exact check_of_frontier tree 0 t6_314root t6_314jobs t6_314frontier t6_314all
theorem t6_315choices : plan6814.choices=[1,3,7,7,7,7].map (options 6 4) := by rfl


theorem t6_315part0 : t6_315jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_315part1 : t6_315jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_315part2 : t6_315jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_315frontier : t6_315root.frontier 1=t6_315jobs := by rfl
theorem t6_315all : t6_315jobs.all (Job.check tree)=true := by
  simp only [t6_315jobs,List.all_append,List.all_nil,t6_315part0,t6_315part1,t6_315part2,Bool.and_self]
theorem t6_315checked : Checked tree [1,3,7,7,7,7] := by
  refine ⟨plan6814,valid6814,t6_315choices,?_⟩
  exact check_of_frontier tree 1 t6_315root t6_315jobs t6_315frontier t6_315all
theorem t6_316choices : plan6815.choices=[1,3,10,7,7,7].map (options 6 4) := by rfl


theorem t6_316part0 : t6_316jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_316part1 : t6_316jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_316part2 : t6_316jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_316part3 : t6_316jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_316part4 : t6_316jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_316frontier : t6_316root.frontier 2=t6_316jobs := by rfl
theorem t6_316all : t6_316jobs.all (Job.check tree)=true := by
  simp only [t6_316jobs,List.all_append,List.all_nil,t6_316part0,t6_316part1,t6_316part2,t6_316part3,t6_316part4,Bool.and_self]
theorem t6_316checked : Checked tree [1,3,10,7,7,7] := by
  refine ⟨plan6815,valid6815,t6_316choices,?_⟩
  exact check_of_frontier tree 2 t6_316root t6_316jobs t6_316frontier t6_316all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks055 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_313checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_314checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_315checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_316checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_312checked⟩
