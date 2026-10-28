-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks164
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:06:27.89299+00:00
-- url     : https://prove2.me/submissions/f25445c1-fbb2-4839-ae09-d77828de09ef

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks164
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks164
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































































































































theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3617 : plan3617.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3618 : plan3618.Valid := valid_step _ _ _ valid1665 (by decide +kernel)

theorem valid3619 : plan3619.Valid := valid_step _ _ _ valid1666 (by decide +kernel)


























































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



















































































theorem valid6186 : plan6186.Valid := valid_step _ _ _ valid3617 (by decide +kernel)

theorem valid6187 : plan6187.Valid := valid_step _ _ _ valid3618 (by decide +kernel)

theorem valid6188 : plan6188.Valid := valid_step _ _ _ valid3619 (by decide +kernel)



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

























































theorem valid8189 : plan8189.Valid := valid_step _ _ _ valid6186 (by decide +kernel)

theorem valid8190 : plan8190.Valid := valid_step _ _ _ valid6187 (by decide +kernel)

theorem valid8191 : plan8191.Valid := valid_step _ _ _ valid6188 (by decide +kernel)



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





































































































































theorem valid8611 : plan8611.Valid := valid_step _ _ _ valid8189 (by decide +kernel)

theorem valid8612 : plan8612.Valid := valid_step _ _ _ valid8190 (by decide +kernel)

theorem valid8613 : plan8613.Valid := valid_step _ _ _ valid8191 (by decide +kernel)

theorem valid8614 : plan8614.Valid := valid_step _ _ _ valid8193 (by decide +kernel)




















































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
theorem t7_177choices : plan8611.choices=[2,3,6,10,7,7,7].map (options 7 5) := by rfl


theorem t7_177part0 : t7_177jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_177part1 : t7_177jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_177part2 : t7_177jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_177part3 : t7_177jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_177part4 : t7_177jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_177part5 : t7_177jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_177part6 : t7_177jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_177part7 : t7_177jobs7.all (Job.check tree)=true := by decide +kernel

theorem t7_177frontier : t7_177root.frontier 3=t7_177jobs := by rfl
theorem t7_177all : t7_177jobs.all (Job.check tree)=true := by
  simp only [t7_177jobs,List.all_append,List.all_nil,t7_177part0,t7_177part1,t7_177part2,t7_177part3,t7_177part4,t7_177part5,t7_177part6,t7_177part7,Bool.and_self]
theorem t7_177checked : Checked tree [2,3,6,10,7,7,7] := by
  refine ⟨plan8611,valid8611,t7_177choices,?_⟩
  exact check_of_frontier tree 3 t7_177root t7_177jobs t7_177frontier t7_177all
theorem t7_178choices : plan8612.choices=[2,3,6,10,10,7,7].map (options 7 5) := by rfl


theorem t7_178part0 : t7_178jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_178part1 : t7_178jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_178part2 : t7_178jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_178part3 : t7_178jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_178frontier : t7_178root.frontier 3=t7_178jobs := by rfl
theorem t7_178all : t7_178jobs.all (Job.check tree)=true := by
  simp only [t7_178jobs,List.all_append,List.all_nil,t7_178part0,t7_178part1,t7_178part2,t7_178part3,Bool.and_self]
theorem t7_178checked : Checked tree [2,3,6,10,10,7,7] := by
  refine ⟨plan8612,valid8612,t7_178choices,?_⟩
  exact check_of_frontier tree 3 t7_178root t7_178jobs t7_178frontier t7_178all
theorem t7_179choices : plan8613.choices=[2,3,6,10,10,10,7].map (options 7 5) := by rfl


theorem t7_179part0 : t7_179jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_179frontier : t7_179root.frontier 0=t7_179jobs := by rfl
theorem t7_179all : t7_179jobs.all (Job.check tree)=true := by
  simp only [t7_179jobs,List.all_append,List.all_nil,t7_179part0,Bool.and_self]
theorem t7_179checked : Checked tree [2,3,6,10,10,10,7] := by
  refine ⟨plan8613,valid8613,t7_179choices,?_⟩
  exact check_of_frontier tree 0 t7_179root t7_179jobs t7_179frontier t7_179all
theorem t7_180choices : plan8614.choices=[2,3,7,7,7,7,7].map (options 7 5) := by rfl


theorem t7_180part0 : t7_180jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_180part1 : t7_180jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_180part2 : t7_180jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_180part3 : t7_180jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_180part4 : t7_180jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_180part5 : t7_180jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_180frontier : t7_180root.frontier 2=t7_180jobs := by rfl
theorem t7_180all : t7_180jobs.all (Job.check tree)=true := by
  simp only [t7_180jobs,List.all_append,List.all_nil,t7_180part0,t7_180part1,t7_180part2,t7_180part3,t7_180part4,t7_180part5,Bool.and_self]
theorem t7_180checked : Checked tree [2,3,7,7,7,7,7] := by
  refine ⟨plan8614,valid8614,t7_180choices,?_⟩
  exact check_of_frontier tree 2 t7_180root t7_180jobs t7_180frontier t7_180all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks164 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_177checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_178checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_179checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_180checked⟩
