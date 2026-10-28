-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks081
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:19:46.694253+00:00
-- url     : https://prove2.me/submissions/0289dde5-a510-4a4e-bf9e-bccbc8122cae

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks081
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks081
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
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























































theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid125 : plan125.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)






























































































































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





































































































































theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid548 : plan548.Valid := valid_step _ _ _ valid125 (by decide +kernel)





















theorem valid559 : plan559.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)






























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

























































































































































theorem valid1517 : plan1517.Valid := valid_step _ _ _ valid547 (by decide +kernel)

theorem valid1518 : plan1518.Valid := valid_step _ _ _ valid548 (by decide +kernel)



























theorem valid1532 : plan1532.Valid := valid_step _ _ _ valid559 (by decide +kernel)

theorem valid1533 : plan1533.Valid := valid_step _ _ _ valid560 (by decide +kernel)

theorem valid1534 : plan1534.Valid := valid_step _ _ _ valid561 (by decide +kernel)




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



theorem valid3266 : plan3266.Valid := valid_step _ _ _ valid1517 (by decide +kernel)

theorem valid3267 : plan3267.Valid := valid_step _ _ _ valid1518 (by decide +kernel)













































































theorem valid3306 : plan3306.Valid := valid_step _ _ _ valid1532 (by decide +kernel)

theorem valid3307 : plan3307.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3308 : plan3308.Valid := valid_step _ _ _ valid1534 (by decide +kernel)








































































































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

























































theorem valid5405 : plan5405.Valid := valid_step _ _ _ valid3266 (by decide +kernel)

theorem valid5406 : plan5406.Valid := valid_step _ _ _ valid3267 (by decide +kernel)




































































































































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































































theorem valid5504 : plan5504.Valid := valid_step _ _ _ valid3306 (by decide +kernel)

theorem valid5505 : plan5505.Valid := valid_step _ _ _ valid3307 (by decide +kernel)

theorem valid5506 : plan5506.Valid := valid_step _ _ _ valid3308 (by decide +kernel)




























































































































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

















































































































theorem valid6393 : plan6393.Valid := valid_step _ _ _ valid5405 (by decide +kernel)

theorem valid6394 : plan6394.Valid := valid_step _ _ _ valid5406 (by decide +kernel)












































































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





















































































































theorem valid6587 : plan6587.Valid := valid_step _ _ _ valid5504 (by decide +kernel)

theorem valid6588 : plan6588.Valid := valid_step _ _ _ valid5505 (by decide +kernel)

theorem valid6589 : plan6589.Valid := valid_step _ _ _ valid5506 (by decide +kernel)






































































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
theorem t6_668choices : plan6393.choices=[2,5,3,3,3,7].map (options 6 2) := by rfl


theorem t6_668part0 : t6_668jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_668part1 : t6_668jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_668part2 : t6_668jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_668part3 : t6_668jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_668frontier : t6_668root.frontier 1=t6_668jobs := by rfl
theorem t6_668all : t6_668jobs.all (Job.check tree)=true := by
  simp only [t6_668jobs,List.all_append,List.all_nil,t6_668part0,t6_668part1,t6_668part2,t6_668part3,Bool.and_self]
theorem t6_668checked : Checked tree [2,5,3,3,3,7] := by
  refine ⟨plan6393,valid6393,t6_668choices,?_⟩
  exact check_of_frontier tree 1 t6_668root t6_668jobs t6_668frontier t6_668all
theorem t6_669choices : plan6394.choices=[2,5,3,3,3,10].map (options 6 2) := by rfl


theorem t6_669part0 : t6_669jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_669frontier : t6_669root.frontier 0=t6_669jobs := by rfl
theorem t6_669all : t6_669jobs.all (Job.check tree)=true := by
  simp only [t6_669jobs,List.all_append,List.all_nil,t6_669part0,Bool.and_self]
theorem t6_669checked : Checked tree [2,5,3,3,3,10] := by
  refine ⟨plan6394,valid6394,t6_669choices,?_⟩
  exact check_of_frontier tree 0 t6_669root t6_669jobs t6_669frontier t6_669all
theorem t6_670choices : plan6587.choices=[2,5,3,3,6,6].map (options 6 3) := by rfl


theorem t6_670part0 : t6_670jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_670part1 : t6_670jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_670frontier : t6_670root.frontier 1=t6_670jobs := by rfl
theorem t6_670all : t6_670jobs.all (Job.check tree)=true := by
  simp only [t6_670jobs,List.all_append,List.all_nil,t6_670part0,t6_670part1,Bool.and_self]
theorem t6_670checked : Checked tree [2,5,3,3,6,6] := by
  refine ⟨plan6587,valid6587,t6_670choices,?_⟩
  exact check_of_frontier tree 1 t6_670root t6_670jobs t6_670frontier t6_670all
theorem t6_671choices : plan6588.choices=[2,5,3,3,6,7].map (options 6 3) := by rfl


theorem t6_671part0 : t6_671jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_671part1 : t6_671jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_671part2 : t6_671jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_671part3 : t6_671jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_671part4 : t6_671jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_671part5 : t6_671jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_671part6 : t6_671jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_671frontier : t6_671root.frontier 2=t6_671jobs := by rfl
theorem t6_671all : t6_671jobs.all (Job.check tree)=true := by
  simp only [t6_671jobs,List.all_append,List.all_nil,t6_671part0,t6_671part1,t6_671part2,t6_671part3,t6_671part4,t6_671part5,t6_671part6,Bool.and_self]
theorem t6_671checked : Checked tree [2,5,3,3,6,7] := by
  refine ⟨plan6588,valid6588,t6_671choices,?_⟩
  exact check_of_frontier tree 2 t6_671root t6_671jobs t6_671frontier t6_671all
theorem t6_672choices : plan6589.choices=[2,5,3,3,6,10].map (options 6 3) := by rfl


theorem t6_672part0 : t6_672jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_672part1 : t6_672jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_672part2 : t6_672jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_672frontier : t6_672root.frontier 1=t6_672jobs := by rfl
theorem t6_672all : t6_672jobs.all (Job.check tree)=true := by
  simp only [t6_672jobs,List.all_append,List.all_nil,t6_672part0,t6_672part1,t6_672part2,Bool.and_self]
theorem t6_672checked : Checked tree [2,5,3,3,6,10] := by
  refine ⟨plan6589,valid6589,t6_672choices,?_⟩
  exact check_of_frontier tree 1 t6_672root t6_672jobs t6_672frontier t6_672all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks081 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_668checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_669checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_670checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_671checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_672checked⟩
