-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks174
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:12:07.906973+00:00
-- url     : https://prove2.me/submissions/d6935a73-5fef-4b15-8924-c8ca873d20bc

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks174
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks174
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
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











































theorem valid1654 : plan1654.Valid := valid_step _ _ _ valid607 (by decide +kernel)




















































































































































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



























































































theorem valid3598 : plan3598.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

theorem valid3599 : plan3599.Valid := valid_step _ _ _ valid1654 (by decide +kernel)


































































































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











theorem valid6150 : plan6150.Valid := valid_step _ _ _ valid3598 (by decide +kernel)

theorem valid6151 : plan6151.Valid := valid_step _ _ _ valid3599 (by decide +kernel)


















































































































































































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







































































































































theorem valid8132 : plan8132.Valid := valid_step _ _ _ valid6150 (by decide +kernel)

theorem valid8133 : plan8133.Valid := valid_step _ _ _ valid6151 (by decide +kernel)






















































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













































































































































theorem valid8519 : plan8519.Valid := valid_step _ _ _ valid8132 (by decide +kernel)

theorem valid8520 : plan8520.Valid := valid_step _ _ _ valid8133 (by decide +kernel)
















































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
theorem t7_288choices : plan8519.choices=[3,3,3,7,7,7,7].map (options 7 4) := by rfl


theorem t7_288part0 : t7_288jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_288part1 : t7_288jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_288part2 : t7_288jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_288part3 : t7_288jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_288part4 : t7_288jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_288part5 : t7_288jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_288part6 : t7_288jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_288frontier : t7_288root.frontier 2=t7_288jobs := by rfl
theorem t7_288all : t7_288jobs.all (Job.check tree)=true := by
  simp only [t7_288jobs,List.all_append,List.all_nil,t7_288part0,t7_288part1,t7_288part2,t7_288part3,t7_288part4,t7_288part5,t7_288part6,Bool.and_self]
theorem t7_288checked : Checked tree [3,3,3,7,7,7,7] := by
  refine ⟨plan8519,valid8519,t7_288choices,?_⟩
  exact check_of_frontier tree 2 t7_288root t7_288jobs t7_288frontier t7_288all
theorem t7_289choices : plan8520.choices=[3,3,3,10,7,7,7].map (options 7 4) := by rfl


theorem t7_289part0 : t7_289jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_289part1 : t7_289jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_289part2 : t7_289jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_289part3 : t7_289jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_289part4 : t7_289jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_289part5 : t7_289jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_289part6 : t7_289jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_289part7 : t7_289jobs7.all (Job.check tree)=true := by decide +kernel

theorem t7_289part8 : t7_289jobs8.all (Job.check tree)=true := by decide +kernel

theorem t7_289frontier : t7_289root.frontier 4=t7_289jobs := by rfl
theorem t7_289all : t7_289jobs.all (Job.check tree)=true := by
  simp only [t7_289jobs,List.all_append,List.all_nil,t7_289part0,t7_289part1,t7_289part2,t7_289part3,t7_289part4,t7_289part5,t7_289part6,t7_289part7,t7_289part8,Bool.and_self]
theorem t7_289checked : Checked tree [3,3,3,10,7,7,7] := by
  refine ⟨plan8520,valid8520,t7_289choices,?_⟩
  exact check_of_frontier tree 4 t7_289root t7_289jobs t7_289frontier t7_289all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks174 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_289checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_288checked⟩
