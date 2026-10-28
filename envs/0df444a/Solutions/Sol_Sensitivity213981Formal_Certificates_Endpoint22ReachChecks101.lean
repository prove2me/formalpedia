-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks101
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:37:34.482706+00:00
-- url     : https://prove2.me/submissions/acad7b2b-649d-426c-94f5-f39b18796d45

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks101
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks101
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
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





































































































































































theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)
























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



















theorem valid1546 : plan1546.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1547 : plan1547.Valid := valid_step _ _ _ valid564 (by decide +kernel)










































































































































































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







































































































theorem valid3316 : plan3316.Valid := valid_step _ _ _ valid1546 (by decide +kernel)

theorem valid3317 : plan3317.Valid := valid_step _ _ _ valid1547 (by decide +kernel)






















































































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



































theorem valid5490 : plan5490.Valid := valid_step _ _ _ valid3316 (by decide +kernel)

theorem valid5491 : plan5491.Valid := valid_step _ _ _ valid3317 (by decide +kernel)


























































































































































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







































































































































































theorem valid6612 : plan6612.Valid := valid_step _ _ _ valid5490 (by decide +kernel)

theorem valid6613 : plan6613.Valid := valid_step _ _ _ valid5491 (by decide +kernel)






















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
theorem t6_847choices : plan6612.choices=[3,3,3,6,10,7].map (options 6 3) := by rfl


theorem t6_847part0 : t6_847jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_847part1 : t6_847jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_847part2 : t6_847jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_847part3 : t6_847jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_847part4 : t6_847jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_847part5 : t6_847jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_847part6 : t6_847jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_847part7 : t6_847jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_847part8 : t6_847jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_847part9 : t6_847jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_847part10 : t6_847jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_847part11 : t6_847jobs11.all (Job.check tree)=true := by decide +kernel

theorem t6_847part12 : t6_847jobs12.all (Job.check tree)=true := by decide +kernel

theorem t6_847part13 : t6_847jobs13.all (Job.check tree)=true := by decide +kernel

theorem t6_847frontier : t6_847root.frontier 2=t6_847jobs := by rfl
theorem t6_847all : t6_847jobs.all (Job.check tree)=true := by
  simp only [t6_847jobs,List.all_append,List.all_nil,t6_847part0,t6_847part1,t6_847part2,t6_847part3,t6_847part4,t6_847part5,t6_847part6,t6_847part7,t6_847part8,t6_847part9,t6_847part10,t6_847part11,t6_847part12,t6_847part13,Bool.and_self]
theorem t6_847checked : Checked tree [3,3,3,6,10,7] := by
  refine ⟨plan6612,valid6612,t6_847choices,?_⟩
  exact check_of_frontier tree 2 t6_847root t6_847jobs t6_847frontier t6_847all
theorem t6_848choices : plan6613.choices=[3,3,3,6,10,10].map (options 6 3) := by rfl


theorem t6_848part0 : t6_848jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_848part1 : t6_848jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_848part2 : t6_848jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_848part3 : t6_848jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_848frontier : t6_848root.frontier 1=t6_848jobs := by rfl
theorem t6_848all : t6_848jobs.all (Job.check tree)=true := by
  simp only [t6_848jobs,List.all_append,List.all_nil,t6_848part0,t6_848part1,t6_848part2,t6_848part3,Bool.and_self]
theorem t6_848checked : Checked tree [3,3,3,6,10,10] := by
  refine ⟨plan6613,valid6613,t6_848choices,?_⟩
  exact check_of_frontier tree 1 t6_848root t6_848jobs t6_848frontier t6_848all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks101 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_847checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_848checked⟩
