-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks160
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:02:56.014813+00:00
-- url     : https://prove2.me/submissions/de37cbd1-44a9-428c-9fa5-aeee0a8dec88

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks160
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks160
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
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

theorem valid608 : plan608.Valid := valid_step _ _ _ valid150 (by decide +kernel)
































































































































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





































theorem valid1651 : plan1651.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1652 : plan1652.Valid := valid_step _ _ _ valid608 (by decide +kernel)



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













































































theorem valid3591 : plan3591.Valid := valid_step _ _ _ valid1651 (by decide +kernel)

theorem valid3592 : plan3592.Valid := valid_step _ _ _ valid1652 (by decide +kernel)



theorem valid3594 : plan3594.Valid := valid_step _ _ _ valid1654 (by decide +kernel)












































































































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





























































































































































































theorem valid6143 : plan6143.Valid := valid_step _ _ _ valid3591 (by decide +kernel)

theorem valid6144 : plan6144.Valid := valid_step _ _ _ valid3592 (by decide +kernel)
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



theorem valid6146 : plan6146.Valid := valid_step _ _ _ valid3594 (by decide +kernel)




























































































































































































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

























































































































theorem valid8125 : plan8125.Valid := valid_step _ _ _ valid6143 (by decide +kernel)

theorem valid8126 : plan8126.Valid := valid_step _ _ _ valid6144 (by decide +kernel)



theorem valid8128 : plan8128.Valid := valid_step _ _ _ valid6146 (by decide +kernel)
































































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



























































































theorem valid8494 : plan8494.Valid := valid_step _ _ _ valid8125 (by decide +kernel)

theorem valid8495 : plan8495.Valid := valid_step _ _ _ valid8126 (by decide +kernel)

theorem valid8496 : plan8496.Valid := valid_step _ _ _ valid8128 (by decide +kernel)
































































































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
theorem t7_161choices : plan8494.choices=[2,3,3,6,6,7,7].map (options 7 4) := by rfl


theorem t7_161part0 : t7_161jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_161part1 : t7_161jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_161part2 : t7_161jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_161part3 : t7_161jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_161frontier : t7_161root.frontier 2=t7_161jobs := by rfl
theorem t7_161all : t7_161jobs.all (Job.check tree)=true := by
  simp only [t7_161jobs,List.all_append,List.all_nil,t7_161part0,t7_161part1,t7_161part2,t7_161part3,Bool.and_self]
theorem t7_161checked : Checked tree [2,3,3,6,6,7,7] := by
  refine ⟨plan8494,valid8494,t7_161choices,?_⟩
  exact check_of_frontier tree 2 t7_161root t7_161jobs t7_161frontier t7_161all
theorem t7_162choices : plan8495.choices=[2,3,3,6,6,10,7].map (options 7 4) := by rfl


theorem t7_162part0 : t7_162jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_162part1 : t7_162jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_162part2 : t7_162jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_162frontier : t7_162root.frontier 1=t7_162jobs := by rfl
theorem t7_162all : t7_162jobs.all (Job.check tree)=true := by
  simp only [t7_162jobs,List.all_append,List.all_nil,t7_162part0,t7_162part1,t7_162part2,Bool.and_self]
theorem t7_162checked : Checked tree [2,3,3,6,6,10,7] := by
  refine ⟨plan8495,valid8495,t7_162choices,?_⟩
  exact check_of_frontier tree 1 t7_162root t7_162jobs t7_162frontier t7_162all
theorem t7_163choices : plan8496.choices=[2,3,3,6,7,7,7].map (options 7 4) := by rfl


theorem t7_163part0 : t7_163jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_163part1 : t7_163jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_163part2 : t7_163jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_163part3 : t7_163jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_163part4 : t7_163jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_163part5 : t7_163jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_163part6 : t7_163jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_163part7 : t7_163jobs7.all (Job.check tree)=true := by decide +kernel

theorem t7_163part8 : t7_163jobs8.all (Job.check tree)=true := by decide +kernel

theorem t7_163part9 : t7_163jobs9.all (Job.check tree)=true := by decide +kernel

theorem t7_163frontier : t7_163root.frontier 2=t7_163jobs := by rfl
theorem t7_163all : t7_163jobs.all (Job.check tree)=true := by
  simp only [t7_163jobs,List.all_append,List.all_nil,t7_163part0,t7_163part1,t7_163part2,t7_163part3,t7_163part4,t7_163part5,t7_163part6,t7_163part7,t7_163part8,t7_163part9,Bool.and_self]
theorem t7_163checked : Checked tree [2,3,3,6,7,7,7] := by
  refine ⟨plan8496,valid8496,t7_163choices,?_⟩
  exact check_of_frontier tree 2 t7_163root t7_163jobs t7_163frontier t7_163all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks160 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_163checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_161checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_162checked⟩
