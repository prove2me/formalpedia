-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks173
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:08:17.121172+00:00
-- url     : https://prove2.me/submissions/11325eb4-020c-4194-a7f9-fabce9b77f1a

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks173
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks173
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

theorem valid151 : plan151.Valid := valid_step _ _ _ valid0 (by decide +kernel)


















































































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

theorem valid609 : plan609.Valid := valid_step _ _ _ valid151 (by decide +kernel)






























































































































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













































theorem valid1655 : plan1655.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1656 : plan1656.Valid := valid_step _ _ _ valid608 (by decide +kernel)

theorem valid1657 : plan1657.Valid := valid_step _ _ _ valid609 (by decide +kernel)














































































































































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





















































































theorem valid3595 : plan3595.Valid := valid_step _ _ _ valid1655 (by decide +kernel)

theorem valid3596 : plan3596.Valid := valid_step _ _ _ valid1656 (by decide +kernel)

theorem valid3597 : plan3597.Valid := valid_step _ _ _ valid1657 (by decide +kernel)






































































































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





theorem valid6147 : plan6147.Valid := valid_step _ _ _ valid3595 (by decide +kernel)

theorem valid6148 : plan6148.Valid := valid_step _ _ _ valid3596 (by decide +kernel)

theorem valid6149 : plan6149.Valid := valid_step _ _ _ valid3597 (by decide +kernel)






















































































































































































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

































































































































theorem valid8129 : plan8129.Valid := valid_step _ _ _ valid6147 (by decide +kernel)

theorem valid8130 : plan8130.Valid := valid_step _ _ _ valid6148 (by decide +kernel)

theorem valid8131 : plan8131.Valid := valid_step _ _ _ valid6149 (by decide +kernel)


























































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







































































































































theorem valid8516 : plan8516.Valid := valid_step _ _ _ valid8129 (by decide +kernel)

theorem valid8517 : plan8517.Valid := valid_step _ _ _ valid8130 (by decide +kernel)

theorem valid8518 : plan8518.Valid := valid_step _ _ _ valid8131 (by decide +kernel)




















































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
theorem t7_285choices : plan8516.choices=[3,3,3,6,10,7,7].map (options 7 4) := by rfl


theorem t7_285part0 : t7_285jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_285part1 : t7_285jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_285part2 : t7_285jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_285part3 : t7_285jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_285part4 : t7_285jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_285part5 : t7_285jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_285part6 : t7_285jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_285part7 : t7_285jobs7.all (Job.check tree)=true := by decide +kernel

theorem t7_285part8 : t7_285jobs8.all (Job.check tree)=true := by decide +kernel

theorem t7_285part9 : t7_285jobs9.all (Job.check tree)=true := by decide +kernel

theorem t7_285part10 : t7_285jobs10.all (Job.check tree)=true := by decide +kernel

theorem t7_285frontier : t7_285root.frontier 4=t7_285jobs := by rfl
theorem t7_285all : t7_285jobs.all (Job.check tree)=true := by
  simp only [t7_285jobs,List.all_append,List.all_nil,t7_285part0,t7_285part1,t7_285part2,t7_285part3,t7_285part4,t7_285part5,t7_285part6,t7_285part7,t7_285part8,t7_285part9,t7_285part10,Bool.and_self]
theorem t7_285checked : Checked tree [3,3,3,6,10,7,7] := by
  refine ⟨plan8516,valid8516,t7_285choices,?_⟩
  exact check_of_frontier tree 4 t7_285root t7_285jobs t7_285frontier t7_285all
theorem t7_286choices : plan8517.choices=[3,3,3,6,10,10,7].map (options 7 4) := by rfl


theorem t7_286part0 : t7_286jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_286part1 : t7_286jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_286part2 : t7_286jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_286part3 : t7_286jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_286frontier : t7_286root.frontier 4=t7_286jobs := by rfl
theorem t7_286all : t7_286jobs.all (Job.check tree)=true := by
  simp only [t7_286jobs,List.all_append,List.all_nil,t7_286part0,t7_286part1,t7_286part2,t7_286part3,Bool.and_self]
theorem t7_286checked : Checked tree [3,3,3,6,10,10,7] := by
  refine ⟨plan8517,valid8517,t7_286choices,?_⟩
  exact check_of_frontier tree 4 t7_286root t7_286jobs t7_286frontier t7_286all
theorem t7_287choices : plan8518.choices=[3,3,3,6,10,10,10].map (options 7 4) := by rfl


theorem t7_287part0 : t7_287jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_287frontier : t7_287root.frontier 0=t7_287jobs := by rfl
theorem t7_287all : t7_287jobs.all (Job.check tree)=true := by
  simp only [t7_287jobs,List.all_append,List.all_nil,t7_287part0,Bool.and_self]
theorem t7_287checked : Checked tree [3,3,3,6,10,10,10] := by
  refine ⟨plan8518,valid8518,t7_287choices,?_⟩
  exact check_of_frontier tree 0 t7_287root t7_287jobs t7_287frontier t7_287all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks173 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_285checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_286checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_287checked⟩
