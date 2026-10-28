-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks146
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:00:31.864348+00:00
-- url     : https://prove2.me/submissions/2c066fee-8a43-4c6f-8799-33233ca9bd11

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks146
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks146
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans069
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans074
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

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)




























































































































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

































































































































































theorem valid561 : plan561.Valid := valid_step _ _ _ valid129 (by decide +kernel)

theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)
















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



























































































































































































theorem valid1534 : plan1534.Valid := valid_step _ _ _ valid561 (by decide +kernel)

theorem valid1535 : plan1535.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1536 : plan1536.Valid := valid_step _ _ _ valid563 (by decide +kernel)
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

theorem valid1537 : plan1537.Valid := valid_step _ _ _ valid564 (by decide +kernel)































































theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)






























































































































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























































































theorem valid3308 : plan3308.Valid := valid_step _ _ _ valid1534 (by decide +kernel)

theorem valid3309 : plan3309.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3310 : plan3310.Valid := valid_step _ _ _ valid1536 (by decide +kernel)

theorem valid3311 : plan3311.Valid := valid_step _ _ _ valid1537 (by decide +kernel)

































































































theorem valid3360 : plan3360.Valid := valid_step _ _ _ valid1569 (by decide +kernel)
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



















theorem valid5482 : plan5482.Valid := valid_step _ _ _ valid3308 (by decide +kernel)

theorem valid5483 : plan5483.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5484 : plan5484.Valid := valid_step _ _ _ valid3310 (by decide +kernel)

theorem valid5485 : plan5485.Valid := valid_step _ _ _ valid3311 (by decide +kernel)






































































































































































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











































































































theorem valid5622 : plan5622.Valid := valid_step _ _ _ valid3360 (by decide +kernel)




















































































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



























































































































theorem valid6686 : plan6686.Valid := valid_step _ _ _ valid5482 (by decide +kernel)

theorem valid6687 : plan6687.Valid := valid_step _ _ _ valid5483 (by decide +kernel)

theorem valid6688 : plan6688.Valid := valid_step _ _ _ valid5484 (by decide +kernel)

theorem valid6689 : plan6689.Valid := valid_step _ _ _ valid5485 (by decide +kernel)






























































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













































theorem valid7127 : plan7127.Valid := valid_step _ _ _ valid5622 (by decide +kernel)


















































































































































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
theorem t6_1681choices : plan6686.choices=[9,3,3,3,6,10].map (options 6 3) := by rfl


theorem t6_1681part0 : t6_1681jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1681part1 : t6_1681jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1681part2 : t6_1681jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1681part3 : t6_1681jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1681frontier : t6_1681root.frontier 1=t6_1681jobs := by rfl
theorem t6_1681all : t6_1681jobs.all (Job.check tree)=true := by
  simp only [t6_1681jobs,List.all_append,List.all_nil,t6_1681part0,t6_1681part1,t6_1681part2,t6_1681part3,Bool.and_self]
theorem t6_1681checked : Checked tree [9,3,3,3,6,10] := by
  refine ⟨plan6686,valid6686,t6_1681choices,?_⟩
  exact check_of_frontier tree 1 t6_1681root t6_1681jobs t6_1681frontier t6_1681all
theorem t6_1682choices : plan6687.choices=[9,3,3,3,7,7].map (options 6 3) := by rfl


theorem t6_1682part0 : t6_1682jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1682part1 : t6_1682jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1682part2 : t6_1682jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1682part3 : t6_1682jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1682part4 : t6_1682jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1682frontier : t6_1682root.frontier 2=t6_1682jobs := by rfl
theorem t6_1682all : t6_1682jobs.all (Job.check tree)=true := by
  simp only [t6_1682jobs,List.all_append,List.all_nil,t6_1682part0,t6_1682part1,t6_1682part2,t6_1682part3,t6_1682part4,Bool.and_self]
theorem t6_1682checked : Checked tree [9,3,3,3,7,7] := by
  refine ⟨plan6687,valid6687,t6_1682choices,?_⟩
  exact check_of_frontier tree 2 t6_1682root t6_1682jobs t6_1682frontier t6_1682all
theorem t6_1683choices : plan6688.choices=[9,3,3,3,10,7].map (options 6 3) := by rfl


theorem t6_1683part0 : t6_1683jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1683part1 : t6_1683jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1683part2 : t6_1683jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_1683part3 : t6_1683jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_1683part4 : t6_1683jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_1683part5 : t6_1683jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_1683frontier : t6_1683root.frontier 2=t6_1683jobs := by rfl
theorem t6_1683all : t6_1683jobs.all (Job.check tree)=true := by
  simp only [t6_1683jobs,List.all_append,List.all_nil,t6_1683part0,t6_1683part1,t6_1683part2,t6_1683part3,t6_1683part4,t6_1683part5,Bool.and_self]
theorem t6_1683checked : Checked tree [9,3,3,3,10,7] := by
  refine ⟨plan6688,valid6688,t6_1683choices,?_⟩
  exact check_of_frontier tree 2 t6_1683root t6_1683jobs t6_1683frontier t6_1683all
theorem t6_1684choices : plan6689.choices=[9,3,3,3,10,10].map (options 6 3) := by rfl


theorem t6_1684part0 : t6_1684jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1684part1 : t6_1684jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1684frontier : t6_1684root.frontier 1=t6_1684jobs := by rfl
theorem t6_1684all : t6_1684jobs.all (Job.check tree)=true := by
  simp only [t6_1684jobs,List.all_append,List.all_nil,t6_1684part0,t6_1684part1,Bool.and_self]
theorem t6_1684checked : Checked tree [9,3,3,3,10,10] := by
  refine ⟨plan6689,valid6689,t6_1684choices,?_⟩
  exact check_of_frontier tree 1 t6_1684root t6_1684jobs t6_1684frontier t6_1684all
theorem t6_1685choices : plan7127.choices=[9,3,3,6,6,6].map (options 6 4) := by rfl


theorem t6_1685part0 : t6_1685jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_1685part1 : t6_1685jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_1685frontier : t6_1685root.frontier 1=t6_1685jobs := by rfl
theorem t6_1685all : t6_1685jobs.all (Job.check tree)=true := by
  simp only [t6_1685jobs,List.all_append,List.all_nil,t6_1685part0,t6_1685part1,Bool.and_self]
theorem t6_1685checked : Checked tree [9,3,3,6,6,6] := by
  refine ⟨plan7127,valid7127,t6_1685choices,?_⟩
  exact check_of_frontier tree 1 t6_1685root t6_1685jobs t6_1685frontier t6_1685all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks146 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1683checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1684checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1685checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1681checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_1682checked⟩
