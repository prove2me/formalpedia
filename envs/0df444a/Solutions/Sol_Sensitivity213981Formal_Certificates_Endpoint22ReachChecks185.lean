-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks185
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:13:47.214059+00:00
-- url     : https://prove2.me/submissions/64da75ea-34b6-4833-b053-df5e8231c02f

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks185
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks185
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
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





























































theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)

theorem valid608 : plan608.Valid := valid_step _ _ _ valid150 (by decide +kernel)





theorem valid611 : plan611.Valid := valid_step _ _ _ valid153 (by decide +kernel)



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







































theorem valid1652 : plan1652.Valid := valid_step _ _ _ valid608 (by decide +kernel)



theorem valid1654 : plan1654.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1655 : plan1655.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1656 : plan1656.Valid := valid_step _ _ _ valid608 (by decide +kernel)





theorem valid1659 : plan1659.Valid := valid_step _ _ _ valid611 (by decide +kernel)



theorem valid1661 : plan1661.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1662 : plan1662.Valid := valid_step _ _ _ valid614 (by decide +kernel)



theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)
































































































































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































































theorem valid3584 : plan3584.Valid := valid_step _ _ _ valid1652 (by decide +kernel)

theorem valid3585 : plan3585.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

theorem valid3586 : plan3586.Valid := valid_step _ _ _ valid1655 (by decide +kernel)

theorem valid3587 : plan3587.Valid := valid_step _ _ _ valid1656 (by decide +kernel)







































theorem valid3607 : plan3607.Valid := valid_step _ _ _ valid1659 (by decide +kernel)



theorem valid3609 : plan3609.Valid := valid_step _ _ _ valid1661 (by decide +kernel)

theorem valid3610 : plan3610.Valid := valid_step _ _ _ valid1662 (by decide +kernel)



theorem valid3612 : plan3612.Valid := valid_step _ _ _ valid1664 (by decide +kernel)








































































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















































































































































































theorem valid6136 : plan6136.Valid := valid_step _ _ _ valid3584 (by decide +kernel)

theorem valid6137 : plan6137.Valid := valid_step _ _ _ valid3585 (by decide +kernel)

theorem valid6138 : plan6138.Valid := valid_step _ _ _ valid3586 (by decide +kernel)

theorem valid6139 : plan6139.Valid := valid_step _ _ _ valid3587 (by decide +kernel)










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

































theorem valid6161 : plan6161.Valid := valid_step _ _ _ valid3607 (by decide +kernel)

theorem valid6162 : plan6162.Valid := valid_step _ _ _ valid3609 (by decide +kernel)

theorem valid6163 : plan6163.Valid := valid_step _ _ _ valid3610 (by decide +kernel)

theorem valid6164 : plan6164.Valid := valid_step _ _ _ valid3612 (by decide +kernel)
























































































































































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











































































































theorem valid8118 : plan8118.Valid := valid_step _ _ _ valid6136 (by decide +kernel)

theorem valid8119 : plan8119.Valid := valid_step _ _ _ valid6137 (by decide +kernel)

theorem valid8120 : plan8120.Valid := valid_step _ _ _ valid6138 (by decide +kernel)

theorem valid8121 : plan8121.Valid := valid_step _ _ _ valid6139 (by decide +kernel)














































































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



































































































































































theorem valid8530 : plan8530.Valid := valid_step _ _ _ valid8118 (by decide +kernel)

theorem valid8531 : plan8531.Valid := valid_step _ _ _ valid8119 (by decide +kernel)

theorem valid8532 : plan8532.Valid := valid_step _ _ _ valid8120 (by decide +kernel)

theorem valid8533 : plan8533.Valid := valid_step _ _ _ valid8121 (by decide +kernel)






















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















theorem valid8168 : plan8168.Valid := valid_step _ _ _ valid6161 (by decide +kernel)

theorem valid8169 : plan8169.Valid := valid_step _ _ _ valid6162 (by decide +kernel)

theorem valid8170 : plan8170.Valid := valid_step _ _ _ valid6163 (by decide +kernel)

theorem valid8171 : plan8171.Valid := valid_step _ _ _ valid6164 (by decide +kernel)










































































































































































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





















































theorem valid8667 : plan8667.Valid := valid_step _ _ _ valid8168 (by decide +kernel)

theorem valid8668 : plan8668.Valid := valid_step _ _ _ valid8169 (by decide +kernel)

theorem valid8669 : plan8669.Valid := valid_step _ _ _ valid8170 (by decide +kernel)

theorem valid8670 : plan8670.Valid := valid_step _ _ _ valid8171 (by decide +kernel)




































































































































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
theorem t7_427choices : plan8530.choices=[5,3,3,3,6,10,7].map (options 7 4) := by rfl


theorem t7_427part0 : t7_427jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_427part1 : t7_427jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_427frontier : t7_427root.frontier 1=t7_427jobs := by rfl
theorem t7_427all : t7_427jobs.all (Job.check tree)=true := by
  simp only [t7_427jobs,List.all_append,List.all_nil,t7_427part0,t7_427part1,Bool.and_self]
theorem t7_427checked : Checked tree [5,3,3,3,6,10,7] := by
  refine ⟨plan8530,valid8530,t7_427choices,?_⟩
  exact check_of_frontier tree 1 t7_427root t7_427jobs t7_427frontier t7_427all
theorem t7_428choices : plan8531.choices=[5,3,3,3,7,7,7].map (options 7 4) := by rfl


theorem t7_428part0 : t7_428jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_428part1 : t7_428jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_428part2 : t7_428jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_428part3 : t7_428jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_428frontier : t7_428root.frontier 1=t7_428jobs := by rfl
theorem t7_428all : t7_428jobs.all (Job.check tree)=true := by
  simp only [t7_428jobs,List.all_append,List.all_nil,t7_428part0,t7_428part1,t7_428part2,t7_428part3,Bool.and_self]
theorem t7_428checked : Checked tree [5,3,3,3,7,7,7] := by
  refine ⟨plan8531,valid8531,t7_428choices,?_⟩
  exact check_of_frontier tree 1 t7_428root t7_428jobs t7_428frontier t7_428all
theorem t7_429choices : plan8532.choices=[5,3,3,3,10,7,7].map (options 7 4) := by rfl


theorem t7_429part0 : t7_429jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_429part1 : t7_429jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_429part2 : t7_429jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_429frontier : t7_429root.frontier 1=t7_429jobs := by rfl
theorem t7_429all : t7_429jobs.all (Job.check tree)=true := by
  simp only [t7_429jobs,List.all_append,List.all_nil,t7_429part0,t7_429part1,t7_429part2,Bool.and_self]
theorem t7_429checked : Checked tree [5,3,3,3,10,7,7] := by
  refine ⟨plan8532,valid8532,t7_429choices,?_⟩
  exact check_of_frontier tree 1 t7_429root t7_429jobs t7_429frontier t7_429all
theorem t7_430choices : plan8533.choices=[5,3,3,3,10,10,7].map (options 7 4) := by rfl


theorem t7_430part0 : t7_430jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_430frontier : t7_430root.frontier 0=t7_430jobs := by rfl
theorem t7_430all : t7_430jobs.all (Job.check tree)=true := by
  simp only [t7_430jobs,List.all_append,List.all_nil,t7_430part0,Bool.and_self]
theorem t7_430checked : Checked tree [5,3,3,3,10,10,7] := by
  refine ⟨plan8533,valid8533,t7_430choices,?_⟩
  exact check_of_frontier tree 0 t7_430root t7_430jobs t7_430frontier t7_430all
theorem t7_431choices : plan8667.choices=[5,3,3,6,6,6,7].map (options 7 5) := by rfl


theorem t7_431part0 : t7_431jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_431frontier : t7_431root.frontier 0=t7_431jobs := by rfl
theorem t7_431all : t7_431jobs.all (Job.check tree)=true := by
  simp only [t7_431jobs,List.all_append,List.all_nil,t7_431part0,Bool.and_self]
theorem t7_431checked : Checked tree [5,3,3,6,6,6,7] := by
  refine ⟨plan8667,valid8667,t7_431choices,?_⟩
  exact check_of_frontier tree 0 t7_431root t7_431jobs t7_431frontier t7_431all
theorem t7_432choices : plan8668.choices=[5,3,3,6,6,7,7].map (options 7 5) := by rfl


theorem t7_432part0 : t7_432jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_432part1 : t7_432jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_432part2 : t7_432jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_432frontier : t7_432root.frontier 1=t7_432jobs := by rfl
theorem t7_432all : t7_432jobs.all (Job.check tree)=true := by
  simp only [t7_432jobs,List.all_append,List.all_nil,t7_432part0,t7_432part1,t7_432part2,Bool.and_self]
theorem t7_432checked : Checked tree [5,3,3,6,6,7,7] := by
  refine ⟨plan8668,valid8668,t7_432choices,?_⟩
  exact check_of_frontier tree 1 t7_432root t7_432jobs t7_432frontier t7_432all
theorem t7_433choices : plan8669.choices=[5,3,3,6,6,10,7].map (options 7 5) := by rfl


theorem t7_433part0 : t7_433jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_433frontier : t7_433root.frontier 0=t7_433jobs := by rfl
theorem t7_433all : t7_433jobs.all (Job.check tree)=true := by
  simp only [t7_433jobs,List.all_append,List.all_nil,t7_433part0,Bool.and_self]
theorem t7_433checked : Checked tree [5,3,3,6,6,10,7] := by
  refine ⟨plan8669,valid8669,t7_433choices,?_⟩
  exact check_of_frontier tree 0 t7_433root t7_433jobs t7_433frontier t7_433all
theorem t7_434choices : plan8670.choices=[5,3,3,6,7,7,7].map (options 7 5) := by rfl


theorem t7_434part0 : t7_434jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_434part1 : t7_434jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_434part2 : t7_434jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_434part3 : t7_434jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_434part4 : t7_434jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_434part5 : t7_434jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_434frontier : t7_434root.frontier 2=t7_434jobs := by rfl
theorem t7_434all : t7_434jobs.all (Job.check tree)=true := by
  simp only [t7_434jobs,List.all_append,List.all_nil,t7_434part0,t7_434part1,t7_434part2,t7_434part3,t7_434part4,t7_434part5,Bool.and_self]
theorem t7_434checked : Checked tree [5,3,3,6,7,7,7] := by
  refine ⟨plan8670,valid8670,t7_434choices,?_⟩
  exact check_of_frontier tree 2 t7_434root t7_434jobs t7_434frontier t7_434all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks185 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_434checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_427checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_428checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_429checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_430checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_431checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_432checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_433checked⟩
