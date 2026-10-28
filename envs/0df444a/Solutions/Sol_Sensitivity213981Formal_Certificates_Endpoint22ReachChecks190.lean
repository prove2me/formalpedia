-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks190
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:16:50.333999+00:00
-- url     : https://prove2.me/submissions/99153ac6-21fd-4749-9002-945aca0d4492

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks190
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks190
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
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































































































theorem valid144 : plan144.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid147 : plan147.Valid := valid_step _ _ _ valid0 (by decide +kernel)





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





























theorem valid591 : plan591.Valid := valid_step _ _ _ valid144 (by decide +kernel)















theorem valid599 : plan599.Valid := valid_step _ _ _ valid147 (by decide +kernel)



theorem valid601 : plan601.Valid := valid_step _ _ _ valid147 (by decide +kernel)

theorem valid602 : plan602.Valid := valid_step _ _ _ valid147 (by decide +kernel)





theorem valid605 : plan605.Valid := valid_step _ _ _ valid150 (by decide +kernel)



theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)

theorem valid608 : plan608.Valid := valid_step _ _ _ valid150 (by decide +kernel)





theorem valid611 : plan611.Valid := valid_step _ _ _ valid153 (by decide +kernel)



theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)






















































































































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



theorem valid1634 : plan1634.Valid := valid_step _ _ _ valid599 (by decide +kernel)

theorem valid1635 : plan1635.Valid := valid_step _ _ _ valid601 (by decide +kernel)

theorem valid1636 : plan1636.Valid := valid_step _ _ _ valid602 (by decide +kernel)

























theorem valid1649 : plan1649.Valid := valid_step _ _ _ valid605 (by decide +kernel)



theorem valid1651 : plan1651.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1652 : plan1652.Valid := valid_step _ _ _ valid608 (by decide +kernel)



theorem valid1654 : plan1654.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1655 : plan1655.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1656 : plan1656.Valid := valid_step _ _ _ valid608 (by decide +kernel)





theorem valid1659 : plan1659.Valid := valid_step _ _ _ valid611 (by decide +kernel)



theorem valid1661 : plan1661.Valid := valid_step _ _ _ valid613 (by decide +kernel)






































































































































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





















































































































































































theorem valid1627 : plan1627.Valid := valid_step _ _ _ valid591 (by decide +kernel)










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

















theorem valid3561 : plan3561.Valid := valid_step _ _ _ valid1627 (by decide +kernel)













theorem valid3568 : plan3568.Valid := valid_step _ _ _ valid1634 (by decide +kernel)

theorem valid3569 : plan3569.Valid := valid_step _ _ _ valid1635 (by decide +kernel)

theorem valid3570 : plan3570.Valid := valid_step _ _ _ valid1636 (by decide +kernel)























theorem valid3582 : plan3582.Valid := valid_step _ _ _ valid1649 (by decide +kernel)

theorem valid3583 : plan3583.Valid := valid_step _ _ _ valid1651 (by decide +kernel)

theorem valid3584 : plan3584.Valid := valid_step _ _ _ valid1652 (by decide +kernel)

theorem valid3585 : plan3585.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

theorem valid3586 : plan3586.Valid := valid_step _ _ _ valid1655 (by decide +kernel)

theorem valid3587 : plan3587.Valid := valid_step _ _ _ valid1656 (by decide +kernel)







































theorem valid3607 : plan3607.Valid := valid_step _ _ _ valid1659 (by decide +kernel)



theorem valid3609 : plan3609.Valid := valid_step _ _ _ valid1661 (by decide +kernel)














































































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

























































































































theorem valid6109 : plan6109.Valid := valid_step _ _ _ valid3561 (by decide +kernel)















theorem valid6117 : plan6117.Valid := valid_step _ _ _ valid3568 (by decide +kernel)

theorem valid6118 : plan6118.Valid := valid_step _ _ _ valid3569 (by decide +kernel)

theorem valid6119 : plan6119.Valid := valid_step _ _ _ valid3570 (by decide +kernel)





























theorem valid6134 : plan6134.Valid := valid_step _ _ _ valid3582 (by decide +kernel)

theorem valid6135 : plan6135.Valid := valid_step _ _ _ valid3583 (by decide +kernel)

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

























theorem valid8077 : plan8077.Valid := valid_step _ _ _ valid6109 (by decide +kernel)





















theorem valid8088 : plan8088.Valid := valid_step _ _ _ valid6117 (by decide +kernel)

theorem valid8089 : plan8089.Valid := valid_step _ _ _ valid6118 (by decide +kernel)

theorem valid8090 : plan8090.Valid := valid_step _ _ _ valid6119 (by decide +kernel)



















































theorem valid8116 : plan8116.Valid := valid_step _ _ _ valid6134 (by decide +kernel)

theorem valid8117 : plan8117.Valid := valid_step _ _ _ valid6135 (by decide +kernel)

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

























































































































































theorem valid8429 : plan8429.Valid := valid_step _ _ _ valid8077 (by decide +kernel)






































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



























theorem valid8462 : plan8462.Valid := valid_step _ _ _ valid8088 (by decide +kernel)

theorem valid8463 : plan8463.Valid := valid_step _ _ _ valid8089 (by decide +kernel)

theorem valid8464 : plan8464.Valid := valid_step _ _ _ valid8090 (by decide +kernel)























































































































































theorem valid8540 : plan8540.Valid := valid_step _ _ _ valid8116 (by decide +kernel)

theorem valid8541 : plan8541.Valid := valid_step _ _ _ valid8117 (by decide +kernel)

theorem valid8542 : plan8542.Valid := valid_step _ _ _ valid8118 (by decide +kernel)

theorem valid8543 : plan8543.Valid := valid_step _ _ _ valid8119 (by decide +kernel)

theorem valid8544 : plan8544.Valid := valid_step _ _ _ valid8120 (by decide +kernel)
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

theorem valid8545 : plan8545.Valid := valid_step _ _ _ valid8121 (by decide +kernel)






























































































































































































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













































































































theorem valid8695 : plan8695.Valid := valid_step _ _ _ valid8168 (by decide +kernel)

theorem valid8696 : plan8696.Valid := valid_step _ _ _ valid8169 (by decide +kernel)
















































































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
theorem t7_633choices : plan8429.choices=[9,3,3,3,3,3,7].map (options 7 2) := by rfl


theorem t7_633part0 : t7_633jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_633frontier : t7_633root.frontier 0=t7_633jobs := by rfl
theorem t7_633all : t7_633jobs.all (Job.check tree)=true := by
  simp only [t7_633jobs,List.all_append,List.all_nil,t7_633part0,Bool.and_self]
theorem t7_633checked : Checked tree [9,3,3,3,3,3,7] := by
  refine ⟨plan8429,valid8429,t7_633choices,?_⟩
  exact check_of_frontier tree 0 t7_633root t7_633jobs t7_633frontier t7_633all
theorem t7_634choices : plan8462.choices=[9,3,3,3,3,6,7].map (options 7 3) := by rfl


theorem t7_634part0 : t7_634jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_634frontier : t7_634root.frontier 0=t7_634jobs := by rfl
theorem t7_634all : t7_634jobs.all (Job.check tree)=true := by
  simp only [t7_634jobs,List.all_append,List.all_nil,t7_634part0,Bool.and_self]
theorem t7_634checked : Checked tree [9,3,3,3,3,6,7] := by
  refine ⟨plan8462,valid8462,t7_634choices,?_⟩
  exact check_of_frontier tree 0 t7_634root t7_634jobs t7_634frontier t7_634all
theorem t7_635choices : plan8463.choices=[9,3,3,3,3,7,7].map (options 7 3) := by rfl


theorem t7_635part0 : t7_635jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_635part1 : t7_635jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_635frontier : t7_635root.frontier 1=t7_635jobs := by rfl
theorem t7_635all : t7_635jobs.all (Job.check tree)=true := by
  simp only [t7_635jobs,List.all_append,List.all_nil,t7_635part0,t7_635part1,Bool.and_self]
theorem t7_635checked : Checked tree [9,3,3,3,3,7,7] := by
  refine ⟨plan8463,valid8463,t7_635choices,?_⟩
  exact check_of_frontier tree 1 t7_635root t7_635jobs t7_635frontier t7_635all
theorem t7_636choices : plan8464.choices=[9,3,3,3,3,10,7].map (options 7 3) := by rfl


theorem t7_636part0 : t7_636jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_636frontier : t7_636root.frontier 0=t7_636jobs := by rfl
theorem t7_636all : t7_636jobs.all (Job.check tree)=true := by
  simp only [t7_636jobs,List.all_append,List.all_nil,t7_636part0,Bool.and_self]
theorem t7_636checked : Checked tree [9,3,3,3,3,10,7] := by
  refine ⟨plan8464,valid8464,t7_636choices,?_⟩
  exact check_of_frontier tree 0 t7_636root t7_636jobs t7_636frontier t7_636all
theorem t7_637choices : plan8540.choices=[9,3,3,3,6,6,7].map (options 7 4) := by rfl


theorem t7_637part0 : t7_637jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_637frontier : t7_637root.frontier 0=t7_637jobs := by rfl
theorem t7_637all : t7_637jobs.all (Job.check tree)=true := by
  simp only [t7_637jobs,List.all_append,List.all_nil,t7_637part0,Bool.and_self]
theorem t7_637checked : Checked tree [9,3,3,3,6,6,7] := by
  refine ⟨plan8540,valid8540,t7_637choices,?_⟩
  exact check_of_frontier tree 0 t7_637root t7_637jobs t7_637frontier t7_637all
theorem t7_638choices : plan8541.choices=[9,3,3,3,6,7,7].map (options 7 4) := by rfl


theorem t7_638part0 : t7_638jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_638part1 : t7_638jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_638part2 : t7_638jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_638frontier : t7_638root.frontier 1=t7_638jobs := by rfl
theorem t7_638all : t7_638jobs.all (Job.check tree)=true := by
  simp only [t7_638jobs,List.all_append,List.all_nil,t7_638part0,t7_638part1,t7_638part2,Bool.and_self]
theorem t7_638checked : Checked tree [9,3,3,3,6,7,7] := by
  refine ⟨plan8541,valid8541,t7_638choices,?_⟩
  exact check_of_frontier tree 1 t7_638root t7_638jobs t7_638frontier t7_638all
theorem t7_639choices : plan8542.choices=[9,3,3,3,6,10,7].map (options 7 4) := by rfl


theorem t7_639part0 : t7_639jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_639part1 : t7_639jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_639frontier : t7_639root.frontier 1=t7_639jobs := by rfl
theorem t7_639all : t7_639jobs.all (Job.check tree)=true := by
  simp only [t7_639jobs,List.all_append,List.all_nil,t7_639part0,t7_639part1,Bool.and_self]
theorem t7_639checked : Checked tree [9,3,3,3,6,10,7] := by
  refine ⟨plan8542,valid8542,t7_639choices,?_⟩
  exact check_of_frontier tree 1 t7_639root t7_639jobs t7_639frontier t7_639all
theorem t7_640choices : plan8543.choices=[9,3,3,3,7,7,7].map (options 7 4) := by rfl


theorem t7_640part0 : t7_640jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_640part1 : t7_640jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_640part2 : t7_640jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_640part3 : t7_640jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_640frontier : t7_640root.frontier 1=t7_640jobs := by rfl
theorem t7_640all : t7_640jobs.all (Job.check tree)=true := by
  simp only [t7_640jobs,List.all_append,List.all_nil,t7_640part0,t7_640part1,t7_640part2,t7_640part3,Bool.and_self]
theorem t7_640checked : Checked tree [9,3,3,3,7,7,7] := by
  refine ⟨plan8543,valid8543,t7_640choices,?_⟩
  exact check_of_frontier tree 1 t7_640root t7_640jobs t7_640frontier t7_640all
theorem t7_641choices : plan8544.choices=[9,3,3,3,10,7,7].map (options 7 4) := by rfl


theorem t7_641part0 : t7_641jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_641part1 : t7_641jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_641part2 : t7_641jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_641frontier : t7_641root.frontier 1=t7_641jobs := by rfl
theorem t7_641all : t7_641jobs.all (Job.check tree)=true := by
  simp only [t7_641jobs,List.all_append,List.all_nil,t7_641part0,t7_641part1,t7_641part2,Bool.and_self]
theorem t7_641checked : Checked tree [9,3,3,3,10,7,7] := by
  refine ⟨plan8544,valid8544,t7_641choices,?_⟩
  exact check_of_frontier tree 1 t7_641root t7_641jobs t7_641frontier t7_641all
theorem t7_642choices : plan8545.choices=[9,3,3,3,10,10,7].map (options 7 4) := by rfl


theorem t7_642part0 : t7_642jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_642frontier : t7_642root.frontier 0=t7_642jobs := by rfl
theorem t7_642all : t7_642jobs.all (Job.check tree)=true := by
  simp only [t7_642jobs,List.all_append,List.all_nil,t7_642part0,Bool.and_self]
theorem t7_642checked : Checked tree [9,3,3,3,10,10,7] := by
  refine ⟨plan8545,valid8545,t7_642choices,?_⟩
  exact check_of_frontier tree 0 t7_642root t7_642jobs t7_642frontier t7_642all
theorem t7_643choices : plan8695.choices=[9,3,3,6,6,6,7].map (options 7 5) := by rfl


theorem t7_643part0 : t7_643jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_643frontier : t7_643root.frontier 0=t7_643jobs := by rfl
theorem t7_643all : t7_643jobs.all (Job.check tree)=true := by
  simp only [t7_643jobs,List.all_append,List.all_nil,t7_643part0,Bool.and_self]
theorem t7_643checked : Checked tree [9,3,3,6,6,6,7] := by
  refine ⟨plan8695,valid8695,t7_643choices,?_⟩
  exact check_of_frontier tree 0 t7_643root t7_643jobs t7_643frontier t7_643all
theorem t7_644choices : plan8696.choices=[9,3,3,6,6,7,7].map (options 7 5) := by rfl


theorem t7_644part0 : t7_644jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_644part1 : t7_644jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_644part2 : t7_644jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_644frontier : t7_644root.frontier 1=t7_644jobs := by rfl
theorem t7_644all : t7_644jobs.all (Job.check tree)=true := by
  simp only [t7_644jobs,List.all_append,List.all_nil,t7_644part0,t7_644part1,t7_644part2,Bool.and_self]
theorem t7_644checked : Checked tree [9,3,3,6,6,7,7] := by
  refine ⟨plan8696,valid8696,t7_644choices,?_⟩
  exact check_of_frontier tree 1 t7_644root t7_644jobs t7_644frontier t7_644all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks190 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_642checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_643checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_644checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_634checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_635checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_636checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_637checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_638checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_639checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_640checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_641checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_633checked⟩
