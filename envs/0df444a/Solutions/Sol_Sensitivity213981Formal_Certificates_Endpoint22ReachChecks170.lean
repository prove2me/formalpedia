-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks170
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:06:46.273989+00:00
-- url     : https://prove2.me/submissions/5e45cbb0-e394-4fc7-bd51-1a87e2ce5bf8

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks170
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks170
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
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





































































































theorem valid147 : plan147.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid148 : plan148.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid149 : plan149.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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

















































theorem valid601 : plan601.Valid := valid_step _ _ _ valid147 (by decide +kernel)

theorem valid602 : plan602.Valid := valid_step _ _ _ valid147 (by decide +kernel)

theorem valid603 : plan603.Valid := valid_step _ _ _ valid148 (by decide +kernel)

theorem valid604 : plan604.Valid := valid_step _ _ _ valid149 (by decide +kernel)

theorem valid605 : plan605.Valid := valid_step _ _ _ valid150 (by decide +kernel)

theorem valid606 : plan606.Valid := valid_step _ _ _ valid151 (by decide +kernel)




































































































































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





















theorem valid1643 : plan1643.Valid := valid_step _ _ _ valid601 (by decide +kernel)

theorem valid1644 : plan1644.Valid := valid_step _ _ _ valid601 (by decide +kernel)

theorem valid1645 : plan1645.Valid := valid_step _ _ _ valid602 (by decide +kernel)

theorem valid1646 : plan1646.Valid := valid_step _ _ _ valid603 (by decide +kernel)



theorem valid1648 : plan1648.Valid := valid_step _ _ _ valid604 (by decide +kernel)

theorem valid1649 : plan1649.Valid := valid_step _ _ _ valid605 (by decide +kernel)

theorem valid1650 : plan1650.Valid := valid_step _ _ _ valid606 (by decide +kernel)




























































































































































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

















































theorem valid3577 : plan3577.Valid := valid_step _ _ _ valid1643 (by decide +kernel)

theorem valid3578 : plan3578.Valid := valid_step _ _ _ valid1644 (by decide +kernel)

theorem valid3579 : plan3579.Valid := valid_step _ _ _ valid1645 (by decide +kernel)

theorem valid3580 : plan3580.Valid := valid_step _ _ _ valid1646 (by decide +kernel)















theorem valid3588 : plan3588.Valid := valid_step _ _ _ valid1648 (by decide +kernel)

theorem valid3589 : plan3589.Valid := valid_step _ _ _ valid1649 (by decide +kernel)

theorem valid3590 : plan3590.Valid := valid_step _ _ _ valid1650 (by decide +kernel)




















































































































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



























































































































































theorem valid6126 : plan6126.Valid := valid_step _ _ _ valid3577 (by decide +kernel)

theorem valid6127 : plan6127.Valid := valid_step _ _ _ valid3578 (by decide +kernel)

theorem valid6128 : plan6128.Valid := valid_step _ _ _ valid3579 (by decide +kernel)

theorem valid6129 : plan6129.Valid := valid_step _ _ _ valid3580 (by decide +kernel)





















theorem valid6140 : plan6140.Valid := valid_step _ _ _ valid3588 (by decide +kernel)

theorem valid6141 : plan6141.Valid := valid_step _ _ _ valid3589 (by decide +kernel)

theorem valid6142 : plan6142.Valid := valid_step _ _ _ valid3590 (by decide +kernel)




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

































































theorem valid8097 : plan8097.Valid := valid_step _ _ _ valid6126 (by decide +kernel)

theorem valid8098 : plan8098.Valid := valid_step _ _ _ valid6127 (by decide +kernel)

theorem valid8099 : plan8099.Valid := valid_step _ _ _ valid6128 (by decide +kernel)

theorem valid8100 : plan8100.Valid := valid_step _ _ _ valid6129 (by decide +kernel)











































theorem valid8122 : plan8122.Valid := valid_step _ _ _ valid6140 (by decide +kernel)

theorem valid8123 : plan8123.Valid := valid_step _ _ _ valid6141 (by decide +kernel)

theorem valid8124 : plan8124.Valid := valid_step _ _ _ valid6142 (by decide +kernel)








































































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









theorem valid8453 : plan8453.Valid := valid_step _ _ _ valid8097 (by decide +kernel)

theorem valid8454 : plan8454.Valid := valid_step _ _ _ valid8098 (by decide +kernel)

theorem valid8455 : plan8455.Valid := valid_step _ _ _ valid8099 (by decide +kernel)

theorem valid8456 : plan8456.Valid := valid_step _ _ _ valid8100 (by decide +kernel)









































































































theorem valid8509 : plan8509.Valid := valid_step _ _ _ valid8122 (by decide +kernel)

theorem valid8510 : plan8510.Valid := valid_step _ _ _ valid8123 (by decide +kernel)

theorem valid8511 : plan8511.Valid := valid_step _ _ _ valid8124 (by decide +kernel)


































































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
theorem t7_274choices : plan8453.choices=[3,3,3,3,7,7,7].map (options 7 3) := by rfl


theorem t7_274part0 : t7_274jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_274part1 : t7_274jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_274part2 : t7_274jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_274part3 : t7_274jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_274part4 : t7_274jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_274frontier : t7_274root.frontier 1=t7_274jobs := by rfl
theorem t7_274all : t7_274jobs.all (Job.check tree)=true := by
  simp only [t7_274jobs,List.all_append,List.all_nil,t7_274part0,t7_274part1,t7_274part2,t7_274part3,t7_274part4,Bool.and_self]
theorem t7_274checked : Checked tree [3,3,3,3,7,7,7] := by
  refine ⟨plan8453,valid8453,t7_274choices,?_⟩
  exact check_of_frontier tree 1 t7_274root t7_274jobs t7_274frontier t7_274all
theorem t7_275choices : plan8454.choices=[3,3,3,3,10,7,7].map (options 7 3) := by rfl


theorem t7_275part0 : t7_275jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_275part1 : t7_275jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_275part2 : t7_275jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_275part3 : t7_275jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_275part4 : t7_275jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_275part5 : t7_275jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_275frontier : t7_275root.frontier 1=t7_275jobs := by rfl
theorem t7_275all : t7_275jobs.all (Job.check tree)=true := by
  simp only [t7_275jobs,List.all_append,List.all_nil,t7_275part0,t7_275part1,t7_275part2,t7_275part3,t7_275part4,t7_275part5,Bool.and_self]
theorem t7_275checked : Checked tree [3,3,3,3,10,7,7] := by
  refine ⟨plan8454,valid8454,t7_275choices,?_⟩
  exact check_of_frontier tree 1 t7_275root t7_275jobs t7_275frontier t7_275all
theorem t7_276choices : plan8455.choices=[3,3,3,3,10,10,7].map (options 7 3) := by rfl


theorem t7_276part0 : t7_276jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_276part1 : t7_276jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_276frontier : t7_276root.frontier 1=t7_276jobs := by rfl
theorem t7_276all : t7_276jobs.all (Job.check tree)=true := by
  simp only [t7_276jobs,List.all_append,List.all_nil,t7_276part0,t7_276part1,Bool.and_self]
theorem t7_276checked : Checked tree [3,3,3,3,10,10,7] := by
  refine ⟨plan8455,valid8455,t7_276choices,?_⟩
  exact check_of_frontier tree 1 t7_276root t7_276jobs t7_276frontier t7_276all
theorem t7_277choices : plan8456.choices=[3,3,3,3,10,10,10].map (options 7 3) := by rfl


theorem t7_277part0 : t7_277jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_277frontier : t7_277root.frontier 0=t7_277jobs := by rfl
theorem t7_277all : t7_277jobs.all (Job.check tree)=true := by
  simp only [t7_277jobs,List.all_append,List.all_nil,t7_277part0,Bool.and_self]
theorem t7_277checked : Checked tree [3,3,3,3,10,10,10] := by
  refine ⟨plan8456,valid8456,t7_277choices,?_⟩
  exact check_of_frontier tree 0 t7_277root t7_277jobs t7_277frontier t7_277all
theorem t7_278choices : plan8509.choices=[3,3,3,6,6,6,6].map (options 7 4) := by rfl


theorem t7_278part0 : t7_278jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_278frontier : t7_278root.frontier 0=t7_278jobs := by rfl
theorem t7_278all : t7_278jobs.all (Job.check tree)=true := by
  simp only [t7_278jobs,List.all_append,List.all_nil,t7_278part0,Bool.and_self]
theorem t7_278checked : Checked tree [3,3,3,6,6,6,6] := by
  refine ⟨plan8509,valid8509,t7_278choices,?_⟩
  exact check_of_frontier tree 0 t7_278root t7_278jobs t7_278frontier t7_278all
theorem t7_279choices : plan8510.choices=[3,3,3,6,6,6,7].map (options 7 4) := by rfl


theorem t7_279part0 : t7_279jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_279part1 : t7_279jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_279frontier : t7_279root.frontier 1=t7_279jobs := by rfl
theorem t7_279all : t7_279jobs.all (Job.check tree)=true := by
  simp only [t7_279jobs,List.all_append,List.all_nil,t7_279part0,t7_279part1,Bool.and_self]
theorem t7_279checked : Checked tree [3,3,3,6,6,6,7] := by
  refine ⟨plan8510,valid8510,t7_279choices,?_⟩
  exact check_of_frontier tree 1 t7_279root t7_279jobs t7_279frontier t7_279all
theorem t7_280choices : plan8511.choices=[3,3,3,6,6,6,10].map (options 7 4) := by rfl


theorem t7_280part0 : t7_280jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_280frontier : t7_280root.frontier 0=t7_280jobs := by rfl
theorem t7_280all : t7_280jobs.all (Job.check tree)=true := by
  simp only [t7_280jobs,List.all_append,List.all_nil,t7_280part0,Bool.and_self]
theorem t7_280checked : Checked tree [3,3,3,6,6,6,10] := by
  refine ⟨plan8511,valid8511,t7_280choices,?_⟩
  exact check_of_frontier tree 0 t7_280root t7_280jobs t7_280frontier t7_280all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks170 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_274checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_275checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_276checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_277checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_278checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_279checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_280checked⟩
