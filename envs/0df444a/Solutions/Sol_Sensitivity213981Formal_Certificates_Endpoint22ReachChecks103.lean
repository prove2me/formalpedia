-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks103
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:38:54.336993+00:00
-- url     : https://prove2.me/submissions/60f0992c-3c56-44a2-9331-69111618b40d

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks103
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks103
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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

theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)
























































































































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







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)












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



































theorem valid1554 : plan1554.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1555 : plan1555.Valid := valid_step _ _ _ valid564 (by decide +kernel)



























theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)


























































































































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















































































































theorem valid3320 : plan3320.Valid := valid_step _ _ _ valid1554 (by decide +kernel)

theorem valid3321 : plan3321.Valid := valid_step _ _ _ valid1555 (by decide +kernel)














































































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











































































theorem valid3398 : plan3398.Valid := valid_step _ _ _ valid1569 (by decide +kernel)

theorem valid3399 : plan3399.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3400 : plan3400.Valid := valid_step _ _ _ valid1571 (by decide +kernel)
















































































































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











































theorem valid5494 : plan5494.Valid := valid_step _ _ _ valid3320 (by decide +kernel)

theorem valid5495 : plan5495.Valid := valid_step _ _ _ valid3321 (by decide +kernel)


















































































































































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































































































































theorem valid5632 : plan5632.Valid := valid_step _ _ _ valid3398 (by decide +kernel)

theorem valid5633 : plan5633.Valid := valid_step _ _ _ valid3399 (by decide +kernel)

theorem valid5634 : plan5634.Valid := valid_step _ _ _ valid3400 (by decide +kernel)




























































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















































































































































































theorem valid6616 : plan6616.Valid := valid_step _ _ _ valid5494 (by decide +kernel)

theorem valid6617 : plan6617.Valid := valid_step _ _ _ valid5495 (by decide +kernel)














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





















































































































theorem valid6971 : plan6971.Valid := valid_step _ _ _ valid5632 (by decide +kernel)

theorem valid6972 : plan6972.Valid := valid_step _ _ _ valid5633 (by decide +kernel)

theorem valid6973 : plan6973.Valid := valid_step _ _ _ valid5634 (by decide +kernel)






































































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
theorem t6_851choices : plan6616.choices=[3,3,3,10,10,7].map (options 6 3) := by rfl


theorem t6_851part0 : t6_851jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_851part1 : t6_851jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_851part2 : t6_851jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_851part3 : t6_851jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_851part4 : t6_851jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_851part5 : t6_851jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_851frontier : t6_851root.frontier 2=t6_851jobs := by rfl
theorem t6_851all : t6_851jobs.all (Job.check tree)=true := by
  simp only [t6_851jobs,List.all_append,List.all_nil,t6_851part0,t6_851part1,t6_851part2,t6_851part3,t6_851part4,t6_851part5,Bool.and_self]
theorem t6_851checked : Checked tree [3,3,3,10,10,7] := by
  refine ⟨plan6616,valid6616,t6_851choices,?_⟩
  exact check_of_frontier tree 2 t6_851root t6_851jobs t6_851frontier t6_851all
theorem t6_852choices : plan6617.choices=[3,3,3,10,10,10].map (options 6 3) := by rfl


theorem t6_852part0 : t6_852jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_852part1 : t6_852jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_852frontier : t6_852root.frontier 1=t6_852jobs := by rfl
theorem t6_852all : t6_852jobs.all (Job.check tree)=true := by
  simp only [t6_852jobs,List.all_append,List.all_nil,t6_852part0,t6_852part1,Bool.and_self]
theorem t6_852checked : Checked tree [3,3,3,10,10,10] := by
  refine ⟨plan6617,valid6617,t6_852choices,?_⟩
  exact check_of_frontier tree 1 t6_852root t6_852jobs t6_852frontier t6_852all
theorem t6_853choices : plan6971.choices=[3,3,6,6,6,6].map (options 6 4) := by rfl


theorem t6_853part0 : t6_853jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_853frontier : t6_853root.frontier 0=t6_853jobs := by rfl
theorem t6_853all : t6_853jobs.all (Job.check tree)=true := by
  simp only [t6_853jobs,List.all_append,List.all_nil,t6_853part0,Bool.and_self]
theorem t6_853checked : Checked tree [3,3,6,6,6,6] := by
  refine ⟨plan6971,valid6971,t6_853choices,?_⟩
  exact check_of_frontier tree 0 t6_853root t6_853jobs t6_853frontier t6_853all
theorem t6_854choices : plan6972.choices=[3,3,6,6,6,7].map (options 6 4) := by rfl


theorem t6_854part0 : t6_854jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_854part1 : t6_854jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_854part2 : t6_854jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_854part3 : t6_854jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_854part4 : t6_854jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_854frontier : t6_854root.frontier 2=t6_854jobs := by rfl
theorem t6_854all : t6_854jobs.all (Job.check tree)=true := by
  simp only [t6_854jobs,List.all_append,List.all_nil,t6_854part0,t6_854part1,t6_854part2,t6_854part3,t6_854part4,Bool.and_self]
theorem t6_854checked : Checked tree [3,3,6,6,6,7] := by
  refine ⟨plan6972,valid6972,t6_854choices,?_⟩
  exact check_of_frontier tree 2 t6_854root t6_854jobs t6_854frontier t6_854all
theorem t6_855choices : plan6973.choices=[3,3,6,6,6,10].map (options 6 4) := by rfl


theorem t6_855part0 : t6_855jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_855part1 : t6_855jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_855part2 : t6_855jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_855part3 : t6_855jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_855frontier : t6_855root.frontier 1=t6_855jobs := by rfl
theorem t6_855all : t6_855jobs.all (Job.check tree)=true := by
  simp only [t6_855jobs,List.all_append,List.all_nil,t6_855part0,t6_855part1,t6_855part2,t6_855part3,Bool.and_self]
theorem t6_855checked : Checked tree [3,3,6,6,6,10] := by
  refine ⟨plan6973,valid6973,t6_855choices,?_⟩
  exact check_of_frontier tree 1 t6_855root t6_855jobs t6_855frontier t6_855all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks103 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_854checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_855checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_851checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_852checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_853checked⟩
