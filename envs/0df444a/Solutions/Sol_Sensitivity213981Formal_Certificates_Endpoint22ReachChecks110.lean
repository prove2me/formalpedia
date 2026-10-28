-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks110
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:40:28.883027+00:00
-- url     : https://prove2.me/submissions/a86a7f59-ebff-4bd1-8889-4b6a9ccc0734

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks110
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks110
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans077
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





































































theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid133 : plan133.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid134 : plan134.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid135 : plan135.Valid := valid_step _ _ _ valid0 (by decide +kernel)


















































































































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

theorem valid577 : plan577.Valid := valid_step _ _ _ valid135 (by decide +kernel)






























































































































































































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





















































































































































































theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid573 : plan573.Valid := valid_step _ _ _ valid132 (by decide +kernel)



theorem valid575 : plan575.Valid := valid_step _ _ _ valid133 (by decide +kernel)

theorem valid576 : plan576.Valid := valid_step _ _ _ valid134 (by decide +kernel)
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























































































theorem valid1580 : plan1580.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1581 : plan1581.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1582 : plan1582.Valid := valid_step _ _ _ valid573 (by decide +kernel)





















theorem valid1593 : plan1593.Valid := valid_step _ _ _ valid575 (by decide +kernel)

theorem valid1594 : plan1594.Valid := valid_step _ _ _ valid576 (by decide +kernel)

theorem valid1595 : plan1595.Valid := valid_step _ _ _ valid577 (by decide +kernel)










































































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



















































































































































theorem valid3434 : plan3434.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3435 : plan3435.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3436 : plan3436.Valid := valid_step _ _ _ valid1582 (by decide +kernel)








































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























































































































































theorem valid5644 : plan5644.Valid := valid_step _ _ _ valid3434 (by decide +kernel)

theorem valid5645 : plan5645.Valid := valid_step _ _ _ valid3435 (by decide +kernel)

theorem valid5646 : plan5646.Valid := valid_step _ _ _ valid3436 (by decide +kernel)




































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





































theorem valid3475 : plan3475.Valid := valid_step _ _ _ valid1593 (by decide +kernel)

theorem valid3476 : plan3476.Valid := valid_step _ _ _ valid1594 (by decide +kernel)

theorem valid3477 : plan3477.Valid := valid_step _ _ _ valid1595 (by decide +kernel)






















































































































































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





















































theorem valid5883 : plan5883.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5884 : plan5884.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5885 : plan5885.Valid := valid_step _ _ _ valid3477 (by decide +kernel)






































































































































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













































































































































theorem valid6983 : plan6983.Valid := valid_step _ _ _ valid5644 (by decide +kernel)

theorem valid6984 : plan6984.Valid := valid_step _ _ _ valid5645 (by decide +kernel)

theorem valid6985 : plan6985.Valid := valid_step _ _ _ valid5646 (by decide +kernel)














































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









































theorem valid7413 : plan7413.Valid := valid_step _ _ _ valid5883 (by decide +kernel)

theorem valid7414 : plan7414.Valid := valid_step _ _ _ valid5884 (by decide +kernel)

theorem valid7415 : plan7415.Valid := valid_step _ _ _ valid5885 (by decide +kernel)


















































































































































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
theorem t6_865choices : plan6983.choices=[3,3,10,10,7,7].map (options 6 4) := by rfl


theorem t6_865part0 : t6_865jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_865part1 : t6_865jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_865part2 : t6_865jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_865part3 : t6_865jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_865part4 : t6_865jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_865part5 : t6_865jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_865part6 : t6_865jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_865part7 : t6_865jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_865part8 : t6_865jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_865frontier : t6_865root.frontier 3=t6_865jobs := by rfl
theorem t6_865all : t6_865jobs.all (Job.check tree)=true := by
  simp only [t6_865jobs,List.all_append,List.all_nil,t6_865part0,t6_865part1,t6_865part2,t6_865part3,t6_865part4,t6_865part5,t6_865part6,t6_865part7,t6_865part8,Bool.and_self]
theorem t6_865checked : Checked tree [3,3,10,10,7,7] := by
  refine ⟨plan6983,valid6983,t6_865choices,?_⟩
  exact check_of_frontier tree 3 t6_865root t6_865jobs t6_865frontier t6_865all
theorem t6_866choices : plan6984.choices=[3,3,10,10,10,7].map (options 6 4) := by rfl


theorem t6_866part0 : t6_866jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_866part1 : t6_866jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_866part2 : t6_866jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_866part3 : t6_866jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_866part4 : t6_866jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_866frontier : t6_866root.frontier 2=t6_866jobs := by rfl
theorem t6_866all : t6_866jobs.all (Job.check tree)=true := by
  simp only [t6_866jobs,List.all_append,List.all_nil,t6_866part0,t6_866part1,t6_866part2,t6_866part3,t6_866part4,Bool.and_self]
theorem t6_866checked : Checked tree [3,3,10,10,10,7] := by
  refine ⟨plan6984,valid6984,t6_866choices,?_⟩
  exact check_of_frontier tree 2 t6_866root t6_866jobs t6_866frontier t6_866all
theorem t6_867choices : plan6985.choices=[3,3,10,10,10,10].map (options 6 4) := by rfl


theorem t6_867part0 : t6_867jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_867frontier : t6_867root.frontier 0=t6_867jobs := by rfl
theorem t6_867all : t6_867jobs.all (Job.check tree)=true := by
  simp only [t6_867jobs,List.all_append,List.all_nil,t6_867part0,Bool.and_self]
theorem t6_867checked : Checked tree [3,3,10,10,10,10] := by
  refine ⟨plan6985,valid6985,t6_867choices,?_⟩
  exact check_of_frontier tree 0 t6_867root t6_867jobs t6_867frontier t6_867all
theorem t6_868choices : plan7413.choices=[3,6,6,6,6,6].map (options 6 5) := by rfl


theorem t6_868part0 : t6_868jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_868frontier : t6_868root.frontier 0=t6_868jobs := by rfl
theorem t6_868all : t6_868jobs.all (Job.check tree)=true := by
  simp only [t6_868jobs,List.all_append,List.all_nil,t6_868part0,Bool.and_self]
theorem t6_868checked : Checked tree [3,6,6,6,6,6] := by
  refine ⟨plan7413,valid7413,t6_868choices,?_⟩
  exact check_of_frontier tree 0 t6_868root t6_868jobs t6_868frontier t6_868all
theorem t6_869choices : plan7414.choices=[3,6,6,6,6,7].map (options 6 5) := by rfl


theorem t6_869part0 : t6_869jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_869part1 : t6_869jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_869frontier : t6_869root.frontier 1=t6_869jobs := by rfl
theorem t6_869all : t6_869jobs.all (Job.check tree)=true := by
  simp only [t6_869jobs,List.all_append,List.all_nil,t6_869part0,t6_869part1,Bool.and_self]
theorem t6_869checked : Checked tree [3,6,6,6,6,7] := by
  refine ⟨plan7414,valid7414,t6_869choices,?_⟩
  exact check_of_frontier tree 1 t6_869root t6_869jobs t6_869frontier t6_869all
theorem t6_870choices : plan7415.choices=[3,6,6,6,6,10].map (options 6 5) := by rfl


theorem t6_870part0 : t6_870jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_870frontier : t6_870root.frontier 0=t6_870jobs := by rfl
theorem t6_870all : t6_870jobs.all (Job.check tree)=true := by
  simp only [t6_870jobs,List.all_append,List.all_nil,t6_870part0,Bool.and_self]
theorem t6_870checked : Checked tree [3,6,6,6,6,10] := by
  refine ⟨plan7415,valid7415,t6_870choices,?_⟩
  exact check_of_frontier tree 0 t6_870root t6_870jobs t6_870frontier t6_870all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks110 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_865checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_866checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_867checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_868checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_869checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_870checked⟩
