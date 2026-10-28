-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks095
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:34:32.217683+00:00
-- url     : https://prove2.me/submissions/38b04332-82b9-4e75-8e5d-9e4952a6a57c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks095
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks095
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans076
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

theorem valid578 : plan578.Valid := valid_step _ _ _ valid134 (by decide +kernel)




























































































































































































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

theorem valid1596 : plan1596.Valid := valid_step _ _ _ valid578 (by decide +kernel)








































































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













theorem valid3367 : plan3367.Valid := valid_step _ _ _ valid1580 (by decide +kernel)

theorem valid3368 : plan3368.Valid := valid_step _ _ _ valid1581 (by decide +kernel)

theorem valid3369 : plan3369.Valid := valid_step _ _ _ valid1582 (by decide +kernel)














































































































































































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

theorem valid3478 : plan3478.Valid := valid_step _ _ _ valid1596 (by decide +kernel)




















































































































































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





























































































































theorem valid5727 : plan5727.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5728 : plan5728.Valid := valid_step _ _ _ valid3368 (by decide +kernel)

theorem valid5729 : plan5729.Valid := valid_step _ _ _ valid3369 (by decide +kernel)






























































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

































































































































































theorem valid5937 : plan5937.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5938 : plan5938.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5939 : plan5939.Valid := valid_step _ _ _ valid3477 (by decide +kernel)

theorem valid5940 : plan5940.Valid := valid_step _ _ _ valid3478 (by decide +kernel)
























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







































































































































































theorem valid7380 : plan7380.Valid := valid_step _ _ _ valid5937 (by decide +kernel)

theorem valid7381 : plan7381.Valid := valid_step _ _ _ valid5938 (by decide +kernel)

theorem valid7382 : plan7382.Valid := valid_step _ _ _ valid5939 (by decide +kernel)

theorem valid7383 : plan7383.Valid := valid_step _ _ _ valid5940 (by decide +kernel)


















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

































































































theorem valid6961 : plan6961.Valid := valid_step _ _ _ valid5727 (by decide +kernel)

theorem valid6962 : plan6962.Valid := valid_step _ _ _ valid5728 (by decide +kernel)

theorem valid6963 : plan6963.Valid := valid_step _ _ _ valid5729 (by decide +kernel)


























































































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
theorem t6_786choices : plan6961.choices=[2,9,3,10,7,7].map (options 6 4) := by rfl


theorem t6_786part0 : t6_786jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_786part1 : t6_786jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_786part2 : t6_786jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_786part3 : t6_786jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_786part4 : t6_786jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_786part5 : t6_786jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_786part6 : t6_786jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_786part7 : t6_786jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_786part8 : t6_786jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_786part9 : t6_786jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_786part10 : t6_786jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_786frontier : t6_786root.frontier 2=t6_786jobs := by rfl
theorem t6_786all : t6_786jobs.all (Job.check tree)=true := by
  simp only [t6_786jobs,List.all_append,List.all_nil,t6_786part0,t6_786part1,t6_786part2,t6_786part3,t6_786part4,t6_786part5,t6_786part6,t6_786part7,t6_786part8,t6_786part9,t6_786part10,Bool.and_self]
theorem t6_786checked : Checked tree [2,9,3,10,7,7] := by
  refine ⟨plan6961,valid6961,t6_786choices,?_⟩
  exact check_of_frontier tree 2 t6_786root t6_786jobs t6_786frontier t6_786all
theorem t6_787choices : plan6962.choices=[2,9,3,10,10,7].map (options 6 4) := by rfl


theorem t6_787part0 : t6_787jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_787part1 : t6_787jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_787part2 : t6_787jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_787part3 : t6_787jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_787part4 : t6_787jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_787part5 : t6_787jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_787frontier : t6_787root.frontier 2=t6_787jobs := by rfl
theorem t6_787all : t6_787jobs.all (Job.check tree)=true := by
  simp only [t6_787jobs,List.all_append,List.all_nil,t6_787part0,t6_787part1,t6_787part2,t6_787part3,t6_787part4,t6_787part5,Bool.and_self]
theorem t6_787checked : Checked tree [2,9,3,10,10,7] := by
  refine ⟨plan6962,valid6962,t6_787choices,?_⟩
  exact check_of_frontier tree 2 t6_787root t6_787jobs t6_787frontier t6_787all
theorem t6_788choices : plan6963.choices=[2,9,3,10,10,10].map (options 6 4) := by rfl


theorem t6_788part0 : t6_788jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_788frontier : t6_788root.frontier 0=t6_788jobs := by rfl
theorem t6_788all : t6_788jobs.all (Job.check tree)=true := by
  simp only [t6_788jobs,List.all_append,List.all_nil,t6_788part0,Bool.and_self]
theorem t6_788checked : Checked tree [2,9,3,10,10,10] := by
  refine ⟨plan6963,valid6963,t6_788choices,?_⟩
  exact check_of_frontier tree 0 t6_788root t6_788jobs t6_788frontier t6_788all
theorem t6_789choices : plan7380.choices=[2,9,6,6,6,6].map (options 6 5) := by rfl


theorem t6_789part0 : t6_789jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_789frontier : t6_789root.frontier 0=t6_789jobs := by rfl
theorem t6_789all : t6_789jobs.all (Job.check tree)=true := by
  simp only [t6_789jobs,List.all_append,List.all_nil,t6_789part0,Bool.and_self]
theorem t6_789checked : Checked tree [2,9,6,6,6,6] := by
  refine ⟨plan7380,valid7380,t6_789choices,?_⟩
  exact check_of_frontier tree 0 t6_789root t6_789jobs t6_789frontier t6_789all
theorem t6_790choices : plan7381.choices=[2,9,6,6,6,7].map (options 6 5) := by rfl


theorem t6_790part0 : t6_790jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_790frontier : t6_790root.frontier 0=t6_790jobs := by rfl
theorem t6_790all : t6_790jobs.all (Job.check tree)=true := by
  simp only [t6_790jobs,List.all_append,List.all_nil,t6_790part0,Bool.and_self]
theorem t6_790checked : Checked tree [2,9,6,6,6,7] := by
  refine ⟨plan7381,valid7381,t6_790choices,?_⟩
  exact check_of_frontier tree 0 t6_790root t6_790jobs t6_790frontier t6_790all
theorem t6_791choices : plan7382.choices=[2,9,6,6,6,10].map (options 6 5) := by rfl


theorem t6_791part0 : t6_791jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_791frontier : t6_791root.frontier 0=t6_791jobs := by rfl
theorem t6_791all : t6_791jobs.all (Job.check tree)=true := by
  simp only [t6_791jobs,List.all_append,List.all_nil,t6_791part0,Bool.and_self]
theorem t6_791checked : Checked tree [2,9,6,6,6,10] := by
  refine ⟨plan7382,valid7382,t6_791choices,?_⟩
  exact check_of_frontier tree 0 t6_791root t6_791jobs t6_791frontier t6_791all
theorem t6_792choices : plan7383.choices=[2,9,6,6,7,7].map (options 6 5) := by rfl


theorem t6_792part0 : t6_792jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_792part1 : t6_792jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_792frontier : t6_792root.frontier 2=t6_792jobs := by rfl
theorem t6_792all : t6_792jobs.all (Job.check tree)=true := by
  simp only [t6_792jobs,List.all_append,List.all_nil,t6_792part0,t6_792part1,Bool.and_self]
theorem t6_792checked : Checked tree [2,9,6,6,7,7] := by
  refine ⟨plan7383,valid7383,t6_792choices,?_⟩
  exact check_of_frontier tree 2 t6_792root t6_792jobs t6_792frontier t6_792all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks095 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_790checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_791checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_792checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_786checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_787checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_788checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_789checked⟩
