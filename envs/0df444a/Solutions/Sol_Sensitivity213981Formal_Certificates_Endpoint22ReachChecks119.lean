-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks119
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:42:39.43299+00:00
-- url     : https://prove2.me/submissions/f78fee74-2073-4639-a68e-54b8d33aabb4

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks119
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks119
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans060
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans073
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







































































theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)

theorem valid1574 : plan1574.Valid := valid_step _ _ _ valid573 (by decide +kernel)

theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)









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





theorem valid3363 : plan3363.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3364 : plan3364.Valid := valid_step _ _ _ valid1573 (by decide +kernel)

theorem valid3365 : plan3365.Valid := valid_step _ _ _ valid1574 (by decide +kernel)

theorem valid3366 : plan3366.Valid := valid_step _ _ _ valid1575 (by decide +kernel)

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

















































































































theorem valid5625 : plan5625.Valid := valid_step _ _ _ valid3363 (by decide +kernel)

theorem valid5626 : plan5626.Valid := valid_step _ _ _ valid3364 (by decide +kernel)

theorem valid5627 : plan5627.Valid := valid_step _ _ _ valid3365 (by decide +kernel)

theorem valid5628 : plan5628.Valid := valid_step _ _ _ valid3366 (by decide +kernel)

theorem valid5629 : plan5629.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5630 : plan5630.Valid := valid_step _ _ _ valid3368 (by decide +kernel)

theorem valid5631 : plan5631.Valid := valid_step _ _ _ valid3369 (by decide +kernel)


































































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



















theorem valid5770 : plan5770.Valid := valid_step _ _ _ valid3475 (by decide +kernel)

theorem valid5771 : plan5771.Valid := valid_step _ _ _ valid3476 (by decide +kernel)

theorem valid5772 : plan5772.Valid := valid_step _ _ _ valid3477 (by decide +kernel)

theorem valid5773 : plan5773.Valid := valid_step _ _ _ valid3478 (by decide +kernel)






































































































































































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















































































































































theorem valid7464 : plan7464.Valid := valid_step _ _ _ valid5770 (by decide +kernel)

theorem valid7465 : plan7465.Valid := valid_step _ _ _ valid5771 (by decide +kernel)

theorem valid7466 : plan7466.Valid := valid_step _ _ _ valid5772 (by decide +kernel)

theorem valid7467 : plan7467.Valid := valid_step _ _ _ valid5773 (by decide +kernel)










































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









theorem valid7013 : plan7013.Valid := valid_step _ _ _ valid5625 (by decide +kernel)

theorem valid7014 : plan7014.Valid := valid_step _ _ _ valid5626 (by decide +kernel)

theorem valid7015 : plan7015.Valid := valid_step _ _ _ valid5627 (by decide +kernel)

theorem valid7016 : plan7016.Valid := valid_step _ _ _ valid5628 (by decide +kernel)

theorem valid7017 : plan7017.Valid := valid_step _ _ _ valid5629 (by decide +kernel)

theorem valid7018 : plan7018.Valid := valid_step _ _ _ valid5630 (by decide +kernel)

theorem valid7019 : plan7019.Valid := valid_step _ _ _ valid5631 (by decide +kernel)










































































































































































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
theorem t6_973choices : plan7013.choices=[4,3,3,6,7,7].map (options 6 4) := by rfl


theorem t6_973part0 : t6_973jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_973part1 : t6_973jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_973part2 : t6_973jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_973frontier : t6_973root.frontier 2=t6_973jobs := by rfl
theorem t6_973all : t6_973jobs.all (Job.check tree)=true := by
  simp only [t6_973jobs,List.all_append,List.all_nil,t6_973part0,t6_973part1,t6_973part2,Bool.and_self]
theorem t6_973checked : Checked tree [4,3,3,6,7,7] := by
  refine ⟨plan7013,valid7013,t6_973choices,?_⟩
  exact check_of_frontier tree 2 t6_973root t6_973jobs t6_973frontier t6_973all
theorem t6_974choices : plan7014.choices=[4,3,3,6,10,7].map (options 6 4) := by rfl


theorem t6_974part0 : t6_974jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_974part1 : t6_974jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_974part2 : t6_974jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_974frontier : t6_974root.frontier 2=t6_974jobs := by rfl
theorem t6_974all : t6_974jobs.all (Job.check tree)=true := by
  simp only [t6_974jobs,List.all_append,List.all_nil,t6_974part0,t6_974part1,t6_974part2,Bool.and_self]
theorem t6_974checked : Checked tree [4,3,3,6,10,7] := by
  refine ⟨plan7014,valid7014,t6_974choices,?_⟩
  exact check_of_frontier tree 2 t6_974root t6_974jobs t6_974frontier t6_974all
theorem t6_975choices : plan7015.choices=[4,3,3,6,10,10].map (options 6 4) := by rfl


theorem t6_975part0 : t6_975jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_975frontier : t6_975root.frontier 0=t6_975jobs := by rfl
theorem t6_975all : t6_975jobs.all (Job.check tree)=true := by
  simp only [t6_975jobs,List.all_append,List.all_nil,t6_975part0,Bool.and_self]
theorem t6_975checked : Checked tree [4,3,3,6,10,10] := by
  refine ⟨plan7015,valid7015,t6_975choices,?_⟩
  exact check_of_frontier tree 0 t6_975root t6_975jobs t6_975frontier t6_975all
theorem t6_976choices : plan7016.choices=[4,3,3,7,7,7].map (options 6 4) := by rfl


theorem t6_976part0 : t6_976jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_976part1 : t6_976jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_976part2 : t6_976jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_976frontier : t6_976root.frontier 1=t6_976jobs := by rfl
theorem t6_976all : t6_976jobs.all (Job.check tree)=true := by
  simp only [t6_976jobs,List.all_append,List.all_nil,t6_976part0,t6_976part1,t6_976part2,Bool.and_self]
theorem t6_976checked : Checked tree [4,3,3,7,7,7] := by
  refine ⟨plan7016,valid7016,t6_976choices,?_⟩
  exact check_of_frontier tree 1 t6_976root t6_976jobs t6_976frontier t6_976all
theorem t6_977choices : plan7017.choices=[4,3,3,10,7,7].map (options 6 4) := by rfl


theorem t6_977part0 : t6_977jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_977part1 : t6_977jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_977part2 : t6_977jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_977frontier : t6_977root.frontier 2=t6_977jobs := by rfl
theorem t6_977all : t6_977jobs.all (Job.check tree)=true := by
  simp only [t6_977jobs,List.all_append,List.all_nil,t6_977part0,t6_977part1,t6_977part2,Bool.and_self]
theorem t6_977checked : Checked tree [4,3,3,10,7,7] := by
  refine ⟨plan7017,valid7017,t6_977choices,?_⟩
  exact check_of_frontier tree 2 t6_977root t6_977jobs t6_977frontier t6_977all
theorem t6_978choices : plan7018.choices=[4,3,3,10,10,7].map (options 6 4) := by rfl


theorem t6_978part0 : t6_978jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_978part1 : t6_978jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_978frontier : t6_978root.frontier 1=t6_978jobs := by rfl
theorem t6_978all : t6_978jobs.all (Job.check tree)=true := by
  simp only [t6_978jobs,List.all_append,List.all_nil,t6_978part0,t6_978part1,Bool.and_self]
theorem t6_978checked : Checked tree [4,3,3,10,10,7] := by
  refine ⟨plan7018,valid7018,t6_978choices,?_⟩
  exact check_of_frontier tree 1 t6_978root t6_978jobs t6_978frontier t6_978all
theorem t6_979choices : plan7019.choices=[4,3,3,10,10,10].map (options 6 4) := by rfl


theorem t6_979part0 : t6_979jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_979frontier : t6_979root.frontier 0=t6_979jobs := by rfl
theorem t6_979all : t6_979jobs.all (Job.check tree)=true := by
  simp only [t6_979jobs,List.all_append,List.all_nil,t6_979part0,Bool.and_self]
theorem t6_979checked : Checked tree [4,3,3,10,10,10] := by
  refine ⟨plan7019,valid7019,t6_979choices,?_⟩
  exact check_of_frontier tree 0 t6_979root t6_979jobs t6_979frontier t6_979all
theorem t6_980choices : plan7464.choices=[4,3,6,6,6,6].map (options 6 5) := by rfl


theorem t6_980part0 : t6_980jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_980frontier : t6_980root.frontier 0=t6_980jobs := by rfl
theorem t6_980all : t6_980jobs.all (Job.check tree)=true := by
  simp only [t6_980jobs,List.all_append,List.all_nil,t6_980part0,Bool.and_self]
theorem t6_980checked : Checked tree [4,3,6,6,6,6] := by
  refine ⟨plan7464,valid7464,t6_980choices,?_⟩
  exact check_of_frontier tree 0 t6_980root t6_980jobs t6_980frontier t6_980all
theorem t6_981choices : plan7465.choices=[4,3,6,6,6,7].map (options 6 5) := by rfl


theorem t6_981part0 : t6_981jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_981frontier : t6_981root.frontier 0=t6_981jobs := by rfl
theorem t6_981all : t6_981jobs.all (Job.check tree)=true := by
  simp only [t6_981jobs,List.all_append,List.all_nil,t6_981part0,Bool.and_self]
theorem t6_981checked : Checked tree [4,3,6,6,6,7] := by
  refine ⟨plan7465,valid7465,t6_981choices,?_⟩
  exact check_of_frontier tree 0 t6_981root t6_981jobs t6_981frontier t6_981all
theorem t6_982choices : plan7466.choices=[4,3,6,6,6,10].map (options 6 5) := by rfl


theorem t6_982part0 : t6_982jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_982frontier : t6_982root.frontier 0=t6_982jobs := by rfl
theorem t6_982all : t6_982jobs.all (Job.check tree)=true := by
  simp only [t6_982jobs,List.all_append,List.all_nil,t6_982part0,Bool.and_self]
theorem t6_982checked : Checked tree [4,3,6,6,6,10] := by
  refine ⟨plan7466,valid7466,t6_982choices,?_⟩
  exact check_of_frontier tree 0 t6_982root t6_982jobs t6_982frontier t6_982all
theorem t6_983choices : plan7467.choices=[4,3,6,6,7,7].map (options 6 5) := by rfl


theorem t6_983part0 : t6_983jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_983part1 : t6_983jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_983frontier : t6_983root.frontier 1=t6_983jobs := by rfl
theorem t6_983all : t6_983jobs.all (Job.check tree)=true := by
  simp only [t6_983jobs,List.all_append,List.all_nil,t6_983part0,t6_983part1,Bool.and_self]
theorem t6_983checked : Checked tree [4,3,6,6,7,7] := by
  refine ⟨plan7467,valid7467,t6_983choices,?_⟩
  exact check_of_frontier tree 1 t6_983root t6_983jobs t6_983frontier t6_983all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks119 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_978checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_979checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_980checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_981checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_982checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_983checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_973checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_974checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_975checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_976checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_977checked⟩
