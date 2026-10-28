-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks080
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:19:28.932488+00:00
-- url     : https://prove2.me/submissions/52c34fb9-7cb1-4cae-b2dc-6b03c1c57209

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks080
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks080
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
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











































theorem valid118 : plan118.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid123 : plan123.Valid := valid_step _ _ _ valid0 (by decide +kernel)















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

























































































































theorem valid541 : plan541.Valid := valid_step _ _ _ valid118 (by decide +kernel)









theorem valid546 : plan546.Valid := valid_step _ _ _ valid123 (by decide +kernel)

















































theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid573 : plan573.Valid := valid_step _ _ _ valid132 (by decide +kernel)






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







































































































































theorem valid1508 : plan1508.Valid := valid_step _ _ _ valid541 (by decide +kernel)















theorem valid1516 : plan1516.Valid := valid_step _ _ _ valid546 (by decide +kernel)








































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



























































































































































theorem valid3246 : plan3246.Valid := valid_step _ _ _ valid1508 (by decide +kernel)




































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

theorem valid3265 : plan3265.Valid := valid_step _ _ _ valid1516 (by decide +kernel)






























































































































































































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































































































































































theorem valid5360 : plan5360.Valid := valid_step _ _ _ valid3246 (by decide +kernel)
































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























































theorem valid5404 : plan5404.Valid := valid_step _ _ _ valid3265 (by decide +kernel)








































































































































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









































































































































theorem valid6309 : plan6309.Valid := valid_step _ _ _ valid5360 (by decide +kernel)






















































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















































































































theorem valid6392 : plan6392.Valid := valid_step _ _ _ valid5404 (by decide +kernel)
















































































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



























theorem valid6926 : plan6926.Valid := valid_step _ _ _ valid5644 (by decide +kernel)

theorem valid6927 : plan6927.Valid := valid_step _ _ _ valid5645 (by decide +kernel)

theorem valid6928 : plan6928.Valid := valid_step _ _ _ valid5646 (by decide +kernel)
































































































































































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
theorem t6_663choices : plan6926.choices=[2,3,10,10,7,7].map (options 6 4) := by rfl


theorem t6_663part0 : t6_663jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_663part1 : t6_663jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_663part2 : t6_663jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_663part3 : t6_663jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_663part4 : t6_663jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_663part5 : t6_663jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_663part6 : t6_663jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_663part7 : t6_663jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_663part8 : t6_663jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_663frontier : t6_663root.frontier 3=t6_663jobs := by rfl
theorem t6_663all : t6_663jobs.all (Job.check tree)=true := by
  simp only [t6_663jobs,List.all_append,List.all_nil,t6_663part0,t6_663part1,t6_663part2,t6_663part3,t6_663part4,t6_663part5,t6_663part6,t6_663part7,t6_663part8,Bool.and_self]
theorem t6_663checked : Checked tree [2,3,10,10,7,7] := by
  refine ⟨plan6926,valid6926,t6_663choices,?_⟩
  exact check_of_frontier tree 3 t6_663root t6_663jobs t6_663frontier t6_663all
theorem t6_664choices : plan6927.choices=[2,3,10,10,10,7].map (options 6 4) := by rfl


theorem t6_664part0 : t6_664jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_664part1 : t6_664jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_664part2 : t6_664jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_664part3 : t6_664jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_664part4 : t6_664jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_664frontier : t6_664root.frontier 2=t6_664jobs := by rfl
theorem t6_664all : t6_664jobs.all (Job.check tree)=true := by
  simp only [t6_664jobs,List.all_append,List.all_nil,t6_664part0,t6_664part1,t6_664part2,t6_664part3,t6_664part4,Bool.and_self]
theorem t6_664checked : Checked tree [2,3,10,10,10,7] := by
  refine ⟨plan6927,valid6927,t6_664choices,?_⟩
  exact check_of_frontier tree 2 t6_664root t6_664jobs t6_664frontier t6_664all
theorem t6_665choices : plan6928.choices=[2,3,10,10,10,10].map (options 6 4) := by rfl


theorem t6_665part0 : t6_665jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_665frontier : t6_665root.frontier 0=t6_665jobs := by rfl
theorem t6_665all : t6_665jobs.all (Job.check tree)=true := by
  simp only [t6_665jobs,List.all_append,List.all_nil,t6_665part0,Bool.and_self]
theorem t6_665checked : Checked tree [2,3,10,10,10,10] := by
  refine ⟨plan6928,valid6928,t6_665choices,?_⟩
  exact check_of_frontier tree 0 t6_665root t6_665jobs t6_665frontier t6_665all
theorem t6_666choices : plan6309.choices=[2,5,3,3,3,3].map (options 6 1) := by rfl


theorem t6_666part0 : t6_666jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_666frontier : t6_666root.frontier 0=t6_666jobs := by rfl
theorem t6_666all : t6_666jobs.all (Job.check tree)=true := by
  simp only [t6_666jobs,List.all_append,List.all_nil,t6_666part0,Bool.and_self]
theorem t6_666checked : Checked tree [2,5,3,3,3,3] := by
  refine ⟨plan6309,valid6309,t6_666choices,?_⟩
  exact check_of_frontier tree 0 t6_666root t6_666jobs t6_666frontier t6_666all
theorem t6_667choices : plan6392.choices=[2,5,3,3,3,6].map (options 6 2) := by rfl


theorem t6_667part0 : t6_667jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_667frontier : t6_667root.frontier 0=t6_667jobs := by rfl
theorem t6_667all : t6_667jobs.all (Job.check tree)=true := by
  simp only [t6_667jobs,List.all_append,List.all_nil,t6_667part0,Bool.and_self]
theorem t6_667checked : Checked tree [2,5,3,3,3,6] := by
  refine ⟨plan6392,valid6392,t6_667choices,?_⟩
  exact check_of_frontier tree 0 t6_667root t6_667jobs t6_667frontier t6_667all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks080 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_663checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_664checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_665checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_666checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_667checked⟩
