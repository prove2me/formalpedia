-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks165
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:06:57.300755+00:00
-- url     : https://prove2.me/submissions/32775eea-cd89-49c2-9b79-8711bba84869

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks165
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks165
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
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

















































theorem valid601 : plan601.Valid := valid_step _ _ _ valid147 (by decide +kernel)











theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)











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





theorem valid1635 : plan1635.Valid := valid_step _ _ _ valid601 (by decide +kernel)































theorem valid1651 : plan1651.Valid := valid_step _ _ _ valid607 (by decide +kernel)

























theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1666 : plan1666.Valid := valid_step _ _ _ valid614 (by decide +kernel)




























































































































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

































theorem valid3569 : plan3569.Valid := valid_step _ _ _ valid1635 (by decide +kernel)



























theorem valid3583 : plan3583.Valid := valid_step _ _ _ valid1651 (by decide +kernel)

































































theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3617 : plan3617.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3618 : plan3618.Valid := valid_step _ _ _ valid1665 (by decide +kernel)

theorem valid3619 : plan3619.Valid := valid_step _ _ _ valid1666 (by decide +kernel)


























































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











































































































































theorem valid6118 : plan6118.Valid := valid_step _ _ _ valid3569 (by decide +kernel)

































theorem valid6135 : plan6135.Valid := valid_step _ _ _ valid3583 (by decide +kernel)


















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





































































































theorem valid6195 : plan6195.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6196 : plan6196.Valid := valid_step _ _ _ valid3617 (by decide +kernel)

theorem valid6197 : plan6197.Valid := valid_step _ _ _ valid3618 (by decide +kernel)

theorem valid6198 : plan6198.Valid := valid_step _ _ _ valid3619 (by decide +kernel)




















































































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









































































theorem valid8101 : plan8101.Valid := valid_step _ _ _ valid6118 (by decide +kernel)









































































theorem valid8138 : plan8138.Valid := valid_step _ _ _ valid6135 (by decide +kernel)












































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

























































































































































































theorem valid8445 : plan8445.Valid := valid_step _ _ _ valid8101 (by decide +kernel)






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













































































































theorem valid8503 : plan8503.Valid := valid_step _ _ _ valid8138 (by decide +kernel)


















































































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



































































theorem valid8194 : plan8194.Valid := valid_step _ _ _ valid6195 (by decide +kernel)

theorem valid8195 : plan8195.Valid := valid_step _ _ _ valid6196 (by decide +kernel)

theorem valid8196 : plan8196.Valid := valid_step _ _ _ valid6197 (by decide +kernel)

theorem valid8197 : plan8197.Valid := valid_step _ _ _ valid6198 (by decide +kernel)






















































































































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













































































































































theorem valid8615 : plan8615.Valid := valid_step _ _ _ valid8194 (by decide +kernel)

theorem valid8616 : plan8616.Valid := valid_step _ _ _ valid8195 (by decide +kernel)

theorem valid8617 : plan8617.Valid := valid_step _ _ _ valid8196 (by decide +kernel)

theorem valid8618 : plan8618.Valid := valid_step _ _ _ valid8197 (by decide +kernel)












































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
theorem t7_181choices : plan8615.choices=[2,3,10,7,7,7,7].map (options 7 5) := by rfl


theorem t7_181part0 : t7_181jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_181part1 : t7_181jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_181part2 : t7_181jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_181part3 : t7_181jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_181part4 : t7_181jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_181part5 : t7_181jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_181part6 : t7_181jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_181part7 : t7_181jobs7.all (Job.check tree)=true := by decide +kernel

theorem t7_181frontier : t7_181root.frontier 3=t7_181jobs := by rfl
theorem t7_181all : t7_181jobs.all (Job.check tree)=true := by
  simp only [t7_181jobs,List.all_append,List.all_nil,t7_181part0,t7_181part1,t7_181part2,t7_181part3,t7_181part4,t7_181part5,t7_181part6,t7_181part7,Bool.and_self]
theorem t7_181checked : Checked tree [2,3,10,7,7,7,7] := by
  refine ⟨plan8615,valid8615,t7_181choices,?_⟩
  exact check_of_frontier tree 3 t7_181root t7_181jobs t7_181frontier t7_181all
theorem t7_182choices : plan8616.choices=[2,3,10,10,7,7,7].map (options 7 5) := by rfl


theorem t7_182part0 : t7_182jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_182part1 : t7_182jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_182part2 : t7_182jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_182part3 : t7_182jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_182part4 : t7_182jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_182frontier : t7_182root.frontier 3=t7_182jobs := by rfl
theorem t7_182all : t7_182jobs.all (Job.check tree)=true := by
  simp only [t7_182jobs,List.all_append,List.all_nil,t7_182part0,t7_182part1,t7_182part2,t7_182part3,t7_182part4,Bool.and_self]
theorem t7_182checked : Checked tree [2,3,10,10,7,7,7] := by
  refine ⟨plan8616,valid8616,t7_182choices,?_⟩
  exact check_of_frontier tree 3 t7_182root t7_182jobs t7_182frontier t7_182all
theorem t7_183choices : plan8617.choices=[2,3,10,10,10,7,7].map (options 7 5) := by rfl


theorem t7_183part0 : t7_183jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_183part1 : t7_183jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_183frontier : t7_183root.frontier 1=t7_183jobs := by rfl
theorem t7_183all : t7_183jobs.all (Job.check tree)=true := by
  simp only [t7_183jobs,List.all_append,List.all_nil,t7_183part0,t7_183part1,Bool.and_self]
theorem t7_183checked : Checked tree [2,3,10,10,10,7,7] := by
  refine ⟨plan8617,valid8617,t7_183choices,?_⟩
  exact check_of_frontier tree 1 t7_183root t7_183jobs t7_183frontier t7_183all
theorem t7_184choices : plan8618.choices=[2,3,10,10,10,10,7].map (options 7 5) := by rfl


theorem t7_184part0 : t7_184jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_184frontier : t7_184root.frontier 0=t7_184jobs := by rfl
theorem t7_184all : t7_184jobs.all (Job.check tree)=true := by
  simp only [t7_184jobs,List.all_append,List.all_nil,t7_184part0,Bool.and_self]
theorem t7_184checked : Checked tree [2,3,10,10,10,10,7] := by
  refine ⟨plan8618,valid8618,t7_184choices,?_⟩
  exact check_of_frontier tree 0 t7_184root t7_184jobs t7_184frontier t7_184all
theorem t7_185choices : plan8445.choices=[2,5,3,3,3,7,7].map (options 7 3) := by rfl


theorem t7_185part0 : t7_185jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_185frontier : t7_185root.frontier 0=t7_185jobs := by rfl
theorem t7_185all : t7_185jobs.all (Job.check tree)=true := by
  simp only [t7_185jobs,List.all_append,List.all_nil,t7_185part0,Bool.and_self]
theorem t7_185checked : Checked tree [2,5,3,3,3,7,7] := by
  refine ⟨plan8445,valid8445,t7_185choices,?_⟩
  exact check_of_frontier tree 0 t7_185root t7_185jobs t7_185frontier t7_185all
theorem t7_186choices : plan8503.choices=[2,5,3,3,6,7,7].map (options 7 4) := by rfl


theorem t7_186part0 : t7_186jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_186part1 : t7_186jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_186frontier : t7_186root.frontier 1=t7_186jobs := by rfl
theorem t7_186all : t7_186jobs.all (Job.check tree)=true := by
  simp only [t7_186jobs,List.all_append,List.all_nil,t7_186part0,t7_186part1,Bool.and_self]
theorem t7_186checked : Checked tree [2,5,3,3,6,7,7] := by
  refine ⟨plan8503,valid8503,t7_186choices,?_⟩
  exact check_of_frontier tree 1 t7_186root t7_186jobs t7_186frontier t7_186all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks165 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_181checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_182checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_183checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_184checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_185checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_186checked⟩
