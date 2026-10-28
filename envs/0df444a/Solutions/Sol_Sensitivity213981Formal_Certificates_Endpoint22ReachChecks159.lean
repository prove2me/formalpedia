-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks159
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:01:33.317993+00:00
-- url     : https://prove2.me/submissions/a46bdc9c-baed-4eb0-aba3-c5771a8ed07d

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks159
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks159
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

























































































theorem valid141 : plan141.Valid := valid_step _ _ _ valid0 (by decide +kernel)





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

























theorem valid589 : plan589.Valid := valid_step _ _ _ valid141 (by decide +kernel)







theorem valid593 : plan593.Valid := valid_step _ _ _ valid144 (by decide +kernel)



theorem valid595 : plan595.Valid := valid_step _ _ _ valid144 (by decide +kernel)

theorem valid596 : plan596.Valid := valid_step _ _ _ valid144 (by decide +kernel)





theorem valid599 : plan599.Valid := valid_step _ _ _ valid147 (by decide +kernel)



theorem valid601 : plan601.Valid := valid_step _ _ _ valid147 (by decide +kernel)

theorem valid602 : plan602.Valid := valid_step _ _ _ valid147 (by decide +kernel)





theorem valid605 : plan605.Valid := valid_step _ _ _ valid150 (by decide +kernel)















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











theorem valid1638 : plan1638.Valid := valid_step _ _ _ valid599 (by decide +kernel)



theorem valid1640 : plan1640.Valid := valid_step _ _ _ valid601 (by decide +kernel)

theorem valid1641 : plan1641.Valid := valid_step _ _ _ valid602 (by decide +kernel)



theorem valid1643 : plan1643.Valid := valid_step _ _ _ valid601 (by decide +kernel)

theorem valid1644 : plan1644.Valid := valid_step _ _ _ valid601 (by decide +kernel)

theorem valid1645 : plan1645.Valid := valid_step _ _ _ valid602 (by decide +kernel)







theorem valid1649 : plan1649.Valid := valid_step _ _ _ valid605 (by decide +kernel)































theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)






























































































































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

















































































































































































theorem valid1625 : plan1625.Valid := valid_step _ _ _ valid589 (by decide +kernel)







theorem valid1629 : plan1629.Valid := valid_step _ _ _ valid593 (by decide +kernel)



theorem valid1631 : plan1631.Valid := valid_step _ _ _ valid595 (by decide +kernel)

theorem valid1632 : plan1632.Valid := valid_step _ _ _ valid596 (by decide +kernel)
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













theorem valid3559 : plan3559.Valid := valid_step _ _ _ valid1625 (by decide +kernel)







theorem valid3563 : plan3563.Valid := valid_step _ _ _ valid1629 (by decide +kernel)



theorem valid3565 : plan3565.Valid := valid_step _ _ _ valid1631 (by decide +kernel)

theorem valid3566 : plan3566.Valid := valid_step _ _ _ valid1632 (by decide +kernel)











theorem valid3572 : plan3572.Valid := valid_step _ _ _ valid1638 (by decide +kernel)



theorem valid3574 : plan3574.Valid := valid_step _ _ _ valid1640 (by decide +kernel)

theorem valid3575 : plan3575.Valid := valid_step _ _ _ valid1641 (by decide +kernel)



theorem valid3577 : plan3577.Valid := valid_step _ _ _ valid1643 (by decide +kernel)

theorem valid3578 : plan3578.Valid := valid_step _ _ _ valid1644 (by decide +kernel)

theorem valid3579 : plan3579.Valid := valid_step _ _ _ valid1645 (by decide +kernel)



















theorem valid3589 : plan3589.Valid := valid_step _ _ _ valid1649 (by decide +kernel)

























































theorem valid3618 : plan3618.Valid := valid_step _ _ _ valid1665 (by decide +kernel)




























































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





















































































































theorem valid6107 : plan6107.Valid := valid_step _ _ _ valid3559 (by decide +kernel)







theorem valid6111 : plan6111.Valid := valid_step _ _ _ valid3563 (by decide +kernel)



theorem valid6113 : plan6113.Valid := valid_step _ _ _ valid3565 (by decide +kernel)

theorem valid6114 : plan6114.Valid := valid_step _ _ _ valid3566 (by decide +kernel)













theorem valid6121 : plan6121.Valid := valid_step _ _ _ valid3572 (by decide +kernel)



theorem valid6123 : plan6123.Valid := valid_step _ _ _ valid3574 (by decide +kernel)

theorem valid6124 : plan6124.Valid := valid_step _ _ _ valid3575 (by decide +kernel)



theorem valid6126 : plan6126.Valid := valid_step _ _ _ valid3577 (by decide +kernel)

theorem valid6127 : plan6127.Valid := valid_step _ _ _ valid3578 (by decide +kernel)

theorem valid6128 : plan6128.Valid := valid_step _ _ _ valid3579 (by decide +kernel)

























theorem valid6141 : plan6141.Valid := valid_step _ _ _ valid3589 (by decide +kernel)






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









































































































theorem valid6197 : plan6197.Valid := valid_step _ _ _ valid3618 (by decide +kernel)






















































































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



















theorem valid8074 : plan8074.Valid := valid_step _ _ _ valid6107 (by decide +kernel)









theorem valid8079 : plan8079.Valid := valid_step _ _ _ valid6111 (by decide +kernel)



theorem valid8081 : plan8081.Valid := valid_step _ _ _ valid6113 (by decide +kernel)

theorem valid8082 : plan8082.Valid := valid_step _ _ _ valid6114 (by decide +kernel)



















theorem valid8092 : plan8092.Valid := valid_step _ _ _ valid6121 (by decide +kernel)



theorem valid8094 : plan8094.Valid := valid_step _ _ _ valid6123 (by decide +kernel)

theorem valid8095 : plan8095.Valid := valid_step _ _ _ valid6124 (by decide +kernel)



theorem valid8097 : plan8097.Valid := valid_step _ _ _ valid6126 (by decide +kernel)

theorem valid8098 : plan8098.Valid := valid_step _ _ _ valid6127 (by decide +kernel)

theorem valid8099 : plan8099.Valid := valid_step _ _ _ valid6128 (by decide +kernel)















































theorem valid8123 : plan8123.Valid := valid_step _ _ _ valid6141 (by decide +kernel)










































































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

























































































































theorem valid8413 : plan8413.Valid := valid_step _ _ _ valid8074 (by decide +kernel)











theorem valid8419 : plan8419.Valid := valid_step _ _ _ valid8079 (by decide +kernel)

theorem valid8420 : plan8420.Valid := valid_step _ _ _ valid8081 (by decide +kernel)

theorem valid8421 : plan8421.Valid := valid_step _ _ _ valid8082 (by decide +kernel)



































theorem valid8439 : plan8439.Valid := valid_step _ _ _ valid8092 (by decide +kernel)

theorem valid8440 : plan8440.Valid := valid_step _ _ _ valid8094 (by decide +kernel)

theorem valid8441 : plan8441.Valid := valid_step _ _ _ valid8095 (by decide +kernel)

theorem valid8442 : plan8442.Valid := valid_step _ _ _ valid8097 (by decide +kernel)

theorem valid8443 : plan8443.Valid := valid_step _ _ _ valid8098 (by decide +kernel)

theorem valid8444 : plan8444.Valid := valid_step _ _ _ valid8099 (by decide +kernel)








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

























































































theorem valid8493 : plan8493.Valid := valid_step _ _ _ valid8123 (by decide +kernel)






































































































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













theorem valid8167 : plan8167.Valid := valid_step _ _ _ valid6197 (by decide +kernel)


















































































































































































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





















































































































theorem valid8603 : plan8603.Valid := valid_step _ _ _ valid8167 (by decide +kernel)










































































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
theorem t7_149choices : plan8603.choices=[2,2,10,10,10,7,7].map (options 7 5) := by rfl


theorem t7_149part0 : t7_149jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_149frontier : t7_149root.frontier 0=t7_149jobs := by rfl
theorem t7_149all : t7_149jobs.all (Job.check tree)=true := by
  simp only [t7_149jobs,List.all_append,List.all_nil,t7_149part0,Bool.and_self]
theorem t7_149checked : Checked tree [2,2,10,10,10,7,7] := by
  refine ⟨plan8603,valid8603,t7_149choices,?_⟩
  exact check_of_frontier tree 0 t7_149root t7_149jobs t7_149frontier t7_149all
theorem t7_150choices : plan8413.choices=[2,3,3,3,3,3,7].map (options 7 1) := by rfl


theorem t7_150part0 : t7_150jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_150frontier : t7_150root.frontier 0=t7_150jobs := by rfl
theorem t7_150all : t7_150jobs.all (Job.check tree)=true := by
  simp only [t7_150jobs,List.all_append,List.all_nil,t7_150part0,Bool.and_self]
theorem t7_150checked : Checked tree [2,3,3,3,3,3,7] := by
  refine ⟨plan8413,valid8413,t7_150choices,?_⟩
  exact check_of_frontier tree 0 t7_150root t7_150jobs t7_150frontier t7_150all
theorem t7_151choices : plan8419.choices=[2,3,3,3,3,6,7].map (options 7 2) := by rfl


theorem t7_151part0 : t7_151jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_151frontier : t7_151root.frontier 0=t7_151jobs := by rfl
theorem t7_151all : t7_151jobs.all (Job.check tree)=true := by
  simp only [t7_151jobs,List.all_append,List.all_nil,t7_151part0,Bool.and_self]
theorem t7_151checked : Checked tree [2,3,3,3,3,6,7] := by
  refine ⟨plan8419,valid8419,t7_151choices,?_⟩
  exact check_of_frontier tree 0 t7_151root t7_151jobs t7_151frontier t7_151all
theorem t7_152choices : plan8420.choices=[2,3,3,3,3,7,7].map (options 7 2) := by rfl


theorem t7_152part0 : t7_152jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_152frontier : t7_152root.frontier 0=t7_152jobs := by rfl
theorem t7_152all : t7_152jobs.all (Job.check tree)=true := by
  simp only [t7_152jobs,List.all_append,List.all_nil,t7_152part0,Bool.and_self]
theorem t7_152checked : Checked tree [2,3,3,3,3,7,7] := by
  refine ⟨plan8420,valid8420,t7_152choices,?_⟩
  exact check_of_frontier tree 0 t7_152root t7_152jobs t7_152frontier t7_152all
theorem t7_153choices : plan8421.choices=[2,3,3,3,3,10,7].map (options 7 2) := by rfl


theorem t7_153part0 : t7_153jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_153frontier : t7_153root.frontier 0=t7_153jobs := by rfl
theorem t7_153all : t7_153jobs.all (Job.check tree)=true := by
  simp only [t7_153jobs,List.all_append,List.all_nil,t7_153part0,Bool.and_self]
theorem t7_153checked : Checked tree [2,3,3,3,3,10,7] := by
  refine ⟨plan8421,valid8421,t7_153choices,?_⟩
  exact check_of_frontier tree 0 t7_153root t7_153jobs t7_153frontier t7_153all
theorem t7_154choices : plan8439.choices=[2,3,3,3,6,6,7].map (options 7 3) := by rfl


theorem t7_154part0 : t7_154jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_154frontier : t7_154root.frontier 0=t7_154jobs := by rfl
theorem t7_154all : t7_154jobs.all (Job.check tree)=true := by
  simp only [t7_154jobs,List.all_append,List.all_nil,t7_154part0,Bool.and_self]
theorem t7_154checked : Checked tree [2,3,3,3,6,6,7] := by
  refine ⟨plan8439,valid8439,t7_154choices,?_⟩
  exact check_of_frontier tree 0 t7_154root t7_154jobs t7_154frontier t7_154all
theorem t7_155choices : plan8440.choices=[2,3,3,3,6,7,7].map (options 7 3) := by rfl


theorem t7_155part0 : t7_155jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_155part1 : t7_155jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_155part2 : t7_155jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_155part3 : t7_155jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_155frontier : t7_155root.frontier 1=t7_155jobs := by rfl
theorem t7_155all : t7_155jobs.all (Job.check tree)=true := by
  simp only [t7_155jobs,List.all_append,List.all_nil,t7_155part0,t7_155part1,t7_155part2,t7_155part3,Bool.and_self]
theorem t7_155checked : Checked tree [2,3,3,3,6,7,7] := by
  refine ⟨plan8440,valid8440,t7_155choices,?_⟩
  exact check_of_frontier tree 1 t7_155root t7_155jobs t7_155frontier t7_155all
theorem t7_156choices : plan8441.choices=[2,3,3,3,6,10,7].map (options 7 3) := by rfl


theorem t7_156part0 : t7_156jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_156part1 : t7_156jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_156frontier : t7_156root.frontier 1=t7_156jobs := by rfl
theorem t7_156all : t7_156jobs.all (Job.check tree)=true := by
  simp only [t7_156jobs,List.all_append,List.all_nil,t7_156part0,t7_156part1,Bool.and_self]
theorem t7_156checked : Checked tree [2,3,3,3,6,10,7] := by
  refine ⟨plan8441,valid8441,t7_156choices,?_⟩
  exact check_of_frontier tree 1 t7_156root t7_156jobs t7_156frontier t7_156all
theorem t7_157choices : plan8442.choices=[2,3,3,3,7,7,7].map (options 7 3) := by rfl


theorem t7_157part0 : t7_157jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_157part1 : t7_157jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_157part2 : t7_157jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_157part3 : t7_157jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_157frontier : t7_157root.frontier 1=t7_157jobs := by rfl
theorem t7_157all : t7_157jobs.all (Job.check tree)=true := by
  simp only [t7_157jobs,List.all_append,List.all_nil,t7_157part0,t7_157part1,t7_157part2,t7_157part3,Bool.and_self]
theorem t7_157checked : Checked tree [2,3,3,3,7,7,7] := by
  refine ⟨plan8442,valid8442,t7_157choices,?_⟩
  exact check_of_frontier tree 1 t7_157root t7_157jobs t7_157frontier t7_157all
theorem t7_158choices : plan8443.choices=[2,3,3,3,10,7,7].map (options 7 3) := by rfl


theorem t7_158part0 : t7_158jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_158part1 : t7_158jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_158part2 : t7_158jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_158part3 : t7_158jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_158frontier : t7_158root.frontier 1=t7_158jobs := by rfl
theorem t7_158all : t7_158jobs.all (Job.check tree)=true := by
  simp only [t7_158jobs,List.all_append,List.all_nil,t7_158part0,t7_158part1,t7_158part2,t7_158part3,Bool.and_self]
theorem t7_158checked : Checked tree [2,3,3,3,10,7,7] := by
  refine ⟨plan8443,valid8443,t7_158choices,?_⟩
  exact check_of_frontier tree 1 t7_158root t7_158jobs t7_158frontier t7_158all
theorem t7_159choices : plan8444.choices=[2,3,3,3,10,10,7].map (options 7 3) := by rfl


theorem t7_159part0 : t7_159jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_159frontier : t7_159root.frontier 0=t7_159jobs := by rfl
theorem t7_159all : t7_159jobs.all (Job.check tree)=true := by
  simp only [t7_159jobs,List.all_append,List.all_nil,t7_159part0,Bool.and_self]
theorem t7_159checked : Checked tree [2,3,3,3,10,10,7] := by
  refine ⟨plan8444,valid8444,t7_159choices,?_⟩
  exact check_of_frontier tree 0 t7_159root t7_159jobs t7_159frontier t7_159all
theorem t7_160choices : plan8493.choices=[2,3,3,6,6,6,7].map (options 7 4) := by rfl


theorem t7_160part0 : t7_160jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_160frontier : t7_160root.frontier 0=t7_160jobs := by rfl
theorem t7_160all : t7_160jobs.all (Job.check tree)=true := by
  simp only [t7_160jobs,List.all_append,List.all_nil,t7_160part0,Bool.and_self]
theorem t7_160checked : Checked tree [2,3,3,6,6,6,7] := by
  refine ⟨plan8493,valid8493,t7_160choices,?_⟩
  exact check_of_frontier tree 0 t7_160root t7_160jobs t7_160frontier t7_160all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks159 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_158checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_159checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_160checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_150checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_151checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_152checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_153checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_154checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_155checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_156checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_157checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_149checked⟩
