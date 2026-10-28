-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks162
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:02:07.757992+00:00
-- url     : https://prove2.me/submissions/edeb103e-1cf1-46e5-9c80-9c04f1bbc3a5

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks162
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks162
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
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











































theorem valid1654 : plan1654.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1655 : plan1655.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1656 : plan1656.Valid := valid_step _ _ _ valid608 (by decide +kernel)





theorem valid1659 : plan1659.Valid := valid_step _ _ _ valid611 (by decide +kernel)



theorem valid1661 : plan1661.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1662 : plan1662.Valid := valid_step _ _ _ valid614 (by decide +kernel)




































































































































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





























































































theorem valid3599 : plan3599.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

theorem valid3600 : plan3600.Valid := valid_step _ _ _ valid1655 (by decide +kernel)

theorem valid3601 : plan3601.Valid := valid_step _ _ _ valid1656 (by decide +kernel)











theorem valid3607 : plan3607.Valid := valid_step _ _ _ valid1659 (by decide +kernel)



theorem valid3609 : plan3609.Valid := valid_step _ _ _ valid1661 (by decide +kernel)

theorem valid3610 : plan3610.Valid := valid_step _ _ _ valid1662 (by decide +kernel)












































































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













theorem valid6151 : plan6151.Valid := valid_step _ _ _ valid3599 (by decide +kernel)

theorem valid6152 : plan6152.Valid := valid_step _ _ _ valid3600 (by decide +kernel)

theorem valid6153 : plan6153.Valid := valid_step _ _ _ valid3601 (by decide +kernel)













































theorem valid6176 : plan6176.Valid := valid_step _ _ _ valid3607 (by decide +kernel)



theorem valid6178 : plan6178.Valid := valid_step _ _ _ valid3609 (by decide +kernel)

theorem valid6179 : plan6179.Valid := valid_step _ _ _ valid3610 (by decide +kernel)


























































































































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









































































































































theorem valid8133 : plan8133.Valid := valid_step _ _ _ valid6151 (by decide +kernel)

theorem valid8134 : plan8134.Valid := valid_step _ _ _ valid6152 (by decide +kernel)

theorem valid8135 : plan8135.Valid := valid_step _ _ _ valid6153 (by decide +kernel)


















































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







































































































theorem valid8500 : plan8500.Valid := valid_step _ _ _ valid8133 (by decide +kernel)

theorem valid8501 : plan8501.Valid := valid_step _ _ _ valid8134 (by decide +kernel)

theorem valid8502 : plan8502.Valid := valid_step _ _ _ valid8135 (by decide +kernel)




















































































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





































theorem valid8179 : plan8179.Valid := valid_step _ _ _ valid6176 (by decide +kernel)



theorem valid8181 : plan8181.Valid := valid_step _ _ _ valid6178 (by decide +kernel)

theorem valid8182 : plan8182.Valid := valid_step _ _ _ valid6179 (by decide +kernel)




















































































































































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























































































































theorem valid8604 : plan8604.Valid := valid_step _ _ _ valid8179 (by decide +kernel)

theorem valid8605 : plan8605.Valid := valid_step _ _ _ valid8181 (by decide +kernel)

theorem valid8606 : plan8606.Valid := valid_step _ _ _ valid8182 (by decide +kernel)




































































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
theorem t7_167choices : plan8500.choices=[2,3,3,10,7,7,7].map (options 7 4) := by rfl


theorem t7_167part0 : t7_167jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_167part1 : t7_167jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_167part2 : t7_167jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_167part3 : t7_167jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_167part4 : t7_167jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_167part5 : t7_167jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_167part6 : t7_167jobs6.all (Job.check tree)=true := by decide +kernel

theorem t7_167part7 : t7_167jobs7.all (Job.check tree)=true := by decide +kernel

theorem t7_167part8 : t7_167jobs8.all (Job.check tree)=true := by decide +kernel

theorem t7_167part9 : t7_167jobs9.all (Job.check tree)=true := by decide +kernel

theorem t7_167frontier : t7_167root.frontier 2=t7_167jobs := by rfl
theorem t7_167all : t7_167jobs.all (Job.check tree)=true := by
  simp only [t7_167jobs,List.all_append,List.all_nil,t7_167part0,t7_167part1,t7_167part2,t7_167part3,t7_167part4,t7_167part5,t7_167part6,t7_167part7,t7_167part8,t7_167part9,Bool.and_self]
theorem t7_167checked : Checked tree [2,3,3,10,7,7,7] := by
  refine ⟨plan8500,valid8500,t7_167choices,?_⟩
  exact check_of_frontier tree 2 t7_167root t7_167jobs t7_167frontier t7_167all
theorem t7_168choices : plan8501.choices=[2,3,3,10,10,7,7].map (options 7 4) := by rfl


theorem t7_168part0 : t7_168jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_168part1 : t7_168jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_168part2 : t7_168jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_168part3 : t7_168jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_168frontier : t7_168root.frontier 2=t7_168jobs := by rfl
theorem t7_168all : t7_168jobs.all (Job.check tree)=true := by
  simp only [t7_168jobs,List.all_append,List.all_nil,t7_168part0,t7_168part1,t7_168part2,t7_168part3,Bool.and_self]
theorem t7_168checked : Checked tree [2,3,3,10,10,7,7] := by
  refine ⟨plan8501,valid8501,t7_168choices,?_⟩
  exact check_of_frontier tree 2 t7_168root t7_168jobs t7_168frontier t7_168all
theorem t7_169choices : plan8502.choices=[2,3,3,10,10,10,7].map (options 7 4) := by rfl


theorem t7_169part0 : t7_169jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_169frontier : t7_169root.frontier 0=t7_169jobs := by rfl
theorem t7_169all : t7_169jobs.all (Job.check tree)=true := by
  simp only [t7_169jobs,List.all_append,List.all_nil,t7_169part0,Bool.and_self]
theorem t7_169checked : Checked tree [2,3,3,10,10,10,7] := by
  refine ⟨plan8502,valid8502,t7_169choices,?_⟩
  exact check_of_frontier tree 0 t7_169root t7_169jobs t7_169frontier t7_169all
theorem t7_170choices : plan8604.choices=[2,3,6,6,6,6,7].map (options 7 5) := by rfl


theorem t7_170part0 : t7_170jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_170frontier : t7_170root.frontier 0=t7_170jobs := by rfl
theorem t7_170all : t7_170jobs.all (Job.check tree)=true := by
  simp only [t7_170jobs,List.all_append,List.all_nil,t7_170part0,Bool.and_self]
theorem t7_170checked : Checked tree [2,3,6,6,6,6,7] := by
  refine ⟨plan8604,valid8604,t7_170choices,?_⟩
  exact check_of_frontier tree 0 t7_170root t7_170jobs t7_170frontier t7_170all
theorem t7_171choices : plan8605.choices=[2,3,6,6,6,7,7].map (options 7 5) := by rfl


theorem t7_171part0 : t7_171jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_171part1 : t7_171jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_171frontier : t7_171root.frontier 1=t7_171jobs := by rfl
theorem t7_171all : t7_171jobs.all (Job.check tree)=true := by
  simp only [t7_171jobs,List.all_append,List.all_nil,t7_171part0,t7_171part1,Bool.and_self]
theorem t7_171checked : Checked tree [2,3,6,6,6,7,7] := by
  refine ⟨plan8605,valid8605,t7_171choices,?_⟩
  exact check_of_frontier tree 1 t7_171root t7_171jobs t7_171frontier t7_171all
theorem t7_172choices : plan8606.choices=[2,3,6,6,6,10,7].map (options 7 5) := by rfl


theorem t7_172part0 : t7_172jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_172frontier : t7_172root.frontier 0=t7_172jobs := by rfl
theorem t7_172all : t7_172jobs.all (Job.check tree)=true := by
  simp only [t7_172jobs,List.all_append,List.all_nil,t7_172part0,Bool.and_self]
theorem t7_172checked : Checked tree [2,3,6,6,6,10,7] := by
  refine ⟨plan8606,valid8606,t7_172choices,?_⟩
  exact check_of_frontier tree 0 t7_172root t7_172jobs t7_172frontier t7_172all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks162 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_168checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_169checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_170checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_171checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_172checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_167checked⟩
