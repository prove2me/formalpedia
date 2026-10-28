-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks182
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:12:51.511925+00:00
-- url     : https://prove2.me/submissions/9c9b3dc6-3c7c-483b-b628-ed85f010836f

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks182
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks182
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans086
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans091
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans092
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























































































































theorem valid156 : plan156.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid157 : plan157.Valid := valid_step _ _ _ valid0 (by decide +kernel)






































































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





















































































theorem valid619 : plan619.Valid := valid_step _ _ _ valid156 (by decide +kernel)

theorem valid620 : plan620.Valid := valid_step _ _ _ valid156 (by decide +kernel)

theorem valid621 : plan621.Valid := valid_step _ _ _ valid157 (by decide +kernel)






































































































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



















































































theorem valid1674 : plan1674.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1675 : plan1675.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1676 : plan1676.Valid := valid_step _ _ _ valid620 (by decide +kernel)

theorem valid1677 : plan1677.Valid := valid_step _ _ _ valid621 (by decide +kernel)






































































































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































































































































































theorem valid3632 : plan3632.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3633 : plan3633.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3634 : plan3634.Valid := valid_step _ _ _ valid1675 (by decide +kernel)

theorem valid3635 : plan3635.Valid := valid_step _ _ _ valid1676 (by decide +kernel)

theorem valid3636 : plan3636.Valid := valid_step _ _ _ valid1677 (by decide +kernel)
























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





























































































































































theorem valid6223 : plan6223.Valid := valid_step _ _ _ valid3635 (by decide +kernel)

theorem valid6224 : plan6224.Valid := valid_step _ _ _ valid3636 (by decide +kernel)

theorem valid6225 : plan6225.Valid := valid_step _ _ _ valid3632 (by decide +kernel)









theorem valid6230 : plan6230.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6231 : plan6231.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6232 : plan6232.Valid := valid_step _ _ _ valid3634 (by decide +kernel)

theorem valid6233 : plan6233.Valid := valid_step _ _ _ valid3635 (by decide +kernel)

theorem valid6234 : plan6234.Valid := valid_step _ _ _ valid3636 (by decide +kernel)












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



























































theorem valid8286 : plan8286.Valid := valid_step _ _ _ valid6223 (by decide +kernel)

theorem valid8287 : plan8287.Valid := valid_step _ _ _ valid6224 (by decide +kernel)

theorem valid8288 : plan8288.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8289 : plan8289.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8290 : plan8290.Valid := valid_step _ _ _ valid6231 (by decide +kernel)

theorem valid8291 : plan8291.Valid := valid_step _ _ _ valid6232 (by decide +kernel)

theorem valid8292 : plan8292.Valid := valid_step _ _ _ valid6233 (by decide +kernel)

theorem valid8293 : plan8293.Valid := valid_step _ _ _ valid6234 (by decide +kernel)

theorem valid8294 : plan8294.Valid := valid_step _ _ _ valid6225 (by decide +kernel)




















































































































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

















































































































































































theorem valid8825 : plan8825.Valid := valid_step _ _ _ valid8286 (by decide +kernel)

theorem valid8826 : plan8826.Valid := valid_step _ _ _ valid8287 (by decide +kernel)

theorem valid8827 : plan8827.Valid := valid_step _ _ _ valid8288 (by decide +kernel)

theorem valid8828 : plan8828.Valid := valid_step _ _ _ valid8289 (by decide +kernel)

theorem valid8829 : plan8829.Valid := valid_step _ _ _ valid8290 (by decide +kernel)

theorem valid8830 : plan8830.Valid := valid_step _ _ _ valid8291 (by decide +kernel)

theorem valid8831 : plan8831.Valid := valid_step _ _ _ valid8292 (by decide +kernel)

theorem valid8832 : plan8832.Valid := valid_step _ _ _ valid8293 (by decide +kernel)
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

theorem valid8833 : plan8833.Valid := valid_step _ _ _ valid8294 (by decide +kernel)






























































































































































































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
theorem t7_327choices : plan8825.choices=[3,6,6,10,10,10,7].map (options 7 6) := by rfl


theorem t7_327part0 : t7_327jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_327frontier : t7_327root.frontier 0=t7_327jobs := by rfl
theorem t7_327all : t7_327jobs.all (Job.check tree)=true := by
  simp only [t7_327jobs,List.all_append,List.all_nil,t7_327part0,Bool.and_self]
theorem t7_327checked : Checked tree [3,6,6,10,10,10,7] := by
  refine ⟨plan8825,valid8825,t7_327choices,?_⟩
  exact check_of_frontier tree 0 t7_327root t7_327jobs t7_327frontier t7_327all
theorem t7_328choices : plan8826.choices=[3,6,6,10,10,10,10].map (options 7 6) := by rfl


theorem t7_328part0 : t7_328jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_328frontier : t7_328root.frontier 0=t7_328jobs := by rfl
theorem t7_328all : t7_328jobs.all (Job.check tree)=true := by
  simp only [t7_328jobs,List.all_append,List.all_nil,t7_328part0,Bool.and_self]
theorem t7_328checked : Checked tree [3,6,6,10,10,10,10] := by
  refine ⟨plan8826,valid8826,t7_328choices,?_⟩
  exact check_of_frontier tree 0 t7_328root t7_328jobs t7_328frontier t7_328all
theorem t7_329choices : plan8827.choices=[3,6,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_329part0 : t7_329jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_329part1 : t7_329jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_329part2 : t7_329jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_329part3 : t7_329jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_329frontier : t7_329root.frontier 2=t7_329jobs := by rfl
theorem t7_329all : t7_329jobs.all (Job.check tree)=true := by
  simp only [t7_329jobs,List.all_append,List.all_nil,t7_329part0,t7_329part1,t7_329part2,t7_329part3,Bool.and_self]
theorem t7_329checked : Checked tree [3,6,7,7,7,7,7] := by
  refine ⟨plan8827,valid8827,t7_329choices,?_⟩
  exact check_of_frontier tree 2 t7_329root t7_329jobs t7_329frontier t7_329all
theorem t7_330choices : plan8828.choices=[3,6,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_330part0 : t7_330jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_330part1 : t7_330jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_330part2 : t7_330jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_330part3 : t7_330jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_330part4 : t7_330jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_330part5 : t7_330jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_330frontier : t7_330root.frontier 2=t7_330jobs := by rfl
theorem t7_330all : t7_330jobs.all (Job.check tree)=true := by
  simp only [t7_330jobs,List.all_append,List.all_nil,t7_330part0,t7_330part1,t7_330part2,t7_330part3,t7_330part4,t7_330part5,Bool.and_self]
theorem t7_330checked : Checked tree [3,6,10,7,7,7,7] := by
  refine ⟨plan8828,valid8828,t7_330choices,?_⟩
  exact check_of_frontier tree 2 t7_330root t7_330jobs t7_330frontier t7_330all
theorem t7_331choices : plan8829.choices=[3,6,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_331part0 : t7_331jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_331part1 : t7_331jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_331part2 : t7_331jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_331part3 : t7_331jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_331part4 : t7_331jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_331frontier : t7_331root.frontier 2=t7_331jobs := by rfl
theorem t7_331all : t7_331jobs.all (Job.check tree)=true := by
  simp only [t7_331jobs,List.all_append,List.all_nil,t7_331part0,t7_331part1,t7_331part2,t7_331part3,t7_331part4,Bool.and_self]
theorem t7_331checked : Checked tree [3,6,10,10,7,7,7] := by
  refine ⟨plan8829,valid8829,t7_331choices,?_⟩
  exact check_of_frontier tree 2 t7_331root t7_331jobs t7_331frontier t7_331all
theorem t7_332choices : plan8830.choices=[3,6,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_332part0 : t7_332jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_332part1 : t7_332jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_332frontier : t7_332root.frontier 1=t7_332jobs := by rfl
theorem t7_332all : t7_332jobs.all (Job.check tree)=true := by
  simp only [t7_332jobs,List.all_append,List.all_nil,t7_332part0,t7_332part1,Bool.and_self]
theorem t7_332checked : Checked tree [3,6,10,10,10,7,7] := by
  refine ⟨plan8830,valid8830,t7_332choices,?_⟩
  exact check_of_frontier tree 1 t7_332root t7_332jobs t7_332frontier t7_332all
theorem t7_333choices : plan8831.choices=[3,6,10,10,10,10,7].map (options 7 6) := by rfl


theorem t7_333part0 : t7_333jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_333frontier : t7_333root.frontier 0=t7_333jobs := by rfl
theorem t7_333all : t7_333jobs.all (Job.check tree)=true := by
  simp only [t7_333jobs,List.all_append,List.all_nil,t7_333part0,Bool.and_self]
theorem t7_333checked : Checked tree [3,6,10,10,10,10,7] := by
  refine ⟨plan8831,valid8831,t7_333choices,?_⟩
  exact check_of_frontier tree 0 t7_333root t7_333jobs t7_333frontier t7_333all
theorem t7_334choices : plan8832.choices=[3,6,10,10,10,10,10].map (options 7 6) := by rfl


theorem t7_334part0 : t7_334jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_334frontier : t7_334root.frontier 0=t7_334jobs := by rfl
theorem t7_334all : t7_334jobs.all (Job.check tree)=true := by
  simp only [t7_334jobs,List.all_append,List.all_nil,t7_334part0,Bool.and_self]
theorem t7_334checked : Checked tree [3,6,10,10,10,10,10] := by
  refine ⟨plan8832,valid8832,t7_334choices,?_⟩
  exact check_of_frontier tree 0 t7_334root t7_334jobs t7_334frontier t7_334all
theorem t7_335choices : plan8833.choices=[3,7,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_335part0 : t7_335jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_335part1 : t7_335jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_335frontier : t7_335root.frontier 1=t7_335jobs := by rfl
theorem t7_335all : t7_335jobs.all (Job.check tree)=true := by
  simp only [t7_335jobs,List.all_append,List.all_nil,t7_335part0,t7_335part1,Bool.and_self]
theorem t7_335checked : Checked tree [3,7,7,7,7,7,7] := by
  refine ⟨plan8833,valid8833,t7_335choices,?_⟩
  exact check_of_frontier tree 1 t7_335root t7_335jobs t7_335frontier t7_335all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks182 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_331checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_332checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_333checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_334checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_335checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_328checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_329checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_330checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_327checked⟩
