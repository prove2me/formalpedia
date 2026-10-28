-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks050
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:05:15.947774+00:00
-- url     : https://prove2.me/submissions/e7a9914b-cf13-44fd-a51d-7e29ac513109

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks050
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks050
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
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























































theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)







theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)


























































































































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





































































































































theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)

























theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)



theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)









theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)



theorem valid571 : plan571.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid572 : plan572.Valid := valid_step _ _ _ valid131 (by decide +kernel)








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

























































































































































theorem valid1517 : plan1517.Valid := valid_step _ _ _ valid547 (by decide +kernel)































theorem valid1533 : plan1533.Valid := valid_step _ _ _ valid560 (by decide +kernel)



theorem valid1535 : plan1535.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1536 : plan1536.Valid := valid_step _ _ _ valid563 (by decide +kernel)
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

















theorem valid1545 : plan1545.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1546 : plan1546.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1547 : plan1547.Valid := valid_step _ _ _ valid564 (by decide +kernel)

theorem valid1548 : plan1548.Valid := valid_step _ _ _ valid562 (by decide +kernel)









theorem valid1553 : plan1553.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1554 : plan1554.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1555 : plan1555.Valid := valid_step _ _ _ valid564 (by decide +kernel)























theorem valid1567 : plan1567.Valid := valid_step _ _ _ valid571 (by decide +kernel)





theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)



theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)



theorem valid1575 : plan1575.Valid := valid_step _ _ _ valid571 (by decide +kernel)





theorem valid1578 : plan1578.Valid := valid_step _ _ _ valid571 (by decide +kernel)












































































































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























theorem valid3276 : plan3276.Valid := valid_step _ _ _ valid1517 (by decide +kernel)













































































theorem valid3315 : plan3315.Valid := valid_step _ _ _ valid1545 (by decide +kernel)

theorem valid3316 : plan3316.Valid := valid_step _ _ _ valid1546 (by decide +kernel)

theorem valid3317 : plan3317.Valid := valid_step _ _ _ valid1547 (by decide +kernel)

theorem valid3318 : plan3318.Valid := valid_step _ _ _ valid1548 (by decide +kernel)

theorem valid3319 : plan3319.Valid := valid_step _ _ _ valid1553 (by decide +kernel)

theorem valid3320 : plan3320.Valid := valid_step _ _ _ valid1554 (by decide +kernel)

theorem valid3321 : plan3321.Valid := valid_step _ _ _ valid1555 (by decide +kernel)











theorem valid3327 : plan3327.Valid := valid_step _ _ _ valid1533 (by decide +kernel)



theorem valid3329 : plan3329.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3330 : plan3330.Valid := valid_step _ _ _ valid1536 (by decide +kernel)




























































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























theorem valid5388 : plan5388.Valid := valid_step _ _ _ valid3276 (by decide +kernel)







































































































































theorem valid5456 : plan5456.Valid := valid_step _ _ _ valid3315 (by decide +kernel)

theorem valid5457 : plan5457.Valid := valid_step _ _ _ valid3316 (by decide +kernel)

theorem valid5458 : plan5458.Valid := valid_step _ _ _ valid3317 (by decide +kernel)

theorem valid5459 : plan5459.Valid := valid_step _ _ _ valid3318 (by decide +kernel)

theorem valid5460 : plan5460.Valid := valid_step _ _ _ valid3319 (by decide +kernel)

theorem valid5461 : plan5461.Valid := valid_step _ _ _ valid3320 (by decide +kernel)

theorem valid5462 : plan5462.Valid := valid_step _ _ _ valid3321 (by decide +kernel)





theorem valid5465 : plan5465.Valid := valid_step _ _ _ valid3327 (by decide +kernel)



theorem valid5467 : plan5467.Valid := valid_step _ _ _ valid3329 (by decide +kernel)

theorem valid5468 : plan5468.Valid := valid_step _ _ _ valid3330 (by decide +kernel)








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











































theorem valid3382 : plan3382.Valid := valid_step _ _ _ valid1567 (by decide +kernel)





theorem valid3385 : plan3385.Valid := valid_step _ _ _ valid1570 (by decide +kernel)



theorem valid3387 : plan3387.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3388 : plan3388.Valid := valid_step _ _ _ valid1573 (by decide +kernel)



theorem valid3390 : plan3390.Valid := valid_step _ _ _ valid1575 (by decide +kernel)





theorem valid3393 : plan3393.Valid := valid_step _ _ _ valid1578 (by decide +kernel)






























































































































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



















































































































theorem valid6490 : plan6490.Valid := valid_step _ _ _ valid5456 (by decide +kernel)

theorem valid6491 : plan6491.Valid := valid_step _ _ _ valid5457 (by decide +kernel)

theorem valid6492 : plan6492.Valid := valid_step _ _ _ valid5458 (by decide +kernel)

theorem valid6493 : plan6493.Valid := valid_step _ _ _ valid5459 (by decide +kernel)

theorem valid6494 : plan6494.Valid := valid_step _ _ _ valid5460 (by decide +kernel)

theorem valid6495 : plan6495.Valid := valid_step _ _ _ valid5461 (by decide +kernel)

theorem valid6496 : plan6496.Valid := valid_step _ _ _ valid5462 (by decide +kernel)

theorem valid6497 : plan6497.Valid := valid_step _ _ _ valid5465 (by decide +kernel)

theorem valid6498 : plan6498.Valid := valid_step _ _ _ valid5467 (by decide +kernel)

theorem valid6499 : plan6499.Valid := valid_step _ _ _ valid5468 (by decide +kernel)


























































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















theorem valid5576 : plan5576.Valid := valid_step _ _ _ valid3382 (by decide +kernel)





theorem valid5579 : plan5579.Valid := valid_step _ _ _ valid3385 (by decide +kernel)



theorem valid5581 : plan5581.Valid := valid_step _ _ _ valid3387 (by decide +kernel)

theorem valid5582 : plan5582.Valid := valid_step _ _ _ valid3388 (by decide +kernel)



theorem valid5584 : plan5584.Valid := valid_step _ _ _ valid3390 (by decide +kernel)



theorem valid5586 : plan5586.Valid := valid_step _ _ _ valid3393 (by decide +kernel)




























































































































































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











































































































theorem valid6774 : plan6774.Valid := valid_step _ _ _ valid5576 (by decide +kernel)

theorem valid6775 : plan6775.Valid := valid_step _ _ _ valid5579 (by decide +kernel)

theorem valid6776 : plan6776.Valid := valid_step _ _ _ valid5581 (by decide +kernel)

theorem valid6777 : plan6777.Valid := valid_step _ _ _ valid5582 (by decide +kernel)

theorem valid6778 : plan6778.Valid := valid_step _ _ _ valid5584 (by decide +kernel)

theorem valid6779 : plan6779.Valid := valid_step _ _ _ valid5586 (by decide +kernel)










































































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





















theorem valid6347 : plan6347.Valid := valid_step _ _ _ valid5388 (by decide +kernel)










































































































































































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
theorem t6_240choices : plan6490.choices=[1,2,3,6,7,7].map (options 6 3) := by rfl


theorem t6_240part0 : t6_240jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_240part1 : t6_240jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_240part2 : t6_240jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_240frontier : t6_240root.frontier 2=t6_240jobs := by rfl
theorem t6_240all : t6_240jobs.all (Job.check tree)=true := by
  simp only [t6_240jobs,List.all_append,List.all_nil,t6_240part0,t6_240part1,t6_240part2,Bool.and_self]
theorem t6_240checked : Checked tree [1,2,3,6,7,7] := by
  refine ⟨plan6490,valid6490,t6_240choices,?_⟩
  exact check_of_frontier tree 2 t6_240root t6_240jobs t6_240frontier t6_240all
theorem t6_241choices : plan6491.choices=[1,2,3,6,10,7].map (options 6 3) := by rfl


theorem t6_241part0 : t6_241jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_241part1 : t6_241jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_241part2 : t6_241jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_241frontier : t6_241root.frontier 2=t6_241jobs := by rfl
theorem t6_241all : t6_241jobs.all (Job.check tree)=true := by
  simp only [t6_241jobs,List.all_append,List.all_nil,t6_241part0,t6_241part1,t6_241part2,Bool.and_self]
theorem t6_241checked : Checked tree [1,2,3,6,10,7] := by
  refine ⟨plan6491,valid6491,t6_241choices,?_⟩
  exact check_of_frontier tree 2 t6_241root t6_241jobs t6_241frontier t6_241all
theorem t6_242choices : plan6492.choices=[1,2,3,6,10,10].map (options 6 3) := by rfl


theorem t6_242part0 : t6_242jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_242frontier : t6_242root.frontier 0=t6_242jobs := by rfl
theorem t6_242all : t6_242jobs.all (Job.check tree)=true := by
  simp only [t6_242jobs,List.all_append,List.all_nil,t6_242part0,Bool.and_self]
theorem t6_242checked : Checked tree [1,2,3,6,10,10] := by
  refine ⟨plan6492,valid6492,t6_242choices,?_⟩
  exact check_of_frontier tree 0 t6_242root t6_242jobs t6_242frontier t6_242all
theorem t6_243choices : plan6493.choices=[1,2,3,7,7,7].map (options 6 3) := by rfl


theorem t6_243part0 : t6_243jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_243part1 : t6_243jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_243frontier : t6_243root.frontier 1=t6_243jobs := by rfl
theorem t6_243all : t6_243jobs.all (Job.check tree)=true := by
  simp only [t6_243jobs,List.all_append,List.all_nil,t6_243part0,t6_243part1,Bool.and_self]
theorem t6_243checked : Checked tree [1,2,3,7,7,7] := by
  refine ⟨plan6493,valid6493,t6_243choices,?_⟩
  exact check_of_frontier tree 1 t6_243root t6_243jobs t6_243frontier t6_243all
theorem t6_244choices : plan6494.choices=[1,2,3,10,7,7].map (options 6 3) := by rfl


theorem t6_244part0 : t6_244jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_244part1 : t6_244jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_244part2 : t6_244jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_244frontier : t6_244root.frontier 2=t6_244jobs := by rfl
theorem t6_244all : t6_244jobs.all (Job.check tree)=true := by
  simp only [t6_244jobs,List.all_append,List.all_nil,t6_244part0,t6_244part1,t6_244part2,Bool.and_self]
theorem t6_244checked : Checked tree [1,2,3,10,7,7] := by
  refine ⟨plan6494,valid6494,t6_244choices,?_⟩
  exact check_of_frontier tree 2 t6_244root t6_244jobs t6_244frontier t6_244all
theorem t6_245choices : plan6495.choices=[1,2,3,10,10,7].map (options 6 3) := by rfl


theorem t6_245part0 : t6_245jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_245part1 : t6_245jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_245frontier : t6_245root.frontier 1=t6_245jobs := by rfl
theorem t6_245all : t6_245jobs.all (Job.check tree)=true := by
  simp only [t6_245jobs,List.all_append,List.all_nil,t6_245part0,t6_245part1,Bool.and_self]
theorem t6_245checked : Checked tree [1,2,3,10,10,7] := by
  refine ⟨plan6495,valid6495,t6_245choices,?_⟩
  exact check_of_frontier tree 1 t6_245root t6_245jobs t6_245frontier t6_245all
theorem t6_246choices : plan6496.choices=[1,2,3,10,10,10].map (options 6 3) := by rfl


theorem t6_246part0 : t6_246jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_246frontier : t6_246root.frontier 0=t6_246jobs := by rfl
theorem t6_246all : t6_246jobs.all (Job.check tree)=true := by
  simp only [t6_246jobs,List.all_append,List.all_nil,t6_246part0,Bool.and_self]
theorem t6_246checked : Checked tree [1,2,3,10,10,10] := by
  refine ⟨plan6496,valid6496,t6_246choices,?_⟩
  exact check_of_frontier tree 0 t6_246root t6_246jobs t6_246frontier t6_246all
theorem t6_247choices : plan6347.choices=[1,2,5,3,3,7].map (options 6 2) := by rfl


theorem t6_247part0 : t6_247jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_247frontier : t6_247root.frontier 0=t6_247jobs := by rfl
theorem t6_247all : t6_247jobs.all (Job.check tree)=true := by
  simp only [t6_247jobs,List.all_append,List.all_nil,t6_247part0,Bool.and_self]
theorem t6_247checked : Checked tree [1,2,5,3,3,7] := by
  refine ⟨plan6347,valid6347,t6_247choices,?_⟩
  exact check_of_frontier tree 0 t6_247root t6_247jobs t6_247frontier t6_247all
theorem t6_248choices : plan6497.choices=[1,2,5,3,6,7].map (options 6 3) := by rfl


theorem t6_248part0 : t6_248jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_248frontier : t6_248root.frontier 0=t6_248jobs := by rfl
theorem t6_248all : t6_248jobs.all (Job.check tree)=true := by
  simp only [t6_248jobs,List.all_append,List.all_nil,t6_248part0,Bool.and_self]
theorem t6_248checked : Checked tree [1,2,5,3,6,7] := by
  refine ⟨plan6497,valid6497,t6_248choices,?_⟩
  exact check_of_frontier tree 0 t6_248root t6_248jobs t6_248frontier t6_248all
theorem t6_249choices : plan6498.choices=[1,2,5,3,7,7].map (options 6 3) := by rfl


theorem t6_249part0 : t6_249jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_249part1 : t6_249jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_249frontier : t6_249root.frontier 1=t6_249jobs := by rfl
theorem t6_249all : t6_249jobs.all (Job.check tree)=true := by
  simp only [t6_249jobs,List.all_append,List.all_nil,t6_249part0,t6_249part1,Bool.and_self]
theorem t6_249checked : Checked tree [1,2,5,3,7,7] := by
  refine ⟨plan6498,valid6498,t6_249choices,?_⟩
  exact check_of_frontier tree 1 t6_249root t6_249jobs t6_249frontier t6_249all
theorem t6_250choices : plan6499.choices=[1,2,5,3,10,7].map (options 6 3) := by rfl


theorem t6_250part0 : t6_250jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_250frontier : t6_250root.frontier 0=t6_250jobs := by rfl
theorem t6_250all : t6_250jobs.all (Job.check tree)=true := by
  simp only [t6_250jobs,List.all_append,List.all_nil,t6_250part0,Bool.and_self]
theorem t6_250checked : Checked tree [1,2,5,3,10,7] := by
  refine ⟨plan6499,valid6499,t6_250choices,?_⟩
  exact check_of_frontier tree 0 t6_250root t6_250jobs t6_250frontier t6_250all
theorem t6_251choices : plan6774.choices=[1,2,5,5,7,7].map (options 6 4) := by rfl


theorem t6_251part0 : t6_251jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_251frontier : t6_251root.frontier 0=t6_251jobs := by rfl
theorem t6_251all : t6_251jobs.all (Job.check tree)=true := by
  simp only [t6_251jobs,List.all_append,List.all_nil,t6_251part0,Bool.and_self]
theorem t6_251checked : Checked tree [1,2,5,5,7,7] := by
  refine ⟨plan6774,valid6774,t6_251choices,?_⟩
  exact check_of_frontier tree 0 t6_251root t6_251jobs t6_251frontier t6_251all
theorem t6_252choices : plan6775.choices=[1,2,5,6,6,7].map (options 6 4) := by rfl


theorem t6_252part0 : t6_252jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_252frontier : t6_252root.frontier 0=t6_252jobs := by rfl
theorem t6_252all : t6_252jobs.all (Job.check tree)=true := by
  simp only [t6_252jobs,List.all_append,List.all_nil,t6_252part0,Bool.and_self]
theorem t6_252checked : Checked tree [1,2,5,6,6,7] := by
  refine ⟨plan6775,valid6775,t6_252choices,?_⟩
  exact check_of_frontier tree 0 t6_252root t6_252jobs t6_252frontier t6_252all
theorem t6_253choices : plan6776.choices=[1,2,5,6,7,7].map (options 6 4) := by rfl


theorem t6_253part0 : t6_253jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_253frontier : t6_253root.frontier 0=t6_253jobs := by rfl
theorem t6_253all : t6_253jobs.all (Job.check tree)=true := by
  simp only [t6_253jobs,List.all_append,List.all_nil,t6_253part0,Bool.and_self]
theorem t6_253checked : Checked tree [1,2,5,6,7,7] := by
  refine ⟨plan6776,valid6776,t6_253choices,?_⟩
  exact check_of_frontier tree 0 t6_253root t6_253jobs t6_253frontier t6_253all
theorem t6_254choices : plan6777.choices=[1,2,5,6,10,7].map (options 6 4) := by rfl


theorem t6_254part0 : t6_254jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_254frontier : t6_254root.frontier 0=t6_254jobs := by rfl
theorem t6_254all : t6_254jobs.all (Job.check tree)=true := by
  simp only [t6_254jobs,List.all_append,List.all_nil,t6_254part0,Bool.and_self]
theorem t6_254checked : Checked tree [1,2,5,6,10,7] := by
  refine ⟨plan6777,valid6777,t6_254choices,?_⟩
  exact check_of_frontier tree 0 t6_254root t6_254jobs t6_254frontier t6_254all
theorem t6_255choices : plan6778.choices=[1,2,5,7,7,7].map (options 6 4) := by rfl


theorem t6_255part0 : t6_255jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_255frontier : t6_255root.frontier 0=t6_255jobs := by rfl
theorem t6_255all : t6_255jobs.all (Job.check tree)=true := by
  simp only [t6_255jobs,List.all_append,List.all_nil,t6_255part0,Bool.and_self]
theorem t6_255checked : Checked tree [1,2,5,7,7,7] := by
  refine ⟨plan6778,valid6778,t6_255choices,?_⟩
  exact check_of_frontier tree 0 t6_255root t6_255jobs t6_255frontier t6_255all
theorem t6_256choices : plan6779.choices=[1,2,5,9,7,7].map (options 6 4) := by rfl


theorem t6_256part0 : t6_256jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_256frontier : t6_256root.frontier 0=t6_256jobs := by rfl
theorem t6_256all : t6_256jobs.all (Job.check tree)=true := by
  simp only [t6_256jobs,List.all_append,List.all_nil,t6_256part0,Bool.and_self]
theorem t6_256checked : Checked tree [1,2,5,9,7,7] := by
  refine ⟨plan6779,valid6779,t6_256choices,?_⟩
  exact check_of_frontier tree 0 t6_256root t6_256jobs t6_256frontier t6_256all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks050 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_245checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_246checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_247checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_248checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_249checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_250checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_251checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_252checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_253checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_254checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_255checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_256checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_240checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_241checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_242checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_243checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_244checked⟩
