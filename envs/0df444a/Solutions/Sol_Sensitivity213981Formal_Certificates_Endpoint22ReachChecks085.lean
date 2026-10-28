-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks085
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:24:20.833988+00:00
-- url     : https://prove2.me/submissions/68762a11-b5a1-4d3e-9d3a-9cbf88dd4477

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
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



















































theorem valid122 : plan122.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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

































































































































theorem valid545 : plan545.Valid := valid_step _ _ _ valid122 (by decide +kernel)





















theorem valid556 : plan556.Valid := valid_step _ _ _ valid127 (by decide +kernel)

theorem valid557 : plan557.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid558 : plan558.Valid := valid_step _ _ _ valid129 (by decide +kernel)



















theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)





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





















































































































































theorem valid1515 : plan1515.Valid := valid_step _ _ _ valid545 (by decide +kernel)



























theorem valid1529 : plan1529.Valid := valid_step _ _ _ valid556 (by decide +kernel)

theorem valid1530 : plan1530.Valid := valid_step _ _ _ valid557 (by decide +kernel)

theorem valid1531 : plan1531.Valid := valid_step _ _ _ valid558 (by decide +kernel)










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













































theorem valid1559 : plan1559.Valid := valid_step _ _ _ valid568 (by decide +kernel)









































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



















theorem valid3274 : plan3274.Valid := valid_step _ _ _ valid1515 (by decide +kernel)

































































































theorem valid3323 : plan3323.Valid := valid_step _ _ _ valid1529 (by decide +kernel)

theorem valid3324 : plan3324.Valid := valid_step _ _ _ valid1530 (by decide +kernel)

theorem valid3325 : plan3325.Valid := valid_step _ _ _ valid1531 (by decide +kernel)






































































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





























































theorem valid5407 : plan5407.Valid := valid_step _ _ _ valid3274 (by decide +kernel)


































































































































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









theorem valid3374 : plan3374.Valid := valid_step _ _ _ valid1559 (by decide +kernel)




































































































































































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













































































theorem valid5511 : plan5511.Valid := valid_step _ _ _ valid3323 (by decide +kernel)

theorem valid5512 : plan5512.Valid := valid_step _ _ _ valid3324 (by decide +kernel)

theorem valid5513 : plan5513.Valid := valid_step _ _ _ valid3325 (by decide +kernel)














































































































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





















theorem valid5675 : plan5675.Valid := valid_step _ _ _ valid3367 (by decide +kernel)

theorem valid5676 : plan5676.Valid := valid_step _ _ _ valid3368 (by decide +kernel)

theorem valid5677 : plan5677.Valid := valid_step _ _ _ valid3369 (by decide +kernel)







theorem valid5681 : plan5681.Valid := valid_step _ _ _ valid3374 (by decide +kernel)






























































































































































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





















































































































theorem valid6395 : plan6395.Valid := valid_step _ _ _ valid5407 (by decide +kernel)










































































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

































































































































theorem valid6593 : plan6593.Valid := valid_step _ _ _ valid5511 (by decide +kernel)

theorem valid6594 : plan6594.Valid := valid_step _ _ _ valid5512 (by decide +kernel)

theorem valid6595 : plan6595.Valid := valid_step _ _ _ valid5513 (by decide +kernel)


























































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















































theorem valid6936 : plan6936.Valid := valid_step _ _ _ valid5675 (by decide +kernel)

theorem valid6937 : plan6937.Valid := valid_step _ _ _ valid5676 (by decide +kernel)

theorem valid6938 : plan6938.Valid := valid_step _ _ _ valid5677 (by decide +kernel)

theorem valid6939 : plan6939.Valid := valid_step _ _ _ valid5681 (by decide +kernel)










































































































































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
theorem t6_683choices : plan6936.choices=[2,5,3,10,7,7].map (options 6 4) := by rfl


theorem t6_683part0 : t6_683jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_683part1 : t6_683jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_683part2 : t6_683jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_683part3 : t6_683jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_683part4 : t6_683jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_683part5 : t6_683jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_683part6 : t6_683jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_683part7 : t6_683jobs7.all (Job.check tree)=true := by decide +kernel

theorem t6_683part8 : t6_683jobs8.all (Job.check tree)=true := by decide +kernel

theorem t6_683part9 : t6_683jobs9.all (Job.check tree)=true := by decide +kernel

theorem t6_683part10 : t6_683jobs10.all (Job.check tree)=true := by decide +kernel

theorem t6_683frontier : t6_683root.frontier 2=t6_683jobs := by rfl
theorem t6_683all : t6_683jobs.all (Job.check tree)=true := by
  simp only [t6_683jobs,List.all_append,List.all_nil,t6_683part0,t6_683part1,t6_683part2,t6_683part3,t6_683part4,t6_683part5,t6_683part6,t6_683part7,t6_683part8,t6_683part9,t6_683part10,Bool.and_self]
theorem t6_683checked : Checked tree [2,5,3,10,7,7] := by
  refine ⟨plan6936,valid6936,t6_683choices,?_⟩
  exact check_of_frontier tree 2 t6_683root t6_683jobs t6_683frontier t6_683all
theorem t6_684choices : plan6937.choices=[2,5,3,10,10,7].map (options 6 4) := by rfl


theorem t6_684part0 : t6_684jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_684part1 : t6_684jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_684part2 : t6_684jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_684part3 : t6_684jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_684part4 : t6_684jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_684part5 : t6_684jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_684frontier : t6_684root.frontier 2=t6_684jobs := by rfl
theorem t6_684all : t6_684jobs.all (Job.check tree)=true := by
  simp only [t6_684jobs,List.all_append,List.all_nil,t6_684part0,t6_684part1,t6_684part2,t6_684part3,t6_684part4,t6_684part5,Bool.and_self]
theorem t6_684checked : Checked tree [2,5,3,10,10,7] := by
  refine ⟨plan6937,valid6937,t6_684choices,?_⟩
  exact check_of_frontier tree 2 t6_684root t6_684jobs t6_684frontier t6_684all
theorem t6_685choices : plan6938.choices=[2,5,3,10,10,10].map (options 6 4) := by rfl


theorem t6_685part0 : t6_685jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_685frontier : t6_685root.frontier 0=t6_685jobs := by rfl
theorem t6_685all : t6_685jobs.all (Job.check tree)=true := by
  simp only [t6_685jobs,List.all_append,List.all_nil,t6_685part0,Bool.and_self]
theorem t6_685checked : Checked tree [2,5,3,10,10,10] := by
  refine ⟨plan6938,valid6938,t6_685choices,?_⟩
  exact check_of_frontier tree 0 t6_685root t6_685jobs t6_685frontier t6_685all
theorem t6_686choices : plan6395.choices=[2,5,5,3,3,3].map (options 6 2) := by rfl


theorem t6_686part0 : t6_686jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_686frontier : t6_686root.frontier 0=t6_686jobs := by rfl
theorem t6_686all : t6_686jobs.all (Job.check tree)=true := by
  simp only [t6_686jobs,List.all_append,List.all_nil,t6_686part0,Bool.and_self]
theorem t6_686checked : Checked tree [2,5,5,3,3,3] := by
  refine ⟨plan6395,valid6395,t6_686choices,?_⟩
  exact check_of_frontier tree 0 t6_686root t6_686jobs t6_686frontier t6_686all
theorem t6_687choices : plan6593.choices=[2,5,5,3,3,6].map (options 6 3) := by rfl


theorem t6_687part0 : t6_687jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_687frontier : t6_687root.frontier 0=t6_687jobs := by rfl
theorem t6_687all : t6_687jobs.all (Job.check tree)=true := by
  simp only [t6_687jobs,List.all_append,List.all_nil,t6_687part0,Bool.and_self]
theorem t6_687checked : Checked tree [2,5,5,3,3,6] := by
  refine ⟨plan6593,valid6593,t6_687choices,?_⟩
  exact check_of_frontier tree 0 t6_687root t6_687jobs t6_687frontier t6_687all
theorem t6_688choices : plan6594.choices=[2,5,5,3,3,7].map (options 6 3) := by rfl


theorem t6_688part0 : t6_688jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_688part1 : t6_688jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_688frontier : t6_688root.frontier 1=t6_688jobs := by rfl
theorem t6_688all : t6_688jobs.all (Job.check tree)=true := by
  simp only [t6_688jobs,List.all_append,List.all_nil,t6_688part0,t6_688part1,Bool.and_self]
theorem t6_688checked : Checked tree [2,5,5,3,3,7] := by
  refine ⟨plan6594,valid6594,t6_688choices,?_⟩
  exact check_of_frontier tree 1 t6_688root t6_688jobs t6_688frontier t6_688all
theorem t6_689choices : plan6595.choices=[2,5,5,3,3,10].map (options 6 3) := by rfl


theorem t6_689part0 : t6_689jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_689frontier : t6_689root.frontier 0=t6_689jobs := by rfl
theorem t6_689all : t6_689jobs.all (Job.check tree)=true := by
  simp only [t6_689jobs,List.all_append,List.all_nil,t6_689part0,Bool.and_self]
theorem t6_689checked : Checked tree [2,5,5,3,3,10] := by
  refine ⟨plan6595,valid6595,t6_689choices,?_⟩
  exact check_of_frontier tree 0 t6_689root t6_689jobs t6_689frontier t6_689all
theorem t6_690choices : plan6939.choices=[2,5,5,3,6,6].map (options 6 4) := by rfl


theorem t6_690part0 : t6_690jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_690frontier : t6_690root.frontier 0=t6_690jobs := by rfl
theorem t6_690all : t6_690jobs.all (Job.check tree)=true := by
  simp only [t6_690jobs,List.all_append,List.all_nil,t6_690part0,Bool.and_self]
theorem t6_690checked : Checked tree [2,5,5,3,6,6] := by
  refine ⟨plan6939,valid6939,t6_690choices,?_⟩
  exact check_of_frontier tree 0 t6_690root t6_690jobs t6_690frontier t6_690all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks085 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_687checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_688checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_689checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_690checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_683checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_684checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_685checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_686checked⟩
