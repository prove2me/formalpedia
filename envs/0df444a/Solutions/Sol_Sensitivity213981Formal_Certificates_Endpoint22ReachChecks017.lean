-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks017
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:56:27.554224+00:00
-- url     : https://prove2.me/submissions/339b0df7-d3b7-4305-8034-190151bc2180

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans040
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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













































































































































































theorem valid87 : plan87.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid90 : plan90.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid91 : plan91.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid93 : plan93.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid96 : plan96.Valid := valid_step _ _ _ valid0 (by decide +kernel)
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

theorem valid97 : plan97.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid99 : plan99.Valid := valid_step _ _ _ valid0 (by decide +kernel)







theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid105 : plan105.Valid := valid_step _ _ _ valid0 (by decide +kernel)














































































































































































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



























































































































theorem valid446 : plan446.Valid := valid_step _ _ _ valid87 (by decide +kernel)















theorem valid454 : plan454.Valid := valid_step _ _ _ valid90 (by decide +kernel)

theorem valid455 : plan455.Valid := valid_step _ _ _ valid91 (by decide +kernel)

theorem valid456 : plan456.Valid := valid_step _ _ _ valid93 (by decide +kernel)































theorem valid472 : plan472.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid473 : plan473.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid474 : plan474.Valid := valid_step _ _ _ valid99 (by decide +kernel)

theorem valid475 : plan475.Valid := valid_step _ _ _ valid97 (by decide +kernel)










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

theorem valid481 : plan481.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid482 : plan482.Valid := valid_step _ _ _ valid99 (by decide +kernel)





























theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)











theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)
















































































































































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



theorem valid1250 : plan1250.Valid := valid_step _ _ _ valid446 (by decide +kernel)





























theorem valid1265 : plan1265.Valid := valid_step _ _ _ valid454 (by decide +kernel)

theorem valid1266 : plan1266.Valid := valid_step _ _ _ valid455 (by decide +kernel)

theorem valid1267 : plan1267.Valid := valid_step _ _ _ valid456 (by decide +kernel)



































































theorem valid1301 : plan1301.Valid := valid_step _ _ _ valid472 (by decide +kernel)

theorem valid1302 : plan1302.Valid := valid_step _ _ _ valid473 (by decide +kernel)

theorem valid1303 : plan1303.Valid := valid_step _ _ _ valid474 (by decide +kernel)

theorem valid1304 : plan1304.Valid := valid_step _ _ _ valid475 (by decide +kernel)

theorem valid1305 : plan1305.Valid := valid_step _ _ _ valid481 (by decide +kernel)

theorem valid1306 : plan1306.Valid := valid_step _ _ _ valid482 (by decide +kernel)












































































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















































theorem valid2520 : plan2520.Valid := valid_step _ _ _ valid1250 (by decide +kernel)



























































theorem valid2550 : plan2550.Valid := valid_step _ _ _ valid1265 (by decide +kernel)

theorem valid2551 : plan2551.Valid := valid_step _ _ _ valid1266 (by decide +kernel)

theorem valid2552 : plan2552.Valid := valid_step _ _ _ valid1267 (by decide +kernel)
















































































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















































theorem valid3672 : plan3672.Valid := valid_step _ _ _ valid2520 (by decide +kernel)









































































































































theorem valid3741 : plan3741.Valid := valid_step _ _ _ valid2550 (by decide +kernel)

theorem valid3742 : plan3742.Valid := valid_step _ _ _ valid2551 (by decide +kernel)

theorem valid3743 : plan3743.Valid := valid_step _ _ _ valid2552 (by decide +kernel)


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





































































































theorem valid1395 : plan1395.Valid := valid_step _ _ _ valid504 (by decide +kernel)

theorem valid1396 : plan1396.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1397 : plan1397.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1398 : plan1398.Valid := valid_step _ _ _ valid504 (by decide +kernel)




















































































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











































































theorem valid2630 : plan2630.Valid := valid_step _ _ _ valid1301 (by decide +kernel)

theorem valid2631 : plan2631.Valid := valid_step _ _ _ valid1302 (by decide +kernel)

theorem valid2632 : plan2632.Valid := valid_step _ _ _ valid1303 (by decide +kernel)

theorem valid2633 : plan2633.Valid := valid_step _ _ _ valid1304 (by decide +kernel)

theorem valid2634 : plan2634.Valid := valid_step _ _ _ valid1305 (by decide +kernel)

theorem valid2635 : plan2635.Valid := valid_step _ _ _ valid1306 (by decide +kernel)










































































































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











































































































































theorem valid2758 : plan2758.Valid := valid_step _ _ _ valid1395 (by decide +kernel)

theorem valid2759 : plan2759.Valid := valid_step _ _ _ valid1396 (by decide +kernel)

theorem valid2760 : plan2760.Valid := valid_step _ _ _ valid1397 (by decide +kernel)

theorem valid2761 : plan2761.Valid := valid_step _ _ _ valid1398 (by decide +kernel)














































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















































































































































































theorem valid3928 : plan3928.Valid := valid_step _ _ _ valid2630 (by decide +kernel)

theorem valid3929 : plan3929.Valid := valid_step _ _ _ valid2631 (by decide +kernel)

theorem valid3930 : plan3930.Valid := valid_step _ _ _ valid2632 (by decide +kernel)

theorem valid3931 : plan3931.Valid := valid_step _ _ _ valid2633 (by decide +kernel)

theorem valid3932 : plan3932.Valid := valid_step _ _ _ valid2634 (by decide +kernel)

theorem valid3933 : plan3933.Valid := valid_step _ _ _ valid2635 (by decide +kernel)






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

















































































theorem valid4265 : plan4265.Valid := valid_step _ _ _ valid2758 (by decide +kernel)

theorem valid4266 : plan4266.Valid := valid_step _ _ _ valid2759 (by decide +kernel)

theorem valid4267 : plan4267.Valid := valid_step _ _ _ valid2760 (by decide +kernel)

theorem valid4268 : plan4268.Valid := valid_step _ _ _ valid2761 (by decide +kernel)








































































































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
theorem t5_728choices : plan4265.choices=[2,2,9,10,10].map (options 5 3) := by rfl


theorem t5_728part0 : t5_728jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_728frontier : t5_728root.frontier 0=t5_728jobs := by rfl
theorem t5_728all : t5_728jobs.all (Job.check tree)=true := by
  simp only [t5_728jobs,List.all_append,List.all_nil,t5_728part0,Bool.and_self]
theorem t5_728checked : Checked tree [2,2,9,10,10] := by
  refine ⟨plan4265,valid4265,t5_728choices,?_⟩
  exact check_of_frontier tree 0 t5_728root t5_728jobs t5_728frontier t5_728all
theorem t5_729choices : plan4266.choices=[2,2,10,7,7].map (options 5 3) := by rfl


theorem t5_729part0 : t5_729jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_729frontier : t5_729root.frontier 0=t5_729jobs := by rfl
theorem t5_729all : t5_729jobs.all (Job.check tree)=true := by
  simp only [t5_729jobs,List.all_append,List.all_nil,t5_729part0,Bool.and_self]
theorem t5_729checked : Checked tree [2,2,10,7,7] := by
  refine ⟨plan4266,valid4266,t5_729choices,?_⟩
  exact check_of_frontier tree 0 t5_729root t5_729jobs t5_729frontier t5_729all
theorem t5_730choices : plan4267.choices=[2,2,10,10,7].map (options 5 3) := by rfl


theorem t5_730part0 : t5_730jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_730frontier : t5_730root.frontier 0=t5_730jobs := by rfl
theorem t5_730all : t5_730jobs.all (Job.check tree)=true := by
  simp only [t5_730jobs,List.all_append,List.all_nil,t5_730part0,Bool.and_self]
theorem t5_730checked : Checked tree [2,2,10,10,7] := by
  refine ⟨plan4267,valid4267,t5_730choices,?_⟩
  exact check_of_frontier tree 0 t5_730root t5_730jobs t5_730frontier t5_730all
theorem t5_731choices : plan4268.choices=[2,2,10,10,10].map (options 5 3) := by rfl


theorem t5_731part0 : t5_731jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_731frontier : t5_731root.frontier 0=t5_731jobs := by rfl
theorem t5_731all : t5_731jobs.all (Job.check tree)=true := by
  simp only [t5_731jobs,List.all_append,List.all_nil,t5_731part0,Bool.and_self]
theorem t5_731checked : Checked tree [2,2,10,10,10] := by
  refine ⟨plan4268,valid4268,t5_731choices,?_⟩
  exact check_of_frontier tree 0 t5_731root t5_731jobs t5_731frontier t5_731all
theorem t5_732choices : plan3672.choices=[2,3,3,3,3].map (options 5 0) := by rfl


theorem t5_732part0 : t5_732jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_732frontier : t5_732root.frontier 0=t5_732jobs := by rfl
theorem t5_732all : t5_732jobs.all (Job.check tree)=true := by
  simp only [t5_732jobs,List.all_append,List.all_nil,t5_732part0,Bool.and_self]
theorem t5_732checked : Checked tree [2,3,3,3,3] := by
  refine ⟨plan3672,valid3672,t5_732choices,?_⟩
  exact check_of_frontier tree 0 t5_732root t5_732jobs t5_732frontier t5_732all
theorem t5_733choices : plan3741.choices=[2,3,3,3,6].map (options 5 1) := by rfl


theorem t5_733part0 : t5_733jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_733frontier : t5_733root.frontier 0=t5_733jobs := by rfl
theorem t5_733all : t5_733jobs.all (Job.check tree)=true := by
  simp only [t5_733jobs,List.all_append,List.all_nil,t5_733part0,Bool.and_self]
theorem t5_733checked : Checked tree [2,3,3,3,6] := by
  refine ⟨plan3741,valid3741,t5_733choices,?_⟩
  exact check_of_frontier tree 0 t5_733root t5_733jobs t5_733frontier t5_733all
theorem t5_734choices : plan3742.choices=[2,3,3,3,7].map (options 5 1) := by rfl


theorem t5_734part0 : t5_734jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_734frontier : t5_734root.frontier 0=t5_734jobs := by rfl
theorem t5_734all : t5_734jobs.all (Job.check tree)=true := by
  simp only [t5_734jobs,List.all_append,List.all_nil,t5_734part0,Bool.and_self]
theorem t5_734checked : Checked tree [2,3,3,3,7] := by
  refine ⟨plan3742,valid3742,t5_734choices,?_⟩
  exact check_of_frontier tree 0 t5_734root t5_734jobs t5_734frontier t5_734all
theorem t5_735choices : plan3743.choices=[2,3,3,3,10].map (options 5 1) := by rfl


theorem t5_735part0 : t5_735jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_735frontier : t5_735root.frontier 0=t5_735jobs := by rfl
theorem t5_735all : t5_735jobs.all (Job.check tree)=true := by
  simp only [t5_735jobs,List.all_append,List.all_nil,t5_735part0,Bool.and_self]
theorem t5_735checked : Checked tree [2,3,3,3,10] := by
  refine ⟨plan3743,valid3743,t5_735choices,?_⟩
  exact check_of_frontier tree 0 t5_735root t5_735jobs t5_735frontier t5_735all
theorem t5_736choices : plan3928.choices=[2,3,3,6,6].map (options 5 2) := by rfl


theorem t5_736part0 : t5_736jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_736part1 : t5_736jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_736frontier : t5_736root.frontier 1=t5_736jobs := by rfl
theorem t5_736all : t5_736jobs.all (Job.check tree)=true := by
  simp only [t5_736jobs,List.all_append,List.all_nil,t5_736part0,t5_736part1,Bool.and_self]
theorem t5_736checked : Checked tree [2,3,3,6,6] := by
  refine ⟨plan3928,valid3928,t5_736choices,?_⟩
  exact check_of_frontier tree 1 t5_736root t5_736jobs t5_736frontier t5_736all
theorem t5_737choices : plan3929.choices=[2,3,3,6,7].map (options 5 2) := by rfl


theorem t5_737part0 : t5_737jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_737part1 : t5_737jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_737part2 : t5_737jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_737part3 : t5_737jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_737frontier : t5_737root.frontier 1=t5_737jobs := by rfl
theorem t5_737all : t5_737jobs.all (Job.check tree)=true := by
  simp only [t5_737jobs,List.all_append,List.all_nil,t5_737part0,t5_737part1,t5_737part2,t5_737part3,Bool.and_self]
theorem t5_737checked : Checked tree [2,3,3,6,7] := by
  refine ⟨plan3929,valid3929,t5_737choices,?_⟩
  exact check_of_frontier tree 1 t5_737root t5_737jobs t5_737frontier t5_737all
theorem t5_738choices : plan3930.choices=[2,3,3,6,10].map (options 5 2) := by rfl


theorem t5_738part0 : t5_738jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_738part1 : t5_738jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_738part2 : t5_738jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_738frontier : t5_738root.frontier 1=t5_738jobs := by rfl
theorem t5_738all : t5_738jobs.all (Job.check tree)=true := by
  simp only [t5_738jobs,List.all_append,List.all_nil,t5_738part0,t5_738part1,t5_738part2,Bool.and_self]
theorem t5_738checked : Checked tree [2,3,3,6,10] := by
  refine ⟨plan3930,valid3930,t5_738choices,?_⟩
  exact check_of_frontier tree 1 t5_738root t5_738jobs t5_738frontier t5_738all
theorem t5_739choices : plan3931.choices=[2,3,3,7,7].map (options 5 2) := by rfl


theorem t5_739part0 : t5_739jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_739part1 : t5_739jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_739part2 : t5_739jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_739frontier : t5_739root.frontier 1=t5_739jobs := by rfl
theorem t5_739all : t5_739jobs.all (Job.check tree)=true := by
  simp only [t5_739jobs,List.all_append,List.all_nil,t5_739part0,t5_739part1,t5_739part2,Bool.and_self]
theorem t5_739checked : Checked tree [2,3,3,7,7] := by
  refine ⟨plan3931,valid3931,t5_739choices,?_⟩
  exact check_of_frontier tree 1 t5_739root t5_739jobs t5_739frontier t5_739all
theorem t5_740choices : plan3932.choices=[2,3,3,10,7].map (options 5 2) := by rfl


theorem t5_740part0 : t5_740jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_740part1 : t5_740jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_740part2 : t5_740jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_740part3 : t5_740jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_740frontier : t5_740root.frontier 1=t5_740jobs := by rfl
theorem t5_740all : t5_740jobs.all (Job.check tree)=true := by
  simp only [t5_740jobs,List.all_append,List.all_nil,t5_740part0,t5_740part1,t5_740part2,t5_740part3,Bool.and_self]
theorem t5_740checked : Checked tree [2,3,3,10,7] := by
  refine ⟨plan3932,valid3932,t5_740choices,?_⟩
  exact check_of_frontier tree 1 t5_740root t5_740jobs t5_740frontier t5_740all
theorem t5_741choices : plan3933.choices=[2,3,3,10,10].map (options 5 2) := by rfl


theorem t5_741part0 : t5_741jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_741part1 : t5_741jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_741frontier : t5_741root.frontier 1=t5_741jobs := by rfl
theorem t5_741all : t5_741jobs.all (Job.check tree)=true := by
  simp only [t5_741jobs,List.all_append,List.all_nil,t5_741part0,t5_741part1,Bool.and_self]
theorem t5_741checked : Checked tree [2,3,3,10,10] := by
  refine ⟨plan3933,valid3933,t5_741choices,?_⟩
  exact check_of_frontier tree 1 t5_741root t5_741jobs t5_741frontier t5_741all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks017 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_738checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_739checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_740checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_741checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_729checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_730checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_731checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_732checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_733checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_734checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_735checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_736checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_737checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_728checked⟩
