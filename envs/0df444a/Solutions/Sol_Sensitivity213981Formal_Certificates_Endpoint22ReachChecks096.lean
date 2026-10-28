-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks096
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:34:44.580437+00:00
-- url     : https://prove2.me/submissions/55ed999c-3565-4a47-b5f2-48660bbbe5c0

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks096
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks096
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans061
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
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



















































theorem valid122 : plan122.Valid := valid_step _ _ _ valid0 (by decide +kernel)









theorem valid127 : plan127.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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



theorem valid578 : plan578.Valid := valid_step _ _ _ valid134 (by decide +kernel)

theorem valid579 : plan579.Valid := valid_step _ _ _ valid134 (by decide +kernel)

theorem valid580 : plan580.Valid := valid_step _ _ _ valid135 (by decide +kernel)
























































































































































































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

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)












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

theorem valid1560 : plan1560.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1561 : plan1561.Valid := valid_step _ _ _ valid570 (by decide +kernel)







































































theorem valid1597 : plan1597.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1598 : plan1598.Valid := valid_step _ _ _ valid580 (by decide +kernel)

theorem valid1599 : plan1599.Valid := valid_step _ _ _ valid578 (by decide +kernel)









theorem valid1604 : plan1604.Valid := valid_step _ _ _ valid578 (by decide +kernel)

theorem valid1605 : plan1605.Valid := valid_step _ _ _ valid579 (by decide +kernel)

theorem valid1606 : plan1606.Valid := valid_step _ _ _ valid580 (by decide +kernel)




















































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



























theorem valid3278 : plan3278.Valid := valid_step _ _ _ valid1515 (by decide +kernel)

















































































































theorem valid3335 : plan3335.Valid := valid_step _ _ _ valid1529 (by decide +kernel)

theorem valid3336 : plan3336.Valid := valid_step _ _ _ valid1530 (by decide +kernel)

theorem valid3337 : plan3337.Valid := valid_step _ _ _ valid1531 (by decide +kernel)














































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











































































theorem valid5414 : plan5414.Valid := valid_step _ _ _ valid3278 (by decide +kernel)




















































































































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









































































































theorem valid3413 : plan3413.Valid := valid_step _ _ _ valid1559 (by decide +kernel)

theorem valid3414 : plan3414.Valid := valid_step _ _ _ valid1560 (by decide +kernel)

theorem valid3415 : plan3415.Valid := valid_step _ _ _ valid1561 (by decide +kernel)


















































































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

























































































































theorem valid5533 : plan5533.Valid := valid_step _ _ _ valid3335 (by decide +kernel)

theorem valid5534 : plan5534.Valid := valid_step _ _ _ valid3336 (by decide +kernel)

theorem valid5535 : plan5535.Valid := valid_step _ _ _ valid3337 (by decide +kernel)


































































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













































theorem valid3479 : plan3479.Valid := valid_step _ _ _ valid1597 (by decide +kernel)

theorem valid3480 : plan3480.Valid := valid_step _ _ _ valid1598 (by decide +kernel)

theorem valid3481 : plan3481.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3482 : plan3482.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3483 : plan3483.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3484 : plan3484.Valid := valid_step _ _ _ valid1606 (by decide +kernel)

theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)






































































































































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









































































































































theorem valid5733 : plan5733.Valid := valid_step _ _ _ valid3413 (by decide +kernel)

theorem valid5734 : plan5734.Valid := valid_step _ _ _ valid3414 (by decide +kernel)

theorem valid5735 : plan5735.Valid := valid_step _ _ _ valid3415 (by decide +kernel)


















































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









































































































































































theorem valid5941 : plan5941.Valid := valid_step _ _ _ valid3479 (by decide +kernel)

theorem valid5942 : plan5942.Valid := valid_step _ _ _ valid3480 (by decide +kernel)

theorem valid5943 : plan5943.Valid := valid_step _ _ _ valid3481 (by decide +kernel)

theorem valid5944 : plan5944.Valid := valid_step _ _ _ valid3482 (by decide +kernel)

theorem valid5945 : plan5945.Valid := valid_step _ _ _ valid3483 (by decide +kernel)

theorem valid5946 : plan5946.Valid := valid_step _ _ _ valid3484 (by decide +kernel)

theorem valid5947 : plan5947.Valid := valid_step _ _ _ valid3485 (by decide +kernel)










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































































































































theorem valid6400 : plan6400.Valid := valid_step _ _ _ valid5414 (by decide +kernel)
































































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

























































































































































theorem valid6605 : plan6605.Valid := valid_step _ _ _ valid5533 (by decide +kernel)

theorem valid6606 : plan6606.Valid := valid_step _ _ _ valid5534 (by decide +kernel)

theorem valid6607 : plan6607.Valid := valid_step _ _ _ valid5535 (by decide +kernel)


































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















































































































































































theorem valid7384 : plan7384.Valid := valid_step _ _ _ valid5941 (by decide +kernel)

theorem valid7385 : plan7385.Valid := valid_step _ _ _ valid5942 (by decide +kernel)

theorem valid7386 : plan7386.Valid := valid_step _ _ _ valid5943 (by decide +kernel)

theorem valid7387 : plan7387.Valid := valid_step _ _ _ valid5944 (by decide +kernel)

theorem valid7388 : plan7388.Valid := valid_step _ _ _ valid5945 (by decide +kernel)

theorem valid7389 : plan7389.Valid := valid_step _ _ _ valid5946 (by decide +kernel)

theorem valid7390 : plan7390.Valid := valid_step _ _ _ valid5947 (by decide +kernel)




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







































































































theorem valid6964 : plan6964.Valid := valid_step _ _ _ valid5733 (by decide +kernel)

theorem valid6965 : plan6965.Valid := valid_step _ _ _ valid5734 (by decide +kernel)

theorem valid6966 : plan6966.Valid := valid_step _ _ _ valid5735 (by decide +kernel)




















































































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
theorem t6_793choices : plan7384.choices=[2,9,6,6,10,7].map (options 6 5) := by rfl


theorem t6_793part0 : t6_793jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_793part1 : t6_793jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_793frontier : t6_793root.frontier 2=t6_793jobs := by rfl
theorem t6_793all : t6_793jobs.all (Job.check tree)=true := by
  simp only [t6_793jobs,List.all_append,List.all_nil,t6_793part0,t6_793part1,Bool.and_self]
theorem t6_793checked : Checked tree [2,9,6,6,10,7] := by
  refine ⟨plan7384,valid7384,t6_793choices,?_⟩
  exact check_of_frontier tree 2 t6_793root t6_793jobs t6_793frontier t6_793all
theorem t6_794choices : plan7385.choices=[2,9,6,6,10,10].map (options 6 5) := by rfl


theorem t6_794part0 : t6_794jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_794frontier : t6_794root.frontier 0=t6_794jobs := by rfl
theorem t6_794all : t6_794jobs.all (Job.check tree)=true := by
  simp only [t6_794jobs,List.all_append,List.all_nil,t6_794part0,Bool.and_self]
theorem t6_794checked : Checked tree [2,9,6,6,10,10] := by
  refine ⟨plan7385,valid7385,t6_794choices,?_⟩
  exact check_of_frontier tree 0 t6_794root t6_794jobs t6_794frontier t6_794all
theorem t6_795choices : plan7386.choices=[2,9,6,7,7,7].map (options 6 5) := by rfl


theorem t6_795part0 : t6_795jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_795part1 : t6_795jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_795part2 : t6_795jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_795frontier : t6_795root.frontier 2=t6_795jobs := by rfl
theorem t6_795all : t6_795jobs.all (Job.check tree)=true := by
  simp only [t6_795jobs,List.all_append,List.all_nil,t6_795part0,t6_795part1,t6_795part2,Bool.and_self]
theorem t6_795checked : Checked tree [2,9,6,7,7,7] := by
  refine ⟨plan7386,valid7386,t6_795choices,?_⟩
  exact check_of_frontier tree 2 t6_795root t6_795jobs t6_795frontier t6_795all
theorem t6_796choices : plan7387.choices=[2,9,6,10,7,7].map (options 6 5) := by rfl


theorem t6_796part0 : t6_796jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_796part1 : t6_796jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_796part2 : t6_796jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_796part3 : t6_796jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_796frontier : t6_796root.frontier 2=t6_796jobs := by rfl
theorem t6_796all : t6_796jobs.all (Job.check tree)=true := by
  simp only [t6_796jobs,List.all_append,List.all_nil,t6_796part0,t6_796part1,t6_796part2,t6_796part3,Bool.and_self]
theorem t6_796checked : Checked tree [2,9,6,10,7,7] := by
  refine ⟨plan7387,valid7387,t6_796choices,?_⟩
  exact check_of_frontier tree 2 t6_796root t6_796jobs t6_796frontier t6_796all
theorem t6_797choices : plan7388.choices=[2,9,6,10,10,7].map (options 6 5) := by rfl


theorem t6_797part0 : t6_797jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_797part1 : t6_797jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_797frontier : t6_797root.frontier 2=t6_797jobs := by rfl
theorem t6_797all : t6_797jobs.all (Job.check tree)=true := by
  simp only [t6_797jobs,List.all_append,List.all_nil,t6_797part0,t6_797part1,Bool.and_self]
theorem t6_797checked : Checked tree [2,9,6,10,10,7] := by
  refine ⟨plan7388,valid7388,t6_797choices,?_⟩
  exact check_of_frontier tree 2 t6_797root t6_797jobs t6_797frontier t6_797all
theorem t6_798choices : plan7389.choices=[2,9,6,10,10,10].map (options 6 5) := by rfl


theorem t6_798part0 : t6_798jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_798frontier : t6_798root.frontier 0=t6_798jobs := by rfl
theorem t6_798all : t6_798jobs.all (Job.check tree)=true := by
  simp only [t6_798jobs,List.all_append,List.all_nil,t6_798part0,Bool.and_self]
theorem t6_798checked : Checked tree [2,9,6,10,10,10] := by
  refine ⟨plan7389,valid7389,t6_798choices,?_⟩
  exact check_of_frontier tree 0 t6_798root t6_798jobs t6_798frontier t6_798all
theorem t6_799choices : plan7390.choices=[2,9,7,7,7,7].map (options 6 5) := by rfl


theorem t6_799part0 : t6_799jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_799part1 : t6_799jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_799frontier : t6_799root.frontier 1=t6_799jobs := by rfl
theorem t6_799all : t6_799jobs.all (Job.check tree)=true := by
  simp only [t6_799jobs,List.all_append,List.all_nil,t6_799part0,t6_799part1,Bool.and_self]
theorem t6_799checked : Checked tree [2,9,7,7,7,7] := by
  refine ⟨plan7390,valid7390,t6_799choices,?_⟩
  exact check_of_frontier tree 1 t6_799root t6_799jobs t6_799frontier t6_799all
theorem t6_800choices : plan6400.choices=[2,9,9,3,3,3].map (options 6 2) := by rfl


theorem t6_800part0 : t6_800jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_800frontier : t6_800root.frontier 0=t6_800jobs := by rfl
theorem t6_800all : t6_800jobs.all (Job.check tree)=true := by
  simp only [t6_800jobs,List.all_append,List.all_nil,t6_800part0,Bool.and_self]
theorem t6_800checked : Checked tree [2,9,9,3,3,3] := by
  refine ⟨plan6400,valid6400,t6_800choices,?_⟩
  exact check_of_frontier tree 0 t6_800root t6_800jobs t6_800frontier t6_800all
theorem t6_801choices : plan6605.choices=[2,9,9,3,3,6].map (options 6 3) := by rfl


theorem t6_801part0 : t6_801jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_801frontier : t6_801root.frontier 0=t6_801jobs := by rfl
theorem t6_801all : t6_801jobs.all (Job.check tree)=true := by
  simp only [t6_801jobs,List.all_append,List.all_nil,t6_801part0,Bool.and_self]
theorem t6_801checked : Checked tree [2,9,9,3,3,6] := by
  refine ⟨plan6605,valid6605,t6_801choices,?_⟩
  exact check_of_frontier tree 0 t6_801root t6_801jobs t6_801frontier t6_801all
theorem t6_802choices : plan6606.choices=[2,9,9,3,3,7].map (options 6 3) := by rfl


theorem t6_802part0 : t6_802jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_802part1 : t6_802jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_802frontier : t6_802root.frontier 1=t6_802jobs := by rfl
theorem t6_802all : t6_802jobs.all (Job.check tree)=true := by
  simp only [t6_802jobs,List.all_append,List.all_nil,t6_802part0,t6_802part1,Bool.and_self]
theorem t6_802checked : Checked tree [2,9,9,3,3,7] := by
  refine ⟨plan6606,valid6606,t6_802choices,?_⟩
  exact check_of_frontier tree 1 t6_802root t6_802jobs t6_802frontier t6_802all
theorem t6_803choices : plan6607.choices=[2,9,9,3,3,10].map (options 6 3) := by rfl


theorem t6_803part0 : t6_803jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_803frontier : t6_803root.frontier 0=t6_803jobs := by rfl
theorem t6_803all : t6_803jobs.all (Job.check tree)=true := by
  simp only [t6_803jobs,List.all_append,List.all_nil,t6_803part0,Bool.and_self]
theorem t6_803checked : Checked tree [2,9,9,3,3,10] := by
  refine ⟨plan6607,valid6607,t6_803choices,?_⟩
  exact check_of_frontier tree 0 t6_803root t6_803jobs t6_803frontier t6_803all
theorem t6_804choices : plan6964.choices=[2,9,9,3,6,6].map (options 6 4) := by rfl


theorem t6_804part0 : t6_804jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_804frontier : t6_804root.frontier 0=t6_804jobs := by rfl
theorem t6_804all : t6_804jobs.all (Job.check tree)=true := by
  simp only [t6_804jobs,List.all_append,List.all_nil,t6_804part0,Bool.and_self]
theorem t6_804checked : Checked tree [2,9,9,3,6,6] := by
  refine ⟨plan6964,valid6964,t6_804choices,?_⟩
  exact check_of_frontier tree 0 t6_804root t6_804jobs t6_804frontier t6_804all
theorem t6_805choices : plan6965.choices=[2,9,9,3,6,7].map (options 6 4) := by rfl


theorem t6_805part0 : t6_805jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_805part1 : t6_805jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_805part2 : t6_805jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_805frontier : t6_805root.frontier 1=t6_805jobs := by rfl
theorem t6_805all : t6_805jobs.all (Job.check tree)=true := by
  simp only [t6_805jobs,List.all_append,List.all_nil,t6_805part0,t6_805part1,t6_805part2,Bool.and_self]
theorem t6_805checked : Checked tree [2,9,9,3,6,7] := by
  refine ⟨plan6965,valid6965,t6_805choices,?_⟩
  exact check_of_frontier tree 1 t6_805root t6_805jobs t6_805frontier t6_805all
theorem t6_806choices : plan6966.choices=[2,9,9,3,6,10].map (options 6 4) := by rfl


theorem t6_806part0 : t6_806jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_806frontier : t6_806root.frontier 0=t6_806jobs := by rfl
theorem t6_806all : t6_806jobs.all (Job.check tree)=true := by
  simp only [t6_806jobs,List.all_append,List.all_nil,t6_806part0,Bool.and_self]
theorem t6_806checked : Checked tree [2,9,9,3,6,10] := by
  refine ⟨plan6966,valid6966,t6_806choices,?_⟩
  exact check_of_frontier tree 0 t6_806root t6_806jobs t6_806frontier t6_806all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks096 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_798checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_799checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_800checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_801checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_802checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_803checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_804checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_805checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_806checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_793checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_794checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_795checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_796checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_797checked⟩
