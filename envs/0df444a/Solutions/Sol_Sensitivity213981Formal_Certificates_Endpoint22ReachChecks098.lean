-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks098
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:39:29.583995+00:00
-- url     : https://prove2.me/submissions/9ee51888-063c-4e74-9cb6-3bfc8f980b6d

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks098
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks098
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans055
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans056
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
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









































theorem valid117 : plan117.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid119 : plan119.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid120 : plan120.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid121 : plan121.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid123 : plan123.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid125 : plan125.Valid := valid_step _ _ _ valid0 (by decide +kernel)

















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























































































































theorem valid540 : plan540.Valid := valid_step _ _ _ valid117 (by decide +kernel)



theorem valid542 : plan542.Valid := valid_step _ _ _ valid119 (by decide +kernel)

theorem valid543 : plan543.Valid := valid_step _ _ _ valid120 (by decide +kernel)

theorem valid544 : plan544.Valid := valid_step _ _ _ valid121 (by decide +kernel)









theorem valid549 : plan549.Valid := valid_step _ _ _ valid123 (by decide +kernel)

theorem valid550 : plan550.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid551 : plan551.Valid := valid_step _ _ _ valid125 (by decide +kernel)

theorem valid552 : plan552.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid553 : plan553.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid554 : plan554.Valid := valid_step _ _ _ valid125 (by decide +kernel)












































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



































































































































theorem valid1506 : plan1506.Valid := valid_step _ _ _ valid540 (by decide +kernel)





theorem valid1509 : plan1509.Valid := valid_step _ _ _ valid542 (by decide +kernel)

theorem valid1510 : plan1510.Valid := valid_step _ _ _ valid543 (by decide +kernel)

theorem valid1511 : plan1511.Valid := valid_step _ _ _ valid544 (by decide +kernel)















theorem valid1519 : plan1519.Valid := valid_step _ _ _ valid549 (by decide +kernel)

theorem valid1520 : plan1520.Valid := valid_step _ _ _ valid550 (by decide +kernel)

theorem valid1521 : plan1521.Valid := valid_step _ _ _ valid551 (by decide +kernel)

theorem valid1522 : plan1522.Valid := valid_step _ _ _ valid552 (by decide +kernel)

theorem valid1523 : plan1523.Valid := valid_step _ _ _ valid553 (by decide +kernel)

theorem valid1524 : plan1524.Valid := valid_step _ _ _ valid554 (by decide +kernel)
























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

















































































































































theorem valid3241 : plan3241.Valid := valid_step _ _ _ valid1506 (by decide +kernel)











theorem valid3247 : plan3247.Valid := valid_step _ _ _ valid1509 (by decide +kernel)

theorem valid3248 : plan3248.Valid := valid_step _ _ _ valid1510 (by decide +kernel)

theorem valid3249 : plan3249.Valid := valid_step _ _ _ valid1511 (by decide +kernel)






























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







theorem valid3268 : plan3268.Valid := valid_step _ _ _ valid1519 (by decide +kernel)

theorem valid3269 : plan3269.Valid := valid_step _ _ _ valid1520 (by decide +kernel)

theorem valid3270 : plan3270.Valid := valid_step _ _ _ valid1521 (by decide +kernel)

theorem valid3271 : plan3271.Valid := valid_step _ _ _ valid1522 (by decide +kernel)

theorem valid3272 : plan3272.Valid := valid_step _ _ _ valid1523 (by decide +kernel)

theorem valid3273 : plan3273.Valid := valid_step _ _ _ valid1524 (by decide +kernel)














































































































































































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































































































































theorem valid5344 : plan5344.Valid := valid_step _ _ _ valid3241 (by decide +kernel)

























theorem valid5357 : plan5357.Valid := valid_step _ _ _ valid3247 (by decide +kernel)

theorem valid5358 : plan5358.Valid := valid_step _ _ _ valid3248 (by decide +kernel)

theorem valid5359 : plan5359.Valid := valid_step _ _ _ valid3249 (by decide +kernel)


































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







































theorem valid5396 : plan5396.Valid := valid_step _ _ _ valid3268 (by decide +kernel)

theorem valid5397 : plan5397.Valid := valid_step _ _ _ valid3269 (by decide +kernel)

theorem valid5398 : plan5398.Valid := valid_step _ _ _ valid3270 (by decide +kernel)

theorem valid5399 : plan5399.Valid := valid_step _ _ _ valid3271 (by decide +kernel)

theorem valid5400 : plan5400.Valid := valid_step _ _ _ valid3272 (by decide +kernel)

theorem valid5401 : plan5401.Valid := valid_step _ _ _ valid3273 (by decide +kernel)














































































































































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



















































































theorem valid6282 : plan6282.Valid := valid_step _ _ _ valid5344 (by decide +kernel)

























































theorem valid6311 : plan6311.Valid := valid_step _ _ _ valid5357 (by decide +kernel)

theorem valid6312 : plan6312.Valid := valid_step _ _ _ valid5358 (by decide +kernel)

theorem valid6313 : plan6313.Valid := valid_step _ _ _ valid5359 (by decide +kernel)














































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





































































































theorem valid3507 : plan3507.Valid := valid_step _ _ _ valid1599 (by decide +kernel)

theorem valid3508 : plan3508.Valid := valid_step _ _ _ valid1604 (by decide +kernel)

theorem valid3509 : plan3509.Valid := valid_step _ _ _ valid1605 (by decide +kernel)

theorem valid3510 : plan3510.Valid := valid_step _ _ _ valid1606 (by decide +kernel)




















































































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

































































































































theorem valid6401 : plan6401.Valid := valid_step _ _ _ valid5396 (by decide +kernel)

theorem valid6402 : plan6402.Valid := valid_step _ _ _ valid5397 (by decide +kernel)

theorem valid6403 : plan6403.Valid := valid_step _ _ _ valid5398 (by decide +kernel)

theorem valid6404 : plan6404.Valid := valid_step _ _ _ valid5399 (by decide +kernel)

theorem valid6405 : plan6405.Valid := valid_step _ _ _ valid5400 (by decide +kernel)

theorem valid6406 : plan6406.Valid := valid_step _ _ _ valid5401 (by decide +kernel)




















































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









































theorem valid5973 : plan5973.Valid := valid_step _ _ _ valid3507 (by decide +kernel)

theorem valid5974 : plan5974.Valid := valid_step _ _ _ valid3508 (by decide +kernel)

theorem valid5975 : plan5975.Valid := valid_step _ _ _ valid3509 (by decide +kernel)

theorem valid5976 : plan5976.Valid := valid_step _ _ _ valid3510 (by decide +kernel)
















































































































































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

































theorem valid7409 : plan7409.Valid := valid_step _ _ _ valid5973 (by decide +kernel)

theorem valid7410 : plan7410.Valid := valid_step _ _ _ valid5974 (by decide +kernel)

theorem valid7411 : plan7411.Valid := valid_step _ _ _ valid5975 (by decide +kernel)

theorem valid7412 : plan7412.Valid := valid_step _ _ _ valid5976 (by decide +kernel)
























































































































































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
theorem t6_829choices : plan7409.choices=[2,10,10,7,7,7].map (options 6 5) := by rfl


theorem t6_829part0 : t6_829jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_829part1 : t6_829jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_829part2 : t6_829jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_829frontier : t6_829root.frontier 2=t6_829jobs := by rfl
theorem t6_829all : t6_829jobs.all (Job.check tree)=true := by
  simp only [t6_829jobs,List.all_append,List.all_nil,t6_829part0,t6_829part1,t6_829part2,Bool.and_self]
theorem t6_829checked : Checked tree [2,10,10,7,7,7] := by
  refine ⟨plan7409,valid7409,t6_829choices,?_⟩
  exact check_of_frontier tree 2 t6_829root t6_829jobs t6_829frontier t6_829all
theorem t6_830choices : plan7410.choices=[2,10,10,10,7,7].map (options 6 5) := by rfl


theorem t6_830part0 : t6_830jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_830part1 : t6_830jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_830frontier : t6_830root.frontier 1=t6_830jobs := by rfl
theorem t6_830all : t6_830jobs.all (Job.check tree)=true := by
  simp only [t6_830jobs,List.all_append,List.all_nil,t6_830part0,t6_830part1,Bool.and_self]
theorem t6_830checked : Checked tree [2,10,10,10,7,7] := by
  refine ⟨plan7410,valid7410,t6_830choices,?_⟩
  exact check_of_frontier tree 1 t6_830root t6_830jobs t6_830frontier t6_830all
theorem t6_831choices : plan7411.choices=[2,10,10,10,10,7].map (options 6 5) := by rfl


theorem t6_831part0 : t6_831jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_831frontier : t6_831root.frontier 0=t6_831jobs := by rfl
theorem t6_831all : t6_831jobs.all (Job.check tree)=true := by
  simp only [t6_831jobs,List.all_append,List.all_nil,t6_831part0,Bool.and_self]
theorem t6_831checked : Checked tree [2,10,10,10,10,7] := by
  refine ⟨plan7411,valid7411,t6_831choices,?_⟩
  exact check_of_frontier tree 0 t6_831root t6_831jobs t6_831frontier t6_831all
theorem t6_832choices : plan7412.choices=[2,10,10,10,10,10].map (options 6 5) := by rfl


theorem t6_832part0 : t6_832jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_832frontier : t6_832root.frontier 0=t6_832jobs := by rfl
theorem t6_832all : t6_832jobs.all (Job.check tree)=true := by
  simp only [t6_832jobs,List.all_append,List.all_nil,t6_832part0,Bool.and_self]
theorem t6_832checked : Checked tree [2,10,10,10,10,10] := by
  refine ⟨plan7412,valid7412,t6_832choices,?_⟩
  exact check_of_frontier tree 0 t6_832root t6_832jobs t6_832frontier t6_832all
theorem t6_833choices : plan6282.choices=[3,3,3,3,3,3].map (options 6 0) := by rfl


theorem t6_833part0 : t6_833jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_833frontier : t6_833root.frontier 0=t6_833jobs := by rfl
theorem t6_833all : t6_833jobs.all (Job.check tree)=true := by
  simp only [t6_833jobs,List.all_append,List.all_nil,t6_833part0,Bool.and_self]
theorem t6_833checked : Checked tree [3,3,3,3,3,3] := by
  refine ⟨plan6282,valid6282,t6_833choices,?_⟩
  exact check_of_frontier tree 0 t6_833root t6_833jobs t6_833frontier t6_833all
theorem t6_834choices : plan6311.choices=[3,3,3,3,3,6].map (options 6 1) := by rfl


theorem t6_834part0 : t6_834jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_834frontier : t6_834root.frontier 0=t6_834jobs := by rfl
theorem t6_834all : t6_834jobs.all (Job.check tree)=true := by
  simp only [t6_834jobs,List.all_append,List.all_nil,t6_834part0,Bool.and_self]
theorem t6_834checked : Checked tree [3,3,3,3,3,6] := by
  refine ⟨plan6311,valid6311,t6_834choices,?_⟩
  exact check_of_frontier tree 0 t6_834root t6_834jobs t6_834frontier t6_834all
theorem t6_835choices : plan6312.choices=[3,3,3,3,3,7].map (options 6 1) := by rfl


theorem t6_835part0 : t6_835jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_835frontier : t6_835root.frontier 0=t6_835jobs := by rfl
theorem t6_835all : t6_835jobs.all (Job.check tree)=true := by
  simp only [t6_835jobs,List.all_append,List.all_nil,t6_835part0,Bool.and_self]
theorem t6_835checked : Checked tree [3,3,3,3,3,7] := by
  refine ⟨plan6312,valid6312,t6_835choices,?_⟩
  exact check_of_frontier tree 0 t6_835root t6_835jobs t6_835frontier t6_835all
theorem t6_836choices : plan6313.choices=[3,3,3,3,3,10].map (options 6 1) := by rfl


theorem t6_836part0 : t6_836jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_836frontier : t6_836root.frontier 0=t6_836jobs := by rfl
theorem t6_836all : t6_836jobs.all (Job.check tree)=true := by
  simp only [t6_836jobs,List.all_append,List.all_nil,t6_836part0,Bool.and_self]
theorem t6_836checked : Checked tree [3,3,3,3,3,10] := by
  refine ⟨plan6313,valid6313,t6_836choices,?_⟩
  exact check_of_frontier tree 0 t6_836root t6_836jobs t6_836frontier t6_836all
theorem t6_837choices : plan6401.choices=[3,3,3,3,6,6].map (options 6 2) := by rfl


theorem t6_837part0 : t6_837jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_837frontier : t6_837root.frontier 0=t6_837jobs := by rfl
theorem t6_837all : t6_837jobs.all (Job.check tree)=true := by
  simp only [t6_837jobs,List.all_append,List.all_nil,t6_837part0,Bool.and_self]
theorem t6_837checked : Checked tree [3,3,3,3,6,6] := by
  refine ⟨plan6401,valid6401,t6_837choices,?_⟩
  exact check_of_frontier tree 0 t6_837root t6_837jobs t6_837frontier t6_837all
theorem t6_838choices : plan6402.choices=[3,3,3,3,6,7].map (options 6 2) := by rfl


theorem t6_838part0 : t6_838jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_838part1 : t6_838jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_838part2 : t6_838jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_838part3 : t6_838jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_838frontier : t6_838root.frontier 1=t6_838jobs := by rfl
theorem t6_838all : t6_838jobs.all (Job.check tree)=true := by
  simp only [t6_838jobs,List.all_append,List.all_nil,t6_838part0,t6_838part1,t6_838part2,t6_838part3,Bool.and_self]
theorem t6_838checked : Checked tree [3,3,3,3,6,7] := by
  refine ⟨plan6402,valid6402,t6_838choices,?_⟩
  exact check_of_frontier tree 1 t6_838root t6_838jobs t6_838frontier t6_838all
theorem t6_839choices : plan6403.choices=[3,3,3,3,6,10].map (options 6 2) := by rfl


theorem t6_839part0 : t6_839jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_839part1 : t6_839jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_839frontier : t6_839root.frontier 1=t6_839jobs := by rfl
theorem t6_839all : t6_839jobs.all (Job.check tree)=true := by
  simp only [t6_839jobs,List.all_append,List.all_nil,t6_839part0,t6_839part1,Bool.and_self]
theorem t6_839checked : Checked tree [3,3,3,3,6,10] := by
  refine ⟨plan6403,valid6403,t6_839choices,?_⟩
  exact check_of_frontier tree 1 t6_839root t6_839jobs t6_839frontier t6_839all
theorem t6_840choices : plan6404.choices=[3,3,3,3,7,7].map (options 6 2) := by rfl


theorem t6_840part0 : t6_840jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_840part1 : t6_840jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_840part2 : t6_840jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_840frontier : t6_840root.frontier 1=t6_840jobs := by rfl
theorem t6_840all : t6_840jobs.all (Job.check tree)=true := by
  simp only [t6_840jobs,List.all_append,List.all_nil,t6_840part0,t6_840part1,t6_840part2,Bool.and_self]
theorem t6_840checked : Checked tree [3,3,3,3,7,7] := by
  refine ⟨plan6404,valid6404,t6_840choices,?_⟩
  exact check_of_frontier tree 1 t6_840root t6_840jobs t6_840frontier t6_840all
theorem t6_841choices : plan6405.choices=[3,3,3,3,10,7].map (options 6 2) := by rfl


theorem t6_841part0 : t6_841jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_841part1 : t6_841jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_841part2 : t6_841jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_841part3 : t6_841jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_841frontier : t6_841root.frontier 1=t6_841jobs := by rfl
theorem t6_841all : t6_841jobs.all (Job.check tree)=true := by
  simp only [t6_841jobs,List.all_append,List.all_nil,t6_841part0,t6_841part1,t6_841part2,t6_841part3,Bool.and_self]
theorem t6_841checked : Checked tree [3,3,3,3,10,7] := by
  refine ⟨plan6405,valid6405,t6_841choices,?_⟩
  exact check_of_frontier tree 1 t6_841root t6_841jobs t6_841frontier t6_841all
theorem t6_842choices : plan6406.choices=[3,3,3,3,10,10].map (options 6 2) := by rfl


theorem t6_842part0 : t6_842jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_842frontier : t6_842root.frontier 0=t6_842jobs := by rfl
theorem t6_842all : t6_842jobs.all (Job.check tree)=true := by
  simp only [t6_842jobs,List.all_append,List.all_nil,t6_842part0,Bool.and_self]
theorem t6_842checked : Checked tree [3,3,3,3,10,10] := by
  refine ⟨plan6406,valid6406,t6_842choices,?_⟩
  exact check_of_frontier tree 0 t6_842root t6_842jobs t6_842frontier t6_842all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks098 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_838checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_839checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_840checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_841checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_842checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_829checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_830checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_831checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_832checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_833checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_834checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_835checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_836checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_837checked⟩
