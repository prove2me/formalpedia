-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks068
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:20:12.358629+00:00
-- url     : https://prove2.me/submissions/1698098f-0e42-4870-b54f-795337079cd1

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks068
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans071
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









































theorem valid117 : plan117.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid119 : plan119.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid120 : plan120.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid121 : plan121.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid123 : plan123.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid125 : plan125.Valid := valid_step _ _ _ valid0 (by decide +kernel)











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























































































































theorem valid540 : plan540.Valid := valid_step _ _ _ valid117 (by decide +kernel)



theorem valid542 : plan542.Valid := valid_step _ _ _ valid119 (by decide +kernel)

theorem valid543 : plan543.Valid := valid_step _ _ _ valid120 (by decide +kernel)

theorem valid544 : plan544.Valid := valid_step _ _ _ valid121 (by decide +kernel)









theorem valid549 : plan549.Valid := valid_step _ _ _ valid123 (by decide +kernel)

theorem valid550 : plan550.Valid := valid_step _ _ _ valid124 (by decide +kernel)

theorem valid551 : plan551.Valid := valid_step _ _ _ valid125 (by decide +kernel)

theorem valid552 : plan552.Valid := valid_step _ _ _ valid124 (by decide +kernel)





































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



































































































































theorem valid1506 : plan1506.Valid := valid_step _ _ _ valid540 (by decide +kernel)





theorem valid1509 : plan1509.Valid := valid_step _ _ _ valid542 (by decide +kernel)

theorem valid1510 : plan1510.Valid := valid_step _ _ _ valid543 (by decide +kernel)

theorem valid1511 : plan1511.Valid := valid_step _ _ _ valid544 (by decide +kernel)















theorem valid1519 : plan1519.Valid := valid_step _ _ _ valid549 (by decide +kernel)

theorem valid1520 : plan1520.Valid := valid_step _ _ _ valid550 (by decide +kernel)

theorem valid1521 : plan1521.Valid := valid_step _ _ _ valid551 (by decide +kernel)

theorem valid1522 : plan1522.Valid := valid_step _ _ _ valid552 (by decide +kernel)




























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







theorem valid3268 : plan3268.Valid := valid_step _ _ _ valid1519 (by decide +kernel)

theorem valid3269 : plan3269.Valid := valid_step _ _ _ valid1520 (by decide +kernel)

theorem valid3270 : plan3270.Valid := valid_step _ _ _ valid1521 (by decide +kernel)

theorem valid3271 : plan3271.Valid := valid_step _ _ _ valid1522 (by decide +kernel)


















































































































































































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

















































































theorem valid6281 : plan6281.Valid := valid_step _ _ _ valid5344 (by decide +kernel)

















































theorem valid6306 : plan6306.Valid := valid_step _ _ _ valid5357 (by decide +kernel)

theorem valid6307 : plan6307.Valid := valid_step _ _ _ valid5358 (by decide +kernel)

theorem valid6308 : plan6308.Valid := valid_step _ _ _ valid5359 (by decide +kernel)
























































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





































































































theorem valid5619 : plan5619.Valid := valid_step _ _ _ valid3434 (by decide +kernel)

theorem valid5620 : plan5620.Valid := valid_step _ _ _ valid3435 (by decide +kernel)

theorem valid5621 : plan5621.Valid := valid_step _ _ _ valid3436 (by decide +kernel)






















































































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



































































































theorem valid6386 : plan6386.Valid := valid_step _ _ _ valid5396 (by decide +kernel)

theorem valid6387 : plan6387.Valid := valid_step _ _ _ valid5397 (by decide +kernel)

theorem valid6388 : plan6388.Valid := valid_step _ _ _ valid5398 (by decide +kernel)

theorem valid6389 : plan6389.Valid := valid_step _ _ _ valid5399 (by decide +kernel)






















































































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





























































































































































































theorem valid6911 : plan6911.Valid := valid_step _ _ _ valid5619 (by decide +kernel)

theorem valid6912 : plan6912.Valid := valid_step _ _ _ valid5620 (by decide +kernel)
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

theorem valid6913 : plan6913.Valid := valid_step _ _ _ valid5621 (by decide +kernel)






























































































































































































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
theorem t6_628choices : plan6911.choices=[2,2,10,10,7,7].map (options 6 4) := by rfl


theorem t6_628part0 : t6_628jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_628part1 : t6_628jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_628frontier : t6_628root.frontier 1=t6_628jobs := by rfl
theorem t6_628all : t6_628jobs.all (Job.check tree)=true := by
  simp only [t6_628jobs,List.all_append,List.all_nil,t6_628part0,t6_628part1,Bool.and_self]
theorem t6_628checked : Checked tree [2,2,10,10,7,7] := by
  refine ⟨plan6911,valid6911,t6_628choices,?_⟩
  exact check_of_frontier tree 1 t6_628root t6_628jobs t6_628frontier t6_628all
theorem t6_629choices : plan6912.choices=[2,2,10,10,10,7].map (options 6 4) := by rfl


theorem t6_629part0 : t6_629jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_629frontier : t6_629root.frontier 0=t6_629jobs := by rfl
theorem t6_629all : t6_629jobs.all (Job.check tree)=true := by
  simp only [t6_629jobs,List.all_append,List.all_nil,t6_629part0,Bool.and_self]
theorem t6_629checked : Checked tree [2,2,10,10,10,7] := by
  refine ⟨plan6912,valid6912,t6_629choices,?_⟩
  exact check_of_frontier tree 0 t6_629root t6_629jobs t6_629frontier t6_629all
theorem t6_630choices : plan6913.choices=[2,2,10,10,10,10].map (options 6 4) := by rfl


theorem t6_630part0 : t6_630jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_630frontier : t6_630root.frontier 0=t6_630jobs := by rfl
theorem t6_630all : t6_630jobs.all (Job.check tree)=true := by
  simp only [t6_630jobs,List.all_append,List.all_nil,t6_630part0,Bool.and_self]
theorem t6_630checked : Checked tree [2,2,10,10,10,10] := by
  refine ⟨plan6913,valid6913,t6_630choices,?_⟩
  exact check_of_frontier tree 0 t6_630root t6_630jobs t6_630frontier t6_630all
theorem t6_631choices : plan6281.choices=[2,3,3,3,3,3].map (options 6 0) := by rfl


theorem t6_631part0 : t6_631jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_631frontier : t6_631root.frontier 0=t6_631jobs := by rfl
theorem t6_631all : t6_631jobs.all (Job.check tree)=true := by
  simp only [t6_631jobs,List.all_append,List.all_nil,t6_631part0,Bool.and_self]
theorem t6_631checked : Checked tree [2,3,3,3,3,3] := by
  refine ⟨plan6281,valid6281,t6_631choices,?_⟩
  exact check_of_frontier tree 0 t6_631root t6_631jobs t6_631frontier t6_631all
theorem t6_632choices : plan6306.choices=[2,3,3,3,3,6].map (options 6 1) := by rfl


theorem t6_632part0 : t6_632jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_632frontier : t6_632root.frontier 0=t6_632jobs := by rfl
theorem t6_632all : t6_632jobs.all (Job.check tree)=true := by
  simp only [t6_632jobs,List.all_append,List.all_nil,t6_632part0,Bool.and_self]
theorem t6_632checked : Checked tree [2,3,3,3,3,6] := by
  refine ⟨plan6306,valid6306,t6_632choices,?_⟩
  exact check_of_frontier tree 0 t6_632root t6_632jobs t6_632frontier t6_632all
theorem t6_633choices : plan6307.choices=[2,3,3,3,3,7].map (options 6 1) := by rfl


theorem t6_633part0 : t6_633jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_633frontier : t6_633root.frontier 0=t6_633jobs := by rfl
theorem t6_633all : t6_633jobs.all (Job.check tree)=true := by
  simp only [t6_633jobs,List.all_append,List.all_nil,t6_633part0,Bool.and_self]
theorem t6_633checked : Checked tree [2,3,3,3,3,7] := by
  refine ⟨plan6307,valid6307,t6_633choices,?_⟩
  exact check_of_frontier tree 0 t6_633root t6_633jobs t6_633frontier t6_633all
theorem t6_634choices : plan6308.choices=[2,3,3,3,3,10].map (options 6 1) := by rfl


theorem t6_634part0 : t6_634jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_634frontier : t6_634root.frontier 0=t6_634jobs := by rfl
theorem t6_634all : t6_634jobs.all (Job.check tree)=true := by
  simp only [t6_634jobs,List.all_append,List.all_nil,t6_634part0,Bool.and_self]
theorem t6_634checked : Checked tree [2,3,3,3,3,10] := by
  refine ⟨plan6308,valid6308,t6_634choices,?_⟩
  exact check_of_frontier tree 0 t6_634root t6_634jobs t6_634frontier t6_634all
theorem t6_635choices : plan6386.choices=[2,3,3,3,6,6].map (options 6 2) := by rfl


theorem t6_635part0 : t6_635jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_635part1 : t6_635jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_635frontier : t6_635root.frontier 1=t6_635jobs := by rfl
theorem t6_635all : t6_635jobs.all (Job.check tree)=true := by
  simp only [t6_635jobs,List.all_append,List.all_nil,t6_635part0,t6_635part1,Bool.and_self]
theorem t6_635checked : Checked tree [2,3,3,3,6,6] := by
  refine ⟨plan6386,valid6386,t6_635choices,?_⟩
  exact check_of_frontier tree 1 t6_635root t6_635jobs t6_635frontier t6_635all
theorem t6_636choices : plan6387.choices=[2,3,3,3,6,7].map (options 6 2) := by rfl


theorem t6_636part0 : t6_636jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_636part1 : t6_636jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_636part2 : t6_636jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_636part3 : t6_636jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_636part4 : t6_636jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_636frontier : t6_636root.frontier 1=t6_636jobs := by rfl
theorem t6_636all : t6_636jobs.all (Job.check tree)=true := by
  simp only [t6_636jobs,List.all_append,List.all_nil,t6_636part0,t6_636part1,t6_636part2,t6_636part3,t6_636part4,Bool.and_self]
theorem t6_636checked : Checked tree [2,3,3,3,6,7] := by
  refine ⟨plan6387,valid6387,t6_636choices,?_⟩
  exact check_of_frontier tree 1 t6_636root t6_636jobs t6_636frontier t6_636all
theorem t6_637choices : plan6388.choices=[2,3,3,3,6,10].map (options 6 2) := by rfl


theorem t6_637part0 : t6_637jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_637part1 : t6_637jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_637frontier : t6_637root.frontier 1=t6_637jobs := by rfl
theorem t6_637all : t6_637jobs.all (Job.check tree)=true := by
  simp only [t6_637jobs,List.all_append,List.all_nil,t6_637part0,t6_637part1,Bool.and_self]
theorem t6_637checked : Checked tree [2,3,3,3,6,10] := by
  refine ⟨plan6388,valid6388,t6_637choices,?_⟩
  exact check_of_frontier tree 1 t6_637root t6_637jobs t6_637frontier t6_637all
theorem t6_638choices : plan6389.choices=[2,3,3,3,7,7].map (options 6 2) := by rfl


theorem t6_638part0 : t6_638jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_638part1 : t6_638jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_638part2 : t6_638jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_638part3 : t6_638jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_638part4 : t6_638jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_638frontier : t6_638root.frontier 1=t6_638jobs := by rfl
theorem t6_638all : t6_638jobs.all (Job.check tree)=true := by
  simp only [t6_638jobs,List.all_append,List.all_nil,t6_638part0,t6_638part1,t6_638part2,t6_638part3,t6_638part4,Bool.and_self]
theorem t6_638checked : Checked tree [2,3,3,3,7,7] := by
  refine ⟨plan6389,valid6389,t6_638choices,?_⟩
  exact check_of_frontier tree 1 t6_638root t6_638jobs t6_638frontier t6_638all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks068 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_638checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_628checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_629checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_630checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_631checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_632checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_633checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_634checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_635checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_636checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_637checked⟩
