-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks115
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:41:49.473986+00:00
-- url     : https://prove2.me/submissions/b6e29b96-79b4-49d4-bf98-df29d4a3c874

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks115
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks115
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans066
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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























































theorem valid124 : plan124.Valid := valid_step _ _ _ valid0 (by decide +kernel)







theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)





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





































































































































theorem valid547 : plan547.Valid := valid_step _ _ _ valid124 (by decide +kernel)

























theorem valid560 : plan560.Valid := valid_step _ _ _ valid128 (by decide +kernel)



theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)











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



















theorem valid1527 : plan1527.Valid := valid_step _ _ _ valid562 (by decide +kernel)











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













































































































































































theorem valid3255 : plan3255.Valid := valid_step _ _ _ valid1517 (by decide +kernel)


















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





























































theorem valid1567 : plan1567.Valid := valid_step _ _ _ valid571 (by decide +kernel)





theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)



theorem valid1572 : plan1572.Valid := valid_step _ _ _ valid571 (by decide +kernel)

theorem valid1573 : plan1573.Valid := valid_step _ _ _ valid572 (by decide +kernel)



















































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





































theorem valid3283 : plan3283.Valid := valid_step _ _ _ valid1527 (by decide +kernel)

theorem valid3284 : plan3284.Valid := valid_step _ _ _ valid1533 (by decide +kernel)

theorem valid3285 : plan3285.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3286 : plan3286.Valid := valid_step _ _ _ valid1536 (by decide +kernel)























































































































theorem valid3346 : plan3346.Valid := valid_step _ _ _ valid1567 (by decide +kernel)

theorem valid3347 : plan3347.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3348 : plan3348.Valid := valid_step _ _ _ valid1572 (by decide +kernel)

theorem valid3349 : plan3349.Valid := valid_step _ _ _ valid1573 (by decide +kernel)






















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

















































































































































































theorem valid5369 : plan5369.Valid := valid_step _ _ _ valid3255 (by decide +kernel)














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





































































































theorem valid5427 : plan5427.Valid := valid_step _ _ _ valid3283 (by decide +kernel)

theorem valid5428 : plan5428.Valid := valid_step _ _ _ valid3284 (by decide +kernel)

theorem valid5429 : plan5429.Valid := valid_step _ _ _ valid3285 (by decide +kernel)

theorem valid5430 : plan5430.Valid := valid_step _ _ _ valid3286 (by decide +kernel)




















































































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



































































































































































theorem valid5554 : plan5554.Valid := valid_step _ _ _ valid3346 (by decide +kernel)

theorem valid5555 : plan5555.Valid := valid_step _ _ _ valid3347 (by decide +kernel)

theorem valid5556 : plan5556.Valid := valid_step _ _ _ valid3348 (by decide +kernel)

theorem valid5557 : plan5557.Valid := valid_step _ _ _ valid3349 (by decide +kernel)






















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

























































theorem valid3485 : plan3485.Valid := valid_step _ _ _ valid1599 (by decide +kernel)











































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













































































































































theorem valid6407 : plan6407.Valid := valid_step _ _ _ valid5369 (by decide +kernel)


















































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







































theorem valid5972 : plan5972.Valid := valid_step _ _ _ valid3485 (by decide +kernel)

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



















































































































































































theorem valid6618 : plan6618.Valid := valid_step _ _ _ valid5427 (by decide +kernel)

theorem valid6619 : plan6619.Valid := valid_step _ _ _ valid5428 (by decide +kernel)

theorem valid6620 : plan6620.Valid := valid_step _ _ _ valid5429 (by decide +kernel)

theorem valid6621 : plan6621.Valid := valid_step _ _ _ valid5430 (by decide +kernel)






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



















































































































































theorem valid6986 : plan6986.Valid := valid_step _ _ _ valid5554 (by decide +kernel)

theorem valid6987 : plan6987.Valid := valid_step _ _ _ valid5555 (by decide +kernel)

theorem valid6988 : plan6988.Valid := valid_step _ _ _ valid5556 (by decide +kernel)

theorem valid6989 : plan6989.Valid := valid_step _ _ _ valid5557 (by decide +kernel)






































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









































































theorem valid7429 : plan7429.Valid := valid_step _ _ _ valid5972 (by decide +kernel)

theorem valid7430 : plan7430.Valid := valid_step _ _ _ valid5973 (by decide +kernel)

theorem valid7431 : plan7431.Valid := valid_step _ _ _ valid5974 (by decide +kernel)

theorem valid7432 : plan7432.Valid := valid_step _ _ _ valid5975 (by decide +kernel)

theorem valid7433 : plan7433.Valid := valid_step _ _ _ valid5976 (by decide +kernel)














































































































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
theorem t6_884choices : plan7429.choices=[3,10,7,7,7,7].map (options 6 5) := by rfl


theorem t6_884part0 : t6_884jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_884part1 : t6_884jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_884part2 : t6_884jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_884part3 : t6_884jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_884part4 : t6_884jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_884part5 : t6_884jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_884frontier : t6_884root.frontier 2=t6_884jobs := by rfl
theorem t6_884all : t6_884jobs.all (Job.check tree)=true := by
  simp only [t6_884jobs,List.all_append,List.all_nil,t6_884part0,t6_884part1,t6_884part2,t6_884part3,t6_884part4,t6_884part5,Bool.and_self]
theorem t6_884checked : Checked tree [3,10,7,7,7,7] := by
  refine ⟨plan7429,valid7429,t6_884choices,?_⟩
  exact check_of_frontier tree 2 t6_884root t6_884jobs t6_884frontier t6_884all
theorem t6_885choices : plan7430.choices=[3,10,10,7,7,7].map (options 6 5) := by rfl


theorem t6_885part0 : t6_885jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_885part1 : t6_885jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_885part2 : t6_885jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_885part3 : t6_885jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_885part4 : t6_885jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_885part5 : t6_885jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_885frontier : t6_885root.frontier 2=t6_885jobs := by rfl
theorem t6_885all : t6_885jobs.all (Job.check tree)=true := by
  simp only [t6_885jobs,List.all_append,List.all_nil,t6_885part0,t6_885part1,t6_885part2,t6_885part3,t6_885part4,t6_885part5,Bool.and_self]
theorem t6_885checked : Checked tree [3,10,10,7,7,7] := by
  refine ⟨plan7430,valid7430,t6_885choices,?_⟩
  exact check_of_frontier tree 2 t6_885root t6_885jobs t6_885frontier t6_885all
theorem t6_886choices : plan7431.choices=[3,10,10,10,7,7].map (options 6 5) := by rfl


theorem t6_886part0 : t6_886jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_886part1 : t6_886jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_886part2 : t6_886jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_886part3 : t6_886jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_886frontier : t6_886root.frontier 2=t6_886jobs := by rfl
theorem t6_886all : t6_886jobs.all (Job.check tree)=true := by
  simp only [t6_886jobs,List.all_append,List.all_nil,t6_886part0,t6_886part1,t6_886part2,t6_886part3,Bool.and_self]
theorem t6_886checked : Checked tree [3,10,10,10,7,7] := by
  refine ⟨plan7431,valid7431,t6_886choices,?_⟩
  exact check_of_frontier tree 2 t6_886root t6_886jobs t6_886frontier t6_886all
theorem t6_887choices : plan7432.choices=[3,10,10,10,10,7].map (options 6 5) := by rfl


theorem t6_887part0 : t6_887jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_887part1 : t6_887jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_887frontier : t6_887root.frontier 1=t6_887jobs := by rfl
theorem t6_887all : t6_887jobs.all (Job.check tree)=true := by
  simp only [t6_887jobs,List.all_append,List.all_nil,t6_887part0,t6_887part1,Bool.and_self]
theorem t6_887checked : Checked tree [3,10,10,10,10,7] := by
  refine ⟨plan7432,valid7432,t6_887choices,?_⟩
  exact check_of_frontier tree 1 t6_887root t6_887jobs t6_887frontier t6_887all
theorem t6_888choices : plan7433.choices=[3,10,10,10,10,10].map (options 6 5) := by rfl


theorem t6_888part0 : t6_888jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_888frontier : t6_888root.frontier 0=t6_888jobs := by rfl
theorem t6_888all : t6_888jobs.all (Job.check tree)=true := by
  simp only [t6_888jobs,List.all_append,List.all_nil,t6_888part0,Bool.and_self]
theorem t6_888checked : Checked tree [3,10,10,10,10,10] := by
  refine ⟨plan7433,valid7433,t6_888choices,?_⟩
  exact check_of_frontier tree 0 t6_888root t6_888jobs t6_888frontier t6_888all
theorem t6_889choices : plan6618.choices=[4,2,2,2,7,7].map (options 6 3) := by rfl


theorem t6_889part0 : t6_889jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_889frontier : t6_889root.frontier 0=t6_889jobs := by rfl
theorem t6_889all : t6_889jobs.all (Job.check tree)=true := by
  simp only [t6_889jobs,List.all_append,List.all_nil,t6_889part0,Bool.and_self]
theorem t6_889checked : Checked tree [4,2,2,2,7,7] := by
  refine ⟨plan6618,valid6618,t6_889choices,?_⟩
  exact check_of_frontier tree 0 t6_889root t6_889jobs t6_889frontier t6_889all
theorem t6_890choices : plan6407.choices=[4,2,2,3,3,7].map (options 6 2) := by rfl


theorem t6_890part0 : t6_890jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_890frontier : t6_890root.frontier 0=t6_890jobs := by rfl
theorem t6_890all : t6_890jobs.all (Job.check tree)=true := by
  simp only [t6_890jobs,List.all_append,List.all_nil,t6_890part0,Bool.and_self]
theorem t6_890checked : Checked tree [4,2,2,3,3,7] := by
  refine ⟨plan6407,valid6407,t6_890choices,?_⟩
  exact check_of_frontier tree 0 t6_890root t6_890jobs t6_890frontier t6_890all
theorem t6_891choices : plan6619.choices=[4,2,2,3,6,7].map (options 6 3) := by rfl


theorem t6_891part0 : t6_891jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_891frontier : t6_891root.frontier 0=t6_891jobs := by rfl
theorem t6_891all : t6_891jobs.all (Job.check tree)=true := by
  simp only [t6_891jobs,List.all_append,List.all_nil,t6_891part0,Bool.and_self]
theorem t6_891checked : Checked tree [4,2,2,3,6,7] := by
  refine ⟨plan6619,valid6619,t6_891choices,?_⟩
  exact check_of_frontier tree 0 t6_891root t6_891jobs t6_891frontier t6_891all
theorem t6_892choices : plan6620.choices=[4,2,2,3,7,7].map (options 6 3) := by rfl


theorem t6_892part0 : t6_892jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_892frontier : t6_892root.frontier 0=t6_892jobs := by rfl
theorem t6_892all : t6_892jobs.all (Job.check tree)=true := by
  simp only [t6_892jobs,List.all_append,List.all_nil,t6_892part0,Bool.and_self]
theorem t6_892checked : Checked tree [4,2,2,3,7,7] := by
  refine ⟨plan6620,valid6620,t6_892choices,?_⟩
  exact check_of_frontier tree 0 t6_892root t6_892jobs t6_892frontier t6_892all
theorem t6_893choices : plan6621.choices=[4,2,2,3,10,7].map (options 6 3) := by rfl


theorem t6_893part0 : t6_893jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_893frontier : t6_893root.frontier 0=t6_893jobs := by rfl
theorem t6_893all : t6_893jobs.all (Job.check tree)=true := by
  simp only [t6_893jobs,List.all_append,List.all_nil,t6_893part0,Bool.and_self]
theorem t6_893checked : Checked tree [4,2,2,3,10,7] := by
  refine ⟨plan6621,valid6621,t6_893choices,?_⟩
  exact check_of_frontier tree 0 t6_893root t6_893jobs t6_893frontier t6_893all
theorem t6_894choices : plan6986.choices=[4,2,2,5,7,7].map (options 6 4) := by rfl


theorem t6_894part0 : t6_894jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_894frontier : t6_894root.frontier 0=t6_894jobs := by rfl
theorem t6_894all : t6_894jobs.all (Job.check tree)=true := by
  simp only [t6_894jobs,List.all_append,List.all_nil,t6_894part0,Bool.and_self]
theorem t6_894checked : Checked tree [4,2,2,5,7,7] := by
  refine ⟨plan6986,valid6986,t6_894choices,?_⟩
  exact check_of_frontier tree 0 t6_894root t6_894jobs t6_894frontier t6_894all
theorem t6_895choices : plan6987.choices=[4,2,2,6,6,7].map (options 6 4) := by rfl


theorem t6_895part0 : t6_895jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_895frontier : t6_895root.frontier 0=t6_895jobs := by rfl
theorem t6_895all : t6_895jobs.all (Job.check tree)=true := by
  simp only [t6_895jobs,List.all_append,List.all_nil,t6_895part0,Bool.and_self]
theorem t6_895checked : Checked tree [4,2,2,6,6,7] := by
  refine ⟨plan6987,valid6987,t6_895choices,?_⟩
  exact check_of_frontier tree 0 t6_895root t6_895jobs t6_895frontier t6_895all
theorem t6_896choices : plan6988.choices=[4,2,2,6,7,7].map (options 6 4) := by rfl


theorem t6_896part0 : t6_896jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_896frontier : t6_896root.frontier 0=t6_896jobs := by rfl
theorem t6_896all : t6_896jobs.all (Job.check tree)=true := by
  simp only [t6_896jobs,List.all_append,List.all_nil,t6_896part0,Bool.and_self]
theorem t6_896checked : Checked tree [4,2,2,6,7,7] := by
  refine ⟨plan6988,valid6988,t6_896choices,?_⟩
  exact check_of_frontier tree 0 t6_896root t6_896jobs t6_896frontier t6_896all
theorem t6_897choices : plan6989.choices=[4,2,2,6,10,7].map (options 6 4) := by rfl


theorem t6_897part0 : t6_897jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_897frontier : t6_897root.frontier 0=t6_897jobs := by rfl
theorem t6_897all : t6_897jobs.all (Job.check tree)=true := by
  simp only [t6_897jobs,List.all_append,List.all_nil,t6_897part0,Bool.and_self]
theorem t6_897checked : Checked tree [4,2,2,6,10,7] := by
  refine ⟨plan6989,valid6989,t6_897choices,?_⟩
  exact check_of_frontier tree 0 t6_897root t6_897jobs t6_897frontier t6_897all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks115 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_886checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_887checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_888checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_889checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_890checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_891checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_892checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_893checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_894checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_895checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_896checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_897checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_884checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_885checked⟩
