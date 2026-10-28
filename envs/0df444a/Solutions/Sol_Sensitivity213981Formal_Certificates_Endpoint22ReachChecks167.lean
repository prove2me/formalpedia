-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks167
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:07:39.823903+00:00
-- url     : https://prove2.me/submissions/d30275b1-2b32-4227-b2f2-af22ff4a9ec3

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks167
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks167
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans086
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans091
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





































































































theorem valid147 : plan147.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid150 : plan150.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid153 : plan153.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid156 : plan156.Valid := valid_step _ _ _ valid0 (by decide +kernel)








































































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

















































theorem valid601 : plan601.Valid := valid_step _ _ _ valid147 (by decide +kernel)











theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)











theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)







theorem valid617 : plan617.Valid := valid_step _ _ _ valid156 (by decide +kernel)



theorem valid619 : plan619.Valid := valid_step _ _ _ valid156 (by decide +kernel)

theorem valid620 : plan620.Valid := valid_step _ _ _ valid156 (by decide +kernel)








































































































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





theorem valid1635 : plan1635.Valid := valid_step _ _ _ valid601 (by decide +kernel)































theorem valid1651 : plan1651.Valid := valid_step _ _ _ valid607 (by decide +kernel)

























theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)









theorem valid1669 : plan1669.Valid := valid_step _ _ _ valid617 (by decide +kernel)



theorem valid1671 : plan1671.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1672 : plan1672.Valid := valid_step _ _ _ valid620 (by decide +kernel)



theorem valid1674 : plan1674.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1675 : plan1675.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1676 : plan1676.Valid := valid_step _ _ _ valid620 (by decide +kernel)








































































































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

































theorem valid3569 : plan3569.Valid := valid_step _ _ _ valid1635 (by decide +kernel)



























theorem valid3583 : plan3583.Valid := valid_step _ _ _ valid1651 (by decide +kernel)









































theorem valid3604 : plan3604.Valid := valid_step _ _ _ valid1664 (by decide +kernel)





































theorem valid3623 : plan3623.Valid := valid_step _ _ _ valid1669 (by decide +kernel)



theorem valid3625 : plan3625.Valid := valid_step _ _ _ valid1671 (by decide +kernel)

theorem valid3626 : plan3626.Valid := valid_step _ _ _ valid1672 (by decide +kernel)



theorem valid3628 : plan3628.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3629 : plan3629.Valid := valid_step _ _ _ valid1675 (by decide +kernel)

theorem valid3630 : plan3630.Valid := valid_step _ _ _ valid1676 (by decide +kernel)



theorem valid3632 : plan3632.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3633 : plan3633.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3634 : plan3634.Valid := valid_step _ _ _ valid1675 (by decide +kernel)

theorem valid3635 : plan3635.Valid := valid_step _ _ _ valid1676 (by decide +kernel)


























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











































































































































theorem valid6118 : plan6118.Valid := valid_step _ _ _ valid3569 (by decide +kernel)

































theorem valid6135 : plan6135.Valid := valid_step _ _ _ valid3583 (by decide +kernel)


















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





























































































theorem valid6191 : plan6191.Valid := valid_step _ _ _ valid3604 (by decide +kernel)







































theorem valid6211 : plan6211.Valid := valid_step _ _ _ valid3623 (by decide +kernel)



theorem valid6213 : plan6213.Valid := valid_step _ _ _ valid3625 (by decide +kernel)

theorem valid6214 : plan6214.Valid := valid_step _ _ _ valid3626 (by decide +kernel)



theorem valid6216 : plan6216.Valid := valid_step _ _ _ valid3628 (by decide +kernel)

theorem valid6217 : plan6217.Valid := valid_step _ _ _ valid3629 (by decide +kernel)

theorem valid6218 : plan6218.Valid := valid_step _ _ _ valid3630 (by decide +kernel)



theorem valid6220 : plan6220.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6221 : plan6221.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6222 : plan6222.Valid := valid_step _ _ _ valid3634 (by decide +kernel)

theorem valid6223 : plan6223.Valid := valid_step _ _ _ valid3635 (by decide +kernel)



theorem valid6225 : plan6225.Valid := valid_step _ _ _ valid3632 (by decide +kernel)



theorem valid6227 : plan6227.Valid := valid_step _ _ _ valid3628 (by decide +kernel)

theorem valid6228 : plan6228.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6229 : plan6229.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6230 : plan6230.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6231 : plan6231.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6232 : plan6232.Valid := valid_step _ _ _ valid3634 (by decide +kernel)

theorem valid6233 : plan6233.Valid := valid_step _ _ _ valid3635 (by decide +kernel)














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











































































theorem valid8102 : plan8102.Valid := valid_step _ _ _ valid6118 (by decide +kernel)















































































theorem valid8142 : plan8142.Valid := valid_step _ _ _ valid6135 (by decide +kernel)




































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



























































































































































































theorem valid8446 : plan8446.Valid := valid_step _ _ _ valid8102 (by decide +kernel)




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



















































































































theorem valid8506 : plan8506.Valid := valid_step _ _ _ valid8142 (by decide +kernel)












































































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



































































































theorem valid8210 : plan8210.Valid := valid_step _ _ _ valid6191 (by decide +kernel)




























































































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



































































































































































theorem valid8626 : plan8626.Valid := valid_step _ _ _ valid8210 (by decide +kernel)




























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

















theorem valid8265 : plan8265.Valid := valid_step _ _ _ valid6225 (by decide +kernel)



theorem valid8267 : plan8267.Valid := valid_step _ _ _ valid6227 (by decide +kernel)

theorem valid8268 : plan8268.Valid := valid_step _ _ _ valid6228 (by decide +kernel)

theorem valid8269 : plan8269.Valid := valid_step _ _ _ valid6229 (by decide +kernel)

theorem valid8270 : plan8270.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8271 : plan8271.Valid := valid_step _ _ _ valid6231 (by decide +kernel)

theorem valid8272 : plan8272.Valid := valid_step _ _ _ valid6232 (by decide +kernel)



theorem valid8274 : plan8274.Valid := valid_step _ _ _ valid6211 (by decide +kernel)



theorem valid8276 : plan8276.Valid := valid_step _ _ _ valid6213 (by decide +kernel)

theorem valid8277 : plan8277.Valid := valid_step _ _ _ valid6214 (by decide +kernel)



theorem valid8279 : plan8279.Valid := valid_step _ _ _ valid6216 (by decide +kernel)

theorem valid8280 : plan8280.Valid := valid_step _ _ _ valid6217 (by decide +kernel)

theorem valid8281 : plan8281.Valid := valid_step _ _ _ valid6218 (by decide +kernel)



theorem valid8283 : plan8283.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8284 : plan8284.Valid := valid_step _ _ _ valid6221 (by decide +kernel)

theorem valid8285 : plan8285.Valid := valid_step _ _ _ valid6222 (by decide +kernel)

theorem valid8286 : plan8286.Valid := valid_step _ _ _ valid6223 (by decide +kernel)



theorem valid8288 : plan8288.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8289 : plan8289.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8290 : plan8290.Valid := valid_step _ _ _ valid6231 (by decide +kernel)

theorem valid8291 : plan8291.Valid := valid_step _ _ _ valid6232 (by decide +kernel)

theorem valid8292 : plan8292.Valid := valid_step _ _ _ valid6233 (by decide +kernel)



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





































































theorem valid8771 : plan8771.Valid := valid_step _ _ _ valid8265 (by decide +kernel)

theorem valid8772 : plan8772.Valid := valid_step _ _ _ valid8267 (by decide +kernel)

theorem valid8773 : plan8773.Valid := valid_step _ _ _ valid8268 (by decide +kernel)

theorem valid8774 : plan8774.Valid := valid_step _ _ _ valid8269 (by decide +kernel)

theorem valid8775 : plan8775.Valid := valid_step _ _ _ valid8270 (by decide +kernel)

theorem valid8776 : plan8776.Valid := valid_step _ _ _ valid8271 (by decide +kernel)

theorem valid8777 : plan8777.Valid := valid_step _ _ _ valid8272 (by decide +kernel)

theorem valid8778 : plan8778.Valid := valid_step _ _ _ valid8274 (by decide +kernel)

theorem valid8779 : plan8779.Valid := valid_step _ _ _ valid8276 (by decide +kernel)

theorem valid8780 : plan8780.Valid := valid_step _ _ _ valid8277 (by decide +kernel)

theorem valid8781 : plan8781.Valid := valid_step _ _ _ valid8279 (by decide +kernel)

theorem valid8782 : plan8782.Valid := valid_step _ _ _ valid8280 (by decide +kernel)

theorem valid8783 : plan8783.Valid := valid_step _ _ _ valid8281 (by decide +kernel)

theorem valid8784 : plan8784.Valid := valid_step _ _ _ valid8283 (by decide +kernel)

theorem valid8785 : plan8785.Valid := valid_step _ _ _ valid8284 (by decide +kernel)

theorem valid8786 : plan8786.Valid := valid_step _ _ _ valid8285 (by decide +kernel)

theorem valid8787 : plan8787.Valid := valid_step _ _ _ valid8286 (by decide +kernel)

theorem valid8788 : plan8788.Valid := valid_step _ _ _ valid8288 (by decide +kernel)

theorem valid8789 : plan8789.Valid := valid_step _ _ _ valid8289 (by decide +kernel)

theorem valid8790 : plan8790.Valid := valid_step _ _ _ valid8290 (by decide +kernel)

theorem valid8791 : plan8791.Valid := valid_step _ _ _ valid8291 (by decide +kernel)

theorem valid8792 : plan8792.Valid := valid_step _ _ _ valid8292 (by decide +kernel)

theorem valid8793 : plan8793.Valid := valid_step _ _ _ valid8294 (by decide +kernel)














































































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
theorem t7_205choices : plan8771.choices=[2,5,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_205part0 : t7_205jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_205frontier : t7_205root.frontier 0=t7_205jobs := by rfl
theorem t7_205all : t7_205jobs.all (Job.check tree)=true := by
  simp only [t7_205jobs,List.all_append,List.all_nil,t7_205part0,Bool.and_self]
theorem t7_205checked : Checked tree [2,5,7,7,7,7,7] := by
  refine ⟨plan8771,valid8771,t7_205choices,?_⟩
  exact check_of_frontier tree 0 t7_205root t7_205jobs t7_205frontier t7_205all
theorem t7_206choices : plan8626.choices=[2,5,9,3,7,7,7].map (options 7 5) := by rfl


theorem t7_206part0 : t7_206jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_206frontier : t7_206root.frontier 0=t7_206jobs := by rfl
theorem t7_206all : t7_206jobs.all (Job.check tree)=true := by
  simp only [t7_206jobs,List.all_append,List.all_nil,t7_206part0,Bool.and_self]
theorem t7_206checked : Checked tree [2,5,9,3,7,7,7] := by
  refine ⟨plan8626,valid8626,t7_206choices,?_⟩
  exact check_of_frontier tree 0 t7_206root t7_206jobs t7_206frontier t7_206all
theorem t7_207choices : plan8772.choices=[2,5,9,6,7,7,7].map (options 7 6) := by rfl


theorem t7_207part0 : t7_207jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_207frontier : t7_207root.frontier 0=t7_207jobs := by rfl
theorem t7_207all : t7_207jobs.all (Job.check tree)=true := by
  simp only [t7_207jobs,List.all_append,List.all_nil,t7_207part0,Bool.and_self]
theorem t7_207checked : Checked tree [2,5,9,6,7,7,7] := by
  refine ⟨plan8772,valid8772,t7_207choices,?_⟩
  exact check_of_frontier tree 0 t7_207root t7_207jobs t7_207frontier t7_207all
theorem t7_208choices : plan8773.choices=[2,5,9,7,7,7,7].map (options 7 6) := by rfl


theorem t7_208part0 : t7_208jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_208frontier : t7_208root.frontier 0=t7_208jobs := by rfl
theorem t7_208all : t7_208jobs.all (Job.check tree)=true := by
  simp only [t7_208jobs,List.all_append,List.all_nil,t7_208part0,Bool.and_self]
theorem t7_208checked : Checked tree [2,5,9,7,7,7,7] := by
  refine ⟨plan8773,valid8773,t7_208choices,?_⟩
  exact check_of_frontier tree 0 t7_208root t7_208jobs t7_208frontier t7_208all
theorem t7_209choices : plan8774.choices=[2,5,9,10,7,7,7].map (options 7 6) := by rfl


theorem t7_209part0 : t7_209jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_209frontier : t7_209root.frontier 0=t7_209jobs := by rfl
theorem t7_209all : t7_209jobs.all (Job.check tree)=true := by
  simp only [t7_209jobs,List.all_append,List.all_nil,t7_209part0,Bool.and_self]
theorem t7_209checked : Checked tree [2,5,9,10,7,7,7] := by
  refine ⟨plan8774,valid8774,t7_209choices,?_⟩
  exact check_of_frontier tree 0 t7_209root t7_209jobs t7_209frontier t7_209all
theorem t7_210choices : plan8775.choices=[2,5,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_210part0 : t7_210jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_210frontier : t7_210root.frontier 0=t7_210jobs := by rfl
theorem t7_210all : t7_210jobs.all (Job.check tree)=true := by
  simp only [t7_210jobs,List.all_append,List.all_nil,t7_210part0,Bool.and_self]
theorem t7_210checked : Checked tree [2,5,10,7,7,7,7] := by
  refine ⟨plan8775,valid8775,t7_210choices,?_⟩
  exact check_of_frontier tree 0 t7_210root t7_210jobs t7_210frontier t7_210all
theorem t7_211choices : plan8776.choices=[2,5,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_211part0 : t7_211jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_211frontier : t7_211root.frontier 0=t7_211jobs := by rfl
theorem t7_211all : t7_211jobs.all (Job.check tree)=true := by
  simp only [t7_211jobs,List.all_append,List.all_nil,t7_211part0,Bool.and_self]
theorem t7_211checked : Checked tree [2,5,10,10,7,7,7] := by
  refine ⟨plan8776,valid8776,t7_211choices,?_⟩
  exact check_of_frontier tree 0 t7_211root t7_211jobs t7_211frontier t7_211all
theorem t7_212choices : plan8777.choices=[2,5,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_212part0 : t7_212jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_212frontier : t7_212root.frontier 0=t7_212jobs := by rfl
theorem t7_212all : t7_212jobs.all (Job.check tree)=true := by
  simp only [t7_212jobs,List.all_append,List.all_nil,t7_212part0,Bool.and_self]
theorem t7_212checked : Checked tree [2,5,10,10,10,7,7] := by
  refine ⟨plan8777,valid8777,t7_212choices,?_⟩
  exact check_of_frontier tree 0 t7_212root t7_212jobs t7_212frontier t7_212all
theorem t7_213choices : plan8778.choices=[2,6,6,6,6,6,7].map (options 7 6) := by rfl


theorem t7_213part0 : t7_213jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_213frontier : t7_213root.frontier 0=t7_213jobs := by rfl
theorem t7_213all : t7_213jobs.all (Job.check tree)=true := by
  simp only [t7_213jobs,List.all_append,List.all_nil,t7_213part0,Bool.and_self]
theorem t7_213checked : Checked tree [2,6,6,6,6,6,7] := by
  refine ⟨plan8778,valid8778,t7_213choices,?_⟩
  exact check_of_frontier tree 0 t7_213root t7_213jobs t7_213frontier t7_213all
theorem t7_214choices : plan8779.choices=[2,6,6,6,6,7,7].map (options 7 6) := by rfl


theorem t7_214part0 : t7_214jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_214frontier : t7_214root.frontier 0=t7_214jobs := by rfl
theorem t7_214all : t7_214jobs.all (Job.check tree)=true := by
  simp only [t7_214jobs,List.all_append,List.all_nil,t7_214part0,Bool.and_self]
theorem t7_214checked : Checked tree [2,6,6,6,6,7,7] := by
  refine ⟨plan8779,valid8779,t7_214choices,?_⟩
  exact check_of_frontier tree 0 t7_214root t7_214jobs t7_214frontier t7_214all
theorem t7_215choices : plan8780.choices=[2,6,6,6,6,10,7].map (options 7 6) := by rfl


theorem t7_215part0 : t7_215jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_215frontier : t7_215root.frontier 0=t7_215jobs := by rfl
theorem t7_215all : t7_215jobs.all (Job.check tree)=true := by
  simp only [t7_215jobs,List.all_append,List.all_nil,t7_215part0,Bool.and_self]
theorem t7_215checked : Checked tree [2,6,6,6,6,10,7] := by
  refine ⟨plan8780,valid8780,t7_215choices,?_⟩
  exact check_of_frontier tree 0 t7_215root t7_215jobs t7_215frontier t7_215all
theorem t7_216choices : plan8781.choices=[2,6,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_216part0 : t7_216jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_216frontier : t7_216root.frontier 0=t7_216jobs := by rfl
theorem t7_216all : t7_216jobs.all (Job.check tree)=true := by
  simp only [t7_216jobs,List.all_append,List.all_nil,t7_216part0,Bool.and_self]
theorem t7_216checked : Checked tree [2,6,6,6,7,7,7] := by
  refine ⟨plan8781,valid8781,t7_216choices,?_⟩
  exact check_of_frontier tree 0 t7_216root t7_216jobs t7_216frontier t7_216all
theorem t7_217choices : plan8782.choices=[2,6,6,6,10,7,7].map (options 7 6) := by rfl


theorem t7_217part0 : t7_217jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_217frontier : t7_217root.frontier 0=t7_217jobs := by rfl
theorem t7_217all : t7_217jobs.all (Job.check tree)=true := by
  simp only [t7_217jobs,List.all_append,List.all_nil,t7_217part0,Bool.and_self]
theorem t7_217checked : Checked tree [2,6,6,6,10,7,7] := by
  refine ⟨plan8782,valid8782,t7_217choices,?_⟩
  exact check_of_frontier tree 0 t7_217root t7_217jobs t7_217frontier t7_217all
theorem t7_218choices : plan8783.choices=[2,6,6,6,10,10,7].map (options 7 6) := by rfl


theorem t7_218part0 : t7_218jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_218frontier : t7_218root.frontier 0=t7_218jobs := by rfl
theorem t7_218all : t7_218jobs.all (Job.check tree)=true := by
  simp only [t7_218jobs,List.all_append,List.all_nil,t7_218part0,Bool.and_self]
theorem t7_218checked : Checked tree [2,6,6,6,10,10,7] := by
  refine ⟨plan8783,valid8783,t7_218choices,?_⟩
  exact check_of_frontier tree 0 t7_218root t7_218jobs t7_218frontier t7_218all
theorem t7_219choices : plan8784.choices=[2,6,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_219part0 : t7_219jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_219part1 : t7_219jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_219frontier : t7_219root.frontier 1=t7_219jobs := by rfl
theorem t7_219all : t7_219jobs.all (Job.check tree)=true := by
  simp only [t7_219jobs,List.all_append,List.all_nil,t7_219part0,t7_219part1,Bool.and_self]
theorem t7_219checked : Checked tree [2,6,6,7,7,7,7] := by
  refine ⟨plan8784,valid8784,t7_219choices,?_⟩
  exact check_of_frontier tree 1 t7_219root t7_219jobs t7_219frontier t7_219all
theorem t7_220choices : plan8785.choices=[2,6,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_220part0 : t7_220jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_220part1 : t7_220jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_220frontier : t7_220root.frontier 1=t7_220jobs := by rfl
theorem t7_220all : t7_220jobs.all (Job.check tree)=true := by
  simp only [t7_220jobs,List.all_append,List.all_nil,t7_220part0,t7_220part1,Bool.and_self]
theorem t7_220checked : Checked tree [2,6,6,10,7,7,7] := by
  refine ⟨plan8785,valid8785,t7_220choices,?_⟩
  exact check_of_frontier tree 1 t7_220root t7_220jobs t7_220frontier t7_220all
theorem t7_221choices : plan8786.choices=[2,6,6,10,10,7,7].map (options 7 6) := by rfl


theorem t7_221part0 : t7_221jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_221frontier : t7_221root.frontier 0=t7_221jobs := by rfl
theorem t7_221all : t7_221jobs.all (Job.check tree)=true := by
  simp only [t7_221jobs,List.all_append,List.all_nil,t7_221part0,Bool.and_self]
theorem t7_221checked : Checked tree [2,6,6,10,10,7,7] := by
  refine ⟨plan8786,valid8786,t7_221choices,?_⟩
  exact check_of_frontier tree 0 t7_221root t7_221jobs t7_221frontier t7_221all
theorem t7_222choices : plan8787.choices=[2,6,6,10,10,10,7].map (options 7 6) := by rfl


theorem t7_222part0 : t7_222jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_222frontier : t7_222root.frontier 0=t7_222jobs := by rfl
theorem t7_222all : t7_222jobs.all (Job.check tree)=true := by
  simp only [t7_222jobs,List.all_append,List.all_nil,t7_222part0,Bool.and_self]
theorem t7_222checked : Checked tree [2,6,6,10,10,10,7] := by
  refine ⟨plan8787,valid8787,t7_222choices,?_⟩
  exact check_of_frontier tree 0 t7_222root t7_222jobs t7_222frontier t7_222all
theorem t7_223choices : plan8788.choices=[2,6,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_223part0 : t7_223jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_223part1 : t7_223jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_223frontier : t7_223root.frontier 1=t7_223jobs := by rfl
theorem t7_223all : t7_223jobs.all (Job.check tree)=true := by
  simp only [t7_223jobs,List.all_append,List.all_nil,t7_223part0,t7_223part1,Bool.and_self]
theorem t7_223checked : Checked tree [2,6,7,7,7,7,7] := by
  refine ⟨plan8788,valid8788,t7_223choices,?_⟩
  exact check_of_frontier tree 1 t7_223root t7_223jobs t7_223frontier t7_223all
theorem t7_224choices : plan8789.choices=[2,6,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_224part0 : t7_224jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_224part1 : t7_224jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_224frontier : t7_224root.frontier 2=t7_224jobs := by rfl
theorem t7_224all : t7_224jobs.all (Job.check tree)=true := by
  simp only [t7_224jobs,List.all_append,List.all_nil,t7_224part0,t7_224part1,Bool.and_self]
theorem t7_224checked : Checked tree [2,6,10,7,7,7,7] := by
  refine ⟨plan8789,valid8789,t7_224choices,?_⟩
  exact check_of_frontier tree 2 t7_224root t7_224jobs t7_224frontier t7_224all
theorem t7_225choices : plan8790.choices=[2,6,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_225part0 : t7_225jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_225part1 : t7_225jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_225frontier : t7_225root.frontier 1=t7_225jobs := by rfl
theorem t7_225all : t7_225jobs.all (Job.check tree)=true := by
  simp only [t7_225jobs,List.all_append,List.all_nil,t7_225part0,t7_225part1,Bool.and_self]
theorem t7_225checked : Checked tree [2,6,10,10,7,7,7] := by
  refine ⟨plan8790,valid8790,t7_225choices,?_⟩
  exact check_of_frontier tree 1 t7_225root t7_225jobs t7_225frontier t7_225all
theorem t7_226choices : plan8791.choices=[2,6,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_226part0 : t7_226jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_226frontier : t7_226root.frontier 0=t7_226jobs := by rfl
theorem t7_226all : t7_226jobs.all (Job.check tree)=true := by
  simp only [t7_226jobs,List.all_append,List.all_nil,t7_226part0,Bool.and_self]
theorem t7_226checked : Checked tree [2,6,10,10,10,7,7] := by
  refine ⟨plan8791,valid8791,t7_226choices,?_⟩
  exact check_of_frontier tree 0 t7_226root t7_226jobs t7_226frontier t7_226all
theorem t7_227choices : plan8792.choices=[2,6,10,10,10,10,7].map (options 7 6) := by rfl


theorem t7_227part0 : t7_227jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_227frontier : t7_227root.frontier 0=t7_227jobs := by rfl
theorem t7_227all : t7_227jobs.all (Job.check tree)=true := by
  simp only [t7_227jobs,List.all_append,List.all_nil,t7_227part0,Bool.and_self]
theorem t7_227checked : Checked tree [2,6,10,10,10,10,7] := by
  refine ⟨plan8792,valid8792,t7_227choices,?_⟩
  exact check_of_frontier tree 0 t7_227root t7_227jobs t7_227frontier t7_227all
theorem t7_228choices : plan8793.choices=[2,7,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_228part0 : t7_228jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_228frontier : t7_228root.frontier 0=t7_228jobs := by rfl
theorem t7_228all : t7_228jobs.all (Job.check tree)=true := by
  simp only [t7_228jobs,List.all_append,List.all_nil,t7_228part0,Bool.and_self]
theorem t7_228checked : Checked tree [2,7,7,7,7,7,7] := by
  refine ⟨plan8793,valid8793,t7_228choices,?_⟩
  exact check_of_frontier tree 0 t7_228root t7_228jobs t7_228frontier t7_228all
theorem t7_229choices : plan8446.choices=[2,9,3,3,3,7,7].map (options 7 3) := by rfl


theorem t7_229part0 : t7_229jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_229frontier : t7_229root.frontier 0=t7_229jobs := by rfl
theorem t7_229all : t7_229jobs.all (Job.check tree)=true := by
  simp only [t7_229jobs,List.all_append,List.all_nil,t7_229part0,Bool.and_self]
theorem t7_229checked : Checked tree [2,9,3,3,3,7,7] := by
  refine ⟨plan8446,valid8446,t7_229choices,?_⟩
  exact check_of_frontier tree 0 t7_229root t7_229jobs t7_229frontier t7_229all
theorem t7_230choices : plan8506.choices=[2,9,3,3,6,7,7].map (options 7 4) := by rfl


theorem t7_230part0 : t7_230jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_230part1 : t7_230jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_230frontier : t7_230root.frontier 1=t7_230jobs := by rfl
theorem t7_230all : t7_230jobs.all (Job.check tree)=true := by
  simp only [t7_230jobs,List.all_append,List.all_nil,t7_230part0,t7_230part1,Bool.and_self]
theorem t7_230checked : Checked tree [2,9,3,3,6,7,7] := by
  refine ⟨plan8506,valid8506,t7_230choices,?_⟩
  exact check_of_frontier tree 1 t7_230root t7_230jobs t7_230frontier t7_230all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks167 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_218checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_219checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_220checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_221checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_222checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_223checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_206checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_224checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_225checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_226checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_227checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_228checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_229checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_230checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_207checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_208checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_209checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_210checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_211checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_212checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_213checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_214checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_215checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_216checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_217checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_205checked⟩
