-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks183
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:13:20.842001+00:00
-- url     : https://prove2.me/submissions/52690eb2-07b3-481b-9c4f-0a098bd7c12d

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks183
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks183
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
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





































































































theorem valid147 : plan147.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid150 : plan150.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid153 : plan153.Valid := valid_step _ _ _ valid0 (by decide +kernel)





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

















































theorem valid601 : plan601.Valid := valid_step _ _ _ valid147 (by decide +kernel)











theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)











theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)











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





theorem valid1635 : plan1635.Valid := valid_step _ _ _ valid601 (by decide +kernel)































theorem valid1651 : plan1651.Valid := valid_step _ _ _ valid607 (by decide +kernel)





theorem valid1654 : plan1654.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1655 : plan1655.Valid := valid_step _ _ _ valid607 (by decide +kernel)











theorem valid1661 : plan1661.Valid := valid_step _ _ _ valid613 (by decide +kernel)





theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)

















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

































theorem valid3569 : plan3569.Valid := valid_step _ _ _ valid1635 (by decide +kernel)



























theorem valid3583 : plan3583.Valid := valid_step _ _ _ valid1651 (by decide +kernel)



theorem valid3585 : plan3585.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

theorem valid3586 : plan3586.Valid := valid_step _ _ _ valid1655 (by decide +kernel)













































theorem valid3609 : plan3609.Valid := valid_step _ _ _ valid1661 (by decide +kernel)





theorem valid3612 : plan3612.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3613 : plan3613.Valid := valid_step _ _ _ valid1665 (by decide +kernel)





theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3617 : plan3617.Valid := valid_step _ _ _ valid1664 (by decide +kernel)





















theorem valid3628 : plan3628.Valid := valid_step _ _ _ valid1674 (by decide +kernel)







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











































































































































theorem valid6118 : plan6118.Valid := valid_step _ _ _ valid3569 (by decide +kernel)

































theorem valid6135 : plan6135.Valid := valid_step _ _ _ valid3583 (by decide +kernel)



theorem valid6137 : plan6137.Valid := valid_step _ _ _ valid3585 (by decide +kernel)

theorem valid6138 : plan6138.Valid := valid_step _ _ _ valid3586 (by decide +kernel)












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

























theorem valid6157 : plan6157.Valid := valid_step _ _ _ valid3616 (by decide +kernel)









theorem valid6162 : plan6162.Valid := valid_step _ _ _ valid3609 (by decide +kernel)



theorem valid6164 : plan6164.Valid := valid_step _ _ _ valid3612 (by decide +kernel)

theorem valid6165 : plan6165.Valid := valid_step _ _ _ valid3613 (by decide +kernel)



theorem valid6167 : plan6167.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6168 : plan6168.Valid := valid_step _ _ _ valid3617 (by decide +kernel)















































































theorem valid6208 : plan6208.Valid := valid_step _ _ _ valid3632 (by decide +kernel)















theorem valid6216 : plan6216.Valid := valid_step _ _ _ valid3628 (by decide +kernel)







theorem valid6220 : plan6220.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6221 : plan6221.Valid := valid_step _ _ _ valid3633 (by decide +kernel)







theorem valid6225 : plan6225.Valid := valid_step _ _ _ valid3632 (by decide +kernel)





theorem valid6228 : plan6228.Valid := valid_step _ _ _ valid3632 (by decide +kernel)



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

















































theorem valid8089 : plan8089.Valid := valid_step _ _ _ valid6118 (by decide +kernel)



































theorem valid8107 : plan8107.Valid := valid_step _ _ _ valid6137 (by decide +kernel)



















theorem valid8117 : plan8117.Valid := valid_step _ _ _ valid6135 (by decide +kernel)



theorem valid8119 : plan8119.Valid := valid_step _ _ _ valid6137 (by decide +kernel)

theorem valid8120 : plan8120.Valid := valid_step _ _ _ valid6138 (by decide +kernel)























































theorem valid8148 : plan8148.Valid := valid_step _ _ _ valid6157 (by decide +kernel)

theorem valid8149 : plan8149.Valid := valid_step _ _ _ valid6164 (by decide +kernel)

theorem valid8150 : plan8150.Valid := valid_step _ _ _ valid6167 (by decide +kernel)

theorem valid8151 : plan8151.Valid := valid_step _ _ _ valid6168 (by decide +kernel)


















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

















theorem valid8457 : plan8457.Valid := valid_step _ _ _ valid8089 (by decide +kernel)





































































































































theorem valid8524 : plan8524.Valid := valid_step _ _ _ valid8107 (by decide +kernel)

theorem valid8525 : plan8525.Valid := valid_step _ _ _ valid8117 (by decide +kernel)

theorem valid8526 : plan8526.Valid := valid_step _ _ _ valid8119 (by decide +kernel)

theorem valid8527 : plan8527.Valid := valid_step _ _ _ valid8120 (by decide +kernel)


































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

















theorem valid8169 : plan8169.Valid := valid_step _ _ _ valid6162 (by decide +kernel)



theorem valid8171 : plan8171.Valid := valid_step _ _ _ valid6164 (by decide +kernel)

theorem valid8172 : plan8172.Valid := valid_step _ _ _ valid6165 (by decide +kernel)



theorem valid8174 : plan8174.Valid := valid_step _ _ _ valid6167 (by decide +kernel)































































































theorem valid8222 : plan8222.Valid := valid_step _ _ _ valid6208 (by decide +kernel)

theorem valid8223 : plan8223.Valid := valid_step _ _ _ valid6216 (by decide +kernel)

theorem valid8224 : plan8224.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8225 : plan8225.Valid := valid_step _ _ _ valid6221 (by decide +kernel)

theorem valid8226 : plan8226.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8227 : plan8227.Valid := valid_step _ _ _ valid6228 (by decide +kernel)

theorem valid8228 : plan8228.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8229 : plan8229.Valid := valid_step _ _ _ valid6231 (by decide +kernel)






















































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





























































































































theorem valid8319 : plan8319.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8320 : plan8320.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8321 : plan8321.Valid := valid_step _ _ _ valid6231 (by decide +kernel)

theorem valid8322 : plan8322.Valid := valid_step _ _ _ valid6232 (by decide +kernel)

theorem valid8323 : plan8323.Valid := valid_step _ _ _ valid6233 (by decide +kernel)

theorem valid8324 : plan8324.Valid := valid_step _ _ _ valid6234 (by decide +kernel)
























































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





























theorem valid8655 : plan8655.Valid := valid_step _ _ _ valid8148 (by decide +kernel)

theorem valid8656 : plan8656.Valid := valid_step _ _ _ valid8149 (by decide +kernel)

theorem valid8657 : plan8657.Valid := valid_step _ _ _ valid8150 (by decide +kernel)

theorem valid8658 : plan8658.Valid := valid_step _ _ _ valid8151 (by decide +kernel)

theorem valid8659 : plan8659.Valid := valid_step _ _ _ valid8169 (by decide +kernel)

theorem valid8660 : plan8660.Valid := valid_step _ _ _ valid8171 (by decide +kernel)

theorem valid8661 : plan8661.Valid := valid_step _ _ _ valid8172 (by decide +kernel)

theorem valid8662 : plan8662.Valid := valid_step _ _ _ valid8174 (by decide +kernel)




















































































































































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



theorem valid8834 : plan8834.Valid := valid_step _ _ _ valid8319 (by decide +kernel)

theorem valid8835 : plan8835.Valid := valid_step _ _ _ valid8320 (by decide +kernel)

theorem valid8836 : plan8836.Valid := valid_step _ _ _ valid8321 (by decide +kernel)

theorem valid8837 : plan8837.Valid := valid_step _ _ _ valid8322 (by decide +kernel)

theorem valid8838 : plan8838.Valid := valid_step _ _ _ valid8323 (by decide +kernel)

theorem valid8839 : plan8839.Valid := valid_step _ _ _ valid8324 (by decide +kernel)

theorem valid8840 : plan8840.Valid := valid_step _ _ _ valid8222 (by decide +kernel)

theorem valid8841 : plan8841.Valid := valid_step _ _ _ valid8223 (by decide +kernel)

theorem valid8842 : plan8842.Valid := valid_step _ _ _ valid8224 (by decide +kernel)

theorem valid8843 : plan8843.Valid := valid_step _ _ _ valid8225 (by decide +kernel)

theorem valid8844 : plan8844.Valid := valid_step _ _ _ valid8226 (by decide +kernel)

theorem valid8845 : plan8845.Valid := valid_step _ _ _ valid8227 (by decide +kernel)

theorem valid8846 : plan8846.Valid := valid_step _ _ _ valid8228 (by decide +kernel)

theorem valid8847 : plan8847.Valid := valid_step _ _ _ valid8229 (by decide +kernel)


































































































































































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
theorem t7_336choices : plan8834.choices=[3,10,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_336part0 : t7_336jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_336part1 : t7_336jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_336part2 : t7_336jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_336part3 : t7_336jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_336frontier : t7_336root.frontier 2=t7_336jobs := by rfl
theorem t7_336all : t7_336jobs.all (Job.check tree)=true := by
  simp only [t7_336jobs,List.all_append,List.all_nil,t7_336part0,t7_336part1,t7_336part2,t7_336part3,Bool.and_self]
theorem t7_336checked : Checked tree [3,10,7,7,7,7,7] := by
  refine ⟨plan8834,valid8834,t7_336choices,?_⟩
  exact check_of_frontier tree 2 t7_336root t7_336jobs t7_336frontier t7_336all
theorem t7_337choices : plan8835.choices=[3,10,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_337part0 : t7_337jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_337part1 : t7_337jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_337part2 : t7_337jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_337part3 : t7_337jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_337frontier : t7_337root.frontier 2=t7_337jobs := by rfl
theorem t7_337all : t7_337jobs.all (Job.check tree)=true := by
  simp only [t7_337jobs,List.all_append,List.all_nil,t7_337part0,t7_337part1,t7_337part2,t7_337part3,Bool.and_self]
theorem t7_337checked : Checked tree [3,10,10,7,7,7,7] := by
  refine ⟨plan8835,valid8835,t7_337choices,?_⟩
  exact check_of_frontier tree 2 t7_337root t7_337jobs t7_337frontier t7_337all
theorem t7_338choices : plan8836.choices=[3,10,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_338part0 : t7_338jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_338part1 : t7_338jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_338frontier : t7_338root.frontier 2=t7_338jobs := by rfl
theorem t7_338all : t7_338jobs.all (Job.check tree)=true := by
  simp only [t7_338jobs,List.all_append,List.all_nil,t7_338part0,t7_338part1,Bool.and_self]
theorem t7_338checked : Checked tree [3,10,10,10,7,7,7] := by
  refine ⟨plan8836,valid8836,t7_338choices,?_⟩
  exact check_of_frontier tree 2 t7_338root t7_338jobs t7_338frontier t7_338all
theorem t7_339choices : plan8837.choices=[3,10,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_339part0 : t7_339jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_339frontier : t7_339root.frontier 0=t7_339jobs := by rfl
theorem t7_339all : t7_339jobs.all (Job.check tree)=true := by
  simp only [t7_339jobs,List.all_append,List.all_nil,t7_339part0,Bool.and_self]
theorem t7_339checked : Checked tree [3,10,10,10,10,7,7] := by
  refine ⟨plan8837,valid8837,t7_339choices,?_⟩
  exact check_of_frontier tree 0 t7_339root t7_339jobs t7_339frontier t7_339all
theorem t7_340choices : plan8838.choices=[3,10,10,10,10,10,7].map (options 7 6) := by rfl


theorem t7_340part0 : t7_340jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_340frontier : t7_340root.frontier 0=t7_340jobs := by rfl
theorem t7_340all : t7_340jobs.all (Job.check tree)=true := by
  simp only [t7_340jobs,List.all_append,List.all_nil,t7_340part0,Bool.and_self]
theorem t7_340checked : Checked tree [3,10,10,10,10,10,7] := by
  refine ⟨plan8838,valid8838,t7_340choices,?_⟩
  exact check_of_frontier tree 0 t7_340root t7_340jobs t7_340frontier t7_340all
theorem t7_341choices : plan8839.choices=[3,10,10,10,10,10,10].map (options 7 6) := by rfl


theorem t7_341part0 : t7_341jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_341frontier : t7_341root.frontier 0=t7_341jobs := by rfl
theorem t7_341all : t7_341jobs.all (Job.check tree)=true := by
  simp only [t7_341jobs,List.all_append,List.all_nil,t7_341part0,Bool.and_self]
theorem t7_341checked : Checked tree [3,10,10,10,10,10,10] := by
  refine ⟨plan8839,valid8839,t7_341choices,?_⟩
  exact check_of_frontier tree 0 t7_341root t7_341jobs t7_341frontier t7_341all
theorem t7_342choices : plan8655.choices=[4,2,2,7,7,7,7].map (options 7 5) := by rfl


theorem t7_342part0 : t7_342jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_342frontier : t7_342root.frontier 0=t7_342jobs := by rfl
theorem t7_342all : t7_342jobs.all (Job.check tree)=true := by
  simp only [t7_342jobs,List.all_append,List.all_nil,t7_342part0,Bool.and_self]
theorem t7_342checked : Checked tree [4,2,2,7,7,7,7] := by
  refine ⟨plan8655,valid8655,t7_342choices,?_⟩
  exact check_of_frontier tree 0 t7_342root t7_342jobs t7_342frontier t7_342all
theorem t7_343choices : plan8524.choices=[4,2,3,3,7,7,7].map (options 7 4) := by rfl


theorem t7_343part0 : t7_343jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_343frontier : t7_343root.frontier 0=t7_343jobs := by rfl
theorem t7_343all : t7_343jobs.all (Job.check tree)=true := by
  simp only [t7_343jobs,List.all_append,List.all_nil,t7_343part0,Bool.and_self]
theorem t7_343checked : Checked tree [4,2,3,3,7,7,7] := by
  refine ⟨plan8524,valid8524,t7_343choices,?_⟩
  exact check_of_frontier tree 0 t7_343root t7_343jobs t7_343frontier t7_343all
theorem t7_344choices : plan8656.choices=[4,2,3,6,7,7,7].map (options 7 5) := by rfl


theorem t7_344part0 : t7_344jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_344frontier : t7_344root.frontier 0=t7_344jobs := by rfl
theorem t7_344all : t7_344jobs.all (Job.check tree)=true := by
  simp only [t7_344jobs,List.all_append,List.all_nil,t7_344part0,Bool.and_self]
theorem t7_344checked : Checked tree [4,2,3,6,7,7,7] := by
  refine ⟨plan8656,valid8656,t7_344choices,?_⟩
  exact check_of_frontier tree 0 t7_344root t7_344jobs t7_344frontier t7_344all
theorem t7_345choices : plan8657.choices=[4,2,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_345part0 : t7_345jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_345frontier : t7_345root.frontier 0=t7_345jobs := by rfl
theorem t7_345all : t7_345jobs.all (Job.check tree)=true := by
  simp only [t7_345jobs,List.all_append,List.all_nil,t7_345part0,Bool.and_self]
theorem t7_345checked : Checked tree [4,2,3,7,7,7,7] := by
  refine ⟨plan8657,valid8657,t7_345choices,?_⟩
  exact check_of_frontier tree 0 t7_345root t7_345jobs t7_345frontier t7_345all
theorem t7_346choices : plan8658.choices=[4,2,3,10,7,7,7].map (options 7 5) := by rfl


theorem t7_346part0 : t7_346jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_346frontier : t7_346root.frontier 0=t7_346jobs := by rfl
theorem t7_346all : t7_346jobs.all (Job.check tree)=true := by
  simp only [t7_346jobs,List.all_append,List.all_nil,t7_346part0,Bool.and_self]
theorem t7_346checked : Checked tree [4,2,3,10,7,7,7] := by
  refine ⟨plan8658,valid8658,t7_346choices,?_⟩
  exact check_of_frontier tree 0 t7_346root t7_346jobs t7_346frontier t7_346all
theorem t7_347choices : plan8840.choices=[4,2,5,7,7,7,7].map (options 7 6) := by rfl


theorem t7_347part0 : t7_347jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_347frontier : t7_347root.frontier 0=t7_347jobs := by rfl
theorem t7_347all : t7_347jobs.all (Job.check tree)=true := by
  simp only [t7_347jobs,List.all_append,List.all_nil,t7_347part0,Bool.and_self]
theorem t7_347checked : Checked tree [4,2,5,7,7,7,7] := by
  refine ⟨plan8840,valid8840,t7_347choices,?_⟩
  exact check_of_frontier tree 0 t7_347root t7_347jobs t7_347frontier t7_347all
theorem t7_348choices : plan8841.choices=[4,2,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_348part0 : t7_348jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_348frontier : t7_348root.frontier 0=t7_348jobs := by rfl
theorem t7_348all : t7_348jobs.all (Job.check tree)=true := by
  simp only [t7_348jobs,List.all_append,List.all_nil,t7_348part0,Bool.and_self]
theorem t7_348checked : Checked tree [4,2,6,6,7,7,7] := by
  refine ⟨plan8841,valid8841,t7_348choices,?_⟩
  exact check_of_frontier tree 0 t7_348root t7_348jobs t7_348frontier t7_348all
theorem t7_349choices : plan8842.choices=[4,2,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_349part0 : t7_349jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_349frontier : t7_349root.frontier 0=t7_349jobs := by rfl
theorem t7_349all : t7_349jobs.all (Job.check tree)=true := by
  simp only [t7_349jobs,List.all_append,List.all_nil,t7_349part0,Bool.and_self]
theorem t7_349checked : Checked tree [4,2,6,7,7,7,7] := by
  refine ⟨plan8842,valid8842,t7_349choices,?_⟩
  exact check_of_frontier tree 0 t7_349root t7_349jobs t7_349frontier t7_349all
theorem t7_350choices : plan8843.choices=[4,2,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_350part0 : t7_350jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_350frontier : t7_350root.frontier 0=t7_350jobs := by rfl
theorem t7_350all : t7_350jobs.all (Job.check tree)=true := by
  simp only [t7_350jobs,List.all_append,List.all_nil,t7_350part0,Bool.and_self]
theorem t7_350checked : Checked tree [4,2,6,10,7,7,7] := by
  refine ⟨plan8843,valid8843,t7_350choices,?_⟩
  exact check_of_frontier tree 0 t7_350root t7_350jobs t7_350frontier t7_350all
theorem t7_351choices : plan8844.choices=[4,2,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_351part0 : t7_351jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_351frontier : t7_351root.frontier 0=t7_351jobs := by rfl
theorem t7_351all : t7_351jobs.all (Job.check tree)=true := by
  simp only [t7_351jobs,List.all_append,List.all_nil,t7_351part0,Bool.and_self]
theorem t7_351checked : Checked tree [4,2,7,7,7,7,7] := by
  refine ⟨plan8844,valid8844,t7_351choices,?_⟩
  exact check_of_frontier tree 0 t7_351root t7_351jobs t7_351frontier t7_351all
theorem t7_352choices : plan8845.choices=[4,2,9,7,7,7,7].map (options 7 6) := by rfl


theorem t7_352part0 : t7_352jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_352frontier : t7_352root.frontier 0=t7_352jobs := by rfl
theorem t7_352all : t7_352jobs.all (Job.check tree)=true := by
  simp only [t7_352jobs,List.all_append,List.all_nil,t7_352part0,Bool.and_self]
theorem t7_352checked : Checked tree [4,2,9,7,7,7,7] := by
  refine ⟨plan8845,valid8845,t7_352choices,?_⟩
  exact check_of_frontier tree 0 t7_352root t7_352jobs t7_352frontier t7_352all
theorem t7_353choices : plan8846.choices=[4,2,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_353part0 : t7_353jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_353frontier : t7_353root.frontier 0=t7_353jobs := by rfl
theorem t7_353all : t7_353jobs.all (Job.check tree)=true := by
  simp only [t7_353jobs,List.all_append,List.all_nil,t7_353part0,Bool.and_self]
theorem t7_353checked : Checked tree [4,2,10,7,7,7,7] := by
  refine ⟨plan8846,valid8846,t7_353choices,?_⟩
  exact check_of_frontier tree 0 t7_353root t7_353jobs t7_353frontier t7_353all
theorem t7_354choices : plan8847.choices=[4,2,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_354part0 : t7_354jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_354frontier : t7_354root.frontier 0=t7_354jobs := by rfl
theorem t7_354all : t7_354jobs.all (Job.check tree)=true := by
  simp only [t7_354jobs,List.all_append,List.all_nil,t7_354part0,Bool.and_self]
theorem t7_354checked : Checked tree [4,2,10,10,7,7,7] := by
  refine ⟨plan8847,valid8847,t7_354choices,?_⟩
  exact check_of_frontier tree 0 t7_354root t7_354jobs t7_354frontier t7_354all
theorem t7_355choices : plan8457.choices=[4,3,3,3,3,7,7].map (options 7 3) := by rfl


theorem t7_355part0 : t7_355jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_355frontier : t7_355root.frontier 0=t7_355jobs := by rfl
theorem t7_355all : t7_355jobs.all (Job.check tree)=true := by
  simp only [t7_355jobs,List.all_append,List.all_nil,t7_355part0,Bool.and_self]
theorem t7_355checked : Checked tree [4,3,3,3,3,7,7] := by
  refine ⟨plan8457,valid8457,t7_355choices,?_⟩
  exact check_of_frontier tree 0 t7_355root t7_355jobs t7_355frontier t7_355all
theorem t7_356choices : plan8525.choices=[4,3,3,3,6,7,7].map (options 7 4) := by rfl


theorem t7_356part0 : t7_356jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_356frontier : t7_356root.frontier 0=t7_356jobs := by rfl
theorem t7_356all : t7_356jobs.all (Job.check tree)=true := by
  simp only [t7_356jobs,List.all_append,List.all_nil,t7_356part0,Bool.and_self]
theorem t7_356checked : Checked tree [4,3,3,3,6,7,7] := by
  refine ⟨plan8525,valid8525,t7_356choices,?_⟩
  exact check_of_frontier tree 0 t7_356root t7_356jobs t7_356frontier t7_356all
theorem t7_357choices : plan8526.choices=[4,3,3,3,7,7,7].map (options 7 4) := by rfl


theorem t7_357part0 : t7_357jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_357frontier : t7_357root.frontier 0=t7_357jobs := by rfl
theorem t7_357all : t7_357jobs.all (Job.check tree)=true := by
  simp only [t7_357jobs,List.all_append,List.all_nil,t7_357part0,Bool.and_self]
theorem t7_357checked : Checked tree [4,3,3,3,7,7,7] := by
  refine ⟨plan8526,valid8526,t7_357choices,?_⟩
  exact check_of_frontier tree 0 t7_357root t7_357jobs t7_357frontier t7_357all
theorem t7_358choices : plan8527.choices=[4,3,3,3,10,7,7].map (options 7 4) := by rfl


theorem t7_358part0 : t7_358jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_358frontier : t7_358root.frontier 0=t7_358jobs := by rfl
theorem t7_358all : t7_358jobs.all (Job.check tree)=true := by
  simp only [t7_358jobs,List.all_append,List.all_nil,t7_358part0,Bool.and_self]
theorem t7_358checked : Checked tree [4,3,3,3,10,7,7] := by
  refine ⟨plan8527,valid8527,t7_358choices,?_⟩
  exact check_of_frontier tree 0 t7_358root t7_358jobs t7_358frontier t7_358all
theorem t7_359choices : plan8659.choices=[4,3,3,6,6,7,7].map (options 7 5) := by rfl


theorem t7_359part0 : t7_359jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_359frontier : t7_359root.frontier 0=t7_359jobs := by rfl
theorem t7_359all : t7_359jobs.all (Job.check tree)=true := by
  simp only [t7_359jobs,List.all_append,List.all_nil,t7_359part0,Bool.and_self]
theorem t7_359checked : Checked tree [4,3,3,6,6,7,7] := by
  refine ⟨plan8659,valid8659,t7_359choices,?_⟩
  exact check_of_frontier tree 0 t7_359root t7_359jobs t7_359frontier t7_359all
theorem t7_360choices : plan8660.choices=[4,3,3,6,7,7,7].map (options 7 5) := by rfl


theorem t7_360part0 : t7_360jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_360frontier : t7_360root.frontier 0=t7_360jobs := by rfl
theorem t7_360all : t7_360jobs.all (Job.check tree)=true := by
  simp only [t7_360jobs,List.all_append,List.all_nil,t7_360part0,Bool.and_self]
theorem t7_360checked : Checked tree [4,3,3,6,7,7,7] := by
  refine ⟨plan8660,valid8660,t7_360choices,?_⟩
  exact check_of_frontier tree 0 t7_360root t7_360jobs t7_360frontier t7_360all
theorem t7_361choices : plan8661.choices=[4,3,3,6,10,7,7].map (options 7 5) := by rfl


theorem t7_361part0 : t7_361jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_361frontier : t7_361root.frontier 0=t7_361jobs := by rfl
theorem t7_361all : t7_361jobs.all (Job.check tree)=true := by
  simp only [t7_361jobs,List.all_append,List.all_nil,t7_361part0,Bool.and_self]
theorem t7_361checked : Checked tree [4,3,3,6,10,7,7] := by
  refine ⟨plan8661,valid8661,t7_361choices,?_⟩
  exact check_of_frontier tree 0 t7_361root t7_361jobs t7_361frontier t7_361all
theorem t7_362choices : plan8662.choices=[4,3,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_362part0 : t7_362jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_362frontier : t7_362root.frontier 0=t7_362jobs := by rfl
theorem t7_362all : t7_362jobs.all (Job.check tree)=true := by
  simp only [t7_362jobs,List.all_append,List.all_nil,t7_362part0,Bool.and_self]
theorem t7_362checked : Checked tree [4,3,3,7,7,7,7] := by
  refine ⟨plan8662,valid8662,t7_362choices,?_⟩
  exact check_of_frontier tree 0 t7_362root t7_362jobs t7_362frontier t7_362all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks183 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_339checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_340checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_341checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_342checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_343checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_344checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_345checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_346checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_347checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_348checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_349checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_350checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_351checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_352checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_353checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_354checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_355checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_356checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_357checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_358checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_359checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_360checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_361checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_362checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_336checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_337checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_338checked⟩
