-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks181
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:10:33.442633+00:00
-- url     : https://prove2.me/submissions/be1fa8f7-cf16-442b-9322-e627ffe6c3e7

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks181
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks181
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans086
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
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

















































































































theorem valid153 : plan153.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid154 : plan154.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid155 : plan155.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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









































































theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)

theorem valid614 : plan614.Valid := valid_step _ _ _ valid153 (by decide +kernel)

theorem valid615 : plan615.Valid := valid_step _ _ _ valid154 (by decide +kernel)

theorem valid616 : plan616.Valid := valid_step _ _ _ valid155 (by decide +kernel)

theorem valid617 : plan617.Valid := valid_step _ _ _ valid156 (by decide +kernel)

theorem valid618 : plan618.Valid := valid_step _ _ _ valid157 (by decide +kernel)

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

































































theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1666 : plan1666.Valid := valid_step _ _ _ valid614 (by decide +kernel)

theorem valid1667 : plan1667.Valid := valid_step _ _ _ valid615 (by decide +kernel)

theorem valid1668 : plan1668.Valid := valid_step _ _ _ valid616 (by decide +kernel)

theorem valid1669 : plan1669.Valid := valid_step _ _ _ valid617 (by decide +kernel)

theorem valid1670 : plan1670.Valid := valid_step _ _ _ valid618 (by decide +kernel)

theorem valid1671 : plan1671.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1672 : plan1672.Valid := valid_step _ _ _ valid620 (by decide +kernel)

theorem valid1673 : plan1673.Valid := valid_step _ _ _ valid621 (by decide +kernel)

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



































































































































theorem valid3618 : plan3618.Valid := valid_step _ _ _ valid1665 (by decide +kernel)

theorem valid3619 : plan3619.Valid := valid_step _ _ _ valid1666 (by decide +kernel)

theorem valid3620 : plan3620.Valid := valid_step _ _ _ valid1667 (by decide +kernel)



theorem valid3622 : plan3622.Valid := valid_step _ _ _ valid1668 (by decide +kernel)

theorem valid3623 : plan3623.Valid := valid_step _ _ _ valid1669 (by decide +kernel)

theorem valid3624 : plan3624.Valid := valid_step _ _ _ valid1670 (by decide +kernel)

theorem valid3625 : plan3625.Valid := valid_step _ _ _ valid1671 (by decide +kernel)

theorem valid3626 : plan3626.Valid := valid_step _ _ _ valid1672 (by decide +kernel)

theorem valid3627 : plan3627.Valid := valid_step _ _ _ valid1673 (by decide +kernel)

theorem valid3628 : plan3628.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3629 : plan3629.Valid := valid_step _ _ _ valid1675 (by decide +kernel)

theorem valid3630 : plan3630.Valid := valid_step _ _ _ valid1676 (by decide +kernel)

theorem valid3631 : plan3631.Valid := valid_step _ _ _ valid1677 (by decide +kernel)

theorem valid3632 : plan3632.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3633 : plan3633.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3634 : plan3634.Valid := valid_step _ _ _ valid1675 (by decide +kernel)




























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









































































































theorem valid6197 : plan6197.Valid := valid_step _ _ _ valid3618 (by decide +kernel)

theorem valid6198 : plan6198.Valid := valid_step _ _ _ valid3619 (by decide +kernel)

theorem valid6199 : plan6199.Valid := valid_step _ _ _ valid3620 (by decide +kernel)





















theorem valid6210 : plan6210.Valid := valid_step _ _ _ valid3622 (by decide +kernel)

theorem valid6211 : plan6211.Valid := valid_step _ _ _ valid3623 (by decide +kernel)

theorem valid6212 : plan6212.Valid := valid_step _ _ _ valid3624 (by decide +kernel)

theorem valid6213 : plan6213.Valid := valid_step _ _ _ valid3625 (by decide +kernel)

theorem valid6214 : plan6214.Valid := valid_step _ _ _ valid3626 (by decide +kernel)

theorem valid6215 : plan6215.Valid := valid_step _ _ _ valid3627 (by decide +kernel)

theorem valid6216 : plan6216.Valid := valid_step _ _ _ valid3628 (by decide +kernel)

theorem valid6217 : plan6217.Valid := valid_step _ _ _ valid3629 (by decide +kernel)

theorem valid6218 : plan6218.Valid := valid_step _ _ _ valid3630 (by decide +kernel)

theorem valid6219 : plan6219.Valid := valid_step _ _ _ valid3631 (by decide +kernel)

theorem valid6220 : plan6220.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6221 : plan6221.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6222 : plan6222.Valid := valid_step _ _ _ valid3634 (by decide +kernel)




































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







































































theorem valid8196 : plan8196.Valid := valid_step _ _ _ valid6197 (by decide +kernel)

theorem valid8197 : plan8197.Valid := valid_step _ _ _ valid6198 (by decide +kernel)

theorem valid8198 : plan8198.Valid := valid_step _ _ _ valid6199 (by decide +kernel)




















































































































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

































theorem valid8273 : plan8273.Valid := valid_step _ _ _ valid6210 (by decide +kernel)

theorem valid8274 : plan8274.Valid := valid_step _ _ _ valid6211 (by decide +kernel)

theorem valid8275 : plan8275.Valid := valid_step _ _ _ valid6212 (by decide +kernel)

theorem valid8276 : plan8276.Valid := valid_step _ _ _ valid6213 (by decide +kernel)

theorem valid8277 : plan8277.Valid := valid_step _ _ _ valid6214 (by decide +kernel)

theorem valid8278 : plan8278.Valid := valid_step _ _ _ valid6215 (by decide +kernel)

theorem valid8279 : plan8279.Valid := valid_step _ _ _ valid6216 (by decide +kernel)

theorem valid8280 : plan8280.Valid := valid_step _ _ _ valid6217 (by decide +kernel)

theorem valid8281 : plan8281.Valid := valid_step _ _ _ valid6218 (by decide +kernel)

theorem valid8282 : plan8282.Valid := valid_step _ _ _ valid6219 (by decide +kernel)

theorem valid8283 : plan8283.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8284 : plan8284.Valid := valid_step _ _ _ valid6221 (by decide +kernel)

theorem valid8285 : plan8285.Valid := valid_step _ _ _ valid6222 (by decide +kernel)






































































































































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























theorem valid8652 : plan8652.Valid := valid_step _ _ _ valid8196 (by decide +kernel)

theorem valid8653 : plan8653.Valid := valid_step _ _ _ valid8197 (by decide +kernel)

theorem valid8654 : plan8654.Valid := valid_step _ _ _ valid8198 (by decide +kernel)




































































































































































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























































































































































theorem valid8812 : plan8812.Valid := valid_step _ _ _ valid8273 (by decide +kernel)

theorem valid8813 : plan8813.Valid := valid_step _ _ _ valid8274 (by decide +kernel)

theorem valid8814 : plan8814.Valid := valid_step _ _ _ valid8275 (by decide +kernel)

theorem valid8815 : plan8815.Valid := valid_step _ _ _ valid8276 (by decide +kernel)

theorem valid8816 : plan8816.Valid := valid_step _ _ _ valid8277 (by decide +kernel)

theorem valid8817 : plan8817.Valid := valid_step _ _ _ valid8278 (by decide +kernel)

theorem valid8818 : plan8818.Valid := valid_step _ _ _ valid8279 (by decide +kernel)

theorem valid8819 : plan8819.Valid := valid_step _ _ _ valid8280 (by decide +kernel)

theorem valid8820 : plan8820.Valid := valid_step _ _ _ valid8281 (by decide +kernel)

theorem valid8821 : plan8821.Valid := valid_step _ _ _ valid8282 (by decide +kernel)

theorem valid8822 : plan8822.Valid := valid_step _ _ _ valid8283 (by decide +kernel)

theorem valid8823 : plan8823.Valid := valid_step _ _ _ valid8284 (by decide +kernel)

theorem valid8824 : plan8824.Valid := valid_step _ _ _ valid8285 (by decide +kernel)
















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
theorem t7_311choices : plan8652.choices=[3,3,10,10,10,7,7].map (options 7 5) := by rfl


theorem t7_311part0 : t7_311jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_311part1 : t7_311jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_311part2 : t7_311jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_311frontier : t7_311root.frontier 3=t7_311jobs := by rfl
theorem t7_311all : t7_311jobs.all (Job.check tree)=true := by
  simp only [t7_311jobs,List.all_append,List.all_nil,t7_311part0,t7_311part1,t7_311part2,Bool.and_self]
theorem t7_311checked : Checked tree [3,3,10,10,10,7,7] := by
  refine ⟨plan8652,valid8652,t7_311choices,?_⟩
  exact check_of_frontier tree 3 t7_311root t7_311jobs t7_311frontier t7_311all
theorem t7_312choices : plan8653.choices=[3,3,10,10,10,10,7].map (options 7 5) := by rfl


theorem t7_312part0 : t7_312jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_312frontier : t7_312root.frontier 0=t7_312jobs := by rfl
theorem t7_312all : t7_312jobs.all (Job.check tree)=true := by
  simp only [t7_312jobs,List.all_append,List.all_nil,t7_312part0,Bool.and_self]
theorem t7_312checked : Checked tree [3,3,10,10,10,10,7] := by
  refine ⟨plan8653,valid8653,t7_312choices,?_⟩
  exact check_of_frontier tree 0 t7_312root t7_312jobs t7_312frontier t7_312all
theorem t7_313choices : plan8654.choices=[3,3,10,10,10,10,10].map (options 7 5) := by rfl


theorem t7_313part0 : t7_313jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_313frontier : t7_313root.frontier 0=t7_313jobs := by rfl
theorem t7_313all : t7_313jobs.all (Job.check tree)=true := by
  simp only [t7_313jobs,List.all_append,List.all_nil,t7_313part0,Bool.and_self]
theorem t7_313checked : Checked tree [3,3,10,10,10,10,10] := by
  refine ⟨plan8654,valid8654,t7_313choices,?_⟩
  exact check_of_frontier tree 0 t7_313root t7_313jobs t7_313frontier t7_313all
theorem t7_314choices : plan8812.choices=[3,6,6,6,6,6,6].map (options 7 6) := by rfl


theorem t7_314part0 : t7_314jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_314frontier : t7_314root.frontier 0=t7_314jobs := by rfl
theorem t7_314all : t7_314jobs.all (Job.check tree)=true := by
  simp only [t7_314jobs,List.all_append,List.all_nil,t7_314part0,Bool.and_self]
theorem t7_314checked : Checked tree [3,6,6,6,6,6,6] := by
  refine ⟨plan8812,valid8812,t7_314choices,?_⟩
  exact check_of_frontier tree 0 t7_314root t7_314jobs t7_314frontier t7_314all
theorem t7_315choices : plan8813.choices=[3,6,6,6,6,6,7].map (options 7 6) := by rfl


theorem t7_315part0 : t7_315jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_315frontier : t7_315root.frontier 0=t7_315jobs := by rfl
theorem t7_315all : t7_315jobs.all (Job.check tree)=true := by
  simp only [t7_315jobs,List.all_append,List.all_nil,t7_315part0,Bool.and_self]
theorem t7_315checked : Checked tree [3,6,6,6,6,6,7] := by
  refine ⟨plan8813,valid8813,t7_315choices,?_⟩
  exact check_of_frontier tree 0 t7_315root t7_315jobs t7_315frontier t7_315all
theorem t7_316choices : plan8814.choices=[3,6,6,6,6,6,10].map (options 7 6) := by rfl


theorem t7_316part0 : t7_316jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_316frontier : t7_316root.frontier 0=t7_316jobs := by rfl
theorem t7_316all : t7_316jobs.all (Job.check tree)=true := by
  simp only [t7_316jobs,List.all_append,List.all_nil,t7_316part0,Bool.and_self]
theorem t7_316checked : Checked tree [3,6,6,6,6,6,10] := by
  refine ⟨plan8814,valid8814,t7_316choices,?_⟩
  exact check_of_frontier tree 0 t7_316root t7_316jobs t7_316frontier t7_316all
theorem t7_317choices : plan8815.choices=[3,6,6,6,6,7,7].map (options 7 6) := by rfl


theorem t7_317part0 : t7_317jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_317frontier : t7_317root.frontier 0=t7_317jobs := by rfl
theorem t7_317all : t7_317jobs.all (Job.check tree)=true := by
  simp only [t7_317jobs,List.all_append,List.all_nil,t7_317part0,Bool.and_self]
theorem t7_317checked : Checked tree [3,6,6,6,6,7,7] := by
  refine ⟨plan8815,valid8815,t7_317choices,?_⟩
  exact check_of_frontier tree 0 t7_317root t7_317jobs t7_317frontier t7_317all
theorem t7_318choices : plan8816.choices=[3,6,6,6,6,10,7].map (options 7 6) := by rfl


theorem t7_318part0 : t7_318jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_318frontier : t7_318root.frontier 0=t7_318jobs := by rfl
theorem t7_318all : t7_318jobs.all (Job.check tree)=true := by
  simp only [t7_318jobs,List.all_append,List.all_nil,t7_318part0,Bool.and_self]
theorem t7_318checked : Checked tree [3,6,6,6,6,10,7] := by
  refine ⟨plan8816,valid8816,t7_318choices,?_⟩
  exact check_of_frontier tree 0 t7_318root t7_318jobs t7_318frontier t7_318all
theorem t7_319choices : plan8817.choices=[3,6,6,6,6,10,10].map (options 7 6) := by rfl


theorem t7_319part0 : t7_319jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_319frontier : t7_319root.frontier 0=t7_319jobs := by rfl
theorem t7_319all : t7_319jobs.all (Job.check tree)=true := by
  simp only [t7_319jobs,List.all_append,List.all_nil,t7_319part0,Bool.and_self]
theorem t7_319checked : Checked tree [3,6,6,6,6,10,10] := by
  refine ⟨plan8817,valid8817,t7_319choices,?_⟩
  exact check_of_frontier tree 0 t7_319root t7_319jobs t7_319frontier t7_319all
theorem t7_320choices : plan8818.choices=[3,6,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_320part0 : t7_320jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_320part1 : t7_320jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_320frontier : t7_320root.frontier 2=t7_320jobs := by rfl
theorem t7_320all : t7_320jobs.all (Job.check tree)=true := by
  simp only [t7_320jobs,List.all_append,List.all_nil,t7_320part0,t7_320part1,Bool.and_self]
theorem t7_320checked : Checked tree [3,6,6,6,7,7,7] := by
  refine ⟨plan8818,valid8818,t7_320choices,?_⟩
  exact check_of_frontier tree 2 t7_320root t7_320jobs t7_320frontier t7_320all
theorem t7_321choices : plan8819.choices=[3,6,6,6,10,7,7].map (options 7 6) := by rfl


theorem t7_321part0 : t7_321jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_321part1 : t7_321jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_321frontier : t7_321root.frontier 1=t7_321jobs := by rfl
theorem t7_321all : t7_321jobs.all (Job.check tree)=true := by
  simp only [t7_321jobs,List.all_append,List.all_nil,t7_321part0,t7_321part1,Bool.and_self]
theorem t7_321checked : Checked tree [3,6,6,6,10,7,7] := by
  refine ⟨plan8819,valid8819,t7_321choices,?_⟩
  exact check_of_frontier tree 1 t7_321root t7_321jobs t7_321frontier t7_321all
theorem t7_322choices : plan8820.choices=[3,6,6,6,10,10,7].map (options 7 6) := by rfl


theorem t7_322part0 : t7_322jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_322frontier : t7_322root.frontier 0=t7_322jobs := by rfl
theorem t7_322all : t7_322jobs.all (Job.check tree)=true := by
  simp only [t7_322jobs,List.all_append,List.all_nil,t7_322part0,Bool.and_self]
theorem t7_322checked : Checked tree [3,6,6,6,10,10,7] := by
  refine ⟨plan8820,valid8820,t7_322choices,?_⟩
  exact check_of_frontier tree 0 t7_322root t7_322jobs t7_322frontier t7_322all
theorem t7_323choices : plan8821.choices=[3,6,6,6,10,10,10].map (options 7 6) := by rfl


theorem t7_323part0 : t7_323jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_323frontier : t7_323root.frontier 0=t7_323jobs := by rfl
theorem t7_323all : t7_323jobs.all (Job.check tree)=true := by
  simp only [t7_323jobs,List.all_append,List.all_nil,t7_323part0,Bool.and_self]
theorem t7_323checked : Checked tree [3,6,6,6,10,10,10] := by
  refine ⟨plan8821,valid8821,t7_323choices,?_⟩
  exact check_of_frontier tree 0 t7_323root t7_323jobs t7_323frontier t7_323all
theorem t7_324choices : plan8822.choices=[3,6,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_324part0 : t7_324jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_324part1 : t7_324jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_324part2 : t7_324jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_324part3 : t7_324jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_324frontier : t7_324root.frontier 2=t7_324jobs := by rfl
theorem t7_324all : t7_324jobs.all (Job.check tree)=true := by
  simp only [t7_324jobs,List.all_append,List.all_nil,t7_324part0,t7_324part1,t7_324part2,t7_324part3,Bool.and_self]
theorem t7_324checked : Checked tree [3,6,6,7,7,7,7] := by
  refine ⟨plan8822,valid8822,t7_324choices,?_⟩
  exact check_of_frontier tree 2 t7_324root t7_324jobs t7_324frontier t7_324all
theorem t7_325choices : plan8823.choices=[3,6,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_325part0 : t7_325jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_325part1 : t7_325jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_325part2 : t7_325jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_325part3 : t7_325jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_325frontier : t7_325root.frontier 2=t7_325jobs := by rfl
theorem t7_325all : t7_325jobs.all (Job.check tree)=true := by
  simp only [t7_325jobs,List.all_append,List.all_nil,t7_325part0,t7_325part1,t7_325part2,t7_325part3,Bool.and_self]
theorem t7_325checked : Checked tree [3,6,6,10,7,7,7] := by
  refine ⟨plan8823,valid8823,t7_325choices,?_⟩
  exact check_of_frontier tree 2 t7_325root t7_325jobs t7_325frontier t7_325all
theorem t7_326choices : plan8824.choices=[3,6,6,10,10,7,7].map (options 7 6) := by rfl


theorem t7_326part0 : t7_326jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_326part1 : t7_326jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_326frontier : t7_326root.frontier 2=t7_326jobs := by rfl
theorem t7_326all : t7_326jobs.all (Job.check tree)=true := by
  simp only [t7_326jobs,List.all_append,List.all_nil,t7_326part0,t7_326part1,Bool.and_self]
theorem t7_326checked : Checked tree [3,6,6,10,10,7,7] := by
  refine ⟨plan8824,valid8824,t7_326choices,?_⟩
  exact check_of_frontier tree 2 t7_326root t7_326jobs t7_326frontier t7_326all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks181 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_317checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_318checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_319checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_320checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_321checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_322checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_323checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_324checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_325checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_326checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_311checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_312checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_313checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_314checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_315checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_316checked⟩
