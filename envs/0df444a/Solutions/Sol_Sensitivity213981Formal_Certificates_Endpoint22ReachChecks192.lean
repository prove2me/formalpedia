-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks192
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:18:44.333564+00:00
-- url     : https://prove2.me/submissions/9d455c51-eebf-4622-af57-cd3c10d6f4d1

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks192
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks192
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans090
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans092
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans093
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









































































theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)

theorem valid614 : plan614.Valid := valid_step _ _ _ valid153 (by decide +kernel)





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































































theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1666 : plan1666.Valid := valid_step _ _ _ valid614 (by decide +kernel)





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

































































































































theorem valid3617 : plan3617.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3618 : plan3618.Valid := valid_step _ _ _ valid1665 (by decide +kernel)

theorem valid3619 : plan3619.Valid := valid_step _ _ _ valid1666 (by decide +kernel)







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















































theorem valid6168 : plan6168.Valid := valid_step _ _ _ valid3617 (by decide +kernel)

theorem valid6169 : plan6169.Valid := valid_step _ _ _ valid3618 (by decide +kernel)

theorem valid6170 : plan6170.Valid := valid_step _ _ _ valid3619 (by decide +kernel)

















































































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





























theorem valid8175 : plan8175.Valid := valid_step _ _ _ valid6168 (by decide +kernel)

theorem valid8176 : plan8176.Valid := valid_step _ _ _ valid6169 (by decide +kernel)

theorem valid8177 : plan8177.Valid := valid_step _ _ _ valid6170 (by decide +kernel)









































































































theorem valid8230 : plan8230.Valid := valid_step _ _ _ valid6211 (by decide +kernel)

theorem valid8231 : plan8231.Valid := valid_step _ _ _ valid6213 (by decide +kernel)

theorem valid8232 : plan8232.Valid := valid_step _ _ _ valid6214 (by decide +kernel)

theorem valid8233 : plan8233.Valid := valid_step _ _ _ valid6216 (by decide +kernel)

theorem valid8234 : plan8234.Valid := valid_step _ _ _ valid6217 (by decide +kernel)

theorem valid8235 : plan8235.Valid := valid_step _ _ _ valid6218 (by decide +kernel)

theorem valid8236 : plan8236.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8237 : plan8237.Valid := valid_step _ _ _ valid6221 (by decide +kernel)

theorem valid8238 : plan8238.Valid := valid_step _ _ _ valid6222 (by decide +kernel)

theorem valid8239 : plan8239.Valid := valid_step _ _ _ valid6223 (by decide +kernel)


































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



























































































































theorem valid8702 : plan8702.Valid := valid_step _ _ _ valid8175 (by decide +kernel)

theorem valid8703 : plan8703.Valid := valid_step _ _ _ valid8176 (by decide +kernel)

theorem valid8704 : plan8704.Valid := valid_step _ _ _ valid8177 (by decide +kernel)
































































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

















































































































































































theorem valid8921 : plan8921.Valid := valid_step _ _ _ valid8230 (by decide +kernel)

theorem valid8922 : plan8922.Valid := valid_step _ _ _ valid8231 (by decide +kernel)

theorem valid8923 : plan8923.Valid := valid_step _ _ _ valid8232 (by decide +kernel)

theorem valid8924 : plan8924.Valid := valid_step _ _ _ valid8233 (by decide +kernel)

theorem valid8925 : plan8925.Valid := valid_step _ _ _ valid8234 (by decide +kernel)

theorem valid8926 : plan8926.Valid := valid_step _ _ _ valid8235 (by decide +kernel)

theorem valid8927 : plan8927.Valid := valid_step _ _ _ valid8236 (by decide +kernel)

theorem valid8928 : plan8928.Valid := valid_step _ _ _ valid8237 (by decide +kernel)
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

theorem valid8929 : plan8929.Valid := valid_step _ _ _ valid8238 (by decide +kernel)

theorem valid8930 : plan8930.Valid := valid_step _ _ _ valid8239 (by decide +kernel)




























































































































































































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
theorem t7_650choices : plan8702.choices=[9,3,3,10,7,7,7].map (options 7 5) := by rfl


theorem t7_650part0 : t7_650jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_650part1 : t7_650jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_650part2 : t7_650jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_650part3 : t7_650jobs3.all (Job.check tree)=true := by decide +kernel

theorem t7_650part4 : t7_650jobs4.all (Job.check tree)=true := by decide +kernel

theorem t7_650part5 : t7_650jobs5.all (Job.check tree)=true := by decide +kernel

theorem t7_650frontier : t7_650root.frontier 2=t7_650jobs := by rfl
theorem t7_650all : t7_650jobs.all (Job.check tree)=true := by
  simp only [t7_650jobs,List.all_append,List.all_nil,t7_650part0,t7_650part1,t7_650part2,t7_650part3,t7_650part4,t7_650part5,Bool.and_self]
theorem t7_650checked : Checked tree [9,3,3,10,7,7,7] := by
  refine ⟨plan8702,valid8702,t7_650choices,?_⟩
  exact check_of_frontier tree 2 t7_650root t7_650jobs t7_650frontier t7_650all
theorem t7_651choices : plan8703.choices=[9,3,3,10,10,7,7].map (options 7 5) := by rfl


theorem t7_651part0 : t7_651jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_651part1 : t7_651jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_651part2 : t7_651jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_651frontier : t7_651root.frontier 1=t7_651jobs := by rfl
theorem t7_651all : t7_651jobs.all (Job.check tree)=true := by
  simp only [t7_651jobs,List.all_append,List.all_nil,t7_651part0,t7_651part1,t7_651part2,Bool.and_self]
theorem t7_651checked : Checked tree [9,3,3,10,10,7,7] := by
  refine ⟨plan8703,valid8703,t7_651choices,?_⟩
  exact check_of_frontier tree 1 t7_651root t7_651jobs t7_651frontier t7_651all
theorem t7_652choices : plan8704.choices=[9,3,3,10,10,10,7].map (options 7 5) := by rfl


theorem t7_652part0 : t7_652jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_652frontier : t7_652root.frontier 0=t7_652jobs := by rfl
theorem t7_652all : t7_652jobs.all (Job.check tree)=true := by
  simp only [t7_652jobs,List.all_append,List.all_nil,t7_652part0,Bool.and_self]
theorem t7_652checked : Checked tree [9,3,3,10,10,10,7] := by
  refine ⟨plan8704,valid8704,t7_652choices,?_⟩
  exact check_of_frontier tree 0 t7_652root t7_652jobs t7_652frontier t7_652all
theorem t7_653choices : plan8921.choices=[9,3,6,6,6,6,7].map (options 7 6) := by rfl


theorem t7_653part0 : t7_653jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_653frontier : t7_653root.frontier 0=t7_653jobs := by rfl
theorem t7_653all : t7_653jobs.all (Job.check tree)=true := by
  simp only [t7_653jobs,List.all_append,List.all_nil,t7_653part0,Bool.and_self]
theorem t7_653checked : Checked tree [9,3,6,6,6,6,7] := by
  refine ⟨plan8921,valid8921,t7_653choices,?_⟩
  exact check_of_frontier tree 0 t7_653root t7_653jobs t7_653frontier t7_653all
theorem t7_654choices : plan8922.choices=[9,3,6,6,6,7,7].map (options 7 6) := by rfl


theorem t7_654part0 : t7_654jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_654frontier : t7_654root.frontier 0=t7_654jobs := by rfl
theorem t7_654all : t7_654jobs.all (Job.check tree)=true := by
  simp only [t7_654jobs,List.all_append,List.all_nil,t7_654part0,Bool.and_self]
theorem t7_654checked : Checked tree [9,3,6,6,6,7,7] := by
  refine ⟨plan8922,valid8922,t7_654choices,?_⟩
  exact check_of_frontier tree 0 t7_654root t7_654jobs t7_654frontier t7_654all
theorem t7_655choices : plan8923.choices=[9,3,6,6,6,10,7].map (options 7 6) := by rfl


theorem t7_655part0 : t7_655jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_655frontier : t7_655root.frontier 0=t7_655jobs := by rfl
theorem t7_655all : t7_655jobs.all (Job.check tree)=true := by
  simp only [t7_655jobs,List.all_append,List.all_nil,t7_655part0,Bool.and_self]
theorem t7_655checked : Checked tree [9,3,6,6,6,10,7] := by
  refine ⟨plan8923,valid8923,t7_655choices,?_⟩
  exact check_of_frontier tree 0 t7_655root t7_655jobs t7_655frontier t7_655all
theorem t7_656choices : plan8924.choices=[9,3,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_656part0 : t7_656jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_656part1 : t7_656jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_656frontier : t7_656root.frontier 1=t7_656jobs := by rfl
theorem t7_656all : t7_656jobs.all (Job.check tree)=true := by
  simp only [t7_656jobs,List.all_append,List.all_nil,t7_656part0,t7_656part1,Bool.and_self]
theorem t7_656checked : Checked tree [9,3,6,6,7,7,7] := by
  refine ⟨plan8924,valid8924,t7_656choices,?_⟩
  exact check_of_frontier tree 1 t7_656root t7_656jobs t7_656frontier t7_656all
theorem t7_657choices : plan8925.choices=[9,3,6,6,10,7,7].map (options 7 6) := by rfl


theorem t7_657part0 : t7_657jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_657frontier : t7_657root.frontier 0=t7_657jobs := by rfl
theorem t7_657all : t7_657jobs.all (Job.check tree)=true := by
  simp only [t7_657jobs,List.all_append,List.all_nil,t7_657part0,Bool.and_self]
theorem t7_657checked : Checked tree [9,3,6,6,10,7,7] := by
  refine ⟨plan8925,valid8925,t7_657choices,?_⟩
  exact check_of_frontier tree 0 t7_657root t7_657jobs t7_657frontier t7_657all
theorem t7_658choices : plan8926.choices=[9,3,6,6,10,10,7].map (options 7 6) := by rfl


theorem t7_658part0 : t7_658jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_658frontier : t7_658root.frontier 0=t7_658jobs := by rfl
theorem t7_658all : t7_658jobs.all (Job.check tree)=true := by
  simp only [t7_658jobs,List.all_append,List.all_nil,t7_658part0,Bool.and_self]
theorem t7_658checked : Checked tree [9,3,6,6,10,10,7] := by
  refine ⟨plan8926,valid8926,t7_658choices,?_⟩
  exact check_of_frontier tree 0 t7_658root t7_658jobs t7_658frontier t7_658all
theorem t7_659choices : plan8927.choices=[9,3,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_659part0 : t7_659jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_659part1 : t7_659jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_659part2 : t7_659jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_659frontier : t7_659root.frontier 1=t7_659jobs := by rfl
theorem t7_659all : t7_659jobs.all (Job.check tree)=true := by
  simp only [t7_659jobs,List.all_append,List.all_nil,t7_659part0,t7_659part1,t7_659part2,Bool.and_self]
theorem t7_659checked : Checked tree [9,3,6,7,7,7,7] := by
  refine ⟨plan8927,valid8927,t7_659choices,?_⟩
  exact check_of_frontier tree 1 t7_659root t7_659jobs t7_659frontier t7_659all
theorem t7_660choices : plan8928.choices=[9,3,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_660part0 : t7_660jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_660part1 : t7_660jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_660part2 : t7_660jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_660frontier : t7_660root.frontier 1=t7_660jobs := by rfl
theorem t7_660all : t7_660jobs.all (Job.check tree)=true := by
  simp only [t7_660jobs,List.all_append,List.all_nil,t7_660part0,t7_660part1,t7_660part2,Bool.and_self]
theorem t7_660checked : Checked tree [9,3,6,10,7,7,7] := by
  refine ⟨plan8928,valid8928,t7_660choices,?_⟩
  exact check_of_frontier tree 1 t7_660root t7_660jobs t7_660frontier t7_660all
theorem t7_661choices : plan8929.choices=[9,3,6,10,10,7,7].map (options 7 6) := by rfl


theorem t7_661part0 : t7_661jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_661frontier : t7_661root.frontier 0=t7_661jobs := by rfl
theorem t7_661all : t7_661jobs.all (Job.check tree)=true := by
  simp only [t7_661jobs,List.all_append,List.all_nil,t7_661part0,Bool.and_self]
theorem t7_661checked : Checked tree [9,3,6,10,10,7,7] := by
  refine ⟨plan8929,valid8929,t7_661choices,?_⟩
  exact check_of_frontier tree 0 t7_661root t7_661jobs t7_661frontier t7_661all
theorem t7_662choices : plan8930.choices=[9,3,6,10,10,10,7].map (options 7 6) := by rfl


theorem t7_662part0 : t7_662jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_662frontier : t7_662root.frontier 0=t7_662jobs := by rfl
theorem t7_662all : t7_662jobs.all (Job.check tree)=true := by
  simp only [t7_662jobs,List.all_append,List.all_nil,t7_662part0,Bool.and_self]
theorem t7_662checked : Checked tree [9,3,6,10,10,10,7] := by
  refine ⟨plan8930,valid8930,t7_662choices,?_⟩
  exact check_of_frontier tree 0 t7_662root t7_662jobs t7_662frontier t7_662all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks192 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_656checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_657checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_658checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_659checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_660checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_661checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_662checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_650checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_651checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_652checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_653checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_654checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_655checked⟩
