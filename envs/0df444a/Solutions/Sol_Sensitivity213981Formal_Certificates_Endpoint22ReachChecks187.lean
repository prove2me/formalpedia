-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks187
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:16:18.143502+00:00
-- url     : https://prove2.me/submissions/22e21a7a-e51b-4412-92a8-63ebe99eea1d

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks187
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks187
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
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





























































theorem valid607 : plan607.Valid := valid_step _ _ _ valid150 (by decide +kernel)











theorem valid613 : plan613.Valid := valid_step _ _ _ valid153 (by decide +kernel)











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





























theorem valid1647 : plan1647.Valid := valid_step _ _ _ valid607 (by decide +kernel)



























theorem valid1661 : plan1661.Valid := valid_step _ _ _ valid613 (by decide +kernel)





theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)











theorem valid1671 : plan1671.Valid := valid_step _ _ _ valid619 (by decide +kernel)





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

























































theorem valid3581 : plan3581.Valid := valid_step _ _ _ valid1647 (by decide +kernel)











































theorem valid3603 : plan3603.Valid := valid_step _ _ _ valid1661 (by decide +kernel)

theorem valid3604 : plan3604.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3605 : plan3605.Valid := valid_step _ _ _ valid1665 (by decide +kernel)







































theorem valid3625 : plan3625.Valid := valid_step _ _ _ valid1671 (by decide +kernel)





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









































































































































































theorem valid6133 : plan6133.Valid := valid_step _ _ _ valid3581 (by decide +kernel)






















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



























theorem valid6158 : plan6158.Valid := valid_step _ _ _ valid3603 (by decide +kernel)

theorem valid6159 : plan6159.Valid := valid_step _ _ _ valid3604 (by decide +kernel)

theorem valid6160 : plan6160.Valid := valid_step _ _ _ valid3605 (by decide +kernel)















































































theorem valid6200 : plan6200.Valid := valid_step _ _ _ valid3625 (by decide +kernel)

theorem valid6201 : plan6201.Valid := valid_step _ _ _ valid3628 (by decide +kernel)

theorem valid6202 : plan6202.Valid := valid_step _ _ _ valid3629 (by decide +kernel)





























theorem valid6217 : plan6217.Valid := valid_step _ _ _ valid3629 (by decide +kernel)

theorem valid6218 : plan6218.Valid := valid_step _ _ _ valid3630 (by decide +kernel)



theorem valid6220 : plan6220.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6221 : plan6221.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6222 : plan6222.Valid := valid_step _ _ _ valid3634 (by decide +kernel)

theorem valid6223 : plan6223.Valid := valid_step _ _ _ valid3635 (by decide +kernel)



theorem valid6225 : plan6225.Valid := valid_step _ _ _ valid3632 (by decide +kernel)









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

















































































































































theorem valid8137 : plan8137.Valid := valid_step _ _ _ valid6133 (by decide +kernel)














































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











































































































































































theorem valid8534 : plan8534.Valid := valid_step _ _ _ valid8137 (by decide +kernel)




















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















































































theorem valid8200 : plan8200.Valid := valid_step _ _ _ valid6158 (by decide +kernel)

theorem valid8201 : plan8201.Valid := valid_step _ _ _ valid6159 (by decide +kernel)

theorem valid8202 : plan8202.Valid := valid_step _ _ _ valid6160 (by decide +kernel)































































theorem valid8234 : plan8234.Valid := valid_step _ _ _ valid6217 (by decide +kernel)

theorem valid8235 : plan8235.Valid := valid_step _ _ _ valid6218 (by decide +kernel)

theorem valid8236 : plan8236.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8237 : plan8237.Valid := valid_step _ _ _ valid6221 (by decide +kernel)

theorem valid8238 : plan8238.Valid := valid_step _ _ _ valid6222 (by decide +kernel)

theorem valid8239 : plan8239.Valid := valid_step _ _ _ valid6223 (by decide +kernel)

theorem valid8240 : plan8240.Valid := valid_step _ _ _ valid6225 (by decide +kernel)

theorem valid8241 : plan8241.Valid := valid_step _ _ _ valid6230 (by decide +kernel)

theorem valid8242 : plan8242.Valid := valid_step _ _ _ valid6231 (by decide +kernel)

theorem valid8243 : plan8243.Valid := valid_step _ _ _ valid6232 (by decide +kernel)

theorem valid8244 : plan8244.Valid := valid_step _ _ _ valid6233 (by decide +kernel)









theorem valid8249 : plan8249.Valid := valid_step _ _ _ valid6200 (by decide +kernel)

theorem valid8250 : plan8250.Valid := valid_step _ _ _ valid6201 (by decide +kernel)

theorem valid8251 : plan8251.Valid := valid_step _ _ _ valid6202 (by decide +kernel)










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









































































theorem valid8677 : plan8677.Valid := valid_step _ _ _ valid8200 (by decide +kernel)

theorem valid8678 : plan8678.Valid := valid_step _ _ _ valid8201 (by decide +kernel)

theorem valid8679 : plan8679.Valid := valid_step _ _ _ valid8202 (by decide +kernel)


















































































































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











































































theorem valid8870 : plan8870.Valid := valid_step _ _ _ valid8234 (by decide +kernel)

theorem valid8871 : plan8871.Valid := valid_step _ _ _ valid8235 (by decide +kernel)

theorem valid8872 : plan8872.Valid := valid_step _ _ _ valid8236 (by decide +kernel)

theorem valid8873 : plan8873.Valid := valid_step _ _ _ valid8237 (by decide +kernel)

theorem valid8874 : plan8874.Valid := valid_step _ _ _ valid8238 (by decide +kernel)

theorem valid8875 : plan8875.Valid := valid_step _ _ _ valid8239 (by decide +kernel)

theorem valid8876 : plan8876.Valid := valid_step _ _ _ valid8240 (by decide +kernel)

theorem valid8877 : plan8877.Valid := valid_step _ _ _ valid8241 (by decide +kernel)

theorem valid8878 : plan8878.Valid := valid_step _ _ _ valid8242 (by decide +kernel)

theorem valid8879 : plan8879.Valid := valid_step _ _ _ valid8243 (by decide +kernel)

theorem valid8880 : plan8880.Valid := valid_step _ _ _ valid8244 (by decide +kernel)

theorem valid8881 : plan8881.Valid := valid_step _ _ _ valid8249 (by decide +kernel)

theorem valid8882 : plan8882.Valid := valid_step _ _ _ valid8250 (by decide +kernel)

theorem valid8883 : plan8883.Valid := valid_step _ _ _ valid8251 (by decide +kernel)


























































































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
theorem t7_445choices : plan8870.choices=[5,3,6,6,10,7,7].map (options 7 6) := by rfl


theorem t7_445part0 : t7_445jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_445frontier : t7_445root.frontier 0=t7_445jobs := by rfl
theorem t7_445all : t7_445jobs.all (Job.check tree)=true := by
  simp only [t7_445jobs,List.all_append,List.all_nil,t7_445part0,Bool.and_self]
theorem t7_445checked : Checked tree [5,3,6,6,10,7,7] := by
  refine ⟨plan8870,valid8870,t7_445choices,?_⟩
  exact check_of_frontier tree 0 t7_445root t7_445jobs t7_445frontier t7_445all
theorem t7_446choices : plan8871.choices=[5,3,6,6,10,10,7].map (options 7 6) := by rfl


theorem t7_446part0 : t7_446jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_446frontier : t7_446root.frontier 0=t7_446jobs := by rfl
theorem t7_446all : t7_446jobs.all (Job.check tree)=true := by
  simp only [t7_446jobs,List.all_append,List.all_nil,t7_446part0,Bool.and_self]
theorem t7_446checked : Checked tree [5,3,6,6,10,10,7] := by
  refine ⟨plan8871,valid8871,t7_446choices,?_⟩
  exact check_of_frontier tree 0 t7_446root t7_446jobs t7_446frontier t7_446all
theorem t7_447choices : plan8872.choices=[5,3,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_447part0 : t7_447jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_447part1 : t7_447jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_447part2 : t7_447jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_447frontier : t7_447root.frontier 1=t7_447jobs := by rfl
theorem t7_447all : t7_447jobs.all (Job.check tree)=true := by
  simp only [t7_447jobs,List.all_append,List.all_nil,t7_447part0,t7_447part1,t7_447part2,Bool.and_self]
theorem t7_447checked : Checked tree [5,3,6,7,7,7,7] := by
  refine ⟨plan8872,valid8872,t7_447choices,?_⟩
  exact check_of_frontier tree 1 t7_447root t7_447jobs t7_447frontier t7_447all
theorem t7_448choices : plan8873.choices=[5,3,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_448part0 : t7_448jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_448part1 : t7_448jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_448part2 : t7_448jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_448frontier : t7_448root.frontier 1=t7_448jobs := by rfl
theorem t7_448all : t7_448jobs.all (Job.check tree)=true := by
  simp only [t7_448jobs,List.all_append,List.all_nil,t7_448part0,t7_448part1,t7_448part2,Bool.and_self]
theorem t7_448checked : Checked tree [5,3,6,10,7,7,7] := by
  refine ⟨plan8873,valid8873,t7_448choices,?_⟩
  exact check_of_frontier tree 1 t7_448root t7_448jobs t7_448frontier t7_448all
theorem t7_449choices : plan8874.choices=[5,3,6,10,10,7,7].map (options 7 6) := by rfl


theorem t7_449part0 : t7_449jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_449frontier : t7_449root.frontier 0=t7_449jobs := by rfl
theorem t7_449all : t7_449jobs.all (Job.check tree)=true := by
  simp only [t7_449jobs,List.all_append,List.all_nil,t7_449part0,Bool.and_self]
theorem t7_449checked : Checked tree [5,3,6,10,10,7,7] := by
  refine ⟨plan8874,valid8874,t7_449choices,?_⟩
  exact check_of_frontier tree 0 t7_449root t7_449jobs t7_449frontier t7_449all
theorem t7_450choices : plan8875.choices=[5,3,6,10,10,10,7].map (options 7 6) := by rfl


theorem t7_450part0 : t7_450jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_450frontier : t7_450root.frontier 0=t7_450jobs := by rfl
theorem t7_450all : t7_450jobs.all (Job.check tree)=true := by
  simp only [t7_450jobs,List.all_append,List.all_nil,t7_450part0,Bool.and_self]
theorem t7_450checked : Checked tree [5,3,6,10,10,10,7] := by
  refine ⟨plan8875,valid8875,t7_450choices,?_⟩
  exact check_of_frontier tree 0 t7_450root t7_450jobs t7_450frontier t7_450all
theorem t7_451choices : plan8876.choices=[5,3,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_451part0 : t7_451jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_451part1 : t7_451jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_451part2 : t7_451jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_451frontier : t7_451root.frontier 1=t7_451jobs := by rfl
theorem t7_451all : t7_451jobs.all (Job.check tree)=true := by
  simp only [t7_451jobs,List.all_append,List.all_nil,t7_451part0,t7_451part1,t7_451part2,Bool.and_self]
theorem t7_451checked : Checked tree [5,3,7,7,7,7,7] := by
  refine ⟨plan8876,valid8876,t7_451choices,?_⟩
  exact check_of_frontier tree 1 t7_451root t7_451jobs t7_451frontier t7_451all
theorem t7_452choices : plan8877.choices=[5,3,10,7,7,7,7].map (options 7 6) := by rfl


theorem t7_452part0 : t7_452jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_452part1 : t7_452jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_452part2 : t7_452jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_452frontier : t7_452root.frontier 1=t7_452jobs := by rfl
theorem t7_452all : t7_452jobs.all (Job.check tree)=true := by
  simp only [t7_452jobs,List.all_append,List.all_nil,t7_452part0,t7_452part1,t7_452part2,Bool.and_self]
theorem t7_452checked : Checked tree [5,3,10,7,7,7,7] := by
  refine ⟨plan8877,valid8877,t7_452choices,?_⟩
  exact check_of_frontier tree 1 t7_452root t7_452jobs t7_452frontier t7_452all
theorem t7_453choices : plan8878.choices=[5,3,10,10,7,7,7].map (options 7 6) := by rfl


theorem t7_453part0 : t7_453jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_453part1 : t7_453jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_453frontier : t7_453root.frontier 1=t7_453jobs := by rfl
theorem t7_453all : t7_453jobs.all (Job.check tree)=true := by
  simp only [t7_453jobs,List.all_append,List.all_nil,t7_453part0,t7_453part1,Bool.and_self]
theorem t7_453checked : Checked tree [5,3,10,10,7,7,7] := by
  refine ⟨plan8878,valid8878,t7_453choices,?_⟩
  exact check_of_frontier tree 1 t7_453root t7_453jobs t7_453frontier t7_453all
theorem t7_454choices : plan8879.choices=[5,3,10,10,10,7,7].map (options 7 6) := by rfl


theorem t7_454part0 : t7_454jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_454frontier : t7_454root.frontier 0=t7_454jobs := by rfl
theorem t7_454all : t7_454jobs.all (Job.check tree)=true := by
  simp only [t7_454jobs,List.all_append,List.all_nil,t7_454part0,Bool.and_self]
theorem t7_454checked : Checked tree [5,3,10,10,10,7,7] := by
  refine ⟨plan8879,valid8879,t7_454choices,?_⟩
  exact check_of_frontier tree 0 t7_454root t7_454jobs t7_454frontier t7_454all
theorem t7_455choices : plan8880.choices=[5,3,10,10,10,10,7].map (options 7 6) := by rfl


theorem t7_455part0 : t7_455jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_455frontier : t7_455root.frontier 0=t7_455jobs := by rfl
theorem t7_455all : t7_455jobs.all (Job.check tree)=true := by
  simp only [t7_455jobs,List.all_append,List.all_nil,t7_455part0,Bool.and_self]
theorem t7_455checked : Checked tree [5,3,10,10,10,10,7] := by
  refine ⟨plan8880,valid8880,t7_455choices,?_⟩
  exact check_of_frontier tree 0 t7_455root t7_455jobs t7_455frontier t7_455all
theorem t7_456choices : plan8534.choices=[5,5,3,3,3,7,7].map (options 7 4) := by rfl


theorem t7_456part0 : t7_456jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_456frontier : t7_456root.frontier 0=t7_456jobs := by rfl
theorem t7_456all : t7_456jobs.all (Job.check tree)=true := by
  simp only [t7_456jobs,List.all_append,List.all_nil,t7_456part0,Bool.and_self]
theorem t7_456checked : Checked tree [5,5,3,3,3,7,7] := by
  refine ⟨plan8534,valid8534,t7_456choices,?_⟩
  exact check_of_frontier tree 0 t7_456root t7_456jobs t7_456frontier t7_456all
theorem t7_457choices : plan8677.choices=[5,5,3,3,6,7,7].map (options 7 5) := by rfl


theorem t7_457part0 : t7_457jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_457frontier : t7_457root.frontier 0=t7_457jobs := by rfl
theorem t7_457all : t7_457jobs.all (Job.check tree)=true := by
  simp only [t7_457jobs,List.all_append,List.all_nil,t7_457part0,Bool.and_self]
theorem t7_457checked : Checked tree [5,5,3,3,6,7,7] := by
  refine ⟨plan8677,valid8677,t7_457choices,?_⟩
  exact check_of_frontier tree 0 t7_457root t7_457jobs t7_457frontier t7_457all
theorem t7_458choices : plan8678.choices=[5,5,3,3,7,7,7].map (options 7 5) := by rfl


theorem t7_458part0 : t7_458jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_458frontier : t7_458root.frontier 0=t7_458jobs := by rfl
theorem t7_458all : t7_458jobs.all (Job.check tree)=true := by
  simp only [t7_458jobs,List.all_append,List.all_nil,t7_458part0,Bool.and_self]
theorem t7_458checked : Checked tree [5,5,3,3,7,7,7] := by
  refine ⟨plan8678,valid8678,t7_458choices,?_⟩
  exact check_of_frontier tree 0 t7_458root t7_458jobs t7_458frontier t7_458all
theorem t7_459choices : plan8679.choices=[5,5,3,3,10,7,7].map (options 7 5) := by rfl


theorem t7_459part0 : t7_459jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_459frontier : t7_459root.frontier 0=t7_459jobs := by rfl
theorem t7_459all : t7_459jobs.all (Job.check tree)=true := by
  simp only [t7_459jobs,List.all_append,List.all_nil,t7_459part0,Bool.and_self]
theorem t7_459checked : Checked tree [5,5,3,3,10,7,7] := by
  refine ⟨plan8679,valid8679,t7_459choices,?_⟩
  exact check_of_frontier tree 0 t7_459root t7_459jobs t7_459frontier t7_459all
theorem t7_460choices : plan8881.choices=[5,5,3,6,6,7,7].map (options 7 6) := by rfl


theorem t7_460part0 : t7_460jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_460frontier : t7_460root.frontier 0=t7_460jobs := by rfl
theorem t7_460all : t7_460jobs.all (Job.check tree)=true := by
  simp only [t7_460jobs,List.all_append,List.all_nil,t7_460part0,Bool.and_self]
theorem t7_460checked : Checked tree [5,5,3,6,6,7,7] := by
  refine ⟨plan8881,valid8881,t7_460choices,?_⟩
  exact check_of_frontier tree 0 t7_460root t7_460jobs t7_460frontier t7_460all
theorem t7_461choices : plan8882.choices=[5,5,3,6,7,7,7].map (options 7 6) := by rfl


theorem t7_461part0 : t7_461jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_461frontier : t7_461root.frontier 0=t7_461jobs := by rfl
theorem t7_461all : t7_461jobs.all (Job.check tree)=true := by
  simp only [t7_461jobs,List.all_append,List.all_nil,t7_461part0,Bool.and_self]
theorem t7_461checked : Checked tree [5,5,3,6,7,7,7] := by
  refine ⟨plan8882,valid8882,t7_461choices,?_⟩
  exact check_of_frontier tree 0 t7_461root t7_461jobs t7_461frontier t7_461all
theorem t7_462choices : plan8883.choices=[5,5,3,6,10,7,7].map (options 7 6) := by rfl


theorem t7_462part0 : t7_462jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_462frontier : t7_462root.frontier 0=t7_462jobs := by rfl
theorem t7_462all : t7_462jobs.all (Job.check tree)=true := by
  simp only [t7_462jobs,List.all_append,List.all_nil,t7_462part0,Bool.and_self]
theorem t7_462checked : Checked tree [5,5,3,6,10,7,7] := by
  refine ⟨plan8883,valid8883,t7_462choices,?_⟩
  exact check_of_frontier tree 0 t7_462root t7_462jobs t7_462frontier t7_462all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks187 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_454checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_455checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_456checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_457checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_458checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_459checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_460checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_461checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_462checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_446checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_447checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_448checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_449checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_450checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_451checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_452checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_453checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_445checked⟩
