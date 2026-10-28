-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks158
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:25:15.954676+00:00
-- url     : https://prove2.me/submissions/ec60efde-48f9-4f4d-9be0-f1b58bde9ef3

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks158
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks158
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans088
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans089
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











































theorem valid1654 : plan1654.Valid := valid_step _ _ _ valid607 (by decide +kernel)

theorem valid1655 : plan1655.Valid := valid_step _ _ _ valid607 (by decide +kernel)











theorem valid1661 : plan1661.Valid := valid_step _ _ _ valid613 (by decide +kernel)





theorem valid1664 : plan1664.Valid := valid_step _ _ _ valid613 (by decide +kernel)

theorem valid1665 : plan1665.Valid := valid_step _ _ _ valid613 (by decide +kernel)






























































































































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

































































theorem valid3585 : plan3585.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

















theorem valid3594 : plan3594.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

theorem valid3595 : plan3595.Valid := valid_step _ _ _ valid1655 (by decide +kernel)





theorem valid3598 : plan3598.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

theorem valid3599 : plan3599.Valid := valid_step _ _ _ valid1654 (by decide +kernel)

theorem valid3600 : plan3600.Valid := valid_step _ _ _ valid1655 (by decide +kernel)

















theorem valid3609 : plan3609.Valid := valid_step _ _ _ valid1661 (by decide +kernel)





theorem valid3612 : plan3612.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3613 : plan3613.Valid := valid_step _ _ _ valid1665 (by decide +kernel)





theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3617 : plan3617.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3618 : plan3618.Valid := valid_step _ _ _ valid1665 (by decide +kernel)




























































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



theorem valid6146 : plan6146.Valid := valid_step _ _ _ valid3594 (by decide +kernel)

theorem valid6147 : plan6147.Valid := valid_step _ _ _ valid3595 (by decide +kernel)





theorem valid6150 : plan6150.Valid := valid_step _ _ _ valid3598 (by decide +kernel)

theorem valid6151 : plan6151.Valid := valid_step _ _ _ valid3599 (by decide +kernel)

theorem valid6152 : plan6152.Valid := valid_step _ _ _ valid3600 (by decide +kernel)





theorem valid6155 : plan6155.Valid := valid_step _ _ _ valid3585 (by decide +kernel)

theorem valid6156 : plan6156.Valid := valid_step _ _ _ valid3585 (by decide +kernel)































theorem valid6172 : plan6172.Valid := valid_step _ _ _ valid3612 (by decide +kernel)

theorem valid6173 : plan6173.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6174 : plan6174.Valid := valid_step _ _ _ valid3617 (by decide +kernel)







theorem valid6178 : plan6178.Valid := valid_step _ _ _ valid3609 (by decide +kernel)





theorem valid6181 : plan6181.Valid := valid_step _ _ _ valid3612 (by decide +kernel)

theorem valid6182 : plan6182.Valid := valid_step _ _ _ valid3613 (by decide +kernel)





theorem valid6185 : plan6185.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6186 : plan6186.Valid := valid_step _ _ _ valid3617 (by decide +kernel)

theorem valid6187 : plan6187.Valid := valid_step _ _ _ valid3618 (by decide +kernel)





theorem valid6190 : plan6190.Valid := valid_step _ _ _ valid3616 (by decide +kernel)



theorem valid6192 : plan6192.Valid := valid_step _ _ _ valid3612 (by decide +kernel)

theorem valid6193 : plan6193.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6194 : plan6194.Valid := valid_step _ _ _ valid3617 (by decide +kernel)

theorem valid6195 : plan6195.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6196 : plan6196.Valid := valid_step _ _ _ valid3617 (by decide +kernel)
























































































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

























































































theorem valid8109 : plan8109.Valid := valid_step _ _ _ valid6146 (by decide +kernel)

theorem valid8110 : plan8110.Valid := valid_step _ _ _ valid6147 (by decide +kernel)

theorem valid8111 : plan8111.Valid := valid_step _ _ _ valid6150 (by decide +kernel)

theorem valid8112 : plan8112.Valid := valid_step _ _ _ valid6151 (by decide +kernel)

theorem valid8113 : plan8113.Valid := valid_step _ _ _ valid6152 (by decide +kernel)

theorem valid8114 : plan8114.Valid := valid_step _ _ _ valid6155 (by decide +kernel)

theorem valid8115 : plan8115.Valid := valid_step _ _ _ valid6156 (by decide +kernel)









































































theorem valid8152 : plan8152.Valid := valid_step _ _ _ valid6172 (by decide +kernel)

theorem valid8153 : plan8153.Valid := valid_step _ _ _ valid6173 (by decide +kernel)

theorem valid8154 : plan8154.Valid := valid_step _ _ _ valid6174 (by decide +kernel)

theorem valid8155 : plan8155.Valid := valid_step _ _ _ valid6178 (by decide +kernel)

theorem valid8156 : plan8156.Valid := valid_step _ _ _ valid6181 (by decide +kernel)

theorem valid8157 : plan8157.Valid := valid_step _ _ _ valid6182 (by decide +kernel)

theorem valid8158 : plan8158.Valid := valid_step _ _ _ valid6185 (by decide +kernel)

theorem valid8159 : plan8159.Valid := valid_step _ _ _ valid6186 (by decide +kernel)

theorem valid8160 : plan8160.Valid := valid_step _ _ _ valid6187 (by decide +kernel)
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











































































theorem valid8486 : plan8486.Valid := valid_step _ _ _ valid8109 (by decide +kernel)

theorem valid8487 : plan8487.Valid := valid_step _ _ _ valid8110 (by decide +kernel)

theorem valid8488 : plan8488.Valid := valid_step _ _ _ valid8111 (by decide +kernel)

theorem valid8489 : plan8489.Valid := valid_step _ _ _ valid8112 (by decide +kernel)

theorem valid8490 : plan8490.Valid := valid_step _ _ _ valid8113 (by decide +kernel)

theorem valid8491 : plan8491.Valid := valid_step _ _ _ valid8114 (by decide +kernel)

theorem valid8492 : plan8492.Valid := valid_step _ _ _ valid8115 (by decide +kernel)








































































































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

theorem valid8161 : plan8161.Valid := valid_step _ _ _ valid6190 (by decide +kernel)

theorem valid8162 : plan8162.Valid := valid_step _ _ _ valid6192 (by decide +kernel)

theorem valid8163 : plan8163.Valid := valid_step _ _ _ valid6193 (by decide +kernel)

theorem valid8164 : plan8164.Valid := valid_step _ _ _ valid6194 (by decide +kernel)

theorem valid8165 : plan8165.Valid := valid_step _ _ _ valid6195 (by decide +kernel)

theorem valid8166 : plan8166.Valid := valid_step _ _ _ valid6196 (by decide +kernel)




















































































































































































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























































































theorem valid8588 : plan8588.Valid := valid_step _ _ _ valid8152 (by decide +kernel)

theorem valid8589 : plan8589.Valid := valid_step _ _ _ valid8153 (by decide +kernel)

theorem valid8590 : plan8590.Valid := valid_step _ _ _ valid8154 (by decide +kernel)

theorem valid8591 : plan8591.Valid := valid_step _ _ _ valid8155 (by decide +kernel)

theorem valid8592 : plan8592.Valid := valid_step _ _ _ valid8156 (by decide +kernel)

theorem valid8593 : plan8593.Valid := valid_step _ _ _ valid8157 (by decide +kernel)

theorem valid8594 : plan8594.Valid := valid_step _ _ _ valid8158 (by decide +kernel)

theorem valid8595 : plan8595.Valid := valid_step _ _ _ valid8159 (by decide +kernel)

theorem valid8596 : plan8596.Valid := valid_step _ _ _ valid8160 (by decide +kernel)

theorem valid8597 : plan8597.Valid := valid_step _ _ _ valid8161 (by decide +kernel)

theorem valid8598 : plan8598.Valid := valid_step _ _ _ valid8162 (by decide +kernel)

theorem valid8599 : plan8599.Valid := valid_step _ _ _ valid8163 (by decide +kernel)

theorem valid8600 : plan8600.Valid := valid_step _ _ _ valid8164 (by decide +kernel)

theorem valid8601 : plan8601.Valid := valid_step _ _ _ valid8165 (by decide +kernel)

theorem valid8602 : plan8602.Valid := valid_step _ _ _ valid8166 (by decide +kernel)












































































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
theorem t7_127choices : plan8486.choices=[2,2,3,6,7,7,7].map (options 7 4) := by rfl


theorem t7_127part0 : t7_127jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_127part1 : t7_127jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_127part2 : t7_127jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_127frontier : t7_127root.frontier 1=t7_127jobs := by rfl
theorem t7_127all : t7_127jobs.all (Job.check tree)=true := by
  simp only [t7_127jobs,List.all_append,List.all_nil,t7_127part0,t7_127part1,t7_127part2,Bool.and_self]
theorem t7_127checked : Checked tree [2,2,3,6,7,7,7] := by
  refine ⟨plan8486,valid8486,t7_127choices,?_⟩
  exact check_of_frontier tree 1 t7_127root t7_127jobs t7_127frontier t7_127all
theorem t7_128choices : plan8487.choices=[2,2,3,6,10,7,7].map (options 7 4) := by rfl


theorem t7_128part0 : t7_128jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_128part1 : t7_128jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_128frontier : t7_128root.frontier 1=t7_128jobs := by rfl
theorem t7_128all : t7_128jobs.all (Job.check tree)=true := by
  simp only [t7_128jobs,List.all_append,List.all_nil,t7_128part0,t7_128part1,Bool.and_self]
theorem t7_128checked : Checked tree [2,2,3,6,10,7,7] := by
  refine ⟨plan8487,valid8487,t7_128choices,?_⟩
  exact check_of_frontier tree 1 t7_128root t7_128jobs t7_128frontier t7_128all
theorem t7_129choices : plan8488.choices=[2,2,3,7,7,7,7].map (options 7 4) := by rfl


theorem t7_129part0 : t7_129jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_129part1 : t7_129jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_129part2 : t7_129jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_129frontier : t7_129root.frontier 1=t7_129jobs := by rfl
theorem t7_129all : t7_129jobs.all (Job.check tree)=true := by
  simp only [t7_129jobs,List.all_append,List.all_nil,t7_129part0,t7_129part1,t7_129part2,Bool.and_self]
theorem t7_129checked : Checked tree [2,2,3,7,7,7,7] := by
  refine ⟨plan8488,valid8488,t7_129choices,?_⟩
  exact check_of_frontier tree 1 t7_129root t7_129jobs t7_129frontier t7_129all
theorem t7_130choices : plan8489.choices=[2,2,3,10,7,7,7].map (options 7 4) := by rfl


theorem t7_130part0 : t7_130jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_130part1 : t7_130jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_130part2 : t7_130jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_130frontier : t7_130root.frontier 1=t7_130jobs := by rfl
theorem t7_130all : t7_130jobs.all (Job.check tree)=true := by
  simp only [t7_130jobs,List.all_append,List.all_nil,t7_130part0,t7_130part1,t7_130part2,Bool.and_self]
theorem t7_130checked : Checked tree [2,2,3,10,7,7,7] := by
  refine ⟨plan8489,valid8489,t7_130choices,?_⟩
  exact check_of_frontier tree 1 t7_130root t7_130jobs t7_130frontier t7_130all
theorem t7_131choices : plan8490.choices=[2,2,3,10,10,7,7].map (options 7 4) := by rfl


theorem t7_131part0 : t7_131jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_131frontier : t7_131root.frontier 0=t7_131jobs := by rfl
theorem t7_131all : t7_131jobs.all (Job.check tree)=true := by
  simp only [t7_131jobs,List.all_append,List.all_nil,t7_131part0,Bool.and_self]
theorem t7_131checked : Checked tree [2,2,3,10,10,7,7] := by
  refine ⟨plan8490,valid8490,t7_131choices,?_⟩
  exact check_of_frontier tree 0 t7_131root t7_131jobs t7_131frontier t7_131all
theorem t7_132choices : plan8491.choices=[2,2,5,3,7,7,7].map (options 7 4) := by rfl


theorem t7_132part0 : t7_132jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_132frontier : t7_132root.frontier 0=t7_132jobs := by rfl
theorem t7_132all : t7_132jobs.all (Job.check tree)=true := by
  simp only [t7_132jobs,List.all_append,List.all_nil,t7_132part0,Bool.and_self]
theorem t7_132checked : Checked tree [2,2,5,3,7,7,7] := by
  refine ⟨plan8491,valid8491,t7_132choices,?_⟩
  exact check_of_frontier tree 0 t7_132root t7_132jobs t7_132frontier t7_132all
theorem t7_133choices : plan8588.choices=[2,2,5,6,7,7,7].map (options 7 5) := by rfl


theorem t7_133part0 : t7_133jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_133frontier : t7_133root.frontier 0=t7_133jobs := by rfl
theorem t7_133all : t7_133jobs.all (Job.check tree)=true := by
  simp only [t7_133jobs,List.all_append,List.all_nil,t7_133part0,Bool.and_self]
theorem t7_133checked : Checked tree [2,2,5,6,7,7,7] := by
  refine ⟨plan8588,valid8588,t7_133choices,?_⟩
  exact check_of_frontier tree 0 t7_133root t7_133jobs t7_133frontier t7_133all
theorem t7_134choices : plan8589.choices=[2,2,5,7,7,7,7].map (options 7 5) := by rfl


theorem t7_134part0 : t7_134jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_134frontier : t7_134root.frontier 0=t7_134jobs := by rfl
theorem t7_134all : t7_134jobs.all (Job.check tree)=true := by
  simp only [t7_134jobs,List.all_append,List.all_nil,t7_134part0,Bool.and_self]
theorem t7_134checked : Checked tree [2,2,5,7,7,7,7] := by
  refine ⟨plan8589,valid8589,t7_134choices,?_⟩
  exact check_of_frontier tree 0 t7_134root t7_134jobs t7_134frontier t7_134all
theorem t7_135choices : plan8590.choices=[2,2,5,10,7,7,7].map (options 7 5) := by rfl


theorem t7_135part0 : t7_135jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_135frontier : t7_135root.frontier 0=t7_135jobs := by rfl
theorem t7_135all : t7_135jobs.all (Job.check tree)=true := by
  simp only [t7_135jobs,List.all_append,List.all_nil,t7_135part0,Bool.and_self]
theorem t7_135checked : Checked tree [2,2,5,10,7,7,7] := by
  refine ⟨plan8590,valid8590,t7_135choices,?_⟩
  exact check_of_frontier tree 0 t7_135root t7_135jobs t7_135frontier t7_135all
theorem t7_136choices : plan8591.choices=[2,2,6,6,6,7,7].map (options 7 5) := by rfl


theorem t7_136part0 : t7_136jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_136frontier : t7_136root.frontier 0=t7_136jobs := by rfl
theorem t7_136all : t7_136jobs.all (Job.check tree)=true := by
  simp only [t7_136jobs,List.all_append,List.all_nil,t7_136part0,Bool.and_self]
theorem t7_136checked : Checked tree [2,2,6,6,6,7,7] := by
  refine ⟨plan8591,valid8591,t7_136choices,?_⟩
  exact check_of_frontier tree 0 t7_136root t7_136jobs t7_136frontier t7_136all
theorem t7_137choices : plan8592.choices=[2,2,6,6,7,7,7].map (options 7 5) := by rfl


theorem t7_137part0 : t7_137jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_137frontier : t7_137root.frontier 0=t7_137jobs := by rfl
theorem t7_137all : t7_137jobs.all (Job.check tree)=true := by
  simp only [t7_137jobs,List.all_append,List.all_nil,t7_137part0,Bool.and_self]
theorem t7_137checked : Checked tree [2,2,6,6,7,7,7] := by
  refine ⟨plan8592,valid8592,t7_137choices,?_⟩
  exact check_of_frontier tree 0 t7_137root t7_137jobs t7_137frontier t7_137all
theorem t7_138choices : plan8593.choices=[2,2,6,6,10,7,7].map (options 7 5) := by rfl


theorem t7_138part0 : t7_138jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_138frontier : t7_138root.frontier 0=t7_138jobs := by rfl
theorem t7_138all : t7_138jobs.all (Job.check tree)=true := by
  simp only [t7_138jobs,List.all_append,List.all_nil,t7_138part0,Bool.and_self]
theorem t7_138checked : Checked tree [2,2,6,6,10,7,7] := by
  refine ⟨plan8593,valid8593,t7_138choices,?_⟩
  exact check_of_frontier tree 0 t7_138root t7_138jobs t7_138frontier t7_138all
theorem t7_139choices : plan8594.choices=[2,2,6,7,7,7,7].map (options 7 5) := by rfl


theorem t7_139part0 : t7_139jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_139part1 : t7_139jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_139frontier : t7_139root.frontier 1=t7_139jobs := by rfl
theorem t7_139all : t7_139jobs.all (Job.check tree)=true := by
  simp only [t7_139jobs,List.all_append,List.all_nil,t7_139part0,t7_139part1,Bool.and_self]
theorem t7_139checked : Checked tree [2,2,6,7,7,7,7] := by
  refine ⟨plan8594,valid8594,t7_139choices,?_⟩
  exact check_of_frontier tree 1 t7_139root t7_139jobs t7_139frontier t7_139all
theorem t7_140choices : plan8595.choices=[2,2,6,10,7,7,7].map (options 7 5) := by rfl


theorem t7_140part0 : t7_140jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_140frontier : t7_140root.frontier 0=t7_140jobs := by rfl
theorem t7_140all : t7_140jobs.all (Job.check tree)=true := by
  simp only [t7_140jobs,List.all_append,List.all_nil,t7_140part0,Bool.and_self]
theorem t7_140checked : Checked tree [2,2,6,10,7,7,7] := by
  refine ⟨plan8595,valid8595,t7_140choices,?_⟩
  exact check_of_frontier tree 0 t7_140root t7_140jobs t7_140frontier t7_140all
theorem t7_141choices : plan8596.choices=[2,2,6,10,10,7,7].map (options 7 5) := by rfl


theorem t7_141part0 : t7_141jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_141frontier : t7_141root.frontier 0=t7_141jobs := by rfl
theorem t7_141all : t7_141jobs.all (Job.check tree)=true := by
  simp only [t7_141jobs,List.all_append,List.all_nil,t7_141part0,Bool.and_self]
theorem t7_141checked : Checked tree [2,2,6,10,10,7,7] := by
  refine ⟨plan8596,valid8596,t7_141choices,?_⟩
  exact check_of_frontier tree 0 t7_141root t7_141jobs t7_141frontier t7_141all
theorem t7_142choices : plan8597.choices=[2,2,7,7,7,7,7].map (options 7 5) := by rfl


theorem t7_142part0 : t7_142jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_142frontier : t7_142root.frontier 0=t7_142jobs := by rfl
theorem t7_142all : t7_142jobs.all (Job.check tree)=true := by
  simp only [t7_142jobs,List.all_append,List.all_nil,t7_142part0,Bool.and_self]
theorem t7_142checked : Checked tree [2,2,7,7,7,7,7] := by
  refine ⟨plan8597,valid8597,t7_142choices,?_⟩
  exact check_of_frontier tree 0 t7_142root t7_142jobs t7_142frontier t7_142all
theorem t7_143choices : plan8492.choices=[2,2,9,3,7,7,7].map (options 7 4) := by rfl


theorem t7_143part0 : t7_143jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_143frontier : t7_143root.frontier 0=t7_143jobs := by rfl
theorem t7_143all : t7_143jobs.all (Job.check tree)=true := by
  simp only [t7_143jobs,List.all_append,List.all_nil,t7_143part0,Bool.and_self]
theorem t7_143checked : Checked tree [2,2,9,3,7,7,7] := by
  refine ⟨plan8492,valid8492,t7_143choices,?_⟩
  exact check_of_frontier tree 0 t7_143root t7_143jobs t7_143frontier t7_143all
theorem t7_144choices : plan8598.choices=[2,2,9,6,7,7,7].map (options 7 5) := by rfl


theorem t7_144part0 : t7_144jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_144frontier : t7_144root.frontier 0=t7_144jobs := by rfl
theorem t7_144all : t7_144jobs.all (Job.check tree)=true := by
  simp only [t7_144jobs,List.all_append,List.all_nil,t7_144part0,Bool.and_self]
theorem t7_144checked : Checked tree [2,2,9,6,7,7,7] := by
  refine ⟨plan8598,valid8598,t7_144choices,?_⟩
  exact check_of_frontier tree 0 t7_144root t7_144jobs t7_144frontier t7_144all
theorem t7_145choices : plan8599.choices=[2,2,9,7,7,7,7].map (options 7 5) := by rfl


theorem t7_145part0 : t7_145jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_145frontier : t7_145root.frontier 0=t7_145jobs := by rfl
theorem t7_145all : t7_145jobs.all (Job.check tree)=true := by
  simp only [t7_145jobs,List.all_append,List.all_nil,t7_145part0,Bool.and_self]
theorem t7_145checked : Checked tree [2,2,9,7,7,7,7] := by
  refine ⟨plan8599,valid8599,t7_145choices,?_⟩
  exact check_of_frontier tree 0 t7_145root t7_145jobs t7_145frontier t7_145all
theorem t7_146choices : plan8600.choices=[2,2,9,10,7,7,7].map (options 7 5) := by rfl


theorem t7_146part0 : t7_146jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_146frontier : t7_146root.frontier 0=t7_146jobs := by rfl
theorem t7_146all : t7_146jobs.all (Job.check tree)=true := by
  simp only [t7_146jobs,List.all_append,List.all_nil,t7_146part0,Bool.and_self]
theorem t7_146checked : Checked tree [2,2,9,10,7,7,7] := by
  refine ⟨plan8600,valid8600,t7_146choices,?_⟩
  exact check_of_frontier tree 0 t7_146root t7_146jobs t7_146frontier t7_146all
theorem t7_147choices : plan8601.choices=[2,2,10,7,7,7,7].map (options 7 5) := by rfl


theorem t7_147part0 : t7_147jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_147part1 : t7_147jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_147frontier : t7_147root.frontier 1=t7_147jobs := by rfl
theorem t7_147all : t7_147jobs.all (Job.check tree)=true := by
  simp only [t7_147jobs,List.all_append,List.all_nil,t7_147part0,t7_147part1,Bool.and_self]
theorem t7_147checked : Checked tree [2,2,10,7,7,7,7] := by
  refine ⟨plan8601,valid8601,t7_147choices,?_⟩
  exact check_of_frontier tree 1 t7_147root t7_147jobs t7_147frontier t7_147all
theorem t7_148choices : plan8602.choices=[2,2,10,10,7,7,7].map (options 7 5) := by rfl


theorem t7_148part0 : t7_148jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_148frontier : t7_148root.frontier 0=t7_148jobs := by rfl
theorem t7_148all : t7_148jobs.all (Job.check tree)=true := by
  simp only [t7_148jobs,List.all_append,List.all_nil,t7_148part0,Bool.and_self]
theorem t7_148checked : Checked tree [2,2,10,10,7,7,7] := by
  refine ⟨plan8602,valid8602,t7_148choices,?_⟩
  exact check_of_frontier tree 0 t7_148root t7_148jobs t7_148frontier t7_148all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks158 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_137checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_138checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_139checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_140checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_141checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_142checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_127checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_143checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_144checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_145checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_146checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_147checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_148checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_128checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_129checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_130checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_131checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_132checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_133checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_134checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_135checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_136checked⟩
