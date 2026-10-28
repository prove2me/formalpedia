-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks156
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:19:16.411999+00:00
-- url     : https://prove2.me/submissions/1b577d04-2fd9-49dc-9f10-e2ed5d2c01cb

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks156
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks156
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



















































theorem valid6178 : plan6178.Valid := valid_step _ _ _ valid3609 (by decide +kernel)





theorem valid6181 : plan6181.Valid := valid_step _ _ _ valid3612 (by decide +kernel)

theorem valid6182 : plan6182.Valid := valid_step _ _ _ valid3613 (by decide +kernel)





theorem valid6185 : plan6185.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6186 : plan6186.Valid := valid_step _ _ _ valid3617 (by decide +kernel)

theorem valid6187 : plan6187.Valid := valid_step _ _ _ valid3618 (by decide +kernel)





theorem valid6190 : plan6190.Valid := valid_step _ _ _ valid3616 (by decide +kernel)









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































































































































theorem valid8128 : plan8128.Valid := valid_step _ _ _ valid6146 (by decide +kernel)

theorem valid8129 : plan8129.Valid := valid_step _ _ _ valid6147 (by decide +kernel)





theorem valid8132 : plan8132.Valid := valid_step _ _ _ valid6150 (by decide +kernel)

theorem valid8133 : plan8133.Valid := valid_step _ _ _ valid6151 (by decide +kernel)

theorem valid8134 : plan8134.Valid := valid_step _ _ _ valid6152 (by decide +kernel)




















































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





















































theorem valid8475 : plan8475.Valid := valid_step _ _ _ valid8128 (by decide +kernel)

theorem valid8476 : plan8476.Valid := valid_step _ _ _ valid8129 (by decide +kernel)

theorem valid8477 : plan8477.Valid := valid_step _ _ _ valid8132 (by decide +kernel)

theorem valid8478 : plan8478.Valid := valid_step _ _ _ valid8133 (by decide +kernel)

theorem valid8479 : plan8479.Valid := valid_step _ _ _ valid8134 (by decide +kernel)


































































































































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









































theorem valid8181 : plan8181.Valid := valid_step _ _ _ valid6178 (by decide +kernel)





theorem valid8184 : plan8184.Valid := valid_step _ _ _ valid6181 (by decide +kernel)

theorem valid8185 : plan8185.Valid := valid_step _ _ _ valid6182 (by decide +kernel)





theorem valid8188 : plan8188.Valid := valid_step _ _ _ valid6185 (by decide +kernel)

theorem valid8189 : plan8189.Valid := valid_step _ _ _ valid6186 (by decide +kernel)

theorem valid8190 : plan8190.Valid := valid_step _ _ _ valid6187 (by decide +kernel)





theorem valid8193 : plan8193.Valid := valid_step _ _ _ valid6190 (by decide +kernel)

theorem valid8194 : plan8194.Valid := valid_step _ _ _ valid6195 (by decide +kernel)

theorem valid8195 : plan8195.Valid := valid_step _ _ _ valid6196 (by decide +kernel)


























































































































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



















































theorem valid8570 : plan8570.Valid := valid_step _ _ _ valid8181 (by decide +kernel)

theorem valid8571 : plan8571.Valid := valid_step _ _ _ valid8184 (by decide +kernel)

theorem valid8572 : plan8572.Valid := valid_step _ _ _ valid8185 (by decide +kernel)

theorem valid8573 : plan8573.Valid := valid_step _ _ _ valid8188 (by decide +kernel)

theorem valid8574 : plan8574.Valid := valid_step _ _ _ valid8189 (by decide +kernel)

theorem valid8575 : plan8575.Valid := valid_step _ _ _ valid8190 (by decide +kernel)

theorem valid8576 : plan8576.Valid := valid_step _ _ _ valid8193 (by decide +kernel)

theorem valid8577 : plan8577.Valid := valid_step _ _ _ valid8194 (by decide +kernel)

theorem valid8578 : plan8578.Valid := valid_step _ _ _ valid8195 (by decide +kernel)




























































































































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
theorem t7_57choices : plan8475.choices=[1,3,3,6,7,7,7].map (options 7 4) := by rfl


theorem t7_57part0 : t7_57jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_57part1 : t7_57jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_57frontier : t7_57root.frontier 1=t7_57jobs := by rfl
theorem t7_57all : t7_57jobs.all (Job.check tree)=true := by
  simp only [t7_57jobs,List.all_append,List.all_nil,t7_57part0,t7_57part1,Bool.and_self]
theorem t7_57checked : Checked tree [1,3,3,6,7,7,7] := by
  refine ⟨plan8475,valid8475,t7_57choices,?_⟩
  exact check_of_frontier tree 1 t7_57root t7_57jobs t7_57frontier t7_57all
theorem t7_58choices : plan8476.choices=[1,3,3,6,10,7,7].map (options 7 4) := by rfl


theorem t7_58part0 : t7_58jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_58frontier : t7_58root.frontier 0=t7_58jobs := by rfl
theorem t7_58all : t7_58jobs.all (Job.check tree)=true := by
  simp only [t7_58jobs,List.all_append,List.all_nil,t7_58part0,Bool.and_self]
theorem t7_58checked : Checked tree [1,3,3,6,10,7,7] := by
  refine ⟨plan8476,valid8476,t7_58choices,?_⟩
  exact check_of_frontier tree 0 t7_58root t7_58jobs t7_58frontier t7_58all
theorem t7_59choices : plan8477.choices=[1,3,3,7,7,7,7].map (options 7 4) := by rfl


theorem t7_59part0 : t7_59jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_59part1 : t7_59jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_59frontier : t7_59root.frontier 1=t7_59jobs := by rfl
theorem t7_59all : t7_59jobs.all (Job.check tree)=true := by
  simp only [t7_59jobs,List.all_append,List.all_nil,t7_59part0,t7_59part1,Bool.and_self]
theorem t7_59checked : Checked tree [1,3,3,7,7,7,7] := by
  refine ⟨plan8477,valid8477,t7_59choices,?_⟩
  exact check_of_frontier tree 1 t7_59root t7_59jobs t7_59frontier t7_59all
theorem t7_60choices : plan8478.choices=[1,3,3,10,7,7,7].map (options 7 4) := by rfl


theorem t7_60part0 : t7_60jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_60part1 : t7_60jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_60frontier : t7_60root.frontier 1=t7_60jobs := by rfl
theorem t7_60all : t7_60jobs.all (Job.check tree)=true := by
  simp only [t7_60jobs,List.all_append,List.all_nil,t7_60part0,t7_60part1,Bool.and_self]
theorem t7_60checked : Checked tree [1,3,3,10,7,7,7] := by
  refine ⟨plan8478,valid8478,t7_60choices,?_⟩
  exact check_of_frontier tree 1 t7_60root t7_60jobs t7_60frontier t7_60all
theorem t7_61choices : plan8479.choices=[1,3,3,10,10,7,7].map (options 7 4) := by rfl


theorem t7_61part0 : t7_61jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_61frontier : t7_61root.frontier 0=t7_61jobs := by rfl
theorem t7_61all : t7_61jobs.all (Job.check tree)=true := by
  simp only [t7_61jobs,List.all_append,List.all_nil,t7_61part0,Bool.and_self]
theorem t7_61checked : Checked tree [1,3,3,10,10,7,7] := by
  refine ⟨plan8479,valid8479,t7_61choices,?_⟩
  exact check_of_frontier tree 0 t7_61root t7_61jobs t7_61frontier t7_61all
theorem t7_62choices : plan8570.choices=[1,3,6,6,6,7,7].map (options 7 5) := by rfl


theorem t7_62part0 : t7_62jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_62frontier : t7_62root.frontier 0=t7_62jobs := by rfl
theorem t7_62all : t7_62jobs.all (Job.check tree)=true := by
  simp only [t7_62jobs,List.all_append,List.all_nil,t7_62part0,Bool.and_self]
theorem t7_62checked : Checked tree [1,3,6,6,6,7,7] := by
  refine ⟨plan8570,valid8570,t7_62choices,?_⟩
  exact check_of_frontier tree 0 t7_62root t7_62jobs t7_62frontier t7_62all
theorem t7_63choices : plan8571.choices=[1,3,6,6,7,7,7].map (options 7 5) := by rfl


theorem t7_63part0 : t7_63jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_63frontier : t7_63root.frontier 0=t7_63jobs := by rfl
theorem t7_63all : t7_63jobs.all (Job.check tree)=true := by
  simp only [t7_63jobs,List.all_append,List.all_nil,t7_63part0,Bool.and_self]
theorem t7_63checked : Checked tree [1,3,6,6,7,7,7] := by
  refine ⟨plan8571,valid8571,t7_63choices,?_⟩
  exact check_of_frontier tree 0 t7_63root t7_63jobs t7_63frontier t7_63all
theorem t7_64choices : plan8572.choices=[1,3,6,6,10,7,7].map (options 7 5) := by rfl


theorem t7_64part0 : t7_64jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_64frontier : t7_64root.frontier 0=t7_64jobs := by rfl
theorem t7_64all : t7_64jobs.all (Job.check tree)=true := by
  simp only [t7_64jobs,List.all_append,List.all_nil,t7_64part0,Bool.and_self]
theorem t7_64checked : Checked tree [1,3,6,6,10,7,7] := by
  refine ⟨plan8572,valid8572,t7_64choices,?_⟩
  exact check_of_frontier tree 0 t7_64root t7_64jobs t7_64frontier t7_64all
theorem t7_65choices : plan8573.choices=[1,3,6,7,7,7,7].map (options 7 5) := by rfl


theorem t7_65part0 : t7_65jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_65part1 : t7_65jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_65part2 : t7_65jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_65frontier : t7_65root.frontier 1=t7_65jobs := by rfl
theorem t7_65all : t7_65jobs.all (Job.check tree)=true := by
  simp only [t7_65jobs,List.all_append,List.all_nil,t7_65part0,t7_65part1,t7_65part2,Bool.and_self]
theorem t7_65checked : Checked tree [1,3,6,7,7,7,7] := by
  refine ⟨plan8573,valid8573,t7_65choices,?_⟩
  exact check_of_frontier tree 1 t7_65root t7_65jobs t7_65frontier t7_65all
theorem t7_66choices : plan8574.choices=[1,3,6,10,7,7,7].map (options 7 5) := by rfl


theorem t7_66part0 : t7_66jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_66part1 : t7_66jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_66frontier : t7_66root.frontier 1=t7_66jobs := by rfl
theorem t7_66all : t7_66jobs.all (Job.check tree)=true := by
  simp only [t7_66jobs,List.all_append,List.all_nil,t7_66part0,t7_66part1,Bool.and_self]
theorem t7_66checked : Checked tree [1,3,6,10,7,7,7] := by
  refine ⟨plan8574,valid8574,t7_66choices,?_⟩
  exact check_of_frontier tree 1 t7_66root t7_66jobs t7_66frontier t7_66all
theorem t7_67choices : plan8575.choices=[1,3,6,10,10,7,7].map (options 7 5) := by rfl


theorem t7_67part0 : t7_67jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_67frontier : t7_67root.frontier 0=t7_67jobs := by rfl
theorem t7_67all : t7_67jobs.all (Job.check tree)=true := by
  simp only [t7_67jobs,List.all_append,List.all_nil,t7_67part0,Bool.and_self]
theorem t7_67checked : Checked tree [1,3,6,10,10,7,7] := by
  refine ⟨plan8575,valid8575,t7_67choices,?_⟩
  exact check_of_frontier tree 0 t7_67root t7_67jobs t7_67frontier t7_67all
theorem t7_68choices : plan8576.choices=[1,3,7,7,7,7,7].map (options 7 5) := by rfl


theorem t7_68part0 : t7_68jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_68part1 : t7_68jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_68frontier : t7_68root.frontier 1=t7_68jobs := by rfl
theorem t7_68all : t7_68jobs.all (Job.check tree)=true := by
  simp only [t7_68jobs,List.all_append,List.all_nil,t7_68part0,t7_68part1,Bool.and_self]
theorem t7_68checked : Checked tree [1,3,7,7,7,7,7] := by
  refine ⟨plan8576,valid8576,t7_68choices,?_⟩
  exact check_of_frontier tree 1 t7_68root t7_68jobs t7_68frontier t7_68all
theorem t7_69choices : plan8577.choices=[1,3,10,7,7,7,7].map (options 7 5) := by rfl


theorem t7_69part0 : t7_69jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_69part1 : t7_69jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_69part2 : t7_69jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_69frontier : t7_69root.frontier 1=t7_69jobs := by rfl
theorem t7_69all : t7_69jobs.all (Job.check tree)=true := by
  simp only [t7_69jobs,List.all_append,List.all_nil,t7_69part0,t7_69part1,t7_69part2,Bool.and_self]
theorem t7_69checked : Checked tree [1,3,10,7,7,7,7] := by
  refine ⟨plan8577,valid8577,t7_69choices,?_⟩
  exact check_of_frontier tree 1 t7_69root t7_69jobs t7_69frontier t7_69all
theorem t7_70choices : plan8578.choices=[1,3,10,10,7,7,7].map (options 7 5) := by rfl


theorem t7_70part0 : t7_70jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_70frontier : t7_70root.frontier 0=t7_70jobs := by rfl
theorem t7_70all : t7_70jobs.all (Job.check tree)=true := by
  simp only [t7_70jobs,List.all_append,List.all_nil,t7_70part0,Bool.and_self]
theorem t7_70checked : Checked tree [1,3,10,10,7,7,7] := by
  refine ⟨plan8578,valid8578,t7_70choices,?_⟩
  exact check_of_frontier tree 0 t7_70root t7_70jobs t7_70frontier t7_70all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks156 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_68checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_69checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_57checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_70checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_58checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_59checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_60checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_61checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_62checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_63checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_64checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_65checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_66checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_67checked⟩
