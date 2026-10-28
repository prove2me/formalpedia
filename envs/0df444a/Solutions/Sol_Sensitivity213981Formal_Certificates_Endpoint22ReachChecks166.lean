-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks166
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:05:39.541021+00:00
-- url     : https://prove2.me/submissions/3c3db33e-d3bf-4271-8f28-ed0c9fe25a98

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks166
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks166
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











theorem valid1671 : plan1671.Valid := valid_step _ _ _ valid619 (by decide +kernel)





theorem valid1674 : plan1674.Valid := valid_step _ _ _ valid619 (by decide +kernel)

theorem valid1675 : plan1675.Valid := valid_step _ _ _ valid619 (by decide +kernel)










































































































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

theorem valid3586 : plan3586.Valid := valid_step _ _ _ valid1655 (by decide +kernel)



































theorem valid3604 : plan3604.Valid := valid_step _ _ _ valid1664 (by decide +kernel)









theorem valid3609 : plan3609.Valid := valid_step _ _ _ valid1661 (by decide +kernel)





theorem valid3612 : plan3612.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3613 : plan3613.Valid := valid_step _ _ _ valid1665 (by decide +kernel)





theorem valid3616 : plan3616.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3617 : plan3617.Valid := valid_step _ _ _ valid1664 (by decide +kernel)

theorem valid3618 : plan3618.Valid := valid_step _ _ _ valid1665 (by decide +kernel)













theorem valid3625 : plan3625.Valid := valid_step _ _ _ valid1671 (by decide +kernel)





theorem valid3628 : plan3628.Valid := valid_step _ _ _ valid1674 (by decide +kernel)

theorem valid3629 : plan3629.Valid := valid_step _ _ _ valid1675 (by decide +kernel)





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



































theorem valid6162 : plan6162.Valid := valid_step _ _ _ valid3609 (by decide +kernel)



theorem valid6164 : plan6164.Valid := valid_step _ _ _ valid3612 (by decide +kernel)

theorem valid6165 : plan6165.Valid := valid_step _ _ _ valid3613 (by decide +kernel)



theorem valid6167 : plan6167.Valid := valid_step _ _ _ valid3616 (by decide +kernel)

theorem valid6168 : plan6168.Valid := valid_step _ _ _ valid3617 (by decide +kernel)

theorem valid6169 : plan6169.Valid := valid_step _ _ _ valid3618 (by decide +kernel)



theorem valid6171 : plan6171.Valid := valid_step _ _ _ valid3604 (by decide +kernel)







































































theorem valid6207 : plan6207.Valid := valid_step _ _ _ valid3628 (by decide +kernel)

theorem valid6208 : plan6208.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6209 : plan6209.Valid := valid_step _ _ _ valid3633 (by decide +kernel)







theorem valid6213 : plan6213.Valid := valid_step _ _ _ valid3625 (by decide +kernel)





theorem valid6216 : plan6216.Valid := valid_step _ _ _ valid3628 (by decide +kernel)

theorem valid6217 : plan6217.Valid := valid_step _ _ _ valid3629 (by decide +kernel)





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





















































































































































theorem valid8139 : plan8139.Valid := valid_step _ _ _ valid6137 (by decide +kernel)

theorem valid8140 : plan8140.Valid := valid_step _ _ _ valid6138 (by decide +kernel)








































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















































































































theorem valid8504 : plan8504.Valid := valid_step _ _ _ valid8139 (by decide +kernel)

theorem valid8505 : plan8505.Valid := valid_step _ _ _ valid8140 (by decide +kernel)














































































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





















































































theorem valid8203 : plan8203.Valid := valid_step _ _ _ valid6162 (by decide +kernel)

theorem valid8204 : plan8204.Valid := valid_step _ _ _ valid6164 (by decide +kernel)

theorem valid8205 : plan8205.Valid := valid_step _ _ _ valid6165 (by decide +kernel)

theorem valid8206 : plan8206.Valid := valid_step _ _ _ valid6167 (by decide +kernel)

theorem valid8207 : plan8207.Valid := valid_step _ _ _ valid6168 (by decide +kernel)

theorem valid8208 : plan8208.Valid := valid_step _ _ _ valid6169 (by decide +kernel)

theorem valid8209 : plan8209.Valid := valid_step _ _ _ valid6171 (by decide +kernel)





























































































theorem valid8256 : plan8256.Valid := valid_step _ _ _ valid6207 (by decide +kernel)
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





















































































































































theorem valid8619 : plan8619.Valid := valid_step _ _ _ valid8203 (by decide +kernel)

theorem valid8620 : plan8620.Valid := valid_step _ _ _ valid8204 (by decide +kernel)

theorem valid8621 : plan8621.Valid := valid_step _ _ _ valid8205 (by decide +kernel)

theorem valid8622 : plan8622.Valid := valid_step _ _ _ valid8206 (by decide +kernel)

theorem valid8623 : plan8623.Valid := valid_step _ _ _ valid8207 (by decide +kernel)

theorem valid8624 : plan8624.Valid := valid_step _ _ _ valid8208 (by decide +kernel)

theorem valid8625 : plan8625.Valid := valid_step _ _ _ valid8209 (by decide +kernel)






























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

theorem valid8257 : plan8257.Valid := valid_step _ _ _ valid6208 (by decide +kernel)

theorem valid8258 : plan8258.Valid := valid_step _ _ _ valid6209 (by decide +kernel)

theorem valid8259 : plan8259.Valid := valid_step _ _ _ valid6213 (by decide +kernel)

theorem valid8260 : plan8260.Valid := valid_step _ _ _ valid6216 (by decide +kernel)

theorem valid8261 : plan8261.Valid := valid_step _ _ _ valid6217 (by decide +kernel)

theorem valid8262 : plan8262.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8263 : plan8263.Valid := valid_step _ _ _ valid6221 (by decide +kernel)

theorem valid8264 : plan8264.Valid := valid_step _ _ _ valid6222 (by decide +kernel)
















































































































































































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



















































theorem valid8762 : plan8762.Valid := valid_step _ _ _ valid8256 (by decide +kernel)

theorem valid8763 : plan8763.Valid := valid_step _ _ _ valid8257 (by decide +kernel)

theorem valid8764 : plan8764.Valid := valid_step _ _ _ valid8258 (by decide +kernel)

theorem valid8765 : plan8765.Valid := valid_step _ _ _ valid8259 (by decide +kernel)

theorem valid8766 : plan8766.Valid := valid_step _ _ _ valid8260 (by decide +kernel)

theorem valid8767 : plan8767.Valid := valid_step _ _ _ valid8261 (by decide +kernel)

theorem valid8768 : plan8768.Valid := valid_step _ _ _ valid8262 (by decide +kernel)

theorem valid8769 : plan8769.Valid := valid_step _ _ _ valid8263 (by decide +kernel)

theorem valid8770 : plan8770.Valid := valid_step _ _ _ valid8264 (by decide +kernel)




























































































































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
theorem t7_187choices : plan8504.choices=[2,5,3,3,7,7,7].map (options 7 4) := by rfl


theorem t7_187part0 : t7_187jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_187part1 : t7_187jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_187part2 : t7_187jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_187frontier : t7_187root.frontier 1=t7_187jobs := by rfl
theorem t7_187all : t7_187jobs.all (Job.check tree)=true := by
  simp only [t7_187jobs,List.all_append,List.all_nil,t7_187part0,t7_187part1,t7_187part2,Bool.and_self]
theorem t7_187checked : Checked tree [2,5,3,3,7,7,7] := by
  refine ⟨plan8504,valid8504,t7_187choices,?_⟩
  exact check_of_frontier tree 1 t7_187root t7_187jobs t7_187frontier t7_187all
theorem t7_188choices : plan8505.choices=[2,5,3,3,10,7,7].map (options 7 4) := by rfl


theorem t7_188part0 : t7_188jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_188part1 : t7_188jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_188frontier : t7_188root.frontier 1=t7_188jobs := by rfl
theorem t7_188all : t7_188jobs.all (Job.check tree)=true := by
  simp only [t7_188jobs,List.all_append,List.all_nil,t7_188part0,t7_188part1,Bool.and_self]
theorem t7_188checked : Checked tree [2,5,3,3,10,7,7] := by
  refine ⟨plan8505,valid8505,t7_188choices,?_⟩
  exact check_of_frontier tree 1 t7_188root t7_188jobs t7_188frontier t7_188all
theorem t7_189choices : plan8619.choices=[2,5,3,6,6,7,7].map (options 7 5) := by rfl


theorem t7_189part0 : t7_189jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_189frontier : t7_189root.frontier 0=t7_189jobs := by rfl
theorem t7_189all : t7_189jobs.all (Job.check tree)=true := by
  simp only [t7_189jobs,List.all_append,List.all_nil,t7_189part0,Bool.and_self]
theorem t7_189checked : Checked tree [2,5,3,6,6,7,7] := by
  refine ⟨plan8619,valid8619,t7_189choices,?_⟩
  exact check_of_frontier tree 0 t7_189root t7_189jobs t7_189frontier t7_189all
theorem t7_190choices : plan8620.choices=[2,5,3,6,7,7,7].map (options 7 5) := by rfl


theorem t7_190part0 : t7_190jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_190part1 : t7_190jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_190part2 : t7_190jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_190frontier : t7_190root.frontier 1=t7_190jobs := by rfl
theorem t7_190all : t7_190jobs.all (Job.check tree)=true := by
  simp only [t7_190jobs,List.all_append,List.all_nil,t7_190part0,t7_190part1,t7_190part2,Bool.and_self]
theorem t7_190checked : Checked tree [2,5,3,6,7,7,7] := by
  refine ⟨plan8620,valid8620,t7_190choices,?_⟩
  exact check_of_frontier tree 1 t7_190root t7_190jobs t7_190frontier t7_190all
theorem t7_191choices : plan8621.choices=[2,5,3,6,10,7,7].map (options 7 5) := by rfl


theorem t7_191part0 : t7_191jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_191frontier : t7_191root.frontier 0=t7_191jobs := by rfl
theorem t7_191all : t7_191jobs.all (Job.check tree)=true := by
  simp only [t7_191jobs,List.all_append,List.all_nil,t7_191part0,Bool.and_self]
theorem t7_191checked : Checked tree [2,5,3,6,10,7,7] := by
  refine ⟨plan8621,valid8621,t7_191choices,?_⟩
  exact check_of_frontier tree 0 t7_191root t7_191jobs t7_191frontier t7_191all
theorem t7_192choices : plan8622.choices=[2,5,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_192part0 : t7_192jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_192part1 : t7_192jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_192part2 : t7_192jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_192frontier : t7_192root.frontier 1=t7_192jobs := by rfl
theorem t7_192all : t7_192jobs.all (Job.check tree)=true := by
  simp only [t7_192jobs,List.all_append,List.all_nil,t7_192part0,t7_192part1,t7_192part2,Bool.and_self]
theorem t7_192checked : Checked tree [2,5,3,7,7,7,7] := by
  refine ⟨plan8622,valid8622,t7_192choices,?_⟩
  exact check_of_frontier tree 1 t7_192root t7_192jobs t7_192frontier t7_192all
theorem t7_193choices : plan8623.choices=[2,5,3,10,7,7,7].map (options 7 5) := by rfl


theorem t7_193part0 : t7_193jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_193part1 : t7_193jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_193part2 : t7_193jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_193frontier : t7_193root.frontier 1=t7_193jobs := by rfl
theorem t7_193all : t7_193jobs.all (Job.check tree)=true := by
  simp only [t7_193jobs,List.all_append,List.all_nil,t7_193part0,t7_193part1,t7_193part2,Bool.and_self]
theorem t7_193checked : Checked tree [2,5,3,10,7,7,7] := by
  refine ⟨plan8623,valid8623,t7_193choices,?_⟩
  exact check_of_frontier tree 1 t7_193root t7_193jobs t7_193frontier t7_193all
theorem t7_194choices : plan8624.choices=[2,5,3,10,10,7,7].map (options 7 5) := by rfl


theorem t7_194part0 : t7_194jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_194frontier : t7_194root.frontier 0=t7_194jobs := by rfl
theorem t7_194all : t7_194jobs.all (Job.check tree)=true := by
  simp only [t7_194jobs,List.all_append,List.all_nil,t7_194part0,Bool.and_self]
theorem t7_194checked : Checked tree [2,5,3,10,10,7,7] := by
  refine ⟨plan8624,valid8624,t7_194choices,?_⟩
  exact check_of_frontier tree 0 t7_194root t7_194jobs t7_194frontier t7_194all
theorem t7_195choices : plan8625.choices=[2,5,5,3,7,7,7].map (options 7 5) := by rfl


theorem t7_195part0 : t7_195jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_195frontier : t7_195root.frontier 0=t7_195jobs := by rfl
theorem t7_195all : t7_195jobs.all (Job.check tree)=true := by
  simp only [t7_195jobs,List.all_append,List.all_nil,t7_195part0,Bool.and_self]
theorem t7_195checked : Checked tree [2,5,5,3,7,7,7] := by
  refine ⟨plan8625,valid8625,t7_195choices,?_⟩
  exact check_of_frontier tree 0 t7_195root t7_195jobs t7_195frontier t7_195all
theorem t7_196choices : plan8762.choices=[2,5,5,6,7,7,7].map (options 7 6) := by rfl


theorem t7_196part0 : t7_196jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_196frontier : t7_196root.frontier 0=t7_196jobs := by rfl
theorem t7_196all : t7_196jobs.all (Job.check tree)=true := by
  simp only [t7_196jobs,List.all_append,List.all_nil,t7_196part0,Bool.and_self]
theorem t7_196checked : Checked tree [2,5,5,6,7,7,7] := by
  refine ⟨plan8762,valid8762,t7_196choices,?_⟩
  exact check_of_frontier tree 0 t7_196root t7_196jobs t7_196frontier t7_196all
theorem t7_197choices : plan8763.choices=[2,5,5,7,7,7,7].map (options 7 6) := by rfl


theorem t7_197part0 : t7_197jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_197frontier : t7_197root.frontier 0=t7_197jobs := by rfl
theorem t7_197all : t7_197jobs.all (Job.check tree)=true := by
  simp only [t7_197jobs,List.all_append,List.all_nil,t7_197part0,Bool.and_self]
theorem t7_197checked : Checked tree [2,5,5,7,7,7,7] := by
  refine ⟨plan8763,valid8763,t7_197choices,?_⟩
  exact check_of_frontier tree 0 t7_197root t7_197jobs t7_197frontier t7_197all
theorem t7_198choices : plan8764.choices=[2,5,5,10,7,7,7].map (options 7 6) := by rfl


theorem t7_198part0 : t7_198jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_198frontier : t7_198root.frontier 0=t7_198jobs := by rfl
theorem t7_198all : t7_198jobs.all (Job.check tree)=true := by
  simp only [t7_198jobs,List.all_append,List.all_nil,t7_198part0,Bool.and_self]
theorem t7_198checked : Checked tree [2,5,5,10,7,7,7] := by
  refine ⟨plan8764,valid8764,t7_198choices,?_⟩
  exact check_of_frontier tree 0 t7_198root t7_198jobs t7_198frontier t7_198all
theorem t7_199choices : plan8765.choices=[2,5,6,6,6,7,7].map (options 7 6) := by rfl


theorem t7_199part0 : t7_199jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_199frontier : t7_199root.frontier 0=t7_199jobs := by rfl
theorem t7_199all : t7_199jobs.all (Job.check tree)=true := by
  simp only [t7_199jobs,List.all_append,List.all_nil,t7_199part0,Bool.and_self]
theorem t7_199checked : Checked tree [2,5,6,6,6,7,7] := by
  refine ⟨plan8765,valid8765,t7_199choices,?_⟩
  exact check_of_frontier tree 0 t7_199root t7_199jobs t7_199frontier t7_199all
theorem t7_200choices : plan8766.choices=[2,5,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_200part0 : t7_200jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_200frontier : t7_200root.frontier 0=t7_200jobs := by rfl
theorem t7_200all : t7_200jobs.all (Job.check tree)=true := by
  simp only [t7_200jobs,List.all_append,List.all_nil,t7_200part0,Bool.and_self]
theorem t7_200checked : Checked tree [2,5,6,6,7,7,7] := by
  refine ⟨plan8766,valid8766,t7_200choices,?_⟩
  exact check_of_frontier tree 0 t7_200root t7_200jobs t7_200frontier t7_200all
theorem t7_201choices : plan8767.choices=[2,5,6,6,10,7,7].map (options 7 6) := by rfl


theorem t7_201part0 : t7_201jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_201frontier : t7_201root.frontier 0=t7_201jobs := by rfl
theorem t7_201all : t7_201jobs.all (Job.check tree)=true := by
  simp only [t7_201jobs,List.all_append,List.all_nil,t7_201part0,Bool.and_self]
theorem t7_201checked : Checked tree [2,5,6,6,10,7,7] := by
  refine ⟨plan8767,valid8767,t7_201choices,?_⟩
  exact check_of_frontier tree 0 t7_201root t7_201jobs t7_201frontier t7_201all
theorem t7_202choices : plan8768.choices=[2,5,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_202part0 : t7_202jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_202frontier : t7_202root.frontier 0=t7_202jobs := by rfl
theorem t7_202all : t7_202jobs.all (Job.check tree)=true := by
  simp only [t7_202jobs,List.all_append,List.all_nil,t7_202part0,Bool.and_self]
theorem t7_202checked : Checked tree [2,5,6,7,7,7,7] := by
  refine ⟨plan8768,valid8768,t7_202choices,?_⟩
  exact check_of_frontier tree 0 t7_202root t7_202jobs t7_202frontier t7_202all
theorem t7_203choices : plan8769.choices=[2,5,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_203part0 : t7_203jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_203frontier : t7_203root.frontier 0=t7_203jobs := by rfl
theorem t7_203all : t7_203jobs.all (Job.check tree)=true := by
  simp only [t7_203jobs,List.all_append,List.all_nil,t7_203part0,Bool.and_self]
theorem t7_203checked : Checked tree [2,5,6,10,7,7,7] := by
  refine ⟨plan8769,valid8769,t7_203choices,?_⟩
  exact check_of_frontier tree 0 t7_203root t7_203jobs t7_203frontier t7_203all
theorem t7_204choices : plan8770.choices=[2,5,6,10,10,7,7].map (options 7 6) := by rfl


theorem t7_204part0 : t7_204jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_204frontier : t7_204root.frontier 0=t7_204jobs := by rfl
theorem t7_204all : t7_204jobs.all (Job.check tree)=true := by
  simp only [t7_204jobs,List.all_append,List.all_nil,t7_204part0,Bool.and_self]
theorem t7_204checked : Checked tree [2,5,6,10,10,7,7] := by
  refine ⟨plan8770,valid8770,t7_204choices,?_⟩
  exact check_of_frontier tree 0 t7_204root t7_204jobs t7_204frontier t7_204all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks166 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_196checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_197checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_198checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_199checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_200checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_201checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_202checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_203checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_187checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_204checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_188checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_189checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_190checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_191checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_192checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_193checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_194checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_195checked⟩
