-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks168
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T04:05:27.420637+00:00
-- url     : https://prove2.me/submissions/7e413ef6-22d2-4b43-a836-23dfbe6f0d8e

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks168
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks168
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











































theorem valid6191 : plan6191.Valid := valid_step _ _ _ valid3604 (by decide +kernel)











































theorem valid6213 : plan6213.Valid := valid_step _ _ _ valid3625 (by decide +kernel)





theorem valid6216 : plan6216.Valid := valid_step _ _ _ valid3628 (by decide +kernel)

theorem valid6217 : plan6217.Valid := valid_step _ _ _ valid3629 (by decide +kernel)





theorem valid6220 : plan6220.Valid := valid_step _ _ _ valid3632 (by decide +kernel)

theorem valid6221 : plan6221.Valid := valid_step _ _ _ valid3633 (by decide +kernel)

theorem valid6222 : plan6222.Valid := valid_step _ _ _ valid3634 (by decide +kernel)





theorem valid6225 : plan6225.Valid := valid_step _ _ _ valid3632 (by decide +kernel)



theorem valid6227 : plan6227.Valid := valid_step _ _ _ valid3628 (by decide +kernel)


























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





























































































































































theorem valid8143 : plan8143.Valid := valid_step _ _ _ valid6137 (by decide +kernel)

theorem valid8144 : plan8144.Valid := valid_step _ _ _ valid6138 (by decide +kernel)
































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





















































































































theorem valid8507 : plan8507.Valid := valid_step _ _ _ valid8143 (by decide +kernel)

theorem valid8508 : plan8508.Valid := valid_step _ _ _ valid8144 (by decide +kernel)








































































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













































































































theorem valid8215 : plan8215.Valid := valid_step _ _ _ valid6162 (by decide +kernel)

theorem valid8216 : plan8216.Valid := valid_step _ _ _ valid6164 (by decide +kernel)

theorem valid8217 : plan8217.Valid := valid_step _ _ _ valid6165 (by decide +kernel)

theorem valid8218 : plan8218.Valid := valid_step _ _ _ valid6167 (by decide +kernel)

theorem valid8219 : plan8219.Valid := valid_step _ _ _ valid6168 (by decide +kernel)

theorem valid8220 : plan8220.Valid := valid_step _ _ _ valid6169 (by decide +kernel)

theorem valid8221 : plan8221.Valid := valid_step _ _ _ valid6191 (by decide +kernel)






































































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





































































































































































theorem valid8627 : plan8627.Valid := valid_step _ _ _ valid8215 (by decide +kernel)

theorem valid8628 : plan8628.Valid := valid_step _ _ _ valid8216 (by decide +kernel)

theorem valid8629 : plan8629.Valid := valid_step _ _ _ valid8217 (by decide +kernel)

theorem valid8630 : plan8630.Valid := valid_step _ _ _ valid8218 (by decide +kernel)

theorem valid8631 : plan8631.Valid := valid_step _ _ _ valid8219 (by decide +kernel)

theorem valid8632 : plan8632.Valid := valid_step _ _ _ valid8220 (by decide +kernel)

theorem valid8633 : plan8633.Valid := valid_step _ _ _ valid8221 (by decide +kernel)














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

































































































theorem valid8305 : plan8305.Valid := valid_step _ _ _ valid6213 (by decide +kernel)

theorem valid8306 : plan8306.Valid := valid_step _ _ _ valid6216 (by decide +kernel)

theorem valid8307 : plan8307.Valid := valid_step _ _ _ valid6217 (by decide +kernel)

theorem valid8308 : plan8308.Valid := valid_step _ _ _ valid6220 (by decide +kernel)

theorem valid8309 : plan8309.Valid := valid_step _ _ _ valid6221 (by decide +kernel)

theorem valid8310 : plan8310.Valid := valid_step _ _ _ valid6222 (by decide +kernel)

theorem valid8311 : plan8311.Valid := valid_step _ _ _ valid6225 (by decide +kernel)



theorem valid8313 : plan8313.Valid := valid_step _ _ _ valid6227 (by decide +kernel)














































































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



















































































































theorem valid8794 : plan8794.Valid := valid_step _ _ _ valid8305 (by decide +kernel)

theorem valid8795 : plan8795.Valid := valid_step _ _ _ valid8306 (by decide +kernel)

theorem valid8796 : plan8796.Valid := valid_step _ _ _ valid8307 (by decide +kernel)

theorem valid8797 : plan8797.Valid := valid_step _ _ _ valid8308 (by decide +kernel)

theorem valid8798 : plan8798.Valid := valid_step _ _ _ valid8309 (by decide +kernel)

theorem valid8799 : plan8799.Valid := valid_step _ _ _ valid8310 (by decide +kernel)

theorem valid8800 : plan8800.Valid := valid_step _ _ _ valid8311 (by decide +kernel)

theorem valid8801 : plan8801.Valid := valid_step _ _ _ valid8313 (by decide +kernel)






























































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
theorem t7_231choices : plan8507.choices=[2,9,3,3,7,7,7].map (options 7 4) := by rfl


theorem t7_231part0 : t7_231jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_231part1 : t7_231jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_231part2 : t7_231jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_231frontier : t7_231root.frontier 1=t7_231jobs := by rfl
theorem t7_231all : t7_231jobs.all (Job.check tree)=true := by
  simp only [t7_231jobs,List.all_append,List.all_nil,t7_231part0,t7_231part1,t7_231part2,Bool.and_self]
theorem t7_231checked : Checked tree [2,9,3,3,7,7,7] := by
  refine ⟨plan8507,valid8507,t7_231choices,?_⟩
  exact check_of_frontier tree 1 t7_231root t7_231jobs t7_231frontier t7_231all
theorem t7_232choices : plan8508.choices=[2,9,3,3,10,7,7].map (options 7 4) := by rfl


theorem t7_232part0 : t7_232jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_232part1 : t7_232jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_232frontier : t7_232root.frontier 1=t7_232jobs := by rfl
theorem t7_232all : t7_232jobs.all (Job.check tree)=true := by
  simp only [t7_232jobs,List.all_append,List.all_nil,t7_232part0,t7_232part1,Bool.and_self]
theorem t7_232checked : Checked tree [2,9,3,3,10,7,7] := by
  refine ⟨plan8508,valid8508,t7_232choices,?_⟩
  exact check_of_frontier tree 1 t7_232root t7_232jobs t7_232frontier t7_232all
theorem t7_233choices : plan8627.choices=[2,9,3,6,6,7,7].map (options 7 5) := by rfl


theorem t7_233part0 : t7_233jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_233frontier : t7_233root.frontier 0=t7_233jobs := by rfl
theorem t7_233all : t7_233jobs.all (Job.check tree)=true := by
  simp only [t7_233jobs,List.all_append,List.all_nil,t7_233part0,Bool.and_self]
theorem t7_233checked : Checked tree [2,9,3,6,6,7,7] := by
  refine ⟨plan8627,valid8627,t7_233choices,?_⟩
  exact check_of_frontier tree 0 t7_233root t7_233jobs t7_233frontier t7_233all
theorem t7_234choices : plan8628.choices=[2,9,3,6,7,7,7].map (options 7 5) := by rfl


theorem t7_234part0 : t7_234jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_234part1 : t7_234jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_234part2 : t7_234jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_234frontier : t7_234root.frontier 1=t7_234jobs := by rfl
theorem t7_234all : t7_234jobs.all (Job.check tree)=true := by
  simp only [t7_234jobs,List.all_append,List.all_nil,t7_234part0,t7_234part1,t7_234part2,Bool.and_self]
theorem t7_234checked : Checked tree [2,9,3,6,7,7,7] := by
  refine ⟨plan8628,valid8628,t7_234choices,?_⟩
  exact check_of_frontier tree 1 t7_234root t7_234jobs t7_234frontier t7_234all
theorem t7_235choices : plan8629.choices=[2,9,3,6,10,7,7].map (options 7 5) := by rfl


theorem t7_235part0 : t7_235jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_235frontier : t7_235root.frontier 0=t7_235jobs := by rfl
theorem t7_235all : t7_235jobs.all (Job.check tree)=true := by
  simp only [t7_235jobs,List.all_append,List.all_nil,t7_235part0,Bool.and_self]
theorem t7_235checked : Checked tree [2,9,3,6,10,7,7] := by
  refine ⟨plan8629,valid8629,t7_235choices,?_⟩
  exact check_of_frontier tree 0 t7_235root t7_235jobs t7_235frontier t7_235all
theorem t7_236choices : plan8630.choices=[2,9,3,7,7,7,7].map (options 7 5) := by rfl


theorem t7_236part0 : t7_236jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_236part1 : t7_236jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_236part2 : t7_236jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_236frontier : t7_236root.frontier 1=t7_236jobs := by rfl
theorem t7_236all : t7_236jobs.all (Job.check tree)=true := by
  simp only [t7_236jobs,List.all_append,List.all_nil,t7_236part0,t7_236part1,t7_236part2,Bool.and_self]
theorem t7_236checked : Checked tree [2,9,3,7,7,7,7] := by
  refine ⟨plan8630,valid8630,t7_236choices,?_⟩
  exact check_of_frontier tree 1 t7_236root t7_236jobs t7_236frontier t7_236all
theorem t7_237choices : plan8631.choices=[2,9,3,10,7,7,7].map (options 7 5) := by rfl


theorem t7_237part0 : t7_237jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_237part1 : t7_237jobs1.all (Job.check tree)=true := by decide +kernel

theorem t7_237part2 : t7_237jobs2.all (Job.check tree)=true := by decide +kernel

theorem t7_237frontier : t7_237root.frontier 1=t7_237jobs := by rfl
theorem t7_237all : t7_237jobs.all (Job.check tree)=true := by
  simp only [t7_237jobs,List.all_append,List.all_nil,t7_237part0,t7_237part1,t7_237part2,Bool.and_self]
theorem t7_237checked : Checked tree [2,9,3,10,7,7,7] := by
  refine ⟨plan8631,valid8631,t7_237choices,?_⟩
  exact check_of_frontier tree 1 t7_237root t7_237jobs t7_237frontier t7_237all
theorem t7_238choices : plan8632.choices=[2,9,3,10,10,7,7].map (options 7 5) := by rfl


theorem t7_238part0 : t7_238jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_238frontier : t7_238root.frontier 0=t7_238jobs := by rfl
theorem t7_238all : t7_238jobs.all (Job.check tree)=true := by
  simp only [t7_238jobs,List.all_append,List.all_nil,t7_238part0,Bool.and_self]
theorem t7_238checked : Checked tree [2,9,3,10,10,7,7] := by
  refine ⟨plan8632,valid8632,t7_238choices,?_⟩
  exact check_of_frontier tree 0 t7_238root t7_238jobs t7_238frontier t7_238all
theorem t7_239choices : plan8794.choices=[2,9,6,6,6,7,7].map (options 7 6) := by rfl


theorem t7_239part0 : t7_239jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_239frontier : t7_239root.frontier 0=t7_239jobs := by rfl
theorem t7_239all : t7_239jobs.all (Job.check tree)=true := by
  simp only [t7_239jobs,List.all_append,List.all_nil,t7_239part0,Bool.and_self]
theorem t7_239checked : Checked tree [2,9,6,6,6,7,7] := by
  refine ⟨plan8794,valid8794,t7_239choices,?_⟩
  exact check_of_frontier tree 0 t7_239root t7_239jobs t7_239frontier t7_239all
theorem t7_240choices : plan8795.choices=[2,9,6,6,7,7,7].map (options 7 6) := by rfl


theorem t7_240part0 : t7_240jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_240frontier : t7_240root.frontier 0=t7_240jobs := by rfl
theorem t7_240all : t7_240jobs.all (Job.check tree)=true := by
  simp only [t7_240jobs,List.all_append,List.all_nil,t7_240part0,Bool.and_self]
theorem t7_240checked : Checked tree [2,9,6,6,7,7,7] := by
  refine ⟨plan8795,valid8795,t7_240choices,?_⟩
  exact check_of_frontier tree 0 t7_240root t7_240jobs t7_240frontier t7_240all
theorem t7_241choices : plan8796.choices=[2,9,6,6,10,7,7].map (options 7 6) := by rfl


theorem t7_241part0 : t7_241jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_241frontier : t7_241root.frontier 0=t7_241jobs := by rfl
theorem t7_241all : t7_241jobs.all (Job.check tree)=true := by
  simp only [t7_241jobs,List.all_append,List.all_nil,t7_241part0,Bool.and_self]
theorem t7_241checked : Checked tree [2,9,6,6,10,7,7] := by
  refine ⟨plan8796,valid8796,t7_241choices,?_⟩
  exact check_of_frontier tree 0 t7_241root t7_241jobs t7_241frontier t7_241all
theorem t7_242choices : plan8797.choices=[2,9,6,7,7,7,7].map (options 7 6) := by rfl


theorem t7_242part0 : t7_242jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_242frontier : t7_242root.frontier 0=t7_242jobs := by rfl
theorem t7_242all : t7_242jobs.all (Job.check tree)=true := by
  simp only [t7_242jobs,List.all_append,List.all_nil,t7_242part0,Bool.and_self]
theorem t7_242checked : Checked tree [2,9,6,7,7,7,7] := by
  refine ⟨plan8797,valid8797,t7_242choices,?_⟩
  exact check_of_frontier tree 0 t7_242root t7_242jobs t7_242frontier t7_242all
theorem t7_243choices : plan8798.choices=[2,9,6,10,7,7,7].map (options 7 6) := by rfl


theorem t7_243part0 : t7_243jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_243frontier : t7_243root.frontier 0=t7_243jobs := by rfl
theorem t7_243all : t7_243jobs.all (Job.check tree)=true := by
  simp only [t7_243jobs,List.all_append,List.all_nil,t7_243part0,Bool.and_self]
theorem t7_243checked : Checked tree [2,9,6,10,7,7,7] := by
  refine ⟨plan8798,valid8798,t7_243choices,?_⟩
  exact check_of_frontier tree 0 t7_243root t7_243jobs t7_243frontier t7_243all
theorem t7_244choices : plan8799.choices=[2,9,6,10,10,7,7].map (options 7 6) := by rfl


theorem t7_244part0 : t7_244jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_244frontier : t7_244root.frontier 0=t7_244jobs := by rfl
theorem t7_244all : t7_244jobs.all (Job.check tree)=true := by
  simp only [t7_244jobs,List.all_append,List.all_nil,t7_244part0,Bool.and_self]
theorem t7_244checked : Checked tree [2,9,6,10,10,7,7] := by
  refine ⟨plan8799,valid8799,t7_244choices,?_⟩
  exact check_of_frontier tree 0 t7_244root t7_244jobs t7_244frontier t7_244all
theorem t7_245choices : plan8800.choices=[2,9,7,7,7,7,7].map (options 7 6) := by rfl


theorem t7_245part0 : t7_245jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_245frontier : t7_245root.frontier 0=t7_245jobs := by rfl
theorem t7_245all : t7_245jobs.all (Job.check tree)=true := by
  simp only [t7_245jobs,List.all_append,List.all_nil,t7_245part0,Bool.and_self]
theorem t7_245checked : Checked tree [2,9,7,7,7,7,7] := by
  refine ⟨plan8800,valid8800,t7_245choices,?_⟩
  exact check_of_frontier tree 0 t7_245root t7_245jobs t7_245frontier t7_245all
theorem t7_246choices : plan8633.choices=[2,9,9,3,7,7,7].map (options 7 5) := by rfl


theorem t7_246part0 : t7_246jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_246frontier : t7_246root.frontier 0=t7_246jobs := by rfl
theorem t7_246all : t7_246jobs.all (Job.check tree)=true := by
  simp only [t7_246jobs,List.all_append,List.all_nil,t7_246part0,Bool.and_self]
theorem t7_246checked : Checked tree [2,9,9,3,7,7,7] := by
  refine ⟨plan8633,valid8633,t7_246choices,?_⟩
  exact check_of_frontier tree 0 t7_246root t7_246jobs t7_246frontier t7_246all
theorem t7_247choices : plan8801.choices=[2,9,9,6,7,7,7].map (options 7 6) := by rfl


theorem t7_247part0 : t7_247jobs0.all (Job.check tree)=true := by decide +kernel

theorem t7_247frontier : t7_247root.frontier 0=t7_247jobs := by rfl
theorem t7_247all : t7_247jobs.all (Job.check tree)=true := by
  simp only [t7_247jobs,List.all_append,List.all_nil,t7_247part0,Bool.and_self]
theorem t7_247checked : Checked tree [2,9,9,6,7,7,7] := by
  refine ⟨plan8801,valid8801,t7_247choices,?_⟩
  exact check_of_frontier tree 0 t7_247root t7_247jobs t7_247frontier t7_247all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks168 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_240checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_241checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_242checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_243checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_244checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_245checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_246checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_247checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_231checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_232checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_233checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_234checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_235checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_236checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_237checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_238checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t7_239checked⟩
