-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks082
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:20:30.283997+00:00
-- url     : https://prove2.me/submissions/410499be-8902-411e-bc0c-ceeb1f044a25

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks082
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks082
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans059
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans068
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans072
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































































theorem valid128 : plan128.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid129 : plan129.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid130 : plan130.Valid := valid_step _ _ _ valid0 (by decide +kernel)




























































































































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



































































































































































theorem valid562 : plan562.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid563 : plan563.Valid := valid_step _ _ _ valid128 (by decide +kernel)

theorem valid564 : plan564.Valid := valid_step _ _ _ valid129 (by decide +kernel)







theorem valid568 : plan568.Valid := valid_step _ _ _ valid130 (by decide +kernel)
















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

theorem valid1537 : plan1537.Valid := valid_step _ _ _ valid564 (by decide +kernel)































































theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)






























































































































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

























































































theorem valid3309 : plan3309.Valid := valid_step _ _ _ valid1535 (by decide +kernel)

theorem valid3310 : plan3310.Valid := valid_step _ _ _ valid1536 (by decide +kernel)

theorem valid3311 : plan3311.Valid := valid_step _ _ _ valid1537 (by decide +kernel)

































































































theorem valid3360 : plan3360.Valid := valid_step _ _ _ valid1569 (by decide +kernel)
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





































































theorem valid5507 : plan5507.Valid := valid_step _ _ _ valid3309 (by decide +kernel)

theorem valid5508 : plan5508.Valid := valid_step _ _ _ valid3310 (by decide +kernel)

theorem valid5509 : plan5509.Valid := valid_step _ _ _ valid3311 (by decide +kernel)






















































































































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







theorem valid5668 : plan5668.Valid := valid_step _ _ _ valid3360 (by decide +kernel)
























































































































































































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



























































































































theorem valid6590 : plan6590.Valid := valid_step _ _ _ valid5507 (by decide +kernel)

theorem valid6591 : plan6591.Valid := valid_step _ _ _ valid5508 (by decide +kernel)

theorem valid6592 : plan6592.Valid := valid_step _ _ _ valid5509 (by decide +kernel)
































































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

































theorem valid6929 : plan6929.Valid := valid_step _ _ _ valid5668 (by decide +kernel)






























































































































































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
theorem t6_673choices : plan6590.choices=[2,5,3,3,7,7].map (options 6 3) := by rfl


theorem t6_673part0 : t6_673jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_673part1 : t6_673jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_673part2 : t6_673jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_673part3 : t6_673jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_673part4 : t6_673jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_673part5 : t6_673jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_673part6 : t6_673jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_673frontier : t6_673root.frontier 2=t6_673jobs := by rfl
theorem t6_673all : t6_673jobs.all (Job.check tree)=true := by
  simp only [t6_673jobs,List.all_append,List.all_nil,t6_673part0,t6_673part1,t6_673part2,t6_673part3,t6_673part4,t6_673part5,t6_673part6,Bool.and_self]
theorem t6_673checked : Checked tree [2,5,3,3,7,7] := by
  refine ⟨plan6590,valid6590,t6_673choices,?_⟩
  exact check_of_frontier tree 2 t6_673root t6_673jobs t6_673frontier t6_673all
theorem t6_674choices : plan6591.choices=[2,5,3,3,10,7].map (options 6 3) := by rfl


theorem t6_674part0 : t6_674jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_674part1 : t6_674jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_674part2 : t6_674jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_674part3 : t6_674jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_674part4 : t6_674jobs4.all (Job.check tree)=true := by decide +kernel

theorem t6_674part5 : t6_674jobs5.all (Job.check tree)=true := by decide +kernel

theorem t6_674part6 : t6_674jobs6.all (Job.check tree)=true := by decide +kernel

theorem t6_674frontier : t6_674root.frontier 2=t6_674jobs := by rfl
theorem t6_674all : t6_674jobs.all (Job.check tree)=true := by
  simp only [t6_674jobs,List.all_append,List.all_nil,t6_674part0,t6_674part1,t6_674part2,t6_674part3,t6_674part4,t6_674part5,t6_674part6,Bool.and_self]
theorem t6_674checked : Checked tree [2,5,3,3,10,7] := by
  refine ⟨plan6591,valid6591,t6_674choices,?_⟩
  exact check_of_frontier tree 2 t6_674root t6_674jobs t6_674frontier t6_674all
theorem t6_675choices : plan6592.choices=[2,5,3,3,10,10].map (options 6 3) := by rfl


theorem t6_675part0 : t6_675jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_675part1 : t6_675jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_675frontier : t6_675root.frontier 1=t6_675jobs := by rfl
theorem t6_675all : t6_675jobs.all (Job.check tree)=true := by
  simp only [t6_675jobs,List.all_append,List.all_nil,t6_675part0,t6_675part1,Bool.and_self]
theorem t6_675checked : Checked tree [2,5,3,3,10,10] := by
  refine ⟨plan6592,valid6592,t6_675choices,?_⟩
  exact check_of_frontier tree 1 t6_675root t6_675jobs t6_675frontier t6_675all
theorem t6_676choices : plan6929.choices=[2,5,3,6,6,6].map (options 6 4) := by rfl


theorem t6_676part0 : t6_676jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_676frontier : t6_676root.frontier 0=t6_676jobs := by rfl
theorem t6_676all : t6_676jobs.all (Job.check tree)=true := by
  simp only [t6_676jobs,List.all_append,List.all_nil,t6_676part0,Bool.and_self]
theorem t6_676checked : Checked tree [2,5,3,6,6,6] := by
  refine ⟨plan6929,valid6929,t6_676choices,?_⟩
  exact check_of_frontier tree 0 t6_676root t6_676jobs t6_676frontier t6_676all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks082 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_676checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_673checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_674checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_675checked⟩
