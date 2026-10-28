-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks053
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:05:17.783237+00:00
-- url     : https://prove2.me/submissions/624367b1-71dc-4027-a22c-07a8276a6267

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks053
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks053
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans035
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans057
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans058
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans067
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans070
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

theorem valid131 : plan131.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid132 : plan132.Valid := valid_step _ _ _ valid0 (by decide +kernel)
























































































































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

theorem valid569 : plan569.Valid := valid_step _ _ _ valid131 (by decide +kernel)

theorem valid570 : plan570.Valid := valid_step _ _ _ valid132 (by decide +kernel)












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



















theorem valid1546 : plan1546.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1547 : plan1547.Valid := valid_step _ _ _ valid564 (by decide +kernel)

theorem valid1548 : plan1548.Valid := valid_step _ _ _ valid562 (by decide +kernel)









theorem valid1553 : plan1553.Valid := valid_step _ _ _ valid562 (by decide +kernel)

theorem valid1554 : plan1554.Valid := valid_step _ _ _ valid563 (by decide +kernel)

theorem valid1555 : plan1555.Valid := valid_step _ _ _ valid564 (by decide +kernel)



























theorem valid1569 : plan1569.Valid := valid_step _ _ _ valid568 (by decide +kernel)

theorem valid1570 : plan1570.Valid := valid_step _ _ _ valid569 (by decide +kernel)

theorem valid1571 : plan1571.Valid := valid_step _ _ _ valid570 (by decide +kernel)


























































































































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







































































































theorem valid3316 : plan3316.Valid := valid_step _ _ _ valid1546 (by decide +kernel)

theorem valid3317 : plan3317.Valid := valid_step _ _ _ valid1547 (by decide +kernel)

theorem valid3318 : plan3318.Valid := valid_step _ _ _ valid1548 (by decide +kernel)

theorem valid3319 : plan3319.Valid := valid_step _ _ _ valid1553 (by decide +kernel)

theorem valid3320 : plan3320.Valid := valid_step _ _ _ valid1554 (by decide +kernel)

theorem valid3321 : plan3321.Valid := valid_step _ _ _ valid1555 (by decide +kernel)














































































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











































































theorem valid3398 : plan3398.Valid := valid_step _ _ _ valid1569 (by decide +kernel)

theorem valid3399 : plan3399.Valid := valid_step _ _ _ valid1570 (by decide +kernel)

theorem valid3400 : plan3400.Valid := valid_step _ _ _ valid1571 (by decide +kernel)
















































































































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



































theorem valid5490 : plan5490.Valid := valid_step _ _ _ valid3316 (by decide +kernel)

theorem valid5491 : plan5491.Valid := valid_step _ _ _ valid3317 (by decide +kernel)

theorem valid5492 : plan5492.Valid := valid_step _ _ _ valid3318 (by decide +kernel)

theorem valid5493 : plan5493.Valid := valid_step _ _ _ valid3319 (by decide +kernel)

theorem valid5494 : plan5494.Valid := valid_step _ _ _ valid3320 (by decide +kernel)

theorem valid5495 : plan5495.Valid := valid_step _ _ _ valid3321 (by decide +kernel)


















































































































































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





















































































































































theorem valid6507 : plan6507.Valid := valid_step _ _ _ valid5490 (by decide +kernel)

theorem valid6508 : plan6508.Valid := valid_step _ _ _ valid5491 (by decide +kernel)

theorem valid6509 : plan6509.Valid := valid_step _ _ _ valid5492 (by decide +kernel)

theorem valid6510 : plan6510.Valid := valid_step _ _ _ valid5493 (by decide +kernel)

theorem valid6511 : plan6511.Valid := valid_step _ _ _ valid5494 (by decide +kernel)

theorem valid6512 : plan6512.Valid := valid_step _ _ _ valid5495 (by decide +kernel)
































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































































































































theorem valid5632 : plan5632.Valid := valid_step _ _ _ valid3398 (by decide +kernel)

theorem valid5633 : plan5633.Valid := valid_step _ _ _ valid3399 (by decide +kernel)

theorem valid5634 : plan5634.Valid := valid_step _ _ _ valid3400 (by decide +kernel)




























































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







































































































































































theorem valid6804 : plan6804.Valid := valid_step _ _ _ valid5632 (by decide +kernel)

theorem valid6805 : plan6805.Valid := valid_step _ _ _ valid5633 (by decide +kernel)

theorem valid6806 : plan6806.Valid := valid_step _ _ _ valid5634 (by decide +kernel)




















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
theorem t6_299choices : plan6507.choices=[1,3,3,6,10,7].map (options 6 3) := by rfl


theorem t6_299part0 : t6_299jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_299part1 : t6_299jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_299part2 : t6_299jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_299part3 : t6_299jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_299frontier : t6_299root.frontier 2=t6_299jobs := by rfl
theorem t6_299all : t6_299jobs.all (Job.check tree)=true := by
  simp only [t6_299jobs,List.all_append,List.all_nil,t6_299part0,t6_299part1,t6_299part2,t6_299part3,Bool.and_self]
theorem t6_299checked : Checked tree [1,3,3,6,10,7] := by
  refine ⟨plan6507,valid6507,t6_299choices,?_⟩
  exact check_of_frontier tree 2 t6_299root t6_299jobs t6_299frontier t6_299all
theorem t6_300choices : plan6508.choices=[1,3,3,6,10,10].map (options 6 3) := by rfl


theorem t6_300part0 : t6_300jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_300frontier : t6_300root.frontier 0=t6_300jobs := by rfl
theorem t6_300all : t6_300jobs.all (Job.check tree)=true := by
  simp only [t6_300jobs,List.all_append,List.all_nil,t6_300part0,Bool.and_self]
theorem t6_300checked : Checked tree [1,3,3,6,10,10] := by
  refine ⟨plan6508,valid6508,t6_300choices,?_⟩
  exact check_of_frontier tree 0 t6_300root t6_300jobs t6_300frontier t6_300all
theorem t6_301choices : plan6509.choices=[1,3,3,7,7,7].map (options 6 3) := by rfl


theorem t6_301part0 : t6_301jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_301part1 : t6_301jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_301part2 : t6_301jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_301frontier : t6_301root.frontier 2=t6_301jobs := by rfl
theorem t6_301all : t6_301jobs.all (Job.check tree)=true := by
  simp only [t6_301jobs,List.all_append,List.all_nil,t6_301part0,t6_301part1,t6_301part2,Bool.and_self]
theorem t6_301checked : Checked tree [1,3,3,7,7,7] := by
  refine ⟨plan6509,valid6509,t6_301choices,?_⟩
  exact check_of_frontier tree 2 t6_301root t6_301jobs t6_301frontier t6_301all
theorem t6_302choices : plan6510.choices=[1,3,3,10,7,7].map (options 6 3) := by rfl


theorem t6_302part0 : t6_302jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_302part1 : t6_302jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_302part2 : t6_302jobs2.all (Job.check tree)=true := by decide +kernel

theorem t6_302part3 : t6_302jobs3.all (Job.check tree)=true := by decide +kernel

theorem t6_302frontier : t6_302root.frontier 2=t6_302jobs := by rfl
theorem t6_302all : t6_302jobs.all (Job.check tree)=true := by
  simp only [t6_302jobs,List.all_append,List.all_nil,t6_302part0,t6_302part1,t6_302part2,t6_302part3,Bool.and_self]
theorem t6_302checked : Checked tree [1,3,3,10,7,7] := by
  refine ⟨plan6510,valid6510,t6_302choices,?_⟩
  exact check_of_frontier tree 2 t6_302root t6_302jobs t6_302frontier t6_302all
theorem t6_303choices : plan6511.choices=[1,3,3,10,10,7].map (options 6 3) := by rfl


theorem t6_303part0 : t6_303jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_303part1 : t6_303jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_303frontier : t6_303root.frontier 2=t6_303jobs := by rfl
theorem t6_303all : t6_303jobs.all (Job.check tree)=true := by
  simp only [t6_303jobs,List.all_append,List.all_nil,t6_303part0,t6_303part1,Bool.and_self]
theorem t6_303checked : Checked tree [1,3,3,10,10,7] := by
  refine ⟨plan6511,valid6511,t6_303choices,?_⟩
  exact check_of_frontier tree 2 t6_303root t6_303jobs t6_303frontier t6_303all
theorem t6_304choices : plan6512.choices=[1,3,3,10,10,10].map (options 6 3) := by rfl


theorem t6_304part0 : t6_304jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_304frontier : t6_304root.frontier 0=t6_304jobs := by rfl
theorem t6_304all : t6_304jobs.all (Job.check tree)=true := by
  simp only [t6_304jobs,List.all_append,List.all_nil,t6_304part0,Bool.and_self]
theorem t6_304checked : Checked tree [1,3,3,10,10,10] := by
  refine ⟨plan6512,valid6512,t6_304choices,?_⟩
  exact check_of_frontier tree 0 t6_304root t6_304jobs t6_304frontier t6_304all
theorem t6_305choices : plan6804.choices=[1,3,6,6,6,6].map (options 6 4) := by rfl


theorem t6_305part0 : t6_305jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_305frontier : t6_305root.frontier 0=t6_305jobs := by rfl
theorem t6_305all : t6_305jobs.all (Job.check tree)=true := by
  simp only [t6_305jobs,List.all_append,List.all_nil,t6_305part0,Bool.and_self]
theorem t6_305checked : Checked tree [1,3,6,6,6,6] := by
  refine ⟨plan6804,valid6804,t6_305choices,?_⟩
  exact check_of_frontier tree 0 t6_305root t6_305jobs t6_305frontier t6_305all
theorem t6_306choices : plan6805.choices=[1,3,6,6,6,7].map (options 6 4) := by rfl


theorem t6_306part0 : t6_306jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_306part1 : t6_306jobs1.all (Job.check tree)=true := by decide +kernel

theorem t6_306frontier : t6_306root.frontier 1=t6_306jobs := by rfl
theorem t6_306all : t6_306jobs.all (Job.check tree)=true := by
  simp only [t6_306jobs,List.all_append,List.all_nil,t6_306part0,t6_306part1,Bool.and_self]
theorem t6_306checked : Checked tree [1,3,6,6,6,7] := by
  refine ⟨plan6805,valid6805,t6_306choices,?_⟩
  exact check_of_frontier tree 1 t6_306root t6_306jobs t6_306frontier t6_306all
theorem t6_307choices : plan6806.choices=[1,3,6,6,6,10].map (options 6 4) := by rfl


theorem t6_307part0 : t6_307jobs0.all (Job.check tree)=true := by decide +kernel

theorem t6_307frontier : t6_307root.frontier 0=t6_307jobs := by rfl
theorem t6_307all : t6_307jobs.all (Job.check tree)=true := by
  simp only [t6_307jobs,List.all_append,List.all_nil,t6_307part0,Bool.and_self]
theorem t6_307checked : Checked tree [1,3,6,6,6,10] := by
  refine ⟨plan6806,valid6806,t6_307choices,?_⟩
  exact check_of_frontier tree 0 t6_307root t6_307jobs t6_307frontier t6_307all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks053 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_302checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_303checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_304checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_305checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_306checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_307checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_299checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_300checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t6_301checked⟩
