-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks045
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:09:46.979621+00:00
-- url     : https://prove2.me/submissions/88ffb797-112c-4c0a-af20-6b69b7d3ea96

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks045
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans051
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













theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid105 : plan105.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid108 : plan108.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid109 : plan109.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid111 : plan111.Valid := valid_step _ _ _ valid0 (by decide +kernel)


































































































































































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































theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)











theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)



















theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)






















































































































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

























































































































































































theorem valid1341 : plan1341.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1342 : plan1342.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1343 : plan1343.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1344 : plan1344.Valid := valid_step _ _ _ valid504 (by decide +kernel)
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

























































































































































































theorem valid1437 : plan1437.Valid := valid_step _ _ _ valid514 (by decide +kernel)

theorem valid1438 : plan1438.Valid := valid_step _ _ _ valid515 (by decide +kernel)

theorem valid1439 : plan1439.Valid := valid_step _ _ _ valid516 (by decide +kernel)

theorem valid1440 : plan1440.Valid := valid_step _ _ _ valid517 (by decide +kernel)
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























































































































































theorem valid2764 : plan2764.Valid := valid_step _ _ _ valid1341 (by decide +kernel)

theorem valid2765 : plan2765.Valid := valid_step _ _ _ valid1342 (by decide +kernel)

theorem valid2766 : plan2766.Valid := valid_step _ _ _ valid1343 (by decide +kernel)

theorem valid2767 : plan2767.Valid := valid_step _ _ _ valid1344 (by decide +kernel)


































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















































theorem valid2904 : plan2904.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid2905 : plan2905.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid2906 : plan2906.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid2907 : plan2907.Valid := valid_step _ _ _ valid1440 (by decide +kernel)










































































































































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



















































theorem valid4442 : plan4442.Valid := valid_step _ _ _ valid2764 (by decide +kernel)

theorem valid4443 : plan4443.Valid := valid_step _ _ _ valid2765 (by decide +kernel)

theorem valid4444 : plan4444.Valid := valid_step _ _ _ valid2766 (by decide +kernel)

theorem valid4445 : plan4445.Valid := valid_step _ _ _ valid2767 (by decide +kernel)






































































































































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





































































































































































theorem valid4979 : plan4979.Valid := valid_step _ _ _ valid2904 (by decide +kernel)

theorem valid4980 : plan4980.Valid := valid_step _ _ _ valid2905 (by decide +kernel)

theorem valid4981 : plan4981.Valid := valid_step _ _ _ valid2906 (by decide +kernel)

theorem valid4982 : plan4982.Valid := valid_step _ _ _ valid2907 (by decide +kernel)




















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
theorem t5_1615choices : plan4442.choices=[9,3,3,6,10].map (options 5 3) := by rfl


theorem t5_1615part0 : t5_1615jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1615part1 : t5_1615jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1615part2 : t5_1615jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1615frontier : t5_1615root.frontier 1=t5_1615jobs := by rfl
theorem t5_1615all : t5_1615jobs.all (Job.check tree)=true := by
  simp only [t5_1615jobs,List.all_append,List.all_nil,t5_1615part0,t5_1615part1,t5_1615part2,Bool.and_self]
theorem t5_1615checked : Checked tree [9,3,3,6,10] := by
  refine ⟨plan4442,valid4442,t5_1615choices,?_⟩
  exact check_of_frontier tree 1 t5_1615root t5_1615jobs t5_1615frontier t5_1615all
theorem t5_1616choices : plan4443.choices=[9,3,3,7,7].map (options 5 3) := by rfl


theorem t5_1616part0 : t5_1616jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1616part1 : t5_1616jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1616part2 : t5_1616jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1616frontier : t5_1616root.frontier 1=t5_1616jobs := by rfl
theorem t5_1616all : t5_1616jobs.all (Job.check tree)=true := by
  simp only [t5_1616jobs,List.all_append,List.all_nil,t5_1616part0,t5_1616part1,t5_1616part2,Bool.and_self]
theorem t5_1616checked : Checked tree [9,3,3,7,7] := by
  refine ⟨plan4443,valid4443,t5_1616choices,?_⟩
  exact check_of_frontier tree 1 t5_1616root t5_1616jobs t5_1616frontier t5_1616all
theorem t5_1617choices : plan4444.choices=[9,3,3,10,7].map (options 5 3) := by rfl


theorem t5_1617part0 : t5_1617jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1617part1 : t5_1617jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1617part2 : t5_1617jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1617part3 : t5_1617jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_1617frontier : t5_1617root.frontier 1=t5_1617jobs := by rfl
theorem t5_1617all : t5_1617jobs.all (Job.check tree)=true := by
  simp only [t5_1617jobs,List.all_append,List.all_nil,t5_1617part0,t5_1617part1,t5_1617part2,t5_1617part3,Bool.and_self]
theorem t5_1617checked : Checked tree [9,3,3,10,7] := by
  refine ⟨plan4444,valid4444,t5_1617choices,?_⟩
  exact check_of_frontier tree 1 t5_1617root t5_1617jobs t5_1617frontier t5_1617all
theorem t5_1618choices : plan4445.choices=[9,3,3,10,10].map (options 5 3) := by rfl


theorem t5_1618part0 : t5_1618jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1618part1 : t5_1618jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1618frontier : t5_1618root.frontier 1=t5_1618jobs := by rfl
theorem t5_1618all : t5_1618jobs.all (Job.check tree)=true := by
  simp only [t5_1618jobs,List.all_append,List.all_nil,t5_1618part0,t5_1618part1,Bool.and_self]
theorem t5_1618checked : Checked tree [9,3,3,10,10] := by
  refine ⟨plan4445,valid4445,t5_1618choices,?_⟩
  exact check_of_frontier tree 1 t5_1618root t5_1618jobs t5_1618frontier t5_1618all
theorem t5_1619choices : plan4979.choices=[9,3,6,6,6].map (options 5 4) := by rfl


theorem t5_1619part0 : t5_1619jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1619frontier : t5_1619root.frontier 0=t5_1619jobs := by rfl
theorem t5_1619all : t5_1619jobs.all (Job.check tree)=true := by
  simp only [t5_1619jobs,List.all_append,List.all_nil,t5_1619part0,Bool.and_self]
theorem t5_1619checked : Checked tree [9,3,6,6,6] := by
  refine ⟨plan4979,valid4979,t5_1619choices,?_⟩
  exact check_of_frontier tree 0 t5_1619root t5_1619jobs t5_1619frontier t5_1619all
theorem t5_1620choices : plan4980.choices=[9,3,6,6,7].map (options 5 4) := by rfl


theorem t5_1620part0 : t5_1620jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1620part1 : t5_1620jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1620frontier : t5_1620root.frontier 1=t5_1620jobs := by rfl
theorem t5_1620all : t5_1620jobs.all (Job.check tree)=true := by
  simp only [t5_1620jobs,List.all_append,List.all_nil,t5_1620part0,t5_1620part1,Bool.and_self]
theorem t5_1620checked : Checked tree [9,3,6,6,7] := by
  refine ⟨plan4980,valid4980,t5_1620choices,?_⟩
  exact check_of_frontier tree 1 t5_1620root t5_1620jobs t5_1620frontier t5_1620all
theorem t5_1621choices : plan4981.choices=[9,3,6,6,10].map (options 5 4) := by rfl


theorem t5_1621part0 : t5_1621jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1621part1 : t5_1621jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1621frontier : t5_1621root.frontier 1=t5_1621jobs := by rfl
theorem t5_1621all : t5_1621jobs.all (Job.check tree)=true := by
  simp only [t5_1621jobs,List.all_append,List.all_nil,t5_1621part0,t5_1621part1,Bool.and_self]
theorem t5_1621checked : Checked tree [9,3,6,6,10] := by
  refine ⟨plan4981,valid4981,t5_1621choices,?_⟩
  exact check_of_frontier tree 1 t5_1621root t5_1621jobs t5_1621frontier t5_1621all
theorem t5_1622choices : plan4982.choices=[9,3,6,7,7].map (options 5 4) := by rfl


theorem t5_1622part0 : t5_1622jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1622part1 : t5_1622jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_1622part2 : t5_1622jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_1622frontier : t5_1622root.frontier 1=t5_1622jobs := by rfl
theorem t5_1622all : t5_1622jobs.all (Job.check tree)=true := by
  simp only [t5_1622jobs,List.all_append,List.all_nil,t5_1622part0,t5_1622part1,t5_1622part2,Bool.and_self]
theorem t5_1622checked : Checked tree [9,3,6,7,7] := by
  refine ⟨plan4982,valid4982,t5_1622choices,?_⟩
  exact check_of_frontier tree 1 t5_1622root t5_1622jobs t5_1622frontier t5_1622all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks045 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1622checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1615checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1616checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1617checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1618checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1619checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1620checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1621checked⟩
