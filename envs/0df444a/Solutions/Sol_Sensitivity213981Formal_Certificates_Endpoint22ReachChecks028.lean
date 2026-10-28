-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks028
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:24.249417+00:00
-- url     : https://prove2.me/submissions/21e988b8-9b80-4ada-a1e5-c0f1f91e6e3c

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans049
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

































theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)











theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)



















theorem valid514 : plan514.Valid := valid_step _ _ _ valid108 (by decide +kernel)

theorem valid515 : plan515.Valid := valid_step _ _ _ valid109 (by decide +kernel)

theorem valid516 : plan516.Valid := valid_step _ _ _ valid111 (by decide +kernel)

theorem valid517 : plan517.Valid := valid_step _ _ _ valid109 (by decide +kernel)











theorem valid523 : plan523.Valid := valid_step _ _ _ valid109 (by decide +kernel)










































































































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





























































theorem valid1375 : plan1375.Valid := valid_step _ _ _ valid504 (by decide +kernel)

theorem valid1376 : plan1376.Valid := valid_step _ _ _ valid497 (by decide +kernel)







































theorem valid1396 : plan1396.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1397 : plan1397.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1398 : plan1398.Valid := valid_step _ _ _ valid504 (by decide +kernel)













































































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









































































































































































theorem valid2773 : plan2773.Valid := valid_step _ _ _ valid1375 (by decide +kernel)

theorem valid2774 : plan2774.Valid := valid_step _ _ _ valid1376 (by decide +kernel)

theorem valid2775 : plan2775.Valid := valid_step _ _ _ valid1396 (by decide +kernel)

theorem valid2776 : plan2776.Valid := valid_step _ _ _ valid1397 (by decide +kernel)

theorem valid2777 : plan2777.Valid := valid_step _ _ _ valid1398 (by decide +kernel)














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

theorem valid1441 : plan1441.Valid := valid_step _ _ _ valid523 (by decide +kernel)






























































































































































































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

















































































theorem valid3017 : plan3017.Valid := valid_step _ _ _ valid1437 (by decide +kernel)

theorem valid3018 : plan3018.Valid := valid_step _ _ _ valid1438 (by decide +kernel)

theorem valid3019 : plan3019.Valid := valid_step _ _ _ valid1439 (by decide +kernel)

theorem valid3020 : plan3020.Valid := valid_step _ _ _ valid1440 (by decide +kernel)

theorem valid3021 : plan3021.Valid := valid_step _ _ _ valid1441 (by decide +kernel)






































































































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









































































































































































theorem valid4309 : plan4309.Valid := valid_step _ _ _ valid2773 (by decide +kernel)

theorem valid4310 : plan4310.Valid := valid_step _ _ _ valid2774 (by decide +kernel)

theorem valid4311 : plan4311.Valid := valid_step _ _ _ valid2775 (by decide +kernel)

theorem valid4312 : plan4312.Valid := valid_step _ _ _ valid2776 (by decide +kernel)

theorem valid4313 : plan4313.Valid := valid_step _ _ _ valid2777 (by decide +kernel)














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

























































theorem valid4733 : plan4733.Valid := valid_step _ _ _ valid3017 (by decide +kernel)

theorem valid4734 : plan4734.Valid := valid_step _ _ _ valid3018 (by decide +kernel)

theorem valid4735 : plan4735.Valid := valid_step _ _ _ valid3019 (by decide +kernel)

theorem valid4736 : plan4736.Valid := valid_step _ _ _ valid3020 (by decide +kernel)

theorem valid4737 : plan4737.Valid := valid_step _ _ _ valid3021 (by decide +kernel)






























































































































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
theorem t5_873choices : plan4309.choices=[3,3,6,10,10].map (options 5 3) := by rfl


theorem t5_873part0 : t5_873jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_873part1 : t5_873jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_873frontier : t5_873root.frontier 1=t5_873jobs := by rfl
theorem t5_873all : t5_873jobs.all (Job.check tree)=true := by
  simp only [t5_873jobs,List.all_append,List.all_nil,t5_873part0,t5_873part1,Bool.and_self]
theorem t5_873checked : Checked tree [3,3,6,10,10] := by
  refine ⟨plan4309,valid4309,t5_873choices,?_⟩
  exact check_of_frontier tree 1 t5_873root t5_873jobs t5_873frontier t5_873all
theorem t5_874choices : plan4310.choices=[3,3,7,7,7].map (options 5 3) := by rfl


theorem t5_874part0 : t5_874jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_874part1 : t5_874jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_874frontier : t5_874root.frontier 1=t5_874jobs := by rfl
theorem t5_874all : t5_874jobs.all (Job.check tree)=true := by
  simp only [t5_874jobs,List.all_append,List.all_nil,t5_874part0,t5_874part1,Bool.and_self]
theorem t5_874checked : Checked tree [3,3,7,7,7] := by
  refine ⟨plan4310,valid4310,t5_874choices,?_⟩
  exact check_of_frontier tree 1 t5_874root t5_874jobs t5_874frontier t5_874all
theorem t5_875choices : plan4311.choices=[3,3,10,7,7].map (options 5 3) := by rfl


theorem t5_875part0 : t5_875jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_875part1 : t5_875jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_875part2 : t5_875jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_875part3 : t5_875jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_875frontier : t5_875root.frontier 1=t5_875jobs := by rfl
theorem t5_875all : t5_875jobs.all (Job.check tree)=true := by
  simp only [t5_875jobs,List.all_append,List.all_nil,t5_875part0,t5_875part1,t5_875part2,t5_875part3,Bool.and_self]
theorem t5_875checked : Checked tree [3,3,10,7,7] := by
  refine ⟨plan4311,valid4311,t5_875choices,?_⟩
  exact check_of_frontier tree 1 t5_875root t5_875jobs t5_875frontier t5_875all
theorem t5_876choices : plan4312.choices=[3,3,10,10,7].map (options 5 3) := by rfl


theorem t5_876part0 : t5_876jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_876part1 : t5_876jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_876part2 : t5_876jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_876frontier : t5_876root.frontier 1=t5_876jobs := by rfl
theorem t5_876all : t5_876jobs.all (Job.check tree)=true := by
  simp only [t5_876jobs,List.all_append,List.all_nil,t5_876part0,t5_876part1,t5_876part2,Bool.and_self]
theorem t5_876checked : Checked tree [3,3,10,10,7] := by
  refine ⟨plan4312,valid4312,t5_876choices,?_⟩
  exact check_of_frontier tree 1 t5_876root t5_876jobs t5_876frontier t5_876all
theorem t5_877choices : plan4313.choices=[3,3,10,10,10].map (options 5 3) := by rfl


theorem t5_877part0 : t5_877jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_877frontier : t5_877root.frontier 0=t5_877jobs := by rfl
theorem t5_877all : t5_877jobs.all (Job.check tree)=true := by
  simp only [t5_877jobs,List.all_append,List.all_nil,t5_877part0,Bool.and_self]
theorem t5_877checked : Checked tree [3,3,10,10,10] := by
  refine ⟨plan4313,valid4313,t5_877choices,?_⟩
  exact check_of_frontier tree 0 t5_877root t5_877jobs t5_877frontier t5_877all
theorem t5_878choices : plan4733.choices=[3,6,6,6,6].map (options 5 4) := by rfl


theorem t5_878part0 : t5_878jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_878frontier : t5_878root.frontier 0=t5_878jobs := by rfl
theorem t5_878all : t5_878jobs.all (Job.check tree)=true := by
  simp only [t5_878jobs,List.all_append,List.all_nil,t5_878part0,Bool.and_self]
theorem t5_878checked : Checked tree [3,6,6,6,6] := by
  refine ⟨plan4733,valid4733,t5_878choices,?_⟩
  exact check_of_frontier tree 0 t5_878root t5_878jobs t5_878frontier t5_878all
theorem t5_879choices : plan4734.choices=[3,6,6,6,7].map (options 5 4) := by rfl


theorem t5_879part0 : t5_879jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_879part1 : t5_879jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_879frontier : t5_879root.frontier 1=t5_879jobs := by rfl
theorem t5_879all : t5_879jobs.all (Job.check tree)=true := by
  simp only [t5_879jobs,List.all_append,List.all_nil,t5_879part0,t5_879part1,Bool.and_self]
theorem t5_879checked : Checked tree [3,6,6,6,7] := by
  refine ⟨plan4734,valid4734,t5_879choices,?_⟩
  exact check_of_frontier tree 1 t5_879root t5_879jobs t5_879frontier t5_879all
theorem t5_880choices : plan4735.choices=[3,6,6,6,10].map (options 5 4) := by rfl


theorem t5_880part0 : t5_880jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_880frontier : t5_880root.frontier 0=t5_880jobs := by rfl
theorem t5_880all : t5_880jobs.all (Job.check tree)=true := by
  simp only [t5_880jobs,List.all_append,List.all_nil,t5_880part0,Bool.and_self]
theorem t5_880checked : Checked tree [3,6,6,6,10] := by
  refine ⟨plan4735,valid4735,t5_880choices,?_⟩
  exact check_of_frontier tree 0 t5_880root t5_880jobs t5_880frontier t5_880all
theorem t5_881choices : plan4736.choices=[3,6,6,7,7].map (options 5 4) := by rfl


theorem t5_881part0 : t5_881jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_881part1 : t5_881jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_881part2 : t5_881jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_881frontier : t5_881root.frontier 1=t5_881jobs := by rfl
theorem t5_881all : t5_881jobs.all (Job.check tree)=true := by
  simp only [t5_881jobs,List.all_append,List.all_nil,t5_881part0,t5_881part1,t5_881part2,Bool.and_self]
theorem t5_881checked : Checked tree [3,6,6,7,7] := by
  refine ⟨plan4736,valid4736,t5_881choices,?_⟩
  exact check_of_frontier tree 1 t5_881root t5_881jobs t5_881frontier t5_881all
theorem t5_882choices : plan4737.choices=[3,6,6,10,7].map (options 5 4) := by rfl


theorem t5_882part0 : t5_882jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_882part1 : t5_882jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_882part2 : t5_882jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_882frontier : t5_882root.frontier 1=t5_882jobs := by rfl
theorem t5_882all : t5_882jobs.all (Job.check tree)=true := by
  simp only [t5_882jobs,List.all_append,List.all_nil,t5_882part0,t5_882part1,t5_882part2,Bool.and_self]
theorem t5_882checked : Checked tree [3,6,6,10,7] := by
  refine ⟨plan4737,valid4737,t5_882choices,?_⟩
  exact check_of_frontier tree 1 t5_882root t5_882jobs t5_882frontier t5_882all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks028 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_881checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_882checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_873checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_874checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_875checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_876checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_877checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_878checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_879checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_880checked⟩
