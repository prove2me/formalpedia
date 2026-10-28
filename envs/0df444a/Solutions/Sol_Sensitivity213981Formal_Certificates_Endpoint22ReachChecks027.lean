-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks027
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:51:23.661225+00:00
-- url     : https://prove2.me/submissions/f638fed1-a891-4d4c-ba26-03efd67fc99f

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
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

theorem valid97 : plan97.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid99 : plan99.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid102 : plan102.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid103 : plan103.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid105 : plan105.Valid := valid_step _ _ _ valid0 (by decide +kernel)














































































































































































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





















































































































































































theorem valid475 : plan475.Valid := valid_step _ _ _ valid97 (by decide +kernel)










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

theorem valid481 : plan481.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid482 : plan482.Valid := valid_step _ _ _ valid99 (by decide +kernel)























theorem valid494 : plan494.Valid := valid_step _ _ _ valid102 (by decide +kernel)

theorem valid495 : plan495.Valid := valid_step _ _ _ valid103 (by decide +kernel)

theorem valid496 : plan496.Valid := valid_step _ _ _ valid105 (by decide +kernel)

theorem valid497 : plan497.Valid := valid_step _ _ _ valid103 (by decide +kernel)











theorem valid503 : plan503.Valid := valid_step _ _ _ valid103 (by decide +kernel)


















































































































































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















































































































theorem valid1304 : plan1304.Valid := valid_step _ _ _ valid475 (by decide +kernel)

theorem valid1305 : plan1305.Valid := valid_step _ _ _ valid481 (by decide +kernel)

theorem valid1306 : plan1306.Valid := valid_step _ _ _ valid482 (by decide +kernel)












































































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



















































theorem valid1370 : plan1370.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1371 : plan1371.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1372 : plan1372.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1373 : plan1373.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1374 : plan1374.Valid := valid_step _ _ _ valid503 (by decide +kernel)




































































































































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

















































































theorem valid2633 : plan2633.Valid := valid_step _ _ _ valid1304 (by decide +kernel)

theorem valid2634 : plan2634.Valid := valid_step _ _ _ valid1305 (by decide +kernel)

theorem valid2635 : plan2635.Valid := valid_step _ _ _ valid1306 (by decide +kernel)










































































































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































































































































































theorem valid2768 : plan2768.Valid := valid_step _ _ _ valid1370 (by decide +kernel)

theorem valid2769 : plan2769.Valid := valid_step _ _ _ valid1371 (by decide +kernel)

theorem valid2770 : plan2770.Valid := valid_step _ _ _ valid1372 (by decide +kernel)

theorem valid2771 : plan2771.Valid := valid_step _ _ _ valid1373 (by decide +kernel)

theorem valid2772 : plan2772.Valid := valid_step _ _ _ valid1374 (by decide +kernel)
























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



















theorem valid3946 : plan3946.Valid := valid_step _ _ _ valid2633 (by decide +kernel)

theorem valid3947 : plan3947.Valid := valid_step _ _ _ valid2634 (by decide +kernel)

theorem valid3948 : plan3948.Valid := valid_step _ _ _ valid2635 (by decide +kernel)








































































































































































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































































































































































theorem valid4304 : plan4304.Valid := valid_step _ _ _ valid2768 (by decide +kernel)

theorem valid4305 : plan4305.Valid := valid_step _ _ _ valid2769 (by decide +kernel)

theorem valid4306 : plan4306.Valid := valid_step _ _ _ valid2770 (by decide +kernel)

theorem valid4307 : plan4307.Valid := valid_step _ _ _ valid2771 (by decide +kernel)

theorem valid4308 : plan4308.Valid := valid_step _ _ _ valid2772 (by decide +kernel)
























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
theorem t5_865choices : plan3946.choices=[3,3,3,7,7].map (options 5 2) := by rfl


theorem t5_865part0 : t5_865jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_865part1 : t5_865jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_865frontier : t5_865root.frontier 1=t5_865jobs := by rfl
theorem t5_865all : t5_865jobs.all (Job.check tree)=true := by
  simp only [t5_865jobs,List.all_append,List.all_nil,t5_865part0,t5_865part1,Bool.and_self]
theorem t5_865checked : Checked tree [3,3,3,7,7] := by
  refine ⟨plan3946,valid3946,t5_865choices,?_⟩
  exact check_of_frontier tree 1 t5_865root t5_865jobs t5_865frontier t5_865all
theorem t5_866choices : plan3947.choices=[3,3,3,10,7].map (options 5 2) := by rfl


theorem t5_866part0 : t5_866jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_866part1 : t5_866jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_866frontier : t5_866root.frontier 1=t5_866jobs := by rfl
theorem t5_866all : t5_866jobs.all (Job.check tree)=true := by
  simp only [t5_866jobs,List.all_append,List.all_nil,t5_866part0,t5_866part1,Bool.and_self]
theorem t5_866checked : Checked tree [3,3,3,10,7] := by
  refine ⟨plan3947,valid3947,t5_866choices,?_⟩
  exact check_of_frontier tree 1 t5_866root t5_866jobs t5_866frontier t5_866all
theorem t5_867choices : plan3948.choices=[3,3,3,10,10].map (options 5 2) := by rfl


theorem t5_867part0 : t5_867jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_867frontier : t5_867root.frontier 0=t5_867jobs := by rfl
theorem t5_867all : t5_867jobs.all (Job.check tree)=true := by
  simp only [t5_867jobs,List.all_append,List.all_nil,t5_867part0,Bool.and_self]
theorem t5_867checked : Checked tree [3,3,3,10,10] := by
  refine ⟨plan3948,valid3948,t5_867choices,?_⟩
  exact check_of_frontier tree 0 t5_867root t5_867jobs t5_867frontier t5_867all
theorem t5_868choices : plan4304.choices=[3,3,6,6,6].map (options 5 3) := by rfl


theorem t5_868part0 : t5_868jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_868frontier : t5_868root.frontier 0=t5_868jobs := by rfl
theorem t5_868all : t5_868jobs.all (Job.check tree)=true := by
  simp only [t5_868jobs,List.all_append,List.all_nil,t5_868part0,Bool.and_self]
theorem t5_868checked : Checked tree [3,3,6,6,6] := by
  refine ⟨plan4304,valid4304,t5_868choices,?_⟩
  exact check_of_frontier tree 0 t5_868root t5_868jobs t5_868frontier t5_868all
theorem t5_869choices : plan4305.choices=[3,3,6,6,7].map (options 5 3) := by rfl


theorem t5_869part0 : t5_869jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_869part1 : t5_869jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_869part2 : t5_869jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_869frontier : t5_869root.frontier 1=t5_869jobs := by rfl
theorem t5_869all : t5_869jobs.all (Job.check tree)=true := by
  simp only [t5_869jobs,List.all_append,List.all_nil,t5_869part0,t5_869part1,t5_869part2,Bool.and_self]
theorem t5_869checked : Checked tree [3,3,6,6,7] := by
  refine ⟨plan4305,valid4305,t5_869choices,?_⟩
  exact check_of_frontier tree 1 t5_869root t5_869jobs t5_869frontier t5_869all
theorem t5_870choices : plan4306.choices=[3,3,6,6,10].map (options 5 3) := by rfl


theorem t5_870part0 : t5_870jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_870part1 : t5_870jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_870frontier : t5_870root.frontier 1=t5_870jobs := by rfl
theorem t5_870all : t5_870jobs.all (Job.check tree)=true := by
  simp only [t5_870jobs,List.all_append,List.all_nil,t5_870part0,t5_870part1,Bool.and_self]
theorem t5_870checked : Checked tree [3,3,6,6,10] := by
  refine ⟨plan4306,valid4306,t5_870choices,?_⟩
  exact check_of_frontier tree 1 t5_870root t5_870jobs t5_870frontier t5_870all
theorem t5_871choices : plan4307.choices=[3,3,6,7,7].map (options 5 3) := by rfl


theorem t5_871part0 : t5_871jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_871part1 : t5_871jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_871part2 : t5_871jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_871part3 : t5_871jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_871frontier : t5_871root.frontier 1=t5_871jobs := by rfl
theorem t5_871all : t5_871jobs.all (Job.check tree)=true := by
  simp only [t5_871jobs,List.all_append,List.all_nil,t5_871part0,t5_871part1,t5_871part2,t5_871part3,Bool.and_self]
theorem t5_871checked : Checked tree [3,3,6,7,7] := by
  refine ⟨plan4307,valid4307,t5_871choices,?_⟩
  exact check_of_frontier tree 1 t5_871root t5_871jobs t5_871frontier t5_871all
theorem t5_872choices : plan4308.choices=[3,3,6,10,7].map (options 5 3) := by rfl


theorem t5_872part0 : t5_872jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_872part1 : t5_872jobs1.all (Job.check tree)=true := by decide +kernel

theorem t5_872part2 : t5_872jobs2.all (Job.check tree)=true := by decide +kernel

theorem t5_872part3 : t5_872jobs3.all (Job.check tree)=true := by decide +kernel

theorem t5_872part4 : t5_872jobs4.all (Job.check tree)=true := by decide +kernel

theorem t5_872frontier : t5_872root.frontier 1=t5_872jobs := by rfl
theorem t5_872all : t5_872jobs.all (Job.check tree)=true := by
  simp only [t5_872jobs,List.all_append,List.all_nil,t5_872part0,t5_872part1,t5_872part2,t5_872part3,t5_872part4,Bool.and_self]
theorem t5_872checked : Checked tree [3,3,6,10,7] := by
  refine ⟨plan4308,valid4308,t5_872choices,?_⟩
  exact check_of_frontier tree 1 t5_872root t5_872jobs t5_872frontier t5_872all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks027 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_872checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_865checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_866checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_867checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_868checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_869checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_870checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_871checked⟩
