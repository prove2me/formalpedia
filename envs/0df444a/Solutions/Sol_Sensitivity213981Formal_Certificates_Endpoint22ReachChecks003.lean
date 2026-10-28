-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks003
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:01:44.291679+00:00
-- url     : https://prove2.me/submissions/8f48d1db-0b36-4710-a672-8f81d449a6eb

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans018
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans020
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans022
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans023
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans024
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























































































































theorem valid60 : plan60.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid61 : plan61.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid62 : plan62.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid64 : plan64.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid65 : plan65.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid67 : plan67.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid68 : plan68.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid69 : plan69.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid70 : plan70.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid71 : plan71.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid72 : plan72.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid73 : plan73.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid74 : plan74.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid75 : plan75.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid76 : plan76.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid77 : plan77.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid78 : plan78.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid79 : plan79.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid80 : plan80.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid81 : plan81.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid82 : plan82.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid83 : plan83.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid84 : plan84.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid85 : plan85.Valid := valid_step _ _ _ valid0 (by decide +kernel)






















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





























































































theorem valid335 : plan335.Valid := valid_step _ _ _ valid60 (by decide +kernel)







theorem valid339 : plan339.Valid := valid_step _ _ _ valid61 (by decide +kernel)

theorem valid340 : plan340.Valid := valid_step _ _ _ valid62 (by decide +kernel)











theorem valid346 : plan346.Valid := valid_step _ _ _ valid62 (by decide +kernel)

theorem valid347 : plan347.Valid := valid_step _ _ _ valid64 (by decide +kernel)

theorem valid348 : plan348.Valid := valid_step _ _ _ valid65 (by decide +kernel)

theorem valid349 : plan349.Valid := valid_step _ _ _ valid67 (by decide +kernel)









theorem valid354 : plan354.Valid := valid_step _ _ _ valid68 (by decide +kernel)

theorem valid355 : plan355.Valid := valid_step _ _ _ valid69 (by decide +kernel)

theorem valid356 : plan356.Valid := valid_step _ _ _ valid70 (by decide +kernel)

theorem valid357 : plan357.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid358 : plan358.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid359 : plan359.Valid := valid_step _ _ _ valid73 (by decide +kernel)

theorem valid360 : plan360.Valid := valid_step _ _ _ valid74 (by decide +kernel)

theorem valid361 : plan361.Valid := valid_step _ _ _ valid69 (by decide +kernel)

theorem valid362 : plan362.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid363 : plan363.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid364 : plan364.Valid := valid_step _ _ _ valid74 (by decide +kernel)









theorem valid369 : plan369.Valid := valid_step _ _ _ valid69 (by decide +kernel)











theorem valid375 : plan375.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid376 : plan376.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid377 : plan377.Valid := valid_step _ _ _ valid74 (by decide +kernel)

theorem valid378 : plan378.Valid := valid_step _ _ _ valid72 (by decide +kernel)









theorem valid383 : plan383.Valid := valid_step _ _ _ valid69 (by decide +kernel)


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



























































































theorem valid910 : plan910.Valid := valid_step _ _ _ valid335 (by decide +kernel)































theorem valid926 : plan926.Valid := valid_step _ _ _ valid339 (by decide +kernel)

theorem valid927 : plan927.Valid := valid_step _ _ _ valid340 (by decide +kernel)











theorem valid933 : plan933.Valid := valid_step _ _ _ valid346 (by decide +kernel)











theorem valid939 : plan939.Valid := valid_step _ _ _ valid346 (by decide +kernel)

theorem valid940 : plan940.Valid := valid_step _ _ _ valid347 (by decide +kernel)

theorem valid941 : plan941.Valid := valid_step _ _ _ valid348 (by decide +kernel)

theorem valid942 : plan942.Valid := valid_step _ _ _ valid349 (by decide +kernel)




































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































































































































































theorem valid1712 : plan1712.Valid := valid_step _ _ _ valid910 (by decide +kernel)
































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







theorem valid388 : plan388.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid389 : plan389.Valid := valid_step _ _ _ valid74 (by decide +kernel)

theorem valid390 : plan390.Valid := valid_step _ _ _ valid76 (by decide +kernel)

theorem valid391 : plan391.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid392 : plan392.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid393 : plan393.Valid := valid_step _ _ _ valid79 (by decide +kernel)

theorem valid394 : plan394.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid395 : plan395.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid396 : plan396.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid397 : plan397.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid398 : plan398.Valid := valid_step _ _ _ valid75 (by decide +kernel)







theorem valid402 : plan402.Valid := valid_step _ _ _ valid75 (by decide +kernel)

theorem valid403 : plan403.Valid := valid_step _ _ _ valid76 (by decide +kernel)

theorem valid404 : plan404.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid405 : plan405.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid406 : plan406.Valid := valid_step _ _ _ valid79 (by decide +kernel)

theorem valid407 : plan407.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid408 : plan408.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid409 : plan409.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid410 : plan410.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid411 : plan411.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid412 : plan412.Valid := valid_step _ _ _ valid75 (by decide +kernel)







theorem valid416 : plan416.Valid := valid_step _ _ _ valid75 (by decide +kernel)

theorem valid417 : plan417.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid418 : plan418.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid419 : plan419.Valid := valid_step _ _ _ valid79 (by decide +kernel)

theorem valid420 : plan420.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid421 : plan421.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid422 : plan422.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid423 : plan423.Valid := valid_step _ _ _ valid82 (by decide +kernel)

theorem valid424 : plan424.Valid := valid_step _ _ _ valid83 (by decide +kernel)

theorem valid425 : plan425.Valid := valid_step _ _ _ valid85 (by decide +kernel)

theorem valid426 : plan426.Valid := valid_step _ _ _ valid81 (by decide +kernel)

theorem valid427 : plan427.Valid := valid_step _ _ _ valid82 (by decide +kernel)

theorem valid428 : plan428.Valid := valid_step _ _ _ valid83 (by decide +kernel)

theorem valid429 : plan429.Valid := valid_step _ _ _ valid84 (by decide +kernel)

theorem valid430 : plan430.Valid := valid_step _ _ _ valid85 (by decide +kernel)

theorem valid431 : plan431.Valid := valid_step _ _ _ valid82 (by decide +kernel)

theorem valid432 : plan432.Valid := valid_step _ _ _ valid83 (by decide +kernel)

theorem valid433 : plan433.Valid := valid_step _ _ _ valid85 (by decide +kernel)

theorem valid434 : plan434.Valid := valid_step _ _ _ valid83 (by decide +kernel)

theorem valid435 : plan435.Valid := valid_step _ _ _ valid82 (by decide +kernel)

theorem valid436 : plan436.Valid := valid_step _ _ _ valid83 (by decide +kernel)

theorem valid437 : plan437.Valid := valid_step _ _ _ valid85 (by decide +kernel)

theorem valid438 : plan438.Valid := valid_step _ _ _ valid82 (by decide +kernel)

theorem valid439 : plan439.Valid := valid_step _ _ _ valid83 (by decide +kernel)

theorem valid440 : plan440.Valid := valid_step _ _ _ valid84 (by decide +kernel)

theorem valid441 : plan441.Valid := valid_step _ _ _ valid85 (by decide +kernel)

theorem valid442 : plan442.Valid := valid_step _ _ _ valid83 (by decide +kernel)

theorem valid443 : plan443.Valid := valid_step _ _ _ valid85 (by decide +kernel)










































































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























theorem valid972 : plan972.Valid := valid_step _ _ _ valid356 (by decide +kernel)

theorem valid973 : plan973.Valid := valid_step _ _ _ valid357 (by decide +kernel)

theorem valid974 : plan974.Valid := valid_step _ _ _ valid358 (by decide +kernel)

theorem valid975 : plan975.Valid := valid_step _ _ _ valid359 (by decide +kernel)

theorem valid976 : plan976.Valid := valid_step _ _ _ valid360 (by decide +kernel)

theorem valid977 : plan977.Valid := valid_step _ _ _ valid362 (by decide +kernel)

theorem valid978 : plan978.Valid := valid_step _ _ _ valid363 (by decide +kernel)

theorem valid979 : plan979.Valid := valid_step _ _ _ valid364 (by decide +kernel)

theorem valid980 : plan980.Valid := valid_step _ _ _ valid369 (by decide +kernel)



















theorem valid990 : plan990.Valid := valid_step _ _ _ valid383 (by decide +kernel)













theorem valid997 : plan997.Valid := valid_step _ _ _ valid362 (by decide +kernel)

theorem valid998 : plan998.Valid := valid_step _ _ _ valid363 (by decide +kernel)

theorem valid999 : plan999.Valid := valid_step _ _ _ valid364 (by decide +kernel)

theorem valid1000 : plan1000.Valid := valid_step _ _ _ valid375 (by decide +kernel)

theorem valid1001 : plan1001.Valid := valid_step _ _ _ valid376 (by decide +kernel)

theorem valid1002 : plan1002.Valid := valid_step _ _ _ valid377 (by decide +kernel)

theorem valid1003 : plan1003.Valid := valid_step _ _ _ valid378 (by decide +kernel)

theorem valid1004 : plan1004.Valid := valid_step _ _ _ valid388 (by decide +kernel)

theorem valid1005 : plan1005.Valid := valid_step _ _ _ valid389 (by decide +kernel)

theorem valid1006 : plan1006.Valid := valid_step _ _ _ valid354 (by decide +kernel)

theorem valid1007 : plan1007.Valid := valid_step _ _ _ valid355 (by decide +kernel)











theorem valid1013 : plan1013.Valid := valid_step _ _ _ valid361 (by decide +kernel)















theorem valid1021 : plan1021.Valid := valid_step _ _ _ valid361 (by decide +kernel)











theorem valid1027 : plan1027.Valid := valid_step _ _ _ valid354 (by decide +kernel)

theorem valid1028 : plan1028.Valid := valid_step _ _ _ valid355 (by decide +kernel)











theorem valid1034 : plan1034.Valid := valid_step _ _ _ valid361 (by decide +kernel)























theorem valid1046 : plan1046.Valid := valid_step _ _ _ valid403 (by decide +kernel)

theorem valid1047 : plan1047.Valid := valid_step _ _ _ valid404 (by decide +kernel)

theorem valid1048 : plan1048.Valid := valid_step _ _ _ valid405 (by decide +kernel)

theorem valid1049 : plan1049.Valid := valid_step _ _ _ valid406 (by decide +kernel)

theorem valid1050 : plan1050.Valid := valid_step _ _ _ valid407 (by decide +kernel)

theorem valid1051 : plan1051.Valid := valid_step _ _ _ valid408 (by decide +kernel)

theorem valid1052 : plan1052.Valid := valid_step _ _ _ valid409 (by decide +kernel)

theorem valid1053 : plan1053.Valid := valid_step _ _ _ valid410 (by decide +kernel)

theorem valid1054 : plan1054.Valid := valid_step _ _ _ valid411 (by decide +kernel)

theorem valid1055 : plan1055.Valid := valid_step _ _ _ valid417 (by decide +kernel)

theorem valid1056 : plan1056.Valid := valid_step _ _ _ valid418 (by decide +kernel)
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





























































































































theorem valid1791 : plan1791.Valid := valid_step _ _ _ valid940 (by decide +kernel)

theorem valid1792 : plan1792.Valid := valid_step _ _ _ valid941 (by decide +kernel)

theorem valid1793 : plan1793.Valid := valid_step _ _ _ valid942 (by decide +kernel)

theorem valid1794 : plan1794.Valid := valid_step _ _ _ valid926 (by decide +kernel)

theorem valid1795 : plan1795.Valid := valid_step _ _ _ valid927 (by decide +kernel)

theorem valid1796 : plan1796.Valid := valid_step _ _ _ valid933 (by decide +kernel)

theorem valid1797 : plan1797.Valid := valid_step _ _ _ valid939 (by decide +kernel)






















































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

theorem valid1057 : plan1057.Valid := valid_step _ _ _ valid419 (by decide +kernel)

theorem valid1058 : plan1058.Valid := valid_step _ _ _ valid420 (by decide +kernel)

theorem valid1059 : plan1059.Valid := valid_step _ _ _ valid421 (by decide +kernel)

theorem valid1060 : plan1060.Valid := valid_step _ _ _ valid422 (by decide +kernel)

theorem valid1061 : plan1061.Valid := valid_step _ _ _ valid408 (by decide +kernel)

theorem valid1062 : plan1062.Valid := valid_step _ _ _ valid409 (by decide +kernel)

theorem valid1063 : plan1063.Valid := valid_step _ _ _ valid410 (by decide +kernel)

theorem valid1064 : plan1064.Valid := valid_step _ _ _ valid411 (by decide +kernel)

theorem valid1065 : plan1065.Valid := valid_step _ _ _ valid421 (by decide +kernel)

theorem valid1066 : plan1066.Valid := valid_step _ _ _ valid422 (by decide +kernel)

theorem valid1067 : plan1067.Valid := valid_step _ _ _ valid390 (by decide +kernel)

theorem valid1068 : plan1068.Valid := valid_step _ _ _ valid391 (by decide +kernel)

theorem valid1069 : plan1069.Valid := valid_step _ _ _ valid392 (by decide +kernel)

theorem valid1070 : plan1070.Valid := valid_step _ _ _ valid393 (by decide +kernel)

theorem valid1071 : plan1071.Valid := valid_step _ _ _ valid394 (by decide +kernel)

theorem valid1072 : plan1072.Valid := valid_step _ _ _ valid395 (by decide +kernel)

theorem valid1073 : plan1073.Valid := valid_step _ _ _ valid396 (by decide +kernel)

theorem valid1074 : plan1074.Valid := valid_step _ _ _ valid397 (by decide +kernel)

theorem valid1075 : plan1075.Valid := valid_step _ _ _ valid398 (by decide +kernel)







theorem valid1079 : plan1079.Valid := valid_step _ _ _ valid402 (by decide +kernel)



















theorem valid1089 : plan1089.Valid := valid_step _ _ _ valid412 (by decide +kernel)







theorem valid1093 : plan1093.Valid := valid_step _ _ _ valid416 (by decide +kernel)













theorem valid1100 : plan1100.Valid := valid_step _ _ _ valid395 (by decide +kernel)

theorem valid1101 : plan1101.Valid := valid_step _ _ _ valid396 (by decide +kernel)

theorem valid1102 : plan1102.Valid := valid_step _ _ _ valid397 (by decide +kernel)

theorem valid1103 : plan1103.Valid := valid_step _ _ _ valid402 (by decide +kernel)



















theorem valid1113 : plan1113.Valid := valid_step _ _ _ valid416 (by decide +kernel)













theorem valid1120 : plan1120.Valid := valid_step _ _ _ valid408 (by decide +kernel)

theorem valid1121 : plan1121.Valid := valid_step _ _ _ valid409 (by decide +kernel)

theorem valid1122 : plan1122.Valid := valid_step _ _ _ valid410 (by decide +kernel)

theorem valid1123 : plan1123.Valid := valid_step _ _ _ valid411 (by decide +kernel)

theorem valid1124 : plan1124.Valid := valid_step _ _ _ valid421 (by decide +kernel)

theorem valid1125 : plan1125.Valid := valid_step _ _ _ valid422 (by decide +kernel)

theorem valid1126 : plan1126.Valid := valid_step _ _ _ valid411 (by decide +kernel)

theorem valid1127 : plan1127.Valid := valid_step _ _ _ valid390 (by decide +kernel)

theorem valid1128 : plan1128.Valid := valid_step _ _ _ valid391 (by decide +kernel)

theorem valid1129 : plan1129.Valid := valid_step _ _ _ valid392 (by decide +kernel)

theorem valid1130 : plan1130.Valid := valid_step _ _ _ valid393 (by decide +kernel)

theorem valid1131 : plan1131.Valid := valid_step _ _ _ valid394 (by decide +kernel)

theorem valid1132 : plan1132.Valid := valid_step _ _ _ valid395 (by decide +kernel)








































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





























theorem valid1167 : plan1167.Valid := valid_step _ _ _ valid420 (by decide +kernel)

theorem valid1168 : plan1168.Valid := valid_step _ _ _ valid421 (by decide +kernel)

theorem valid1169 : plan1169.Valid := valid_step _ _ _ valid422 (by decide +kernel)

theorem valid1170 : plan1170.Valid := valid_step _ _ _ valid411 (by decide +kernel)

theorem valid1171 : plan1171.Valid := valid_step _ _ _ valid421 (by decide +kernel)

theorem valid1172 : plan1172.Valid := valid_step _ _ _ valid422 (by decide +kernel)

theorem valid1173 : plan1173.Valid := valid_step _ _ _ valid423 (by decide +kernel)

theorem valid1174 : plan1174.Valid := valid_step _ _ _ valid424 (by decide +kernel)

theorem valid1175 : plan1175.Valid := valid_step _ _ _ valid425 (by decide +kernel)

theorem valid1176 : plan1176.Valid := valid_step _ _ _ valid426 (by decide +kernel)

theorem valid1177 : plan1177.Valid := valid_step _ _ _ valid427 (by decide +kernel)

theorem valid1178 : plan1178.Valid := valid_step _ _ _ valid428 (by decide +kernel)

theorem valid1179 : plan1179.Valid := valid_step _ _ _ valid429 (by decide +kernel)

theorem valid1180 : plan1180.Valid := valid_step _ _ _ valid430 (by decide +kernel)

theorem valid1181 : plan1181.Valid := valid_step _ _ _ valid431 (by decide +kernel)

theorem valid1182 : plan1182.Valid := valid_step _ _ _ valid432 (by decide +kernel)

theorem valid1183 : plan1183.Valid := valid_step _ _ _ valid433 (by decide +kernel)

theorem valid1184 : plan1184.Valid := valid_step _ _ _ valid434 (by decide +kernel)

theorem valid1185 : plan1185.Valid := valid_step _ _ _ valid435 (by decide +kernel)

theorem valid1186 : plan1186.Valid := valid_step _ _ _ valid436 (by decide +kernel)

theorem valid1187 : plan1187.Valid := valid_step _ _ _ valid437 (by decide +kernel)

theorem valid1188 : plan1188.Valid := valid_step _ _ _ valid438 (by decide +kernel)

theorem valid1189 : plan1189.Valid := valid_step _ _ _ valid439 (by decide +kernel)

theorem valid1190 : plan1190.Valid := valid_step _ _ _ valid440 (by decide +kernel)

theorem valid1191 : plan1191.Valid := valid_step _ _ _ valid441 (by decide +kernel)

theorem valid1192 : plan1192.Valid := valid_step _ _ _ valid442 (by decide +kernel)

theorem valid1193 : plan1193.Valid := valid_step _ _ _ valid443 (by decide +kernel)

theorem valid1194 : plan1194.Valid := valid_step _ _ _ valid426 (by decide +kernel)

theorem valid1195 : plan1195.Valid := valid_step _ _ _ valid427 (by decide +kernel)

theorem valid1196 : plan1196.Valid := valid_step _ _ _ valid428 (by decide +kernel)

theorem valid1197 : plan1197.Valid := valid_step _ _ _ valid429 (by decide +kernel)

theorem valid1198 : plan1198.Valid := valid_step _ _ _ valid430 (by decide +kernel)

theorem valid1199 : plan1199.Valid := valid_step _ _ _ valid431 (by decide +kernel)

theorem valid1200 : plan1200.Valid := valid_step _ _ _ valid432 (by decide +kernel)

theorem valid1201 : plan1201.Valid := valid_step _ _ _ valid433 (by decide +kernel)

theorem valid1202 : plan1202.Valid := valid_step _ _ _ valid434 (by decide +kernel)

theorem valid1203 : plan1203.Valid := valid_step _ _ _ valid438 (by decide +kernel)

theorem valid1204 : plan1204.Valid := valid_step _ _ _ valid439 (by decide +kernel)

theorem valid1205 : plan1205.Valid := valid_step _ _ _ valid440 (by decide +kernel)

theorem valid1206 : plan1206.Valid := valid_step _ _ _ valid441 (by decide +kernel)

theorem valid1207 : plan1207.Valid := valid_step _ _ _ valid442 (by decide +kernel)

theorem valid1208 : plan1208.Valid := valid_step _ _ _ valid443 (by decide +kernel)

theorem valid1209 : plan1209.Valid := valid_step _ _ _ valid431 (by decide +kernel)

theorem valid1210 : plan1210.Valid := valid_step _ _ _ valid432 (by decide +kernel)

theorem valid1211 : plan1211.Valid := valid_step _ _ _ valid433 (by decide +kernel)

theorem valid1212 : plan1212.Valid := valid_step _ _ _ valid434 (by decide +kernel)

theorem valid1213 : plan1213.Valid := valid_step _ _ _ valid442 (by decide +kernel)

theorem valid1214 : plan1214.Valid := valid_step _ _ _ valid443 (by decide +kernel)

theorem valid1215 : plan1215.Valid := valid_step _ _ _ valid434 (by decide +kernel)


































































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



























































































theorem valid1966 : plan1966.Valid := valid_step _ _ _ valid1000 (by decide +kernel)

theorem valid1967 : plan1967.Valid := valid_step _ _ _ valid1001 (by decide +kernel)

theorem valid1968 : plan1968.Valid := valid_step _ _ _ valid1002 (by decide +kernel)

theorem valid1969 : plan1969.Valid := valid_step _ _ _ valid1003 (by decide +kernel)

theorem valid1970 : plan1970.Valid := valid_step _ _ _ valid1004 (by decide +kernel)

theorem valid1971 : plan1971.Valid := valid_step _ _ _ valid1005 (by decide +kernel)

theorem valid1972 : plan1972.Valid := valid_step _ _ _ valid972 (by decide +kernel)

theorem valid1973 : plan1973.Valid := valid_step _ _ _ valid973 (by decide +kernel)

theorem valid1974 : plan1974.Valid := valid_step _ _ _ valid974 (by decide +kernel)

theorem valid1975 : plan1975.Valid := valid_step _ _ _ valid975 (by decide +kernel)

theorem valid1976 : plan1976.Valid := valid_step _ _ _ valid976 (by decide +kernel)

theorem valid1977 : plan1977.Valid := valid_step _ _ _ valid977 (by decide +kernel)

theorem valid1978 : plan1978.Valid := valid_step _ _ _ valid978 (by decide +kernel)

theorem valid1979 : plan1979.Valid := valid_step _ _ _ valid979 (by decide +kernel)

theorem valid1980 : plan1980.Valid := valid_step _ _ _ valid980 (by decide +kernel)

theorem valid1981 : plan1981.Valid := valid_step _ _ _ valid990 (by decide +kernel)

theorem valid1982 : plan1982.Valid := valid_step _ _ _ valid997 (by decide +kernel)

theorem valid1983 : plan1983.Valid := valid_step _ _ _ valid998 (by decide +kernel)

theorem valid1984 : plan1984.Valid := valid_step _ _ _ valid999 (by decide +kernel)

theorem valid1985 : plan1985.Valid := valid_step _ _ _ valid1006 (by decide +kernel)

theorem valid1986 : plan1986.Valid := valid_step _ _ _ valid1007 (by decide +kernel)

theorem valid1987 : plan1987.Valid := valid_step _ _ _ valid1013 (by decide +kernel)

theorem valid1988 : plan1988.Valid := valid_step _ _ _ valid1021 (by decide +kernel)

theorem valid1989 : plan1989.Valid := valid_step _ _ _ valid1027 (by decide +kernel)

theorem valid1990 : plan1990.Valid := valid_step _ _ _ valid1028 (by decide +kernel)

theorem valid1991 : plan1991.Valid := valid_step _ _ _ valid1034 (by decide +kernel)


















































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











































































































































theorem valid2182 : plan2182.Valid := valid_step _ _ _ valid1167 (by decide +kernel)

theorem valid2183 : plan2183.Valid := valid_step _ _ _ valid1168 (by decide +kernel)

theorem valid2184 : plan2184.Valid := valid_step _ _ _ valid1169 (by decide +kernel)

theorem valid2185 : plan2185.Valid := valid_step _ _ _ valid1170 (by decide +kernel)

theorem valid2186 : plan2186.Valid := valid_step _ _ _ valid1171 (by decide +kernel)

theorem valid2187 : plan2187.Valid := valid_step _ _ _ valid1172 (by decide +kernel)

theorem valid2188 : plan2188.Valid := valid_step _ _ _ valid1120 (by decide +kernel)

theorem valid2189 : plan2189.Valid := valid_step _ _ _ valid1121 (by decide +kernel)

theorem valid2190 : plan2190.Valid := valid_step _ _ _ valid1122 (by decide +kernel)

theorem valid2191 : plan2191.Valid := valid_step _ _ _ valid1123 (by decide +kernel)

theorem valid2192 : plan2192.Valid := valid_step _ _ _ valid1124 (by decide +kernel)

theorem valid2193 : plan2193.Valid := valid_step _ _ _ valid1125 (by decide +kernel)

theorem valid2194 : plan2194.Valid := valid_step _ _ _ valid1126 (by decide +kernel)

theorem valid2195 : plan2195.Valid := valid_step _ _ _ valid1170 (by decide +kernel)

theorem valid2196 : plan2196.Valid := valid_step _ _ _ valid1171 (by decide +kernel)

theorem valid2197 : plan2197.Valid := valid_step _ _ _ valid1172 (by decide +kernel)

theorem valid2198 : plan2198.Valid := valid_step _ _ _ valid1046 (by decide +kernel)

theorem valid2199 : plan2199.Valid := valid_step _ _ _ valid1047 (by decide +kernel)

theorem valid2200 : plan2200.Valid := valid_step _ _ _ valid1048 (by decide +kernel)

theorem valid2201 : plan2201.Valid := valid_step _ _ _ valid1049 (by decide +kernel)

theorem valid2202 : plan2202.Valid := valid_step _ _ _ valid1050 (by decide +kernel)

theorem valid2203 : plan2203.Valid := valid_step _ _ _ valid1051 (by decide +kernel)

theorem valid2204 : plan2204.Valid := valid_step _ _ _ valid1052 (by decide +kernel)

theorem valid2205 : plan2205.Valid := valid_step _ _ _ valid1053 (by decide +kernel)

theorem valid2206 : plan2206.Valid := valid_step _ _ _ valid1054 (by decide +kernel)

theorem valid2207 : plan2207.Valid := valid_step _ _ _ valid1055 (by decide +kernel)

theorem valid2208 : plan2208.Valid := valid_step _ _ _ valid1056 (by decide +kernel)
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

theorem valid2209 : plan2209.Valid := valid_step _ _ _ valid1057 (by decide +kernel)

theorem valid2210 : plan2210.Valid := valid_step _ _ _ valid1058 (by decide +kernel)

theorem valid2211 : plan2211.Valid := valid_step _ _ _ valid1059 (by decide +kernel)

theorem valid2212 : plan2212.Valid := valid_step _ _ _ valid1060 (by decide +kernel)

theorem valid2213 : plan2213.Valid := valid_step _ _ _ valid1061 (by decide +kernel)

theorem valid2214 : plan2214.Valid := valid_step _ _ _ valid1062 (by decide +kernel)

theorem valid2215 : plan2215.Valid := valid_step _ _ _ valid1063 (by decide +kernel)

theorem valid2216 : plan2216.Valid := valid_step _ _ _ valid1064 (by decide +kernel)

theorem valid2217 : plan2217.Valid := valid_step _ _ _ valid1065 (by decide +kernel)

theorem valid2218 : plan2218.Valid := valid_step _ _ _ valid1066 (by decide +kernel)

theorem valid2219 : plan2219.Valid := valid_step _ _ _ valid1067 (by decide +kernel)

theorem valid2220 : plan2220.Valid := valid_step _ _ _ valid1068 (by decide +kernel)

theorem valid2221 : plan2221.Valid := valid_step _ _ _ valid1069 (by decide +kernel)

theorem valid2222 : plan2222.Valid := valid_step _ _ _ valid1070 (by decide +kernel)

theorem valid2223 : plan2223.Valid := valid_step _ _ _ valid1071 (by decide +kernel)

theorem valid2224 : plan2224.Valid := valid_step _ _ _ valid1072 (by decide +kernel)

theorem valid2225 : plan2225.Valid := valid_step _ _ _ valid1073 (by decide +kernel)

theorem valid2226 : plan2226.Valid := valid_step _ _ _ valid1074 (by decide +kernel)

theorem valid2227 : plan2227.Valid := valid_step _ _ _ valid1075 (by decide +kernel)

theorem valid2228 : plan2228.Valid := valid_step _ _ _ valid1079 (by decide +kernel)

theorem valid2229 : plan2229.Valid := valid_step _ _ _ valid1089 (by decide +kernel)

theorem valid2230 : plan2230.Valid := valid_step _ _ _ valid1093 (by decide +kernel)

theorem valid2231 : plan2231.Valid := valid_step _ _ _ valid1100 (by decide +kernel)

theorem valid2232 : plan2232.Valid := valid_step _ _ _ valid1101 (by decide +kernel)

theorem valid2233 : plan2233.Valid := valid_step _ _ _ valid1102 (by decide +kernel)

theorem valid2234 : plan2234.Valid := valid_step _ _ _ valid1103 (by decide +kernel)

theorem valid2235 : plan2235.Valid := valid_step _ _ _ valid1113 (by decide +kernel)

theorem valid2236 : plan2236.Valid := valid_step _ _ _ valid1127 (by decide +kernel)

theorem valid2237 : plan2237.Valid := valid_step _ _ _ valid1128 (by decide +kernel)

theorem valid2238 : plan2238.Valid := valid_step _ _ _ valid1129 (by decide +kernel)

theorem valid2239 : plan2239.Valid := valid_step _ _ _ valid1130 (by decide +kernel)

theorem valid2240 : plan2240.Valid := valid_step _ _ _ valid1131 (by decide +kernel)

theorem valid2241 : plan2241.Valid := valid_step _ _ _ valid1132 (by decide +kernel)






























































































































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

























theorem valid2317 : plan2317.Valid := valid_step _ _ _ valid1173 (by decide +kernel)

theorem valid2318 : plan2318.Valid := valid_step _ _ _ valid1174 (by decide +kernel)

theorem valid2319 : plan2319.Valid := valid_step _ _ _ valid1175 (by decide +kernel)

theorem valid2320 : plan2320.Valid := valid_step _ _ _ valid1176 (by decide +kernel)

theorem valid2321 : plan2321.Valid := valid_step _ _ _ valid1177 (by decide +kernel)

theorem valid2322 : plan2322.Valid := valid_step _ _ _ valid1178 (by decide +kernel)

theorem valid2323 : plan2323.Valid := valid_step _ _ _ valid1179 (by decide +kernel)

theorem valid2324 : plan2324.Valid := valid_step _ _ _ valid1180 (by decide +kernel)

theorem valid2325 : plan2325.Valid := valid_step _ _ _ valid1181 (by decide +kernel)

theorem valid2326 : plan2326.Valid := valid_step _ _ _ valid1182 (by decide +kernel)

theorem valid2327 : plan2327.Valid := valid_step _ _ _ valid1183 (by decide +kernel)

theorem valid2328 : plan2328.Valid := valid_step _ _ _ valid1184 (by decide +kernel)

theorem valid2329 : plan2329.Valid := valid_step _ _ _ valid1185 (by decide +kernel)

theorem valid2330 : plan2330.Valid := valid_step _ _ _ valid1186 (by decide +kernel)

theorem valid2331 : plan2331.Valid := valid_step _ _ _ valid1187 (by decide +kernel)

theorem valid2332 : plan2332.Valid := valid_step _ _ _ valid1188 (by decide +kernel)

theorem valid2333 : plan2333.Valid := valid_step _ _ _ valid1189 (by decide +kernel)

theorem valid2334 : plan2334.Valid := valid_step _ _ _ valid1190 (by decide +kernel)

theorem valid2335 : plan2335.Valid := valid_step _ _ _ valid1191 (by decide +kernel)

theorem valid2336 : plan2336.Valid := valid_step _ _ _ valid1192 (by decide +kernel)

theorem valid2337 : plan2337.Valid := valid_step _ _ _ valid1193 (by decide +kernel)

theorem valid2338 : plan2338.Valid := valid_step _ _ _ valid1194 (by decide +kernel)

theorem valid2339 : plan2339.Valid := valid_step _ _ _ valid1195 (by decide +kernel)

theorem valid2340 : plan2340.Valid := valid_step _ _ _ valid1196 (by decide +kernel)

theorem valid2341 : plan2341.Valid := valid_step _ _ _ valid1197 (by decide +kernel)

theorem valid2342 : plan2342.Valid := valid_step _ _ _ valid1198 (by decide +kernel)

theorem valid2343 : plan2343.Valid := valid_step _ _ _ valid1199 (by decide +kernel)

theorem valid2344 : plan2344.Valid := valid_step _ _ _ valid1200 (by decide +kernel)

theorem valid2345 : plan2345.Valid := valid_step _ _ _ valid1201 (by decide +kernel)

theorem valid2346 : plan2346.Valid := valid_step _ _ _ valid1202 (by decide +kernel)

theorem valid2347 : plan2347.Valid := valid_step _ _ _ valid1203 (by decide +kernel)

theorem valid2348 : plan2348.Valid := valid_step _ _ _ valid1204 (by decide +kernel)

theorem valid2349 : plan2349.Valid := valid_step _ _ _ valid1205 (by decide +kernel)

theorem valid2350 : plan2350.Valid := valid_step _ _ _ valid1206 (by decide +kernel)

theorem valid2351 : plan2351.Valid := valid_step _ _ _ valid1207 (by decide +kernel)

theorem valid2352 : plan2352.Valid := valid_step _ _ _ valid1208 (by decide +kernel)

theorem valid2353 : plan2353.Valid := valid_step _ _ _ valid1209 (by decide +kernel)

theorem valid2354 : plan2354.Valid := valid_step _ _ _ valid1210 (by decide +kernel)

theorem valid2355 : plan2355.Valid := valid_step _ _ _ valid1211 (by decide +kernel)

theorem valid2356 : plan2356.Valid := valid_step _ _ _ valid1212 (by decide +kernel)

theorem valid2357 : plan2357.Valid := valid_step _ _ _ valid1213 (by decide +kernel)

theorem valid2358 : plan2358.Valid := valid_step _ _ _ valid1214 (by decide +kernel)

theorem valid2359 : plan2359.Valid := valid_step _ _ _ valid1215 (by decide +kernel)


















































































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
theorem t4_420choices : plan2182.choices=[2,9,9,10].map (options 4 3) := by rfl


theorem t4_420part0 : t4_420jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_420frontier : t4_420root.frontier 0=t4_420jobs := by rfl
theorem t4_420all : t4_420jobs.all (Job.check tree)=true := by
  simp only [t4_420jobs,List.all_append,List.all_nil,t4_420part0,Bool.and_self]
theorem t4_420checked : Checked tree [2,9,9,10] := by
  refine ⟨plan2182,valid2182,t4_420choices,?_⟩
  exact check_of_frontier tree 0 t4_420root t4_420jobs t4_420frontier t4_420all
theorem t4_421choices : plan2183.choices=[2,9,10,7].map (options 4 3) := by rfl


theorem t4_421part0 : t4_421jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_421frontier : t4_421root.frontier 0=t4_421jobs := by rfl
theorem t4_421all : t4_421jobs.all (Job.check tree)=true := by
  simp only [t4_421jobs,List.all_append,List.all_nil,t4_421part0,Bool.and_self]
theorem t4_421checked : Checked tree [2,9,10,7] := by
  refine ⟨plan2183,valid2183,t4_421choices,?_⟩
  exact check_of_frontier tree 0 t4_421root t4_421jobs t4_421frontier t4_421all
theorem t4_422choices : plan2184.choices=[2,9,10,10].map (options 4 3) := by rfl


theorem t4_422part0 : t4_422jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_422frontier : t4_422root.frontier 0=t4_422jobs := by rfl
theorem t4_422all : t4_422jobs.all (Job.check tree)=true := by
  simp only [t4_422jobs,List.all_append,List.all_nil,t4_422part0,Bool.and_self]
theorem t4_422checked : Checked tree [2,9,10,10] := by
  refine ⟨plan2184,valid2184,t4_422choices,?_⟩
  exact check_of_frontier tree 0 t4_422root t4_422jobs t4_422frontier t4_422all
theorem t4_423choices : plan2185.choices=[2,10,7,7].map (options 4 3) := by rfl


theorem t4_423part0 : t4_423jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_423frontier : t4_423root.frontier 0=t4_423jobs := by rfl
theorem t4_423all : t4_423jobs.all (Job.check tree)=true := by
  simp only [t4_423jobs,List.all_append,List.all_nil,t4_423part0,Bool.and_self]
theorem t4_423checked : Checked tree [2,10,7,7] := by
  refine ⟨plan2185,valid2185,t4_423choices,?_⟩
  exact check_of_frontier tree 0 t4_423root t4_423jobs t4_423frontier t4_423all
theorem t4_424choices : plan2186.choices=[2,10,10,7].map (options 4 3) := by rfl


theorem t4_424part0 : t4_424jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_424frontier : t4_424root.frontier 0=t4_424jobs := by rfl
theorem t4_424all : t4_424jobs.all (Job.check tree)=true := by
  simp only [t4_424jobs,List.all_append,List.all_nil,t4_424part0,Bool.and_self]
theorem t4_424checked : Checked tree [2,10,10,7] := by
  refine ⟨plan2186,valid2186,t4_424choices,?_⟩
  exact check_of_frontier tree 0 t4_424root t4_424jobs t4_424frontier t4_424all
theorem t4_425choices : plan2187.choices=[2,10,10,10].map (options 4 3) := by rfl


theorem t4_425part0 : t4_425jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_425frontier : t4_425root.frontier 0=t4_425jobs := by rfl
theorem t4_425all : t4_425jobs.all (Job.check tree)=true := by
  simp only [t4_425jobs,List.all_append,List.all_nil,t4_425part0,Bool.and_self]
theorem t4_425checked : Checked tree [2,10,10,10] := by
  refine ⟨plan2187,valid2187,t4_425choices,?_⟩
  exact check_of_frontier tree 0 t4_425root t4_425jobs t4_425frontier t4_425all
theorem t4_426choices : plan1712.choices=[3,3,3,3].map (options 4 0) := by rfl


theorem t4_426part0 : t4_426jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_426frontier : t4_426root.frontier 0=t4_426jobs := by rfl
theorem t4_426all : t4_426jobs.all (Job.check tree)=true := by
  simp only [t4_426jobs,List.all_append,List.all_nil,t4_426part0,Bool.and_self]
theorem t4_426checked : Checked tree [3,3,3,3] := by
  refine ⟨plan1712,valid1712,t4_426choices,?_⟩
  exact check_of_frontier tree 0 t4_426root t4_426jobs t4_426frontier t4_426all
theorem t4_427choices : plan1791.choices=[3,3,3,6].map (options 4 1) := by rfl


theorem t4_427part0 : t4_427jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_427frontier : t4_427root.frontier 0=t4_427jobs := by rfl
theorem t4_427all : t4_427jobs.all (Job.check tree)=true := by
  simp only [t4_427jobs,List.all_append,List.all_nil,t4_427part0,Bool.and_self]
theorem t4_427checked : Checked tree [3,3,3,6] := by
  refine ⟨plan1791,valid1791,t4_427choices,?_⟩
  exact check_of_frontier tree 0 t4_427root t4_427jobs t4_427frontier t4_427all
theorem t4_428choices : plan1792.choices=[3,3,3,7].map (options 4 1) := by rfl


theorem t4_428part0 : t4_428jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_428frontier : t4_428root.frontier 0=t4_428jobs := by rfl
theorem t4_428all : t4_428jobs.all (Job.check tree)=true := by
  simp only [t4_428jobs,List.all_append,List.all_nil,t4_428part0,Bool.and_self]
theorem t4_428checked : Checked tree [3,3,3,7] := by
  refine ⟨plan1792,valid1792,t4_428choices,?_⟩
  exact check_of_frontier tree 0 t4_428root t4_428jobs t4_428frontier t4_428all
theorem t4_429choices : plan1793.choices=[3,3,3,10].map (options 4 1) := by rfl


theorem t4_429part0 : t4_429jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_429frontier : t4_429root.frontier 0=t4_429jobs := by rfl
theorem t4_429all : t4_429jobs.all (Job.check tree)=true := by
  simp only [t4_429jobs,List.all_append,List.all_nil,t4_429part0,Bool.and_self]
theorem t4_429checked : Checked tree [3,3,3,10] := by
  refine ⟨plan1793,valid1793,t4_429choices,?_⟩
  exact check_of_frontier tree 0 t4_429root t4_429jobs t4_429frontier t4_429all
theorem t4_430choices : plan1966.choices=[3,3,6,6].map (options 4 2) := by rfl


theorem t4_430part0 : t4_430jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_430frontier : t4_430root.frontier 0=t4_430jobs := by rfl
theorem t4_430all : t4_430jobs.all (Job.check tree)=true := by
  simp only [t4_430jobs,List.all_append,List.all_nil,t4_430part0,Bool.and_self]
theorem t4_430checked : Checked tree [3,3,6,6] := by
  refine ⟨plan1966,valid1966,t4_430choices,?_⟩
  exact check_of_frontier tree 0 t4_430root t4_430jobs t4_430frontier t4_430all
theorem t4_431choices : plan1967.choices=[3,3,6,7].map (options 4 2) := by rfl


theorem t4_431part0 : t4_431jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_431frontier : t4_431root.frontier 0=t4_431jobs := by rfl
theorem t4_431all : t4_431jobs.all (Job.check tree)=true := by
  simp only [t4_431jobs,List.all_append,List.all_nil,t4_431part0,Bool.and_self]
theorem t4_431checked : Checked tree [3,3,6,7] := by
  refine ⟨plan1967,valid1967,t4_431choices,?_⟩
  exact check_of_frontier tree 0 t4_431root t4_431jobs t4_431frontier t4_431all
theorem t4_432choices : plan1968.choices=[3,3,6,10].map (options 4 2) := by rfl


theorem t4_432part0 : t4_432jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_432frontier : t4_432root.frontier 0=t4_432jobs := by rfl
theorem t4_432all : t4_432jobs.all (Job.check tree)=true := by
  simp only [t4_432jobs,List.all_append,List.all_nil,t4_432part0,Bool.and_self]
theorem t4_432checked : Checked tree [3,3,6,10] := by
  refine ⟨plan1968,valid1968,t4_432choices,?_⟩
  exact check_of_frontier tree 0 t4_432root t4_432jobs t4_432frontier t4_432all
theorem t4_433choices : plan1969.choices=[3,3,7,7].map (options 4 2) := by rfl


theorem t4_433part0 : t4_433jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_433frontier : t4_433root.frontier 0=t4_433jobs := by rfl
theorem t4_433all : t4_433jobs.all (Job.check tree)=true := by
  simp only [t4_433jobs,List.all_append,List.all_nil,t4_433part0,Bool.and_self]
theorem t4_433checked : Checked tree [3,3,7,7] := by
  refine ⟨plan1969,valid1969,t4_433choices,?_⟩
  exact check_of_frontier tree 0 t4_433root t4_433jobs t4_433frontier t4_433all
theorem t4_434choices : plan1970.choices=[3,3,10,7].map (options 4 2) := by rfl


theorem t4_434part0 : t4_434jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_434frontier : t4_434root.frontier 0=t4_434jobs := by rfl
theorem t4_434all : t4_434jobs.all (Job.check tree)=true := by
  simp only [t4_434jobs,List.all_append,List.all_nil,t4_434part0,Bool.and_self]
theorem t4_434checked : Checked tree [3,3,10,7] := by
  refine ⟨plan1970,valid1970,t4_434choices,?_⟩
  exact check_of_frontier tree 0 t4_434root t4_434jobs t4_434frontier t4_434all
theorem t4_435choices : plan1971.choices=[3,3,10,10].map (options 4 2) := by rfl


theorem t4_435part0 : t4_435jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_435frontier : t4_435root.frontier 0=t4_435jobs := by rfl
theorem t4_435all : t4_435jobs.all (Job.check tree)=true := by
  simp only [t4_435jobs,List.all_append,List.all_nil,t4_435part0,Bool.and_self]
theorem t4_435checked : Checked tree [3,3,10,10] := by
  refine ⟨plan1971,valid1971,t4_435choices,?_⟩
  exact check_of_frontier tree 0 t4_435root t4_435jobs t4_435frontier t4_435all
theorem t4_436choices : plan2188.choices=[3,6,6,6].map (options 4 3) := by rfl


theorem t4_436part0 : t4_436jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_436frontier : t4_436root.frontier 0=t4_436jobs := by rfl
theorem t4_436all : t4_436jobs.all (Job.check tree)=true := by
  simp only [t4_436jobs,List.all_append,List.all_nil,t4_436part0,Bool.and_self]
theorem t4_436checked : Checked tree [3,6,6,6] := by
  refine ⟨plan2188,valid2188,t4_436choices,?_⟩
  exact check_of_frontier tree 0 t4_436root t4_436jobs t4_436frontier t4_436all
theorem t4_437choices : plan2189.choices=[3,6,6,7].map (options 4 3) := by rfl


theorem t4_437part0 : t4_437jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_437frontier : t4_437root.frontier 0=t4_437jobs := by rfl
theorem t4_437all : t4_437jobs.all (Job.check tree)=true := by
  simp only [t4_437jobs,List.all_append,List.all_nil,t4_437part0,Bool.and_self]
theorem t4_437checked : Checked tree [3,6,6,7] := by
  refine ⟨plan2189,valid2189,t4_437choices,?_⟩
  exact check_of_frontier tree 0 t4_437root t4_437jobs t4_437frontier t4_437all
theorem t4_438choices : plan2190.choices=[3,6,6,10].map (options 4 3) := by rfl


theorem t4_438part0 : t4_438jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_438frontier : t4_438root.frontier 0=t4_438jobs := by rfl
theorem t4_438all : t4_438jobs.all (Job.check tree)=true := by
  simp only [t4_438jobs,List.all_append,List.all_nil,t4_438part0,Bool.and_self]
theorem t4_438checked : Checked tree [3,6,6,10] := by
  refine ⟨plan2190,valid2190,t4_438choices,?_⟩
  exact check_of_frontier tree 0 t4_438root t4_438jobs t4_438frontier t4_438all
theorem t4_439choices : plan2191.choices=[3,6,7,7].map (options 4 3) := by rfl


theorem t4_439part0 : t4_439jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_439frontier : t4_439root.frontier 0=t4_439jobs := by rfl
theorem t4_439all : t4_439jobs.all (Job.check tree)=true := by
  simp only [t4_439jobs,List.all_append,List.all_nil,t4_439part0,Bool.and_self]
theorem t4_439checked : Checked tree [3,6,7,7] := by
  refine ⟨plan2191,valid2191,t4_439choices,?_⟩
  exact check_of_frontier tree 0 t4_439root t4_439jobs t4_439frontier t4_439all
theorem t4_440choices : plan2192.choices=[3,6,10,7].map (options 4 3) := by rfl


theorem t4_440part0 : t4_440jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_440frontier : t4_440root.frontier 0=t4_440jobs := by rfl
theorem t4_440all : t4_440jobs.all (Job.check tree)=true := by
  simp only [t4_440jobs,List.all_append,List.all_nil,t4_440part0,Bool.and_self]
theorem t4_440checked : Checked tree [3,6,10,7] := by
  refine ⟨plan2192,valid2192,t4_440choices,?_⟩
  exact check_of_frontier tree 0 t4_440root t4_440jobs t4_440frontier t4_440all
theorem t4_441choices : plan2193.choices=[3,6,10,10].map (options 4 3) := by rfl


theorem t4_441part0 : t4_441jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_441frontier : t4_441root.frontier 0=t4_441jobs := by rfl
theorem t4_441all : t4_441jobs.all (Job.check tree)=true := by
  simp only [t4_441jobs,List.all_append,List.all_nil,t4_441part0,Bool.and_self]
theorem t4_441checked : Checked tree [3,6,10,10] := by
  refine ⟨plan2193,valid2193,t4_441choices,?_⟩
  exact check_of_frontier tree 0 t4_441root t4_441jobs t4_441frontier t4_441all
theorem t4_442choices : plan2194.choices=[3,7,7,7].map (options 4 3) := by rfl


theorem t4_442part0 : t4_442jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_442frontier : t4_442root.frontier 0=t4_442jobs := by rfl
theorem t4_442all : t4_442jobs.all (Job.check tree)=true := by
  simp only [t4_442jobs,List.all_append,List.all_nil,t4_442part0,Bool.and_self]
theorem t4_442checked : Checked tree [3,7,7,7] := by
  refine ⟨plan2194,valid2194,t4_442choices,?_⟩
  exact check_of_frontier tree 0 t4_442root t4_442jobs t4_442frontier t4_442all
theorem t4_443choices : plan2195.choices=[3,10,7,7].map (options 4 3) := by rfl


theorem t4_443part0 : t4_443jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_443frontier : t4_443root.frontier 0=t4_443jobs := by rfl
theorem t4_443all : t4_443jobs.all (Job.check tree)=true := by
  simp only [t4_443jobs,List.all_append,List.all_nil,t4_443part0,Bool.and_self]
theorem t4_443checked : Checked tree [3,10,7,7] := by
  refine ⟨plan2195,valid2195,t4_443choices,?_⟩
  exact check_of_frontier tree 0 t4_443root t4_443jobs t4_443frontier t4_443all
theorem t4_444choices : plan2196.choices=[3,10,10,7].map (options 4 3) := by rfl


theorem t4_444part0 : t4_444jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_444frontier : t4_444root.frontier 0=t4_444jobs := by rfl
theorem t4_444all : t4_444jobs.all (Job.check tree)=true := by
  simp only [t4_444jobs,List.all_append,List.all_nil,t4_444part0,Bool.and_self]
theorem t4_444checked : Checked tree [3,10,10,7] := by
  refine ⟨plan2196,valid2196,t4_444choices,?_⟩
  exact check_of_frontier tree 0 t4_444root t4_444jobs t4_444frontier t4_444all
theorem t4_445choices : plan2197.choices=[3,10,10,10].map (options 4 3) := by rfl


theorem t4_445part0 : t4_445jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_445frontier : t4_445root.frontier 0=t4_445jobs := by rfl
theorem t4_445all : t4_445jobs.all (Job.check tree)=true := by
  simp only [t4_445jobs,List.all_append,List.all_nil,t4_445part0,Bool.and_self]
theorem t4_445checked : Checked tree [3,10,10,10] := by
  refine ⟨plan2197,valid2197,t4_445choices,?_⟩
  exact check_of_frontier tree 0 t4_445root t4_445jobs t4_445frontier t4_445all
theorem t4_446choices : plan1794.choices=[4,2,2,2].map (options 4 1) := by rfl


theorem t4_446part0 : t4_446jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_446frontier : t4_446root.frontier 0=t4_446jobs := by rfl
theorem t4_446all : t4_446jobs.all (Job.check tree)=true := by
  simp only [t4_446jobs,List.all_append,List.all_nil,t4_446part0,Bool.and_self]
theorem t4_446checked : Checked tree [4,2,2,2] := by
  refine ⟨plan1794,valid1794,t4_446choices,?_⟩
  exact check_of_frontier tree 0 t4_446root t4_446jobs t4_446frontier t4_446all
theorem t4_447choices : plan1795.choices=[4,2,2,3].map (options 4 1) := by rfl


theorem t4_447part0 : t4_447jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_447frontier : t4_447root.frontier 0=t4_447jobs := by rfl
theorem t4_447all : t4_447jobs.all (Job.check tree)=true := by
  simp only [t4_447jobs,List.all_append,List.all_nil,t4_447part0,Bool.and_self]
theorem t4_447checked : Checked tree [4,2,2,3] := by
  refine ⟨plan1795,valid1795,t4_447choices,?_⟩
  exact check_of_frontier tree 0 t4_447root t4_447jobs t4_447frontier t4_447all
theorem t4_448choices : plan1972.choices=[4,2,2,5].map (options 4 2) := by rfl


theorem t4_448part0 : t4_448jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_448frontier : t4_448root.frontier 0=t4_448jobs := by rfl
theorem t4_448all : t4_448jobs.all (Job.check tree)=true := by
  simp only [t4_448jobs,List.all_append,List.all_nil,t4_448part0,Bool.and_self]
theorem t4_448checked : Checked tree [4,2,2,5] := by
  refine ⟨plan1972,valid1972,t4_448choices,?_⟩
  exact check_of_frontier tree 0 t4_448root t4_448jobs t4_448frontier t4_448all
theorem t4_449choices : plan1973.choices=[4,2,2,6].map (options 4 2) := by rfl


theorem t4_449part0 : t4_449jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_449frontier : t4_449root.frontier 0=t4_449jobs := by rfl
theorem t4_449all : t4_449jobs.all (Job.check tree)=true := by
  simp only [t4_449jobs,List.all_append,List.all_nil,t4_449part0,Bool.and_self]
theorem t4_449checked : Checked tree [4,2,2,6] := by
  refine ⟨plan1973,valid1973,t4_449choices,?_⟩
  exact check_of_frontier tree 0 t4_449root t4_449jobs t4_449frontier t4_449all
theorem t4_450choices : plan1974.choices=[4,2,2,7].map (options 4 2) := by rfl


theorem t4_450part0 : t4_450jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_450frontier : t4_450root.frontier 0=t4_450jobs := by rfl
theorem t4_450all : t4_450jobs.all (Job.check tree)=true := by
  simp only [t4_450jobs,List.all_append,List.all_nil,t4_450part0,Bool.and_self]
theorem t4_450checked : Checked tree [4,2,2,7] := by
  refine ⟨plan1974,valid1974,t4_450choices,?_⟩
  exact check_of_frontier tree 0 t4_450root t4_450jobs t4_450frontier t4_450all
theorem t4_451choices : plan1975.choices=[4,2,2,9].map (options 4 2) := by rfl


theorem t4_451part0 : t4_451jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_451frontier : t4_451root.frontier 0=t4_451jobs := by rfl
theorem t4_451all : t4_451jobs.all (Job.check tree)=true := by
  simp only [t4_451jobs,List.all_append,List.all_nil,t4_451part0,Bool.and_self]
theorem t4_451checked : Checked tree [4,2,2,9] := by
  refine ⟨plan1975,valid1975,t4_451choices,?_⟩
  exact check_of_frontier tree 0 t4_451root t4_451jobs t4_451frontier t4_451all
theorem t4_452choices : plan1976.choices=[4,2,2,10].map (options 4 2) := by rfl


theorem t4_452part0 : t4_452jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_452frontier : t4_452root.frontier 0=t4_452jobs := by rfl
theorem t4_452all : t4_452jobs.all (Job.check tree)=true := by
  simp only [t4_452jobs,List.all_append,List.all_nil,t4_452part0,Bool.and_self]
theorem t4_452checked : Checked tree [4,2,2,10] := by
  refine ⟨plan1976,valid1976,t4_452choices,?_⟩
  exact check_of_frontier tree 0 t4_452root t4_452jobs t4_452frontier t4_452all
theorem t4_453choices : plan1796.choices=[4,2,3,3].map (options 4 1) := by rfl


theorem t4_453part0 : t4_453jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_453frontier : t4_453root.frontier 0=t4_453jobs := by rfl
theorem t4_453all : t4_453jobs.all (Job.check tree)=true := by
  simp only [t4_453jobs,List.all_append,List.all_nil,t4_453part0,Bool.and_self]
theorem t4_453checked : Checked tree [4,2,3,3] := by
  refine ⟨plan1796,valid1796,t4_453choices,?_⟩
  exact check_of_frontier tree 0 t4_453root t4_453jobs t4_453frontier t4_453all
theorem t4_454choices : plan1977.choices=[4,2,3,6].map (options 4 2) := by rfl


theorem t4_454part0 : t4_454jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_454frontier : t4_454root.frontier 0=t4_454jobs := by rfl
theorem t4_454all : t4_454jobs.all (Job.check tree)=true := by
  simp only [t4_454jobs,List.all_append,List.all_nil,t4_454part0,Bool.and_self]
theorem t4_454checked : Checked tree [4,2,3,6] := by
  refine ⟨plan1977,valid1977,t4_454choices,?_⟩
  exact check_of_frontier tree 0 t4_454root t4_454jobs t4_454frontier t4_454all
theorem t4_455choices : plan1978.choices=[4,2,3,7].map (options 4 2) := by rfl


theorem t4_455part0 : t4_455jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_455frontier : t4_455root.frontier 0=t4_455jobs := by rfl
theorem t4_455all : t4_455jobs.all (Job.check tree)=true := by
  simp only [t4_455jobs,List.all_append,List.all_nil,t4_455part0,Bool.and_self]
theorem t4_455checked : Checked tree [4,2,3,7] := by
  refine ⟨plan1978,valid1978,t4_455choices,?_⟩
  exact check_of_frontier tree 0 t4_455root t4_455jobs t4_455frontier t4_455all
theorem t4_456choices : plan1979.choices=[4,2,3,10].map (options 4 2) := by rfl


theorem t4_456part0 : t4_456jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_456frontier : t4_456root.frontier 0=t4_456jobs := by rfl
theorem t4_456all : t4_456jobs.all (Job.check tree)=true := by
  simp only [t4_456jobs,List.all_append,List.all_nil,t4_456part0,Bool.and_self]
theorem t4_456checked : Checked tree [4,2,3,10] := by
  refine ⟨plan1979,valid1979,t4_456choices,?_⟩
  exact check_of_frontier tree 0 t4_456root t4_456jobs t4_456frontier t4_456all
theorem t4_457choices : plan1980.choices=[4,2,5,3].map (options 4 2) := by rfl


theorem t4_457part0 : t4_457jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_457frontier : t4_457root.frontier 0=t4_457jobs := by rfl
theorem t4_457all : t4_457jobs.all (Job.check tree)=true := by
  simp only [t4_457jobs,List.all_append,List.all_nil,t4_457part0,Bool.and_self]
theorem t4_457checked : Checked tree [4,2,5,3] := by
  refine ⟨plan1980,valid1980,t4_457choices,?_⟩
  exact check_of_frontier tree 0 t4_457root t4_457jobs t4_457frontier t4_457all
theorem t4_458choices : plan2198.choices=[4,2,5,5].map (options 4 3) := by rfl


theorem t4_458part0 : t4_458jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_458frontier : t4_458root.frontier 0=t4_458jobs := by rfl
theorem t4_458all : t4_458jobs.all (Job.check tree)=true := by
  simp only [t4_458jobs,List.all_append,List.all_nil,t4_458part0,Bool.and_self]
theorem t4_458checked : Checked tree [4,2,5,5] := by
  refine ⟨plan2198,valid2198,t4_458choices,?_⟩
  exact check_of_frontier tree 0 t4_458root t4_458jobs t4_458frontier t4_458all
theorem t4_459choices : plan2199.choices=[4,2,5,6].map (options 4 3) := by rfl


theorem t4_459part0 : t4_459jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_459frontier : t4_459root.frontier 0=t4_459jobs := by rfl
theorem t4_459all : t4_459jobs.all (Job.check tree)=true := by
  simp only [t4_459jobs,List.all_append,List.all_nil,t4_459part0,Bool.and_self]
theorem t4_459checked : Checked tree [4,2,5,6] := by
  refine ⟨plan2199,valid2199,t4_459choices,?_⟩
  exact check_of_frontier tree 0 t4_459root t4_459jobs t4_459frontier t4_459all
theorem t4_460choices : plan2200.choices=[4,2,5,7].map (options 4 3) := by rfl


theorem t4_460part0 : t4_460jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_460frontier : t4_460root.frontier 0=t4_460jobs := by rfl
theorem t4_460all : t4_460jobs.all (Job.check tree)=true := by
  simp only [t4_460jobs,List.all_append,List.all_nil,t4_460part0,Bool.and_self]
theorem t4_460checked : Checked tree [4,2,5,7] := by
  refine ⟨plan2200,valid2200,t4_460choices,?_⟩
  exact check_of_frontier tree 0 t4_460root t4_460jobs t4_460frontier t4_460all
theorem t4_461choices : plan2201.choices=[4,2,5,9].map (options 4 3) := by rfl


theorem t4_461part0 : t4_461jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_461frontier : t4_461root.frontier 0=t4_461jobs := by rfl
theorem t4_461all : t4_461jobs.all (Job.check tree)=true := by
  simp only [t4_461jobs,List.all_append,List.all_nil,t4_461part0,Bool.and_self]
theorem t4_461checked : Checked tree [4,2,5,9] := by
  refine ⟨plan2201,valid2201,t4_461choices,?_⟩
  exact check_of_frontier tree 0 t4_461root t4_461jobs t4_461frontier t4_461all
theorem t4_462choices : plan2202.choices=[4,2,5,10].map (options 4 3) := by rfl


theorem t4_462part0 : t4_462jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_462frontier : t4_462root.frontier 0=t4_462jobs := by rfl
theorem t4_462all : t4_462jobs.all (Job.check tree)=true := by
  simp only [t4_462jobs,List.all_append,List.all_nil,t4_462part0,Bool.and_self]
theorem t4_462checked : Checked tree [4,2,5,10] := by
  refine ⟨plan2202,valid2202,t4_462choices,?_⟩
  exact check_of_frontier tree 0 t4_462root t4_462jobs t4_462frontier t4_462all
theorem t4_463choices : plan2203.choices=[4,2,6,6].map (options 4 3) := by rfl


theorem t4_463part0 : t4_463jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_463frontier : t4_463root.frontier 0=t4_463jobs := by rfl
theorem t4_463all : t4_463jobs.all (Job.check tree)=true := by
  simp only [t4_463jobs,List.all_append,List.all_nil,t4_463part0,Bool.and_self]
theorem t4_463checked : Checked tree [4,2,6,6] := by
  refine ⟨plan2203,valid2203,t4_463choices,?_⟩
  exact check_of_frontier tree 0 t4_463root t4_463jobs t4_463frontier t4_463all
theorem t4_464choices : plan2204.choices=[4,2,6,7].map (options 4 3) := by rfl


theorem t4_464part0 : t4_464jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_464frontier : t4_464root.frontier 0=t4_464jobs := by rfl
theorem t4_464all : t4_464jobs.all (Job.check tree)=true := by
  simp only [t4_464jobs,List.all_append,List.all_nil,t4_464part0,Bool.and_self]
theorem t4_464checked : Checked tree [4,2,6,7] := by
  refine ⟨plan2204,valid2204,t4_464choices,?_⟩
  exact check_of_frontier tree 0 t4_464root t4_464jobs t4_464frontier t4_464all
theorem t4_465choices : plan2205.choices=[4,2,6,10].map (options 4 3) := by rfl


theorem t4_465part0 : t4_465jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_465frontier : t4_465root.frontier 0=t4_465jobs := by rfl
theorem t4_465all : t4_465jobs.all (Job.check tree)=true := by
  simp only [t4_465jobs,List.all_append,List.all_nil,t4_465part0,Bool.and_self]
theorem t4_465checked : Checked tree [4,2,6,10] := by
  refine ⟨plan2205,valid2205,t4_465choices,?_⟩
  exact check_of_frontier tree 0 t4_465root t4_465jobs t4_465frontier t4_465all
theorem t4_466choices : plan2206.choices=[4,2,7,7].map (options 4 3) := by rfl


theorem t4_466part0 : t4_466jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_466frontier : t4_466root.frontier 0=t4_466jobs := by rfl
theorem t4_466all : t4_466jobs.all (Job.check tree)=true := by
  simp only [t4_466jobs,List.all_append,List.all_nil,t4_466part0,Bool.and_self]
theorem t4_466checked : Checked tree [4,2,7,7] := by
  refine ⟨plan2206,valid2206,t4_466choices,?_⟩
  exact check_of_frontier tree 0 t4_466root t4_466jobs t4_466frontier t4_466all
theorem t4_467choices : plan1981.choices=[4,2,9,3].map (options 4 2) := by rfl


theorem t4_467part0 : t4_467jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_467frontier : t4_467root.frontier 0=t4_467jobs := by rfl
theorem t4_467all : t4_467jobs.all (Job.check tree)=true := by
  simp only [t4_467jobs,List.all_append,List.all_nil,t4_467part0,Bool.and_self]
theorem t4_467checked : Checked tree [4,2,9,3] := by
  refine ⟨plan1981,valid1981,t4_467choices,?_⟩
  exact check_of_frontier tree 0 t4_467root t4_467jobs t4_467frontier t4_467all
theorem t4_468choices : plan2207.choices=[4,2,9,6].map (options 4 3) := by rfl


theorem t4_468part0 : t4_468jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_468frontier : t4_468root.frontier 0=t4_468jobs := by rfl
theorem t4_468all : t4_468jobs.all (Job.check tree)=true := by
  simp only [t4_468jobs,List.all_append,List.all_nil,t4_468part0,Bool.and_self]
theorem t4_468checked : Checked tree [4,2,9,6] := by
  refine ⟨plan2207,valid2207,t4_468choices,?_⟩
  exact check_of_frontier tree 0 t4_468root t4_468jobs t4_468frontier t4_468all
theorem t4_469choices : plan2208.choices=[4,2,9,7].map (options 4 3) := by rfl


theorem t4_469part0 : t4_469jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_469frontier : t4_469root.frontier 0=t4_469jobs := by rfl
theorem t4_469all : t4_469jobs.all (Job.check tree)=true := by
  simp only [t4_469jobs,List.all_append,List.all_nil,t4_469part0,Bool.and_self]
theorem t4_469checked : Checked tree [4,2,9,7] := by
  refine ⟨plan2208,valid2208,t4_469choices,?_⟩
  exact check_of_frontier tree 0 t4_469root t4_469jobs t4_469frontier t4_469all
theorem t4_470choices : plan2209.choices=[4,2,9,9].map (options 4 3) := by rfl


theorem t4_470part0 : t4_470jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_470frontier : t4_470root.frontier 0=t4_470jobs := by rfl
theorem t4_470all : t4_470jobs.all (Job.check tree)=true := by
  simp only [t4_470jobs,List.all_append,List.all_nil,t4_470part0,Bool.and_self]
theorem t4_470checked : Checked tree [4,2,9,9] := by
  refine ⟨plan2209,valid2209,t4_470choices,?_⟩
  exact check_of_frontier tree 0 t4_470root t4_470jobs t4_470frontier t4_470all
theorem t4_471choices : plan2210.choices=[4,2,9,10].map (options 4 3) := by rfl


theorem t4_471part0 : t4_471jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_471frontier : t4_471root.frontier 0=t4_471jobs := by rfl
theorem t4_471all : t4_471jobs.all (Job.check tree)=true := by
  simp only [t4_471jobs,List.all_append,List.all_nil,t4_471part0,Bool.and_self]
theorem t4_471checked : Checked tree [4,2,9,10] := by
  refine ⟨plan2210,valid2210,t4_471choices,?_⟩
  exact check_of_frontier tree 0 t4_471root t4_471jobs t4_471frontier t4_471all
theorem t4_472choices : plan2211.choices=[4,2,10,7].map (options 4 3) := by rfl


theorem t4_472part0 : t4_472jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_472frontier : t4_472root.frontier 0=t4_472jobs := by rfl
theorem t4_472all : t4_472jobs.all (Job.check tree)=true := by
  simp only [t4_472jobs,List.all_append,List.all_nil,t4_472part0,Bool.and_self]
theorem t4_472checked : Checked tree [4,2,10,7] := by
  refine ⟨plan2211,valid2211,t4_472choices,?_⟩
  exact check_of_frontier tree 0 t4_472root t4_472jobs t4_472frontier t4_472all
theorem t4_473choices : plan2212.choices=[4,2,10,10].map (options 4 3) := by rfl


theorem t4_473part0 : t4_473jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_473frontier : t4_473root.frontier 0=t4_473jobs := by rfl
theorem t4_473all : t4_473jobs.all (Job.check tree)=true := by
  simp only [t4_473jobs,List.all_append,List.all_nil,t4_473part0,Bool.and_self]
theorem t4_473checked : Checked tree [4,2,10,10] := by
  refine ⟨plan2212,valid2212,t4_473choices,?_⟩
  exact check_of_frontier tree 0 t4_473root t4_473jobs t4_473frontier t4_473all
theorem t4_474choices : plan1797.choices=[4,3,3,3].map (options 4 1) := by rfl


theorem t4_474part0 : t4_474jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_474frontier : t4_474root.frontier 0=t4_474jobs := by rfl
theorem t4_474all : t4_474jobs.all (Job.check tree)=true := by
  simp only [t4_474jobs,List.all_append,List.all_nil,t4_474part0,Bool.and_self]
theorem t4_474checked : Checked tree [4,3,3,3] := by
  refine ⟨plan1797,valid1797,t4_474choices,?_⟩
  exact check_of_frontier tree 0 t4_474root t4_474jobs t4_474frontier t4_474all
theorem t4_475choices : plan1982.choices=[4,3,3,6].map (options 4 2) := by rfl


theorem t4_475part0 : t4_475jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_475frontier : t4_475root.frontier 0=t4_475jobs := by rfl
theorem t4_475all : t4_475jobs.all (Job.check tree)=true := by
  simp only [t4_475jobs,List.all_append,List.all_nil,t4_475part0,Bool.and_self]
theorem t4_475checked : Checked tree [4,3,3,6] := by
  refine ⟨plan1982,valid1982,t4_475choices,?_⟩
  exact check_of_frontier tree 0 t4_475root t4_475jobs t4_475frontier t4_475all
theorem t4_476choices : plan1983.choices=[4,3,3,7].map (options 4 2) := by rfl


theorem t4_476part0 : t4_476jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_476frontier : t4_476root.frontier 0=t4_476jobs := by rfl
theorem t4_476all : t4_476jobs.all (Job.check tree)=true := by
  simp only [t4_476jobs,List.all_append,List.all_nil,t4_476part0,Bool.and_self]
theorem t4_476checked : Checked tree [4,3,3,7] := by
  refine ⟨plan1983,valid1983,t4_476choices,?_⟩
  exact check_of_frontier tree 0 t4_476root t4_476jobs t4_476frontier t4_476all
theorem t4_477choices : plan1984.choices=[4,3,3,10].map (options 4 2) := by rfl


theorem t4_477part0 : t4_477jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_477frontier : t4_477root.frontier 0=t4_477jobs := by rfl
theorem t4_477all : t4_477jobs.all (Job.check tree)=true := by
  simp only [t4_477jobs,List.all_append,List.all_nil,t4_477part0,Bool.and_self]
theorem t4_477checked : Checked tree [4,3,3,10] := by
  refine ⟨plan1984,valid1984,t4_477choices,?_⟩
  exact check_of_frontier tree 0 t4_477root t4_477jobs t4_477frontier t4_477all
theorem t4_478choices : plan2213.choices=[4,3,6,6].map (options 4 3) := by rfl


theorem t4_478part0 : t4_478jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_478frontier : t4_478root.frontier 0=t4_478jobs := by rfl
theorem t4_478all : t4_478jobs.all (Job.check tree)=true := by
  simp only [t4_478jobs,List.all_append,List.all_nil,t4_478part0,Bool.and_self]
theorem t4_478checked : Checked tree [4,3,6,6] := by
  refine ⟨plan2213,valid2213,t4_478choices,?_⟩
  exact check_of_frontier tree 0 t4_478root t4_478jobs t4_478frontier t4_478all
theorem t4_479choices : plan2214.choices=[4,3,6,7].map (options 4 3) := by rfl


theorem t4_479part0 : t4_479jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_479frontier : t4_479root.frontier 0=t4_479jobs := by rfl
theorem t4_479all : t4_479jobs.all (Job.check tree)=true := by
  simp only [t4_479jobs,List.all_append,List.all_nil,t4_479part0,Bool.and_self]
theorem t4_479checked : Checked tree [4,3,6,7] := by
  refine ⟨plan2214,valid2214,t4_479choices,?_⟩
  exact check_of_frontier tree 0 t4_479root t4_479jobs t4_479frontier t4_479all
theorem t4_480choices : plan2215.choices=[4,3,6,10].map (options 4 3) := by rfl


theorem t4_480part0 : t4_480jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_480frontier : t4_480root.frontier 0=t4_480jobs := by rfl
theorem t4_480all : t4_480jobs.all (Job.check tree)=true := by
  simp only [t4_480jobs,List.all_append,List.all_nil,t4_480part0,Bool.and_self]
theorem t4_480checked : Checked tree [4,3,6,10] := by
  refine ⟨plan2215,valid2215,t4_480choices,?_⟩
  exact check_of_frontier tree 0 t4_480root t4_480jobs t4_480frontier t4_480all
theorem t4_481choices : plan2216.choices=[4,3,7,7].map (options 4 3) := by rfl


theorem t4_481part0 : t4_481jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_481frontier : t4_481root.frontier 0=t4_481jobs := by rfl
theorem t4_481all : t4_481jobs.all (Job.check tree)=true := by
  simp only [t4_481jobs,List.all_append,List.all_nil,t4_481part0,Bool.and_self]
theorem t4_481checked : Checked tree [4,3,7,7] := by
  refine ⟨plan2216,valid2216,t4_481choices,?_⟩
  exact check_of_frontier tree 0 t4_481root t4_481jobs t4_481frontier t4_481all
theorem t4_482choices : plan2217.choices=[4,3,10,7].map (options 4 3) := by rfl


theorem t4_482part0 : t4_482jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_482frontier : t4_482root.frontier 0=t4_482jobs := by rfl
theorem t4_482all : t4_482jobs.all (Job.check tree)=true := by
  simp only [t4_482jobs,List.all_append,List.all_nil,t4_482part0,Bool.and_self]
theorem t4_482checked : Checked tree [4,3,10,7] := by
  refine ⟨plan2217,valid2217,t4_482choices,?_⟩
  exact check_of_frontier tree 0 t4_482root t4_482jobs t4_482frontier t4_482all
theorem t4_483choices : plan2218.choices=[4,3,10,10].map (options 4 3) := by rfl


theorem t4_483part0 : t4_483jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_483frontier : t4_483root.frontier 0=t4_483jobs := by rfl
theorem t4_483all : t4_483jobs.all (Job.check tree)=true := by
  simp only [t4_483jobs,List.all_append,List.all_nil,t4_483part0,Bool.and_self]
theorem t4_483checked : Checked tree [4,3,10,10] := by
  refine ⟨plan2218,valid2218,t4_483choices,?_⟩
  exact check_of_frontier tree 0 t4_483root t4_483jobs t4_483frontier t4_483all
theorem t4_484choices : plan1985.choices=[4,4,2,2].map (options 4 2) := by rfl


theorem t4_484part0 : t4_484jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_484frontier : t4_484root.frontier 0=t4_484jobs := by rfl
theorem t4_484all : t4_484jobs.all (Job.check tree)=true := by
  simp only [t4_484jobs,List.all_append,List.all_nil,t4_484part0,Bool.and_self]
theorem t4_484checked : Checked tree [4,4,2,2] := by
  refine ⟨plan1985,valid1985,t4_484choices,?_⟩
  exact check_of_frontier tree 0 t4_484root t4_484jobs t4_484frontier t4_484all
theorem t4_485choices : plan1986.choices=[4,4,2,3].map (options 4 2) := by rfl


theorem t4_485part0 : t4_485jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_485frontier : t4_485root.frontier 0=t4_485jobs := by rfl
theorem t4_485all : t4_485jobs.all (Job.check tree)=true := by
  simp only [t4_485jobs,List.all_append,List.all_nil,t4_485part0,Bool.and_self]
theorem t4_485checked : Checked tree [4,4,2,3] := by
  refine ⟨plan1986,valid1986,t4_485choices,?_⟩
  exact check_of_frontier tree 0 t4_485root t4_485jobs t4_485frontier t4_485all
theorem t4_486choices : plan2219.choices=[4,4,2,5].map (options 4 3) := by rfl


theorem t4_486part0 : t4_486jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_486frontier : t4_486root.frontier 0=t4_486jobs := by rfl
theorem t4_486all : t4_486jobs.all (Job.check tree)=true := by
  simp only [t4_486jobs,List.all_append,List.all_nil,t4_486part0,Bool.and_self]
theorem t4_486checked : Checked tree [4,4,2,5] := by
  refine ⟨plan2219,valid2219,t4_486choices,?_⟩
  exact check_of_frontier tree 0 t4_486root t4_486jobs t4_486frontier t4_486all
theorem t4_487choices : plan2220.choices=[4,4,2,6].map (options 4 3) := by rfl


theorem t4_487part0 : t4_487jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_487frontier : t4_487root.frontier 0=t4_487jobs := by rfl
theorem t4_487all : t4_487jobs.all (Job.check tree)=true := by
  simp only [t4_487jobs,List.all_append,List.all_nil,t4_487part0,Bool.and_self]
theorem t4_487checked : Checked tree [4,4,2,6] := by
  refine ⟨plan2220,valid2220,t4_487choices,?_⟩
  exact check_of_frontier tree 0 t4_487root t4_487jobs t4_487frontier t4_487all
theorem t4_488choices : plan2221.choices=[4,4,2,7].map (options 4 3) := by rfl


theorem t4_488part0 : t4_488jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_488frontier : t4_488root.frontier 0=t4_488jobs := by rfl
theorem t4_488all : t4_488jobs.all (Job.check tree)=true := by
  simp only [t4_488jobs,List.all_append,List.all_nil,t4_488part0,Bool.and_self]
theorem t4_488checked : Checked tree [4,4,2,7] := by
  refine ⟨plan2221,valid2221,t4_488choices,?_⟩
  exact check_of_frontier tree 0 t4_488root t4_488jobs t4_488frontier t4_488all
theorem t4_489choices : plan2222.choices=[4,4,2,9].map (options 4 3) := by rfl


theorem t4_489part0 : t4_489jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_489frontier : t4_489root.frontier 0=t4_489jobs := by rfl
theorem t4_489all : t4_489jobs.all (Job.check tree)=true := by
  simp only [t4_489jobs,List.all_append,List.all_nil,t4_489part0,Bool.and_self]
theorem t4_489checked : Checked tree [4,4,2,9] := by
  refine ⟨plan2222,valid2222,t4_489choices,?_⟩
  exact check_of_frontier tree 0 t4_489root t4_489jobs t4_489frontier t4_489all
theorem t4_490choices : plan2223.choices=[4,4,2,10].map (options 4 3) := by rfl


theorem t4_490part0 : t4_490jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_490frontier : t4_490root.frontier 0=t4_490jobs := by rfl
theorem t4_490all : t4_490jobs.all (Job.check tree)=true := by
  simp only [t4_490jobs,List.all_append,List.all_nil,t4_490part0,Bool.and_self]
theorem t4_490checked : Checked tree [4,4,2,10] := by
  refine ⟨plan2223,valid2223,t4_490choices,?_⟩
  exact check_of_frontier tree 0 t4_490root t4_490jobs t4_490frontier t4_490all
theorem t4_491choices : plan1987.choices=[4,4,3,3].map (options 4 2) := by rfl


theorem t4_491part0 : t4_491jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_491frontier : t4_491root.frontier 0=t4_491jobs := by rfl
theorem t4_491all : t4_491jobs.all (Job.check tree)=true := by
  simp only [t4_491jobs,List.all_append,List.all_nil,t4_491part0,Bool.and_self]
theorem t4_491checked : Checked tree [4,4,3,3] := by
  refine ⟨plan1987,valid1987,t4_491choices,?_⟩
  exact check_of_frontier tree 0 t4_491root t4_491jobs t4_491frontier t4_491all
theorem t4_492choices : plan2224.choices=[4,4,3,6].map (options 4 3) := by rfl


theorem t4_492part0 : t4_492jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_492frontier : t4_492root.frontier 0=t4_492jobs := by rfl
theorem t4_492all : t4_492jobs.all (Job.check tree)=true := by
  simp only [t4_492jobs,List.all_append,List.all_nil,t4_492part0,Bool.and_self]
theorem t4_492checked : Checked tree [4,4,3,6] := by
  refine ⟨plan2224,valid2224,t4_492choices,?_⟩
  exact check_of_frontier tree 0 t4_492root t4_492jobs t4_492frontier t4_492all
theorem t4_493choices : plan2225.choices=[4,4,3,7].map (options 4 3) := by rfl


theorem t4_493part0 : t4_493jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_493frontier : t4_493root.frontier 0=t4_493jobs := by rfl
theorem t4_493all : t4_493jobs.all (Job.check tree)=true := by
  simp only [t4_493jobs,List.all_append,List.all_nil,t4_493part0,Bool.and_self]
theorem t4_493checked : Checked tree [4,4,3,7] := by
  refine ⟨plan2225,valid2225,t4_493choices,?_⟩
  exact check_of_frontier tree 0 t4_493root t4_493jobs t4_493frontier t4_493all
theorem t4_494choices : plan2226.choices=[4,4,3,10].map (options 4 3) := by rfl


theorem t4_494part0 : t4_494jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_494frontier : t4_494root.frontier 0=t4_494jobs := by rfl
theorem t4_494all : t4_494jobs.all (Job.check tree)=true := by
  simp only [t4_494jobs,List.all_append,List.all_nil,t4_494part0,Bool.and_self]
theorem t4_494checked : Checked tree [4,4,3,10] := by
  refine ⟨plan2226,valid2226,t4_494choices,?_⟩
  exact check_of_frontier tree 0 t4_494root t4_494jobs t4_494frontier t4_494all
theorem t4_495choices : plan2227.choices=[4,4,4,3].map (options 4 3) := by rfl


theorem t4_495part0 : t4_495jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_495frontier : t4_495root.frontier 0=t4_495jobs := by rfl
theorem t4_495all : t4_495jobs.all (Job.check tree)=true := by
  simp only [t4_495jobs,List.all_append,List.all_nil,t4_495part0,Bool.and_self]
theorem t4_495checked : Checked tree [4,4,4,3] := by
  refine ⟨plan2227,valid2227,t4_495choices,?_⟩
  exact check_of_frontier tree 0 t4_495root t4_495jobs t4_495frontier t4_495all
theorem t4_496choices : plan2317.choices=[4,4,4,6].map (options 4 4) := by rfl


theorem t4_496part0 : t4_496jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_496frontier : t4_496root.frontier 0=t4_496jobs := by rfl
theorem t4_496all : t4_496jobs.all (Job.check tree)=true := by
  simp only [t4_496jobs,List.all_append,List.all_nil,t4_496part0,Bool.and_self]
theorem t4_496checked : Checked tree [4,4,4,6] := by
  refine ⟨plan2317,valid2317,t4_496choices,?_⟩
  exact check_of_frontier tree 0 t4_496root t4_496jobs t4_496frontier t4_496all
theorem t4_497choices : plan2318.choices=[4,4,4,7].map (options 4 4) := by rfl


theorem t4_497part0 : t4_497jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_497frontier : t4_497root.frontier 0=t4_497jobs := by rfl
theorem t4_497all : t4_497jobs.all (Job.check tree)=true := by
  simp only [t4_497jobs,List.all_append,List.all_nil,t4_497part0,Bool.and_self]
theorem t4_497checked : Checked tree [4,4,4,7] := by
  refine ⟨plan2318,valid2318,t4_497choices,?_⟩
  exact check_of_frontier tree 0 t4_497root t4_497jobs t4_497frontier t4_497all
theorem t4_498choices : plan2319.choices=[4,4,4,10].map (options 4 4) := by rfl


theorem t4_498part0 : t4_498jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_498frontier : t4_498root.frontier 0=t4_498jobs := by rfl
theorem t4_498all : t4_498jobs.all (Job.check tree)=true := by
  simp only [t4_498jobs,List.all_append,List.all_nil,t4_498part0,Bool.and_self]
theorem t4_498checked : Checked tree [4,4,4,10] := by
  refine ⟨plan2319,valid2319,t4_498choices,?_⟩
  exact check_of_frontier tree 0 t4_498root t4_498jobs t4_498frontier t4_498all
theorem t4_499choices : plan2228.choices=[4,4,5,3].map (options 4 3) := by rfl


theorem t4_499part0 : t4_499jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_499frontier : t4_499root.frontier 0=t4_499jobs := by rfl
theorem t4_499all : t4_499jobs.all (Job.check tree)=true := by
  simp only [t4_499jobs,List.all_append,List.all_nil,t4_499part0,Bool.and_self]
theorem t4_499checked : Checked tree [4,4,5,3] := by
  refine ⟨plan2228,valid2228,t4_499choices,?_⟩
  exact check_of_frontier tree 0 t4_499root t4_499jobs t4_499frontier t4_499all
theorem t4_500choices : plan2320.choices=[4,4,5,5].map (options 4 4) := by rfl


theorem t4_500part0 : t4_500jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_500frontier : t4_500root.frontier 0=t4_500jobs := by rfl
theorem t4_500all : t4_500jobs.all (Job.check tree)=true := by
  simp only [t4_500jobs,List.all_append,List.all_nil,t4_500part0,Bool.and_self]
theorem t4_500checked : Checked tree [4,4,5,5] := by
  refine ⟨plan2320,valid2320,t4_500choices,?_⟩
  exact check_of_frontier tree 0 t4_500root t4_500jobs t4_500frontier t4_500all
theorem t4_501choices : plan2321.choices=[4,4,5,6].map (options 4 4) := by rfl


theorem t4_501part0 : t4_501jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_501frontier : t4_501root.frontier 0=t4_501jobs := by rfl
theorem t4_501all : t4_501jobs.all (Job.check tree)=true := by
  simp only [t4_501jobs,List.all_append,List.all_nil,t4_501part0,Bool.and_self]
theorem t4_501checked : Checked tree [4,4,5,6] := by
  refine ⟨plan2321,valid2321,t4_501choices,?_⟩
  exact check_of_frontier tree 0 t4_501root t4_501jobs t4_501frontier t4_501all
theorem t4_502choices : plan2322.choices=[4,4,5,7].map (options 4 4) := by rfl


theorem t4_502part0 : t4_502jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_502frontier : t4_502root.frontier 0=t4_502jobs := by rfl
theorem t4_502all : t4_502jobs.all (Job.check tree)=true := by
  simp only [t4_502jobs,List.all_append,List.all_nil,t4_502part0,Bool.and_self]
theorem t4_502checked : Checked tree [4,4,5,7] := by
  refine ⟨plan2322,valid2322,t4_502choices,?_⟩
  exact check_of_frontier tree 0 t4_502root t4_502jobs t4_502frontier t4_502all
theorem t4_503choices : plan2323.choices=[4,4,5,9].map (options 4 4) := by rfl


theorem t4_503part0 : t4_503jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_503frontier : t4_503root.frontier 0=t4_503jobs := by rfl
theorem t4_503all : t4_503jobs.all (Job.check tree)=true := by
  simp only [t4_503jobs,List.all_append,List.all_nil,t4_503part0,Bool.and_self]
theorem t4_503checked : Checked tree [4,4,5,9] := by
  refine ⟨plan2323,valid2323,t4_503choices,?_⟩
  exact check_of_frontier tree 0 t4_503root t4_503jobs t4_503frontier t4_503all
theorem t4_504choices : plan2324.choices=[4,4,5,10].map (options 4 4) := by rfl


theorem t4_504part0 : t4_504jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_504frontier : t4_504root.frontier 0=t4_504jobs := by rfl
theorem t4_504all : t4_504jobs.all (Job.check tree)=true := by
  simp only [t4_504jobs,List.all_append,List.all_nil,t4_504part0,Bool.and_self]
theorem t4_504checked : Checked tree [4,4,5,10] := by
  refine ⟨plan2324,valid2324,t4_504choices,?_⟩
  exact check_of_frontier tree 0 t4_504root t4_504jobs t4_504frontier t4_504all
theorem t4_505choices : plan2325.choices=[4,4,6,6].map (options 4 4) := by rfl


theorem t4_505part0 : t4_505jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_505frontier : t4_505root.frontier 0=t4_505jobs := by rfl
theorem t4_505all : t4_505jobs.all (Job.check tree)=true := by
  simp only [t4_505jobs,List.all_append,List.all_nil,t4_505part0,Bool.and_self]
theorem t4_505checked : Checked tree [4,4,6,6] := by
  refine ⟨plan2325,valid2325,t4_505choices,?_⟩
  exact check_of_frontier tree 0 t4_505root t4_505jobs t4_505frontier t4_505all
theorem t4_506choices : plan2326.choices=[4,4,6,7].map (options 4 4) := by rfl


theorem t4_506part0 : t4_506jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_506frontier : t4_506root.frontier 0=t4_506jobs := by rfl
theorem t4_506all : t4_506jobs.all (Job.check tree)=true := by
  simp only [t4_506jobs,List.all_append,List.all_nil,t4_506part0,Bool.and_self]
theorem t4_506checked : Checked tree [4,4,6,7] := by
  refine ⟨plan2326,valid2326,t4_506choices,?_⟩
  exact check_of_frontier tree 0 t4_506root t4_506jobs t4_506frontier t4_506all
theorem t4_507choices : plan2327.choices=[4,4,6,10].map (options 4 4) := by rfl


theorem t4_507part0 : t4_507jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_507frontier : t4_507root.frontier 0=t4_507jobs := by rfl
theorem t4_507all : t4_507jobs.all (Job.check tree)=true := by
  simp only [t4_507jobs,List.all_append,List.all_nil,t4_507part0,Bool.and_self]
theorem t4_507checked : Checked tree [4,4,6,10] := by
  refine ⟨plan2327,valid2327,t4_507choices,?_⟩
  exact check_of_frontier tree 0 t4_507root t4_507jobs t4_507frontier t4_507all
theorem t4_508choices : plan2328.choices=[4,4,7,7].map (options 4 4) := by rfl


theorem t4_508part0 : t4_508jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_508frontier : t4_508root.frontier 0=t4_508jobs := by rfl
theorem t4_508all : t4_508jobs.all (Job.check tree)=true := by
  simp only [t4_508jobs,List.all_append,List.all_nil,t4_508part0,Bool.and_self]
theorem t4_508checked : Checked tree [4,4,7,7] := by
  refine ⟨plan2328,valid2328,t4_508choices,?_⟩
  exact check_of_frontier tree 0 t4_508root t4_508jobs t4_508frontier t4_508all
theorem t4_509choices : plan2229.choices=[4,4,8,3].map (options 4 3) := by rfl


theorem t4_509part0 : t4_509jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_509frontier : t4_509root.frontier 0=t4_509jobs := by rfl
theorem t4_509all : t4_509jobs.all (Job.check tree)=true := by
  simp only [t4_509jobs,List.all_append,List.all_nil,t4_509part0,Bool.and_self]
theorem t4_509checked : Checked tree [4,4,8,3] := by
  refine ⟨plan2229,valid2229,t4_509choices,?_⟩
  exact check_of_frontier tree 0 t4_509root t4_509jobs t4_509frontier t4_509all
theorem t4_510choices : plan2329.choices=[4,4,8,6].map (options 4 4) := by rfl


theorem t4_510part0 : t4_510jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_510frontier : t4_510root.frontier 0=t4_510jobs := by rfl
theorem t4_510all : t4_510jobs.all (Job.check tree)=true := by
  simp only [t4_510jobs,List.all_append,List.all_nil,t4_510part0,Bool.and_self]
theorem t4_510checked : Checked tree [4,4,8,6] := by
  refine ⟨plan2329,valid2329,t4_510choices,?_⟩
  exact check_of_frontier tree 0 t4_510root t4_510jobs t4_510frontier t4_510all
theorem t4_511choices : plan2330.choices=[4,4,8,7].map (options 4 4) := by rfl


theorem t4_511part0 : t4_511jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_511frontier : t4_511root.frontier 0=t4_511jobs := by rfl
theorem t4_511all : t4_511jobs.all (Job.check tree)=true := by
  simp only [t4_511jobs,List.all_append,List.all_nil,t4_511part0,Bool.and_self]
theorem t4_511checked : Checked tree [4,4,8,7] := by
  refine ⟨plan2330,valid2330,t4_511choices,?_⟩
  exact check_of_frontier tree 0 t4_511root t4_511jobs t4_511frontier t4_511all
theorem t4_512choices : plan2331.choices=[4,4,8,10].map (options 4 4) := by rfl


theorem t4_512part0 : t4_512jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_512frontier : t4_512root.frontier 0=t4_512jobs := by rfl
theorem t4_512all : t4_512jobs.all (Job.check tree)=true := by
  simp only [t4_512jobs,List.all_append,List.all_nil,t4_512part0,Bool.and_self]
theorem t4_512checked : Checked tree [4,4,8,10] := by
  refine ⟨plan2331,valid2331,t4_512choices,?_⟩
  exact check_of_frontier tree 0 t4_512root t4_512jobs t4_512frontier t4_512all
theorem t4_513choices : plan2230.choices=[4,4,9,3].map (options 4 3) := by rfl


theorem t4_513part0 : t4_513jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_513frontier : t4_513root.frontier 0=t4_513jobs := by rfl
theorem t4_513all : t4_513jobs.all (Job.check tree)=true := by
  simp only [t4_513jobs,List.all_append,List.all_nil,t4_513part0,Bool.and_self]
theorem t4_513checked : Checked tree [4,4,9,3] := by
  refine ⟨plan2230,valid2230,t4_513choices,?_⟩
  exact check_of_frontier tree 0 t4_513root t4_513jobs t4_513frontier t4_513all
theorem t4_514choices : plan2332.choices=[4,4,9,6].map (options 4 4) := by rfl


theorem t4_514part0 : t4_514jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_514frontier : t4_514root.frontier 0=t4_514jobs := by rfl
theorem t4_514all : t4_514jobs.all (Job.check tree)=true := by
  simp only [t4_514jobs,List.all_append,List.all_nil,t4_514part0,Bool.and_self]
theorem t4_514checked : Checked tree [4,4,9,6] := by
  refine ⟨plan2332,valid2332,t4_514choices,?_⟩
  exact check_of_frontier tree 0 t4_514root t4_514jobs t4_514frontier t4_514all
theorem t4_515choices : plan2333.choices=[4,4,9,7].map (options 4 4) := by rfl


theorem t4_515part0 : t4_515jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_515frontier : t4_515root.frontier 0=t4_515jobs := by rfl
theorem t4_515all : t4_515jobs.all (Job.check tree)=true := by
  simp only [t4_515jobs,List.all_append,List.all_nil,t4_515part0,Bool.and_self]
theorem t4_515checked : Checked tree [4,4,9,7] := by
  refine ⟨plan2333,valid2333,t4_515choices,?_⟩
  exact check_of_frontier tree 0 t4_515root t4_515jobs t4_515frontier t4_515all
theorem t4_516choices : plan2334.choices=[4,4,9,9].map (options 4 4) := by rfl


theorem t4_516part0 : t4_516jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_516frontier : t4_516root.frontier 0=t4_516jobs := by rfl
theorem t4_516all : t4_516jobs.all (Job.check tree)=true := by
  simp only [t4_516jobs,List.all_append,List.all_nil,t4_516part0,Bool.and_self]
theorem t4_516checked : Checked tree [4,4,9,9] := by
  refine ⟨plan2334,valid2334,t4_516choices,?_⟩
  exact check_of_frontier tree 0 t4_516root t4_516jobs t4_516frontier t4_516all
theorem t4_517choices : plan2335.choices=[4,4,9,10].map (options 4 4) := by rfl


theorem t4_517part0 : t4_517jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_517frontier : t4_517root.frontier 0=t4_517jobs := by rfl
theorem t4_517all : t4_517jobs.all (Job.check tree)=true := by
  simp only [t4_517jobs,List.all_append,List.all_nil,t4_517part0,Bool.and_self]
theorem t4_517checked : Checked tree [4,4,9,10] := by
  refine ⟨plan2335,valid2335,t4_517choices,?_⟩
  exact check_of_frontier tree 0 t4_517root t4_517jobs t4_517frontier t4_517all
theorem t4_518choices : plan2336.choices=[4,4,10,7].map (options 4 4) := by rfl


theorem t4_518part0 : t4_518jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_518frontier : t4_518root.frontier 0=t4_518jobs := by rfl
theorem t4_518all : t4_518jobs.all (Job.check tree)=true := by
  simp only [t4_518jobs,List.all_append,List.all_nil,t4_518part0,Bool.and_self]
theorem t4_518checked : Checked tree [4,4,10,7] := by
  refine ⟨plan2336,valid2336,t4_518choices,?_⟩
  exact check_of_frontier tree 0 t4_518root t4_518jobs t4_518frontier t4_518all
theorem t4_519choices : plan2337.choices=[4,4,10,10].map (options 4 4) := by rfl


theorem t4_519part0 : t4_519jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_519frontier : t4_519root.frontier 0=t4_519jobs := by rfl
theorem t4_519all : t4_519jobs.all (Job.check tree)=true := by
  simp only [t4_519jobs,List.all_append,List.all_nil,t4_519part0,Bool.and_self]
theorem t4_519checked : Checked tree [4,4,10,10] := by
  refine ⟨plan2337,valid2337,t4_519choices,?_⟩
  exact check_of_frontier tree 0 t4_519root t4_519jobs t4_519frontier t4_519all
theorem t4_520choices : plan1988.choices=[4,5,3,3].map (options 4 2) := by rfl


theorem t4_520part0 : t4_520jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_520frontier : t4_520root.frontier 0=t4_520jobs := by rfl
theorem t4_520all : t4_520jobs.all (Job.check tree)=true := by
  simp only [t4_520jobs,List.all_append,List.all_nil,t4_520part0,Bool.and_self]
theorem t4_520checked : Checked tree [4,5,3,3] := by
  refine ⟨plan1988,valid1988,t4_520choices,?_⟩
  exact check_of_frontier tree 0 t4_520root t4_520jobs t4_520frontier t4_520all
theorem t4_521choices : plan2231.choices=[4,5,3,6].map (options 4 3) := by rfl


theorem t4_521part0 : t4_521jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_521frontier : t4_521root.frontier 0=t4_521jobs := by rfl
theorem t4_521all : t4_521jobs.all (Job.check tree)=true := by
  simp only [t4_521jobs,List.all_append,List.all_nil,t4_521part0,Bool.and_self]
theorem t4_521checked : Checked tree [4,5,3,6] := by
  refine ⟨plan2231,valid2231,t4_521choices,?_⟩
  exact check_of_frontier tree 0 t4_521root t4_521jobs t4_521frontier t4_521all
theorem t4_522choices : plan2232.choices=[4,5,3,7].map (options 4 3) := by rfl


theorem t4_522part0 : t4_522jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_522frontier : t4_522root.frontier 0=t4_522jobs := by rfl
theorem t4_522all : t4_522jobs.all (Job.check tree)=true := by
  simp only [t4_522jobs,List.all_append,List.all_nil,t4_522part0,Bool.and_self]
theorem t4_522checked : Checked tree [4,5,3,7] := by
  refine ⟨plan2232,valid2232,t4_522choices,?_⟩
  exact check_of_frontier tree 0 t4_522root t4_522jobs t4_522frontier t4_522all
theorem t4_523choices : plan2233.choices=[4,5,3,10].map (options 4 3) := by rfl


theorem t4_523part0 : t4_523jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_523frontier : t4_523root.frontier 0=t4_523jobs := by rfl
theorem t4_523all : t4_523jobs.all (Job.check tree)=true := by
  simp only [t4_523jobs,List.all_append,List.all_nil,t4_523part0,Bool.and_self]
theorem t4_523checked : Checked tree [4,5,3,10] := by
  refine ⟨plan2233,valid2233,t4_523choices,?_⟩
  exact check_of_frontier tree 0 t4_523root t4_523jobs t4_523frontier t4_523all
theorem t4_524choices : plan2234.choices=[4,5,5,3].map (options 4 3) := by rfl


theorem t4_524part0 : t4_524jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_524frontier : t4_524root.frontier 0=t4_524jobs := by rfl
theorem t4_524all : t4_524jobs.all (Job.check tree)=true := by
  simp only [t4_524jobs,List.all_append,List.all_nil,t4_524part0,Bool.and_self]
theorem t4_524checked : Checked tree [4,5,5,3] := by
  refine ⟨plan2234,valid2234,t4_524choices,?_⟩
  exact check_of_frontier tree 0 t4_524root t4_524jobs t4_524frontier t4_524all
theorem t4_525choices : plan2338.choices=[4,5,5,5].map (options 4 4) := by rfl


theorem t4_525part0 : t4_525jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_525frontier : t4_525root.frontier 0=t4_525jobs := by rfl
theorem t4_525all : t4_525jobs.all (Job.check tree)=true := by
  simp only [t4_525jobs,List.all_append,List.all_nil,t4_525part0,Bool.and_self]
theorem t4_525checked : Checked tree [4,5,5,5] := by
  refine ⟨plan2338,valid2338,t4_525choices,?_⟩
  exact check_of_frontier tree 0 t4_525root t4_525jobs t4_525frontier t4_525all
theorem t4_526choices : plan2339.choices=[4,5,5,6].map (options 4 4) := by rfl


theorem t4_526part0 : t4_526jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_526frontier : t4_526root.frontier 0=t4_526jobs := by rfl
theorem t4_526all : t4_526jobs.all (Job.check tree)=true := by
  simp only [t4_526jobs,List.all_append,List.all_nil,t4_526part0,Bool.and_self]
theorem t4_526checked : Checked tree [4,5,5,6] := by
  refine ⟨plan2339,valid2339,t4_526choices,?_⟩
  exact check_of_frontier tree 0 t4_526root t4_526jobs t4_526frontier t4_526all
theorem t4_527choices : plan2340.choices=[4,5,5,7].map (options 4 4) := by rfl


theorem t4_527part0 : t4_527jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_527frontier : t4_527root.frontier 0=t4_527jobs := by rfl
theorem t4_527all : t4_527jobs.all (Job.check tree)=true := by
  simp only [t4_527jobs,List.all_append,List.all_nil,t4_527part0,Bool.and_self]
theorem t4_527checked : Checked tree [4,5,5,7] := by
  refine ⟨plan2340,valid2340,t4_527choices,?_⟩
  exact check_of_frontier tree 0 t4_527root t4_527jobs t4_527frontier t4_527all
theorem t4_528choices : plan2341.choices=[4,5,5,9].map (options 4 4) := by rfl


theorem t4_528part0 : t4_528jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_528frontier : t4_528root.frontier 0=t4_528jobs := by rfl
theorem t4_528all : t4_528jobs.all (Job.check tree)=true := by
  simp only [t4_528jobs,List.all_append,List.all_nil,t4_528part0,Bool.and_self]
theorem t4_528checked : Checked tree [4,5,5,9] := by
  refine ⟨plan2341,valid2341,t4_528choices,?_⟩
  exact check_of_frontier tree 0 t4_528root t4_528jobs t4_528frontier t4_528all
theorem t4_529choices : plan2342.choices=[4,5,5,10].map (options 4 4) := by rfl


theorem t4_529part0 : t4_529jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_529frontier : t4_529root.frontier 0=t4_529jobs := by rfl
theorem t4_529all : t4_529jobs.all (Job.check tree)=true := by
  simp only [t4_529jobs,List.all_append,List.all_nil,t4_529part0,Bool.and_self]
theorem t4_529checked : Checked tree [4,5,5,10] := by
  refine ⟨plan2342,valid2342,t4_529choices,?_⟩
  exact check_of_frontier tree 0 t4_529root t4_529jobs t4_529frontier t4_529all
theorem t4_530choices : plan2343.choices=[4,5,6,6].map (options 4 4) := by rfl


theorem t4_530part0 : t4_530jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_530frontier : t4_530root.frontier 0=t4_530jobs := by rfl
theorem t4_530all : t4_530jobs.all (Job.check tree)=true := by
  simp only [t4_530jobs,List.all_append,List.all_nil,t4_530part0,Bool.and_self]
theorem t4_530checked : Checked tree [4,5,6,6] := by
  refine ⟨plan2343,valid2343,t4_530choices,?_⟩
  exact check_of_frontier tree 0 t4_530root t4_530jobs t4_530frontier t4_530all
theorem t4_531choices : plan2344.choices=[4,5,6,7].map (options 4 4) := by rfl


theorem t4_531part0 : t4_531jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_531frontier : t4_531root.frontier 0=t4_531jobs := by rfl
theorem t4_531all : t4_531jobs.all (Job.check tree)=true := by
  simp only [t4_531jobs,List.all_append,List.all_nil,t4_531part0,Bool.and_self]
theorem t4_531checked : Checked tree [4,5,6,7] := by
  refine ⟨plan2344,valid2344,t4_531choices,?_⟩
  exact check_of_frontier tree 0 t4_531root t4_531jobs t4_531frontier t4_531all
theorem t4_532choices : plan2345.choices=[4,5,6,10].map (options 4 4) := by rfl


theorem t4_532part0 : t4_532jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_532frontier : t4_532root.frontier 0=t4_532jobs := by rfl
theorem t4_532all : t4_532jobs.all (Job.check tree)=true := by
  simp only [t4_532jobs,List.all_append,List.all_nil,t4_532part0,Bool.and_self]
theorem t4_532checked : Checked tree [4,5,6,10] := by
  refine ⟨plan2345,valid2345,t4_532choices,?_⟩
  exact check_of_frontier tree 0 t4_532root t4_532jobs t4_532frontier t4_532all
theorem t4_533choices : plan2346.choices=[4,5,7,7].map (options 4 4) := by rfl


theorem t4_533part0 : t4_533jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_533frontier : t4_533root.frontier 0=t4_533jobs := by rfl
theorem t4_533all : t4_533jobs.all (Job.check tree)=true := by
  simp only [t4_533jobs,List.all_append,List.all_nil,t4_533part0,Bool.and_self]
theorem t4_533checked : Checked tree [4,5,7,7] := by
  refine ⟨plan2346,valid2346,t4_533choices,?_⟩
  exact check_of_frontier tree 0 t4_533root t4_533jobs t4_533frontier t4_533all
theorem t4_534choices : plan2235.choices=[4,5,9,3].map (options 4 3) := by rfl


theorem t4_534part0 : t4_534jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_534frontier : t4_534root.frontier 0=t4_534jobs := by rfl
theorem t4_534all : t4_534jobs.all (Job.check tree)=true := by
  simp only [t4_534jobs,List.all_append,List.all_nil,t4_534part0,Bool.and_self]
theorem t4_534checked : Checked tree [4,5,9,3] := by
  refine ⟨plan2235,valid2235,t4_534choices,?_⟩
  exact check_of_frontier tree 0 t4_534root t4_534jobs t4_534frontier t4_534all
theorem t4_535choices : plan2347.choices=[4,5,9,6].map (options 4 4) := by rfl


theorem t4_535part0 : t4_535jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_535frontier : t4_535root.frontier 0=t4_535jobs := by rfl
theorem t4_535all : t4_535jobs.all (Job.check tree)=true := by
  simp only [t4_535jobs,List.all_append,List.all_nil,t4_535part0,Bool.and_self]
theorem t4_535checked : Checked tree [4,5,9,6] := by
  refine ⟨plan2347,valid2347,t4_535choices,?_⟩
  exact check_of_frontier tree 0 t4_535root t4_535jobs t4_535frontier t4_535all
theorem t4_536choices : plan2348.choices=[4,5,9,7].map (options 4 4) := by rfl


theorem t4_536part0 : t4_536jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_536frontier : t4_536root.frontier 0=t4_536jobs := by rfl
theorem t4_536all : t4_536jobs.all (Job.check tree)=true := by
  simp only [t4_536jobs,List.all_append,List.all_nil,t4_536part0,Bool.and_self]
theorem t4_536checked : Checked tree [4,5,9,7] := by
  refine ⟨plan2348,valid2348,t4_536choices,?_⟩
  exact check_of_frontier tree 0 t4_536root t4_536jobs t4_536frontier t4_536all
theorem t4_537choices : plan2349.choices=[4,5,9,9].map (options 4 4) := by rfl


theorem t4_537part0 : t4_537jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_537frontier : t4_537root.frontier 0=t4_537jobs := by rfl
theorem t4_537all : t4_537jobs.all (Job.check tree)=true := by
  simp only [t4_537jobs,List.all_append,List.all_nil,t4_537part0,Bool.and_self]
theorem t4_537checked : Checked tree [4,5,9,9] := by
  refine ⟨plan2349,valid2349,t4_537choices,?_⟩
  exact check_of_frontier tree 0 t4_537root t4_537jobs t4_537frontier t4_537all
theorem t4_538choices : plan2350.choices=[4,5,9,10].map (options 4 4) := by rfl


theorem t4_538part0 : t4_538jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_538frontier : t4_538root.frontier 0=t4_538jobs := by rfl
theorem t4_538all : t4_538jobs.all (Job.check tree)=true := by
  simp only [t4_538jobs,List.all_append,List.all_nil,t4_538part0,Bool.and_self]
theorem t4_538checked : Checked tree [4,5,9,10] := by
  refine ⟨plan2350,valid2350,t4_538choices,?_⟩
  exact check_of_frontier tree 0 t4_538root t4_538jobs t4_538frontier t4_538all
theorem t4_539choices : plan2351.choices=[4,5,10,7].map (options 4 4) := by rfl


theorem t4_539part0 : t4_539jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_539frontier : t4_539root.frontier 0=t4_539jobs := by rfl
theorem t4_539all : t4_539jobs.all (Job.check tree)=true := by
  simp only [t4_539jobs,List.all_append,List.all_nil,t4_539part0,Bool.and_self]
theorem t4_539checked : Checked tree [4,5,10,7] := by
  refine ⟨plan2351,valid2351,t4_539choices,?_⟩
  exact check_of_frontier tree 0 t4_539root t4_539jobs t4_539frontier t4_539all
theorem t4_540choices : plan2352.choices=[4,5,10,10].map (options 4 4) := by rfl


theorem t4_540part0 : t4_540jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_540frontier : t4_540root.frontier 0=t4_540jobs := by rfl
theorem t4_540all : t4_540jobs.all (Job.check tree)=true := by
  simp only [t4_540jobs,List.all_append,List.all_nil,t4_540part0,Bool.and_self]
theorem t4_540checked : Checked tree [4,5,10,10] := by
  refine ⟨plan2352,valid2352,t4_540choices,?_⟩
  exact check_of_frontier tree 0 t4_540root t4_540jobs t4_540frontier t4_540all
theorem t4_541choices : plan2353.choices=[4,6,6,6].map (options 4 4) := by rfl


theorem t4_541part0 : t4_541jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_541frontier : t4_541root.frontier 0=t4_541jobs := by rfl
theorem t4_541all : t4_541jobs.all (Job.check tree)=true := by
  simp only [t4_541jobs,List.all_append,List.all_nil,t4_541part0,Bool.and_self]
theorem t4_541checked : Checked tree [4,6,6,6] := by
  refine ⟨plan2353,valid2353,t4_541choices,?_⟩
  exact check_of_frontier tree 0 t4_541root t4_541jobs t4_541frontier t4_541all
theorem t4_542choices : plan2354.choices=[4,6,6,7].map (options 4 4) := by rfl


theorem t4_542part0 : t4_542jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_542frontier : t4_542root.frontier 0=t4_542jobs := by rfl
theorem t4_542all : t4_542jobs.all (Job.check tree)=true := by
  simp only [t4_542jobs,List.all_append,List.all_nil,t4_542part0,Bool.and_self]
theorem t4_542checked : Checked tree [4,6,6,7] := by
  refine ⟨plan2354,valid2354,t4_542choices,?_⟩
  exact check_of_frontier tree 0 t4_542root t4_542jobs t4_542frontier t4_542all
theorem t4_543choices : plan2355.choices=[4,6,6,10].map (options 4 4) := by rfl


theorem t4_543part0 : t4_543jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_543frontier : t4_543root.frontier 0=t4_543jobs := by rfl
theorem t4_543all : t4_543jobs.all (Job.check tree)=true := by
  simp only [t4_543jobs,List.all_append,List.all_nil,t4_543part0,Bool.and_self]
theorem t4_543checked : Checked tree [4,6,6,10] := by
  refine ⟨plan2355,valid2355,t4_543choices,?_⟩
  exact check_of_frontier tree 0 t4_543root t4_543jobs t4_543frontier t4_543all
theorem t4_544choices : plan2356.choices=[4,6,7,7].map (options 4 4) := by rfl


theorem t4_544part0 : t4_544jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_544frontier : t4_544root.frontier 0=t4_544jobs := by rfl
theorem t4_544all : t4_544jobs.all (Job.check tree)=true := by
  simp only [t4_544jobs,List.all_append,List.all_nil,t4_544part0,Bool.and_self]
theorem t4_544checked : Checked tree [4,6,7,7] := by
  refine ⟨plan2356,valid2356,t4_544choices,?_⟩
  exact check_of_frontier tree 0 t4_544root t4_544jobs t4_544frontier t4_544all
theorem t4_545choices : plan2357.choices=[4,6,10,7].map (options 4 4) := by rfl


theorem t4_545part0 : t4_545jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_545frontier : t4_545root.frontier 0=t4_545jobs := by rfl
theorem t4_545all : t4_545jobs.all (Job.check tree)=true := by
  simp only [t4_545jobs,List.all_append,List.all_nil,t4_545part0,Bool.and_self]
theorem t4_545checked : Checked tree [4,6,10,7] := by
  refine ⟨plan2357,valid2357,t4_545choices,?_⟩
  exact check_of_frontier tree 0 t4_545root t4_545jobs t4_545frontier t4_545all
theorem t4_546choices : plan2358.choices=[4,6,10,10].map (options 4 4) := by rfl


theorem t4_546part0 : t4_546jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_546frontier : t4_546root.frontier 0=t4_546jobs := by rfl
theorem t4_546all : t4_546jobs.all (Job.check tree)=true := by
  simp only [t4_546jobs,List.all_append,List.all_nil,t4_546part0,Bool.and_self]
theorem t4_546checked : Checked tree [4,6,10,10] := by
  refine ⟨plan2358,valid2358,t4_546choices,?_⟩
  exact check_of_frontier tree 0 t4_546root t4_546jobs t4_546frontier t4_546all
theorem t4_547choices : plan2359.choices=[4,7,7,7].map (options 4 4) := by rfl


theorem t4_547part0 : t4_547jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_547frontier : t4_547root.frontier 0=t4_547jobs := by rfl
theorem t4_547all : t4_547jobs.all (Job.check tree)=true := by
  simp only [t4_547jobs,List.all_append,List.all_nil,t4_547part0,Bool.and_self]
theorem t4_547checked : Checked tree [4,7,7,7] := by
  refine ⟨plan2359,valid2359,t4_547choices,?_⟩
  exact check_of_frontier tree 0 t4_547root t4_547jobs t4_547frontier t4_547all
theorem t4_548choices : plan1989.choices=[4,8,2,2].map (options 4 2) := by rfl


theorem t4_548part0 : t4_548jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_548frontier : t4_548root.frontier 0=t4_548jobs := by rfl
theorem t4_548all : t4_548jobs.all (Job.check tree)=true := by
  simp only [t4_548jobs,List.all_append,List.all_nil,t4_548part0,Bool.and_self]
theorem t4_548checked : Checked tree [4,8,2,2] := by
  refine ⟨plan1989,valid1989,t4_548choices,?_⟩
  exact check_of_frontier tree 0 t4_548root t4_548jobs t4_548frontier t4_548all
theorem t4_549choices : plan1990.choices=[4,8,2,3].map (options 4 2) := by rfl


theorem t4_549part0 : t4_549jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_549frontier : t4_549root.frontier 0=t4_549jobs := by rfl
theorem t4_549all : t4_549jobs.all (Job.check tree)=true := by
  simp only [t4_549jobs,List.all_append,List.all_nil,t4_549part0,Bool.and_self]
theorem t4_549checked : Checked tree [4,8,2,3] := by
  refine ⟨plan1990,valid1990,t4_549choices,?_⟩
  exact check_of_frontier tree 0 t4_549root t4_549jobs t4_549frontier t4_549all
theorem t4_550choices : plan2236.choices=[4,8,2,5].map (options 4 3) := by rfl


theorem t4_550part0 : t4_550jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_550frontier : t4_550root.frontier 0=t4_550jobs := by rfl
theorem t4_550all : t4_550jobs.all (Job.check tree)=true := by
  simp only [t4_550jobs,List.all_append,List.all_nil,t4_550part0,Bool.and_self]
theorem t4_550checked : Checked tree [4,8,2,5] := by
  refine ⟨plan2236,valid2236,t4_550choices,?_⟩
  exact check_of_frontier tree 0 t4_550root t4_550jobs t4_550frontier t4_550all
theorem t4_551choices : plan2237.choices=[4,8,2,6].map (options 4 3) := by rfl


theorem t4_551part0 : t4_551jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_551frontier : t4_551root.frontier 0=t4_551jobs := by rfl
theorem t4_551all : t4_551jobs.all (Job.check tree)=true := by
  simp only [t4_551jobs,List.all_append,List.all_nil,t4_551part0,Bool.and_self]
theorem t4_551checked : Checked tree [4,8,2,6] := by
  refine ⟨plan2237,valid2237,t4_551choices,?_⟩
  exact check_of_frontier tree 0 t4_551root t4_551jobs t4_551frontier t4_551all
theorem t4_552choices : plan2238.choices=[4,8,2,7].map (options 4 3) := by rfl


theorem t4_552part0 : t4_552jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_552frontier : t4_552root.frontier 0=t4_552jobs := by rfl
theorem t4_552all : t4_552jobs.all (Job.check tree)=true := by
  simp only [t4_552jobs,List.all_append,List.all_nil,t4_552part0,Bool.and_self]
theorem t4_552checked : Checked tree [4,8,2,7] := by
  refine ⟨plan2238,valid2238,t4_552choices,?_⟩
  exact check_of_frontier tree 0 t4_552root t4_552jobs t4_552frontier t4_552all
theorem t4_553choices : plan2239.choices=[4,8,2,9].map (options 4 3) := by rfl


theorem t4_553part0 : t4_553jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_553frontier : t4_553root.frontier 0=t4_553jobs := by rfl
theorem t4_553all : t4_553jobs.all (Job.check tree)=true := by
  simp only [t4_553jobs,List.all_append,List.all_nil,t4_553part0,Bool.and_self]
theorem t4_553checked : Checked tree [4,8,2,9] := by
  refine ⟨plan2239,valid2239,t4_553choices,?_⟩
  exact check_of_frontier tree 0 t4_553root t4_553jobs t4_553frontier t4_553all
theorem t4_554choices : plan2240.choices=[4,8,2,10].map (options 4 3) := by rfl


theorem t4_554part0 : t4_554jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_554frontier : t4_554root.frontier 0=t4_554jobs := by rfl
theorem t4_554all : t4_554jobs.all (Job.check tree)=true := by
  simp only [t4_554jobs,List.all_append,List.all_nil,t4_554part0,Bool.and_self]
theorem t4_554checked : Checked tree [4,8,2,10] := by
  refine ⟨plan2240,valid2240,t4_554choices,?_⟩
  exact check_of_frontier tree 0 t4_554root t4_554jobs t4_554frontier t4_554all
theorem t4_555choices : plan1991.choices=[4,8,3,3].map (options 4 2) := by rfl


theorem t4_555part0 : t4_555jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_555frontier : t4_555root.frontier 0=t4_555jobs := by rfl
theorem t4_555all : t4_555jobs.all (Job.check tree)=true := by
  simp only [t4_555jobs,List.all_append,List.all_nil,t4_555part0,Bool.and_self]
theorem t4_555checked : Checked tree [4,8,3,3] := by
  refine ⟨plan1991,valid1991,t4_555choices,?_⟩
  exact check_of_frontier tree 0 t4_555root t4_555jobs t4_555frontier t4_555all
theorem t4_556choices : plan2241.choices=[4,8,3,6].map (options 4 3) := by rfl


theorem t4_556part0 : t4_556jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_556frontier : t4_556root.frontier 0=t4_556jobs := by rfl
theorem t4_556all : t4_556jobs.all (Job.check tree)=true := by
  simp only [t4_556jobs,List.all_append,List.all_nil,t4_556part0,Bool.and_self]
theorem t4_556checked : Checked tree [4,8,3,6] := by
  refine ⟨plan2241,valid2241,t4_556choices,?_⟩
  exact check_of_frontier tree 0 t4_556root t4_556jobs t4_556frontier t4_556all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks003 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_420checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_433checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_434checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_435checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_436checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_437checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_438checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_439checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_440checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_441checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_442checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_421checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_443checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_444checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_445checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_446checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_447checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_448checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_449checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_450checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_451checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_452checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_422checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_453checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_454checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_455checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_456checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_457checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_458checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_459checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_460checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_461checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_462checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_463checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_423checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_464checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_465checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_466checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_467checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_468checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_469checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_470checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_471checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_472checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_473checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_424checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_474checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_475checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_476checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_477checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_478checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_479checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_480checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_481checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_482checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_483checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_425checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_484checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_485checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_486checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_487checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_488checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_489checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_490checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_491checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_492checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_493checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_426checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_494checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_495checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_496checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_497checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_498checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_499checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_500checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_501checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_502checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_503checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_427checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_504checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_505checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_506checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_507checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_508checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_509checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_510checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_511checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_512checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_513checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_428checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_514checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_515checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_516checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_517checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_518checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_519checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_520checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_521checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_522checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_523checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_429checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_524checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_525checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_526checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_527checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_528checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_529checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_530checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_531checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_532checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_533checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_430checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_534checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_535checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_536checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_537checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_538checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_539checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_540checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_541checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_542checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_543checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_431checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_544checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_545checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_546checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_547checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_548checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_549checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_550checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_551checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_552checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_553checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_432checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_554checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_555checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_556checked⟩
