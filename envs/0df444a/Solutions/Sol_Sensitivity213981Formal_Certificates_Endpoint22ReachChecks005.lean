-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks005
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:07:53.177997+00:00
-- url     : https://prove2.me/submissions/c145f187-c2bb-40e2-9502-afdbae0d2e5a

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans018
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans020
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans021
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans023
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans024
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans025
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans039
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans041
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



























































































































theorem valid62 : plan62.Valid := valid_step _ _ _ valid0 (by decide +kernel)











theorem valid68 : plan68.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid69 : plan69.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid71 : plan71.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid72 : plan72.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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



theorem valid87 : plan87.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid90 : plan90.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid91 : plan91.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid93 : plan93.Valid := valid_step _ _ _ valid0 (by decide +kernel)





theorem valid96 : plan96.Valid := valid_step _ _ _ valid0 (by decide +kernel)
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



















































































































theorem valid346 : plan346.Valid := valid_step _ _ _ valid62 (by decide +kernel)















theorem valid354 : plan354.Valid := valid_step _ _ _ valid68 (by decide +kernel)

theorem valid355 : plan355.Valid := valid_step _ _ _ valid69 (by decide +kernel)











theorem valid361 : plan361.Valid := valid_step _ _ _ valid69 (by decide +kernel)

theorem valid362 : plan362.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid363 : plan363.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid364 : plan364.Valid := valid_step _ _ _ valid74 (by decide +kernel)








































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





















































































































































theorem valid939 : plan939.Valid := valid_step _ _ _ valid346 (by decide +kernel)










































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











theorem valid390 : plan390.Valid := valid_step _ _ _ valid76 (by decide +kernel)

theorem valid391 : plan391.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid392 : plan392.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid393 : plan393.Valid := valid_step _ _ _ valid79 (by decide +kernel)

theorem valid394 : plan394.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid395 : plan395.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid396 : plan396.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid397 : plan397.Valid := valid_step _ _ _ valid80 (by decide +kernel)









theorem valid402 : plan402.Valid := valid_step _ _ _ valid75 (by decide +kernel)











theorem valid408 : plan408.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid409 : plan409.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid410 : plan410.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid411 : plan411.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid412 : plan412.Valid := valid_step _ _ _ valid75 (by decide +kernel)







theorem valid416 : plan416.Valid := valid_step _ _ _ valid75 (by decide +kernel)



theorem valid418 : plan418.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid419 : plan419.Valid := valid_step _ _ _ valid79 (by decide +kernel)

theorem valid420 : plan420.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid421 : plan421.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid422 : plan422.Valid := valid_step _ _ _ valid80 (by decide +kernel)







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





theorem valid446 : plan446.Valid := valid_step _ _ _ valid87 (by decide +kernel)







theorem valid450 : plan450.Valid := valid_step _ _ _ valid91 (by decide +kernel)







theorem valid454 : plan454.Valid := valid_step _ _ _ valid90 (by decide +kernel)

theorem valid455 : plan455.Valid := valid_step _ _ _ valid91 (by decide +kernel)

theorem valid456 : plan456.Valid := valid_step _ _ _ valid93 (by decide +kernel)















theorem valid464 : plan464.Valid := valid_step _ _ _ valid97 (by decide +kernel)









theorem valid469 : plan469.Valid := valid_step _ _ _ valid97 (by decide +kernel)





theorem valid472 : plan472.Valid := valid_step _ _ _ valid96 (by decide +kernel)

theorem valid473 : plan473.Valid := valid_step _ _ _ valid97 (by decide +kernel)

theorem valid474 : plan474.Valid := valid_step _ _ _ valid99 (by decide +kernel)

theorem valid475 : plan475.Valid := valid_step _ _ _ valid97 (by decide +kernel)





theorem valid478 : plan478.Valid := valid_step _ _ _ valid97 (by decide +kernel)




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









































































theorem valid997 : plan997.Valid := valid_step _ _ _ valid362 (by decide +kernel)

theorem valid998 : plan998.Valid := valid_step _ _ _ valid363 (by decide +kernel)

theorem valid999 : plan999.Valid := valid_step _ _ _ valid364 (by decide +kernel)











































theorem valid1021 : plan1021.Valid := valid_step _ _ _ valid361 (by decide +kernel)











theorem valid1027 : plan1027.Valid := valid_step _ _ _ valid354 (by decide +kernel)

theorem valid1028 : plan1028.Valid := valid_step _ _ _ valid355 (by decide +kernel)











theorem valid1034 : plan1034.Valid := valid_step _ _ _ valid361 (by decide +kernel)













theorem valid1041 : plan1041.Valid := valid_step _ _ _ valid361 (by decide +kernel)





























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



















































































































































theorem valid1802 : plan1802.Valid := valid_step _ _ _ valid939 (by decide +kernel)

theorem valid1803 : plan1803.Valid := valid_step _ _ _ valid939 (by decide +kernel)










































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



































































theorem valid1100 : plan1100.Valid := valid_step _ _ _ valid395 (by decide +kernel)

theorem valid1101 : plan1101.Valid := valid_step _ _ _ valid396 (by decide +kernel)

theorem valid1102 : plan1102.Valid := valid_step _ _ _ valid397 (by decide +kernel)

theorem valid1103 : plan1103.Valid := valid_step _ _ _ valid402 (by decide +kernel)



















theorem valid1113 : plan1113.Valid := valid_step _ _ _ valid416 (by decide +kernel)



























theorem valid1127 : plan1127.Valid := valid_step _ _ _ valid390 (by decide +kernel)

theorem valid1128 : plan1128.Valid := valid_step _ _ _ valid391 (by decide +kernel)

theorem valid1129 : plan1129.Valid := valid_step _ _ _ valid392 (by decide +kernel)

theorem valid1130 : plan1130.Valid := valid_step _ _ _ valid393 (by decide +kernel)

theorem valid1131 : plan1131.Valid := valid_step _ _ _ valid394 (by decide +kernel)

theorem valid1132 : plan1132.Valid := valid_step _ _ _ valid395 (by decide +kernel)

theorem valid1133 : plan1133.Valid := valid_step _ _ _ valid396 (by decide +kernel)

theorem valid1134 : plan1134.Valid := valid_step _ _ _ valid397 (by decide +kernel)

theorem valid1135 : plan1135.Valid := valid_step _ _ _ valid402 (by decide +kernel)



















theorem valid1145 : plan1145.Valid := valid_step _ _ _ valid412 (by decide +kernel)







theorem valid1149 : plan1149.Valid := valid_step _ _ _ valid416 (by decide +kernel)






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







theorem valid1156 : plan1156.Valid := valid_step _ _ _ valid395 (by decide +kernel)

theorem valid1157 : plan1157.Valid := valid_step _ _ _ valid396 (by decide +kernel)

theorem valid1158 : plan1158.Valid := valid_step _ _ _ valid397 (by decide +kernel)









theorem valid1163 : plan1163.Valid := valid_step _ _ _ valid416 (by decide +kernel)





























































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

theorem valid1216 : plan1216.Valid := valid_step _ _ _ valid426 (by decide +kernel)

theorem valid1217 : plan1217.Valid := valid_step _ _ _ valid427 (by decide +kernel)

theorem valid1218 : plan1218.Valid := valid_step _ _ _ valid428 (by decide +kernel)

theorem valid1219 : plan1219.Valid := valid_step _ _ _ valid429 (by decide +kernel)

theorem valid1220 : plan1220.Valid := valid_step _ _ _ valid430 (by decide +kernel)

theorem valid1221 : plan1221.Valid := valid_step _ _ _ valid431 (by decide +kernel)

theorem valid1222 : plan1222.Valid := valid_step _ _ _ valid432 (by decide +kernel)

theorem valid1223 : plan1223.Valid := valid_step _ _ _ valid433 (by decide +kernel)

theorem valid1224 : plan1224.Valid := valid_step _ _ _ valid434 (by decide +kernel)

theorem valid1225 : plan1225.Valid := valid_step _ _ _ valid435 (by decide +kernel)

theorem valid1226 : plan1226.Valid := valid_step _ _ _ valid436 (by decide +kernel)

theorem valid1227 : plan1227.Valid := valid_step _ _ _ valid437 (by decide +kernel)

theorem valid1228 : plan1228.Valid := valid_step _ _ _ valid438 (by decide +kernel)

theorem valid1229 : plan1229.Valid := valid_step _ _ _ valid439 (by decide +kernel)

theorem valid1230 : plan1230.Valid := valid_step _ _ _ valid440 (by decide +kernel)

theorem valid1231 : plan1231.Valid := valid_step _ _ _ valid441 (by decide +kernel)

theorem valid1232 : plan1232.Valid := valid_step _ _ _ valid442 (by decide +kernel)

theorem valid1233 : plan1233.Valid := valid_step _ _ _ valid443 (by decide +kernel)

theorem valid1234 : plan1234.Valid := valid_step _ _ _ valid431 (by decide +kernel)

theorem valid1235 : plan1235.Valid := valid_step _ _ _ valid432 (by decide +kernel)

theorem valid1236 : plan1236.Valid := valid_step _ _ _ valid433 (by decide +kernel)

theorem valid1237 : plan1237.Valid := valid_step _ _ _ valid434 (by decide +kernel)

theorem valid1238 : plan1238.Valid := valid_step _ _ _ valid438 (by decide +kernel)

theorem valid1239 : plan1239.Valid := valid_step _ _ _ valid439 (by decide +kernel)

theorem valid1240 : plan1240.Valid := valid_step _ _ _ valid440 (by decide +kernel)

theorem valid1241 : plan1241.Valid := valid_step _ _ _ valid441 (by decide +kernel)

theorem valid1242 : plan1242.Valid := valid_step _ _ _ valid442 (by decide +kernel)

theorem valid1243 : plan1243.Valid := valid_step _ _ _ valid443 (by decide +kernel)

theorem valid1244 : plan1244.Valid := valid_step _ _ _ valid434 (by decide +kernel)

theorem valid1245 : plan1245.Valid := valid_step _ _ _ valid442 (by decide +kernel)

theorem valid1246 : plan1246.Valid := valid_step _ _ _ valid443 (by decide +kernel)




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

theorem valid2017 : plan2017.Valid := valid_step _ _ _ valid998 (by decide +kernel)

theorem valid2018 : plan2018.Valid := valid_step _ _ _ valid999 (by decide +kernel)

theorem valid2019 : plan2019.Valid := valid_step _ _ _ valid1041 (by decide +kernel)


























































































































































































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















































































































































































theorem valid2008 : plan2008.Valid := valid_step _ _ _ valid997 (by decide +kernel)

theorem valid2009 : plan2009.Valid := valid_step _ _ _ valid998 (by decide +kernel)

theorem valid2010 : plan2010.Valid := valid_step _ _ _ valid999 (by decide +kernel)

theorem valid2011 : plan2011.Valid := valid_step _ _ _ valid1021 (by decide +kernel)

theorem valid2012 : plan2012.Valid := valid_step _ _ _ valid1027 (by decide +kernel)

theorem valid2013 : plan2013.Valid := valid_step _ _ _ valid1028 (by decide +kernel)

theorem valid2014 : plan2014.Valid := valid_step _ _ _ valid1034 (by decide +kernel)

theorem valid2015 : plan2015.Valid := valid_step _ _ _ valid1041 (by decide +kernel)

theorem valid2016 : plan2016.Valid := valid_step _ _ _ valid997 (by decide +kernel)
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







































































































































theorem valid2276 : plan2276.Valid := valid_step _ _ _ valid1056 (by decide +kernel)

theorem valid2277 : plan2277.Valid := valid_step _ _ _ valid1057 (by decide +kernel)

theorem valid2278 : plan2278.Valid := valid_step _ _ _ valid1058 (by decide +kernel)

theorem valid2279 : plan2279.Valid := valid_step _ _ _ valid1059 (by decide +kernel)

theorem valid2280 : plan2280.Valid := valid_step _ _ _ valid1060 (by decide +kernel)

theorem valid2281 : plan2281.Valid := valid_step _ _ _ valid1061 (by decide +kernel)

theorem valid2282 : plan2282.Valid := valid_step _ _ _ valid1062 (by decide +kernel)

theorem valid2283 : plan2283.Valid := valid_step _ _ _ valid1063 (by decide +kernel)

theorem valid2284 : plan2284.Valid := valid_step _ _ _ valid1064 (by decide +kernel)

theorem valid2285 : plan2285.Valid := valid_step _ _ _ valid1065 (by decide +kernel)

theorem valid2286 : plan2286.Valid := valid_step _ _ _ valid1066 (by decide +kernel)

theorem valid2287 : plan2287.Valid := valid_step _ _ _ valid1100 (by decide +kernel)

theorem valid2288 : plan2288.Valid := valid_step _ _ _ valid1101 (by decide +kernel)

theorem valid2289 : plan2289.Valid := valid_step _ _ _ valid1102 (by decide +kernel)

theorem valid2290 : plan2290.Valid := valid_step _ _ _ valid1103 (by decide +kernel)

theorem valid2291 : plan2291.Valid := valid_step _ _ _ valid1113 (by decide +kernel)

theorem valid2292 : plan2292.Valid := valid_step _ _ _ valid1127 (by decide +kernel)

theorem valid2293 : plan2293.Valid := valid_step _ _ _ valid1128 (by decide +kernel)

theorem valid2294 : plan2294.Valid := valid_step _ _ _ valid1129 (by decide +kernel)

theorem valid2295 : plan2295.Valid := valid_step _ _ _ valid1130 (by decide +kernel)

theorem valid2296 : plan2296.Valid := valid_step _ _ _ valid1131 (by decide +kernel)

theorem valid2297 : plan2297.Valid := valid_step _ _ _ valid1132 (by decide +kernel)

theorem valid2298 : plan2298.Valid := valid_step _ _ _ valid1133 (by decide +kernel)

theorem valid2299 : plan2299.Valid := valid_step _ _ _ valid1134 (by decide +kernel)

theorem valid2300 : plan2300.Valid := valid_step _ _ _ valid1135 (by decide +kernel)

theorem valid2301 : plan2301.Valid := valid_step _ _ _ valid1145 (by decide +kernel)

theorem valid2302 : plan2302.Valid := valid_step _ _ _ valid1149 (by decide +kernel)

theorem valid2303 : plan2303.Valid := valid_step _ _ _ valid1156 (by decide +kernel)

theorem valid2304 : plan2304.Valid := valid_step _ _ _ valid1157 (by decide +kernel)
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

theorem valid2305 : plan2305.Valid := valid_step _ _ _ valid1158 (by decide +kernel)

theorem valid2306 : plan2306.Valid := valid_step _ _ _ valid1163 (by decide +kernel)

theorem valid2307 : plan2307.Valid := valid_step _ _ _ valid1061 (by decide +kernel)

theorem valid2308 : plan2308.Valid := valid_step _ _ _ valid1062 (by decide +kernel)

theorem valid2309 : plan2309.Valid := valid_step _ _ _ valid1063 (by decide +kernel)

theorem valid2310 : plan2310.Valid := valid_step _ _ _ valid1064 (by decide +kernel)

theorem valid2311 : plan2311.Valid := valid_step _ _ _ valid1065 (by decide +kernel)

theorem valid2312 : plan2312.Valid := valid_step _ _ _ valid1066 (by decide +kernel)

theorem valid2313 : plan2313.Valid := valid_step _ _ _ valid1156 (by decide +kernel)

theorem valid2314 : plan2314.Valid := valid_step _ _ _ valid1157 (by decide +kernel)

theorem valid2315 : plan2315.Valid := valid_step _ _ _ valid1158 (by decide +kernel)

theorem valid2316 : plan2316.Valid := valid_step _ _ _ valid1163 (by decide +kernel)








































































































































































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









































































theorem valid2437 : plan2437.Valid := valid_step _ _ _ valid1194 (by decide +kernel)

theorem valid2438 : plan2438.Valid := valid_step _ _ _ valid1195 (by decide +kernel)

theorem valid2439 : plan2439.Valid := valid_step _ _ _ valid1196 (by decide +kernel)

theorem valid2440 : plan2440.Valid := valid_step _ _ _ valid1197 (by decide +kernel)

theorem valid2441 : plan2441.Valid := valid_step _ _ _ valid1198 (by decide +kernel)

theorem valid2442 : plan2442.Valid := valid_step _ _ _ valid1199 (by decide +kernel)

theorem valid2443 : plan2443.Valid := valid_step _ _ _ valid1200 (by decide +kernel)

theorem valid2444 : plan2444.Valid := valid_step _ _ _ valid1201 (by decide +kernel)

theorem valid2445 : plan2445.Valid := valid_step _ _ _ valid1202 (by decide +kernel)

theorem valid2446 : plan2446.Valid := valid_step _ _ _ valid1203 (by decide +kernel)

theorem valid2447 : plan2447.Valid := valid_step _ _ _ valid1204 (by decide +kernel)

theorem valid2448 : plan2448.Valid := valid_step _ _ _ valid1205 (by decide +kernel)

theorem valid2449 : plan2449.Valid := valid_step _ _ _ valid1206 (by decide +kernel)

theorem valid2450 : plan2450.Valid := valid_step _ _ _ valid1207 (by decide +kernel)

theorem valid2451 : plan2451.Valid := valid_step _ _ _ valid1208 (by decide +kernel)

theorem valid2452 : plan2452.Valid := valid_step _ _ _ valid1209 (by decide +kernel)

theorem valid2453 : plan2453.Valid := valid_step _ _ _ valid1210 (by decide +kernel)

theorem valid2454 : plan2454.Valid := valid_step _ _ _ valid1211 (by decide +kernel)

theorem valid2455 : plan2455.Valid := valid_step _ _ _ valid1212 (by decide +kernel)

theorem valid2456 : plan2456.Valid := valid_step _ _ _ valid1213 (by decide +kernel)

theorem valid2457 : plan2457.Valid := valid_step _ _ _ valid1214 (by decide +kernel)

theorem valid2458 : plan2458.Valid := valid_step _ _ _ valid1215 (by decide +kernel)

theorem valid2459 : plan2459.Valid := valid_step _ _ _ valid1216 (by decide +kernel)

theorem valid2460 : plan2460.Valid := valid_step _ _ _ valid1217 (by decide +kernel)

theorem valid2461 : plan2461.Valid := valid_step _ _ _ valid1218 (by decide +kernel)

theorem valid2462 : plan2462.Valid := valid_step _ _ _ valid1219 (by decide +kernel)

theorem valid2463 : plan2463.Valid := valid_step _ _ _ valid1220 (by decide +kernel)

theorem valid2464 : plan2464.Valid := valid_step _ _ _ valid1221 (by decide +kernel)

theorem valid2465 : plan2465.Valid := valid_step _ _ _ valid1222 (by decide +kernel)

theorem valid2466 : plan2466.Valid := valid_step _ _ _ valid1223 (by decide +kernel)

theorem valid2467 : plan2467.Valid := valid_step _ _ _ valid1224 (by decide +kernel)

theorem valid2468 : plan2468.Valid := valid_step _ _ _ valid1225 (by decide +kernel)

theorem valid2469 : plan2469.Valid := valid_step _ _ _ valid1226 (by decide +kernel)

theorem valid2470 : plan2470.Valid := valid_step _ _ _ valid1227 (by decide +kernel)

theorem valid2471 : plan2471.Valid := valid_step _ _ _ valid1228 (by decide +kernel)

theorem valid2472 : plan2472.Valid := valid_step _ _ _ valid1229 (by decide +kernel)

theorem valid2473 : plan2473.Valid := valid_step _ _ _ valid1230 (by decide +kernel)

theorem valid2474 : plan2474.Valid := valid_step _ _ _ valid1231 (by decide +kernel)

theorem valid2475 : plan2475.Valid := valid_step _ _ _ valid1232 (by decide +kernel)

theorem valid2476 : plan2476.Valid := valid_step _ _ _ valid1233 (by decide +kernel)

theorem valid2477 : plan2477.Valid := valid_step _ _ _ valid1234 (by decide +kernel)

theorem valid2478 : plan2478.Valid := valid_step _ _ _ valid1235 (by decide +kernel)

theorem valid2479 : plan2479.Valid := valid_step _ _ _ valid1236 (by decide +kernel)

theorem valid2480 : plan2480.Valid := valid_step _ _ _ valid1237 (by decide +kernel)

theorem valid2481 : plan2481.Valid := valid_step _ _ _ valid1238 (by decide +kernel)

theorem valid2482 : plan2482.Valid := valid_step _ _ _ valid1239 (by decide +kernel)

theorem valid2483 : plan2483.Valid := valid_step _ _ _ valid1240 (by decide +kernel)

theorem valid2484 : plan2484.Valid := valid_step _ _ _ valid1241 (by decide +kernel)

theorem valid2485 : plan2485.Valid := valid_step _ _ _ valid1242 (by decide +kernel)

theorem valid2486 : plan2486.Valid := valid_step _ _ _ valid1243 (by decide +kernel)

theorem valid2487 : plan2487.Valid := valid_step _ _ _ valid1244 (by decide +kernel)

theorem valid2488 : plan2488.Valid := valid_step _ _ _ valid1245 (by decide +kernel)

theorem valid2489 : plan2489.Valid := valid_step _ _ _ valid1246 (by decide +kernel)

theorem valid2490 : plan2490.Valid := valid_step _ _ _ valid1209 (by decide +kernel)

theorem valid2491 : plan2491.Valid := valid_step _ _ _ valid1210 (by decide +kernel)

theorem valid2492 : plan2492.Valid := valid_step _ _ _ valid1211 (by decide +kernel)

theorem valid2493 : plan2493.Valid := valid_step _ _ _ valid1212 (by decide +kernel)

theorem valid2494 : plan2494.Valid := valid_step _ _ _ valid1213 (by decide +kernel)

theorem valid2495 : plan2495.Valid := valid_step _ _ _ valid1214 (by decide +kernel)

theorem valid2496 : plan2496.Valid := valid_step _ _ _ valid1215 (by decide +kernel)
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

theorem valid504 : plan504.Valid := valid_step _ _ _ valid105 (by decide +kernel)
















































































































































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

theorem valid1249 : plan1249.Valid := valid_step _ _ _ valid446 (by decide +kernel)

theorem valid1250 : plan1250.Valid := valid_step _ _ _ valid446 (by decide +kernel)









theorem valid1255 : plan1255.Valid := valid_step _ _ _ valid450 (by decide +kernel)







theorem valid1259 : plan1259.Valid := valid_step _ _ _ valid454 (by decide +kernel)

theorem valid1260 : plan1260.Valid := valid_step _ _ _ valid455 (by decide +kernel)

theorem valid1261 : plan1261.Valid := valid_step _ _ _ valid456 (by decide +kernel)







theorem valid1265 : plan1265.Valid := valid_step _ _ _ valid454 (by decide +kernel)

theorem valid1266 : plan1266.Valid := valid_step _ _ _ valid455 (by decide +kernel)

theorem valid1267 : plan1267.Valid := valid_step _ _ _ valid456 (by decide +kernel)































theorem valid1283 : plan1283.Valid := valid_step _ _ _ valid469 (by decide +kernel)





theorem valid1286 : plan1286.Valid := valid_step _ _ _ valid472 (by decide +kernel)

theorem valid1287 : plan1287.Valid := valid_step _ _ _ valid473 (by decide +kernel)

theorem valid1288 : plan1288.Valid := valid_step _ _ _ valid474 (by decide +kernel)

theorem valid1289 : plan1289.Valid := valid_step _ _ _ valid475 (by decide +kernel)





theorem valid1292 : plan1292.Valid := valid_step _ _ _ valid478 (by decide +kernel)





theorem valid1295 : plan1295.Valid := valid_step _ _ _ valid481 (by decide +kernel)

theorem valid1296 : plan1296.Valid := valid_step _ _ _ valid482 (by decide +kernel)









theorem valid1301 : plan1301.Valid := valid_step _ _ _ valid472 (by decide +kernel)

theorem valid1302 : plan1302.Valid := valid_step _ _ _ valid473 (by decide +kernel)

theorem valid1303 : plan1303.Valid := valid_step _ _ _ valid474 (by decide +kernel)

theorem valid1304 : plan1304.Valid := valid_step _ _ _ valid475 (by decide +kernel)

theorem valid1305 : plan1305.Valid := valid_step _ _ _ valid481 (by decide +kernel)

theorem valid1306 : plan1306.Valid := valid_step _ _ _ valid482 (by decide +kernel)







theorem valid1310 : plan1310.Valid := valid_step _ _ _ valid464 (by decide +kernel)













theorem valid1317 : plan1317.Valid := valid_step _ _ _ valid464 (by decide +kernel)






















































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

theorem valid2497 : plan2497.Valid := valid_step _ _ _ valid1234 (by decide +kernel)

theorem valid2498 : plan2498.Valid := valid_step _ _ _ valid1235 (by decide +kernel)

theorem valid2499 : plan2499.Valid := valid_step _ _ _ valid1236 (by decide +kernel)

theorem valid2500 : plan2500.Valid := valid_step _ _ _ valid1237 (by decide +kernel)

theorem valid2501 : plan2501.Valid := valid_step _ _ _ valid1238 (by decide +kernel)

theorem valid2502 : plan2502.Valid := valid_step _ _ _ valid1239 (by decide +kernel)

theorem valid2503 : plan2503.Valid := valid_step _ _ _ valid1240 (by decide +kernel)

theorem valid2504 : plan2504.Valid := valid_step _ _ _ valid1241 (by decide +kernel)

theorem valid2505 : plan2505.Valid := valid_step _ _ _ valid1242 (by decide +kernel)

theorem valid2506 : plan2506.Valid := valid_step _ _ _ valid1243 (by decide +kernel)

theorem valid2507 : plan2507.Valid := valid_step _ _ _ valid1244 (by decide +kernel)

theorem valid2508 : plan2508.Valid := valid_step _ _ _ valid1245 (by decide +kernel)

theorem valid2509 : plan2509.Valid := valid_step _ _ _ valid1246 (by decide +kernel)

theorem valid2510 : plan2510.Valid := valid_step _ _ _ valid1215 (by decide +kernel)

theorem valid2511 : plan2511.Valid := valid_step _ _ _ valid1244 (by decide +kernel)

theorem valid2512 : plan2512.Valid := valid_step _ _ _ valid1245 (by decide +kernel)

theorem valid2513 : plan2513.Valid := valid_step _ _ _ valid1246 (by decide +kernel)



theorem valid2515 : plan2515.Valid := valid_step _ _ _ valid1250 (by decide +kernel)





theorem valid2518 : plan2518.Valid := valid_step _ _ _ valid1249 (by decide +kernel)

theorem valid2519 : plan2519.Valid := valid_step _ _ _ valid1250 (by decide +kernel)









theorem valid2524 : plan2524.Valid := valid_step _ _ _ valid1260 (by decide +kernel)



theorem valid2526 : plan2526.Valid := valid_step _ _ _ valid1265 (by decide +kernel)

theorem valid2527 : plan2527.Valid := valid_step _ _ _ valid1266 (by decide +kernel)

theorem valid2528 : plan2528.Valid := valid_step _ _ _ valid1267 (by decide +kernel)











theorem valid2534 : plan2534.Valid := valid_step _ _ _ valid1255 (by decide +kernel)







theorem valid2538 : plan2538.Valid := valid_step _ _ _ valid1259 (by decide +kernel)

theorem valid2539 : plan2539.Valid := valid_step _ _ _ valid1260 (by decide +kernel)

theorem valid2540 : plan2540.Valid := valid_step _ _ _ valid1261 (by decide +kernel)







theorem valid2544 : plan2544.Valid := valid_step _ _ _ valid1265 (by decide +kernel)

theorem valid2545 : plan2545.Valid := valid_step _ _ _ valid1266 (by decide +kernel)

theorem valid2546 : plan2546.Valid := valid_step _ _ _ valid1267 (by decide +kernel)



































theorem valid2564 : plan2564.Valid := valid_step _ _ _ valid1287 (by decide +kernel)



theorem valid2566 : plan2566.Valid := valid_step _ _ _ valid1289 (by decide +kernel)



theorem valid2568 : plan2568.Valid := valid_step _ _ _ valid1295 (by decide +kernel)



theorem valid2570 : plan2570.Valid := valid_step _ _ _ valid1301 (by decide +kernel)

theorem valid2571 : plan2571.Valid := valid_step _ _ _ valid1302 (by decide +kernel)

theorem valid2572 : plan2572.Valid := valid_step _ _ _ valid1303 (by decide +kernel)

theorem valid2573 : plan2573.Valid := valid_step _ _ _ valid1304 (by decide +kernel)

theorem valid2574 : plan2574.Valid := valid_step _ _ _ valid1305 (by decide +kernel)

theorem valid2575 : plan2575.Valid := valid_step _ _ _ valid1306 (by decide +kernel)





theorem valid2578 : plan2578.Valid := valid_step _ _ _ valid1310 (by decide +kernel)







theorem valid2582 : plan2582.Valid := valid_step _ _ _ valid1317 (by decide +kernel)




















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



















theorem valid3658 : plan3658.Valid := valid_step _ _ _ valid2515 (by decide +kernel)

theorem valid3659 : plan3659.Valid := valid_step _ _ _ valid2518 (by decide +kernel)

theorem valid3660 : plan3660.Valid := valid_step _ _ _ valid2519 (by decide +kernel)



























theorem valid3674 : plan3674.Valid := valid_step _ _ _ valid2524 (by decide +kernel)

theorem valid3675 : plan3675.Valid := valid_step _ _ _ valid2526 (by decide +kernel)

theorem valid3676 : plan3676.Valid := valid_step _ _ _ valid2527 (by decide +kernel)

theorem valid3677 : plan3677.Valid := valid_step _ _ _ valid2528 (by decide +kernel)

theorem valid3678 : plan3678.Valid := valid_step _ _ _ valid2534 (by decide +kernel)

theorem valid3679 : plan3679.Valid := valid_step _ _ _ valid2538 (by decide +kernel)

theorem valid3680 : plan3680.Valid := valid_step _ _ _ valid2539 (by decide +kernel)

theorem valid3681 : plan3681.Valid := valid_step _ _ _ valid2540 (by decide +kernel)

theorem valid3682 : plan3682.Valid := valid_step _ _ _ valid2544 (by decide +kernel)

theorem valid3683 : plan3683.Valid := valid_step _ _ _ valid2545 (by decide +kernel)

theorem valid3684 : plan3684.Valid := valid_step _ _ _ valid2546 (by decide +kernel)
























































































































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































theorem valid1360 : plan1360.Valid := valid_step _ _ _ valid495 (by decide +kernel)



theorem valid1362 : plan1362.Valid := valid_step _ _ _ valid497 (by decide +kernel)











theorem valid1368 : plan1368.Valid := valid_step _ _ _ valid503 (by decide +kernel)



theorem valid1370 : plan1370.Valid := valid_step _ _ _ valid494 (by decide +kernel)

theorem valid1371 : plan1371.Valid := valid_step _ _ _ valid495 (by decide +kernel)

theorem valid1372 : plan1372.Valid := valid_step _ _ _ valid496 (by decide +kernel)

theorem valid1373 : plan1373.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1374 : plan1374.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1375 : plan1375.Valid := valid_step _ _ _ valid504 (by decide +kernel)

theorem valid1376 : plan1376.Valid := valid_step _ _ _ valid497 (by decide +kernel)



















theorem valid1386 : plan1386.Valid := valid_step _ _ _ valid495 (by decide +kernel)



theorem valid1388 : plan1388.Valid := valid_step _ _ _ valid497 (by decide +kernel)











theorem valid1394 : plan1394.Valid := valid_step _ _ _ valid503 (by decide +kernel)



theorem valid1396 : plan1396.Valid := valid_step _ _ _ valid497 (by decide +kernel)

theorem valid1397 : plan1397.Valid := valid_step _ _ _ valid503 (by decide +kernel)

theorem valid1398 : plan1398.Valid := valid_step _ _ _ valid504 (by decide +kernel)




















































































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

theorem valid2593 : plan2593.Valid := valid_step _ _ _ valid1283 (by decide +kernel)





theorem valid2596 : plan2596.Valid := valid_step _ _ _ valid1286 (by decide +kernel)

theorem valid2597 : plan2597.Valid := valid_step _ _ _ valid1287 (by decide +kernel)

theorem valid2598 : plan2598.Valid := valid_step _ _ _ valid1288 (by decide +kernel)

theorem valid2599 : plan2599.Valid := valid_step _ _ _ valid1289 (by decide +kernel)





theorem valid2602 : plan2602.Valid := valid_step _ _ _ valid1292 (by decide +kernel)





theorem valid2605 : plan2605.Valid := valid_step _ _ _ valid1295 (by decide +kernel)

theorem valid2606 : plan2606.Valid := valid_step _ _ _ valid1296 (by decide +kernel)







theorem valid2610 : plan2610.Valid := valid_step _ _ _ valid1301 (by decide +kernel)

theorem valid2611 : plan2611.Valid := valid_step _ _ _ valid1302 (by decide +kernel)

theorem valid2612 : plan2612.Valid := valid_step _ _ _ valid1303 (by decide +kernel)



























































































































theorem valid2674 : plan2674.Valid := valid_step _ _ _ valid1360 (by decide +kernel)



theorem valid2676 : plan2676.Valid := valid_step _ _ _ valid1362 (by decide +kernel)



theorem valid2678 : plan2678.Valid := valid_step _ _ _ valid1368 (by decide +kernel)



theorem valid2680 : plan2680.Valid := valid_step _ _ _ valid1370 (by decide +kernel)

theorem valid2681 : plan2681.Valid := valid_step _ _ _ valid1371 (by decide +kernel)

theorem valid2682 : plan2682.Valid := valid_step _ _ _ valid1372 (by decide +kernel)

theorem valid2683 : plan2683.Valid := valid_step _ _ _ valid1373 (by decide +kernel)

theorem valid2684 : plan2684.Valid := valid_step _ _ _ valid1374 (by decide +kernel)

theorem valid2685 : plan2685.Valid := valid_step _ _ _ valid1375 (by decide +kernel)

theorem valid2686 : plan2686.Valid := valid_step _ _ _ valid1376 (by decide +kernel)




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





























theorem valid3759 : plan3759.Valid := valid_step _ _ _ valid2564 (by decide +kernel)

theorem valid3760 : plan3760.Valid := valid_step _ _ _ valid2566 (by decide +kernel)

theorem valid3761 : plan3761.Valid := valid_step _ _ _ valid2568 (by decide +kernel)

theorem valid3762 : plan3762.Valid := valid_step _ _ _ valid2570 (by decide +kernel)

theorem valid3763 : plan3763.Valid := valid_step _ _ _ valid2571 (by decide +kernel)

theorem valid3764 : plan3764.Valid := valid_step _ _ _ valid2572 (by decide +kernel)

theorem valid3765 : plan3765.Valid := valid_step _ _ _ valid2573 (by decide +kernel)

theorem valid3766 : plan3766.Valid := valid_step _ _ _ valid2574 (by decide +kernel)

theorem valid3767 : plan3767.Valid := valid_step _ _ _ valid2575 (by decide +kernel)

theorem valid3768 : plan3768.Valid := valid_step _ _ _ valid2578 (by decide +kernel)

theorem valid3769 : plan3769.Valid := valid_step _ _ _ valid2582 (by decide +kernel)

theorem valid3770 : plan3770.Valid := valid_step _ _ _ valid2593 (by decide +kernel)

theorem valid3771 : plan3771.Valid := valid_step _ _ _ valid2596 (by decide +kernel)

theorem valid3772 : plan3772.Valid := valid_step _ _ _ valid2597 (by decide +kernel)

theorem valid3773 : plan3773.Valid := valid_step _ _ _ valid2598 (by decide +kernel)

theorem valid3774 : plan3774.Valid := valid_step _ _ _ valid2599 (by decide +kernel)

theorem valid3775 : plan3775.Valid := valid_step _ _ _ valid2602 (by decide +kernel)

theorem valid3776 : plan3776.Valid := valid_step _ _ _ valid2605 (by decide +kernel)

theorem valid3777 : plan3777.Valid := valid_step _ _ _ valid2606 (by decide +kernel)

theorem valid3778 : plan3778.Valid := valid_step _ _ _ valid2610 (by decide +kernel)

theorem valid3779 : plan3779.Valid := valid_step _ _ _ valid2611 (by decide +kernel)

theorem valid3780 : plan3780.Valid := valid_step _ _ _ valid2612 (by decide +kernel)
























































































































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





theorem valid2691 : plan2691.Valid := valid_step _ _ _ valid1386 (by decide +kernel)



theorem valid2693 : plan2693.Valid := valid_step _ _ _ valid1388 (by decide +kernel)



theorem valid2695 : plan2695.Valid := valid_step _ _ _ valid1394 (by decide +kernel)



theorem valid2697 : plan2697.Valid := valid_step _ _ _ valid1396 (by decide +kernel)

theorem valid2698 : plan2698.Valid := valid_step _ _ _ valid1397 (by decide +kernel)

theorem valid2699 : plan2699.Valid := valid_step _ _ _ valid1398 (by decide +kernel)










































































































































































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































































































































theorem valid4000 : plan4000.Valid := valid_step _ _ _ valid2674 (by decide +kernel)

theorem valid4001 : plan4001.Valid := valid_step _ _ _ valid2676 (by decide +kernel)

theorem valid4002 : plan4002.Valid := valid_step _ _ _ valid2678 (by decide +kernel)

theorem valid4003 : plan4003.Valid := valid_step _ _ _ valid2680 (by decide +kernel)

theorem valid4004 : plan4004.Valid := valid_step _ _ _ valid2681 (by decide +kernel)

theorem valid4005 : plan4005.Valid := valid_step _ _ _ valid2682 (by decide +kernel)

theorem valid4006 : plan4006.Valid := valid_step _ _ _ valid2683 (by decide +kernel)

theorem valid4007 : plan4007.Valid := valid_step _ _ _ valid2684 (by decide +kernel)

theorem valid4008 : plan4008.Valid := valid_step _ _ _ valid2685 (by decide +kernel)

theorem valid4009 : plan4009.Valid := valid_step _ _ _ valid2686 (by decide +kernel)

theorem valid4010 : plan4010.Valid := valid_step _ _ _ valid2691 (by decide +kernel)

theorem valid4011 : plan4011.Valid := valid_step _ _ _ valid2693 (by decide +kernel)

theorem valid4012 : plan4012.Valid := valid_step _ _ _ valid2695 (by decide +kernel)

theorem valid4013 : plan4013.Valid := valid_step _ _ _ valid2697 (by decide +kernel)

theorem valid4014 : plan4014.Valid := valid_step _ _ _ valid2698 (by decide +kernel)

theorem valid4015 : plan4015.Valid := valid_step _ _ _ valid2699 (by decide +kernel)


































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
theorem t4_688choices : plan2276.choices=[8,2,9,7].map (options 4 3) := by rfl


theorem t4_688part0 : t4_688jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_688frontier : t4_688root.frontier 0=t4_688jobs := by rfl
theorem t4_688all : t4_688jobs.all (Job.check tree)=true := by
  simp only [t4_688jobs,List.all_append,List.all_nil,t4_688part0,Bool.and_self]
theorem t4_688checked : Checked tree [8,2,9,7] := by
  refine ⟨plan2276,valid2276,t4_688choices,?_⟩
  exact check_of_frontier tree 0 t4_688root t4_688jobs t4_688frontier t4_688all
theorem t4_689choices : plan2277.choices=[8,2,9,9].map (options 4 3) := by rfl


theorem t4_689part0 : t4_689jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_689frontier : t4_689root.frontier 0=t4_689jobs := by rfl
theorem t4_689all : t4_689jobs.all (Job.check tree)=true := by
  simp only [t4_689jobs,List.all_append,List.all_nil,t4_689part0,Bool.and_self]
theorem t4_689checked : Checked tree [8,2,9,9] := by
  refine ⟨plan2277,valid2277,t4_689choices,?_⟩
  exact check_of_frontier tree 0 t4_689root t4_689jobs t4_689frontier t4_689all
theorem t4_690choices : plan2278.choices=[8,2,9,10].map (options 4 3) := by rfl


theorem t4_690part0 : t4_690jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_690frontier : t4_690root.frontier 0=t4_690jobs := by rfl
theorem t4_690all : t4_690jobs.all (Job.check tree)=true := by
  simp only [t4_690jobs,List.all_append,List.all_nil,t4_690part0,Bool.and_self]
theorem t4_690checked : Checked tree [8,2,9,10] := by
  refine ⟨plan2278,valid2278,t4_690choices,?_⟩
  exact check_of_frontier tree 0 t4_690root t4_690jobs t4_690frontier t4_690all
theorem t4_691choices : plan2279.choices=[8,2,10,7].map (options 4 3) := by rfl


theorem t4_691part0 : t4_691jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_691frontier : t4_691root.frontier 0=t4_691jobs := by rfl
theorem t4_691all : t4_691jobs.all (Job.check tree)=true := by
  simp only [t4_691jobs,List.all_append,List.all_nil,t4_691part0,Bool.and_self]
theorem t4_691checked : Checked tree [8,2,10,7] := by
  refine ⟨plan2279,valid2279,t4_691choices,?_⟩
  exact check_of_frontier tree 0 t4_691root t4_691jobs t4_691frontier t4_691all
theorem t4_692choices : plan2280.choices=[8,2,10,10].map (options 4 3) := by rfl


theorem t4_692part0 : t4_692jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_692frontier : t4_692root.frontier 0=t4_692jobs := by rfl
theorem t4_692all : t4_692jobs.all (Job.check tree)=true := by
  simp only [t4_692jobs,List.all_append,List.all_nil,t4_692part0,Bool.and_self]
theorem t4_692checked : Checked tree [8,2,10,10] := by
  refine ⟨plan2280,valid2280,t4_692choices,?_⟩
  exact check_of_frontier tree 0 t4_692root t4_692jobs t4_692frontier t4_692all
theorem t4_693choices : plan1802.choices=[8,3,3,3].map (options 4 1) := by rfl


theorem t4_693part0 : t4_693jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_693frontier : t4_693root.frontier 0=t4_693jobs := by rfl
theorem t4_693all : t4_693jobs.all (Job.check tree)=true := by
  simp only [t4_693jobs,List.all_append,List.all_nil,t4_693part0,Bool.and_self]
theorem t4_693checked : Checked tree [8,3,3,3] := by
  refine ⟨plan1802,valid1802,t4_693choices,?_⟩
  exact check_of_frontier tree 0 t4_693root t4_693jobs t4_693frontier t4_693all
theorem t4_694choices : plan2008.choices=[8,3,3,6].map (options 4 2) := by rfl


theorem t4_694part0 : t4_694jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_694frontier : t4_694root.frontier 0=t4_694jobs := by rfl
theorem t4_694all : t4_694jobs.all (Job.check tree)=true := by
  simp only [t4_694jobs,List.all_append,List.all_nil,t4_694part0,Bool.and_self]
theorem t4_694checked : Checked tree [8,3,3,6] := by
  refine ⟨plan2008,valid2008,t4_694choices,?_⟩
  exact check_of_frontier tree 0 t4_694root t4_694jobs t4_694frontier t4_694all
theorem t4_695choices : plan2009.choices=[8,3,3,7].map (options 4 2) := by rfl


theorem t4_695part0 : t4_695jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_695frontier : t4_695root.frontier 0=t4_695jobs := by rfl
theorem t4_695all : t4_695jobs.all (Job.check tree)=true := by
  simp only [t4_695jobs,List.all_append,List.all_nil,t4_695part0,Bool.and_self]
theorem t4_695checked : Checked tree [8,3,3,7] := by
  refine ⟨plan2009,valid2009,t4_695choices,?_⟩
  exact check_of_frontier tree 0 t4_695root t4_695jobs t4_695frontier t4_695all
theorem t4_696choices : plan2010.choices=[8,3,3,10].map (options 4 2) := by rfl


theorem t4_696part0 : t4_696jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_696frontier : t4_696root.frontier 0=t4_696jobs := by rfl
theorem t4_696all : t4_696jobs.all (Job.check tree)=true := by
  simp only [t4_696jobs,List.all_append,List.all_nil,t4_696part0,Bool.and_self]
theorem t4_696checked : Checked tree [8,3,3,10] := by
  refine ⟨plan2010,valid2010,t4_696choices,?_⟩
  exact check_of_frontier tree 0 t4_696root t4_696jobs t4_696frontier t4_696all
theorem t4_697choices : plan2281.choices=[8,3,6,6].map (options 4 3) := by rfl


theorem t4_697part0 : t4_697jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_697frontier : t4_697root.frontier 0=t4_697jobs := by rfl
theorem t4_697all : t4_697jobs.all (Job.check tree)=true := by
  simp only [t4_697jobs,List.all_append,List.all_nil,t4_697part0,Bool.and_self]
theorem t4_697checked : Checked tree [8,3,6,6] := by
  refine ⟨plan2281,valid2281,t4_697choices,?_⟩
  exact check_of_frontier tree 0 t4_697root t4_697jobs t4_697frontier t4_697all
theorem t4_698choices : plan2282.choices=[8,3,6,7].map (options 4 3) := by rfl


theorem t4_698part0 : t4_698jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_698frontier : t4_698root.frontier 0=t4_698jobs := by rfl
theorem t4_698all : t4_698jobs.all (Job.check tree)=true := by
  simp only [t4_698jobs,List.all_append,List.all_nil,t4_698part0,Bool.and_self]
theorem t4_698checked : Checked tree [8,3,6,7] := by
  refine ⟨plan2282,valid2282,t4_698choices,?_⟩
  exact check_of_frontier tree 0 t4_698root t4_698jobs t4_698frontier t4_698all
theorem t4_699choices : plan2283.choices=[8,3,6,10].map (options 4 3) := by rfl


theorem t4_699part0 : t4_699jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_699frontier : t4_699root.frontier 0=t4_699jobs := by rfl
theorem t4_699all : t4_699jobs.all (Job.check tree)=true := by
  simp only [t4_699jobs,List.all_append,List.all_nil,t4_699part0,Bool.and_self]
theorem t4_699checked : Checked tree [8,3,6,10] := by
  refine ⟨plan2283,valid2283,t4_699choices,?_⟩
  exact check_of_frontier tree 0 t4_699root t4_699jobs t4_699frontier t4_699all
theorem t4_700choices : plan2284.choices=[8,3,7,7].map (options 4 3) := by rfl


theorem t4_700part0 : t4_700jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_700frontier : t4_700root.frontier 0=t4_700jobs := by rfl
theorem t4_700all : t4_700jobs.all (Job.check tree)=true := by
  simp only [t4_700jobs,List.all_append,List.all_nil,t4_700part0,Bool.and_self]
theorem t4_700checked : Checked tree [8,3,7,7] := by
  refine ⟨plan2284,valid2284,t4_700choices,?_⟩
  exact check_of_frontier tree 0 t4_700root t4_700jobs t4_700frontier t4_700all
theorem t4_701choices : plan2285.choices=[8,3,10,7].map (options 4 3) := by rfl


theorem t4_701part0 : t4_701jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_701frontier : t4_701root.frontier 0=t4_701jobs := by rfl
theorem t4_701all : t4_701jobs.all (Job.check tree)=true := by
  simp only [t4_701jobs,List.all_append,List.all_nil,t4_701part0,Bool.and_self]
theorem t4_701checked : Checked tree [8,3,10,7] := by
  refine ⟨plan2285,valid2285,t4_701choices,?_⟩
  exact check_of_frontier tree 0 t4_701root t4_701jobs t4_701frontier t4_701all
theorem t4_702choices : plan2286.choices=[8,3,10,10].map (options 4 3) := by rfl


theorem t4_702part0 : t4_702jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_702frontier : t4_702root.frontier 0=t4_702jobs := by rfl
theorem t4_702all : t4_702jobs.all (Job.check tree)=true := by
  simp only [t4_702jobs,List.all_append,List.all_nil,t4_702part0,Bool.and_self]
theorem t4_702checked : Checked tree [8,3,10,10] := by
  refine ⟨plan2286,valid2286,t4_702choices,?_⟩
  exact check_of_frontier tree 0 t4_702root t4_702jobs t4_702frontier t4_702all
theorem t4_703choices : plan2011.choices=[8,5,3,3].map (options 4 2) := by rfl


theorem t4_703part0 : t4_703jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_703frontier : t4_703root.frontier 0=t4_703jobs := by rfl
theorem t4_703all : t4_703jobs.all (Job.check tree)=true := by
  simp only [t4_703jobs,List.all_append,List.all_nil,t4_703part0,Bool.and_self]
theorem t4_703checked : Checked tree [8,5,3,3] := by
  refine ⟨plan2011,valid2011,t4_703choices,?_⟩
  exact check_of_frontier tree 0 t4_703root t4_703jobs t4_703frontier t4_703all
theorem t4_704choices : plan2287.choices=[8,5,3,6].map (options 4 3) := by rfl


theorem t4_704part0 : t4_704jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_704frontier : t4_704root.frontier 0=t4_704jobs := by rfl
theorem t4_704all : t4_704jobs.all (Job.check tree)=true := by
  simp only [t4_704jobs,List.all_append,List.all_nil,t4_704part0,Bool.and_self]
theorem t4_704checked : Checked tree [8,5,3,6] := by
  refine ⟨plan2287,valid2287,t4_704choices,?_⟩
  exact check_of_frontier tree 0 t4_704root t4_704jobs t4_704frontier t4_704all
theorem t4_705choices : plan2288.choices=[8,5,3,7].map (options 4 3) := by rfl


theorem t4_705part0 : t4_705jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_705frontier : t4_705root.frontier 0=t4_705jobs := by rfl
theorem t4_705all : t4_705jobs.all (Job.check tree)=true := by
  simp only [t4_705jobs,List.all_append,List.all_nil,t4_705part0,Bool.and_self]
theorem t4_705checked : Checked tree [8,5,3,7] := by
  refine ⟨plan2288,valid2288,t4_705choices,?_⟩
  exact check_of_frontier tree 0 t4_705root t4_705jobs t4_705frontier t4_705all
theorem t4_706choices : plan2289.choices=[8,5,3,10].map (options 4 3) := by rfl


theorem t4_706part0 : t4_706jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_706frontier : t4_706root.frontier 0=t4_706jobs := by rfl
theorem t4_706all : t4_706jobs.all (Job.check tree)=true := by
  simp only [t4_706jobs,List.all_append,List.all_nil,t4_706part0,Bool.and_self]
theorem t4_706checked : Checked tree [8,5,3,10] := by
  refine ⟨plan2289,valid2289,t4_706choices,?_⟩
  exact check_of_frontier tree 0 t4_706root t4_706jobs t4_706frontier t4_706all
theorem t4_707choices : plan2290.choices=[8,5,5,3].map (options 4 3) := by rfl


theorem t4_707part0 : t4_707jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_707frontier : t4_707root.frontier 0=t4_707jobs := by rfl
theorem t4_707all : t4_707jobs.all (Job.check tree)=true := by
  simp only [t4_707jobs,List.all_append,List.all_nil,t4_707part0,Bool.and_self]
theorem t4_707checked : Checked tree [8,5,5,3] := by
  refine ⟨plan2290,valid2290,t4_707choices,?_⟩
  exact check_of_frontier tree 0 t4_707root t4_707jobs t4_707frontier t4_707all
theorem t4_708choices : plan2437.choices=[8,5,5,5].map (options 4 4) := by rfl


theorem t4_708part0 : t4_708jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_708frontier : t4_708root.frontier 0=t4_708jobs := by rfl
theorem t4_708all : t4_708jobs.all (Job.check tree)=true := by
  simp only [t4_708jobs,List.all_append,List.all_nil,t4_708part0,Bool.and_self]
theorem t4_708checked : Checked tree [8,5,5,5] := by
  refine ⟨plan2437,valid2437,t4_708choices,?_⟩
  exact check_of_frontier tree 0 t4_708root t4_708jobs t4_708frontier t4_708all
theorem t4_709choices : plan2438.choices=[8,5,5,6].map (options 4 4) := by rfl


theorem t4_709part0 : t4_709jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_709frontier : t4_709root.frontier 0=t4_709jobs := by rfl
theorem t4_709all : t4_709jobs.all (Job.check tree)=true := by
  simp only [t4_709jobs,List.all_append,List.all_nil,t4_709part0,Bool.and_self]
theorem t4_709checked : Checked tree [8,5,5,6] := by
  refine ⟨plan2438,valid2438,t4_709choices,?_⟩
  exact check_of_frontier tree 0 t4_709root t4_709jobs t4_709frontier t4_709all
theorem t4_710choices : plan2439.choices=[8,5,5,7].map (options 4 4) := by rfl


theorem t4_710part0 : t4_710jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_710frontier : t4_710root.frontier 0=t4_710jobs := by rfl
theorem t4_710all : t4_710jobs.all (Job.check tree)=true := by
  simp only [t4_710jobs,List.all_append,List.all_nil,t4_710part0,Bool.and_self]
theorem t4_710checked : Checked tree [8,5,5,7] := by
  refine ⟨plan2439,valid2439,t4_710choices,?_⟩
  exact check_of_frontier tree 0 t4_710root t4_710jobs t4_710frontier t4_710all
theorem t4_711choices : plan2440.choices=[8,5,5,9].map (options 4 4) := by rfl


theorem t4_711part0 : t4_711jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_711frontier : t4_711root.frontier 0=t4_711jobs := by rfl
theorem t4_711all : t4_711jobs.all (Job.check tree)=true := by
  simp only [t4_711jobs,List.all_append,List.all_nil,t4_711part0,Bool.and_self]
theorem t4_711checked : Checked tree [8,5,5,9] := by
  refine ⟨plan2440,valid2440,t4_711choices,?_⟩
  exact check_of_frontier tree 0 t4_711root t4_711jobs t4_711frontier t4_711all
theorem t4_712choices : plan2441.choices=[8,5,5,10].map (options 4 4) := by rfl


theorem t4_712part0 : t4_712jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_712frontier : t4_712root.frontier 0=t4_712jobs := by rfl
theorem t4_712all : t4_712jobs.all (Job.check tree)=true := by
  simp only [t4_712jobs,List.all_append,List.all_nil,t4_712part0,Bool.and_self]
theorem t4_712checked : Checked tree [8,5,5,10] := by
  refine ⟨plan2441,valid2441,t4_712choices,?_⟩
  exact check_of_frontier tree 0 t4_712root t4_712jobs t4_712frontier t4_712all
theorem t4_713choices : plan2442.choices=[8,5,6,6].map (options 4 4) := by rfl


theorem t4_713part0 : t4_713jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_713frontier : t4_713root.frontier 0=t4_713jobs := by rfl
theorem t4_713all : t4_713jobs.all (Job.check tree)=true := by
  simp only [t4_713jobs,List.all_append,List.all_nil,t4_713part0,Bool.and_self]
theorem t4_713checked : Checked tree [8,5,6,6] := by
  refine ⟨plan2442,valid2442,t4_713choices,?_⟩
  exact check_of_frontier tree 0 t4_713root t4_713jobs t4_713frontier t4_713all
theorem t4_714choices : plan2443.choices=[8,5,6,7].map (options 4 4) := by rfl


theorem t4_714part0 : t4_714jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_714frontier : t4_714root.frontier 0=t4_714jobs := by rfl
theorem t4_714all : t4_714jobs.all (Job.check tree)=true := by
  simp only [t4_714jobs,List.all_append,List.all_nil,t4_714part0,Bool.and_self]
theorem t4_714checked : Checked tree [8,5,6,7] := by
  refine ⟨plan2443,valid2443,t4_714choices,?_⟩
  exact check_of_frontier tree 0 t4_714root t4_714jobs t4_714frontier t4_714all
theorem t4_715choices : plan2444.choices=[8,5,6,10].map (options 4 4) := by rfl


theorem t4_715part0 : t4_715jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_715frontier : t4_715root.frontier 0=t4_715jobs := by rfl
theorem t4_715all : t4_715jobs.all (Job.check tree)=true := by
  simp only [t4_715jobs,List.all_append,List.all_nil,t4_715part0,Bool.and_self]
theorem t4_715checked : Checked tree [8,5,6,10] := by
  refine ⟨plan2444,valid2444,t4_715choices,?_⟩
  exact check_of_frontier tree 0 t4_715root t4_715jobs t4_715frontier t4_715all
theorem t4_716choices : plan2445.choices=[8,5,7,7].map (options 4 4) := by rfl


theorem t4_716part0 : t4_716jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_716frontier : t4_716root.frontier 0=t4_716jobs := by rfl
theorem t4_716all : t4_716jobs.all (Job.check tree)=true := by
  simp only [t4_716jobs,List.all_append,List.all_nil,t4_716part0,Bool.and_self]
theorem t4_716checked : Checked tree [8,5,7,7] := by
  refine ⟨plan2445,valid2445,t4_716choices,?_⟩
  exact check_of_frontier tree 0 t4_716root t4_716jobs t4_716frontier t4_716all
theorem t4_717choices : plan2291.choices=[8,5,9,3].map (options 4 3) := by rfl


theorem t4_717part0 : t4_717jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_717frontier : t4_717root.frontier 0=t4_717jobs := by rfl
theorem t4_717all : t4_717jobs.all (Job.check tree)=true := by
  simp only [t4_717jobs,List.all_append,List.all_nil,t4_717part0,Bool.and_self]
theorem t4_717checked : Checked tree [8,5,9,3] := by
  refine ⟨plan2291,valid2291,t4_717choices,?_⟩
  exact check_of_frontier tree 0 t4_717root t4_717jobs t4_717frontier t4_717all
theorem t4_718choices : plan2446.choices=[8,5,9,6].map (options 4 4) := by rfl


theorem t4_718part0 : t4_718jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_718frontier : t4_718root.frontier 0=t4_718jobs := by rfl
theorem t4_718all : t4_718jobs.all (Job.check tree)=true := by
  simp only [t4_718jobs,List.all_append,List.all_nil,t4_718part0,Bool.and_self]
theorem t4_718checked : Checked tree [8,5,9,6] := by
  refine ⟨plan2446,valid2446,t4_718choices,?_⟩
  exact check_of_frontier tree 0 t4_718root t4_718jobs t4_718frontier t4_718all
theorem t4_719choices : plan2447.choices=[8,5,9,7].map (options 4 4) := by rfl


theorem t4_719part0 : t4_719jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_719frontier : t4_719root.frontier 0=t4_719jobs := by rfl
theorem t4_719all : t4_719jobs.all (Job.check tree)=true := by
  simp only [t4_719jobs,List.all_append,List.all_nil,t4_719part0,Bool.and_self]
theorem t4_719checked : Checked tree [8,5,9,7] := by
  refine ⟨plan2447,valid2447,t4_719choices,?_⟩
  exact check_of_frontier tree 0 t4_719root t4_719jobs t4_719frontier t4_719all
theorem t4_720choices : plan2448.choices=[8,5,9,9].map (options 4 4) := by rfl


theorem t4_720part0 : t4_720jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_720frontier : t4_720root.frontier 0=t4_720jobs := by rfl
theorem t4_720all : t4_720jobs.all (Job.check tree)=true := by
  simp only [t4_720jobs,List.all_append,List.all_nil,t4_720part0,Bool.and_self]
theorem t4_720checked : Checked tree [8,5,9,9] := by
  refine ⟨plan2448,valid2448,t4_720choices,?_⟩
  exact check_of_frontier tree 0 t4_720root t4_720jobs t4_720frontier t4_720all
theorem t4_721choices : plan2449.choices=[8,5,9,10].map (options 4 4) := by rfl


theorem t4_721part0 : t4_721jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_721frontier : t4_721root.frontier 0=t4_721jobs := by rfl
theorem t4_721all : t4_721jobs.all (Job.check tree)=true := by
  simp only [t4_721jobs,List.all_append,List.all_nil,t4_721part0,Bool.and_self]
theorem t4_721checked : Checked tree [8,5,9,10] := by
  refine ⟨plan2449,valid2449,t4_721choices,?_⟩
  exact check_of_frontier tree 0 t4_721root t4_721jobs t4_721frontier t4_721all
theorem t4_722choices : plan2450.choices=[8,5,10,7].map (options 4 4) := by rfl


theorem t4_722part0 : t4_722jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_722frontier : t4_722root.frontier 0=t4_722jobs := by rfl
theorem t4_722all : t4_722jobs.all (Job.check tree)=true := by
  simp only [t4_722jobs,List.all_append,List.all_nil,t4_722part0,Bool.and_self]
theorem t4_722checked : Checked tree [8,5,10,7] := by
  refine ⟨plan2450,valid2450,t4_722choices,?_⟩
  exact check_of_frontier tree 0 t4_722root t4_722jobs t4_722frontier t4_722all
theorem t4_723choices : plan2451.choices=[8,5,10,10].map (options 4 4) := by rfl


theorem t4_723part0 : t4_723jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_723frontier : t4_723root.frontier 0=t4_723jobs := by rfl
theorem t4_723all : t4_723jobs.all (Job.check tree)=true := by
  simp only [t4_723jobs,List.all_append,List.all_nil,t4_723part0,Bool.and_self]
theorem t4_723checked : Checked tree [8,5,10,10] := by
  refine ⟨plan2451,valid2451,t4_723choices,?_⟩
  exact check_of_frontier tree 0 t4_723root t4_723jobs t4_723frontier t4_723all
theorem t4_724choices : plan2452.choices=[8,6,6,6].map (options 4 4) := by rfl


theorem t4_724part0 : t4_724jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_724frontier : t4_724root.frontier 0=t4_724jobs := by rfl
theorem t4_724all : t4_724jobs.all (Job.check tree)=true := by
  simp only [t4_724jobs,List.all_append,List.all_nil,t4_724part0,Bool.and_self]
theorem t4_724checked : Checked tree [8,6,6,6] := by
  refine ⟨plan2452,valid2452,t4_724choices,?_⟩
  exact check_of_frontier tree 0 t4_724root t4_724jobs t4_724frontier t4_724all
theorem t4_725choices : plan2453.choices=[8,6,6,7].map (options 4 4) := by rfl


theorem t4_725part0 : t4_725jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_725frontier : t4_725root.frontier 0=t4_725jobs := by rfl
theorem t4_725all : t4_725jobs.all (Job.check tree)=true := by
  simp only [t4_725jobs,List.all_append,List.all_nil,t4_725part0,Bool.and_self]
theorem t4_725checked : Checked tree [8,6,6,7] := by
  refine ⟨plan2453,valid2453,t4_725choices,?_⟩
  exact check_of_frontier tree 0 t4_725root t4_725jobs t4_725frontier t4_725all
theorem t4_726choices : plan2454.choices=[8,6,6,10].map (options 4 4) := by rfl


theorem t4_726part0 : t4_726jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_726frontier : t4_726root.frontier 0=t4_726jobs := by rfl
theorem t4_726all : t4_726jobs.all (Job.check tree)=true := by
  simp only [t4_726jobs,List.all_append,List.all_nil,t4_726part0,Bool.and_self]
theorem t4_726checked : Checked tree [8,6,6,10] := by
  refine ⟨plan2454,valid2454,t4_726choices,?_⟩
  exact check_of_frontier tree 0 t4_726root t4_726jobs t4_726frontier t4_726all
theorem t4_727choices : plan2455.choices=[8,6,7,7].map (options 4 4) := by rfl


theorem t4_727part0 : t4_727jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_727frontier : t4_727root.frontier 0=t4_727jobs := by rfl
theorem t4_727all : t4_727jobs.all (Job.check tree)=true := by
  simp only [t4_727jobs,List.all_append,List.all_nil,t4_727part0,Bool.and_self]
theorem t4_727checked : Checked tree [8,6,7,7] := by
  refine ⟨plan2455,valid2455,t4_727choices,?_⟩
  exact check_of_frontier tree 0 t4_727root t4_727jobs t4_727frontier t4_727all
theorem t4_728choices : plan2456.choices=[8,6,10,7].map (options 4 4) := by rfl


theorem t4_728part0 : t4_728jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_728frontier : t4_728root.frontier 0=t4_728jobs := by rfl
theorem t4_728all : t4_728jobs.all (Job.check tree)=true := by
  simp only [t4_728jobs,List.all_append,List.all_nil,t4_728part0,Bool.and_self]
theorem t4_728checked : Checked tree [8,6,10,7] := by
  refine ⟨plan2456,valid2456,t4_728choices,?_⟩
  exact check_of_frontier tree 0 t4_728root t4_728jobs t4_728frontier t4_728all
theorem t4_729choices : plan2457.choices=[8,6,10,10].map (options 4 4) := by rfl


theorem t4_729part0 : t4_729jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_729frontier : t4_729root.frontier 0=t4_729jobs := by rfl
theorem t4_729all : t4_729jobs.all (Job.check tree)=true := by
  simp only [t4_729jobs,List.all_append,List.all_nil,t4_729part0,Bool.and_self]
theorem t4_729checked : Checked tree [8,6,10,10] := by
  refine ⟨plan2457,valid2457,t4_729choices,?_⟩
  exact check_of_frontier tree 0 t4_729root t4_729jobs t4_729frontier t4_729all
theorem t4_730choices : plan2458.choices=[8,7,7,7].map (options 4 4) := by rfl


theorem t4_730part0 : t4_730jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_730frontier : t4_730root.frontier 0=t4_730jobs := by rfl
theorem t4_730all : t4_730jobs.all (Job.check tree)=true := by
  simp only [t4_730jobs,List.all_append,List.all_nil,t4_730part0,Bool.and_self]
theorem t4_730checked : Checked tree [8,7,7,7] := by
  refine ⟨plan2458,valid2458,t4_730choices,?_⟩
  exact check_of_frontier tree 0 t4_730root t4_730jobs t4_730frontier t4_730all
theorem t4_731choices : plan2012.choices=[8,8,2,2].map (options 4 2) := by rfl


theorem t4_731part0 : t4_731jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_731frontier : t4_731root.frontier 0=t4_731jobs := by rfl
theorem t4_731all : t4_731jobs.all (Job.check tree)=true := by
  simp only [t4_731jobs,List.all_append,List.all_nil,t4_731part0,Bool.and_self]
theorem t4_731checked : Checked tree [8,8,2,2] := by
  refine ⟨plan2012,valid2012,t4_731choices,?_⟩
  exact check_of_frontier tree 0 t4_731root t4_731jobs t4_731frontier t4_731all
theorem t4_732choices : plan2013.choices=[8,8,2,3].map (options 4 2) := by rfl


theorem t4_732part0 : t4_732jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_732frontier : t4_732root.frontier 0=t4_732jobs := by rfl
theorem t4_732all : t4_732jobs.all (Job.check tree)=true := by
  simp only [t4_732jobs,List.all_append,List.all_nil,t4_732part0,Bool.and_self]
theorem t4_732checked : Checked tree [8,8,2,3] := by
  refine ⟨plan2013,valid2013,t4_732choices,?_⟩
  exact check_of_frontier tree 0 t4_732root t4_732jobs t4_732frontier t4_732all
theorem t4_733choices : plan2292.choices=[8,8,2,5].map (options 4 3) := by rfl


theorem t4_733part0 : t4_733jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_733frontier : t4_733root.frontier 0=t4_733jobs := by rfl
theorem t4_733all : t4_733jobs.all (Job.check tree)=true := by
  simp only [t4_733jobs,List.all_append,List.all_nil,t4_733part0,Bool.and_self]
theorem t4_733checked : Checked tree [8,8,2,5] := by
  refine ⟨plan2292,valid2292,t4_733choices,?_⟩
  exact check_of_frontier tree 0 t4_733root t4_733jobs t4_733frontier t4_733all
theorem t4_734choices : plan2293.choices=[8,8,2,6].map (options 4 3) := by rfl


theorem t4_734part0 : t4_734jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_734frontier : t4_734root.frontier 0=t4_734jobs := by rfl
theorem t4_734all : t4_734jobs.all (Job.check tree)=true := by
  simp only [t4_734jobs,List.all_append,List.all_nil,t4_734part0,Bool.and_self]
theorem t4_734checked : Checked tree [8,8,2,6] := by
  refine ⟨plan2293,valid2293,t4_734choices,?_⟩
  exact check_of_frontier tree 0 t4_734root t4_734jobs t4_734frontier t4_734all
theorem t4_735choices : plan2294.choices=[8,8,2,7].map (options 4 3) := by rfl


theorem t4_735part0 : t4_735jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_735frontier : t4_735root.frontier 0=t4_735jobs := by rfl
theorem t4_735all : t4_735jobs.all (Job.check tree)=true := by
  simp only [t4_735jobs,List.all_append,List.all_nil,t4_735part0,Bool.and_self]
theorem t4_735checked : Checked tree [8,8,2,7] := by
  refine ⟨plan2294,valid2294,t4_735choices,?_⟩
  exact check_of_frontier tree 0 t4_735root t4_735jobs t4_735frontier t4_735all
theorem t4_736choices : plan2295.choices=[8,8,2,9].map (options 4 3) := by rfl


theorem t4_736part0 : t4_736jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_736frontier : t4_736root.frontier 0=t4_736jobs := by rfl
theorem t4_736all : t4_736jobs.all (Job.check tree)=true := by
  simp only [t4_736jobs,List.all_append,List.all_nil,t4_736part0,Bool.and_self]
theorem t4_736checked : Checked tree [8,8,2,9] := by
  refine ⟨plan2295,valid2295,t4_736choices,?_⟩
  exact check_of_frontier tree 0 t4_736root t4_736jobs t4_736frontier t4_736all
theorem t4_737choices : plan2296.choices=[8,8,2,10].map (options 4 3) := by rfl


theorem t4_737part0 : t4_737jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_737frontier : t4_737root.frontier 0=t4_737jobs := by rfl
theorem t4_737all : t4_737jobs.all (Job.check tree)=true := by
  simp only [t4_737jobs,List.all_append,List.all_nil,t4_737part0,Bool.and_self]
theorem t4_737checked : Checked tree [8,8,2,10] := by
  refine ⟨plan2296,valid2296,t4_737choices,?_⟩
  exact check_of_frontier tree 0 t4_737root t4_737jobs t4_737frontier t4_737all
theorem t4_738choices : plan2014.choices=[8,8,3,3].map (options 4 2) := by rfl


theorem t4_738part0 : t4_738jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_738frontier : t4_738root.frontier 0=t4_738jobs := by rfl
theorem t4_738all : t4_738jobs.all (Job.check tree)=true := by
  simp only [t4_738jobs,List.all_append,List.all_nil,t4_738part0,Bool.and_self]
theorem t4_738checked : Checked tree [8,8,3,3] := by
  refine ⟨plan2014,valid2014,t4_738choices,?_⟩
  exact check_of_frontier tree 0 t4_738root t4_738jobs t4_738frontier t4_738all
theorem t4_739choices : plan2297.choices=[8,8,3,6].map (options 4 3) := by rfl


theorem t4_739part0 : t4_739jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_739frontier : t4_739root.frontier 0=t4_739jobs := by rfl
theorem t4_739all : t4_739jobs.all (Job.check tree)=true := by
  simp only [t4_739jobs,List.all_append,List.all_nil,t4_739part0,Bool.and_self]
theorem t4_739checked : Checked tree [8,8,3,6] := by
  refine ⟨plan2297,valid2297,t4_739choices,?_⟩
  exact check_of_frontier tree 0 t4_739root t4_739jobs t4_739frontier t4_739all
theorem t4_740choices : plan2298.choices=[8,8,3,7].map (options 4 3) := by rfl


theorem t4_740part0 : t4_740jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_740frontier : t4_740root.frontier 0=t4_740jobs := by rfl
theorem t4_740all : t4_740jobs.all (Job.check tree)=true := by
  simp only [t4_740jobs,List.all_append,List.all_nil,t4_740part0,Bool.and_self]
theorem t4_740checked : Checked tree [8,8,3,7] := by
  refine ⟨plan2298,valid2298,t4_740choices,?_⟩
  exact check_of_frontier tree 0 t4_740root t4_740jobs t4_740frontier t4_740all
theorem t4_741choices : plan2299.choices=[8,8,3,10].map (options 4 3) := by rfl


theorem t4_741part0 : t4_741jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_741frontier : t4_741root.frontier 0=t4_741jobs := by rfl
theorem t4_741all : t4_741jobs.all (Job.check tree)=true := by
  simp only [t4_741jobs,List.all_append,List.all_nil,t4_741part0,Bool.and_self]
theorem t4_741checked : Checked tree [8,8,3,10] := by
  refine ⟨plan2299,valid2299,t4_741choices,?_⟩
  exact check_of_frontier tree 0 t4_741root t4_741jobs t4_741frontier t4_741all
theorem t4_742choices : plan2300.choices=[8,8,5,3].map (options 4 3) := by rfl


theorem t4_742part0 : t4_742jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_742frontier : t4_742root.frontier 0=t4_742jobs := by rfl
theorem t4_742all : t4_742jobs.all (Job.check tree)=true := by
  simp only [t4_742jobs,List.all_append,List.all_nil,t4_742part0,Bool.and_self]
theorem t4_742checked : Checked tree [8,8,5,3] := by
  refine ⟨plan2300,valid2300,t4_742choices,?_⟩
  exact check_of_frontier tree 0 t4_742root t4_742jobs t4_742frontier t4_742all
theorem t4_743choices : plan2459.choices=[8,8,5,5].map (options 4 4) := by rfl


theorem t4_743part0 : t4_743jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_743frontier : t4_743root.frontier 0=t4_743jobs := by rfl
theorem t4_743all : t4_743jobs.all (Job.check tree)=true := by
  simp only [t4_743jobs,List.all_append,List.all_nil,t4_743part0,Bool.and_self]
theorem t4_743checked : Checked tree [8,8,5,5] := by
  refine ⟨plan2459,valid2459,t4_743choices,?_⟩
  exact check_of_frontier tree 0 t4_743root t4_743jobs t4_743frontier t4_743all
theorem t4_744choices : plan2460.choices=[8,8,5,6].map (options 4 4) := by rfl


theorem t4_744part0 : t4_744jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_744frontier : t4_744root.frontier 0=t4_744jobs := by rfl
theorem t4_744all : t4_744jobs.all (Job.check tree)=true := by
  simp only [t4_744jobs,List.all_append,List.all_nil,t4_744part0,Bool.and_self]
theorem t4_744checked : Checked tree [8,8,5,6] := by
  refine ⟨plan2460,valid2460,t4_744choices,?_⟩
  exact check_of_frontier tree 0 t4_744root t4_744jobs t4_744frontier t4_744all
theorem t4_745choices : plan2461.choices=[8,8,5,7].map (options 4 4) := by rfl


theorem t4_745part0 : t4_745jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_745frontier : t4_745root.frontier 0=t4_745jobs := by rfl
theorem t4_745all : t4_745jobs.all (Job.check tree)=true := by
  simp only [t4_745jobs,List.all_append,List.all_nil,t4_745part0,Bool.and_self]
theorem t4_745checked : Checked tree [8,8,5,7] := by
  refine ⟨plan2461,valid2461,t4_745choices,?_⟩
  exact check_of_frontier tree 0 t4_745root t4_745jobs t4_745frontier t4_745all
theorem t4_746choices : plan2462.choices=[8,8,5,9].map (options 4 4) := by rfl


theorem t4_746part0 : t4_746jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_746frontier : t4_746root.frontier 0=t4_746jobs := by rfl
theorem t4_746all : t4_746jobs.all (Job.check tree)=true := by
  simp only [t4_746jobs,List.all_append,List.all_nil,t4_746part0,Bool.and_self]
theorem t4_746checked : Checked tree [8,8,5,9] := by
  refine ⟨plan2462,valid2462,t4_746choices,?_⟩
  exact check_of_frontier tree 0 t4_746root t4_746jobs t4_746frontier t4_746all
theorem t4_747choices : plan2463.choices=[8,8,5,10].map (options 4 4) := by rfl


theorem t4_747part0 : t4_747jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_747frontier : t4_747root.frontier 0=t4_747jobs := by rfl
theorem t4_747all : t4_747jobs.all (Job.check tree)=true := by
  simp only [t4_747jobs,List.all_append,List.all_nil,t4_747part0,Bool.and_self]
theorem t4_747checked : Checked tree [8,8,5,10] := by
  refine ⟨plan2463,valid2463,t4_747choices,?_⟩
  exact check_of_frontier tree 0 t4_747root t4_747jobs t4_747frontier t4_747all
theorem t4_748choices : plan2464.choices=[8,8,6,6].map (options 4 4) := by rfl


theorem t4_748part0 : t4_748jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_748frontier : t4_748root.frontier 0=t4_748jobs := by rfl
theorem t4_748all : t4_748jobs.all (Job.check tree)=true := by
  simp only [t4_748jobs,List.all_append,List.all_nil,t4_748part0,Bool.and_self]
theorem t4_748checked : Checked tree [8,8,6,6] := by
  refine ⟨plan2464,valid2464,t4_748choices,?_⟩
  exact check_of_frontier tree 0 t4_748root t4_748jobs t4_748frontier t4_748all
theorem t4_749choices : plan2465.choices=[8,8,6,7].map (options 4 4) := by rfl


theorem t4_749part0 : t4_749jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_749frontier : t4_749root.frontier 0=t4_749jobs := by rfl
theorem t4_749all : t4_749jobs.all (Job.check tree)=true := by
  simp only [t4_749jobs,List.all_append,List.all_nil,t4_749part0,Bool.and_self]
theorem t4_749checked : Checked tree [8,8,6,7] := by
  refine ⟨plan2465,valid2465,t4_749choices,?_⟩
  exact check_of_frontier tree 0 t4_749root t4_749jobs t4_749frontier t4_749all
theorem t4_750choices : plan2466.choices=[8,8,6,10].map (options 4 4) := by rfl


theorem t4_750part0 : t4_750jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_750frontier : t4_750root.frontier 0=t4_750jobs := by rfl
theorem t4_750all : t4_750jobs.all (Job.check tree)=true := by
  simp only [t4_750jobs,List.all_append,List.all_nil,t4_750part0,Bool.and_self]
theorem t4_750checked : Checked tree [8,8,6,10] := by
  refine ⟨plan2466,valid2466,t4_750choices,?_⟩
  exact check_of_frontier tree 0 t4_750root t4_750jobs t4_750frontier t4_750all
theorem t4_751choices : plan2467.choices=[8,8,7,7].map (options 4 4) := by rfl


theorem t4_751part0 : t4_751jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_751frontier : t4_751root.frontier 0=t4_751jobs := by rfl
theorem t4_751all : t4_751jobs.all (Job.check tree)=true := by
  simp only [t4_751jobs,List.all_append,List.all_nil,t4_751part0,Bool.and_self]
theorem t4_751checked : Checked tree [8,8,7,7] := by
  refine ⟨plan2467,valid2467,t4_751choices,?_⟩
  exact check_of_frontier tree 0 t4_751root t4_751jobs t4_751frontier t4_751all
theorem t4_752choices : plan2301.choices=[8,8,8,3].map (options 4 3) := by rfl


theorem t4_752part0 : t4_752jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_752frontier : t4_752root.frontier 0=t4_752jobs := by rfl
theorem t4_752all : t4_752jobs.all (Job.check tree)=true := by
  simp only [t4_752jobs,List.all_append,List.all_nil,t4_752part0,Bool.and_self]
theorem t4_752checked : Checked tree [8,8,8,3] := by
  refine ⟨plan2301,valid2301,t4_752choices,?_⟩
  exact check_of_frontier tree 0 t4_752root t4_752jobs t4_752frontier t4_752all
theorem t4_753choices : plan2468.choices=[8,8,8,6].map (options 4 4) := by rfl


theorem t4_753part0 : t4_753jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_753frontier : t4_753root.frontier 0=t4_753jobs := by rfl
theorem t4_753all : t4_753jobs.all (Job.check tree)=true := by
  simp only [t4_753jobs,List.all_append,List.all_nil,t4_753part0,Bool.and_self]
theorem t4_753checked : Checked tree [8,8,8,6] := by
  refine ⟨plan2468,valid2468,t4_753choices,?_⟩
  exact check_of_frontier tree 0 t4_753root t4_753jobs t4_753frontier t4_753all
theorem t4_754choices : plan2469.choices=[8,8,8,7].map (options 4 4) := by rfl


theorem t4_754part0 : t4_754jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_754frontier : t4_754root.frontier 0=t4_754jobs := by rfl
theorem t4_754all : t4_754jobs.all (Job.check tree)=true := by
  simp only [t4_754jobs,List.all_append,List.all_nil,t4_754part0,Bool.and_self]
theorem t4_754checked : Checked tree [8,8,8,7] := by
  refine ⟨plan2469,valid2469,t4_754choices,?_⟩
  exact check_of_frontier tree 0 t4_754root t4_754jobs t4_754frontier t4_754all
theorem t4_755choices : plan2470.choices=[8,8,8,10].map (options 4 4) := by rfl


theorem t4_755part0 : t4_755jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_755frontier : t4_755root.frontier 0=t4_755jobs := by rfl
theorem t4_755all : t4_755jobs.all (Job.check tree)=true := by
  simp only [t4_755jobs,List.all_append,List.all_nil,t4_755part0,Bool.and_self]
theorem t4_755checked : Checked tree [8,8,8,10] := by
  refine ⟨plan2470,valid2470,t4_755choices,?_⟩
  exact check_of_frontier tree 0 t4_755root t4_755jobs t4_755frontier t4_755all
theorem t4_756choices : plan2302.choices=[8,8,9,3].map (options 4 3) := by rfl


theorem t4_756part0 : t4_756jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_756frontier : t4_756root.frontier 0=t4_756jobs := by rfl
theorem t4_756all : t4_756jobs.all (Job.check tree)=true := by
  simp only [t4_756jobs,List.all_append,List.all_nil,t4_756part0,Bool.and_self]
theorem t4_756checked : Checked tree [8,8,9,3] := by
  refine ⟨plan2302,valid2302,t4_756choices,?_⟩
  exact check_of_frontier tree 0 t4_756root t4_756jobs t4_756frontier t4_756all
theorem t4_757choices : plan2471.choices=[8,8,9,6].map (options 4 4) := by rfl


theorem t4_757part0 : t4_757jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_757frontier : t4_757root.frontier 0=t4_757jobs := by rfl
theorem t4_757all : t4_757jobs.all (Job.check tree)=true := by
  simp only [t4_757jobs,List.all_append,List.all_nil,t4_757part0,Bool.and_self]
theorem t4_757checked : Checked tree [8,8,9,6] := by
  refine ⟨plan2471,valid2471,t4_757choices,?_⟩
  exact check_of_frontier tree 0 t4_757root t4_757jobs t4_757frontier t4_757all
theorem t4_758choices : plan2472.choices=[8,8,9,7].map (options 4 4) := by rfl


theorem t4_758part0 : t4_758jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_758frontier : t4_758root.frontier 0=t4_758jobs := by rfl
theorem t4_758all : t4_758jobs.all (Job.check tree)=true := by
  simp only [t4_758jobs,List.all_append,List.all_nil,t4_758part0,Bool.and_self]
theorem t4_758checked : Checked tree [8,8,9,7] := by
  refine ⟨plan2472,valid2472,t4_758choices,?_⟩
  exact check_of_frontier tree 0 t4_758root t4_758jobs t4_758frontier t4_758all
theorem t4_759choices : plan2473.choices=[8,8,9,9].map (options 4 4) := by rfl


theorem t4_759part0 : t4_759jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_759frontier : t4_759root.frontier 0=t4_759jobs := by rfl
theorem t4_759all : t4_759jobs.all (Job.check tree)=true := by
  simp only [t4_759jobs,List.all_append,List.all_nil,t4_759part0,Bool.and_self]
theorem t4_759checked : Checked tree [8,8,9,9] := by
  refine ⟨plan2473,valid2473,t4_759choices,?_⟩
  exact check_of_frontier tree 0 t4_759root t4_759jobs t4_759frontier t4_759all
theorem t4_760choices : plan2474.choices=[8,8,9,10].map (options 4 4) := by rfl


theorem t4_760part0 : t4_760jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_760frontier : t4_760root.frontier 0=t4_760jobs := by rfl
theorem t4_760all : t4_760jobs.all (Job.check tree)=true := by
  simp only [t4_760jobs,List.all_append,List.all_nil,t4_760part0,Bool.and_self]
theorem t4_760checked : Checked tree [8,8,9,10] := by
  refine ⟨plan2474,valid2474,t4_760choices,?_⟩
  exact check_of_frontier tree 0 t4_760root t4_760jobs t4_760frontier t4_760all
theorem t4_761choices : plan2475.choices=[8,8,10,7].map (options 4 4) := by rfl


theorem t4_761part0 : t4_761jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_761frontier : t4_761root.frontier 0=t4_761jobs := by rfl
theorem t4_761all : t4_761jobs.all (Job.check tree)=true := by
  simp only [t4_761jobs,List.all_append,List.all_nil,t4_761part0,Bool.and_self]
theorem t4_761checked : Checked tree [8,8,10,7] := by
  refine ⟨plan2475,valid2475,t4_761choices,?_⟩
  exact check_of_frontier tree 0 t4_761root t4_761jobs t4_761frontier t4_761all
theorem t4_762choices : plan2476.choices=[8,8,10,10].map (options 4 4) := by rfl


theorem t4_762part0 : t4_762jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_762frontier : t4_762root.frontier 0=t4_762jobs := by rfl
theorem t4_762all : t4_762jobs.all (Job.check tree)=true := by
  simp only [t4_762jobs,List.all_append,List.all_nil,t4_762part0,Bool.and_self]
theorem t4_762checked : Checked tree [8,8,10,10] := by
  refine ⟨plan2476,valid2476,t4_762choices,?_⟩
  exact check_of_frontier tree 0 t4_762root t4_762jobs t4_762frontier t4_762all
theorem t4_763choices : plan2015.choices=[8,9,3,3].map (options 4 2) := by rfl


theorem t4_763part0 : t4_763jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_763frontier : t4_763root.frontier 0=t4_763jobs := by rfl
theorem t4_763all : t4_763jobs.all (Job.check tree)=true := by
  simp only [t4_763jobs,List.all_append,List.all_nil,t4_763part0,Bool.and_self]
theorem t4_763checked : Checked tree [8,9,3,3] := by
  refine ⟨plan2015,valid2015,t4_763choices,?_⟩
  exact check_of_frontier tree 0 t4_763root t4_763jobs t4_763frontier t4_763all
theorem t4_764choices : plan2303.choices=[8,9,3,6].map (options 4 3) := by rfl


theorem t4_764part0 : t4_764jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_764frontier : t4_764root.frontier 0=t4_764jobs := by rfl
theorem t4_764all : t4_764jobs.all (Job.check tree)=true := by
  simp only [t4_764jobs,List.all_append,List.all_nil,t4_764part0,Bool.and_self]
theorem t4_764checked : Checked tree [8,9,3,6] := by
  refine ⟨plan2303,valid2303,t4_764choices,?_⟩
  exact check_of_frontier tree 0 t4_764root t4_764jobs t4_764frontier t4_764all
theorem t4_765choices : plan2304.choices=[8,9,3,7].map (options 4 3) := by rfl


theorem t4_765part0 : t4_765jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_765frontier : t4_765root.frontier 0=t4_765jobs := by rfl
theorem t4_765all : t4_765jobs.all (Job.check tree)=true := by
  simp only [t4_765jobs,List.all_append,List.all_nil,t4_765part0,Bool.and_self]
theorem t4_765checked : Checked tree [8,9,3,7] := by
  refine ⟨plan2304,valid2304,t4_765choices,?_⟩
  exact check_of_frontier tree 0 t4_765root t4_765jobs t4_765frontier t4_765all
theorem t4_766choices : plan2305.choices=[8,9,3,10].map (options 4 3) := by rfl


theorem t4_766part0 : t4_766jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_766frontier : t4_766root.frontier 0=t4_766jobs := by rfl
theorem t4_766all : t4_766jobs.all (Job.check tree)=true := by
  simp only [t4_766jobs,List.all_append,List.all_nil,t4_766part0,Bool.and_self]
theorem t4_766checked : Checked tree [8,9,3,10] := by
  refine ⟨plan2305,valid2305,t4_766choices,?_⟩
  exact check_of_frontier tree 0 t4_766root t4_766jobs t4_766frontier t4_766all
theorem t4_767choices : plan2477.choices=[8,9,6,6].map (options 4 4) := by rfl


theorem t4_767part0 : t4_767jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_767frontier : t4_767root.frontier 0=t4_767jobs := by rfl
theorem t4_767all : t4_767jobs.all (Job.check tree)=true := by
  simp only [t4_767jobs,List.all_append,List.all_nil,t4_767part0,Bool.and_self]
theorem t4_767checked : Checked tree [8,9,6,6] := by
  refine ⟨plan2477,valid2477,t4_767choices,?_⟩
  exact check_of_frontier tree 0 t4_767root t4_767jobs t4_767frontier t4_767all
theorem t4_768choices : plan2478.choices=[8,9,6,7].map (options 4 4) := by rfl


theorem t4_768part0 : t4_768jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_768frontier : t4_768root.frontier 0=t4_768jobs := by rfl
theorem t4_768all : t4_768jobs.all (Job.check tree)=true := by
  simp only [t4_768jobs,List.all_append,List.all_nil,t4_768part0,Bool.and_self]
theorem t4_768checked : Checked tree [8,9,6,7] := by
  refine ⟨plan2478,valid2478,t4_768choices,?_⟩
  exact check_of_frontier tree 0 t4_768root t4_768jobs t4_768frontier t4_768all
theorem t4_769choices : plan2479.choices=[8,9,6,10].map (options 4 4) := by rfl


theorem t4_769part0 : t4_769jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_769frontier : t4_769root.frontier 0=t4_769jobs := by rfl
theorem t4_769all : t4_769jobs.all (Job.check tree)=true := by
  simp only [t4_769jobs,List.all_append,List.all_nil,t4_769part0,Bool.and_self]
theorem t4_769checked : Checked tree [8,9,6,10] := by
  refine ⟨plan2479,valid2479,t4_769choices,?_⟩
  exact check_of_frontier tree 0 t4_769root t4_769jobs t4_769frontier t4_769all
theorem t4_770choices : plan2480.choices=[8,9,7,7].map (options 4 4) := by rfl


theorem t4_770part0 : t4_770jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_770frontier : t4_770root.frontier 0=t4_770jobs := by rfl
theorem t4_770all : t4_770jobs.all (Job.check tree)=true := by
  simp only [t4_770jobs,List.all_append,List.all_nil,t4_770part0,Bool.and_self]
theorem t4_770checked : Checked tree [8,9,7,7] := by
  refine ⟨plan2480,valid2480,t4_770choices,?_⟩
  exact check_of_frontier tree 0 t4_770root t4_770jobs t4_770frontier t4_770all
theorem t4_771choices : plan2306.choices=[8,9,9,3].map (options 4 3) := by rfl


theorem t4_771part0 : t4_771jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_771frontier : t4_771root.frontier 0=t4_771jobs := by rfl
theorem t4_771all : t4_771jobs.all (Job.check tree)=true := by
  simp only [t4_771jobs,List.all_append,List.all_nil,t4_771part0,Bool.and_self]
theorem t4_771checked : Checked tree [8,9,9,3] := by
  refine ⟨plan2306,valid2306,t4_771choices,?_⟩
  exact check_of_frontier tree 0 t4_771root t4_771jobs t4_771frontier t4_771all
theorem t4_772choices : plan2481.choices=[8,9,9,6].map (options 4 4) := by rfl


theorem t4_772part0 : t4_772jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_772frontier : t4_772root.frontier 0=t4_772jobs := by rfl
theorem t4_772all : t4_772jobs.all (Job.check tree)=true := by
  simp only [t4_772jobs,List.all_append,List.all_nil,t4_772part0,Bool.and_self]
theorem t4_772checked : Checked tree [8,9,9,6] := by
  refine ⟨plan2481,valid2481,t4_772choices,?_⟩
  exact check_of_frontier tree 0 t4_772root t4_772jobs t4_772frontier t4_772all
theorem t4_773choices : plan2482.choices=[8,9,9,7].map (options 4 4) := by rfl


theorem t4_773part0 : t4_773jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_773frontier : t4_773root.frontier 0=t4_773jobs := by rfl
theorem t4_773all : t4_773jobs.all (Job.check tree)=true := by
  simp only [t4_773jobs,List.all_append,List.all_nil,t4_773part0,Bool.and_self]
theorem t4_773checked : Checked tree [8,9,9,7] := by
  refine ⟨plan2482,valid2482,t4_773choices,?_⟩
  exact check_of_frontier tree 0 t4_773root t4_773jobs t4_773frontier t4_773all
theorem t4_774choices : plan2483.choices=[8,9,9,9].map (options 4 4) := by rfl


theorem t4_774part0 : t4_774jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_774frontier : t4_774root.frontier 0=t4_774jobs := by rfl
theorem t4_774all : t4_774jobs.all (Job.check tree)=true := by
  simp only [t4_774jobs,List.all_append,List.all_nil,t4_774part0,Bool.and_self]
theorem t4_774checked : Checked tree [8,9,9,9] := by
  refine ⟨plan2483,valid2483,t4_774choices,?_⟩
  exact check_of_frontier tree 0 t4_774root t4_774jobs t4_774frontier t4_774all
theorem t4_775choices : plan2484.choices=[8,9,9,10].map (options 4 4) := by rfl


theorem t4_775part0 : t4_775jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_775frontier : t4_775root.frontier 0=t4_775jobs := by rfl
theorem t4_775all : t4_775jobs.all (Job.check tree)=true := by
  simp only [t4_775jobs,List.all_append,List.all_nil,t4_775part0,Bool.and_self]
theorem t4_775checked : Checked tree [8,9,9,10] := by
  refine ⟨plan2484,valid2484,t4_775choices,?_⟩
  exact check_of_frontier tree 0 t4_775root t4_775jobs t4_775frontier t4_775all
theorem t4_776choices : plan2485.choices=[8,9,10,7].map (options 4 4) := by rfl


theorem t4_776part0 : t4_776jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_776frontier : t4_776root.frontier 0=t4_776jobs := by rfl
theorem t4_776all : t4_776jobs.all (Job.check tree)=true := by
  simp only [t4_776jobs,List.all_append,List.all_nil,t4_776part0,Bool.and_self]
theorem t4_776checked : Checked tree [8,9,10,7] := by
  refine ⟨plan2485,valid2485,t4_776choices,?_⟩
  exact check_of_frontier tree 0 t4_776root t4_776jobs t4_776frontier t4_776all
theorem t4_777choices : plan2486.choices=[8,9,10,10].map (options 4 4) := by rfl


theorem t4_777part0 : t4_777jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_777frontier : t4_777root.frontier 0=t4_777jobs := by rfl
theorem t4_777all : t4_777jobs.all (Job.check tree)=true := by
  simp only [t4_777jobs,List.all_append,List.all_nil,t4_777part0,Bool.and_self]
theorem t4_777checked : Checked tree [8,9,10,10] := by
  refine ⟨plan2486,valid2486,t4_777choices,?_⟩
  exact check_of_frontier tree 0 t4_777root t4_777jobs t4_777frontier t4_777all
theorem t4_778choices : plan2487.choices=[8,10,7,7].map (options 4 4) := by rfl


theorem t4_778part0 : t4_778jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_778frontier : t4_778root.frontier 0=t4_778jobs := by rfl
theorem t4_778all : t4_778jobs.all (Job.check tree)=true := by
  simp only [t4_778jobs,List.all_append,List.all_nil,t4_778part0,Bool.and_self]
theorem t4_778checked : Checked tree [8,10,7,7] := by
  refine ⟨plan2487,valid2487,t4_778choices,?_⟩
  exact check_of_frontier tree 0 t4_778root t4_778jobs t4_778frontier t4_778all
theorem t4_779choices : plan2488.choices=[8,10,10,7].map (options 4 4) := by rfl


theorem t4_779part0 : t4_779jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_779frontier : t4_779root.frontier 0=t4_779jobs := by rfl
theorem t4_779all : t4_779jobs.all (Job.check tree)=true := by
  simp only [t4_779jobs,List.all_append,List.all_nil,t4_779part0,Bool.and_self]
theorem t4_779checked : Checked tree [8,10,10,7] := by
  refine ⟨plan2488,valid2488,t4_779choices,?_⟩
  exact check_of_frontier tree 0 t4_779root t4_779jobs t4_779frontier t4_779all
theorem t4_780choices : plan2489.choices=[8,10,10,10].map (options 4 4) := by rfl


theorem t4_780part0 : t4_780jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_780frontier : t4_780root.frontier 0=t4_780jobs := by rfl
theorem t4_780all : t4_780jobs.all (Job.check tree)=true := by
  simp only [t4_780jobs,List.all_append,List.all_nil,t4_780part0,Bool.and_self]
theorem t4_780checked : Checked tree [8,10,10,10] := by
  refine ⟨plan2489,valid2489,t4_780choices,?_⟩
  exact check_of_frontier tree 0 t4_780root t4_780jobs t4_780frontier t4_780all
theorem t4_781choices : plan1803.choices=[9,3,3,3].map (options 4 1) := by rfl


theorem t4_781part0 : t4_781jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_781frontier : t4_781root.frontier 0=t4_781jobs := by rfl
theorem t4_781all : t4_781jobs.all (Job.check tree)=true := by
  simp only [t4_781jobs,List.all_append,List.all_nil,t4_781part0,Bool.and_self]
theorem t4_781checked : Checked tree [9,3,3,3] := by
  refine ⟨plan1803,valid1803,t4_781choices,?_⟩
  exact check_of_frontier tree 0 t4_781root t4_781jobs t4_781frontier t4_781all
theorem t4_782choices : plan2016.choices=[9,3,3,6].map (options 4 2) := by rfl


theorem t4_782part0 : t4_782jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_782frontier : t4_782root.frontier 0=t4_782jobs := by rfl
theorem t4_782all : t4_782jobs.all (Job.check tree)=true := by
  simp only [t4_782jobs,List.all_append,List.all_nil,t4_782part0,Bool.and_self]
theorem t4_782checked : Checked tree [9,3,3,6] := by
  refine ⟨plan2016,valid2016,t4_782choices,?_⟩
  exact check_of_frontier tree 0 t4_782root t4_782jobs t4_782frontier t4_782all
theorem t4_783choices : plan2017.choices=[9,3,3,7].map (options 4 2) := by rfl


theorem t4_783part0 : t4_783jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_783frontier : t4_783root.frontier 0=t4_783jobs := by rfl
theorem t4_783all : t4_783jobs.all (Job.check tree)=true := by
  simp only [t4_783jobs,List.all_append,List.all_nil,t4_783part0,Bool.and_self]
theorem t4_783checked : Checked tree [9,3,3,7] := by
  refine ⟨plan2017,valid2017,t4_783choices,?_⟩
  exact check_of_frontier tree 0 t4_783root t4_783jobs t4_783frontier t4_783all
theorem t4_784choices : plan2018.choices=[9,3,3,10].map (options 4 2) := by rfl


theorem t4_784part0 : t4_784jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_784frontier : t4_784root.frontier 0=t4_784jobs := by rfl
theorem t4_784all : t4_784jobs.all (Job.check tree)=true := by
  simp only [t4_784jobs,List.all_append,List.all_nil,t4_784part0,Bool.and_self]
theorem t4_784checked : Checked tree [9,3,3,10] := by
  refine ⟨plan2018,valid2018,t4_784choices,?_⟩
  exact check_of_frontier tree 0 t4_784root t4_784jobs t4_784frontier t4_784all
theorem t4_785choices : plan2307.choices=[9,3,6,6].map (options 4 3) := by rfl


theorem t4_785part0 : t4_785jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_785frontier : t4_785root.frontier 0=t4_785jobs := by rfl
theorem t4_785all : t4_785jobs.all (Job.check tree)=true := by
  simp only [t4_785jobs,List.all_append,List.all_nil,t4_785part0,Bool.and_self]
theorem t4_785checked : Checked tree [9,3,6,6] := by
  refine ⟨plan2307,valid2307,t4_785choices,?_⟩
  exact check_of_frontier tree 0 t4_785root t4_785jobs t4_785frontier t4_785all
theorem t4_786choices : plan2308.choices=[9,3,6,7].map (options 4 3) := by rfl


theorem t4_786part0 : t4_786jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_786frontier : t4_786root.frontier 0=t4_786jobs := by rfl
theorem t4_786all : t4_786jobs.all (Job.check tree)=true := by
  simp only [t4_786jobs,List.all_append,List.all_nil,t4_786part0,Bool.and_self]
theorem t4_786checked : Checked tree [9,3,6,7] := by
  refine ⟨plan2308,valid2308,t4_786choices,?_⟩
  exact check_of_frontier tree 0 t4_786root t4_786jobs t4_786frontier t4_786all
theorem t4_787choices : plan2309.choices=[9,3,6,10].map (options 4 3) := by rfl


theorem t4_787part0 : t4_787jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_787frontier : t4_787root.frontier 0=t4_787jobs := by rfl
theorem t4_787all : t4_787jobs.all (Job.check tree)=true := by
  simp only [t4_787jobs,List.all_append,List.all_nil,t4_787part0,Bool.and_self]
theorem t4_787checked : Checked tree [9,3,6,10] := by
  refine ⟨plan2309,valid2309,t4_787choices,?_⟩
  exact check_of_frontier tree 0 t4_787root t4_787jobs t4_787frontier t4_787all
theorem t4_788choices : plan2310.choices=[9,3,7,7].map (options 4 3) := by rfl


theorem t4_788part0 : t4_788jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_788frontier : t4_788root.frontier 0=t4_788jobs := by rfl
theorem t4_788all : t4_788jobs.all (Job.check tree)=true := by
  simp only [t4_788jobs,List.all_append,List.all_nil,t4_788part0,Bool.and_self]
theorem t4_788checked : Checked tree [9,3,7,7] := by
  refine ⟨plan2310,valid2310,t4_788choices,?_⟩
  exact check_of_frontier tree 0 t4_788root t4_788jobs t4_788frontier t4_788all
theorem t4_789choices : plan2311.choices=[9,3,10,7].map (options 4 3) := by rfl


theorem t4_789part0 : t4_789jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_789frontier : t4_789root.frontier 0=t4_789jobs := by rfl
theorem t4_789all : t4_789jobs.all (Job.check tree)=true := by
  simp only [t4_789jobs,List.all_append,List.all_nil,t4_789part0,Bool.and_self]
theorem t4_789checked : Checked tree [9,3,10,7] := by
  refine ⟨plan2311,valid2311,t4_789choices,?_⟩
  exact check_of_frontier tree 0 t4_789root t4_789jobs t4_789frontier t4_789all
theorem t4_790choices : plan2312.choices=[9,3,10,10].map (options 4 3) := by rfl


theorem t4_790part0 : t4_790jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_790frontier : t4_790root.frontier 0=t4_790jobs := by rfl
theorem t4_790all : t4_790jobs.all (Job.check tree)=true := by
  simp only [t4_790jobs,List.all_append,List.all_nil,t4_790part0,Bool.and_self]
theorem t4_790checked : Checked tree [9,3,10,10] := by
  refine ⟨plan2312,valid2312,t4_790choices,?_⟩
  exact check_of_frontier tree 0 t4_790root t4_790jobs t4_790frontier t4_790all
theorem t4_791choices : plan2490.choices=[9,6,6,6].map (options 4 4) := by rfl


theorem t4_791part0 : t4_791jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_791frontier : t4_791root.frontier 0=t4_791jobs := by rfl
theorem t4_791all : t4_791jobs.all (Job.check tree)=true := by
  simp only [t4_791jobs,List.all_append,List.all_nil,t4_791part0,Bool.and_self]
theorem t4_791checked : Checked tree [9,6,6,6] := by
  refine ⟨plan2490,valid2490,t4_791choices,?_⟩
  exact check_of_frontier tree 0 t4_791root t4_791jobs t4_791frontier t4_791all
theorem t4_792choices : plan2491.choices=[9,6,6,7].map (options 4 4) := by rfl


theorem t4_792part0 : t4_792jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_792frontier : t4_792root.frontier 0=t4_792jobs := by rfl
theorem t4_792all : t4_792jobs.all (Job.check tree)=true := by
  simp only [t4_792jobs,List.all_append,List.all_nil,t4_792part0,Bool.and_self]
theorem t4_792checked : Checked tree [9,6,6,7] := by
  refine ⟨plan2491,valid2491,t4_792choices,?_⟩
  exact check_of_frontier tree 0 t4_792root t4_792jobs t4_792frontier t4_792all
theorem t4_793choices : plan2492.choices=[9,6,6,10].map (options 4 4) := by rfl


theorem t4_793part0 : t4_793jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_793frontier : t4_793root.frontier 0=t4_793jobs := by rfl
theorem t4_793all : t4_793jobs.all (Job.check tree)=true := by
  simp only [t4_793jobs,List.all_append,List.all_nil,t4_793part0,Bool.and_self]
theorem t4_793checked : Checked tree [9,6,6,10] := by
  refine ⟨plan2492,valid2492,t4_793choices,?_⟩
  exact check_of_frontier tree 0 t4_793root t4_793jobs t4_793frontier t4_793all
theorem t4_794choices : plan2493.choices=[9,6,7,7].map (options 4 4) := by rfl


theorem t4_794part0 : t4_794jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_794frontier : t4_794root.frontier 0=t4_794jobs := by rfl
theorem t4_794all : t4_794jobs.all (Job.check tree)=true := by
  simp only [t4_794jobs,List.all_append,List.all_nil,t4_794part0,Bool.and_self]
theorem t4_794checked : Checked tree [9,6,7,7] := by
  refine ⟨plan2493,valid2493,t4_794choices,?_⟩
  exact check_of_frontier tree 0 t4_794root t4_794jobs t4_794frontier t4_794all
theorem t4_795choices : plan2494.choices=[9,6,10,7].map (options 4 4) := by rfl


theorem t4_795part0 : t4_795jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_795frontier : t4_795root.frontier 0=t4_795jobs := by rfl
theorem t4_795all : t4_795jobs.all (Job.check tree)=true := by
  simp only [t4_795jobs,List.all_append,List.all_nil,t4_795part0,Bool.and_self]
theorem t4_795checked : Checked tree [9,6,10,7] := by
  refine ⟨plan2494,valid2494,t4_795choices,?_⟩
  exact check_of_frontier tree 0 t4_795root t4_795jobs t4_795frontier t4_795all
theorem t4_796choices : plan2495.choices=[9,6,10,10].map (options 4 4) := by rfl


theorem t4_796part0 : t4_796jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_796frontier : t4_796root.frontier 0=t4_796jobs := by rfl
theorem t4_796all : t4_796jobs.all (Job.check tree)=true := by
  simp only [t4_796jobs,List.all_append,List.all_nil,t4_796part0,Bool.and_self]
theorem t4_796checked : Checked tree [9,6,10,10] := by
  refine ⟨plan2495,valid2495,t4_796choices,?_⟩
  exact check_of_frontier tree 0 t4_796root t4_796jobs t4_796frontier t4_796all
theorem t4_797choices : plan2496.choices=[9,7,7,7].map (options 4 4) := by rfl


theorem t4_797part0 : t4_797jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_797frontier : t4_797root.frontier 0=t4_797jobs := by rfl
theorem t4_797all : t4_797jobs.all (Job.check tree)=true := by
  simp only [t4_797jobs,List.all_append,List.all_nil,t4_797part0,Bool.and_self]
theorem t4_797checked : Checked tree [9,7,7,7] := by
  refine ⟨plan2496,valid2496,t4_797choices,?_⟩
  exact check_of_frontier tree 0 t4_797root t4_797jobs t4_797frontier t4_797all
theorem t4_798choices : plan2019.choices=[9,9,3,3].map (options 4 2) := by rfl


theorem t4_798part0 : t4_798jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_798frontier : t4_798root.frontier 0=t4_798jobs := by rfl
theorem t4_798all : t4_798jobs.all (Job.check tree)=true := by
  simp only [t4_798jobs,List.all_append,List.all_nil,t4_798part0,Bool.and_self]
theorem t4_798checked : Checked tree [9,9,3,3] := by
  refine ⟨plan2019,valid2019,t4_798choices,?_⟩
  exact check_of_frontier tree 0 t4_798root t4_798jobs t4_798frontier t4_798all
theorem t4_799choices : plan2313.choices=[9,9,3,6].map (options 4 3) := by rfl


theorem t4_799part0 : t4_799jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_799frontier : t4_799root.frontier 0=t4_799jobs := by rfl
theorem t4_799all : t4_799jobs.all (Job.check tree)=true := by
  simp only [t4_799jobs,List.all_append,List.all_nil,t4_799part0,Bool.and_self]
theorem t4_799checked : Checked tree [9,9,3,6] := by
  refine ⟨plan2313,valid2313,t4_799choices,?_⟩
  exact check_of_frontier tree 0 t4_799root t4_799jobs t4_799frontier t4_799all
theorem t4_800choices : plan2314.choices=[9,9,3,7].map (options 4 3) := by rfl


theorem t4_800part0 : t4_800jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_800frontier : t4_800root.frontier 0=t4_800jobs := by rfl
theorem t4_800all : t4_800jobs.all (Job.check tree)=true := by
  simp only [t4_800jobs,List.all_append,List.all_nil,t4_800part0,Bool.and_self]
theorem t4_800checked : Checked tree [9,9,3,7] := by
  refine ⟨plan2314,valid2314,t4_800choices,?_⟩
  exact check_of_frontier tree 0 t4_800root t4_800jobs t4_800frontier t4_800all
theorem t4_801choices : plan2315.choices=[9,9,3,10].map (options 4 3) := by rfl


theorem t4_801part0 : t4_801jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_801frontier : t4_801root.frontier 0=t4_801jobs := by rfl
theorem t4_801all : t4_801jobs.all (Job.check tree)=true := by
  simp only [t4_801jobs,List.all_append,List.all_nil,t4_801part0,Bool.and_self]
theorem t4_801checked : Checked tree [9,9,3,10] := by
  refine ⟨plan2315,valid2315,t4_801choices,?_⟩
  exact check_of_frontier tree 0 t4_801root t4_801jobs t4_801frontier t4_801all
theorem t4_802choices : plan2497.choices=[9,9,6,6].map (options 4 4) := by rfl


theorem t4_802part0 : t4_802jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_802frontier : t4_802root.frontier 0=t4_802jobs := by rfl
theorem t4_802all : t4_802jobs.all (Job.check tree)=true := by
  simp only [t4_802jobs,List.all_append,List.all_nil,t4_802part0,Bool.and_self]
theorem t4_802checked : Checked tree [9,9,6,6] := by
  refine ⟨plan2497,valid2497,t4_802choices,?_⟩
  exact check_of_frontier tree 0 t4_802root t4_802jobs t4_802frontier t4_802all
theorem t4_803choices : plan2498.choices=[9,9,6,7].map (options 4 4) := by rfl


theorem t4_803part0 : t4_803jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_803frontier : t4_803root.frontier 0=t4_803jobs := by rfl
theorem t4_803all : t4_803jobs.all (Job.check tree)=true := by
  simp only [t4_803jobs,List.all_append,List.all_nil,t4_803part0,Bool.and_self]
theorem t4_803checked : Checked tree [9,9,6,7] := by
  refine ⟨plan2498,valid2498,t4_803choices,?_⟩
  exact check_of_frontier tree 0 t4_803root t4_803jobs t4_803frontier t4_803all
theorem t4_804choices : plan2499.choices=[9,9,6,10].map (options 4 4) := by rfl


theorem t4_804part0 : t4_804jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_804frontier : t4_804root.frontier 0=t4_804jobs := by rfl
theorem t4_804all : t4_804jobs.all (Job.check tree)=true := by
  simp only [t4_804jobs,List.all_append,List.all_nil,t4_804part0,Bool.and_self]
theorem t4_804checked : Checked tree [9,9,6,10] := by
  refine ⟨plan2499,valid2499,t4_804choices,?_⟩
  exact check_of_frontier tree 0 t4_804root t4_804jobs t4_804frontier t4_804all
theorem t4_805choices : plan2500.choices=[9,9,7,7].map (options 4 4) := by rfl


theorem t4_805part0 : t4_805jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_805frontier : t4_805root.frontier 0=t4_805jobs := by rfl
theorem t4_805all : t4_805jobs.all (Job.check tree)=true := by
  simp only [t4_805jobs,List.all_append,List.all_nil,t4_805part0,Bool.and_self]
theorem t4_805checked : Checked tree [9,9,7,7] := by
  refine ⟨plan2500,valid2500,t4_805choices,?_⟩
  exact check_of_frontier tree 0 t4_805root t4_805jobs t4_805frontier t4_805all
theorem t4_806choices : plan2316.choices=[9,9,9,3].map (options 4 3) := by rfl


theorem t4_806part0 : t4_806jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_806frontier : t4_806root.frontier 0=t4_806jobs := by rfl
theorem t4_806all : t4_806jobs.all (Job.check tree)=true := by
  simp only [t4_806jobs,List.all_append,List.all_nil,t4_806part0,Bool.and_self]
theorem t4_806checked : Checked tree [9,9,9,3] := by
  refine ⟨plan2316,valid2316,t4_806choices,?_⟩
  exact check_of_frontier tree 0 t4_806root t4_806jobs t4_806frontier t4_806all
theorem t4_807choices : plan2501.choices=[9,9,9,6].map (options 4 4) := by rfl


theorem t4_807part0 : t4_807jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_807frontier : t4_807root.frontier 0=t4_807jobs := by rfl
theorem t4_807all : t4_807jobs.all (Job.check tree)=true := by
  simp only [t4_807jobs,List.all_append,List.all_nil,t4_807part0,Bool.and_self]
theorem t4_807checked : Checked tree [9,9,9,6] := by
  refine ⟨plan2501,valid2501,t4_807choices,?_⟩
  exact check_of_frontier tree 0 t4_807root t4_807jobs t4_807frontier t4_807all
theorem t4_808choices : plan2502.choices=[9,9,9,7].map (options 4 4) := by rfl


theorem t4_808part0 : t4_808jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_808frontier : t4_808root.frontier 0=t4_808jobs := by rfl
theorem t4_808all : t4_808jobs.all (Job.check tree)=true := by
  simp only [t4_808jobs,List.all_append,List.all_nil,t4_808part0,Bool.and_self]
theorem t4_808checked : Checked tree [9,9,9,7] := by
  refine ⟨plan2502,valid2502,t4_808choices,?_⟩
  exact check_of_frontier tree 0 t4_808root t4_808jobs t4_808frontier t4_808all
theorem t4_809choices : plan2503.choices=[9,9,9,9].map (options 4 4) := by rfl


theorem t4_809part0 : t4_809jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_809frontier : t4_809root.frontier 0=t4_809jobs := by rfl
theorem t4_809all : t4_809jobs.all (Job.check tree)=true := by
  simp only [t4_809jobs,List.all_append,List.all_nil,t4_809part0,Bool.and_self]
theorem t4_809checked : Checked tree [9,9,9,9] := by
  refine ⟨plan2503,valid2503,t4_809choices,?_⟩
  exact check_of_frontier tree 0 t4_809root t4_809jobs t4_809frontier t4_809all
theorem t4_810choices : plan2504.choices=[9,9,9,10].map (options 4 4) := by rfl


theorem t4_810part0 : t4_810jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_810frontier : t4_810root.frontier 0=t4_810jobs := by rfl
theorem t4_810all : t4_810jobs.all (Job.check tree)=true := by
  simp only [t4_810jobs,List.all_append,List.all_nil,t4_810part0,Bool.and_self]
theorem t4_810checked : Checked tree [9,9,9,10] := by
  refine ⟨plan2504,valid2504,t4_810choices,?_⟩
  exact check_of_frontier tree 0 t4_810root t4_810jobs t4_810frontier t4_810all
theorem t4_811choices : plan2505.choices=[9,9,10,7].map (options 4 4) := by rfl


theorem t4_811part0 : t4_811jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_811frontier : t4_811root.frontier 0=t4_811jobs := by rfl
theorem t4_811all : t4_811jobs.all (Job.check tree)=true := by
  simp only [t4_811jobs,List.all_append,List.all_nil,t4_811part0,Bool.and_self]
theorem t4_811checked : Checked tree [9,9,10,7] := by
  refine ⟨plan2505,valid2505,t4_811choices,?_⟩
  exact check_of_frontier tree 0 t4_811root t4_811jobs t4_811frontier t4_811all
theorem t4_812choices : plan2506.choices=[9,9,10,10].map (options 4 4) := by rfl


theorem t4_812part0 : t4_812jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_812frontier : t4_812root.frontier 0=t4_812jobs := by rfl
theorem t4_812all : t4_812jobs.all (Job.check tree)=true := by
  simp only [t4_812jobs,List.all_append,List.all_nil,t4_812part0,Bool.and_self]
theorem t4_812checked : Checked tree [9,9,10,10] := by
  refine ⟨plan2506,valid2506,t4_812choices,?_⟩
  exact check_of_frontier tree 0 t4_812root t4_812jobs t4_812frontier t4_812all
theorem t4_813choices : plan2507.choices=[9,10,7,7].map (options 4 4) := by rfl


theorem t4_813part0 : t4_813jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_813frontier : t4_813root.frontier 0=t4_813jobs := by rfl
theorem t4_813all : t4_813jobs.all (Job.check tree)=true := by
  simp only [t4_813jobs,List.all_append,List.all_nil,t4_813part0,Bool.and_self]
theorem t4_813checked : Checked tree [9,10,7,7] := by
  refine ⟨plan2507,valid2507,t4_813choices,?_⟩
  exact check_of_frontier tree 0 t4_813root t4_813jobs t4_813frontier t4_813all
theorem t4_814choices : plan2508.choices=[9,10,10,7].map (options 4 4) := by rfl


theorem t4_814part0 : t4_814jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_814frontier : t4_814root.frontier 0=t4_814jobs := by rfl
theorem t4_814all : t4_814jobs.all (Job.check tree)=true := by
  simp only [t4_814jobs,List.all_append,List.all_nil,t4_814part0,Bool.and_self]
theorem t4_814checked : Checked tree [9,10,10,7] := by
  refine ⟨plan2508,valid2508,t4_814choices,?_⟩
  exact check_of_frontier tree 0 t4_814root t4_814jobs t4_814frontier t4_814all
theorem t4_815choices : plan2509.choices=[9,10,10,10].map (options 4 4) := by rfl


theorem t4_815part0 : t4_815jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_815frontier : t4_815root.frontier 0=t4_815jobs := by rfl
theorem t4_815all : t4_815jobs.all (Job.check tree)=true := by
  simp only [t4_815jobs,List.all_append,List.all_nil,t4_815part0,Bool.and_self]
theorem t4_815checked : Checked tree [9,10,10,10] := by
  refine ⟨plan2509,valid2509,t4_815choices,?_⟩
  exact check_of_frontier tree 0 t4_815root t4_815jobs t4_815frontier t4_815all
theorem t4_816choices : plan2510.choices=[10,7,7,7].map (options 4 4) := by rfl


theorem t4_816part0 : t4_816jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_816frontier : t4_816root.frontier 0=t4_816jobs := by rfl
theorem t4_816all : t4_816jobs.all (Job.check tree)=true := by
  simp only [t4_816jobs,List.all_append,List.all_nil,t4_816part0,Bool.and_self]
theorem t4_816checked : Checked tree [10,7,7,7] := by
  refine ⟨plan2510,valid2510,t4_816choices,?_⟩
  exact check_of_frontier tree 0 t4_816root t4_816jobs t4_816frontier t4_816all
theorem t4_817choices : plan2511.choices=[10,10,7,7].map (options 4 4) := by rfl


theorem t4_817part0 : t4_817jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_817frontier : t4_817root.frontier 0=t4_817jobs := by rfl
theorem t4_817all : t4_817jobs.all (Job.check tree)=true := by
  simp only [t4_817jobs,List.all_append,List.all_nil,t4_817part0,Bool.and_self]
theorem t4_817checked : Checked tree [10,10,7,7] := by
  refine ⟨plan2511,valid2511,t4_817choices,?_⟩
  exact check_of_frontier tree 0 t4_817root t4_817jobs t4_817frontier t4_817all
theorem t4_818choices : plan2512.choices=[10,10,10,7].map (options 4 4) := by rfl


theorem t4_818part0 : t4_818jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_818frontier : t4_818root.frontier 0=t4_818jobs := by rfl
theorem t4_818all : t4_818jobs.all (Job.check tree)=true := by
  simp only [t4_818jobs,List.all_append,List.all_nil,t4_818part0,Bool.and_self]
theorem t4_818checked : Checked tree [10,10,10,7] := by
  refine ⟨plan2512,valid2512,t4_818choices,?_⟩
  exact check_of_frontier tree 0 t4_818root t4_818jobs t4_818frontier t4_818all
theorem t4_819choices : plan2513.choices=[10,10,10,10].map (options 4 4) := by rfl


theorem t4_819part0 : t4_819jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_819frontier : t4_819root.frontier 0=t4_819jobs := by rfl
theorem t4_819all : t4_819jobs.all (Job.check tree)=true := by
  simp only [t4_819jobs,List.all_append,List.all_nil,t4_819part0,Bool.and_self]
theorem t4_819checked : Checked tree [10,10,10,10] := by
  refine ⟨plan2513,valid2513,t4_819choices,?_⟩
  exact check_of_frontier tree 0 t4_819root t4_819jobs t4_819frontier t4_819all
theorem t5_0choices : plan3674.choices=[0,1,2,3,7].map (options 5 1) := by rfl


theorem t5_0part0 : t5_0jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_0frontier : t5_0root.frontier 0=t5_0jobs := by rfl
theorem t5_0all : t5_0jobs.all (Job.check tree)=true := by
  simp only [t5_0jobs,List.all_append,List.all_nil,t5_0part0,Bool.and_self]
theorem t5_0checked : Checked tree [0,1,2,3,7] := by
  refine ⟨plan3674,valid3674,t5_0choices,?_⟩
  exact check_of_frontier tree 0 t5_0root t5_0jobs t5_0frontier t5_0all
theorem t5_1choices : plan3759.choices=[0,1,2,6,7].map (options 5 2) := by rfl


theorem t5_1part0 : t5_1jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_1frontier : t5_1root.frontier 0=t5_1jobs := by rfl
theorem t5_1all : t5_1jobs.all (Job.check tree)=true := by
  simp only [t5_1jobs,List.all_append,List.all_nil,t5_1part0,Bool.and_self]
theorem t5_1checked : Checked tree [0,1,2,6,7] := by
  refine ⟨plan3759,valid3759,t5_1choices,?_⟩
  exact check_of_frontier tree 0 t5_1root t5_1jobs t5_1frontier t5_1all
theorem t5_2choices : plan3760.choices=[0,1,2,7,7].map (options 5 2) := by rfl


theorem t5_2part0 : t5_2jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_2frontier : t5_2root.frontier 0=t5_2jobs := by rfl
theorem t5_2all : t5_2jobs.all (Job.check tree)=true := by
  simp only [t5_2jobs,List.all_append,List.all_nil,t5_2part0,Bool.and_self]
theorem t5_2checked : Checked tree [0,1,2,7,7] := by
  refine ⟨plan3760,valid3760,t5_2choices,?_⟩
  exact check_of_frontier tree 0 t5_2root t5_2jobs t5_2frontier t5_2all
theorem t5_3choices : plan3761.choices=[0,1,2,10,7].map (options 5 2) := by rfl


theorem t5_3part0 : t5_3jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_3frontier : t5_3root.frontier 0=t5_3jobs := by rfl
theorem t5_3all : t5_3jobs.all (Job.check tree)=true := by
  simp only [t5_3jobs,List.all_append,List.all_nil,t5_3part0,Bool.and_self]
theorem t5_3checked : Checked tree [0,1,2,10,7] := by
  refine ⟨plan3761,valid3761,t5_3choices,?_⟩
  exact check_of_frontier tree 0 t5_3root t5_3jobs t5_3frontier t5_3all
theorem t5_4choices : plan3658.choices=[0,1,3,3,3].map (options 5 0) := by rfl


theorem t5_4part0 : t5_4jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_4frontier : t5_4root.frontier 0=t5_4jobs := by rfl
theorem t5_4all : t5_4jobs.all (Job.check tree)=true := by
  simp only [t5_4jobs,List.all_append,List.all_nil,t5_4part0,Bool.and_self]
theorem t5_4checked : Checked tree [0,1,3,3,3] := by
  refine ⟨plan3658,valid3658,t5_4choices,?_⟩
  exact check_of_frontier tree 0 t5_4root t5_4jobs t5_4frontier t5_4all
theorem t5_5choices : plan3675.choices=[0,1,3,3,6].map (options 5 1) := by rfl


theorem t5_5part0 : t5_5jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_5frontier : t5_5root.frontier 0=t5_5jobs := by rfl
theorem t5_5all : t5_5jobs.all (Job.check tree)=true := by
  simp only [t5_5jobs,List.all_append,List.all_nil,t5_5part0,Bool.and_self]
theorem t5_5checked : Checked tree [0,1,3,3,6] := by
  refine ⟨plan3675,valid3675,t5_5choices,?_⟩
  exact check_of_frontier tree 0 t5_5root t5_5jobs t5_5frontier t5_5all
theorem t5_6choices : plan3676.choices=[0,1,3,3,7].map (options 5 1) := by rfl


theorem t5_6part0 : t5_6jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_6frontier : t5_6root.frontier 0=t5_6jobs := by rfl
theorem t5_6all : t5_6jobs.all (Job.check tree)=true := by
  simp only [t5_6jobs,List.all_append,List.all_nil,t5_6part0,Bool.and_self]
theorem t5_6checked : Checked tree [0,1,3,3,7] := by
  refine ⟨plan3676,valid3676,t5_6choices,?_⟩
  exact check_of_frontier tree 0 t5_6root t5_6jobs t5_6frontier t5_6all
theorem t5_7choices : plan3677.choices=[0,1,3,3,10].map (options 5 1) := by rfl


theorem t5_7part0 : t5_7jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_7frontier : t5_7root.frontier 0=t5_7jobs := by rfl
theorem t5_7all : t5_7jobs.all (Job.check tree)=true := by
  simp only [t5_7jobs,List.all_append,List.all_nil,t5_7part0,Bool.and_self]
theorem t5_7checked : Checked tree [0,1,3,3,10] := by
  refine ⟨plan3677,valid3677,t5_7choices,?_⟩
  exact check_of_frontier tree 0 t5_7root t5_7jobs t5_7frontier t5_7all
theorem t5_8choices : plan3762.choices=[0,1,3,6,6].map (options 5 2) := by rfl


theorem t5_8part0 : t5_8jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_8frontier : t5_8root.frontier 0=t5_8jobs := by rfl
theorem t5_8all : t5_8jobs.all (Job.check tree)=true := by
  simp only [t5_8jobs,List.all_append,List.all_nil,t5_8part0,Bool.and_self]
theorem t5_8checked : Checked tree [0,1,3,6,6] := by
  refine ⟨plan3762,valid3762,t5_8choices,?_⟩
  exact check_of_frontier tree 0 t5_8root t5_8jobs t5_8frontier t5_8all
theorem t5_9choices : plan3763.choices=[0,1,3,6,7].map (options 5 2) := by rfl


theorem t5_9part0 : t5_9jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_9frontier : t5_9root.frontier 0=t5_9jobs := by rfl
theorem t5_9all : t5_9jobs.all (Job.check tree)=true := by
  simp only [t5_9jobs,List.all_append,List.all_nil,t5_9part0,Bool.and_self]
theorem t5_9checked : Checked tree [0,1,3,6,7] := by
  refine ⟨plan3763,valid3763,t5_9choices,?_⟩
  exact check_of_frontier tree 0 t5_9root t5_9jobs t5_9frontier t5_9all
theorem t5_10choices : plan3764.choices=[0,1,3,6,10].map (options 5 2) := by rfl


theorem t5_10part0 : t5_10jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_10frontier : t5_10root.frontier 0=t5_10jobs := by rfl
theorem t5_10all : t5_10jobs.all (Job.check tree)=true := by
  simp only [t5_10jobs,List.all_append,List.all_nil,t5_10part0,Bool.and_self]
theorem t5_10checked : Checked tree [0,1,3,6,10] := by
  refine ⟨plan3764,valid3764,t5_10choices,?_⟩
  exact check_of_frontier tree 0 t5_10root t5_10jobs t5_10frontier t5_10all
theorem t5_11choices : plan3765.choices=[0,1,3,7,7].map (options 5 2) := by rfl


theorem t5_11part0 : t5_11jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_11frontier : t5_11root.frontier 0=t5_11jobs := by rfl
theorem t5_11all : t5_11jobs.all (Job.check tree)=true := by
  simp only [t5_11jobs,List.all_append,List.all_nil,t5_11part0,Bool.and_self]
theorem t5_11checked : Checked tree [0,1,3,7,7] := by
  refine ⟨plan3765,valid3765,t5_11choices,?_⟩
  exact check_of_frontier tree 0 t5_11root t5_11jobs t5_11frontier t5_11all
theorem t5_12choices : plan3766.choices=[0,1,3,10,7].map (options 5 2) := by rfl


theorem t5_12part0 : t5_12jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_12frontier : t5_12root.frontier 0=t5_12jobs := by rfl
theorem t5_12all : t5_12jobs.all (Job.check tree)=true := by
  simp only [t5_12jobs,List.all_append,List.all_nil,t5_12part0,Bool.and_self]
theorem t5_12checked : Checked tree [0,1,3,10,7] := by
  refine ⟨plan3766,valid3766,t5_12choices,?_⟩
  exact check_of_frontier tree 0 t5_12root t5_12jobs t5_12frontier t5_12all
theorem t5_13choices : plan3767.choices=[0,1,3,10,10].map (options 5 2) := by rfl


theorem t5_13part0 : t5_13jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_13frontier : t5_13root.frontier 0=t5_13jobs := by rfl
theorem t5_13all : t5_13jobs.all (Job.check tree)=true := by
  simp only [t5_13jobs,List.all_append,List.all_nil,t5_13part0,Bool.and_self]
theorem t5_13checked : Checked tree [0,1,3,10,10] := by
  refine ⟨plan3767,valid3767,t5_13choices,?_⟩
  exact check_of_frontier tree 0 t5_13root t5_13jobs t5_13frontier t5_13all
theorem t5_14choices : plan3768.choices=[0,1,5,3,7].map (options 5 2) := by rfl


theorem t5_14part0 : t5_14jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_14frontier : t5_14root.frontier 0=t5_14jobs := by rfl
theorem t5_14all : t5_14jobs.all (Job.check tree)=true := by
  simp only [t5_14jobs,List.all_append,List.all_nil,t5_14part0,Bool.and_self]
theorem t5_14checked : Checked tree [0,1,5,3,7] := by
  refine ⟨plan3768,valid3768,t5_14choices,?_⟩
  exact check_of_frontier tree 0 t5_14root t5_14jobs t5_14frontier t5_14all
theorem t5_15choices : plan4000.choices=[0,1,5,6,7].map (options 5 3) := by rfl


theorem t5_15part0 : t5_15jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_15frontier : t5_15root.frontier 0=t5_15jobs := by rfl
theorem t5_15all : t5_15jobs.all (Job.check tree)=true := by
  simp only [t5_15jobs,List.all_append,List.all_nil,t5_15part0,Bool.and_self]
theorem t5_15checked : Checked tree [0,1,5,6,7] := by
  refine ⟨plan4000,valid4000,t5_15choices,?_⟩
  exact check_of_frontier tree 0 t5_15root t5_15jobs t5_15frontier t5_15all
theorem t5_16choices : plan4001.choices=[0,1,5,7,7].map (options 5 3) := by rfl


theorem t5_16part0 : t5_16jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_16frontier : t5_16root.frontier 0=t5_16jobs := by rfl
theorem t5_16all : t5_16jobs.all (Job.check tree)=true := by
  simp only [t5_16jobs,List.all_append,List.all_nil,t5_16part0,Bool.and_self]
theorem t5_16checked : Checked tree [0,1,5,7,7] := by
  refine ⟨plan4001,valid4001,t5_16choices,?_⟩
  exact check_of_frontier tree 0 t5_16root t5_16jobs t5_16frontier t5_16all
theorem t5_17choices : plan4002.choices=[0,1,5,10,7].map (options 5 3) := by rfl


theorem t5_17part0 : t5_17jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_17frontier : t5_17root.frontier 0=t5_17jobs := by rfl
theorem t5_17all : t5_17jobs.all (Job.check tree)=true := by
  simp only [t5_17jobs,List.all_append,List.all_nil,t5_17part0,Bool.and_self]
theorem t5_17checked : Checked tree [0,1,5,10,7] := by
  refine ⟨plan4002,valid4002,t5_17choices,?_⟩
  exact check_of_frontier tree 0 t5_17root t5_17jobs t5_17frontier t5_17all
theorem t5_18choices : plan4003.choices=[0,1,6,6,6].map (options 5 3) := by rfl


theorem t5_18part0 : t5_18jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_18frontier : t5_18root.frontier 0=t5_18jobs := by rfl
theorem t5_18all : t5_18jobs.all (Job.check tree)=true := by
  simp only [t5_18jobs,List.all_append,List.all_nil,t5_18part0,Bool.and_self]
theorem t5_18checked : Checked tree [0,1,6,6,6] := by
  refine ⟨plan4003,valid4003,t5_18choices,?_⟩
  exact check_of_frontier tree 0 t5_18root t5_18jobs t5_18frontier t5_18all
theorem t5_19choices : plan4004.choices=[0,1,6,6,7].map (options 5 3) := by rfl


theorem t5_19part0 : t5_19jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_19frontier : t5_19root.frontier 0=t5_19jobs := by rfl
theorem t5_19all : t5_19jobs.all (Job.check tree)=true := by
  simp only [t5_19jobs,List.all_append,List.all_nil,t5_19part0,Bool.and_self]
theorem t5_19checked : Checked tree [0,1,6,6,7] := by
  refine ⟨plan4004,valid4004,t5_19choices,?_⟩
  exact check_of_frontier tree 0 t5_19root t5_19jobs t5_19frontier t5_19all
theorem t5_20choices : plan4005.choices=[0,1,6,6,10].map (options 5 3) := by rfl


theorem t5_20part0 : t5_20jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_20frontier : t5_20root.frontier 0=t5_20jobs := by rfl
theorem t5_20all : t5_20jobs.all (Job.check tree)=true := by
  simp only [t5_20jobs,List.all_append,List.all_nil,t5_20part0,Bool.and_self]
theorem t5_20checked : Checked tree [0,1,6,6,10] := by
  refine ⟨plan4005,valid4005,t5_20choices,?_⟩
  exact check_of_frontier tree 0 t5_20root t5_20jobs t5_20frontier t5_20all
theorem t5_21choices : plan4006.choices=[0,1,6,7,7].map (options 5 3) := by rfl


theorem t5_21part0 : t5_21jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_21frontier : t5_21root.frontier 0=t5_21jobs := by rfl
theorem t5_21all : t5_21jobs.all (Job.check tree)=true := by
  simp only [t5_21jobs,List.all_append,List.all_nil,t5_21part0,Bool.and_self]
theorem t5_21checked : Checked tree [0,1,6,7,7] := by
  refine ⟨plan4006,valid4006,t5_21choices,?_⟩
  exact check_of_frontier tree 0 t5_21root t5_21jobs t5_21frontier t5_21all
theorem t5_22choices : plan4007.choices=[0,1,6,10,7].map (options 5 3) := by rfl


theorem t5_22part0 : t5_22jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_22frontier : t5_22root.frontier 0=t5_22jobs := by rfl
theorem t5_22all : t5_22jobs.all (Job.check tree)=true := by
  simp only [t5_22jobs,List.all_append,List.all_nil,t5_22part0,Bool.and_self]
theorem t5_22checked : Checked tree [0,1,6,10,7] := by
  refine ⟨plan4007,valid4007,t5_22choices,?_⟩
  exact check_of_frontier tree 0 t5_22root t5_22jobs t5_22frontier t5_22all
theorem t5_23choices : plan4008.choices=[0,1,6,10,10].map (options 5 3) := by rfl


theorem t5_23part0 : t5_23jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_23frontier : t5_23root.frontier 0=t5_23jobs := by rfl
theorem t5_23all : t5_23jobs.all (Job.check tree)=true := by
  simp only [t5_23jobs,List.all_append,List.all_nil,t5_23part0,Bool.and_self]
theorem t5_23checked : Checked tree [0,1,6,10,10] := by
  refine ⟨plan4008,valid4008,t5_23choices,?_⟩
  exact check_of_frontier tree 0 t5_23root t5_23jobs t5_23frontier t5_23all
theorem t5_24choices : plan4009.choices=[0,1,7,7,7].map (options 5 3) := by rfl


theorem t5_24part0 : t5_24jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_24frontier : t5_24root.frontier 0=t5_24jobs := by rfl
theorem t5_24all : t5_24jobs.all (Job.check tree)=true := by
  simp only [t5_24jobs,List.all_append,List.all_nil,t5_24part0,Bool.and_self]
theorem t5_24checked : Checked tree [0,1,7,7,7] := by
  refine ⟨plan4009,valid4009,t5_24choices,?_⟩
  exact check_of_frontier tree 0 t5_24root t5_24jobs t5_24frontier t5_24all
theorem t5_25choices : plan3769.choices=[0,1,9,3,7].map (options 5 2) := by rfl


theorem t5_25part0 : t5_25jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_25frontier : t5_25root.frontier 0=t5_25jobs := by rfl
theorem t5_25all : t5_25jobs.all (Job.check tree)=true := by
  simp only [t5_25jobs,List.all_append,List.all_nil,t5_25part0,Bool.and_self]
theorem t5_25checked : Checked tree [0,1,9,3,7] := by
  refine ⟨plan3769,valid3769,t5_25choices,?_⟩
  exact check_of_frontier tree 0 t5_25root t5_25jobs t5_25frontier t5_25all
theorem t5_26choices : plan4010.choices=[0,1,9,6,7].map (options 5 3) := by rfl


theorem t5_26part0 : t5_26jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_26frontier : t5_26root.frontier 0=t5_26jobs := by rfl
theorem t5_26all : t5_26jobs.all (Job.check tree)=true := by
  simp only [t5_26jobs,List.all_append,List.all_nil,t5_26part0,Bool.and_self]
theorem t5_26checked : Checked tree [0,1,9,6,7] := by
  refine ⟨plan4010,valid4010,t5_26choices,?_⟩
  exact check_of_frontier tree 0 t5_26root t5_26jobs t5_26frontier t5_26all
theorem t5_27choices : plan4011.choices=[0,1,9,7,7].map (options 5 3) := by rfl


theorem t5_27part0 : t5_27jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_27frontier : t5_27root.frontier 0=t5_27jobs := by rfl
theorem t5_27all : t5_27jobs.all (Job.check tree)=true := by
  simp only [t5_27jobs,List.all_append,List.all_nil,t5_27part0,Bool.and_self]
theorem t5_27checked : Checked tree [0,1,9,7,7] := by
  refine ⟨plan4011,valid4011,t5_27choices,?_⟩
  exact check_of_frontier tree 0 t5_27root t5_27jobs t5_27frontier t5_27all
theorem t5_28choices : plan4012.choices=[0,1,9,10,7].map (options 5 3) := by rfl


theorem t5_28part0 : t5_28jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_28frontier : t5_28root.frontier 0=t5_28jobs := by rfl
theorem t5_28all : t5_28jobs.all (Job.check tree)=true := by
  simp only [t5_28jobs,List.all_append,List.all_nil,t5_28part0,Bool.and_self]
theorem t5_28checked : Checked tree [0,1,9,10,7] := by
  refine ⟨plan4012,valid4012,t5_28choices,?_⟩
  exact check_of_frontier tree 0 t5_28root t5_28jobs t5_28frontier t5_28all
theorem t5_29choices : plan4013.choices=[0,1,10,7,7].map (options 5 3) := by rfl


theorem t5_29part0 : t5_29jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_29frontier : t5_29root.frontier 0=t5_29jobs := by rfl
theorem t5_29all : t5_29jobs.all (Job.check tree)=true := by
  simp only [t5_29jobs,List.all_append,List.all_nil,t5_29part0,Bool.and_self]
theorem t5_29checked : Checked tree [0,1,10,7,7] := by
  refine ⟨plan4013,valid4013,t5_29choices,?_⟩
  exact check_of_frontier tree 0 t5_29root t5_29jobs t5_29frontier t5_29all
theorem t5_30choices : plan4014.choices=[0,1,10,10,7].map (options 5 3) := by rfl


theorem t5_30part0 : t5_30jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_30frontier : t5_30root.frontier 0=t5_30jobs := by rfl
theorem t5_30all : t5_30jobs.all (Job.check tree)=true := by
  simp only [t5_30jobs,List.all_append,List.all_nil,t5_30part0,Bool.and_self]
theorem t5_30checked : Checked tree [0,1,10,10,7] := by
  refine ⟨plan4014,valid4014,t5_30choices,?_⟩
  exact check_of_frontier tree 0 t5_30root t5_30jobs t5_30frontier t5_30all
theorem t5_31choices : plan4015.choices=[0,1,10,10,10].map (options 5 3) := by rfl


theorem t5_31part0 : t5_31jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_31frontier : t5_31root.frontier 0=t5_31jobs := by rfl
theorem t5_31all : t5_31jobs.all (Job.check tree)=true := by
  simp only [t5_31jobs,List.all_append,List.all_nil,t5_31part0,Bool.and_self]
theorem t5_31checked : Checked tree [0,1,10,10,10] := by
  refine ⟨plan4015,valid4015,t5_31choices,?_⟩
  exact check_of_frontier tree 0 t5_31root t5_31jobs t5_31frontier t5_31all
theorem t5_32choices : plan3678.choices=[0,2,2,2,7].map (options 5 1) := by rfl


theorem t5_32part0 : t5_32jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_32frontier : t5_32root.frontier 0=t5_32jobs := by rfl
theorem t5_32all : t5_32jobs.all (Job.check tree)=true := by
  simp only [t5_32jobs,List.all_append,List.all_nil,t5_32part0,Bool.and_self]
theorem t5_32checked : Checked tree [0,2,2,2,7] := by
  refine ⟨plan3678,valid3678,t5_32choices,?_⟩
  exact check_of_frontier tree 0 t5_32root t5_32jobs t5_32frontier t5_32all
theorem t5_33choices : plan3659.choices=[0,2,2,3,3].map (options 5 0) := by rfl


theorem t5_33part0 : t5_33jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_33frontier : t5_33root.frontier 0=t5_33jobs := by rfl
theorem t5_33all : t5_33jobs.all (Job.check tree)=true := by
  simp only [t5_33jobs,List.all_append,List.all_nil,t5_33part0,Bool.and_self]
theorem t5_33checked : Checked tree [0,2,2,3,3] := by
  refine ⟨plan3659,valid3659,t5_33choices,?_⟩
  exact check_of_frontier tree 0 t5_33root t5_33jobs t5_33frontier t5_33all
theorem t5_34choices : plan3679.choices=[0,2,2,3,6].map (options 5 1) := by rfl


theorem t5_34part0 : t5_34jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_34frontier : t5_34root.frontier 0=t5_34jobs := by rfl
theorem t5_34all : t5_34jobs.all (Job.check tree)=true := by
  simp only [t5_34jobs,List.all_append,List.all_nil,t5_34part0,Bool.and_self]
theorem t5_34checked : Checked tree [0,2,2,3,6] := by
  refine ⟨plan3679,valid3679,t5_34choices,?_⟩
  exact check_of_frontier tree 0 t5_34root t5_34jobs t5_34frontier t5_34all
theorem t5_35choices : plan3680.choices=[0,2,2,3,7].map (options 5 1) := by rfl


theorem t5_35part0 : t5_35jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_35frontier : t5_35root.frontier 0=t5_35jobs := by rfl
theorem t5_35all : t5_35jobs.all (Job.check tree)=true := by
  simp only [t5_35jobs,List.all_append,List.all_nil,t5_35part0,Bool.and_self]
theorem t5_35checked : Checked tree [0,2,2,3,7] := by
  refine ⟨plan3680,valid3680,t5_35choices,?_⟩
  exact check_of_frontier tree 0 t5_35root t5_35jobs t5_35frontier t5_35all
theorem t5_36choices : plan3681.choices=[0,2,2,3,10].map (options 5 1) := by rfl


theorem t5_36part0 : t5_36jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_36frontier : t5_36root.frontier 0=t5_36jobs := by rfl
theorem t5_36all : t5_36jobs.all (Job.check tree)=true := by
  simp only [t5_36jobs,List.all_append,List.all_nil,t5_36part0,Bool.and_self]
theorem t5_36checked : Checked tree [0,2,2,3,10] := by
  refine ⟨plan3681,valid3681,t5_36choices,?_⟩
  exact check_of_frontier tree 0 t5_36root t5_36jobs t5_36frontier t5_36all
theorem t5_37choices : plan3770.choices=[0,2,2,5,7].map (options 5 2) := by rfl


theorem t5_37part0 : t5_37jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_37frontier : t5_37root.frontier 0=t5_37jobs := by rfl
theorem t5_37all : t5_37jobs.all (Job.check tree)=true := by
  simp only [t5_37jobs,List.all_append,List.all_nil,t5_37part0,Bool.and_self]
theorem t5_37checked : Checked tree [0,2,2,5,7] := by
  refine ⟨plan3770,valid3770,t5_37choices,?_⟩
  exact check_of_frontier tree 0 t5_37root t5_37jobs t5_37frontier t5_37all
theorem t5_38choices : plan3771.choices=[0,2,2,6,6].map (options 5 2) := by rfl


theorem t5_38part0 : t5_38jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_38frontier : t5_38root.frontier 0=t5_38jobs := by rfl
theorem t5_38all : t5_38jobs.all (Job.check tree)=true := by
  simp only [t5_38jobs,List.all_append,List.all_nil,t5_38part0,Bool.and_self]
theorem t5_38checked : Checked tree [0,2,2,6,6] := by
  refine ⟨plan3771,valid3771,t5_38choices,?_⟩
  exact check_of_frontier tree 0 t5_38root t5_38jobs t5_38frontier t5_38all
theorem t5_39choices : plan3772.choices=[0,2,2,6,7].map (options 5 2) := by rfl


theorem t5_39part0 : t5_39jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_39frontier : t5_39root.frontier 0=t5_39jobs := by rfl
theorem t5_39all : t5_39jobs.all (Job.check tree)=true := by
  simp only [t5_39jobs,List.all_append,List.all_nil,t5_39part0,Bool.and_self]
theorem t5_39checked : Checked tree [0,2,2,6,7] := by
  refine ⟨plan3772,valid3772,t5_39choices,?_⟩
  exact check_of_frontier tree 0 t5_39root t5_39jobs t5_39frontier t5_39all
theorem t5_40choices : plan3773.choices=[0,2,2,6,10].map (options 5 2) := by rfl


theorem t5_40part0 : t5_40jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_40frontier : t5_40root.frontier 0=t5_40jobs := by rfl
theorem t5_40all : t5_40jobs.all (Job.check tree)=true := by
  simp only [t5_40jobs,List.all_append,List.all_nil,t5_40part0,Bool.and_self]
theorem t5_40checked : Checked tree [0,2,2,6,10] := by
  refine ⟨plan3773,valid3773,t5_40choices,?_⟩
  exact check_of_frontier tree 0 t5_40root t5_40jobs t5_40frontier t5_40all
theorem t5_41choices : plan3774.choices=[0,2,2,7,7].map (options 5 2) := by rfl


theorem t5_41part0 : t5_41jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_41frontier : t5_41root.frontier 0=t5_41jobs := by rfl
theorem t5_41all : t5_41jobs.all (Job.check tree)=true := by
  simp only [t5_41jobs,List.all_append,List.all_nil,t5_41part0,Bool.and_self]
theorem t5_41checked : Checked tree [0,2,2,7,7] := by
  refine ⟨plan3774,valid3774,t5_41choices,?_⟩
  exact check_of_frontier tree 0 t5_41root t5_41jobs t5_41frontier t5_41all
theorem t5_42choices : plan3775.choices=[0,2,2,9,7].map (options 5 2) := by rfl


theorem t5_42part0 : t5_42jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_42frontier : t5_42root.frontier 0=t5_42jobs := by rfl
theorem t5_42all : t5_42jobs.all (Job.check tree)=true := by
  simp only [t5_42jobs,List.all_append,List.all_nil,t5_42part0,Bool.and_self]
theorem t5_42checked : Checked tree [0,2,2,9,7] := by
  refine ⟨plan3775,valid3775,t5_42choices,?_⟩
  exact check_of_frontier tree 0 t5_42root t5_42jobs t5_42frontier t5_42all
theorem t5_43choices : plan3776.choices=[0,2,2,10,7].map (options 5 2) := by rfl


theorem t5_43part0 : t5_43jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_43frontier : t5_43root.frontier 0=t5_43jobs := by rfl
theorem t5_43all : t5_43jobs.all (Job.check tree)=true := by
  simp only [t5_43jobs,List.all_append,List.all_nil,t5_43part0,Bool.and_self]
theorem t5_43checked : Checked tree [0,2,2,10,7] := by
  refine ⟨plan3776,valid3776,t5_43choices,?_⟩
  exact check_of_frontier tree 0 t5_43root t5_43jobs t5_43frontier t5_43all
theorem t5_44choices : plan3777.choices=[0,2,2,10,10].map (options 5 2) := by rfl


theorem t5_44part0 : t5_44jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_44frontier : t5_44root.frontier 0=t5_44jobs := by rfl
theorem t5_44all : t5_44jobs.all (Job.check tree)=true := by
  simp only [t5_44jobs,List.all_append,List.all_nil,t5_44part0,Bool.and_self]
theorem t5_44checked : Checked tree [0,2,2,10,10] := by
  refine ⟨plan3777,valid3777,t5_44choices,?_⟩
  exact check_of_frontier tree 0 t5_44root t5_44jobs t5_44frontier t5_44all
theorem t5_45choices : plan3660.choices=[0,2,3,3,3].map (options 5 0) := by rfl


theorem t5_45part0 : t5_45jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_45frontier : t5_45root.frontier 0=t5_45jobs := by rfl
theorem t5_45all : t5_45jobs.all (Job.check tree)=true := by
  simp only [t5_45jobs,List.all_append,List.all_nil,t5_45part0,Bool.and_self]
theorem t5_45checked : Checked tree [0,2,3,3,3] := by
  refine ⟨plan3660,valid3660,t5_45choices,?_⟩
  exact check_of_frontier tree 0 t5_45root t5_45jobs t5_45frontier t5_45all
theorem t5_46choices : plan3682.choices=[0,2,3,3,6].map (options 5 1) := by rfl


theorem t5_46part0 : t5_46jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_46frontier : t5_46root.frontier 0=t5_46jobs := by rfl
theorem t5_46all : t5_46jobs.all (Job.check tree)=true := by
  simp only [t5_46jobs,List.all_append,List.all_nil,t5_46part0,Bool.and_self]
theorem t5_46checked : Checked tree [0,2,3,3,6] := by
  refine ⟨plan3682,valid3682,t5_46choices,?_⟩
  exact check_of_frontier tree 0 t5_46root t5_46jobs t5_46frontier t5_46all
theorem t5_47choices : plan3683.choices=[0,2,3,3,7].map (options 5 1) := by rfl


theorem t5_47part0 : t5_47jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_47frontier : t5_47root.frontier 0=t5_47jobs := by rfl
theorem t5_47all : t5_47jobs.all (Job.check tree)=true := by
  simp only [t5_47jobs,List.all_append,List.all_nil,t5_47part0,Bool.and_self]
theorem t5_47checked : Checked tree [0,2,3,3,7] := by
  refine ⟨plan3683,valid3683,t5_47choices,?_⟩
  exact check_of_frontier tree 0 t5_47root t5_47jobs t5_47frontier t5_47all
theorem t5_48choices : plan3684.choices=[0,2,3,3,10].map (options 5 1) := by rfl


theorem t5_48part0 : t5_48jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_48frontier : t5_48root.frontier 0=t5_48jobs := by rfl
theorem t5_48all : t5_48jobs.all (Job.check tree)=true := by
  simp only [t5_48jobs,List.all_append,List.all_nil,t5_48part0,Bool.and_self]
theorem t5_48checked : Checked tree [0,2,3,3,10] := by
  refine ⟨plan3684,valid3684,t5_48choices,?_⟩
  exact check_of_frontier tree 0 t5_48root t5_48jobs t5_48frontier t5_48all
theorem t5_49choices : plan3778.choices=[0,2,3,6,6].map (options 5 2) := by rfl


theorem t5_49part0 : t5_49jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_49frontier : t5_49root.frontier 0=t5_49jobs := by rfl
theorem t5_49all : t5_49jobs.all (Job.check tree)=true := by
  simp only [t5_49jobs,List.all_append,List.all_nil,t5_49part0,Bool.and_self]
theorem t5_49checked : Checked tree [0,2,3,6,6] := by
  refine ⟨plan3778,valid3778,t5_49choices,?_⟩
  exact check_of_frontier tree 0 t5_49root t5_49jobs t5_49frontier t5_49all
theorem t5_50choices : plan3779.choices=[0,2,3,6,7].map (options 5 2) := by rfl


theorem t5_50part0 : t5_50jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_50frontier : t5_50root.frontier 0=t5_50jobs := by rfl
theorem t5_50all : t5_50jobs.all (Job.check tree)=true := by
  simp only [t5_50jobs,List.all_append,List.all_nil,t5_50part0,Bool.and_self]
theorem t5_50checked : Checked tree [0,2,3,6,7] := by
  refine ⟨plan3779,valid3779,t5_50choices,?_⟩
  exact check_of_frontier tree 0 t5_50root t5_50jobs t5_50frontier t5_50all
theorem t5_51choices : plan3780.choices=[0,2,3,6,10].map (options 5 2) := by rfl


theorem t5_51part0 : t5_51jobs0.all (Job.check tree)=true := by decide +kernel

theorem t5_51frontier : t5_51root.frontier 0=t5_51jobs := by rfl
theorem t5_51all : t5_51jobs.all (Job.check tree)=true := by
  simp only [t5_51jobs,List.all_append,List.all_nil,t5_51part0,Bool.and_self]
theorem t5_51checked : Checked tree [0,2,3,6,10] := by
  refine ⟨plan3780,valid3780,t5_51choices,?_⟩
  exact check_of_frontier tree 0 t5_51root t5_51jobs t5_51frontier t5_51all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks005 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_5checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_6checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_7checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_8checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_9checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_10checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_11checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_12checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_13checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_701checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_14checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_15checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_16checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_17checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_18checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_19checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_20checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_21checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_22checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_23checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_702checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_24checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_25checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_26checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_27checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_28checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_688checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_29checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_30checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_31checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_32checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_33checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_703checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_34checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_35checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_36checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_37checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_38checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_39checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_40checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_41checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_42checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_43checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_704checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_44checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_45checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_46checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_47checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_48checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_49checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_50checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_51checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_705checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_706checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_707checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_708checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_709checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_710checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_711checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_712checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_689checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_713checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_714checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_715checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_716checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_717checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_718checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_719checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_720checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_721checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_722checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_690checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_723checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_724checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_725checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_726checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_727checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_728checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_729checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_730checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_731checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_732checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_691checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_733checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_734checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_735checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_736checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_737checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_738checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_739checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_740checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_741checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_742checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_692checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_743checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_744checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_745checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_746checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_747checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_748checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_749checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_750checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_751checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_752checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_693checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_753checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_754checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_755checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_756checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_757checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_758checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_759checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_760checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_761checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_762checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_694checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_763checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_764checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_765checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_766checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_767checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_768checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_769checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_770checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_771checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_772checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_695checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_773checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_774checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_775checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_776checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_777checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_778checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_779checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_780checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_781checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_782checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_696checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_783checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_784checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_785checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_786checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_787checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_788checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_789checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_790checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_791checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_792checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_697checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_793checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_794checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_795checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_796checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_797checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_798checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_799checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_800checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_801checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_802checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_698checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_803checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_804checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_805checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_806checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_807checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_808checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_809checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_810checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_811checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_812checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_699checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_813checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_814checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_815checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_816checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_817checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_818checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_819checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_0checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_1checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_2checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_700checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_3checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t5_4checked⟩
