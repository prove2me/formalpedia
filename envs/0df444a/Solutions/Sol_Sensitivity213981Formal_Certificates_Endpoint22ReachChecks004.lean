-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks004
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:02:21.541378+00:00
-- url     : https://prove2.me/submissions/517f7e12-77b5-46ca-9143-929562b4b347

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans018
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans020
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans023
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans024
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans025
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

























































































































theorem valid61 : plan61.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid62 : plan62.Valid := valid_step _ _ _ valid0 (by decide +kernel)













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





































































































theorem valid339 : plan339.Valid := valid_step _ _ _ valid61 (by decide +kernel)

theorem valid340 : plan340.Valid := valid_step _ _ _ valid62 (by decide +kernel)











theorem valid346 : plan346.Valid := valid_step _ _ _ valid62 (by decide +kernel)



















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



























































































































theorem valid926 : plan926.Valid := valid_step _ _ _ valid339 (by decide +kernel)

theorem valid927 : plan927.Valid := valid_step _ _ _ valid340 (by decide +kernel)











theorem valid933 : plan933.Valid := valid_step _ _ _ valid346 (by decide +kernel)











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





















theorem valid395 : plan395.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid396 : plan396.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid397 : plan397.Valid := valid_step _ _ _ valid80 (by decide +kernel)









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











































theorem valid1021 : plan1021.Valid := valid_step _ _ _ valid361 (by decide +kernel)







































theorem valid1041 : plan1041.Valid := valid_step _ _ _ valid361 (by decide +kernel)









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











































































































































theorem valid1798 : plan1798.Valid := valid_step _ _ _ valid939 (by decide +kernel)

theorem valid1799 : plan1799.Valid := valid_step _ _ _ valid926 (by decide +kernel)

theorem valid1800 : plan1800.Valid := valid_step _ _ _ valid927 (by decide +kernel)

theorem valid1801 : plan1801.Valid := valid_step _ _ _ valid933 (by decide +kernel)














































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















































































































































theorem valid1992 : plan1992.Valid := valid_step _ _ _ valid1041 (by decide +kernel)

theorem valid1993 : plan1993.Valid := valid_step _ _ _ valid997 (by decide +kernel)

theorem valid1994 : plan1994.Valid := valid_step _ _ _ valid998 (by decide +kernel)

theorem valid1995 : plan1995.Valid := valid_step _ _ _ valid999 (by decide +kernel)

theorem valid1996 : plan1996.Valid := valid_step _ _ _ valid1021 (by decide +kernel)

theorem valid1997 : plan1997.Valid := valid_step _ _ _ valid1041 (by decide +kernel)

theorem valid1998 : plan1998.Valid := valid_step _ _ _ valid972 (by decide +kernel)

theorem valid1999 : plan1999.Valid := valid_step _ _ _ valid973 (by decide +kernel)

theorem valid2000 : plan2000.Valid := valid_step _ _ _ valid974 (by decide +kernel)

theorem valid2001 : plan2001.Valid := valid_step _ _ _ valid975 (by decide +kernel)

theorem valid2002 : plan2002.Valid := valid_step _ _ _ valid976 (by decide +kernel)

theorem valid2003 : plan2003.Valid := valid_step _ _ _ valid977 (by decide +kernel)

theorem valid2004 : plan2004.Valid := valid_step _ _ _ valid978 (by decide +kernel)

theorem valid2005 : plan2005.Valid := valid_step _ _ _ valid979 (by decide +kernel)

theorem valid2006 : plan2006.Valid := valid_step _ _ _ valid980 (by decide +kernel)

theorem valid2007 : plan2007.Valid := valid_step _ _ _ valid990 (by decide +kernel)


















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



































































theorem valid2242 : plan2242.Valid := valid_step _ _ _ valid1133 (by decide +kernel)

theorem valid2243 : plan2243.Valid := valid_step _ _ _ valid1134 (by decide +kernel)

theorem valid2244 : plan2244.Valid := valid_step _ _ _ valid1135 (by decide +kernel)

theorem valid2245 : plan2245.Valid := valid_step _ _ _ valid1145 (by decide +kernel)

theorem valid2246 : plan2246.Valid := valid_step _ _ _ valid1149 (by decide +kernel)

theorem valid2247 : plan2247.Valid := valid_step _ _ _ valid1156 (by decide +kernel)

theorem valid2248 : plan2248.Valid := valid_step _ _ _ valid1157 (by decide +kernel)

theorem valid2249 : plan2249.Valid := valid_step _ _ _ valid1158 (by decide +kernel)

theorem valid2250 : plan2250.Valid := valid_step _ _ _ valid1163 (by decide +kernel)

theorem valid2251 : plan2251.Valid := valid_step _ _ _ valid1061 (by decide +kernel)

theorem valid2252 : plan2252.Valid := valid_step _ _ _ valid1062 (by decide +kernel)

theorem valid2253 : plan2253.Valid := valid_step _ _ _ valid1063 (by decide +kernel)

theorem valid2254 : plan2254.Valid := valid_step _ _ _ valid1064 (by decide +kernel)

theorem valid2255 : plan2255.Valid := valid_step _ _ _ valid1065 (by decide +kernel)

theorem valid2256 : plan2256.Valid := valid_step _ _ _ valid1066 (by decide +kernel)

theorem valid2257 : plan2257.Valid := valid_step _ _ _ valid1100 (by decide +kernel)

theorem valid2258 : plan2258.Valid := valid_step _ _ _ valid1101 (by decide +kernel)

theorem valid2259 : plan2259.Valid := valid_step _ _ _ valid1102 (by decide +kernel)

theorem valid2260 : plan2260.Valid := valid_step _ _ _ valid1103 (by decide +kernel)

theorem valid2261 : plan2261.Valid := valid_step _ _ _ valid1113 (by decide +kernel)

theorem valid2262 : plan2262.Valid := valid_step _ _ _ valid1156 (by decide +kernel)

theorem valid2263 : plan2263.Valid := valid_step _ _ _ valid1157 (by decide +kernel)

theorem valid2264 : plan2264.Valid := valid_step _ _ _ valid1158 (by decide +kernel)

theorem valid2265 : plan2265.Valid := valid_step _ _ _ valid1163 (by decide +kernel)

theorem valid2266 : plan2266.Valid := valid_step _ _ _ valid1046 (by decide +kernel)

theorem valid2267 : plan2267.Valid := valid_step _ _ _ valid1047 (by decide +kernel)

theorem valid2268 : plan2268.Valid := valid_step _ _ _ valid1048 (by decide +kernel)

theorem valid2269 : plan2269.Valid := valid_step _ _ _ valid1049 (by decide +kernel)

theorem valid2270 : plan2270.Valid := valid_step _ _ _ valid1050 (by decide +kernel)

theorem valid2271 : plan2271.Valid := valid_step _ _ _ valid1051 (by decide +kernel)

theorem valid2272 : plan2272.Valid := valid_step _ _ _ valid1052 (by decide +kernel)

theorem valid2273 : plan2273.Valid := valid_step _ _ _ valid1053 (by decide +kernel)

theorem valid2274 : plan2274.Valid := valid_step _ _ _ valid1054 (by decide +kernel)

theorem valid2275 : plan2275.Valid := valid_step _ _ _ valid1055 (by decide +kernel)


























































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















































































































theorem valid2360 : plan2360.Valid := valid_step _ _ _ valid1216 (by decide +kernel)

theorem valid2361 : plan2361.Valid := valid_step _ _ _ valid1217 (by decide +kernel)

theorem valid2362 : plan2362.Valid := valid_step _ _ _ valid1218 (by decide +kernel)

theorem valid2363 : plan2363.Valid := valid_step _ _ _ valid1219 (by decide +kernel)

theorem valid2364 : plan2364.Valid := valid_step _ _ _ valid1220 (by decide +kernel)

theorem valid2365 : plan2365.Valid := valid_step _ _ _ valid1221 (by decide +kernel)

theorem valid2366 : plan2366.Valid := valid_step _ _ _ valid1222 (by decide +kernel)

theorem valid2367 : plan2367.Valid := valid_step _ _ _ valid1223 (by decide +kernel)

theorem valid2368 : plan2368.Valid := valid_step _ _ _ valid1224 (by decide +kernel)

theorem valid2369 : plan2369.Valid := valid_step _ _ _ valid1225 (by decide +kernel)

theorem valid2370 : plan2370.Valid := valid_step _ _ _ valid1226 (by decide +kernel)

theorem valid2371 : plan2371.Valid := valid_step _ _ _ valid1227 (by decide +kernel)

theorem valid2372 : plan2372.Valid := valid_step _ _ _ valid1228 (by decide +kernel)

theorem valid2373 : plan2373.Valid := valid_step _ _ _ valid1229 (by decide +kernel)

theorem valid2374 : plan2374.Valid := valid_step _ _ _ valid1230 (by decide +kernel)

theorem valid2375 : plan2375.Valid := valid_step _ _ _ valid1231 (by decide +kernel)

theorem valid2376 : plan2376.Valid := valid_step _ _ _ valid1232 (by decide +kernel)

theorem valid2377 : plan2377.Valid := valid_step _ _ _ valid1233 (by decide +kernel)

theorem valid2378 : plan2378.Valid := valid_step _ _ _ valid1234 (by decide +kernel)

theorem valid2379 : plan2379.Valid := valid_step _ _ _ valid1235 (by decide +kernel)

theorem valid2380 : plan2380.Valid := valid_step _ _ _ valid1236 (by decide +kernel)

theorem valid2381 : plan2381.Valid := valid_step _ _ _ valid1237 (by decide +kernel)

theorem valid2382 : plan2382.Valid := valid_step _ _ _ valid1238 (by decide +kernel)

theorem valid2383 : plan2383.Valid := valid_step _ _ _ valid1239 (by decide +kernel)

theorem valid2384 : plan2384.Valid := valid_step _ _ _ valid1240 (by decide +kernel)

theorem valid2385 : plan2385.Valid := valid_step _ _ _ valid1241 (by decide +kernel)

theorem valid2386 : plan2386.Valid := valid_step _ _ _ valid1242 (by decide +kernel)

theorem valid2387 : plan2387.Valid := valid_step _ _ _ valid1243 (by decide +kernel)

theorem valid2388 : plan2388.Valid := valid_step _ _ _ valid1244 (by decide +kernel)

theorem valid2389 : plan2389.Valid := valid_step _ _ _ valid1245 (by decide +kernel)

theorem valid2390 : plan2390.Valid := valid_step _ _ _ valid1246 (by decide +kernel)

theorem valid2391 : plan2391.Valid := valid_step _ _ _ valid1194 (by decide +kernel)

theorem valid2392 : plan2392.Valid := valid_step _ _ _ valid1195 (by decide +kernel)

theorem valid2393 : plan2393.Valid := valid_step _ _ _ valid1196 (by decide +kernel)

theorem valid2394 : plan2394.Valid := valid_step _ _ _ valid1197 (by decide +kernel)

theorem valid2395 : plan2395.Valid := valid_step _ _ _ valid1198 (by decide +kernel)

theorem valid2396 : plan2396.Valid := valid_step _ _ _ valid1199 (by decide +kernel)

theorem valid2397 : plan2397.Valid := valid_step _ _ _ valid1200 (by decide +kernel)

theorem valid2398 : plan2398.Valid := valid_step _ _ _ valid1201 (by decide +kernel)

theorem valid2399 : plan2399.Valid := valid_step _ _ _ valid1202 (by decide +kernel)

theorem valid2400 : plan2400.Valid := valid_step _ _ _ valid1203 (by decide +kernel)
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

theorem valid2401 : plan2401.Valid := valid_step _ _ _ valid1204 (by decide +kernel)

theorem valid2402 : plan2402.Valid := valid_step _ _ _ valid1205 (by decide +kernel)

theorem valid2403 : plan2403.Valid := valid_step _ _ _ valid1206 (by decide +kernel)

theorem valid2404 : plan2404.Valid := valid_step _ _ _ valid1207 (by decide +kernel)

theorem valid2405 : plan2405.Valid := valid_step _ _ _ valid1208 (by decide +kernel)

theorem valid2406 : plan2406.Valid := valid_step _ _ _ valid1209 (by decide +kernel)

theorem valid2407 : plan2407.Valid := valid_step _ _ _ valid1210 (by decide +kernel)

theorem valid2408 : plan2408.Valid := valid_step _ _ _ valid1211 (by decide +kernel)

theorem valid2409 : plan2409.Valid := valid_step _ _ _ valid1212 (by decide +kernel)

theorem valid2410 : plan2410.Valid := valid_step _ _ _ valid1213 (by decide +kernel)

theorem valid2411 : plan2411.Valid := valid_step _ _ _ valid1214 (by decide +kernel)

theorem valid2412 : plan2412.Valid := valid_step _ _ _ valid1215 (by decide +kernel)

theorem valid2413 : plan2413.Valid := valid_step _ _ _ valid1234 (by decide +kernel)

theorem valid2414 : plan2414.Valid := valid_step _ _ _ valid1235 (by decide +kernel)

theorem valid2415 : plan2415.Valid := valid_step _ _ _ valid1236 (by decide +kernel)

theorem valid2416 : plan2416.Valid := valid_step _ _ _ valid1237 (by decide +kernel)

theorem valid2417 : plan2417.Valid := valid_step _ _ _ valid1238 (by decide +kernel)

theorem valid2418 : plan2418.Valid := valid_step _ _ _ valid1239 (by decide +kernel)

theorem valid2419 : plan2419.Valid := valid_step _ _ _ valid1240 (by decide +kernel)

theorem valid2420 : plan2420.Valid := valid_step _ _ _ valid1241 (by decide +kernel)

theorem valid2421 : plan2421.Valid := valid_step _ _ _ valid1242 (by decide +kernel)

theorem valid2422 : plan2422.Valid := valid_step _ _ _ valid1243 (by decide +kernel)

theorem valid2423 : plan2423.Valid := valid_step _ _ _ valid1244 (by decide +kernel)

theorem valid2424 : plan2424.Valid := valid_step _ _ _ valid1245 (by decide +kernel)

theorem valid2425 : plan2425.Valid := valid_step _ _ _ valid1246 (by decide +kernel)

theorem valid2426 : plan2426.Valid := valid_step _ _ _ valid1209 (by decide +kernel)

theorem valid2427 : plan2427.Valid := valid_step _ _ _ valid1210 (by decide +kernel)

theorem valid2428 : plan2428.Valid := valid_step _ _ _ valid1211 (by decide +kernel)

theorem valid2429 : plan2429.Valid := valid_step _ _ _ valid1212 (by decide +kernel)

theorem valid2430 : plan2430.Valid := valid_step _ _ _ valid1213 (by decide +kernel)

theorem valid2431 : plan2431.Valid := valid_step _ _ _ valid1214 (by decide +kernel)

theorem valid2432 : plan2432.Valid := valid_step _ _ _ valid1215 (by decide +kernel)

theorem valid2433 : plan2433.Valid := valid_step _ _ _ valid1244 (by decide +kernel)

theorem valid2434 : plan2434.Valid := valid_step _ _ _ valid1245 (by decide +kernel)

theorem valid2435 : plan2435.Valid := valid_step _ _ _ valid1246 (by decide +kernel)

theorem valid2436 : plan2436.Valid := valid_step _ _ _ valid1215 (by decide +kernel)
























































































































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
theorem t4_557choices : plan2242.choices=[4,8,3,7].map (options 4 3) := by rfl


theorem t4_557part0 : t4_557jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_557frontier : t4_557root.frontier 0=t4_557jobs := by rfl
theorem t4_557all : t4_557jobs.all (Job.check tree)=true := by
  simp only [t4_557jobs,List.all_append,List.all_nil,t4_557part0,Bool.and_self]
theorem t4_557checked : Checked tree [4,8,3,7] := by
  refine ⟨plan2242,valid2242,t4_557choices,?_⟩
  exact check_of_frontier tree 0 t4_557root t4_557jobs t4_557frontier t4_557all
theorem t4_558choices : plan2243.choices=[4,8,3,10].map (options 4 3) := by rfl


theorem t4_558part0 : t4_558jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_558frontier : t4_558root.frontier 0=t4_558jobs := by rfl
theorem t4_558all : t4_558jobs.all (Job.check tree)=true := by
  simp only [t4_558jobs,List.all_append,List.all_nil,t4_558part0,Bool.and_self]
theorem t4_558checked : Checked tree [4,8,3,10] := by
  refine ⟨plan2243,valid2243,t4_558choices,?_⟩
  exact check_of_frontier tree 0 t4_558root t4_558jobs t4_558frontier t4_558all
theorem t4_559choices : plan2244.choices=[4,8,5,3].map (options 4 3) := by rfl


theorem t4_559part0 : t4_559jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_559frontier : t4_559root.frontier 0=t4_559jobs := by rfl
theorem t4_559all : t4_559jobs.all (Job.check tree)=true := by
  simp only [t4_559jobs,List.all_append,List.all_nil,t4_559part0,Bool.and_self]
theorem t4_559checked : Checked tree [4,8,5,3] := by
  refine ⟨plan2244,valid2244,t4_559choices,?_⟩
  exact check_of_frontier tree 0 t4_559root t4_559jobs t4_559frontier t4_559all
theorem t4_560choices : plan2360.choices=[4,8,5,5].map (options 4 4) := by rfl


theorem t4_560part0 : t4_560jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_560frontier : t4_560root.frontier 0=t4_560jobs := by rfl
theorem t4_560all : t4_560jobs.all (Job.check tree)=true := by
  simp only [t4_560jobs,List.all_append,List.all_nil,t4_560part0,Bool.and_self]
theorem t4_560checked : Checked tree [4,8,5,5] := by
  refine ⟨plan2360,valid2360,t4_560choices,?_⟩
  exact check_of_frontier tree 0 t4_560root t4_560jobs t4_560frontier t4_560all
theorem t4_561choices : plan2361.choices=[4,8,5,6].map (options 4 4) := by rfl


theorem t4_561part0 : t4_561jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_561frontier : t4_561root.frontier 0=t4_561jobs := by rfl
theorem t4_561all : t4_561jobs.all (Job.check tree)=true := by
  simp only [t4_561jobs,List.all_append,List.all_nil,t4_561part0,Bool.and_self]
theorem t4_561checked : Checked tree [4,8,5,6] := by
  refine ⟨plan2361,valid2361,t4_561choices,?_⟩
  exact check_of_frontier tree 0 t4_561root t4_561jobs t4_561frontier t4_561all
theorem t4_562choices : plan2362.choices=[4,8,5,7].map (options 4 4) := by rfl


theorem t4_562part0 : t4_562jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_562frontier : t4_562root.frontier 0=t4_562jobs := by rfl
theorem t4_562all : t4_562jobs.all (Job.check tree)=true := by
  simp only [t4_562jobs,List.all_append,List.all_nil,t4_562part0,Bool.and_self]
theorem t4_562checked : Checked tree [4,8,5,7] := by
  refine ⟨plan2362,valid2362,t4_562choices,?_⟩
  exact check_of_frontier tree 0 t4_562root t4_562jobs t4_562frontier t4_562all
theorem t4_563choices : plan2363.choices=[4,8,5,9].map (options 4 4) := by rfl


theorem t4_563part0 : t4_563jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_563frontier : t4_563root.frontier 0=t4_563jobs := by rfl
theorem t4_563all : t4_563jobs.all (Job.check tree)=true := by
  simp only [t4_563jobs,List.all_append,List.all_nil,t4_563part0,Bool.and_self]
theorem t4_563checked : Checked tree [4,8,5,9] := by
  refine ⟨plan2363,valid2363,t4_563choices,?_⟩
  exact check_of_frontier tree 0 t4_563root t4_563jobs t4_563frontier t4_563all
theorem t4_564choices : plan2364.choices=[4,8,5,10].map (options 4 4) := by rfl


theorem t4_564part0 : t4_564jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_564frontier : t4_564root.frontier 0=t4_564jobs := by rfl
theorem t4_564all : t4_564jobs.all (Job.check tree)=true := by
  simp only [t4_564jobs,List.all_append,List.all_nil,t4_564part0,Bool.and_self]
theorem t4_564checked : Checked tree [4,8,5,10] := by
  refine ⟨plan2364,valid2364,t4_564choices,?_⟩
  exact check_of_frontier tree 0 t4_564root t4_564jobs t4_564frontier t4_564all
theorem t4_565choices : plan2365.choices=[4,8,6,6].map (options 4 4) := by rfl


theorem t4_565part0 : t4_565jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_565frontier : t4_565root.frontier 0=t4_565jobs := by rfl
theorem t4_565all : t4_565jobs.all (Job.check tree)=true := by
  simp only [t4_565jobs,List.all_append,List.all_nil,t4_565part0,Bool.and_self]
theorem t4_565checked : Checked tree [4,8,6,6] := by
  refine ⟨plan2365,valid2365,t4_565choices,?_⟩
  exact check_of_frontier tree 0 t4_565root t4_565jobs t4_565frontier t4_565all
theorem t4_566choices : plan2366.choices=[4,8,6,7].map (options 4 4) := by rfl


theorem t4_566part0 : t4_566jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_566frontier : t4_566root.frontier 0=t4_566jobs := by rfl
theorem t4_566all : t4_566jobs.all (Job.check tree)=true := by
  simp only [t4_566jobs,List.all_append,List.all_nil,t4_566part0,Bool.and_self]
theorem t4_566checked : Checked tree [4,8,6,7] := by
  refine ⟨plan2366,valid2366,t4_566choices,?_⟩
  exact check_of_frontier tree 0 t4_566root t4_566jobs t4_566frontier t4_566all
theorem t4_567choices : plan2367.choices=[4,8,6,10].map (options 4 4) := by rfl


theorem t4_567part0 : t4_567jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_567frontier : t4_567root.frontier 0=t4_567jobs := by rfl
theorem t4_567all : t4_567jobs.all (Job.check tree)=true := by
  simp only [t4_567jobs,List.all_append,List.all_nil,t4_567part0,Bool.and_self]
theorem t4_567checked : Checked tree [4,8,6,10] := by
  refine ⟨plan2367,valid2367,t4_567choices,?_⟩
  exact check_of_frontier tree 0 t4_567root t4_567jobs t4_567frontier t4_567all
theorem t4_568choices : plan2368.choices=[4,8,7,7].map (options 4 4) := by rfl


theorem t4_568part0 : t4_568jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_568frontier : t4_568root.frontier 0=t4_568jobs := by rfl
theorem t4_568all : t4_568jobs.all (Job.check tree)=true := by
  simp only [t4_568jobs,List.all_append,List.all_nil,t4_568part0,Bool.and_self]
theorem t4_568checked : Checked tree [4,8,7,7] := by
  refine ⟨plan2368,valid2368,t4_568choices,?_⟩
  exact check_of_frontier tree 0 t4_568root t4_568jobs t4_568frontier t4_568all
theorem t4_569choices : plan2245.choices=[4,8,8,3].map (options 4 3) := by rfl


theorem t4_569part0 : t4_569jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_569frontier : t4_569root.frontier 0=t4_569jobs := by rfl
theorem t4_569all : t4_569jobs.all (Job.check tree)=true := by
  simp only [t4_569jobs,List.all_append,List.all_nil,t4_569part0,Bool.and_self]
theorem t4_569checked : Checked tree [4,8,8,3] := by
  refine ⟨plan2245,valid2245,t4_569choices,?_⟩
  exact check_of_frontier tree 0 t4_569root t4_569jobs t4_569frontier t4_569all
theorem t4_570choices : plan2369.choices=[4,8,8,6].map (options 4 4) := by rfl


theorem t4_570part0 : t4_570jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_570frontier : t4_570root.frontier 0=t4_570jobs := by rfl
theorem t4_570all : t4_570jobs.all (Job.check tree)=true := by
  simp only [t4_570jobs,List.all_append,List.all_nil,t4_570part0,Bool.and_self]
theorem t4_570checked : Checked tree [4,8,8,6] := by
  refine ⟨plan2369,valid2369,t4_570choices,?_⟩
  exact check_of_frontier tree 0 t4_570root t4_570jobs t4_570frontier t4_570all
theorem t4_571choices : plan2370.choices=[4,8,8,7].map (options 4 4) := by rfl


theorem t4_571part0 : t4_571jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_571frontier : t4_571root.frontier 0=t4_571jobs := by rfl
theorem t4_571all : t4_571jobs.all (Job.check tree)=true := by
  simp only [t4_571jobs,List.all_append,List.all_nil,t4_571part0,Bool.and_self]
theorem t4_571checked : Checked tree [4,8,8,7] := by
  refine ⟨plan2370,valid2370,t4_571choices,?_⟩
  exact check_of_frontier tree 0 t4_571root t4_571jobs t4_571frontier t4_571all
theorem t4_572choices : plan2371.choices=[4,8,8,10].map (options 4 4) := by rfl


theorem t4_572part0 : t4_572jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_572frontier : t4_572root.frontier 0=t4_572jobs := by rfl
theorem t4_572all : t4_572jobs.all (Job.check tree)=true := by
  simp only [t4_572jobs,List.all_append,List.all_nil,t4_572part0,Bool.and_self]
theorem t4_572checked : Checked tree [4,8,8,10] := by
  refine ⟨plan2371,valid2371,t4_572choices,?_⟩
  exact check_of_frontier tree 0 t4_572root t4_572jobs t4_572frontier t4_572all
theorem t4_573choices : plan2246.choices=[4,8,9,3].map (options 4 3) := by rfl


theorem t4_573part0 : t4_573jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_573frontier : t4_573root.frontier 0=t4_573jobs := by rfl
theorem t4_573all : t4_573jobs.all (Job.check tree)=true := by
  simp only [t4_573jobs,List.all_append,List.all_nil,t4_573part0,Bool.and_self]
theorem t4_573checked : Checked tree [4,8,9,3] := by
  refine ⟨plan2246,valid2246,t4_573choices,?_⟩
  exact check_of_frontier tree 0 t4_573root t4_573jobs t4_573frontier t4_573all
theorem t4_574choices : plan2372.choices=[4,8,9,6].map (options 4 4) := by rfl


theorem t4_574part0 : t4_574jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_574frontier : t4_574root.frontier 0=t4_574jobs := by rfl
theorem t4_574all : t4_574jobs.all (Job.check tree)=true := by
  simp only [t4_574jobs,List.all_append,List.all_nil,t4_574part0,Bool.and_self]
theorem t4_574checked : Checked tree [4,8,9,6] := by
  refine ⟨plan2372,valid2372,t4_574choices,?_⟩
  exact check_of_frontier tree 0 t4_574root t4_574jobs t4_574frontier t4_574all
theorem t4_575choices : plan2373.choices=[4,8,9,7].map (options 4 4) := by rfl


theorem t4_575part0 : t4_575jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_575frontier : t4_575root.frontier 0=t4_575jobs := by rfl
theorem t4_575all : t4_575jobs.all (Job.check tree)=true := by
  simp only [t4_575jobs,List.all_append,List.all_nil,t4_575part0,Bool.and_self]
theorem t4_575checked : Checked tree [4,8,9,7] := by
  refine ⟨plan2373,valid2373,t4_575choices,?_⟩
  exact check_of_frontier tree 0 t4_575root t4_575jobs t4_575frontier t4_575all
theorem t4_576choices : plan2374.choices=[4,8,9,9].map (options 4 4) := by rfl


theorem t4_576part0 : t4_576jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_576frontier : t4_576root.frontier 0=t4_576jobs := by rfl
theorem t4_576all : t4_576jobs.all (Job.check tree)=true := by
  simp only [t4_576jobs,List.all_append,List.all_nil,t4_576part0,Bool.and_self]
theorem t4_576checked : Checked tree [4,8,9,9] := by
  refine ⟨plan2374,valid2374,t4_576choices,?_⟩
  exact check_of_frontier tree 0 t4_576root t4_576jobs t4_576frontier t4_576all
theorem t4_577choices : plan2375.choices=[4,8,9,10].map (options 4 4) := by rfl


theorem t4_577part0 : t4_577jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_577frontier : t4_577root.frontier 0=t4_577jobs := by rfl
theorem t4_577all : t4_577jobs.all (Job.check tree)=true := by
  simp only [t4_577jobs,List.all_append,List.all_nil,t4_577part0,Bool.and_self]
theorem t4_577checked : Checked tree [4,8,9,10] := by
  refine ⟨plan2375,valid2375,t4_577choices,?_⟩
  exact check_of_frontier tree 0 t4_577root t4_577jobs t4_577frontier t4_577all
theorem t4_578choices : plan2376.choices=[4,8,10,7].map (options 4 4) := by rfl


theorem t4_578part0 : t4_578jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_578frontier : t4_578root.frontier 0=t4_578jobs := by rfl
theorem t4_578all : t4_578jobs.all (Job.check tree)=true := by
  simp only [t4_578jobs,List.all_append,List.all_nil,t4_578part0,Bool.and_self]
theorem t4_578checked : Checked tree [4,8,10,7] := by
  refine ⟨plan2376,valid2376,t4_578choices,?_⟩
  exact check_of_frontier tree 0 t4_578root t4_578jobs t4_578frontier t4_578all
theorem t4_579choices : plan2377.choices=[4,8,10,10].map (options 4 4) := by rfl


theorem t4_579part0 : t4_579jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_579frontier : t4_579root.frontier 0=t4_579jobs := by rfl
theorem t4_579all : t4_579jobs.all (Job.check tree)=true := by
  simp only [t4_579jobs,List.all_append,List.all_nil,t4_579part0,Bool.and_self]
theorem t4_579checked : Checked tree [4,8,10,10] := by
  refine ⟨plan2377,valid2377,t4_579choices,?_⟩
  exact check_of_frontier tree 0 t4_579root t4_579jobs t4_579frontier t4_579all
theorem t4_580choices : plan1992.choices=[4,9,3,3].map (options 4 2) := by rfl


theorem t4_580part0 : t4_580jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_580frontier : t4_580root.frontier 0=t4_580jobs := by rfl
theorem t4_580all : t4_580jobs.all (Job.check tree)=true := by
  simp only [t4_580jobs,List.all_append,List.all_nil,t4_580part0,Bool.and_self]
theorem t4_580checked : Checked tree [4,9,3,3] := by
  refine ⟨plan1992,valid1992,t4_580choices,?_⟩
  exact check_of_frontier tree 0 t4_580root t4_580jobs t4_580frontier t4_580all
theorem t4_581choices : plan2247.choices=[4,9,3,6].map (options 4 3) := by rfl


theorem t4_581part0 : t4_581jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_581frontier : t4_581root.frontier 0=t4_581jobs := by rfl
theorem t4_581all : t4_581jobs.all (Job.check tree)=true := by
  simp only [t4_581jobs,List.all_append,List.all_nil,t4_581part0,Bool.and_self]
theorem t4_581checked : Checked tree [4,9,3,6] := by
  refine ⟨plan2247,valid2247,t4_581choices,?_⟩
  exact check_of_frontier tree 0 t4_581root t4_581jobs t4_581frontier t4_581all
theorem t4_582choices : plan2248.choices=[4,9,3,7].map (options 4 3) := by rfl


theorem t4_582part0 : t4_582jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_582frontier : t4_582root.frontier 0=t4_582jobs := by rfl
theorem t4_582all : t4_582jobs.all (Job.check tree)=true := by
  simp only [t4_582jobs,List.all_append,List.all_nil,t4_582part0,Bool.and_self]
theorem t4_582checked : Checked tree [4,9,3,7] := by
  refine ⟨plan2248,valid2248,t4_582choices,?_⟩
  exact check_of_frontier tree 0 t4_582root t4_582jobs t4_582frontier t4_582all
theorem t4_583choices : plan2249.choices=[4,9,3,10].map (options 4 3) := by rfl


theorem t4_583part0 : t4_583jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_583frontier : t4_583root.frontier 0=t4_583jobs := by rfl
theorem t4_583all : t4_583jobs.all (Job.check tree)=true := by
  simp only [t4_583jobs,List.all_append,List.all_nil,t4_583part0,Bool.and_self]
theorem t4_583checked : Checked tree [4,9,3,10] := by
  refine ⟨plan2249,valid2249,t4_583choices,?_⟩
  exact check_of_frontier tree 0 t4_583root t4_583jobs t4_583frontier t4_583all
theorem t4_584choices : plan2378.choices=[4,9,6,6].map (options 4 4) := by rfl


theorem t4_584part0 : t4_584jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_584frontier : t4_584root.frontier 0=t4_584jobs := by rfl
theorem t4_584all : t4_584jobs.all (Job.check tree)=true := by
  simp only [t4_584jobs,List.all_append,List.all_nil,t4_584part0,Bool.and_self]
theorem t4_584checked : Checked tree [4,9,6,6] := by
  refine ⟨plan2378,valid2378,t4_584choices,?_⟩
  exact check_of_frontier tree 0 t4_584root t4_584jobs t4_584frontier t4_584all
theorem t4_585choices : plan2379.choices=[4,9,6,7].map (options 4 4) := by rfl


theorem t4_585part0 : t4_585jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_585frontier : t4_585root.frontier 0=t4_585jobs := by rfl
theorem t4_585all : t4_585jobs.all (Job.check tree)=true := by
  simp only [t4_585jobs,List.all_append,List.all_nil,t4_585part0,Bool.and_self]
theorem t4_585checked : Checked tree [4,9,6,7] := by
  refine ⟨plan2379,valid2379,t4_585choices,?_⟩
  exact check_of_frontier tree 0 t4_585root t4_585jobs t4_585frontier t4_585all
theorem t4_586choices : plan2380.choices=[4,9,6,10].map (options 4 4) := by rfl


theorem t4_586part0 : t4_586jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_586frontier : t4_586root.frontier 0=t4_586jobs := by rfl
theorem t4_586all : t4_586jobs.all (Job.check tree)=true := by
  simp only [t4_586jobs,List.all_append,List.all_nil,t4_586part0,Bool.and_self]
theorem t4_586checked : Checked tree [4,9,6,10] := by
  refine ⟨plan2380,valid2380,t4_586choices,?_⟩
  exact check_of_frontier tree 0 t4_586root t4_586jobs t4_586frontier t4_586all
theorem t4_587choices : plan2381.choices=[4,9,7,7].map (options 4 4) := by rfl


theorem t4_587part0 : t4_587jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_587frontier : t4_587root.frontier 0=t4_587jobs := by rfl
theorem t4_587all : t4_587jobs.all (Job.check tree)=true := by
  simp only [t4_587jobs,List.all_append,List.all_nil,t4_587part0,Bool.and_self]
theorem t4_587checked : Checked tree [4,9,7,7] := by
  refine ⟨plan2381,valid2381,t4_587choices,?_⟩
  exact check_of_frontier tree 0 t4_587root t4_587jobs t4_587frontier t4_587all
theorem t4_588choices : plan2250.choices=[4,9,9,3].map (options 4 3) := by rfl


theorem t4_588part0 : t4_588jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_588frontier : t4_588root.frontier 0=t4_588jobs := by rfl
theorem t4_588all : t4_588jobs.all (Job.check tree)=true := by
  simp only [t4_588jobs,List.all_append,List.all_nil,t4_588part0,Bool.and_self]
theorem t4_588checked : Checked tree [4,9,9,3] := by
  refine ⟨plan2250,valid2250,t4_588choices,?_⟩
  exact check_of_frontier tree 0 t4_588root t4_588jobs t4_588frontier t4_588all
theorem t4_589choices : plan2382.choices=[4,9,9,6].map (options 4 4) := by rfl


theorem t4_589part0 : t4_589jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_589frontier : t4_589root.frontier 0=t4_589jobs := by rfl
theorem t4_589all : t4_589jobs.all (Job.check tree)=true := by
  simp only [t4_589jobs,List.all_append,List.all_nil,t4_589part0,Bool.and_self]
theorem t4_589checked : Checked tree [4,9,9,6] := by
  refine ⟨plan2382,valid2382,t4_589choices,?_⟩
  exact check_of_frontier tree 0 t4_589root t4_589jobs t4_589frontier t4_589all
theorem t4_590choices : plan2383.choices=[4,9,9,7].map (options 4 4) := by rfl


theorem t4_590part0 : t4_590jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_590frontier : t4_590root.frontier 0=t4_590jobs := by rfl
theorem t4_590all : t4_590jobs.all (Job.check tree)=true := by
  simp only [t4_590jobs,List.all_append,List.all_nil,t4_590part0,Bool.and_self]
theorem t4_590checked : Checked tree [4,9,9,7] := by
  refine ⟨plan2383,valid2383,t4_590choices,?_⟩
  exact check_of_frontier tree 0 t4_590root t4_590jobs t4_590frontier t4_590all
theorem t4_591choices : plan2384.choices=[4,9,9,9].map (options 4 4) := by rfl


theorem t4_591part0 : t4_591jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_591frontier : t4_591root.frontier 0=t4_591jobs := by rfl
theorem t4_591all : t4_591jobs.all (Job.check tree)=true := by
  simp only [t4_591jobs,List.all_append,List.all_nil,t4_591part0,Bool.and_self]
theorem t4_591checked : Checked tree [4,9,9,9] := by
  refine ⟨plan2384,valid2384,t4_591choices,?_⟩
  exact check_of_frontier tree 0 t4_591root t4_591jobs t4_591frontier t4_591all
theorem t4_592choices : plan2385.choices=[4,9,9,10].map (options 4 4) := by rfl


theorem t4_592part0 : t4_592jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_592frontier : t4_592root.frontier 0=t4_592jobs := by rfl
theorem t4_592all : t4_592jobs.all (Job.check tree)=true := by
  simp only [t4_592jobs,List.all_append,List.all_nil,t4_592part0,Bool.and_self]
theorem t4_592checked : Checked tree [4,9,9,10] := by
  refine ⟨plan2385,valid2385,t4_592choices,?_⟩
  exact check_of_frontier tree 0 t4_592root t4_592jobs t4_592frontier t4_592all
theorem t4_593choices : plan2386.choices=[4,9,10,7].map (options 4 4) := by rfl


theorem t4_593part0 : t4_593jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_593frontier : t4_593root.frontier 0=t4_593jobs := by rfl
theorem t4_593all : t4_593jobs.all (Job.check tree)=true := by
  simp only [t4_593jobs,List.all_append,List.all_nil,t4_593part0,Bool.and_self]
theorem t4_593checked : Checked tree [4,9,10,7] := by
  refine ⟨plan2386,valid2386,t4_593choices,?_⟩
  exact check_of_frontier tree 0 t4_593root t4_593jobs t4_593frontier t4_593all
theorem t4_594choices : plan2387.choices=[4,9,10,10].map (options 4 4) := by rfl


theorem t4_594part0 : t4_594jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_594frontier : t4_594root.frontier 0=t4_594jobs := by rfl
theorem t4_594all : t4_594jobs.all (Job.check tree)=true := by
  simp only [t4_594jobs,List.all_append,List.all_nil,t4_594part0,Bool.and_self]
theorem t4_594checked : Checked tree [4,9,10,10] := by
  refine ⟨plan2387,valid2387,t4_594choices,?_⟩
  exact check_of_frontier tree 0 t4_594root t4_594jobs t4_594frontier t4_594all
theorem t4_595choices : plan2388.choices=[4,10,7,7].map (options 4 4) := by rfl


theorem t4_595part0 : t4_595jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_595frontier : t4_595root.frontier 0=t4_595jobs := by rfl
theorem t4_595all : t4_595jobs.all (Job.check tree)=true := by
  simp only [t4_595jobs,List.all_append,List.all_nil,t4_595part0,Bool.and_self]
theorem t4_595checked : Checked tree [4,10,7,7] := by
  refine ⟨plan2388,valid2388,t4_595choices,?_⟩
  exact check_of_frontier tree 0 t4_595root t4_595jobs t4_595frontier t4_595all
theorem t4_596choices : plan2389.choices=[4,10,10,7].map (options 4 4) := by rfl


theorem t4_596part0 : t4_596jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_596frontier : t4_596root.frontier 0=t4_596jobs := by rfl
theorem t4_596all : t4_596jobs.all (Job.check tree)=true := by
  simp only [t4_596jobs,List.all_append,List.all_nil,t4_596part0,Bool.and_self]
theorem t4_596checked : Checked tree [4,10,10,7] := by
  refine ⟨plan2389,valid2389,t4_596choices,?_⟩
  exact check_of_frontier tree 0 t4_596root t4_596jobs t4_596frontier t4_596all
theorem t4_597choices : plan2390.choices=[4,10,10,10].map (options 4 4) := by rfl


theorem t4_597part0 : t4_597jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_597frontier : t4_597root.frontier 0=t4_597jobs := by rfl
theorem t4_597all : t4_597jobs.all (Job.check tree)=true := by
  simp only [t4_597jobs,List.all_append,List.all_nil,t4_597part0,Bool.and_self]
theorem t4_597checked : Checked tree [4,10,10,10] := by
  refine ⟨plan2390,valid2390,t4_597choices,?_⟩
  exact check_of_frontier tree 0 t4_597root t4_597jobs t4_597frontier t4_597all
theorem t4_598choices : plan1798.choices=[5,3,3,3].map (options 4 1) := by rfl


theorem t4_598part0 : t4_598jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_598frontier : t4_598root.frontier 0=t4_598jobs := by rfl
theorem t4_598all : t4_598jobs.all (Job.check tree)=true := by
  simp only [t4_598jobs,List.all_append,List.all_nil,t4_598part0,Bool.and_self]
theorem t4_598checked : Checked tree [5,3,3,3] := by
  refine ⟨plan1798,valid1798,t4_598choices,?_⟩
  exact check_of_frontier tree 0 t4_598root t4_598jobs t4_598frontier t4_598all
theorem t4_599choices : plan1993.choices=[5,3,3,6].map (options 4 2) := by rfl


theorem t4_599part0 : t4_599jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_599frontier : t4_599root.frontier 0=t4_599jobs := by rfl
theorem t4_599all : t4_599jobs.all (Job.check tree)=true := by
  simp only [t4_599jobs,List.all_append,List.all_nil,t4_599part0,Bool.and_self]
theorem t4_599checked : Checked tree [5,3,3,6] := by
  refine ⟨plan1993,valid1993,t4_599choices,?_⟩
  exact check_of_frontier tree 0 t4_599root t4_599jobs t4_599frontier t4_599all
theorem t4_600choices : plan1994.choices=[5,3,3,7].map (options 4 2) := by rfl


theorem t4_600part0 : t4_600jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_600frontier : t4_600root.frontier 0=t4_600jobs := by rfl
theorem t4_600all : t4_600jobs.all (Job.check tree)=true := by
  simp only [t4_600jobs,List.all_append,List.all_nil,t4_600part0,Bool.and_self]
theorem t4_600checked : Checked tree [5,3,3,7] := by
  refine ⟨plan1994,valid1994,t4_600choices,?_⟩
  exact check_of_frontier tree 0 t4_600root t4_600jobs t4_600frontier t4_600all
theorem t4_601choices : plan1995.choices=[5,3,3,10].map (options 4 2) := by rfl


theorem t4_601part0 : t4_601jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_601frontier : t4_601root.frontier 0=t4_601jobs := by rfl
theorem t4_601all : t4_601jobs.all (Job.check tree)=true := by
  simp only [t4_601jobs,List.all_append,List.all_nil,t4_601part0,Bool.and_self]
theorem t4_601checked : Checked tree [5,3,3,10] := by
  refine ⟨plan1995,valid1995,t4_601choices,?_⟩
  exact check_of_frontier tree 0 t4_601root t4_601jobs t4_601frontier t4_601all
theorem t4_602choices : plan2251.choices=[5,3,6,6].map (options 4 3) := by rfl


theorem t4_602part0 : t4_602jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_602frontier : t4_602root.frontier 0=t4_602jobs := by rfl
theorem t4_602all : t4_602jobs.all (Job.check tree)=true := by
  simp only [t4_602jobs,List.all_append,List.all_nil,t4_602part0,Bool.and_self]
theorem t4_602checked : Checked tree [5,3,6,6] := by
  refine ⟨plan2251,valid2251,t4_602choices,?_⟩
  exact check_of_frontier tree 0 t4_602root t4_602jobs t4_602frontier t4_602all
theorem t4_603choices : plan2252.choices=[5,3,6,7].map (options 4 3) := by rfl


theorem t4_603part0 : t4_603jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_603frontier : t4_603root.frontier 0=t4_603jobs := by rfl
theorem t4_603all : t4_603jobs.all (Job.check tree)=true := by
  simp only [t4_603jobs,List.all_append,List.all_nil,t4_603part0,Bool.and_self]
theorem t4_603checked : Checked tree [5,3,6,7] := by
  refine ⟨plan2252,valid2252,t4_603choices,?_⟩
  exact check_of_frontier tree 0 t4_603root t4_603jobs t4_603frontier t4_603all
theorem t4_604choices : plan2253.choices=[5,3,6,10].map (options 4 3) := by rfl


theorem t4_604part0 : t4_604jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_604frontier : t4_604root.frontier 0=t4_604jobs := by rfl
theorem t4_604all : t4_604jobs.all (Job.check tree)=true := by
  simp only [t4_604jobs,List.all_append,List.all_nil,t4_604part0,Bool.and_self]
theorem t4_604checked : Checked tree [5,3,6,10] := by
  refine ⟨plan2253,valid2253,t4_604choices,?_⟩
  exact check_of_frontier tree 0 t4_604root t4_604jobs t4_604frontier t4_604all
theorem t4_605choices : plan2254.choices=[5,3,7,7].map (options 4 3) := by rfl


theorem t4_605part0 : t4_605jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_605frontier : t4_605root.frontier 0=t4_605jobs := by rfl
theorem t4_605all : t4_605jobs.all (Job.check tree)=true := by
  simp only [t4_605jobs,List.all_append,List.all_nil,t4_605part0,Bool.and_self]
theorem t4_605checked : Checked tree [5,3,7,7] := by
  refine ⟨plan2254,valid2254,t4_605choices,?_⟩
  exact check_of_frontier tree 0 t4_605root t4_605jobs t4_605frontier t4_605all
theorem t4_606choices : plan2255.choices=[5,3,10,7].map (options 4 3) := by rfl


theorem t4_606part0 : t4_606jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_606frontier : t4_606root.frontier 0=t4_606jobs := by rfl
theorem t4_606all : t4_606jobs.all (Job.check tree)=true := by
  simp only [t4_606jobs,List.all_append,List.all_nil,t4_606part0,Bool.and_self]
theorem t4_606checked : Checked tree [5,3,10,7] := by
  refine ⟨plan2255,valid2255,t4_606choices,?_⟩
  exact check_of_frontier tree 0 t4_606root t4_606jobs t4_606frontier t4_606all
theorem t4_607choices : plan2256.choices=[5,3,10,10].map (options 4 3) := by rfl


theorem t4_607part0 : t4_607jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_607frontier : t4_607root.frontier 0=t4_607jobs := by rfl
theorem t4_607all : t4_607jobs.all (Job.check tree)=true := by
  simp only [t4_607jobs,List.all_append,List.all_nil,t4_607part0,Bool.and_self]
theorem t4_607checked : Checked tree [5,3,10,10] := by
  refine ⟨plan2256,valid2256,t4_607choices,?_⟩
  exact check_of_frontier tree 0 t4_607root t4_607jobs t4_607frontier t4_607all
theorem t4_608choices : plan1996.choices=[5,5,3,3].map (options 4 2) := by rfl


theorem t4_608part0 : t4_608jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_608frontier : t4_608root.frontier 0=t4_608jobs := by rfl
theorem t4_608all : t4_608jobs.all (Job.check tree)=true := by
  simp only [t4_608jobs,List.all_append,List.all_nil,t4_608part0,Bool.and_self]
theorem t4_608checked : Checked tree [5,5,3,3] := by
  refine ⟨plan1996,valid1996,t4_608choices,?_⟩
  exact check_of_frontier tree 0 t4_608root t4_608jobs t4_608frontier t4_608all
theorem t4_609choices : plan2257.choices=[5,5,3,6].map (options 4 3) := by rfl


theorem t4_609part0 : t4_609jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_609frontier : t4_609root.frontier 0=t4_609jobs := by rfl
theorem t4_609all : t4_609jobs.all (Job.check tree)=true := by
  simp only [t4_609jobs,List.all_append,List.all_nil,t4_609part0,Bool.and_self]
theorem t4_609checked : Checked tree [5,5,3,6] := by
  refine ⟨plan2257,valid2257,t4_609choices,?_⟩
  exact check_of_frontier tree 0 t4_609root t4_609jobs t4_609frontier t4_609all
theorem t4_610choices : plan2258.choices=[5,5,3,7].map (options 4 3) := by rfl


theorem t4_610part0 : t4_610jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_610frontier : t4_610root.frontier 0=t4_610jobs := by rfl
theorem t4_610all : t4_610jobs.all (Job.check tree)=true := by
  simp only [t4_610jobs,List.all_append,List.all_nil,t4_610part0,Bool.and_self]
theorem t4_610checked : Checked tree [5,5,3,7] := by
  refine ⟨plan2258,valid2258,t4_610choices,?_⟩
  exact check_of_frontier tree 0 t4_610root t4_610jobs t4_610frontier t4_610all
theorem t4_611choices : plan2259.choices=[5,5,3,10].map (options 4 3) := by rfl


theorem t4_611part0 : t4_611jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_611frontier : t4_611root.frontier 0=t4_611jobs := by rfl
theorem t4_611all : t4_611jobs.all (Job.check tree)=true := by
  simp only [t4_611jobs,List.all_append,List.all_nil,t4_611part0,Bool.and_self]
theorem t4_611checked : Checked tree [5,5,3,10] := by
  refine ⟨plan2259,valid2259,t4_611choices,?_⟩
  exact check_of_frontier tree 0 t4_611root t4_611jobs t4_611frontier t4_611all
theorem t4_612choices : plan2260.choices=[5,5,5,3].map (options 4 3) := by rfl


theorem t4_612part0 : t4_612jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_612frontier : t4_612root.frontier 0=t4_612jobs := by rfl
theorem t4_612all : t4_612jobs.all (Job.check tree)=true := by
  simp only [t4_612jobs,List.all_append,List.all_nil,t4_612part0,Bool.and_self]
theorem t4_612checked : Checked tree [5,5,5,3] := by
  refine ⟨plan2260,valid2260,t4_612choices,?_⟩
  exact check_of_frontier tree 0 t4_612root t4_612jobs t4_612frontier t4_612all
theorem t4_613choices : plan2391.choices=[5,5,5,5].map (options 4 4) := by rfl


theorem t4_613part0 : t4_613jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_613frontier : t4_613root.frontier 0=t4_613jobs := by rfl
theorem t4_613all : t4_613jobs.all (Job.check tree)=true := by
  simp only [t4_613jobs,List.all_append,List.all_nil,t4_613part0,Bool.and_self]
theorem t4_613checked : Checked tree [5,5,5,5] := by
  refine ⟨plan2391,valid2391,t4_613choices,?_⟩
  exact check_of_frontier tree 0 t4_613root t4_613jobs t4_613frontier t4_613all
theorem t4_614choices : plan2392.choices=[5,5,5,6].map (options 4 4) := by rfl


theorem t4_614part0 : t4_614jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_614frontier : t4_614root.frontier 0=t4_614jobs := by rfl
theorem t4_614all : t4_614jobs.all (Job.check tree)=true := by
  simp only [t4_614jobs,List.all_append,List.all_nil,t4_614part0,Bool.and_self]
theorem t4_614checked : Checked tree [5,5,5,6] := by
  refine ⟨plan2392,valid2392,t4_614choices,?_⟩
  exact check_of_frontier tree 0 t4_614root t4_614jobs t4_614frontier t4_614all
theorem t4_615choices : plan2393.choices=[5,5,5,7].map (options 4 4) := by rfl


theorem t4_615part0 : t4_615jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_615frontier : t4_615root.frontier 0=t4_615jobs := by rfl
theorem t4_615all : t4_615jobs.all (Job.check tree)=true := by
  simp only [t4_615jobs,List.all_append,List.all_nil,t4_615part0,Bool.and_self]
theorem t4_615checked : Checked tree [5,5,5,7] := by
  refine ⟨plan2393,valid2393,t4_615choices,?_⟩
  exact check_of_frontier tree 0 t4_615root t4_615jobs t4_615frontier t4_615all
theorem t4_616choices : plan2394.choices=[5,5,5,9].map (options 4 4) := by rfl


theorem t4_616part0 : t4_616jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_616frontier : t4_616root.frontier 0=t4_616jobs := by rfl
theorem t4_616all : t4_616jobs.all (Job.check tree)=true := by
  simp only [t4_616jobs,List.all_append,List.all_nil,t4_616part0,Bool.and_self]
theorem t4_616checked : Checked tree [5,5,5,9] := by
  refine ⟨plan2394,valid2394,t4_616choices,?_⟩
  exact check_of_frontier tree 0 t4_616root t4_616jobs t4_616frontier t4_616all
theorem t4_617choices : plan2395.choices=[5,5,5,10].map (options 4 4) := by rfl


theorem t4_617part0 : t4_617jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_617frontier : t4_617root.frontier 0=t4_617jobs := by rfl
theorem t4_617all : t4_617jobs.all (Job.check tree)=true := by
  simp only [t4_617jobs,List.all_append,List.all_nil,t4_617part0,Bool.and_self]
theorem t4_617checked : Checked tree [5,5,5,10] := by
  refine ⟨plan2395,valid2395,t4_617choices,?_⟩
  exact check_of_frontier tree 0 t4_617root t4_617jobs t4_617frontier t4_617all
theorem t4_618choices : plan2396.choices=[5,5,6,6].map (options 4 4) := by rfl


theorem t4_618part0 : t4_618jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_618frontier : t4_618root.frontier 0=t4_618jobs := by rfl
theorem t4_618all : t4_618jobs.all (Job.check tree)=true := by
  simp only [t4_618jobs,List.all_append,List.all_nil,t4_618part0,Bool.and_self]
theorem t4_618checked : Checked tree [5,5,6,6] := by
  refine ⟨plan2396,valid2396,t4_618choices,?_⟩
  exact check_of_frontier tree 0 t4_618root t4_618jobs t4_618frontier t4_618all
theorem t4_619choices : plan2397.choices=[5,5,6,7].map (options 4 4) := by rfl


theorem t4_619part0 : t4_619jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_619frontier : t4_619root.frontier 0=t4_619jobs := by rfl
theorem t4_619all : t4_619jobs.all (Job.check tree)=true := by
  simp only [t4_619jobs,List.all_append,List.all_nil,t4_619part0,Bool.and_self]
theorem t4_619checked : Checked tree [5,5,6,7] := by
  refine ⟨plan2397,valid2397,t4_619choices,?_⟩
  exact check_of_frontier tree 0 t4_619root t4_619jobs t4_619frontier t4_619all
theorem t4_620choices : plan2398.choices=[5,5,6,10].map (options 4 4) := by rfl


theorem t4_620part0 : t4_620jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_620frontier : t4_620root.frontier 0=t4_620jobs := by rfl
theorem t4_620all : t4_620jobs.all (Job.check tree)=true := by
  simp only [t4_620jobs,List.all_append,List.all_nil,t4_620part0,Bool.and_self]
theorem t4_620checked : Checked tree [5,5,6,10] := by
  refine ⟨plan2398,valid2398,t4_620choices,?_⟩
  exact check_of_frontier tree 0 t4_620root t4_620jobs t4_620frontier t4_620all
theorem t4_621choices : plan2399.choices=[5,5,7,7].map (options 4 4) := by rfl


theorem t4_621part0 : t4_621jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_621frontier : t4_621root.frontier 0=t4_621jobs := by rfl
theorem t4_621all : t4_621jobs.all (Job.check tree)=true := by
  simp only [t4_621jobs,List.all_append,List.all_nil,t4_621part0,Bool.and_self]
theorem t4_621checked : Checked tree [5,5,7,7] := by
  refine ⟨plan2399,valid2399,t4_621choices,?_⟩
  exact check_of_frontier tree 0 t4_621root t4_621jobs t4_621frontier t4_621all
theorem t4_622choices : plan2261.choices=[5,5,9,3].map (options 4 3) := by rfl


theorem t4_622part0 : t4_622jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_622frontier : t4_622root.frontier 0=t4_622jobs := by rfl
theorem t4_622all : t4_622jobs.all (Job.check tree)=true := by
  simp only [t4_622jobs,List.all_append,List.all_nil,t4_622part0,Bool.and_self]
theorem t4_622checked : Checked tree [5,5,9,3] := by
  refine ⟨plan2261,valid2261,t4_622choices,?_⟩
  exact check_of_frontier tree 0 t4_622root t4_622jobs t4_622frontier t4_622all
theorem t4_623choices : plan2400.choices=[5,5,9,6].map (options 4 4) := by rfl


theorem t4_623part0 : t4_623jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_623frontier : t4_623root.frontier 0=t4_623jobs := by rfl
theorem t4_623all : t4_623jobs.all (Job.check tree)=true := by
  simp only [t4_623jobs,List.all_append,List.all_nil,t4_623part0,Bool.and_self]
theorem t4_623checked : Checked tree [5,5,9,6] := by
  refine ⟨plan2400,valid2400,t4_623choices,?_⟩
  exact check_of_frontier tree 0 t4_623root t4_623jobs t4_623frontier t4_623all
theorem t4_624choices : plan2401.choices=[5,5,9,7].map (options 4 4) := by rfl


theorem t4_624part0 : t4_624jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_624frontier : t4_624root.frontier 0=t4_624jobs := by rfl
theorem t4_624all : t4_624jobs.all (Job.check tree)=true := by
  simp only [t4_624jobs,List.all_append,List.all_nil,t4_624part0,Bool.and_self]
theorem t4_624checked : Checked tree [5,5,9,7] := by
  refine ⟨plan2401,valid2401,t4_624choices,?_⟩
  exact check_of_frontier tree 0 t4_624root t4_624jobs t4_624frontier t4_624all
theorem t4_625choices : plan2402.choices=[5,5,9,9].map (options 4 4) := by rfl


theorem t4_625part0 : t4_625jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_625frontier : t4_625root.frontier 0=t4_625jobs := by rfl
theorem t4_625all : t4_625jobs.all (Job.check tree)=true := by
  simp only [t4_625jobs,List.all_append,List.all_nil,t4_625part0,Bool.and_self]
theorem t4_625checked : Checked tree [5,5,9,9] := by
  refine ⟨plan2402,valid2402,t4_625choices,?_⟩
  exact check_of_frontier tree 0 t4_625root t4_625jobs t4_625frontier t4_625all
theorem t4_626choices : plan2403.choices=[5,5,9,10].map (options 4 4) := by rfl


theorem t4_626part0 : t4_626jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_626frontier : t4_626root.frontier 0=t4_626jobs := by rfl
theorem t4_626all : t4_626jobs.all (Job.check tree)=true := by
  simp only [t4_626jobs,List.all_append,List.all_nil,t4_626part0,Bool.and_self]
theorem t4_626checked : Checked tree [5,5,9,10] := by
  refine ⟨plan2403,valid2403,t4_626choices,?_⟩
  exact check_of_frontier tree 0 t4_626root t4_626jobs t4_626frontier t4_626all
theorem t4_627choices : plan2404.choices=[5,5,10,7].map (options 4 4) := by rfl


theorem t4_627part0 : t4_627jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_627frontier : t4_627root.frontier 0=t4_627jobs := by rfl
theorem t4_627all : t4_627jobs.all (Job.check tree)=true := by
  simp only [t4_627jobs,List.all_append,List.all_nil,t4_627part0,Bool.and_self]
theorem t4_627checked : Checked tree [5,5,10,7] := by
  refine ⟨plan2404,valid2404,t4_627choices,?_⟩
  exact check_of_frontier tree 0 t4_627root t4_627jobs t4_627frontier t4_627all
theorem t4_628choices : plan2405.choices=[5,5,10,10].map (options 4 4) := by rfl


theorem t4_628part0 : t4_628jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_628frontier : t4_628root.frontier 0=t4_628jobs := by rfl
theorem t4_628all : t4_628jobs.all (Job.check tree)=true := by
  simp only [t4_628jobs,List.all_append,List.all_nil,t4_628part0,Bool.and_self]
theorem t4_628checked : Checked tree [5,5,10,10] := by
  refine ⟨plan2405,valid2405,t4_628choices,?_⟩
  exact check_of_frontier tree 0 t4_628root t4_628jobs t4_628frontier t4_628all
theorem t4_629choices : plan2406.choices=[5,6,6,6].map (options 4 4) := by rfl


theorem t4_629part0 : t4_629jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_629frontier : t4_629root.frontier 0=t4_629jobs := by rfl
theorem t4_629all : t4_629jobs.all (Job.check tree)=true := by
  simp only [t4_629jobs,List.all_append,List.all_nil,t4_629part0,Bool.and_self]
theorem t4_629checked : Checked tree [5,6,6,6] := by
  refine ⟨plan2406,valid2406,t4_629choices,?_⟩
  exact check_of_frontier tree 0 t4_629root t4_629jobs t4_629frontier t4_629all
theorem t4_630choices : plan2407.choices=[5,6,6,7].map (options 4 4) := by rfl


theorem t4_630part0 : t4_630jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_630frontier : t4_630root.frontier 0=t4_630jobs := by rfl
theorem t4_630all : t4_630jobs.all (Job.check tree)=true := by
  simp only [t4_630jobs,List.all_append,List.all_nil,t4_630part0,Bool.and_self]
theorem t4_630checked : Checked tree [5,6,6,7] := by
  refine ⟨plan2407,valid2407,t4_630choices,?_⟩
  exact check_of_frontier tree 0 t4_630root t4_630jobs t4_630frontier t4_630all
theorem t4_631choices : plan2408.choices=[5,6,6,10].map (options 4 4) := by rfl


theorem t4_631part0 : t4_631jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_631frontier : t4_631root.frontier 0=t4_631jobs := by rfl
theorem t4_631all : t4_631jobs.all (Job.check tree)=true := by
  simp only [t4_631jobs,List.all_append,List.all_nil,t4_631part0,Bool.and_self]
theorem t4_631checked : Checked tree [5,6,6,10] := by
  refine ⟨plan2408,valid2408,t4_631choices,?_⟩
  exact check_of_frontier tree 0 t4_631root t4_631jobs t4_631frontier t4_631all
theorem t4_632choices : plan2409.choices=[5,6,7,7].map (options 4 4) := by rfl


theorem t4_632part0 : t4_632jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_632frontier : t4_632root.frontier 0=t4_632jobs := by rfl
theorem t4_632all : t4_632jobs.all (Job.check tree)=true := by
  simp only [t4_632jobs,List.all_append,List.all_nil,t4_632part0,Bool.and_self]
theorem t4_632checked : Checked tree [5,6,7,7] := by
  refine ⟨plan2409,valid2409,t4_632choices,?_⟩
  exact check_of_frontier tree 0 t4_632root t4_632jobs t4_632frontier t4_632all
theorem t4_633choices : plan2410.choices=[5,6,10,7].map (options 4 4) := by rfl


theorem t4_633part0 : t4_633jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_633frontier : t4_633root.frontier 0=t4_633jobs := by rfl
theorem t4_633all : t4_633jobs.all (Job.check tree)=true := by
  simp only [t4_633jobs,List.all_append,List.all_nil,t4_633part0,Bool.and_self]
theorem t4_633checked : Checked tree [5,6,10,7] := by
  refine ⟨plan2410,valid2410,t4_633choices,?_⟩
  exact check_of_frontier tree 0 t4_633root t4_633jobs t4_633frontier t4_633all
theorem t4_634choices : plan2411.choices=[5,6,10,10].map (options 4 4) := by rfl


theorem t4_634part0 : t4_634jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_634frontier : t4_634root.frontier 0=t4_634jobs := by rfl
theorem t4_634all : t4_634jobs.all (Job.check tree)=true := by
  simp only [t4_634jobs,List.all_append,List.all_nil,t4_634part0,Bool.and_self]
theorem t4_634checked : Checked tree [5,6,10,10] := by
  refine ⟨plan2411,valid2411,t4_634choices,?_⟩
  exact check_of_frontier tree 0 t4_634root t4_634jobs t4_634frontier t4_634all
theorem t4_635choices : plan2412.choices=[5,7,7,7].map (options 4 4) := by rfl


theorem t4_635part0 : t4_635jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_635frontier : t4_635root.frontier 0=t4_635jobs := by rfl
theorem t4_635all : t4_635jobs.all (Job.check tree)=true := by
  simp only [t4_635jobs,List.all_append,List.all_nil,t4_635part0,Bool.and_self]
theorem t4_635checked : Checked tree [5,7,7,7] := by
  refine ⟨plan2412,valid2412,t4_635choices,?_⟩
  exact check_of_frontier tree 0 t4_635root t4_635jobs t4_635frontier t4_635all
theorem t4_636choices : plan1997.choices=[5,9,3,3].map (options 4 2) := by rfl


theorem t4_636part0 : t4_636jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_636frontier : t4_636root.frontier 0=t4_636jobs := by rfl
theorem t4_636all : t4_636jobs.all (Job.check tree)=true := by
  simp only [t4_636jobs,List.all_append,List.all_nil,t4_636part0,Bool.and_self]
theorem t4_636checked : Checked tree [5,9,3,3] := by
  refine ⟨plan1997,valid1997,t4_636choices,?_⟩
  exact check_of_frontier tree 0 t4_636root t4_636jobs t4_636frontier t4_636all
theorem t4_637choices : plan2262.choices=[5,9,3,6].map (options 4 3) := by rfl


theorem t4_637part0 : t4_637jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_637frontier : t4_637root.frontier 0=t4_637jobs := by rfl
theorem t4_637all : t4_637jobs.all (Job.check tree)=true := by
  simp only [t4_637jobs,List.all_append,List.all_nil,t4_637part0,Bool.and_self]
theorem t4_637checked : Checked tree [5,9,3,6] := by
  refine ⟨plan2262,valid2262,t4_637choices,?_⟩
  exact check_of_frontier tree 0 t4_637root t4_637jobs t4_637frontier t4_637all
theorem t4_638choices : plan2263.choices=[5,9,3,7].map (options 4 3) := by rfl


theorem t4_638part0 : t4_638jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_638frontier : t4_638root.frontier 0=t4_638jobs := by rfl
theorem t4_638all : t4_638jobs.all (Job.check tree)=true := by
  simp only [t4_638jobs,List.all_append,List.all_nil,t4_638part0,Bool.and_self]
theorem t4_638checked : Checked tree [5,9,3,7] := by
  refine ⟨plan2263,valid2263,t4_638choices,?_⟩
  exact check_of_frontier tree 0 t4_638root t4_638jobs t4_638frontier t4_638all
theorem t4_639choices : plan2264.choices=[5,9,3,10].map (options 4 3) := by rfl


theorem t4_639part0 : t4_639jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_639frontier : t4_639root.frontier 0=t4_639jobs := by rfl
theorem t4_639all : t4_639jobs.all (Job.check tree)=true := by
  simp only [t4_639jobs,List.all_append,List.all_nil,t4_639part0,Bool.and_self]
theorem t4_639checked : Checked tree [5,9,3,10] := by
  refine ⟨plan2264,valid2264,t4_639choices,?_⟩
  exact check_of_frontier tree 0 t4_639root t4_639jobs t4_639frontier t4_639all
theorem t4_640choices : plan2413.choices=[5,9,6,6].map (options 4 4) := by rfl


theorem t4_640part0 : t4_640jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_640frontier : t4_640root.frontier 0=t4_640jobs := by rfl
theorem t4_640all : t4_640jobs.all (Job.check tree)=true := by
  simp only [t4_640jobs,List.all_append,List.all_nil,t4_640part0,Bool.and_self]
theorem t4_640checked : Checked tree [5,9,6,6] := by
  refine ⟨plan2413,valid2413,t4_640choices,?_⟩
  exact check_of_frontier tree 0 t4_640root t4_640jobs t4_640frontier t4_640all
theorem t4_641choices : plan2414.choices=[5,9,6,7].map (options 4 4) := by rfl


theorem t4_641part0 : t4_641jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_641frontier : t4_641root.frontier 0=t4_641jobs := by rfl
theorem t4_641all : t4_641jobs.all (Job.check tree)=true := by
  simp only [t4_641jobs,List.all_append,List.all_nil,t4_641part0,Bool.and_self]
theorem t4_641checked : Checked tree [5,9,6,7] := by
  refine ⟨plan2414,valid2414,t4_641choices,?_⟩
  exact check_of_frontier tree 0 t4_641root t4_641jobs t4_641frontier t4_641all
theorem t4_642choices : plan2415.choices=[5,9,6,10].map (options 4 4) := by rfl


theorem t4_642part0 : t4_642jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_642frontier : t4_642root.frontier 0=t4_642jobs := by rfl
theorem t4_642all : t4_642jobs.all (Job.check tree)=true := by
  simp only [t4_642jobs,List.all_append,List.all_nil,t4_642part0,Bool.and_self]
theorem t4_642checked : Checked tree [5,9,6,10] := by
  refine ⟨plan2415,valid2415,t4_642choices,?_⟩
  exact check_of_frontier tree 0 t4_642root t4_642jobs t4_642frontier t4_642all
theorem t4_643choices : plan2416.choices=[5,9,7,7].map (options 4 4) := by rfl


theorem t4_643part0 : t4_643jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_643frontier : t4_643root.frontier 0=t4_643jobs := by rfl
theorem t4_643all : t4_643jobs.all (Job.check tree)=true := by
  simp only [t4_643jobs,List.all_append,List.all_nil,t4_643part0,Bool.and_self]
theorem t4_643checked : Checked tree [5,9,7,7] := by
  refine ⟨plan2416,valid2416,t4_643choices,?_⟩
  exact check_of_frontier tree 0 t4_643root t4_643jobs t4_643frontier t4_643all
theorem t4_644choices : plan2265.choices=[5,9,9,3].map (options 4 3) := by rfl


theorem t4_644part0 : t4_644jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_644frontier : t4_644root.frontier 0=t4_644jobs := by rfl
theorem t4_644all : t4_644jobs.all (Job.check tree)=true := by
  simp only [t4_644jobs,List.all_append,List.all_nil,t4_644part0,Bool.and_self]
theorem t4_644checked : Checked tree [5,9,9,3] := by
  refine ⟨plan2265,valid2265,t4_644choices,?_⟩
  exact check_of_frontier tree 0 t4_644root t4_644jobs t4_644frontier t4_644all
theorem t4_645choices : plan2417.choices=[5,9,9,6].map (options 4 4) := by rfl


theorem t4_645part0 : t4_645jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_645frontier : t4_645root.frontier 0=t4_645jobs := by rfl
theorem t4_645all : t4_645jobs.all (Job.check tree)=true := by
  simp only [t4_645jobs,List.all_append,List.all_nil,t4_645part0,Bool.and_self]
theorem t4_645checked : Checked tree [5,9,9,6] := by
  refine ⟨plan2417,valid2417,t4_645choices,?_⟩
  exact check_of_frontier tree 0 t4_645root t4_645jobs t4_645frontier t4_645all
theorem t4_646choices : plan2418.choices=[5,9,9,7].map (options 4 4) := by rfl


theorem t4_646part0 : t4_646jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_646frontier : t4_646root.frontier 0=t4_646jobs := by rfl
theorem t4_646all : t4_646jobs.all (Job.check tree)=true := by
  simp only [t4_646jobs,List.all_append,List.all_nil,t4_646part0,Bool.and_self]
theorem t4_646checked : Checked tree [5,9,9,7] := by
  refine ⟨plan2418,valid2418,t4_646choices,?_⟩
  exact check_of_frontier tree 0 t4_646root t4_646jobs t4_646frontier t4_646all
theorem t4_647choices : plan2419.choices=[5,9,9,9].map (options 4 4) := by rfl


theorem t4_647part0 : t4_647jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_647frontier : t4_647root.frontier 0=t4_647jobs := by rfl
theorem t4_647all : t4_647jobs.all (Job.check tree)=true := by
  simp only [t4_647jobs,List.all_append,List.all_nil,t4_647part0,Bool.and_self]
theorem t4_647checked : Checked tree [5,9,9,9] := by
  refine ⟨plan2419,valid2419,t4_647choices,?_⟩
  exact check_of_frontier tree 0 t4_647root t4_647jobs t4_647frontier t4_647all
theorem t4_648choices : plan2420.choices=[5,9,9,10].map (options 4 4) := by rfl


theorem t4_648part0 : t4_648jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_648frontier : t4_648root.frontier 0=t4_648jobs := by rfl
theorem t4_648all : t4_648jobs.all (Job.check tree)=true := by
  simp only [t4_648jobs,List.all_append,List.all_nil,t4_648part0,Bool.and_self]
theorem t4_648checked : Checked tree [5,9,9,10] := by
  refine ⟨plan2420,valid2420,t4_648choices,?_⟩
  exact check_of_frontier tree 0 t4_648root t4_648jobs t4_648frontier t4_648all
theorem t4_649choices : plan2421.choices=[5,9,10,7].map (options 4 4) := by rfl


theorem t4_649part0 : t4_649jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_649frontier : t4_649root.frontier 0=t4_649jobs := by rfl
theorem t4_649all : t4_649jobs.all (Job.check tree)=true := by
  simp only [t4_649jobs,List.all_append,List.all_nil,t4_649part0,Bool.and_self]
theorem t4_649checked : Checked tree [5,9,10,7] := by
  refine ⟨plan2421,valid2421,t4_649choices,?_⟩
  exact check_of_frontier tree 0 t4_649root t4_649jobs t4_649frontier t4_649all
theorem t4_650choices : plan2422.choices=[5,9,10,10].map (options 4 4) := by rfl


theorem t4_650part0 : t4_650jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_650frontier : t4_650root.frontier 0=t4_650jobs := by rfl
theorem t4_650all : t4_650jobs.all (Job.check tree)=true := by
  simp only [t4_650jobs,List.all_append,List.all_nil,t4_650part0,Bool.and_self]
theorem t4_650checked : Checked tree [5,9,10,10] := by
  refine ⟨plan2422,valid2422,t4_650choices,?_⟩
  exact check_of_frontier tree 0 t4_650root t4_650jobs t4_650frontier t4_650all
theorem t4_651choices : plan2423.choices=[5,10,7,7].map (options 4 4) := by rfl


theorem t4_651part0 : t4_651jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_651frontier : t4_651root.frontier 0=t4_651jobs := by rfl
theorem t4_651all : t4_651jobs.all (Job.check tree)=true := by
  simp only [t4_651jobs,List.all_append,List.all_nil,t4_651part0,Bool.and_self]
theorem t4_651checked : Checked tree [5,10,7,7] := by
  refine ⟨plan2423,valid2423,t4_651choices,?_⟩
  exact check_of_frontier tree 0 t4_651root t4_651jobs t4_651frontier t4_651all
theorem t4_652choices : plan2424.choices=[5,10,10,7].map (options 4 4) := by rfl


theorem t4_652part0 : t4_652jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_652frontier : t4_652root.frontier 0=t4_652jobs := by rfl
theorem t4_652all : t4_652jobs.all (Job.check tree)=true := by
  simp only [t4_652jobs,List.all_append,List.all_nil,t4_652part0,Bool.and_self]
theorem t4_652checked : Checked tree [5,10,10,7] := by
  refine ⟨plan2424,valid2424,t4_652choices,?_⟩
  exact check_of_frontier tree 0 t4_652root t4_652jobs t4_652frontier t4_652all
theorem t4_653choices : plan2425.choices=[5,10,10,10].map (options 4 4) := by rfl


theorem t4_653part0 : t4_653jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_653frontier : t4_653root.frontier 0=t4_653jobs := by rfl
theorem t4_653all : t4_653jobs.all (Job.check tree)=true := by
  simp only [t4_653jobs,List.all_append,List.all_nil,t4_653part0,Bool.and_self]
theorem t4_653checked : Checked tree [5,10,10,10] := by
  refine ⟨plan2425,valid2425,t4_653choices,?_⟩
  exact check_of_frontier tree 0 t4_653root t4_653jobs t4_653frontier t4_653all
theorem t4_654choices : plan2426.choices=[6,6,6,6].map (options 4 4) := by rfl


theorem t4_654part0 : t4_654jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_654frontier : t4_654root.frontier 0=t4_654jobs := by rfl
theorem t4_654all : t4_654jobs.all (Job.check tree)=true := by
  simp only [t4_654jobs,List.all_append,List.all_nil,t4_654part0,Bool.and_self]
theorem t4_654checked : Checked tree [6,6,6,6] := by
  refine ⟨plan2426,valid2426,t4_654choices,?_⟩
  exact check_of_frontier tree 0 t4_654root t4_654jobs t4_654frontier t4_654all
theorem t4_655choices : plan2427.choices=[6,6,6,7].map (options 4 4) := by rfl


theorem t4_655part0 : t4_655jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_655frontier : t4_655root.frontier 0=t4_655jobs := by rfl
theorem t4_655all : t4_655jobs.all (Job.check tree)=true := by
  simp only [t4_655jobs,List.all_append,List.all_nil,t4_655part0,Bool.and_self]
theorem t4_655checked : Checked tree [6,6,6,7] := by
  refine ⟨plan2427,valid2427,t4_655choices,?_⟩
  exact check_of_frontier tree 0 t4_655root t4_655jobs t4_655frontier t4_655all
theorem t4_656choices : plan2428.choices=[6,6,6,10].map (options 4 4) := by rfl


theorem t4_656part0 : t4_656jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_656frontier : t4_656root.frontier 0=t4_656jobs := by rfl
theorem t4_656all : t4_656jobs.all (Job.check tree)=true := by
  simp only [t4_656jobs,List.all_append,List.all_nil,t4_656part0,Bool.and_self]
theorem t4_656checked : Checked tree [6,6,6,10] := by
  refine ⟨plan2428,valid2428,t4_656choices,?_⟩
  exact check_of_frontier tree 0 t4_656root t4_656jobs t4_656frontier t4_656all
theorem t4_657choices : plan2429.choices=[6,6,7,7].map (options 4 4) := by rfl


theorem t4_657part0 : t4_657jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_657frontier : t4_657root.frontier 0=t4_657jobs := by rfl
theorem t4_657all : t4_657jobs.all (Job.check tree)=true := by
  simp only [t4_657jobs,List.all_append,List.all_nil,t4_657part0,Bool.and_self]
theorem t4_657checked : Checked tree [6,6,7,7] := by
  refine ⟨plan2429,valid2429,t4_657choices,?_⟩
  exact check_of_frontier tree 0 t4_657root t4_657jobs t4_657frontier t4_657all
theorem t4_658choices : plan2430.choices=[6,6,10,7].map (options 4 4) := by rfl


theorem t4_658part0 : t4_658jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_658frontier : t4_658root.frontier 0=t4_658jobs := by rfl
theorem t4_658all : t4_658jobs.all (Job.check tree)=true := by
  simp only [t4_658jobs,List.all_append,List.all_nil,t4_658part0,Bool.and_self]
theorem t4_658checked : Checked tree [6,6,10,7] := by
  refine ⟨plan2430,valid2430,t4_658choices,?_⟩
  exact check_of_frontier tree 0 t4_658root t4_658jobs t4_658frontier t4_658all
theorem t4_659choices : plan2431.choices=[6,6,10,10].map (options 4 4) := by rfl


theorem t4_659part0 : t4_659jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_659frontier : t4_659root.frontier 0=t4_659jobs := by rfl
theorem t4_659all : t4_659jobs.all (Job.check tree)=true := by
  simp only [t4_659jobs,List.all_append,List.all_nil,t4_659part0,Bool.and_self]
theorem t4_659checked : Checked tree [6,6,10,10] := by
  refine ⟨plan2431,valid2431,t4_659choices,?_⟩
  exact check_of_frontier tree 0 t4_659root t4_659jobs t4_659frontier t4_659all
theorem t4_660choices : plan2432.choices=[6,7,7,7].map (options 4 4) := by rfl


theorem t4_660part0 : t4_660jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_660frontier : t4_660root.frontier 0=t4_660jobs := by rfl
theorem t4_660all : t4_660jobs.all (Job.check tree)=true := by
  simp only [t4_660jobs,List.all_append,List.all_nil,t4_660part0,Bool.and_self]
theorem t4_660checked : Checked tree [6,7,7,7] := by
  refine ⟨plan2432,valid2432,t4_660choices,?_⟩
  exact check_of_frontier tree 0 t4_660root t4_660jobs t4_660frontier t4_660all
theorem t4_661choices : plan2433.choices=[6,10,7,7].map (options 4 4) := by rfl


theorem t4_661part0 : t4_661jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_661frontier : t4_661root.frontier 0=t4_661jobs := by rfl
theorem t4_661all : t4_661jobs.all (Job.check tree)=true := by
  simp only [t4_661jobs,List.all_append,List.all_nil,t4_661part0,Bool.and_self]
theorem t4_661checked : Checked tree [6,10,7,7] := by
  refine ⟨plan2433,valid2433,t4_661choices,?_⟩
  exact check_of_frontier tree 0 t4_661root t4_661jobs t4_661frontier t4_661all
theorem t4_662choices : plan2434.choices=[6,10,10,7].map (options 4 4) := by rfl


theorem t4_662part0 : t4_662jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_662frontier : t4_662root.frontier 0=t4_662jobs := by rfl
theorem t4_662all : t4_662jobs.all (Job.check tree)=true := by
  simp only [t4_662jobs,List.all_append,List.all_nil,t4_662part0,Bool.and_self]
theorem t4_662checked : Checked tree [6,10,10,7] := by
  refine ⟨plan2434,valid2434,t4_662choices,?_⟩
  exact check_of_frontier tree 0 t4_662root t4_662jobs t4_662frontier t4_662all
theorem t4_663choices : plan2435.choices=[6,10,10,10].map (options 4 4) := by rfl


theorem t4_663part0 : t4_663jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_663frontier : t4_663root.frontier 0=t4_663jobs := by rfl
theorem t4_663all : t4_663jobs.all (Job.check tree)=true := by
  simp only [t4_663jobs,List.all_append,List.all_nil,t4_663part0,Bool.and_self]
theorem t4_663checked : Checked tree [6,10,10,10] := by
  refine ⟨plan2435,valid2435,t4_663choices,?_⟩
  exact check_of_frontier tree 0 t4_663root t4_663jobs t4_663frontier t4_663all
theorem t4_664choices : plan2436.choices=[7,7,7,7].map (options 4 4) := by rfl


theorem t4_664part0 : t4_664jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_664frontier : t4_664root.frontier 0=t4_664jobs := by rfl
theorem t4_664all : t4_664jobs.all (Job.check tree)=true := by
  simp only [t4_664jobs,List.all_append,List.all_nil,t4_664part0,Bool.and_self]
theorem t4_664checked : Checked tree [7,7,7,7] := by
  refine ⟨plan2436,valid2436,t4_664choices,?_⟩
  exact check_of_frontier tree 0 t4_664root t4_664jobs t4_664frontier t4_664all
theorem t4_665choices : plan1799.choices=[8,2,2,2].map (options 4 1) := by rfl


theorem t4_665part0 : t4_665jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_665frontier : t4_665root.frontier 0=t4_665jobs := by rfl
theorem t4_665all : t4_665jobs.all (Job.check tree)=true := by
  simp only [t4_665jobs,List.all_append,List.all_nil,t4_665part0,Bool.and_self]
theorem t4_665checked : Checked tree [8,2,2,2] := by
  refine ⟨plan1799,valid1799,t4_665choices,?_⟩
  exact check_of_frontier tree 0 t4_665root t4_665jobs t4_665frontier t4_665all
theorem t4_666choices : plan1800.choices=[8,2,2,3].map (options 4 1) := by rfl


theorem t4_666part0 : t4_666jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_666frontier : t4_666root.frontier 0=t4_666jobs := by rfl
theorem t4_666all : t4_666jobs.all (Job.check tree)=true := by
  simp only [t4_666jobs,List.all_append,List.all_nil,t4_666part0,Bool.and_self]
theorem t4_666checked : Checked tree [8,2,2,3] := by
  refine ⟨plan1800,valid1800,t4_666choices,?_⟩
  exact check_of_frontier tree 0 t4_666root t4_666jobs t4_666frontier t4_666all
theorem t4_667choices : plan1998.choices=[8,2,2,5].map (options 4 2) := by rfl


theorem t4_667part0 : t4_667jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_667frontier : t4_667root.frontier 0=t4_667jobs := by rfl
theorem t4_667all : t4_667jobs.all (Job.check tree)=true := by
  simp only [t4_667jobs,List.all_append,List.all_nil,t4_667part0,Bool.and_self]
theorem t4_667checked : Checked tree [8,2,2,5] := by
  refine ⟨plan1998,valid1998,t4_667choices,?_⟩
  exact check_of_frontier tree 0 t4_667root t4_667jobs t4_667frontier t4_667all
theorem t4_668choices : plan1999.choices=[8,2,2,6].map (options 4 2) := by rfl


theorem t4_668part0 : t4_668jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_668frontier : t4_668root.frontier 0=t4_668jobs := by rfl
theorem t4_668all : t4_668jobs.all (Job.check tree)=true := by
  simp only [t4_668jobs,List.all_append,List.all_nil,t4_668part0,Bool.and_self]
theorem t4_668checked : Checked tree [8,2,2,6] := by
  refine ⟨plan1999,valid1999,t4_668choices,?_⟩
  exact check_of_frontier tree 0 t4_668root t4_668jobs t4_668frontier t4_668all
theorem t4_669choices : plan2000.choices=[8,2,2,7].map (options 4 2) := by rfl


theorem t4_669part0 : t4_669jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_669frontier : t4_669root.frontier 0=t4_669jobs := by rfl
theorem t4_669all : t4_669jobs.all (Job.check tree)=true := by
  simp only [t4_669jobs,List.all_append,List.all_nil,t4_669part0,Bool.and_self]
theorem t4_669checked : Checked tree [8,2,2,7] := by
  refine ⟨plan2000,valid2000,t4_669choices,?_⟩
  exact check_of_frontier tree 0 t4_669root t4_669jobs t4_669frontier t4_669all
theorem t4_670choices : plan2001.choices=[8,2,2,9].map (options 4 2) := by rfl


theorem t4_670part0 : t4_670jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_670frontier : t4_670root.frontier 0=t4_670jobs := by rfl
theorem t4_670all : t4_670jobs.all (Job.check tree)=true := by
  simp only [t4_670jobs,List.all_append,List.all_nil,t4_670part0,Bool.and_self]
theorem t4_670checked : Checked tree [8,2,2,9] := by
  refine ⟨plan2001,valid2001,t4_670choices,?_⟩
  exact check_of_frontier tree 0 t4_670root t4_670jobs t4_670frontier t4_670all
theorem t4_671choices : plan2002.choices=[8,2,2,10].map (options 4 2) := by rfl


theorem t4_671part0 : t4_671jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_671frontier : t4_671root.frontier 0=t4_671jobs := by rfl
theorem t4_671all : t4_671jobs.all (Job.check tree)=true := by
  simp only [t4_671jobs,List.all_append,List.all_nil,t4_671part0,Bool.and_self]
theorem t4_671checked : Checked tree [8,2,2,10] := by
  refine ⟨plan2002,valid2002,t4_671choices,?_⟩
  exact check_of_frontier tree 0 t4_671root t4_671jobs t4_671frontier t4_671all
theorem t4_672choices : plan1801.choices=[8,2,3,3].map (options 4 1) := by rfl


theorem t4_672part0 : t4_672jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_672frontier : t4_672root.frontier 0=t4_672jobs := by rfl
theorem t4_672all : t4_672jobs.all (Job.check tree)=true := by
  simp only [t4_672jobs,List.all_append,List.all_nil,t4_672part0,Bool.and_self]
theorem t4_672checked : Checked tree [8,2,3,3] := by
  refine ⟨plan1801,valid1801,t4_672choices,?_⟩
  exact check_of_frontier tree 0 t4_672root t4_672jobs t4_672frontier t4_672all
theorem t4_673choices : plan2003.choices=[8,2,3,6].map (options 4 2) := by rfl


theorem t4_673part0 : t4_673jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_673frontier : t4_673root.frontier 0=t4_673jobs := by rfl
theorem t4_673all : t4_673jobs.all (Job.check tree)=true := by
  simp only [t4_673jobs,List.all_append,List.all_nil,t4_673part0,Bool.and_self]
theorem t4_673checked : Checked tree [8,2,3,6] := by
  refine ⟨plan2003,valid2003,t4_673choices,?_⟩
  exact check_of_frontier tree 0 t4_673root t4_673jobs t4_673frontier t4_673all
theorem t4_674choices : plan2004.choices=[8,2,3,7].map (options 4 2) := by rfl


theorem t4_674part0 : t4_674jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_674frontier : t4_674root.frontier 0=t4_674jobs := by rfl
theorem t4_674all : t4_674jobs.all (Job.check tree)=true := by
  simp only [t4_674jobs,List.all_append,List.all_nil,t4_674part0,Bool.and_self]
theorem t4_674checked : Checked tree [8,2,3,7] := by
  refine ⟨plan2004,valid2004,t4_674choices,?_⟩
  exact check_of_frontier tree 0 t4_674root t4_674jobs t4_674frontier t4_674all
theorem t4_675choices : plan2005.choices=[8,2,3,10].map (options 4 2) := by rfl


theorem t4_675part0 : t4_675jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_675frontier : t4_675root.frontier 0=t4_675jobs := by rfl
theorem t4_675all : t4_675jobs.all (Job.check tree)=true := by
  simp only [t4_675jobs,List.all_append,List.all_nil,t4_675part0,Bool.and_self]
theorem t4_675checked : Checked tree [8,2,3,10] := by
  refine ⟨plan2005,valid2005,t4_675choices,?_⟩
  exact check_of_frontier tree 0 t4_675root t4_675jobs t4_675frontier t4_675all
theorem t4_676choices : plan2006.choices=[8,2,5,3].map (options 4 2) := by rfl


theorem t4_676part0 : t4_676jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_676frontier : t4_676root.frontier 0=t4_676jobs := by rfl
theorem t4_676all : t4_676jobs.all (Job.check tree)=true := by
  simp only [t4_676jobs,List.all_append,List.all_nil,t4_676part0,Bool.and_self]
theorem t4_676checked : Checked tree [8,2,5,3] := by
  refine ⟨plan2006,valid2006,t4_676choices,?_⟩
  exact check_of_frontier tree 0 t4_676root t4_676jobs t4_676frontier t4_676all
theorem t4_677choices : plan2266.choices=[8,2,5,5].map (options 4 3) := by rfl


theorem t4_677part0 : t4_677jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_677frontier : t4_677root.frontier 0=t4_677jobs := by rfl
theorem t4_677all : t4_677jobs.all (Job.check tree)=true := by
  simp only [t4_677jobs,List.all_append,List.all_nil,t4_677part0,Bool.and_self]
theorem t4_677checked : Checked tree [8,2,5,5] := by
  refine ⟨plan2266,valid2266,t4_677choices,?_⟩
  exact check_of_frontier tree 0 t4_677root t4_677jobs t4_677frontier t4_677all
theorem t4_678choices : plan2267.choices=[8,2,5,6].map (options 4 3) := by rfl


theorem t4_678part0 : t4_678jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_678frontier : t4_678root.frontier 0=t4_678jobs := by rfl
theorem t4_678all : t4_678jobs.all (Job.check tree)=true := by
  simp only [t4_678jobs,List.all_append,List.all_nil,t4_678part0,Bool.and_self]
theorem t4_678checked : Checked tree [8,2,5,6] := by
  refine ⟨plan2267,valid2267,t4_678choices,?_⟩
  exact check_of_frontier tree 0 t4_678root t4_678jobs t4_678frontier t4_678all
theorem t4_679choices : plan2268.choices=[8,2,5,7].map (options 4 3) := by rfl


theorem t4_679part0 : t4_679jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_679frontier : t4_679root.frontier 0=t4_679jobs := by rfl
theorem t4_679all : t4_679jobs.all (Job.check tree)=true := by
  simp only [t4_679jobs,List.all_append,List.all_nil,t4_679part0,Bool.and_self]
theorem t4_679checked : Checked tree [8,2,5,7] := by
  refine ⟨plan2268,valid2268,t4_679choices,?_⟩
  exact check_of_frontier tree 0 t4_679root t4_679jobs t4_679frontier t4_679all
theorem t4_680choices : plan2269.choices=[8,2,5,9].map (options 4 3) := by rfl


theorem t4_680part0 : t4_680jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_680frontier : t4_680root.frontier 0=t4_680jobs := by rfl
theorem t4_680all : t4_680jobs.all (Job.check tree)=true := by
  simp only [t4_680jobs,List.all_append,List.all_nil,t4_680part0,Bool.and_self]
theorem t4_680checked : Checked tree [8,2,5,9] := by
  refine ⟨plan2269,valid2269,t4_680choices,?_⟩
  exact check_of_frontier tree 0 t4_680root t4_680jobs t4_680frontier t4_680all
theorem t4_681choices : plan2270.choices=[8,2,5,10].map (options 4 3) := by rfl


theorem t4_681part0 : t4_681jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_681frontier : t4_681root.frontier 0=t4_681jobs := by rfl
theorem t4_681all : t4_681jobs.all (Job.check tree)=true := by
  simp only [t4_681jobs,List.all_append,List.all_nil,t4_681part0,Bool.and_self]
theorem t4_681checked : Checked tree [8,2,5,10] := by
  refine ⟨plan2270,valid2270,t4_681choices,?_⟩
  exact check_of_frontier tree 0 t4_681root t4_681jobs t4_681frontier t4_681all
theorem t4_682choices : plan2271.choices=[8,2,6,6].map (options 4 3) := by rfl


theorem t4_682part0 : t4_682jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_682frontier : t4_682root.frontier 0=t4_682jobs := by rfl
theorem t4_682all : t4_682jobs.all (Job.check tree)=true := by
  simp only [t4_682jobs,List.all_append,List.all_nil,t4_682part0,Bool.and_self]
theorem t4_682checked : Checked tree [8,2,6,6] := by
  refine ⟨plan2271,valid2271,t4_682choices,?_⟩
  exact check_of_frontier tree 0 t4_682root t4_682jobs t4_682frontier t4_682all
theorem t4_683choices : plan2272.choices=[8,2,6,7].map (options 4 3) := by rfl


theorem t4_683part0 : t4_683jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_683frontier : t4_683root.frontier 0=t4_683jobs := by rfl
theorem t4_683all : t4_683jobs.all (Job.check tree)=true := by
  simp only [t4_683jobs,List.all_append,List.all_nil,t4_683part0,Bool.and_self]
theorem t4_683checked : Checked tree [8,2,6,7] := by
  refine ⟨plan2272,valid2272,t4_683choices,?_⟩
  exact check_of_frontier tree 0 t4_683root t4_683jobs t4_683frontier t4_683all
theorem t4_684choices : plan2273.choices=[8,2,6,10].map (options 4 3) := by rfl


theorem t4_684part0 : t4_684jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_684frontier : t4_684root.frontier 0=t4_684jobs := by rfl
theorem t4_684all : t4_684jobs.all (Job.check tree)=true := by
  simp only [t4_684jobs,List.all_append,List.all_nil,t4_684part0,Bool.and_self]
theorem t4_684checked : Checked tree [8,2,6,10] := by
  refine ⟨plan2273,valid2273,t4_684choices,?_⟩
  exact check_of_frontier tree 0 t4_684root t4_684jobs t4_684frontier t4_684all
theorem t4_685choices : plan2274.choices=[8,2,7,7].map (options 4 3) := by rfl


theorem t4_685part0 : t4_685jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_685frontier : t4_685root.frontier 0=t4_685jobs := by rfl
theorem t4_685all : t4_685jobs.all (Job.check tree)=true := by
  simp only [t4_685jobs,List.all_append,List.all_nil,t4_685part0,Bool.and_self]
theorem t4_685checked : Checked tree [8,2,7,7] := by
  refine ⟨plan2274,valid2274,t4_685choices,?_⟩
  exact check_of_frontier tree 0 t4_685root t4_685jobs t4_685frontier t4_685all
theorem t4_686choices : plan2007.choices=[8,2,9,3].map (options 4 2) := by rfl


theorem t4_686part0 : t4_686jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_686frontier : t4_686root.frontier 0=t4_686jobs := by rfl
theorem t4_686all : t4_686jobs.all (Job.check tree)=true := by
  simp only [t4_686jobs,List.all_append,List.all_nil,t4_686part0,Bool.and_self]
theorem t4_686checked : Checked tree [8,2,9,3] := by
  refine ⟨plan2007,valid2007,t4_686choices,?_⟩
  exact check_of_frontier tree 0 t4_686root t4_686jobs t4_686frontier t4_686all
theorem t4_687choices : plan2275.choices=[8,2,9,6].map (options 4 3) := by rfl


theorem t4_687part0 : t4_687jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_687frontier : t4_687root.frontier 0=t4_687jobs := by rfl
theorem t4_687all : t4_687jobs.all (Job.check tree)=true := by
  simp only [t4_687jobs,List.all_append,List.all_nil,t4_687part0,Bool.and_self]
theorem t4_687checked : Checked tree [8,2,9,6] := by
  refine ⟨plan2275,valid2275,t4_687choices,?_⟩
  exact check_of_frontier tree 0 t4_687root t4_687jobs t4_687frontier t4_687all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks004 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_557checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_570checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_571checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_572checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_573checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_574checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_575checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_576checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_577checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_578checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_579checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_558checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_580checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_581checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_582checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_583checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_584checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_585checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_586checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_587checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_588checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_589checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_559checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_590checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_591checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_592checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_593checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_594checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_595checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_596checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_597checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_598checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_599checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_560checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_600checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_601checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_602checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_603checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_604checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_605checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_606checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_607checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_608checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_609checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_561checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_610checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_611checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_612checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_613checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_614checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_615checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_616checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_617checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_618checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_619checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_562checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_620checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_621checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_622checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_623checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_624checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_625checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_626checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_627checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_628checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_629checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_563checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_630checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_631checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_632checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_633checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_634checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_635checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_636checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_637checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_638checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_639checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_564checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_640checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_641checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_642checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_643checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_644checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_645checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_646checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_647checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_648checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_649checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_565checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_650checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_651checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_652checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_653checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_654checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_655checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_656checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_657checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_658checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_659checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_566checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_660checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_661checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_662checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_663checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_664checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_665checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_666checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_667checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_668checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_669checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_567checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_670checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_671checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_672checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_673checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_674checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_675checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_676checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_677checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_678checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_679checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_568checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_680checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_681checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_682checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_683checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_684checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_685checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_686checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_687checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_569checked⟩
