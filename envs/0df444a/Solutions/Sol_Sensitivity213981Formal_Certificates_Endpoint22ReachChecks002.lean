-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks002
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:46:06.174155+00:00
-- url     : https://prove2.me/submissions/12d27fe7-f953-44a9-9daa-52c0aa1baa74

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks002
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



theorem valid62 : plan62.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid64 : plan64.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid65 : plan65.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid67 : plan67.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid69 : plan69.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid71 : plan71.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid72 : plan72.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid73 : plan73.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid74 : plan74.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid76 : plan76.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid77 : plan77.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid78 : plan78.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid79 : plan79.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid80 : plan80.Valid := valid_step _ _ _ valid0 (by decide +kernel)
































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





















theorem valid346 : plan346.Valid := valid_step _ _ _ valid62 (by decide +kernel)

theorem valid347 : plan347.Valid := valid_step _ _ _ valid64 (by decide +kernel)

theorem valid348 : plan348.Valid := valid_step _ _ _ valid65 (by decide +kernel)

theorem valid349 : plan349.Valid := valid_step _ _ _ valid67 (by decide +kernel)







theorem valid353 : plan353.Valid := valid_step _ _ _ valid62 (by decide +kernel)

















theorem valid362 : plan362.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid363 : plan363.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid364 : plan364.Valid := valid_step _ _ _ valid74 (by decide +kernel)









theorem valid369 : plan369.Valid := valid_step _ _ _ valid69 (by decide +kernel)











theorem valid375 : plan375.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid376 : plan376.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid377 : plan377.Valid := valid_step _ _ _ valid74 (by decide +kernel)

theorem valid378 : plan378.Valid := valid_step _ _ _ valid72 (by decide +kernel)









theorem valid383 : plan383.Valid := valid_step _ _ _ valid69 (by decide +kernel)

theorem valid384 : plan384.Valid := valid_step _ _ _ valid71 (by decide +kernel)
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























































theorem valid938 : plan938.Valid := valid_step _ _ _ valid353 (by decide +kernel)



theorem valid940 : plan940.Valid := valid_step _ _ _ valid347 (by decide +kernel)

theorem valid941 : plan941.Valid := valid_step _ _ _ valid348 (by decide +kernel)

theorem valid942 : plan942.Valid := valid_step _ _ _ valid349 (by decide +kernel)







theorem valid946 : plan946.Valid := valid_step _ _ _ valid346 (by decide +kernel)







theorem valid950 : plan950.Valid := valid_step _ _ _ valid346 (by decide +kernel)




















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





























































































































































theorem valid1711 : plan1711.Valid := valid_step _ _ _ valid910 (by decide +kernel)


































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

theorem valid385 : plan385.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid386 : plan386.Valid := valid_step _ _ _ valid73 (by decide +kernel)

theorem valid387 : plan387.Valid := valid_step _ _ _ valid74 (by decide +kernel)

theorem valid388 : plan388.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid389 : plan389.Valid := valid_step _ _ _ valid74 (by decide +kernel)



























theorem valid403 : plan403.Valid := valid_step _ _ _ valid76 (by decide +kernel)

theorem valid404 : plan404.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid405 : plan405.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid406 : plan406.Valid := valid_step _ _ _ valid79 (by decide +kernel)

theorem valid407 : plan407.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid408 : plan408.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid409 : plan409.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid410 : plan410.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid411 : plan411.Valid := valid_step _ _ _ valid78 (by decide +kernel)











theorem valid417 : plan417.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid418 : plan418.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid419 : plan419.Valid := valid_step _ _ _ valid79 (by decide +kernel)

theorem valid420 : plan420.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid421 : plan421.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid422 : plan422.Valid := valid_step _ _ _ valid80 (by decide +kernel)




















































































































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



















































theorem valid986 : plan986.Valid := valid_step _ _ _ valid375 (by decide +kernel)

theorem valid987 : plan987.Valid := valid_step _ _ _ valid376 (by decide +kernel)

theorem valid988 : plan988.Valid := valid_step _ _ _ valid377 (by decide +kernel)

theorem valid989 : plan989.Valid := valid_step _ _ _ valid378 (by decide +kernel)



theorem valid991 : plan991.Valid := valid_step _ _ _ valid384 (by decide +kernel)

theorem valid992 : plan992.Valid := valid_step _ _ _ valid385 (by decide +kernel)

theorem valid993 : plan993.Valid := valid_step _ _ _ valid386 (by decide +kernel)

theorem valid994 : plan994.Valid := valid_step _ _ _ valid387 (by decide +kernel)

theorem valid995 : plan995.Valid := valid_step _ _ _ valid388 (by decide +kernel)

theorem valid996 : plan996.Valid := valid_step _ _ _ valid389 (by decide +kernel)







theorem valid1000 : plan1000.Valid := valid_step _ _ _ valid375 (by decide +kernel)

theorem valid1001 : plan1001.Valid := valid_step _ _ _ valid376 (by decide +kernel)

theorem valid1002 : plan1002.Valid := valid_step _ _ _ valid377 (by decide +kernel)

theorem valid1003 : plan1003.Valid := valid_step _ _ _ valid378 (by decide +kernel)

theorem valid1004 : plan1004.Valid := valid_step _ _ _ valid388 (by decide +kernel)

theorem valid1005 : plan1005.Valid := valid_step _ _ _ valid389 (by decide +kernel)

































theorem valid1022 : plan1022.Valid := valid_step _ _ _ valid362 (by decide +kernel)

theorem valid1023 : plan1023.Valid := valid_step _ _ _ valid363 (by decide +kernel)

theorem valid1024 : plan1024.Valid := valid_step _ _ _ valid364 (by decide +kernel)

theorem valid1025 : plan1025.Valid := valid_step _ _ _ valid369 (by decide +kernel)

theorem valid1026 : plan1026.Valid := valid_step _ _ _ valid383 (by decide +kernel)































theorem valid1042 : plan1042.Valid := valid_step _ _ _ valid362 (by decide +kernel)

theorem valid1043 : plan1043.Valid := valid_step _ _ _ valid363 (by decide +kernel)

theorem valid1044 : plan1044.Valid := valid_step _ _ _ valid364 (by decide +kernel)

theorem valid1045 : plan1045.Valid := valid_step _ _ _ valid383 (by decide +kernel)






















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

















































































































theorem valid1785 : plan1785.Valid := valid_step _ _ _ valid938 (by decide +kernel)

theorem valid1786 : plan1786.Valid := valid_step _ _ _ valid940 (by decide +kernel)

theorem valid1787 : plan1787.Valid := valid_step _ _ _ valid941 (by decide +kernel)

theorem valid1788 : plan1788.Valid := valid_step _ _ _ valid942 (by decide +kernel)

theorem valid1789 : plan1789.Valid := valid_step _ _ _ valid946 (by decide +kernel)

theorem valid1790 : plan1790.Valid := valid_step _ _ _ valid950 (by decide +kernel)




































































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































































































theorem valid1104 : plan1104.Valid := valid_step _ _ _ valid403 (by decide +kernel)

theorem valid1105 : plan1105.Valid := valid_step _ _ _ valid404 (by decide +kernel)

theorem valid1106 : plan1106.Valid := valid_step _ _ _ valid405 (by decide +kernel)

theorem valid1107 : plan1107.Valid := valid_step _ _ _ valid406 (by decide +kernel)

theorem valid1108 : plan1108.Valid := valid_step _ _ _ valid407 (by decide +kernel)

theorem valid1109 : plan1109.Valid := valid_step _ _ _ valid408 (by decide +kernel)

theorem valid1110 : plan1110.Valid := valid_step _ _ _ valid409 (by decide +kernel)

theorem valid1111 : plan1111.Valid := valid_step _ _ _ valid410 (by decide +kernel)

theorem valid1112 : plan1112.Valid := valid_step _ _ _ valid411 (by decide +kernel)



theorem valid1114 : plan1114.Valid := valid_step _ _ _ valid417 (by decide +kernel)

theorem valid1115 : plan1115.Valid := valid_step _ _ _ valid418 (by decide +kernel)

theorem valid1116 : plan1116.Valid := valid_step _ _ _ valid419 (by decide +kernel)

theorem valid1117 : plan1117.Valid := valid_step _ _ _ valid420 (by decide +kernel)

theorem valid1118 : plan1118.Valid := valid_step _ _ _ valid421 (by decide +kernel)

theorem valid1119 : plan1119.Valid := valid_step _ _ _ valid422 (by decide +kernel)

theorem valid1120 : plan1120.Valid := valid_step _ _ _ valid408 (by decide +kernel)

theorem valid1121 : plan1121.Valid := valid_step _ _ _ valid409 (by decide +kernel)

theorem valid1122 : plan1122.Valid := valid_step _ _ _ valid410 (by decide +kernel)

theorem valid1123 : plan1123.Valid := valid_step _ _ _ valid411 (by decide +kernel)

theorem valid1124 : plan1124.Valid := valid_step _ _ _ valid421 (by decide +kernel)

theorem valid1125 : plan1125.Valid := valid_step _ _ _ valid422 (by decide +kernel)

theorem valid1126 : plan1126.Valid := valid_step _ _ _ valid411 (by decide +kernel)




















































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













theorem valid1159 : plan1159.Valid := valid_step _ _ _ valid408 (by decide +kernel)

theorem valid1160 : plan1160.Valid := valid_step _ _ _ valid409 (by decide +kernel)

theorem valid1161 : plan1161.Valid := valid_step _ _ _ valid410 (by decide +kernel)

theorem valid1162 : plan1162.Valid := valid_step _ _ _ valid411 (by decide +kernel)



theorem valid1164 : plan1164.Valid := valid_step _ _ _ valid417 (by decide +kernel)

theorem valid1165 : plan1165.Valid := valid_step _ _ _ valid418 (by decide +kernel)

theorem valid1166 : plan1166.Valid := valid_step _ _ _ valid419 (by decide +kernel)




































































































































































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









































theorem valid1941 : plan1941.Valid := valid_step _ _ _ valid986 (by decide +kernel)

theorem valid1942 : plan1942.Valid := valid_step _ _ _ valid987 (by decide +kernel)

theorem valid1943 : plan1943.Valid := valid_step _ _ _ valid988 (by decide +kernel)

theorem valid1944 : plan1944.Valid := valid_step _ _ _ valid989 (by decide +kernel)

theorem valid1945 : plan1945.Valid := valid_step _ _ _ valid991 (by decide +kernel)

theorem valid1946 : plan1946.Valid := valid_step _ _ _ valid992 (by decide +kernel)

theorem valid1947 : plan1947.Valid := valid_step _ _ _ valid993 (by decide +kernel)

theorem valid1948 : plan1948.Valid := valid_step _ _ _ valid994 (by decide +kernel)

theorem valid1949 : plan1949.Valid := valid_step _ _ _ valid995 (by decide +kernel)

theorem valid1950 : plan1950.Valid := valid_step _ _ _ valid996 (by decide +kernel)

theorem valid1951 : plan1951.Valid := valid_step _ _ _ valid1000 (by decide +kernel)

theorem valid1952 : plan1952.Valid := valid_step _ _ _ valid1001 (by decide +kernel)

theorem valid1953 : plan1953.Valid := valid_step _ _ _ valid1002 (by decide +kernel)

theorem valid1954 : plan1954.Valid := valid_step _ _ _ valid1003 (by decide +kernel)

theorem valid1955 : plan1955.Valid := valid_step _ _ _ valid1004 (by decide +kernel)

theorem valid1956 : plan1956.Valid := valid_step _ _ _ valid1005 (by decide +kernel)

theorem valid1957 : plan1957.Valid := valid_step _ _ _ valid1022 (by decide +kernel)

theorem valid1958 : plan1958.Valid := valid_step _ _ _ valid1023 (by decide +kernel)

theorem valid1959 : plan1959.Valid := valid_step _ _ _ valid1024 (by decide +kernel)

theorem valid1960 : plan1960.Valid := valid_step _ _ _ valid1025 (by decide +kernel)

theorem valid1961 : plan1961.Valid := valid_step _ _ _ valid1026 (by decide +kernel)

theorem valid1962 : plan1962.Valid := valid_step _ _ _ valid1042 (by decide +kernel)

theorem valid1963 : plan1963.Valid := valid_step _ _ _ valid1043 (by decide +kernel)

theorem valid1964 : plan1964.Valid := valid_step _ _ _ valid1044 (by decide +kernel)

theorem valid1965 : plan1965.Valid := valid_step _ _ _ valid1045 (by decide +kernel)






































































































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

















































































theorem valid2153 : plan2153.Valid := valid_step _ _ _ valid1104 (by decide +kernel)

theorem valid2154 : plan2154.Valid := valid_step _ _ _ valid1105 (by decide +kernel)

theorem valid2155 : plan2155.Valid := valid_step _ _ _ valid1106 (by decide +kernel)

theorem valid2156 : plan2156.Valid := valid_step _ _ _ valid1107 (by decide +kernel)

theorem valid2157 : plan2157.Valid := valid_step _ _ _ valid1108 (by decide +kernel)

theorem valid2158 : plan2158.Valid := valid_step _ _ _ valid1109 (by decide +kernel)

theorem valid2159 : plan2159.Valid := valid_step _ _ _ valid1110 (by decide +kernel)

theorem valid2160 : plan2160.Valid := valid_step _ _ _ valid1111 (by decide +kernel)

theorem valid2161 : plan2161.Valid := valid_step _ _ _ valid1112 (by decide +kernel)

theorem valid2162 : plan2162.Valid := valid_step _ _ _ valid1114 (by decide +kernel)

theorem valid2163 : plan2163.Valid := valid_step _ _ _ valid1115 (by decide +kernel)

theorem valid2164 : plan2164.Valid := valid_step _ _ _ valid1116 (by decide +kernel)

theorem valid2165 : plan2165.Valid := valid_step _ _ _ valid1117 (by decide +kernel)

theorem valid2166 : plan2166.Valid := valid_step _ _ _ valid1118 (by decide +kernel)

theorem valid2167 : plan2167.Valid := valid_step _ _ _ valid1119 (by decide +kernel)

theorem valid2168 : plan2168.Valid := valid_step _ _ _ valid1120 (by decide +kernel)

theorem valid2169 : plan2169.Valid := valid_step _ _ _ valid1121 (by decide +kernel)

theorem valid2170 : plan2170.Valid := valid_step _ _ _ valid1122 (by decide +kernel)

theorem valid2171 : plan2171.Valid := valid_step _ _ _ valid1123 (by decide +kernel)

theorem valid2172 : plan2172.Valid := valid_step _ _ _ valid1124 (by decide +kernel)

theorem valid2173 : plan2173.Valid := valid_step _ _ _ valid1125 (by decide +kernel)

theorem valid2174 : plan2174.Valid := valid_step _ _ _ valid1126 (by decide +kernel)

theorem valid2175 : plan2175.Valid := valid_step _ _ _ valid1159 (by decide +kernel)

theorem valid2176 : plan2176.Valid := valid_step _ _ _ valid1160 (by decide +kernel)

theorem valid2177 : plan2177.Valid := valid_step _ _ _ valid1161 (by decide +kernel)

theorem valid2178 : plan2178.Valid := valid_step _ _ _ valid1162 (by decide +kernel)

theorem valid2179 : plan2179.Valid := valid_step _ _ _ valid1164 (by decide +kernel)

theorem valid2180 : plan2180.Valid := valid_step _ _ _ valid1165 (by decide +kernel)

theorem valid2181 : plan2181.Valid := valid_step _ _ _ valid1166 (by decide +kernel)






















































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
theorem t4_359choices : plan1941.choices=[2,2,6,6].map (options 4 2) := by rfl


theorem t4_359part0 : t4_359jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_359frontier : t4_359root.frontier 0=t4_359jobs := by rfl
theorem t4_359all : t4_359jobs.all (Job.check tree)=true := by
  simp only [t4_359jobs,List.all_append,List.all_nil,t4_359part0,Bool.and_self]
theorem t4_359checked : Checked tree [2,2,6,6] := by
  refine ⟨plan1941,valid1941,t4_359choices,?_⟩
  exact check_of_frontier tree 0 t4_359root t4_359jobs t4_359frontier t4_359all
theorem t4_360choices : plan1942.choices=[2,2,6,7].map (options 4 2) := by rfl


theorem t4_360part0 : t4_360jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_360frontier : t4_360root.frontier 0=t4_360jobs := by rfl
theorem t4_360all : t4_360jobs.all (Job.check tree)=true := by
  simp only [t4_360jobs,List.all_append,List.all_nil,t4_360part0,Bool.and_self]
theorem t4_360checked : Checked tree [2,2,6,7] := by
  refine ⟨plan1942,valid1942,t4_360choices,?_⟩
  exact check_of_frontier tree 0 t4_360root t4_360jobs t4_360frontier t4_360all
theorem t4_361choices : plan1943.choices=[2,2,6,10].map (options 4 2) := by rfl


theorem t4_361part0 : t4_361jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_361frontier : t4_361root.frontier 0=t4_361jobs := by rfl
theorem t4_361all : t4_361jobs.all (Job.check tree)=true := by
  simp only [t4_361jobs,List.all_append,List.all_nil,t4_361part0,Bool.and_self]
theorem t4_361checked : Checked tree [2,2,6,10] := by
  refine ⟨plan1943,valid1943,t4_361choices,?_⟩
  exact check_of_frontier tree 0 t4_361root t4_361jobs t4_361frontier t4_361all
theorem t4_362choices : plan1944.choices=[2,2,7,7].map (options 4 2) := by rfl


theorem t4_362part0 : t4_362jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_362frontier : t4_362root.frontier 0=t4_362jobs := by rfl
theorem t4_362all : t4_362jobs.all (Job.check tree)=true := by
  simp only [t4_362jobs,List.all_append,List.all_nil,t4_362part0,Bool.and_self]
theorem t4_362checked : Checked tree [2,2,7,7] := by
  refine ⟨plan1944,valid1944,t4_362choices,?_⟩
  exact check_of_frontier tree 0 t4_362root t4_362jobs t4_362frontier t4_362all
theorem t4_363choices : plan1785.choices=[2,2,9,3].map (options 4 1) := by rfl


theorem t4_363part0 : t4_363jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_363frontier : t4_363root.frontier 0=t4_363jobs := by rfl
theorem t4_363all : t4_363jobs.all (Job.check tree)=true := by
  simp only [t4_363jobs,List.all_append,List.all_nil,t4_363part0,Bool.and_self]
theorem t4_363checked : Checked tree [2,2,9,3] := by
  refine ⟨plan1785,valid1785,t4_363choices,?_⟩
  exact check_of_frontier tree 0 t4_363root t4_363jobs t4_363frontier t4_363all
theorem t4_364choices : plan1945.choices=[2,2,9,6].map (options 4 2) := by rfl


theorem t4_364part0 : t4_364jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_364frontier : t4_364root.frontier 0=t4_364jobs := by rfl
theorem t4_364all : t4_364jobs.all (Job.check tree)=true := by
  simp only [t4_364jobs,List.all_append,List.all_nil,t4_364part0,Bool.and_self]
theorem t4_364checked : Checked tree [2,2,9,6] := by
  refine ⟨plan1945,valid1945,t4_364choices,?_⟩
  exact check_of_frontier tree 0 t4_364root t4_364jobs t4_364frontier t4_364all
theorem t4_365choices : plan1946.choices=[2,2,9,7].map (options 4 2) := by rfl


theorem t4_365part0 : t4_365jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_365frontier : t4_365root.frontier 0=t4_365jobs := by rfl
theorem t4_365all : t4_365jobs.all (Job.check tree)=true := by
  simp only [t4_365jobs,List.all_append,List.all_nil,t4_365part0,Bool.and_self]
theorem t4_365checked : Checked tree [2,2,9,7] := by
  refine ⟨plan1946,valid1946,t4_365choices,?_⟩
  exact check_of_frontier tree 0 t4_365root t4_365jobs t4_365frontier t4_365all
theorem t4_366choices : plan1947.choices=[2,2,9,9].map (options 4 2) := by rfl


theorem t4_366part0 : t4_366jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_366frontier : t4_366root.frontier 0=t4_366jobs := by rfl
theorem t4_366all : t4_366jobs.all (Job.check tree)=true := by
  simp only [t4_366jobs,List.all_append,List.all_nil,t4_366part0,Bool.and_self]
theorem t4_366checked : Checked tree [2,2,9,9] := by
  refine ⟨plan1947,valid1947,t4_366choices,?_⟩
  exact check_of_frontier tree 0 t4_366root t4_366jobs t4_366frontier t4_366all
theorem t4_367choices : plan1948.choices=[2,2,9,10].map (options 4 2) := by rfl


theorem t4_367part0 : t4_367jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_367frontier : t4_367root.frontier 0=t4_367jobs := by rfl
theorem t4_367all : t4_367jobs.all (Job.check tree)=true := by
  simp only [t4_367jobs,List.all_append,List.all_nil,t4_367part0,Bool.and_self]
theorem t4_367checked : Checked tree [2,2,9,10] := by
  refine ⟨plan1948,valid1948,t4_367choices,?_⟩
  exact check_of_frontier tree 0 t4_367root t4_367jobs t4_367frontier t4_367all
theorem t4_368choices : plan1949.choices=[2,2,10,7].map (options 4 2) := by rfl


theorem t4_368part0 : t4_368jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_368frontier : t4_368root.frontier 0=t4_368jobs := by rfl
theorem t4_368all : t4_368jobs.all (Job.check tree)=true := by
  simp only [t4_368jobs,List.all_append,List.all_nil,t4_368part0,Bool.and_self]
theorem t4_368checked : Checked tree [2,2,10,7] := by
  refine ⟨plan1949,valid1949,t4_368choices,?_⟩
  exact check_of_frontier tree 0 t4_368root t4_368jobs t4_368frontier t4_368all
theorem t4_369choices : plan1950.choices=[2,2,10,10].map (options 4 2) := by rfl


theorem t4_369part0 : t4_369jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_369frontier : t4_369root.frontier 0=t4_369jobs := by rfl
theorem t4_369all : t4_369jobs.all (Job.check tree)=true := by
  simp only [t4_369jobs,List.all_append,List.all_nil,t4_369part0,Bool.and_self]
theorem t4_369checked : Checked tree [2,2,10,10] := by
  refine ⟨plan1950,valid1950,t4_369choices,?_⟩
  exact check_of_frontier tree 0 t4_369root t4_369jobs t4_369frontier t4_369all
theorem t4_370choices : plan1711.choices=[2,3,3,3].map (options 4 0) := by rfl


theorem t4_370part0 : t4_370jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_370frontier : t4_370root.frontier 0=t4_370jobs := by rfl
theorem t4_370all : t4_370jobs.all (Job.check tree)=true := by
  simp only [t4_370jobs,List.all_append,List.all_nil,t4_370part0,Bool.and_self]
theorem t4_370checked : Checked tree [2,3,3,3] := by
  refine ⟨plan1711,valid1711,t4_370choices,?_⟩
  exact check_of_frontier tree 0 t4_370root t4_370jobs t4_370frontier t4_370all
theorem t4_371choices : plan1786.choices=[2,3,3,6].map (options 4 1) := by rfl


theorem t4_371part0 : t4_371jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_371frontier : t4_371root.frontier 0=t4_371jobs := by rfl
theorem t4_371all : t4_371jobs.all (Job.check tree)=true := by
  simp only [t4_371jobs,List.all_append,List.all_nil,t4_371part0,Bool.and_self]
theorem t4_371checked : Checked tree [2,3,3,6] := by
  refine ⟨plan1786,valid1786,t4_371choices,?_⟩
  exact check_of_frontier tree 0 t4_371root t4_371jobs t4_371frontier t4_371all
theorem t4_372choices : plan1787.choices=[2,3,3,7].map (options 4 1) := by rfl


theorem t4_372part0 : t4_372jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_372frontier : t4_372root.frontier 0=t4_372jobs := by rfl
theorem t4_372all : t4_372jobs.all (Job.check tree)=true := by
  simp only [t4_372jobs,List.all_append,List.all_nil,t4_372part0,Bool.and_self]
theorem t4_372checked : Checked tree [2,3,3,7] := by
  refine ⟨plan1787,valid1787,t4_372choices,?_⟩
  exact check_of_frontier tree 0 t4_372root t4_372jobs t4_372frontier t4_372all
theorem t4_373choices : plan1788.choices=[2,3,3,10].map (options 4 1) := by rfl


theorem t4_373part0 : t4_373jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_373frontier : t4_373root.frontier 0=t4_373jobs := by rfl
theorem t4_373all : t4_373jobs.all (Job.check tree)=true := by
  simp only [t4_373jobs,List.all_append,List.all_nil,t4_373part0,Bool.and_self]
theorem t4_373checked : Checked tree [2,3,3,10] := by
  refine ⟨plan1788,valid1788,t4_373choices,?_⟩
  exact check_of_frontier tree 0 t4_373root t4_373jobs t4_373frontier t4_373all
theorem t4_374choices : plan1951.choices=[2,3,6,6].map (options 4 2) := by rfl


theorem t4_374part0 : t4_374jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_374frontier : t4_374root.frontier 0=t4_374jobs := by rfl
theorem t4_374all : t4_374jobs.all (Job.check tree)=true := by
  simp only [t4_374jobs,List.all_append,List.all_nil,t4_374part0,Bool.and_self]
theorem t4_374checked : Checked tree [2,3,6,6] := by
  refine ⟨plan1951,valid1951,t4_374choices,?_⟩
  exact check_of_frontier tree 0 t4_374root t4_374jobs t4_374frontier t4_374all
theorem t4_375choices : plan1952.choices=[2,3,6,7].map (options 4 2) := by rfl


theorem t4_375part0 : t4_375jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_375frontier : t4_375root.frontier 0=t4_375jobs := by rfl
theorem t4_375all : t4_375jobs.all (Job.check tree)=true := by
  simp only [t4_375jobs,List.all_append,List.all_nil,t4_375part0,Bool.and_self]
theorem t4_375checked : Checked tree [2,3,6,7] := by
  refine ⟨plan1952,valid1952,t4_375choices,?_⟩
  exact check_of_frontier tree 0 t4_375root t4_375jobs t4_375frontier t4_375all
theorem t4_376choices : plan1953.choices=[2,3,6,10].map (options 4 2) := by rfl


theorem t4_376part0 : t4_376jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_376frontier : t4_376root.frontier 0=t4_376jobs := by rfl
theorem t4_376all : t4_376jobs.all (Job.check tree)=true := by
  simp only [t4_376jobs,List.all_append,List.all_nil,t4_376part0,Bool.and_self]
theorem t4_376checked : Checked tree [2,3,6,10] := by
  refine ⟨plan1953,valid1953,t4_376choices,?_⟩
  exact check_of_frontier tree 0 t4_376root t4_376jobs t4_376frontier t4_376all
theorem t4_377choices : plan1954.choices=[2,3,7,7].map (options 4 2) := by rfl


theorem t4_377part0 : t4_377jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_377frontier : t4_377root.frontier 0=t4_377jobs := by rfl
theorem t4_377all : t4_377jobs.all (Job.check tree)=true := by
  simp only [t4_377jobs,List.all_append,List.all_nil,t4_377part0,Bool.and_self]
theorem t4_377checked : Checked tree [2,3,7,7] := by
  refine ⟨plan1954,valid1954,t4_377choices,?_⟩
  exact check_of_frontier tree 0 t4_377root t4_377jobs t4_377frontier t4_377all
theorem t4_378choices : plan1955.choices=[2,3,10,7].map (options 4 2) := by rfl


theorem t4_378part0 : t4_378jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_378frontier : t4_378root.frontier 0=t4_378jobs := by rfl
theorem t4_378all : t4_378jobs.all (Job.check tree)=true := by
  simp only [t4_378jobs,List.all_append,List.all_nil,t4_378part0,Bool.and_self]
theorem t4_378checked : Checked tree [2,3,10,7] := by
  refine ⟨plan1955,valid1955,t4_378choices,?_⟩
  exact check_of_frontier tree 0 t4_378root t4_378jobs t4_378frontier t4_378all
theorem t4_379choices : plan1956.choices=[2,3,10,10].map (options 4 2) := by rfl


theorem t4_379part0 : t4_379jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_379frontier : t4_379root.frontier 0=t4_379jobs := by rfl
theorem t4_379all : t4_379jobs.all (Job.check tree)=true := by
  simp only [t4_379jobs,List.all_append,List.all_nil,t4_379part0,Bool.and_self]
theorem t4_379checked : Checked tree [2,3,10,10] := by
  refine ⟨plan1956,valid1956,t4_379choices,?_⟩
  exact check_of_frontier tree 0 t4_379root t4_379jobs t4_379frontier t4_379all
theorem t4_380choices : plan1789.choices=[2,5,3,3].map (options 4 1) := by rfl


theorem t4_380part0 : t4_380jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_380frontier : t4_380root.frontier 0=t4_380jobs := by rfl
theorem t4_380all : t4_380jobs.all (Job.check tree)=true := by
  simp only [t4_380jobs,List.all_append,List.all_nil,t4_380part0,Bool.and_self]
theorem t4_380checked : Checked tree [2,5,3,3] := by
  refine ⟨plan1789,valid1789,t4_380choices,?_⟩
  exact check_of_frontier tree 0 t4_380root t4_380jobs t4_380frontier t4_380all
theorem t4_381choices : plan1957.choices=[2,5,3,6].map (options 4 2) := by rfl


theorem t4_381part0 : t4_381jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_381frontier : t4_381root.frontier 0=t4_381jobs := by rfl
theorem t4_381all : t4_381jobs.all (Job.check tree)=true := by
  simp only [t4_381jobs,List.all_append,List.all_nil,t4_381part0,Bool.and_self]
theorem t4_381checked : Checked tree [2,5,3,6] := by
  refine ⟨plan1957,valid1957,t4_381choices,?_⟩
  exact check_of_frontier tree 0 t4_381root t4_381jobs t4_381frontier t4_381all
theorem t4_382choices : plan1958.choices=[2,5,3,7].map (options 4 2) := by rfl


theorem t4_382part0 : t4_382jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_382frontier : t4_382root.frontier 0=t4_382jobs := by rfl
theorem t4_382all : t4_382jobs.all (Job.check tree)=true := by
  simp only [t4_382jobs,List.all_append,List.all_nil,t4_382part0,Bool.and_self]
theorem t4_382checked : Checked tree [2,5,3,7] := by
  refine ⟨plan1958,valid1958,t4_382choices,?_⟩
  exact check_of_frontier tree 0 t4_382root t4_382jobs t4_382frontier t4_382all
theorem t4_383choices : plan1959.choices=[2,5,3,10].map (options 4 2) := by rfl


theorem t4_383part0 : t4_383jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_383frontier : t4_383root.frontier 0=t4_383jobs := by rfl
theorem t4_383all : t4_383jobs.all (Job.check tree)=true := by
  simp only [t4_383jobs,List.all_append,List.all_nil,t4_383part0,Bool.and_self]
theorem t4_383checked : Checked tree [2,5,3,10] := by
  refine ⟨plan1959,valid1959,t4_383choices,?_⟩
  exact check_of_frontier tree 0 t4_383root t4_383jobs t4_383frontier t4_383all
theorem t4_384choices : plan1960.choices=[2,5,5,3].map (options 4 2) := by rfl


theorem t4_384part0 : t4_384jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_384frontier : t4_384root.frontier 0=t4_384jobs := by rfl
theorem t4_384all : t4_384jobs.all (Job.check tree)=true := by
  simp only [t4_384jobs,List.all_append,List.all_nil,t4_384part0,Bool.and_self]
theorem t4_384checked : Checked tree [2,5,5,3] := by
  refine ⟨plan1960,valid1960,t4_384choices,?_⟩
  exact check_of_frontier tree 0 t4_384root t4_384jobs t4_384frontier t4_384all
theorem t4_385choices : plan2153.choices=[2,5,5,5].map (options 4 3) := by rfl


theorem t4_385part0 : t4_385jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_385frontier : t4_385root.frontier 0=t4_385jobs := by rfl
theorem t4_385all : t4_385jobs.all (Job.check tree)=true := by
  simp only [t4_385jobs,List.all_append,List.all_nil,t4_385part0,Bool.and_self]
theorem t4_385checked : Checked tree [2,5,5,5] := by
  refine ⟨plan2153,valid2153,t4_385choices,?_⟩
  exact check_of_frontier tree 0 t4_385root t4_385jobs t4_385frontier t4_385all
theorem t4_386choices : plan2154.choices=[2,5,5,6].map (options 4 3) := by rfl


theorem t4_386part0 : t4_386jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_386frontier : t4_386root.frontier 0=t4_386jobs := by rfl
theorem t4_386all : t4_386jobs.all (Job.check tree)=true := by
  simp only [t4_386jobs,List.all_append,List.all_nil,t4_386part0,Bool.and_self]
theorem t4_386checked : Checked tree [2,5,5,6] := by
  refine ⟨plan2154,valid2154,t4_386choices,?_⟩
  exact check_of_frontier tree 0 t4_386root t4_386jobs t4_386frontier t4_386all
theorem t4_387choices : plan2155.choices=[2,5,5,7].map (options 4 3) := by rfl


theorem t4_387part0 : t4_387jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_387frontier : t4_387root.frontier 0=t4_387jobs := by rfl
theorem t4_387all : t4_387jobs.all (Job.check tree)=true := by
  simp only [t4_387jobs,List.all_append,List.all_nil,t4_387part0,Bool.and_self]
theorem t4_387checked : Checked tree [2,5,5,7] := by
  refine ⟨plan2155,valid2155,t4_387choices,?_⟩
  exact check_of_frontier tree 0 t4_387root t4_387jobs t4_387frontier t4_387all
theorem t4_388choices : plan2156.choices=[2,5,5,9].map (options 4 3) := by rfl


theorem t4_388part0 : t4_388jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_388frontier : t4_388root.frontier 0=t4_388jobs := by rfl
theorem t4_388all : t4_388jobs.all (Job.check tree)=true := by
  simp only [t4_388jobs,List.all_append,List.all_nil,t4_388part0,Bool.and_self]
theorem t4_388checked : Checked tree [2,5,5,9] := by
  refine ⟨plan2156,valid2156,t4_388choices,?_⟩
  exact check_of_frontier tree 0 t4_388root t4_388jobs t4_388frontier t4_388all
theorem t4_389choices : plan2157.choices=[2,5,5,10].map (options 4 3) := by rfl


theorem t4_389part0 : t4_389jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_389frontier : t4_389root.frontier 0=t4_389jobs := by rfl
theorem t4_389all : t4_389jobs.all (Job.check tree)=true := by
  simp only [t4_389jobs,List.all_append,List.all_nil,t4_389part0,Bool.and_self]
theorem t4_389checked : Checked tree [2,5,5,10] := by
  refine ⟨plan2157,valid2157,t4_389choices,?_⟩
  exact check_of_frontier tree 0 t4_389root t4_389jobs t4_389frontier t4_389all
theorem t4_390choices : plan2158.choices=[2,5,6,6].map (options 4 3) := by rfl


theorem t4_390part0 : t4_390jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_390frontier : t4_390root.frontier 0=t4_390jobs := by rfl
theorem t4_390all : t4_390jobs.all (Job.check tree)=true := by
  simp only [t4_390jobs,List.all_append,List.all_nil,t4_390part0,Bool.and_self]
theorem t4_390checked : Checked tree [2,5,6,6] := by
  refine ⟨plan2158,valid2158,t4_390choices,?_⟩
  exact check_of_frontier tree 0 t4_390root t4_390jobs t4_390frontier t4_390all
theorem t4_391choices : plan2159.choices=[2,5,6,7].map (options 4 3) := by rfl


theorem t4_391part0 : t4_391jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_391frontier : t4_391root.frontier 0=t4_391jobs := by rfl
theorem t4_391all : t4_391jobs.all (Job.check tree)=true := by
  simp only [t4_391jobs,List.all_append,List.all_nil,t4_391part0,Bool.and_self]
theorem t4_391checked : Checked tree [2,5,6,7] := by
  refine ⟨plan2159,valid2159,t4_391choices,?_⟩
  exact check_of_frontier tree 0 t4_391root t4_391jobs t4_391frontier t4_391all
theorem t4_392choices : plan2160.choices=[2,5,6,10].map (options 4 3) := by rfl


theorem t4_392part0 : t4_392jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_392frontier : t4_392root.frontier 0=t4_392jobs := by rfl
theorem t4_392all : t4_392jobs.all (Job.check tree)=true := by
  simp only [t4_392jobs,List.all_append,List.all_nil,t4_392part0,Bool.and_self]
theorem t4_392checked : Checked tree [2,5,6,10] := by
  refine ⟨plan2160,valid2160,t4_392choices,?_⟩
  exact check_of_frontier tree 0 t4_392root t4_392jobs t4_392frontier t4_392all
theorem t4_393choices : plan2161.choices=[2,5,7,7].map (options 4 3) := by rfl


theorem t4_393part0 : t4_393jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_393frontier : t4_393root.frontier 0=t4_393jobs := by rfl
theorem t4_393all : t4_393jobs.all (Job.check tree)=true := by
  simp only [t4_393jobs,List.all_append,List.all_nil,t4_393part0,Bool.and_self]
theorem t4_393checked : Checked tree [2,5,7,7] := by
  refine ⟨plan2161,valid2161,t4_393choices,?_⟩
  exact check_of_frontier tree 0 t4_393root t4_393jobs t4_393frontier t4_393all
theorem t4_394choices : plan1961.choices=[2,5,9,3].map (options 4 2) := by rfl


theorem t4_394part0 : t4_394jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_394frontier : t4_394root.frontier 0=t4_394jobs := by rfl
theorem t4_394all : t4_394jobs.all (Job.check tree)=true := by
  simp only [t4_394jobs,List.all_append,List.all_nil,t4_394part0,Bool.and_self]
theorem t4_394checked : Checked tree [2,5,9,3] := by
  refine ⟨plan1961,valid1961,t4_394choices,?_⟩
  exact check_of_frontier tree 0 t4_394root t4_394jobs t4_394frontier t4_394all
theorem t4_395choices : plan2162.choices=[2,5,9,6].map (options 4 3) := by rfl


theorem t4_395part0 : t4_395jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_395frontier : t4_395root.frontier 0=t4_395jobs := by rfl
theorem t4_395all : t4_395jobs.all (Job.check tree)=true := by
  simp only [t4_395jobs,List.all_append,List.all_nil,t4_395part0,Bool.and_self]
theorem t4_395checked : Checked tree [2,5,9,6] := by
  refine ⟨plan2162,valid2162,t4_395choices,?_⟩
  exact check_of_frontier tree 0 t4_395root t4_395jobs t4_395frontier t4_395all
theorem t4_396choices : plan2163.choices=[2,5,9,7].map (options 4 3) := by rfl


theorem t4_396part0 : t4_396jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_396frontier : t4_396root.frontier 0=t4_396jobs := by rfl
theorem t4_396all : t4_396jobs.all (Job.check tree)=true := by
  simp only [t4_396jobs,List.all_append,List.all_nil,t4_396part0,Bool.and_self]
theorem t4_396checked : Checked tree [2,5,9,7] := by
  refine ⟨plan2163,valid2163,t4_396choices,?_⟩
  exact check_of_frontier tree 0 t4_396root t4_396jobs t4_396frontier t4_396all
theorem t4_397choices : plan2164.choices=[2,5,9,9].map (options 4 3) := by rfl


theorem t4_397part0 : t4_397jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_397frontier : t4_397root.frontier 0=t4_397jobs := by rfl
theorem t4_397all : t4_397jobs.all (Job.check tree)=true := by
  simp only [t4_397jobs,List.all_append,List.all_nil,t4_397part0,Bool.and_self]
theorem t4_397checked : Checked tree [2,5,9,9] := by
  refine ⟨plan2164,valid2164,t4_397choices,?_⟩
  exact check_of_frontier tree 0 t4_397root t4_397jobs t4_397frontier t4_397all
theorem t4_398choices : plan2165.choices=[2,5,9,10].map (options 4 3) := by rfl


theorem t4_398part0 : t4_398jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_398frontier : t4_398root.frontier 0=t4_398jobs := by rfl
theorem t4_398all : t4_398jobs.all (Job.check tree)=true := by
  simp only [t4_398jobs,List.all_append,List.all_nil,t4_398part0,Bool.and_self]
theorem t4_398checked : Checked tree [2,5,9,10] := by
  refine ⟨plan2165,valid2165,t4_398choices,?_⟩
  exact check_of_frontier tree 0 t4_398root t4_398jobs t4_398frontier t4_398all
theorem t4_399choices : plan2166.choices=[2,5,10,7].map (options 4 3) := by rfl


theorem t4_399part0 : t4_399jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_399frontier : t4_399root.frontier 0=t4_399jobs := by rfl
theorem t4_399all : t4_399jobs.all (Job.check tree)=true := by
  simp only [t4_399jobs,List.all_append,List.all_nil,t4_399part0,Bool.and_self]
theorem t4_399checked : Checked tree [2,5,10,7] := by
  refine ⟨plan2166,valid2166,t4_399choices,?_⟩
  exact check_of_frontier tree 0 t4_399root t4_399jobs t4_399frontier t4_399all
theorem t4_400choices : plan2167.choices=[2,5,10,10].map (options 4 3) := by rfl


theorem t4_400part0 : t4_400jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_400frontier : t4_400root.frontier 0=t4_400jobs := by rfl
theorem t4_400all : t4_400jobs.all (Job.check tree)=true := by
  simp only [t4_400jobs,List.all_append,List.all_nil,t4_400part0,Bool.and_self]
theorem t4_400checked : Checked tree [2,5,10,10] := by
  refine ⟨plan2167,valid2167,t4_400choices,?_⟩
  exact check_of_frontier tree 0 t4_400root t4_400jobs t4_400frontier t4_400all
theorem t4_401choices : plan2168.choices=[2,6,6,6].map (options 4 3) := by rfl


theorem t4_401part0 : t4_401jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_401frontier : t4_401root.frontier 0=t4_401jobs := by rfl
theorem t4_401all : t4_401jobs.all (Job.check tree)=true := by
  simp only [t4_401jobs,List.all_append,List.all_nil,t4_401part0,Bool.and_self]
theorem t4_401checked : Checked tree [2,6,6,6] := by
  refine ⟨plan2168,valid2168,t4_401choices,?_⟩
  exact check_of_frontier tree 0 t4_401root t4_401jobs t4_401frontier t4_401all
theorem t4_402choices : plan2169.choices=[2,6,6,7].map (options 4 3) := by rfl


theorem t4_402part0 : t4_402jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_402frontier : t4_402root.frontier 0=t4_402jobs := by rfl
theorem t4_402all : t4_402jobs.all (Job.check tree)=true := by
  simp only [t4_402jobs,List.all_append,List.all_nil,t4_402part0,Bool.and_self]
theorem t4_402checked : Checked tree [2,6,6,7] := by
  refine ⟨plan2169,valid2169,t4_402choices,?_⟩
  exact check_of_frontier tree 0 t4_402root t4_402jobs t4_402frontier t4_402all
theorem t4_403choices : plan2170.choices=[2,6,6,10].map (options 4 3) := by rfl


theorem t4_403part0 : t4_403jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_403frontier : t4_403root.frontier 0=t4_403jobs := by rfl
theorem t4_403all : t4_403jobs.all (Job.check tree)=true := by
  simp only [t4_403jobs,List.all_append,List.all_nil,t4_403part0,Bool.and_self]
theorem t4_403checked : Checked tree [2,6,6,10] := by
  refine ⟨plan2170,valid2170,t4_403choices,?_⟩
  exact check_of_frontier tree 0 t4_403root t4_403jobs t4_403frontier t4_403all
theorem t4_404choices : plan2171.choices=[2,6,7,7].map (options 4 3) := by rfl


theorem t4_404part0 : t4_404jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_404frontier : t4_404root.frontier 0=t4_404jobs := by rfl
theorem t4_404all : t4_404jobs.all (Job.check tree)=true := by
  simp only [t4_404jobs,List.all_append,List.all_nil,t4_404part0,Bool.and_self]
theorem t4_404checked : Checked tree [2,6,7,7] := by
  refine ⟨plan2171,valid2171,t4_404choices,?_⟩
  exact check_of_frontier tree 0 t4_404root t4_404jobs t4_404frontier t4_404all
theorem t4_405choices : plan2172.choices=[2,6,10,7].map (options 4 3) := by rfl


theorem t4_405part0 : t4_405jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_405frontier : t4_405root.frontier 0=t4_405jobs := by rfl
theorem t4_405all : t4_405jobs.all (Job.check tree)=true := by
  simp only [t4_405jobs,List.all_append,List.all_nil,t4_405part0,Bool.and_self]
theorem t4_405checked : Checked tree [2,6,10,7] := by
  refine ⟨plan2172,valid2172,t4_405choices,?_⟩
  exact check_of_frontier tree 0 t4_405root t4_405jobs t4_405frontier t4_405all
theorem t4_406choices : plan2173.choices=[2,6,10,10].map (options 4 3) := by rfl


theorem t4_406part0 : t4_406jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_406frontier : t4_406root.frontier 0=t4_406jobs := by rfl
theorem t4_406all : t4_406jobs.all (Job.check tree)=true := by
  simp only [t4_406jobs,List.all_append,List.all_nil,t4_406part0,Bool.and_self]
theorem t4_406checked : Checked tree [2,6,10,10] := by
  refine ⟨plan2173,valid2173,t4_406choices,?_⟩
  exact check_of_frontier tree 0 t4_406root t4_406jobs t4_406frontier t4_406all
theorem t4_407choices : plan2174.choices=[2,7,7,7].map (options 4 3) := by rfl


theorem t4_407part0 : t4_407jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_407frontier : t4_407root.frontier 0=t4_407jobs := by rfl
theorem t4_407all : t4_407jobs.all (Job.check tree)=true := by
  simp only [t4_407jobs,List.all_append,List.all_nil,t4_407part0,Bool.and_self]
theorem t4_407checked : Checked tree [2,7,7,7] := by
  refine ⟨plan2174,valid2174,t4_407choices,?_⟩
  exact check_of_frontier tree 0 t4_407root t4_407jobs t4_407frontier t4_407all
theorem t4_408choices : plan1790.choices=[2,9,3,3].map (options 4 1) := by rfl


theorem t4_408part0 : t4_408jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_408frontier : t4_408root.frontier 0=t4_408jobs := by rfl
theorem t4_408all : t4_408jobs.all (Job.check tree)=true := by
  simp only [t4_408jobs,List.all_append,List.all_nil,t4_408part0,Bool.and_self]
theorem t4_408checked : Checked tree [2,9,3,3] := by
  refine ⟨plan1790,valid1790,t4_408choices,?_⟩
  exact check_of_frontier tree 0 t4_408root t4_408jobs t4_408frontier t4_408all
theorem t4_409choices : plan1962.choices=[2,9,3,6].map (options 4 2) := by rfl


theorem t4_409part0 : t4_409jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_409frontier : t4_409root.frontier 0=t4_409jobs := by rfl
theorem t4_409all : t4_409jobs.all (Job.check tree)=true := by
  simp only [t4_409jobs,List.all_append,List.all_nil,t4_409part0,Bool.and_self]
theorem t4_409checked : Checked tree [2,9,3,6] := by
  refine ⟨plan1962,valid1962,t4_409choices,?_⟩
  exact check_of_frontier tree 0 t4_409root t4_409jobs t4_409frontier t4_409all
theorem t4_410choices : plan1963.choices=[2,9,3,7].map (options 4 2) := by rfl


theorem t4_410part0 : t4_410jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_410frontier : t4_410root.frontier 0=t4_410jobs := by rfl
theorem t4_410all : t4_410jobs.all (Job.check tree)=true := by
  simp only [t4_410jobs,List.all_append,List.all_nil,t4_410part0,Bool.and_self]
theorem t4_410checked : Checked tree [2,9,3,7] := by
  refine ⟨plan1963,valid1963,t4_410choices,?_⟩
  exact check_of_frontier tree 0 t4_410root t4_410jobs t4_410frontier t4_410all
theorem t4_411choices : plan1964.choices=[2,9,3,10].map (options 4 2) := by rfl


theorem t4_411part0 : t4_411jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_411frontier : t4_411root.frontier 0=t4_411jobs := by rfl
theorem t4_411all : t4_411jobs.all (Job.check tree)=true := by
  simp only [t4_411jobs,List.all_append,List.all_nil,t4_411part0,Bool.and_self]
theorem t4_411checked : Checked tree [2,9,3,10] := by
  refine ⟨plan1964,valid1964,t4_411choices,?_⟩
  exact check_of_frontier tree 0 t4_411root t4_411jobs t4_411frontier t4_411all
theorem t4_412choices : plan2175.choices=[2,9,6,6].map (options 4 3) := by rfl


theorem t4_412part0 : t4_412jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_412frontier : t4_412root.frontier 0=t4_412jobs := by rfl
theorem t4_412all : t4_412jobs.all (Job.check tree)=true := by
  simp only [t4_412jobs,List.all_append,List.all_nil,t4_412part0,Bool.and_self]
theorem t4_412checked : Checked tree [2,9,6,6] := by
  refine ⟨plan2175,valid2175,t4_412choices,?_⟩
  exact check_of_frontier tree 0 t4_412root t4_412jobs t4_412frontier t4_412all
theorem t4_413choices : plan2176.choices=[2,9,6,7].map (options 4 3) := by rfl


theorem t4_413part0 : t4_413jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_413frontier : t4_413root.frontier 0=t4_413jobs := by rfl
theorem t4_413all : t4_413jobs.all (Job.check tree)=true := by
  simp only [t4_413jobs,List.all_append,List.all_nil,t4_413part0,Bool.and_self]
theorem t4_413checked : Checked tree [2,9,6,7] := by
  refine ⟨plan2176,valid2176,t4_413choices,?_⟩
  exact check_of_frontier tree 0 t4_413root t4_413jobs t4_413frontier t4_413all
theorem t4_414choices : plan2177.choices=[2,9,6,10].map (options 4 3) := by rfl


theorem t4_414part0 : t4_414jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_414frontier : t4_414root.frontier 0=t4_414jobs := by rfl
theorem t4_414all : t4_414jobs.all (Job.check tree)=true := by
  simp only [t4_414jobs,List.all_append,List.all_nil,t4_414part0,Bool.and_self]
theorem t4_414checked : Checked tree [2,9,6,10] := by
  refine ⟨plan2177,valid2177,t4_414choices,?_⟩
  exact check_of_frontier tree 0 t4_414root t4_414jobs t4_414frontier t4_414all
theorem t4_415choices : plan2178.choices=[2,9,7,7].map (options 4 3) := by rfl


theorem t4_415part0 : t4_415jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_415frontier : t4_415root.frontier 0=t4_415jobs := by rfl
theorem t4_415all : t4_415jobs.all (Job.check tree)=true := by
  simp only [t4_415jobs,List.all_append,List.all_nil,t4_415part0,Bool.and_self]
theorem t4_415checked : Checked tree [2,9,7,7] := by
  refine ⟨plan2178,valid2178,t4_415choices,?_⟩
  exact check_of_frontier tree 0 t4_415root t4_415jobs t4_415frontier t4_415all
theorem t4_416choices : plan1965.choices=[2,9,9,3].map (options 4 2) := by rfl


theorem t4_416part0 : t4_416jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_416frontier : t4_416root.frontier 0=t4_416jobs := by rfl
theorem t4_416all : t4_416jobs.all (Job.check tree)=true := by
  simp only [t4_416jobs,List.all_append,List.all_nil,t4_416part0,Bool.and_self]
theorem t4_416checked : Checked tree [2,9,9,3] := by
  refine ⟨plan1965,valid1965,t4_416choices,?_⟩
  exact check_of_frontier tree 0 t4_416root t4_416jobs t4_416frontier t4_416all
theorem t4_417choices : plan2179.choices=[2,9,9,6].map (options 4 3) := by rfl


theorem t4_417part0 : t4_417jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_417frontier : t4_417root.frontier 0=t4_417jobs := by rfl
theorem t4_417all : t4_417jobs.all (Job.check tree)=true := by
  simp only [t4_417jobs,List.all_append,List.all_nil,t4_417part0,Bool.and_self]
theorem t4_417checked : Checked tree [2,9,9,6] := by
  refine ⟨plan2179,valid2179,t4_417choices,?_⟩
  exact check_of_frontier tree 0 t4_417root t4_417jobs t4_417frontier t4_417all
theorem t4_418choices : plan2180.choices=[2,9,9,7].map (options 4 3) := by rfl


theorem t4_418part0 : t4_418jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_418frontier : t4_418root.frontier 0=t4_418jobs := by rfl
theorem t4_418all : t4_418jobs.all (Job.check tree)=true := by
  simp only [t4_418jobs,List.all_append,List.all_nil,t4_418part0,Bool.and_self]
theorem t4_418checked : Checked tree [2,9,9,7] := by
  refine ⟨plan2180,valid2180,t4_418choices,?_⟩
  exact check_of_frontier tree 0 t4_418root t4_418jobs t4_418frontier t4_418all
theorem t4_419choices : plan2181.choices=[2,9,9,9].map (options 4 3) := by rfl


theorem t4_419part0 : t4_419jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_419frontier : t4_419root.frontier 0=t4_419jobs := by rfl
theorem t4_419all : t4_419jobs.all (Job.check tree)=true := by
  simp only [t4_419jobs,List.all_append,List.all_nil,t4_419part0,Bool.and_self]
theorem t4_419checked : Checked tree [2,9,9,9] := by
  refine ⟨plan2181,valid2181,t4_419choices,?_⟩
  exact check_of_frontier tree 0 t4_419root t4_419jobs t4_419frontier t4_419all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks002 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_372checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_373checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_374checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_375checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_376checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_377checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_378checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_379checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_380checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_381checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_360checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_382checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_383checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_384checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_385checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_386checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_387checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_388checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_389checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_390checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_391checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_361checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_392checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_393checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_394checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_395checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_396checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_397checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_398checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_399checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_400checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_401checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_362checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_402checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_403checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_404checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_405checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_406checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_407checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_408checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_409checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_410checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_411checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_363checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_412checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_413checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_414checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_415checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_416checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_417checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_418checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_419checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_364checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_365checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_366checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_367checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_368checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_369checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_370checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_371checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_359checked⟩
