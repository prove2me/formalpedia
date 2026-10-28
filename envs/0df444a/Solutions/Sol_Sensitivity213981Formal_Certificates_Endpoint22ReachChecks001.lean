-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks001
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:02:20.674004+00:00
-- url     : https://prove2.me/submissions/329b3b8b-c629-4434-b83a-b2fba26e0778

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks001
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
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans019
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans020
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans021
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





















































































































theorem valid59 : plan59.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid60 : plan60.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid61 : plan61.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid62 : plan62.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid63 : plan63.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid64 : plan64.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid65 : plan65.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid66 : plan66.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid67 : plan67.Valid := valid_step _ _ _ valid0 (by decide +kernel)



theorem valid69 : plan69.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid70 : plan70.Valid := valid_step _ _ _ valid0 (by decide +kernel)

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

























































































theorem valid333 : plan333.Valid := valid_step _ _ _ valid59 (by decide +kernel)

theorem valid334 : plan334.Valid := valid_step _ _ _ valid60 (by decide +kernel)

theorem valid335 : plan335.Valid := valid_step _ _ _ valid60 (by decide +kernel)







theorem valid339 : plan339.Valid := valid_step _ _ _ valid61 (by decide +kernel)

theorem valid340 : plan340.Valid := valid_step _ _ _ valid62 (by decide +kernel)

theorem valid341 : plan341.Valid := valid_step _ _ _ valid63 (by decide +kernel)

theorem valid342 : plan342.Valid := valid_step _ _ _ valid64 (by decide +kernel)

theorem valid343 : plan343.Valid := valid_step _ _ _ valid65 (by decide +kernel)

theorem valid344 : plan344.Valid := valid_step _ _ _ valid66 (by decide +kernel)

theorem valid345 : plan345.Valid := valid_step _ _ _ valid67 (by decide +kernel)

theorem valid346 : plan346.Valid := valid_step _ _ _ valid62 (by decide +kernel)

theorem valid347 : plan347.Valid := valid_step _ _ _ valid64 (by decide +kernel)

theorem valid348 : plan348.Valid := valid_step _ _ _ valid65 (by decide +kernel)

theorem valid349 : plan349.Valid := valid_step _ _ _ valid67 (by decide +kernel)



theorem valid351 : plan351.Valid := valid_step _ _ _ valid62 (by decide +kernel)









theorem valid356 : plan356.Valid := valid_step _ _ _ valid70 (by decide +kernel)

theorem valid357 : plan357.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid358 : plan358.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid359 : plan359.Valid := valid_step _ _ _ valid73 (by decide +kernel)

theorem valid360 : plan360.Valid := valid_step _ _ _ valid74 (by decide +kernel)



theorem valid362 : plan362.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid363 : plan363.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid364 : plan364.Valid := valid_step _ _ _ valid74 (by decide +kernel)

theorem valid365 : plan365.Valid := valid_step _ _ _ valid69 (by decide +kernel)







theorem valid369 : plan369.Valid := valid_step _ _ _ valid69 (by decide +kernel)

theorem valid370 : plan370.Valid := valid_step _ _ _ valid70 (by decide +kernel)

theorem valid371 : plan371.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid372 : plan372.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid373 : plan373.Valid := valid_step _ _ _ valid73 (by decide +kernel)

theorem valid374 : plan374.Valid := valid_step _ _ _ valid74 (by decide +kernel)

theorem valid375 : plan375.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid376 : plan376.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid377 : plan377.Valid := valid_step _ _ _ valid74 (by decide +kernel)

theorem valid378 : plan378.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid379 : plan379.Valid := valid_step _ _ _ valid69 (by decide +kernel)







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





















































































theorem valid907 : plan907.Valid := valid_step _ _ _ valid333 (by decide +kernel)

theorem valid908 : plan908.Valid := valid_step _ _ _ valid334 (by decide +kernel)

theorem valid909 : plan909.Valid := valid_step _ _ _ valid335 (by decide +kernel)

theorem valid910 : plan910.Valid := valid_step _ _ _ valid335 (by decide +kernel)



































theorem valid928 : plan928.Valid := valid_step _ _ _ valid341 (by decide +kernel)

theorem valid929 : plan929.Valid := valid_step _ _ _ valid342 (by decide +kernel)

theorem valid930 : plan930.Valid := valid_step _ _ _ valid343 (by decide +kernel)

theorem valid931 : plan931.Valid := valid_step _ _ _ valid344 (by decide +kernel)

theorem valid932 : plan932.Valid := valid_step _ _ _ valid345 (by decide +kernel)



theorem valid934 : plan934.Valid := valid_step _ _ _ valid347 (by decide +kernel)

theorem valid935 : plan935.Valid := valid_step _ _ _ valid348 (by decide +kernel)

theorem valid936 : plan936.Valid := valid_step _ _ _ valid349 (by decide +kernel)

theorem valid937 : plan937.Valid := valid_step _ _ _ valid351 (by decide +kernel)





theorem valid940 : plan940.Valid := valid_step _ _ _ valid347 (by decide +kernel)

theorem valid941 : plan941.Valid := valid_step _ _ _ valid348 (by decide +kernel)

theorem valid942 : plan942.Valid := valid_step _ _ _ valid349 (by decide +kernel)

theorem valid943 : plan943.Valid := valid_step _ _ _ valid339 (by decide +kernel)

theorem valid944 : plan944.Valid := valid_step _ _ _ valid340 (by decide +kernel)

theorem valid945 : plan945.Valid := valid_step _ _ _ valid346 (by decide +kernel)

theorem valid946 : plan946.Valid := valid_step _ _ _ valid346 (by decide +kernel)

theorem valid947 : plan947.Valid := valid_step _ _ _ valid339 (by decide +kernel)

theorem valid948 : plan948.Valid := valid_step _ _ _ valid340 (by decide +kernel)

theorem valid949 : plan949.Valid := valid_step _ _ _ valid346 (by decide +kernel)

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





















































































































































theorem valid1707 : plan1707.Valid := valid_step _ _ _ valid910 (by decide +kernel)

theorem valid1708 : plan1708.Valid := valid_step _ _ _ valid907 (by decide +kernel)

theorem valid1709 : plan1709.Valid := valid_step _ _ _ valid908 (by decide +kernel)

theorem valid1710 : plan1710.Valid := valid_step _ _ _ valid909 (by decide +kernel)




































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



















theorem valid399 : plan399.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid400 : plan400.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid401 : plan401.Valid := valid_step _ _ _ valid80 (by decide +kernel)



theorem valid403 : plan403.Valid := valid_step _ _ _ valid76 (by decide +kernel)

theorem valid404 : plan404.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid405 : plan405.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid406 : plan406.Valid := valid_step _ _ _ valid79 (by decide +kernel)

theorem valid407 : plan407.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid408 : plan408.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid409 : plan409.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid410 : plan410.Valid := valid_step _ _ _ valid80 (by decide +kernel)

theorem valid411 : plan411.Valid := valid_step _ _ _ valid78 (by decide +kernel)



theorem valid413 : plan413.Valid := valid_step _ _ _ valid77 (by decide +kernel)

theorem valid414 : plan414.Valid := valid_step _ _ _ valid78 (by decide +kernel)

theorem valid415 : plan415.Valid := valid_step _ _ _ valid80 (by decide +kernel)



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









































theorem valid981 : plan981.Valid := valid_step _ _ _ valid370 (by decide +kernel)

theorem valid982 : plan982.Valid := valid_step _ _ _ valid371 (by decide +kernel)

theorem valid983 : plan983.Valid := valid_step _ _ _ valid372 (by decide +kernel)

theorem valid984 : plan984.Valid := valid_step _ _ _ valid373 (by decide +kernel)

theorem valid985 : plan985.Valid := valid_step _ _ _ valid374 (by decide +kernel)













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





theorem valid1008 : plan1008.Valid := valid_step _ _ _ valid356 (by decide +kernel)

theorem valid1009 : plan1009.Valid := valid_step _ _ _ valid357 (by decide +kernel)

theorem valid1010 : plan1010.Valid := valid_step _ _ _ valid358 (by decide +kernel)

theorem valid1011 : plan1011.Valid := valid_step _ _ _ valid359 (by decide +kernel)

theorem valid1012 : plan1012.Valid := valid_step _ _ _ valid360 (by decide +kernel)



theorem valid1014 : plan1014.Valid := valid_step _ _ _ valid362 (by decide +kernel)

theorem valid1015 : plan1015.Valid := valid_step _ _ _ valid363 (by decide +kernel)

theorem valid1016 : plan1016.Valid := valid_step _ _ _ valid364 (by decide +kernel)

theorem valid1017 : plan1017.Valid := valid_step _ _ _ valid365 (by decide +kernel)

theorem valid1018 : plan1018.Valid := valid_step _ _ _ valid369 (by decide +kernel)

theorem valid1019 : plan1019.Valid := valid_step _ _ _ valid379 (by decide +kernel)

theorem valid1020 : plan1020.Valid := valid_step _ _ _ valid383 (by decide +kernel)



theorem valid1022 : plan1022.Valid := valid_step _ _ _ valid362 (by decide +kernel)

theorem valid1023 : plan1023.Valid := valid_step _ _ _ valid363 (by decide +kernel)

theorem valid1024 : plan1024.Valid := valid_step _ _ _ valid364 (by decide +kernel)

theorem valid1025 : plan1025.Valid := valid_step _ _ _ valid369 (by decide +kernel)

theorem valid1026 : plan1026.Valid := valid_step _ _ _ valid383 (by decide +kernel)





theorem valid1029 : plan1029.Valid := valid_step _ _ _ valid356 (by decide +kernel)

theorem valid1030 : plan1030.Valid := valid_step _ _ _ valid357 (by decide +kernel)

theorem valid1031 : plan1031.Valid := valid_step _ _ _ valid358 (by decide +kernel)

theorem valid1032 : plan1032.Valid := valid_step _ _ _ valid359 (by decide +kernel)

theorem valid1033 : plan1033.Valid := valid_step _ _ _ valid360 (by decide +kernel)



theorem valid1035 : plan1035.Valid := valid_step _ _ _ valid362 (by decide +kernel)

theorem valid1036 : plan1036.Valid := valid_step _ _ _ valid363 (by decide +kernel)

theorem valid1037 : plan1037.Valid := valid_step _ _ _ valid364 (by decide +kernel)

theorem valid1038 : plan1038.Valid := valid_step _ _ _ valid369 (by decide +kernel)

theorem valid1039 : plan1039.Valid := valid_step _ _ _ valid379 (by decide +kernel)

theorem valid1040 : plan1040.Valid := valid_step _ _ _ valid383 (by decide +kernel)



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









































































theorem valid1765 : plan1765.Valid := valid_step _ _ _ valid940 (by decide +kernel)

theorem valid1766 : plan1766.Valid := valid_step _ _ _ valid941 (by decide +kernel)

theorem valid1767 : plan1767.Valid := valid_step _ _ _ valid942 (by decide +kernel)

theorem valid1768 : plan1768.Valid := valid_step _ _ _ valid943 (by decide +kernel)

theorem valid1769 : plan1769.Valid := valid_step _ _ _ valid944 (by decide +kernel)

theorem valid1770 : plan1770.Valid := valid_step _ _ _ valid945 (by decide +kernel)

theorem valid1771 : plan1771.Valid := valid_step _ _ _ valid946 (by decide +kernel)

theorem valid1772 : plan1772.Valid := valid_step _ _ _ valid947 (by decide +kernel)

theorem valid1773 : plan1773.Valid := valid_step _ _ _ valid948 (by decide +kernel)

theorem valid1774 : plan1774.Valid := valid_step _ _ _ valid949 (by decide +kernel)

theorem valid1775 : plan1775.Valid := valid_step _ _ _ valid950 (by decide +kernel)

theorem valid1776 : plan1776.Valid := valid_step _ _ _ valid928 (by decide +kernel)

theorem valid1777 : plan1777.Valid := valid_step _ _ _ valid929 (by decide +kernel)

theorem valid1778 : plan1778.Valid := valid_step _ _ _ valid930 (by decide +kernel)

theorem valid1779 : plan1779.Valid := valid_step _ _ _ valid931 (by decide +kernel)

theorem valid1780 : plan1780.Valid := valid_step _ _ _ valid932 (by decide +kernel)

theorem valid1781 : plan1781.Valid := valid_step _ _ _ valid934 (by decide +kernel)

theorem valid1782 : plan1782.Valid := valid_step _ _ _ valid935 (by decide +kernel)

theorem valid1783 : plan1783.Valid := valid_step _ _ _ valid936 (by decide +kernel)

theorem valid1784 : plan1784.Valid := valid_step _ _ _ valid937 (by decide +kernel)
















































































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









































































































































theorem valid1893 : plan1893.Valid := valid_step _ _ _ valid992 (by decide +kernel)

theorem valid1894 : plan1894.Valid := valid_step _ _ _ valid993 (by decide +kernel)

theorem valid1895 : plan1895.Valid := valid_step _ _ _ valid994 (by decide +kernel)

theorem valid1896 : plan1896.Valid := valid_step _ _ _ valid995 (by decide +kernel)

theorem valid1897 : plan1897.Valid := valid_step _ _ _ valid996 (by decide +kernel)

theorem valid1898 : plan1898.Valid := valid_step _ _ _ valid1000 (by decide +kernel)

theorem valid1899 : plan1899.Valid := valid_step _ _ _ valid1001 (by decide +kernel)

theorem valid1900 : plan1900.Valid := valid_step _ _ _ valid1002 (by decide +kernel)

theorem valid1901 : plan1901.Valid := valid_step _ _ _ valid1003 (by decide +kernel)

theorem valid1902 : plan1902.Valid := valid_step _ _ _ valid1004 (by decide +kernel)

theorem valid1903 : plan1903.Valid := valid_step _ _ _ valid1005 (by decide +kernel)

theorem valid1904 : plan1904.Valid := valid_step _ _ _ valid1008 (by decide +kernel)

theorem valid1905 : plan1905.Valid := valid_step _ _ _ valid1009 (by decide +kernel)

theorem valid1906 : plan1906.Valid := valid_step _ _ _ valid1010 (by decide +kernel)

theorem valid1907 : plan1907.Valid := valid_step _ _ _ valid1011 (by decide +kernel)

theorem valid1908 : plan1908.Valid := valid_step _ _ _ valid1012 (by decide +kernel)

theorem valid1909 : plan1909.Valid := valid_step _ _ _ valid1014 (by decide +kernel)

theorem valid1910 : plan1910.Valid := valid_step _ _ _ valid1015 (by decide +kernel)

theorem valid1911 : plan1911.Valid := valid_step _ _ _ valid1016 (by decide +kernel)

theorem valid1912 : plan1912.Valid := valid_step _ _ _ valid1017 (by decide +kernel)

theorem valid1913 : plan1913.Valid := valid_step _ _ _ valid1018 (by decide +kernel)

theorem valid1914 : plan1914.Valid := valid_step _ _ _ valid1019 (by decide +kernel)

theorem valid1915 : plan1915.Valid := valid_step _ _ _ valid1020 (by decide +kernel)

theorem valid1916 : plan1916.Valid := valid_step _ _ _ valid1022 (by decide +kernel)

theorem valid1917 : plan1917.Valid := valid_step _ _ _ valid1023 (by decide +kernel)

theorem valid1918 : plan1918.Valid := valid_step _ _ _ valid1024 (by decide +kernel)

theorem valid1919 : plan1919.Valid := valid_step _ _ _ valid1025 (by decide +kernel)

theorem valid1920 : plan1920.Valid := valid_step _ _ _ valid1026 (by decide +kernel)
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







































theorem valid1076 : plan1076.Valid := valid_step _ _ _ valid399 (by decide +kernel)

theorem valid1077 : plan1077.Valid := valid_step _ _ _ valid400 (by decide +kernel)

theorem valid1078 : plan1078.Valid := valid_step _ _ _ valid401 (by decide +kernel)



theorem valid1080 : plan1080.Valid := valid_step _ _ _ valid403 (by decide +kernel)

theorem valid1081 : plan1081.Valid := valid_step _ _ _ valid404 (by decide +kernel)

theorem valid1082 : plan1082.Valid := valid_step _ _ _ valid405 (by decide +kernel)

theorem valid1083 : plan1083.Valid := valid_step _ _ _ valid406 (by decide +kernel)

theorem valid1084 : plan1084.Valid := valid_step _ _ _ valid407 (by decide +kernel)

theorem valid1085 : plan1085.Valid := valid_step _ _ _ valid408 (by decide +kernel)

theorem valid1086 : plan1086.Valid := valid_step _ _ _ valid409 (by decide +kernel)

theorem valid1087 : plan1087.Valid := valid_step _ _ _ valid410 (by decide +kernel)

theorem valid1088 : plan1088.Valid := valid_step _ _ _ valid411 (by decide +kernel)



theorem valid1090 : plan1090.Valid := valid_step _ _ _ valid413 (by decide +kernel)

theorem valid1091 : plan1091.Valid := valid_step _ _ _ valid414 (by decide +kernel)

theorem valid1092 : plan1092.Valid := valid_step _ _ _ valid415 (by decide +kernel)



theorem valid1094 : plan1094.Valid := valid_step _ _ _ valid417 (by decide +kernel)

theorem valid1095 : plan1095.Valid := valid_step _ _ _ valid418 (by decide +kernel)

theorem valid1096 : plan1096.Valid := valid_step _ _ _ valid419 (by decide +kernel)

theorem valid1097 : plan1097.Valid := valid_step _ _ _ valid420 (by decide +kernel)

theorem valid1098 : plan1098.Valid := valid_step _ _ _ valid421 (by decide +kernel)

theorem valid1099 : plan1099.Valid := valid_step _ _ _ valid422 (by decide +kernel)









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



















theorem valid1136 : plan1136.Valid := valid_step _ _ _ valid403 (by decide +kernel)

theorem valid1137 : plan1137.Valid := valid_step _ _ _ valid404 (by decide +kernel)

theorem valid1138 : plan1138.Valid := valid_step _ _ _ valid405 (by decide +kernel)

theorem valid1139 : plan1139.Valid := valid_step _ _ _ valid406 (by decide +kernel)

theorem valid1140 : plan1140.Valid := valid_step _ _ _ valid407 (by decide +kernel)

theorem valid1141 : plan1141.Valid := valid_step _ _ _ valid408 (by decide +kernel)

theorem valid1142 : plan1142.Valid := valid_step _ _ _ valid409 (by decide +kernel)

theorem valid1143 : plan1143.Valid := valid_step _ _ _ valid410 (by decide +kernel)

theorem valid1144 : plan1144.Valid := valid_step _ _ _ valid411 (by decide +kernel)



theorem valid1146 : plan1146.Valid := valid_step _ _ _ valid413 (by decide +kernel)

theorem valid1147 : plan1147.Valid := valid_step _ _ _ valid414 (by decide +kernel)

theorem valid1148 : plan1148.Valid := valid_step _ _ _ valid415 (by decide +kernel)



theorem valid1150 : plan1150.Valid := valid_step _ _ _ valid417 (by decide +kernel)

theorem valid1151 : plan1151.Valid := valid_step _ _ _ valid418 (by decide +kernel)

theorem valid1152 : plan1152.Valid := valid_step _ _ _ valid419 (by decide +kernel)
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

theorem valid1153 : plan1153.Valid := valid_step _ _ _ valid420 (by decide +kernel)

theorem valid1154 : plan1154.Valid := valid_step _ _ _ valid421 (by decide +kernel)

theorem valid1155 : plan1155.Valid := valid_step _ _ _ valid422 (by decide +kernel)







theorem valid1159 : plan1159.Valid := valid_step _ _ _ valid408 (by decide +kernel)

theorem valid1160 : plan1160.Valid := valid_step _ _ _ valid409 (by decide +kernel)

theorem valid1161 : plan1161.Valid := valid_step _ _ _ valid410 (by decide +kernel)

theorem valid1162 : plan1162.Valid := valid_step _ _ _ valid411 (by decide +kernel)



theorem valid1164 : plan1164.Valid := valid_step _ _ _ valid417 (by decide +kernel)

theorem valid1165 : plan1165.Valid := valid_step _ _ _ valid418 (by decide +kernel)

theorem valid1166 : plan1166.Valid := valid_step _ _ _ valid419 (by decide +kernel)

theorem valid1167 : plan1167.Valid := valid_step _ _ _ valid420 (by decide +kernel)

theorem valid1168 : plan1168.Valid := valid_step _ _ _ valid421 (by decide +kernel)

theorem valid1169 : plan1169.Valid := valid_step _ _ _ valid422 (by decide +kernel)

theorem valid1170 : plan1170.Valid := valid_step _ _ _ valid411 (by decide +kernel)

theorem valid1171 : plan1171.Valid := valid_step _ _ _ valid421 (by decide +kernel)

theorem valid1172 : plan1172.Valid := valid_step _ _ _ valid422 (by decide +kernel)
























































































































































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





























































































































theorem valid2079 : plan2079.Valid := valid_step _ _ _ valid1076 (by decide +kernel)

theorem valid2080 : plan2080.Valid := valid_step _ _ _ valid1077 (by decide +kernel)

theorem valid2081 : plan2081.Valid := valid_step _ _ _ valid1078 (by decide +kernel)

theorem valid2082 : plan2082.Valid := valid_step _ _ _ valid1080 (by decide +kernel)

theorem valid2083 : plan2083.Valid := valid_step _ _ _ valid1081 (by decide +kernel)

theorem valid2084 : plan2084.Valid := valid_step _ _ _ valid1082 (by decide +kernel)

theorem valid2085 : plan2085.Valid := valid_step _ _ _ valid1083 (by decide +kernel)

theorem valid2086 : plan2086.Valid := valid_step _ _ _ valid1084 (by decide +kernel)

theorem valid2087 : plan2087.Valid := valid_step _ _ _ valid1085 (by decide +kernel)

theorem valid2088 : plan2088.Valid := valid_step _ _ _ valid1086 (by decide +kernel)

theorem valid2089 : plan2089.Valid := valid_step _ _ _ valid1087 (by decide +kernel)

theorem valid2090 : plan2090.Valid := valid_step _ _ _ valid1088 (by decide +kernel)

theorem valid2091 : plan2091.Valid := valid_step _ _ _ valid1090 (by decide +kernel)

theorem valid2092 : plan2092.Valid := valid_step _ _ _ valid1091 (by decide +kernel)

theorem valid2093 : plan2093.Valid := valid_step _ _ _ valid1092 (by decide +kernel)

theorem valid2094 : plan2094.Valid := valid_step _ _ _ valid1094 (by decide +kernel)

theorem valid2095 : plan2095.Valid := valid_step _ _ _ valid1095 (by decide +kernel)

theorem valid2096 : plan2096.Valid := valid_step _ _ _ valid1096 (by decide +kernel)

theorem valid2097 : plan2097.Valid := valid_step _ _ _ valid1097 (by decide +kernel)

theorem valid2098 : plan2098.Valid := valid_step _ _ _ valid1098 (by decide +kernel)

theorem valid2099 : plan2099.Valid := valid_step _ _ _ valid1099 (by decide +kernel)

theorem valid2100 : plan2100.Valid := valid_step _ _ _ valid1104 (by decide +kernel)

theorem valid2101 : plan2101.Valid := valid_step _ _ _ valid1105 (by decide +kernel)

theorem valid2102 : plan2102.Valid := valid_step _ _ _ valid1106 (by decide +kernel)

theorem valid2103 : plan2103.Valid := valid_step _ _ _ valid1107 (by decide +kernel)

theorem valid2104 : plan2104.Valid := valid_step _ _ _ valid1108 (by decide +kernel)

theorem valid2105 : plan2105.Valid := valid_step _ _ _ valid1109 (by decide +kernel)

theorem valid2106 : plan2106.Valid := valid_step _ _ _ valid1110 (by decide +kernel)

theorem valid2107 : plan2107.Valid := valid_step _ _ _ valid1111 (by decide +kernel)

theorem valid2108 : plan2108.Valid := valid_step _ _ _ valid1112 (by decide +kernel)

theorem valid2109 : plan2109.Valid := valid_step _ _ _ valid1114 (by decide +kernel)

theorem valid2110 : plan2110.Valid := valid_step _ _ _ valid1115 (by decide +kernel)

theorem valid2111 : plan2111.Valid := valid_step _ _ _ valid1116 (by decide +kernel)

theorem valid2112 : plan2112.Valid := valid_step _ _ _ valid1117 (by decide +kernel)
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

theorem valid1921 : plan1921.Valid := valid_step _ _ _ valid1029 (by decide +kernel)

theorem valid1922 : plan1922.Valid := valid_step _ _ _ valid1030 (by decide +kernel)

theorem valid1923 : plan1923.Valid := valid_step _ _ _ valid1031 (by decide +kernel)

theorem valid1924 : plan1924.Valid := valid_step _ _ _ valid1032 (by decide +kernel)

theorem valid1925 : plan1925.Valid := valid_step _ _ _ valid1033 (by decide +kernel)

theorem valid1926 : plan1926.Valid := valid_step _ _ _ valid1035 (by decide +kernel)

theorem valid1927 : plan1927.Valid := valid_step _ _ _ valid1036 (by decide +kernel)

theorem valid1928 : plan1928.Valid := valid_step _ _ _ valid1037 (by decide +kernel)

theorem valid1929 : plan1929.Valid := valid_step _ _ _ valid1038 (by decide +kernel)

theorem valid1930 : plan1930.Valid := valid_step _ _ _ valid1039 (by decide +kernel)

theorem valid1931 : plan1931.Valid := valid_step _ _ _ valid1040 (by decide +kernel)

theorem valid1932 : plan1932.Valid := valid_step _ _ _ valid1042 (by decide +kernel)

theorem valid1933 : plan1933.Valid := valid_step _ _ _ valid1043 (by decide +kernel)

theorem valid1934 : plan1934.Valid := valid_step _ _ _ valid1044 (by decide +kernel)

theorem valid1935 : plan1935.Valid := valid_step _ _ _ valid1045 (by decide +kernel)

theorem valid1936 : plan1936.Valid := valid_step _ _ _ valid981 (by decide +kernel)

theorem valid1937 : plan1937.Valid := valid_step _ _ _ valid982 (by decide +kernel)

theorem valid1938 : plan1938.Valid := valid_step _ _ _ valid983 (by decide +kernel)

theorem valid1939 : plan1939.Valid := valid_step _ _ _ valid984 (by decide +kernel)

theorem valid1940 : plan1940.Valid := valid_step _ _ _ valid985 (by decide +kernel)
























































































































































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

theorem valid2113 : plan2113.Valid := valid_step _ _ _ valid1118 (by decide +kernel)

theorem valid2114 : plan2114.Valid := valid_step _ _ _ valid1119 (by decide +kernel)

theorem valid2115 : plan2115.Valid := valid_step _ _ _ valid1120 (by decide +kernel)

theorem valid2116 : plan2116.Valid := valid_step _ _ _ valid1121 (by decide +kernel)

theorem valid2117 : plan2117.Valid := valid_step _ _ _ valid1122 (by decide +kernel)

theorem valid2118 : plan2118.Valid := valid_step _ _ _ valid1123 (by decide +kernel)

theorem valid2119 : plan2119.Valid := valid_step _ _ _ valid1124 (by decide +kernel)

theorem valid2120 : plan2120.Valid := valid_step _ _ _ valid1125 (by decide +kernel)

theorem valid2121 : plan2121.Valid := valid_step _ _ _ valid1126 (by decide +kernel)

theorem valid2122 : plan2122.Valid := valid_step _ _ _ valid1136 (by decide +kernel)

theorem valid2123 : plan2123.Valid := valid_step _ _ _ valid1137 (by decide +kernel)

theorem valid2124 : plan2124.Valid := valid_step _ _ _ valid1138 (by decide +kernel)

theorem valid2125 : plan2125.Valid := valid_step _ _ _ valid1139 (by decide +kernel)

theorem valid2126 : plan2126.Valid := valid_step _ _ _ valid1140 (by decide +kernel)

theorem valid2127 : plan2127.Valid := valid_step _ _ _ valid1141 (by decide +kernel)

theorem valid2128 : plan2128.Valid := valid_step _ _ _ valid1142 (by decide +kernel)

theorem valid2129 : plan2129.Valid := valid_step _ _ _ valid1143 (by decide +kernel)

theorem valid2130 : plan2130.Valid := valid_step _ _ _ valid1144 (by decide +kernel)

theorem valid2131 : plan2131.Valid := valid_step _ _ _ valid1146 (by decide +kernel)

theorem valid2132 : plan2132.Valid := valid_step _ _ _ valid1147 (by decide +kernel)

theorem valid2133 : plan2133.Valid := valid_step _ _ _ valid1148 (by decide +kernel)

theorem valid2134 : plan2134.Valid := valid_step _ _ _ valid1150 (by decide +kernel)

theorem valid2135 : plan2135.Valid := valid_step _ _ _ valid1151 (by decide +kernel)

theorem valid2136 : plan2136.Valid := valid_step _ _ _ valid1152 (by decide +kernel)

theorem valid2137 : plan2137.Valid := valid_step _ _ _ valid1153 (by decide +kernel)

theorem valid2138 : plan2138.Valid := valid_step _ _ _ valid1154 (by decide +kernel)

theorem valid2139 : plan2139.Valid := valid_step _ _ _ valid1155 (by decide +kernel)

theorem valid2140 : plan2140.Valid := valid_step _ _ _ valid1159 (by decide +kernel)

theorem valid2141 : plan2141.Valid := valid_step _ _ _ valid1160 (by decide +kernel)

theorem valid2142 : plan2142.Valid := valid_step _ _ _ valid1161 (by decide +kernel)

theorem valid2143 : plan2143.Valid := valid_step _ _ _ valid1162 (by decide +kernel)

theorem valid2144 : plan2144.Valid := valid_step _ _ _ valid1164 (by decide +kernel)

theorem valid2145 : plan2145.Valid := valid_step _ _ _ valid1165 (by decide +kernel)

theorem valid2146 : plan2146.Valid := valid_step _ _ _ valid1166 (by decide +kernel)

theorem valid2147 : plan2147.Valid := valid_step _ _ _ valid1167 (by decide +kernel)

theorem valid2148 : plan2148.Valid := valid_step _ _ _ valid1168 (by decide +kernel)

theorem valid2149 : plan2149.Valid := valid_step _ _ _ valid1169 (by decide +kernel)

theorem valid2150 : plan2150.Valid := valid_step _ _ _ valid1170 (by decide +kernel)

theorem valid2151 : plan2151.Valid := valid_step _ _ _ valid1171 (by decide +kernel)

theorem valid2152 : plan2152.Valid := valid_step _ _ _ valid1172 (by decide +kernel)
















































































































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
theorem t4_213choices : plan1893.choices=[1,2,9,7].map (options 4 2) := by rfl


theorem t4_213part0 : t4_213jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_213frontier : t4_213root.frontier 0=t4_213jobs := by rfl
theorem t4_213all : t4_213jobs.all (Job.check tree)=true := by
  simp only [t4_213jobs,List.all_append,List.all_nil,t4_213part0,Bool.and_self]
theorem t4_213checked : Checked tree [1,2,9,7] := by
  refine ⟨plan1893,valid1893,t4_213choices,?_⟩
  exact check_of_frontier tree 0 t4_213root t4_213jobs t4_213frontier t4_213all
theorem t4_214choices : plan1894.choices=[1,2,9,9].map (options 4 2) := by rfl


theorem t4_214part0 : t4_214jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_214frontier : t4_214root.frontier 0=t4_214jobs := by rfl
theorem t4_214all : t4_214jobs.all (Job.check tree)=true := by
  simp only [t4_214jobs,List.all_append,List.all_nil,t4_214part0,Bool.and_self]
theorem t4_214checked : Checked tree [1,2,9,9] := by
  refine ⟨plan1894,valid1894,t4_214choices,?_⟩
  exact check_of_frontier tree 0 t4_214root t4_214jobs t4_214frontier t4_214all
theorem t4_215choices : plan1895.choices=[1,2,9,10].map (options 4 2) := by rfl


theorem t4_215part0 : t4_215jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_215frontier : t4_215root.frontier 0=t4_215jobs := by rfl
theorem t4_215all : t4_215jobs.all (Job.check tree)=true := by
  simp only [t4_215jobs,List.all_append,List.all_nil,t4_215part0,Bool.and_self]
theorem t4_215checked : Checked tree [1,2,9,10] := by
  refine ⟨plan1895,valid1895,t4_215choices,?_⟩
  exact check_of_frontier tree 0 t4_215root t4_215jobs t4_215frontier t4_215all
theorem t4_216choices : plan1896.choices=[1,2,10,7].map (options 4 2) := by rfl


theorem t4_216part0 : t4_216jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_216frontier : t4_216root.frontier 0=t4_216jobs := by rfl
theorem t4_216all : t4_216jobs.all (Job.check tree)=true := by
  simp only [t4_216jobs,List.all_append,List.all_nil,t4_216part0,Bool.and_self]
theorem t4_216checked : Checked tree [1,2,10,7] := by
  refine ⟨plan1896,valid1896,t4_216choices,?_⟩
  exact check_of_frontier tree 0 t4_216root t4_216jobs t4_216frontier t4_216all
theorem t4_217choices : plan1897.choices=[1,2,10,10].map (options 4 2) := by rfl


theorem t4_217part0 : t4_217jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_217frontier : t4_217root.frontier 0=t4_217jobs := by rfl
theorem t4_217all : t4_217jobs.all (Job.check tree)=true := by
  simp only [t4_217jobs,List.all_append,List.all_nil,t4_217part0,Bool.and_self]
theorem t4_217checked : Checked tree [1,2,10,10] := by
  refine ⟨plan1897,valid1897,t4_217choices,?_⟩
  exact check_of_frontier tree 0 t4_217root t4_217jobs t4_217frontier t4_217all
theorem t4_218choices : plan1707.choices=[1,3,3,3].map (options 4 0) := by rfl


theorem t4_218part0 : t4_218jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_218frontier : t4_218root.frontier 0=t4_218jobs := by rfl
theorem t4_218all : t4_218jobs.all (Job.check tree)=true := by
  simp only [t4_218jobs,List.all_append,List.all_nil,t4_218part0,Bool.and_self]
theorem t4_218checked : Checked tree [1,3,3,3] := by
  refine ⟨plan1707,valid1707,t4_218choices,?_⟩
  exact check_of_frontier tree 0 t4_218root t4_218jobs t4_218frontier t4_218all
theorem t4_219choices : plan1765.choices=[1,3,3,6].map (options 4 1) := by rfl


theorem t4_219part0 : t4_219jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_219frontier : t4_219root.frontier 0=t4_219jobs := by rfl
theorem t4_219all : t4_219jobs.all (Job.check tree)=true := by
  simp only [t4_219jobs,List.all_append,List.all_nil,t4_219part0,Bool.and_self]
theorem t4_219checked : Checked tree [1,3,3,6] := by
  refine ⟨plan1765,valid1765,t4_219choices,?_⟩
  exact check_of_frontier tree 0 t4_219root t4_219jobs t4_219frontier t4_219all
theorem t4_220choices : plan1766.choices=[1,3,3,7].map (options 4 1) := by rfl


theorem t4_220part0 : t4_220jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_220frontier : t4_220root.frontier 0=t4_220jobs := by rfl
theorem t4_220all : t4_220jobs.all (Job.check tree)=true := by
  simp only [t4_220jobs,List.all_append,List.all_nil,t4_220part0,Bool.and_self]
theorem t4_220checked : Checked tree [1,3,3,7] := by
  refine ⟨plan1766,valid1766,t4_220choices,?_⟩
  exact check_of_frontier tree 0 t4_220root t4_220jobs t4_220frontier t4_220all
theorem t4_221choices : plan1767.choices=[1,3,3,10].map (options 4 1) := by rfl


theorem t4_221part0 : t4_221jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_221frontier : t4_221root.frontier 0=t4_221jobs := by rfl
theorem t4_221all : t4_221jobs.all (Job.check tree)=true := by
  simp only [t4_221jobs,List.all_append,List.all_nil,t4_221part0,Bool.and_self]
theorem t4_221checked : Checked tree [1,3,3,10] := by
  refine ⟨plan1767,valid1767,t4_221choices,?_⟩
  exact check_of_frontier tree 0 t4_221root t4_221jobs t4_221frontier t4_221all
theorem t4_222choices : plan1898.choices=[1,3,6,6].map (options 4 2) := by rfl


theorem t4_222part0 : t4_222jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_222frontier : t4_222root.frontier 0=t4_222jobs := by rfl
theorem t4_222all : t4_222jobs.all (Job.check tree)=true := by
  simp only [t4_222jobs,List.all_append,List.all_nil,t4_222part0,Bool.and_self]
theorem t4_222checked : Checked tree [1,3,6,6] := by
  refine ⟨plan1898,valid1898,t4_222choices,?_⟩
  exact check_of_frontier tree 0 t4_222root t4_222jobs t4_222frontier t4_222all
theorem t4_223choices : plan1899.choices=[1,3,6,7].map (options 4 2) := by rfl


theorem t4_223part0 : t4_223jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_223frontier : t4_223root.frontier 0=t4_223jobs := by rfl
theorem t4_223all : t4_223jobs.all (Job.check tree)=true := by
  simp only [t4_223jobs,List.all_append,List.all_nil,t4_223part0,Bool.and_self]
theorem t4_223checked : Checked tree [1,3,6,7] := by
  refine ⟨plan1899,valid1899,t4_223choices,?_⟩
  exact check_of_frontier tree 0 t4_223root t4_223jobs t4_223frontier t4_223all
theorem t4_224choices : plan1900.choices=[1,3,6,10].map (options 4 2) := by rfl


theorem t4_224part0 : t4_224jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_224frontier : t4_224root.frontier 0=t4_224jobs := by rfl
theorem t4_224all : t4_224jobs.all (Job.check tree)=true := by
  simp only [t4_224jobs,List.all_append,List.all_nil,t4_224part0,Bool.and_self]
theorem t4_224checked : Checked tree [1,3,6,10] := by
  refine ⟨plan1900,valid1900,t4_224choices,?_⟩
  exact check_of_frontier tree 0 t4_224root t4_224jobs t4_224frontier t4_224all
theorem t4_225choices : plan1901.choices=[1,3,7,7].map (options 4 2) := by rfl


theorem t4_225part0 : t4_225jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_225frontier : t4_225root.frontier 0=t4_225jobs := by rfl
theorem t4_225all : t4_225jobs.all (Job.check tree)=true := by
  simp only [t4_225jobs,List.all_append,List.all_nil,t4_225part0,Bool.and_self]
theorem t4_225checked : Checked tree [1,3,7,7] := by
  refine ⟨plan1901,valid1901,t4_225choices,?_⟩
  exact check_of_frontier tree 0 t4_225root t4_225jobs t4_225frontier t4_225all
theorem t4_226choices : plan1902.choices=[1,3,10,7].map (options 4 2) := by rfl


theorem t4_226part0 : t4_226jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_226frontier : t4_226root.frontier 0=t4_226jobs := by rfl
theorem t4_226all : t4_226jobs.all (Job.check tree)=true := by
  simp only [t4_226jobs,List.all_append,List.all_nil,t4_226part0,Bool.and_self]
theorem t4_226checked : Checked tree [1,3,10,7] := by
  refine ⟨plan1902,valid1902,t4_226choices,?_⟩
  exact check_of_frontier tree 0 t4_226root t4_226jobs t4_226frontier t4_226all
theorem t4_227choices : plan1903.choices=[1,3,10,10].map (options 4 2) := by rfl


theorem t4_227part0 : t4_227jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_227frontier : t4_227root.frontier 0=t4_227jobs := by rfl
theorem t4_227all : t4_227jobs.all (Job.check tree)=true := by
  simp only [t4_227jobs,List.all_append,List.all_nil,t4_227part0,Bool.and_self]
theorem t4_227checked : Checked tree [1,3,10,10] := by
  refine ⟨plan1903,valid1903,t4_227choices,?_⟩
  exact check_of_frontier tree 0 t4_227root t4_227jobs t4_227frontier t4_227all
theorem t4_228choices : plan1768.choices=[1,4,2,2].map (options 4 1) := by rfl


theorem t4_228part0 : t4_228jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_228frontier : t4_228root.frontier 0=t4_228jobs := by rfl
theorem t4_228all : t4_228jobs.all (Job.check tree)=true := by
  simp only [t4_228jobs,List.all_append,List.all_nil,t4_228part0,Bool.and_self]
theorem t4_228checked : Checked tree [1,4,2,2] := by
  refine ⟨plan1768,valid1768,t4_228choices,?_⟩
  exact check_of_frontier tree 0 t4_228root t4_228jobs t4_228frontier t4_228all
theorem t4_229choices : plan1769.choices=[1,4,2,3].map (options 4 1) := by rfl


theorem t4_229part0 : t4_229jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_229frontier : t4_229root.frontier 0=t4_229jobs := by rfl
theorem t4_229all : t4_229jobs.all (Job.check tree)=true := by
  simp only [t4_229jobs,List.all_append,List.all_nil,t4_229part0,Bool.and_self]
theorem t4_229checked : Checked tree [1,4,2,3] := by
  refine ⟨plan1769,valid1769,t4_229choices,?_⟩
  exact check_of_frontier tree 0 t4_229root t4_229jobs t4_229frontier t4_229all
theorem t4_230choices : plan1904.choices=[1,4,2,5].map (options 4 2) := by rfl


theorem t4_230part0 : t4_230jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_230frontier : t4_230root.frontier 0=t4_230jobs := by rfl
theorem t4_230all : t4_230jobs.all (Job.check tree)=true := by
  simp only [t4_230jobs,List.all_append,List.all_nil,t4_230part0,Bool.and_self]
theorem t4_230checked : Checked tree [1,4,2,5] := by
  refine ⟨plan1904,valid1904,t4_230choices,?_⟩
  exact check_of_frontier tree 0 t4_230root t4_230jobs t4_230frontier t4_230all
theorem t4_231choices : plan1905.choices=[1,4,2,6].map (options 4 2) := by rfl


theorem t4_231part0 : t4_231jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_231frontier : t4_231root.frontier 0=t4_231jobs := by rfl
theorem t4_231all : t4_231jobs.all (Job.check tree)=true := by
  simp only [t4_231jobs,List.all_append,List.all_nil,t4_231part0,Bool.and_self]
theorem t4_231checked : Checked tree [1,4,2,6] := by
  refine ⟨plan1905,valid1905,t4_231choices,?_⟩
  exact check_of_frontier tree 0 t4_231root t4_231jobs t4_231frontier t4_231all
theorem t4_232choices : plan1906.choices=[1,4,2,7].map (options 4 2) := by rfl


theorem t4_232part0 : t4_232jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_232frontier : t4_232root.frontier 0=t4_232jobs := by rfl
theorem t4_232all : t4_232jobs.all (Job.check tree)=true := by
  simp only [t4_232jobs,List.all_append,List.all_nil,t4_232part0,Bool.and_self]
theorem t4_232checked : Checked tree [1,4,2,7] := by
  refine ⟨plan1906,valid1906,t4_232choices,?_⟩
  exact check_of_frontier tree 0 t4_232root t4_232jobs t4_232frontier t4_232all
theorem t4_233choices : plan1907.choices=[1,4,2,9].map (options 4 2) := by rfl


theorem t4_233part0 : t4_233jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_233frontier : t4_233root.frontier 0=t4_233jobs := by rfl
theorem t4_233all : t4_233jobs.all (Job.check tree)=true := by
  simp only [t4_233jobs,List.all_append,List.all_nil,t4_233part0,Bool.and_self]
theorem t4_233checked : Checked tree [1,4,2,9] := by
  refine ⟨plan1907,valid1907,t4_233choices,?_⟩
  exact check_of_frontier tree 0 t4_233root t4_233jobs t4_233frontier t4_233all
theorem t4_234choices : plan1908.choices=[1,4,2,10].map (options 4 2) := by rfl


theorem t4_234part0 : t4_234jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_234frontier : t4_234root.frontier 0=t4_234jobs := by rfl
theorem t4_234all : t4_234jobs.all (Job.check tree)=true := by
  simp only [t4_234jobs,List.all_append,List.all_nil,t4_234part0,Bool.and_self]
theorem t4_234checked : Checked tree [1,4,2,10] := by
  refine ⟨plan1908,valid1908,t4_234choices,?_⟩
  exact check_of_frontier tree 0 t4_234root t4_234jobs t4_234frontier t4_234all
theorem t4_235choices : plan1770.choices=[1,4,3,3].map (options 4 1) := by rfl


theorem t4_235part0 : t4_235jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_235frontier : t4_235root.frontier 0=t4_235jobs := by rfl
theorem t4_235all : t4_235jobs.all (Job.check tree)=true := by
  simp only [t4_235jobs,List.all_append,List.all_nil,t4_235part0,Bool.and_self]
theorem t4_235checked : Checked tree [1,4,3,3] := by
  refine ⟨plan1770,valid1770,t4_235choices,?_⟩
  exact check_of_frontier tree 0 t4_235root t4_235jobs t4_235frontier t4_235all
theorem t4_236choices : plan1909.choices=[1,4,3,6].map (options 4 2) := by rfl


theorem t4_236part0 : t4_236jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_236frontier : t4_236root.frontier 0=t4_236jobs := by rfl
theorem t4_236all : t4_236jobs.all (Job.check tree)=true := by
  simp only [t4_236jobs,List.all_append,List.all_nil,t4_236part0,Bool.and_self]
theorem t4_236checked : Checked tree [1,4,3,6] := by
  refine ⟨plan1909,valid1909,t4_236choices,?_⟩
  exact check_of_frontier tree 0 t4_236root t4_236jobs t4_236frontier t4_236all
theorem t4_237choices : plan1910.choices=[1,4,3,7].map (options 4 2) := by rfl


theorem t4_237part0 : t4_237jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_237frontier : t4_237root.frontier 0=t4_237jobs := by rfl
theorem t4_237all : t4_237jobs.all (Job.check tree)=true := by
  simp only [t4_237jobs,List.all_append,List.all_nil,t4_237part0,Bool.and_self]
theorem t4_237checked : Checked tree [1,4,3,7] := by
  refine ⟨plan1910,valid1910,t4_237choices,?_⟩
  exact check_of_frontier tree 0 t4_237root t4_237jobs t4_237frontier t4_237all
theorem t4_238choices : plan1911.choices=[1,4,3,10].map (options 4 2) := by rfl


theorem t4_238part0 : t4_238jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_238frontier : t4_238root.frontier 0=t4_238jobs := by rfl
theorem t4_238all : t4_238jobs.all (Job.check tree)=true := by
  simp only [t4_238jobs,List.all_append,List.all_nil,t4_238part0,Bool.and_self]
theorem t4_238checked : Checked tree [1,4,3,10] := by
  refine ⟨plan1911,valid1911,t4_238choices,?_⟩
  exact check_of_frontier tree 0 t4_238root t4_238jobs t4_238frontier t4_238all
theorem t4_239choices : plan1912.choices=[1,4,4,3].map (options 4 2) := by rfl


theorem t4_239part0 : t4_239jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_239frontier : t4_239root.frontier 0=t4_239jobs := by rfl
theorem t4_239all : t4_239jobs.all (Job.check tree)=true := by
  simp only [t4_239jobs,List.all_append,List.all_nil,t4_239part0,Bool.and_self]
theorem t4_239checked : Checked tree [1,4,4,3] := by
  refine ⟨plan1912,valid1912,t4_239choices,?_⟩
  exact check_of_frontier tree 0 t4_239root t4_239jobs t4_239frontier t4_239all
theorem t4_240choices : plan2079.choices=[1,4,4,6].map (options 4 3) := by rfl


theorem t4_240part0 : t4_240jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_240frontier : t4_240root.frontier 0=t4_240jobs := by rfl
theorem t4_240all : t4_240jobs.all (Job.check tree)=true := by
  simp only [t4_240jobs,List.all_append,List.all_nil,t4_240part0,Bool.and_self]
theorem t4_240checked : Checked tree [1,4,4,6] := by
  refine ⟨plan2079,valid2079,t4_240choices,?_⟩
  exact check_of_frontier tree 0 t4_240root t4_240jobs t4_240frontier t4_240all
theorem t4_241choices : plan2080.choices=[1,4,4,7].map (options 4 3) := by rfl


theorem t4_241part0 : t4_241jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_241frontier : t4_241root.frontier 0=t4_241jobs := by rfl
theorem t4_241all : t4_241jobs.all (Job.check tree)=true := by
  simp only [t4_241jobs,List.all_append,List.all_nil,t4_241part0,Bool.and_self]
theorem t4_241checked : Checked tree [1,4,4,7] := by
  refine ⟨plan2080,valid2080,t4_241choices,?_⟩
  exact check_of_frontier tree 0 t4_241root t4_241jobs t4_241frontier t4_241all
theorem t4_242choices : plan2081.choices=[1,4,4,10].map (options 4 3) := by rfl


theorem t4_242part0 : t4_242jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_242frontier : t4_242root.frontier 0=t4_242jobs := by rfl
theorem t4_242all : t4_242jobs.all (Job.check tree)=true := by
  simp only [t4_242jobs,List.all_append,List.all_nil,t4_242part0,Bool.and_self]
theorem t4_242checked : Checked tree [1,4,4,10] := by
  refine ⟨plan2081,valid2081,t4_242choices,?_⟩
  exact check_of_frontier tree 0 t4_242root t4_242jobs t4_242frontier t4_242all
theorem t4_243choices : plan1913.choices=[1,4,5,3].map (options 4 2) := by rfl


theorem t4_243part0 : t4_243jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_243frontier : t4_243root.frontier 0=t4_243jobs := by rfl
theorem t4_243all : t4_243jobs.all (Job.check tree)=true := by
  simp only [t4_243jobs,List.all_append,List.all_nil,t4_243part0,Bool.and_self]
theorem t4_243checked : Checked tree [1,4,5,3] := by
  refine ⟨plan1913,valid1913,t4_243choices,?_⟩
  exact check_of_frontier tree 0 t4_243root t4_243jobs t4_243frontier t4_243all
theorem t4_244choices : plan2082.choices=[1,4,5,5].map (options 4 3) := by rfl


theorem t4_244part0 : t4_244jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_244frontier : t4_244root.frontier 0=t4_244jobs := by rfl
theorem t4_244all : t4_244jobs.all (Job.check tree)=true := by
  simp only [t4_244jobs,List.all_append,List.all_nil,t4_244part0,Bool.and_self]
theorem t4_244checked : Checked tree [1,4,5,5] := by
  refine ⟨plan2082,valid2082,t4_244choices,?_⟩
  exact check_of_frontier tree 0 t4_244root t4_244jobs t4_244frontier t4_244all
theorem t4_245choices : plan2083.choices=[1,4,5,6].map (options 4 3) := by rfl


theorem t4_245part0 : t4_245jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_245frontier : t4_245root.frontier 0=t4_245jobs := by rfl
theorem t4_245all : t4_245jobs.all (Job.check tree)=true := by
  simp only [t4_245jobs,List.all_append,List.all_nil,t4_245part0,Bool.and_self]
theorem t4_245checked : Checked tree [1,4,5,6] := by
  refine ⟨plan2083,valid2083,t4_245choices,?_⟩
  exact check_of_frontier tree 0 t4_245root t4_245jobs t4_245frontier t4_245all
theorem t4_246choices : plan2084.choices=[1,4,5,7].map (options 4 3) := by rfl


theorem t4_246part0 : t4_246jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_246frontier : t4_246root.frontier 0=t4_246jobs := by rfl
theorem t4_246all : t4_246jobs.all (Job.check tree)=true := by
  simp only [t4_246jobs,List.all_append,List.all_nil,t4_246part0,Bool.and_self]
theorem t4_246checked : Checked tree [1,4,5,7] := by
  refine ⟨plan2084,valid2084,t4_246choices,?_⟩
  exact check_of_frontier tree 0 t4_246root t4_246jobs t4_246frontier t4_246all
theorem t4_247choices : plan2085.choices=[1,4,5,9].map (options 4 3) := by rfl


theorem t4_247part0 : t4_247jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_247frontier : t4_247root.frontier 0=t4_247jobs := by rfl
theorem t4_247all : t4_247jobs.all (Job.check tree)=true := by
  simp only [t4_247jobs,List.all_append,List.all_nil,t4_247part0,Bool.and_self]
theorem t4_247checked : Checked tree [1,4,5,9] := by
  refine ⟨plan2085,valid2085,t4_247choices,?_⟩
  exact check_of_frontier tree 0 t4_247root t4_247jobs t4_247frontier t4_247all
theorem t4_248choices : plan2086.choices=[1,4,5,10].map (options 4 3) := by rfl


theorem t4_248part0 : t4_248jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_248frontier : t4_248root.frontier 0=t4_248jobs := by rfl
theorem t4_248all : t4_248jobs.all (Job.check tree)=true := by
  simp only [t4_248jobs,List.all_append,List.all_nil,t4_248part0,Bool.and_self]
theorem t4_248checked : Checked tree [1,4,5,10] := by
  refine ⟨plan2086,valid2086,t4_248choices,?_⟩
  exact check_of_frontier tree 0 t4_248root t4_248jobs t4_248frontier t4_248all
theorem t4_249choices : plan2087.choices=[1,4,6,6].map (options 4 3) := by rfl


theorem t4_249part0 : t4_249jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_249frontier : t4_249root.frontier 0=t4_249jobs := by rfl
theorem t4_249all : t4_249jobs.all (Job.check tree)=true := by
  simp only [t4_249jobs,List.all_append,List.all_nil,t4_249part0,Bool.and_self]
theorem t4_249checked : Checked tree [1,4,6,6] := by
  refine ⟨plan2087,valid2087,t4_249choices,?_⟩
  exact check_of_frontier tree 0 t4_249root t4_249jobs t4_249frontier t4_249all
theorem t4_250choices : plan2088.choices=[1,4,6,7].map (options 4 3) := by rfl


theorem t4_250part0 : t4_250jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_250frontier : t4_250root.frontier 0=t4_250jobs := by rfl
theorem t4_250all : t4_250jobs.all (Job.check tree)=true := by
  simp only [t4_250jobs,List.all_append,List.all_nil,t4_250part0,Bool.and_self]
theorem t4_250checked : Checked tree [1,4,6,7] := by
  refine ⟨plan2088,valid2088,t4_250choices,?_⟩
  exact check_of_frontier tree 0 t4_250root t4_250jobs t4_250frontier t4_250all
theorem t4_251choices : plan2089.choices=[1,4,6,10].map (options 4 3) := by rfl


theorem t4_251part0 : t4_251jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_251frontier : t4_251root.frontier 0=t4_251jobs := by rfl
theorem t4_251all : t4_251jobs.all (Job.check tree)=true := by
  simp only [t4_251jobs,List.all_append,List.all_nil,t4_251part0,Bool.and_self]
theorem t4_251checked : Checked tree [1,4,6,10] := by
  refine ⟨plan2089,valid2089,t4_251choices,?_⟩
  exact check_of_frontier tree 0 t4_251root t4_251jobs t4_251frontier t4_251all
theorem t4_252choices : plan2090.choices=[1,4,7,7].map (options 4 3) := by rfl


theorem t4_252part0 : t4_252jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_252frontier : t4_252root.frontier 0=t4_252jobs := by rfl
theorem t4_252all : t4_252jobs.all (Job.check tree)=true := by
  simp only [t4_252jobs,List.all_append,List.all_nil,t4_252part0,Bool.and_self]
theorem t4_252checked : Checked tree [1,4,7,7] := by
  refine ⟨plan2090,valid2090,t4_252choices,?_⟩
  exact check_of_frontier tree 0 t4_252root t4_252jobs t4_252frontier t4_252all
theorem t4_253choices : plan1914.choices=[1,4,8,3].map (options 4 2) := by rfl


theorem t4_253part0 : t4_253jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_253frontier : t4_253root.frontier 0=t4_253jobs := by rfl
theorem t4_253all : t4_253jobs.all (Job.check tree)=true := by
  simp only [t4_253jobs,List.all_append,List.all_nil,t4_253part0,Bool.and_self]
theorem t4_253checked : Checked tree [1,4,8,3] := by
  refine ⟨plan1914,valid1914,t4_253choices,?_⟩
  exact check_of_frontier tree 0 t4_253root t4_253jobs t4_253frontier t4_253all
theorem t4_254choices : plan2091.choices=[1,4,8,6].map (options 4 3) := by rfl


theorem t4_254part0 : t4_254jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_254frontier : t4_254root.frontier 0=t4_254jobs := by rfl
theorem t4_254all : t4_254jobs.all (Job.check tree)=true := by
  simp only [t4_254jobs,List.all_append,List.all_nil,t4_254part0,Bool.and_self]
theorem t4_254checked : Checked tree [1,4,8,6] := by
  refine ⟨plan2091,valid2091,t4_254choices,?_⟩
  exact check_of_frontier tree 0 t4_254root t4_254jobs t4_254frontier t4_254all
theorem t4_255choices : plan2092.choices=[1,4,8,7].map (options 4 3) := by rfl


theorem t4_255part0 : t4_255jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_255frontier : t4_255root.frontier 0=t4_255jobs := by rfl
theorem t4_255all : t4_255jobs.all (Job.check tree)=true := by
  simp only [t4_255jobs,List.all_append,List.all_nil,t4_255part0,Bool.and_self]
theorem t4_255checked : Checked tree [1,4,8,7] := by
  refine ⟨plan2092,valid2092,t4_255choices,?_⟩
  exact check_of_frontier tree 0 t4_255root t4_255jobs t4_255frontier t4_255all
theorem t4_256choices : plan2093.choices=[1,4,8,10].map (options 4 3) := by rfl


theorem t4_256part0 : t4_256jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_256frontier : t4_256root.frontier 0=t4_256jobs := by rfl
theorem t4_256all : t4_256jobs.all (Job.check tree)=true := by
  simp only [t4_256jobs,List.all_append,List.all_nil,t4_256part0,Bool.and_self]
theorem t4_256checked : Checked tree [1,4,8,10] := by
  refine ⟨plan2093,valid2093,t4_256choices,?_⟩
  exact check_of_frontier tree 0 t4_256root t4_256jobs t4_256frontier t4_256all
theorem t4_257choices : plan1915.choices=[1,4,9,3].map (options 4 2) := by rfl


theorem t4_257part0 : t4_257jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_257frontier : t4_257root.frontier 0=t4_257jobs := by rfl
theorem t4_257all : t4_257jobs.all (Job.check tree)=true := by
  simp only [t4_257jobs,List.all_append,List.all_nil,t4_257part0,Bool.and_self]
theorem t4_257checked : Checked tree [1,4,9,3] := by
  refine ⟨plan1915,valid1915,t4_257choices,?_⟩
  exact check_of_frontier tree 0 t4_257root t4_257jobs t4_257frontier t4_257all
theorem t4_258choices : plan2094.choices=[1,4,9,6].map (options 4 3) := by rfl


theorem t4_258part0 : t4_258jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_258frontier : t4_258root.frontier 0=t4_258jobs := by rfl
theorem t4_258all : t4_258jobs.all (Job.check tree)=true := by
  simp only [t4_258jobs,List.all_append,List.all_nil,t4_258part0,Bool.and_self]
theorem t4_258checked : Checked tree [1,4,9,6] := by
  refine ⟨plan2094,valid2094,t4_258choices,?_⟩
  exact check_of_frontier tree 0 t4_258root t4_258jobs t4_258frontier t4_258all
theorem t4_259choices : plan2095.choices=[1,4,9,7].map (options 4 3) := by rfl


theorem t4_259part0 : t4_259jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_259frontier : t4_259root.frontier 0=t4_259jobs := by rfl
theorem t4_259all : t4_259jobs.all (Job.check tree)=true := by
  simp only [t4_259jobs,List.all_append,List.all_nil,t4_259part0,Bool.and_self]
theorem t4_259checked : Checked tree [1,4,9,7] := by
  refine ⟨plan2095,valid2095,t4_259choices,?_⟩
  exact check_of_frontier tree 0 t4_259root t4_259jobs t4_259frontier t4_259all
theorem t4_260choices : plan2096.choices=[1,4,9,9].map (options 4 3) := by rfl


theorem t4_260part0 : t4_260jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_260frontier : t4_260root.frontier 0=t4_260jobs := by rfl
theorem t4_260all : t4_260jobs.all (Job.check tree)=true := by
  simp only [t4_260jobs,List.all_append,List.all_nil,t4_260part0,Bool.and_self]
theorem t4_260checked : Checked tree [1,4,9,9] := by
  refine ⟨plan2096,valid2096,t4_260choices,?_⟩
  exact check_of_frontier tree 0 t4_260root t4_260jobs t4_260frontier t4_260all
theorem t4_261choices : plan2097.choices=[1,4,9,10].map (options 4 3) := by rfl


theorem t4_261part0 : t4_261jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_261frontier : t4_261root.frontier 0=t4_261jobs := by rfl
theorem t4_261all : t4_261jobs.all (Job.check tree)=true := by
  simp only [t4_261jobs,List.all_append,List.all_nil,t4_261part0,Bool.and_self]
theorem t4_261checked : Checked tree [1,4,9,10] := by
  refine ⟨plan2097,valid2097,t4_261choices,?_⟩
  exact check_of_frontier tree 0 t4_261root t4_261jobs t4_261frontier t4_261all
theorem t4_262choices : plan2098.choices=[1,4,10,7].map (options 4 3) := by rfl


theorem t4_262part0 : t4_262jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_262frontier : t4_262root.frontier 0=t4_262jobs := by rfl
theorem t4_262all : t4_262jobs.all (Job.check tree)=true := by
  simp only [t4_262jobs,List.all_append,List.all_nil,t4_262part0,Bool.and_self]
theorem t4_262checked : Checked tree [1,4,10,7] := by
  refine ⟨plan2098,valid2098,t4_262choices,?_⟩
  exact check_of_frontier tree 0 t4_262root t4_262jobs t4_262frontier t4_262all
theorem t4_263choices : plan2099.choices=[1,4,10,10].map (options 4 3) := by rfl


theorem t4_263part0 : t4_263jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_263frontier : t4_263root.frontier 0=t4_263jobs := by rfl
theorem t4_263all : t4_263jobs.all (Job.check tree)=true := by
  simp only [t4_263jobs,List.all_append,List.all_nil,t4_263part0,Bool.and_self]
theorem t4_263checked : Checked tree [1,4,10,10] := by
  refine ⟨plan2099,valid2099,t4_263choices,?_⟩
  exact check_of_frontier tree 0 t4_263root t4_263jobs t4_263frontier t4_263all
theorem t4_264choices : plan1771.choices=[1,5,3,3].map (options 4 1) := by rfl


theorem t4_264part0 : t4_264jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_264frontier : t4_264root.frontier 0=t4_264jobs := by rfl
theorem t4_264all : t4_264jobs.all (Job.check tree)=true := by
  simp only [t4_264jobs,List.all_append,List.all_nil,t4_264part0,Bool.and_self]
theorem t4_264checked : Checked tree [1,5,3,3] := by
  refine ⟨plan1771,valid1771,t4_264choices,?_⟩
  exact check_of_frontier tree 0 t4_264root t4_264jobs t4_264frontier t4_264all
theorem t4_265choices : plan1916.choices=[1,5,3,6].map (options 4 2) := by rfl


theorem t4_265part0 : t4_265jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_265frontier : t4_265root.frontier 0=t4_265jobs := by rfl
theorem t4_265all : t4_265jobs.all (Job.check tree)=true := by
  simp only [t4_265jobs,List.all_append,List.all_nil,t4_265part0,Bool.and_self]
theorem t4_265checked : Checked tree [1,5,3,6] := by
  refine ⟨plan1916,valid1916,t4_265choices,?_⟩
  exact check_of_frontier tree 0 t4_265root t4_265jobs t4_265frontier t4_265all
theorem t4_266choices : plan1917.choices=[1,5,3,7].map (options 4 2) := by rfl


theorem t4_266part0 : t4_266jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_266frontier : t4_266root.frontier 0=t4_266jobs := by rfl
theorem t4_266all : t4_266jobs.all (Job.check tree)=true := by
  simp only [t4_266jobs,List.all_append,List.all_nil,t4_266part0,Bool.and_self]
theorem t4_266checked : Checked tree [1,5,3,7] := by
  refine ⟨plan1917,valid1917,t4_266choices,?_⟩
  exact check_of_frontier tree 0 t4_266root t4_266jobs t4_266frontier t4_266all
theorem t4_267choices : plan1918.choices=[1,5,3,10].map (options 4 2) := by rfl


theorem t4_267part0 : t4_267jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_267frontier : t4_267root.frontier 0=t4_267jobs := by rfl
theorem t4_267all : t4_267jobs.all (Job.check tree)=true := by
  simp only [t4_267jobs,List.all_append,List.all_nil,t4_267part0,Bool.and_self]
theorem t4_267checked : Checked tree [1,5,3,10] := by
  refine ⟨plan1918,valid1918,t4_267choices,?_⟩
  exact check_of_frontier tree 0 t4_267root t4_267jobs t4_267frontier t4_267all
theorem t4_268choices : plan1919.choices=[1,5,5,3].map (options 4 2) := by rfl


theorem t4_268part0 : t4_268jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_268frontier : t4_268root.frontier 0=t4_268jobs := by rfl
theorem t4_268all : t4_268jobs.all (Job.check tree)=true := by
  simp only [t4_268jobs,List.all_append,List.all_nil,t4_268part0,Bool.and_self]
theorem t4_268checked : Checked tree [1,5,5,3] := by
  refine ⟨plan1919,valid1919,t4_268choices,?_⟩
  exact check_of_frontier tree 0 t4_268root t4_268jobs t4_268frontier t4_268all
theorem t4_269choices : plan2100.choices=[1,5,5,5].map (options 4 3) := by rfl


theorem t4_269part0 : t4_269jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_269frontier : t4_269root.frontier 0=t4_269jobs := by rfl
theorem t4_269all : t4_269jobs.all (Job.check tree)=true := by
  simp only [t4_269jobs,List.all_append,List.all_nil,t4_269part0,Bool.and_self]
theorem t4_269checked : Checked tree [1,5,5,5] := by
  refine ⟨plan2100,valid2100,t4_269choices,?_⟩
  exact check_of_frontier tree 0 t4_269root t4_269jobs t4_269frontier t4_269all
theorem t4_270choices : plan2101.choices=[1,5,5,6].map (options 4 3) := by rfl


theorem t4_270part0 : t4_270jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_270frontier : t4_270root.frontier 0=t4_270jobs := by rfl
theorem t4_270all : t4_270jobs.all (Job.check tree)=true := by
  simp only [t4_270jobs,List.all_append,List.all_nil,t4_270part0,Bool.and_self]
theorem t4_270checked : Checked tree [1,5,5,6] := by
  refine ⟨plan2101,valid2101,t4_270choices,?_⟩
  exact check_of_frontier tree 0 t4_270root t4_270jobs t4_270frontier t4_270all
theorem t4_271choices : plan2102.choices=[1,5,5,7].map (options 4 3) := by rfl


theorem t4_271part0 : t4_271jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_271frontier : t4_271root.frontier 0=t4_271jobs := by rfl
theorem t4_271all : t4_271jobs.all (Job.check tree)=true := by
  simp only [t4_271jobs,List.all_append,List.all_nil,t4_271part0,Bool.and_self]
theorem t4_271checked : Checked tree [1,5,5,7] := by
  refine ⟨plan2102,valid2102,t4_271choices,?_⟩
  exact check_of_frontier tree 0 t4_271root t4_271jobs t4_271frontier t4_271all
theorem t4_272choices : plan2103.choices=[1,5,5,9].map (options 4 3) := by rfl


theorem t4_272part0 : t4_272jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_272frontier : t4_272root.frontier 0=t4_272jobs := by rfl
theorem t4_272all : t4_272jobs.all (Job.check tree)=true := by
  simp only [t4_272jobs,List.all_append,List.all_nil,t4_272part0,Bool.and_self]
theorem t4_272checked : Checked tree [1,5,5,9] := by
  refine ⟨plan2103,valid2103,t4_272choices,?_⟩
  exact check_of_frontier tree 0 t4_272root t4_272jobs t4_272frontier t4_272all
theorem t4_273choices : plan2104.choices=[1,5,5,10].map (options 4 3) := by rfl


theorem t4_273part0 : t4_273jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_273frontier : t4_273root.frontier 0=t4_273jobs := by rfl
theorem t4_273all : t4_273jobs.all (Job.check tree)=true := by
  simp only [t4_273jobs,List.all_append,List.all_nil,t4_273part0,Bool.and_self]
theorem t4_273checked : Checked tree [1,5,5,10] := by
  refine ⟨plan2104,valid2104,t4_273choices,?_⟩
  exact check_of_frontier tree 0 t4_273root t4_273jobs t4_273frontier t4_273all
theorem t4_274choices : plan2105.choices=[1,5,6,6].map (options 4 3) := by rfl


theorem t4_274part0 : t4_274jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_274frontier : t4_274root.frontier 0=t4_274jobs := by rfl
theorem t4_274all : t4_274jobs.all (Job.check tree)=true := by
  simp only [t4_274jobs,List.all_append,List.all_nil,t4_274part0,Bool.and_self]
theorem t4_274checked : Checked tree [1,5,6,6] := by
  refine ⟨plan2105,valid2105,t4_274choices,?_⟩
  exact check_of_frontier tree 0 t4_274root t4_274jobs t4_274frontier t4_274all
theorem t4_275choices : plan2106.choices=[1,5,6,7].map (options 4 3) := by rfl


theorem t4_275part0 : t4_275jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_275frontier : t4_275root.frontier 0=t4_275jobs := by rfl
theorem t4_275all : t4_275jobs.all (Job.check tree)=true := by
  simp only [t4_275jobs,List.all_append,List.all_nil,t4_275part0,Bool.and_self]
theorem t4_275checked : Checked tree [1,5,6,7] := by
  refine ⟨plan2106,valid2106,t4_275choices,?_⟩
  exact check_of_frontier tree 0 t4_275root t4_275jobs t4_275frontier t4_275all
theorem t4_276choices : plan2107.choices=[1,5,6,10].map (options 4 3) := by rfl


theorem t4_276part0 : t4_276jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_276frontier : t4_276root.frontier 0=t4_276jobs := by rfl
theorem t4_276all : t4_276jobs.all (Job.check tree)=true := by
  simp only [t4_276jobs,List.all_append,List.all_nil,t4_276part0,Bool.and_self]
theorem t4_276checked : Checked tree [1,5,6,10] := by
  refine ⟨plan2107,valid2107,t4_276choices,?_⟩
  exact check_of_frontier tree 0 t4_276root t4_276jobs t4_276frontier t4_276all
theorem t4_277choices : plan2108.choices=[1,5,7,7].map (options 4 3) := by rfl


theorem t4_277part0 : t4_277jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_277frontier : t4_277root.frontier 0=t4_277jobs := by rfl
theorem t4_277all : t4_277jobs.all (Job.check tree)=true := by
  simp only [t4_277jobs,List.all_append,List.all_nil,t4_277part0,Bool.and_self]
theorem t4_277checked : Checked tree [1,5,7,7] := by
  refine ⟨plan2108,valid2108,t4_277choices,?_⟩
  exact check_of_frontier tree 0 t4_277root t4_277jobs t4_277frontier t4_277all
theorem t4_278choices : plan1920.choices=[1,5,9,3].map (options 4 2) := by rfl


theorem t4_278part0 : t4_278jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_278frontier : t4_278root.frontier 0=t4_278jobs := by rfl
theorem t4_278all : t4_278jobs.all (Job.check tree)=true := by
  simp only [t4_278jobs,List.all_append,List.all_nil,t4_278part0,Bool.and_self]
theorem t4_278checked : Checked tree [1,5,9,3] := by
  refine ⟨plan1920,valid1920,t4_278choices,?_⟩
  exact check_of_frontier tree 0 t4_278root t4_278jobs t4_278frontier t4_278all
theorem t4_279choices : plan2109.choices=[1,5,9,6].map (options 4 3) := by rfl


theorem t4_279part0 : t4_279jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_279frontier : t4_279root.frontier 0=t4_279jobs := by rfl
theorem t4_279all : t4_279jobs.all (Job.check tree)=true := by
  simp only [t4_279jobs,List.all_append,List.all_nil,t4_279part0,Bool.and_self]
theorem t4_279checked : Checked tree [1,5,9,6] := by
  refine ⟨plan2109,valid2109,t4_279choices,?_⟩
  exact check_of_frontier tree 0 t4_279root t4_279jobs t4_279frontier t4_279all
theorem t4_280choices : plan2110.choices=[1,5,9,7].map (options 4 3) := by rfl


theorem t4_280part0 : t4_280jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_280frontier : t4_280root.frontier 0=t4_280jobs := by rfl
theorem t4_280all : t4_280jobs.all (Job.check tree)=true := by
  simp only [t4_280jobs,List.all_append,List.all_nil,t4_280part0,Bool.and_self]
theorem t4_280checked : Checked tree [1,5,9,7] := by
  refine ⟨plan2110,valid2110,t4_280choices,?_⟩
  exact check_of_frontier tree 0 t4_280root t4_280jobs t4_280frontier t4_280all
theorem t4_281choices : plan2111.choices=[1,5,9,9].map (options 4 3) := by rfl


theorem t4_281part0 : t4_281jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_281frontier : t4_281root.frontier 0=t4_281jobs := by rfl
theorem t4_281all : t4_281jobs.all (Job.check tree)=true := by
  simp only [t4_281jobs,List.all_append,List.all_nil,t4_281part0,Bool.and_self]
theorem t4_281checked : Checked tree [1,5,9,9] := by
  refine ⟨plan2111,valid2111,t4_281choices,?_⟩
  exact check_of_frontier tree 0 t4_281root t4_281jobs t4_281frontier t4_281all
theorem t4_282choices : plan2112.choices=[1,5,9,10].map (options 4 3) := by rfl


theorem t4_282part0 : t4_282jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_282frontier : t4_282root.frontier 0=t4_282jobs := by rfl
theorem t4_282all : t4_282jobs.all (Job.check tree)=true := by
  simp only [t4_282jobs,List.all_append,List.all_nil,t4_282part0,Bool.and_self]
theorem t4_282checked : Checked tree [1,5,9,10] := by
  refine ⟨plan2112,valid2112,t4_282choices,?_⟩
  exact check_of_frontier tree 0 t4_282root t4_282jobs t4_282frontier t4_282all
theorem t4_283choices : plan2113.choices=[1,5,10,7].map (options 4 3) := by rfl


theorem t4_283part0 : t4_283jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_283frontier : t4_283root.frontier 0=t4_283jobs := by rfl
theorem t4_283all : t4_283jobs.all (Job.check tree)=true := by
  simp only [t4_283jobs,List.all_append,List.all_nil,t4_283part0,Bool.and_self]
theorem t4_283checked : Checked tree [1,5,10,7] := by
  refine ⟨plan2113,valid2113,t4_283choices,?_⟩
  exact check_of_frontier tree 0 t4_283root t4_283jobs t4_283frontier t4_283all
theorem t4_284choices : plan2114.choices=[1,5,10,10].map (options 4 3) := by rfl


theorem t4_284part0 : t4_284jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_284frontier : t4_284root.frontier 0=t4_284jobs := by rfl
theorem t4_284all : t4_284jobs.all (Job.check tree)=true := by
  simp only [t4_284jobs,List.all_append,List.all_nil,t4_284part0,Bool.and_self]
theorem t4_284checked : Checked tree [1,5,10,10] := by
  refine ⟨plan2114,valid2114,t4_284choices,?_⟩
  exact check_of_frontier tree 0 t4_284root t4_284jobs t4_284frontier t4_284all
theorem t4_285choices : plan2115.choices=[1,6,6,6].map (options 4 3) := by rfl


theorem t4_285part0 : t4_285jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_285frontier : t4_285root.frontier 0=t4_285jobs := by rfl
theorem t4_285all : t4_285jobs.all (Job.check tree)=true := by
  simp only [t4_285jobs,List.all_append,List.all_nil,t4_285part0,Bool.and_self]
theorem t4_285checked : Checked tree [1,6,6,6] := by
  refine ⟨plan2115,valid2115,t4_285choices,?_⟩
  exact check_of_frontier tree 0 t4_285root t4_285jobs t4_285frontier t4_285all
theorem t4_286choices : plan2116.choices=[1,6,6,7].map (options 4 3) := by rfl


theorem t4_286part0 : t4_286jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_286frontier : t4_286root.frontier 0=t4_286jobs := by rfl
theorem t4_286all : t4_286jobs.all (Job.check tree)=true := by
  simp only [t4_286jobs,List.all_append,List.all_nil,t4_286part0,Bool.and_self]
theorem t4_286checked : Checked tree [1,6,6,7] := by
  refine ⟨plan2116,valid2116,t4_286choices,?_⟩
  exact check_of_frontier tree 0 t4_286root t4_286jobs t4_286frontier t4_286all
theorem t4_287choices : plan2117.choices=[1,6,6,10].map (options 4 3) := by rfl


theorem t4_287part0 : t4_287jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_287frontier : t4_287root.frontier 0=t4_287jobs := by rfl
theorem t4_287all : t4_287jobs.all (Job.check tree)=true := by
  simp only [t4_287jobs,List.all_append,List.all_nil,t4_287part0,Bool.and_self]
theorem t4_287checked : Checked tree [1,6,6,10] := by
  refine ⟨plan2117,valid2117,t4_287choices,?_⟩
  exact check_of_frontier tree 0 t4_287root t4_287jobs t4_287frontier t4_287all
theorem t4_288choices : plan2118.choices=[1,6,7,7].map (options 4 3) := by rfl


theorem t4_288part0 : t4_288jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_288frontier : t4_288root.frontier 0=t4_288jobs := by rfl
theorem t4_288all : t4_288jobs.all (Job.check tree)=true := by
  simp only [t4_288jobs,List.all_append,List.all_nil,t4_288part0,Bool.and_self]
theorem t4_288checked : Checked tree [1,6,7,7] := by
  refine ⟨plan2118,valid2118,t4_288choices,?_⟩
  exact check_of_frontier tree 0 t4_288root t4_288jobs t4_288frontier t4_288all
theorem t4_289choices : plan2119.choices=[1,6,10,7].map (options 4 3) := by rfl


theorem t4_289part0 : t4_289jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_289frontier : t4_289root.frontier 0=t4_289jobs := by rfl
theorem t4_289all : t4_289jobs.all (Job.check tree)=true := by
  simp only [t4_289jobs,List.all_append,List.all_nil,t4_289part0,Bool.and_self]
theorem t4_289checked : Checked tree [1,6,10,7] := by
  refine ⟨plan2119,valid2119,t4_289choices,?_⟩
  exact check_of_frontier tree 0 t4_289root t4_289jobs t4_289frontier t4_289all
theorem t4_290choices : plan2120.choices=[1,6,10,10].map (options 4 3) := by rfl


theorem t4_290part0 : t4_290jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_290frontier : t4_290root.frontier 0=t4_290jobs := by rfl
theorem t4_290all : t4_290jobs.all (Job.check tree)=true := by
  simp only [t4_290jobs,List.all_append,List.all_nil,t4_290part0,Bool.and_self]
theorem t4_290checked : Checked tree [1,6,10,10] := by
  refine ⟨plan2120,valid2120,t4_290choices,?_⟩
  exact check_of_frontier tree 0 t4_290root t4_290jobs t4_290frontier t4_290all
theorem t4_291choices : plan2121.choices=[1,7,7,7].map (options 4 3) := by rfl


theorem t4_291part0 : t4_291jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_291frontier : t4_291root.frontier 0=t4_291jobs := by rfl
theorem t4_291all : t4_291jobs.all (Job.check tree)=true := by
  simp only [t4_291jobs,List.all_append,List.all_nil,t4_291part0,Bool.and_self]
theorem t4_291checked : Checked tree [1,7,7,7] := by
  refine ⟨plan2121,valid2121,t4_291choices,?_⟩
  exact check_of_frontier tree 0 t4_291root t4_291jobs t4_291frontier t4_291all
theorem t4_292choices : plan1772.choices=[1,8,2,2].map (options 4 1) := by rfl


theorem t4_292part0 : t4_292jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_292frontier : t4_292root.frontier 0=t4_292jobs := by rfl
theorem t4_292all : t4_292jobs.all (Job.check tree)=true := by
  simp only [t4_292jobs,List.all_append,List.all_nil,t4_292part0,Bool.and_self]
theorem t4_292checked : Checked tree [1,8,2,2] := by
  refine ⟨plan1772,valid1772,t4_292choices,?_⟩
  exact check_of_frontier tree 0 t4_292root t4_292jobs t4_292frontier t4_292all
theorem t4_293choices : plan1773.choices=[1,8,2,3].map (options 4 1) := by rfl


theorem t4_293part0 : t4_293jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_293frontier : t4_293root.frontier 0=t4_293jobs := by rfl
theorem t4_293all : t4_293jobs.all (Job.check tree)=true := by
  simp only [t4_293jobs,List.all_append,List.all_nil,t4_293part0,Bool.and_self]
theorem t4_293checked : Checked tree [1,8,2,3] := by
  refine ⟨plan1773,valid1773,t4_293choices,?_⟩
  exact check_of_frontier tree 0 t4_293root t4_293jobs t4_293frontier t4_293all
theorem t4_294choices : plan1921.choices=[1,8,2,5].map (options 4 2) := by rfl


theorem t4_294part0 : t4_294jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_294frontier : t4_294root.frontier 0=t4_294jobs := by rfl
theorem t4_294all : t4_294jobs.all (Job.check tree)=true := by
  simp only [t4_294jobs,List.all_append,List.all_nil,t4_294part0,Bool.and_self]
theorem t4_294checked : Checked tree [1,8,2,5] := by
  refine ⟨plan1921,valid1921,t4_294choices,?_⟩
  exact check_of_frontier tree 0 t4_294root t4_294jobs t4_294frontier t4_294all
theorem t4_295choices : plan1922.choices=[1,8,2,6].map (options 4 2) := by rfl


theorem t4_295part0 : t4_295jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_295frontier : t4_295root.frontier 0=t4_295jobs := by rfl
theorem t4_295all : t4_295jobs.all (Job.check tree)=true := by
  simp only [t4_295jobs,List.all_append,List.all_nil,t4_295part0,Bool.and_self]
theorem t4_295checked : Checked tree [1,8,2,6] := by
  refine ⟨plan1922,valid1922,t4_295choices,?_⟩
  exact check_of_frontier tree 0 t4_295root t4_295jobs t4_295frontier t4_295all
theorem t4_296choices : plan1923.choices=[1,8,2,7].map (options 4 2) := by rfl


theorem t4_296part0 : t4_296jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_296frontier : t4_296root.frontier 0=t4_296jobs := by rfl
theorem t4_296all : t4_296jobs.all (Job.check tree)=true := by
  simp only [t4_296jobs,List.all_append,List.all_nil,t4_296part0,Bool.and_self]
theorem t4_296checked : Checked tree [1,8,2,7] := by
  refine ⟨plan1923,valid1923,t4_296choices,?_⟩
  exact check_of_frontier tree 0 t4_296root t4_296jobs t4_296frontier t4_296all
theorem t4_297choices : plan1924.choices=[1,8,2,9].map (options 4 2) := by rfl


theorem t4_297part0 : t4_297jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_297frontier : t4_297root.frontier 0=t4_297jobs := by rfl
theorem t4_297all : t4_297jobs.all (Job.check tree)=true := by
  simp only [t4_297jobs,List.all_append,List.all_nil,t4_297part0,Bool.and_self]
theorem t4_297checked : Checked tree [1,8,2,9] := by
  refine ⟨plan1924,valid1924,t4_297choices,?_⟩
  exact check_of_frontier tree 0 t4_297root t4_297jobs t4_297frontier t4_297all
theorem t4_298choices : plan1925.choices=[1,8,2,10].map (options 4 2) := by rfl


theorem t4_298part0 : t4_298jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_298frontier : t4_298root.frontier 0=t4_298jobs := by rfl
theorem t4_298all : t4_298jobs.all (Job.check tree)=true := by
  simp only [t4_298jobs,List.all_append,List.all_nil,t4_298part0,Bool.and_self]
theorem t4_298checked : Checked tree [1,8,2,10] := by
  refine ⟨plan1925,valid1925,t4_298choices,?_⟩
  exact check_of_frontier tree 0 t4_298root t4_298jobs t4_298frontier t4_298all
theorem t4_299choices : plan1774.choices=[1,8,3,3].map (options 4 1) := by rfl


theorem t4_299part0 : t4_299jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_299frontier : t4_299root.frontier 0=t4_299jobs := by rfl
theorem t4_299all : t4_299jobs.all (Job.check tree)=true := by
  simp only [t4_299jobs,List.all_append,List.all_nil,t4_299part0,Bool.and_self]
theorem t4_299checked : Checked tree [1,8,3,3] := by
  refine ⟨plan1774,valid1774,t4_299choices,?_⟩
  exact check_of_frontier tree 0 t4_299root t4_299jobs t4_299frontier t4_299all
theorem t4_300choices : plan1926.choices=[1,8,3,6].map (options 4 2) := by rfl


theorem t4_300part0 : t4_300jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_300frontier : t4_300root.frontier 0=t4_300jobs := by rfl
theorem t4_300all : t4_300jobs.all (Job.check tree)=true := by
  simp only [t4_300jobs,List.all_append,List.all_nil,t4_300part0,Bool.and_self]
theorem t4_300checked : Checked tree [1,8,3,6] := by
  refine ⟨plan1926,valid1926,t4_300choices,?_⟩
  exact check_of_frontier tree 0 t4_300root t4_300jobs t4_300frontier t4_300all
theorem t4_301choices : plan1927.choices=[1,8,3,7].map (options 4 2) := by rfl


theorem t4_301part0 : t4_301jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_301frontier : t4_301root.frontier 0=t4_301jobs := by rfl
theorem t4_301all : t4_301jobs.all (Job.check tree)=true := by
  simp only [t4_301jobs,List.all_append,List.all_nil,t4_301part0,Bool.and_self]
theorem t4_301checked : Checked tree [1,8,3,7] := by
  refine ⟨plan1927,valid1927,t4_301choices,?_⟩
  exact check_of_frontier tree 0 t4_301root t4_301jobs t4_301frontier t4_301all
theorem t4_302choices : plan1928.choices=[1,8,3,10].map (options 4 2) := by rfl


theorem t4_302part0 : t4_302jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_302frontier : t4_302root.frontier 0=t4_302jobs := by rfl
theorem t4_302all : t4_302jobs.all (Job.check tree)=true := by
  simp only [t4_302jobs,List.all_append,List.all_nil,t4_302part0,Bool.and_self]
theorem t4_302checked : Checked tree [1,8,3,10] := by
  refine ⟨plan1928,valid1928,t4_302choices,?_⟩
  exact check_of_frontier tree 0 t4_302root t4_302jobs t4_302frontier t4_302all
theorem t4_303choices : plan1929.choices=[1,8,5,3].map (options 4 2) := by rfl


theorem t4_303part0 : t4_303jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_303frontier : t4_303root.frontier 0=t4_303jobs := by rfl
theorem t4_303all : t4_303jobs.all (Job.check tree)=true := by
  simp only [t4_303jobs,List.all_append,List.all_nil,t4_303part0,Bool.and_self]
theorem t4_303checked : Checked tree [1,8,5,3] := by
  refine ⟨plan1929,valid1929,t4_303choices,?_⟩
  exact check_of_frontier tree 0 t4_303root t4_303jobs t4_303frontier t4_303all
theorem t4_304choices : plan2122.choices=[1,8,5,5].map (options 4 3) := by rfl


theorem t4_304part0 : t4_304jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_304frontier : t4_304root.frontier 0=t4_304jobs := by rfl
theorem t4_304all : t4_304jobs.all (Job.check tree)=true := by
  simp only [t4_304jobs,List.all_append,List.all_nil,t4_304part0,Bool.and_self]
theorem t4_304checked : Checked tree [1,8,5,5] := by
  refine ⟨plan2122,valid2122,t4_304choices,?_⟩
  exact check_of_frontier tree 0 t4_304root t4_304jobs t4_304frontier t4_304all
theorem t4_305choices : plan2123.choices=[1,8,5,6].map (options 4 3) := by rfl


theorem t4_305part0 : t4_305jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_305frontier : t4_305root.frontier 0=t4_305jobs := by rfl
theorem t4_305all : t4_305jobs.all (Job.check tree)=true := by
  simp only [t4_305jobs,List.all_append,List.all_nil,t4_305part0,Bool.and_self]
theorem t4_305checked : Checked tree [1,8,5,6] := by
  refine ⟨plan2123,valid2123,t4_305choices,?_⟩
  exact check_of_frontier tree 0 t4_305root t4_305jobs t4_305frontier t4_305all
theorem t4_306choices : plan2124.choices=[1,8,5,7].map (options 4 3) := by rfl


theorem t4_306part0 : t4_306jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_306frontier : t4_306root.frontier 0=t4_306jobs := by rfl
theorem t4_306all : t4_306jobs.all (Job.check tree)=true := by
  simp only [t4_306jobs,List.all_append,List.all_nil,t4_306part0,Bool.and_self]
theorem t4_306checked : Checked tree [1,8,5,7] := by
  refine ⟨plan2124,valid2124,t4_306choices,?_⟩
  exact check_of_frontier tree 0 t4_306root t4_306jobs t4_306frontier t4_306all
theorem t4_307choices : plan2125.choices=[1,8,5,9].map (options 4 3) := by rfl


theorem t4_307part0 : t4_307jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_307frontier : t4_307root.frontier 0=t4_307jobs := by rfl
theorem t4_307all : t4_307jobs.all (Job.check tree)=true := by
  simp only [t4_307jobs,List.all_append,List.all_nil,t4_307part0,Bool.and_self]
theorem t4_307checked : Checked tree [1,8,5,9] := by
  refine ⟨plan2125,valid2125,t4_307choices,?_⟩
  exact check_of_frontier tree 0 t4_307root t4_307jobs t4_307frontier t4_307all
theorem t4_308choices : plan2126.choices=[1,8,5,10].map (options 4 3) := by rfl


theorem t4_308part0 : t4_308jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_308frontier : t4_308root.frontier 0=t4_308jobs := by rfl
theorem t4_308all : t4_308jobs.all (Job.check tree)=true := by
  simp only [t4_308jobs,List.all_append,List.all_nil,t4_308part0,Bool.and_self]
theorem t4_308checked : Checked tree [1,8,5,10] := by
  refine ⟨plan2126,valid2126,t4_308choices,?_⟩
  exact check_of_frontier tree 0 t4_308root t4_308jobs t4_308frontier t4_308all
theorem t4_309choices : plan2127.choices=[1,8,6,6].map (options 4 3) := by rfl


theorem t4_309part0 : t4_309jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_309frontier : t4_309root.frontier 0=t4_309jobs := by rfl
theorem t4_309all : t4_309jobs.all (Job.check tree)=true := by
  simp only [t4_309jobs,List.all_append,List.all_nil,t4_309part0,Bool.and_self]
theorem t4_309checked : Checked tree [1,8,6,6] := by
  refine ⟨plan2127,valid2127,t4_309choices,?_⟩
  exact check_of_frontier tree 0 t4_309root t4_309jobs t4_309frontier t4_309all
theorem t4_310choices : plan2128.choices=[1,8,6,7].map (options 4 3) := by rfl


theorem t4_310part0 : t4_310jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_310frontier : t4_310root.frontier 0=t4_310jobs := by rfl
theorem t4_310all : t4_310jobs.all (Job.check tree)=true := by
  simp only [t4_310jobs,List.all_append,List.all_nil,t4_310part0,Bool.and_self]
theorem t4_310checked : Checked tree [1,8,6,7] := by
  refine ⟨plan2128,valid2128,t4_310choices,?_⟩
  exact check_of_frontier tree 0 t4_310root t4_310jobs t4_310frontier t4_310all
theorem t4_311choices : plan2129.choices=[1,8,6,10].map (options 4 3) := by rfl


theorem t4_311part0 : t4_311jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_311frontier : t4_311root.frontier 0=t4_311jobs := by rfl
theorem t4_311all : t4_311jobs.all (Job.check tree)=true := by
  simp only [t4_311jobs,List.all_append,List.all_nil,t4_311part0,Bool.and_self]
theorem t4_311checked : Checked tree [1,8,6,10] := by
  refine ⟨plan2129,valid2129,t4_311choices,?_⟩
  exact check_of_frontier tree 0 t4_311root t4_311jobs t4_311frontier t4_311all
theorem t4_312choices : plan2130.choices=[1,8,7,7].map (options 4 3) := by rfl


theorem t4_312part0 : t4_312jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_312frontier : t4_312root.frontier 0=t4_312jobs := by rfl
theorem t4_312all : t4_312jobs.all (Job.check tree)=true := by
  simp only [t4_312jobs,List.all_append,List.all_nil,t4_312part0,Bool.and_self]
theorem t4_312checked : Checked tree [1,8,7,7] := by
  refine ⟨plan2130,valid2130,t4_312choices,?_⟩
  exact check_of_frontier tree 0 t4_312root t4_312jobs t4_312frontier t4_312all
theorem t4_313choices : plan1930.choices=[1,8,8,3].map (options 4 2) := by rfl


theorem t4_313part0 : t4_313jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_313frontier : t4_313root.frontier 0=t4_313jobs := by rfl
theorem t4_313all : t4_313jobs.all (Job.check tree)=true := by
  simp only [t4_313jobs,List.all_append,List.all_nil,t4_313part0,Bool.and_self]
theorem t4_313checked : Checked tree [1,8,8,3] := by
  refine ⟨plan1930,valid1930,t4_313choices,?_⟩
  exact check_of_frontier tree 0 t4_313root t4_313jobs t4_313frontier t4_313all
theorem t4_314choices : plan2131.choices=[1,8,8,6].map (options 4 3) := by rfl


theorem t4_314part0 : t4_314jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_314frontier : t4_314root.frontier 0=t4_314jobs := by rfl
theorem t4_314all : t4_314jobs.all (Job.check tree)=true := by
  simp only [t4_314jobs,List.all_append,List.all_nil,t4_314part0,Bool.and_self]
theorem t4_314checked : Checked tree [1,8,8,6] := by
  refine ⟨plan2131,valid2131,t4_314choices,?_⟩
  exact check_of_frontier tree 0 t4_314root t4_314jobs t4_314frontier t4_314all
theorem t4_315choices : plan2132.choices=[1,8,8,7].map (options 4 3) := by rfl


theorem t4_315part0 : t4_315jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_315frontier : t4_315root.frontier 0=t4_315jobs := by rfl
theorem t4_315all : t4_315jobs.all (Job.check tree)=true := by
  simp only [t4_315jobs,List.all_append,List.all_nil,t4_315part0,Bool.and_self]
theorem t4_315checked : Checked tree [1,8,8,7] := by
  refine ⟨plan2132,valid2132,t4_315choices,?_⟩
  exact check_of_frontier tree 0 t4_315root t4_315jobs t4_315frontier t4_315all
theorem t4_316choices : plan2133.choices=[1,8,8,10].map (options 4 3) := by rfl


theorem t4_316part0 : t4_316jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_316frontier : t4_316root.frontier 0=t4_316jobs := by rfl
theorem t4_316all : t4_316jobs.all (Job.check tree)=true := by
  simp only [t4_316jobs,List.all_append,List.all_nil,t4_316part0,Bool.and_self]
theorem t4_316checked : Checked tree [1,8,8,10] := by
  refine ⟨plan2133,valid2133,t4_316choices,?_⟩
  exact check_of_frontier tree 0 t4_316root t4_316jobs t4_316frontier t4_316all
theorem t4_317choices : plan1931.choices=[1,8,9,3].map (options 4 2) := by rfl


theorem t4_317part0 : t4_317jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_317frontier : t4_317root.frontier 0=t4_317jobs := by rfl
theorem t4_317all : t4_317jobs.all (Job.check tree)=true := by
  simp only [t4_317jobs,List.all_append,List.all_nil,t4_317part0,Bool.and_self]
theorem t4_317checked : Checked tree [1,8,9,3] := by
  refine ⟨plan1931,valid1931,t4_317choices,?_⟩
  exact check_of_frontier tree 0 t4_317root t4_317jobs t4_317frontier t4_317all
theorem t4_318choices : plan2134.choices=[1,8,9,6].map (options 4 3) := by rfl


theorem t4_318part0 : t4_318jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_318frontier : t4_318root.frontier 0=t4_318jobs := by rfl
theorem t4_318all : t4_318jobs.all (Job.check tree)=true := by
  simp only [t4_318jobs,List.all_append,List.all_nil,t4_318part0,Bool.and_self]
theorem t4_318checked : Checked tree [1,8,9,6] := by
  refine ⟨plan2134,valid2134,t4_318choices,?_⟩
  exact check_of_frontier tree 0 t4_318root t4_318jobs t4_318frontier t4_318all
theorem t4_319choices : plan2135.choices=[1,8,9,7].map (options 4 3) := by rfl


theorem t4_319part0 : t4_319jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_319frontier : t4_319root.frontier 0=t4_319jobs := by rfl
theorem t4_319all : t4_319jobs.all (Job.check tree)=true := by
  simp only [t4_319jobs,List.all_append,List.all_nil,t4_319part0,Bool.and_self]
theorem t4_319checked : Checked tree [1,8,9,7] := by
  refine ⟨plan2135,valid2135,t4_319choices,?_⟩
  exact check_of_frontier tree 0 t4_319root t4_319jobs t4_319frontier t4_319all
theorem t4_320choices : plan2136.choices=[1,8,9,9].map (options 4 3) := by rfl


theorem t4_320part0 : t4_320jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_320frontier : t4_320root.frontier 0=t4_320jobs := by rfl
theorem t4_320all : t4_320jobs.all (Job.check tree)=true := by
  simp only [t4_320jobs,List.all_append,List.all_nil,t4_320part0,Bool.and_self]
theorem t4_320checked : Checked tree [1,8,9,9] := by
  refine ⟨plan2136,valid2136,t4_320choices,?_⟩
  exact check_of_frontier tree 0 t4_320root t4_320jobs t4_320frontier t4_320all
theorem t4_321choices : plan2137.choices=[1,8,9,10].map (options 4 3) := by rfl


theorem t4_321part0 : t4_321jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_321frontier : t4_321root.frontier 0=t4_321jobs := by rfl
theorem t4_321all : t4_321jobs.all (Job.check tree)=true := by
  simp only [t4_321jobs,List.all_append,List.all_nil,t4_321part0,Bool.and_self]
theorem t4_321checked : Checked tree [1,8,9,10] := by
  refine ⟨plan2137,valid2137,t4_321choices,?_⟩
  exact check_of_frontier tree 0 t4_321root t4_321jobs t4_321frontier t4_321all
theorem t4_322choices : plan2138.choices=[1,8,10,7].map (options 4 3) := by rfl


theorem t4_322part0 : t4_322jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_322frontier : t4_322root.frontier 0=t4_322jobs := by rfl
theorem t4_322all : t4_322jobs.all (Job.check tree)=true := by
  simp only [t4_322jobs,List.all_append,List.all_nil,t4_322part0,Bool.and_self]
theorem t4_322checked : Checked tree [1,8,10,7] := by
  refine ⟨plan2138,valid2138,t4_322choices,?_⟩
  exact check_of_frontier tree 0 t4_322root t4_322jobs t4_322frontier t4_322all
theorem t4_323choices : plan2139.choices=[1,8,10,10].map (options 4 3) := by rfl


theorem t4_323part0 : t4_323jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_323frontier : t4_323root.frontier 0=t4_323jobs := by rfl
theorem t4_323all : t4_323jobs.all (Job.check tree)=true := by
  simp only [t4_323jobs,List.all_append,List.all_nil,t4_323part0,Bool.and_self]
theorem t4_323checked : Checked tree [1,8,10,10] := by
  refine ⟨plan2139,valid2139,t4_323choices,?_⟩
  exact check_of_frontier tree 0 t4_323root t4_323jobs t4_323frontier t4_323all
theorem t4_324choices : plan1775.choices=[1,9,3,3].map (options 4 1) := by rfl


theorem t4_324part0 : t4_324jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_324frontier : t4_324root.frontier 0=t4_324jobs := by rfl
theorem t4_324all : t4_324jobs.all (Job.check tree)=true := by
  simp only [t4_324jobs,List.all_append,List.all_nil,t4_324part0,Bool.and_self]
theorem t4_324checked : Checked tree [1,9,3,3] := by
  refine ⟨plan1775,valid1775,t4_324choices,?_⟩
  exact check_of_frontier tree 0 t4_324root t4_324jobs t4_324frontier t4_324all
theorem t4_325choices : plan1932.choices=[1,9,3,6].map (options 4 2) := by rfl


theorem t4_325part0 : t4_325jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_325frontier : t4_325root.frontier 0=t4_325jobs := by rfl
theorem t4_325all : t4_325jobs.all (Job.check tree)=true := by
  simp only [t4_325jobs,List.all_append,List.all_nil,t4_325part0,Bool.and_self]
theorem t4_325checked : Checked tree [1,9,3,6] := by
  refine ⟨plan1932,valid1932,t4_325choices,?_⟩
  exact check_of_frontier tree 0 t4_325root t4_325jobs t4_325frontier t4_325all
theorem t4_326choices : plan1933.choices=[1,9,3,7].map (options 4 2) := by rfl


theorem t4_326part0 : t4_326jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_326frontier : t4_326root.frontier 0=t4_326jobs := by rfl
theorem t4_326all : t4_326jobs.all (Job.check tree)=true := by
  simp only [t4_326jobs,List.all_append,List.all_nil,t4_326part0,Bool.and_self]
theorem t4_326checked : Checked tree [1,9,3,7] := by
  refine ⟨plan1933,valid1933,t4_326choices,?_⟩
  exact check_of_frontier tree 0 t4_326root t4_326jobs t4_326frontier t4_326all
theorem t4_327choices : plan1934.choices=[1,9,3,10].map (options 4 2) := by rfl


theorem t4_327part0 : t4_327jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_327frontier : t4_327root.frontier 0=t4_327jobs := by rfl
theorem t4_327all : t4_327jobs.all (Job.check tree)=true := by
  simp only [t4_327jobs,List.all_append,List.all_nil,t4_327part0,Bool.and_self]
theorem t4_327checked : Checked tree [1,9,3,10] := by
  refine ⟨plan1934,valid1934,t4_327choices,?_⟩
  exact check_of_frontier tree 0 t4_327root t4_327jobs t4_327frontier t4_327all
theorem t4_328choices : plan2140.choices=[1,9,6,6].map (options 4 3) := by rfl


theorem t4_328part0 : t4_328jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_328frontier : t4_328root.frontier 0=t4_328jobs := by rfl
theorem t4_328all : t4_328jobs.all (Job.check tree)=true := by
  simp only [t4_328jobs,List.all_append,List.all_nil,t4_328part0,Bool.and_self]
theorem t4_328checked : Checked tree [1,9,6,6] := by
  refine ⟨plan2140,valid2140,t4_328choices,?_⟩
  exact check_of_frontier tree 0 t4_328root t4_328jobs t4_328frontier t4_328all
theorem t4_329choices : plan2141.choices=[1,9,6,7].map (options 4 3) := by rfl


theorem t4_329part0 : t4_329jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_329frontier : t4_329root.frontier 0=t4_329jobs := by rfl
theorem t4_329all : t4_329jobs.all (Job.check tree)=true := by
  simp only [t4_329jobs,List.all_append,List.all_nil,t4_329part0,Bool.and_self]
theorem t4_329checked : Checked tree [1,9,6,7] := by
  refine ⟨plan2141,valid2141,t4_329choices,?_⟩
  exact check_of_frontier tree 0 t4_329root t4_329jobs t4_329frontier t4_329all
theorem t4_330choices : plan2142.choices=[1,9,6,10].map (options 4 3) := by rfl


theorem t4_330part0 : t4_330jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_330frontier : t4_330root.frontier 0=t4_330jobs := by rfl
theorem t4_330all : t4_330jobs.all (Job.check tree)=true := by
  simp only [t4_330jobs,List.all_append,List.all_nil,t4_330part0,Bool.and_self]
theorem t4_330checked : Checked tree [1,9,6,10] := by
  refine ⟨plan2142,valid2142,t4_330choices,?_⟩
  exact check_of_frontier tree 0 t4_330root t4_330jobs t4_330frontier t4_330all
theorem t4_331choices : plan2143.choices=[1,9,7,7].map (options 4 3) := by rfl


theorem t4_331part0 : t4_331jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_331frontier : t4_331root.frontier 0=t4_331jobs := by rfl
theorem t4_331all : t4_331jobs.all (Job.check tree)=true := by
  simp only [t4_331jobs,List.all_append,List.all_nil,t4_331part0,Bool.and_self]
theorem t4_331checked : Checked tree [1,9,7,7] := by
  refine ⟨plan2143,valid2143,t4_331choices,?_⟩
  exact check_of_frontier tree 0 t4_331root t4_331jobs t4_331frontier t4_331all
theorem t4_332choices : plan1935.choices=[1,9,9,3].map (options 4 2) := by rfl


theorem t4_332part0 : t4_332jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_332frontier : t4_332root.frontier 0=t4_332jobs := by rfl
theorem t4_332all : t4_332jobs.all (Job.check tree)=true := by
  simp only [t4_332jobs,List.all_append,List.all_nil,t4_332part0,Bool.and_self]
theorem t4_332checked : Checked tree [1,9,9,3] := by
  refine ⟨plan1935,valid1935,t4_332choices,?_⟩
  exact check_of_frontier tree 0 t4_332root t4_332jobs t4_332frontier t4_332all
theorem t4_333choices : plan2144.choices=[1,9,9,6].map (options 4 3) := by rfl


theorem t4_333part0 : t4_333jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_333frontier : t4_333root.frontier 0=t4_333jobs := by rfl
theorem t4_333all : t4_333jobs.all (Job.check tree)=true := by
  simp only [t4_333jobs,List.all_append,List.all_nil,t4_333part0,Bool.and_self]
theorem t4_333checked : Checked tree [1,9,9,6] := by
  refine ⟨plan2144,valid2144,t4_333choices,?_⟩
  exact check_of_frontier tree 0 t4_333root t4_333jobs t4_333frontier t4_333all
theorem t4_334choices : plan2145.choices=[1,9,9,7].map (options 4 3) := by rfl


theorem t4_334part0 : t4_334jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_334frontier : t4_334root.frontier 0=t4_334jobs := by rfl
theorem t4_334all : t4_334jobs.all (Job.check tree)=true := by
  simp only [t4_334jobs,List.all_append,List.all_nil,t4_334part0,Bool.and_self]
theorem t4_334checked : Checked tree [1,9,9,7] := by
  refine ⟨plan2145,valid2145,t4_334choices,?_⟩
  exact check_of_frontier tree 0 t4_334root t4_334jobs t4_334frontier t4_334all
theorem t4_335choices : plan2146.choices=[1,9,9,9].map (options 4 3) := by rfl


theorem t4_335part0 : t4_335jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_335frontier : t4_335root.frontier 0=t4_335jobs := by rfl
theorem t4_335all : t4_335jobs.all (Job.check tree)=true := by
  simp only [t4_335jobs,List.all_append,List.all_nil,t4_335part0,Bool.and_self]
theorem t4_335checked : Checked tree [1,9,9,9] := by
  refine ⟨plan2146,valid2146,t4_335choices,?_⟩
  exact check_of_frontier tree 0 t4_335root t4_335jobs t4_335frontier t4_335all
theorem t4_336choices : plan2147.choices=[1,9,9,10].map (options 4 3) := by rfl


theorem t4_336part0 : t4_336jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_336frontier : t4_336root.frontier 0=t4_336jobs := by rfl
theorem t4_336all : t4_336jobs.all (Job.check tree)=true := by
  simp only [t4_336jobs,List.all_append,List.all_nil,t4_336part0,Bool.and_self]
theorem t4_336checked : Checked tree [1,9,9,10] := by
  refine ⟨plan2147,valid2147,t4_336choices,?_⟩
  exact check_of_frontier tree 0 t4_336root t4_336jobs t4_336frontier t4_336all
theorem t4_337choices : plan2148.choices=[1,9,10,7].map (options 4 3) := by rfl


theorem t4_337part0 : t4_337jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_337frontier : t4_337root.frontier 0=t4_337jobs := by rfl
theorem t4_337all : t4_337jobs.all (Job.check tree)=true := by
  simp only [t4_337jobs,List.all_append,List.all_nil,t4_337part0,Bool.and_self]
theorem t4_337checked : Checked tree [1,9,10,7] := by
  refine ⟨plan2148,valid2148,t4_337choices,?_⟩
  exact check_of_frontier tree 0 t4_337root t4_337jobs t4_337frontier t4_337all
theorem t4_338choices : plan2149.choices=[1,9,10,10].map (options 4 3) := by rfl


theorem t4_338part0 : t4_338jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_338frontier : t4_338root.frontier 0=t4_338jobs := by rfl
theorem t4_338all : t4_338jobs.all (Job.check tree)=true := by
  simp only [t4_338jobs,List.all_append,List.all_nil,t4_338part0,Bool.and_self]
theorem t4_338checked : Checked tree [1,9,10,10] := by
  refine ⟨plan2149,valid2149,t4_338choices,?_⟩
  exact check_of_frontier tree 0 t4_338root t4_338jobs t4_338frontier t4_338all
theorem t4_339choices : plan2150.choices=[1,10,7,7].map (options 4 3) := by rfl


theorem t4_339part0 : t4_339jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_339frontier : t4_339root.frontier 0=t4_339jobs := by rfl
theorem t4_339all : t4_339jobs.all (Job.check tree)=true := by
  simp only [t4_339jobs,List.all_append,List.all_nil,t4_339part0,Bool.and_self]
theorem t4_339checked : Checked tree [1,10,7,7] := by
  refine ⟨plan2150,valid2150,t4_339choices,?_⟩
  exact check_of_frontier tree 0 t4_339root t4_339jobs t4_339frontier t4_339all
theorem t4_340choices : plan2151.choices=[1,10,10,7].map (options 4 3) := by rfl


theorem t4_340part0 : t4_340jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_340frontier : t4_340root.frontier 0=t4_340jobs := by rfl
theorem t4_340all : t4_340jobs.all (Job.check tree)=true := by
  simp only [t4_340jobs,List.all_append,List.all_nil,t4_340part0,Bool.and_self]
theorem t4_340checked : Checked tree [1,10,10,7] := by
  refine ⟨plan2151,valid2151,t4_340choices,?_⟩
  exact check_of_frontier tree 0 t4_340root t4_340jobs t4_340frontier t4_340all
theorem t4_341choices : plan2152.choices=[1,10,10,10].map (options 4 3) := by rfl


theorem t4_341part0 : t4_341jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_341frontier : t4_341root.frontier 0=t4_341jobs := by rfl
theorem t4_341all : t4_341jobs.all (Job.check tree)=true := by
  simp only [t4_341jobs,List.all_append,List.all_nil,t4_341part0,Bool.and_self]
theorem t4_341checked : Checked tree [1,10,10,10] := by
  refine ⟨plan2152,valid2152,t4_341choices,?_⟩
  exact check_of_frontier tree 0 t4_341root t4_341jobs t4_341frontier t4_341all
theorem t4_342choices : plan1708.choices=[2,2,2,2].map (options 4 0) := by rfl


theorem t4_342part0 : t4_342jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_342frontier : t4_342root.frontier 0=t4_342jobs := by rfl
theorem t4_342all : t4_342jobs.all (Job.check tree)=true := by
  simp only [t4_342jobs,List.all_append,List.all_nil,t4_342part0,Bool.and_self]
theorem t4_342checked : Checked tree [2,2,2,2] := by
  refine ⟨plan1708,valid1708,t4_342choices,?_⟩
  exact check_of_frontier tree 0 t4_342root t4_342jobs t4_342frontier t4_342all
theorem t4_343choices : plan1709.choices=[2,2,2,3].map (options 4 0) := by rfl


theorem t4_343part0 : t4_343jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_343frontier : t4_343root.frontier 0=t4_343jobs := by rfl
theorem t4_343all : t4_343jobs.all (Job.check tree)=true := by
  simp only [t4_343jobs,List.all_append,List.all_nil,t4_343part0,Bool.and_self]
theorem t4_343checked : Checked tree [2,2,2,3] := by
  refine ⟨plan1709,valid1709,t4_343choices,?_⟩
  exact check_of_frontier tree 0 t4_343root t4_343jobs t4_343frontier t4_343all
theorem t4_344choices : plan1776.choices=[2,2,2,5].map (options 4 1) := by rfl


theorem t4_344part0 : t4_344jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_344frontier : t4_344root.frontier 0=t4_344jobs := by rfl
theorem t4_344all : t4_344jobs.all (Job.check tree)=true := by
  simp only [t4_344jobs,List.all_append,List.all_nil,t4_344part0,Bool.and_self]
theorem t4_344checked : Checked tree [2,2,2,5] := by
  refine ⟨plan1776,valid1776,t4_344choices,?_⟩
  exact check_of_frontier tree 0 t4_344root t4_344jobs t4_344frontier t4_344all
theorem t4_345choices : plan1777.choices=[2,2,2,6].map (options 4 1) := by rfl


theorem t4_345part0 : t4_345jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_345frontier : t4_345root.frontier 0=t4_345jobs := by rfl
theorem t4_345all : t4_345jobs.all (Job.check tree)=true := by
  simp only [t4_345jobs,List.all_append,List.all_nil,t4_345part0,Bool.and_self]
theorem t4_345checked : Checked tree [2,2,2,6] := by
  refine ⟨plan1777,valid1777,t4_345choices,?_⟩
  exact check_of_frontier tree 0 t4_345root t4_345jobs t4_345frontier t4_345all
theorem t4_346choices : plan1778.choices=[2,2,2,7].map (options 4 1) := by rfl


theorem t4_346part0 : t4_346jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_346frontier : t4_346root.frontier 0=t4_346jobs := by rfl
theorem t4_346all : t4_346jobs.all (Job.check tree)=true := by
  simp only [t4_346jobs,List.all_append,List.all_nil,t4_346part0,Bool.and_self]
theorem t4_346checked : Checked tree [2,2,2,7] := by
  refine ⟨plan1778,valid1778,t4_346choices,?_⟩
  exact check_of_frontier tree 0 t4_346root t4_346jobs t4_346frontier t4_346all
theorem t4_347choices : plan1779.choices=[2,2,2,9].map (options 4 1) := by rfl


theorem t4_347part0 : t4_347jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_347frontier : t4_347root.frontier 0=t4_347jobs := by rfl
theorem t4_347all : t4_347jobs.all (Job.check tree)=true := by
  simp only [t4_347jobs,List.all_append,List.all_nil,t4_347part0,Bool.and_self]
theorem t4_347checked : Checked tree [2,2,2,9] := by
  refine ⟨plan1779,valid1779,t4_347choices,?_⟩
  exact check_of_frontier tree 0 t4_347root t4_347jobs t4_347frontier t4_347all
theorem t4_348choices : plan1780.choices=[2,2,2,10].map (options 4 1) := by rfl


theorem t4_348part0 : t4_348jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_348frontier : t4_348root.frontier 0=t4_348jobs := by rfl
theorem t4_348all : t4_348jobs.all (Job.check tree)=true := by
  simp only [t4_348jobs,List.all_append,List.all_nil,t4_348part0,Bool.and_self]
theorem t4_348checked : Checked tree [2,2,2,10] := by
  refine ⟨plan1780,valid1780,t4_348choices,?_⟩
  exact check_of_frontier tree 0 t4_348root t4_348jobs t4_348frontier t4_348all
theorem t4_349choices : plan1710.choices=[2,2,3,3].map (options 4 0) := by rfl


theorem t4_349part0 : t4_349jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_349frontier : t4_349root.frontier 0=t4_349jobs := by rfl
theorem t4_349all : t4_349jobs.all (Job.check tree)=true := by
  simp only [t4_349jobs,List.all_append,List.all_nil,t4_349part0,Bool.and_self]
theorem t4_349checked : Checked tree [2,2,3,3] := by
  refine ⟨plan1710,valid1710,t4_349choices,?_⟩
  exact check_of_frontier tree 0 t4_349root t4_349jobs t4_349frontier t4_349all
theorem t4_350choices : plan1781.choices=[2,2,3,6].map (options 4 1) := by rfl


theorem t4_350part0 : t4_350jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_350frontier : t4_350root.frontier 0=t4_350jobs := by rfl
theorem t4_350all : t4_350jobs.all (Job.check tree)=true := by
  simp only [t4_350jobs,List.all_append,List.all_nil,t4_350part0,Bool.and_self]
theorem t4_350checked : Checked tree [2,2,3,6] := by
  refine ⟨plan1781,valid1781,t4_350choices,?_⟩
  exact check_of_frontier tree 0 t4_350root t4_350jobs t4_350frontier t4_350all
theorem t4_351choices : plan1782.choices=[2,2,3,7].map (options 4 1) := by rfl


theorem t4_351part0 : t4_351jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_351frontier : t4_351root.frontier 0=t4_351jobs := by rfl
theorem t4_351all : t4_351jobs.all (Job.check tree)=true := by
  simp only [t4_351jobs,List.all_append,List.all_nil,t4_351part0,Bool.and_self]
theorem t4_351checked : Checked tree [2,2,3,7] := by
  refine ⟨plan1782,valid1782,t4_351choices,?_⟩
  exact check_of_frontier tree 0 t4_351root t4_351jobs t4_351frontier t4_351all
theorem t4_352choices : plan1783.choices=[2,2,3,10].map (options 4 1) := by rfl


theorem t4_352part0 : t4_352jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_352frontier : t4_352root.frontier 0=t4_352jobs := by rfl
theorem t4_352all : t4_352jobs.all (Job.check tree)=true := by
  simp only [t4_352jobs,List.all_append,List.all_nil,t4_352part0,Bool.and_self]
theorem t4_352checked : Checked tree [2,2,3,10] := by
  refine ⟨plan1783,valid1783,t4_352choices,?_⟩
  exact check_of_frontier tree 0 t4_352root t4_352jobs t4_352frontier t4_352all
theorem t4_353choices : plan1784.choices=[2,2,5,3].map (options 4 1) := by rfl


theorem t4_353part0 : t4_353jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_353frontier : t4_353root.frontier 0=t4_353jobs := by rfl
theorem t4_353all : t4_353jobs.all (Job.check tree)=true := by
  simp only [t4_353jobs,List.all_append,List.all_nil,t4_353part0,Bool.and_self]
theorem t4_353checked : Checked tree [2,2,5,3] := by
  refine ⟨plan1784,valid1784,t4_353choices,?_⟩
  exact check_of_frontier tree 0 t4_353root t4_353jobs t4_353frontier t4_353all
theorem t4_354choices : plan1936.choices=[2,2,5,5].map (options 4 2) := by rfl


theorem t4_354part0 : t4_354jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_354frontier : t4_354root.frontier 0=t4_354jobs := by rfl
theorem t4_354all : t4_354jobs.all (Job.check tree)=true := by
  simp only [t4_354jobs,List.all_append,List.all_nil,t4_354part0,Bool.and_self]
theorem t4_354checked : Checked tree [2,2,5,5] := by
  refine ⟨plan1936,valid1936,t4_354choices,?_⟩
  exact check_of_frontier tree 0 t4_354root t4_354jobs t4_354frontier t4_354all
theorem t4_355choices : plan1937.choices=[2,2,5,6].map (options 4 2) := by rfl


theorem t4_355part0 : t4_355jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_355frontier : t4_355root.frontier 0=t4_355jobs := by rfl
theorem t4_355all : t4_355jobs.all (Job.check tree)=true := by
  simp only [t4_355jobs,List.all_append,List.all_nil,t4_355part0,Bool.and_self]
theorem t4_355checked : Checked tree [2,2,5,6] := by
  refine ⟨plan1937,valid1937,t4_355choices,?_⟩
  exact check_of_frontier tree 0 t4_355root t4_355jobs t4_355frontier t4_355all
theorem t4_356choices : plan1938.choices=[2,2,5,7].map (options 4 2) := by rfl


theorem t4_356part0 : t4_356jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_356frontier : t4_356root.frontier 0=t4_356jobs := by rfl
theorem t4_356all : t4_356jobs.all (Job.check tree)=true := by
  simp only [t4_356jobs,List.all_append,List.all_nil,t4_356part0,Bool.and_self]
theorem t4_356checked : Checked tree [2,2,5,7] := by
  refine ⟨plan1938,valid1938,t4_356choices,?_⟩
  exact check_of_frontier tree 0 t4_356root t4_356jobs t4_356frontier t4_356all
theorem t4_357choices : plan1939.choices=[2,2,5,9].map (options 4 2) := by rfl


theorem t4_357part0 : t4_357jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_357frontier : t4_357root.frontier 0=t4_357jobs := by rfl
theorem t4_357all : t4_357jobs.all (Job.check tree)=true := by
  simp only [t4_357jobs,List.all_append,List.all_nil,t4_357part0,Bool.and_self]
theorem t4_357checked : Checked tree [2,2,5,9] := by
  refine ⟨plan1939,valid1939,t4_357choices,?_⟩
  exact check_of_frontier tree 0 t4_357root t4_357jobs t4_357frontier t4_357all
theorem t4_358choices : plan1940.choices=[2,2,5,10].map (options 4 2) := by rfl


theorem t4_358part0 : t4_358jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_358frontier : t4_358root.frontier 0=t4_358jobs := by rfl
theorem t4_358all : t4_358jobs.all (Job.check tree)=true := by
  simp only [t4_358jobs,List.all_append,List.all_nil,t4_358part0,Bool.and_self]
theorem t4_358checked : Checked tree [2,2,5,10] := by
  refine ⟨plan1940,valid1940,t4_358choices,?_⟩
  exact check_of_frontier tree 0 t4_358root t4_358jobs t4_358frontier t4_358all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks001 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_350checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_351checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_352checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_353checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_354checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_355checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_213checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_356checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_226checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_357checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_358checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_227checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_228checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_229checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_230checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_231checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_232checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_233checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_234checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_235checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_214checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_236checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_237checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_238checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_239checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_240checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_241checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_242checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_243checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_244checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_245checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_215checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_246checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_247checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_248checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_249checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_250checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_251checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_252checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_253checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_254checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_255checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_216checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_256checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_257checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_258checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_259checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_260checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_261checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_262checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_263checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_264checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_265checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_266checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_217checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_267checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_268checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_269checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_270checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_271checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_272checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_273checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_274checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_275checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_276checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_218checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_277checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_278checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_279checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_280checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_281checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_282checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_283checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_284checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_285checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_286checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_219checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_287checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_288checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_289checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_290checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_291checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_292checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_293checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_294checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_295checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_296checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_220checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_297checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_298checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_299checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_300checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_301checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_302checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_303checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_304checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_305checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_306checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_221checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_307checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_308checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_309checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_310checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_311checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_312checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_313checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_314checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_315checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_316checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_222checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_317checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_318checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_319checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_320checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_321checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_322checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_323checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_324checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_325checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_326checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_223checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_327checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_328checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_329checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_330checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_331checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_332checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_333checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_334checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_335checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_336checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_224checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_337checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_338checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_339checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_340checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_341checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_342checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_343checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_344checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_345checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_346checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_225checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_347checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_348checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_349checked⟩
