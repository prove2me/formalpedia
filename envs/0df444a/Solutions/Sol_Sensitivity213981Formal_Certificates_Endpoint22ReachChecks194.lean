-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks194
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T03:16:09.716913+00:00
-- url     : https://prove2.me/submissions/d96de295-e387-4a6f-aa4c-6ba7e824d8f6

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks194
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks194
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans038
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans065
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans087
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans095
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans096
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

































































































































theorem valid161 : plan161.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid162 : plan162.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid163 : plan163.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid164 : plan164.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid165 : plan165.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid166 : plan166.Valid := valid_step _ _ _ valid0 (by decide +kernel)




















































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







































































































theorem valid628 : plan628.Valid := valid_step _ _ _ valid161 (by decide +kernel)

theorem valid629 : plan629.Valid := valid_step _ _ _ valid162 (by decide +kernel)

theorem valid630 : plan630.Valid := valid_step _ _ _ valid163 (by decide +kernel)

theorem valid631 : plan631.Valid := valid_step _ _ _ valid164 (by decide +kernel)

theorem valid632 : plan632.Valid := valid_step _ _ _ valid165 (by decide +kernel)

theorem valid633 : plan633.Valid := valid_step _ _ _ valid166 (by decide +kernel)














































































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















































































































theorem valid1688 : plan1688.Valid := valid_step _ _ _ valid628 (by decide +kernel)

theorem valid1689 : plan1689.Valid := valid_step _ _ _ valid629 (by decide +kernel)

theorem valid1690 : plan1690.Valid := valid_step _ _ _ valid630 (by decide +kernel)

theorem valid1691 : plan1691.Valid := valid_step _ _ _ valid631 (by decide +kernel)

theorem valid1692 : plan1692.Valid := valid_step _ _ _ valid632 (by decide +kernel)

theorem valid1693 : plan1693.Valid := valid_step _ _ _ valid633 (by decide +kernel)






































































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







theorem valid3652 : plan3652.Valid := valid_step _ _ _ valid1688 (by decide +kernel)

theorem valid3653 : plan3653.Valid := valid_step _ _ _ valid1689 (by decide +kernel)

theorem valid3654 : plan3654.Valid := valid_step _ _ _ valid1690 (by decide +kernel)

theorem valid3655 : plan3655.Valid := valid_step _ _ _ valid1691 (by decide +kernel)

theorem valid3656 : plan3656.Valid := valid_step _ _ _ valid1692 (by decide +kernel)

theorem valid3657 : plan3657.Valid := valid_step _ _ _ valid1693 (by decide +kernel)














































































































































































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











































theorem valid6262 : plan6262.Valid := valid_step _ _ _ valid3652 (by decide +kernel)

theorem valid6263 : plan6263.Valid := valid_step _ _ _ valid3653 (by decide +kernel)

theorem valid6264 : plan6264.Valid := valid_step _ _ _ valid3653 (by decide +kernel)

theorem valid6265 : plan6265.Valid := valid_step _ _ _ valid3653 (by decide +kernel)

theorem valid6266 : plan6266.Valid := valid_step _ _ _ valid3654 (by decide +kernel)

theorem valid6267 : plan6267.Valid := valid_step _ _ _ valid3654 (by decide +kernel)

theorem valid6268 : plan6268.Valid := valid_step _ _ _ valid3654 (by decide +kernel)

theorem valid6269 : plan6269.Valid := valid_step _ _ _ valid3655 (by decide +kernel)

theorem valid6270 : plan6270.Valid := valid_step _ _ _ valid3655 (by decide +kernel)

theorem valid6271 : plan6271.Valid := valid_step _ _ _ valid3655 (by decide +kernel)

theorem valid6272 : plan6272.Valid := valid_step _ _ _ valid3656 (by decide +kernel)

theorem valid6273 : plan6273.Valid := valid_step _ _ _ valid3656 (by decide +kernel)

theorem valid6274 : plan6274.Valid := valid_step _ _ _ valid3656 (by decide +kernel)

theorem valid6275 : plan6275.Valid := valid_step _ _ _ valid3657 (by decide +kernel)


























































































































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







































































theorem valid8388 : plan8388.Valid := valid_step _ _ _ valid6262 (by decide +kernel)

theorem valid8389 : plan8389.Valid := valid_step _ _ _ valid6263 (by decide +kernel)

theorem valid8390 : plan8390.Valid := valid_step _ _ _ valid6264 (by decide +kernel)

theorem valid8391 : plan8391.Valid := valid_step _ _ _ valid6265 (by decide +kernel)

theorem valid8392 : plan8392.Valid := valid_step _ _ _ valid6267 (by decide +kernel)

theorem valid8393 : plan8393.Valid := valid_step _ _ _ valid6266 (by decide +kernel)

theorem valid8394 : plan8394.Valid := valid_step _ _ _ valid6267 (by decide +kernel)

theorem valid8395 : plan8395.Valid := valid_step _ _ _ valid6268 (by decide +kernel)

theorem valid8396 : plan8396.Valid := valid_step _ _ _ valid6267 (by decide +kernel)

theorem valid8397 : plan8397.Valid := valid_step _ _ _ valid6267 (by decide +kernel)

theorem valid8398 : plan8398.Valid := valid_step _ _ _ valid6268 (by decide +kernel)

theorem valid8399 : plan8399.Valid := valid_step _ _ _ valid6269 (by decide +kernel)

theorem valid8400 : plan8400.Valid := valid_step _ _ _ valid6270 (by decide +kernel)

theorem valid8401 : plan8401.Valid := valid_step _ _ _ valid6271 (by decide +kernel)

theorem valid8402 : plan8402.Valid := valid_step _ _ _ valid6270 (by decide +kernel)

theorem valid8403 : plan8403.Valid := valid_step _ _ _ valid6270 (by decide +kernel)

theorem valid8404 : plan8404.Valid := valid_step _ _ _ valid6271 (by decide +kernel)

theorem valid8405 : plan8405.Valid := valid_step _ _ _ valid6272 (by decide +kernel)

theorem valid8406 : plan8406.Valid := valid_step _ _ _ valid6273 (by decide +kernel)

theorem valid8407 : plan8407.Valid := valid_step _ _ _ valid6274 (by decide +kernel)

theorem valid8408 : plan8408.Valid := valid_step _ _ _ valid6273 (by decide +kernel)

theorem valid8409 : plan8409.Valid := valid_step _ _ _ valid6273 (by decide +kernel)

theorem valid8410 : plan8410.Valid := valid_step _ _ _ valid6274 (by decide +kernel)

theorem valid8411 : plan8411.Valid := valid_step _ _ _ valid6275 (by decide +kernel)










































































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























theorem valid9132 : plan9132.Valid := valid_step _ _ _ valid8388 (by decide +kernel)

theorem valid9133 : plan9133.Valid := valid_step _ _ _ valid8389 (by decide +kernel)

theorem valid9134 : plan9134.Valid := valid_step _ _ _ valid8390 (by decide +kernel)

theorem valid9135 : plan9135.Valid := valid_step _ _ _ valid8391 (by decide +kernel)



theorem valid9137 : plan9137.Valid := valid_step _ _ _ valid8392 (by decide +kernel)

theorem valid9138 : plan9138.Valid := valid_step _ _ _ valid8393 (by decide +kernel)

theorem valid9139 : plan9139.Valid := valid_step _ _ _ valid8394 (by decide +kernel)

theorem valid9140 : plan9140.Valid := valid_step _ _ _ valid8395 (by decide +kernel)

theorem valid9141 : plan9141.Valid := valid_step _ _ _ valid8396 (by decide +kernel)

theorem valid9142 : plan9142.Valid := valid_step _ _ _ valid8397 (by decide +kernel)

theorem valid9143 : plan9143.Valid := valid_step _ _ _ valid8398 (by decide +kernel)

theorem valid9144 : plan9144.Valid := valid_step _ _ _ valid8400 (by decide +kernel)

theorem valid9145 : plan9145.Valid := valid_step _ _ _ valid8402 (by decide +kernel)

theorem valid9146 : plan9146.Valid := valid_step _ _ _ valid8403 (by decide +kernel)

theorem valid9147 : plan9147.Valid := valid_step _ _ _ valid8402 (by decide +kernel)

theorem valid9148 : plan9148.Valid := valid_step _ _ _ valid8399 (by decide +kernel)

theorem valid9149 : plan9149.Valid := valid_step _ _ _ valid8400 (by decide +kernel)

theorem valid9150 : plan9150.Valid := valid_step _ _ _ valid8401 (by decide +kernel)

theorem valid9151 : plan9151.Valid := valid_step _ _ _ valid8402 (by decide +kernel)

theorem valid9152 : plan9152.Valid := valid_step _ _ _ valid8403 (by decide +kernel)

theorem valid9153 : plan9153.Valid := valid_step _ _ _ valid8404 (by decide +kernel)

theorem valid9154 : plan9154.Valid := valid_step _ _ _ valid8402 (by decide +kernel)

theorem valid9155 : plan9155.Valid := valid_step _ _ _ valid8402 (by decide +kernel)

theorem valid9156 : plan9156.Valid := valid_step _ _ _ valid8402 (by decide +kernel)

theorem valid9157 : plan9157.Valid := valid_step _ _ _ valid8403 (by decide +kernel)

theorem valid9158 : plan9158.Valid := valid_step _ _ _ valid8404 (by decide +kernel)

theorem valid9159 : plan9159.Valid := valid_step _ _ _ valid8408 (by decide +kernel)

theorem valid9160 : plan9160.Valid := valid_step _ _ _ valid8405 (by decide +kernel)

theorem valid9161 : plan9161.Valid := valid_step _ _ _ valid8406 (by decide +kernel)

theorem valid9162 : plan9162.Valid := valid_step _ _ _ valid8407 (by decide +kernel)

theorem valid9163 : plan9163.Valid := valid_step _ _ _ valid8408 (by decide +kernel)

theorem valid9164 : plan9164.Valid := valid_step _ _ _ valid8409 (by decide +kernel)

theorem valid9165 : plan9165.Valid := valid_step _ _ _ valid8410 (by decide +kernel)

theorem valid9166 : plan9166.Valid := valid_step _ _ _ valid8408 (by decide +kernel)

theorem valid9167 : plan9167.Valid := valid_step _ _ _ valid8408 (by decide +kernel)

theorem valid9168 : plan9168.Valid := valid_step _ _ _ valid8408 (by decide +kernel)

theorem valid9169 : plan9169.Valid := valid_step _ _ _ valid8409 (by decide +kernel)

theorem valid9170 : plan9170.Valid := valid_step _ _ _ valid8410 (by decide +kernel)

theorem valid9171 : plan9171.Valid := valid_step _ _ _ valid8411 (by decide +kernel)

theorem valid9172 : plan9172.Valid := valid_step _ _ _ valid9132 (by decide +kernel)



theorem valid9174 : plan9174.Valid := valid_step _ _ _ valid9133 (by decide +kernel)

theorem valid9175 : plan9175.Valid := valid_step _ _ _ valid9134 (by decide +kernel)

theorem valid9176 : plan9176.Valid := valid_step _ _ _ valid9135 (by decide +kernel)











theorem valid9182 : plan9182.Valid := valid_step _ _ _ valid9138 (by decide +kernel)

theorem valid9183 : plan9183.Valid := valid_step _ _ _ valid9139 (by decide +kernel)

theorem valid9184 : plan9184.Valid := valid_step _ _ _ valid9140 (by decide +kernel)

theorem valid9185 : plan9185.Valid := valid_step _ _ _ valid9141 (by decide +kernel)

theorem valid9186 : plan9186.Valid := valid_step _ _ _ valid9142 (by decide +kernel)

theorem valid9187 : plan9187.Valid := valid_step _ _ _ valid9143 (by decide +kernel)

theorem valid9188 : plan9188.Valid := valid_step _ _ _ valid9137 (by decide +kernel)

theorem valid9189 : plan9189.Valid := valid_step _ _ _ valid9137 (by decide +kernel)









theorem valid9194 : plan9194.Valid := valid_step _ _ _ valid9147 (by decide +kernel)

theorem valid9195 : plan9195.Valid := valid_step _ _ _ valid9149 (by decide +kernel)

theorem valid9196 : plan9196.Valid := valid_step _ _ _ valid9151 (by decide +kernel)

theorem valid9197 : plan9197.Valid := valid_step _ _ _ valid9152 (by decide +kernel)

theorem valid9198 : plan9198.Valid := valid_step _ _ _ valid9154 (by decide +kernel)

theorem valid9199 : plan9199.Valid := valid_step _ _ _ valid9155 (by decide +kernel)

theorem valid9200 : plan9200.Valid := valid_step _ _ _ valid9156 (by decide +kernel)

theorem valid9201 : plan9201.Valid := valid_step _ _ _ valid9157 (by decide +kernel)

theorem valid9202 : plan9202.Valid := valid_step _ _ _ valid9148 (by decide +kernel)

theorem valid9203 : plan9203.Valid := valid_step _ _ _ valid9149 (by decide +kernel)

theorem valid9204 : plan9204.Valid := valid_step _ _ _ valid9150 (by decide +kernel)

theorem valid9205 : plan9205.Valid := valid_step _ _ _ valid9151 (by decide +kernel)

theorem valid9206 : plan9206.Valid := valid_step _ _ _ valid9152 (by decide +kernel)

theorem valid9207 : plan9207.Valid := valid_step _ _ _ valid9153 (by decide +kernel)

theorem valid9208 : plan9208.Valid := valid_step _ _ _ valid9154 (by decide +kernel)

theorem valid9209 : plan9209.Valid := valid_step _ _ _ valid9156 (by decide +kernel)

theorem valid9210 : plan9210.Valid := valid_step _ _ _ valid9157 (by decide +kernel)

theorem valid9211 : plan9211.Valid := valid_step _ _ _ valid9158 (by decide +kernel)

theorem valid9212 : plan9212.Valid := valid_step _ _ _ valid9145 (by decide +kernel)

theorem valid9213 : plan9213.Valid := valid_step _ _ _ valid9144 (by decide +kernel)

theorem valid9214 : plan9214.Valid := valid_step _ _ _ valid9145 (by decide +kernel)

theorem valid9215 : plan9215.Valid := valid_step _ _ _ valid9146 (by decide +kernel)

theorem valid9216 : plan9216.Valid := valid_step _ _ _ valid9145 (by decide +kernel)
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

theorem valid9217 : plan9217.Valid := valid_step _ _ _ valid9144 (by decide +kernel)

theorem valid9218 : plan9218.Valid := valid_step _ _ _ valid9145 (by decide +kernel)

theorem valid9219 : plan9219.Valid := valid_step _ _ _ valid9146 (by decide +kernel)

theorem valid9220 : plan9220.Valid := valid_step _ _ _ valid9163 (by decide +kernel)

theorem valid9221 : plan9221.Valid := valid_step _ _ _ valid9166 (by decide +kernel)

theorem valid9222 : plan9222.Valid := valid_step _ _ _ valid9168 (by decide +kernel)

theorem valid9223 : plan9223.Valid := valid_step _ _ _ valid9159 (by decide +kernel)

theorem valid9224 : plan9224.Valid := valid_step _ _ _ valid9161 (by decide +kernel)

theorem valid9225 : plan9225.Valid := valid_step _ _ _ valid9163 (by decide +kernel)

theorem valid9226 : plan9226.Valid := valid_step _ _ _ valid9164 (by decide +kernel)

theorem valid9227 : plan9227.Valid := valid_step _ _ _ valid9166 (by decide +kernel)

theorem valid9228 : plan9228.Valid := valid_step _ _ _ valid9167 (by decide +kernel)

theorem valid9229 : plan9229.Valid := valid_step _ _ _ valid9168 (by decide +kernel)

theorem valid9230 : plan9230.Valid := valid_step _ _ _ valid9169 (by decide +kernel)

theorem valid9231 : plan9231.Valid := valid_step _ _ _ valid9160 (by decide +kernel)

theorem valid9232 : plan9232.Valid := valid_step _ _ _ valid9161 (by decide +kernel)

theorem valid9233 : plan9233.Valid := valid_step _ _ _ valid9162 (by decide +kernel)

theorem valid9234 : plan9234.Valid := valid_step _ _ _ valid9163 (by decide +kernel)

theorem valid9235 : plan9235.Valid := valid_step _ _ _ valid9164 (by decide +kernel)

theorem valid9236 : plan9236.Valid := valid_step _ _ _ valid9165 (by decide +kernel)

theorem valid9237 : plan9237.Valid := valid_step _ _ _ valid9166 (by decide +kernel)

theorem valid9238 : plan9238.Valid := valid_step _ _ _ valid9168 (by decide +kernel)

theorem valid9239 : plan9239.Valid := valid_step _ _ _ valid9169 (by decide +kernel)

theorem valid9240 : plan9240.Valid := valid_step _ _ _ valid9170 (by decide +kernel)

theorem valid9241 : plan9241.Valid := valid_step _ _ _ valid9166 (by decide +kernel)

theorem valid9242 : plan9242.Valid := valid_step _ _ _ valid9163 (by decide +kernel)

theorem valid9243 : plan9243.Valid := valid_step _ _ _ valid9166 (by decide +kernel)

theorem valid9244 : plan9244.Valid := valid_step _ _ _ valid9168 (by decide +kernel)

theorem valid9245 : plan9245.Valid := valid_step _ _ _ valid9161 (by decide +kernel)

theorem valid9246 : plan9246.Valid := valid_step _ _ _ valid9163 (by decide +kernel)

theorem valid9247 : plan9247.Valid := valid_step _ _ _ valid9164 (by decide +kernel)

theorem valid9248 : plan9248.Valid := valid_step _ _ _ valid9166 (by decide +kernel)

theorem valid9249 : plan9249.Valid := valid_step _ _ _ valid9167 (by decide +kernel)

theorem valid9250 : plan9250.Valid := valid_step _ _ _ valid9168 (by decide +kernel)

theorem valid9251 : plan9251.Valid := valid_step _ _ _ valid9169 (by decide +kernel)

theorem valid9252 : plan9252.Valid := valid_step _ _ _ valid9166 (by decide +kernel)

theorem valid9253 : plan9253.Valid := valid_step _ _ _ valid9168 (by decide +kernel)

theorem valid9254 : plan9254.Valid := valid_step _ _ _ valid9169 (by decide +kernel)

theorem valid9255 : plan9255.Valid := valid_step _ _ _ valid9170 (by decide +kernel)

theorem valid9256 : plan9256.Valid := valid_step _ _ _ valid9171 (by decide +kernel)

theorem valid9257 : plan9257.Valid := valid_step _ _ _ valid9256 (by decide +kernel)
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
theorem t8_10choices : plan9194.choices=[2,5,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_10part0 : t8_10jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_10frontier : t8_10root.frontier 0=t8_10jobs := by rfl
theorem t8_10all : t8_10jobs.all (Job.check tree)=true := by
  simp only [t8_10jobs,List.all_append,List.all_nil,t8_10part0,Bool.and_self]
theorem t8_10checked : Checked tree [2,5,7,7,7,7,7,7] := by
  refine ⟨plan9194,valid9194,t8_10choices,?_⟩
  exact check_of_frontier tree 0 t8_10root t8_10jobs t8_10frontier t8_10all
theorem t8_11choices : plan9195.choices=[2,6,6,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_11part0 : t8_11jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_11frontier : t8_11root.frontier 0=t8_11jobs := by rfl
theorem t8_11all : t8_11jobs.all (Job.check tree)=true := by
  simp only [t8_11jobs,List.all_append,List.all_nil,t8_11part0,Bool.and_self]
theorem t8_11checked : Checked tree [2,6,6,7,7,7,7,7] := by
  refine ⟨plan9195,valid9195,t8_11choices,?_⟩
  exact check_of_frontier tree 0 t8_11root t8_11jobs t8_11frontier t8_11all
theorem t8_12choices : plan9196.choices=[2,6,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_12part0 : t8_12jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_12frontier : t8_12root.frontier 0=t8_12jobs := by rfl
theorem t8_12all : t8_12jobs.all (Job.check tree)=true := by
  simp only [t8_12jobs,List.all_append,List.all_nil,t8_12part0,Bool.and_self]
theorem t8_12checked : Checked tree [2,6,7,7,7,7,7,7] := by
  refine ⟨plan9196,valid9196,t8_12choices,?_⟩
  exact check_of_frontier tree 0 t8_12root t8_12jobs t8_12frontier t8_12all
theorem t8_13choices : plan9197.choices=[2,6,10,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_13part0 : t8_13jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_13frontier : t8_13root.frontier 0=t8_13jobs := by rfl
theorem t8_13all : t8_13jobs.all (Job.check tree)=true := by
  simp only [t8_13jobs,List.all_append,List.all_nil,t8_13part0,Bool.and_self]
theorem t8_13checked : Checked tree [2,6,10,7,7,7,7,7] := by
  refine ⟨plan9197,valid9197,t8_13choices,?_⟩
  exact check_of_frontier tree 0 t8_13root t8_13jobs t8_13frontier t8_13all
theorem t8_14choices : plan9198.choices=[2,7,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_14part0 : t8_14jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_14frontier : t8_14root.frontier 0=t8_14jobs := by rfl
theorem t8_14all : t8_14jobs.all (Job.check tree)=true := by
  simp only [t8_14jobs,List.all_append,List.all_nil,t8_14part0,Bool.and_self]
theorem t8_14checked : Checked tree [2,7,7,7,7,7,7,7] := by
  refine ⟨plan9198,valid9198,t8_14choices,?_⟩
  exact check_of_frontier tree 0 t8_14root t8_14jobs t8_14frontier t8_14all
theorem t8_15choices : plan9199.choices=[2,9,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_15part0 : t8_15jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_15frontier : t8_15root.frontier 0=t8_15jobs := by rfl
theorem t8_15all : t8_15jobs.all (Job.check tree)=true := by
  simp only [t8_15jobs,List.all_append,List.all_nil,t8_15part0,Bool.and_self]
theorem t8_15checked : Checked tree [2,9,7,7,7,7,7,7] := by
  refine ⟨plan9199,valid9199,t8_15choices,?_⟩
  exact check_of_frontier tree 0 t8_15root t8_15jobs t8_15frontier t8_15all
theorem t8_16choices : plan9200.choices=[2,10,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_16part0 : t8_16jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_16frontier : t8_16root.frontier 0=t8_16jobs := by rfl
theorem t8_16all : t8_16jobs.all (Job.check tree)=true := by
  simp only [t8_16jobs,List.all_append,List.all_nil,t8_16part0,Bool.and_self]
theorem t8_16checked : Checked tree [2,10,7,7,7,7,7,7] := by
  refine ⟨plan9200,valid9200,t8_16choices,?_⟩
  exact check_of_frontier tree 0 t8_16root t8_16jobs t8_16frontier t8_16all
theorem t8_17choices : plan9201.choices=[2,10,10,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_17part0 : t8_17jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_17frontier : t8_17root.frontier 0=t8_17jobs := by rfl
theorem t8_17all : t8_17jobs.all (Job.check tree)=true := by
  simp only [t8_17jobs,List.all_append,List.all_nil,t8_17part0,Bool.and_self]
theorem t8_17checked : Checked tree [2,10,10,7,7,7,7,7] := by
  refine ⟨plan9201,valid9201,t8_17choices,?_⟩
  exact check_of_frontier tree 0 t8_17root t8_17jobs t8_17frontier t8_17all
theorem t8_18choices : plan9172.choices=[3,3,3,3,7,7,7,7].map (options 8 4) := by rfl


theorem t8_18part0 : t8_18jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_18frontier : t8_18root.frontier 0=t8_18jobs := by rfl
theorem t8_18all : t8_18jobs.all (Job.check tree)=true := by
  simp only [t8_18jobs,List.all_append,List.all_nil,t8_18part0,Bool.and_self]
theorem t8_18checked : Checked tree [3,3,3,3,7,7,7,7] := by
  refine ⟨plan9172,valid9172,t8_18choices,?_⟩
  exact check_of_frontier tree 0 t8_18root t8_18jobs t8_18frontier t8_18all
theorem t8_19choices : plan9174.choices=[3,3,3,6,7,7,7,7].map (options 8 5) := by rfl


theorem t8_19part0 : t8_19jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_19frontier : t8_19root.frontier 0=t8_19jobs := by rfl
theorem t8_19all : t8_19jobs.all (Job.check tree)=true := by
  simp only [t8_19jobs,List.all_append,List.all_nil,t8_19part0,Bool.and_self]
theorem t8_19checked : Checked tree [3,3,3,6,7,7,7,7] := by
  refine ⟨plan9174,valid9174,t8_19choices,?_⟩
  exact check_of_frontier tree 0 t8_19root t8_19jobs t8_19frontier t8_19all
theorem t8_20choices : plan9175.choices=[3,3,3,7,7,7,7,7].map (options 8 5) := by rfl


theorem t8_20part0 : t8_20jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_20frontier : t8_20root.frontier 0=t8_20jobs := by rfl
theorem t8_20all : t8_20jobs.all (Job.check tree)=true := by
  simp only [t8_20jobs,List.all_append,List.all_nil,t8_20part0,Bool.and_self]
theorem t8_20checked : Checked tree [3,3,3,7,7,7,7,7] := by
  refine ⟨plan9175,valid9175,t8_20choices,?_⟩
  exact check_of_frontier tree 0 t8_20root t8_20jobs t8_20frontier t8_20all
theorem t8_21choices : plan9176.choices=[3,3,3,10,7,7,7,7].map (options 8 5) := by rfl


theorem t8_21part0 : t8_21jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_21frontier : t8_21root.frontier 0=t8_21jobs := by rfl
theorem t8_21all : t8_21jobs.all (Job.check tree)=true := by
  simp only [t8_21jobs,List.all_append,List.all_nil,t8_21part0,Bool.and_self]
theorem t8_21checked : Checked tree [3,3,3,10,7,7,7,7] := by
  refine ⟨plan9176,valid9176,t8_21choices,?_⟩
  exact check_of_frontier tree 0 t8_21root t8_21jobs t8_21frontier t8_21all
theorem t8_22choices : plan9182.choices=[3,3,6,6,7,7,7,7].map (options 8 6) := by rfl


theorem t8_22part0 : t8_22jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_22frontier : t8_22root.frontier 0=t8_22jobs := by rfl
theorem t8_22all : t8_22jobs.all (Job.check tree)=true := by
  simp only [t8_22jobs,List.all_append,List.all_nil,t8_22part0,Bool.and_self]
theorem t8_22checked : Checked tree [3,3,6,6,7,7,7,7] := by
  refine ⟨plan9182,valid9182,t8_22choices,?_⟩
  exact check_of_frontier tree 0 t8_22root t8_22jobs t8_22frontier t8_22all
theorem t8_23choices : plan9183.choices=[3,3,6,7,7,7,7,7].map (options 8 6) := by rfl


theorem t8_23part0 : t8_23jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_23frontier : t8_23root.frontier 0=t8_23jobs := by rfl
theorem t8_23all : t8_23jobs.all (Job.check tree)=true := by
  simp only [t8_23jobs,List.all_append,List.all_nil,t8_23part0,Bool.and_self]
theorem t8_23checked : Checked tree [3,3,6,7,7,7,7,7] := by
  refine ⟨plan9183,valid9183,t8_23choices,?_⟩
  exact check_of_frontier tree 0 t8_23root t8_23jobs t8_23frontier t8_23all
theorem t8_24choices : plan9184.choices=[3,3,6,10,7,7,7,7].map (options 8 6) := by rfl


theorem t8_24part0 : t8_24jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_24frontier : t8_24root.frontier 0=t8_24jobs := by rfl
theorem t8_24all : t8_24jobs.all (Job.check tree)=true := by
  simp only [t8_24jobs,List.all_append,List.all_nil,t8_24part0,Bool.and_self]
theorem t8_24checked : Checked tree [3,3,6,10,7,7,7,7] := by
  refine ⟨plan9184,valid9184,t8_24choices,?_⟩
  exact check_of_frontier tree 0 t8_24root t8_24jobs t8_24frontier t8_24all
theorem t8_25choices : plan9185.choices=[3,3,7,7,7,7,7,7].map (options 8 6) := by rfl


theorem t8_25part0 : t8_25jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_25frontier : t8_25root.frontier 0=t8_25jobs := by rfl
theorem t8_25all : t8_25jobs.all (Job.check tree)=true := by
  simp only [t8_25jobs,List.all_append,List.all_nil,t8_25part0,Bool.and_self]
theorem t8_25checked : Checked tree [3,3,7,7,7,7,7,7] := by
  refine ⟨plan9185,valid9185,t8_25choices,?_⟩
  exact check_of_frontier tree 0 t8_25root t8_25jobs t8_25frontier t8_25all
theorem t8_26choices : plan9186.choices=[3,3,10,7,7,7,7,7].map (options 8 6) := by rfl


theorem t8_26part0 : t8_26jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_26frontier : t8_26root.frontier 0=t8_26jobs := by rfl
theorem t8_26all : t8_26jobs.all (Job.check tree)=true := by
  simp only [t8_26jobs,List.all_append,List.all_nil,t8_26part0,Bool.and_self]
theorem t8_26checked : Checked tree [3,3,10,7,7,7,7,7] := by
  refine ⟨plan9186,valid9186,t8_26choices,?_⟩
  exact check_of_frontier tree 0 t8_26root t8_26jobs t8_26frontier t8_26all
theorem t8_27choices : plan9187.choices=[3,3,10,10,7,7,7,7].map (options 8 6) := by rfl


theorem t8_27part0 : t8_27jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_27frontier : t8_27root.frontier 0=t8_27jobs := by rfl
theorem t8_27all : t8_27jobs.all (Job.check tree)=true := by
  simp only [t8_27jobs,List.all_append,List.all_nil,t8_27part0,Bool.and_self]
theorem t8_27checked : Checked tree [3,3,10,10,7,7,7,7] := by
  refine ⟨plan9187,valid9187,t8_27choices,?_⟩
  exact check_of_frontier tree 0 t8_27root t8_27jobs t8_27frontier t8_27all
theorem t8_28choices : plan9202.choices=[3,6,6,6,7,7,7,7].map (options 8 7) := by rfl


theorem t8_28part0 : t8_28jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_28frontier : t8_28root.frontier 0=t8_28jobs := by rfl
theorem t8_28all : t8_28jobs.all (Job.check tree)=true := by
  simp only [t8_28jobs,List.all_append,List.all_nil,t8_28part0,Bool.and_self]
theorem t8_28checked : Checked tree [3,6,6,6,7,7,7,7] := by
  refine ⟨plan9202,valid9202,t8_28choices,?_⟩
  exact check_of_frontier tree 0 t8_28root t8_28jobs t8_28frontier t8_28all
theorem t8_29choices : plan9203.choices=[3,6,6,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_29part0 : t8_29jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_29frontier : t8_29root.frontier 0=t8_29jobs := by rfl
theorem t8_29all : t8_29jobs.all (Job.check tree)=true := by
  simp only [t8_29jobs,List.all_append,List.all_nil,t8_29part0,Bool.and_self]
theorem t8_29checked : Checked tree [3,6,6,7,7,7,7,7] := by
  refine ⟨plan9203,valid9203,t8_29choices,?_⟩
  exact check_of_frontier tree 0 t8_29root t8_29jobs t8_29frontier t8_29all
theorem t8_30choices : plan9204.choices=[3,6,6,10,7,7,7,7].map (options 8 7) := by rfl


theorem t8_30part0 : t8_30jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_30frontier : t8_30root.frontier 0=t8_30jobs := by rfl
theorem t8_30all : t8_30jobs.all (Job.check tree)=true := by
  simp only [t8_30jobs,List.all_append,List.all_nil,t8_30part0,Bool.and_self]
theorem t8_30checked : Checked tree [3,6,6,10,7,7,7,7] := by
  refine ⟨plan9204,valid9204,t8_30choices,?_⟩
  exact check_of_frontier tree 0 t8_30root t8_30jobs t8_30frontier t8_30all
theorem t8_31choices : plan9205.choices=[3,6,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_31part0 : t8_31jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_31frontier : t8_31root.frontier 0=t8_31jobs := by rfl
theorem t8_31all : t8_31jobs.all (Job.check tree)=true := by
  simp only [t8_31jobs,List.all_append,List.all_nil,t8_31part0,Bool.and_self]
theorem t8_31checked : Checked tree [3,6,7,7,7,7,7,7] := by
  refine ⟨plan9205,valid9205,t8_31choices,?_⟩
  exact check_of_frontier tree 0 t8_31root t8_31jobs t8_31frontier t8_31all
theorem t8_32choices : plan9206.choices=[3,6,10,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_32part0 : t8_32jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_32frontier : t8_32root.frontier 0=t8_32jobs := by rfl
theorem t8_32all : t8_32jobs.all (Job.check tree)=true := by
  simp only [t8_32jobs,List.all_append,List.all_nil,t8_32part0,Bool.and_self]
theorem t8_32checked : Checked tree [3,6,10,7,7,7,7,7] := by
  refine ⟨plan9206,valid9206,t8_32choices,?_⟩
  exact check_of_frontier tree 0 t8_32root t8_32jobs t8_32frontier t8_32all
theorem t8_33choices : plan9207.choices=[3,6,10,10,7,7,7,7].map (options 8 7) := by rfl


theorem t8_33part0 : t8_33jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_33frontier : t8_33root.frontier 0=t8_33jobs := by rfl
theorem t8_33all : t8_33jobs.all (Job.check tree)=true := by
  simp only [t8_33jobs,List.all_append,List.all_nil,t8_33part0,Bool.and_self]
theorem t8_33checked : Checked tree [3,6,10,10,7,7,7,7] := by
  refine ⟨plan9207,valid9207,t8_33choices,?_⟩
  exact check_of_frontier tree 0 t8_33root t8_33jobs t8_33frontier t8_33all
theorem t8_34choices : plan9208.choices=[3,7,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_34part0 : t8_34jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_34frontier : t8_34root.frontier 0=t8_34jobs := by rfl
theorem t8_34all : t8_34jobs.all (Job.check tree)=true := by
  simp only [t8_34jobs,List.all_append,List.all_nil,t8_34part0,Bool.and_self]
theorem t8_34checked : Checked tree [3,7,7,7,7,7,7,7] := by
  refine ⟨plan9208,valid9208,t8_34choices,?_⟩
  exact check_of_frontier tree 0 t8_34root t8_34jobs t8_34frontier t8_34all
theorem t8_35choices : plan9209.choices=[3,10,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_35part0 : t8_35jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_35frontier : t8_35root.frontier 0=t8_35jobs := by rfl
theorem t8_35all : t8_35jobs.all (Job.check tree)=true := by
  simp only [t8_35jobs,List.all_append,List.all_nil,t8_35part0,Bool.and_self]
theorem t8_35checked : Checked tree [3,10,7,7,7,7,7,7] := by
  refine ⟨plan9209,valid9209,t8_35choices,?_⟩
  exact check_of_frontier tree 0 t8_35root t8_35jobs t8_35frontier t8_35all
theorem t8_36choices : plan9210.choices=[3,10,10,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_36part0 : t8_36jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_36frontier : t8_36root.frontier 0=t8_36jobs := by rfl
theorem t8_36all : t8_36jobs.all (Job.check tree)=true := by
  simp only [t8_36jobs,List.all_append,List.all_nil,t8_36part0,Bool.and_self]
theorem t8_36checked : Checked tree [3,10,10,7,7,7,7,7] := by
  refine ⟨plan9210,valid9210,t8_36choices,?_⟩
  exact check_of_frontier tree 0 t8_36root t8_36jobs t8_36frontier t8_36all
theorem t8_37choices : plan9211.choices=[3,10,10,10,7,7,7,7].map (options 8 7) := by rfl


theorem t8_37part0 : t8_37jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_37frontier : t8_37root.frontier 0=t8_37jobs := by rfl
theorem t8_37all : t8_37jobs.all (Job.check tree)=true := by
  simp only [t8_37jobs,List.all_append,List.all_nil,t8_37part0,Bool.and_self]
theorem t8_37checked : Checked tree [3,10,10,10,7,7,7,7] := by
  refine ⟨plan9211,valid9211,t8_37choices,?_⟩
  exact check_of_frontier tree 0 t8_37root t8_37jobs t8_37frontier t8_37all
theorem t8_38choices : plan9212.choices=[4,3,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_38part0 : t8_38jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_38frontier : t8_38root.frontier 0=t8_38jobs := by rfl
theorem t8_38all : t8_38jobs.all (Job.check tree)=true := by
  simp only [t8_38jobs,List.all_append,List.all_nil,t8_38part0,Bool.and_self]
theorem t8_38checked : Checked tree [4,3,7,7,7,7,7,7] := by
  refine ⟨plan9212,valid9212,t8_38choices,?_⟩
  exact check_of_frontier tree 0 t8_38root t8_38jobs t8_38frontier t8_38all
theorem t8_39choices : plan9220.choices=[4,6,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_39part0 : t8_39jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_39frontier : t8_39root.frontier 0=t8_39jobs := by rfl
theorem t8_39all : t8_39jobs.all (Job.check tree)=true := by
  simp only [t8_39jobs,List.all_append,List.all_nil,t8_39part0,Bool.and_self]
theorem t8_39checked : Checked tree [4,6,7,7,7,7,7,7] := by
  refine ⟨plan9220,valid9220,t8_39choices,?_⟩
  exact check_of_frontier tree 0 t8_39root t8_39jobs t8_39frontier t8_39all
theorem t8_40choices : plan9221.choices=[4,7,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_40part0 : t8_40jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_40frontier : t8_40root.frontier 0=t8_40jobs := by rfl
theorem t8_40all : t8_40jobs.all (Job.check tree)=true := by
  simp only [t8_40jobs,List.all_append,List.all_nil,t8_40part0,Bool.and_self]
theorem t8_40checked : Checked tree [4,7,7,7,7,7,7,7] := by
  refine ⟨plan9221,valid9221,t8_40choices,?_⟩
  exact check_of_frontier tree 0 t8_40root t8_40jobs t8_40frontier t8_40all
theorem t8_41choices : plan9222.choices=[4,10,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_41part0 : t8_41jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_41frontier : t8_41root.frontier 0=t8_41jobs := by rfl
theorem t8_41all : t8_41jobs.all (Job.check tree)=true := by
  simp only [t8_41jobs,List.all_append,List.all_nil,t8_41part0,Bool.and_self]
theorem t8_41checked : Checked tree [4,10,7,7,7,7,7,7] := by
  refine ⟨plan9222,valid9222,t8_41choices,?_⟩
  exact check_of_frontier tree 0 t8_41root t8_41jobs t8_41frontier t8_41all
theorem t8_42choices : plan9188.choices=[5,3,3,7,7,7,7,7].map (options 8 6) := by rfl


theorem t8_42part0 : t8_42jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_42frontier : t8_42root.frontier 0=t8_42jobs := by rfl
theorem t8_42all : t8_42jobs.all (Job.check tree)=true := by
  simp only [t8_42jobs,List.all_append,List.all_nil,t8_42part0,Bool.and_self]
theorem t8_42checked : Checked tree [5,3,3,7,7,7,7,7] := by
  refine ⟨plan9188,valid9188,t8_42choices,?_⟩
  exact check_of_frontier tree 0 t8_42root t8_42jobs t8_42frontier t8_42all
theorem t8_43choices : plan9213.choices=[5,3,6,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_43part0 : t8_43jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_43frontier : t8_43root.frontier 0=t8_43jobs := by rfl
theorem t8_43all : t8_43jobs.all (Job.check tree)=true := by
  simp only [t8_43jobs,List.all_append,List.all_nil,t8_43part0,Bool.and_self]
theorem t8_43checked : Checked tree [5,3,6,7,7,7,7,7] := by
  refine ⟨plan9213,valid9213,t8_43choices,?_⟩
  exact check_of_frontier tree 0 t8_43root t8_43jobs t8_43frontier t8_43all
theorem t8_44choices : plan9214.choices=[5,3,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_44part0 : t8_44jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_44frontier : t8_44root.frontier 0=t8_44jobs := by rfl
theorem t8_44all : t8_44jobs.all (Job.check tree)=true := by
  simp only [t8_44jobs,List.all_append,List.all_nil,t8_44part0,Bool.and_self]
theorem t8_44checked : Checked tree [5,3,7,7,7,7,7,7] := by
  refine ⟨plan9214,valid9214,t8_44choices,?_⟩
  exact check_of_frontier tree 0 t8_44root t8_44jobs t8_44frontier t8_44all
theorem t8_45choices : plan9215.choices=[5,3,10,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_45part0 : t8_45jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_45frontier : t8_45root.frontier 0=t8_45jobs := by rfl
theorem t8_45all : t8_45jobs.all (Job.check tree)=true := by
  simp only [t8_45jobs,List.all_append,List.all_nil,t8_45part0,Bool.and_self]
theorem t8_45checked : Checked tree [5,3,10,7,7,7,7,7] := by
  refine ⟨plan9215,valid9215,t8_45choices,?_⟩
  exact check_of_frontier tree 0 t8_45root t8_45jobs t8_45frontier t8_45all
theorem t8_46choices : plan9223.choices=[5,5,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_46part0 : t8_46jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_46frontier : t8_46root.frontier 0=t8_46jobs := by rfl
theorem t8_46all : t8_46jobs.all (Job.check tree)=true := by
  simp only [t8_46jobs,List.all_append,List.all_nil,t8_46part0,Bool.and_self]
theorem t8_46checked : Checked tree [5,5,7,7,7,7,7,7] := by
  refine ⟨plan9223,valid9223,t8_46choices,?_⟩
  exact check_of_frontier tree 0 t8_46root t8_46jobs t8_46frontier t8_46all
theorem t8_47choices : plan9224.choices=[5,6,6,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_47part0 : t8_47jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_47frontier : t8_47root.frontier 0=t8_47jobs := by rfl
theorem t8_47all : t8_47jobs.all (Job.check tree)=true := by
  simp only [t8_47jobs,List.all_append,List.all_nil,t8_47part0,Bool.and_self]
theorem t8_47checked : Checked tree [5,6,6,7,7,7,7,7] := by
  refine ⟨plan9224,valid9224,t8_47choices,?_⟩
  exact check_of_frontier tree 0 t8_47root t8_47jobs t8_47frontier t8_47all
theorem t8_48choices : plan9225.choices=[5,6,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_48part0 : t8_48jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_48frontier : t8_48root.frontier 0=t8_48jobs := by rfl
theorem t8_48all : t8_48jobs.all (Job.check tree)=true := by
  simp only [t8_48jobs,List.all_append,List.all_nil,t8_48part0,Bool.and_self]
theorem t8_48checked : Checked tree [5,6,7,7,7,7,7,7] := by
  refine ⟨plan9225,valid9225,t8_48choices,?_⟩
  exact check_of_frontier tree 0 t8_48root t8_48jobs t8_48frontier t8_48all
theorem t8_49choices : plan9226.choices=[5,6,10,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_49part0 : t8_49jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_49frontier : t8_49root.frontier 0=t8_49jobs := by rfl
theorem t8_49all : t8_49jobs.all (Job.check tree)=true := by
  simp only [t8_49jobs,List.all_append,List.all_nil,t8_49part0,Bool.and_self]
theorem t8_49checked : Checked tree [5,6,10,7,7,7,7,7] := by
  refine ⟨plan9226,valid9226,t8_49choices,?_⟩
  exact check_of_frontier tree 0 t8_49root t8_49jobs t8_49frontier t8_49all
theorem t8_50choices : plan9227.choices=[5,7,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_50part0 : t8_50jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_50frontier : t8_50root.frontier 0=t8_50jobs := by rfl
theorem t8_50all : t8_50jobs.all (Job.check tree)=true := by
  simp only [t8_50jobs,List.all_append,List.all_nil,t8_50part0,Bool.and_self]
theorem t8_50checked : Checked tree [5,7,7,7,7,7,7,7] := by
  refine ⟨plan9227,valid9227,t8_50choices,?_⟩
  exact check_of_frontier tree 0 t8_50root t8_50jobs t8_50frontier t8_50all
theorem t8_51choices : plan9228.choices=[5,9,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_51part0 : t8_51jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_51frontier : t8_51root.frontier 0=t8_51jobs := by rfl
theorem t8_51all : t8_51jobs.all (Job.check tree)=true := by
  simp only [t8_51jobs,List.all_append,List.all_nil,t8_51part0,Bool.and_self]
theorem t8_51checked : Checked tree [5,9,7,7,7,7,7,7] := by
  refine ⟨plan9228,valid9228,t8_51choices,?_⟩
  exact check_of_frontier tree 0 t8_51root t8_51jobs t8_51frontier t8_51all
theorem t8_52choices : plan9229.choices=[5,10,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_52part0 : t8_52jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_52frontier : t8_52root.frontier 0=t8_52jobs := by rfl
theorem t8_52all : t8_52jobs.all (Job.check tree)=true := by
  simp only [t8_52jobs,List.all_append,List.all_nil,t8_52part0,Bool.and_self]
theorem t8_52checked : Checked tree [5,10,7,7,7,7,7,7] := by
  refine ⟨plan9229,valid9229,t8_52choices,?_⟩
  exact check_of_frontier tree 0 t8_52root t8_52jobs t8_52frontier t8_52all
theorem t8_53choices : plan9230.choices=[5,10,10,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_53part0 : t8_53jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_53frontier : t8_53root.frontier 0=t8_53jobs := by rfl
theorem t8_53all : t8_53jobs.all (Job.check tree)=true := by
  simp only [t8_53jobs,List.all_append,List.all_nil,t8_53part0,Bool.and_self]
theorem t8_53checked : Checked tree [5,10,10,7,7,7,7,7] := by
  refine ⟨plan9230,valid9230,t8_53choices,?_⟩
  exact check_of_frontier tree 0 t8_53root t8_53jobs t8_53frontier t8_53all
theorem t8_54choices : plan9231.choices=[6,6,6,6,7,7,7,7].map (options 8 8) := by rfl


theorem t8_54part0 : t8_54jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_54frontier : t8_54root.frontier 0=t8_54jobs := by rfl
theorem t8_54all : t8_54jobs.all (Job.check tree)=true := by
  simp only [t8_54jobs,List.all_append,List.all_nil,t8_54part0,Bool.and_self]
theorem t8_54checked : Checked tree [6,6,6,6,7,7,7,7] := by
  refine ⟨plan9231,valid9231,t8_54choices,?_⟩
  exact check_of_frontier tree 0 t8_54root t8_54jobs t8_54frontier t8_54all
theorem t8_55choices : plan9232.choices=[6,6,6,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_55part0 : t8_55jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_55frontier : t8_55root.frontier 0=t8_55jobs := by rfl
theorem t8_55all : t8_55jobs.all (Job.check tree)=true := by
  simp only [t8_55jobs,List.all_append,List.all_nil,t8_55part0,Bool.and_self]
theorem t8_55checked : Checked tree [6,6,6,7,7,7,7,7] := by
  refine ⟨plan9232,valid9232,t8_55choices,?_⟩
  exact check_of_frontier tree 0 t8_55root t8_55jobs t8_55frontier t8_55all
theorem t8_56choices : plan9233.choices=[6,6,6,10,7,7,7,7].map (options 8 8) := by rfl


theorem t8_56part0 : t8_56jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_56frontier : t8_56root.frontier 0=t8_56jobs := by rfl
theorem t8_56all : t8_56jobs.all (Job.check tree)=true := by
  simp only [t8_56jobs,List.all_append,List.all_nil,t8_56part0,Bool.and_self]
theorem t8_56checked : Checked tree [6,6,6,10,7,7,7,7] := by
  refine ⟨plan9233,valid9233,t8_56choices,?_⟩
  exact check_of_frontier tree 0 t8_56root t8_56jobs t8_56frontier t8_56all
theorem t8_57choices : plan9234.choices=[6,6,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_57part0 : t8_57jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_57frontier : t8_57root.frontier 0=t8_57jobs := by rfl
theorem t8_57all : t8_57jobs.all (Job.check tree)=true := by
  simp only [t8_57jobs,List.all_append,List.all_nil,t8_57part0,Bool.and_self]
theorem t8_57checked : Checked tree [6,6,7,7,7,7,7,7] := by
  refine ⟨plan9234,valid9234,t8_57choices,?_⟩
  exact check_of_frontier tree 0 t8_57root t8_57jobs t8_57frontier t8_57all
theorem t8_58choices : plan9235.choices=[6,6,10,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_58part0 : t8_58jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_58frontier : t8_58root.frontier 0=t8_58jobs := by rfl
theorem t8_58all : t8_58jobs.all (Job.check tree)=true := by
  simp only [t8_58jobs,List.all_append,List.all_nil,t8_58part0,Bool.and_self]
theorem t8_58checked : Checked tree [6,6,10,7,7,7,7,7] := by
  refine ⟨plan9235,valid9235,t8_58choices,?_⟩
  exact check_of_frontier tree 0 t8_58root t8_58jobs t8_58frontier t8_58all
theorem t8_59choices : plan9236.choices=[6,6,10,10,7,7,7,7].map (options 8 8) := by rfl


theorem t8_59part0 : t8_59jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_59frontier : t8_59root.frontier 0=t8_59jobs := by rfl
theorem t8_59all : t8_59jobs.all (Job.check tree)=true := by
  simp only [t8_59jobs,List.all_append,List.all_nil,t8_59part0,Bool.and_self]
theorem t8_59checked : Checked tree [6,6,10,10,7,7,7,7] := by
  refine ⟨plan9236,valid9236,t8_59choices,?_⟩
  exact check_of_frontier tree 0 t8_59root t8_59jobs t8_59frontier t8_59all
theorem t8_60choices : plan9237.choices=[6,7,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_60part0 : t8_60jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_60frontier : t8_60root.frontier 0=t8_60jobs := by rfl
theorem t8_60all : t8_60jobs.all (Job.check tree)=true := by
  simp only [t8_60jobs,List.all_append,List.all_nil,t8_60part0,Bool.and_self]
theorem t8_60checked : Checked tree [6,7,7,7,7,7,7,7] := by
  refine ⟨plan9237,valid9237,t8_60choices,?_⟩
  exact check_of_frontier tree 0 t8_60root t8_60jobs t8_60frontier t8_60all
theorem t8_61choices : plan9238.choices=[6,10,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_61part0 : t8_61jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_61frontier : t8_61root.frontier 0=t8_61jobs := by rfl
theorem t8_61all : t8_61jobs.all (Job.check tree)=true := by
  simp only [t8_61jobs,List.all_append,List.all_nil,t8_61part0,Bool.and_self]
theorem t8_61checked : Checked tree [6,10,7,7,7,7,7,7] := by
  refine ⟨plan9238,valid9238,t8_61choices,?_⟩
  exact check_of_frontier tree 0 t8_61root t8_61jobs t8_61frontier t8_61all
theorem t8_62choices : plan9239.choices=[6,10,10,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_62part0 : t8_62jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_62frontier : t8_62root.frontier 0=t8_62jobs := by rfl
theorem t8_62all : t8_62jobs.all (Job.check tree)=true := by
  simp only [t8_62jobs,List.all_append,List.all_nil,t8_62part0,Bool.and_self]
theorem t8_62checked : Checked tree [6,10,10,7,7,7,7,7] := by
  refine ⟨plan9239,valid9239,t8_62choices,?_⟩
  exact check_of_frontier tree 0 t8_62root t8_62jobs t8_62frontier t8_62all
theorem t8_63choices : plan9240.choices=[6,10,10,10,7,7,7,7].map (options 8 8) := by rfl


theorem t8_63part0 : t8_63jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_63frontier : t8_63root.frontier 0=t8_63jobs := by rfl
theorem t8_63all : t8_63jobs.all (Job.check tree)=true := by
  simp only [t8_63jobs,List.all_append,List.all_nil,t8_63part0,Bool.and_self]
theorem t8_63checked : Checked tree [6,10,10,10,7,7,7,7] := by
  refine ⟨plan9240,valid9240,t8_63choices,?_⟩
  exact check_of_frontier tree 0 t8_63root t8_63jobs t8_63frontier t8_63all
theorem t8_64choices : plan9241.choices=[7,7,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_64part0 : t8_64jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_64frontier : t8_64root.frontier 0=t8_64jobs := by rfl
theorem t8_64all : t8_64jobs.all (Job.check tree)=true := by
  simp only [t8_64jobs,List.all_append,List.all_nil,t8_64part0,Bool.and_self]
theorem t8_64checked : Checked tree [7,7,7,7,7,7,7,7] := by
  refine ⟨plan9241,valid9241,t8_64choices,?_⟩
  exact check_of_frontier tree 0 t8_64root t8_64jobs t8_64frontier t8_64all
theorem t8_65choices : plan9216.choices=[8,3,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_65part0 : t8_65jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_65frontier : t8_65root.frontier 0=t8_65jobs := by rfl
theorem t8_65all : t8_65jobs.all (Job.check tree)=true := by
  simp only [t8_65jobs,List.all_append,List.all_nil,t8_65part0,Bool.and_self]
theorem t8_65checked : Checked tree [8,3,7,7,7,7,7,7] := by
  refine ⟨plan9216,valid9216,t8_65choices,?_⟩
  exact check_of_frontier tree 0 t8_65root t8_65jobs t8_65frontier t8_65all
theorem t8_66choices : plan9242.choices=[8,6,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_66part0 : t8_66jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_66frontier : t8_66root.frontier 0=t8_66jobs := by rfl
theorem t8_66all : t8_66jobs.all (Job.check tree)=true := by
  simp only [t8_66jobs,List.all_append,List.all_nil,t8_66part0,Bool.and_self]
theorem t8_66checked : Checked tree [8,6,7,7,7,7,7,7] := by
  refine ⟨plan9242,valid9242,t8_66choices,?_⟩
  exact check_of_frontier tree 0 t8_66root t8_66jobs t8_66frontier t8_66all
theorem t8_67choices : plan9243.choices=[8,7,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_67part0 : t8_67jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_67frontier : t8_67root.frontier 0=t8_67jobs := by rfl
theorem t8_67all : t8_67jobs.all (Job.check tree)=true := by
  simp only [t8_67jobs,List.all_append,List.all_nil,t8_67part0,Bool.and_self]
theorem t8_67checked : Checked tree [8,7,7,7,7,7,7,7] := by
  refine ⟨plan9243,valid9243,t8_67choices,?_⟩
  exact check_of_frontier tree 0 t8_67root t8_67jobs t8_67frontier t8_67all
theorem t8_68choices : plan9244.choices=[8,10,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_68part0 : t8_68jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_68frontier : t8_68root.frontier 0=t8_68jobs := by rfl
theorem t8_68all : t8_68jobs.all (Job.check tree)=true := by
  simp only [t8_68jobs,List.all_append,List.all_nil,t8_68part0,Bool.and_self]
theorem t8_68checked : Checked tree [8,10,7,7,7,7,7,7] := by
  refine ⟨plan9244,valid9244,t8_68choices,?_⟩
  exact check_of_frontier tree 0 t8_68root t8_68jobs t8_68frontier t8_68all
theorem t8_69choices : plan9189.choices=[9,3,3,7,7,7,7,7].map (options 8 6) := by rfl


theorem t8_69part0 : t8_69jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_69frontier : t8_69root.frontier 0=t8_69jobs := by rfl
theorem t8_69all : t8_69jobs.all (Job.check tree)=true := by
  simp only [t8_69jobs,List.all_append,List.all_nil,t8_69part0,Bool.and_self]
theorem t8_69checked : Checked tree [9,3,3,7,7,7,7,7] := by
  refine ⟨plan9189,valid9189,t8_69choices,?_⟩
  exact check_of_frontier tree 0 t8_69root t8_69jobs t8_69frontier t8_69all
theorem t8_70choices : plan9217.choices=[9,3,6,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_70part0 : t8_70jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_70frontier : t8_70root.frontier 0=t8_70jobs := by rfl
theorem t8_70all : t8_70jobs.all (Job.check tree)=true := by
  simp only [t8_70jobs,List.all_append,List.all_nil,t8_70part0,Bool.and_self]
theorem t8_70checked : Checked tree [9,3,6,7,7,7,7,7] := by
  refine ⟨plan9217,valid9217,t8_70choices,?_⟩
  exact check_of_frontier tree 0 t8_70root t8_70jobs t8_70frontier t8_70all
theorem t8_71choices : plan9218.choices=[9,3,7,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_71part0 : t8_71jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_71frontier : t8_71root.frontier 0=t8_71jobs := by rfl
theorem t8_71all : t8_71jobs.all (Job.check tree)=true := by
  simp only [t8_71jobs,List.all_append,List.all_nil,t8_71part0,Bool.and_self]
theorem t8_71checked : Checked tree [9,3,7,7,7,7,7,7] := by
  refine ⟨plan9218,valid9218,t8_71choices,?_⟩
  exact check_of_frontier tree 0 t8_71root t8_71jobs t8_71frontier t8_71all
theorem t8_72choices : plan9219.choices=[9,3,10,7,7,7,7,7].map (options 8 7) := by rfl


theorem t8_72part0 : t8_72jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_72frontier : t8_72root.frontier 0=t8_72jobs := by rfl
theorem t8_72all : t8_72jobs.all (Job.check tree)=true := by
  simp only [t8_72jobs,List.all_append,List.all_nil,t8_72part0,Bool.and_self]
theorem t8_72checked : Checked tree [9,3,10,7,7,7,7,7] := by
  refine ⟨plan9219,valid9219,t8_72choices,?_⟩
  exact check_of_frontier tree 0 t8_72root t8_72jobs t8_72frontier t8_72all
theorem t8_73choices : plan9245.choices=[9,6,6,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_73part0 : t8_73jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_73frontier : t8_73root.frontier 0=t8_73jobs := by rfl
theorem t8_73all : t8_73jobs.all (Job.check tree)=true := by
  simp only [t8_73jobs,List.all_append,List.all_nil,t8_73part0,Bool.and_self]
theorem t8_73checked : Checked tree [9,6,6,7,7,7,7,7] := by
  refine ⟨plan9245,valid9245,t8_73choices,?_⟩
  exact check_of_frontier tree 0 t8_73root t8_73jobs t8_73frontier t8_73all
theorem t8_74choices : plan9246.choices=[9,6,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_74part0 : t8_74jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_74frontier : t8_74root.frontier 0=t8_74jobs := by rfl
theorem t8_74all : t8_74jobs.all (Job.check tree)=true := by
  simp only [t8_74jobs,List.all_append,List.all_nil,t8_74part0,Bool.and_self]
theorem t8_74checked : Checked tree [9,6,7,7,7,7,7,7] := by
  refine ⟨plan9246,valid9246,t8_74choices,?_⟩
  exact check_of_frontier tree 0 t8_74root t8_74jobs t8_74frontier t8_74all
theorem t8_75choices : plan9247.choices=[9,6,10,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_75part0 : t8_75jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_75frontier : t8_75root.frontier 0=t8_75jobs := by rfl
theorem t8_75all : t8_75jobs.all (Job.check tree)=true := by
  simp only [t8_75jobs,List.all_append,List.all_nil,t8_75part0,Bool.and_self]
theorem t8_75checked : Checked tree [9,6,10,7,7,7,7,7] := by
  refine ⟨plan9247,valid9247,t8_75choices,?_⟩
  exact check_of_frontier tree 0 t8_75root t8_75jobs t8_75frontier t8_75all
theorem t8_76choices : plan9248.choices=[9,7,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_76part0 : t8_76jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_76frontier : t8_76root.frontier 0=t8_76jobs := by rfl
theorem t8_76all : t8_76jobs.all (Job.check tree)=true := by
  simp only [t8_76jobs,List.all_append,List.all_nil,t8_76part0,Bool.and_self]
theorem t8_76checked : Checked tree [9,7,7,7,7,7,7,7] := by
  refine ⟨plan9248,valid9248,t8_76choices,?_⟩
  exact check_of_frontier tree 0 t8_76root t8_76jobs t8_76frontier t8_76all
theorem t8_77choices : plan9249.choices=[9,9,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_77part0 : t8_77jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_77frontier : t8_77root.frontier 0=t8_77jobs := by rfl
theorem t8_77all : t8_77jobs.all (Job.check tree)=true := by
  simp only [t8_77jobs,List.all_append,List.all_nil,t8_77part0,Bool.and_self]
theorem t8_77checked : Checked tree [9,9,7,7,7,7,7,7] := by
  refine ⟨plan9249,valid9249,t8_77choices,?_⟩
  exact check_of_frontier tree 0 t8_77root t8_77jobs t8_77frontier t8_77all
theorem t8_78choices : plan9250.choices=[9,10,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_78part0 : t8_78jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_78frontier : t8_78root.frontier 0=t8_78jobs := by rfl
theorem t8_78all : t8_78jobs.all (Job.check tree)=true := by
  simp only [t8_78jobs,List.all_append,List.all_nil,t8_78part0,Bool.and_self]
theorem t8_78checked : Checked tree [9,10,7,7,7,7,7,7] := by
  refine ⟨plan9250,valid9250,t8_78choices,?_⟩
  exact check_of_frontier tree 0 t8_78root t8_78jobs t8_78frontier t8_78all
theorem t8_79choices : plan9251.choices=[9,10,10,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_79part0 : t8_79jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_79frontier : t8_79root.frontier 0=t8_79jobs := by rfl
theorem t8_79all : t8_79jobs.all (Job.check tree)=true := by
  simp only [t8_79jobs,List.all_append,List.all_nil,t8_79part0,Bool.and_self]
theorem t8_79checked : Checked tree [9,10,10,7,7,7,7,7] := by
  refine ⟨plan9251,valid9251,t8_79choices,?_⟩
  exact check_of_frontier tree 0 t8_79root t8_79jobs t8_79frontier t8_79all
theorem t8_80choices : plan9252.choices=[10,7,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_80part0 : t8_80jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_80frontier : t8_80root.frontier 0=t8_80jobs := by rfl
theorem t8_80all : t8_80jobs.all (Job.check tree)=true := by
  simp only [t8_80jobs,List.all_append,List.all_nil,t8_80part0,Bool.and_self]
theorem t8_80checked : Checked tree [10,7,7,7,7,7,7,7] := by
  refine ⟨plan9252,valid9252,t8_80choices,?_⟩
  exact check_of_frontier tree 0 t8_80root t8_80jobs t8_80frontier t8_80all
theorem t8_81choices : plan9253.choices=[10,10,7,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_81part0 : t8_81jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_81frontier : t8_81root.frontier 0=t8_81jobs := by rfl
theorem t8_81all : t8_81jobs.all (Job.check tree)=true := by
  simp only [t8_81jobs,List.all_append,List.all_nil,t8_81part0,Bool.and_self]
theorem t8_81checked : Checked tree [10,10,7,7,7,7,7,7] := by
  refine ⟨plan9253,valid9253,t8_81choices,?_⟩
  exact check_of_frontier tree 0 t8_81root t8_81jobs t8_81frontier t8_81all
theorem t8_82choices : plan9254.choices=[10,10,10,7,7,7,7,7].map (options 8 8) := by rfl


theorem t8_82part0 : t8_82jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_82frontier : t8_82root.frontier 0=t8_82jobs := by rfl
theorem t8_82all : t8_82jobs.all (Job.check tree)=true := by
  simp only [t8_82jobs,List.all_append,List.all_nil,t8_82part0,Bool.and_self]
theorem t8_82checked : Checked tree [10,10,10,7,7,7,7,7] := by
  refine ⟨plan9254,valid9254,t8_82choices,?_⟩
  exact check_of_frontier tree 0 t8_82root t8_82jobs t8_82frontier t8_82all
theorem t8_83choices : plan9255.choices=[10,10,10,10,7,7,7,7].map (options 8 8) := by rfl


theorem t8_83part0 : t8_83jobs0.all (Job.check tree)=true := by decide +kernel

theorem t8_83frontier : t8_83root.frontier 0=t8_83jobs := by rfl
theorem t8_83all : t8_83jobs.all (Job.check tree)=true := by
  simp only [t8_83jobs,List.all_append,List.all_nil,t8_83part0,Bool.and_self]
theorem t8_83checked : Checked tree [10,10,10,10,7,7,7,7] := by
  refine ⟨plan9255,valid9255,t8_83choices,?_⟩
  exact check_of_frontier tree 0 t8_83root t8_83jobs t8_83frontier t8_83all
theorem t9_0choices : plan9257.choices=[7,7,7,7,7,7,7,7,7].map (options 9 9) := by rfl


theorem t9_0part0 : t9_0jobs0.all (Job.check tree)=true := by decide +kernel

theorem t9_0frontier : t9_0root.frontier 0=t9_0jobs := by rfl
theorem t9_0all : t9_0jobs.all (Job.check tree)=true := by
  simp only [t9_0jobs,List.all_append,List.all_nil,t9_0part0,Bool.and_self]
theorem t9_0checked : Checked tree [7,7,7,7,7,7,7,7,7] := by
  refine ⟨plan9257,valid9257,t9_0choices,?_⟩
  exact check_of_frontier tree 0 t9_0root t9_0jobs t9_0frontier t9_0all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks194 :=
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_23checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_24checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_25checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_26checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_27checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_28checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_29checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_30checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_31checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_11checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_32checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_33checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_34checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_35checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_36checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_37checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_38checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_39checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_40checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_41checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_12checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_42checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_43checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_44checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_45checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_46checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_47checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_48checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_49checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_50checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_51checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_13checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_52checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_53checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_54checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_55checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_56checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_57checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_58checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_59checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_60checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_61checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_14checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_62checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_63checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_64checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_65checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_66checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_67checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_68checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_69checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_70checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_71checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_15checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_72checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_73checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_74checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_75checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_76checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_77checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_78checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_79checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_80checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_81checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_16checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_82checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_83checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t9_0checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_17checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_18checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_19checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_20checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_21checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_10checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t8_22checked⟩
