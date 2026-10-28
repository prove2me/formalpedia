-- Prove2me | solution 1 for Sensitivity213981Formal.Certificates.Endpoint22ReachChecks000
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T02:45:19.750173+00:00
-- url     : https://prove2.me/submissions/20b841f2-ed6c-4e16-b629-4fd0afa0c86b

import Definitions.Def_Sensitivity213981Formal_Contract_Endpoint22ReachChecks000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChecks000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans000
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans018
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans019
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans021
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

theorem valid1 : plan1.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid2 : plan2.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid3 : plan3.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid4 : plan4.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid5 : plan5.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid6 : plan6.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid7 : plan7.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid8 : plan8.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid9 : plan9.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid10 : plan10.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid11 : plan11.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid12 : plan12.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid13 : plan13.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid14 : plan14.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid15 : plan15.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid16 : plan16.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid17 : plan17.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid18 : plan18.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid19 : plan19.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid20 : plan20.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid21 : plan21.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid22 : plan22.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid23 : plan23.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid24 : plan24.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid25 : plan25.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid26 : plan26.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid27 : plan27.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid28 : plan28.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid29 : plan29.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid30 : plan30.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid31 : plan31.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid32 : plan32.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid33 : plan33.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid34 : plan34.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid35 : plan35.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid36 : plan36.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid37 : plan37.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid38 : plan38.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid39 : plan39.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid40 : plan40.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid41 : plan41.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid42 : plan42.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid43 : plan43.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid44 : plan44.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid45 : plan45.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid46 : plan46.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid47 : plan47.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid48 : plan48.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid49 : plan49.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid50 : plan50.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid51 : plan51.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid52 : plan52.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid53 : plan53.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid54 : plan54.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid55 : plan55.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid56 : plan56.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid57 : plan57.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid58 : plan58.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid59 : plan59.Valid := valid_step _ _ _ valid0 (by decide +kernel)

theorem valid60 : plan60.Valid := valid_step _ _ _ valid0 (by decide +kernel)



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













































































































































theorem valid167 : plan167.Valid := valid_step _ _ _ valid12 (by decide +kernel)

theorem valid168 : plan168.Valid := valid_step _ _ _ valid13 (by decide +kernel)

theorem valid169 : plan169.Valid := valid_step _ _ _ valid14 (by decide +kernel)

theorem valid170 : plan170.Valid := valid_step _ _ _ valid12 (by decide +kernel)

theorem valid171 : plan171.Valid := valid_step _ _ _ valid13 (by decide +kernel)

theorem valid172 : plan172.Valid := valid_step _ _ _ valid14 (by decide +kernel)

theorem valid173 : plan173.Valid := valid_step _ _ _ valid13 (by decide +kernel)

theorem valid174 : plan174.Valid := valid_step _ _ _ valid14 (by decide +kernel)

theorem valid175 : plan175.Valid := valid_step _ _ _ valid14 (by decide +kernel)

theorem valid176 : plan176.Valid := valid_step _ _ _ valid17 (by decide +kernel)

theorem valid177 : plan177.Valid := valid_step _ _ _ valid18 (by decide +kernel)

theorem valid178 : plan178.Valid := valid_step _ _ _ valid19 (by decide +kernel)

theorem valid179 : plan179.Valid := valid_step _ _ _ valid20 (by decide +kernel)

theorem valid180 : plan180.Valid := valid_step _ _ _ valid21 (by decide +kernel)

theorem valid181 : plan181.Valid := valid_step _ _ _ valid22 (by decide +kernel)

theorem valid182 : plan182.Valid := valid_step _ _ _ valid23 (by decide +kernel)

theorem valid183 : plan183.Valid := valid_step _ _ _ valid17 (by decide +kernel)

theorem valid184 : plan184.Valid := valid_step _ _ _ valid18 (by decide +kernel)

theorem valid185 : plan185.Valid := valid_step _ _ _ valid19 (by decide +kernel)

theorem valid186 : plan186.Valid := valid_step _ _ _ valid20 (by decide +kernel)

theorem valid187 : plan187.Valid := valid_step _ _ _ valid21 (by decide +kernel)

theorem valid188 : plan188.Valid := valid_step _ _ _ valid22 (by decide +kernel)

theorem valid189 : plan189.Valid := valid_step _ _ _ valid23 (by decide +kernel)

theorem valid190 : plan190.Valid := valid_step _ _ _ valid18 (by decide +kernel)

theorem valid191 : plan191.Valid := valid_step _ _ _ valid19 (by decide +kernel)

theorem valid192 : plan192.Valid := valid_step _ _ _ valid20 (by decide +kernel)
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

theorem valid193 : plan193.Valid := valid_step _ _ _ valid22 (by decide +kernel)

theorem valid194 : plan194.Valid := valid_step _ _ _ valid23 (by decide +kernel)

theorem valid195 : plan195.Valid := valid_step _ _ _ valid19 (by decide +kernel)

theorem valid196 : plan196.Valid := valid_step _ _ _ valid20 (by decide +kernel)

theorem valid197 : plan197.Valid := valid_step _ _ _ valid23 (by decide +kernel)

theorem valid198 : plan198.Valid := valid_step _ _ _ valid15 (by decide +kernel)

theorem valid199 : plan199.Valid := valid_step _ _ _ valid16 (by decide +kernel)

theorem valid200 : plan200.Valid := valid_step _ _ _ valid16 (by decide +kernel)

theorem valid201 : plan201.Valid := valid_step _ _ _ valid15 (by decide +kernel)

theorem valid202 : plan202.Valid := valid_step _ _ _ valid16 (by decide +kernel)

theorem valid203 : plan203.Valid := valid_step _ _ _ valid16 (by decide +kernel)

theorem valid204 : plan204.Valid := valid_step _ _ _ valid24 (by decide +kernel)

theorem valid205 : plan205.Valid := valid_step _ _ _ valid25 (by decide +kernel)

theorem valid206 : plan206.Valid := valid_step _ _ _ valid26 (by decide +kernel)

theorem valid207 : plan207.Valid := valid_step _ _ _ valid27 (by decide +kernel)

theorem valid208 : plan208.Valid := valid_step _ _ _ valid28 (by decide +kernel)

theorem valid209 : plan209.Valid := valid_step _ _ _ valid29 (by decide +kernel)

theorem valid210 : plan210.Valid := valid_step _ _ _ valid30 (by decide +kernel)

theorem valid211 : plan211.Valid := valid_step _ _ _ valid25 (by decide +kernel)

theorem valid212 : plan212.Valid := valid_step _ _ _ valid26 (by decide +kernel)

theorem valid213 : plan213.Valid := valid_step _ _ _ valid27 (by decide +kernel)

theorem valid214 : plan214.Valid := valid_step _ _ _ valid29 (by decide +kernel)

theorem valid215 : plan215.Valid := valid_step _ _ _ valid30 (by decide +kernel)

theorem valid216 : plan216.Valid := valid_step _ _ _ valid26 (by decide +kernel)

theorem valid217 : plan217.Valid := valid_step _ _ _ valid27 (by decide +kernel)

theorem valid218 : plan218.Valid := valid_step _ _ _ valid30 (by decide +kernel)

theorem valid219 : plan219.Valid := valid_step _ _ _ valid27 (by decide +kernel)

theorem valid220 : plan220.Valid := valid_step _ _ _ valid25 (by decide +kernel)

theorem valid221 : plan221.Valid := valid_step _ _ _ valid26 (by decide +kernel)

theorem valid222 : plan222.Valid := valid_step _ _ _ valid27 (by decide +kernel)

theorem valid223 : plan223.Valid := valid_step _ _ _ valid28 (by decide +kernel)

theorem valid224 : plan224.Valid := valid_step _ _ _ valid29 (by decide +kernel)

theorem valid225 : plan225.Valid := valid_step _ _ _ valid30 (by decide +kernel)

theorem valid226 : plan226.Valid := valid_step _ _ _ valid26 (by decide +kernel)

theorem valid227 : plan227.Valid := valid_step _ _ _ valid27 (by decide +kernel)

theorem valid228 : plan228.Valid := valid_step _ _ _ valid29 (by decide +kernel)

theorem valid229 : plan229.Valid := valid_step _ _ _ valid30 (by decide +kernel)

theorem valid230 : plan230.Valid := valid_step _ _ _ valid27 (by decide +kernel)

theorem valid231 : plan231.Valid := valid_step _ _ _ valid30 (by decide +kernel)

theorem valid232 : plan232.Valid := valid_step _ _ _ valid31 (by decide +kernel)

theorem valid233 : plan233.Valid := valid_step _ _ _ valid32 (by decide +kernel)

theorem valid234 : plan234.Valid := valid_step _ _ _ valid33 (by decide +kernel)

theorem valid235 : plan235.Valid := valid_step _ _ _ valid32 (by decide +kernel)

theorem valid236 : plan236.Valid := valid_step _ _ _ valid33 (by decide +kernel)

theorem valid237 : plan237.Valid := valid_step _ _ _ valid33 (by decide +kernel)

theorem valid238 : plan238.Valid := valid_step _ _ _ valid36 (by decide +kernel)

theorem valid239 : plan239.Valid := valid_step _ _ _ valid37 (by decide +kernel)

theorem valid240 : plan240.Valid := valid_step _ _ _ valid38 (by decide +kernel)

theorem valid241 : plan241.Valid := valid_step _ _ _ valid39 (by decide +kernel)

theorem valid242 : plan242.Valid := valid_step _ _ _ valid40 (by decide +kernel)

theorem valid243 : plan243.Valid := valid_step _ _ _ valid41 (by decide +kernel)

theorem valid244 : plan244.Valid := valid_step _ _ _ valid42 (by decide +kernel)

theorem valid245 : plan245.Valid := valid_step _ _ _ valid34 (by decide +kernel)

theorem valid246 : plan246.Valid := valid_step _ _ _ valid35 (by decide +kernel)

theorem valid247 : plan247.Valid := valid_step _ _ _ valid37 (by decide +kernel)

theorem valid248 : plan248.Valid := valid_step _ _ _ valid38 (by decide +kernel)

theorem valid249 : plan249.Valid := valid_step _ _ _ valid39 (by decide +kernel)

theorem valid250 : plan250.Valid := valid_step _ _ _ valid41 (by decide +kernel)

theorem valid251 : plan251.Valid := valid_step _ _ _ valid42 (by decide +kernel)

theorem valid252 : plan252.Valid := valid_step _ _ _ valid35 (by decide +kernel)

theorem valid253 : plan253.Valid := valid_step _ _ _ valid38 (by decide +kernel)

theorem valid254 : plan254.Valid := valid_step _ _ _ valid39 (by decide +kernel)

theorem valid255 : plan255.Valid := valid_step _ _ _ valid42 (by decide +kernel)

theorem valid256 : plan256.Valid := valid_step _ _ _ valid34 (by decide +kernel)

theorem valid257 : plan257.Valid := valid_step _ _ _ valid35 (by decide +kernel)

theorem valid258 : plan258.Valid := valid_step _ _ _ valid35 (by decide +kernel)

theorem valid259 : plan259.Valid := valid_step _ _ _ valid34 (by decide +kernel)

theorem valid260 : plan260.Valid := valid_step _ _ _ valid35 (by decide +kernel)

theorem valid261 : plan261.Valid := valid_step _ _ _ valid35 (by decide +kernel)

theorem valid262 : plan262.Valid := valid_step _ _ _ valid46 (by decide +kernel)

theorem valid263 : plan263.Valid := valid_step _ _ _ valid47 (by decide +kernel)

theorem valid264 : plan264.Valid := valid_step _ _ _ valid48 (by decide +kernel)

theorem valid265 : plan265.Valid := valid_step _ _ _ valid50 (by decide +kernel)

theorem valid266 : plan266.Valid := valid_step _ _ _ valid51 (by decide +kernel)

theorem valid267 : plan267.Valid := valid_step _ _ _ valid47 (by decide +kernel)

theorem valid268 : plan268.Valid := valid_step _ _ _ valid48 (by decide +kernel)

theorem valid269 : plan269.Valid := valid_step _ _ _ valid51 (by decide +kernel)

theorem valid270 : plan270.Valid := valid_step _ _ _ valid43 (by decide +kernel)

theorem valid271 : plan271.Valid := valid_step _ _ _ valid44 (by decide +kernel)

theorem valid272 : plan272.Valid := valid_step _ _ _ valid45 (by decide +kernel)

theorem valid273 : plan273.Valid := valid_step _ _ _ valid46 (by decide +kernel)

theorem valid274 : plan274.Valid := valid_step _ _ _ valid47 (by decide +kernel)

theorem valid275 : plan275.Valid := valid_step _ _ _ valid48 (by decide +kernel)

theorem valid276 : plan276.Valid := valid_step _ _ _ valid49 (by decide +kernel)

theorem valid277 : plan277.Valid := valid_step _ _ _ valid50 (by decide +kernel)

theorem valid278 : plan278.Valid := valid_step _ _ _ valid51 (by decide +kernel)

theorem valid279 : plan279.Valid := valid_step _ _ _ valid44 (by decide +kernel)

theorem valid280 : plan280.Valid := valid_step _ _ _ valid46 (by decide +kernel)

theorem valid281 : plan281.Valid := valid_step _ _ _ valid47 (by decide +kernel)

theorem valid282 : plan282.Valid := valid_step _ _ _ valid48 (by decide +kernel)

theorem valid283 : plan283.Valid := valid_step _ _ _ valid50 (by decide +kernel)

theorem valid284 : plan284.Valid := valid_step _ _ _ valid51 (by decide +kernel)

theorem valid285 : plan285.Valid := valid_step _ _ _ valid47 (by decide +kernel)

theorem valid286 : plan286.Valid := valid_step _ _ _ valid48 (by decide +kernel)

theorem valid287 : plan287.Valid := valid_step _ _ _ valid51 (by decide +kernel)

theorem valid288 : plan288.Valid := valid_step _ _ _ valid48 (by decide +kernel)
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



















































































































theorem valid634 : plan634.Valid := valid_step _ _ _ valid233 (by decide +kernel)

theorem valid635 : plan635.Valid := valid_step _ _ _ valid234 (by decide +kernel)

theorem valid636 : plan636.Valid := valid_step _ _ _ valid235 (by decide +kernel)

theorem valid637 : plan637.Valid := valid_step _ _ _ valid236 (by decide +kernel)

theorem valid638 : plan638.Valid := valid_step _ _ _ valid237 (by decide +kernel)

theorem valid639 : plan639.Valid := valid_step _ _ _ valid232 (by decide +kernel)

theorem valid640 : plan640.Valid := valid_step _ _ _ valid233 (by decide +kernel)

theorem valid641 : plan641.Valid := valid_step _ _ _ valid234 (by decide +kernel)

theorem valid642 : plan642.Valid := valid_step _ _ _ valid235 (by decide +kernel)

theorem valid643 : plan643.Valid := valid_step _ _ _ valid236 (by decide +kernel)

theorem valid644 : plan644.Valid := valid_step _ _ _ valid237 (by decide +kernel)

theorem valid645 : plan645.Valid := valid_step _ _ _ valid235 (by decide +kernel)

theorem valid646 : plan646.Valid := valid_step _ _ _ valid236 (by decide +kernel)

theorem valid647 : plan647.Valid := valid_step _ _ _ valid237 (by decide +kernel)

theorem valid648 : plan648.Valid := valid_step _ _ _ valid237 (by decide +kernel)

theorem valid649 : plan649.Valid := valid_step _ _ _ valid239 (by decide +kernel)

theorem valid650 : plan650.Valid := valid_step _ _ _ valid240 (by decide +kernel)

theorem valid651 : plan651.Valid := valid_step _ _ _ valid241 (by decide +kernel)

theorem valid652 : plan652.Valid := valid_step _ _ _ valid243 (by decide +kernel)

theorem valid653 : plan653.Valid := valid_step _ _ _ valid244 (by decide +kernel)

theorem valid654 : plan654.Valid := valid_step _ _ _ valid247 (by decide +kernel)

theorem valid655 : plan655.Valid := valid_step _ _ _ valid248 (by decide +kernel)

theorem valid656 : plan656.Valid := valid_step _ _ _ valid249 (by decide +kernel)

theorem valid657 : plan657.Valid := valid_step _ _ _ valid250 (by decide +kernel)

theorem valid658 : plan658.Valid := valid_step _ _ _ valid251 (by decide +kernel)

theorem valid659 : plan659.Valid := valid_step _ _ _ valid253 (by decide +kernel)

theorem valid660 : plan660.Valid := valid_step _ _ _ valid254 (by decide +kernel)

theorem valid661 : plan661.Valid := valid_step _ _ _ valid255 (by decide +kernel)

theorem valid662 : plan662.Valid := valid_step _ _ _ valid256 (by decide +kernel)

theorem valid663 : plan663.Valid := valid_step _ _ _ valid257 (by decide +kernel)

theorem valid664 : plan664.Valid := valid_step _ _ _ valid258 (by decide +kernel)

theorem valid665 : plan665.Valid := valid_step _ _ _ valid259 (by decide +kernel)

theorem valid666 : plan666.Valid := valid_step _ _ _ valid260 (by decide +kernel)

theorem valid667 : plan667.Valid := valid_step _ _ _ valid261 (by decide +kernel)

theorem valid668 : plan668.Valid := valid_step _ _ _ valid238 (by decide +kernel)

theorem valid669 : plan669.Valid := valid_step _ _ _ valid239 (by decide +kernel)

theorem valid670 : plan670.Valid := valid_step _ _ _ valid240 (by decide +kernel)

theorem valid671 : plan671.Valid := valid_step _ _ _ valid241 (by decide +kernel)

theorem valid672 : plan672.Valid := valid_step _ _ _ valid242 (by decide +kernel)
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

theorem valid289 : plan289.Valid := valid_step _ _ _ valid43 (by decide +kernel)

theorem valid290 : plan290.Valid := valid_step _ _ _ valid44 (by decide +kernel)

theorem valid291 : plan291.Valid := valid_step _ _ _ valid46 (by decide +kernel)

theorem valid292 : plan292.Valid := valid_step _ _ _ valid47 (by decide +kernel)

theorem valid293 : plan293.Valid := valid_step _ _ _ valid48 (by decide +kernel)

theorem valid294 : plan294.Valid := valid_step _ _ _ valid49 (by decide +kernel)

theorem valid295 : plan295.Valid := valid_step _ _ _ valid50 (by decide +kernel)

theorem valid296 : plan296.Valid := valid_step _ _ _ valid51 (by decide +kernel)

theorem valid297 : plan297.Valid := valid_step _ _ _ valid44 (by decide +kernel)

theorem valid298 : plan298.Valid := valid_step _ _ _ valid47 (by decide +kernel)

theorem valid299 : plan299.Valid := valid_step _ _ _ valid48 (by decide +kernel)

theorem valid300 : plan300.Valid := valid_step _ _ _ valid50 (by decide +kernel)

theorem valid301 : plan301.Valid := valid_step _ _ _ valid51 (by decide +kernel)

theorem valid302 : plan302.Valid := valid_step _ _ _ valid48 (by decide +kernel)

theorem valid303 : plan303.Valid := valid_step _ _ _ valid51 (by decide +kernel)

theorem valid304 : plan304.Valid := valid_step _ _ _ valid52 (by decide +kernel)

theorem valid305 : plan305.Valid := valid_step _ _ _ valid53 (by decide +kernel)

theorem valid306 : plan306.Valid := valid_step _ _ _ valid54 (by decide +kernel)

theorem valid307 : plan307.Valid := valid_step _ _ _ valid55 (by decide +kernel)

theorem valid308 : plan308.Valid := valid_step _ _ _ valid56 (by decide +kernel)

theorem valid309 : plan309.Valid := valid_step _ _ _ valid57 (by decide +kernel)

theorem valid310 : plan310.Valid := valid_step _ _ _ valid58 (by decide +kernel)

theorem valid311 : plan311.Valid := valid_step _ _ _ valid53 (by decide +kernel)

theorem valid312 : plan312.Valid := valid_step _ _ _ valid54 (by decide +kernel)

theorem valid313 : plan313.Valid := valid_step _ _ _ valid55 (by decide +kernel)

theorem valid314 : plan314.Valid := valid_step _ _ _ valid57 (by decide +kernel)

theorem valid315 : plan315.Valid := valid_step _ _ _ valid58 (by decide +kernel)

theorem valid316 : plan316.Valid := valid_step _ _ _ valid54 (by decide +kernel)

theorem valid317 : plan317.Valid := valid_step _ _ _ valid55 (by decide +kernel)

theorem valid318 : plan318.Valid := valid_step _ _ _ valid58 (by decide +kernel)

theorem valid319 : plan319.Valid := valid_step _ _ _ valid55 (by decide +kernel)

theorem valid320 : plan320.Valid := valid_step _ _ _ valid53 (by decide +kernel)

theorem valid321 : plan321.Valid := valid_step _ _ _ valid54 (by decide +kernel)

theorem valid322 : plan322.Valid := valid_step _ _ _ valid55 (by decide +kernel)

theorem valid323 : plan323.Valid := valid_step _ _ _ valid56 (by decide +kernel)

theorem valid324 : plan324.Valid := valid_step _ _ _ valid57 (by decide +kernel)

theorem valid325 : plan325.Valid := valid_step _ _ _ valid58 (by decide +kernel)

theorem valid326 : plan326.Valid := valid_step _ _ _ valid54 (by decide +kernel)

theorem valid327 : plan327.Valid := valid_step _ _ _ valid55 (by decide +kernel)

theorem valid328 : plan328.Valid := valid_step _ _ _ valid57 (by decide +kernel)

theorem valid329 : plan329.Valid := valid_step _ _ _ valid58 (by decide +kernel)

theorem valid330 : plan330.Valid := valid_step _ _ _ valid55 (by decide +kernel)

theorem valid331 : plan331.Valid := valid_step _ _ _ valid58 (by decide +kernel)

theorem valid332 : plan332.Valid := valid_step _ _ _ valid60 (by decide +kernel)

theorem valid333 : plan333.Valid := valid_step _ _ _ valid59 (by decide +kernel)

theorem valid334 : plan334.Valid := valid_step _ _ _ valid60 (by decide +kernel)

theorem valid335 : plan335.Valid := valid_step _ _ _ valid60 (by decide +kernel)

theorem valid336 : plan336.Valid := valid_step _ _ _ valid64 (by decide +kernel)

theorem valid337 : plan337.Valid := valid_step _ _ _ valid65 (by decide +kernel)

theorem valid338 : plan338.Valid := valid_step _ _ _ valid67 (by decide +kernel)



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

theorem valid350 : plan350.Valid := valid_step _ _ _ valid62 (by decide +kernel)

theorem valid351 : plan351.Valid := valid_step _ _ _ valid62 (by decide +kernel)

theorem valid352 : plan352.Valid := valid_step _ _ _ valid62 (by decide +kernel)

theorem valid353 : plan353.Valid := valid_step _ _ _ valid62 (by decide +kernel)







theorem valid357 : plan357.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid358 : plan358.Valid := valid_step _ _ _ valid72 (by decide +kernel)



theorem valid360 : plan360.Valid := valid_step _ _ _ valid74 (by decide +kernel)



theorem valid362 : plan362.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid363 : plan363.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid364 : plan364.Valid := valid_step _ _ _ valid74 (by decide +kernel)



theorem valid366 : plan366.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid367 : plan367.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid368 : plan368.Valid := valid_step _ _ _ valid74 (by decide +kernel)

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



theorem valid380 : plan380.Valid := valid_step _ _ _ valid71 (by decide +kernel)

theorem valid381 : plan381.Valid := valid_step _ _ _ valid72 (by decide +kernel)

theorem valid382 : plan382.Valid := valid_step _ _ _ valid74 (by decide +kernel)

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

theorem valid673 : plan673.Valid := valid_step _ _ _ valid243 (by decide +kernel)

theorem valid674 : plan674.Valid := valid_step _ _ _ valid244 (by decide +kernel)

theorem valid675 : plan675.Valid := valid_step _ _ _ valid247 (by decide +kernel)

theorem valid676 : plan676.Valid := valid_step _ _ _ valid248 (by decide +kernel)

theorem valid677 : plan677.Valid := valid_step _ _ _ valid249 (by decide +kernel)

theorem valid678 : plan678.Valid := valid_step _ _ _ valid250 (by decide +kernel)

theorem valid679 : plan679.Valid := valid_step _ _ _ valid251 (by decide +kernel)

theorem valid680 : plan680.Valid := valid_step _ _ _ valid253 (by decide +kernel)

theorem valid681 : plan681.Valid := valid_step _ _ _ valid254 (by decide +kernel)

theorem valid682 : plan682.Valid := valid_step _ _ _ valid255 (by decide +kernel)

theorem valid683 : plan683.Valid := valid_step _ _ _ valid256 (by decide +kernel)

theorem valid684 : plan684.Valid := valid_step _ _ _ valid257 (by decide +kernel)

theorem valid685 : plan685.Valid := valid_step _ _ _ valid258 (by decide +kernel)

theorem valid686 : plan686.Valid := valid_step _ _ _ valid259 (by decide +kernel)

theorem valid687 : plan687.Valid := valid_step _ _ _ valid260 (by decide +kernel)

theorem valid688 : plan688.Valid := valid_step _ _ _ valid261 (by decide +kernel)

theorem valid689 : plan689.Valid := valid_step _ _ _ valid247 (by decide +kernel)

theorem valid690 : plan690.Valid := valid_step _ _ _ valid248 (by decide +kernel)

theorem valid691 : plan691.Valid := valid_step _ _ _ valid249 (by decide +kernel)

theorem valid692 : plan692.Valid := valid_step _ _ _ valid250 (by decide +kernel)

theorem valid693 : plan693.Valid := valid_step _ _ _ valid251 (by decide +kernel)

theorem valid694 : plan694.Valid := valid_step _ _ _ valid253 (by decide +kernel)

theorem valid695 : plan695.Valid := valid_step _ _ _ valid254 (by decide +kernel)

theorem valid696 : plan696.Valid := valid_step _ _ _ valid255 (by decide +kernel)

theorem valid697 : plan697.Valid := valid_step _ _ _ valid258 (by decide +kernel)

theorem valid698 : plan698.Valid := valid_step _ _ _ valid261 (by decide +kernel)

theorem valid699 : plan699.Valid := valid_step _ _ _ valid253 (by decide +kernel)

theorem valid700 : plan700.Valid := valid_step _ _ _ valid254 (by decide +kernel)

theorem valid701 : plan701.Valid := valid_step _ _ _ valid255 (by decide +kernel)

theorem valid702 : plan702.Valid := valid_step _ _ _ valid245 (by decide +kernel)

theorem valid703 : plan703.Valid := valid_step _ _ _ valid246 (by decide +kernel)

theorem valid704 : plan704.Valid := valid_step _ _ _ valid252 (by decide +kernel)

theorem valid705 : plan705.Valid := valid_step _ _ _ valid252 (by decide +kernel)

theorem valid706 : plan706.Valid := valid_step _ _ _ valid245 (by decide +kernel)

theorem valid707 : plan707.Valid := valid_step _ _ _ valid246 (by decide +kernel)

theorem valid708 : plan708.Valid := valid_step _ _ _ valid252 (by decide +kernel)

theorem valid709 : plan709.Valid := valid_step _ _ _ valid252 (by decide +kernel)

theorem valid710 : plan710.Valid := valid_step _ _ _ valid273 (by decide +kernel)

theorem valid711 : plan711.Valid := valid_step _ _ _ valid274 (by decide +kernel)

theorem valid712 : plan712.Valid := valid_step _ _ _ valid275 (by decide +kernel)

theorem valid713 : plan713.Valid := valid_step _ _ _ valid277 (by decide +kernel)

theorem valid714 : plan714.Valid := valid_step _ _ _ valid278 (by decide +kernel)

theorem valid715 : plan715.Valid := valid_step _ _ _ valid280 (by decide +kernel)

theorem valid716 : plan716.Valid := valid_step _ _ _ valid281 (by decide +kernel)

theorem valid717 : plan717.Valid := valid_step _ _ _ valid282 (by decide +kernel)

theorem valid718 : plan718.Valid := valid_step _ _ _ valid283 (by decide +kernel)

theorem valid719 : plan719.Valid := valid_step _ _ _ valid284 (by decide +kernel)

theorem valid720 : plan720.Valid := valid_step _ _ _ valid285 (by decide +kernel)

theorem valid721 : plan721.Valid := valid_step _ _ _ valid286 (by decide +kernel)

theorem valid722 : plan722.Valid := valid_step _ _ _ valid287 (by decide +kernel)

theorem valid723 : plan723.Valid := valid_step _ _ _ valid288 (by decide +kernel)

theorem valid724 : plan724.Valid := valid_step _ _ _ valid291 (by decide +kernel)

theorem valid725 : plan725.Valid := valid_step _ _ _ valid292 (by decide +kernel)

theorem valid726 : plan726.Valid := valid_step _ _ _ valid293 (by decide +kernel)

theorem valid727 : plan727.Valid := valid_step _ _ _ valid295 (by decide +kernel)

theorem valid728 : plan728.Valid := valid_step _ _ _ valid296 (by decide +kernel)

theorem valid729 : plan729.Valid := valid_step _ _ _ valid298 (by decide +kernel)

theorem valid730 : plan730.Valid := valid_step _ _ _ valid299 (by decide +kernel)

theorem valid731 : plan731.Valid := valid_step _ _ _ valid300 (by decide +kernel)

theorem valid732 : plan732.Valid := valid_step _ _ _ valid301 (by decide +kernel)

theorem valid733 : plan733.Valid := valid_step _ _ _ valid302 (by decide +kernel)

theorem valid734 : plan734.Valid := valid_step _ _ _ valid303 (by decide +kernel)

theorem valid735 : plan735.Valid := valid_step _ _ _ valid272 (by decide +kernel)

theorem valid736 : plan736.Valid := valid_step _ _ _ valid273 (by decide +kernel)

theorem valid737 : plan737.Valid := valid_step _ _ _ valid274 (by decide +kernel)

theorem valid738 : plan738.Valid := valid_step _ _ _ valid275 (by decide +kernel)

theorem valid739 : plan739.Valid := valid_step _ _ _ valid276 (by decide +kernel)

theorem valid740 : plan740.Valid := valid_step _ _ _ valid277 (by decide +kernel)

theorem valid741 : plan741.Valid := valid_step _ _ _ valid278 (by decide +kernel)

theorem valid742 : plan742.Valid := valid_step _ _ _ valid280 (by decide +kernel)

theorem valid743 : plan743.Valid := valid_step _ _ _ valid281 (by decide +kernel)

theorem valid744 : plan744.Valid := valid_step _ _ _ valid282 (by decide +kernel)

theorem valid745 : plan745.Valid := valid_step _ _ _ valid283 (by decide +kernel)

theorem valid746 : plan746.Valid := valid_step _ _ _ valid284 (by decide +kernel)

theorem valid747 : plan747.Valid := valid_step _ _ _ valid285 (by decide +kernel)

theorem valid748 : plan748.Valid := valid_step _ _ _ valid286 (by decide +kernel)

theorem valid749 : plan749.Valid := valid_step _ _ _ valid287 (by decide +kernel)

theorem valid750 : plan750.Valid := valid_step _ _ _ valid288 (by decide +kernel)

theorem valid751 : plan751.Valid := valid_step _ _ _ valid291 (by decide +kernel)

theorem valid752 : plan752.Valid := valid_step _ _ _ valid292 (by decide +kernel)

theorem valid753 : plan753.Valid := valid_step _ _ _ valid293 (by decide +kernel)

theorem valid754 : plan754.Valid := valid_step _ _ _ valid294 (by decide +kernel)

theorem valid755 : plan755.Valid := valid_step _ _ _ valid295 (by decide +kernel)

theorem valid756 : plan756.Valid := valid_step _ _ _ valid296 (by decide +kernel)

theorem valid757 : plan757.Valid := valid_step _ _ _ valid298 (by decide +kernel)

theorem valid758 : plan758.Valid := valid_step _ _ _ valid299 (by decide +kernel)

theorem valid759 : plan759.Valid := valid_step _ _ _ valid300 (by decide +kernel)

theorem valid760 : plan760.Valid := valid_step _ _ _ valid301 (by decide +kernel)

theorem valid761 : plan761.Valid := valid_step _ _ _ valid302 (by decide +kernel)

theorem valid762 : plan762.Valid := valid_step _ _ _ valid303 (by decide +kernel)

theorem valid763 : plan763.Valid := valid_step _ _ _ valid280 (by decide +kernel)

theorem valid764 : plan764.Valid := valid_step _ _ _ valid281 (by decide +kernel)

theorem valid765 : plan765.Valid := valid_step _ _ _ valid282 (by decide +kernel)

theorem valid766 : plan766.Valid := valid_step _ _ _ valid283 (by decide +kernel)

theorem valid767 : plan767.Valid := valid_step _ _ _ valid284 (by decide +kernel)

theorem valid768 : plan768.Valid := valid_step _ _ _ valid285 (by decide +kernel)
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

theorem valid769 : plan769.Valid := valid_step _ _ _ valid286 (by decide +kernel)

theorem valid770 : plan770.Valid := valid_step _ _ _ valid287 (by decide +kernel)

theorem valid771 : plan771.Valid := valid_step _ _ _ valid288 (by decide +kernel)

theorem valid772 : plan772.Valid := valid_step _ _ _ valid298 (by decide +kernel)

theorem valid773 : plan773.Valid := valid_step _ _ _ valid299 (by decide +kernel)

theorem valid774 : plan774.Valid := valid_step _ _ _ valid300 (by decide +kernel)

theorem valid775 : plan775.Valid := valid_step _ _ _ valid301 (by decide +kernel)

theorem valid776 : plan776.Valid := valid_step _ _ _ valid302 (by decide +kernel)

theorem valid777 : plan777.Valid := valid_step _ _ _ valid303 (by decide +kernel)

theorem valid778 : plan778.Valid := valid_step _ _ _ valid285 (by decide +kernel)

theorem valid779 : plan779.Valid := valid_step _ _ _ valid286 (by decide +kernel)

theorem valid780 : plan780.Valid := valid_step _ _ _ valid287 (by decide +kernel)

theorem valid781 : plan781.Valid := valid_step _ _ _ valid288 (by decide +kernel)

theorem valid782 : plan782.Valid := valid_step _ _ _ valid302 (by decide +kernel)

theorem valid783 : plan783.Valid := valid_step _ _ _ valid303 (by decide +kernel)

theorem valid784 : plan784.Valid := valid_step _ _ _ valid262 (by decide +kernel)

theorem valid785 : plan785.Valid := valid_step _ _ _ valid263 (by decide +kernel)

theorem valid786 : plan786.Valid := valid_step _ _ _ valid264 (by decide +kernel)

theorem valid787 : plan787.Valid := valid_step _ _ _ valid265 (by decide +kernel)

theorem valid788 : plan788.Valid := valid_step _ _ _ valid266 (by decide +kernel)

theorem valid789 : plan789.Valid := valid_step _ _ _ valid267 (by decide +kernel)

theorem valid790 : plan790.Valid := valid_step _ _ _ valid268 (by decide +kernel)

theorem valid791 : plan791.Valid := valid_step _ _ _ valid269 (by decide +kernel)

theorem valid792 : plan792.Valid := valid_step _ _ _ valid270 (by decide +kernel)

theorem valid793 : plan793.Valid := valid_step _ _ _ valid271 (by decide +kernel)

theorem valid794 : plan794.Valid := valid_step _ _ _ valid279 (by decide +kernel)

theorem valid795 : plan795.Valid := valid_step _ _ _ valid289 (by decide +kernel)

theorem valid796 : plan796.Valid := valid_step _ _ _ valid290 (by decide +kernel)

theorem valid797 : plan797.Valid := valid_step _ _ _ valid297 (by decide +kernel)

theorem valid798 : plan798.Valid := valid_step _ _ _ valid267 (by decide +kernel)

theorem valid799 : plan799.Valid := valid_step _ _ _ valid268 (by decide +kernel)

theorem valid800 : plan800.Valid := valid_step _ _ _ valid269 (by decide +kernel)

theorem valid801 : plan801.Valid := valid_step _ _ _ valid279 (by decide +kernel)

theorem valid802 : plan802.Valid := valid_step _ _ _ valid297 (by decide +kernel)

theorem valid803 : plan803.Valid := valid_step _ _ _ valid262 (by decide +kernel)

theorem valid804 : plan804.Valid := valid_step _ _ _ valid263 (by decide +kernel)

theorem valid805 : plan805.Valid := valid_step _ _ _ valid264 (by decide +kernel)

theorem valid806 : plan806.Valid := valid_step _ _ _ valid265 (by decide +kernel)

theorem valid807 : plan807.Valid := valid_step _ _ _ valid266 (by decide +kernel)

theorem valid808 : plan808.Valid := valid_step _ _ _ valid267 (by decide +kernel)

theorem valid809 : plan809.Valid := valid_step _ _ _ valid268 (by decide +kernel)

theorem valid810 : plan810.Valid := valid_step _ _ _ valid269 (by decide +kernel)

theorem valid811 : plan811.Valid := valid_step _ _ _ valid279 (by decide +kernel)

theorem valid812 : plan812.Valid := valid_step _ _ _ valid289 (by decide +kernel)

theorem valid813 : plan813.Valid := valid_step _ _ _ valid290 (by decide +kernel)

theorem valid814 : plan814.Valid := valid_step _ _ _ valid297 (by decide +kernel)

theorem valid815 : plan815.Valid := valid_step _ _ _ valid267 (by decide +kernel)

theorem valid816 : plan816.Valid := valid_step _ _ _ valid268 (by decide +kernel)

theorem valid817 : plan817.Valid := valid_step _ _ _ valid269 (by decide +kernel)

theorem valid818 : plan818.Valid := valid_step _ _ _ valid297 (by decide +kernel)

theorem valid819 : plan819.Valid := valid_step _ _ _ valid304 (by decide +kernel)

theorem valid820 : plan820.Valid := valid_step _ _ _ valid305 (by decide +kernel)

theorem valid821 : plan821.Valid := valid_step _ _ _ valid306 (by decide +kernel)

theorem valid822 : plan822.Valid := valid_step _ _ _ valid307 (by decide +kernel)

theorem valid823 : plan823.Valid := valid_step _ _ _ valid308 (by decide +kernel)

theorem valid824 : plan824.Valid := valid_step _ _ _ valid309 (by decide +kernel)

theorem valid825 : plan825.Valid := valid_step _ _ _ valid310 (by decide +kernel)

theorem valid826 : plan826.Valid := valid_step _ _ _ valid311 (by decide +kernel)

theorem valid827 : plan827.Valid := valid_step _ _ _ valid312 (by decide +kernel)

theorem valid828 : plan828.Valid := valid_step _ _ _ valid313 (by decide +kernel)

theorem valid829 : plan829.Valid := valid_step _ _ _ valid314 (by decide +kernel)

theorem valid830 : plan830.Valid := valid_step _ _ _ valid315 (by decide +kernel)

theorem valid831 : plan831.Valid := valid_step _ _ _ valid316 (by decide +kernel)

theorem valid832 : plan832.Valid := valid_step _ _ _ valid317 (by decide +kernel)

theorem valid833 : plan833.Valid := valid_step _ _ _ valid318 (by decide +kernel)

theorem valid834 : plan834.Valid := valid_step _ _ _ valid319 (by decide +kernel)

theorem valid835 : plan835.Valid := valid_step _ _ _ valid320 (by decide +kernel)

theorem valid836 : plan836.Valid := valid_step _ _ _ valid321 (by decide +kernel)

theorem valid837 : plan837.Valid := valid_step _ _ _ valid322 (by decide +kernel)

theorem valid838 : plan838.Valid := valid_step _ _ _ valid323 (by decide +kernel)

theorem valid839 : plan839.Valid := valid_step _ _ _ valid324 (by decide +kernel)

theorem valid840 : plan840.Valid := valid_step _ _ _ valid325 (by decide +kernel)

theorem valid841 : plan841.Valid := valid_step _ _ _ valid326 (by decide +kernel)

theorem valid842 : plan842.Valid := valid_step _ _ _ valid327 (by decide +kernel)

theorem valid843 : plan843.Valid := valid_step _ _ _ valid328 (by decide +kernel)

theorem valid844 : plan844.Valid := valid_step _ _ _ valid329 (by decide +kernel)

theorem valid845 : plan845.Valid := valid_step _ _ _ valid330 (by decide +kernel)

theorem valid846 : plan846.Valid := valid_step _ _ _ valid331 (by decide +kernel)

theorem valid847 : plan847.Valid := valid_step _ _ _ valid311 (by decide +kernel)

theorem valid848 : plan848.Valid := valid_step _ _ _ valid312 (by decide +kernel)

theorem valid849 : plan849.Valid := valid_step _ _ _ valid313 (by decide +kernel)

theorem valid850 : plan850.Valid := valid_step _ _ _ valid314 (by decide +kernel)

theorem valid851 : plan851.Valid := valid_step _ _ _ valid315 (by decide +kernel)

theorem valid852 : plan852.Valid := valid_step _ _ _ valid316 (by decide +kernel)

theorem valid853 : plan853.Valid := valid_step _ _ _ valid317 (by decide +kernel)

theorem valid854 : plan854.Valid := valid_step _ _ _ valid318 (by decide +kernel)

theorem valid855 : plan855.Valid := valid_step _ _ _ valid319 (by decide +kernel)

theorem valid856 : plan856.Valid := valid_step _ _ _ valid326 (by decide +kernel)

theorem valid857 : plan857.Valid := valid_step _ _ _ valid327 (by decide +kernel)

theorem valid858 : plan858.Valid := valid_step _ _ _ valid328 (by decide +kernel)

theorem valid859 : plan859.Valid := valid_step _ _ _ valid329 (by decide +kernel)

theorem valid860 : plan860.Valid := valid_step _ _ _ valid330 (by decide +kernel)

theorem valid861 : plan861.Valid := valid_step _ _ _ valid331 (by decide +kernel)

theorem valid862 : plan862.Valid := valid_step _ _ _ valid316 (by decide +kernel)

theorem valid863 : plan863.Valid := valid_step _ _ _ valid317 (by decide +kernel)

theorem valid864 : plan864.Valid := valid_step _ _ _ valid318 (by decide +kernel)
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

theorem valid865 : plan865.Valid := valid_step _ _ _ valid319 (by decide +kernel)

theorem valid866 : plan866.Valid := valid_step _ _ _ valid330 (by decide +kernel)

theorem valid867 : plan867.Valid := valid_step _ _ _ valid331 (by decide +kernel)

theorem valid868 : plan868.Valid := valid_step _ _ _ valid319 (by decide +kernel)

theorem valid869 : plan869.Valid := valid_step _ _ _ valid311 (by decide +kernel)

theorem valid870 : plan870.Valid := valid_step _ _ _ valid312 (by decide +kernel)

theorem valid871 : plan871.Valid := valid_step _ _ _ valid313 (by decide +kernel)

theorem valid872 : plan872.Valid := valid_step _ _ _ valid314 (by decide +kernel)

theorem valid873 : plan873.Valid := valid_step _ _ _ valid315 (by decide +kernel)

theorem valid874 : plan874.Valid := valid_step _ _ _ valid316 (by decide +kernel)

theorem valid875 : plan875.Valid := valid_step _ _ _ valid317 (by decide +kernel)

theorem valid876 : plan876.Valid := valid_step _ _ _ valid318 (by decide +kernel)

theorem valid877 : plan877.Valid := valid_step _ _ _ valid319 (by decide +kernel)

theorem valid878 : plan878.Valid := valid_step _ _ _ valid320 (by decide +kernel)

theorem valid879 : plan879.Valid := valid_step _ _ _ valid321 (by decide +kernel)

theorem valid880 : plan880.Valid := valid_step _ _ _ valid322 (by decide +kernel)

theorem valid881 : plan881.Valid := valid_step _ _ _ valid323 (by decide +kernel)

theorem valid882 : plan882.Valid := valid_step _ _ _ valid324 (by decide +kernel)

theorem valid883 : plan883.Valid := valid_step _ _ _ valid325 (by decide +kernel)

theorem valid884 : plan884.Valid := valid_step _ _ _ valid326 (by decide +kernel)

theorem valid885 : plan885.Valid := valid_step _ _ _ valid327 (by decide +kernel)

theorem valid886 : plan886.Valid := valid_step _ _ _ valid328 (by decide +kernel)

theorem valid887 : plan887.Valid := valid_step _ _ _ valid329 (by decide +kernel)

theorem valid888 : plan888.Valid := valid_step _ _ _ valid330 (by decide +kernel)

theorem valid889 : plan889.Valid := valid_step _ _ _ valid331 (by decide +kernel)

theorem valid890 : plan890.Valid := valid_step _ _ _ valid316 (by decide +kernel)

theorem valid891 : plan891.Valid := valid_step _ _ _ valid317 (by decide +kernel)

theorem valid892 : plan892.Valid := valid_step _ _ _ valid318 (by decide +kernel)

theorem valid893 : plan893.Valid := valid_step _ _ _ valid319 (by decide +kernel)

theorem valid894 : plan894.Valid := valid_step _ _ _ valid326 (by decide +kernel)

theorem valid895 : plan895.Valid := valid_step _ _ _ valid327 (by decide +kernel)

theorem valid896 : plan896.Valid := valid_step _ _ _ valid328 (by decide +kernel)

theorem valid897 : plan897.Valid := valid_step _ _ _ valid329 (by decide +kernel)

theorem valid898 : plan898.Valid := valid_step _ _ _ valid330 (by decide +kernel)

theorem valid899 : plan899.Valid := valid_step _ _ _ valid331 (by decide +kernel)

theorem valid900 : plan900.Valid := valid_step _ _ _ valid319 (by decide +kernel)

theorem valid901 : plan901.Valid := valid_step _ _ _ valid330 (by decide +kernel)

theorem valid902 : plan902.Valid := valid_step _ _ _ valid331 (by decide +kernel)

theorem valid903 : plan903.Valid := valid_step _ _ _ valid332 (by decide +kernel)

theorem valid904 : plan904.Valid := valid_step _ _ _ valid333 (by decide +kernel)

theorem valid905 : plan905.Valid := valid_step _ _ _ valid334 (by decide +kernel)

theorem valid906 : plan906.Valid := valid_step _ _ _ valid335 (by decide +kernel)

theorem valid907 : plan907.Valid := valid_step _ _ _ valid333 (by decide +kernel)

theorem valid908 : plan908.Valid := valid_step _ _ _ valid334 (by decide +kernel)

theorem valid909 : plan909.Valid := valid_step _ _ _ valid335 (by decide +kernel)

theorem valid910 : plan910.Valid := valid_step _ _ _ valid335 (by decide +kernel)

theorem valid911 : plan911.Valid := valid_step _ _ _ valid336 (by decide +kernel)

theorem valid912 : plan912.Valid := valid_step _ _ _ valid337 (by decide +kernel)

theorem valid913 : plan913.Valid := valid_step _ _ _ valid338 (by decide +kernel)

theorem valid914 : plan914.Valid := valid_step _ _ _ valid341 (by decide +kernel)

theorem valid915 : plan915.Valid := valid_step _ _ _ valid342 (by decide +kernel)

theorem valid916 : plan916.Valid := valid_step _ _ _ valid343 (by decide +kernel)

theorem valid917 : plan917.Valid := valid_step _ _ _ valid344 (by decide +kernel)

theorem valid918 : plan918.Valid := valid_step _ _ _ valid345 (by decide +kernel)

theorem valid919 : plan919.Valid := valid_step _ _ _ valid347 (by decide +kernel)

theorem valid920 : plan920.Valid := valid_step _ _ _ valid348 (by decide +kernel)

theorem valid921 : plan921.Valid := valid_step _ _ _ valid349 (by decide +kernel)

theorem valid922 : plan922.Valid := valid_step _ _ _ valid350 (by decide +kernel)

theorem valid923 : plan923.Valid := valid_step _ _ _ valid351 (by decide +kernel)

theorem valid924 : plan924.Valid := valid_step _ _ _ valid352 (by decide +kernel)

theorem valid925 : plan925.Valid := valid_step _ _ _ valid353 (by decide +kernel)





theorem valid928 : plan928.Valid := valid_step _ _ _ valid341 (by decide +kernel)

theorem valid929 : plan929.Valid := valid_step _ _ _ valid342 (by decide +kernel)

theorem valid930 : plan930.Valid := valid_step _ _ _ valid343 (by decide +kernel)

theorem valid931 : plan931.Valid := valid_step _ _ _ valid344 (by decide +kernel)

theorem valid932 : plan932.Valid := valid_step _ _ _ valid345 (by decide +kernel)



theorem valid934 : plan934.Valid := valid_step _ _ _ valid347 (by decide +kernel)

theorem valid935 : plan935.Valid := valid_step _ _ _ valid348 (by decide +kernel)

theorem valid936 : plan936.Valid := valid_step _ _ _ valid349 (by decide +kernel)

theorem valid937 : plan937.Valid := valid_step _ _ _ valid351 (by decide +kernel)

theorem valid938 : plan938.Valid := valid_step _ _ _ valid353 (by decide +kernel)



theorem valid940 : plan940.Valid := valid_step _ _ _ valid347 (by decide +kernel)

theorem valid941 : plan941.Valid := valid_step _ _ _ valid348 (by decide +kernel)

theorem valid942 : plan942.Valid := valid_step _ _ _ valid349 (by decide +kernel)



theorem valid944 : plan944.Valid := valid_step _ _ _ valid340 (by decide +kernel)

theorem valid945 : plan945.Valid := valid_step _ _ _ valid346 (by decide +kernel)

theorem valid946 : plan946.Valid := valid_step _ _ _ valid346 (by decide +kernel)



theorem valid948 : plan948.Valid := valid_step _ _ _ valid340 (by decide +kernel)

theorem valid949 : plan949.Valid := valid_step _ _ _ valid346 (by decide +kernel)

theorem valid950 : plan950.Valid := valid_step _ _ _ valid346 (by decide +kernel)

theorem valid951 : plan951.Valid := valid_step _ _ _ valid366 (by decide +kernel)

theorem valid952 : plan952.Valid := valid_step _ _ _ valid367 (by decide +kernel)

theorem valid953 : plan953.Valid := valid_step _ _ _ valid368 (by decide +kernel)

theorem valid954 : plan954.Valid := valid_step _ _ _ valid370 (by decide +kernel)

theorem valid955 : plan955.Valid := valid_step _ _ _ valid371 (by decide +kernel)

theorem valid956 : plan956.Valid := valid_step _ _ _ valid372 (by decide +kernel)

theorem valid957 : plan957.Valid := valid_step _ _ _ valid373 (by decide +kernel)

theorem valid958 : plan958.Valid := valid_step _ _ _ valid374 (by decide +kernel)

theorem valid959 : plan959.Valid := valid_step _ _ _ valid375 (by decide +kernel)

theorem valid960 : plan960.Valid := valid_step _ _ _ valid376 (by decide +kernel)
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



























































































































theorem valid1694 : plan1694.Valid := valid_step _ _ _ valid905 (by decide +kernel)

theorem valid1695 : plan1695.Valid := valid_step _ _ _ valid906 (by decide +kernel)

theorem valid1696 : plan1696.Valid := valid_step _ _ _ valid907 (by decide +kernel)

theorem valid1697 : plan1697.Valid := valid_step _ _ _ valid908 (by decide +kernel)

theorem valid1698 : plan1698.Valid := valid_step _ _ _ valid909 (by decide +kernel)

theorem valid1699 : plan1699.Valid := valid_step _ _ _ valid910 (by decide +kernel)

theorem valid1700 : plan1700.Valid := valid_step _ _ _ valid903 (by decide +kernel)

theorem valid1701 : plan1701.Valid := valid_step _ _ _ valid904 (by decide +kernel)

theorem valid1702 : plan1702.Valid := valid_step _ _ _ valid905 (by decide +kernel)

theorem valid1703 : plan1703.Valid := valid_step _ _ _ valid906 (by decide +kernel)

theorem valid1704 : plan1704.Valid := valid_step _ _ _ valid907 (by decide +kernel)

theorem valid1705 : plan1705.Valid := valid_step _ _ _ valid908 (by decide +kernel)

theorem valid1706 : plan1706.Valid := valid_step _ _ _ valid909 (by decide +kernel)













theorem valid1713 : plan1713.Valid := valid_step _ _ _ valid915 (by decide +kernel)

theorem valid1714 : plan1714.Valid := valid_step _ _ _ valid916 (by decide +kernel)

theorem valid1715 : plan1715.Valid := valid_step _ _ _ valid918 (by decide +kernel)

theorem valid1716 : plan1716.Valid := valid_step _ _ _ valid919 (by decide +kernel)

theorem valid1717 : plan1717.Valid := valid_step _ _ _ valid920 (by decide +kernel)

theorem valid1718 : plan1718.Valid := valid_step _ _ _ valid921 (by decide +kernel)

theorem valid1719 : plan1719.Valid := valid_step _ _ _ valid923 (by decide +kernel)

theorem valid1720 : plan1720.Valid := valid_step _ _ _ valid925 (by decide +kernel)

theorem valid1721 : plan1721.Valid := valid_step _ _ _ valid928 (by decide +kernel)

theorem valid1722 : plan1722.Valid := valid_step _ _ _ valid929 (by decide +kernel)

theorem valid1723 : plan1723.Valid := valid_step _ _ _ valid930 (by decide +kernel)

theorem valid1724 : plan1724.Valid := valid_step _ _ _ valid931 (by decide +kernel)

theorem valid1725 : plan1725.Valid := valid_step _ _ _ valid932 (by decide +kernel)

theorem valid1726 : plan1726.Valid := valid_step _ _ _ valid934 (by decide +kernel)

theorem valid1727 : plan1727.Valid := valid_step _ _ _ valid935 (by decide +kernel)

theorem valid1728 : plan1728.Valid := valid_step _ _ _ valid936 (by decide +kernel)
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

theorem valid961 : plan961.Valid := valid_step _ _ _ valid377 (by decide +kernel)

theorem valid962 : plan962.Valid := valid_step _ _ _ valid378 (by decide +kernel)

theorem valid963 : plan963.Valid := valid_step _ _ _ valid380 (by decide +kernel)

theorem valid964 : plan964.Valid := valid_step _ _ _ valid381 (by decide +kernel)

theorem valid965 : plan965.Valid := valid_step _ _ _ valid382 (by decide +kernel)

theorem valid966 : plan966.Valid := valid_step _ _ _ valid384 (by decide +kernel)

theorem valid967 : plan967.Valid := valid_step _ _ _ valid385 (by decide +kernel)

theorem valid968 : plan968.Valid := valid_step _ _ _ valid386 (by decide +kernel)

theorem valid969 : plan969.Valid := valid_step _ _ _ valid387 (by decide +kernel)

theorem valid970 : plan970.Valid := valid_step _ _ _ valid388 (by decide +kernel)

theorem valid971 : plan971.Valid := valid_step _ _ _ valid389 (by decide +kernel)



















theorem valid981 : plan981.Valid := valid_step _ _ _ valid370 (by decide +kernel)

theorem valid982 : plan982.Valid := valid_step _ _ _ valid371 (by decide +kernel)

theorem valid983 : plan983.Valid := valid_step _ _ _ valid372 (by decide +kernel)

theorem valid984 : plan984.Valid := valid_step _ _ _ valid373 (by decide +kernel)

theorem valid985 : plan985.Valid := valid_step _ _ _ valid374 (by decide +kernel)

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







theorem valid1009 : plan1009.Valid := valid_step _ _ _ valid357 (by decide +kernel)

theorem valid1010 : plan1010.Valid := valid_step _ _ _ valid358 (by decide +kernel)



theorem valid1012 : plan1012.Valid := valid_step _ _ _ valid360 (by decide +kernel)



theorem valid1014 : plan1014.Valid := valid_step _ _ _ valid362 (by decide +kernel)

theorem valid1015 : plan1015.Valid := valid_step _ _ _ valid363 (by decide +kernel)

theorem valid1016 : plan1016.Valid := valid_step _ _ _ valid364 (by decide +kernel)



theorem valid1018 : plan1018.Valid := valid_step _ _ _ valid369 (by decide +kernel)



theorem valid1020 : plan1020.Valid := valid_step _ _ _ valid383 (by decide +kernel)



theorem valid1022 : plan1022.Valid := valid_step _ _ _ valid362 (by decide +kernel)

theorem valid1023 : plan1023.Valid := valid_step _ _ _ valid363 (by decide +kernel)

theorem valid1024 : plan1024.Valid := valid_step _ _ _ valid364 (by decide +kernel)

theorem valid1025 : plan1025.Valid := valid_step _ _ _ valid369 (by decide +kernel)

theorem valid1026 : plan1026.Valid := valid_step _ _ _ valid383 (by decide +kernel)







theorem valid1030 : plan1030.Valid := valid_step _ _ _ valid357 (by decide +kernel)

theorem valid1031 : plan1031.Valid := valid_step _ _ _ valid358 (by decide +kernel)



theorem valid1033 : plan1033.Valid := valid_step _ _ _ valid360 (by decide +kernel)



theorem valid1035 : plan1035.Valid := valid_step _ _ _ valid362 (by decide +kernel)

theorem valid1036 : plan1036.Valid := valid_step _ _ _ valid363 (by decide +kernel)

theorem valid1037 : plan1037.Valid := valid_step _ _ _ valid364 (by decide +kernel)

theorem valid1038 : plan1038.Valid := valid_step _ _ _ valid369 (by decide +kernel)



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

theorem valid1729 : plan1729.Valid := valid_step _ _ _ valid937 (by decide +kernel)

theorem valid1730 : plan1730.Valid := valid_step _ _ _ valid938 (by decide +kernel)

theorem valid1731 : plan1731.Valid := valid_step _ _ _ valid940 (by decide +kernel)

theorem valid1732 : plan1732.Valid := valid_step _ _ _ valid941 (by decide +kernel)

theorem valid1733 : plan1733.Valid := valid_step _ _ _ valid942 (by decide +kernel)

theorem valid1734 : plan1734.Valid := valid_step _ _ _ valid944 (by decide +kernel)

theorem valid1735 : plan1735.Valid := valid_step _ _ _ valid945 (by decide +kernel)

theorem valid1736 : plan1736.Valid := valid_step _ _ _ valid946 (by decide +kernel)

theorem valid1737 : plan1737.Valid := valid_step _ _ _ valid948 (by decide +kernel)

theorem valid1738 : plan1738.Valid := valid_step _ _ _ valid949 (by decide +kernel)

theorem valid1739 : plan1739.Valid := valid_step _ _ _ valid950 (by decide +kernel)

theorem valid1740 : plan1740.Valid := valid_step _ _ _ valid911 (by decide +kernel)

theorem valid1741 : plan1741.Valid := valid_step _ _ _ valid912 (by decide +kernel)

theorem valid1742 : plan1742.Valid := valid_step _ _ _ valid913 (by decide +kernel)

theorem valid1743 : plan1743.Valid := valid_step _ _ _ valid914 (by decide +kernel)

theorem valid1744 : plan1744.Valid := valid_step _ _ _ valid915 (by decide +kernel)

theorem valid1745 : plan1745.Valid := valid_step _ _ _ valid916 (by decide +kernel)

theorem valid1746 : plan1746.Valid := valid_step _ _ _ valid917 (by decide +kernel)

theorem valid1747 : plan1747.Valid := valid_step _ _ _ valid918 (by decide +kernel)

theorem valid1748 : plan1748.Valid := valid_step _ _ _ valid919 (by decide +kernel)

theorem valid1749 : plan1749.Valid := valid_step _ _ _ valid920 (by decide +kernel)

theorem valid1750 : plan1750.Valid := valid_step _ _ _ valid921 (by decide +kernel)

theorem valid1751 : plan1751.Valid := valid_step _ _ _ valid922 (by decide +kernel)

theorem valid1752 : plan1752.Valid := valid_step _ _ _ valid923 (by decide +kernel)

theorem valid1753 : plan1753.Valid := valid_step _ _ _ valid924 (by decide +kernel)

theorem valid1754 : plan1754.Valid := valid_step _ _ _ valid925 (by decide +kernel)

theorem valid1755 : plan1755.Valid := valid_step _ _ _ valid928 (by decide +kernel)

theorem valid1756 : plan1756.Valid := valid_step _ _ _ valid929 (by decide +kernel)

theorem valid1757 : plan1757.Valid := valid_step _ _ _ valid930 (by decide +kernel)

theorem valid1758 : plan1758.Valid := valid_step _ _ _ valid931 (by decide +kernel)

theorem valid1759 : plan1759.Valid := valid_step _ _ _ valid932 (by decide +kernel)

theorem valid1760 : plan1760.Valid := valid_step _ _ _ valid934 (by decide +kernel)

theorem valid1761 : plan1761.Valid := valid_step _ _ _ valid935 (by decide +kernel)

theorem valid1762 : plan1762.Valid := valid_step _ _ _ valid936 (by decide +kernel)

theorem valid1763 : plan1763.Valid := valid_step _ _ _ valid937 (by decide +kernel)

theorem valid1764 : plan1764.Valid := valid_step _ _ _ valid938 (by decide +kernel)















































































theorem valid1804 : plan1804.Valid := valid_step _ _ _ valid955 (by decide +kernel)

theorem valid1805 : plan1805.Valid := valid_step _ _ _ valid956 (by decide +kernel)

theorem valid1806 : plan1806.Valid := valid_step _ _ _ valid958 (by decide +kernel)

theorem valid1807 : plan1807.Valid := valid_step _ _ _ valid959 (by decide +kernel)

theorem valid1808 : plan1808.Valid := valid_step _ _ _ valid960 (by decide +kernel)

theorem valid1809 : plan1809.Valid := valid_step _ _ _ valid961 (by decide +kernel)

theorem valid1810 : plan1810.Valid := valid_step _ _ _ valid962 (by decide +kernel)

theorem valid1811 : plan1811.Valid := valid_step _ _ _ valid966 (by decide +kernel)

theorem valid1812 : plan1812.Valid := valid_step _ _ _ valid967 (by decide +kernel)

theorem valid1813 : plan1813.Valid := valid_step _ _ _ valid969 (by decide +kernel)

theorem valid1814 : plan1814.Valid := valid_step _ _ _ valid970 (by decide +kernel)

theorem valid1815 : plan1815.Valid := valid_step _ _ _ valid971 (by decide +kernel)

theorem valid1816 : plan1816.Valid := valid_step _ _ _ valid981 (by decide +kernel)

theorem valid1817 : plan1817.Valid := valid_step _ _ _ valid982 (by decide +kernel)

theorem valid1818 : plan1818.Valid := valid_step _ _ _ valid983 (by decide +kernel)

theorem valid1819 : plan1819.Valid := valid_step _ _ _ valid984 (by decide +kernel)

theorem valid1820 : plan1820.Valid := valid_step _ _ _ valid985 (by decide +kernel)

theorem valid1821 : plan1821.Valid := valid_step _ _ _ valid986 (by decide +kernel)

theorem valid1822 : plan1822.Valid := valid_step _ _ _ valid987 (by decide +kernel)

theorem valid1823 : plan1823.Valid := valid_step _ _ _ valid988 (by decide +kernel)

theorem valid1824 : plan1824.Valid := valid_step _ _ _ valid989 (by decide +kernel)
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

theorem valid1825 : plan1825.Valid := valid_step _ _ _ valid991 (by decide +kernel)

theorem valid1826 : plan1826.Valid := valid_step _ _ _ valid992 (by decide +kernel)

theorem valid1827 : plan1827.Valid := valid_step _ _ _ valid993 (by decide +kernel)

theorem valid1828 : plan1828.Valid := valid_step _ _ _ valid994 (by decide +kernel)

theorem valid1829 : plan1829.Valid := valid_step _ _ _ valid995 (by decide +kernel)

theorem valid1830 : plan1830.Valid := valid_step _ _ _ valid996 (by decide +kernel)

theorem valid1831 : plan1831.Valid := valid_step _ _ _ valid1000 (by decide +kernel)

theorem valid1832 : plan1832.Valid := valid_step _ _ _ valid1001 (by decide +kernel)

theorem valid1833 : plan1833.Valid := valid_step _ _ _ valid1002 (by decide +kernel)

theorem valid1834 : plan1834.Valid := valid_step _ _ _ valid1003 (by decide +kernel)

theorem valid1835 : plan1835.Valid := valid_step _ _ _ valid1004 (by decide +kernel)

theorem valid1836 : plan1836.Valid := valid_step _ _ _ valid1005 (by decide +kernel)

theorem valid1837 : plan1837.Valid := valid_step _ _ _ valid1009 (by decide +kernel)

theorem valid1838 : plan1838.Valid := valid_step _ _ _ valid1010 (by decide +kernel)

theorem valid1839 : plan1839.Valid := valid_step _ _ _ valid1012 (by decide +kernel)

theorem valid1840 : plan1840.Valid := valid_step _ _ _ valid1014 (by decide +kernel)

theorem valid1841 : plan1841.Valid := valid_step _ _ _ valid1015 (by decide +kernel)

theorem valid1842 : plan1842.Valid := valid_step _ _ _ valid1016 (by decide +kernel)

theorem valid1843 : plan1843.Valid := valid_step _ _ _ valid1018 (by decide +kernel)

theorem valid1844 : plan1844.Valid := valid_step _ _ _ valid1020 (by decide +kernel)

theorem valid1845 : plan1845.Valid := valid_step _ _ _ valid1022 (by decide +kernel)

theorem valid1846 : plan1846.Valid := valid_step _ _ _ valid1023 (by decide +kernel)

theorem valid1847 : plan1847.Valid := valid_step _ _ _ valid1024 (by decide +kernel)

theorem valid1848 : plan1848.Valid := valid_step _ _ _ valid1025 (by decide +kernel)

theorem valid1849 : plan1849.Valid := valid_step _ _ _ valid1026 (by decide +kernel)

theorem valid1850 : plan1850.Valid := valid_step _ _ _ valid1030 (by decide +kernel)

theorem valid1851 : plan1851.Valid := valid_step _ _ _ valid1031 (by decide +kernel)

theorem valid1852 : plan1852.Valid := valid_step _ _ _ valid1033 (by decide +kernel)

theorem valid1853 : plan1853.Valid := valid_step _ _ _ valid1035 (by decide +kernel)

theorem valid1854 : plan1854.Valid := valid_step _ _ _ valid1036 (by decide +kernel)

theorem valid1855 : plan1855.Valid := valid_step _ _ _ valid1037 (by decide +kernel)

theorem valid1856 : plan1856.Valid := valid_step _ _ _ valid1038 (by decide +kernel)

theorem valid1857 : plan1857.Valid := valid_step _ _ _ valid1040 (by decide +kernel)

theorem valid1858 : plan1858.Valid := valid_step _ _ _ valid1042 (by decide +kernel)

theorem valid1859 : plan1859.Valid := valid_step _ _ _ valid1043 (by decide +kernel)

theorem valid1860 : plan1860.Valid := valid_step _ _ _ valid1044 (by decide +kernel)

theorem valid1861 : plan1861.Valid := valid_step _ _ _ valid1045 (by decide +kernel)

theorem valid1862 : plan1862.Valid := valid_step _ _ _ valid951 (by decide +kernel)

theorem valid1863 : plan1863.Valid := valid_step _ _ _ valid952 (by decide +kernel)

theorem valid1864 : plan1864.Valid := valid_step _ _ _ valid953 (by decide +kernel)

theorem valid1865 : plan1865.Valid := valid_step _ _ _ valid954 (by decide +kernel)

theorem valid1866 : plan1866.Valid := valid_step _ _ _ valid955 (by decide +kernel)

theorem valid1867 : plan1867.Valid := valid_step _ _ _ valid956 (by decide +kernel)

theorem valid1868 : plan1868.Valid := valid_step _ _ _ valid957 (by decide +kernel)

theorem valid1869 : plan1869.Valid := valid_step _ _ _ valid958 (by decide +kernel)

theorem valid1870 : plan1870.Valid := valid_step _ _ _ valid959 (by decide +kernel)

theorem valid1871 : plan1871.Valid := valid_step _ _ _ valid960 (by decide +kernel)

theorem valid1872 : plan1872.Valid := valid_step _ _ _ valid961 (by decide +kernel)

theorem valid1873 : plan1873.Valid := valid_step _ _ _ valid962 (by decide +kernel)

theorem valid1874 : plan1874.Valid := valid_step _ _ _ valid963 (by decide +kernel)

theorem valid1875 : plan1875.Valid := valid_step _ _ _ valid964 (by decide +kernel)

theorem valid1876 : plan1876.Valid := valid_step _ _ _ valid965 (by decide +kernel)

theorem valid1877 : plan1877.Valid := valid_step _ _ _ valid966 (by decide +kernel)

theorem valid1878 : plan1878.Valid := valid_step _ _ _ valid967 (by decide +kernel)

theorem valid1879 : plan1879.Valid := valid_step _ _ _ valid968 (by decide +kernel)

theorem valid1880 : plan1880.Valid := valid_step _ _ _ valid969 (by decide +kernel)

theorem valid1881 : plan1881.Valid := valid_step _ _ _ valid970 (by decide +kernel)

theorem valid1882 : plan1882.Valid := valid_step _ _ _ valid971 (by decide +kernel)

theorem valid1883 : plan1883.Valid := valid_step _ _ _ valid981 (by decide +kernel)

theorem valid1884 : plan1884.Valid := valid_step _ _ _ valid982 (by decide +kernel)

theorem valid1885 : plan1885.Valid := valid_step _ _ _ valid983 (by decide +kernel)

theorem valid1886 : plan1886.Valid := valid_step _ _ _ valid984 (by decide +kernel)

theorem valid1887 : plan1887.Valid := valid_step _ _ _ valid985 (by decide +kernel)

theorem valid1888 : plan1888.Valid := valid_step _ _ _ valid986 (by decide +kernel)

theorem valid1889 : plan1889.Valid := valid_step _ _ _ valid987 (by decide +kernel)

theorem valid1890 : plan1890.Valid := valid_step _ _ _ valid988 (by decide +kernel)

theorem valid1891 : plan1891.Valid := valid_step _ _ _ valid989 (by decide +kernel)

theorem valid1892 : plan1892.Valid := valid_step _ _ _ valid991 (by decide +kernel)
























































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

















































theorem valid1081 : plan1081.Valid := valid_step _ _ _ valid404 (by decide +kernel)

theorem valid1082 : plan1082.Valid := valid_step _ _ _ valid405 (by decide +kernel)



theorem valid1084 : plan1084.Valid := valid_step _ _ _ valid407 (by decide +kernel)

theorem valid1085 : plan1085.Valid := valid_step _ _ _ valid408 (by decide +kernel)

theorem valid1086 : plan1086.Valid := valid_step _ _ _ valid409 (by decide +kernel)

theorem valid1087 : plan1087.Valid := valid_step _ _ _ valid410 (by decide +kernel)

theorem valid1088 : plan1088.Valid := valid_step _ _ _ valid411 (by decide +kernel)











theorem valid1094 : plan1094.Valid := valid_step _ _ _ valid417 (by decide +kernel)

theorem valid1095 : plan1095.Valid := valid_step _ _ _ valid418 (by decide +kernel)



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





















theorem valid1137 : plan1137.Valid := valid_step _ _ _ valid404 (by decide +kernel)

theorem valid1138 : plan1138.Valid := valid_step _ _ _ valid405 (by decide +kernel)



theorem valid1140 : plan1140.Valid := valid_step _ _ _ valid407 (by decide +kernel)

theorem valid1141 : plan1141.Valid := valid_step _ _ _ valid408 (by decide +kernel)

theorem valid1142 : plan1142.Valid := valid_step _ _ _ valid409 (by decide +kernel)

theorem valid1143 : plan1143.Valid := valid_step _ _ _ valid410 (by decide +kernel)

theorem valid1144 : plan1144.Valid := valid_step _ _ _ valid411 (by decide +kernel)











theorem valid1150 : plan1150.Valid := valid_step _ _ _ valid417 (by decide +kernel)

theorem valid1151 : plan1151.Valid := valid_step _ _ _ valid418 (by decide +kernel)


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







theorem valid2020 : plan2020.Valid := valid_step _ _ _ valid1081 (by decide +kernel)

theorem valid2021 : plan2021.Valid := valid_step _ _ _ valid1082 (by decide +kernel)

theorem valid2022 : plan2022.Valid := valid_step _ _ _ valid1084 (by decide +kernel)

theorem valid2023 : plan2023.Valid := valid_step _ _ _ valid1085 (by decide +kernel)

theorem valid2024 : plan2024.Valid := valid_step _ _ _ valid1086 (by decide +kernel)

theorem valid2025 : plan2025.Valid := valid_step _ _ _ valid1087 (by decide +kernel)

theorem valid2026 : plan2026.Valid := valid_step _ _ _ valid1088 (by decide +kernel)

theorem valid2027 : plan2027.Valid := valid_step _ _ _ valid1094 (by decide +kernel)

theorem valid2028 : plan2028.Valid := valid_step _ _ _ valid1095 (by decide +kernel)

theorem valid2029 : plan2029.Valid := valid_step _ _ _ valid1097 (by decide +kernel)

theorem valid2030 : plan2030.Valid := valid_step _ _ _ valid1098 (by decide +kernel)

theorem valid2031 : plan2031.Valid := valid_step _ _ _ valid1099 (by decide +kernel)

theorem valid2032 : plan2032.Valid := valid_step _ _ _ valid1104 (by decide +kernel)

theorem valid2033 : plan2033.Valid := valid_step _ _ _ valid1105 (by decide +kernel)

theorem valid2034 : plan2034.Valid := valid_step _ _ _ valid1106 (by decide +kernel)

theorem valid2035 : plan2035.Valid := valid_step _ _ _ valid1107 (by decide +kernel)

theorem valid2036 : plan2036.Valid := valid_step _ _ _ valid1108 (by decide +kernel)

theorem valid2037 : plan2037.Valid := valid_step _ _ _ valid1109 (by decide +kernel)

theorem valid2038 : plan2038.Valid := valid_step _ _ _ valid1110 (by decide +kernel)

theorem valid2039 : plan2039.Valid := valid_step _ _ _ valid1111 (by decide +kernel)

theorem valid2040 : plan2040.Valid := valid_step _ _ _ valid1112 (by decide +kernel)

theorem valid2041 : plan2041.Valid := valid_step _ _ _ valid1114 (by decide +kernel)

theorem valid2042 : plan2042.Valid := valid_step _ _ _ valid1115 (by decide +kernel)

theorem valid2043 : plan2043.Valid := valid_step _ _ _ valid1116 (by decide +kernel)

theorem valid2044 : plan2044.Valid := valid_step _ _ _ valid1117 (by decide +kernel)

theorem valid2045 : plan2045.Valid := valid_step _ _ _ valid1118 (by decide +kernel)

theorem valid2046 : plan2046.Valid := valid_step _ _ _ valid1119 (by decide +kernel)

theorem valid2047 : plan2047.Valid := valid_step _ _ _ valid1120 (by decide +kernel)

theorem valid2048 : plan2048.Valid := valid_step _ _ _ valid1121 (by decide +kernel)

theorem valid2049 : plan2049.Valid := valid_step _ _ _ valid1122 (by decide +kernel)

theorem valid2050 : plan2050.Valid := valid_step _ _ _ valid1123 (by decide +kernel)

theorem valid2051 : plan2051.Valid := valid_step _ _ _ valid1124 (by decide +kernel)

theorem valid2052 : plan2052.Valid := valid_step _ _ _ valid1125 (by decide +kernel)

theorem valid2053 : plan2053.Valid := valid_step _ _ _ valid1126 (by decide +kernel)

theorem valid2054 : plan2054.Valid := valid_step _ _ _ valid1137 (by decide +kernel)

theorem valid2055 : plan2055.Valid := valid_step _ _ _ valid1138 (by decide +kernel)

theorem valid2056 : plan2056.Valid := valid_step _ _ _ valid1140 (by decide +kernel)

theorem valid2057 : plan2057.Valid := valid_step _ _ _ valid1141 (by decide +kernel)

theorem valid2058 : plan2058.Valid := valid_step _ _ _ valid1142 (by decide +kernel)

theorem valid2059 : plan2059.Valid := valid_step _ _ _ valid1143 (by decide +kernel)

theorem valid2060 : plan2060.Valid := valid_step _ _ _ valid1144 (by decide +kernel)

theorem valid2061 : plan2061.Valid := valid_step _ _ _ valid1150 (by decide +kernel)

theorem valid2062 : plan2062.Valid := valid_step _ _ _ valid1151 (by decide +kernel)

theorem valid2063 : plan2063.Valid := valid_step _ _ _ valid1153 (by decide +kernel)

theorem valid2064 : plan2064.Valid := valid_step _ _ _ valid1154 (by decide +kernel)

theorem valid2065 : plan2065.Valid := valid_step _ _ _ valid1155 (by decide +kernel)

theorem valid2066 : plan2066.Valid := valid_step _ _ _ valid1159 (by decide +kernel)

theorem valid2067 : plan2067.Valid := valid_step _ _ _ valid1160 (by decide +kernel)

theorem valid2068 : plan2068.Valid := valid_step _ _ _ valid1161 (by decide +kernel)

theorem valid2069 : plan2069.Valid := valid_step _ _ _ valid1162 (by decide +kernel)

theorem valid2070 : plan2070.Valid := valid_step _ _ _ valid1164 (by decide +kernel)

theorem valid2071 : plan2071.Valid := valid_step _ _ _ valid1165 (by decide +kernel)

theorem valid2072 : plan2072.Valid := valid_step _ _ _ valid1166 (by decide +kernel)

theorem valid2073 : plan2073.Valid := valid_step _ _ _ valid1167 (by decide +kernel)

theorem valid2074 : plan2074.Valid := valid_step _ _ _ valid1168 (by decide +kernel)

theorem valid2075 : plan2075.Valid := valid_step _ _ _ valid1169 (by decide +kernel)

theorem valid2076 : plan2076.Valid := valid_step _ _ _ valid1170 (by decide +kernel)

theorem valid2077 : plan2077.Valid := valid_step _ _ _ valid1171 (by decide +kernel)

theorem valid2078 : plan2078.Valid := valid_step _ _ _ valid1172 (by decide +kernel)




































































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
theorem t0_0choices : plan0.choices=[].map (options 0 0) := by rfl


theorem t0_0part0 : t0_0jobs0.all (Job.check tree)=true := by decide +kernel

theorem t0_0frontier : t0_0root.frontier 0=t0_0jobs := by rfl
theorem t0_0all : t0_0jobs.all (Job.check tree)=true := by
  simp only [t0_0jobs,List.all_append,List.all_nil,t0_0part0,Bool.and_self]
theorem t0_0checked : Checked tree [] := by
  refine ⟨plan0,valid0,t0_0choices,?_⟩
  exact check_of_frontier tree 0 t0_0root t0_0jobs t0_0frontier t0_0all
theorem t1_0choices : plan1.choices=[0].map (options 1 0) := by rfl


theorem t1_0part0 : t1_0jobs0.all (Job.check tree)=true := by decide +kernel

theorem t1_0frontier : t1_0root.frontier 0=t1_0jobs := by rfl
theorem t1_0all : t1_0jobs.all (Job.check tree)=true := by
  simp only [t1_0jobs,List.all_append,List.all_nil,t1_0part0,Bool.and_self]
theorem t1_0checked : Checked tree [0] := by
  refine ⟨plan1,valid1,t1_0choices,?_⟩
  exact check_of_frontier tree 0 t1_0root t1_0jobs t1_0frontier t1_0all
theorem t1_1choices : plan2.choices=[1].map (options 1 0) := by rfl


theorem t1_1part0 : t1_1jobs0.all (Job.check tree)=true := by decide +kernel

theorem t1_1frontier : t1_1root.frontier 0=t1_1jobs := by rfl
theorem t1_1all : t1_1jobs.all (Job.check tree)=true := by
  simp only [t1_1jobs,List.all_append,List.all_nil,t1_1part0,Bool.and_self]
theorem t1_1checked : Checked tree [1] := by
  refine ⟨plan2,valid2,t1_1choices,?_⟩
  exact check_of_frontier tree 0 t1_1root t1_1jobs t1_1frontier t1_1all
theorem t1_2choices : plan3.choices=[2].map (options 1 0) := by rfl


theorem t1_2part0 : t1_2jobs0.all (Job.check tree)=true := by decide +kernel

theorem t1_2frontier : t1_2root.frontier 0=t1_2jobs := by rfl
theorem t1_2all : t1_2jobs.all (Job.check tree)=true := by
  simp only [t1_2jobs,List.all_append,List.all_nil,t1_2part0,Bool.and_self]
theorem t1_2checked : Checked tree [2] := by
  refine ⟨plan3,valid3,t1_2choices,?_⟩
  exact check_of_frontier tree 0 t1_2root t1_2jobs t1_2frontier t1_2all
theorem t1_3choices : plan4.choices=[3].map (options 1 0) := by rfl


theorem t1_3part0 : t1_3jobs0.all (Job.check tree)=true := by decide +kernel

theorem t1_3frontier : t1_3root.frontier 0=t1_3jobs := by rfl
theorem t1_3all : t1_3jobs.all (Job.check tree)=true := by
  simp only [t1_3jobs,List.all_append,List.all_nil,t1_3part0,Bool.and_self]
theorem t1_3checked : Checked tree [3] := by
  refine ⟨plan4,valid4,t1_3choices,?_⟩
  exact check_of_frontier tree 0 t1_3root t1_3jobs t1_3frontier t1_3all
theorem t1_4choices : plan5.choices=[4].map (options 1 1) := by rfl


theorem t1_4part0 : t1_4jobs0.all (Job.check tree)=true := by decide +kernel

theorem t1_4frontier : t1_4root.frontier 0=t1_4jobs := by rfl
theorem t1_4all : t1_4jobs.all (Job.check tree)=true := by
  simp only [t1_4jobs,List.all_append,List.all_nil,t1_4part0,Bool.and_self]
theorem t1_4checked : Checked tree [4] := by
  refine ⟨plan5,valid5,t1_4choices,?_⟩
  exact check_of_frontier tree 0 t1_4root t1_4jobs t1_4frontier t1_4all
theorem t1_5choices : plan6.choices=[5].map (options 1 1) := by rfl


theorem t1_5part0 : t1_5jobs0.all (Job.check tree)=true := by decide +kernel

theorem t1_5frontier : t1_5root.frontier 0=t1_5jobs := by rfl
theorem t1_5all : t1_5jobs.all (Job.check tree)=true := by
  simp only [t1_5jobs,List.all_append,List.all_nil,t1_5part0,Bool.and_self]
theorem t1_5checked : Checked tree [5] := by
  refine ⟨plan6,valid6,t1_5choices,?_⟩
  exact check_of_frontier tree 0 t1_5root t1_5jobs t1_5frontier t1_5all
theorem t1_6choices : plan7.choices=[6].map (options 1 1) := by rfl


theorem t1_6part0 : t1_6jobs0.all (Job.check tree)=true := by decide +kernel

theorem t1_6frontier : t1_6root.frontier 0=t1_6jobs := by rfl
theorem t1_6all : t1_6jobs.all (Job.check tree)=true := by
  simp only [t1_6jobs,List.all_append,List.all_nil,t1_6part0,Bool.and_self]
theorem t1_6checked : Checked tree [6] := by
  refine ⟨plan7,valid7,t1_6choices,?_⟩
  exact check_of_frontier tree 0 t1_6root t1_6jobs t1_6frontier t1_6all
theorem t1_7choices : plan8.choices=[7].map (options 1 1) := by rfl


theorem t1_7part0 : t1_7jobs0.all (Job.check tree)=true := by decide +kernel

theorem t1_7frontier : t1_7root.frontier 0=t1_7jobs := by rfl
theorem t1_7all : t1_7jobs.all (Job.check tree)=true := by
  simp only [t1_7jobs,List.all_append,List.all_nil,t1_7part0,Bool.and_self]
theorem t1_7checked : Checked tree [7] := by
  refine ⟨plan8,valid8,t1_7choices,?_⟩
  exact check_of_frontier tree 0 t1_7root t1_7jobs t1_7frontier t1_7all
theorem t1_8choices : plan9.choices=[8].map (options 1 1) := by rfl


theorem t1_8part0 : t1_8jobs0.all (Job.check tree)=true := by decide +kernel

theorem t1_8frontier : t1_8root.frontier 0=t1_8jobs := by rfl
theorem t1_8all : t1_8jobs.all (Job.check tree)=true := by
  simp only [t1_8jobs,List.all_append,List.all_nil,t1_8part0,Bool.and_self]
theorem t1_8checked : Checked tree [8] := by
  refine ⟨plan9,valid9,t1_8choices,?_⟩
  exact check_of_frontier tree 0 t1_8root t1_8jobs t1_8frontier t1_8all
theorem t1_9choices : plan10.choices=[9].map (options 1 1) := by rfl


theorem t1_9part0 : t1_9jobs0.all (Job.check tree)=true := by decide +kernel

theorem t1_9frontier : t1_9root.frontier 0=t1_9jobs := by rfl
theorem t1_9all : t1_9jobs.all (Job.check tree)=true := by
  simp only [t1_9jobs,List.all_append,List.all_nil,t1_9part0,Bool.and_self]
theorem t1_9checked : Checked tree [9] := by
  refine ⟨plan10,valid10,t1_9choices,?_⟩
  exact check_of_frontier tree 0 t1_9root t1_9jobs t1_9frontier t1_9all
theorem t1_10choices : plan11.choices=[10].map (options 1 1) := by rfl


theorem t1_10part0 : t1_10jobs0.all (Job.check tree)=true := by decide +kernel

theorem t1_10frontier : t1_10root.frontier 0=t1_10jobs := by rfl
theorem t1_10all : t1_10jobs.all (Job.check tree)=true := by
  simp only [t1_10jobs,List.all_append,List.all_nil,t1_10part0,Bool.and_self]
theorem t1_10checked : Checked tree [10] := by
  refine ⟨plan11,valid11,t1_10choices,?_⟩
  exact check_of_frontier tree 0 t1_10root t1_10jobs t1_10frontier t1_10all
theorem t2_0choices : plan167.choices=[0,1].map (options 2 0) := by rfl


theorem t2_0part0 : t2_0jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_0frontier : t2_0root.frontier 0=t2_0jobs := by rfl
theorem t2_0all : t2_0jobs.all (Job.check tree)=true := by
  simp only [t2_0jobs,List.all_append,List.all_nil,t2_0part0,Bool.and_self]
theorem t2_0checked : Checked tree [0,1] := by
  refine ⟨plan167,valid167,t2_0choices,?_⟩
  exact check_of_frontier tree 0 t2_0root t2_0jobs t2_0frontier t2_0all
theorem t2_1choices : plan168.choices=[0,2].map (options 2 0) := by rfl


theorem t2_1part0 : t2_1jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_1frontier : t2_1root.frontier 0=t2_1jobs := by rfl
theorem t2_1all : t2_1jobs.all (Job.check tree)=true := by
  simp only [t2_1jobs,List.all_append,List.all_nil,t2_1part0,Bool.and_self]
theorem t2_1checked : Checked tree [0,2] := by
  refine ⟨plan168,valid168,t2_1choices,?_⟩
  exact check_of_frontier tree 0 t2_1root t2_1jobs t2_1frontier t2_1all
theorem t2_2choices : plan169.choices=[0,3].map (options 2 0) := by rfl


theorem t2_2part0 : t2_2jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_2frontier : t2_2root.frontier 0=t2_2jobs := by rfl
theorem t2_2all : t2_2jobs.all (Job.check tree)=true := by
  simp only [t2_2jobs,List.all_append,List.all_nil,t2_2part0,Bool.and_self]
theorem t2_2checked : Checked tree [0,3] := by
  refine ⟨plan169,valid169,t2_2choices,?_⟩
  exact check_of_frontier tree 0 t2_2root t2_2jobs t2_2frontier t2_2all
theorem t2_3choices : plan176.choices=[0,4].map (options 2 1) := by rfl


theorem t2_3part0 : t2_3jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_3frontier : t2_3root.frontier 0=t2_3jobs := by rfl
theorem t2_3all : t2_3jobs.all (Job.check tree)=true := by
  simp only [t2_3jobs,List.all_append,List.all_nil,t2_3part0,Bool.and_self]
theorem t2_3checked : Checked tree [0,4] := by
  refine ⟨plan176,valid176,t2_3choices,?_⟩
  exact check_of_frontier tree 0 t2_3root t2_3jobs t2_3frontier t2_3all
theorem t2_4choices : plan177.choices=[0,5].map (options 2 1) := by rfl


theorem t2_4part0 : t2_4jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_4frontier : t2_4root.frontier 0=t2_4jobs := by rfl
theorem t2_4all : t2_4jobs.all (Job.check tree)=true := by
  simp only [t2_4jobs,List.all_append,List.all_nil,t2_4part0,Bool.and_self]
theorem t2_4checked : Checked tree [0,5] := by
  refine ⟨plan177,valid177,t2_4choices,?_⟩
  exact check_of_frontier tree 0 t2_4root t2_4jobs t2_4frontier t2_4all
theorem t2_5choices : plan178.choices=[0,6].map (options 2 1) := by rfl


theorem t2_5part0 : t2_5jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_5frontier : t2_5root.frontier 0=t2_5jobs := by rfl
theorem t2_5all : t2_5jobs.all (Job.check tree)=true := by
  simp only [t2_5jobs,List.all_append,List.all_nil,t2_5part0,Bool.and_self]
theorem t2_5checked : Checked tree [0,6] := by
  refine ⟨plan178,valid178,t2_5choices,?_⟩
  exact check_of_frontier tree 0 t2_5root t2_5jobs t2_5frontier t2_5all
theorem t2_6choices : plan179.choices=[0,7].map (options 2 1) := by rfl


theorem t2_6part0 : t2_6jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_6frontier : t2_6root.frontier 0=t2_6jobs := by rfl
theorem t2_6all : t2_6jobs.all (Job.check tree)=true := by
  simp only [t2_6jobs,List.all_append,List.all_nil,t2_6part0,Bool.and_self]
theorem t2_6checked : Checked tree [0,7] := by
  refine ⟨plan179,valid179,t2_6choices,?_⟩
  exact check_of_frontier tree 0 t2_6root t2_6jobs t2_6frontier t2_6all
theorem t2_7choices : plan180.choices=[0,8].map (options 2 1) := by rfl


theorem t2_7part0 : t2_7jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_7frontier : t2_7root.frontier 0=t2_7jobs := by rfl
theorem t2_7all : t2_7jobs.all (Job.check tree)=true := by
  simp only [t2_7jobs,List.all_append,List.all_nil,t2_7part0,Bool.and_self]
theorem t2_7checked : Checked tree [0,8] := by
  refine ⟨plan180,valid180,t2_7choices,?_⟩
  exact check_of_frontier tree 0 t2_7root t2_7jobs t2_7frontier t2_7all
theorem t2_8choices : plan181.choices=[0,9].map (options 2 1) := by rfl


theorem t2_8part0 : t2_8jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_8frontier : t2_8root.frontier 0=t2_8jobs := by rfl
theorem t2_8all : t2_8jobs.all (Job.check tree)=true := by
  simp only [t2_8jobs,List.all_append,List.all_nil,t2_8part0,Bool.and_self]
theorem t2_8checked : Checked tree [0,9] := by
  refine ⟨plan181,valid181,t2_8choices,?_⟩
  exact check_of_frontier tree 0 t2_8root t2_8jobs t2_8frontier t2_8all
theorem t2_9choices : plan182.choices=[0,10].map (options 2 1) := by rfl


theorem t2_9part0 : t2_9jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_9frontier : t2_9root.frontier 0=t2_9jobs := by rfl
theorem t2_9all : t2_9jobs.all (Job.check tree)=true := by
  simp only [t2_9jobs,List.all_append,List.all_nil,t2_9part0,Bool.and_self]
theorem t2_9checked : Checked tree [0,10] := by
  refine ⟨plan182,valid182,t2_9choices,?_⟩
  exact check_of_frontier tree 0 t2_9root t2_9jobs t2_9frontier t2_9all
theorem t2_10choices : plan170.choices=[1,1].map (options 2 0) := by rfl


theorem t2_10part0 : t2_10jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_10frontier : t2_10root.frontier 0=t2_10jobs := by rfl
theorem t2_10all : t2_10jobs.all (Job.check tree)=true := by
  simp only [t2_10jobs,List.all_append,List.all_nil,t2_10part0,Bool.and_self]
theorem t2_10checked : Checked tree [1,1] := by
  refine ⟨plan170,valid170,t2_10choices,?_⟩
  exact check_of_frontier tree 0 t2_10root t2_10jobs t2_10frontier t2_10all
theorem t2_11choices : plan171.choices=[1,2].map (options 2 0) := by rfl


theorem t2_11part0 : t2_11jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_11frontier : t2_11root.frontier 0=t2_11jobs := by rfl
theorem t2_11all : t2_11jobs.all (Job.check tree)=true := by
  simp only [t2_11jobs,List.all_append,List.all_nil,t2_11part0,Bool.and_self]
theorem t2_11checked : Checked tree [1,2] := by
  refine ⟨plan171,valid171,t2_11choices,?_⟩
  exact check_of_frontier tree 0 t2_11root t2_11jobs t2_11frontier t2_11all
theorem t2_12choices : plan172.choices=[1,3].map (options 2 0) := by rfl


theorem t2_12part0 : t2_12jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_12frontier : t2_12root.frontier 0=t2_12jobs := by rfl
theorem t2_12all : t2_12jobs.all (Job.check tree)=true := by
  simp only [t2_12jobs,List.all_append,List.all_nil,t2_12part0,Bool.and_self]
theorem t2_12checked : Checked tree [1,3] := by
  refine ⟨plan172,valid172,t2_12choices,?_⟩
  exact check_of_frontier tree 0 t2_12root t2_12jobs t2_12frontier t2_12all
theorem t2_13choices : plan183.choices=[1,4].map (options 2 1) := by rfl


theorem t2_13part0 : t2_13jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_13frontier : t2_13root.frontier 0=t2_13jobs := by rfl
theorem t2_13all : t2_13jobs.all (Job.check tree)=true := by
  simp only [t2_13jobs,List.all_append,List.all_nil,t2_13part0,Bool.and_self]
theorem t2_13checked : Checked tree [1,4] := by
  refine ⟨plan183,valid183,t2_13choices,?_⟩
  exact check_of_frontier tree 0 t2_13root t2_13jobs t2_13frontier t2_13all
theorem t2_14choices : plan184.choices=[1,5].map (options 2 1) := by rfl


theorem t2_14part0 : t2_14jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_14frontier : t2_14root.frontier 0=t2_14jobs := by rfl
theorem t2_14all : t2_14jobs.all (Job.check tree)=true := by
  simp only [t2_14jobs,List.all_append,List.all_nil,t2_14part0,Bool.and_self]
theorem t2_14checked : Checked tree [1,5] := by
  refine ⟨plan184,valid184,t2_14choices,?_⟩
  exact check_of_frontier tree 0 t2_14root t2_14jobs t2_14frontier t2_14all
theorem t2_15choices : plan185.choices=[1,6].map (options 2 1) := by rfl


theorem t2_15part0 : t2_15jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_15frontier : t2_15root.frontier 0=t2_15jobs := by rfl
theorem t2_15all : t2_15jobs.all (Job.check tree)=true := by
  simp only [t2_15jobs,List.all_append,List.all_nil,t2_15part0,Bool.and_self]
theorem t2_15checked : Checked tree [1,6] := by
  refine ⟨plan185,valid185,t2_15choices,?_⟩
  exact check_of_frontier tree 0 t2_15root t2_15jobs t2_15frontier t2_15all
theorem t2_16choices : plan186.choices=[1,7].map (options 2 1) := by rfl


theorem t2_16part0 : t2_16jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_16frontier : t2_16root.frontier 0=t2_16jobs := by rfl
theorem t2_16all : t2_16jobs.all (Job.check tree)=true := by
  simp only [t2_16jobs,List.all_append,List.all_nil,t2_16part0,Bool.and_self]
theorem t2_16checked : Checked tree [1,7] := by
  refine ⟨plan186,valid186,t2_16choices,?_⟩
  exact check_of_frontier tree 0 t2_16root t2_16jobs t2_16frontier t2_16all
theorem t2_17choices : plan187.choices=[1,8].map (options 2 1) := by rfl


theorem t2_17part0 : t2_17jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_17frontier : t2_17root.frontier 0=t2_17jobs := by rfl
theorem t2_17all : t2_17jobs.all (Job.check tree)=true := by
  simp only [t2_17jobs,List.all_append,List.all_nil,t2_17part0,Bool.and_self]
theorem t2_17checked : Checked tree [1,8] := by
  refine ⟨plan187,valid187,t2_17choices,?_⟩
  exact check_of_frontier tree 0 t2_17root t2_17jobs t2_17frontier t2_17all
theorem t2_18choices : plan188.choices=[1,9].map (options 2 1) := by rfl


theorem t2_18part0 : t2_18jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_18frontier : t2_18root.frontier 0=t2_18jobs := by rfl
theorem t2_18all : t2_18jobs.all (Job.check tree)=true := by
  simp only [t2_18jobs,List.all_append,List.all_nil,t2_18part0,Bool.and_self]
theorem t2_18checked : Checked tree [1,9] := by
  refine ⟨plan188,valid188,t2_18choices,?_⟩
  exact check_of_frontier tree 0 t2_18root t2_18jobs t2_18frontier t2_18all
theorem t2_19choices : plan189.choices=[1,10].map (options 2 1) := by rfl


theorem t2_19part0 : t2_19jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_19frontier : t2_19root.frontier 0=t2_19jobs := by rfl
theorem t2_19all : t2_19jobs.all (Job.check tree)=true := by
  simp only [t2_19jobs,List.all_append,List.all_nil,t2_19part0,Bool.and_self]
theorem t2_19checked : Checked tree [1,10] := by
  refine ⟨plan189,valid189,t2_19choices,?_⟩
  exact check_of_frontier tree 0 t2_19root t2_19jobs t2_19frontier t2_19all
theorem t2_20choices : plan173.choices=[2,2].map (options 2 0) := by rfl


theorem t2_20part0 : t2_20jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_20frontier : t2_20root.frontier 0=t2_20jobs := by rfl
theorem t2_20all : t2_20jobs.all (Job.check tree)=true := by
  simp only [t2_20jobs,List.all_append,List.all_nil,t2_20part0,Bool.and_self]
theorem t2_20checked : Checked tree [2,2] := by
  refine ⟨plan173,valid173,t2_20choices,?_⟩
  exact check_of_frontier tree 0 t2_20root t2_20jobs t2_20frontier t2_20all
theorem t2_21choices : plan174.choices=[2,3].map (options 2 0) := by rfl


theorem t2_21part0 : t2_21jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_21frontier : t2_21root.frontier 0=t2_21jobs := by rfl
theorem t2_21all : t2_21jobs.all (Job.check tree)=true := by
  simp only [t2_21jobs,List.all_append,List.all_nil,t2_21part0,Bool.and_self]
theorem t2_21checked : Checked tree [2,3] := by
  refine ⟨plan174,valid174,t2_21choices,?_⟩
  exact check_of_frontier tree 0 t2_21root t2_21jobs t2_21frontier t2_21all
theorem t2_22choices : plan190.choices=[2,5].map (options 2 1) := by rfl


theorem t2_22part0 : t2_22jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_22frontier : t2_22root.frontier 0=t2_22jobs := by rfl
theorem t2_22all : t2_22jobs.all (Job.check tree)=true := by
  simp only [t2_22jobs,List.all_append,List.all_nil,t2_22part0,Bool.and_self]
theorem t2_22checked : Checked tree [2,5] := by
  refine ⟨plan190,valid190,t2_22choices,?_⟩
  exact check_of_frontier tree 0 t2_22root t2_22jobs t2_22frontier t2_22all
theorem t2_23choices : plan191.choices=[2,6].map (options 2 1) := by rfl


theorem t2_23part0 : t2_23jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_23frontier : t2_23root.frontier 0=t2_23jobs := by rfl
theorem t2_23all : t2_23jobs.all (Job.check tree)=true := by
  simp only [t2_23jobs,List.all_append,List.all_nil,t2_23part0,Bool.and_self]
theorem t2_23checked : Checked tree [2,6] := by
  refine ⟨plan191,valid191,t2_23choices,?_⟩
  exact check_of_frontier tree 0 t2_23root t2_23jobs t2_23frontier t2_23all
theorem t2_24choices : plan192.choices=[2,7].map (options 2 1) := by rfl


theorem t2_24part0 : t2_24jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_24frontier : t2_24root.frontier 0=t2_24jobs := by rfl
theorem t2_24all : t2_24jobs.all (Job.check tree)=true := by
  simp only [t2_24jobs,List.all_append,List.all_nil,t2_24part0,Bool.and_self]
theorem t2_24checked : Checked tree [2,7] := by
  refine ⟨plan192,valid192,t2_24choices,?_⟩
  exact check_of_frontier tree 0 t2_24root t2_24jobs t2_24frontier t2_24all
theorem t2_25choices : plan193.choices=[2,9].map (options 2 1) := by rfl


theorem t2_25part0 : t2_25jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_25frontier : t2_25root.frontier 0=t2_25jobs := by rfl
theorem t2_25all : t2_25jobs.all (Job.check tree)=true := by
  simp only [t2_25jobs,List.all_append,List.all_nil,t2_25part0,Bool.and_self]
theorem t2_25checked : Checked tree [2,9] := by
  refine ⟨plan193,valid193,t2_25choices,?_⟩
  exact check_of_frontier tree 0 t2_25root t2_25jobs t2_25frontier t2_25all
theorem t2_26choices : plan194.choices=[2,10].map (options 2 1) := by rfl


theorem t2_26part0 : t2_26jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_26frontier : t2_26root.frontier 0=t2_26jobs := by rfl
theorem t2_26all : t2_26jobs.all (Job.check tree)=true := by
  simp only [t2_26jobs,List.all_append,List.all_nil,t2_26part0,Bool.and_self]
theorem t2_26checked : Checked tree [2,10] := by
  refine ⟨plan194,valid194,t2_26choices,?_⟩
  exact check_of_frontier tree 0 t2_26root t2_26jobs t2_26frontier t2_26all
theorem t2_27choices : plan175.choices=[3,3].map (options 2 0) := by rfl


theorem t2_27part0 : t2_27jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_27frontier : t2_27root.frontier 0=t2_27jobs := by rfl
theorem t2_27all : t2_27jobs.all (Job.check tree)=true := by
  simp only [t2_27jobs,List.all_append,List.all_nil,t2_27part0,Bool.and_self]
theorem t2_27checked : Checked tree [3,3] := by
  refine ⟨plan175,valid175,t2_27choices,?_⟩
  exact check_of_frontier tree 0 t2_27root t2_27jobs t2_27frontier t2_27all
theorem t2_28choices : plan195.choices=[3,6].map (options 2 1) := by rfl


theorem t2_28part0 : t2_28jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_28frontier : t2_28root.frontier 0=t2_28jobs := by rfl
theorem t2_28all : t2_28jobs.all (Job.check tree)=true := by
  simp only [t2_28jobs,List.all_append,List.all_nil,t2_28part0,Bool.and_self]
theorem t2_28checked : Checked tree [3,6] := by
  refine ⟨plan195,valid195,t2_28choices,?_⟩
  exact check_of_frontier tree 0 t2_28root t2_28jobs t2_28frontier t2_28all
theorem t2_29choices : plan196.choices=[3,7].map (options 2 1) := by rfl


theorem t2_29part0 : t2_29jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_29frontier : t2_29root.frontier 0=t2_29jobs := by rfl
theorem t2_29all : t2_29jobs.all (Job.check tree)=true := by
  simp only [t2_29jobs,List.all_append,List.all_nil,t2_29part0,Bool.and_self]
theorem t2_29checked : Checked tree [3,7] := by
  refine ⟨plan196,valid196,t2_29choices,?_⟩
  exact check_of_frontier tree 0 t2_29root t2_29jobs t2_29frontier t2_29all
theorem t2_30choices : plan197.choices=[3,10].map (options 2 1) := by rfl


theorem t2_30part0 : t2_30jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_30frontier : t2_30root.frontier 0=t2_30jobs := by rfl
theorem t2_30all : t2_30jobs.all (Job.check tree)=true := by
  simp only [t2_30jobs,List.all_append,List.all_nil,t2_30part0,Bool.and_self]
theorem t2_30checked : Checked tree [3,10] := by
  refine ⟨plan197,valid197,t2_30choices,?_⟩
  exact check_of_frontier tree 0 t2_30root t2_30jobs t2_30frontier t2_30all
theorem t2_31choices : plan198.choices=[4,2].map (options 2 1) := by rfl


theorem t2_31part0 : t2_31jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_31frontier : t2_31root.frontier 0=t2_31jobs := by rfl
theorem t2_31all : t2_31jobs.all (Job.check tree)=true := by
  simp only [t2_31jobs,List.all_append,List.all_nil,t2_31part0,Bool.and_self]
theorem t2_31checked : Checked tree [4,2] := by
  refine ⟨plan198,valid198,t2_31choices,?_⟩
  exact check_of_frontier tree 0 t2_31root t2_31jobs t2_31frontier t2_31all
theorem t2_32choices : plan199.choices=[4,3].map (options 2 1) := by rfl


theorem t2_32part0 : t2_32jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_32frontier : t2_32root.frontier 0=t2_32jobs := by rfl
theorem t2_32all : t2_32jobs.all (Job.check tree)=true := by
  simp only [t2_32jobs,List.all_append,List.all_nil,t2_32part0,Bool.and_self]
theorem t2_32checked : Checked tree [4,3] := by
  refine ⟨plan199,valid199,t2_32choices,?_⟩
  exact check_of_frontier tree 0 t2_32root t2_32jobs t2_32frontier t2_32all
theorem t2_33choices : plan204.choices=[4,4].map (options 2 2) := by rfl


theorem t2_33part0 : t2_33jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_33frontier : t2_33root.frontier 0=t2_33jobs := by rfl
theorem t2_33all : t2_33jobs.all (Job.check tree)=true := by
  simp only [t2_33jobs,List.all_append,List.all_nil,t2_33part0,Bool.and_self]
theorem t2_33checked : Checked tree [4,4] := by
  refine ⟨plan204,valid204,t2_33choices,?_⟩
  exact check_of_frontier tree 0 t2_33root t2_33jobs t2_33frontier t2_33all
theorem t2_34choices : plan205.choices=[4,5].map (options 2 2) := by rfl


theorem t2_34part0 : t2_34jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_34frontier : t2_34root.frontier 0=t2_34jobs := by rfl
theorem t2_34all : t2_34jobs.all (Job.check tree)=true := by
  simp only [t2_34jobs,List.all_append,List.all_nil,t2_34part0,Bool.and_self]
theorem t2_34checked : Checked tree [4,5] := by
  refine ⟨plan205,valid205,t2_34choices,?_⟩
  exact check_of_frontier tree 0 t2_34root t2_34jobs t2_34frontier t2_34all
theorem t2_35choices : plan206.choices=[4,6].map (options 2 2) := by rfl


theorem t2_35part0 : t2_35jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_35frontier : t2_35root.frontier 0=t2_35jobs := by rfl
theorem t2_35all : t2_35jobs.all (Job.check tree)=true := by
  simp only [t2_35jobs,List.all_append,List.all_nil,t2_35part0,Bool.and_self]
theorem t2_35checked : Checked tree [4,6] := by
  refine ⟨plan206,valid206,t2_35choices,?_⟩
  exact check_of_frontier tree 0 t2_35root t2_35jobs t2_35frontier t2_35all
theorem t2_36choices : plan207.choices=[4,7].map (options 2 2) := by rfl


theorem t2_36part0 : t2_36jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_36frontier : t2_36root.frontier 0=t2_36jobs := by rfl
theorem t2_36all : t2_36jobs.all (Job.check tree)=true := by
  simp only [t2_36jobs,List.all_append,List.all_nil,t2_36part0,Bool.and_self]
theorem t2_36checked : Checked tree [4,7] := by
  refine ⟨plan207,valid207,t2_36choices,?_⟩
  exact check_of_frontier tree 0 t2_36root t2_36jobs t2_36frontier t2_36all
theorem t2_37choices : plan208.choices=[4,8].map (options 2 2) := by rfl


theorem t2_37part0 : t2_37jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_37frontier : t2_37root.frontier 0=t2_37jobs := by rfl
theorem t2_37all : t2_37jobs.all (Job.check tree)=true := by
  simp only [t2_37jobs,List.all_append,List.all_nil,t2_37part0,Bool.and_self]
theorem t2_37checked : Checked tree [4,8] := by
  refine ⟨plan208,valid208,t2_37choices,?_⟩
  exact check_of_frontier tree 0 t2_37root t2_37jobs t2_37frontier t2_37all
theorem t2_38choices : plan209.choices=[4,9].map (options 2 2) := by rfl


theorem t2_38part0 : t2_38jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_38frontier : t2_38root.frontier 0=t2_38jobs := by rfl
theorem t2_38all : t2_38jobs.all (Job.check tree)=true := by
  simp only [t2_38jobs,List.all_append,List.all_nil,t2_38part0,Bool.and_self]
theorem t2_38checked : Checked tree [4,9] := by
  refine ⟨plan209,valid209,t2_38choices,?_⟩
  exact check_of_frontier tree 0 t2_38root t2_38jobs t2_38frontier t2_38all
theorem t2_39choices : plan210.choices=[4,10].map (options 2 2) := by rfl


theorem t2_39part0 : t2_39jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_39frontier : t2_39root.frontier 0=t2_39jobs := by rfl
theorem t2_39all : t2_39jobs.all (Job.check tree)=true := by
  simp only [t2_39jobs,List.all_append,List.all_nil,t2_39part0,Bool.and_self]
theorem t2_39checked : Checked tree [4,10] := by
  refine ⟨plan210,valid210,t2_39choices,?_⟩
  exact check_of_frontier tree 0 t2_39root t2_39jobs t2_39frontier t2_39all
theorem t2_40choices : plan200.choices=[5,3].map (options 2 1) := by rfl


theorem t2_40part0 : t2_40jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_40frontier : t2_40root.frontier 0=t2_40jobs := by rfl
theorem t2_40all : t2_40jobs.all (Job.check tree)=true := by
  simp only [t2_40jobs,List.all_append,List.all_nil,t2_40part0,Bool.and_self]
theorem t2_40checked : Checked tree [5,3] := by
  refine ⟨plan200,valid200,t2_40choices,?_⟩
  exact check_of_frontier tree 0 t2_40root t2_40jobs t2_40frontier t2_40all
theorem t2_41choices : plan211.choices=[5,5].map (options 2 2) := by rfl


theorem t2_41part0 : t2_41jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_41frontier : t2_41root.frontier 0=t2_41jobs := by rfl
theorem t2_41all : t2_41jobs.all (Job.check tree)=true := by
  simp only [t2_41jobs,List.all_append,List.all_nil,t2_41part0,Bool.and_self]
theorem t2_41checked : Checked tree [5,5] := by
  refine ⟨plan211,valid211,t2_41choices,?_⟩
  exact check_of_frontier tree 0 t2_41root t2_41jobs t2_41frontier t2_41all
theorem t2_42choices : plan212.choices=[5,6].map (options 2 2) := by rfl


theorem t2_42part0 : t2_42jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_42frontier : t2_42root.frontier 0=t2_42jobs := by rfl
theorem t2_42all : t2_42jobs.all (Job.check tree)=true := by
  simp only [t2_42jobs,List.all_append,List.all_nil,t2_42part0,Bool.and_self]
theorem t2_42checked : Checked tree [5,6] := by
  refine ⟨plan212,valid212,t2_42choices,?_⟩
  exact check_of_frontier tree 0 t2_42root t2_42jobs t2_42frontier t2_42all
theorem t2_43choices : plan213.choices=[5,7].map (options 2 2) := by rfl


theorem t2_43part0 : t2_43jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_43frontier : t2_43root.frontier 0=t2_43jobs := by rfl
theorem t2_43all : t2_43jobs.all (Job.check tree)=true := by
  simp only [t2_43jobs,List.all_append,List.all_nil,t2_43part0,Bool.and_self]
theorem t2_43checked : Checked tree [5,7] := by
  refine ⟨plan213,valid213,t2_43choices,?_⟩
  exact check_of_frontier tree 0 t2_43root t2_43jobs t2_43frontier t2_43all
theorem t2_44choices : plan214.choices=[5,9].map (options 2 2) := by rfl


theorem t2_44part0 : t2_44jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_44frontier : t2_44root.frontier 0=t2_44jobs := by rfl
theorem t2_44all : t2_44jobs.all (Job.check tree)=true := by
  simp only [t2_44jobs,List.all_append,List.all_nil,t2_44part0,Bool.and_self]
theorem t2_44checked : Checked tree [5,9] := by
  refine ⟨plan214,valid214,t2_44choices,?_⟩
  exact check_of_frontier tree 0 t2_44root t2_44jobs t2_44frontier t2_44all
theorem t2_45choices : plan215.choices=[5,10].map (options 2 2) := by rfl


theorem t2_45part0 : t2_45jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_45frontier : t2_45root.frontier 0=t2_45jobs := by rfl
theorem t2_45all : t2_45jobs.all (Job.check tree)=true := by
  simp only [t2_45jobs,List.all_append,List.all_nil,t2_45part0,Bool.and_self]
theorem t2_45checked : Checked tree [5,10] := by
  refine ⟨plan215,valid215,t2_45choices,?_⟩
  exact check_of_frontier tree 0 t2_45root t2_45jobs t2_45frontier t2_45all
theorem t2_46choices : plan216.choices=[6,6].map (options 2 2) := by rfl


theorem t2_46part0 : t2_46jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_46frontier : t2_46root.frontier 0=t2_46jobs := by rfl
theorem t2_46all : t2_46jobs.all (Job.check tree)=true := by
  simp only [t2_46jobs,List.all_append,List.all_nil,t2_46part0,Bool.and_self]
theorem t2_46checked : Checked tree [6,6] := by
  refine ⟨plan216,valid216,t2_46choices,?_⟩
  exact check_of_frontier tree 0 t2_46root t2_46jobs t2_46frontier t2_46all
theorem t2_47choices : plan217.choices=[6,7].map (options 2 2) := by rfl


theorem t2_47part0 : t2_47jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_47frontier : t2_47root.frontier 0=t2_47jobs := by rfl
theorem t2_47all : t2_47jobs.all (Job.check tree)=true := by
  simp only [t2_47jobs,List.all_append,List.all_nil,t2_47part0,Bool.and_self]
theorem t2_47checked : Checked tree [6,7] := by
  refine ⟨plan217,valid217,t2_47choices,?_⟩
  exact check_of_frontier tree 0 t2_47root t2_47jobs t2_47frontier t2_47all
theorem t2_48choices : plan218.choices=[6,10].map (options 2 2) := by rfl


theorem t2_48part0 : t2_48jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_48frontier : t2_48root.frontier 0=t2_48jobs := by rfl
theorem t2_48all : t2_48jobs.all (Job.check tree)=true := by
  simp only [t2_48jobs,List.all_append,List.all_nil,t2_48part0,Bool.and_self]
theorem t2_48checked : Checked tree [6,10] := by
  refine ⟨plan218,valid218,t2_48choices,?_⟩
  exact check_of_frontier tree 0 t2_48root t2_48jobs t2_48frontier t2_48all
theorem t2_49choices : plan219.choices=[7,7].map (options 2 2) := by rfl


theorem t2_49part0 : t2_49jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_49frontier : t2_49root.frontier 0=t2_49jobs := by rfl
theorem t2_49all : t2_49jobs.all (Job.check tree)=true := by
  simp only [t2_49jobs,List.all_append,List.all_nil,t2_49part0,Bool.and_self]
theorem t2_49checked : Checked tree [7,7] := by
  refine ⟨plan219,valid219,t2_49choices,?_⟩
  exact check_of_frontier tree 0 t2_49root t2_49jobs t2_49frontier t2_49all
theorem t2_50choices : plan201.choices=[8,2].map (options 2 1) := by rfl


theorem t2_50part0 : t2_50jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_50frontier : t2_50root.frontier 0=t2_50jobs := by rfl
theorem t2_50all : t2_50jobs.all (Job.check tree)=true := by
  simp only [t2_50jobs,List.all_append,List.all_nil,t2_50part0,Bool.and_self]
theorem t2_50checked : Checked tree [8,2] := by
  refine ⟨plan201,valid201,t2_50choices,?_⟩
  exact check_of_frontier tree 0 t2_50root t2_50jobs t2_50frontier t2_50all
theorem t2_51choices : plan202.choices=[8,3].map (options 2 1) := by rfl


theorem t2_51part0 : t2_51jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_51frontier : t2_51root.frontier 0=t2_51jobs := by rfl
theorem t2_51all : t2_51jobs.all (Job.check tree)=true := by
  simp only [t2_51jobs,List.all_append,List.all_nil,t2_51part0,Bool.and_self]
theorem t2_51checked : Checked tree [8,3] := by
  refine ⟨plan202,valid202,t2_51choices,?_⟩
  exact check_of_frontier tree 0 t2_51root t2_51jobs t2_51frontier t2_51all
theorem t2_52choices : plan220.choices=[8,5].map (options 2 2) := by rfl


theorem t2_52part0 : t2_52jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_52frontier : t2_52root.frontier 0=t2_52jobs := by rfl
theorem t2_52all : t2_52jobs.all (Job.check tree)=true := by
  simp only [t2_52jobs,List.all_append,List.all_nil,t2_52part0,Bool.and_self]
theorem t2_52checked : Checked tree [8,5] := by
  refine ⟨plan220,valid220,t2_52choices,?_⟩
  exact check_of_frontier tree 0 t2_52root t2_52jobs t2_52frontier t2_52all
theorem t2_53choices : plan221.choices=[8,6].map (options 2 2) := by rfl


theorem t2_53part0 : t2_53jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_53frontier : t2_53root.frontier 0=t2_53jobs := by rfl
theorem t2_53all : t2_53jobs.all (Job.check tree)=true := by
  simp only [t2_53jobs,List.all_append,List.all_nil,t2_53part0,Bool.and_self]
theorem t2_53checked : Checked tree [8,6] := by
  refine ⟨plan221,valid221,t2_53choices,?_⟩
  exact check_of_frontier tree 0 t2_53root t2_53jobs t2_53frontier t2_53all
theorem t2_54choices : plan222.choices=[8,7].map (options 2 2) := by rfl


theorem t2_54part0 : t2_54jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_54frontier : t2_54root.frontier 0=t2_54jobs := by rfl
theorem t2_54all : t2_54jobs.all (Job.check tree)=true := by
  simp only [t2_54jobs,List.all_append,List.all_nil,t2_54part0,Bool.and_self]
theorem t2_54checked : Checked tree [8,7] := by
  refine ⟨plan222,valid222,t2_54choices,?_⟩
  exact check_of_frontier tree 0 t2_54root t2_54jobs t2_54frontier t2_54all
theorem t2_55choices : plan223.choices=[8,8].map (options 2 2) := by rfl


theorem t2_55part0 : t2_55jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_55frontier : t2_55root.frontier 0=t2_55jobs := by rfl
theorem t2_55all : t2_55jobs.all (Job.check tree)=true := by
  simp only [t2_55jobs,List.all_append,List.all_nil,t2_55part0,Bool.and_self]
theorem t2_55checked : Checked tree [8,8] := by
  refine ⟨plan223,valid223,t2_55choices,?_⟩
  exact check_of_frontier tree 0 t2_55root t2_55jobs t2_55frontier t2_55all
theorem t2_56choices : plan224.choices=[8,9].map (options 2 2) := by rfl


theorem t2_56part0 : t2_56jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_56frontier : t2_56root.frontier 0=t2_56jobs := by rfl
theorem t2_56all : t2_56jobs.all (Job.check tree)=true := by
  simp only [t2_56jobs,List.all_append,List.all_nil,t2_56part0,Bool.and_self]
theorem t2_56checked : Checked tree [8,9] := by
  refine ⟨plan224,valid224,t2_56choices,?_⟩
  exact check_of_frontier tree 0 t2_56root t2_56jobs t2_56frontier t2_56all
theorem t2_57choices : plan225.choices=[8,10].map (options 2 2) := by rfl


theorem t2_57part0 : t2_57jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_57frontier : t2_57root.frontier 0=t2_57jobs := by rfl
theorem t2_57all : t2_57jobs.all (Job.check tree)=true := by
  simp only [t2_57jobs,List.all_append,List.all_nil,t2_57part0,Bool.and_self]
theorem t2_57checked : Checked tree [8,10] := by
  refine ⟨plan225,valid225,t2_57choices,?_⟩
  exact check_of_frontier tree 0 t2_57root t2_57jobs t2_57frontier t2_57all
theorem t2_58choices : plan203.choices=[9,3].map (options 2 1) := by rfl


theorem t2_58part0 : t2_58jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_58frontier : t2_58root.frontier 0=t2_58jobs := by rfl
theorem t2_58all : t2_58jobs.all (Job.check tree)=true := by
  simp only [t2_58jobs,List.all_append,List.all_nil,t2_58part0,Bool.and_self]
theorem t2_58checked : Checked tree [9,3] := by
  refine ⟨plan203,valid203,t2_58choices,?_⟩
  exact check_of_frontier tree 0 t2_58root t2_58jobs t2_58frontier t2_58all
theorem t2_59choices : plan226.choices=[9,6].map (options 2 2) := by rfl


theorem t2_59part0 : t2_59jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_59frontier : t2_59root.frontier 0=t2_59jobs := by rfl
theorem t2_59all : t2_59jobs.all (Job.check tree)=true := by
  simp only [t2_59jobs,List.all_append,List.all_nil,t2_59part0,Bool.and_self]
theorem t2_59checked : Checked tree [9,6] := by
  refine ⟨plan226,valid226,t2_59choices,?_⟩
  exact check_of_frontier tree 0 t2_59root t2_59jobs t2_59frontier t2_59all
theorem t2_60choices : plan227.choices=[9,7].map (options 2 2) := by rfl


theorem t2_60part0 : t2_60jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_60frontier : t2_60root.frontier 0=t2_60jobs := by rfl
theorem t2_60all : t2_60jobs.all (Job.check tree)=true := by
  simp only [t2_60jobs,List.all_append,List.all_nil,t2_60part0,Bool.and_self]
theorem t2_60checked : Checked tree [9,7] := by
  refine ⟨plan227,valid227,t2_60choices,?_⟩
  exact check_of_frontier tree 0 t2_60root t2_60jobs t2_60frontier t2_60all
theorem t2_61choices : plan228.choices=[9,9].map (options 2 2) := by rfl


theorem t2_61part0 : t2_61jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_61frontier : t2_61root.frontier 0=t2_61jobs := by rfl
theorem t2_61all : t2_61jobs.all (Job.check tree)=true := by
  simp only [t2_61jobs,List.all_append,List.all_nil,t2_61part0,Bool.and_self]
theorem t2_61checked : Checked tree [9,9] := by
  refine ⟨plan228,valid228,t2_61choices,?_⟩
  exact check_of_frontier tree 0 t2_61root t2_61jobs t2_61frontier t2_61all
theorem t2_62choices : plan229.choices=[9,10].map (options 2 2) := by rfl


theorem t2_62part0 : t2_62jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_62frontier : t2_62root.frontier 0=t2_62jobs := by rfl
theorem t2_62all : t2_62jobs.all (Job.check tree)=true := by
  simp only [t2_62jobs,List.all_append,List.all_nil,t2_62part0,Bool.and_self]
theorem t2_62checked : Checked tree [9,10] := by
  refine ⟨plan229,valid229,t2_62choices,?_⟩
  exact check_of_frontier tree 0 t2_62root t2_62jobs t2_62frontier t2_62all
theorem t2_63choices : plan230.choices=[10,7].map (options 2 2) := by rfl


theorem t2_63part0 : t2_63jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_63frontier : t2_63root.frontier 0=t2_63jobs := by rfl
theorem t2_63all : t2_63jobs.all (Job.check tree)=true := by
  simp only [t2_63jobs,List.all_append,List.all_nil,t2_63part0,Bool.and_self]
theorem t2_63checked : Checked tree [10,7] := by
  refine ⟨plan230,valid230,t2_63choices,?_⟩
  exact check_of_frontier tree 0 t2_63root t2_63jobs t2_63frontier t2_63all
theorem t2_64choices : plan231.choices=[10,10].map (options 2 2) := by rfl


theorem t2_64part0 : t2_64jobs0.all (Job.check tree)=true := by decide +kernel

theorem t2_64frontier : t2_64root.frontier 0=t2_64jobs := by rfl
theorem t2_64all : t2_64jobs.all (Job.check tree)=true := by
  simp only [t2_64jobs,List.all_append,List.all_nil,t2_64part0,Bool.and_self]
theorem t2_64checked : Checked tree [10,10] := by
  refine ⟨plan231,valid231,t2_64choices,?_⟩
  exact check_of_frontier tree 0 t2_64root t2_64jobs t2_64frontier t2_64all
theorem t3_0choices : plan634.choices=[0,1,2].map (options 3 0) := by rfl


theorem t3_0part0 : t3_0jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_0frontier : t3_0root.frontier 0=t3_0jobs := by rfl
theorem t3_0all : t3_0jobs.all (Job.check tree)=true := by
  simp only [t3_0jobs,List.all_append,List.all_nil,t3_0part0,Bool.and_self]
theorem t3_0checked : Checked tree [0,1,2] := by
  refine ⟨plan634,valid634,t3_0choices,?_⟩
  exact check_of_frontier tree 0 t3_0root t3_0jobs t3_0frontier t3_0all
theorem t3_1choices : plan635.choices=[0,1,3].map (options 3 0) := by rfl


theorem t3_1part0 : t3_1jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_1frontier : t3_1root.frontier 0=t3_1jobs := by rfl
theorem t3_1all : t3_1jobs.all (Job.check tree)=true := by
  simp only [t3_1jobs,List.all_append,List.all_nil,t3_1part0,Bool.and_self]
theorem t3_1checked : Checked tree [0,1,3] := by
  refine ⟨plan635,valid635,t3_1choices,?_⟩
  exact check_of_frontier tree 0 t3_1root t3_1jobs t3_1frontier t3_1all
theorem t3_2choices : plan649.choices=[0,1,5].map (options 3 1) := by rfl


theorem t3_2part0 : t3_2jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_2frontier : t3_2root.frontier 0=t3_2jobs := by rfl
theorem t3_2all : t3_2jobs.all (Job.check tree)=true := by
  simp only [t3_2jobs,List.all_append,List.all_nil,t3_2part0,Bool.and_self]
theorem t3_2checked : Checked tree [0,1,5] := by
  refine ⟨plan649,valid649,t3_2choices,?_⟩
  exact check_of_frontier tree 0 t3_2root t3_2jobs t3_2frontier t3_2all
theorem t3_3choices : plan650.choices=[0,1,6].map (options 3 1) := by rfl


theorem t3_3part0 : t3_3jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_3frontier : t3_3root.frontier 0=t3_3jobs := by rfl
theorem t3_3all : t3_3jobs.all (Job.check tree)=true := by
  simp only [t3_3jobs,List.all_append,List.all_nil,t3_3part0,Bool.and_self]
theorem t3_3checked : Checked tree [0,1,6] := by
  refine ⟨plan650,valid650,t3_3choices,?_⟩
  exact check_of_frontier tree 0 t3_3root t3_3jobs t3_3frontier t3_3all
theorem t3_4choices : plan651.choices=[0,1,7].map (options 3 1) := by rfl


theorem t3_4part0 : t3_4jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_4frontier : t3_4root.frontier 0=t3_4jobs := by rfl
theorem t3_4all : t3_4jobs.all (Job.check tree)=true := by
  simp only [t3_4jobs,List.all_append,List.all_nil,t3_4part0,Bool.and_self]
theorem t3_4checked : Checked tree [0,1,7] := by
  refine ⟨plan651,valid651,t3_4choices,?_⟩
  exact check_of_frontier tree 0 t3_4root t3_4jobs t3_4frontier t3_4all
theorem t3_5choices : plan652.choices=[0,1,9].map (options 3 1) := by rfl


theorem t3_5part0 : t3_5jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_5frontier : t3_5root.frontier 0=t3_5jobs := by rfl
theorem t3_5all : t3_5jobs.all (Job.check tree)=true := by
  simp only [t3_5jobs,List.all_append,List.all_nil,t3_5part0,Bool.and_self]
theorem t3_5checked : Checked tree [0,1,9] := by
  refine ⟨plan652,valid652,t3_5choices,?_⟩
  exact check_of_frontier tree 0 t3_5root t3_5jobs t3_5frontier t3_5all
theorem t3_6choices : plan653.choices=[0,1,10].map (options 3 1) := by rfl


theorem t3_6part0 : t3_6jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_6frontier : t3_6root.frontier 0=t3_6jobs := by rfl
theorem t3_6all : t3_6jobs.all (Job.check tree)=true := by
  simp only [t3_6jobs,List.all_append,List.all_nil,t3_6part0,Bool.and_self]
theorem t3_6checked : Checked tree [0,1,10] := by
  refine ⟨plan653,valid653,t3_6choices,?_⟩
  exact check_of_frontier tree 0 t3_6root t3_6jobs t3_6frontier t3_6all
theorem t3_7choices : plan636.choices=[0,2,2].map (options 3 0) := by rfl


theorem t3_7part0 : t3_7jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_7frontier : t3_7root.frontier 0=t3_7jobs := by rfl
theorem t3_7all : t3_7jobs.all (Job.check tree)=true := by
  simp only [t3_7jobs,List.all_append,List.all_nil,t3_7part0,Bool.and_self]
theorem t3_7checked : Checked tree [0,2,2] := by
  refine ⟨plan636,valid636,t3_7choices,?_⟩
  exact check_of_frontier tree 0 t3_7root t3_7jobs t3_7frontier t3_7all
theorem t3_8choices : plan637.choices=[0,2,3].map (options 3 0) := by rfl


theorem t3_8part0 : t3_8jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_8frontier : t3_8root.frontier 0=t3_8jobs := by rfl
theorem t3_8all : t3_8jobs.all (Job.check tree)=true := by
  simp only [t3_8jobs,List.all_append,List.all_nil,t3_8part0,Bool.and_self]
theorem t3_8checked : Checked tree [0,2,3] := by
  refine ⟨plan637,valid637,t3_8choices,?_⟩
  exact check_of_frontier tree 0 t3_8root t3_8jobs t3_8frontier t3_8all
theorem t3_9choices : plan654.choices=[0,2,5].map (options 3 1) := by rfl


theorem t3_9part0 : t3_9jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_9frontier : t3_9root.frontier 0=t3_9jobs := by rfl
theorem t3_9all : t3_9jobs.all (Job.check tree)=true := by
  simp only [t3_9jobs,List.all_append,List.all_nil,t3_9part0,Bool.and_self]
theorem t3_9checked : Checked tree [0,2,5] := by
  refine ⟨plan654,valid654,t3_9choices,?_⟩
  exact check_of_frontier tree 0 t3_9root t3_9jobs t3_9frontier t3_9all
theorem t3_10choices : plan655.choices=[0,2,6].map (options 3 1) := by rfl


theorem t3_10part0 : t3_10jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_10frontier : t3_10root.frontier 0=t3_10jobs := by rfl
theorem t3_10all : t3_10jobs.all (Job.check tree)=true := by
  simp only [t3_10jobs,List.all_append,List.all_nil,t3_10part0,Bool.and_self]
theorem t3_10checked : Checked tree [0,2,6] := by
  refine ⟨plan655,valid655,t3_10choices,?_⟩
  exact check_of_frontier tree 0 t3_10root t3_10jobs t3_10frontier t3_10all
theorem t3_11choices : plan656.choices=[0,2,7].map (options 3 1) := by rfl


theorem t3_11part0 : t3_11jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_11frontier : t3_11root.frontier 0=t3_11jobs := by rfl
theorem t3_11all : t3_11jobs.all (Job.check tree)=true := by
  simp only [t3_11jobs,List.all_append,List.all_nil,t3_11part0,Bool.and_self]
theorem t3_11checked : Checked tree [0,2,7] := by
  refine ⟨plan656,valid656,t3_11choices,?_⟩
  exact check_of_frontier tree 0 t3_11root t3_11jobs t3_11frontier t3_11all
theorem t3_12choices : plan657.choices=[0,2,9].map (options 3 1) := by rfl


theorem t3_12part0 : t3_12jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_12frontier : t3_12root.frontier 0=t3_12jobs := by rfl
theorem t3_12all : t3_12jobs.all (Job.check tree)=true := by
  simp only [t3_12jobs,List.all_append,List.all_nil,t3_12part0,Bool.and_self]
theorem t3_12checked : Checked tree [0,2,9] := by
  refine ⟨plan657,valid657,t3_12choices,?_⟩
  exact check_of_frontier tree 0 t3_12root t3_12jobs t3_12frontier t3_12all
theorem t3_13choices : plan658.choices=[0,2,10].map (options 3 1) := by rfl


theorem t3_13part0 : t3_13jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_13frontier : t3_13root.frontier 0=t3_13jobs := by rfl
theorem t3_13all : t3_13jobs.all (Job.check tree)=true := by
  simp only [t3_13jobs,List.all_append,List.all_nil,t3_13part0,Bool.and_self]
theorem t3_13checked : Checked tree [0,2,10] := by
  refine ⟨plan658,valid658,t3_13choices,?_⟩
  exact check_of_frontier tree 0 t3_13root t3_13jobs t3_13frontier t3_13all
theorem t3_14choices : plan638.choices=[0,3,3].map (options 3 0) := by rfl


theorem t3_14part0 : t3_14jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_14frontier : t3_14root.frontier 0=t3_14jobs := by rfl
theorem t3_14all : t3_14jobs.all (Job.check tree)=true := by
  simp only [t3_14jobs,List.all_append,List.all_nil,t3_14part0,Bool.and_self]
theorem t3_14checked : Checked tree [0,3,3] := by
  refine ⟨plan638,valid638,t3_14choices,?_⟩
  exact check_of_frontier tree 0 t3_14root t3_14jobs t3_14frontier t3_14all
theorem t3_15choices : plan659.choices=[0,3,6].map (options 3 1) := by rfl


theorem t3_15part0 : t3_15jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_15frontier : t3_15root.frontier 0=t3_15jobs := by rfl
theorem t3_15all : t3_15jobs.all (Job.check tree)=true := by
  simp only [t3_15jobs,List.all_append,List.all_nil,t3_15part0,Bool.and_self]
theorem t3_15checked : Checked tree [0,3,6] := by
  refine ⟨plan659,valid659,t3_15choices,?_⟩
  exact check_of_frontier tree 0 t3_15root t3_15jobs t3_15frontier t3_15all
theorem t3_16choices : plan660.choices=[0,3,7].map (options 3 1) := by rfl


theorem t3_16part0 : t3_16jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_16frontier : t3_16root.frontier 0=t3_16jobs := by rfl
theorem t3_16all : t3_16jobs.all (Job.check tree)=true := by
  simp only [t3_16jobs,List.all_append,List.all_nil,t3_16part0,Bool.and_self]
theorem t3_16checked : Checked tree [0,3,7] := by
  refine ⟨plan660,valid660,t3_16choices,?_⟩
  exact check_of_frontier tree 0 t3_16root t3_16jobs t3_16frontier t3_16all
theorem t3_17choices : plan661.choices=[0,3,10].map (options 3 1) := by rfl


theorem t3_17part0 : t3_17jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_17frontier : t3_17root.frontier 0=t3_17jobs := by rfl
theorem t3_17all : t3_17jobs.all (Job.check tree)=true := by
  simp only [t3_17jobs,List.all_append,List.all_nil,t3_17part0,Bool.and_self]
theorem t3_17checked : Checked tree [0,3,10] := by
  refine ⟨plan661,valid661,t3_17choices,?_⟩
  exact check_of_frontier tree 0 t3_17root t3_17jobs t3_17frontier t3_17all
theorem t3_18choices : plan662.choices=[0,4,2].map (options 3 1) := by rfl


theorem t3_18part0 : t3_18jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_18frontier : t3_18root.frontier 0=t3_18jobs := by rfl
theorem t3_18all : t3_18jobs.all (Job.check tree)=true := by
  simp only [t3_18jobs,List.all_append,List.all_nil,t3_18part0,Bool.and_self]
theorem t3_18checked : Checked tree [0,4,2] := by
  refine ⟨plan662,valid662,t3_18choices,?_⟩
  exact check_of_frontier tree 0 t3_18root t3_18jobs t3_18frontier t3_18all
theorem t3_19choices : plan663.choices=[0,4,3].map (options 3 1) := by rfl


theorem t3_19part0 : t3_19jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_19frontier : t3_19root.frontier 0=t3_19jobs := by rfl
theorem t3_19all : t3_19jobs.all (Job.check tree)=true := by
  simp only [t3_19jobs,List.all_append,List.all_nil,t3_19part0,Bool.and_self]
theorem t3_19checked : Checked tree [0,4,3] := by
  refine ⟨plan663,valid663,t3_19choices,?_⟩
  exact check_of_frontier tree 0 t3_19root t3_19jobs t3_19frontier t3_19all
theorem t3_20choices : plan710.choices=[0,4,5].map (options 3 2) := by rfl


theorem t3_20part0 : t3_20jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_20frontier : t3_20root.frontier 0=t3_20jobs := by rfl
theorem t3_20all : t3_20jobs.all (Job.check tree)=true := by
  simp only [t3_20jobs,List.all_append,List.all_nil,t3_20part0,Bool.and_self]
theorem t3_20checked : Checked tree [0,4,5] := by
  refine ⟨plan710,valid710,t3_20choices,?_⟩
  exact check_of_frontier tree 0 t3_20root t3_20jobs t3_20frontier t3_20all
theorem t3_21choices : plan711.choices=[0,4,6].map (options 3 2) := by rfl


theorem t3_21part0 : t3_21jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_21frontier : t3_21root.frontier 0=t3_21jobs := by rfl
theorem t3_21all : t3_21jobs.all (Job.check tree)=true := by
  simp only [t3_21jobs,List.all_append,List.all_nil,t3_21part0,Bool.and_self]
theorem t3_21checked : Checked tree [0,4,6] := by
  refine ⟨plan711,valid711,t3_21choices,?_⟩
  exact check_of_frontier tree 0 t3_21root t3_21jobs t3_21frontier t3_21all
theorem t3_22choices : plan712.choices=[0,4,7].map (options 3 2) := by rfl


theorem t3_22part0 : t3_22jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_22frontier : t3_22root.frontier 0=t3_22jobs := by rfl
theorem t3_22all : t3_22jobs.all (Job.check tree)=true := by
  simp only [t3_22jobs,List.all_append,List.all_nil,t3_22part0,Bool.and_self]
theorem t3_22checked : Checked tree [0,4,7] := by
  refine ⟨plan712,valid712,t3_22choices,?_⟩
  exact check_of_frontier tree 0 t3_22root t3_22jobs t3_22frontier t3_22all
theorem t3_23choices : plan713.choices=[0,4,9].map (options 3 2) := by rfl


theorem t3_23part0 : t3_23jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_23frontier : t3_23root.frontier 0=t3_23jobs := by rfl
theorem t3_23all : t3_23jobs.all (Job.check tree)=true := by
  simp only [t3_23jobs,List.all_append,List.all_nil,t3_23part0,Bool.and_self]
theorem t3_23checked : Checked tree [0,4,9] := by
  refine ⟨plan713,valid713,t3_23choices,?_⟩
  exact check_of_frontier tree 0 t3_23root t3_23jobs t3_23frontier t3_23all
theorem t3_24choices : plan714.choices=[0,4,10].map (options 3 2) := by rfl


theorem t3_24part0 : t3_24jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_24frontier : t3_24root.frontier 0=t3_24jobs := by rfl
theorem t3_24all : t3_24jobs.all (Job.check tree)=true := by
  simp only [t3_24jobs,List.all_append,List.all_nil,t3_24part0,Bool.and_self]
theorem t3_24checked : Checked tree [0,4,10] := by
  refine ⟨plan714,valid714,t3_24choices,?_⟩
  exact check_of_frontier tree 0 t3_24root t3_24jobs t3_24frontier t3_24all
theorem t3_25choices : plan664.choices=[0,5,3].map (options 3 1) := by rfl


theorem t3_25part0 : t3_25jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_25frontier : t3_25root.frontier 0=t3_25jobs := by rfl
theorem t3_25all : t3_25jobs.all (Job.check tree)=true := by
  simp only [t3_25jobs,List.all_append,List.all_nil,t3_25part0,Bool.and_self]
theorem t3_25checked : Checked tree [0,5,3] := by
  refine ⟨plan664,valid664,t3_25choices,?_⟩
  exact check_of_frontier tree 0 t3_25root t3_25jobs t3_25frontier t3_25all
theorem t3_26choices : plan715.choices=[0,5,5].map (options 3 2) := by rfl


theorem t3_26part0 : t3_26jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_26frontier : t3_26root.frontier 0=t3_26jobs := by rfl
theorem t3_26all : t3_26jobs.all (Job.check tree)=true := by
  simp only [t3_26jobs,List.all_append,List.all_nil,t3_26part0,Bool.and_self]
theorem t3_26checked : Checked tree [0,5,5] := by
  refine ⟨plan715,valid715,t3_26choices,?_⟩
  exact check_of_frontier tree 0 t3_26root t3_26jobs t3_26frontier t3_26all
theorem t3_27choices : plan716.choices=[0,5,6].map (options 3 2) := by rfl


theorem t3_27part0 : t3_27jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_27frontier : t3_27root.frontier 0=t3_27jobs := by rfl
theorem t3_27all : t3_27jobs.all (Job.check tree)=true := by
  simp only [t3_27jobs,List.all_append,List.all_nil,t3_27part0,Bool.and_self]
theorem t3_27checked : Checked tree [0,5,6] := by
  refine ⟨plan716,valid716,t3_27choices,?_⟩
  exact check_of_frontier tree 0 t3_27root t3_27jobs t3_27frontier t3_27all
theorem t3_28choices : plan717.choices=[0,5,7].map (options 3 2) := by rfl


theorem t3_28part0 : t3_28jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_28frontier : t3_28root.frontier 0=t3_28jobs := by rfl
theorem t3_28all : t3_28jobs.all (Job.check tree)=true := by
  simp only [t3_28jobs,List.all_append,List.all_nil,t3_28part0,Bool.and_self]
theorem t3_28checked : Checked tree [0,5,7] := by
  refine ⟨plan717,valid717,t3_28choices,?_⟩
  exact check_of_frontier tree 0 t3_28root t3_28jobs t3_28frontier t3_28all
theorem t3_29choices : plan718.choices=[0,5,9].map (options 3 2) := by rfl


theorem t3_29part0 : t3_29jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_29frontier : t3_29root.frontier 0=t3_29jobs := by rfl
theorem t3_29all : t3_29jobs.all (Job.check tree)=true := by
  simp only [t3_29jobs,List.all_append,List.all_nil,t3_29part0,Bool.and_self]
theorem t3_29checked : Checked tree [0,5,9] := by
  refine ⟨plan718,valid718,t3_29choices,?_⟩
  exact check_of_frontier tree 0 t3_29root t3_29jobs t3_29frontier t3_29all
theorem t3_30choices : plan719.choices=[0,5,10].map (options 3 2) := by rfl


theorem t3_30part0 : t3_30jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_30frontier : t3_30root.frontier 0=t3_30jobs := by rfl
theorem t3_30all : t3_30jobs.all (Job.check tree)=true := by
  simp only [t3_30jobs,List.all_append,List.all_nil,t3_30part0,Bool.and_self]
theorem t3_30checked : Checked tree [0,5,10] := by
  refine ⟨plan719,valid719,t3_30choices,?_⟩
  exact check_of_frontier tree 0 t3_30root t3_30jobs t3_30frontier t3_30all
theorem t3_31choices : plan720.choices=[0,6,6].map (options 3 2) := by rfl


theorem t3_31part0 : t3_31jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_31frontier : t3_31root.frontier 0=t3_31jobs := by rfl
theorem t3_31all : t3_31jobs.all (Job.check tree)=true := by
  simp only [t3_31jobs,List.all_append,List.all_nil,t3_31part0,Bool.and_self]
theorem t3_31checked : Checked tree [0,6,6] := by
  refine ⟨plan720,valid720,t3_31choices,?_⟩
  exact check_of_frontier tree 0 t3_31root t3_31jobs t3_31frontier t3_31all
theorem t3_32choices : plan721.choices=[0,6,7].map (options 3 2) := by rfl


theorem t3_32part0 : t3_32jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_32frontier : t3_32root.frontier 0=t3_32jobs := by rfl
theorem t3_32all : t3_32jobs.all (Job.check tree)=true := by
  simp only [t3_32jobs,List.all_append,List.all_nil,t3_32part0,Bool.and_self]
theorem t3_32checked : Checked tree [0,6,7] := by
  refine ⟨plan721,valid721,t3_32choices,?_⟩
  exact check_of_frontier tree 0 t3_32root t3_32jobs t3_32frontier t3_32all
theorem t3_33choices : plan722.choices=[0,6,10].map (options 3 2) := by rfl


theorem t3_33part0 : t3_33jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_33frontier : t3_33root.frontier 0=t3_33jobs := by rfl
theorem t3_33all : t3_33jobs.all (Job.check tree)=true := by
  simp only [t3_33jobs,List.all_append,List.all_nil,t3_33part0,Bool.and_self]
theorem t3_33checked : Checked tree [0,6,10] := by
  refine ⟨plan722,valid722,t3_33choices,?_⟩
  exact check_of_frontier tree 0 t3_33root t3_33jobs t3_33frontier t3_33all
theorem t3_34choices : plan723.choices=[0,7,7].map (options 3 2) := by rfl


theorem t3_34part0 : t3_34jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_34frontier : t3_34root.frontier 0=t3_34jobs := by rfl
theorem t3_34all : t3_34jobs.all (Job.check tree)=true := by
  simp only [t3_34jobs,List.all_append,List.all_nil,t3_34part0,Bool.and_self]
theorem t3_34checked : Checked tree [0,7,7] := by
  refine ⟨plan723,valid723,t3_34choices,?_⟩
  exact check_of_frontier tree 0 t3_34root t3_34jobs t3_34frontier t3_34all
theorem t3_35choices : plan665.choices=[0,8,2].map (options 3 1) := by rfl


theorem t3_35part0 : t3_35jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_35frontier : t3_35root.frontier 0=t3_35jobs := by rfl
theorem t3_35all : t3_35jobs.all (Job.check tree)=true := by
  simp only [t3_35jobs,List.all_append,List.all_nil,t3_35part0,Bool.and_self]
theorem t3_35checked : Checked tree [0,8,2] := by
  refine ⟨plan665,valid665,t3_35choices,?_⟩
  exact check_of_frontier tree 0 t3_35root t3_35jobs t3_35frontier t3_35all
theorem t3_36choices : plan666.choices=[0,8,3].map (options 3 1) := by rfl


theorem t3_36part0 : t3_36jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_36frontier : t3_36root.frontier 0=t3_36jobs := by rfl
theorem t3_36all : t3_36jobs.all (Job.check tree)=true := by
  simp only [t3_36jobs,List.all_append,List.all_nil,t3_36part0,Bool.and_self]
theorem t3_36checked : Checked tree [0,8,3] := by
  refine ⟨plan666,valid666,t3_36choices,?_⟩
  exact check_of_frontier tree 0 t3_36root t3_36jobs t3_36frontier t3_36all
theorem t3_37choices : plan724.choices=[0,8,5].map (options 3 2) := by rfl


theorem t3_37part0 : t3_37jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_37frontier : t3_37root.frontier 0=t3_37jobs := by rfl
theorem t3_37all : t3_37jobs.all (Job.check tree)=true := by
  simp only [t3_37jobs,List.all_append,List.all_nil,t3_37part0,Bool.and_self]
theorem t3_37checked : Checked tree [0,8,5] := by
  refine ⟨plan724,valid724,t3_37choices,?_⟩
  exact check_of_frontier tree 0 t3_37root t3_37jobs t3_37frontier t3_37all
theorem t3_38choices : plan725.choices=[0,8,6].map (options 3 2) := by rfl


theorem t3_38part0 : t3_38jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_38frontier : t3_38root.frontier 0=t3_38jobs := by rfl
theorem t3_38all : t3_38jobs.all (Job.check tree)=true := by
  simp only [t3_38jobs,List.all_append,List.all_nil,t3_38part0,Bool.and_self]
theorem t3_38checked : Checked tree [0,8,6] := by
  refine ⟨plan725,valid725,t3_38choices,?_⟩
  exact check_of_frontier tree 0 t3_38root t3_38jobs t3_38frontier t3_38all
theorem t3_39choices : plan726.choices=[0,8,7].map (options 3 2) := by rfl


theorem t3_39part0 : t3_39jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_39frontier : t3_39root.frontier 0=t3_39jobs := by rfl
theorem t3_39all : t3_39jobs.all (Job.check tree)=true := by
  simp only [t3_39jobs,List.all_append,List.all_nil,t3_39part0,Bool.and_self]
theorem t3_39checked : Checked tree [0,8,7] := by
  refine ⟨plan726,valid726,t3_39choices,?_⟩
  exact check_of_frontier tree 0 t3_39root t3_39jobs t3_39frontier t3_39all
theorem t3_40choices : plan727.choices=[0,8,9].map (options 3 2) := by rfl


theorem t3_40part0 : t3_40jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_40frontier : t3_40root.frontier 0=t3_40jobs := by rfl
theorem t3_40all : t3_40jobs.all (Job.check tree)=true := by
  simp only [t3_40jobs,List.all_append,List.all_nil,t3_40part0,Bool.and_self]
theorem t3_40checked : Checked tree [0,8,9] := by
  refine ⟨plan727,valid727,t3_40choices,?_⟩
  exact check_of_frontier tree 0 t3_40root t3_40jobs t3_40frontier t3_40all
theorem t3_41choices : plan728.choices=[0,8,10].map (options 3 2) := by rfl


theorem t3_41part0 : t3_41jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_41frontier : t3_41root.frontier 0=t3_41jobs := by rfl
theorem t3_41all : t3_41jobs.all (Job.check tree)=true := by
  simp only [t3_41jobs,List.all_append,List.all_nil,t3_41part0,Bool.and_self]
theorem t3_41checked : Checked tree [0,8,10] := by
  refine ⟨plan728,valid728,t3_41choices,?_⟩
  exact check_of_frontier tree 0 t3_41root t3_41jobs t3_41frontier t3_41all
theorem t3_42choices : plan667.choices=[0,9,3].map (options 3 1) := by rfl


theorem t3_42part0 : t3_42jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_42frontier : t3_42root.frontier 0=t3_42jobs := by rfl
theorem t3_42all : t3_42jobs.all (Job.check tree)=true := by
  simp only [t3_42jobs,List.all_append,List.all_nil,t3_42part0,Bool.and_self]
theorem t3_42checked : Checked tree [0,9,3] := by
  refine ⟨plan667,valid667,t3_42choices,?_⟩
  exact check_of_frontier tree 0 t3_42root t3_42jobs t3_42frontier t3_42all
theorem t3_43choices : plan729.choices=[0,9,6].map (options 3 2) := by rfl


theorem t3_43part0 : t3_43jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_43frontier : t3_43root.frontier 0=t3_43jobs := by rfl
theorem t3_43all : t3_43jobs.all (Job.check tree)=true := by
  simp only [t3_43jobs,List.all_append,List.all_nil,t3_43part0,Bool.and_self]
theorem t3_43checked : Checked tree [0,9,6] := by
  refine ⟨plan729,valid729,t3_43choices,?_⟩
  exact check_of_frontier tree 0 t3_43root t3_43jobs t3_43frontier t3_43all
theorem t3_44choices : plan730.choices=[0,9,7].map (options 3 2) := by rfl


theorem t3_44part0 : t3_44jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_44frontier : t3_44root.frontier 0=t3_44jobs := by rfl
theorem t3_44all : t3_44jobs.all (Job.check tree)=true := by
  simp only [t3_44jobs,List.all_append,List.all_nil,t3_44part0,Bool.and_self]
theorem t3_44checked : Checked tree [0,9,7] := by
  refine ⟨plan730,valid730,t3_44choices,?_⟩
  exact check_of_frontier tree 0 t3_44root t3_44jobs t3_44frontier t3_44all
theorem t3_45choices : plan731.choices=[0,9,9].map (options 3 2) := by rfl


theorem t3_45part0 : t3_45jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_45frontier : t3_45root.frontier 0=t3_45jobs := by rfl
theorem t3_45all : t3_45jobs.all (Job.check tree)=true := by
  simp only [t3_45jobs,List.all_append,List.all_nil,t3_45part0,Bool.and_self]
theorem t3_45checked : Checked tree [0,9,9] := by
  refine ⟨plan731,valid731,t3_45choices,?_⟩
  exact check_of_frontier tree 0 t3_45root t3_45jobs t3_45frontier t3_45all
theorem t3_46choices : plan732.choices=[0,9,10].map (options 3 2) := by rfl


theorem t3_46part0 : t3_46jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_46frontier : t3_46root.frontier 0=t3_46jobs := by rfl
theorem t3_46all : t3_46jobs.all (Job.check tree)=true := by
  simp only [t3_46jobs,List.all_append,List.all_nil,t3_46part0,Bool.and_self]
theorem t3_46checked : Checked tree [0,9,10] := by
  refine ⟨plan732,valid732,t3_46choices,?_⟩
  exact check_of_frontier tree 0 t3_46root t3_46jobs t3_46frontier t3_46all
theorem t3_47choices : plan733.choices=[0,10,7].map (options 3 2) := by rfl


theorem t3_47part0 : t3_47jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_47frontier : t3_47root.frontier 0=t3_47jobs := by rfl
theorem t3_47all : t3_47jobs.all (Job.check tree)=true := by
  simp only [t3_47jobs,List.all_append,List.all_nil,t3_47part0,Bool.and_self]
theorem t3_47checked : Checked tree [0,10,7] := by
  refine ⟨plan733,valid733,t3_47choices,?_⟩
  exact check_of_frontier tree 0 t3_47root t3_47jobs t3_47frontier t3_47all
theorem t3_48choices : plan734.choices=[0,10,10].map (options 3 2) := by rfl


theorem t3_48part0 : t3_48jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_48frontier : t3_48root.frontier 0=t3_48jobs := by rfl
theorem t3_48all : t3_48jobs.all (Job.check tree)=true := by
  simp only [t3_48jobs,List.all_append,List.all_nil,t3_48part0,Bool.and_self]
theorem t3_48checked : Checked tree [0,10,10] := by
  refine ⟨plan734,valid734,t3_48choices,?_⟩
  exact check_of_frontier tree 0 t3_48root t3_48jobs t3_48frontier t3_48all
theorem t3_49choices : plan639.choices=[1,1,1].map (options 3 0) := by rfl


theorem t3_49part0 : t3_49jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_49frontier : t3_49root.frontier 0=t3_49jobs := by rfl
theorem t3_49all : t3_49jobs.all (Job.check tree)=true := by
  simp only [t3_49jobs,List.all_append,List.all_nil,t3_49part0,Bool.and_self]
theorem t3_49checked : Checked tree [1,1,1] := by
  refine ⟨plan639,valid639,t3_49choices,?_⟩
  exact check_of_frontier tree 0 t3_49root t3_49jobs t3_49frontier t3_49all
theorem t3_50choices : plan640.choices=[1,1,2].map (options 3 0) := by rfl


theorem t3_50part0 : t3_50jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_50frontier : t3_50root.frontier 0=t3_50jobs := by rfl
theorem t3_50all : t3_50jobs.all (Job.check tree)=true := by
  simp only [t3_50jobs,List.all_append,List.all_nil,t3_50part0,Bool.and_self]
theorem t3_50checked : Checked tree [1,1,2] := by
  refine ⟨plan640,valid640,t3_50choices,?_⟩
  exact check_of_frontier tree 0 t3_50root t3_50jobs t3_50frontier t3_50all
theorem t3_51choices : plan641.choices=[1,1,3].map (options 3 0) := by rfl


theorem t3_51part0 : t3_51jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_51frontier : t3_51root.frontier 0=t3_51jobs := by rfl
theorem t3_51all : t3_51jobs.all (Job.check tree)=true := by
  simp only [t3_51jobs,List.all_append,List.all_nil,t3_51part0,Bool.and_self]
theorem t3_51checked : Checked tree [1,1,3] := by
  refine ⟨plan641,valid641,t3_51choices,?_⟩
  exact check_of_frontier tree 0 t3_51root t3_51jobs t3_51frontier t3_51all
theorem t3_52choices : plan668.choices=[1,1,4].map (options 3 1) := by rfl


theorem t3_52part0 : t3_52jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_52frontier : t3_52root.frontier 0=t3_52jobs := by rfl
theorem t3_52all : t3_52jobs.all (Job.check tree)=true := by
  simp only [t3_52jobs,List.all_append,List.all_nil,t3_52part0,Bool.and_self]
theorem t3_52checked : Checked tree [1,1,4] := by
  refine ⟨plan668,valid668,t3_52choices,?_⟩
  exact check_of_frontier tree 0 t3_52root t3_52jobs t3_52frontier t3_52all
theorem t3_53choices : plan669.choices=[1,1,5].map (options 3 1) := by rfl


theorem t3_53part0 : t3_53jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_53frontier : t3_53root.frontier 0=t3_53jobs := by rfl
theorem t3_53all : t3_53jobs.all (Job.check tree)=true := by
  simp only [t3_53jobs,List.all_append,List.all_nil,t3_53part0,Bool.and_self]
theorem t3_53checked : Checked tree [1,1,5] := by
  refine ⟨plan669,valid669,t3_53choices,?_⟩
  exact check_of_frontier tree 0 t3_53root t3_53jobs t3_53frontier t3_53all
theorem t3_54choices : plan670.choices=[1,1,6].map (options 3 1) := by rfl


theorem t3_54part0 : t3_54jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_54frontier : t3_54root.frontier 0=t3_54jobs := by rfl
theorem t3_54all : t3_54jobs.all (Job.check tree)=true := by
  simp only [t3_54jobs,List.all_append,List.all_nil,t3_54part0,Bool.and_self]
theorem t3_54checked : Checked tree [1,1,6] := by
  refine ⟨plan670,valid670,t3_54choices,?_⟩
  exact check_of_frontier tree 0 t3_54root t3_54jobs t3_54frontier t3_54all
theorem t3_55choices : plan671.choices=[1,1,7].map (options 3 1) := by rfl


theorem t3_55part0 : t3_55jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_55frontier : t3_55root.frontier 0=t3_55jobs := by rfl
theorem t3_55all : t3_55jobs.all (Job.check tree)=true := by
  simp only [t3_55jobs,List.all_append,List.all_nil,t3_55part0,Bool.and_self]
theorem t3_55checked : Checked tree [1,1,7] := by
  refine ⟨plan671,valid671,t3_55choices,?_⟩
  exact check_of_frontier tree 0 t3_55root t3_55jobs t3_55frontier t3_55all
theorem t3_56choices : plan672.choices=[1,1,8].map (options 3 1) := by rfl


theorem t3_56part0 : t3_56jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_56frontier : t3_56root.frontier 0=t3_56jobs := by rfl
theorem t3_56all : t3_56jobs.all (Job.check tree)=true := by
  simp only [t3_56jobs,List.all_append,List.all_nil,t3_56part0,Bool.and_self]
theorem t3_56checked : Checked tree [1,1,8] := by
  refine ⟨plan672,valid672,t3_56choices,?_⟩
  exact check_of_frontier tree 0 t3_56root t3_56jobs t3_56frontier t3_56all
theorem t3_57choices : plan673.choices=[1,1,9].map (options 3 1) := by rfl


theorem t3_57part0 : t3_57jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_57frontier : t3_57root.frontier 0=t3_57jobs := by rfl
theorem t3_57all : t3_57jobs.all (Job.check tree)=true := by
  simp only [t3_57jobs,List.all_append,List.all_nil,t3_57part0,Bool.and_self]
theorem t3_57checked : Checked tree [1,1,9] := by
  refine ⟨plan673,valid673,t3_57choices,?_⟩
  exact check_of_frontier tree 0 t3_57root t3_57jobs t3_57frontier t3_57all
theorem t3_58choices : plan674.choices=[1,1,10].map (options 3 1) := by rfl


theorem t3_58part0 : t3_58jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_58frontier : t3_58root.frontier 0=t3_58jobs := by rfl
theorem t3_58all : t3_58jobs.all (Job.check tree)=true := by
  simp only [t3_58jobs,List.all_append,List.all_nil,t3_58part0,Bool.and_self]
theorem t3_58checked : Checked tree [1,1,10] := by
  refine ⟨plan674,valid674,t3_58choices,?_⟩
  exact check_of_frontier tree 0 t3_58root t3_58jobs t3_58frontier t3_58all
theorem t3_59choices : plan642.choices=[1,2,2].map (options 3 0) := by rfl


theorem t3_59part0 : t3_59jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_59frontier : t3_59root.frontier 0=t3_59jobs := by rfl
theorem t3_59all : t3_59jobs.all (Job.check tree)=true := by
  simp only [t3_59jobs,List.all_append,List.all_nil,t3_59part0,Bool.and_self]
theorem t3_59checked : Checked tree [1,2,2] := by
  refine ⟨plan642,valid642,t3_59choices,?_⟩
  exact check_of_frontier tree 0 t3_59root t3_59jobs t3_59frontier t3_59all
theorem t3_60choices : plan643.choices=[1,2,3].map (options 3 0) := by rfl


theorem t3_60part0 : t3_60jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_60frontier : t3_60root.frontier 0=t3_60jobs := by rfl
theorem t3_60all : t3_60jobs.all (Job.check tree)=true := by
  simp only [t3_60jobs,List.all_append,List.all_nil,t3_60part0,Bool.and_self]
theorem t3_60checked : Checked tree [1,2,3] := by
  refine ⟨plan643,valid643,t3_60choices,?_⟩
  exact check_of_frontier tree 0 t3_60root t3_60jobs t3_60frontier t3_60all
theorem t3_61choices : plan675.choices=[1,2,5].map (options 3 1) := by rfl


theorem t3_61part0 : t3_61jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_61frontier : t3_61root.frontier 0=t3_61jobs := by rfl
theorem t3_61all : t3_61jobs.all (Job.check tree)=true := by
  simp only [t3_61jobs,List.all_append,List.all_nil,t3_61part0,Bool.and_self]
theorem t3_61checked : Checked tree [1,2,5] := by
  refine ⟨plan675,valid675,t3_61choices,?_⟩
  exact check_of_frontier tree 0 t3_61root t3_61jobs t3_61frontier t3_61all
theorem t3_62choices : plan676.choices=[1,2,6].map (options 3 1) := by rfl


theorem t3_62part0 : t3_62jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_62frontier : t3_62root.frontier 0=t3_62jobs := by rfl
theorem t3_62all : t3_62jobs.all (Job.check tree)=true := by
  simp only [t3_62jobs,List.all_append,List.all_nil,t3_62part0,Bool.and_self]
theorem t3_62checked : Checked tree [1,2,6] := by
  refine ⟨plan676,valid676,t3_62choices,?_⟩
  exact check_of_frontier tree 0 t3_62root t3_62jobs t3_62frontier t3_62all
theorem t3_63choices : plan677.choices=[1,2,7].map (options 3 1) := by rfl


theorem t3_63part0 : t3_63jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_63frontier : t3_63root.frontier 0=t3_63jobs := by rfl
theorem t3_63all : t3_63jobs.all (Job.check tree)=true := by
  simp only [t3_63jobs,List.all_append,List.all_nil,t3_63part0,Bool.and_self]
theorem t3_63checked : Checked tree [1,2,7] := by
  refine ⟨plan677,valid677,t3_63choices,?_⟩
  exact check_of_frontier tree 0 t3_63root t3_63jobs t3_63frontier t3_63all
theorem t3_64choices : plan678.choices=[1,2,9].map (options 3 1) := by rfl


theorem t3_64part0 : t3_64jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_64frontier : t3_64root.frontier 0=t3_64jobs := by rfl
theorem t3_64all : t3_64jobs.all (Job.check tree)=true := by
  simp only [t3_64jobs,List.all_append,List.all_nil,t3_64part0,Bool.and_self]
theorem t3_64checked : Checked tree [1,2,9] := by
  refine ⟨plan678,valid678,t3_64choices,?_⟩
  exact check_of_frontier tree 0 t3_64root t3_64jobs t3_64frontier t3_64all
theorem t3_65choices : plan679.choices=[1,2,10].map (options 3 1) := by rfl


theorem t3_65part0 : t3_65jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_65frontier : t3_65root.frontier 0=t3_65jobs := by rfl
theorem t3_65all : t3_65jobs.all (Job.check tree)=true := by
  simp only [t3_65jobs,List.all_append,List.all_nil,t3_65part0,Bool.and_self]
theorem t3_65checked : Checked tree [1,2,10] := by
  refine ⟨plan679,valid679,t3_65choices,?_⟩
  exact check_of_frontier tree 0 t3_65root t3_65jobs t3_65frontier t3_65all
theorem t3_66choices : plan644.choices=[1,3,3].map (options 3 0) := by rfl


theorem t3_66part0 : t3_66jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_66frontier : t3_66root.frontier 0=t3_66jobs := by rfl
theorem t3_66all : t3_66jobs.all (Job.check tree)=true := by
  simp only [t3_66jobs,List.all_append,List.all_nil,t3_66part0,Bool.and_self]
theorem t3_66checked : Checked tree [1,3,3] := by
  refine ⟨plan644,valid644,t3_66choices,?_⟩
  exact check_of_frontier tree 0 t3_66root t3_66jobs t3_66frontier t3_66all
theorem t3_67choices : plan680.choices=[1,3,6].map (options 3 1) := by rfl


theorem t3_67part0 : t3_67jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_67frontier : t3_67root.frontier 0=t3_67jobs := by rfl
theorem t3_67all : t3_67jobs.all (Job.check tree)=true := by
  simp only [t3_67jobs,List.all_append,List.all_nil,t3_67part0,Bool.and_self]
theorem t3_67checked : Checked tree [1,3,6] := by
  refine ⟨plan680,valid680,t3_67choices,?_⟩
  exact check_of_frontier tree 0 t3_67root t3_67jobs t3_67frontier t3_67all
theorem t3_68choices : plan681.choices=[1,3,7].map (options 3 1) := by rfl


theorem t3_68part0 : t3_68jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_68frontier : t3_68root.frontier 0=t3_68jobs := by rfl
theorem t3_68all : t3_68jobs.all (Job.check tree)=true := by
  simp only [t3_68jobs,List.all_append,List.all_nil,t3_68part0,Bool.and_self]
theorem t3_68checked : Checked tree [1,3,7] := by
  refine ⟨plan681,valid681,t3_68choices,?_⟩
  exact check_of_frontier tree 0 t3_68root t3_68jobs t3_68frontier t3_68all
theorem t3_69choices : plan682.choices=[1,3,10].map (options 3 1) := by rfl


theorem t3_69part0 : t3_69jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_69frontier : t3_69root.frontier 0=t3_69jobs := by rfl
theorem t3_69all : t3_69jobs.all (Job.check tree)=true := by
  simp only [t3_69jobs,List.all_append,List.all_nil,t3_69part0,Bool.and_self]
theorem t3_69checked : Checked tree [1,3,10] := by
  refine ⟨plan682,valid682,t3_69choices,?_⟩
  exact check_of_frontier tree 0 t3_69root t3_69jobs t3_69frontier t3_69all
theorem t3_70choices : plan683.choices=[1,4,2].map (options 3 1) := by rfl


theorem t3_70part0 : t3_70jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_70frontier : t3_70root.frontier 0=t3_70jobs := by rfl
theorem t3_70all : t3_70jobs.all (Job.check tree)=true := by
  simp only [t3_70jobs,List.all_append,List.all_nil,t3_70part0,Bool.and_self]
theorem t3_70checked : Checked tree [1,4,2] := by
  refine ⟨plan683,valid683,t3_70choices,?_⟩
  exact check_of_frontier tree 0 t3_70root t3_70jobs t3_70frontier t3_70all
theorem t3_71choices : plan684.choices=[1,4,3].map (options 3 1) := by rfl


theorem t3_71part0 : t3_71jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_71frontier : t3_71root.frontier 0=t3_71jobs := by rfl
theorem t3_71all : t3_71jobs.all (Job.check tree)=true := by
  simp only [t3_71jobs,List.all_append,List.all_nil,t3_71part0,Bool.and_self]
theorem t3_71checked : Checked tree [1,4,3] := by
  refine ⟨plan684,valid684,t3_71choices,?_⟩
  exact check_of_frontier tree 0 t3_71root t3_71jobs t3_71frontier t3_71all
theorem t3_72choices : plan735.choices=[1,4,4].map (options 3 2) := by rfl


theorem t3_72part0 : t3_72jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_72frontier : t3_72root.frontier 0=t3_72jobs := by rfl
theorem t3_72all : t3_72jobs.all (Job.check tree)=true := by
  simp only [t3_72jobs,List.all_append,List.all_nil,t3_72part0,Bool.and_self]
theorem t3_72checked : Checked tree [1,4,4] := by
  refine ⟨plan735,valid735,t3_72choices,?_⟩
  exact check_of_frontier tree 0 t3_72root t3_72jobs t3_72frontier t3_72all
theorem t3_73choices : plan736.choices=[1,4,5].map (options 3 2) := by rfl


theorem t3_73part0 : t3_73jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_73frontier : t3_73root.frontier 0=t3_73jobs := by rfl
theorem t3_73all : t3_73jobs.all (Job.check tree)=true := by
  simp only [t3_73jobs,List.all_append,List.all_nil,t3_73part0,Bool.and_self]
theorem t3_73checked : Checked tree [1,4,5] := by
  refine ⟨plan736,valid736,t3_73choices,?_⟩
  exact check_of_frontier tree 0 t3_73root t3_73jobs t3_73frontier t3_73all
theorem t3_74choices : plan737.choices=[1,4,6].map (options 3 2) := by rfl


theorem t3_74part0 : t3_74jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_74frontier : t3_74root.frontier 0=t3_74jobs := by rfl
theorem t3_74all : t3_74jobs.all (Job.check tree)=true := by
  simp only [t3_74jobs,List.all_append,List.all_nil,t3_74part0,Bool.and_self]
theorem t3_74checked : Checked tree [1,4,6] := by
  refine ⟨plan737,valid737,t3_74choices,?_⟩
  exact check_of_frontier tree 0 t3_74root t3_74jobs t3_74frontier t3_74all
theorem t3_75choices : plan738.choices=[1,4,7].map (options 3 2) := by rfl


theorem t3_75part0 : t3_75jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_75frontier : t3_75root.frontier 0=t3_75jobs := by rfl
theorem t3_75all : t3_75jobs.all (Job.check tree)=true := by
  simp only [t3_75jobs,List.all_append,List.all_nil,t3_75part0,Bool.and_self]
theorem t3_75checked : Checked tree [1,4,7] := by
  refine ⟨plan738,valid738,t3_75choices,?_⟩
  exact check_of_frontier tree 0 t3_75root t3_75jobs t3_75frontier t3_75all
theorem t3_76choices : plan739.choices=[1,4,8].map (options 3 2) := by rfl


theorem t3_76part0 : t3_76jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_76frontier : t3_76root.frontier 0=t3_76jobs := by rfl
theorem t3_76all : t3_76jobs.all (Job.check tree)=true := by
  simp only [t3_76jobs,List.all_append,List.all_nil,t3_76part0,Bool.and_self]
theorem t3_76checked : Checked tree [1,4,8] := by
  refine ⟨plan739,valid739,t3_76choices,?_⟩
  exact check_of_frontier tree 0 t3_76root t3_76jobs t3_76frontier t3_76all
theorem t3_77choices : plan740.choices=[1,4,9].map (options 3 2) := by rfl


theorem t3_77part0 : t3_77jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_77frontier : t3_77root.frontier 0=t3_77jobs := by rfl
theorem t3_77all : t3_77jobs.all (Job.check tree)=true := by
  simp only [t3_77jobs,List.all_append,List.all_nil,t3_77part0,Bool.and_self]
theorem t3_77checked : Checked tree [1,4,9] := by
  refine ⟨plan740,valid740,t3_77choices,?_⟩
  exact check_of_frontier tree 0 t3_77root t3_77jobs t3_77frontier t3_77all
theorem t3_78choices : plan741.choices=[1,4,10].map (options 3 2) := by rfl


theorem t3_78part0 : t3_78jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_78frontier : t3_78root.frontier 0=t3_78jobs := by rfl
theorem t3_78all : t3_78jobs.all (Job.check tree)=true := by
  simp only [t3_78jobs,List.all_append,List.all_nil,t3_78part0,Bool.and_self]
theorem t3_78checked : Checked tree [1,4,10] := by
  refine ⟨plan741,valid741,t3_78choices,?_⟩
  exact check_of_frontier tree 0 t3_78root t3_78jobs t3_78frontier t3_78all
theorem t3_79choices : plan685.choices=[1,5,3].map (options 3 1) := by rfl


theorem t3_79part0 : t3_79jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_79frontier : t3_79root.frontier 0=t3_79jobs := by rfl
theorem t3_79all : t3_79jobs.all (Job.check tree)=true := by
  simp only [t3_79jobs,List.all_append,List.all_nil,t3_79part0,Bool.and_self]
theorem t3_79checked : Checked tree [1,5,3] := by
  refine ⟨plan685,valid685,t3_79choices,?_⟩
  exact check_of_frontier tree 0 t3_79root t3_79jobs t3_79frontier t3_79all
theorem t3_80choices : plan742.choices=[1,5,5].map (options 3 2) := by rfl


theorem t3_80part0 : t3_80jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_80frontier : t3_80root.frontier 0=t3_80jobs := by rfl
theorem t3_80all : t3_80jobs.all (Job.check tree)=true := by
  simp only [t3_80jobs,List.all_append,List.all_nil,t3_80part0,Bool.and_self]
theorem t3_80checked : Checked tree [1,5,5] := by
  refine ⟨plan742,valid742,t3_80choices,?_⟩
  exact check_of_frontier tree 0 t3_80root t3_80jobs t3_80frontier t3_80all
theorem t3_81choices : plan743.choices=[1,5,6].map (options 3 2) := by rfl


theorem t3_81part0 : t3_81jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_81frontier : t3_81root.frontier 0=t3_81jobs := by rfl
theorem t3_81all : t3_81jobs.all (Job.check tree)=true := by
  simp only [t3_81jobs,List.all_append,List.all_nil,t3_81part0,Bool.and_self]
theorem t3_81checked : Checked tree [1,5,6] := by
  refine ⟨plan743,valid743,t3_81choices,?_⟩
  exact check_of_frontier tree 0 t3_81root t3_81jobs t3_81frontier t3_81all
theorem t3_82choices : plan744.choices=[1,5,7].map (options 3 2) := by rfl


theorem t3_82part0 : t3_82jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_82frontier : t3_82root.frontier 0=t3_82jobs := by rfl
theorem t3_82all : t3_82jobs.all (Job.check tree)=true := by
  simp only [t3_82jobs,List.all_append,List.all_nil,t3_82part0,Bool.and_self]
theorem t3_82checked : Checked tree [1,5,7] := by
  refine ⟨plan744,valid744,t3_82choices,?_⟩
  exact check_of_frontier tree 0 t3_82root t3_82jobs t3_82frontier t3_82all
theorem t3_83choices : plan745.choices=[1,5,9].map (options 3 2) := by rfl


theorem t3_83part0 : t3_83jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_83frontier : t3_83root.frontier 0=t3_83jobs := by rfl
theorem t3_83all : t3_83jobs.all (Job.check tree)=true := by
  simp only [t3_83jobs,List.all_append,List.all_nil,t3_83part0,Bool.and_self]
theorem t3_83checked : Checked tree [1,5,9] := by
  refine ⟨plan745,valid745,t3_83choices,?_⟩
  exact check_of_frontier tree 0 t3_83root t3_83jobs t3_83frontier t3_83all
theorem t3_84choices : plan746.choices=[1,5,10].map (options 3 2) := by rfl


theorem t3_84part0 : t3_84jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_84frontier : t3_84root.frontier 0=t3_84jobs := by rfl
theorem t3_84all : t3_84jobs.all (Job.check tree)=true := by
  simp only [t3_84jobs,List.all_append,List.all_nil,t3_84part0,Bool.and_self]
theorem t3_84checked : Checked tree [1,5,10] := by
  refine ⟨plan746,valid746,t3_84choices,?_⟩
  exact check_of_frontier tree 0 t3_84root t3_84jobs t3_84frontier t3_84all
theorem t3_85choices : plan747.choices=[1,6,6].map (options 3 2) := by rfl


theorem t3_85part0 : t3_85jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_85frontier : t3_85root.frontier 0=t3_85jobs := by rfl
theorem t3_85all : t3_85jobs.all (Job.check tree)=true := by
  simp only [t3_85jobs,List.all_append,List.all_nil,t3_85part0,Bool.and_self]
theorem t3_85checked : Checked tree [1,6,6] := by
  refine ⟨plan747,valid747,t3_85choices,?_⟩
  exact check_of_frontier tree 0 t3_85root t3_85jobs t3_85frontier t3_85all
theorem t3_86choices : plan748.choices=[1,6,7].map (options 3 2) := by rfl


theorem t3_86part0 : t3_86jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_86frontier : t3_86root.frontier 0=t3_86jobs := by rfl
theorem t3_86all : t3_86jobs.all (Job.check tree)=true := by
  simp only [t3_86jobs,List.all_append,List.all_nil,t3_86part0,Bool.and_self]
theorem t3_86checked : Checked tree [1,6,7] := by
  refine ⟨plan748,valid748,t3_86choices,?_⟩
  exact check_of_frontier tree 0 t3_86root t3_86jobs t3_86frontier t3_86all
theorem t3_87choices : plan749.choices=[1,6,10].map (options 3 2) := by rfl


theorem t3_87part0 : t3_87jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_87frontier : t3_87root.frontier 0=t3_87jobs := by rfl
theorem t3_87all : t3_87jobs.all (Job.check tree)=true := by
  simp only [t3_87jobs,List.all_append,List.all_nil,t3_87part0,Bool.and_self]
theorem t3_87checked : Checked tree [1,6,10] := by
  refine ⟨plan749,valid749,t3_87choices,?_⟩
  exact check_of_frontier tree 0 t3_87root t3_87jobs t3_87frontier t3_87all
theorem t3_88choices : plan750.choices=[1,7,7].map (options 3 2) := by rfl


theorem t3_88part0 : t3_88jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_88frontier : t3_88root.frontier 0=t3_88jobs := by rfl
theorem t3_88all : t3_88jobs.all (Job.check tree)=true := by
  simp only [t3_88jobs,List.all_append,List.all_nil,t3_88part0,Bool.and_self]
theorem t3_88checked : Checked tree [1,7,7] := by
  refine ⟨plan750,valid750,t3_88choices,?_⟩
  exact check_of_frontier tree 0 t3_88root t3_88jobs t3_88frontier t3_88all
theorem t3_89choices : plan686.choices=[1,8,2].map (options 3 1) := by rfl


theorem t3_89part0 : t3_89jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_89frontier : t3_89root.frontier 0=t3_89jobs := by rfl
theorem t3_89all : t3_89jobs.all (Job.check tree)=true := by
  simp only [t3_89jobs,List.all_append,List.all_nil,t3_89part0,Bool.and_self]
theorem t3_89checked : Checked tree [1,8,2] := by
  refine ⟨plan686,valid686,t3_89choices,?_⟩
  exact check_of_frontier tree 0 t3_89root t3_89jobs t3_89frontier t3_89all
theorem t3_90choices : plan687.choices=[1,8,3].map (options 3 1) := by rfl


theorem t3_90part0 : t3_90jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_90frontier : t3_90root.frontier 0=t3_90jobs := by rfl
theorem t3_90all : t3_90jobs.all (Job.check tree)=true := by
  simp only [t3_90jobs,List.all_append,List.all_nil,t3_90part0,Bool.and_self]
theorem t3_90checked : Checked tree [1,8,3] := by
  refine ⟨plan687,valid687,t3_90choices,?_⟩
  exact check_of_frontier tree 0 t3_90root t3_90jobs t3_90frontier t3_90all
theorem t3_91choices : plan751.choices=[1,8,5].map (options 3 2) := by rfl


theorem t3_91part0 : t3_91jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_91frontier : t3_91root.frontier 0=t3_91jobs := by rfl
theorem t3_91all : t3_91jobs.all (Job.check tree)=true := by
  simp only [t3_91jobs,List.all_append,List.all_nil,t3_91part0,Bool.and_self]
theorem t3_91checked : Checked tree [1,8,5] := by
  refine ⟨plan751,valid751,t3_91choices,?_⟩
  exact check_of_frontier tree 0 t3_91root t3_91jobs t3_91frontier t3_91all
theorem t3_92choices : plan752.choices=[1,8,6].map (options 3 2) := by rfl


theorem t3_92part0 : t3_92jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_92frontier : t3_92root.frontier 0=t3_92jobs := by rfl
theorem t3_92all : t3_92jobs.all (Job.check tree)=true := by
  simp only [t3_92jobs,List.all_append,List.all_nil,t3_92part0,Bool.and_self]
theorem t3_92checked : Checked tree [1,8,6] := by
  refine ⟨plan752,valid752,t3_92choices,?_⟩
  exact check_of_frontier tree 0 t3_92root t3_92jobs t3_92frontier t3_92all
theorem t3_93choices : plan753.choices=[1,8,7].map (options 3 2) := by rfl


theorem t3_93part0 : t3_93jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_93frontier : t3_93root.frontier 0=t3_93jobs := by rfl
theorem t3_93all : t3_93jobs.all (Job.check tree)=true := by
  simp only [t3_93jobs,List.all_append,List.all_nil,t3_93part0,Bool.and_self]
theorem t3_93checked : Checked tree [1,8,7] := by
  refine ⟨plan753,valid753,t3_93choices,?_⟩
  exact check_of_frontier tree 0 t3_93root t3_93jobs t3_93frontier t3_93all
theorem t3_94choices : plan754.choices=[1,8,8].map (options 3 2) := by rfl


theorem t3_94part0 : t3_94jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_94frontier : t3_94root.frontier 0=t3_94jobs := by rfl
theorem t3_94all : t3_94jobs.all (Job.check tree)=true := by
  simp only [t3_94jobs,List.all_append,List.all_nil,t3_94part0,Bool.and_self]
theorem t3_94checked : Checked tree [1,8,8] := by
  refine ⟨plan754,valid754,t3_94choices,?_⟩
  exact check_of_frontier tree 0 t3_94root t3_94jobs t3_94frontier t3_94all
theorem t3_95choices : plan755.choices=[1,8,9].map (options 3 2) := by rfl


theorem t3_95part0 : t3_95jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_95frontier : t3_95root.frontier 0=t3_95jobs := by rfl
theorem t3_95all : t3_95jobs.all (Job.check tree)=true := by
  simp only [t3_95jobs,List.all_append,List.all_nil,t3_95part0,Bool.and_self]
theorem t3_95checked : Checked tree [1,8,9] := by
  refine ⟨plan755,valid755,t3_95choices,?_⟩
  exact check_of_frontier tree 0 t3_95root t3_95jobs t3_95frontier t3_95all
theorem t3_96choices : plan756.choices=[1,8,10].map (options 3 2) := by rfl


theorem t3_96part0 : t3_96jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_96frontier : t3_96root.frontier 0=t3_96jobs := by rfl
theorem t3_96all : t3_96jobs.all (Job.check tree)=true := by
  simp only [t3_96jobs,List.all_append,List.all_nil,t3_96part0,Bool.and_self]
theorem t3_96checked : Checked tree [1,8,10] := by
  refine ⟨plan756,valid756,t3_96choices,?_⟩
  exact check_of_frontier tree 0 t3_96root t3_96jobs t3_96frontier t3_96all
theorem t3_97choices : plan688.choices=[1,9,3].map (options 3 1) := by rfl


theorem t3_97part0 : t3_97jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_97frontier : t3_97root.frontier 0=t3_97jobs := by rfl
theorem t3_97all : t3_97jobs.all (Job.check tree)=true := by
  simp only [t3_97jobs,List.all_append,List.all_nil,t3_97part0,Bool.and_self]
theorem t3_97checked : Checked tree [1,9,3] := by
  refine ⟨plan688,valid688,t3_97choices,?_⟩
  exact check_of_frontier tree 0 t3_97root t3_97jobs t3_97frontier t3_97all
theorem t3_98choices : plan757.choices=[1,9,6].map (options 3 2) := by rfl


theorem t3_98part0 : t3_98jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_98frontier : t3_98root.frontier 0=t3_98jobs := by rfl
theorem t3_98all : t3_98jobs.all (Job.check tree)=true := by
  simp only [t3_98jobs,List.all_append,List.all_nil,t3_98part0,Bool.and_self]
theorem t3_98checked : Checked tree [1,9,6] := by
  refine ⟨plan757,valid757,t3_98choices,?_⟩
  exact check_of_frontier tree 0 t3_98root t3_98jobs t3_98frontier t3_98all
theorem t3_99choices : plan758.choices=[1,9,7].map (options 3 2) := by rfl


theorem t3_99part0 : t3_99jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_99frontier : t3_99root.frontier 0=t3_99jobs := by rfl
theorem t3_99all : t3_99jobs.all (Job.check tree)=true := by
  simp only [t3_99jobs,List.all_append,List.all_nil,t3_99part0,Bool.and_self]
theorem t3_99checked : Checked tree [1,9,7] := by
  refine ⟨plan758,valid758,t3_99choices,?_⟩
  exact check_of_frontier tree 0 t3_99root t3_99jobs t3_99frontier t3_99all
theorem t3_100choices : plan759.choices=[1,9,9].map (options 3 2) := by rfl


theorem t3_100part0 : t3_100jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_100frontier : t3_100root.frontier 0=t3_100jobs := by rfl
theorem t3_100all : t3_100jobs.all (Job.check tree)=true := by
  simp only [t3_100jobs,List.all_append,List.all_nil,t3_100part0,Bool.and_self]
theorem t3_100checked : Checked tree [1,9,9] := by
  refine ⟨plan759,valid759,t3_100choices,?_⟩
  exact check_of_frontier tree 0 t3_100root t3_100jobs t3_100frontier t3_100all
theorem t3_101choices : plan760.choices=[1,9,10].map (options 3 2) := by rfl


theorem t3_101part0 : t3_101jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_101frontier : t3_101root.frontier 0=t3_101jobs := by rfl
theorem t3_101all : t3_101jobs.all (Job.check tree)=true := by
  simp only [t3_101jobs,List.all_append,List.all_nil,t3_101part0,Bool.and_self]
theorem t3_101checked : Checked tree [1,9,10] := by
  refine ⟨plan760,valid760,t3_101choices,?_⟩
  exact check_of_frontier tree 0 t3_101root t3_101jobs t3_101frontier t3_101all
theorem t3_102choices : plan761.choices=[1,10,7].map (options 3 2) := by rfl


theorem t3_102part0 : t3_102jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_102frontier : t3_102root.frontier 0=t3_102jobs := by rfl
theorem t3_102all : t3_102jobs.all (Job.check tree)=true := by
  simp only [t3_102jobs,List.all_append,List.all_nil,t3_102part0,Bool.and_self]
theorem t3_102checked : Checked tree [1,10,7] := by
  refine ⟨plan761,valid761,t3_102choices,?_⟩
  exact check_of_frontier tree 0 t3_102root t3_102jobs t3_102frontier t3_102all
theorem t3_103choices : plan762.choices=[1,10,10].map (options 3 2) := by rfl


theorem t3_103part0 : t3_103jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_103frontier : t3_103root.frontier 0=t3_103jobs := by rfl
theorem t3_103all : t3_103jobs.all (Job.check tree)=true := by
  simp only [t3_103jobs,List.all_append,List.all_nil,t3_103part0,Bool.and_self]
theorem t3_103checked : Checked tree [1,10,10] := by
  refine ⟨plan762,valid762,t3_103choices,?_⟩
  exact check_of_frontier tree 0 t3_103root t3_103jobs t3_103frontier t3_103all
theorem t3_104choices : plan645.choices=[2,2,2].map (options 3 0) := by rfl


theorem t3_104part0 : t3_104jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_104frontier : t3_104root.frontier 0=t3_104jobs := by rfl
theorem t3_104all : t3_104jobs.all (Job.check tree)=true := by
  simp only [t3_104jobs,List.all_append,List.all_nil,t3_104part0,Bool.and_self]
theorem t3_104checked : Checked tree [2,2,2] := by
  refine ⟨plan645,valid645,t3_104choices,?_⟩
  exact check_of_frontier tree 0 t3_104root t3_104jobs t3_104frontier t3_104all
theorem t3_105choices : plan646.choices=[2,2,3].map (options 3 0) := by rfl


theorem t3_105part0 : t3_105jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_105frontier : t3_105root.frontier 0=t3_105jobs := by rfl
theorem t3_105all : t3_105jobs.all (Job.check tree)=true := by
  simp only [t3_105jobs,List.all_append,List.all_nil,t3_105part0,Bool.and_self]
theorem t3_105checked : Checked tree [2,2,3] := by
  refine ⟨plan646,valid646,t3_105choices,?_⟩
  exact check_of_frontier tree 0 t3_105root t3_105jobs t3_105frontier t3_105all
theorem t3_106choices : plan689.choices=[2,2,5].map (options 3 1) := by rfl


theorem t3_106part0 : t3_106jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_106frontier : t3_106root.frontier 0=t3_106jobs := by rfl
theorem t3_106all : t3_106jobs.all (Job.check tree)=true := by
  simp only [t3_106jobs,List.all_append,List.all_nil,t3_106part0,Bool.and_self]
theorem t3_106checked : Checked tree [2,2,5] := by
  refine ⟨plan689,valid689,t3_106choices,?_⟩
  exact check_of_frontier tree 0 t3_106root t3_106jobs t3_106frontier t3_106all
theorem t3_107choices : plan690.choices=[2,2,6].map (options 3 1) := by rfl


theorem t3_107part0 : t3_107jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_107frontier : t3_107root.frontier 0=t3_107jobs := by rfl
theorem t3_107all : t3_107jobs.all (Job.check tree)=true := by
  simp only [t3_107jobs,List.all_append,List.all_nil,t3_107part0,Bool.and_self]
theorem t3_107checked : Checked tree [2,2,6] := by
  refine ⟨plan690,valid690,t3_107choices,?_⟩
  exact check_of_frontier tree 0 t3_107root t3_107jobs t3_107frontier t3_107all
theorem t3_108choices : plan691.choices=[2,2,7].map (options 3 1) := by rfl


theorem t3_108part0 : t3_108jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_108frontier : t3_108root.frontier 0=t3_108jobs := by rfl
theorem t3_108all : t3_108jobs.all (Job.check tree)=true := by
  simp only [t3_108jobs,List.all_append,List.all_nil,t3_108part0,Bool.and_self]
theorem t3_108checked : Checked tree [2,2,7] := by
  refine ⟨plan691,valid691,t3_108choices,?_⟩
  exact check_of_frontier tree 0 t3_108root t3_108jobs t3_108frontier t3_108all
theorem t3_109choices : plan692.choices=[2,2,9].map (options 3 1) := by rfl


theorem t3_109part0 : t3_109jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_109frontier : t3_109root.frontier 0=t3_109jobs := by rfl
theorem t3_109all : t3_109jobs.all (Job.check tree)=true := by
  simp only [t3_109jobs,List.all_append,List.all_nil,t3_109part0,Bool.and_self]
theorem t3_109checked : Checked tree [2,2,9] := by
  refine ⟨plan692,valid692,t3_109choices,?_⟩
  exact check_of_frontier tree 0 t3_109root t3_109jobs t3_109frontier t3_109all
theorem t3_110choices : plan693.choices=[2,2,10].map (options 3 1) := by rfl


theorem t3_110part0 : t3_110jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_110frontier : t3_110root.frontier 0=t3_110jobs := by rfl
theorem t3_110all : t3_110jobs.all (Job.check tree)=true := by
  simp only [t3_110jobs,List.all_append,List.all_nil,t3_110part0,Bool.and_self]
theorem t3_110checked : Checked tree [2,2,10] := by
  refine ⟨plan693,valid693,t3_110choices,?_⟩
  exact check_of_frontier tree 0 t3_110root t3_110jobs t3_110frontier t3_110all
theorem t3_111choices : plan647.choices=[2,3,3].map (options 3 0) := by rfl


theorem t3_111part0 : t3_111jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_111frontier : t3_111root.frontier 0=t3_111jobs := by rfl
theorem t3_111all : t3_111jobs.all (Job.check tree)=true := by
  simp only [t3_111jobs,List.all_append,List.all_nil,t3_111part0,Bool.and_self]
theorem t3_111checked : Checked tree [2,3,3] := by
  refine ⟨plan647,valid647,t3_111choices,?_⟩
  exact check_of_frontier tree 0 t3_111root t3_111jobs t3_111frontier t3_111all
theorem t3_112choices : plan694.choices=[2,3,6].map (options 3 1) := by rfl


theorem t3_112part0 : t3_112jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_112frontier : t3_112root.frontier 0=t3_112jobs := by rfl
theorem t3_112all : t3_112jobs.all (Job.check tree)=true := by
  simp only [t3_112jobs,List.all_append,List.all_nil,t3_112part0,Bool.and_self]
theorem t3_112checked : Checked tree [2,3,6] := by
  refine ⟨plan694,valid694,t3_112choices,?_⟩
  exact check_of_frontier tree 0 t3_112root t3_112jobs t3_112frontier t3_112all
theorem t3_113choices : plan695.choices=[2,3,7].map (options 3 1) := by rfl


theorem t3_113part0 : t3_113jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_113frontier : t3_113root.frontier 0=t3_113jobs := by rfl
theorem t3_113all : t3_113jobs.all (Job.check tree)=true := by
  simp only [t3_113jobs,List.all_append,List.all_nil,t3_113part0,Bool.and_self]
theorem t3_113checked : Checked tree [2,3,7] := by
  refine ⟨plan695,valid695,t3_113choices,?_⟩
  exact check_of_frontier tree 0 t3_113root t3_113jobs t3_113frontier t3_113all
theorem t3_114choices : plan696.choices=[2,3,10].map (options 3 1) := by rfl


theorem t3_114part0 : t3_114jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_114frontier : t3_114root.frontier 0=t3_114jobs := by rfl
theorem t3_114all : t3_114jobs.all (Job.check tree)=true := by
  simp only [t3_114jobs,List.all_append,List.all_nil,t3_114part0,Bool.and_self]
theorem t3_114checked : Checked tree [2,3,10] := by
  refine ⟨plan696,valid696,t3_114choices,?_⟩
  exact check_of_frontier tree 0 t3_114root t3_114jobs t3_114frontier t3_114all
theorem t3_115choices : plan697.choices=[2,5,3].map (options 3 1) := by rfl


theorem t3_115part0 : t3_115jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_115frontier : t3_115root.frontier 0=t3_115jobs := by rfl
theorem t3_115all : t3_115jobs.all (Job.check tree)=true := by
  simp only [t3_115jobs,List.all_append,List.all_nil,t3_115part0,Bool.and_self]
theorem t3_115checked : Checked tree [2,5,3] := by
  refine ⟨plan697,valid697,t3_115choices,?_⟩
  exact check_of_frontier tree 0 t3_115root t3_115jobs t3_115frontier t3_115all
theorem t3_116choices : plan763.choices=[2,5,5].map (options 3 2) := by rfl


theorem t3_116part0 : t3_116jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_116frontier : t3_116root.frontier 0=t3_116jobs := by rfl
theorem t3_116all : t3_116jobs.all (Job.check tree)=true := by
  simp only [t3_116jobs,List.all_append,List.all_nil,t3_116part0,Bool.and_self]
theorem t3_116checked : Checked tree [2,5,5] := by
  refine ⟨plan763,valid763,t3_116choices,?_⟩
  exact check_of_frontier tree 0 t3_116root t3_116jobs t3_116frontier t3_116all
theorem t3_117choices : plan764.choices=[2,5,6].map (options 3 2) := by rfl


theorem t3_117part0 : t3_117jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_117frontier : t3_117root.frontier 0=t3_117jobs := by rfl
theorem t3_117all : t3_117jobs.all (Job.check tree)=true := by
  simp only [t3_117jobs,List.all_append,List.all_nil,t3_117part0,Bool.and_self]
theorem t3_117checked : Checked tree [2,5,6] := by
  refine ⟨plan764,valid764,t3_117choices,?_⟩
  exact check_of_frontier tree 0 t3_117root t3_117jobs t3_117frontier t3_117all
theorem t3_118choices : plan765.choices=[2,5,7].map (options 3 2) := by rfl


theorem t3_118part0 : t3_118jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_118frontier : t3_118root.frontier 0=t3_118jobs := by rfl
theorem t3_118all : t3_118jobs.all (Job.check tree)=true := by
  simp only [t3_118jobs,List.all_append,List.all_nil,t3_118part0,Bool.and_self]
theorem t3_118checked : Checked tree [2,5,7] := by
  refine ⟨plan765,valid765,t3_118choices,?_⟩
  exact check_of_frontier tree 0 t3_118root t3_118jobs t3_118frontier t3_118all
theorem t3_119choices : plan766.choices=[2,5,9].map (options 3 2) := by rfl


theorem t3_119part0 : t3_119jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_119frontier : t3_119root.frontier 0=t3_119jobs := by rfl
theorem t3_119all : t3_119jobs.all (Job.check tree)=true := by
  simp only [t3_119jobs,List.all_append,List.all_nil,t3_119part0,Bool.and_self]
theorem t3_119checked : Checked tree [2,5,9] := by
  refine ⟨plan766,valid766,t3_119choices,?_⟩
  exact check_of_frontier tree 0 t3_119root t3_119jobs t3_119frontier t3_119all
theorem t3_120choices : plan767.choices=[2,5,10].map (options 3 2) := by rfl


theorem t3_120part0 : t3_120jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_120frontier : t3_120root.frontier 0=t3_120jobs := by rfl
theorem t3_120all : t3_120jobs.all (Job.check tree)=true := by
  simp only [t3_120jobs,List.all_append,List.all_nil,t3_120part0,Bool.and_self]
theorem t3_120checked : Checked tree [2,5,10] := by
  refine ⟨plan767,valid767,t3_120choices,?_⟩
  exact check_of_frontier tree 0 t3_120root t3_120jobs t3_120frontier t3_120all
theorem t3_121choices : plan768.choices=[2,6,6].map (options 3 2) := by rfl


theorem t3_121part0 : t3_121jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_121frontier : t3_121root.frontier 0=t3_121jobs := by rfl
theorem t3_121all : t3_121jobs.all (Job.check tree)=true := by
  simp only [t3_121jobs,List.all_append,List.all_nil,t3_121part0,Bool.and_self]
theorem t3_121checked : Checked tree [2,6,6] := by
  refine ⟨plan768,valid768,t3_121choices,?_⟩
  exact check_of_frontier tree 0 t3_121root t3_121jobs t3_121frontier t3_121all
theorem t3_122choices : plan769.choices=[2,6,7].map (options 3 2) := by rfl


theorem t3_122part0 : t3_122jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_122frontier : t3_122root.frontier 0=t3_122jobs := by rfl
theorem t3_122all : t3_122jobs.all (Job.check tree)=true := by
  simp only [t3_122jobs,List.all_append,List.all_nil,t3_122part0,Bool.and_self]
theorem t3_122checked : Checked tree [2,6,7] := by
  refine ⟨plan769,valid769,t3_122choices,?_⟩
  exact check_of_frontier tree 0 t3_122root t3_122jobs t3_122frontier t3_122all
theorem t3_123choices : plan770.choices=[2,6,10].map (options 3 2) := by rfl


theorem t3_123part0 : t3_123jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_123frontier : t3_123root.frontier 0=t3_123jobs := by rfl
theorem t3_123all : t3_123jobs.all (Job.check tree)=true := by
  simp only [t3_123jobs,List.all_append,List.all_nil,t3_123part0,Bool.and_self]
theorem t3_123checked : Checked tree [2,6,10] := by
  refine ⟨plan770,valid770,t3_123choices,?_⟩
  exact check_of_frontier tree 0 t3_123root t3_123jobs t3_123frontier t3_123all
theorem t3_124choices : plan771.choices=[2,7,7].map (options 3 2) := by rfl


theorem t3_124part0 : t3_124jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_124frontier : t3_124root.frontier 0=t3_124jobs := by rfl
theorem t3_124all : t3_124jobs.all (Job.check tree)=true := by
  simp only [t3_124jobs,List.all_append,List.all_nil,t3_124part0,Bool.and_self]
theorem t3_124checked : Checked tree [2,7,7] := by
  refine ⟨plan771,valid771,t3_124choices,?_⟩
  exact check_of_frontier tree 0 t3_124root t3_124jobs t3_124frontier t3_124all
theorem t3_125choices : plan698.choices=[2,9,3].map (options 3 1) := by rfl


theorem t3_125part0 : t3_125jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_125frontier : t3_125root.frontier 0=t3_125jobs := by rfl
theorem t3_125all : t3_125jobs.all (Job.check tree)=true := by
  simp only [t3_125jobs,List.all_append,List.all_nil,t3_125part0,Bool.and_self]
theorem t3_125checked : Checked tree [2,9,3] := by
  refine ⟨plan698,valid698,t3_125choices,?_⟩
  exact check_of_frontier tree 0 t3_125root t3_125jobs t3_125frontier t3_125all
theorem t3_126choices : plan772.choices=[2,9,6].map (options 3 2) := by rfl


theorem t3_126part0 : t3_126jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_126frontier : t3_126root.frontier 0=t3_126jobs := by rfl
theorem t3_126all : t3_126jobs.all (Job.check tree)=true := by
  simp only [t3_126jobs,List.all_append,List.all_nil,t3_126part0,Bool.and_self]
theorem t3_126checked : Checked tree [2,9,6] := by
  refine ⟨plan772,valid772,t3_126choices,?_⟩
  exact check_of_frontier tree 0 t3_126root t3_126jobs t3_126frontier t3_126all
theorem t3_127choices : plan773.choices=[2,9,7].map (options 3 2) := by rfl


theorem t3_127part0 : t3_127jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_127frontier : t3_127root.frontier 0=t3_127jobs := by rfl
theorem t3_127all : t3_127jobs.all (Job.check tree)=true := by
  simp only [t3_127jobs,List.all_append,List.all_nil,t3_127part0,Bool.and_self]
theorem t3_127checked : Checked tree [2,9,7] := by
  refine ⟨plan773,valid773,t3_127choices,?_⟩
  exact check_of_frontier tree 0 t3_127root t3_127jobs t3_127frontier t3_127all
theorem t3_128choices : plan774.choices=[2,9,9].map (options 3 2) := by rfl


theorem t3_128part0 : t3_128jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_128frontier : t3_128root.frontier 0=t3_128jobs := by rfl
theorem t3_128all : t3_128jobs.all (Job.check tree)=true := by
  simp only [t3_128jobs,List.all_append,List.all_nil,t3_128part0,Bool.and_self]
theorem t3_128checked : Checked tree [2,9,9] := by
  refine ⟨plan774,valid774,t3_128choices,?_⟩
  exact check_of_frontier tree 0 t3_128root t3_128jobs t3_128frontier t3_128all
theorem t3_129choices : plan775.choices=[2,9,10].map (options 3 2) := by rfl


theorem t3_129part0 : t3_129jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_129frontier : t3_129root.frontier 0=t3_129jobs := by rfl
theorem t3_129all : t3_129jobs.all (Job.check tree)=true := by
  simp only [t3_129jobs,List.all_append,List.all_nil,t3_129part0,Bool.and_self]
theorem t3_129checked : Checked tree [2,9,10] := by
  refine ⟨plan775,valid775,t3_129choices,?_⟩
  exact check_of_frontier tree 0 t3_129root t3_129jobs t3_129frontier t3_129all
theorem t3_130choices : plan776.choices=[2,10,7].map (options 3 2) := by rfl


theorem t3_130part0 : t3_130jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_130frontier : t3_130root.frontier 0=t3_130jobs := by rfl
theorem t3_130all : t3_130jobs.all (Job.check tree)=true := by
  simp only [t3_130jobs,List.all_append,List.all_nil,t3_130part0,Bool.and_self]
theorem t3_130checked : Checked tree [2,10,7] := by
  refine ⟨plan776,valid776,t3_130choices,?_⟩
  exact check_of_frontier tree 0 t3_130root t3_130jobs t3_130frontier t3_130all
theorem t3_131choices : plan777.choices=[2,10,10].map (options 3 2) := by rfl


theorem t3_131part0 : t3_131jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_131frontier : t3_131root.frontier 0=t3_131jobs := by rfl
theorem t3_131all : t3_131jobs.all (Job.check tree)=true := by
  simp only [t3_131jobs,List.all_append,List.all_nil,t3_131part0,Bool.and_self]
theorem t3_131checked : Checked tree [2,10,10] := by
  refine ⟨plan777,valid777,t3_131choices,?_⟩
  exact check_of_frontier tree 0 t3_131root t3_131jobs t3_131frontier t3_131all
theorem t3_132choices : plan648.choices=[3,3,3].map (options 3 0) := by rfl


theorem t3_132part0 : t3_132jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_132frontier : t3_132root.frontier 0=t3_132jobs := by rfl
theorem t3_132all : t3_132jobs.all (Job.check tree)=true := by
  simp only [t3_132jobs,List.all_append,List.all_nil,t3_132part0,Bool.and_self]
theorem t3_132checked : Checked tree [3,3,3] := by
  refine ⟨plan648,valid648,t3_132choices,?_⟩
  exact check_of_frontier tree 0 t3_132root t3_132jobs t3_132frontier t3_132all
theorem t3_133choices : plan699.choices=[3,3,6].map (options 3 1) := by rfl


theorem t3_133part0 : t3_133jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_133frontier : t3_133root.frontier 0=t3_133jobs := by rfl
theorem t3_133all : t3_133jobs.all (Job.check tree)=true := by
  simp only [t3_133jobs,List.all_append,List.all_nil,t3_133part0,Bool.and_self]
theorem t3_133checked : Checked tree [3,3,6] := by
  refine ⟨plan699,valid699,t3_133choices,?_⟩
  exact check_of_frontier tree 0 t3_133root t3_133jobs t3_133frontier t3_133all
theorem t3_134choices : plan700.choices=[3,3,7].map (options 3 1) := by rfl


theorem t3_134part0 : t3_134jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_134frontier : t3_134root.frontier 0=t3_134jobs := by rfl
theorem t3_134all : t3_134jobs.all (Job.check tree)=true := by
  simp only [t3_134jobs,List.all_append,List.all_nil,t3_134part0,Bool.and_self]
theorem t3_134checked : Checked tree [3,3,7] := by
  refine ⟨plan700,valid700,t3_134choices,?_⟩
  exact check_of_frontier tree 0 t3_134root t3_134jobs t3_134frontier t3_134all
theorem t3_135choices : plan701.choices=[3,3,10].map (options 3 1) := by rfl


theorem t3_135part0 : t3_135jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_135frontier : t3_135root.frontier 0=t3_135jobs := by rfl
theorem t3_135all : t3_135jobs.all (Job.check tree)=true := by
  simp only [t3_135jobs,List.all_append,List.all_nil,t3_135part0,Bool.and_self]
theorem t3_135checked : Checked tree [3,3,10] := by
  refine ⟨plan701,valid701,t3_135choices,?_⟩
  exact check_of_frontier tree 0 t3_135root t3_135jobs t3_135frontier t3_135all
theorem t3_136choices : plan778.choices=[3,6,6].map (options 3 2) := by rfl


theorem t3_136part0 : t3_136jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_136frontier : t3_136root.frontier 0=t3_136jobs := by rfl
theorem t3_136all : t3_136jobs.all (Job.check tree)=true := by
  simp only [t3_136jobs,List.all_append,List.all_nil,t3_136part0,Bool.and_self]
theorem t3_136checked : Checked tree [3,6,6] := by
  refine ⟨plan778,valid778,t3_136choices,?_⟩
  exact check_of_frontier tree 0 t3_136root t3_136jobs t3_136frontier t3_136all
theorem t3_137choices : plan779.choices=[3,6,7].map (options 3 2) := by rfl


theorem t3_137part0 : t3_137jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_137frontier : t3_137root.frontier 0=t3_137jobs := by rfl
theorem t3_137all : t3_137jobs.all (Job.check tree)=true := by
  simp only [t3_137jobs,List.all_append,List.all_nil,t3_137part0,Bool.and_self]
theorem t3_137checked : Checked tree [3,6,7] := by
  refine ⟨plan779,valid779,t3_137choices,?_⟩
  exact check_of_frontier tree 0 t3_137root t3_137jobs t3_137frontier t3_137all
theorem t3_138choices : plan780.choices=[3,6,10].map (options 3 2) := by rfl


theorem t3_138part0 : t3_138jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_138frontier : t3_138root.frontier 0=t3_138jobs := by rfl
theorem t3_138all : t3_138jobs.all (Job.check tree)=true := by
  simp only [t3_138jobs,List.all_append,List.all_nil,t3_138part0,Bool.and_self]
theorem t3_138checked : Checked tree [3,6,10] := by
  refine ⟨plan780,valid780,t3_138choices,?_⟩
  exact check_of_frontier tree 0 t3_138root t3_138jobs t3_138frontier t3_138all
theorem t3_139choices : plan781.choices=[3,7,7].map (options 3 2) := by rfl


theorem t3_139part0 : t3_139jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_139frontier : t3_139root.frontier 0=t3_139jobs := by rfl
theorem t3_139all : t3_139jobs.all (Job.check tree)=true := by
  simp only [t3_139jobs,List.all_append,List.all_nil,t3_139part0,Bool.and_self]
theorem t3_139checked : Checked tree [3,7,7] := by
  refine ⟨plan781,valid781,t3_139choices,?_⟩
  exact check_of_frontier tree 0 t3_139root t3_139jobs t3_139frontier t3_139all
theorem t3_140choices : plan782.choices=[3,10,7].map (options 3 2) := by rfl


theorem t3_140part0 : t3_140jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_140frontier : t3_140root.frontier 0=t3_140jobs := by rfl
theorem t3_140all : t3_140jobs.all (Job.check tree)=true := by
  simp only [t3_140jobs,List.all_append,List.all_nil,t3_140part0,Bool.and_self]
theorem t3_140checked : Checked tree [3,10,7] := by
  refine ⟨plan782,valid782,t3_140choices,?_⟩
  exact check_of_frontier tree 0 t3_140root t3_140jobs t3_140frontier t3_140all
theorem t3_141choices : plan783.choices=[3,10,10].map (options 3 2) := by rfl


theorem t3_141part0 : t3_141jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_141frontier : t3_141root.frontier 0=t3_141jobs := by rfl
theorem t3_141all : t3_141jobs.all (Job.check tree)=true := by
  simp only [t3_141jobs,List.all_append,List.all_nil,t3_141part0,Bool.and_self]
theorem t3_141checked : Checked tree [3,10,10] := by
  refine ⟨plan783,valid783,t3_141choices,?_⟩
  exact check_of_frontier tree 0 t3_141root t3_141jobs t3_141frontier t3_141all
theorem t3_142choices : plan702.choices=[4,2,2].map (options 3 1) := by rfl


theorem t3_142part0 : t3_142jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_142frontier : t3_142root.frontier 0=t3_142jobs := by rfl
theorem t3_142all : t3_142jobs.all (Job.check tree)=true := by
  simp only [t3_142jobs,List.all_append,List.all_nil,t3_142part0,Bool.and_self]
theorem t3_142checked : Checked tree [4,2,2] := by
  refine ⟨plan702,valid702,t3_142choices,?_⟩
  exact check_of_frontier tree 0 t3_142root t3_142jobs t3_142frontier t3_142all
theorem t3_143choices : plan703.choices=[4,2,3].map (options 3 1) := by rfl


theorem t3_143part0 : t3_143jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_143frontier : t3_143root.frontier 0=t3_143jobs := by rfl
theorem t3_143all : t3_143jobs.all (Job.check tree)=true := by
  simp only [t3_143jobs,List.all_append,List.all_nil,t3_143part0,Bool.and_self]
theorem t3_143checked : Checked tree [4,2,3] := by
  refine ⟨plan703,valid703,t3_143choices,?_⟩
  exact check_of_frontier tree 0 t3_143root t3_143jobs t3_143frontier t3_143all
theorem t3_144choices : plan784.choices=[4,2,5].map (options 3 2) := by rfl


theorem t3_144part0 : t3_144jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_144frontier : t3_144root.frontier 0=t3_144jobs := by rfl
theorem t3_144all : t3_144jobs.all (Job.check tree)=true := by
  simp only [t3_144jobs,List.all_append,List.all_nil,t3_144part0,Bool.and_self]
theorem t3_144checked : Checked tree [4,2,5] := by
  refine ⟨plan784,valid784,t3_144choices,?_⟩
  exact check_of_frontier tree 0 t3_144root t3_144jobs t3_144frontier t3_144all
theorem t3_145choices : plan785.choices=[4,2,6].map (options 3 2) := by rfl


theorem t3_145part0 : t3_145jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_145frontier : t3_145root.frontier 0=t3_145jobs := by rfl
theorem t3_145all : t3_145jobs.all (Job.check tree)=true := by
  simp only [t3_145jobs,List.all_append,List.all_nil,t3_145part0,Bool.and_self]
theorem t3_145checked : Checked tree [4,2,6] := by
  refine ⟨plan785,valid785,t3_145choices,?_⟩
  exact check_of_frontier tree 0 t3_145root t3_145jobs t3_145frontier t3_145all
theorem t3_146choices : plan786.choices=[4,2,7].map (options 3 2) := by rfl


theorem t3_146part0 : t3_146jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_146frontier : t3_146root.frontier 0=t3_146jobs := by rfl
theorem t3_146all : t3_146jobs.all (Job.check tree)=true := by
  simp only [t3_146jobs,List.all_append,List.all_nil,t3_146part0,Bool.and_self]
theorem t3_146checked : Checked tree [4,2,7] := by
  refine ⟨plan786,valid786,t3_146choices,?_⟩
  exact check_of_frontier tree 0 t3_146root t3_146jobs t3_146frontier t3_146all
theorem t3_147choices : plan787.choices=[4,2,9].map (options 3 2) := by rfl


theorem t3_147part0 : t3_147jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_147frontier : t3_147root.frontier 0=t3_147jobs := by rfl
theorem t3_147all : t3_147jobs.all (Job.check tree)=true := by
  simp only [t3_147jobs,List.all_append,List.all_nil,t3_147part0,Bool.and_self]
theorem t3_147checked : Checked tree [4,2,9] := by
  refine ⟨plan787,valid787,t3_147choices,?_⟩
  exact check_of_frontier tree 0 t3_147root t3_147jobs t3_147frontier t3_147all
theorem t3_148choices : plan788.choices=[4,2,10].map (options 3 2) := by rfl


theorem t3_148part0 : t3_148jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_148frontier : t3_148root.frontier 0=t3_148jobs := by rfl
theorem t3_148all : t3_148jobs.all (Job.check tree)=true := by
  simp only [t3_148jobs,List.all_append,List.all_nil,t3_148part0,Bool.and_self]
theorem t3_148checked : Checked tree [4,2,10] := by
  refine ⟨plan788,valid788,t3_148choices,?_⟩
  exact check_of_frontier tree 0 t3_148root t3_148jobs t3_148frontier t3_148all
theorem t3_149choices : plan704.choices=[4,3,3].map (options 3 1) := by rfl


theorem t3_149part0 : t3_149jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_149frontier : t3_149root.frontier 0=t3_149jobs := by rfl
theorem t3_149all : t3_149jobs.all (Job.check tree)=true := by
  simp only [t3_149jobs,List.all_append,List.all_nil,t3_149part0,Bool.and_self]
theorem t3_149checked : Checked tree [4,3,3] := by
  refine ⟨plan704,valid704,t3_149choices,?_⟩
  exact check_of_frontier tree 0 t3_149root t3_149jobs t3_149frontier t3_149all
theorem t3_150choices : plan789.choices=[4,3,6].map (options 3 2) := by rfl


theorem t3_150part0 : t3_150jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_150frontier : t3_150root.frontier 0=t3_150jobs := by rfl
theorem t3_150all : t3_150jobs.all (Job.check tree)=true := by
  simp only [t3_150jobs,List.all_append,List.all_nil,t3_150part0,Bool.and_self]
theorem t3_150checked : Checked tree [4,3,6] := by
  refine ⟨plan789,valid789,t3_150choices,?_⟩
  exact check_of_frontier tree 0 t3_150root t3_150jobs t3_150frontier t3_150all
theorem t3_151choices : plan790.choices=[4,3,7].map (options 3 2) := by rfl


theorem t3_151part0 : t3_151jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_151frontier : t3_151root.frontier 0=t3_151jobs := by rfl
theorem t3_151all : t3_151jobs.all (Job.check tree)=true := by
  simp only [t3_151jobs,List.all_append,List.all_nil,t3_151part0,Bool.and_self]
theorem t3_151checked : Checked tree [4,3,7] := by
  refine ⟨plan790,valid790,t3_151choices,?_⟩
  exact check_of_frontier tree 0 t3_151root t3_151jobs t3_151frontier t3_151all
theorem t3_152choices : plan791.choices=[4,3,10].map (options 3 2) := by rfl


theorem t3_152part0 : t3_152jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_152frontier : t3_152root.frontier 0=t3_152jobs := by rfl
theorem t3_152all : t3_152jobs.all (Job.check tree)=true := by
  simp only [t3_152jobs,List.all_append,List.all_nil,t3_152part0,Bool.and_self]
theorem t3_152checked : Checked tree [4,3,10] := by
  refine ⟨plan791,valid791,t3_152choices,?_⟩
  exact check_of_frontier tree 0 t3_152root t3_152jobs t3_152frontier t3_152all
theorem t3_153choices : plan792.choices=[4,4,2].map (options 3 2) := by rfl


theorem t3_153part0 : t3_153jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_153frontier : t3_153root.frontier 0=t3_153jobs := by rfl
theorem t3_153all : t3_153jobs.all (Job.check tree)=true := by
  simp only [t3_153jobs,List.all_append,List.all_nil,t3_153part0,Bool.and_self]
theorem t3_153checked : Checked tree [4,4,2] := by
  refine ⟨plan792,valid792,t3_153choices,?_⟩
  exact check_of_frontier tree 0 t3_153root t3_153jobs t3_153frontier t3_153all
theorem t3_154choices : plan793.choices=[4,4,3].map (options 3 2) := by rfl


theorem t3_154part0 : t3_154jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_154frontier : t3_154root.frontier 0=t3_154jobs := by rfl
theorem t3_154all : t3_154jobs.all (Job.check tree)=true := by
  simp only [t3_154jobs,List.all_append,List.all_nil,t3_154part0,Bool.and_self]
theorem t3_154checked : Checked tree [4,4,3] := by
  refine ⟨plan793,valid793,t3_154choices,?_⟩
  exact check_of_frontier tree 0 t3_154root t3_154jobs t3_154frontier t3_154all
theorem t3_155choices : plan819.choices=[4,4,4].map (options 3 3) := by rfl


theorem t3_155part0 : t3_155jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_155frontier : t3_155root.frontier 0=t3_155jobs := by rfl
theorem t3_155all : t3_155jobs.all (Job.check tree)=true := by
  simp only [t3_155jobs,List.all_append,List.all_nil,t3_155part0,Bool.and_self]
theorem t3_155checked : Checked tree [4,4,4] := by
  refine ⟨plan819,valid819,t3_155choices,?_⟩
  exact check_of_frontier tree 0 t3_155root t3_155jobs t3_155frontier t3_155all
theorem t3_156choices : plan820.choices=[4,4,5].map (options 3 3) := by rfl


theorem t3_156part0 : t3_156jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_156frontier : t3_156root.frontier 0=t3_156jobs := by rfl
theorem t3_156all : t3_156jobs.all (Job.check tree)=true := by
  simp only [t3_156jobs,List.all_append,List.all_nil,t3_156part0,Bool.and_self]
theorem t3_156checked : Checked tree [4,4,5] := by
  refine ⟨plan820,valid820,t3_156choices,?_⟩
  exact check_of_frontier tree 0 t3_156root t3_156jobs t3_156frontier t3_156all
theorem t3_157choices : plan821.choices=[4,4,6].map (options 3 3) := by rfl


theorem t3_157part0 : t3_157jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_157frontier : t3_157root.frontier 0=t3_157jobs := by rfl
theorem t3_157all : t3_157jobs.all (Job.check tree)=true := by
  simp only [t3_157jobs,List.all_append,List.all_nil,t3_157part0,Bool.and_self]
theorem t3_157checked : Checked tree [4,4,6] := by
  refine ⟨plan821,valid821,t3_157choices,?_⟩
  exact check_of_frontier tree 0 t3_157root t3_157jobs t3_157frontier t3_157all
theorem t3_158choices : plan822.choices=[4,4,7].map (options 3 3) := by rfl


theorem t3_158part0 : t3_158jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_158frontier : t3_158root.frontier 0=t3_158jobs := by rfl
theorem t3_158all : t3_158jobs.all (Job.check tree)=true := by
  simp only [t3_158jobs,List.all_append,List.all_nil,t3_158part0,Bool.and_self]
theorem t3_158checked : Checked tree [4,4,7] := by
  refine ⟨plan822,valid822,t3_158choices,?_⟩
  exact check_of_frontier tree 0 t3_158root t3_158jobs t3_158frontier t3_158all
theorem t3_159choices : plan823.choices=[4,4,8].map (options 3 3) := by rfl


theorem t3_159part0 : t3_159jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_159frontier : t3_159root.frontier 0=t3_159jobs := by rfl
theorem t3_159all : t3_159jobs.all (Job.check tree)=true := by
  simp only [t3_159jobs,List.all_append,List.all_nil,t3_159part0,Bool.and_self]
theorem t3_159checked : Checked tree [4,4,8] := by
  refine ⟨plan823,valid823,t3_159choices,?_⟩
  exact check_of_frontier tree 0 t3_159root t3_159jobs t3_159frontier t3_159all
theorem t3_160choices : plan824.choices=[4,4,9].map (options 3 3) := by rfl


theorem t3_160part0 : t3_160jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_160frontier : t3_160root.frontier 0=t3_160jobs := by rfl
theorem t3_160all : t3_160jobs.all (Job.check tree)=true := by
  simp only [t3_160jobs,List.all_append,List.all_nil,t3_160part0,Bool.and_self]
theorem t3_160checked : Checked tree [4,4,9] := by
  refine ⟨plan824,valid824,t3_160choices,?_⟩
  exact check_of_frontier tree 0 t3_160root t3_160jobs t3_160frontier t3_160all
theorem t3_161choices : plan825.choices=[4,4,10].map (options 3 3) := by rfl


theorem t3_161part0 : t3_161jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_161frontier : t3_161root.frontier 0=t3_161jobs := by rfl
theorem t3_161all : t3_161jobs.all (Job.check tree)=true := by
  simp only [t3_161jobs,List.all_append,List.all_nil,t3_161part0,Bool.and_self]
theorem t3_161checked : Checked tree [4,4,10] := by
  refine ⟨plan825,valid825,t3_161choices,?_⟩
  exact check_of_frontier tree 0 t3_161root t3_161jobs t3_161frontier t3_161all
theorem t3_162choices : plan794.choices=[4,5,3].map (options 3 2) := by rfl


theorem t3_162part0 : t3_162jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_162frontier : t3_162root.frontier 0=t3_162jobs := by rfl
theorem t3_162all : t3_162jobs.all (Job.check tree)=true := by
  simp only [t3_162jobs,List.all_append,List.all_nil,t3_162part0,Bool.and_self]
theorem t3_162checked : Checked tree [4,5,3] := by
  refine ⟨plan794,valid794,t3_162choices,?_⟩
  exact check_of_frontier tree 0 t3_162root t3_162jobs t3_162frontier t3_162all
theorem t3_163choices : plan826.choices=[4,5,5].map (options 3 3) := by rfl


theorem t3_163part0 : t3_163jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_163frontier : t3_163root.frontier 0=t3_163jobs := by rfl
theorem t3_163all : t3_163jobs.all (Job.check tree)=true := by
  simp only [t3_163jobs,List.all_append,List.all_nil,t3_163part0,Bool.and_self]
theorem t3_163checked : Checked tree [4,5,5] := by
  refine ⟨plan826,valid826,t3_163choices,?_⟩
  exact check_of_frontier tree 0 t3_163root t3_163jobs t3_163frontier t3_163all
theorem t3_164choices : plan827.choices=[4,5,6].map (options 3 3) := by rfl


theorem t3_164part0 : t3_164jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_164frontier : t3_164root.frontier 0=t3_164jobs := by rfl
theorem t3_164all : t3_164jobs.all (Job.check tree)=true := by
  simp only [t3_164jobs,List.all_append,List.all_nil,t3_164part0,Bool.and_self]
theorem t3_164checked : Checked tree [4,5,6] := by
  refine ⟨plan827,valid827,t3_164choices,?_⟩
  exact check_of_frontier tree 0 t3_164root t3_164jobs t3_164frontier t3_164all
theorem t3_165choices : plan828.choices=[4,5,7].map (options 3 3) := by rfl


theorem t3_165part0 : t3_165jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_165frontier : t3_165root.frontier 0=t3_165jobs := by rfl
theorem t3_165all : t3_165jobs.all (Job.check tree)=true := by
  simp only [t3_165jobs,List.all_append,List.all_nil,t3_165part0,Bool.and_self]
theorem t3_165checked : Checked tree [4,5,7] := by
  refine ⟨plan828,valid828,t3_165choices,?_⟩
  exact check_of_frontier tree 0 t3_165root t3_165jobs t3_165frontier t3_165all
theorem t3_166choices : plan829.choices=[4,5,9].map (options 3 3) := by rfl


theorem t3_166part0 : t3_166jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_166frontier : t3_166root.frontier 0=t3_166jobs := by rfl
theorem t3_166all : t3_166jobs.all (Job.check tree)=true := by
  simp only [t3_166jobs,List.all_append,List.all_nil,t3_166part0,Bool.and_self]
theorem t3_166checked : Checked tree [4,5,9] := by
  refine ⟨plan829,valid829,t3_166choices,?_⟩
  exact check_of_frontier tree 0 t3_166root t3_166jobs t3_166frontier t3_166all
theorem t3_167choices : plan830.choices=[4,5,10].map (options 3 3) := by rfl


theorem t3_167part0 : t3_167jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_167frontier : t3_167root.frontier 0=t3_167jobs := by rfl
theorem t3_167all : t3_167jobs.all (Job.check tree)=true := by
  simp only [t3_167jobs,List.all_append,List.all_nil,t3_167part0,Bool.and_self]
theorem t3_167checked : Checked tree [4,5,10] := by
  refine ⟨plan830,valid830,t3_167choices,?_⟩
  exact check_of_frontier tree 0 t3_167root t3_167jobs t3_167frontier t3_167all
theorem t3_168choices : plan831.choices=[4,6,6].map (options 3 3) := by rfl


theorem t3_168part0 : t3_168jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_168frontier : t3_168root.frontier 0=t3_168jobs := by rfl
theorem t3_168all : t3_168jobs.all (Job.check tree)=true := by
  simp only [t3_168jobs,List.all_append,List.all_nil,t3_168part0,Bool.and_self]
theorem t3_168checked : Checked tree [4,6,6] := by
  refine ⟨plan831,valid831,t3_168choices,?_⟩
  exact check_of_frontier tree 0 t3_168root t3_168jobs t3_168frontier t3_168all
theorem t3_169choices : plan832.choices=[4,6,7].map (options 3 3) := by rfl


theorem t3_169part0 : t3_169jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_169frontier : t3_169root.frontier 0=t3_169jobs := by rfl
theorem t3_169all : t3_169jobs.all (Job.check tree)=true := by
  simp only [t3_169jobs,List.all_append,List.all_nil,t3_169part0,Bool.and_self]
theorem t3_169checked : Checked tree [4,6,7] := by
  refine ⟨plan832,valid832,t3_169choices,?_⟩
  exact check_of_frontier tree 0 t3_169root t3_169jobs t3_169frontier t3_169all
theorem t3_170choices : plan833.choices=[4,6,10].map (options 3 3) := by rfl


theorem t3_170part0 : t3_170jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_170frontier : t3_170root.frontier 0=t3_170jobs := by rfl
theorem t3_170all : t3_170jobs.all (Job.check tree)=true := by
  simp only [t3_170jobs,List.all_append,List.all_nil,t3_170part0,Bool.and_self]
theorem t3_170checked : Checked tree [4,6,10] := by
  refine ⟨plan833,valid833,t3_170choices,?_⟩
  exact check_of_frontier tree 0 t3_170root t3_170jobs t3_170frontier t3_170all
theorem t3_171choices : plan834.choices=[4,7,7].map (options 3 3) := by rfl


theorem t3_171part0 : t3_171jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_171frontier : t3_171root.frontier 0=t3_171jobs := by rfl
theorem t3_171all : t3_171jobs.all (Job.check tree)=true := by
  simp only [t3_171jobs,List.all_append,List.all_nil,t3_171part0,Bool.and_self]
theorem t3_171checked : Checked tree [4,7,7] := by
  refine ⟨plan834,valid834,t3_171choices,?_⟩
  exact check_of_frontier tree 0 t3_171root t3_171jobs t3_171frontier t3_171all
theorem t3_172choices : plan795.choices=[4,8,2].map (options 3 2) := by rfl


theorem t3_172part0 : t3_172jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_172frontier : t3_172root.frontier 0=t3_172jobs := by rfl
theorem t3_172all : t3_172jobs.all (Job.check tree)=true := by
  simp only [t3_172jobs,List.all_append,List.all_nil,t3_172part0,Bool.and_self]
theorem t3_172checked : Checked tree [4,8,2] := by
  refine ⟨plan795,valid795,t3_172choices,?_⟩
  exact check_of_frontier tree 0 t3_172root t3_172jobs t3_172frontier t3_172all
theorem t3_173choices : plan796.choices=[4,8,3].map (options 3 2) := by rfl


theorem t3_173part0 : t3_173jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_173frontier : t3_173root.frontier 0=t3_173jobs := by rfl
theorem t3_173all : t3_173jobs.all (Job.check tree)=true := by
  simp only [t3_173jobs,List.all_append,List.all_nil,t3_173part0,Bool.and_self]
theorem t3_173checked : Checked tree [4,8,3] := by
  refine ⟨plan796,valid796,t3_173choices,?_⟩
  exact check_of_frontier tree 0 t3_173root t3_173jobs t3_173frontier t3_173all
theorem t3_174choices : plan835.choices=[4,8,5].map (options 3 3) := by rfl


theorem t3_174part0 : t3_174jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_174frontier : t3_174root.frontier 0=t3_174jobs := by rfl
theorem t3_174all : t3_174jobs.all (Job.check tree)=true := by
  simp only [t3_174jobs,List.all_append,List.all_nil,t3_174part0,Bool.and_self]
theorem t3_174checked : Checked tree [4,8,5] := by
  refine ⟨plan835,valid835,t3_174choices,?_⟩
  exact check_of_frontier tree 0 t3_174root t3_174jobs t3_174frontier t3_174all
theorem t3_175choices : plan836.choices=[4,8,6].map (options 3 3) := by rfl


theorem t3_175part0 : t3_175jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_175frontier : t3_175root.frontier 0=t3_175jobs := by rfl
theorem t3_175all : t3_175jobs.all (Job.check tree)=true := by
  simp only [t3_175jobs,List.all_append,List.all_nil,t3_175part0,Bool.and_self]
theorem t3_175checked : Checked tree [4,8,6] := by
  refine ⟨plan836,valid836,t3_175choices,?_⟩
  exact check_of_frontier tree 0 t3_175root t3_175jobs t3_175frontier t3_175all
theorem t3_176choices : plan837.choices=[4,8,7].map (options 3 3) := by rfl


theorem t3_176part0 : t3_176jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_176frontier : t3_176root.frontier 0=t3_176jobs := by rfl
theorem t3_176all : t3_176jobs.all (Job.check tree)=true := by
  simp only [t3_176jobs,List.all_append,List.all_nil,t3_176part0,Bool.and_self]
theorem t3_176checked : Checked tree [4,8,7] := by
  refine ⟨plan837,valid837,t3_176choices,?_⟩
  exact check_of_frontier tree 0 t3_176root t3_176jobs t3_176frontier t3_176all
theorem t3_177choices : plan838.choices=[4,8,8].map (options 3 3) := by rfl


theorem t3_177part0 : t3_177jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_177frontier : t3_177root.frontier 0=t3_177jobs := by rfl
theorem t3_177all : t3_177jobs.all (Job.check tree)=true := by
  simp only [t3_177jobs,List.all_append,List.all_nil,t3_177part0,Bool.and_self]
theorem t3_177checked : Checked tree [4,8,8] := by
  refine ⟨plan838,valid838,t3_177choices,?_⟩
  exact check_of_frontier tree 0 t3_177root t3_177jobs t3_177frontier t3_177all
theorem t3_178choices : plan839.choices=[4,8,9].map (options 3 3) := by rfl


theorem t3_178part0 : t3_178jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_178frontier : t3_178root.frontier 0=t3_178jobs := by rfl
theorem t3_178all : t3_178jobs.all (Job.check tree)=true := by
  simp only [t3_178jobs,List.all_append,List.all_nil,t3_178part0,Bool.and_self]
theorem t3_178checked : Checked tree [4,8,9] := by
  refine ⟨plan839,valid839,t3_178choices,?_⟩
  exact check_of_frontier tree 0 t3_178root t3_178jobs t3_178frontier t3_178all
theorem t3_179choices : plan840.choices=[4,8,10].map (options 3 3) := by rfl


theorem t3_179part0 : t3_179jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_179frontier : t3_179root.frontier 0=t3_179jobs := by rfl
theorem t3_179all : t3_179jobs.all (Job.check tree)=true := by
  simp only [t3_179jobs,List.all_append,List.all_nil,t3_179part0,Bool.and_self]
theorem t3_179checked : Checked tree [4,8,10] := by
  refine ⟨plan840,valid840,t3_179choices,?_⟩
  exact check_of_frontier tree 0 t3_179root t3_179jobs t3_179frontier t3_179all
theorem t3_180choices : plan797.choices=[4,9,3].map (options 3 2) := by rfl


theorem t3_180part0 : t3_180jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_180frontier : t3_180root.frontier 0=t3_180jobs := by rfl
theorem t3_180all : t3_180jobs.all (Job.check tree)=true := by
  simp only [t3_180jobs,List.all_append,List.all_nil,t3_180part0,Bool.and_self]
theorem t3_180checked : Checked tree [4,9,3] := by
  refine ⟨plan797,valid797,t3_180choices,?_⟩
  exact check_of_frontier tree 0 t3_180root t3_180jobs t3_180frontier t3_180all
theorem t3_181choices : plan841.choices=[4,9,6].map (options 3 3) := by rfl


theorem t3_181part0 : t3_181jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_181frontier : t3_181root.frontier 0=t3_181jobs := by rfl
theorem t3_181all : t3_181jobs.all (Job.check tree)=true := by
  simp only [t3_181jobs,List.all_append,List.all_nil,t3_181part0,Bool.and_self]
theorem t3_181checked : Checked tree [4,9,6] := by
  refine ⟨plan841,valid841,t3_181choices,?_⟩
  exact check_of_frontier tree 0 t3_181root t3_181jobs t3_181frontier t3_181all
theorem t3_182choices : plan842.choices=[4,9,7].map (options 3 3) := by rfl


theorem t3_182part0 : t3_182jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_182frontier : t3_182root.frontier 0=t3_182jobs := by rfl
theorem t3_182all : t3_182jobs.all (Job.check tree)=true := by
  simp only [t3_182jobs,List.all_append,List.all_nil,t3_182part0,Bool.and_self]
theorem t3_182checked : Checked tree [4,9,7] := by
  refine ⟨plan842,valid842,t3_182choices,?_⟩
  exact check_of_frontier tree 0 t3_182root t3_182jobs t3_182frontier t3_182all
theorem t3_183choices : plan843.choices=[4,9,9].map (options 3 3) := by rfl


theorem t3_183part0 : t3_183jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_183frontier : t3_183root.frontier 0=t3_183jobs := by rfl
theorem t3_183all : t3_183jobs.all (Job.check tree)=true := by
  simp only [t3_183jobs,List.all_append,List.all_nil,t3_183part0,Bool.and_self]
theorem t3_183checked : Checked tree [4,9,9] := by
  refine ⟨plan843,valid843,t3_183choices,?_⟩
  exact check_of_frontier tree 0 t3_183root t3_183jobs t3_183frontier t3_183all
theorem t3_184choices : plan844.choices=[4,9,10].map (options 3 3) := by rfl


theorem t3_184part0 : t3_184jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_184frontier : t3_184root.frontier 0=t3_184jobs := by rfl
theorem t3_184all : t3_184jobs.all (Job.check tree)=true := by
  simp only [t3_184jobs,List.all_append,List.all_nil,t3_184part0,Bool.and_self]
theorem t3_184checked : Checked tree [4,9,10] := by
  refine ⟨plan844,valid844,t3_184choices,?_⟩
  exact check_of_frontier tree 0 t3_184root t3_184jobs t3_184frontier t3_184all
theorem t3_185choices : plan845.choices=[4,10,7].map (options 3 3) := by rfl


theorem t3_185part0 : t3_185jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_185frontier : t3_185root.frontier 0=t3_185jobs := by rfl
theorem t3_185all : t3_185jobs.all (Job.check tree)=true := by
  simp only [t3_185jobs,List.all_append,List.all_nil,t3_185part0,Bool.and_self]
theorem t3_185checked : Checked tree [4,10,7] := by
  refine ⟨plan845,valid845,t3_185choices,?_⟩
  exact check_of_frontier tree 0 t3_185root t3_185jobs t3_185frontier t3_185all
theorem t3_186choices : plan846.choices=[4,10,10].map (options 3 3) := by rfl


theorem t3_186part0 : t3_186jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_186frontier : t3_186root.frontier 0=t3_186jobs := by rfl
theorem t3_186all : t3_186jobs.all (Job.check tree)=true := by
  simp only [t3_186jobs,List.all_append,List.all_nil,t3_186part0,Bool.and_self]
theorem t3_186checked : Checked tree [4,10,10] := by
  refine ⟨plan846,valid846,t3_186choices,?_⟩
  exact check_of_frontier tree 0 t3_186root t3_186jobs t3_186frontier t3_186all
theorem t3_187choices : plan705.choices=[5,3,3].map (options 3 1) := by rfl


theorem t3_187part0 : t3_187jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_187frontier : t3_187root.frontier 0=t3_187jobs := by rfl
theorem t3_187all : t3_187jobs.all (Job.check tree)=true := by
  simp only [t3_187jobs,List.all_append,List.all_nil,t3_187part0,Bool.and_self]
theorem t3_187checked : Checked tree [5,3,3] := by
  refine ⟨plan705,valid705,t3_187choices,?_⟩
  exact check_of_frontier tree 0 t3_187root t3_187jobs t3_187frontier t3_187all
theorem t3_188choices : plan798.choices=[5,3,6].map (options 3 2) := by rfl


theorem t3_188part0 : t3_188jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_188frontier : t3_188root.frontier 0=t3_188jobs := by rfl
theorem t3_188all : t3_188jobs.all (Job.check tree)=true := by
  simp only [t3_188jobs,List.all_append,List.all_nil,t3_188part0,Bool.and_self]
theorem t3_188checked : Checked tree [5,3,6] := by
  refine ⟨plan798,valid798,t3_188choices,?_⟩
  exact check_of_frontier tree 0 t3_188root t3_188jobs t3_188frontier t3_188all
theorem t3_189choices : plan799.choices=[5,3,7].map (options 3 2) := by rfl


theorem t3_189part0 : t3_189jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_189frontier : t3_189root.frontier 0=t3_189jobs := by rfl
theorem t3_189all : t3_189jobs.all (Job.check tree)=true := by
  simp only [t3_189jobs,List.all_append,List.all_nil,t3_189part0,Bool.and_self]
theorem t3_189checked : Checked tree [5,3,7] := by
  refine ⟨plan799,valid799,t3_189choices,?_⟩
  exact check_of_frontier tree 0 t3_189root t3_189jobs t3_189frontier t3_189all
theorem t3_190choices : plan800.choices=[5,3,10].map (options 3 2) := by rfl


theorem t3_190part0 : t3_190jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_190frontier : t3_190root.frontier 0=t3_190jobs := by rfl
theorem t3_190all : t3_190jobs.all (Job.check tree)=true := by
  simp only [t3_190jobs,List.all_append,List.all_nil,t3_190part0,Bool.and_self]
theorem t3_190checked : Checked tree [5,3,10] := by
  refine ⟨plan800,valid800,t3_190choices,?_⟩
  exact check_of_frontier tree 0 t3_190root t3_190jobs t3_190frontier t3_190all
theorem t3_191choices : plan801.choices=[5,5,3].map (options 3 2) := by rfl


theorem t3_191part0 : t3_191jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_191frontier : t3_191root.frontier 0=t3_191jobs := by rfl
theorem t3_191all : t3_191jobs.all (Job.check tree)=true := by
  simp only [t3_191jobs,List.all_append,List.all_nil,t3_191part0,Bool.and_self]
theorem t3_191checked : Checked tree [5,5,3] := by
  refine ⟨plan801,valid801,t3_191choices,?_⟩
  exact check_of_frontier tree 0 t3_191root t3_191jobs t3_191frontier t3_191all
theorem t3_192choices : plan847.choices=[5,5,5].map (options 3 3) := by rfl


theorem t3_192part0 : t3_192jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_192frontier : t3_192root.frontier 0=t3_192jobs := by rfl
theorem t3_192all : t3_192jobs.all (Job.check tree)=true := by
  simp only [t3_192jobs,List.all_append,List.all_nil,t3_192part0,Bool.and_self]
theorem t3_192checked : Checked tree [5,5,5] := by
  refine ⟨plan847,valid847,t3_192choices,?_⟩
  exact check_of_frontier tree 0 t3_192root t3_192jobs t3_192frontier t3_192all
theorem t3_193choices : plan848.choices=[5,5,6].map (options 3 3) := by rfl


theorem t3_193part0 : t3_193jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_193frontier : t3_193root.frontier 0=t3_193jobs := by rfl
theorem t3_193all : t3_193jobs.all (Job.check tree)=true := by
  simp only [t3_193jobs,List.all_append,List.all_nil,t3_193part0,Bool.and_self]
theorem t3_193checked : Checked tree [5,5,6] := by
  refine ⟨plan848,valid848,t3_193choices,?_⟩
  exact check_of_frontier tree 0 t3_193root t3_193jobs t3_193frontier t3_193all
theorem t3_194choices : plan849.choices=[5,5,7].map (options 3 3) := by rfl


theorem t3_194part0 : t3_194jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_194frontier : t3_194root.frontier 0=t3_194jobs := by rfl
theorem t3_194all : t3_194jobs.all (Job.check tree)=true := by
  simp only [t3_194jobs,List.all_append,List.all_nil,t3_194part0,Bool.and_self]
theorem t3_194checked : Checked tree [5,5,7] := by
  refine ⟨plan849,valid849,t3_194choices,?_⟩
  exact check_of_frontier tree 0 t3_194root t3_194jobs t3_194frontier t3_194all
theorem t3_195choices : plan850.choices=[5,5,9].map (options 3 3) := by rfl


theorem t3_195part0 : t3_195jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_195frontier : t3_195root.frontier 0=t3_195jobs := by rfl
theorem t3_195all : t3_195jobs.all (Job.check tree)=true := by
  simp only [t3_195jobs,List.all_append,List.all_nil,t3_195part0,Bool.and_self]
theorem t3_195checked : Checked tree [5,5,9] := by
  refine ⟨plan850,valid850,t3_195choices,?_⟩
  exact check_of_frontier tree 0 t3_195root t3_195jobs t3_195frontier t3_195all
theorem t3_196choices : plan851.choices=[5,5,10].map (options 3 3) := by rfl


theorem t3_196part0 : t3_196jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_196frontier : t3_196root.frontier 0=t3_196jobs := by rfl
theorem t3_196all : t3_196jobs.all (Job.check tree)=true := by
  simp only [t3_196jobs,List.all_append,List.all_nil,t3_196part0,Bool.and_self]
theorem t3_196checked : Checked tree [5,5,10] := by
  refine ⟨plan851,valid851,t3_196choices,?_⟩
  exact check_of_frontier tree 0 t3_196root t3_196jobs t3_196frontier t3_196all
theorem t3_197choices : plan852.choices=[5,6,6].map (options 3 3) := by rfl


theorem t3_197part0 : t3_197jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_197frontier : t3_197root.frontier 0=t3_197jobs := by rfl
theorem t3_197all : t3_197jobs.all (Job.check tree)=true := by
  simp only [t3_197jobs,List.all_append,List.all_nil,t3_197part0,Bool.and_self]
theorem t3_197checked : Checked tree [5,6,6] := by
  refine ⟨plan852,valid852,t3_197choices,?_⟩
  exact check_of_frontier tree 0 t3_197root t3_197jobs t3_197frontier t3_197all
theorem t3_198choices : plan853.choices=[5,6,7].map (options 3 3) := by rfl


theorem t3_198part0 : t3_198jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_198frontier : t3_198root.frontier 0=t3_198jobs := by rfl
theorem t3_198all : t3_198jobs.all (Job.check tree)=true := by
  simp only [t3_198jobs,List.all_append,List.all_nil,t3_198part0,Bool.and_self]
theorem t3_198checked : Checked tree [5,6,7] := by
  refine ⟨plan853,valid853,t3_198choices,?_⟩
  exact check_of_frontier tree 0 t3_198root t3_198jobs t3_198frontier t3_198all
theorem t3_199choices : plan854.choices=[5,6,10].map (options 3 3) := by rfl


theorem t3_199part0 : t3_199jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_199frontier : t3_199root.frontier 0=t3_199jobs := by rfl
theorem t3_199all : t3_199jobs.all (Job.check tree)=true := by
  simp only [t3_199jobs,List.all_append,List.all_nil,t3_199part0,Bool.and_self]
theorem t3_199checked : Checked tree [5,6,10] := by
  refine ⟨plan854,valid854,t3_199choices,?_⟩
  exact check_of_frontier tree 0 t3_199root t3_199jobs t3_199frontier t3_199all
theorem t3_200choices : plan855.choices=[5,7,7].map (options 3 3) := by rfl


theorem t3_200part0 : t3_200jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_200frontier : t3_200root.frontier 0=t3_200jobs := by rfl
theorem t3_200all : t3_200jobs.all (Job.check tree)=true := by
  simp only [t3_200jobs,List.all_append,List.all_nil,t3_200part0,Bool.and_self]
theorem t3_200checked : Checked tree [5,7,7] := by
  refine ⟨plan855,valid855,t3_200choices,?_⟩
  exact check_of_frontier tree 0 t3_200root t3_200jobs t3_200frontier t3_200all
theorem t3_201choices : plan802.choices=[5,9,3].map (options 3 2) := by rfl


theorem t3_201part0 : t3_201jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_201frontier : t3_201root.frontier 0=t3_201jobs := by rfl
theorem t3_201all : t3_201jobs.all (Job.check tree)=true := by
  simp only [t3_201jobs,List.all_append,List.all_nil,t3_201part0,Bool.and_self]
theorem t3_201checked : Checked tree [5,9,3] := by
  refine ⟨plan802,valid802,t3_201choices,?_⟩
  exact check_of_frontier tree 0 t3_201root t3_201jobs t3_201frontier t3_201all
theorem t3_202choices : plan856.choices=[5,9,6].map (options 3 3) := by rfl


theorem t3_202part0 : t3_202jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_202frontier : t3_202root.frontier 0=t3_202jobs := by rfl
theorem t3_202all : t3_202jobs.all (Job.check tree)=true := by
  simp only [t3_202jobs,List.all_append,List.all_nil,t3_202part0,Bool.and_self]
theorem t3_202checked : Checked tree [5,9,6] := by
  refine ⟨plan856,valid856,t3_202choices,?_⟩
  exact check_of_frontier tree 0 t3_202root t3_202jobs t3_202frontier t3_202all
theorem t3_203choices : plan857.choices=[5,9,7].map (options 3 3) := by rfl


theorem t3_203part0 : t3_203jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_203frontier : t3_203root.frontier 0=t3_203jobs := by rfl
theorem t3_203all : t3_203jobs.all (Job.check tree)=true := by
  simp only [t3_203jobs,List.all_append,List.all_nil,t3_203part0,Bool.and_self]
theorem t3_203checked : Checked tree [5,9,7] := by
  refine ⟨plan857,valid857,t3_203choices,?_⟩
  exact check_of_frontier tree 0 t3_203root t3_203jobs t3_203frontier t3_203all
theorem t3_204choices : plan858.choices=[5,9,9].map (options 3 3) := by rfl


theorem t3_204part0 : t3_204jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_204frontier : t3_204root.frontier 0=t3_204jobs := by rfl
theorem t3_204all : t3_204jobs.all (Job.check tree)=true := by
  simp only [t3_204jobs,List.all_append,List.all_nil,t3_204part0,Bool.and_self]
theorem t3_204checked : Checked tree [5,9,9] := by
  refine ⟨plan858,valid858,t3_204choices,?_⟩
  exact check_of_frontier tree 0 t3_204root t3_204jobs t3_204frontier t3_204all
theorem t3_205choices : plan859.choices=[5,9,10].map (options 3 3) := by rfl


theorem t3_205part0 : t3_205jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_205frontier : t3_205root.frontier 0=t3_205jobs := by rfl
theorem t3_205all : t3_205jobs.all (Job.check tree)=true := by
  simp only [t3_205jobs,List.all_append,List.all_nil,t3_205part0,Bool.and_self]
theorem t3_205checked : Checked tree [5,9,10] := by
  refine ⟨plan859,valid859,t3_205choices,?_⟩
  exact check_of_frontier tree 0 t3_205root t3_205jobs t3_205frontier t3_205all
theorem t3_206choices : plan860.choices=[5,10,7].map (options 3 3) := by rfl


theorem t3_206part0 : t3_206jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_206frontier : t3_206root.frontier 0=t3_206jobs := by rfl
theorem t3_206all : t3_206jobs.all (Job.check tree)=true := by
  simp only [t3_206jobs,List.all_append,List.all_nil,t3_206part0,Bool.and_self]
theorem t3_206checked : Checked tree [5,10,7] := by
  refine ⟨plan860,valid860,t3_206choices,?_⟩
  exact check_of_frontier tree 0 t3_206root t3_206jobs t3_206frontier t3_206all
theorem t3_207choices : plan861.choices=[5,10,10].map (options 3 3) := by rfl


theorem t3_207part0 : t3_207jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_207frontier : t3_207root.frontier 0=t3_207jobs := by rfl
theorem t3_207all : t3_207jobs.all (Job.check tree)=true := by
  simp only [t3_207jobs,List.all_append,List.all_nil,t3_207part0,Bool.and_self]
theorem t3_207checked : Checked tree [5,10,10] := by
  refine ⟨plan861,valid861,t3_207choices,?_⟩
  exact check_of_frontier tree 0 t3_207root t3_207jobs t3_207frontier t3_207all
theorem t3_208choices : plan862.choices=[6,6,6].map (options 3 3) := by rfl


theorem t3_208part0 : t3_208jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_208frontier : t3_208root.frontier 0=t3_208jobs := by rfl
theorem t3_208all : t3_208jobs.all (Job.check tree)=true := by
  simp only [t3_208jobs,List.all_append,List.all_nil,t3_208part0,Bool.and_self]
theorem t3_208checked : Checked tree [6,6,6] := by
  refine ⟨plan862,valid862,t3_208choices,?_⟩
  exact check_of_frontier tree 0 t3_208root t3_208jobs t3_208frontier t3_208all
theorem t3_209choices : plan863.choices=[6,6,7].map (options 3 3) := by rfl


theorem t3_209part0 : t3_209jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_209frontier : t3_209root.frontier 0=t3_209jobs := by rfl
theorem t3_209all : t3_209jobs.all (Job.check tree)=true := by
  simp only [t3_209jobs,List.all_append,List.all_nil,t3_209part0,Bool.and_self]
theorem t3_209checked : Checked tree [6,6,7] := by
  refine ⟨plan863,valid863,t3_209choices,?_⟩
  exact check_of_frontier tree 0 t3_209root t3_209jobs t3_209frontier t3_209all
theorem t3_210choices : plan864.choices=[6,6,10].map (options 3 3) := by rfl


theorem t3_210part0 : t3_210jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_210frontier : t3_210root.frontier 0=t3_210jobs := by rfl
theorem t3_210all : t3_210jobs.all (Job.check tree)=true := by
  simp only [t3_210jobs,List.all_append,List.all_nil,t3_210part0,Bool.and_self]
theorem t3_210checked : Checked tree [6,6,10] := by
  refine ⟨plan864,valid864,t3_210choices,?_⟩
  exact check_of_frontier tree 0 t3_210root t3_210jobs t3_210frontier t3_210all
theorem t3_211choices : plan865.choices=[6,7,7].map (options 3 3) := by rfl


theorem t3_211part0 : t3_211jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_211frontier : t3_211root.frontier 0=t3_211jobs := by rfl
theorem t3_211all : t3_211jobs.all (Job.check tree)=true := by
  simp only [t3_211jobs,List.all_append,List.all_nil,t3_211part0,Bool.and_self]
theorem t3_211checked : Checked tree [6,7,7] := by
  refine ⟨plan865,valid865,t3_211choices,?_⟩
  exact check_of_frontier tree 0 t3_211root t3_211jobs t3_211frontier t3_211all
theorem t3_212choices : plan866.choices=[6,10,7].map (options 3 3) := by rfl


theorem t3_212part0 : t3_212jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_212frontier : t3_212root.frontier 0=t3_212jobs := by rfl
theorem t3_212all : t3_212jobs.all (Job.check tree)=true := by
  simp only [t3_212jobs,List.all_append,List.all_nil,t3_212part0,Bool.and_self]
theorem t3_212checked : Checked tree [6,10,7] := by
  refine ⟨plan866,valid866,t3_212choices,?_⟩
  exact check_of_frontier tree 0 t3_212root t3_212jobs t3_212frontier t3_212all
theorem t3_213choices : plan867.choices=[6,10,10].map (options 3 3) := by rfl


theorem t3_213part0 : t3_213jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_213frontier : t3_213root.frontier 0=t3_213jobs := by rfl
theorem t3_213all : t3_213jobs.all (Job.check tree)=true := by
  simp only [t3_213jobs,List.all_append,List.all_nil,t3_213part0,Bool.and_self]
theorem t3_213checked : Checked tree [6,10,10] := by
  refine ⟨plan867,valid867,t3_213choices,?_⟩
  exact check_of_frontier tree 0 t3_213root t3_213jobs t3_213frontier t3_213all
theorem t3_214choices : plan868.choices=[7,7,7].map (options 3 3) := by rfl


theorem t3_214part0 : t3_214jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_214frontier : t3_214root.frontier 0=t3_214jobs := by rfl
theorem t3_214all : t3_214jobs.all (Job.check tree)=true := by
  simp only [t3_214jobs,List.all_append,List.all_nil,t3_214part0,Bool.and_self]
theorem t3_214checked : Checked tree [7,7,7] := by
  refine ⟨plan868,valid868,t3_214choices,?_⟩
  exact check_of_frontier tree 0 t3_214root t3_214jobs t3_214frontier t3_214all
theorem t3_215choices : plan706.choices=[8,2,2].map (options 3 1) := by rfl


theorem t3_215part0 : t3_215jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_215frontier : t3_215root.frontier 0=t3_215jobs := by rfl
theorem t3_215all : t3_215jobs.all (Job.check tree)=true := by
  simp only [t3_215jobs,List.all_append,List.all_nil,t3_215part0,Bool.and_self]
theorem t3_215checked : Checked tree [8,2,2] := by
  refine ⟨plan706,valid706,t3_215choices,?_⟩
  exact check_of_frontier tree 0 t3_215root t3_215jobs t3_215frontier t3_215all
theorem t3_216choices : plan707.choices=[8,2,3].map (options 3 1) := by rfl


theorem t3_216part0 : t3_216jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_216frontier : t3_216root.frontier 0=t3_216jobs := by rfl
theorem t3_216all : t3_216jobs.all (Job.check tree)=true := by
  simp only [t3_216jobs,List.all_append,List.all_nil,t3_216part0,Bool.and_self]
theorem t3_216checked : Checked tree [8,2,3] := by
  refine ⟨plan707,valid707,t3_216choices,?_⟩
  exact check_of_frontier tree 0 t3_216root t3_216jobs t3_216frontier t3_216all
theorem t3_217choices : plan803.choices=[8,2,5].map (options 3 2) := by rfl


theorem t3_217part0 : t3_217jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_217frontier : t3_217root.frontier 0=t3_217jobs := by rfl
theorem t3_217all : t3_217jobs.all (Job.check tree)=true := by
  simp only [t3_217jobs,List.all_append,List.all_nil,t3_217part0,Bool.and_self]
theorem t3_217checked : Checked tree [8,2,5] := by
  refine ⟨plan803,valid803,t3_217choices,?_⟩
  exact check_of_frontier tree 0 t3_217root t3_217jobs t3_217frontier t3_217all
theorem t3_218choices : plan804.choices=[8,2,6].map (options 3 2) := by rfl


theorem t3_218part0 : t3_218jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_218frontier : t3_218root.frontier 0=t3_218jobs := by rfl
theorem t3_218all : t3_218jobs.all (Job.check tree)=true := by
  simp only [t3_218jobs,List.all_append,List.all_nil,t3_218part0,Bool.and_self]
theorem t3_218checked : Checked tree [8,2,6] := by
  refine ⟨plan804,valid804,t3_218choices,?_⟩
  exact check_of_frontier tree 0 t3_218root t3_218jobs t3_218frontier t3_218all
theorem t3_219choices : plan805.choices=[8,2,7].map (options 3 2) := by rfl


theorem t3_219part0 : t3_219jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_219frontier : t3_219root.frontier 0=t3_219jobs := by rfl
theorem t3_219all : t3_219jobs.all (Job.check tree)=true := by
  simp only [t3_219jobs,List.all_append,List.all_nil,t3_219part0,Bool.and_self]
theorem t3_219checked : Checked tree [8,2,7] := by
  refine ⟨plan805,valid805,t3_219choices,?_⟩
  exact check_of_frontier tree 0 t3_219root t3_219jobs t3_219frontier t3_219all
theorem t3_220choices : plan806.choices=[8,2,9].map (options 3 2) := by rfl


theorem t3_220part0 : t3_220jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_220frontier : t3_220root.frontier 0=t3_220jobs := by rfl
theorem t3_220all : t3_220jobs.all (Job.check tree)=true := by
  simp only [t3_220jobs,List.all_append,List.all_nil,t3_220part0,Bool.and_self]
theorem t3_220checked : Checked tree [8,2,9] := by
  refine ⟨plan806,valid806,t3_220choices,?_⟩
  exact check_of_frontier tree 0 t3_220root t3_220jobs t3_220frontier t3_220all
theorem t3_221choices : plan807.choices=[8,2,10].map (options 3 2) := by rfl


theorem t3_221part0 : t3_221jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_221frontier : t3_221root.frontier 0=t3_221jobs := by rfl
theorem t3_221all : t3_221jobs.all (Job.check tree)=true := by
  simp only [t3_221jobs,List.all_append,List.all_nil,t3_221part0,Bool.and_self]
theorem t3_221checked : Checked tree [8,2,10] := by
  refine ⟨plan807,valid807,t3_221choices,?_⟩
  exact check_of_frontier tree 0 t3_221root t3_221jobs t3_221frontier t3_221all
theorem t3_222choices : plan708.choices=[8,3,3].map (options 3 1) := by rfl


theorem t3_222part0 : t3_222jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_222frontier : t3_222root.frontier 0=t3_222jobs := by rfl
theorem t3_222all : t3_222jobs.all (Job.check tree)=true := by
  simp only [t3_222jobs,List.all_append,List.all_nil,t3_222part0,Bool.and_self]
theorem t3_222checked : Checked tree [8,3,3] := by
  refine ⟨plan708,valid708,t3_222choices,?_⟩
  exact check_of_frontier tree 0 t3_222root t3_222jobs t3_222frontier t3_222all
theorem t3_223choices : plan808.choices=[8,3,6].map (options 3 2) := by rfl


theorem t3_223part0 : t3_223jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_223frontier : t3_223root.frontier 0=t3_223jobs := by rfl
theorem t3_223all : t3_223jobs.all (Job.check tree)=true := by
  simp only [t3_223jobs,List.all_append,List.all_nil,t3_223part0,Bool.and_self]
theorem t3_223checked : Checked tree [8,3,6] := by
  refine ⟨plan808,valid808,t3_223choices,?_⟩
  exact check_of_frontier tree 0 t3_223root t3_223jobs t3_223frontier t3_223all
theorem t3_224choices : plan809.choices=[8,3,7].map (options 3 2) := by rfl


theorem t3_224part0 : t3_224jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_224frontier : t3_224root.frontier 0=t3_224jobs := by rfl
theorem t3_224all : t3_224jobs.all (Job.check tree)=true := by
  simp only [t3_224jobs,List.all_append,List.all_nil,t3_224part0,Bool.and_self]
theorem t3_224checked : Checked tree [8,3,7] := by
  refine ⟨plan809,valid809,t3_224choices,?_⟩
  exact check_of_frontier tree 0 t3_224root t3_224jobs t3_224frontier t3_224all
theorem t3_225choices : plan810.choices=[8,3,10].map (options 3 2) := by rfl


theorem t3_225part0 : t3_225jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_225frontier : t3_225root.frontier 0=t3_225jobs := by rfl
theorem t3_225all : t3_225jobs.all (Job.check tree)=true := by
  simp only [t3_225jobs,List.all_append,List.all_nil,t3_225part0,Bool.and_self]
theorem t3_225checked : Checked tree [8,3,10] := by
  refine ⟨plan810,valid810,t3_225choices,?_⟩
  exact check_of_frontier tree 0 t3_225root t3_225jobs t3_225frontier t3_225all
theorem t3_226choices : plan811.choices=[8,5,3].map (options 3 2) := by rfl


theorem t3_226part0 : t3_226jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_226frontier : t3_226root.frontier 0=t3_226jobs := by rfl
theorem t3_226all : t3_226jobs.all (Job.check tree)=true := by
  simp only [t3_226jobs,List.all_append,List.all_nil,t3_226part0,Bool.and_self]
theorem t3_226checked : Checked tree [8,5,3] := by
  refine ⟨plan811,valid811,t3_226choices,?_⟩
  exact check_of_frontier tree 0 t3_226root t3_226jobs t3_226frontier t3_226all
theorem t3_227choices : plan869.choices=[8,5,5].map (options 3 3) := by rfl


theorem t3_227part0 : t3_227jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_227frontier : t3_227root.frontier 0=t3_227jobs := by rfl
theorem t3_227all : t3_227jobs.all (Job.check tree)=true := by
  simp only [t3_227jobs,List.all_append,List.all_nil,t3_227part0,Bool.and_self]
theorem t3_227checked : Checked tree [8,5,5] := by
  refine ⟨plan869,valid869,t3_227choices,?_⟩
  exact check_of_frontier tree 0 t3_227root t3_227jobs t3_227frontier t3_227all
theorem t3_228choices : plan870.choices=[8,5,6].map (options 3 3) := by rfl


theorem t3_228part0 : t3_228jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_228frontier : t3_228root.frontier 0=t3_228jobs := by rfl
theorem t3_228all : t3_228jobs.all (Job.check tree)=true := by
  simp only [t3_228jobs,List.all_append,List.all_nil,t3_228part0,Bool.and_self]
theorem t3_228checked : Checked tree [8,5,6] := by
  refine ⟨plan870,valid870,t3_228choices,?_⟩
  exact check_of_frontier tree 0 t3_228root t3_228jobs t3_228frontier t3_228all
theorem t3_229choices : plan871.choices=[8,5,7].map (options 3 3) := by rfl


theorem t3_229part0 : t3_229jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_229frontier : t3_229root.frontier 0=t3_229jobs := by rfl
theorem t3_229all : t3_229jobs.all (Job.check tree)=true := by
  simp only [t3_229jobs,List.all_append,List.all_nil,t3_229part0,Bool.and_self]
theorem t3_229checked : Checked tree [8,5,7] := by
  refine ⟨plan871,valid871,t3_229choices,?_⟩
  exact check_of_frontier tree 0 t3_229root t3_229jobs t3_229frontier t3_229all
theorem t3_230choices : plan872.choices=[8,5,9].map (options 3 3) := by rfl


theorem t3_230part0 : t3_230jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_230frontier : t3_230root.frontier 0=t3_230jobs := by rfl
theorem t3_230all : t3_230jobs.all (Job.check tree)=true := by
  simp only [t3_230jobs,List.all_append,List.all_nil,t3_230part0,Bool.and_self]
theorem t3_230checked : Checked tree [8,5,9] := by
  refine ⟨plan872,valid872,t3_230choices,?_⟩
  exact check_of_frontier tree 0 t3_230root t3_230jobs t3_230frontier t3_230all
theorem t3_231choices : plan873.choices=[8,5,10].map (options 3 3) := by rfl


theorem t3_231part0 : t3_231jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_231frontier : t3_231root.frontier 0=t3_231jobs := by rfl
theorem t3_231all : t3_231jobs.all (Job.check tree)=true := by
  simp only [t3_231jobs,List.all_append,List.all_nil,t3_231part0,Bool.and_self]
theorem t3_231checked : Checked tree [8,5,10] := by
  refine ⟨plan873,valid873,t3_231choices,?_⟩
  exact check_of_frontier tree 0 t3_231root t3_231jobs t3_231frontier t3_231all
theorem t3_232choices : plan874.choices=[8,6,6].map (options 3 3) := by rfl


theorem t3_232part0 : t3_232jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_232frontier : t3_232root.frontier 0=t3_232jobs := by rfl
theorem t3_232all : t3_232jobs.all (Job.check tree)=true := by
  simp only [t3_232jobs,List.all_append,List.all_nil,t3_232part0,Bool.and_self]
theorem t3_232checked : Checked tree [8,6,6] := by
  refine ⟨plan874,valid874,t3_232choices,?_⟩
  exact check_of_frontier tree 0 t3_232root t3_232jobs t3_232frontier t3_232all
theorem t3_233choices : plan875.choices=[8,6,7].map (options 3 3) := by rfl


theorem t3_233part0 : t3_233jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_233frontier : t3_233root.frontier 0=t3_233jobs := by rfl
theorem t3_233all : t3_233jobs.all (Job.check tree)=true := by
  simp only [t3_233jobs,List.all_append,List.all_nil,t3_233part0,Bool.and_self]
theorem t3_233checked : Checked tree [8,6,7] := by
  refine ⟨plan875,valid875,t3_233choices,?_⟩
  exact check_of_frontier tree 0 t3_233root t3_233jobs t3_233frontier t3_233all
theorem t3_234choices : plan876.choices=[8,6,10].map (options 3 3) := by rfl


theorem t3_234part0 : t3_234jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_234frontier : t3_234root.frontier 0=t3_234jobs := by rfl
theorem t3_234all : t3_234jobs.all (Job.check tree)=true := by
  simp only [t3_234jobs,List.all_append,List.all_nil,t3_234part0,Bool.and_self]
theorem t3_234checked : Checked tree [8,6,10] := by
  refine ⟨plan876,valid876,t3_234choices,?_⟩
  exact check_of_frontier tree 0 t3_234root t3_234jobs t3_234frontier t3_234all
theorem t3_235choices : plan877.choices=[8,7,7].map (options 3 3) := by rfl


theorem t3_235part0 : t3_235jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_235frontier : t3_235root.frontier 0=t3_235jobs := by rfl
theorem t3_235all : t3_235jobs.all (Job.check tree)=true := by
  simp only [t3_235jobs,List.all_append,List.all_nil,t3_235part0,Bool.and_self]
theorem t3_235checked : Checked tree [8,7,7] := by
  refine ⟨plan877,valid877,t3_235choices,?_⟩
  exact check_of_frontier tree 0 t3_235root t3_235jobs t3_235frontier t3_235all
theorem t3_236choices : plan812.choices=[8,8,2].map (options 3 2) := by rfl


theorem t3_236part0 : t3_236jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_236frontier : t3_236root.frontier 0=t3_236jobs := by rfl
theorem t3_236all : t3_236jobs.all (Job.check tree)=true := by
  simp only [t3_236jobs,List.all_append,List.all_nil,t3_236part0,Bool.and_self]
theorem t3_236checked : Checked tree [8,8,2] := by
  refine ⟨plan812,valid812,t3_236choices,?_⟩
  exact check_of_frontier tree 0 t3_236root t3_236jobs t3_236frontier t3_236all
theorem t3_237choices : plan813.choices=[8,8,3].map (options 3 2) := by rfl


theorem t3_237part0 : t3_237jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_237frontier : t3_237root.frontier 0=t3_237jobs := by rfl
theorem t3_237all : t3_237jobs.all (Job.check tree)=true := by
  simp only [t3_237jobs,List.all_append,List.all_nil,t3_237part0,Bool.and_self]
theorem t3_237checked : Checked tree [8,8,3] := by
  refine ⟨plan813,valid813,t3_237choices,?_⟩
  exact check_of_frontier tree 0 t3_237root t3_237jobs t3_237frontier t3_237all
theorem t3_238choices : plan878.choices=[8,8,5].map (options 3 3) := by rfl


theorem t3_238part0 : t3_238jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_238frontier : t3_238root.frontier 0=t3_238jobs := by rfl
theorem t3_238all : t3_238jobs.all (Job.check tree)=true := by
  simp only [t3_238jobs,List.all_append,List.all_nil,t3_238part0,Bool.and_self]
theorem t3_238checked : Checked tree [8,8,5] := by
  refine ⟨plan878,valid878,t3_238choices,?_⟩
  exact check_of_frontier tree 0 t3_238root t3_238jobs t3_238frontier t3_238all
theorem t3_239choices : plan879.choices=[8,8,6].map (options 3 3) := by rfl


theorem t3_239part0 : t3_239jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_239frontier : t3_239root.frontier 0=t3_239jobs := by rfl
theorem t3_239all : t3_239jobs.all (Job.check tree)=true := by
  simp only [t3_239jobs,List.all_append,List.all_nil,t3_239part0,Bool.and_self]
theorem t3_239checked : Checked tree [8,8,6] := by
  refine ⟨plan879,valid879,t3_239choices,?_⟩
  exact check_of_frontier tree 0 t3_239root t3_239jobs t3_239frontier t3_239all
theorem t3_240choices : plan880.choices=[8,8,7].map (options 3 3) := by rfl


theorem t3_240part0 : t3_240jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_240frontier : t3_240root.frontier 0=t3_240jobs := by rfl
theorem t3_240all : t3_240jobs.all (Job.check tree)=true := by
  simp only [t3_240jobs,List.all_append,List.all_nil,t3_240part0,Bool.and_self]
theorem t3_240checked : Checked tree [8,8,7] := by
  refine ⟨plan880,valid880,t3_240choices,?_⟩
  exact check_of_frontier tree 0 t3_240root t3_240jobs t3_240frontier t3_240all
theorem t3_241choices : plan881.choices=[8,8,8].map (options 3 3) := by rfl


theorem t3_241part0 : t3_241jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_241frontier : t3_241root.frontier 0=t3_241jobs := by rfl
theorem t3_241all : t3_241jobs.all (Job.check tree)=true := by
  simp only [t3_241jobs,List.all_append,List.all_nil,t3_241part0,Bool.and_self]
theorem t3_241checked : Checked tree [8,8,8] := by
  refine ⟨plan881,valid881,t3_241choices,?_⟩
  exact check_of_frontier tree 0 t3_241root t3_241jobs t3_241frontier t3_241all
theorem t3_242choices : plan882.choices=[8,8,9].map (options 3 3) := by rfl


theorem t3_242part0 : t3_242jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_242frontier : t3_242root.frontier 0=t3_242jobs := by rfl
theorem t3_242all : t3_242jobs.all (Job.check tree)=true := by
  simp only [t3_242jobs,List.all_append,List.all_nil,t3_242part0,Bool.and_self]
theorem t3_242checked : Checked tree [8,8,9] := by
  refine ⟨plan882,valid882,t3_242choices,?_⟩
  exact check_of_frontier tree 0 t3_242root t3_242jobs t3_242frontier t3_242all
theorem t3_243choices : plan883.choices=[8,8,10].map (options 3 3) := by rfl


theorem t3_243part0 : t3_243jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_243frontier : t3_243root.frontier 0=t3_243jobs := by rfl
theorem t3_243all : t3_243jobs.all (Job.check tree)=true := by
  simp only [t3_243jobs,List.all_append,List.all_nil,t3_243part0,Bool.and_self]
theorem t3_243checked : Checked tree [8,8,10] := by
  refine ⟨plan883,valid883,t3_243choices,?_⟩
  exact check_of_frontier tree 0 t3_243root t3_243jobs t3_243frontier t3_243all
theorem t3_244choices : plan814.choices=[8,9,3].map (options 3 2) := by rfl


theorem t3_244part0 : t3_244jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_244frontier : t3_244root.frontier 0=t3_244jobs := by rfl
theorem t3_244all : t3_244jobs.all (Job.check tree)=true := by
  simp only [t3_244jobs,List.all_append,List.all_nil,t3_244part0,Bool.and_self]
theorem t3_244checked : Checked tree [8,9,3] := by
  refine ⟨plan814,valid814,t3_244choices,?_⟩
  exact check_of_frontier tree 0 t3_244root t3_244jobs t3_244frontier t3_244all
theorem t3_245choices : plan884.choices=[8,9,6].map (options 3 3) := by rfl


theorem t3_245part0 : t3_245jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_245frontier : t3_245root.frontier 0=t3_245jobs := by rfl
theorem t3_245all : t3_245jobs.all (Job.check tree)=true := by
  simp only [t3_245jobs,List.all_append,List.all_nil,t3_245part0,Bool.and_self]
theorem t3_245checked : Checked tree [8,9,6] := by
  refine ⟨plan884,valid884,t3_245choices,?_⟩
  exact check_of_frontier tree 0 t3_245root t3_245jobs t3_245frontier t3_245all
theorem t3_246choices : plan885.choices=[8,9,7].map (options 3 3) := by rfl


theorem t3_246part0 : t3_246jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_246frontier : t3_246root.frontier 0=t3_246jobs := by rfl
theorem t3_246all : t3_246jobs.all (Job.check tree)=true := by
  simp only [t3_246jobs,List.all_append,List.all_nil,t3_246part0,Bool.and_self]
theorem t3_246checked : Checked tree [8,9,7] := by
  refine ⟨plan885,valid885,t3_246choices,?_⟩
  exact check_of_frontier tree 0 t3_246root t3_246jobs t3_246frontier t3_246all
theorem t3_247choices : plan886.choices=[8,9,9].map (options 3 3) := by rfl


theorem t3_247part0 : t3_247jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_247frontier : t3_247root.frontier 0=t3_247jobs := by rfl
theorem t3_247all : t3_247jobs.all (Job.check tree)=true := by
  simp only [t3_247jobs,List.all_append,List.all_nil,t3_247part0,Bool.and_self]
theorem t3_247checked : Checked tree [8,9,9] := by
  refine ⟨plan886,valid886,t3_247choices,?_⟩
  exact check_of_frontier tree 0 t3_247root t3_247jobs t3_247frontier t3_247all
theorem t3_248choices : plan887.choices=[8,9,10].map (options 3 3) := by rfl


theorem t3_248part0 : t3_248jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_248frontier : t3_248root.frontier 0=t3_248jobs := by rfl
theorem t3_248all : t3_248jobs.all (Job.check tree)=true := by
  simp only [t3_248jobs,List.all_append,List.all_nil,t3_248part0,Bool.and_self]
theorem t3_248checked : Checked tree [8,9,10] := by
  refine ⟨plan887,valid887,t3_248choices,?_⟩
  exact check_of_frontier tree 0 t3_248root t3_248jobs t3_248frontier t3_248all
theorem t3_249choices : plan888.choices=[8,10,7].map (options 3 3) := by rfl


theorem t3_249part0 : t3_249jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_249frontier : t3_249root.frontier 0=t3_249jobs := by rfl
theorem t3_249all : t3_249jobs.all (Job.check tree)=true := by
  simp only [t3_249jobs,List.all_append,List.all_nil,t3_249part0,Bool.and_self]
theorem t3_249checked : Checked tree [8,10,7] := by
  refine ⟨plan888,valid888,t3_249choices,?_⟩
  exact check_of_frontier tree 0 t3_249root t3_249jobs t3_249frontier t3_249all
theorem t3_250choices : plan889.choices=[8,10,10].map (options 3 3) := by rfl


theorem t3_250part0 : t3_250jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_250frontier : t3_250root.frontier 0=t3_250jobs := by rfl
theorem t3_250all : t3_250jobs.all (Job.check tree)=true := by
  simp only [t3_250jobs,List.all_append,List.all_nil,t3_250part0,Bool.and_self]
theorem t3_250checked : Checked tree [8,10,10] := by
  refine ⟨plan889,valid889,t3_250choices,?_⟩
  exact check_of_frontier tree 0 t3_250root t3_250jobs t3_250frontier t3_250all
theorem t3_251choices : plan709.choices=[9,3,3].map (options 3 1) := by rfl


theorem t3_251part0 : t3_251jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_251frontier : t3_251root.frontier 0=t3_251jobs := by rfl
theorem t3_251all : t3_251jobs.all (Job.check tree)=true := by
  simp only [t3_251jobs,List.all_append,List.all_nil,t3_251part0,Bool.and_self]
theorem t3_251checked : Checked tree [9,3,3] := by
  refine ⟨plan709,valid709,t3_251choices,?_⟩
  exact check_of_frontier tree 0 t3_251root t3_251jobs t3_251frontier t3_251all
theorem t3_252choices : plan815.choices=[9,3,6].map (options 3 2) := by rfl


theorem t3_252part0 : t3_252jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_252frontier : t3_252root.frontier 0=t3_252jobs := by rfl
theorem t3_252all : t3_252jobs.all (Job.check tree)=true := by
  simp only [t3_252jobs,List.all_append,List.all_nil,t3_252part0,Bool.and_self]
theorem t3_252checked : Checked tree [9,3,6] := by
  refine ⟨plan815,valid815,t3_252choices,?_⟩
  exact check_of_frontier tree 0 t3_252root t3_252jobs t3_252frontier t3_252all
theorem t3_253choices : plan816.choices=[9,3,7].map (options 3 2) := by rfl


theorem t3_253part0 : t3_253jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_253frontier : t3_253root.frontier 0=t3_253jobs := by rfl
theorem t3_253all : t3_253jobs.all (Job.check tree)=true := by
  simp only [t3_253jobs,List.all_append,List.all_nil,t3_253part0,Bool.and_self]
theorem t3_253checked : Checked tree [9,3,7] := by
  refine ⟨plan816,valid816,t3_253choices,?_⟩
  exact check_of_frontier tree 0 t3_253root t3_253jobs t3_253frontier t3_253all
theorem t3_254choices : plan817.choices=[9,3,10].map (options 3 2) := by rfl


theorem t3_254part0 : t3_254jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_254frontier : t3_254root.frontier 0=t3_254jobs := by rfl
theorem t3_254all : t3_254jobs.all (Job.check tree)=true := by
  simp only [t3_254jobs,List.all_append,List.all_nil,t3_254part0,Bool.and_self]
theorem t3_254checked : Checked tree [9,3,10] := by
  refine ⟨plan817,valid817,t3_254choices,?_⟩
  exact check_of_frontier tree 0 t3_254root t3_254jobs t3_254frontier t3_254all
theorem t3_255choices : plan890.choices=[9,6,6].map (options 3 3) := by rfl


theorem t3_255part0 : t3_255jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_255frontier : t3_255root.frontier 0=t3_255jobs := by rfl
theorem t3_255all : t3_255jobs.all (Job.check tree)=true := by
  simp only [t3_255jobs,List.all_append,List.all_nil,t3_255part0,Bool.and_self]
theorem t3_255checked : Checked tree [9,6,6] := by
  refine ⟨plan890,valid890,t3_255choices,?_⟩
  exact check_of_frontier tree 0 t3_255root t3_255jobs t3_255frontier t3_255all
theorem t3_256choices : plan891.choices=[9,6,7].map (options 3 3) := by rfl


theorem t3_256part0 : t3_256jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_256frontier : t3_256root.frontier 0=t3_256jobs := by rfl
theorem t3_256all : t3_256jobs.all (Job.check tree)=true := by
  simp only [t3_256jobs,List.all_append,List.all_nil,t3_256part0,Bool.and_self]
theorem t3_256checked : Checked tree [9,6,7] := by
  refine ⟨plan891,valid891,t3_256choices,?_⟩
  exact check_of_frontier tree 0 t3_256root t3_256jobs t3_256frontier t3_256all
theorem t3_257choices : plan892.choices=[9,6,10].map (options 3 3) := by rfl


theorem t3_257part0 : t3_257jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_257frontier : t3_257root.frontier 0=t3_257jobs := by rfl
theorem t3_257all : t3_257jobs.all (Job.check tree)=true := by
  simp only [t3_257jobs,List.all_append,List.all_nil,t3_257part0,Bool.and_self]
theorem t3_257checked : Checked tree [9,6,10] := by
  refine ⟨plan892,valid892,t3_257choices,?_⟩
  exact check_of_frontier tree 0 t3_257root t3_257jobs t3_257frontier t3_257all
theorem t3_258choices : plan893.choices=[9,7,7].map (options 3 3) := by rfl


theorem t3_258part0 : t3_258jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_258frontier : t3_258root.frontier 0=t3_258jobs := by rfl
theorem t3_258all : t3_258jobs.all (Job.check tree)=true := by
  simp only [t3_258jobs,List.all_append,List.all_nil,t3_258part0,Bool.and_self]
theorem t3_258checked : Checked tree [9,7,7] := by
  refine ⟨plan893,valid893,t3_258choices,?_⟩
  exact check_of_frontier tree 0 t3_258root t3_258jobs t3_258frontier t3_258all
theorem t3_259choices : plan818.choices=[9,9,3].map (options 3 2) := by rfl


theorem t3_259part0 : t3_259jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_259frontier : t3_259root.frontier 0=t3_259jobs := by rfl
theorem t3_259all : t3_259jobs.all (Job.check tree)=true := by
  simp only [t3_259jobs,List.all_append,List.all_nil,t3_259part0,Bool.and_self]
theorem t3_259checked : Checked tree [9,9,3] := by
  refine ⟨plan818,valid818,t3_259choices,?_⟩
  exact check_of_frontier tree 0 t3_259root t3_259jobs t3_259frontier t3_259all
theorem t3_260choices : plan894.choices=[9,9,6].map (options 3 3) := by rfl


theorem t3_260part0 : t3_260jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_260frontier : t3_260root.frontier 0=t3_260jobs := by rfl
theorem t3_260all : t3_260jobs.all (Job.check tree)=true := by
  simp only [t3_260jobs,List.all_append,List.all_nil,t3_260part0,Bool.and_self]
theorem t3_260checked : Checked tree [9,9,6] := by
  refine ⟨plan894,valid894,t3_260choices,?_⟩
  exact check_of_frontier tree 0 t3_260root t3_260jobs t3_260frontier t3_260all
theorem t3_261choices : plan895.choices=[9,9,7].map (options 3 3) := by rfl


theorem t3_261part0 : t3_261jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_261frontier : t3_261root.frontier 0=t3_261jobs := by rfl
theorem t3_261all : t3_261jobs.all (Job.check tree)=true := by
  simp only [t3_261jobs,List.all_append,List.all_nil,t3_261part0,Bool.and_self]
theorem t3_261checked : Checked tree [9,9,7] := by
  refine ⟨plan895,valid895,t3_261choices,?_⟩
  exact check_of_frontier tree 0 t3_261root t3_261jobs t3_261frontier t3_261all
theorem t3_262choices : plan896.choices=[9,9,9].map (options 3 3) := by rfl


theorem t3_262part0 : t3_262jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_262frontier : t3_262root.frontier 0=t3_262jobs := by rfl
theorem t3_262all : t3_262jobs.all (Job.check tree)=true := by
  simp only [t3_262jobs,List.all_append,List.all_nil,t3_262part0,Bool.and_self]
theorem t3_262checked : Checked tree [9,9,9] := by
  refine ⟨plan896,valid896,t3_262choices,?_⟩
  exact check_of_frontier tree 0 t3_262root t3_262jobs t3_262frontier t3_262all
theorem t3_263choices : plan897.choices=[9,9,10].map (options 3 3) := by rfl


theorem t3_263part0 : t3_263jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_263frontier : t3_263root.frontier 0=t3_263jobs := by rfl
theorem t3_263all : t3_263jobs.all (Job.check tree)=true := by
  simp only [t3_263jobs,List.all_append,List.all_nil,t3_263part0,Bool.and_self]
theorem t3_263checked : Checked tree [9,9,10] := by
  refine ⟨plan897,valid897,t3_263choices,?_⟩
  exact check_of_frontier tree 0 t3_263root t3_263jobs t3_263frontier t3_263all
theorem t3_264choices : plan898.choices=[9,10,7].map (options 3 3) := by rfl


theorem t3_264part0 : t3_264jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_264frontier : t3_264root.frontier 0=t3_264jobs := by rfl
theorem t3_264all : t3_264jobs.all (Job.check tree)=true := by
  simp only [t3_264jobs,List.all_append,List.all_nil,t3_264part0,Bool.and_self]
theorem t3_264checked : Checked tree [9,10,7] := by
  refine ⟨plan898,valid898,t3_264choices,?_⟩
  exact check_of_frontier tree 0 t3_264root t3_264jobs t3_264frontier t3_264all
theorem t3_265choices : plan899.choices=[9,10,10].map (options 3 3) := by rfl


theorem t3_265part0 : t3_265jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_265frontier : t3_265root.frontier 0=t3_265jobs := by rfl
theorem t3_265all : t3_265jobs.all (Job.check tree)=true := by
  simp only [t3_265jobs,List.all_append,List.all_nil,t3_265part0,Bool.and_self]
theorem t3_265checked : Checked tree [9,10,10] := by
  refine ⟨plan899,valid899,t3_265choices,?_⟩
  exact check_of_frontier tree 0 t3_265root t3_265jobs t3_265frontier t3_265all
theorem t3_266choices : plan900.choices=[10,7,7].map (options 3 3) := by rfl


theorem t3_266part0 : t3_266jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_266frontier : t3_266root.frontier 0=t3_266jobs := by rfl
theorem t3_266all : t3_266jobs.all (Job.check tree)=true := by
  simp only [t3_266jobs,List.all_append,List.all_nil,t3_266part0,Bool.and_self]
theorem t3_266checked : Checked tree [10,7,7] := by
  refine ⟨plan900,valid900,t3_266choices,?_⟩
  exact check_of_frontier tree 0 t3_266root t3_266jobs t3_266frontier t3_266all
theorem t3_267choices : plan901.choices=[10,10,7].map (options 3 3) := by rfl


theorem t3_267part0 : t3_267jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_267frontier : t3_267root.frontier 0=t3_267jobs := by rfl
theorem t3_267all : t3_267jobs.all (Job.check tree)=true := by
  simp only [t3_267jobs,List.all_append,List.all_nil,t3_267part0,Bool.and_self]
theorem t3_267checked : Checked tree [10,10,7] := by
  refine ⟨plan901,valid901,t3_267choices,?_⟩
  exact check_of_frontier tree 0 t3_267root t3_267jobs t3_267frontier t3_267all
theorem t3_268choices : plan902.choices=[10,10,10].map (options 3 3) := by rfl


theorem t3_268part0 : t3_268jobs0.all (Job.check tree)=true := by decide +kernel

theorem t3_268frontier : t3_268root.frontier 0=t3_268jobs := by rfl
theorem t3_268all : t3_268jobs.all (Job.check tree)=true := by
  simp only [t3_268jobs,List.all_append,List.all_nil,t3_268part0,Bool.and_self]
theorem t3_268checked : Checked tree [10,10,10] := by
  refine ⟨plan902,valid902,t3_268choices,?_⟩
  exact check_of_frontier tree 0 t3_268root t3_268jobs t3_268frontier t3_268all
theorem t4_0choices : plan1694.choices=[0,1,2,3].map (options 4 0) := by rfl


theorem t4_0part0 : t4_0jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_0frontier : t4_0root.frontier 0=t4_0jobs := by rfl
theorem t4_0all : t4_0jobs.all (Job.check tree)=true := by
  simp only [t4_0jobs,List.all_append,List.all_nil,t4_0part0,Bool.and_self]
theorem t4_0checked : Checked tree [0,1,2,3] := by
  refine ⟨plan1694,valid1694,t4_0choices,?_⟩
  exact check_of_frontier tree 0 t4_0root t4_0jobs t4_0frontier t4_0all
theorem t4_1choices : plan1713.choices=[0,1,2,6].map (options 4 1) := by rfl


theorem t4_1part0 : t4_1jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_1frontier : t4_1root.frontier 0=t4_1jobs := by rfl
theorem t4_1all : t4_1jobs.all (Job.check tree)=true := by
  simp only [t4_1jobs,List.all_append,List.all_nil,t4_1part0,Bool.and_self]
theorem t4_1checked : Checked tree [0,1,2,6] := by
  refine ⟨plan1713,valid1713,t4_1choices,?_⟩
  exact check_of_frontier tree 0 t4_1root t4_1jobs t4_1frontier t4_1all
theorem t4_2choices : plan1714.choices=[0,1,2,7].map (options 4 1) := by rfl


theorem t4_2part0 : t4_2jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_2frontier : t4_2root.frontier 0=t4_2jobs := by rfl
theorem t4_2all : t4_2jobs.all (Job.check tree)=true := by
  simp only [t4_2jobs,List.all_append,List.all_nil,t4_2part0,Bool.and_self]
theorem t4_2checked : Checked tree [0,1,2,7] := by
  refine ⟨plan1714,valid1714,t4_2choices,?_⟩
  exact check_of_frontier tree 0 t4_2root t4_2jobs t4_2frontier t4_2all
theorem t4_3choices : plan1715.choices=[0,1,2,10].map (options 4 1) := by rfl


theorem t4_3part0 : t4_3jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_3frontier : t4_3root.frontier 0=t4_3jobs := by rfl
theorem t4_3all : t4_3jobs.all (Job.check tree)=true := by
  simp only [t4_3jobs,List.all_append,List.all_nil,t4_3part0,Bool.and_self]
theorem t4_3checked : Checked tree [0,1,2,10] := by
  refine ⟨plan1715,valid1715,t4_3choices,?_⟩
  exact check_of_frontier tree 0 t4_3root t4_3jobs t4_3frontier t4_3all
theorem t4_4choices : plan1695.choices=[0,1,3,3].map (options 4 0) := by rfl


theorem t4_4part0 : t4_4jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_4frontier : t4_4root.frontier 0=t4_4jobs := by rfl
theorem t4_4all : t4_4jobs.all (Job.check tree)=true := by
  simp only [t4_4jobs,List.all_append,List.all_nil,t4_4part0,Bool.and_self]
theorem t4_4checked : Checked tree [0,1,3,3] := by
  refine ⟨plan1695,valid1695,t4_4choices,?_⟩
  exact check_of_frontier tree 0 t4_4root t4_4jobs t4_4frontier t4_4all
theorem t4_5choices : plan1716.choices=[0,1,3,6].map (options 4 1) := by rfl


theorem t4_5part0 : t4_5jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_5frontier : t4_5root.frontier 0=t4_5jobs := by rfl
theorem t4_5all : t4_5jobs.all (Job.check tree)=true := by
  simp only [t4_5jobs,List.all_append,List.all_nil,t4_5part0,Bool.and_self]
theorem t4_5checked : Checked tree [0,1,3,6] := by
  refine ⟨plan1716,valid1716,t4_5choices,?_⟩
  exact check_of_frontier tree 0 t4_5root t4_5jobs t4_5frontier t4_5all
theorem t4_6choices : plan1717.choices=[0,1,3,7].map (options 4 1) := by rfl


theorem t4_6part0 : t4_6jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_6frontier : t4_6root.frontier 0=t4_6jobs := by rfl
theorem t4_6all : t4_6jobs.all (Job.check tree)=true := by
  simp only [t4_6jobs,List.all_append,List.all_nil,t4_6part0,Bool.and_self]
theorem t4_6checked : Checked tree [0,1,3,7] := by
  refine ⟨plan1717,valid1717,t4_6choices,?_⟩
  exact check_of_frontier tree 0 t4_6root t4_6jobs t4_6frontier t4_6all
theorem t4_7choices : plan1718.choices=[0,1,3,10].map (options 4 1) := by rfl


theorem t4_7part0 : t4_7jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_7frontier : t4_7root.frontier 0=t4_7jobs := by rfl
theorem t4_7all : t4_7jobs.all (Job.check tree)=true := by
  simp only [t4_7jobs,List.all_append,List.all_nil,t4_7part0,Bool.and_self]
theorem t4_7checked : Checked tree [0,1,3,10] := by
  refine ⟨plan1718,valid1718,t4_7choices,?_⟩
  exact check_of_frontier tree 0 t4_7root t4_7jobs t4_7frontier t4_7all
theorem t4_8choices : plan1719.choices=[0,1,5,3].map (options 4 1) := by rfl


theorem t4_8part0 : t4_8jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_8frontier : t4_8root.frontier 0=t4_8jobs := by rfl
theorem t4_8all : t4_8jobs.all (Job.check tree)=true := by
  simp only [t4_8jobs,List.all_append,List.all_nil,t4_8part0,Bool.and_self]
theorem t4_8checked : Checked tree [0,1,5,3] := by
  refine ⟨plan1719,valid1719,t4_8choices,?_⟩
  exact check_of_frontier tree 0 t4_8root t4_8jobs t4_8frontier t4_8all
theorem t4_9choices : plan1804.choices=[0,1,5,6].map (options 4 2) := by rfl


theorem t4_9part0 : t4_9jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_9frontier : t4_9root.frontier 0=t4_9jobs := by rfl
theorem t4_9all : t4_9jobs.all (Job.check tree)=true := by
  simp only [t4_9jobs,List.all_append,List.all_nil,t4_9part0,Bool.and_self]
theorem t4_9checked : Checked tree [0,1,5,6] := by
  refine ⟨plan1804,valid1804,t4_9choices,?_⟩
  exact check_of_frontier tree 0 t4_9root t4_9jobs t4_9frontier t4_9all
theorem t4_10choices : plan1805.choices=[0,1,5,7].map (options 4 2) := by rfl


theorem t4_10part0 : t4_10jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_10frontier : t4_10root.frontier 0=t4_10jobs := by rfl
theorem t4_10all : t4_10jobs.all (Job.check tree)=true := by
  simp only [t4_10jobs,List.all_append,List.all_nil,t4_10part0,Bool.and_self]
theorem t4_10checked : Checked tree [0,1,5,7] := by
  refine ⟨plan1805,valid1805,t4_10choices,?_⟩
  exact check_of_frontier tree 0 t4_10root t4_10jobs t4_10frontier t4_10all
theorem t4_11choices : plan1806.choices=[0,1,5,10].map (options 4 2) := by rfl


theorem t4_11part0 : t4_11jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_11frontier : t4_11root.frontier 0=t4_11jobs := by rfl
theorem t4_11all : t4_11jobs.all (Job.check tree)=true := by
  simp only [t4_11jobs,List.all_append,List.all_nil,t4_11part0,Bool.and_self]
theorem t4_11checked : Checked tree [0,1,5,10] := by
  refine ⟨plan1806,valid1806,t4_11choices,?_⟩
  exact check_of_frontier tree 0 t4_11root t4_11jobs t4_11frontier t4_11all
theorem t4_12choices : plan1807.choices=[0,1,6,6].map (options 4 2) := by rfl


theorem t4_12part0 : t4_12jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_12frontier : t4_12root.frontier 0=t4_12jobs := by rfl
theorem t4_12all : t4_12jobs.all (Job.check tree)=true := by
  simp only [t4_12jobs,List.all_append,List.all_nil,t4_12part0,Bool.and_self]
theorem t4_12checked : Checked tree [0,1,6,6] := by
  refine ⟨plan1807,valid1807,t4_12choices,?_⟩
  exact check_of_frontier tree 0 t4_12root t4_12jobs t4_12frontier t4_12all
theorem t4_13choices : plan1808.choices=[0,1,6,7].map (options 4 2) := by rfl


theorem t4_13part0 : t4_13jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_13frontier : t4_13root.frontier 0=t4_13jobs := by rfl
theorem t4_13all : t4_13jobs.all (Job.check tree)=true := by
  simp only [t4_13jobs,List.all_append,List.all_nil,t4_13part0,Bool.and_self]
theorem t4_13checked : Checked tree [0,1,6,7] := by
  refine ⟨plan1808,valid1808,t4_13choices,?_⟩
  exact check_of_frontier tree 0 t4_13root t4_13jobs t4_13frontier t4_13all
theorem t4_14choices : plan1809.choices=[0,1,6,10].map (options 4 2) := by rfl


theorem t4_14part0 : t4_14jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_14frontier : t4_14root.frontier 0=t4_14jobs := by rfl
theorem t4_14all : t4_14jobs.all (Job.check tree)=true := by
  simp only [t4_14jobs,List.all_append,List.all_nil,t4_14part0,Bool.and_self]
theorem t4_14checked : Checked tree [0,1,6,10] := by
  refine ⟨plan1809,valid1809,t4_14choices,?_⟩
  exact check_of_frontier tree 0 t4_14root t4_14jobs t4_14frontier t4_14all
theorem t4_15choices : plan1810.choices=[0,1,7,7].map (options 4 2) := by rfl


theorem t4_15part0 : t4_15jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_15frontier : t4_15root.frontier 0=t4_15jobs := by rfl
theorem t4_15all : t4_15jobs.all (Job.check tree)=true := by
  simp only [t4_15jobs,List.all_append,List.all_nil,t4_15part0,Bool.and_self]
theorem t4_15checked : Checked tree [0,1,7,7] := by
  refine ⟨plan1810,valid1810,t4_15choices,?_⟩
  exact check_of_frontier tree 0 t4_15root t4_15jobs t4_15frontier t4_15all
theorem t4_16choices : plan1720.choices=[0,1,9,3].map (options 4 1) := by rfl


theorem t4_16part0 : t4_16jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_16frontier : t4_16root.frontier 0=t4_16jobs := by rfl
theorem t4_16all : t4_16jobs.all (Job.check tree)=true := by
  simp only [t4_16jobs,List.all_append,List.all_nil,t4_16part0,Bool.and_self]
theorem t4_16checked : Checked tree [0,1,9,3] := by
  refine ⟨plan1720,valid1720,t4_16choices,?_⟩
  exact check_of_frontier tree 0 t4_16root t4_16jobs t4_16frontier t4_16all
theorem t4_17choices : plan1811.choices=[0,1,9,6].map (options 4 2) := by rfl


theorem t4_17part0 : t4_17jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_17frontier : t4_17root.frontier 0=t4_17jobs := by rfl
theorem t4_17all : t4_17jobs.all (Job.check tree)=true := by
  simp only [t4_17jobs,List.all_append,List.all_nil,t4_17part0,Bool.and_self]
theorem t4_17checked : Checked tree [0,1,9,6] := by
  refine ⟨plan1811,valid1811,t4_17choices,?_⟩
  exact check_of_frontier tree 0 t4_17root t4_17jobs t4_17frontier t4_17all
theorem t4_18choices : plan1812.choices=[0,1,9,7].map (options 4 2) := by rfl


theorem t4_18part0 : t4_18jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_18frontier : t4_18root.frontier 0=t4_18jobs := by rfl
theorem t4_18all : t4_18jobs.all (Job.check tree)=true := by
  simp only [t4_18jobs,List.all_append,List.all_nil,t4_18part0,Bool.and_self]
theorem t4_18checked : Checked tree [0,1,9,7] := by
  refine ⟨plan1812,valid1812,t4_18choices,?_⟩
  exact check_of_frontier tree 0 t4_18root t4_18jobs t4_18frontier t4_18all
theorem t4_19choices : plan1813.choices=[0,1,9,10].map (options 4 2) := by rfl


theorem t4_19part0 : t4_19jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_19frontier : t4_19root.frontier 0=t4_19jobs := by rfl
theorem t4_19all : t4_19jobs.all (Job.check tree)=true := by
  simp only [t4_19jobs,List.all_append,List.all_nil,t4_19part0,Bool.and_self]
theorem t4_19checked : Checked tree [0,1,9,10] := by
  refine ⟨plan1813,valid1813,t4_19choices,?_⟩
  exact check_of_frontier tree 0 t4_19root t4_19jobs t4_19frontier t4_19all
theorem t4_20choices : plan1814.choices=[0,1,10,7].map (options 4 2) := by rfl


theorem t4_20part0 : t4_20jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_20frontier : t4_20root.frontier 0=t4_20jobs := by rfl
theorem t4_20all : t4_20jobs.all (Job.check tree)=true := by
  simp only [t4_20jobs,List.all_append,List.all_nil,t4_20part0,Bool.and_self]
theorem t4_20checked : Checked tree [0,1,10,7] := by
  refine ⟨plan1814,valid1814,t4_20choices,?_⟩
  exact check_of_frontier tree 0 t4_20root t4_20jobs t4_20frontier t4_20all
theorem t4_21choices : plan1815.choices=[0,1,10,10].map (options 4 2) := by rfl


theorem t4_21part0 : t4_21jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_21frontier : t4_21root.frontier 0=t4_21jobs := by rfl
theorem t4_21all : t4_21jobs.all (Job.check tree)=true := by
  simp only [t4_21jobs,List.all_append,List.all_nil,t4_21part0,Bool.and_self]
theorem t4_21checked : Checked tree [0,1,10,10] := by
  refine ⟨plan1815,valid1815,t4_21choices,?_⟩
  exact check_of_frontier tree 0 t4_21root t4_21jobs t4_21frontier t4_21all
theorem t4_22choices : plan1696.choices=[0,2,2,2].map (options 4 0) := by rfl


theorem t4_22part0 : t4_22jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_22frontier : t4_22root.frontier 0=t4_22jobs := by rfl
theorem t4_22all : t4_22jobs.all (Job.check tree)=true := by
  simp only [t4_22jobs,List.all_append,List.all_nil,t4_22part0,Bool.and_self]
theorem t4_22checked : Checked tree [0,2,2,2] := by
  refine ⟨plan1696,valid1696,t4_22choices,?_⟩
  exact check_of_frontier tree 0 t4_22root t4_22jobs t4_22frontier t4_22all
theorem t4_23choices : plan1697.choices=[0,2,2,3].map (options 4 0) := by rfl


theorem t4_23part0 : t4_23jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_23frontier : t4_23root.frontier 0=t4_23jobs := by rfl
theorem t4_23all : t4_23jobs.all (Job.check tree)=true := by
  simp only [t4_23jobs,List.all_append,List.all_nil,t4_23part0,Bool.and_self]
theorem t4_23checked : Checked tree [0,2,2,3] := by
  refine ⟨plan1697,valid1697,t4_23choices,?_⟩
  exact check_of_frontier tree 0 t4_23root t4_23jobs t4_23frontier t4_23all
theorem t4_24choices : plan1721.choices=[0,2,2,5].map (options 4 1) := by rfl


theorem t4_24part0 : t4_24jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_24frontier : t4_24root.frontier 0=t4_24jobs := by rfl
theorem t4_24all : t4_24jobs.all (Job.check tree)=true := by
  simp only [t4_24jobs,List.all_append,List.all_nil,t4_24part0,Bool.and_self]
theorem t4_24checked : Checked tree [0,2,2,5] := by
  refine ⟨plan1721,valid1721,t4_24choices,?_⟩
  exact check_of_frontier tree 0 t4_24root t4_24jobs t4_24frontier t4_24all
theorem t4_25choices : plan1722.choices=[0,2,2,6].map (options 4 1) := by rfl


theorem t4_25part0 : t4_25jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_25frontier : t4_25root.frontier 0=t4_25jobs := by rfl
theorem t4_25all : t4_25jobs.all (Job.check tree)=true := by
  simp only [t4_25jobs,List.all_append,List.all_nil,t4_25part0,Bool.and_self]
theorem t4_25checked : Checked tree [0,2,2,6] := by
  refine ⟨plan1722,valid1722,t4_25choices,?_⟩
  exact check_of_frontier tree 0 t4_25root t4_25jobs t4_25frontier t4_25all
theorem t4_26choices : plan1723.choices=[0,2,2,7].map (options 4 1) := by rfl


theorem t4_26part0 : t4_26jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_26frontier : t4_26root.frontier 0=t4_26jobs := by rfl
theorem t4_26all : t4_26jobs.all (Job.check tree)=true := by
  simp only [t4_26jobs,List.all_append,List.all_nil,t4_26part0,Bool.and_self]
theorem t4_26checked : Checked tree [0,2,2,7] := by
  refine ⟨plan1723,valid1723,t4_26choices,?_⟩
  exact check_of_frontier tree 0 t4_26root t4_26jobs t4_26frontier t4_26all
theorem t4_27choices : plan1724.choices=[0,2,2,9].map (options 4 1) := by rfl


theorem t4_27part0 : t4_27jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_27frontier : t4_27root.frontier 0=t4_27jobs := by rfl
theorem t4_27all : t4_27jobs.all (Job.check tree)=true := by
  simp only [t4_27jobs,List.all_append,List.all_nil,t4_27part0,Bool.and_self]
theorem t4_27checked : Checked tree [0,2,2,9] := by
  refine ⟨plan1724,valid1724,t4_27choices,?_⟩
  exact check_of_frontier tree 0 t4_27root t4_27jobs t4_27frontier t4_27all
theorem t4_28choices : plan1725.choices=[0,2,2,10].map (options 4 1) := by rfl


theorem t4_28part0 : t4_28jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_28frontier : t4_28root.frontier 0=t4_28jobs := by rfl
theorem t4_28all : t4_28jobs.all (Job.check tree)=true := by
  simp only [t4_28jobs,List.all_append,List.all_nil,t4_28part0,Bool.and_self]
theorem t4_28checked : Checked tree [0,2,2,10] := by
  refine ⟨plan1725,valid1725,t4_28choices,?_⟩
  exact check_of_frontier tree 0 t4_28root t4_28jobs t4_28frontier t4_28all
theorem t4_29choices : plan1698.choices=[0,2,3,3].map (options 4 0) := by rfl


theorem t4_29part0 : t4_29jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_29frontier : t4_29root.frontier 0=t4_29jobs := by rfl
theorem t4_29all : t4_29jobs.all (Job.check tree)=true := by
  simp only [t4_29jobs,List.all_append,List.all_nil,t4_29part0,Bool.and_self]
theorem t4_29checked : Checked tree [0,2,3,3] := by
  refine ⟨plan1698,valid1698,t4_29choices,?_⟩
  exact check_of_frontier tree 0 t4_29root t4_29jobs t4_29frontier t4_29all
theorem t4_30choices : plan1726.choices=[0,2,3,6].map (options 4 1) := by rfl


theorem t4_30part0 : t4_30jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_30frontier : t4_30root.frontier 0=t4_30jobs := by rfl
theorem t4_30all : t4_30jobs.all (Job.check tree)=true := by
  simp only [t4_30jobs,List.all_append,List.all_nil,t4_30part0,Bool.and_self]
theorem t4_30checked : Checked tree [0,2,3,6] := by
  refine ⟨plan1726,valid1726,t4_30choices,?_⟩
  exact check_of_frontier tree 0 t4_30root t4_30jobs t4_30frontier t4_30all
theorem t4_31choices : plan1727.choices=[0,2,3,7].map (options 4 1) := by rfl


theorem t4_31part0 : t4_31jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_31frontier : t4_31root.frontier 0=t4_31jobs := by rfl
theorem t4_31all : t4_31jobs.all (Job.check tree)=true := by
  simp only [t4_31jobs,List.all_append,List.all_nil,t4_31part0,Bool.and_self]
theorem t4_31checked : Checked tree [0,2,3,7] := by
  refine ⟨plan1727,valid1727,t4_31choices,?_⟩
  exact check_of_frontier tree 0 t4_31root t4_31jobs t4_31frontier t4_31all
theorem t4_32choices : plan1728.choices=[0,2,3,10].map (options 4 1) := by rfl


theorem t4_32part0 : t4_32jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_32frontier : t4_32root.frontier 0=t4_32jobs := by rfl
theorem t4_32all : t4_32jobs.all (Job.check tree)=true := by
  simp only [t4_32jobs,List.all_append,List.all_nil,t4_32part0,Bool.and_self]
theorem t4_32checked : Checked tree [0,2,3,10] := by
  refine ⟨plan1728,valid1728,t4_32choices,?_⟩
  exact check_of_frontier tree 0 t4_32root t4_32jobs t4_32frontier t4_32all
theorem t4_33choices : plan1729.choices=[0,2,5,3].map (options 4 1) := by rfl


theorem t4_33part0 : t4_33jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_33frontier : t4_33root.frontier 0=t4_33jobs := by rfl
theorem t4_33all : t4_33jobs.all (Job.check tree)=true := by
  simp only [t4_33jobs,List.all_append,List.all_nil,t4_33part0,Bool.and_self]
theorem t4_33checked : Checked tree [0,2,5,3] := by
  refine ⟨plan1729,valid1729,t4_33choices,?_⟩
  exact check_of_frontier tree 0 t4_33root t4_33jobs t4_33frontier t4_33all
theorem t4_34choices : plan1816.choices=[0,2,5,5].map (options 4 2) := by rfl


theorem t4_34part0 : t4_34jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_34frontier : t4_34root.frontier 0=t4_34jobs := by rfl
theorem t4_34all : t4_34jobs.all (Job.check tree)=true := by
  simp only [t4_34jobs,List.all_append,List.all_nil,t4_34part0,Bool.and_self]
theorem t4_34checked : Checked tree [0,2,5,5] := by
  refine ⟨plan1816,valid1816,t4_34choices,?_⟩
  exact check_of_frontier tree 0 t4_34root t4_34jobs t4_34frontier t4_34all
theorem t4_35choices : plan1817.choices=[0,2,5,6].map (options 4 2) := by rfl


theorem t4_35part0 : t4_35jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_35frontier : t4_35root.frontier 0=t4_35jobs := by rfl
theorem t4_35all : t4_35jobs.all (Job.check tree)=true := by
  simp only [t4_35jobs,List.all_append,List.all_nil,t4_35part0,Bool.and_self]
theorem t4_35checked : Checked tree [0,2,5,6] := by
  refine ⟨plan1817,valid1817,t4_35choices,?_⟩
  exact check_of_frontier tree 0 t4_35root t4_35jobs t4_35frontier t4_35all
theorem t4_36choices : plan1818.choices=[0,2,5,7].map (options 4 2) := by rfl


theorem t4_36part0 : t4_36jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_36frontier : t4_36root.frontier 0=t4_36jobs := by rfl
theorem t4_36all : t4_36jobs.all (Job.check tree)=true := by
  simp only [t4_36jobs,List.all_append,List.all_nil,t4_36part0,Bool.and_self]
theorem t4_36checked : Checked tree [0,2,5,7] := by
  refine ⟨plan1818,valid1818,t4_36choices,?_⟩
  exact check_of_frontier tree 0 t4_36root t4_36jobs t4_36frontier t4_36all
theorem t4_37choices : plan1819.choices=[0,2,5,9].map (options 4 2) := by rfl


theorem t4_37part0 : t4_37jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_37frontier : t4_37root.frontier 0=t4_37jobs := by rfl
theorem t4_37all : t4_37jobs.all (Job.check tree)=true := by
  simp only [t4_37jobs,List.all_append,List.all_nil,t4_37part0,Bool.and_self]
theorem t4_37checked : Checked tree [0,2,5,9] := by
  refine ⟨plan1819,valid1819,t4_37choices,?_⟩
  exact check_of_frontier tree 0 t4_37root t4_37jobs t4_37frontier t4_37all
theorem t4_38choices : plan1820.choices=[0,2,5,10].map (options 4 2) := by rfl


theorem t4_38part0 : t4_38jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_38frontier : t4_38root.frontier 0=t4_38jobs := by rfl
theorem t4_38all : t4_38jobs.all (Job.check tree)=true := by
  simp only [t4_38jobs,List.all_append,List.all_nil,t4_38part0,Bool.and_self]
theorem t4_38checked : Checked tree [0,2,5,10] := by
  refine ⟨plan1820,valid1820,t4_38choices,?_⟩
  exact check_of_frontier tree 0 t4_38root t4_38jobs t4_38frontier t4_38all
theorem t4_39choices : plan1821.choices=[0,2,6,6].map (options 4 2) := by rfl


theorem t4_39part0 : t4_39jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_39frontier : t4_39root.frontier 0=t4_39jobs := by rfl
theorem t4_39all : t4_39jobs.all (Job.check tree)=true := by
  simp only [t4_39jobs,List.all_append,List.all_nil,t4_39part0,Bool.and_self]
theorem t4_39checked : Checked tree [0,2,6,6] := by
  refine ⟨plan1821,valid1821,t4_39choices,?_⟩
  exact check_of_frontier tree 0 t4_39root t4_39jobs t4_39frontier t4_39all
theorem t4_40choices : plan1822.choices=[0,2,6,7].map (options 4 2) := by rfl


theorem t4_40part0 : t4_40jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_40frontier : t4_40root.frontier 0=t4_40jobs := by rfl
theorem t4_40all : t4_40jobs.all (Job.check tree)=true := by
  simp only [t4_40jobs,List.all_append,List.all_nil,t4_40part0,Bool.and_self]
theorem t4_40checked : Checked tree [0,2,6,7] := by
  refine ⟨plan1822,valid1822,t4_40choices,?_⟩
  exact check_of_frontier tree 0 t4_40root t4_40jobs t4_40frontier t4_40all
theorem t4_41choices : plan1823.choices=[0,2,6,10].map (options 4 2) := by rfl


theorem t4_41part0 : t4_41jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_41frontier : t4_41root.frontier 0=t4_41jobs := by rfl
theorem t4_41all : t4_41jobs.all (Job.check tree)=true := by
  simp only [t4_41jobs,List.all_append,List.all_nil,t4_41part0,Bool.and_self]
theorem t4_41checked : Checked tree [0,2,6,10] := by
  refine ⟨plan1823,valid1823,t4_41choices,?_⟩
  exact check_of_frontier tree 0 t4_41root t4_41jobs t4_41frontier t4_41all
theorem t4_42choices : plan1824.choices=[0,2,7,7].map (options 4 2) := by rfl


theorem t4_42part0 : t4_42jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_42frontier : t4_42root.frontier 0=t4_42jobs := by rfl
theorem t4_42all : t4_42jobs.all (Job.check tree)=true := by
  simp only [t4_42jobs,List.all_append,List.all_nil,t4_42part0,Bool.and_self]
theorem t4_42checked : Checked tree [0,2,7,7] := by
  refine ⟨plan1824,valid1824,t4_42choices,?_⟩
  exact check_of_frontier tree 0 t4_42root t4_42jobs t4_42frontier t4_42all
theorem t4_43choices : plan1730.choices=[0,2,9,3].map (options 4 1) := by rfl


theorem t4_43part0 : t4_43jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_43frontier : t4_43root.frontier 0=t4_43jobs := by rfl
theorem t4_43all : t4_43jobs.all (Job.check tree)=true := by
  simp only [t4_43jobs,List.all_append,List.all_nil,t4_43part0,Bool.and_self]
theorem t4_43checked : Checked tree [0,2,9,3] := by
  refine ⟨plan1730,valid1730,t4_43choices,?_⟩
  exact check_of_frontier tree 0 t4_43root t4_43jobs t4_43frontier t4_43all
theorem t4_44choices : plan1825.choices=[0,2,9,6].map (options 4 2) := by rfl


theorem t4_44part0 : t4_44jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_44frontier : t4_44root.frontier 0=t4_44jobs := by rfl
theorem t4_44all : t4_44jobs.all (Job.check tree)=true := by
  simp only [t4_44jobs,List.all_append,List.all_nil,t4_44part0,Bool.and_self]
theorem t4_44checked : Checked tree [0,2,9,6] := by
  refine ⟨plan1825,valid1825,t4_44choices,?_⟩
  exact check_of_frontier tree 0 t4_44root t4_44jobs t4_44frontier t4_44all
theorem t4_45choices : plan1826.choices=[0,2,9,7].map (options 4 2) := by rfl


theorem t4_45part0 : t4_45jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_45frontier : t4_45root.frontier 0=t4_45jobs := by rfl
theorem t4_45all : t4_45jobs.all (Job.check tree)=true := by
  simp only [t4_45jobs,List.all_append,List.all_nil,t4_45part0,Bool.and_self]
theorem t4_45checked : Checked tree [0,2,9,7] := by
  refine ⟨plan1826,valid1826,t4_45choices,?_⟩
  exact check_of_frontier tree 0 t4_45root t4_45jobs t4_45frontier t4_45all
theorem t4_46choices : plan1827.choices=[0,2,9,9].map (options 4 2) := by rfl


theorem t4_46part0 : t4_46jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_46frontier : t4_46root.frontier 0=t4_46jobs := by rfl
theorem t4_46all : t4_46jobs.all (Job.check tree)=true := by
  simp only [t4_46jobs,List.all_append,List.all_nil,t4_46part0,Bool.and_self]
theorem t4_46checked : Checked tree [0,2,9,9] := by
  refine ⟨plan1827,valid1827,t4_46choices,?_⟩
  exact check_of_frontier tree 0 t4_46root t4_46jobs t4_46frontier t4_46all
theorem t4_47choices : plan1828.choices=[0,2,9,10].map (options 4 2) := by rfl


theorem t4_47part0 : t4_47jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_47frontier : t4_47root.frontier 0=t4_47jobs := by rfl
theorem t4_47all : t4_47jobs.all (Job.check tree)=true := by
  simp only [t4_47jobs,List.all_append,List.all_nil,t4_47part0,Bool.and_self]
theorem t4_47checked : Checked tree [0,2,9,10] := by
  refine ⟨plan1828,valid1828,t4_47choices,?_⟩
  exact check_of_frontier tree 0 t4_47root t4_47jobs t4_47frontier t4_47all
theorem t4_48choices : plan1829.choices=[0,2,10,7].map (options 4 2) := by rfl


theorem t4_48part0 : t4_48jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_48frontier : t4_48root.frontier 0=t4_48jobs := by rfl
theorem t4_48all : t4_48jobs.all (Job.check tree)=true := by
  simp only [t4_48jobs,List.all_append,List.all_nil,t4_48part0,Bool.and_self]
theorem t4_48checked : Checked tree [0,2,10,7] := by
  refine ⟨plan1829,valid1829,t4_48choices,?_⟩
  exact check_of_frontier tree 0 t4_48root t4_48jobs t4_48frontier t4_48all
theorem t4_49choices : plan1830.choices=[0,2,10,10].map (options 4 2) := by rfl


theorem t4_49part0 : t4_49jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_49frontier : t4_49root.frontier 0=t4_49jobs := by rfl
theorem t4_49all : t4_49jobs.all (Job.check tree)=true := by
  simp only [t4_49jobs,List.all_append,List.all_nil,t4_49part0,Bool.and_self]
theorem t4_49checked : Checked tree [0,2,10,10] := by
  refine ⟨plan1830,valid1830,t4_49choices,?_⟩
  exact check_of_frontier tree 0 t4_49root t4_49jobs t4_49frontier t4_49all
theorem t4_50choices : plan1699.choices=[0,3,3,3].map (options 4 0) := by rfl


theorem t4_50part0 : t4_50jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_50frontier : t4_50root.frontier 0=t4_50jobs := by rfl
theorem t4_50all : t4_50jobs.all (Job.check tree)=true := by
  simp only [t4_50jobs,List.all_append,List.all_nil,t4_50part0,Bool.and_self]
theorem t4_50checked : Checked tree [0,3,3,3] := by
  refine ⟨plan1699,valid1699,t4_50choices,?_⟩
  exact check_of_frontier tree 0 t4_50root t4_50jobs t4_50frontier t4_50all
theorem t4_51choices : plan1731.choices=[0,3,3,6].map (options 4 1) := by rfl


theorem t4_51part0 : t4_51jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_51frontier : t4_51root.frontier 0=t4_51jobs := by rfl
theorem t4_51all : t4_51jobs.all (Job.check tree)=true := by
  simp only [t4_51jobs,List.all_append,List.all_nil,t4_51part0,Bool.and_self]
theorem t4_51checked : Checked tree [0,3,3,6] := by
  refine ⟨plan1731,valid1731,t4_51choices,?_⟩
  exact check_of_frontier tree 0 t4_51root t4_51jobs t4_51frontier t4_51all
theorem t4_52choices : plan1732.choices=[0,3,3,7].map (options 4 1) := by rfl


theorem t4_52part0 : t4_52jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_52frontier : t4_52root.frontier 0=t4_52jobs := by rfl
theorem t4_52all : t4_52jobs.all (Job.check tree)=true := by
  simp only [t4_52jobs,List.all_append,List.all_nil,t4_52part0,Bool.and_self]
theorem t4_52checked : Checked tree [0,3,3,7] := by
  refine ⟨plan1732,valid1732,t4_52choices,?_⟩
  exact check_of_frontier tree 0 t4_52root t4_52jobs t4_52frontier t4_52all
theorem t4_53choices : plan1733.choices=[0,3,3,10].map (options 4 1) := by rfl


theorem t4_53part0 : t4_53jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_53frontier : t4_53root.frontier 0=t4_53jobs := by rfl
theorem t4_53all : t4_53jobs.all (Job.check tree)=true := by
  simp only [t4_53jobs,List.all_append,List.all_nil,t4_53part0,Bool.and_self]
theorem t4_53checked : Checked tree [0,3,3,10] := by
  refine ⟨plan1733,valid1733,t4_53choices,?_⟩
  exact check_of_frontier tree 0 t4_53root t4_53jobs t4_53frontier t4_53all
theorem t4_54choices : plan1831.choices=[0,3,6,6].map (options 4 2) := by rfl


theorem t4_54part0 : t4_54jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_54frontier : t4_54root.frontier 0=t4_54jobs := by rfl
theorem t4_54all : t4_54jobs.all (Job.check tree)=true := by
  simp only [t4_54jobs,List.all_append,List.all_nil,t4_54part0,Bool.and_self]
theorem t4_54checked : Checked tree [0,3,6,6] := by
  refine ⟨plan1831,valid1831,t4_54choices,?_⟩
  exact check_of_frontier tree 0 t4_54root t4_54jobs t4_54frontier t4_54all
theorem t4_55choices : plan1832.choices=[0,3,6,7].map (options 4 2) := by rfl


theorem t4_55part0 : t4_55jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_55frontier : t4_55root.frontier 0=t4_55jobs := by rfl
theorem t4_55all : t4_55jobs.all (Job.check tree)=true := by
  simp only [t4_55jobs,List.all_append,List.all_nil,t4_55part0,Bool.and_self]
theorem t4_55checked : Checked tree [0,3,6,7] := by
  refine ⟨plan1832,valid1832,t4_55choices,?_⟩
  exact check_of_frontier tree 0 t4_55root t4_55jobs t4_55frontier t4_55all
theorem t4_56choices : plan1833.choices=[0,3,6,10].map (options 4 2) := by rfl


theorem t4_56part0 : t4_56jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_56frontier : t4_56root.frontier 0=t4_56jobs := by rfl
theorem t4_56all : t4_56jobs.all (Job.check tree)=true := by
  simp only [t4_56jobs,List.all_append,List.all_nil,t4_56part0,Bool.and_self]
theorem t4_56checked : Checked tree [0,3,6,10] := by
  refine ⟨plan1833,valid1833,t4_56choices,?_⟩
  exact check_of_frontier tree 0 t4_56root t4_56jobs t4_56frontier t4_56all
theorem t4_57choices : plan1834.choices=[0,3,7,7].map (options 4 2) := by rfl


theorem t4_57part0 : t4_57jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_57frontier : t4_57root.frontier 0=t4_57jobs := by rfl
theorem t4_57all : t4_57jobs.all (Job.check tree)=true := by
  simp only [t4_57jobs,List.all_append,List.all_nil,t4_57part0,Bool.and_self]
theorem t4_57checked : Checked tree [0,3,7,7] := by
  refine ⟨plan1834,valid1834,t4_57choices,?_⟩
  exact check_of_frontier tree 0 t4_57root t4_57jobs t4_57frontier t4_57all
theorem t4_58choices : plan1835.choices=[0,3,10,7].map (options 4 2) := by rfl


theorem t4_58part0 : t4_58jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_58frontier : t4_58root.frontier 0=t4_58jobs := by rfl
theorem t4_58all : t4_58jobs.all (Job.check tree)=true := by
  simp only [t4_58jobs,List.all_append,List.all_nil,t4_58part0,Bool.and_self]
theorem t4_58checked : Checked tree [0,3,10,7] := by
  refine ⟨plan1835,valid1835,t4_58choices,?_⟩
  exact check_of_frontier tree 0 t4_58root t4_58jobs t4_58frontier t4_58all
theorem t4_59choices : plan1836.choices=[0,3,10,10].map (options 4 2) := by rfl


theorem t4_59part0 : t4_59jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_59frontier : t4_59root.frontier 0=t4_59jobs := by rfl
theorem t4_59all : t4_59jobs.all (Job.check tree)=true := by
  simp only [t4_59jobs,List.all_append,List.all_nil,t4_59part0,Bool.and_self]
theorem t4_59checked : Checked tree [0,3,10,10] := by
  refine ⟨plan1836,valid1836,t4_59choices,?_⟩
  exact check_of_frontier tree 0 t4_59root t4_59jobs t4_59frontier t4_59all
theorem t4_60choices : plan1734.choices=[0,4,2,3].map (options 4 1) := by rfl


theorem t4_60part0 : t4_60jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_60frontier : t4_60root.frontier 0=t4_60jobs := by rfl
theorem t4_60all : t4_60jobs.all (Job.check tree)=true := by
  simp only [t4_60jobs,List.all_append,List.all_nil,t4_60part0,Bool.and_self]
theorem t4_60checked : Checked tree [0,4,2,3] := by
  refine ⟨plan1734,valid1734,t4_60choices,?_⟩
  exact check_of_frontier tree 0 t4_60root t4_60jobs t4_60frontier t4_60all
theorem t4_61choices : plan1837.choices=[0,4,2,6].map (options 4 2) := by rfl


theorem t4_61part0 : t4_61jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_61frontier : t4_61root.frontier 0=t4_61jobs := by rfl
theorem t4_61all : t4_61jobs.all (Job.check tree)=true := by
  simp only [t4_61jobs,List.all_append,List.all_nil,t4_61part0,Bool.and_self]
theorem t4_61checked : Checked tree [0,4,2,6] := by
  refine ⟨plan1837,valid1837,t4_61choices,?_⟩
  exact check_of_frontier tree 0 t4_61root t4_61jobs t4_61frontier t4_61all
theorem t4_62choices : plan1838.choices=[0,4,2,7].map (options 4 2) := by rfl


theorem t4_62part0 : t4_62jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_62frontier : t4_62root.frontier 0=t4_62jobs := by rfl
theorem t4_62all : t4_62jobs.all (Job.check tree)=true := by
  simp only [t4_62jobs,List.all_append,List.all_nil,t4_62part0,Bool.and_self]
theorem t4_62checked : Checked tree [0,4,2,7] := by
  refine ⟨plan1838,valid1838,t4_62choices,?_⟩
  exact check_of_frontier tree 0 t4_62root t4_62jobs t4_62frontier t4_62all
theorem t4_63choices : plan1839.choices=[0,4,2,10].map (options 4 2) := by rfl


theorem t4_63part0 : t4_63jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_63frontier : t4_63root.frontier 0=t4_63jobs := by rfl
theorem t4_63all : t4_63jobs.all (Job.check tree)=true := by
  simp only [t4_63jobs,List.all_append,List.all_nil,t4_63part0,Bool.and_self]
theorem t4_63checked : Checked tree [0,4,2,10] := by
  refine ⟨plan1839,valid1839,t4_63choices,?_⟩
  exact check_of_frontier tree 0 t4_63root t4_63jobs t4_63frontier t4_63all
theorem t4_64choices : plan1735.choices=[0,4,3,3].map (options 4 1) := by rfl


theorem t4_64part0 : t4_64jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_64frontier : t4_64root.frontier 0=t4_64jobs := by rfl
theorem t4_64all : t4_64jobs.all (Job.check tree)=true := by
  simp only [t4_64jobs,List.all_append,List.all_nil,t4_64part0,Bool.and_self]
theorem t4_64checked : Checked tree [0,4,3,3] := by
  refine ⟨plan1735,valid1735,t4_64choices,?_⟩
  exact check_of_frontier tree 0 t4_64root t4_64jobs t4_64frontier t4_64all
theorem t4_65choices : plan1840.choices=[0,4,3,6].map (options 4 2) := by rfl


theorem t4_65part0 : t4_65jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_65frontier : t4_65root.frontier 0=t4_65jobs := by rfl
theorem t4_65all : t4_65jobs.all (Job.check tree)=true := by
  simp only [t4_65jobs,List.all_append,List.all_nil,t4_65part0,Bool.and_self]
theorem t4_65checked : Checked tree [0,4,3,6] := by
  refine ⟨plan1840,valid1840,t4_65choices,?_⟩
  exact check_of_frontier tree 0 t4_65root t4_65jobs t4_65frontier t4_65all
theorem t4_66choices : plan1841.choices=[0,4,3,7].map (options 4 2) := by rfl


theorem t4_66part0 : t4_66jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_66frontier : t4_66root.frontier 0=t4_66jobs := by rfl
theorem t4_66all : t4_66jobs.all (Job.check tree)=true := by
  simp only [t4_66jobs,List.all_append,List.all_nil,t4_66part0,Bool.and_self]
theorem t4_66checked : Checked tree [0,4,3,7] := by
  refine ⟨plan1841,valid1841,t4_66choices,?_⟩
  exact check_of_frontier tree 0 t4_66root t4_66jobs t4_66frontier t4_66all
theorem t4_67choices : plan1842.choices=[0,4,3,10].map (options 4 2) := by rfl


theorem t4_67part0 : t4_67jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_67frontier : t4_67root.frontier 0=t4_67jobs := by rfl
theorem t4_67all : t4_67jobs.all (Job.check tree)=true := by
  simp only [t4_67jobs,List.all_append,List.all_nil,t4_67part0,Bool.and_self]
theorem t4_67checked : Checked tree [0,4,3,10] := by
  refine ⟨plan1842,valid1842,t4_67choices,?_⟩
  exact check_of_frontier tree 0 t4_67root t4_67jobs t4_67frontier t4_67all
theorem t4_68choices : plan1843.choices=[0,4,5,3].map (options 4 2) := by rfl


theorem t4_68part0 : t4_68jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_68frontier : t4_68root.frontier 0=t4_68jobs := by rfl
theorem t4_68all : t4_68jobs.all (Job.check tree)=true := by
  simp only [t4_68jobs,List.all_append,List.all_nil,t4_68part0,Bool.and_self]
theorem t4_68checked : Checked tree [0,4,5,3] := by
  refine ⟨plan1843,valid1843,t4_68choices,?_⟩
  exact check_of_frontier tree 0 t4_68root t4_68jobs t4_68frontier t4_68all
theorem t4_69choices : plan2020.choices=[0,4,5,6].map (options 4 3) := by rfl


theorem t4_69part0 : t4_69jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_69frontier : t4_69root.frontier 0=t4_69jobs := by rfl
theorem t4_69all : t4_69jobs.all (Job.check tree)=true := by
  simp only [t4_69jobs,List.all_append,List.all_nil,t4_69part0,Bool.and_self]
theorem t4_69checked : Checked tree [0,4,5,6] := by
  refine ⟨plan2020,valid2020,t4_69choices,?_⟩
  exact check_of_frontier tree 0 t4_69root t4_69jobs t4_69frontier t4_69all
theorem t4_70choices : plan2021.choices=[0,4,5,7].map (options 4 3) := by rfl


theorem t4_70part0 : t4_70jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_70frontier : t4_70root.frontier 0=t4_70jobs := by rfl
theorem t4_70all : t4_70jobs.all (Job.check tree)=true := by
  simp only [t4_70jobs,List.all_append,List.all_nil,t4_70part0,Bool.and_self]
theorem t4_70checked : Checked tree [0,4,5,7] := by
  refine ⟨plan2021,valid2021,t4_70choices,?_⟩
  exact check_of_frontier tree 0 t4_70root t4_70jobs t4_70frontier t4_70all
theorem t4_71choices : plan2022.choices=[0,4,5,10].map (options 4 3) := by rfl


theorem t4_71part0 : t4_71jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_71frontier : t4_71root.frontier 0=t4_71jobs := by rfl
theorem t4_71all : t4_71jobs.all (Job.check tree)=true := by
  simp only [t4_71jobs,List.all_append,List.all_nil,t4_71part0,Bool.and_self]
theorem t4_71checked : Checked tree [0,4,5,10] := by
  refine ⟨plan2022,valid2022,t4_71choices,?_⟩
  exact check_of_frontier tree 0 t4_71root t4_71jobs t4_71frontier t4_71all
theorem t4_72choices : plan2023.choices=[0,4,6,6].map (options 4 3) := by rfl


theorem t4_72part0 : t4_72jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_72frontier : t4_72root.frontier 0=t4_72jobs := by rfl
theorem t4_72all : t4_72jobs.all (Job.check tree)=true := by
  simp only [t4_72jobs,List.all_append,List.all_nil,t4_72part0,Bool.and_self]
theorem t4_72checked : Checked tree [0,4,6,6] := by
  refine ⟨plan2023,valid2023,t4_72choices,?_⟩
  exact check_of_frontier tree 0 t4_72root t4_72jobs t4_72frontier t4_72all
theorem t4_73choices : plan2024.choices=[0,4,6,7].map (options 4 3) := by rfl


theorem t4_73part0 : t4_73jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_73frontier : t4_73root.frontier 0=t4_73jobs := by rfl
theorem t4_73all : t4_73jobs.all (Job.check tree)=true := by
  simp only [t4_73jobs,List.all_append,List.all_nil,t4_73part0,Bool.and_self]
theorem t4_73checked : Checked tree [0,4,6,7] := by
  refine ⟨plan2024,valid2024,t4_73choices,?_⟩
  exact check_of_frontier tree 0 t4_73root t4_73jobs t4_73frontier t4_73all
theorem t4_74choices : plan2025.choices=[0,4,6,10].map (options 4 3) := by rfl


theorem t4_74part0 : t4_74jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_74frontier : t4_74root.frontier 0=t4_74jobs := by rfl
theorem t4_74all : t4_74jobs.all (Job.check tree)=true := by
  simp only [t4_74jobs,List.all_append,List.all_nil,t4_74part0,Bool.and_self]
theorem t4_74checked : Checked tree [0,4,6,10] := by
  refine ⟨plan2025,valid2025,t4_74choices,?_⟩
  exact check_of_frontier tree 0 t4_74root t4_74jobs t4_74frontier t4_74all
theorem t4_75choices : plan2026.choices=[0,4,7,7].map (options 4 3) := by rfl


theorem t4_75part0 : t4_75jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_75frontier : t4_75root.frontier 0=t4_75jobs := by rfl
theorem t4_75all : t4_75jobs.all (Job.check tree)=true := by
  simp only [t4_75jobs,List.all_append,List.all_nil,t4_75part0,Bool.and_self]
theorem t4_75checked : Checked tree [0,4,7,7] := by
  refine ⟨plan2026,valid2026,t4_75choices,?_⟩
  exact check_of_frontier tree 0 t4_75root t4_75jobs t4_75frontier t4_75all
theorem t4_76choices : plan1844.choices=[0,4,9,3].map (options 4 2) := by rfl


theorem t4_76part0 : t4_76jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_76frontier : t4_76root.frontier 0=t4_76jobs := by rfl
theorem t4_76all : t4_76jobs.all (Job.check tree)=true := by
  simp only [t4_76jobs,List.all_append,List.all_nil,t4_76part0,Bool.and_self]
theorem t4_76checked : Checked tree [0,4,9,3] := by
  refine ⟨plan1844,valid1844,t4_76choices,?_⟩
  exact check_of_frontier tree 0 t4_76root t4_76jobs t4_76frontier t4_76all
theorem t4_77choices : plan2027.choices=[0,4,9,6].map (options 4 3) := by rfl


theorem t4_77part0 : t4_77jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_77frontier : t4_77root.frontier 0=t4_77jobs := by rfl
theorem t4_77all : t4_77jobs.all (Job.check tree)=true := by
  simp only [t4_77jobs,List.all_append,List.all_nil,t4_77part0,Bool.and_self]
theorem t4_77checked : Checked tree [0,4,9,6] := by
  refine ⟨plan2027,valid2027,t4_77choices,?_⟩
  exact check_of_frontier tree 0 t4_77root t4_77jobs t4_77frontier t4_77all
theorem t4_78choices : plan2028.choices=[0,4,9,7].map (options 4 3) := by rfl


theorem t4_78part0 : t4_78jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_78frontier : t4_78root.frontier 0=t4_78jobs := by rfl
theorem t4_78all : t4_78jobs.all (Job.check tree)=true := by
  simp only [t4_78jobs,List.all_append,List.all_nil,t4_78part0,Bool.and_self]
theorem t4_78checked : Checked tree [0,4,9,7] := by
  refine ⟨plan2028,valid2028,t4_78choices,?_⟩
  exact check_of_frontier tree 0 t4_78root t4_78jobs t4_78frontier t4_78all
theorem t4_79choices : plan2029.choices=[0,4,9,10].map (options 4 3) := by rfl


theorem t4_79part0 : t4_79jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_79frontier : t4_79root.frontier 0=t4_79jobs := by rfl
theorem t4_79all : t4_79jobs.all (Job.check tree)=true := by
  simp only [t4_79jobs,List.all_append,List.all_nil,t4_79part0,Bool.and_self]
theorem t4_79checked : Checked tree [0,4,9,10] := by
  refine ⟨plan2029,valid2029,t4_79choices,?_⟩
  exact check_of_frontier tree 0 t4_79root t4_79jobs t4_79frontier t4_79all
theorem t4_80choices : plan2030.choices=[0,4,10,7].map (options 4 3) := by rfl


theorem t4_80part0 : t4_80jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_80frontier : t4_80root.frontier 0=t4_80jobs := by rfl
theorem t4_80all : t4_80jobs.all (Job.check tree)=true := by
  simp only [t4_80jobs,List.all_append,List.all_nil,t4_80part0,Bool.and_self]
theorem t4_80checked : Checked tree [0,4,10,7] := by
  refine ⟨plan2030,valid2030,t4_80choices,?_⟩
  exact check_of_frontier tree 0 t4_80root t4_80jobs t4_80frontier t4_80all
theorem t4_81choices : plan2031.choices=[0,4,10,10].map (options 4 3) := by rfl


theorem t4_81part0 : t4_81jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_81frontier : t4_81root.frontier 0=t4_81jobs := by rfl
theorem t4_81all : t4_81jobs.all (Job.check tree)=true := by
  simp only [t4_81jobs,List.all_append,List.all_nil,t4_81part0,Bool.and_self]
theorem t4_81checked : Checked tree [0,4,10,10] := by
  refine ⟨plan2031,valid2031,t4_81choices,?_⟩
  exact check_of_frontier tree 0 t4_81root t4_81jobs t4_81frontier t4_81all
theorem t4_82choices : plan1736.choices=[0,5,3,3].map (options 4 1) := by rfl


theorem t4_82part0 : t4_82jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_82frontier : t4_82root.frontier 0=t4_82jobs := by rfl
theorem t4_82all : t4_82jobs.all (Job.check tree)=true := by
  simp only [t4_82jobs,List.all_append,List.all_nil,t4_82part0,Bool.and_self]
theorem t4_82checked : Checked tree [0,5,3,3] := by
  refine ⟨plan1736,valid1736,t4_82choices,?_⟩
  exact check_of_frontier tree 0 t4_82root t4_82jobs t4_82frontier t4_82all
theorem t4_83choices : plan1845.choices=[0,5,3,6].map (options 4 2) := by rfl


theorem t4_83part0 : t4_83jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_83frontier : t4_83root.frontier 0=t4_83jobs := by rfl
theorem t4_83all : t4_83jobs.all (Job.check tree)=true := by
  simp only [t4_83jobs,List.all_append,List.all_nil,t4_83part0,Bool.and_self]
theorem t4_83checked : Checked tree [0,5,3,6] := by
  refine ⟨plan1845,valid1845,t4_83choices,?_⟩
  exact check_of_frontier tree 0 t4_83root t4_83jobs t4_83frontier t4_83all
theorem t4_84choices : plan1846.choices=[0,5,3,7].map (options 4 2) := by rfl


theorem t4_84part0 : t4_84jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_84frontier : t4_84root.frontier 0=t4_84jobs := by rfl
theorem t4_84all : t4_84jobs.all (Job.check tree)=true := by
  simp only [t4_84jobs,List.all_append,List.all_nil,t4_84part0,Bool.and_self]
theorem t4_84checked : Checked tree [0,5,3,7] := by
  refine ⟨plan1846,valid1846,t4_84choices,?_⟩
  exact check_of_frontier tree 0 t4_84root t4_84jobs t4_84frontier t4_84all
theorem t4_85choices : plan1847.choices=[0,5,3,10].map (options 4 2) := by rfl


theorem t4_85part0 : t4_85jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_85frontier : t4_85root.frontier 0=t4_85jobs := by rfl
theorem t4_85all : t4_85jobs.all (Job.check tree)=true := by
  simp only [t4_85jobs,List.all_append,List.all_nil,t4_85part0,Bool.and_self]
theorem t4_85checked : Checked tree [0,5,3,10] := by
  refine ⟨plan1847,valid1847,t4_85choices,?_⟩
  exact check_of_frontier tree 0 t4_85root t4_85jobs t4_85frontier t4_85all
theorem t4_86choices : plan1848.choices=[0,5,5,3].map (options 4 2) := by rfl


theorem t4_86part0 : t4_86jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_86frontier : t4_86root.frontier 0=t4_86jobs := by rfl
theorem t4_86all : t4_86jobs.all (Job.check tree)=true := by
  simp only [t4_86jobs,List.all_append,List.all_nil,t4_86part0,Bool.and_self]
theorem t4_86checked : Checked tree [0,5,5,3] := by
  refine ⟨plan1848,valid1848,t4_86choices,?_⟩
  exact check_of_frontier tree 0 t4_86root t4_86jobs t4_86frontier t4_86all
theorem t4_87choices : plan2032.choices=[0,5,5,5].map (options 4 3) := by rfl


theorem t4_87part0 : t4_87jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_87frontier : t4_87root.frontier 0=t4_87jobs := by rfl
theorem t4_87all : t4_87jobs.all (Job.check tree)=true := by
  simp only [t4_87jobs,List.all_append,List.all_nil,t4_87part0,Bool.and_self]
theorem t4_87checked : Checked tree [0,5,5,5] := by
  refine ⟨plan2032,valid2032,t4_87choices,?_⟩
  exact check_of_frontier tree 0 t4_87root t4_87jobs t4_87frontier t4_87all
theorem t4_88choices : plan2033.choices=[0,5,5,6].map (options 4 3) := by rfl


theorem t4_88part0 : t4_88jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_88frontier : t4_88root.frontier 0=t4_88jobs := by rfl
theorem t4_88all : t4_88jobs.all (Job.check tree)=true := by
  simp only [t4_88jobs,List.all_append,List.all_nil,t4_88part0,Bool.and_self]
theorem t4_88checked : Checked tree [0,5,5,6] := by
  refine ⟨plan2033,valid2033,t4_88choices,?_⟩
  exact check_of_frontier tree 0 t4_88root t4_88jobs t4_88frontier t4_88all
theorem t4_89choices : plan2034.choices=[0,5,5,7].map (options 4 3) := by rfl


theorem t4_89part0 : t4_89jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_89frontier : t4_89root.frontier 0=t4_89jobs := by rfl
theorem t4_89all : t4_89jobs.all (Job.check tree)=true := by
  simp only [t4_89jobs,List.all_append,List.all_nil,t4_89part0,Bool.and_self]
theorem t4_89checked : Checked tree [0,5,5,7] := by
  refine ⟨plan2034,valid2034,t4_89choices,?_⟩
  exact check_of_frontier tree 0 t4_89root t4_89jobs t4_89frontier t4_89all
theorem t4_90choices : plan2035.choices=[0,5,5,9].map (options 4 3) := by rfl


theorem t4_90part0 : t4_90jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_90frontier : t4_90root.frontier 0=t4_90jobs := by rfl
theorem t4_90all : t4_90jobs.all (Job.check tree)=true := by
  simp only [t4_90jobs,List.all_append,List.all_nil,t4_90part0,Bool.and_self]
theorem t4_90checked : Checked tree [0,5,5,9] := by
  refine ⟨plan2035,valid2035,t4_90choices,?_⟩
  exact check_of_frontier tree 0 t4_90root t4_90jobs t4_90frontier t4_90all
theorem t4_91choices : plan2036.choices=[0,5,5,10].map (options 4 3) := by rfl


theorem t4_91part0 : t4_91jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_91frontier : t4_91root.frontier 0=t4_91jobs := by rfl
theorem t4_91all : t4_91jobs.all (Job.check tree)=true := by
  simp only [t4_91jobs,List.all_append,List.all_nil,t4_91part0,Bool.and_self]
theorem t4_91checked : Checked tree [0,5,5,10] := by
  refine ⟨plan2036,valid2036,t4_91choices,?_⟩
  exact check_of_frontier tree 0 t4_91root t4_91jobs t4_91frontier t4_91all
theorem t4_92choices : plan2037.choices=[0,5,6,6].map (options 4 3) := by rfl


theorem t4_92part0 : t4_92jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_92frontier : t4_92root.frontier 0=t4_92jobs := by rfl
theorem t4_92all : t4_92jobs.all (Job.check tree)=true := by
  simp only [t4_92jobs,List.all_append,List.all_nil,t4_92part0,Bool.and_self]
theorem t4_92checked : Checked tree [0,5,6,6] := by
  refine ⟨plan2037,valid2037,t4_92choices,?_⟩
  exact check_of_frontier tree 0 t4_92root t4_92jobs t4_92frontier t4_92all
theorem t4_93choices : plan2038.choices=[0,5,6,7].map (options 4 3) := by rfl


theorem t4_93part0 : t4_93jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_93frontier : t4_93root.frontier 0=t4_93jobs := by rfl
theorem t4_93all : t4_93jobs.all (Job.check tree)=true := by
  simp only [t4_93jobs,List.all_append,List.all_nil,t4_93part0,Bool.and_self]
theorem t4_93checked : Checked tree [0,5,6,7] := by
  refine ⟨plan2038,valid2038,t4_93choices,?_⟩
  exact check_of_frontier tree 0 t4_93root t4_93jobs t4_93frontier t4_93all
theorem t4_94choices : plan2039.choices=[0,5,6,10].map (options 4 3) := by rfl


theorem t4_94part0 : t4_94jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_94frontier : t4_94root.frontier 0=t4_94jobs := by rfl
theorem t4_94all : t4_94jobs.all (Job.check tree)=true := by
  simp only [t4_94jobs,List.all_append,List.all_nil,t4_94part0,Bool.and_self]
theorem t4_94checked : Checked tree [0,5,6,10] := by
  refine ⟨plan2039,valid2039,t4_94choices,?_⟩
  exact check_of_frontier tree 0 t4_94root t4_94jobs t4_94frontier t4_94all
theorem t4_95choices : plan2040.choices=[0,5,7,7].map (options 4 3) := by rfl


theorem t4_95part0 : t4_95jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_95frontier : t4_95root.frontier 0=t4_95jobs := by rfl
theorem t4_95all : t4_95jobs.all (Job.check tree)=true := by
  simp only [t4_95jobs,List.all_append,List.all_nil,t4_95part0,Bool.and_self]
theorem t4_95checked : Checked tree [0,5,7,7] := by
  refine ⟨plan2040,valid2040,t4_95choices,?_⟩
  exact check_of_frontier tree 0 t4_95root t4_95jobs t4_95frontier t4_95all
theorem t4_96choices : plan1849.choices=[0,5,9,3].map (options 4 2) := by rfl


theorem t4_96part0 : t4_96jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_96frontier : t4_96root.frontier 0=t4_96jobs := by rfl
theorem t4_96all : t4_96jobs.all (Job.check tree)=true := by
  simp only [t4_96jobs,List.all_append,List.all_nil,t4_96part0,Bool.and_self]
theorem t4_96checked : Checked tree [0,5,9,3] := by
  refine ⟨plan1849,valid1849,t4_96choices,?_⟩
  exact check_of_frontier tree 0 t4_96root t4_96jobs t4_96frontier t4_96all
theorem t4_97choices : plan2041.choices=[0,5,9,6].map (options 4 3) := by rfl


theorem t4_97part0 : t4_97jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_97frontier : t4_97root.frontier 0=t4_97jobs := by rfl
theorem t4_97all : t4_97jobs.all (Job.check tree)=true := by
  simp only [t4_97jobs,List.all_append,List.all_nil,t4_97part0,Bool.and_self]
theorem t4_97checked : Checked tree [0,5,9,6] := by
  refine ⟨plan2041,valid2041,t4_97choices,?_⟩
  exact check_of_frontier tree 0 t4_97root t4_97jobs t4_97frontier t4_97all
theorem t4_98choices : plan2042.choices=[0,5,9,7].map (options 4 3) := by rfl


theorem t4_98part0 : t4_98jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_98frontier : t4_98root.frontier 0=t4_98jobs := by rfl
theorem t4_98all : t4_98jobs.all (Job.check tree)=true := by
  simp only [t4_98jobs,List.all_append,List.all_nil,t4_98part0,Bool.and_self]
theorem t4_98checked : Checked tree [0,5,9,7] := by
  refine ⟨plan2042,valid2042,t4_98choices,?_⟩
  exact check_of_frontier tree 0 t4_98root t4_98jobs t4_98frontier t4_98all
theorem t4_99choices : plan2043.choices=[0,5,9,9].map (options 4 3) := by rfl


theorem t4_99part0 : t4_99jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_99frontier : t4_99root.frontier 0=t4_99jobs := by rfl
theorem t4_99all : t4_99jobs.all (Job.check tree)=true := by
  simp only [t4_99jobs,List.all_append,List.all_nil,t4_99part0,Bool.and_self]
theorem t4_99checked : Checked tree [0,5,9,9] := by
  refine ⟨plan2043,valid2043,t4_99choices,?_⟩
  exact check_of_frontier tree 0 t4_99root t4_99jobs t4_99frontier t4_99all
theorem t4_100choices : plan2044.choices=[0,5,9,10].map (options 4 3) := by rfl


theorem t4_100part0 : t4_100jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_100frontier : t4_100root.frontier 0=t4_100jobs := by rfl
theorem t4_100all : t4_100jobs.all (Job.check tree)=true := by
  simp only [t4_100jobs,List.all_append,List.all_nil,t4_100part0,Bool.and_self]
theorem t4_100checked : Checked tree [0,5,9,10] := by
  refine ⟨plan2044,valid2044,t4_100choices,?_⟩
  exact check_of_frontier tree 0 t4_100root t4_100jobs t4_100frontier t4_100all
theorem t4_101choices : plan2045.choices=[0,5,10,7].map (options 4 3) := by rfl


theorem t4_101part0 : t4_101jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_101frontier : t4_101root.frontier 0=t4_101jobs := by rfl
theorem t4_101all : t4_101jobs.all (Job.check tree)=true := by
  simp only [t4_101jobs,List.all_append,List.all_nil,t4_101part0,Bool.and_self]
theorem t4_101checked : Checked tree [0,5,10,7] := by
  refine ⟨plan2045,valid2045,t4_101choices,?_⟩
  exact check_of_frontier tree 0 t4_101root t4_101jobs t4_101frontier t4_101all
theorem t4_102choices : plan2046.choices=[0,5,10,10].map (options 4 3) := by rfl


theorem t4_102part0 : t4_102jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_102frontier : t4_102root.frontier 0=t4_102jobs := by rfl
theorem t4_102all : t4_102jobs.all (Job.check tree)=true := by
  simp only [t4_102jobs,List.all_append,List.all_nil,t4_102part0,Bool.and_self]
theorem t4_102checked : Checked tree [0,5,10,10] := by
  refine ⟨plan2046,valid2046,t4_102choices,?_⟩
  exact check_of_frontier tree 0 t4_102root t4_102jobs t4_102frontier t4_102all
theorem t4_103choices : plan2047.choices=[0,6,6,6].map (options 4 3) := by rfl


theorem t4_103part0 : t4_103jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_103frontier : t4_103root.frontier 0=t4_103jobs := by rfl
theorem t4_103all : t4_103jobs.all (Job.check tree)=true := by
  simp only [t4_103jobs,List.all_append,List.all_nil,t4_103part0,Bool.and_self]
theorem t4_103checked : Checked tree [0,6,6,6] := by
  refine ⟨plan2047,valid2047,t4_103choices,?_⟩
  exact check_of_frontier tree 0 t4_103root t4_103jobs t4_103frontier t4_103all
theorem t4_104choices : plan2048.choices=[0,6,6,7].map (options 4 3) := by rfl


theorem t4_104part0 : t4_104jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_104frontier : t4_104root.frontier 0=t4_104jobs := by rfl
theorem t4_104all : t4_104jobs.all (Job.check tree)=true := by
  simp only [t4_104jobs,List.all_append,List.all_nil,t4_104part0,Bool.and_self]
theorem t4_104checked : Checked tree [0,6,6,7] := by
  refine ⟨plan2048,valid2048,t4_104choices,?_⟩
  exact check_of_frontier tree 0 t4_104root t4_104jobs t4_104frontier t4_104all
theorem t4_105choices : plan2049.choices=[0,6,6,10].map (options 4 3) := by rfl


theorem t4_105part0 : t4_105jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_105frontier : t4_105root.frontier 0=t4_105jobs := by rfl
theorem t4_105all : t4_105jobs.all (Job.check tree)=true := by
  simp only [t4_105jobs,List.all_append,List.all_nil,t4_105part0,Bool.and_self]
theorem t4_105checked : Checked tree [0,6,6,10] := by
  refine ⟨plan2049,valid2049,t4_105choices,?_⟩
  exact check_of_frontier tree 0 t4_105root t4_105jobs t4_105frontier t4_105all
theorem t4_106choices : plan2050.choices=[0,6,7,7].map (options 4 3) := by rfl


theorem t4_106part0 : t4_106jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_106frontier : t4_106root.frontier 0=t4_106jobs := by rfl
theorem t4_106all : t4_106jobs.all (Job.check tree)=true := by
  simp only [t4_106jobs,List.all_append,List.all_nil,t4_106part0,Bool.and_self]
theorem t4_106checked : Checked tree [0,6,7,7] := by
  refine ⟨plan2050,valid2050,t4_106choices,?_⟩
  exact check_of_frontier tree 0 t4_106root t4_106jobs t4_106frontier t4_106all
theorem t4_107choices : plan2051.choices=[0,6,10,7].map (options 4 3) := by rfl


theorem t4_107part0 : t4_107jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_107frontier : t4_107root.frontier 0=t4_107jobs := by rfl
theorem t4_107all : t4_107jobs.all (Job.check tree)=true := by
  simp only [t4_107jobs,List.all_append,List.all_nil,t4_107part0,Bool.and_self]
theorem t4_107checked : Checked tree [0,6,10,7] := by
  refine ⟨plan2051,valid2051,t4_107choices,?_⟩
  exact check_of_frontier tree 0 t4_107root t4_107jobs t4_107frontier t4_107all
theorem t4_108choices : plan2052.choices=[0,6,10,10].map (options 4 3) := by rfl


theorem t4_108part0 : t4_108jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_108frontier : t4_108root.frontier 0=t4_108jobs := by rfl
theorem t4_108all : t4_108jobs.all (Job.check tree)=true := by
  simp only [t4_108jobs,List.all_append,List.all_nil,t4_108part0,Bool.and_self]
theorem t4_108checked : Checked tree [0,6,10,10] := by
  refine ⟨plan2052,valid2052,t4_108choices,?_⟩
  exact check_of_frontier tree 0 t4_108root t4_108jobs t4_108frontier t4_108all
theorem t4_109choices : plan2053.choices=[0,7,7,7].map (options 4 3) := by rfl


theorem t4_109part0 : t4_109jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_109frontier : t4_109root.frontier 0=t4_109jobs := by rfl
theorem t4_109all : t4_109jobs.all (Job.check tree)=true := by
  simp only [t4_109jobs,List.all_append,List.all_nil,t4_109part0,Bool.and_self]
theorem t4_109checked : Checked tree [0,7,7,7] := by
  refine ⟨plan2053,valid2053,t4_109choices,?_⟩
  exact check_of_frontier tree 0 t4_109root t4_109jobs t4_109frontier t4_109all
theorem t4_110choices : plan1737.choices=[0,8,2,3].map (options 4 1) := by rfl


theorem t4_110part0 : t4_110jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_110frontier : t4_110root.frontier 0=t4_110jobs := by rfl
theorem t4_110all : t4_110jobs.all (Job.check tree)=true := by
  simp only [t4_110jobs,List.all_append,List.all_nil,t4_110part0,Bool.and_self]
theorem t4_110checked : Checked tree [0,8,2,3] := by
  refine ⟨plan1737,valid1737,t4_110choices,?_⟩
  exact check_of_frontier tree 0 t4_110root t4_110jobs t4_110frontier t4_110all
theorem t4_111choices : plan1850.choices=[0,8,2,6].map (options 4 2) := by rfl


theorem t4_111part0 : t4_111jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_111frontier : t4_111root.frontier 0=t4_111jobs := by rfl
theorem t4_111all : t4_111jobs.all (Job.check tree)=true := by
  simp only [t4_111jobs,List.all_append,List.all_nil,t4_111part0,Bool.and_self]
theorem t4_111checked : Checked tree [0,8,2,6] := by
  refine ⟨plan1850,valid1850,t4_111choices,?_⟩
  exact check_of_frontier tree 0 t4_111root t4_111jobs t4_111frontier t4_111all
theorem t4_112choices : plan1851.choices=[0,8,2,7].map (options 4 2) := by rfl


theorem t4_112part0 : t4_112jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_112frontier : t4_112root.frontier 0=t4_112jobs := by rfl
theorem t4_112all : t4_112jobs.all (Job.check tree)=true := by
  simp only [t4_112jobs,List.all_append,List.all_nil,t4_112part0,Bool.and_self]
theorem t4_112checked : Checked tree [0,8,2,7] := by
  refine ⟨plan1851,valid1851,t4_112choices,?_⟩
  exact check_of_frontier tree 0 t4_112root t4_112jobs t4_112frontier t4_112all
theorem t4_113choices : plan1852.choices=[0,8,2,10].map (options 4 2) := by rfl


theorem t4_113part0 : t4_113jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_113frontier : t4_113root.frontier 0=t4_113jobs := by rfl
theorem t4_113all : t4_113jobs.all (Job.check tree)=true := by
  simp only [t4_113jobs,List.all_append,List.all_nil,t4_113part0,Bool.and_self]
theorem t4_113checked : Checked tree [0,8,2,10] := by
  refine ⟨plan1852,valid1852,t4_113choices,?_⟩
  exact check_of_frontier tree 0 t4_113root t4_113jobs t4_113frontier t4_113all
theorem t4_114choices : plan1738.choices=[0,8,3,3].map (options 4 1) := by rfl


theorem t4_114part0 : t4_114jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_114frontier : t4_114root.frontier 0=t4_114jobs := by rfl
theorem t4_114all : t4_114jobs.all (Job.check tree)=true := by
  simp only [t4_114jobs,List.all_append,List.all_nil,t4_114part0,Bool.and_self]
theorem t4_114checked : Checked tree [0,8,3,3] := by
  refine ⟨plan1738,valid1738,t4_114choices,?_⟩
  exact check_of_frontier tree 0 t4_114root t4_114jobs t4_114frontier t4_114all
theorem t4_115choices : plan1853.choices=[0,8,3,6].map (options 4 2) := by rfl


theorem t4_115part0 : t4_115jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_115frontier : t4_115root.frontier 0=t4_115jobs := by rfl
theorem t4_115all : t4_115jobs.all (Job.check tree)=true := by
  simp only [t4_115jobs,List.all_append,List.all_nil,t4_115part0,Bool.and_self]
theorem t4_115checked : Checked tree [0,8,3,6] := by
  refine ⟨plan1853,valid1853,t4_115choices,?_⟩
  exact check_of_frontier tree 0 t4_115root t4_115jobs t4_115frontier t4_115all
theorem t4_116choices : plan1854.choices=[0,8,3,7].map (options 4 2) := by rfl


theorem t4_116part0 : t4_116jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_116frontier : t4_116root.frontier 0=t4_116jobs := by rfl
theorem t4_116all : t4_116jobs.all (Job.check tree)=true := by
  simp only [t4_116jobs,List.all_append,List.all_nil,t4_116part0,Bool.and_self]
theorem t4_116checked : Checked tree [0,8,3,7] := by
  refine ⟨plan1854,valid1854,t4_116choices,?_⟩
  exact check_of_frontier tree 0 t4_116root t4_116jobs t4_116frontier t4_116all
theorem t4_117choices : plan1855.choices=[0,8,3,10].map (options 4 2) := by rfl


theorem t4_117part0 : t4_117jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_117frontier : t4_117root.frontier 0=t4_117jobs := by rfl
theorem t4_117all : t4_117jobs.all (Job.check tree)=true := by
  simp only [t4_117jobs,List.all_append,List.all_nil,t4_117part0,Bool.and_self]
theorem t4_117checked : Checked tree [0,8,3,10] := by
  refine ⟨plan1855,valid1855,t4_117choices,?_⟩
  exact check_of_frontier tree 0 t4_117root t4_117jobs t4_117frontier t4_117all
theorem t4_118choices : plan1856.choices=[0,8,5,3].map (options 4 2) := by rfl


theorem t4_118part0 : t4_118jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_118frontier : t4_118root.frontier 0=t4_118jobs := by rfl
theorem t4_118all : t4_118jobs.all (Job.check tree)=true := by
  simp only [t4_118jobs,List.all_append,List.all_nil,t4_118part0,Bool.and_self]
theorem t4_118checked : Checked tree [0,8,5,3] := by
  refine ⟨plan1856,valid1856,t4_118choices,?_⟩
  exact check_of_frontier tree 0 t4_118root t4_118jobs t4_118frontier t4_118all
theorem t4_119choices : plan2054.choices=[0,8,5,6].map (options 4 3) := by rfl


theorem t4_119part0 : t4_119jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_119frontier : t4_119root.frontier 0=t4_119jobs := by rfl
theorem t4_119all : t4_119jobs.all (Job.check tree)=true := by
  simp only [t4_119jobs,List.all_append,List.all_nil,t4_119part0,Bool.and_self]
theorem t4_119checked : Checked tree [0,8,5,6] := by
  refine ⟨plan2054,valid2054,t4_119choices,?_⟩
  exact check_of_frontier tree 0 t4_119root t4_119jobs t4_119frontier t4_119all
theorem t4_120choices : plan2055.choices=[0,8,5,7].map (options 4 3) := by rfl


theorem t4_120part0 : t4_120jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_120frontier : t4_120root.frontier 0=t4_120jobs := by rfl
theorem t4_120all : t4_120jobs.all (Job.check tree)=true := by
  simp only [t4_120jobs,List.all_append,List.all_nil,t4_120part0,Bool.and_self]
theorem t4_120checked : Checked tree [0,8,5,7] := by
  refine ⟨plan2055,valid2055,t4_120choices,?_⟩
  exact check_of_frontier tree 0 t4_120root t4_120jobs t4_120frontier t4_120all
theorem t4_121choices : plan2056.choices=[0,8,5,10].map (options 4 3) := by rfl


theorem t4_121part0 : t4_121jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_121frontier : t4_121root.frontier 0=t4_121jobs := by rfl
theorem t4_121all : t4_121jobs.all (Job.check tree)=true := by
  simp only [t4_121jobs,List.all_append,List.all_nil,t4_121part0,Bool.and_self]
theorem t4_121checked : Checked tree [0,8,5,10] := by
  refine ⟨plan2056,valid2056,t4_121choices,?_⟩
  exact check_of_frontier tree 0 t4_121root t4_121jobs t4_121frontier t4_121all
theorem t4_122choices : plan2057.choices=[0,8,6,6].map (options 4 3) := by rfl


theorem t4_122part0 : t4_122jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_122frontier : t4_122root.frontier 0=t4_122jobs := by rfl
theorem t4_122all : t4_122jobs.all (Job.check tree)=true := by
  simp only [t4_122jobs,List.all_append,List.all_nil,t4_122part0,Bool.and_self]
theorem t4_122checked : Checked tree [0,8,6,6] := by
  refine ⟨plan2057,valid2057,t4_122choices,?_⟩
  exact check_of_frontier tree 0 t4_122root t4_122jobs t4_122frontier t4_122all
theorem t4_123choices : plan2058.choices=[0,8,6,7].map (options 4 3) := by rfl


theorem t4_123part0 : t4_123jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_123frontier : t4_123root.frontier 0=t4_123jobs := by rfl
theorem t4_123all : t4_123jobs.all (Job.check tree)=true := by
  simp only [t4_123jobs,List.all_append,List.all_nil,t4_123part0,Bool.and_self]
theorem t4_123checked : Checked tree [0,8,6,7] := by
  refine ⟨plan2058,valid2058,t4_123choices,?_⟩
  exact check_of_frontier tree 0 t4_123root t4_123jobs t4_123frontier t4_123all
theorem t4_124choices : plan2059.choices=[0,8,6,10].map (options 4 3) := by rfl


theorem t4_124part0 : t4_124jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_124frontier : t4_124root.frontier 0=t4_124jobs := by rfl
theorem t4_124all : t4_124jobs.all (Job.check tree)=true := by
  simp only [t4_124jobs,List.all_append,List.all_nil,t4_124part0,Bool.and_self]
theorem t4_124checked : Checked tree [0,8,6,10] := by
  refine ⟨plan2059,valid2059,t4_124choices,?_⟩
  exact check_of_frontier tree 0 t4_124root t4_124jobs t4_124frontier t4_124all
theorem t4_125choices : plan2060.choices=[0,8,7,7].map (options 4 3) := by rfl


theorem t4_125part0 : t4_125jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_125frontier : t4_125root.frontier 0=t4_125jobs := by rfl
theorem t4_125all : t4_125jobs.all (Job.check tree)=true := by
  simp only [t4_125jobs,List.all_append,List.all_nil,t4_125part0,Bool.and_self]
theorem t4_125checked : Checked tree [0,8,7,7] := by
  refine ⟨plan2060,valid2060,t4_125choices,?_⟩
  exact check_of_frontier tree 0 t4_125root t4_125jobs t4_125frontier t4_125all
theorem t4_126choices : plan1857.choices=[0,8,9,3].map (options 4 2) := by rfl


theorem t4_126part0 : t4_126jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_126frontier : t4_126root.frontier 0=t4_126jobs := by rfl
theorem t4_126all : t4_126jobs.all (Job.check tree)=true := by
  simp only [t4_126jobs,List.all_append,List.all_nil,t4_126part0,Bool.and_self]
theorem t4_126checked : Checked tree [0,8,9,3] := by
  refine ⟨plan1857,valid1857,t4_126choices,?_⟩
  exact check_of_frontier tree 0 t4_126root t4_126jobs t4_126frontier t4_126all
theorem t4_127choices : plan2061.choices=[0,8,9,6].map (options 4 3) := by rfl


theorem t4_127part0 : t4_127jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_127frontier : t4_127root.frontier 0=t4_127jobs := by rfl
theorem t4_127all : t4_127jobs.all (Job.check tree)=true := by
  simp only [t4_127jobs,List.all_append,List.all_nil,t4_127part0,Bool.and_self]
theorem t4_127checked : Checked tree [0,8,9,6] := by
  refine ⟨plan2061,valid2061,t4_127choices,?_⟩
  exact check_of_frontier tree 0 t4_127root t4_127jobs t4_127frontier t4_127all
theorem t4_128choices : plan2062.choices=[0,8,9,7].map (options 4 3) := by rfl


theorem t4_128part0 : t4_128jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_128frontier : t4_128root.frontier 0=t4_128jobs := by rfl
theorem t4_128all : t4_128jobs.all (Job.check tree)=true := by
  simp only [t4_128jobs,List.all_append,List.all_nil,t4_128part0,Bool.and_self]
theorem t4_128checked : Checked tree [0,8,9,7] := by
  refine ⟨plan2062,valid2062,t4_128choices,?_⟩
  exact check_of_frontier tree 0 t4_128root t4_128jobs t4_128frontier t4_128all
theorem t4_129choices : plan2063.choices=[0,8,9,10].map (options 4 3) := by rfl


theorem t4_129part0 : t4_129jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_129frontier : t4_129root.frontier 0=t4_129jobs := by rfl
theorem t4_129all : t4_129jobs.all (Job.check tree)=true := by
  simp only [t4_129jobs,List.all_append,List.all_nil,t4_129part0,Bool.and_self]
theorem t4_129checked : Checked tree [0,8,9,10] := by
  refine ⟨plan2063,valid2063,t4_129choices,?_⟩
  exact check_of_frontier tree 0 t4_129root t4_129jobs t4_129frontier t4_129all
theorem t4_130choices : plan2064.choices=[0,8,10,7].map (options 4 3) := by rfl


theorem t4_130part0 : t4_130jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_130frontier : t4_130root.frontier 0=t4_130jobs := by rfl
theorem t4_130all : t4_130jobs.all (Job.check tree)=true := by
  simp only [t4_130jobs,List.all_append,List.all_nil,t4_130part0,Bool.and_self]
theorem t4_130checked : Checked tree [0,8,10,7] := by
  refine ⟨plan2064,valid2064,t4_130choices,?_⟩
  exact check_of_frontier tree 0 t4_130root t4_130jobs t4_130frontier t4_130all
theorem t4_131choices : plan2065.choices=[0,8,10,10].map (options 4 3) := by rfl


theorem t4_131part0 : t4_131jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_131frontier : t4_131root.frontier 0=t4_131jobs := by rfl
theorem t4_131all : t4_131jobs.all (Job.check tree)=true := by
  simp only [t4_131jobs,List.all_append,List.all_nil,t4_131part0,Bool.and_self]
theorem t4_131checked : Checked tree [0,8,10,10] := by
  refine ⟨plan2065,valid2065,t4_131choices,?_⟩
  exact check_of_frontier tree 0 t4_131root t4_131jobs t4_131frontier t4_131all
theorem t4_132choices : plan1739.choices=[0,9,3,3].map (options 4 1) := by rfl


theorem t4_132part0 : t4_132jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_132frontier : t4_132root.frontier 0=t4_132jobs := by rfl
theorem t4_132all : t4_132jobs.all (Job.check tree)=true := by
  simp only [t4_132jobs,List.all_append,List.all_nil,t4_132part0,Bool.and_self]
theorem t4_132checked : Checked tree [0,9,3,3] := by
  refine ⟨plan1739,valid1739,t4_132choices,?_⟩
  exact check_of_frontier tree 0 t4_132root t4_132jobs t4_132frontier t4_132all
theorem t4_133choices : plan1858.choices=[0,9,3,6].map (options 4 2) := by rfl


theorem t4_133part0 : t4_133jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_133frontier : t4_133root.frontier 0=t4_133jobs := by rfl
theorem t4_133all : t4_133jobs.all (Job.check tree)=true := by
  simp only [t4_133jobs,List.all_append,List.all_nil,t4_133part0,Bool.and_self]
theorem t4_133checked : Checked tree [0,9,3,6] := by
  refine ⟨plan1858,valid1858,t4_133choices,?_⟩
  exact check_of_frontier tree 0 t4_133root t4_133jobs t4_133frontier t4_133all
theorem t4_134choices : plan1859.choices=[0,9,3,7].map (options 4 2) := by rfl


theorem t4_134part0 : t4_134jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_134frontier : t4_134root.frontier 0=t4_134jobs := by rfl
theorem t4_134all : t4_134jobs.all (Job.check tree)=true := by
  simp only [t4_134jobs,List.all_append,List.all_nil,t4_134part0,Bool.and_self]
theorem t4_134checked : Checked tree [0,9,3,7] := by
  refine ⟨plan1859,valid1859,t4_134choices,?_⟩
  exact check_of_frontier tree 0 t4_134root t4_134jobs t4_134frontier t4_134all
theorem t4_135choices : plan1860.choices=[0,9,3,10].map (options 4 2) := by rfl


theorem t4_135part0 : t4_135jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_135frontier : t4_135root.frontier 0=t4_135jobs := by rfl
theorem t4_135all : t4_135jobs.all (Job.check tree)=true := by
  simp only [t4_135jobs,List.all_append,List.all_nil,t4_135part0,Bool.and_self]
theorem t4_135checked : Checked tree [0,9,3,10] := by
  refine ⟨plan1860,valid1860,t4_135choices,?_⟩
  exact check_of_frontier tree 0 t4_135root t4_135jobs t4_135frontier t4_135all
theorem t4_136choices : plan2066.choices=[0,9,6,6].map (options 4 3) := by rfl


theorem t4_136part0 : t4_136jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_136frontier : t4_136root.frontier 0=t4_136jobs := by rfl
theorem t4_136all : t4_136jobs.all (Job.check tree)=true := by
  simp only [t4_136jobs,List.all_append,List.all_nil,t4_136part0,Bool.and_self]
theorem t4_136checked : Checked tree [0,9,6,6] := by
  refine ⟨plan2066,valid2066,t4_136choices,?_⟩
  exact check_of_frontier tree 0 t4_136root t4_136jobs t4_136frontier t4_136all
theorem t4_137choices : plan2067.choices=[0,9,6,7].map (options 4 3) := by rfl


theorem t4_137part0 : t4_137jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_137frontier : t4_137root.frontier 0=t4_137jobs := by rfl
theorem t4_137all : t4_137jobs.all (Job.check tree)=true := by
  simp only [t4_137jobs,List.all_append,List.all_nil,t4_137part0,Bool.and_self]
theorem t4_137checked : Checked tree [0,9,6,7] := by
  refine ⟨plan2067,valid2067,t4_137choices,?_⟩
  exact check_of_frontier tree 0 t4_137root t4_137jobs t4_137frontier t4_137all
theorem t4_138choices : plan2068.choices=[0,9,6,10].map (options 4 3) := by rfl


theorem t4_138part0 : t4_138jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_138frontier : t4_138root.frontier 0=t4_138jobs := by rfl
theorem t4_138all : t4_138jobs.all (Job.check tree)=true := by
  simp only [t4_138jobs,List.all_append,List.all_nil,t4_138part0,Bool.and_self]
theorem t4_138checked : Checked tree [0,9,6,10] := by
  refine ⟨plan2068,valid2068,t4_138choices,?_⟩
  exact check_of_frontier tree 0 t4_138root t4_138jobs t4_138frontier t4_138all
theorem t4_139choices : plan2069.choices=[0,9,7,7].map (options 4 3) := by rfl


theorem t4_139part0 : t4_139jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_139frontier : t4_139root.frontier 0=t4_139jobs := by rfl
theorem t4_139all : t4_139jobs.all (Job.check tree)=true := by
  simp only [t4_139jobs,List.all_append,List.all_nil,t4_139part0,Bool.and_self]
theorem t4_139checked : Checked tree [0,9,7,7] := by
  refine ⟨plan2069,valid2069,t4_139choices,?_⟩
  exact check_of_frontier tree 0 t4_139root t4_139jobs t4_139frontier t4_139all
theorem t4_140choices : plan1861.choices=[0,9,9,3].map (options 4 2) := by rfl


theorem t4_140part0 : t4_140jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_140frontier : t4_140root.frontier 0=t4_140jobs := by rfl
theorem t4_140all : t4_140jobs.all (Job.check tree)=true := by
  simp only [t4_140jobs,List.all_append,List.all_nil,t4_140part0,Bool.and_self]
theorem t4_140checked : Checked tree [0,9,9,3] := by
  refine ⟨plan1861,valid1861,t4_140choices,?_⟩
  exact check_of_frontier tree 0 t4_140root t4_140jobs t4_140frontier t4_140all
theorem t4_141choices : plan2070.choices=[0,9,9,6].map (options 4 3) := by rfl


theorem t4_141part0 : t4_141jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_141frontier : t4_141root.frontier 0=t4_141jobs := by rfl
theorem t4_141all : t4_141jobs.all (Job.check tree)=true := by
  simp only [t4_141jobs,List.all_append,List.all_nil,t4_141part0,Bool.and_self]
theorem t4_141checked : Checked tree [0,9,9,6] := by
  refine ⟨plan2070,valid2070,t4_141choices,?_⟩
  exact check_of_frontier tree 0 t4_141root t4_141jobs t4_141frontier t4_141all
theorem t4_142choices : plan2071.choices=[0,9,9,7].map (options 4 3) := by rfl


theorem t4_142part0 : t4_142jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_142frontier : t4_142root.frontier 0=t4_142jobs := by rfl
theorem t4_142all : t4_142jobs.all (Job.check tree)=true := by
  simp only [t4_142jobs,List.all_append,List.all_nil,t4_142part0,Bool.and_self]
theorem t4_142checked : Checked tree [0,9,9,7] := by
  refine ⟨plan2071,valid2071,t4_142choices,?_⟩
  exact check_of_frontier tree 0 t4_142root t4_142jobs t4_142frontier t4_142all
theorem t4_143choices : plan2072.choices=[0,9,9,9].map (options 4 3) := by rfl


theorem t4_143part0 : t4_143jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_143frontier : t4_143root.frontier 0=t4_143jobs := by rfl
theorem t4_143all : t4_143jobs.all (Job.check tree)=true := by
  simp only [t4_143jobs,List.all_append,List.all_nil,t4_143part0,Bool.and_self]
theorem t4_143checked : Checked tree [0,9,9,9] := by
  refine ⟨plan2072,valid2072,t4_143choices,?_⟩
  exact check_of_frontier tree 0 t4_143root t4_143jobs t4_143frontier t4_143all
theorem t4_144choices : plan2073.choices=[0,9,9,10].map (options 4 3) := by rfl


theorem t4_144part0 : t4_144jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_144frontier : t4_144root.frontier 0=t4_144jobs := by rfl
theorem t4_144all : t4_144jobs.all (Job.check tree)=true := by
  simp only [t4_144jobs,List.all_append,List.all_nil,t4_144part0,Bool.and_self]
theorem t4_144checked : Checked tree [0,9,9,10] := by
  refine ⟨plan2073,valid2073,t4_144choices,?_⟩
  exact check_of_frontier tree 0 t4_144root t4_144jobs t4_144frontier t4_144all
theorem t4_145choices : plan2074.choices=[0,9,10,7].map (options 4 3) := by rfl


theorem t4_145part0 : t4_145jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_145frontier : t4_145root.frontier 0=t4_145jobs := by rfl
theorem t4_145all : t4_145jobs.all (Job.check tree)=true := by
  simp only [t4_145jobs,List.all_append,List.all_nil,t4_145part0,Bool.and_self]
theorem t4_145checked : Checked tree [0,9,10,7] := by
  refine ⟨plan2074,valid2074,t4_145choices,?_⟩
  exact check_of_frontier tree 0 t4_145root t4_145jobs t4_145frontier t4_145all
theorem t4_146choices : plan2075.choices=[0,9,10,10].map (options 4 3) := by rfl


theorem t4_146part0 : t4_146jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_146frontier : t4_146root.frontier 0=t4_146jobs := by rfl
theorem t4_146all : t4_146jobs.all (Job.check tree)=true := by
  simp only [t4_146jobs,List.all_append,List.all_nil,t4_146part0,Bool.and_self]
theorem t4_146checked : Checked tree [0,9,10,10] := by
  refine ⟨plan2075,valid2075,t4_146choices,?_⟩
  exact check_of_frontier tree 0 t4_146root t4_146jobs t4_146frontier t4_146all
theorem t4_147choices : plan2076.choices=[0,10,7,7].map (options 4 3) := by rfl


theorem t4_147part0 : t4_147jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_147frontier : t4_147root.frontier 0=t4_147jobs := by rfl
theorem t4_147all : t4_147jobs.all (Job.check tree)=true := by
  simp only [t4_147jobs,List.all_append,List.all_nil,t4_147part0,Bool.and_self]
theorem t4_147checked : Checked tree [0,10,7,7] := by
  refine ⟨plan2076,valid2076,t4_147choices,?_⟩
  exact check_of_frontier tree 0 t4_147root t4_147jobs t4_147frontier t4_147all
theorem t4_148choices : plan2077.choices=[0,10,10,7].map (options 4 3) := by rfl


theorem t4_148part0 : t4_148jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_148frontier : t4_148root.frontier 0=t4_148jobs := by rfl
theorem t4_148all : t4_148jobs.all (Job.check tree)=true := by
  simp only [t4_148jobs,List.all_append,List.all_nil,t4_148part0,Bool.and_self]
theorem t4_148checked : Checked tree [0,10,10,7] := by
  refine ⟨plan2077,valid2077,t4_148choices,?_⟩
  exact check_of_frontier tree 0 t4_148root t4_148jobs t4_148frontier t4_148all
theorem t4_149choices : plan2078.choices=[0,10,10,10].map (options 4 3) := by rfl


theorem t4_149part0 : t4_149jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_149frontier : t4_149root.frontier 0=t4_149jobs := by rfl
theorem t4_149all : t4_149jobs.all (Job.check tree)=true := by
  simp only [t4_149jobs,List.all_append,List.all_nil,t4_149part0,Bool.and_self]
theorem t4_149checked : Checked tree [0,10,10,10] := by
  refine ⟨plan2078,valid2078,t4_149choices,?_⟩
  exact check_of_frontier tree 0 t4_149root t4_149jobs t4_149frontier t4_149all
theorem t4_150choices : plan1700.choices=[1,1,1,3].map (options 4 0) := by rfl


theorem t4_150part0 : t4_150jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_150frontier : t4_150root.frontier 0=t4_150jobs := by rfl
theorem t4_150all : t4_150jobs.all (Job.check tree)=true := by
  simp only [t4_150jobs,List.all_append,List.all_nil,t4_150part0,Bool.and_self]
theorem t4_150checked : Checked tree [1,1,1,3] := by
  refine ⟨plan1700,valid1700,t4_150choices,?_⟩
  exact check_of_frontier tree 0 t4_150root t4_150jobs t4_150frontier t4_150all
theorem t4_151choices : plan1740.choices=[1,1,1,6].map (options 4 1) := by rfl


theorem t4_151part0 : t4_151jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_151frontier : t4_151root.frontier 0=t4_151jobs := by rfl
theorem t4_151all : t4_151jobs.all (Job.check tree)=true := by
  simp only [t4_151jobs,List.all_append,List.all_nil,t4_151part0,Bool.and_self]
theorem t4_151checked : Checked tree [1,1,1,6] := by
  refine ⟨plan1740,valid1740,t4_151choices,?_⟩
  exact check_of_frontier tree 0 t4_151root t4_151jobs t4_151frontier t4_151all
theorem t4_152choices : plan1741.choices=[1,1,1,7].map (options 4 1) := by rfl


theorem t4_152part0 : t4_152jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_152frontier : t4_152root.frontier 0=t4_152jobs := by rfl
theorem t4_152all : t4_152jobs.all (Job.check tree)=true := by
  simp only [t4_152jobs,List.all_append,List.all_nil,t4_152part0,Bool.and_self]
theorem t4_152checked : Checked tree [1,1,1,7] := by
  refine ⟨plan1741,valid1741,t4_152choices,?_⟩
  exact check_of_frontier tree 0 t4_152root t4_152jobs t4_152frontier t4_152all
theorem t4_153choices : plan1742.choices=[1,1,1,10].map (options 4 1) := by rfl


theorem t4_153part0 : t4_153jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_153frontier : t4_153root.frontier 0=t4_153jobs := by rfl
theorem t4_153all : t4_153jobs.all (Job.check tree)=true := by
  simp only [t4_153jobs,List.all_append,List.all_nil,t4_153part0,Bool.and_self]
theorem t4_153checked : Checked tree [1,1,1,10] := by
  refine ⟨plan1742,valid1742,t4_153choices,?_⟩
  exact check_of_frontier tree 0 t4_153root t4_153jobs t4_153frontier t4_153all
theorem t4_154choices : plan1701.choices=[1,1,2,2].map (options 4 0) := by rfl


theorem t4_154part0 : t4_154jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_154frontier : t4_154root.frontier 0=t4_154jobs := by rfl
theorem t4_154all : t4_154jobs.all (Job.check tree)=true := by
  simp only [t4_154jobs,List.all_append,List.all_nil,t4_154part0,Bool.and_self]
theorem t4_154checked : Checked tree [1,1,2,2] := by
  refine ⟨plan1701,valid1701,t4_154choices,?_⟩
  exact check_of_frontier tree 0 t4_154root t4_154jobs t4_154frontier t4_154all
theorem t4_155choices : plan1702.choices=[1,1,2,3].map (options 4 0) := by rfl


theorem t4_155part0 : t4_155jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_155frontier : t4_155root.frontier 0=t4_155jobs := by rfl
theorem t4_155all : t4_155jobs.all (Job.check tree)=true := by
  simp only [t4_155jobs,List.all_append,List.all_nil,t4_155part0,Bool.and_self]
theorem t4_155checked : Checked tree [1,1,2,3] := by
  refine ⟨plan1702,valid1702,t4_155choices,?_⟩
  exact check_of_frontier tree 0 t4_155root t4_155jobs t4_155frontier t4_155all
theorem t4_156choices : plan1743.choices=[1,1,2,5].map (options 4 1) := by rfl


theorem t4_156part0 : t4_156jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_156frontier : t4_156root.frontier 0=t4_156jobs := by rfl
theorem t4_156all : t4_156jobs.all (Job.check tree)=true := by
  simp only [t4_156jobs,List.all_append,List.all_nil,t4_156part0,Bool.and_self]
theorem t4_156checked : Checked tree [1,1,2,5] := by
  refine ⟨plan1743,valid1743,t4_156choices,?_⟩
  exact check_of_frontier tree 0 t4_156root t4_156jobs t4_156frontier t4_156all
theorem t4_157choices : plan1744.choices=[1,1,2,6].map (options 4 1) := by rfl


theorem t4_157part0 : t4_157jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_157frontier : t4_157root.frontier 0=t4_157jobs := by rfl
theorem t4_157all : t4_157jobs.all (Job.check tree)=true := by
  simp only [t4_157jobs,List.all_append,List.all_nil,t4_157part0,Bool.and_self]
theorem t4_157checked : Checked tree [1,1,2,6] := by
  refine ⟨plan1744,valid1744,t4_157choices,?_⟩
  exact check_of_frontier tree 0 t4_157root t4_157jobs t4_157frontier t4_157all
theorem t4_158choices : plan1745.choices=[1,1,2,7].map (options 4 1) := by rfl


theorem t4_158part0 : t4_158jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_158frontier : t4_158root.frontier 0=t4_158jobs := by rfl
theorem t4_158all : t4_158jobs.all (Job.check tree)=true := by
  simp only [t4_158jobs,List.all_append,List.all_nil,t4_158part0,Bool.and_self]
theorem t4_158checked : Checked tree [1,1,2,7] := by
  refine ⟨plan1745,valid1745,t4_158choices,?_⟩
  exact check_of_frontier tree 0 t4_158root t4_158jobs t4_158frontier t4_158all
theorem t4_159choices : plan1746.choices=[1,1,2,9].map (options 4 1) := by rfl


theorem t4_159part0 : t4_159jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_159frontier : t4_159root.frontier 0=t4_159jobs := by rfl
theorem t4_159all : t4_159jobs.all (Job.check tree)=true := by
  simp only [t4_159jobs,List.all_append,List.all_nil,t4_159part0,Bool.and_self]
theorem t4_159checked : Checked tree [1,1,2,9] := by
  refine ⟨plan1746,valid1746,t4_159choices,?_⟩
  exact check_of_frontier tree 0 t4_159root t4_159jobs t4_159frontier t4_159all
theorem t4_160choices : plan1747.choices=[1,1,2,10].map (options 4 1) := by rfl


theorem t4_160part0 : t4_160jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_160frontier : t4_160root.frontier 0=t4_160jobs := by rfl
theorem t4_160all : t4_160jobs.all (Job.check tree)=true := by
  simp only [t4_160jobs,List.all_append,List.all_nil,t4_160part0,Bool.and_self]
theorem t4_160checked : Checked tree [1,1,2,10] := by
  refine ⟨plan1747,valid1747,t4_160choices,?_⟩
  exact check_of_frontier tree 0 t4_160root t4_160jobs t4_160frontier t4_160all
theorem t4_161choices : plan1703.choices=[1,1,3,3].map (options 4 0) := by rfl


theorem t4_161part0 : t4_161jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_161frontier : t4_161root.frontier 0=t4_161jobs := by rfl
theorem t4_161all : t4_161jobs.all (Job.check tree)=true := by
  simp only [t4_161jobs,List.all_append,List.all_nil,t4_161part0,Bool.and_self]
theorem t4_161checked : Checked tree [1,1,3,3] := by
  refine ⟨plan1703,valid1703,t4_161choices,?_⟩
  exact check_of_frontier tree 0 t4_161root t4_161jobs t4_161frontier t4_161all
theorem t4_162choices : plan1748.choices=[1,1,3,6].map (options 4 1) := by rfl


theorem t4_162part0 : t4_162jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_162frontier : t4_162root.frontier 0=t4_162jobs := by rfl
theorem t4_162all : t4_162jobs.all (Job.check tree)=true := by
  simp only [t4_162jobs,List.all_append,List.all_nil,t4_162part0,Bool.and_self]
theorem t4_162checked : Checked tree [1,1,3,6] := by
  refine ⟨plan1748,valid1748,t4_162choices,?_⟩
  exact check_of_frontier tree 0 t4_162root t4_162jobs t4_162frontier t4_162all
theorem t4_163choices : plan1749.choices=[1,1,3,7].map (options 4 1) := by rfl


theorem t4_163part0 : t4_163jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_163frontier : t4_163root.frontier 0=t4_163jobs := by rfl
theorem t4_163all : t4_163jobs.all (Job.check tree)=true := by
  simp only [t4_163jobs,List.all_append,List.all_nil,t4_163part0,Bool.and_self]
theorem t4_163checked : Checked tree [1,1,3,7] := by
  refine ⟨plan1749,valid1749,t4_163choices,?_⟩
  exact check_of_frontier tree 0 t4_163root t4_163jobs t4_163frontier t4_163all
theorem t4_164choices : plan1750.choices=[1,1,3,10].map (options 4 1) := by rfl


theorem t4_164part0 : t4_164jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_164frontier : t4_164root.frontier 0=t4_164jobs := by rfl
theorem t4_164all : t4_164jobs.all (Job.check tree)=true := by
  simp only [t4_164jobs,List.all_append,List.all_nil,t4_164part0,Bool.and_self]
theorem t4_164checked : Checked tree [1,1,3,10] := by
  refine ⟨plan1750,valid1750,t4_164choices,?_⟩
  exact check_of_frontier tree 0 t4_164root t4_164jobs t4_164frontier t4_164all
theorem t4_165choices : plan1751.choices=[1,1,4,3].map (options 4 1) := by rfl


theorem t4_165part0 : t4_165jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_165frontier : t4_165root.frontier 0=t4_165jobs := by rfl
theorem t4_165all : t4_165jobs.all (Job.check tree)=true := by
  simp only [t4_165jobs,List.all_append,List.all_nil,t4_165part0,Bool.and_self]
theorem t4_165checked : Checked tree [1,1,4,3] := by
  refine ⟨plan1751,valid1751,t4_165choices,?_⟩
  exact check_of_frontier tree 0 t4_165root t4_165jobs t4_165frontier t4_165all
theorem t4_166choices : plan1862.choices=[1,1,4,6].map (options 4 2) := by rfl


theorem t4_166part0 : t4_166jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_166frontier : t4_166root.frontier 0=t4_166jobs := by rfl
theorem t4_166all : t4_166jobs.all (Job.check tree)=true := by
  simp only [t4_166jobs,List.all_append,List.all_nil,t4_166part0,Bool.and_self]
theorem t4_166checked : Checked tree [1,1,4,6] := by
  refine ⟨plan1862,valid1862,t4_166choices,?_⟩
  exact check_of_frontier tree 0 t4_166root t4_166jobs t4_166frontier t4_166all
theorem t4_167choices : plan1863.choices=[1,1,4,7].map (options 4 2) := by rfl


theorem t4_167part0 : t4_167jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_167frontier : t4_167root.frontier 0=t4_167jobs := by rfl
theorem t4_167all : t4_167jobs.all (Job.check tree)=true := by
  simp only [t4_167jobs,List.all_append,List.all_nil,t4_167part0,Bool.and_self]
theorem t4_167checked : Checked tree [1,1,4,7] := by
  refine ⟨plan1863,valid1863,t4_167choices,?_⟩
  exact check_of_frontier tree 0 t4_167root t4_167jobs t4_167frontier t4_167all
theorem t4_168choices : plan1864.choices=[1,1,4,10].map (options 4 2) := by rfl


theorem t4_168part0 : t4_168jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_168frontier : t4_168root.frontier 0=t4_168jobs := by rfl
theorem t4_168all : t4_168jobs.all (Job.check tree)=true := by
  simp only [t4_168jobs,List.all_append,List.all_nil,t4_168part0,Bool.and_self]
theorem t4_168checked : Checked tree [1,1,4,10] := by
  refine ⟨plan1864,valid1864,t4_168choices,?_⟩
  exact check_of_frontier tree 0 t4_168root t4_168jobs t4_168frontier t4_168all
theorem t4_169choices : plan1752.choices=[1,1,5,3].map (options 4 1) := by rfl


theorem t4_169part0 : t4_169jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_169frontier : t4_169root.frontier 0=t4_169jobs := by rfl
theorem t4_169all : t4_169jobs.all (Job.check tree)=true := by
  simp only [t4_169jobs,List.all_append,List.all_nil,t4_169part0,Bool.and_self]
theorem t4_169checked : Checked tree [1,1,5,3] := by
  refine ⟨plan1752,valid1752,t4_169choices,?_⟩
  exact check_of_frontier tree 0 t4_169root t4_169jobs t4_169frontier t4_169all
theorem t4_170choices : plan1865.choices=[1,1,5,5].map (options 4 2) := by rfl


theorem t4_170part0 : t4_170jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_170frontier : t4_170root.frontier 0=t4_170jobs := by rfl
theorem t4_170all : t4_170jobs.all (Job.check tree)=true := by
  simp only [t4_170jobs,List.all_append,List.all_nil,t4_170part0,Bool.and_self]
theorem t4_170checked : Checked tree [1,1,5,5] := by
  refine ⟨plan1865,valid1865,t4_170choices,?_⟩
  exact check_of_frontier tree 0 t4_170root t4_170jobs t4_170frontier t4_170all
theorem t4_171choices : plan1866.choices=[1,1,5,6].map (options 4 2) := by rfl


theorem t4_171part0 : t4_171jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_171frontier : t4_171root.frontier 0=t4_171jobs := by rfl
theorem t4_171all : t4_171jobs.all (Job.check tree)=true := by
  simp only [t4_171jobs,List.all_append,List.all_nil,t4_171part0,Bool.and_self]
theorem t4_171checked : Checked tree [1,1,5,6] := by
  refine ⟨plan1866,valid1866,t4_171choices,?_⟩
  exact check_of_frontier tree 0 t4_171root t4_171jobs t4_171frontier t4_171all
theorem t4_172choices : plan1867.choices=[1,1,5,7].map (options 4 2) := by rfl


theorem t4_172part0 : t4_172jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_172frontier : t4_172root.frontier 0=t4_172jobs := by rfl
theorem t4_172all : t4_172jobs.all (Job.check tree)=true := by
  simp only [t4_172jobs,List.all_append,List.all_nil,t4_172part0,Bool.and_self]
theorem t4_172checked : Checked tree [1,1,5,7] := by
  refine ⟨plan1867,valid1867,t4_172choices,?_⟩
  exact check_of_frontier tree 0 t4_172root t4_172jobs t4_172frontier t4_172all
theorem t4_173choices : plan1868.choices=[1,1,5,9].map (options 4 2) := by rfl


theorem t4_173part0 : t4_173jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_173frontier : t4_173root.frontier 0=t4_173jobs := by rfl
theorem t4_173all : t4_173jobs.all (Job.check tree)=true := by
  simp only [t4_173jobs,List.all_append,List.all_nil,t4_173part0,Bool.and_self]
theorem t4_173checked : Checked tree [1,1,5,9] := by
  refine ⟨plan1868,valid1868,t4_173choices,?_⟩
  exact check_of_frontier tree 0 t4_173root t4_173jobs t4_173frontier t4_173all
theorem t4_174choices : plan1869.choices=[1,1,5,10].map (options 4 2) := by rfl


theorem t4_174part0 : t4_174jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_174frontier : t4_174root.frontier 0=t4_174jobs := by rfl
theorem t4_174all : t4_174jobs.all (Job.check tree)=true := by
  simp only [t4_174jobs,List.all_append,List.all_nil,t4_174part0,Bool.and_self]
theorem t4_174checked : Checked tree [1,1,5,10] := by
  refine ⟨plan1869,valid1869,t4_174choices,?_⟩
  exact check_of_frontier tree 0 t4_174root t4_174jobs t4_174frontier t4_174all
theorem t4_175choices : plan1870.choices=[1,1,6,6].map (options 4 2) := by rfl


theorem t4_175part0 : t4_175jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_175frontier : t4_175root.frontier 0=t4_175jobs := by rfl
theorem t4_175all : t4_175jobs.all (Job.check tree)=true := by
  simp only [t4_175jobs,List.all_append,List.all_nil,t4_175part0,Bool.and_self]
theorem t4_175checked : Checked tree [1,1,6,6] := by
  refine ⟨plan1870,valid1870,t4_175choices,?_⟩
  exact check_of_frontier tree 0 t4_175root t4_175jobs t4_175frontier t4_175all
theorem t4_176choices : plan1871.choices=[1,1,6,7].map (options 4 2) := by rfl


theorem t4_176part0 : t4_176jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_176frontier : t4_176root.frontier 0=t4_176jobs := by rfl
theorem t4_176all : t4_176jobs.all (Job.check tree)=true := by
  simp only [t4_176jobs,List.all_append,List.all_nil,t4_176part0,Bool.and_self]
theorem t4_176checked : Checked tree [1,1,6,7] := by
  refine ⟨plan1871,valid1871,t4_176choices,?_⟩
  exact check_of_frontier tree 0 t4_176root t4_176jobs t4_176frontier t4_176all
theorem t4_177choices : plan1872.choices=[1,1,6,10].map (options 4 2) := by rfl


theorem t4_177part0 : t4_177jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_177frontier : t4_177root.frontier 0=t4_177jobs := by rfl
theorem t4_177all : t4_177jobs.all (Job.check tree)=true := by
  simp only [t4_177jobs,List.all_append,List.all_nil,t4_177part0,Bool.and_self]
theorem t4_177checked : Checked tree [1,1,6,10] := by
  refine ⟨plan1872,valid1872,t4_177choices,?_⟩
  exact check_of_frontier tree 0 t4_177root t4_177jobs t4_177frontier t4_177all
theorem t4_178choices : plan1873.choices=[1,1,7,7].map (options 4 2) := by rfl


theorem t4_178part0 : t4_178jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_178frontier : t4_178root.frontier 0=t4_178jobs := by rfl
theorem t4_178all : t4_178jobs.all (Job.check tree)=true := by
  simp only [t4_178jobs,List.all_append,List.all_nil,t4_178part0,Bool.and_self]
theorem t4_178checked : Checked tree [1,1,7,7] := by
  refine ⟨plan1873,valid1873,t4_178choices,?_⟩
  exact check_of_frontier tree 0 t4_178root t4_178jobs t4_178frontier t4_178all
theorem t4_179choices : plan1753.choices=[1,1,8,3].map (options 4 1) := by rfl


theorem t4_179part0 : t4_179jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_179frontier : t4_179root.frontier 0=t4_179jobs := by rfl
theorem t4_179all : t4_179jobs.all (Job.check tree)=true := by
  simp only [t4_179jobs,List.all_append,List.all_nil,t4_179part0,Bool.and_self]
theorem t4_179checked : Checked tree [1,1,8,3] := by
  refine ⟨plan1753,valid1753,t4_179choices,?_⟩
  exact check_of_frontier tree 0 t4_179root t4_179jobs t4_179frontier t4_179all
theorem t4_180choices : plan1874.choices=[1,1,8,6].map (options 4 2) := by rfl


theorem t4_180part0 : t4_180jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_180frontier : t4_180root.frontier 0=t4_180jobs := by rfl
theorem t4_180all : t4_180jobs.all (Job.check tree)=true := by
  simp only [t4_180jobs,List.all_append,List.all_nil,t4_180part0,Bool.and_self]
theorem t4_180checked : Checked tree [1,1,8,6] := by
  refine ⟨plan1874,valid1874,t4_180choices,?_⟩
  exact check_of_frontier tree 0 t4_180root t4_180jobs t4_180frontier t4_180all
theorem t4_181choices : plan1875.choices=[1,1,8,7].map (options 4 2) := by rfl


theorem t4_181part0 : t4_181jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_181frontier : t4_181root.frontier 0=t4_181jobs := by rfl
theorem t4_181all : t4_181jobs.all (Job.check tree)=true := by
  simp only [t4_181jobs,List.all_append,List.all_nil,t4_181part0,Bool.and_self]
theorem t4_181checked : Checked tree [1,1,8,7] := by
  refine ⟨plan1875,valid1875,t4_181choices,?_⟩
  exact check_of_frontier tree 0 t4_181root t4_181jobs t4_181frontier t4_181all
theorem t4_182choices : plan1876.choices=[1,1,8,10].map (options 4 2) := by rfl


theorem t4_182part0 : t4_182jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_182frontier : t4_182root.frontier 0=t4_182jobs := by rfl
theorem t4_182all : t4_182jobs.all (Job.check tree)=true := by
  simp only [t4_182jobs,List.all_append,List.all_nil,t4_182part0,Bool.and_self]
theorem t4_182checked : Checked tree [1,1,8,10] := by
  refine ⟨plan1876,valid1876,t4_182choices,?_⟩
  exact check_of_frontier tree 0 t4_182root t4_182jobs t4_182frontier t4_182all
theorem t4_183choices : plan1754.choices=[1,1,9,3].map (options 4 1) := by rfl


theorem t4_183part0 : t4_183jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_183frontier : t4_183root.frontier 0=t4_183jobs := by rfl
theorem t4_183all : t4_183jobs.all (Job.check tree)=true := by
  simp only [t4_183jobs,List.all_append,List.all_nil,t4_183part0,Bool.and_self]
theorem t4_183checked : Checked tree [1,1,9,3] := by
  refine ⟨plan1754,valid1754,t4_183choices,?_⟩
  exact check_of_frontier tree 0 t4_183root t4_183jobs t4_183frontier t4_183all
theorem t4_184choices : plan1877.choices=[1,1,9,6].map (options 4 2) := by rfl


theorem t4_184part0 : t4_184jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_184frontier : t4_184root.frontier 0=t4_184jobs := by rfl
theorem t4_184all : t4_184jobs.all (Job.check tree)=true := by
  simp only [t4_184jobs,List.all_append,List.all_nil,t4_184part0,Bool.and_self]
theorem t4_184checked : Checked tree [1,1,9,6] := by
  refine ⟨plan1877,valid1877,t4_184choices,?_⟩
  exact check_of_frontier tree 0 t4_184root t4_184jobs t4_184frontier t4_184all
theorem t4_185choices : plan1878.choices=[1,1,9,7].map (options 4 2) := by rfl


theorem t4_185part0 : t4_185jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_185frontier : t4_185root.frontier 0=t4_185jobs := by rfl
theorem t4_185all : t4_185jobs.all (Job.check tree)=true := by
  simp only [t4_185jobs,List.all_append,List.all_nil,t4_185part0,Bool.and_self]
theorem t4_185checked : Checked tree [1,1,9,7] := by
  refine ⟨plan1878,valid1878,t4_185choices,?_⟩
  exact check_of_frontier tree 0 t4_185root t4_185jobs t4_185frontier t4_185all
theorem t4_186choices : plan1879.choices=[1,1,9,9].map (options 4 2) := by rfl


theorem t4_186part0 : t4_186jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_186frontier : t4_186root.frontier 0=t4_186jobs := by rfl
theorem t4_186all : t4_186jobs.all (Job.check tree)=true := by
  simp only [t4_186jobs,List.all_append,List.all_nil,t4_186part0,Bool.and_self]
theorem t4_186checked : Checked tree [1,1,9,9] := by
  refine ⟨plan1879,valid1879,t4_186choices,?_⟩
  exact check_of_frontier tree 0 t4_186root t4_186jobs t4_186frontier t4_186all
theorem t4_187choices : plan1880.choices=[1,1,9,10].map (options 4 2) := by rfl


theorem t4_187part0 : t4_187jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_187frontier : t4_187root.frontier 0=t4_187jobs := by rfl
theorem t4_187all : t4_187jobs.all (Job.check tree)=true := by
  simp only [t4_187jobs,List.all_append,List.all_nil,t4_187part0,Bool.and_self]
theorem t4_187checked : Checked tree [1,1,9,10] := by
  refine ⟨plan1880,valid1880,t4_187choices,?_⟩
  exact check_of_frontier tree 0 t4_187root t4_187jobs t4_187frontier t4_187all
theorem t4_188choices : plan1881.choices=[1,1,10,7].map (options 4 2) := by rfl


theorem t4_188part0 : t4_188jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_188frontier : t4_188root.frontier 0=t4_188jobs := by rfl
theorem t4_188all : t4_188jobs.all (Job.check tree)=true := by
  simp only [t4_188jobs,List.all_append,List.all_nil,t4_188part0,Bool.and_self]
theorem t4_188checked : Checked tree [1,1,10,7] := by
  refine ⟨plan1881,valid1881,t4_188choices,?_⟩
  exact check_of_frontier tree 0 t4_188root t4_188jobs t4_188frontier t4_188all
theorem t4_189choices : plan1882.choices=[1,1,10,10].map (options 4 2) := by rfl


theorem t4_189part0 : t4_189jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_189frontier : t4_189root.frontier 0=t4_189jobs := by rfl
theorem t4_189all : t4_189jobs.all (Job.check tree)=true := by
  simp only [t4_189jobs,List.all_append,List.all_nil,t4_189part0,Bool.and_self]
theorem t4_189checked : Checked tree [1,1,10,10] := by
  refine ⟨plan1882,valid1882,t4_189choices,?_⟩
  exact check_of_frontier tree 0 t4_189root t4_189jobs t4_189frontier t4_189all
theorem t4_190choices : plan1704.choices=[1,2,2,2].map (options 4 0) := by rfl


theorem t4_190part0 : t4_190jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_190frontier : t4_190root.frontier 0=t4_190jobs := by rfl
theorem t4_190all : t4_190jobs.all (Job.check tree)=true := by
  simp only [t4_190jobs,List.all_append,List.all_nil,t4_190part0,Bool.and_self]
theorem t4_190checked : Checked tree [1,2,2,2] := by
  refine ⟨plan1704,valid1704,t4_190choices,?_⟩
  exact check_of_frontier tree 0 t4_190root t4_190jobs t4_190frontier t4_190all
theorem t4_191choices : plan1705.choices=[1,2,2,3].map (options 4 0) := by rfl


theorem t4_191part0 : t4_191jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_191frontier : t4_191root.frontier 0=t4_191jobs := by rfl
theorem t4_191all : t4_191jobs.all (Job.check tree)=true := by
  simp only [t4_191jobs,List.all_append,List.all_nil,t4_191part0,Bool.and_self]
theorem t4_191checked : Checked tree [1,2,2,3] := by
  refine ⟨plan1705,valid1705,t4_191choices,?_⟩
  exact check_of_frontier tree 0 t4_191root t4_191jobs t4_191frontier t4_191all
theorem t4_192choices : plan1755.choices=[1,2,2,5].map (options 4 1) := by rfl


theorem t4_192part0 : t4_192jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_192frontier : t4_192root.frontier 0=t4_192jobs := by rfl
theorem t4_192all : t4_192jobs.all (Job.check tree)=true := by
  simp only [t4_192jobs,List.all_append,List.all_nil,t4_192part0,Bool.and_self]
theorem t4_192checked : Checked tree [1,2,2,5] := by
  refine ⟨plan1755,valid1755,t4_192choices,?_⟩
  exact check_of_frontier tree 0 t4_192root t4_192jobs t4_192frontier t4_192all
theorem t4_193choices : plan1756.choices=[1,2,2,6].map (options 4 1) := by rfl


theorem t4_193part0 : t4_193jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_193frontier : t4_193root.frontier 0=t4_193jobs := by rfl
theorem t4_193all : t4_193jobs.all (Job.check tree)=true := by
  simp only [t4_193jobs,List.all_append,List.all_nil,t4_193part0,Bool.and_self]
theorem t4_193checked : Checked tree [1,2,2,6] := by
  refine ⟨plan1756,valid1756,t4_193choices,?_⟩
  exact check_of_frontier tree 0 t4_193root t4_193jobs t4_193frontier t4_193all
theorem t4_194choices : plan1757.choices=[1,2,2,7].map (options 4 1) := by rfl


theorem t4_194part0 : t4_194jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_194frontier : t4_194root.frontier 0=t4_194jobs := by rfl
theorem t4_194all : t4_194jobs.all (Job.check tree)=true := by
  simp only [t4_194jobs,List.all_append,List.all_nil,t4_194part0,Bool.and_self]
theorem t4_194checked : Checked tree [1,2,2,7] := by
  refine ⟨plan1757,valid1757,t4_194choices,?_⟩
  exact check_of_frontier tree 0 t4_194root t4_194jobs t4_194frontier t4_194all
theorem t4_195choices : plan1758.choices=[1,2,2,9].map (options 4 1) := by rfl


theorem t4_195part0 : t4_195jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_195frontier : t4_195root.frontier 0=t4_195jobs := by rfl
theorem t4_195all : t4_195jobs.all (Job.check tree)=true := by
  simp only [t4_195jobs,List.all_append,List.all_nil,t4_195part0,Bool.and_self]
theorem t4_195checked : Checked tree [1,2,2,9] := by
  refine ⟨plan1758,valid1758,t4_195choices,?_⟩
  exact check_of_frontier tree 0 t4_195root t4_195jobs t4_195frontier t4_195all
theorem t4_196choices : plan1759.choices=[1,2,2,10].map (options 4 1) := by rfl


theorem t4_196part0 : t4_196jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_196frontier : t4_196root.frontier 0=t4_196jobs := by rfl
theorem t4_196all : t4_196jobs.all (Job.check tree)=true := by
  simp only [t4_196jobs,List.all_append,List.all_nil,t4_196part0,Bool.and_self]
theorem t4_196checked : Checked tree [1,2,2,10] := by
  refine ⟨plan1759,valid1759,t4_196choices,?_⟩
  exact check_of_frontier tree 0 t4_196root t4_196jobs t4_196frontier t4_196all
theorem t4_197choices : plan1706.choices=[1,2,3,3].map (options 4 0) := by rfl


theorem t4_197part0 : t4_197jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_197frontier : t4_197root.frontier 0=t4_197jobs := by rfl
theorem t4_197all : t4_197jobs.all (Job.check tree)=true := by
  simp only [t4_197jobs,List.all_append,List.all_nil,t4_197part0,Bool.and_self]
theorem t4_197checked : Checked tree [1,2,3,3] := by
  refine ⟨plan1706,valid1706,t4_197choices,?_⟩
  exact check_of_frontier tree 0 t4_197root t4_197jobs t4_197frontier t4_197all
theorem t4_198choices : plan1760.choices=[1,2,3,6].map (options 4 1) := by rfl


theorem t4_198part0 : t4_198jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_198frontier : t4_198root.frontier 0=t4_198jobs := by rfl
theorem t4_198all : t4_198jobs.all (Job.check tree)=true := by
  simp only [t4_198jobs,List.all_append,List.all_nil,t4_198part0,Bool.and_self]
theorem t4_198checked : Checked tree [1,2,3,6] := by
  refine ⟨plan1760,valid1760,t4_198choices,?_⟩
  exact check_of_frontier tree 0 t4_198root t4_198jobs t4_198frontier t4_198all
theorem t4_199choices : plan1761.choices=[1,2,3,7].map (options 4 1) := by rfl


theorem t4_199part0 : t4_199jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_199frontier : t4_199root.frontier 0=t4_199jobs := by rfl
theorem t4_199all : t4_199jobs.all (Job.check tree)=true := by
  simp only [t4_199jobs,List.all_append,List.all_nil,t4_199part0,Bool.and_self]
theorem t4_199checked : Checked tree [1,2,3,7] := by
  refine ⟨plan1761,valid1761,t4_199choices,?_⟩
  exact check_of_frontier tree 0 t4_199root t4_199jobs t4_199frontier t4_199all
theorem t4_200choices : plan1762.choices=[1,2,3,10].map (options 4 1) := by rfl


theorem t4_200part0 : t4_200jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_200frontier : t4_200root.frontier 0=t4_200jobs := by rfl
theorem t4_200all : t4_200jobs.all (Job.check tree)=true := by
  simp only [t4_200jobs,List.all_append,List.all_nil,t4_200part0,Bool.and_self]
theorem t4_200checked : Checked tree [1,2,3,10] := by
  refine ⟨plan1762,valid1762,t4_200choices,?_⟩
  exact check_of_frontier tree 0 t4_200root t4_200jobs t4_200frontier t4_200all
theorem t4_201choices : plan1763.choices=[1,2,5,3].map (options 4 1) := by rfl


theorem t4_201part0 : t4_201jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_201frontier : t4_201root.frontier 0=t4_201jobs := by rfl
theorem t4_201all : t4_201jobs.all (Job.check tree)=true := by
  simp only [t4_201jobs,List.all_append,List.all_nil,t4_201part0,Bool.and_self]
theorem t4_201checked : Checked tree [1,2,5,3] := by
  refine ⟨plan1763,valid1763,t4_201choices,?_⟩
  exact check_of_frontier tree 0 t4_201root t4_201jobs t4_201frontier t4_201all
theorem t4_202choices : plan1883.choices=[1,2,5,5].map (options 4 2) := by rfl


theorem t4_202part0 : t4_202jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_202frontier : t4_202root.frontier 0=t4_202jobs := by rfl
theorem t4_202all : t4_202jobs.all (Job.check tree)=true := by
  simp only [t4_202jobs,List.all_append,List.all_nil,t4_202part0,Bool.and_self]
theorem t4_202checked : Checked tree [1,2,5,5] := by
  refine ⟨plan1883,valid1883,t4_202choices,?_⟩
  exact check_of_frontier tree 0 t4_202root t4_202jobs t4_202frontier t4_202all
theorem t4_203choices : plan1884.choices=[1,2,5,6].map (options 4 2) := by rfl


theorem t4_203part0 : t4_203jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_203frontier : t4_203root.frontier 0=t4_203jobs := by rfl
theorem t4_203all : t4_203jobs.all (Job.check tree)=true := by
  simp only [t4_203jobs,List.all_append,List.all_nil,t4_203part0,Bool.and_self]
theorem t4_203checked : Checked tree [1,2,5,6] := by
  refine ⟨plan1884,valid1884,t4_203choices,?_⟩
  exact check_of_frontier tree 0 t4_203root t4_203jobs t4_203frontier t4_203all
theorem t4_204choices : plan1885.choices=[1,2,5,7].map (options 4 2) := by rfl


theorem t4_204part0 : t4_204jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_204frontier : t4_204root.frontier 0=t4_204jobs := by rfl
theorem t4_204all : t4_204jobs.all (Job.check tree)=true := by
  simp only [t4_204jobs,List.all_append,List.all_nil,t4_204part0,Bool.and_self]
theorem t4_204checked : Checked tree [1,2,5,7] := by
  refine ⟨plan1885,valid1885,t4_204choices,?_⟩
  exact check_of_frontier tree 0 t4_204root t4_204jobs t4_204frontier t4_204all
theorem t4_205choices : plan1886.choices=[1,2,5,9].map (options 4 2) := by rfl


theorem t4_205part0 : t4_205jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_205frontier : t4_205root.frontier 0=t4_205jobs := by rfl
theorem t4_205all : t4_205jobs.all (Job.check tree)=true := by
  simp only [t4_205jobs,List.all_append,List.all_nil,t4_205part0,Bool.and_self]
theorem t4_205checked : Checked tree [1,2,5,9] := by
  refine ⟨plan1886,valid1886,t4_205choices,?_⟩
  exact check_of_frontier tree 0 t4_205root t4_205jobs t4_205frontier t4_205all
theorem t4_206choices : plan1887.choices=[1,2,5,10].map (options 4 2) := by rfl


theorem t4_206part0 : t4_206jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_206frontier : t4_206root.frontier 0=t4_206jobs := by rfl
theorem t4_206all : t4_206jobs.all (Job.check tree)=true := by
  simp only [t4_206jobs,List.all_append,List.all_nil,t4_206part0,Bool.and_self]
theorem t4_206checked : Checked tree [1,2,5,10] := by
  refine ⟨plan1887,valid1887,t4_206choices,?_⟩
  exact check_of_frontier tree 0 t4_206root t4_206jobs t4_206frontier t4_206all
theorem t4_207choices : plan1888.choices=[1,2,6,6].map (options 4 2) := by rfl


theorem t4_207part0 : t4_207jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_207frontier : t4_207root.frontier 0=t4_207jobs := by rfl
theorem t4_207all : t4_207jobs.all (Job.check tree)=true := by
  simp only [t4_207jobs,List.all_append,List.all_nil,t4_207part0,Bool.and_self]
theorem t4_207checked : Checked tree [1,2,6,6] := by
  refine ⟨plan1888,valid1888,t4_207choices,?_⟩
  exact check_of_frontier tree 0 t4_207root t4_207jobs t4_207frontier t4_207all
theorem t4_208choices : plan1889.choices=[1,2,6,7].map (options 4 2) := by rfl


theorem t4_208part0 : t4_208jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_208frontier : t4_208root.frontier 0=t4_208jobs := by rfl
theorem t4_208all : t4_208jobs.all (Job.check tree)=true := by
  simp only [t4_208jobs,List.all_append,List.all_nil,t4_208part0,Bool.and_self]
theorem t4_208checked : Checked tree [1,2,6,7] := by
  refine ⟨plan1889,valid1889,t4_208choices,?_⟩
  exact check_of_frontier tree 0 t4_208root t4_208jobs t4_208frontier t4_208all
theorem t4_209choices : plan1890.choices=[1,2,6,10].map (options 4 2) := by rfl


theorem t4_209part0 : t4_209jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_209frontier : t4_209root.frontier 0=t4_209jobs := by rfl
theorem t4_209all : t4_209jobs.all (Job.check tree)=true := by
  simp only [t4_209jobs,List.all_append,List.all_nil,t4_209part0,Bool.and_self]
theorem t4_209checked : Checked tree [1,2,6,10] := by
  refine ⟨plan1890,valid1890,t4_209choices,?_⟩
  exact check_of_frontier tree 0 t4_209root t4_209jobs t4_209frontier t4_209all
theorem t4_210choices : plan1891.choices=[1,2,7,7].map (options 4 2) := by rfl


theorem t4_210part0 : t4_210jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_210frontier : t4_210root.frontier 0=t4_210jobs := by rfl
theorem t4_210all : t4_210jobs.all (Job.check tree)=true := by
  simp only [t4_210jobs,List.all_append,List.all_nil,t4_210part0,Bool.and_self]
theorem t4_210checked : Checked tree [1,2,7,7] := by
  refine ⟨plan1891,valid1891,t4_210choices,?_⟩
  exact check_of_frontier tree 0 t4_210root t4_210jobs t4_210frontier t4_210all
theorem t4_211choices : plan1764.choices=[1,2,9,3].map (options 4 1) := by rfl


theorem t4_211part0 : t4_211jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_211frontier : t4_211root.frontier 0=t4_211jobs := by rfl
theorem t4_211all : t4_211jobs.all (Job.check tree)=true := by
  simp only [t4_211jobs,List.all_append,List.all_nil,t4_211part0,Bool.and_self]
theorem t4_211checked : Checked tree [1,2,9,3] := by
  refine ⟨plan1764,valid1764,t4_211choices,?_⟩
  exact check_of_frontier tree 0 t4_211root t4_211jobs t4_211frontier t4_211all
theorem t4_212choices : plan1892.choices=[1,2,9,6].map (options 4 2) := by rfl


theorem t4_212part0 : t4_212jobs0.all (Job.check tree)=true := by decide +kernel

theorem t4_212frontier : t4_212root.frontier 0=t4_212jobs := by rfl
theorem t4_212all : t4_212jobs.all (Job.check tree)=true := by
  simp only [t4_212jobs,List.all_append,List.all_nil,t4_212part0,Bool.and_self]
theorem t4_212checked : Checked tree [1,2,9,6] := by
  refine ⟨plan1892,valid1892,t4_212choices,?_⟩
  exact check_of_frontier tree 0 t4_212root t4_212jobs t4_212frontier t4_212all
end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : Sensitivity213981Formal.Contracts.Endpoint22ReachChecks000 :=
  ⟨⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_68checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_69checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_70checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_71checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_72checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_73checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_2checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_74checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_75checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_76checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_77checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_78checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_79checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_80checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_81checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_82checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_3checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_83checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_84checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_85checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_86checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_87checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_88checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_89checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_90checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_91checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_92checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_4checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_93checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t0_0checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_94checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_95checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_96checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_97checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_98checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_99checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_100checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_101checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_5checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_102checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_103checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_104checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_105checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_106checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_107checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_108checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_109checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_110checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_111checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_6checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_112checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_113checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_114checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_115checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_116checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_117checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_118checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_119checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_120checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_7checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_121checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_122checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_123checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_124checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_125checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_126checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_127checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_128checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_129checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_130checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_8checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_131checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_132checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_133checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_134checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_135checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_136checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_137checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_138checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_139checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_9checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_140checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_141checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_142checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_143checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_144checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_145checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_146checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_147checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_148checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_149checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_10checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_150checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_151checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_152checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_153checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_154checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_155checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_156checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_157checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_158checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_11checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_159checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_160checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_161checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_162checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_163checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_164checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_165checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_166checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_167checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_168checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_12checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_169checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_170checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_171checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_172checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_173checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_174checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_175checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_176checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_177checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_178checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_13checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_179checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_180checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_181checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_182checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_183checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_184checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_185checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t1_0checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_186checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_187checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_14checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_188checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_189checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_190checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_191checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_192checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_193checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_194checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_195checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_196checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_197checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_15checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_198checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_199checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_200checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_201checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_202checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_203checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_204checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_205checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_206checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_16checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_207checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_208checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_209checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_210checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_211checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_212checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_213checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_214checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_215checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_216checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_17checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_217checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_218checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_219checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_220checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_221checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_222checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_223checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_224checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_225checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_226checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_18checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_227checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_228checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_229checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_230checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_231checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_232checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_233checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_234checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_235checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_19checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_236checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_237checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_238checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_239checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_240checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_241checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_242checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_243checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_244checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_245checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_20checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_246checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_247checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_248checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_249checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_250checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_251checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_252checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_253checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_254checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_255checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_21checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_256checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_257checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_258checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_259checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_260checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_261checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_262checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_263checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_264checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_22checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_265checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_266checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_267checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_268checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_0checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_1checked⟩,
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_2checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_3checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_4checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_5checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_23checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_6checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_7checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_8checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t1_1checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_9checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_10checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_11checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_12checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_13checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_14checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_15checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_24checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_16checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_17checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_18checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_19checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_20checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_21checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_22checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_23checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_24checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_25checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_25checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_26checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_27checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_28checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_29checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_30checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_31checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_32checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_33checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_34checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_35checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_26checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_36checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_37checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_38checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_39checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_40checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_41checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_42checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_43checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_44checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_45checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_27checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_46checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_47checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_48checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_49checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_50checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_51checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_52checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_53checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_54checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_55checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_28checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_56checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_57checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_58checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_59checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_60checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_61checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_62checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_63checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_64checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_29checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_65checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_66checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_67checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_68checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_69checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_70checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_71checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_72checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_73checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_74checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_30checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_75checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_76checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_77checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_78checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_79checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_80checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_81checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_82checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_83checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_84checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_31checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_85checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_86checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_87checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_88checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_89checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_90checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_91checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_92checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_93checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_94checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_32checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_95checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_96checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_97checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_98checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_99checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_100checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_101checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t1_2checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_102checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_103checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_33checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_104checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_105checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_106checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_107checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_108checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_109checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_110checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_111checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_112checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_113checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_34checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_114checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_115checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_116checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_117checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_118checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_119checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_120checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_121checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_122checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_123checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_35checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_124checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_125checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_126checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_127checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_128checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_129checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_130checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_131checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_132checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_36checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_133checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_134checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_135checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_136checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_137checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_138checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_139checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_140checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_141checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_142checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_37checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_143checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_144checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_145checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_146checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_147checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_148checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_149checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_150checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_151checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_38checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_152checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_153checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_154checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_155checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_156checked⟩,
  ⟨Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_157checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_158checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_159checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_160checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_161checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_39checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_162checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_163checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_164checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_165checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_166checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_167checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_168checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_169checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_170checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_40checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_171checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_172checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_173checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_174checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_175checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_176checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_177checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_178checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_179checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_180checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_41checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_181checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_182checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_183checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_184checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_185checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_186checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_187checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_188checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_189checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_42checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_190checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_191checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_192checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t1_3checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_193checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_194checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_195checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_196checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_197checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_198checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_199checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_43checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_200checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_201checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_202checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_203checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_204checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_205checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_206checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_207checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_208checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_44checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_209checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_210checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_211checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t4_212checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_45checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_46checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_47checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_48checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_49checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_50checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_51checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t1_4checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_52checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_53checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_54checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_55checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_56checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_57checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_58checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_59checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_60checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_61checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t1_5checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_62checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_63checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_64checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_0checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_1checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_2checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_3checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_4checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_5checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t1_6checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_6checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_7checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_8checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_9checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_10checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_11checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_12checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_13checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_14checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_15checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t1_7checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_16checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_17checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_18checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_19checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_20checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_21checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_22checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_23checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_24checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t1_8checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_25checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_26checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_27checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_28checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_29checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_30checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_31checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_32checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_33checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_34checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t1_9checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_35checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_36checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_37checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_38checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_39checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_40checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_41checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_42checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_43checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_44checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t1_10checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_45checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_46checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_47checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_48checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_49checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_50checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_51checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_52checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_53checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_0checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_54checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_55checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_56checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_57checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_58checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_59checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_60checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_61checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_62checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_63checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t2_1checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_64checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_65checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_66checked,
   Sensitivity213981Formal.ThreeBoundEndpoint22Reachable.t3_67checked⟩⟩
