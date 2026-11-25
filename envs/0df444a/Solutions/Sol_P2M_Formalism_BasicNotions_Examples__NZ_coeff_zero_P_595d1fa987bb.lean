-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__NZ_coeff_zero_P_595d1fa987bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:51:30.184772+00:00
-- url     : https://prove2.me/submissions/39cf48e5-6171-40e5-a4b1-e2d2d5e902b3

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeA
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZTypeB
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_orbQ_monic_0e02f754a39e
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_mem_rootsBar_P_9cb9ba47d11d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open Polynomial Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime]
variable {d : ℕ} (hd : 1 ≤ d) (u : (Fbar g)ˣ) (hu : orderOf u = g ^ d - 1)
variable {P : (ZMod g)[X]} (hP : P.map (algebraMap (ZMod g) (Fbar g)) = orbQ d u)
include hP
namespace Formalism.BasicNotions.Examples₂.NZ
theorem _root_.solution : P.coeff 0 ≠ 0 := by
  intro h0
  have hPm : P.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 := by
    rw [hP]; exact (orbQ_monic u).ne_zero
  have h0r : (0 : Fbar g) ∈ rootsBar P := by
    rw [rootsBar, mem_roots hPm, IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
  obtain ⟨i, -, hi⟩ := (mem_rootsBar_P u hP).1 h0r
  exact pow_ne_zero _ u.ne_zero hi.symm
end Formalism.BasicNotions.Examples₂.NZ
