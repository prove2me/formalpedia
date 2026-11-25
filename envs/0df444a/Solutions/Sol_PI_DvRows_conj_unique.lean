-- Prove2me | solution 1 for PI.DvRows.conj_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:22.499884+00:00
-- url     : https://prove2.me/submissions/312b2066-f46f-4cb2-88ff-105685c37419

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Theorems.Thm_PI_DvRows_mem_iff_vAdd_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
open Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K]
namespace PI.DvRows
theorem _root_.solution [StarRing K] {w a b : HeightOneSpectrum (𝓞 K)} (ha : IsConjPlK w a)
    (hb : IsConjPlK w b) : a = b := by
  have hv : ∀ x : K, vAdd a x = vAdd b x := fun x => by rw [ha x, hb x]
  ext r
  by_cases hr : r = 0
  · subst hr
    exact ⟨fun _ => b.asIdeal.zero_mem, fun _ => a.asIdeal.zero_mem⟩
  · rw [mem_iff_vAdd_pos a hr, mem_iff_vAdd_pos b hr, hv]
end PI.DvRows
