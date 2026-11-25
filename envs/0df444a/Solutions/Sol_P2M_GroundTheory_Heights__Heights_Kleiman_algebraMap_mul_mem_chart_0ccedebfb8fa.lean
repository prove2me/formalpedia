-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_mul_mem_chart_0ccedebfb8fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:37:34.316746+00:00
-- url     : https://prove2.me/submissions/72bfa1f7-a51b-41fb-8739-180170605c9f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreRestrKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
open scoped Pointwise nonZeroDivisors
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I : Chart x} (M : Submodule (chartRing S x I) Ω) (d : S) {v : Ω}
    (hv : v ∈ M) : algebraMap S Ω d * v ∈ M := by
  have := M.smul_mem (⟨algebraMap S Ω d, Subalgebra.algebraMap_mem _ d⟩ : chartRing S x I) hv
  rwa [chartRing_smul_def] at this
end GroundTheory.Heights₂.Heights.Kleiman
