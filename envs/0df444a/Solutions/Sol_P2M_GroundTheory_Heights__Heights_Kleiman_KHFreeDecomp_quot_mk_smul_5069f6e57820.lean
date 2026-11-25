-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_quot_mk_smul_5069f6e57820
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:23.779798+00:00
-- url     : https://prove2.me/submissions/077c1548-3db4-44d7-81e2-d3ff612e0661

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeDecompSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeDecomp

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
theorem _root_.solution (s : S) (p : MRingOver S ι) :
    Ideal.Quotient.mk (⊥ : Ideal (MRingOver S ι)) (s • p) = s • Ideal.Quotient.mk ⊥ p := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap]
end GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
