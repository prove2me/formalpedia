-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_comap_C_map_22a1272d45e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:38.973739+00:00
-- url     : https://prove2.me/submissions/1ec48520-aab2-4ae0-a362-a0165d0cbb21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___symm_C_bfe0d688257b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
theorem _root_.solution (W : Ideal (MRing (PBlk n))) :
    (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
        (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) =
      (W.comap (C : ℤ →+* MRing (PBlk n))).map (ι : ℤ →+* 𝓞 ℚ) := by
  ext a
  rw [Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap, Ideal.map_comap_of_equiv,
    Ideal.mem_comap, Ideal.mem_comap]
  exact Iff.of_eq (congrArg (· ∈ W) (Ψ_symm_C a))
end GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
