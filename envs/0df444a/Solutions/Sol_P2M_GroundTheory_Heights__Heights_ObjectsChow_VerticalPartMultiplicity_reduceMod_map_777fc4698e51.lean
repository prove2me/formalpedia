-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_reduceMod_map_777fc4698e51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:59.69328+00:00
-- url     : https://prove2.me/submissions/c53a5486-bb3c-455e-92af-931680d81561

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___C_69cba9f8a099
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___X_2766bae06565
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity___apply_4b7c83e32abd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_finIdeal_eq_map_4a676a9bfd34

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
theorem _root_.solution (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (W : Ideal (MRing (PBlk n))) :
    reduceMod v (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) =
      (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map
        (MvPolynomial.map (Int.castRingHom v.asIdeal.ResidueField)) := by
  rw [reduceMod, finIdeal_eq_map, Ideal.map_map, Ideal.map_map]
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
  · simp [Ψ_C, ι_apply]
  · obtain ⟨⟨⟩, i⟩ := p
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
    rw [Ψ_X]
    simp [eb]
end GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
