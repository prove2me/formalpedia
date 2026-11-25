-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_homogeneousComponent_map_coeffs_93ef5918ee46
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:46.756338+00:00
-- url     : https://prove2.me/submissions/db7c3ced-70c2-4511-8fe7-5bdad82d4bcb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCompDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PMinimalPrimeHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecCompDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (d : ℕ) (p : MvPolynomial (Fin n) R) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.Vertical
