-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_exists_ringKrullDim_quotient_eq_nat_52c672d92a95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:07:11.47727+00:00
-- url     : https://prove2.me/submissions/9b66c5e6-f69c-4ecd-bace-00e33252009b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCompDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFibreCompDim
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_exists_ringKrullDim_eq_trdeg


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
open MvPolynomial IsDedekindDomain
variable {O : Type} [CommRing O] [IsDedekindDomain O] {n : ℕ} (v : HeightOneSpectrum O)
  (W : Ideal (MvPolynomial (Fin n) O))
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution (hWp : W.IsPrime)
    (hW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W) :
    ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) O ⧸ W) = m := by
  let φ : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) v.asIdeal.ResidueField :=
    MvPolynomial.map (algebraMap O v.asIdeal.ResidueField)
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)
  have hkerW : RingHom.ker φ ≤ W := by
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]
    exact hW
  have : (W.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hkerW
  obtain ⟨m, hm, -⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := v.asIdeal.ResidueField) (A := MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸ W.map φ)
  exact ⟨m, (ringKrullDim_eq_of_ringEquiv (quotientResidueEquiv v W hW)).trans hm⟩
end GroundTheory.Heights₂.Heights.Vertical
