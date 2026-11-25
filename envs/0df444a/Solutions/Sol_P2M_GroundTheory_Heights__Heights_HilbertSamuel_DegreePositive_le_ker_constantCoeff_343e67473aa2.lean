-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_DegreePositive_le_ker_constantCoeff_343e67473aa2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:21:40.298033+00:00
-- url     : https://prove2.me/submissions/2ef46089-2389-4142-9b89-0872c3b700b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsDegreePositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertDimZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PIntersectionRecursion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PDegreePositive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.DegreePositive
variable {F : Type} [Field F] {ι₀ : Type} [Fintype ι₀]
omit [Fintype ι₀]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.DegreePositive
theorem _root_.solution (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) :
    q ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by
  intro p hp
  rw [RingHom.mem_ker]
  by_contra h
  have h0 := hq.multiHomog p hp 0
  rw [weightedHomogeneousComponent_zero p (fun v => by
    obtain ⟨⟨⟩, _⟩ := v
    intro h'
    have := congrFun h' ()
    simp [blockWeight] at this)] at h0
  have hu : IsUnit (C (coeff 0 p) : MRing (fun _ : Unit => ι₀) F) :=
    (isUnit_iff_ne_zero.mpr (by rwa [← constantCoeff_eq])).map C
  exact hq.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 hu)
end GroundTheory.Heights₂.Heights.HilbertSamuel.DegreePositive
