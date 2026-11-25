-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__abs_det_trace_form_eq_discr_c436f7ffc8ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:53:00.705116+00:00
-- url     : https://prove2.me/submissions/fe63181e-1828-44a9-8e37-47dfc7809cfa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Module Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (hK : IsCMUnram K) :
    |(Matrix.of fun j j' : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      ((Algebra.trace ℚ K (star (integralBasis K j) * integralBasis K j') : ℚ) : ℝ)).det| = |(discr K : ℝ)| := by
  classical
  set B := integralBasis K with hB
  let s : K →ₗ[ℚ] K := (starRingEnd K).toRatAlgHom.toLinearMap
  have hs : ∀ x, s x = star x := fun x => rfl
  let A := LinearMap.toMatrix B B s
  let Mq : Matrix (Free.ChooseBasisIndex ℤ (𝓞 K)) (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ :=
    Matrix.of fun j j' => Algebra.trace ℚ K (star (B j) * B j')
  have hM : Mq = A.transpose * Algebra.traceMatrix ℚ B := by
    ext j j'
    rw [Matrix.mul_apply]
    simp only [Mq, A, Matrix.of_apply, Matrix.transpose_apply, LinearMap.toMatrix_apply,
      Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    conv_lhs => rw [← B.sum_repr (star (B j))]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, LinearMap.map_smul, smul_eq_mul, hs]
  have hA : A * A = 1 := by
    have hss : s ∘ₗ s = LinearMap.id := by
      ext x
      simp [hs]
    rw [← LinearMap.toMatrix_comp, hss, LinearMap.toMatrix_id]
  have hdet : A.det * A.det = 1 := by
    rw [← Matrix.det_mul, hA, Matrix.det_one]
  have hdet' : |A.det| = 1 := by
    rcases mul_self_eq_one_iff.1 hdet with h | h <;> simp [h]
  have hcast : (Matrix.of fun j j' : Free.ChooseBasisIndex ℤ (𝓞 K) =>
      ((Algebra.trace ℚ K (star (integralBasis K j) * integralBasis K j') : ℚ) : ℝ)).det = ((Mq.det : ℚ) : ℝ) := by
    rw [show ((Mq.det : ℚ) : ℝ) = Rat.castHom ℝ Mq.det from rfl, RingHom.map_det]
    congr 1
  rw [hcast, hM, Matrix.det_mul, Matrix.det_transpose, ← Algebra.discr_def, ← NumberField.coe_discr]
  rw [show (((A.det * (discr K : ℚ) : ℚ)) : ℝ) = ((A.det : ℚ) : ℝ) * ((discr K : ℤ) : ℝ) by push_cast; rfl]
  rw [abs_mul]
  have : |((A.det : ℚ) : ℝ)| = 1 := by
    rw [← Rat.cast_abs, hdet', Rat.cast_one]
  rw [this, one_mul]
end Formalism.MainNotions.BridgeLemma₂
