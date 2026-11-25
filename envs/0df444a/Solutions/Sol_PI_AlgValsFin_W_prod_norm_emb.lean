-- Prove2me | solution 1 for PI.AlgValsFin.W.prod_norm_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:26.470774+00:00
-- url     : https://prove2.me/submissions/f0ab8f27-e7cf-4b8e-9b1d-91aa085beea1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FinprodNormEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
namespace PI.AlgValsFin.W
theorem _root_.solution (x : L) : ∏ φ : L →+* ℂ, ‖φ x‖ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  calc ∏ φ : L →+* ℂ, ‖φ x‖ = ∏ σ : L →ₐ[ℚ] ℂ, ‖σ x‖ :=
        Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ fun _ => rfl
    _ = ‖∏ σ : L →ₐ[ℚ] ℂ, σ x‖ := (norm_prod _ _).symm
    _ = ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ := by rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
    _ = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
      rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
end PI.AlgValsFin.W
