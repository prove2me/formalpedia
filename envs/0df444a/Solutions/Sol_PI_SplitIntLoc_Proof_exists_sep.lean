-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:38:23.946802+00:00
-- url     : https://prove2.me/submissions/dbc5da49-9cdb-4399-8f4b-6c7f239117c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_ExistsUnitDiff
import Theorems.Thm_PI_SplitIntLoc_Proof_exists_small
import Theorems.Thm_PI_SplitIntLoc_Proof_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped TensorProduct
noncomputable section
open PI PI.SplitIntLoc PI.SplitIntLoc.Proof
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))
namespace PI.SplitIntLoc.Proof
theorem _root_.solution (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) :
    ∃ y : E, 1 < Valued.v (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y) ∧
      Valued.v (emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) y) < 1 := by
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_small (v := v)
  obtain ⟨y, h1, h2⟩ := approx spl hspl (spl.symm (ϖ⁻¹, 0))
  rw [RingEquiv.apply_symm_apply] at h1 h2
  dsimp only at h1 h2
  have hinv : 1 < Valued.v ϖ⁻¹ := by
    by_contra h
    rw [not_lt] at h
    have h3 : Valued.v ϖ * Valued.v ϖ⁻¹ < 1 :=
      calc Valued.v ϖ * Valued.v ϖ⁻¹ ≤ Valued.v ϖ * 1 := by gcongr
        _ = Valued.v ϖ := mul_one _
        _ < 1 := hϖ
    rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one] at h3
    exact lt_irrefl _ h3
  refine ⟨y, ?_, ?_⟩
  · have hlt : Valued.v (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) y - ϖ⁻¹) < Valued.v ϖ⁻¹ := by
      rw [Valuation.map_sub_swap]
      exact h1.trans hinv
    rw [Valuation.map_eq_of_sub_lt _ hlt]
    exact hinv
  · rw [zero_sub, Valuation.map_neg] at h2
    exact h2
end PI.SplitIntLoc.Proof
