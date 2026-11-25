-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.spl_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:12.873634+00:00
-- url     : https://prove2.me/submissions/69c13c14-5cca-4f65-b2d1-cf72a3dda32c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_ExistsUnitDiff
import Theorems.Thm_PI_SplitIntLoc_Proof_spl_tmul_one


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
theorem _root_.solution (hspl : ∀ a : (v.adicCompletion F), spl ((1 : E) ⊗ₜ[F] a) = (a, a)) (e : E) (a : (v.adicCompletion F)) :
    spl (e ⊗ₜ[F] a) =
      (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) e * a, emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) e * a) := by
  have h : e ⊗ₜ[F] a = (e ⊗ₜ[F] (1 : (v.adicCompletion F))) * ((1 : E) ⊗ₜ[F] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h, map_mul, spl_tmul_one, hspl]
  rfl
end PI.SplitIntLoc.Proof
