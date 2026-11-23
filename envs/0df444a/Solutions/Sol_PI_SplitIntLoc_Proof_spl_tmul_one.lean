-- Prove2me | solution 1 for PI.SplitIntLoc.Proof.spl_tmul_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:27.220374+00:00
-- url     : https://prove2.me/submissions/a205c4c9-b1ee-4435-91f6-e96979bb73aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitPrimeIntegers_EmbMemOfIsIntegral

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
  (v : HeightOneSpectrum (𝓞 F))
variable {v} (spl : E ⊗[F] (v.adicCompletion F) ≃+* (v.adicCompletion F) × (v.adicCompletion F))
namespace PI.SplitIntLoc.Proof
theorem _root_.solution (e : E) :
    spl (e ⊗ₜ[F] 1) = (emb spl (RingHom.fst (v.adicCompletion F) (v.adicCompletion F)) e, emb spl (RingHom.snd (v.adicCompletion F) (v.adicCompletion F)) e) := rfl
end PI.SplitIntLoc.Proof
