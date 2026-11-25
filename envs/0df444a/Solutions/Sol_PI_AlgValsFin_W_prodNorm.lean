-- Prove2me | solution 1 for PI.AlgValsFin.W.prodNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:57.735872+00:00
-- url     : https://prove2.me/submissions/e98522f1-4528-4cba-b98e-7b604938fecb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FinprodNormEmbedding
import Theorems.Thm_PI_AlgValsFin_W_prod_norm_emb
import Theorems.Thm_PI_AlgValsFin_W_finprod_norm_embedding

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
theorem _root_.solution : ProdNorm L := by
  intro k T hT
  have h3 := FinitePlace.prod_eq_inv_abs_norm (K := L) k.ne_zero
  rw [finprod_norm_embedding k T hT, Finset.prod_inv_distrib, Rat.cast_inv, Rat.cast_abs, inv_inj] at h3
  rw [prod_norm_emb, h3]
end PI.AlgValsFin.W
