-- Prove2me | solution 1 for PositivityTheory.PrwZar.Qi.comp_lmul_map_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:27:07.945166+00:00
-- url     : https://prove2.me/submissions/5cebf4a8-09fc-4d9a-ac45-8063d3be3cc1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_QiCoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_CompLmulMapId

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open PositivityTheory PositivityTheory.PrwZar PositivityTheory.PrwZar.Qi
variable {K H : Type} [Field K] [CommRing H] [Algebra K H]
namespace PositivityTheory.PrwZar.Qi
theorem _root_.solution (ε : H →ₐ[K] K) (f : H →ₐ[K] H) (t : H ⊗[K] H) :
    f (Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε) t)) =
      Algebra.TensorProduct.lmul' K (Algebra.TensorProduct.map f ((Algebra.ofId K H).comp ε) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply,
      AlgHom.comp_apply, Algebra.ofId_apply, map_mul, AlgHom.commutes]
  | add s t hs ht => simp only [map_add, hs, ht]
end PositivityTheory.PrwZar.Qi
