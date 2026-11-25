-- Prove2me | solution 1 for P2M_Formalism_GM_DimensionMonotonicity_aeval_isWH__16e475c86f62
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:01.528076+00:00
-- url     : https://prove2.me/submissions/1d64881a-d961-4dcd-aeeb-82a1d9243c3d

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution {σ τ R M : Type} [CommSemiring R] [AddCommMonoid M] (w' : σ → M) (w : τ → M)
    (g : σ → MvPolynomial τ R) (hg : ∀ x, IsWeightedHomogeneous w (g x) (w' x))
    {f : MvPolynomial σ R} {d : M} (hf : IsWeightedHomogeneous w' f d) :
    IsWeightedHomogeneous w (aeval g f) d := by
  classical
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  have hmd : Finsupp.weight w' m = d := hf (mem_support_iff.mp hm)
  rw [← hmd, Finsupp.weight_apply]
  apply IsWeightedHomogeneous.C_mul
  exact IsWeightedHomogeneous.prod _ _ _ (fun i _ => (hg i).pow (m i))
end Formalism.GM.DimensionMonotonicity
