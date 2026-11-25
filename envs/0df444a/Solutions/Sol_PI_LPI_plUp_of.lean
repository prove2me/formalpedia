-- Prove2me | solution 1 for PI.LPI.plUp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:22.186225+00:00
-- url     : https://prove2.me/submissions/0016a8ff-fc5d-4582-8eac-74bd03a3194b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVSumTmul
import Theorems.Thm_PI_LPI_exists_gen
import Theorems.Thm_PI_LPI_prV_sum_tmul
import Theorems.Thm_PI_LPI_adOf_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
open PI PI.LPI
open Formalism.UG
namespace PI.LPI
theorem _root_.solution (hG : PLGen) (hI : PLInj) : PLUp := by
  intro F E _ _ _ _ _ n Lb hfin y hy
  obtain ⟨k, m, hm, hgen⟩ := exists_gen Lb hfin
  have hloc := fun v : HeightOneSpectrum (𝓞 F) =>
    (hG F E (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring n k Lb m hm hgen
      (fun j => prV (E := E) v (y j))).1 (hy v)
  choose a ha hya using hloc
  let A : Fin k → FiniteAdeleRing (𝓞 F) F := fun i => adOf (fun v => a v i) (fun v => ha v i)
  have hyA : (fun j => ∑ i, m i j ⊗ₜ[F] A i) ∈ latA F Lb :=
    (hG F E (FiniteAdeleRing (𝓞 F) F) (intAd F) n k Lb m hm hgen _).2
      ⟨A, fun i => adOf_mem _ _, rfl⟩
  have hyy : y = fun j => ∑ i, m i j ⊗ₜ[F] A i := by
    funext j
    refine sub_eq_zero.1 (hI F E _ fun v => ?_)
    rw [map_sub, sub_eq_zero, prV_sum_tmul]
    exact congrFun (hya v) j
  rw [hyy]
  exact hyA
end PI.LPI
