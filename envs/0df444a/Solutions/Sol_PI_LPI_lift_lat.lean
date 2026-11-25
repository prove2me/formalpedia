-- Prove2me | solution 1 for PI.LPI.lift_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:18.188823+00:00
-- url     : https://prove2.me/submissions/6fcc0b0e-d54f-439f-8ddb-76249d83442b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVSumTmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_SingleApply
import Theorems.Thm_PI_LPI_single_apply
import Theorems.Thm_PI_LPI_adOf_mem
import Theorems.Thm_PI_LPI_exists_gen
import Theorems.Thm_PI_LPI_prV_sum_tmul


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
theorem _root_.solution (hG : PLGen) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : ℕ} (Lb : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E ⊗[F] v.adicCompletion F) (hx : x ∈ latV v Lb) :
    ∃ y ∈ latA F Lb, (fun j => prV (E := E) v (y j)) = x := by
  obtain ⟨k, m, hm, hgen⟩ := exists_gen Lb hfin
  obtain ⟨a, ha, rfl⟩ :=
    (hG F E (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring n k Lb m hm hgen x).1 hx
  refine ⟨fun j => ∑ i, m i j ⊗ₜ[F] single v (a i) (ha i), ?_, ?_⟩
  · exact (hG F E (FiniteAdeleRing (𝓞 F) F) (intAd F) n k Lb m hm hgen _).2
      ⟨fun i => single v (a i) (ha i), fun i => adOf_mem _ _, rfl⟩
  · funext j
    rw [prV_sum_tmul]
    simp only [single_apply]
end PI.LPI
