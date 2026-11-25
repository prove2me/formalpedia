-- Prove2me | solution 1 for P2M_GlobalTheory_UnitLemma_UnitBase___mem_adjoin_4ad2303c8cd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:09:44.562306+00:00
-- url     : https://prove2.me/submissions/c85ec09e-5c95-455e-9b88-56ed95a0b360

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_UnitBase_mem_adjoin_of_mul_eq_one__921c5f9af334
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_UnitBase___algebraMap_O_5df93c796371
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_UnitBase_isIntegral___13d1f3e3df15

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.UnitBase
theorem _root_.solution {K : UQ} (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (hint : IsIntegral K.O B.g)
    {y : B.A} (hy : y ∈ Algebra.adjoin K.O {B.g}) : B.σ y ∈ Algebra.adjoin K.O {B.g} := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact mem_adjoin_of_mul_eq_one' hg (isIntegral_σ B hint)
  | algebraMap r => rw [σ_algebraMap_O]; exact Subalgebra.algebraMap_mem _ _
  | add x z _ _ hx hz => rw [map_add]; exact Subalgebra.add_mem _ hx hz
  | mul x z _ _ hx hz => rw [map_mul]; exact Subalgebra.mul_mem _ hx hz
end GlobalTheory.UnitLemma.UnitBase
