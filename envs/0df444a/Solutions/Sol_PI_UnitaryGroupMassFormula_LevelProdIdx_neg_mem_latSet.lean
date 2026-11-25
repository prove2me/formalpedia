-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LevelProdIdx.neg_mem_latSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:25.783727+00:00
-- url     : https://prove2.me/submissions/d721d41a-711b-4adf-be43-b5745d5021ec

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_ZeroMemLatSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LevelProdIdx
open Formalism.UG
variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ}
variable {R : Type} [CommRing R] [Algebra F R] {O : Subring R} {k : ℕ} {G : Fin k → (Fin n → E)}
namespace PI.UnitaryGroupMassFormula.LevelProdIdx
theorem _root_.solution {y : Fin n → E ⊗[F] R} (hy : y ∈ latSet R O G) :
    -y ∈ latSet R O G := by
  obtain ⟨c, hc, rfl⟩ := hy
  refine ⟨-c, fun i => O.neg_mem (hc i), ?_⟩
  funext l
  simp [TensorProduct.tmul_neg, Finset.sum_neg_distrib]
end PI.UnitaryGroupMassFormula.LevelProdIdx
