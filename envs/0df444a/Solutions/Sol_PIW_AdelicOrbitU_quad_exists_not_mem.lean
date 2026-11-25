-- Prove2me | solution 1 for PIW.AdelicOrbitU.quad_exists_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:22:04.758959+00:00
-- url     : https://prove2.me/submissions/0265ce5c-6688-4827-b1f2-eefbe2f7ddfd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
namespace PIW.AdelicOrbitU
theorem _root_.solution (h2 : Module.finrank F E = 2) :
    ∃ a : E, a ∉ (algebraMap F E).range := by
  by_contra h
  push_neg at h
  have htop : Submodule.span F ({1} : Set E) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, rfl⟩ := RingHom.mem_range.mp (h x)
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  have hle : Module.finrank F (Submodule.span F ({1} : Set E)) = 1 :=
    finrank_span_singleton one_ne_zero
  rw [htop, finrank_top, h2] at hle
  norm_num at hle
end PIW.AdelicOrbitU
