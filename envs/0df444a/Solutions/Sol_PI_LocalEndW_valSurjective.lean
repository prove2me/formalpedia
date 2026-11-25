-- Prove2me | solution 1 for PI.LocalEndW.valSurjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:03:46.944102+00:00
-- url     : https://prove2.me/submissions/ed55cacf-a26d-4d96-b627-84944256eafc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_IsUniformInducingOfVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalEndomorphisms_AlgebraMapMemRange
import Theorems.Thm_PI_LocalEndW_algebraMap_mem_range
import Theorems.Thm_PI_LocalEndW_isUniformInducing_of_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain Polynomial
namespace PI.LocalEndW
private theorem denseRange_algebraMap_adicCompletion_lemma_2 {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : DenseRange (algebraMap F (v.adicCompletion F)) := by
  exact HeightOneSpectrum.denseRange_algebraMap F v
end PI.LocalEndW
end

set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open PI PI.LocalEndW
namespace PI.LocalEndW
theorem _root_.solution : ValSurjective := by
  intro F _ _ v τ hτ y
  have hclosed : IsClosed (Set.range τ) :=
    (isUniformInducing_of_val τ hτ).isComplete_range.isClosed
  have hdense : Dense (Set.range τ) :=
    (denseRange_algebraMap_adicCompletion_lemma_2 v).mono (by
      rintro _ ⟨a, rfl⟩
      exact algebraMap_mem_range τ a)
  have huniv := hdense.closure_eq
  rw [hclosed.closure_eq] at huniv
  have hy : y ∈ Set.range τ := huniv ▸ Set.mem_univ y
  exact hy
end PI.LocalEndW
