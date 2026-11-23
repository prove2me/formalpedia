-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.crd_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:43.428539+00:00
-- url     : https://prove2.me/submissions/67a2e64b-d348-4280-9f8d-9d26f0544e94

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_int_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V)
    (hspan : Submodule.span E (L0 : Set V) = ⊤) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ i, y • b i ∈ L0 := by
  classical
  have hmem : ∀ i, b i ∈ Submodule.span E (L0 : Set V) := fun i => by rw [hspan]; exact Submodule.mem_top
  choose n f g hfg using fun i => (Submodule.mem_span_set' (R := E)).mp (hmem i)
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.biUnion (fun i => Finset.univ.image (f i)))
  refine ⟨y, hy, fun i => ?_⟩
  rw [← hfg i, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun k _ => ?_)
  have hk : IsIntegral ℤ (y • f i k) := hint _ (Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩)
  rw [← smul_assoc]
  exact int_smul_mem L0 hk (g i k).2
end PI.UnitaryGroupMassFormula.UJClassMass
