-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.cofin1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:22.456398+00:00
-- url     : https://prove2.me/submissions/0ee6c77c-f18a-4ee6-9f4c-353ca2dc8cf1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjSk
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PSurjH
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crd_lower
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_crd_upper
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_int_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (L N : Submodule (𝓞 E) V)
    (hL : L.FG) (hN : Submodule.span E (N : Set V) = ⊤) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ v ∈ L, (y : 𝓞 E) • v ∈ N := by
  classical
  let b := Module.finBasis E V
  obtain ⟨y1, hy1, h1⟩ := crd_upper b L hL
  obtain ⟨y2, hy2, h2⟩ := crd_lower b N hN
  refine ⟨y1 * y2, mul_ne_zero hy1 hy2, fun v hv => ?_⟩
  have hx : b.equivFun v ∈ crdOf b L := by
    show ∑ i, b.equivFun v i • b i ∈ L
    rw [b.sum_equivFun]
    exact hv
  have e : ((y1 * y2 : ℤ) : 𝓞 E) • v = ∑ i, (y1 • b.equivFun v i) • (y2 • b i) := by
    conv_lhs => rw [← b.sum_equivFun v]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← algebraMap_smul E ((y1 * y2 : ℤ) : 𝓞 E), map_intCast, zsmul_eq_mul,
      ← Int.cast_smul_eq_zsmul E y2 (b i), smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [e]
  exact Submodule.sum_mem _ (fun i _ => int_smul_mem N (h1 _ hx i) (h2 i))
end PI.UnitaryGroupMassFormula.UJClassMass
