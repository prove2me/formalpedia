-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.crd_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:48:01.697644+00:00
-- url     : https://prove2.me/submissions/374e7eca-7183-4057-b41f-07fd84ed11f9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_CardStepOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfDeep

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
theorem _root_.solution {M : ℕ} (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (hfg : L0.FG) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ x ∈ crdOf b L0, ∀ i, IsIntegral ℤ (y • x i) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ (Finset.univ : Finset (Fin M))).image (fun p => b.equivFun p.1 p.2))
  refine ⟨y, hy, fun x hx i => ?_⟩
  have hw : (∑ j, x j • b j) ∈ Submodule.span (𝓞 E) (s : Set V) := by rw [hs]; exact hx
  have key : ∀ w ∈ Submodule.span (𝓞 E) (s : Set V), ∀ i, IsIntegral ℤ (y • b.equivFun w i) := by
    intro w hw'
    induction hw' using Submodule.span_induction with
    | mem v hv =>
      intro i
      exact hint _ (Finset.mem_image.mpr ⟨(v, i), Finset.mem_product.mpr ⟨hv, Finset.mem_univ _⟩, rfl⟩)
    | zero => intro i; simp [isIntegral_zero]
    | add v w _ _ hv hw => intro i; rw [map_add, Pi.add_apply, smul_add]; exact (hv i).add (hw i)
    | smul a v _ hv =>
      intro i
      rw [← algebraMap_smul E a v, map_smul, Pi.smul_apply, smul_eq_mul, ← mul_smul_comm]
      exact (RingOfIntegers.isIntegral_coe a).mul (hv i)
  have := key _ hw i
  rwa [show b.equivFun (∑ j, x j • b j) = x by
    rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]] at this
end PI.UnitaryGroupMassFormula.UJClassMass
