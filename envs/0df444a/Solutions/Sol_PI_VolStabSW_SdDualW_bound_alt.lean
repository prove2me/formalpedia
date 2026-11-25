-- Prove2me | solution 1 for PI.VolStabSW.SdDualW.bound_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:24.370437+00:00
-- url     : https://prove2.me/submissions/ae47385b-85a3-4b91-a4a3-b63a49499ba7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Theorems.Thm_PI_VolStabSW_SdDualW_eT_mem
import Theorems.Thm_PI_VolStabSW_SdDualW_BR_expand
import Theorems.Thm_ReciprocityTheory_GeneralLinearIntegers_GeneralLinearIntegersOpenCompact_isCompact_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
include b
namespace PI.VolStabSW.SdDualW
theorem _root_.solution
    (hN : ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, (∀ X, BR (Fv F v) σ J X Y = 0) → Y = 0)
    (c : Fv F v) : ∃ K, IsCompact K ∧
      {y | ∀ x ∈ latSub v b a M, BR (Fv F v) σ J x y ∈
        (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))} ⊆ K := by
  classical
  have hker : LinearMap.ker (phiL (a := a) v b σ J) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro Y hY
    apply hN Y
    intro X
    rw [BR_expand v b σ J X Y]
    refine Finset.sum_eq_zero fun q _ => ?_
    have : BR (Fv F v) σ J (eT v b q) Y = 0 := congrFun hY q
    rw [this, mul_zero]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (phiL (a := a) v b σ J) hker
  have hgc : Continuous g := IsModuleTopology.continuous_of_linearMap g
  let box : Set (Fin a × Fin M × Fin d → Fv F v) :=
    Set.pi Set.univ fun _ => (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))
  have hbox : IsCompact box := isCompact_univ_pi fun _ =>
    (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image (continuous_const.mul continuous_id)
  refine ⟨g '' box, hbox.image hgc, ?_⟩
  intro y hy
  refine ⟨phiL (a := a) v b σ J y, ?_, ?_⟩
  · intro q _
    exact hy _ (eT_mem v b q)
  · exact LinearMap.congr_fun hg y
end PI.VolStabSW.SdDualW
