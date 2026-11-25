-- Prove2me | solution 1 for PI.VolStabW.SdDualW.dualAt_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:56.121717+00:00
-- url     : https://prove2.me/submissions/082a6a69-9abd-4690-8bb0-995a40a4ecb5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Theorems.Thm_PI_VolStabW_SdDualW_crd_smul
import Theorems.Thm_PI_VolStabW_SdDualW_eT_mem
import Theorems.Thm_PI_VolStabW_SdDualW_BR_expand
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_isCompact_latV
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
open PI PI.VolStabW
open PI.VolStabW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E)
include b
namespace PI.VolStabW.SdDualW
theorem _root_.solution
    (hN : ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, (∀ X, BR (Fv F v) σ J X Y = 0) → Y = 0) :
    DualAt v (BR (Fv F v) σ J (n := a)) := by
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
  refine ⟨latSub v b a M, isCompact_latV b v a M, (isClopen_latV b v a M).isOpen, ?_, ?_⟩
  · intro s hs x hx
    refine ⟨s • x, ?_, fun y => BR_smul_left v σ J s x y⟩
    show ∀ p i l, (Algebra.TensorProduct.basis (Fv F v) b).repr ((s • x) p i) l ∈
      v.adicCompletionIntegers F
    intro p i l
    have := crd_smul v b s (x p i) l
    simp only [crd] at this
    rw [Pi.smul_apply, Pi.smul_apply, this]
    exact mul_mem hs (hx p i l)
  · intro c
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
end PI.VolStabW.SdDualW
