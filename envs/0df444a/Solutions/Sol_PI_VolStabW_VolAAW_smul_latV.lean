-- Prove2me | solution 1 for PI.VolStabW.VolAAW.smul_latV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:02.175857+00:00
-- url     : https://prove2.me/submissions/af3fb063-e6d6-4adc-84ca-0ae056f84c52

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolC
import Theorems.Thm_PI_VolStabW_SdDualW_crd_smul


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
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.VolAAW
theorem _root_.solution (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ latV (M := M) (n := a) b v,
      ∃ x' ∈ latV (M := M) (n := a) b v, ∀ y, BR (Fv F v) σ J x' y = s * BR (Fv F v) σ J x y := by
  intro s hs x hx
  refine ⟨s • x, ?_, fun y => BR_smul_left v σ J s x y⟩
  intro p i l
  have := crd_smul v b s (x p i) l
  simp only [crd] at this
  rw [Pi.smul_apply, Pi.smul_apply, this]
  exact mul_mem hs (hx p i l)
end PI.VolStabW.VolAAW
