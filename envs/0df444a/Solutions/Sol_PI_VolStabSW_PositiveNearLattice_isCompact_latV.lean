-- Prove2me | solution 1 for PI.VolStabSW.PositiveNearLattice.isCompact_latV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:09:40.409563+00:00
-- url     : https://prove2.me/submissions/69c154da-b79c-4a53-8751-bb4490cac0da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_ReciprocityTheory_GeneralLinearIntegers_AlgebraMapIntMemOint
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_eq_sum_crd
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isClopen_latV
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
open PI.VolStabSW.PositiveNearLattice
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.PositiveNearLattice
theorem _root_.solution (a M : ℕ) : IsCompact (latV (M := M) (n := a) b v) := by
  let L : (Fin a → Fin M → Fin d → Fv F v) → (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Fv F v) ⊗ₜ[F] b k)
  have hL : Continuous L := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  let K : Set (Fin a → Fin M → Fin d → Fv F v) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hK : IsCompact K := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v
  refine (hK.image hL).of_isClosed_subset (isClopen_latV b v a M).isClosed ?_
  intro Y hY
  refine ⟨fun x i k => crd b (Fv F v) (Y x i) k, ?_, ?_⟩
  · simp only [K, Set.mem_pi, Set.mem_univ, true_implies]
    intro x i k
    exact hY x i k
  · funext x i
    exact (eq_sum_crd b (Fv F v) (Y x i)).symm
end PI.VolStabSW.PositiveNearLattice
