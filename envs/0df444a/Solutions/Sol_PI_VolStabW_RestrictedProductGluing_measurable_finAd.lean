-- Prove2me | solution 1 for PI.VolStabW.RestrictedProductGluing.measurable_finAd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:44:15.071691+00:00
-- url     : https://prove2.me/submissions/5e204a7b-2886-4e56-8ec2-5fdf1741610c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue
import Theorems.Thm_PI_VolStabW_RestrictedProductGluing_evalV_mkAf
import Theorems.Thm_PI_VolStabW_RestrictedProductGluing_measurableSet_good
import Theorems.Thm_PI_VolStabW_RestrictedProductGluing_measurableEmbedding_coeA
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_continuous_crd


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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct
open PI.VolStabW.RestrictedProductGluing
open PositiveNearLattice
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {M a d : ℕ} (b : Module.Basis (Fin d) F E)
namespace PI.VolStabW.RestrictedProductGluing
theorem _root_.solution (i : Fin a) (j : Fin M) (k : Fin d) :
    Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) := by
  classical
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine (measurableEmbedding_coeA (F := F)).measurable_comp_iff.1 ?_
  have e : (coeA (F := F)) ∘ (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) =
      (good b).piecewise (fun p v => crd b (Fv F v) (p.2 v i j) k) 0 := by
    funext p
    by_cases hp : p ∈ good b
    · funext v
      rw [Set.piecewise_eq_of_mem _ _ _ hp]
      simp only [Function.comp, coeA]
      rw [finAd, dif_pos hp, evalV_mkAf]
    · funext v
      rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      simp only [Function.comp, coeA, Pi.zero_apply]
      rw [finAd, dif_neg hp, map_zero]
  rw [e]
  refine Measurable.piecewise (measurableSet_good b) ?_ measurable_const
  exact measurable_pi_lambda _ fun v => (continuous_crd b (Fv F v) k).measurable.comp
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply v).comp measurable_snd)))
end PI.VolStabW.RestrictedProductGluing
