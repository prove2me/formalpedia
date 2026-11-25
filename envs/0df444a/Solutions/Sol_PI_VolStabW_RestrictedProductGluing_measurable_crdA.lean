-- Prove2me | solution 1 for PI.VolStabW.RestrictedProductGluing.measurable_crdA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:26.395082+00:00
-- url     : https://prove2.me/submissions/d462fae9-14f1-4799-80fa-6fe537ad203b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue
import Theorems.Thm_PI_VolStabW_RestrictedProductGluing_measurable_finAd
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
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => crdA b p i j k) := by
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hc : Continuous (fun q : Ainf F × Af F => pairA F q.1 q.2) := continuous_id
  have hx : Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) =>
      crd b (Ainf F) (p.1 i j) k) :=
    (continuous_crd b (Ainf F) k).measurable.comp
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))
  exact hc.measurable.comp (hx.prodMk (measurable_finAd b i j k))
end PI.VolStabW.RestrictedProductGluing
