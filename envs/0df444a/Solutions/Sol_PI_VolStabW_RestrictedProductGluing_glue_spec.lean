-- Prove2me | solution 1 for PI.VolStabW.RestrictedProductGluing.glue_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:16:35.422301+00:00
-- url     : https://prove2.me/submissions/29f64bee-e492-4240-8be1-cf84c138fd25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue
import Theorems.Thm_PI_VolStabW_RestrictedProductGluing_evalV_mkAf
import Theorems.Thm_PI_VolStabW_RestrictedProductGluing_crd_glue
import Theorems.Thm_PI_VolStabW_PositiveNearLattice_crd_map


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
theorem _root_.solution (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (hp : p ∈ good b) :
    projInf (glue b p) = p.1 ∧ ∀ v, projV v (projFin (glue b p)) = p.2 v := by
  refine ⟨?_, fun v => ?_⟩
  · funext i j
    refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
    show crd b (Ainf F) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (glue b p i j)) k =
      crd b (Ainf F) (p.1 i j) k
    rw [crd_map, crd_glue]
    rfl
  · funext i j
    refine (Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_
    show crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (glue b p i j))) k =
      crd b (Fv F v) (p.2 v i j) k
    rw [crd_map, crd_map, crd_glue]
    show evalV F v (finAd b p i j k) = _
    rw [finAd, dif_pos hp, evalV_mkAf]
end PI.VolStabW.RestrictedProductGluing
