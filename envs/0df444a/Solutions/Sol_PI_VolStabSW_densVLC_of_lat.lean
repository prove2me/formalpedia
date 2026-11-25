-- Prove2me | solution 1 for PI.VolStabSW.densVLC_of_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:35.244152+00:00
-- url     : https://prove2.me/submissions/5eb51a4f-259b-4f4d-938a-2b48439fa1a3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVNA
import Theorems.Thm_PI_VolStabSW_isCOBasis_latSub
import Theorems.Thm_PI_VolStabSW_densLC_of_cosB


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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (hT : TensAll) (hC : DensVLat) : DensVLC := by
  unfold DensVLC InCtx
  unfold DensVLat InCtx at hC
  unfold TensAll InCtx at hT
  intro F E _ _ _ _ _ σ hcm M J hJ hs1 hs2 a ha1 ha2 X0 hT' hdet ψ hψ v μv hμ νv hν
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨-, htf⟩ := hT F E σ hcm M J hJ hs1 hs2 a ha1 ha2 X0 hT' hdet
  obtain ⟨h1, h2, h3, -⟩ := htf v
  haveI : OpensMeasurableSpace (Fv F v ⊗[F] E) := by
    first
      | infer_instance
      | exact ⟨le_rfl⟩
  haveI : OpensMeasurableSpace (Fin a → Fin M → Fv F v ⊗[F] E) := by
    first
      | infer_instance
      | exact ⟨le_rfl⟩
  haveI : OpensMeasurableSpace ↥(HermR (Fv F v) σ a) := by
    first
      | infer_instance
      | exact ⟨le_rfl⟩
  haveI : IsFiniteMeasureOnCompacts μv := by
    first
      | infer_instance
      | (haveI := hμ.1; infer_instance)
      | (haveI := hμ.2.1; infer_instance)
      | (haveI := hμ.1.1; infer_instance)
      | (haveI := hμ.2; infer_instance)
  haveI : IsFiniteMeasureOnCompacts νv := by
    first
      | infer_instance
      | (haveI := hν.1; infer_instance)
      | (haveI := hν.2.1; infer_instance)
      | (haveI := hν.1.1; infer_instance)
      | (haveI := hν.2; infer_instance)
  have h := hC F E σ hcm M J hJ hs1 hs2 a ha1 ha2 X0 hT' hdet ψ hψ v μv hμ νv hν _
    (Module.finBasis F E)
  exact densLC_of_cosB _ _ (isCOBasis_latSub (Module.finBasis F E) v a M) h
end PI.VolStabSW
