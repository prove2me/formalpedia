-- Prove2me | solution 1 for PI.VolStabSW.densVLat_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:41.602329+00:00
-- url     : https://prove2.me/submissions/7f064f55-3cd5-49a7-922c-05501b518758

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVNA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGlue
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVCore
import Theorems.Thm_PI_VolStabSW_densCos_of_filt
import Theorems.Thm_PI_VolStabSW_sigma_invol


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
  Topology
open scoped TensorProduct
namespace PI.VolStabSW
theorem _root_.solution (hP1 : HenselCount) (hP2 : CosDens) (hT : TensAll) (hF : GramFilt) :
    DensVLat := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨_t1, t2, t3, _t4, t5, _t6, _t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  intro d b x hx
  obtain ⟨N, hN, hd⟩ := hF F E σ hσ M J hJ.1 hJ.2 a h1 h2 v d b x hx
  refine ⟨N, hN, fun y hy Λ0 hB _ _ hsub => ?_⟩
  obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ := hd y hy Λ0 hB hsub
  subst h0
  exact densCos_of_filt hP1 hP2 μv νv (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ hσ J hJ.1) (Continuous.subtype_mk t5 _) (fun _ => rfl) y Λ H hΛo hΛc hΛa
    hHo hHc hHb D hD hyp
end PI.VolStabSW
