-- Prove2me | solution 1 for PI.VolStabSW.OmFibG.gramFilt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:04:36.438878+00:00
-- url     : https://prove2.me/submissions/d05eea2f-363a-4492-bb72-fb3fa997847f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_FibExGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.OmFibG
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct
namespace PI.VolStabSW.OmFibG
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (v : HeightOneSpectrum (𝓞 F)) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (x : Fin 0 → Fin M → Fv F v ⊗[F] E) :
    FiltConcl σ hσ M J hJ 0 v d b x := by
  haveI hH : Subsingleton (HermR (Fv F v) σ 0) := by
    unfold HermR
    infer_instance
  have hsub : ∀ S : AddSubgroup (Fin 0 → Fin M → Fv F v ⊗[F] E), S = ⊤ := fun S => by
    ext w
    simp only [AddSubgroup.mem_top, iff_true]
    rw [Subsingleton.elim w 0]
    exact S.zero_mem
  have hsubH : ∀ S : AddSubgroup (HermR (Fv F v) σ 0), S = ⊤ := fun S => by
    ext w
    simp only [AddSubgroup.mem_top, iff_true]
    rw [Subsingleton.elim w 0]
    exact S.zero_mem
  refine ⟨Set.univ, Filter.univ_mem, fun y _ Λ0 _ _ => ?_⟩
  refine ⟨fun _ => Λ0, fun _ => ⊤, 0, rfl, fun _ => ?_, fun _ => ?_, antitone_const,
    fun _ => isOpen_univ, fun _ => ?_, fun N' hN' => ⟨0, ?_⟩, fun _ => hsubH _, ?_⟩
  · rw [hsub Λ0]; exact isOpen_univ
  · exact Set.subsingleton_of_subsingleton.isCompact
  · exact Set.subsingleton_of_subsingleton.isCompact
  · intro w _
    rw [Subsingleton.elim w 0]
    exact mem_of_mem_nhds hN'
  · intro n Z _ W _
    rw [hsubH (⊤ : AddSubgroup (HermR (Fv F v) σ 0))]
    exact AddSubgroup.mem_top _
end PI.VolStabSW.OmFibG
