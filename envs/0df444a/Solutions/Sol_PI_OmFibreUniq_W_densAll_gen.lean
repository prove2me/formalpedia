-- Prove2me | solution 1 for PI.OmFibreUniq.W.densAll_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:19:15.112482+00:00
-- url     : https://prove2.me/submissions/315d252a-ac10-493d-9407-4737fbd84c48

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_FibExGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FreeOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_GramMapFibreExistence
import Theorems.Thm_PI_VolStabSW_OmFibG_gramFilt_all
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isCompact_latV
import Theorems.Thm_PI_VolStabSW_TensAllW_isOpen_linIndep
import Theorems.Thm_PI_VolStabSW_TensAllW_lip_field
import Theorems.Thm_PI_VolStabSW_cosDens_holds
import Theorems.Thm_PI_VolStabSW_densAll_iff
import Theorems.Thm_PI_VolStabSW_densApprox_lc
import Theorems.Thm_PI_VolStabSW_densCos_of_filt
import Theorems.Thm_PI_VolStabSW_densLC_of_cosB
import Theorems.Thm_PI_VolStabSW_exists_pow_tendsto_zero_Fv
import Theorems.Thm_PI_VolStabSW_hasCOSub_of_lat
import Theorems.Thm_PI_VolStabSW_henselCount_holds
import Theorems.Thm_PI_VolStabSW_isCOBasis_latSub
import Theorems.Thm_PI_VolStabSW_isOpen_units_Fv
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv
import Theorems.Thm_PI_VolStabSW_tensFacts_of_fib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology
open PI.OmFibreUniq PI.VolStabSW PI.VolStabSW.TensAllW PI.VolStabSW.OmFibG
open scoped TensorProduct
namespace PI.OmFibreUniq.W
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (v : HeightOneSpectrum (𝓞 F)) (a : ℕ)
    (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a))
    (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure) :
    DensAll μ (gramR (Fv F v) σ J) Subtype.val ν
      {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  have hfree := isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv F v) (lip_field _)
    (a := a) (M := n)
  obtain ⟨t1, t2, t3, t4, t5, _t6, t7⟩ := tensFacts_of_fib σ n J a (Fv F v) hσ hJ hfree
  have := hμ
  have := hν
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have hNA : HasCOSub (Fin a → Fin n → Fv F v ⊗[F] E) := by
    obtain ⟨π, h0, hπ⟩ := exists_pow_tendsto_zero_Fv v
    exact hasCOSub_of_lat (latSub (Module.finBasis F E) v a n)
      (PositiveNearLattice.isClopen_latV (Module.finBasis F E) v a n).isOpen
      (PositiveNearLattice.isCompact_latV (Module.finBasis F E) v a n) π h0 hπ
  have hC : DensCosB (scaledB (Fv F v) (latSub (Module.finBasis F E) v a n)) μ
      (gramR (Fv F v) σ J) Subtype.val ν
      {X : Fin a → Fin n → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
    intro x hx
    obtain ⟨N, hN, hd⟩ := gramFilt_all σ hσ n J hJ hdet a v _ (Module.finBasis F E) x hx
    refine ⟨N, hN, fun y hy Λ0 hB _ _ hsub => ?_⟩
    obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ := hd y hy Λ0 hB hsub
    subst h0
    exact densCos_of_filt henselCount_holds cosDens_holds μ ν (gramR (Fv F v) σ J) Subtype.val
      Subtype.val_injective (gramH (Fv F v) σ hσ J hJ) (Continuous.subtype_mk t5 _)
      (fun _ => rfl) y Λ H hΛo hΛc hΛa hHo hHc hHb D hD hyp
  have hLC := densLC_of_cosB _ _ (isCOBasis_latSub (Module.finBasis F E) v a n) hC
  exact (densAll_iff _ _ _ _ _).2 (densApprox_lc μ _ _ ν _ t7 hNA hLC)
end PI.OmFibreUniq.W
