-- Prove2me | solution 1 for PI.VolStabSW.SdDualW.dualAt_H
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:39:59.320726+00:00
-- url     : https://prove2.me/submissions/d7cf745a-f3b0-43e0-8c5f-7ccfcb698a92

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Theorems.Thm_PI_VolStabSW_SdDualW_bound_alt
import Theorems.Thm_PI_VolStabSW_SdDualW_nondeg_BR
import Theorems.Thm_PI_VolStabSW_SdDualW_mem_latS
import Theorems.Thm_PI_VolStabSW_SdDualW_isCompact_latS
import Theorems.Thm_PI_VolStabSW_SdDualW_isOpen_latS
import Theorems.Thm_PI_VolStabSW_SdDualW_smul_mem_latS
import Theorems.Thm_PI_VolStabSW_SdDualW_latH_eq
import Theorems.Thm_PI_VolStabSW_SdDualW_pairHerm_iota
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv


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
open PI.VolStabSW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E]
include b
namespace PI.VolStabSW.SdDualW
theorem _root_.solution [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) :
    DualAt v (pairHerm (Fv F v) σ a) := by
  classical
  have := locallyCompact_Fv F v
  have hcl := (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal
  have hKc : IsCompact ((Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (latS v b σ : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_latS v b σ
  have hKo : IsOpen ((Set.univ.pi fun _ => Set.univ.pi fun _ =>
      (latS v b σ : Set (Fv F v ⊗[F] E))) : Set (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_latS v b σ
  refine ⟨latH v b σ a, ?_, ?_, ?_, ?_⟩
  · rw [latH_eq]
    exact hcl.isCompact_preimage hKc
  · rw [latH_eq]
    exact hKo.preimage continuous_subtype_val
  · intro s hs S hS
    have hmem : s • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ HermR (Fv F v) σ a := by
      intro p q
      simp only [Matrix.smul_apply, sigR_smul, S.2 p q]
    refine ⟨⟨_, hmem⟩, fun p q => smul_mem_latS v b σ hs (hS p q), fun T => ?_⟩
    simp only [pairHerm, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul,
      smul_eq_mul]
    ring
  · intro c
    have hN : ∀ Y : Fin a → Fin a → Fv F v ⊗[F] E,
        (∀ X, BR (Fv F v) σ (1 : Matrix (Fin a) (Fin a) E) X Y = 0) → Y = 0 :=
      fun Y hY => nondeg_BR v σ hσ 1 (by simp) Y hY
    obtain ⟨K, hK, hKs⟩ := bound_alt v b σ (1 : Matrix (Fin a) (Fin a) E) (a := a) hN c
    let tr : (Fin a → Fin a → Fv F v ⊗[F] E) → Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
      fun Y i p => Y p i
    have htr : Continuous tr := continuous_pi fun i => continuous_pi fun p =>
      (continuous_apply i).comp (continuous_apply p)
    refine ⟨Subtype.val ⁻¹' (tr '' K), hcl.isCompact_preimage (hK.image htr), ?_⟩
    intro T hT
    refine ⟨fun p i => (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i p, ?_, rfl⟩
    apply hKs
    intro X hX
    have hS : (⟨iota v σ X, iota_mem v σ hσ X⟩ : HermR (Fv F v) σ a) ∈ latH v b σ a := by
      intro p q
      have h1 : X p q ∈ latA v b := fun k => hX p q k
      have h2 : X q p ∈ latA v b := fun k => hX q p k
      rw [mem_latS]
      exact ⟨X q p, h2, X p q, h1, add_comm _ _⟩
    have := hT _ hS
    rwa [pairHerm_iota v σ hσ] at this
end PI.VolStabSW.SdDualW
