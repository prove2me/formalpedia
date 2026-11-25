-- Prove2me | solution 1 for P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__fibS_integrable_continuousOn_1406fa94d4b3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:09:47.102577+00:00
-- url     : https://prove2.me/submissions/9f74cd7a-4fcd-4c39-8b27-71834598d045

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductScalingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductUniquenessStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductIntegralStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductRecursion
import Theorems.Thm_GlobalTheory_T_continuousOn_preal_units_of_hasCompactSupport
import Theorems.Thm_GlobalTheory_T_continuousOn_schur_coordinates_and_isOpen_Bset
import Theorems.Thm_GlobalTheory_T_gram_fiber_cons_integrable_and_integral_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibS σ J t m₁ m' s B₀ a κ₁ cm S)) ∧ ContinuousOn (fun S => ∫ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S)) (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc
  have h1 := GlobalTheory.T.gram_fiber_cons_integrable_and_integral_eq F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc
  have h2 := GlobalTheory.T.continuousOn_preal_units_of_hasCompactSupport F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc
  obtain ⟨-, ha, hc, hsch, -⟩ := GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  refine ⟨fun S hS => (h1 S hS).1, ?_⟩
  have hsub : (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ⊆
      {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} := fun S hS => hS.1
  have ha' := ha.mono hsub
  have hval := Units.continuous_val.comp_continuousOn ha'
  have hmap := hval.prodMk ((hc.mono hsub).prodMk (hsch.mono hsub))
  have hP := h2.comp hmap (fun S hS => ⟨(a _).isUnit, Set.mem_univ _, hS.2⟩)
  have hk := NNReal.continuous_coe.comp_continuousOn
    ((D.hκc.comp_continuousOn ha').mul ((D.hcmc.comp_continuousOn ha').pow n))
  exact (hk.mul hP).congr (fun S hS => (h1 S hS).2)
end GlobalTheory.CompanionTheory.SW.PiLocalization₂
