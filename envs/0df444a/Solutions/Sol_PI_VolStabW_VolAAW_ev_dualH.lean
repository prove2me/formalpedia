-- Prove2me | solution 1 for PI.VolStabW.VolAAW.ev_dualH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:48.447162+00:00
-- url     : https://prove2.me/submissions/a1f3d4c1-5f76-4208-84bd-7c1e6fde6895

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolC
import Theorems.Thm_PI_VolStabW_VolAAW_ev_sig
import Theorems.Thm_PI_VolStabW_VolAAW_mem_hermO_iff
import Theorems.Thm_PI_VolStabW_SdDualW_crd_smul
import Theorems.Thm_PI_VolStabW_SdDualW_pairHerm_iota
import Theorems.Thm_PI_VolStabW_VolAAW_ev_dual
import Theorems.Thm_PI_VolStabW_VolAAW_ev_int


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
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.VolAAW
theorem _root_.solution [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) :
    ∀ᶠ v in cofinite, {T : HermR (Fv F v) σ a | ∀ S ∈ hermO b v σ a,
      pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F} = hermO b v σ a := by
  filter_upwards [ev_dual b σ hσ (1 : Matrix (Fin a) (Fin a) E) (by simp) (a := a), ev_sig b σ,
    ev_int (1 / 2 : F)] with v hD hS hh
  ext T
  constructor
  · intro hT
    rw [Set.mem_setOf_eq] at hT
    rw [SetLike.mem_coe, mem_hermO_iff, ← hD]
    intro X hX
    rw [← pairHerm_iota v σ hσ X T]
    apply hT
    intro i j k
    have h1 : X i j ∈ latA v b := fun k => hX i j k
    have h2 : X j i ∈ latA v b := fun k => hX j i k
    exact (add_mem (hS _ h1) h2) k
  · intro hT
    rw [SetLike.mem_coe, mem_hermO_iff, ← hD] at hT
    rw [Set.mem_setOf_eq]
    intro S hS
    set c : Fv F v := algebraMap F (Fv F v) (1 / 2) with hc
    let X : Fin a → Fin a → Fv F v ⊗[F] E := fun p q =>
      c • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p
    have hX : X ∈ latV (M := a) (n := a) b v := by
      intro p q k
      have := crd_smul v b c ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p) k
      simp only [crd] at this
      show (Algebra.TensorProduct.basis (Fv F v) b).repr
        (c • (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) q p) k ∈ _
      rw [this]
      exact mul_mem hh (hS q p k)
    have hcc : c + c = 1 := by
      rw [hc, ← map_add]
      norm_num
    have hSX : S = ⟨iota v σ X, iota_mem v σ hσ X⟩ := by
      apply Subtype.ext
      funext p q
      simp only [iota, X, sigR_smul]
      rw [S.2 p q, ← add_smul, hcc, one_smul]
    rw [hSX, pairHerm_iota v σ hσ X T]
    exact hT X hX
end PI.VolStabW.VolAAW
