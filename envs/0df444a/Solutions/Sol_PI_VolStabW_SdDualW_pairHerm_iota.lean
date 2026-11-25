-- Prove2me | solution 1 for PI.VolStabW.SdDualW.pairHerm_iota
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:06:26.872477+00:00
-- url     : https://prove2.me/submissions/cf702d29-a213-4e38-a75b-3aed9b8d9564

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Theorems.Thm_PI_VolStabW_SdDualW_trace_sigR

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
open PI.VolStabW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E]
namespace PI.VolStabW.SdDualW
theorem _root_.solution (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {a : ℕ}
    (X : Fin a → Fin a → Fv F v ⊗[F] E) (T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a ⟨iota v σ X, iota_mem v σ hσ X⟩ T =
      BR (Fv F v) σ (1 : Matrix (Fin a) (Fin a) E) X
        (fun p i => (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i p) := by
  set Tm := (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) with hTm
  have hT : ∀ p q, Tm q p = sigR (Fv F v) σ (Tm p q) := fun p q => (T.2 q p).symm
  have h2 : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ p, ∑ q, X q p * Tm q p) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ p, ∑ q, sigR (Fv F v) σ (X p q) * Tm q p) := by
    simp only [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hT q p, ← trace_sigR v σ hσ, map_mul, sigR_invol (Fv F v) σ hσ]
  have hBR : BR (Fv F v) σ (1 : Matrix (Fin a) (Fin a) E) X (fun p i => Tm i p) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (∑ p, ∑ q, sigR (Fv F v) σ (X p q) * Tm q p) := by
    simp only [BR, hR, Formalism.UG.hform, JR, Matrix.map_apply, Matrix.one_apply, apply_ite,
      map_one, map_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, map_sum]
  rw [hBR]
  simp only [pairHerm, iota, add_mul, Finset.sum_add_distrib, map_add]
  simp only [← hTm]
  rw [h2]
  have h12 : algebraMap F (Fv F v) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul]
    norm_num
  linear_combination (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
    (∑ p, ∑ q, sigR (Fv F v) σ (X p q) * Tm q p)) * h12
end PI.VolStabW.SdDualW
