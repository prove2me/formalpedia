-- Prove2me | solution 1 for PI.VolStabW.FiniteThetaCoordinates.norm_crd_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:49:38.118883+00:00
-- url     : https://prove2.me/submissions/080f4a1f-4a1b-4848-9afe-f431f5bc25c6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta
import Theorems.Thm_PI_VolStabW_FiniteThetaCoordinates_crd_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
namespace PI.VolStabW.FiniteThetaCoordinates
theorem _root_.solution {R K : Type} [CommRing R] [Algebra F R] [NormedField K] (φ : R →+* K)
    {M : ℕ} (m : Matrix (Fin M) (Fin M) (R ⊗[F] E)) (y : Fin M → R ⊗[F] E) {A B C : ℝ}
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ i j p, ‖φ (crd b R (m i j) p)‖ ≤ A) (hB : ∀ j q, ‖φ (crd b R (y j) q)‖ ≤ B)
    (hC : ∀ p q k, ‖φ (algebraMap F R (b.repr (b p * b q) k))‖ ≤ C) (i : Fin M) (k : Fin d) :
    ‖φ (crd b R ((m.mulVec y) i) k)‖ ≤ M * (d * (d * (A * B * C))) := by
  rw [crd_mulVec]
  simp only [map_sum, map_mul]
  have hterm : ∀ j p q, ‖φ (crd b R (m i j) p) * φ (crd b R (y j) q) *
      φ (algebraMap F R (b.repr (b p * b q) k))‖ ≤ A * B * C := by
    intro j p q
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hA i j p) (hB j q) (norm_nonneg _) hA0) (hC p q k) (norm_nonneg _)
      (mul_nonneg hA0 hB0)
  have h3 : ∀ j p, ‖∑ q, φ (crd b R (m i j) p) * φ (crd b R (y j) q) *
      φ (algebraMap F R (b.repr (b p * b q) k))‖ ≤ d * (A * B * C) := fun j p =>
    (norm_sum_le_of_le _ fun q _ => hterm j p q).trans (by simp)
  have h2 : ∀ j, ‖∑ p, ∑ q, φ (crd b R (m i j) p) * φ (crd b R (y j) q) *
      φ (algebraMap F R (b.repr (b p * b q) k))‖ ≤ d * (d * (A * B * C)) := fun j =>
    (norm_sum_le_of_le _ fun p _ => h3 j p).trans (by simp)
  exact (norm_sum_le_of_le _ fun j _ => h2 j).trans (by simp)
end PI.VolStabW.FiniteThetaCoordinates
