-- Prove2me | solution 1 for PI.VolStabW.FiniteThetaCoordinates.exists_bound_crd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:56:56.184188+00:00
-- url     : https://prove2.me/submissions/6d71b182-4aac-4f7b-bc4f-dcfd90cac258

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_FinTheta

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
theorem _root_.solution {R K : Type} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [NormedField K] (φ : R →+* K) (hφ : Continuous φ) {a M : ℕ}
    {S : Set (Fin a → Fin M → R ⊗[F] E)} (hS : IsCompact S) :
    ∃ B, 0 ≤ B ∧ ∀ Y ∈ S, ∀ i j k, ‖φ (crd b R (Y i j) k)‖ ≤ B := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hc : ∀ i j k, Continuous fun Y : (Fin a → Fin M → R ⊗[F] E) => ‖φ (crd b R (Y i j) k)‖ := by
    intro i j k
    have hl : Continuous fun y : R ⊗[F] E => crd b R y k :=
      IsModuleTopology.continuous_of_linearMap
        ((Finsupp.lapply k).comp (Algebra.TensorProduct.basis R b).repr.toLinearMap)
    exact continuous_norm.comp (hφ.comp (hl.comp ((continuous_apply j).comp (continuous_apply i))))
  have hf : Continuous fun Y : (Fin a → Fin M → R ⊗[F] E) =>
      ∑ i, ∑ j, ∑ k, ‖φ (crd b R (Y i j) k)‖ :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun k _ => hc i j k
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun Y hY i j k => ?_⟩
  have h1 : ‖φ (crd b R (Y i j) k)‖ ≤ ∑ i, ∑ j, ∑ k, ‖φ (crd b R (Y i j) k)‖ := by
    calc ‖φ (crd b R (Y i j) k)‖ ≤ ∑ k, ‖φ (crd b R (Y i j) k)‖ :=
          Finset.single_le_sum (f := fun k => ‖φ (crd b R (Y i j) k)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
      _ ≤ ∑ j, ∑ k, ‖φ (crd b R (Y i j) k)‖ :=
          Finset.single_le_sum (f := fun j => ∑ k, ‖φ (crd b R (Y i j) k)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      _ ≤ _ :=
          Finset.single_le_sum (f := fun i => ∑ j, ∑ k, ‖φ (crd b R (Y i j) k)‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ i)
  have h2 := hC Y hY
  rw [Real.norm_eq_abs] at h2
  exact h1.trans ((le_abs_self _).trans (h2.trans (le_max_left _ _)))
end PI.VolStabW.FiniteThetaCoordinates
