-- Prove2me | solution 1 for PI.LevelKSplit.W.ExC.mem_spanR_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:22.016685+00:00
-- url     : https://prove2.me/submissions/8669be0d-467b-48de-b8e5-e8e7b31abc9b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
import Theorems.Thm_PI_LevelKSplit_W_ExC_projD_add
import Theorems.Thm_PI_LevelKSplit_W_ExC_projD_smul
import Theorems.Thm_PI_LevelKSplit_W_ExC_projD_zero
import Theorems.Thm_PI_LevelKSplit_W_Glob_covR_ratV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.ExC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit PI.LevelKSplit.W.Glob
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace PI.LevelKSplit.W.ExC
theorem _root_.solution {m : ℕ} (Y D : Fin m → Fin n → E)
    (hD : ∀ a a', hE σ J (D a') (Y a) = if a = a' then 1 else 0) (s : Set (Fin m))
    (y : Fin n → R ⊗[F] E) :
    y ∈ spanR (F := F) R Y s ↔ y = projD R σ J Y D s y := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a0, ha0, rfl⟩ := hx
      symm
      unfold projD
      rw [Finset.sum_eq_single a0]
      · rw [if_pos ha0, covR_ratV, hD, if_pos rfl, map_one, one_smul]
      · intro a _ hne
        split_ifs
        · rw [covR_ratV, hD, if_neg (Ne.symm hne), map_zero, zero_smul]
        · exact zero_smul _ _
      · intro h
        exact absurd (Finset.mem_univ _) h
    | zero => rw [projD_zero]
    | add x y _ _ hx hy => rw [projD_add, ← hx, ← hy]
    | smul c x _ hx => rw [projD_smul, ← hx]
  · intro h
    rw [h]
    unfold projD
    refine Submodule.sum_mem _ fun a _ => ?_
    split_ifs with ha
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
    · rw [zero_smul]
      exact Submodule.zero_mem _
end PI.LevelKSplit.W.ExC
