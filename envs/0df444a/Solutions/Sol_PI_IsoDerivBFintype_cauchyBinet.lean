-- Prove2me | solution 1 for PI.IsoDerivBFintype.cauchyBinet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:49:12.967477+00:00
-- url     : https://prove2.me/submissions/f0b83af3-2b79-4062-880d-52512d17c0cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Theorems.Thm_PI_IsoDerivBFintype_exists_oe_perm
import Theorems.Thm_GenFrameSpan_det_mul_rect


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.IsoDerivBFintype
namespace PI.IsoDerivBFintype
theorem _root_.solution {R : Type*} [CommRing R] {h n : ℕ}
    (A : Matrix (Fin h) (Fin n) R) (B : Matrix (Fin n) (Fin h) R) :
    (A * B).det = ∑ I : Fin h ↪o Fin n, (A.submatrix id I).det * (B.submatrix I id).det := by
  classical
  rw [GenFrameSpan.det_mul_rect]
  have hR : ∀ I : Fin h ↪o Fin n, (A.submatrix id I).det * (B.submatrix I id).det
      = ∑ σ : Equiv.Perm (Fin h), (∏ i, B (I (σ i)) i) * (A.submatrix id (fun i => I (σ i))).det := by
    intro I
    rw [det_apply (B.submatrix I id), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have e : A.submatrix id (fun i => I (σ i)) = (A.submatrix id I).submatrix id σ := rfl
    rw [e, det_permute']
    simp only [submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun I _ => hR I, ← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => fun i => p.1 (p.2 i)) (fun _ _ _ => Finset.mem_univ _)
    ?_ ?_ (fun _ _ _ => rfl)
  · rintro ⟨I, σ⟩ _ _ ⟨I', σ'⟩ _ _ e
    have e' : (fun i => I (σ i)) = fun i => I' (σ' i) := e
    have hr : Set.range I = Set.range I' := by
      have h1 : Set.range (fun i => I (σ i)) = Set.range I := σ.surjective.range_comp I
      have h2 : Set.range (fun i => I' (σ' i)) = Set.range I' := σ'.surjective.range_comp I'
      rw [← h1, ← h2, e']
    have hI : I = I' := OrderEmbedding.range_inj.mp hr
    subst hI
    have : σ = σ' := by
      ext i
      have := congrFun e' i
      exact congrArg Fin.val (I.injective this)
    rw [this]
  · intro f _ hne
    have hf : Function.Injective f := by
      intro i j e
      by_contra hij
      apply hne
      rw [Matrix.det_zero_of_column_eq hij (by intro r; simp [e]), mul_zero]
    obtain ⟨I, σ, hIσ⟩ := exists_oe_perm f hf
    exact ⟨(I, σ), Finset.mem_univ _, by simpa [hIσ] using hne, funext hIσ⟩
end PI.IsoDerivBFintype
