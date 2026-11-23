-- Prove2me | solution 1 for PI.IsoInvMetricW.metric_constant_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:30.955798+00:00
-- url     : https://prove2.me/submissions/6cf4b3ae-85c5-4965-ab39-c8829e070701

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_MetricConstantBound
import Theorems.Thm_GenFrameSpan_det_mul_rect


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PI PI.IsoInvMetricW
namespace PI.IsoInvMetricW
theorem _root_.solution : CB := by
  intro h N A B
  classical
  rw [GenFrameSpan.det_mul_rect]
  have hR : ∀ J : Fin h ↪o Fin N, (A.submatrix id J).det * (B.submatrix J id).det
      = ∑ σ : Equiv.Perm (Fin h), (∏ i, B (J (σ i)) i) * (A.submatrix id (J ∘ σ)).det := by
    intro J
    rw [det_apply (B.submatrix J id), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hA : A.submatrix id (J ∘ σ) = (A.submatrix id J).submatrix id σ := by
      ext i k; simp
    rw [hA, det_permute']
    simp only [Units.smul_def, zsmul_eq_mul, submatrix_apply, id]
    ring
  rw [Finset.sum_congr rfl (fun J _ => hR J), ← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (p.1 : Fin h → Fin N) ∘ p.2)
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ _ => rfl)
  · rintro ⟨J, σ⟩ _ _ ⟨J', σ'⟩ _ _ heq
    have hr : Set.range J = Set.range J' := by
      have h1 : Set.range ((J : Fin h → Fin N) ∘ σ) = Set.range J :=
        σ.surjective.range_comp _
      have h2 : Set.range ((J' : Fin h → Fin N) ∘ σ') = Set.range J' :=
        σ'.surjective.range_comp _
      rw [← h1, ← h2]
      exact congrArg Set.range heq
    have hJ : J = J' := OrderEmbedding.range_inj.mp hr
    subst hJ
    have hσ : σ = σ' := by
      ext i
      have := congrFun heq i
      simp only [Function.comp_apply] at this
      rw [J.injective this]
    rw [hσ]
  · intro f _ hf
    have hinj : Function.Injective f := by
      by_contra hni
      apply hf
      have : ∃ i j, f i = f j ∧ i ≠ j := by
        by_contra hc
        push Not at hc
        exact hni fun i j e => hc i j e
      obtain ⟨i, j, hij, hne⟩ := this
      rw [Matrix.det_zero_of_column_eq hne (by intro r; simp [hij]), mul_zero]
    set s : Finset (Fin N) := Finset.univ.image f with hs
    have hcard : s.card = h := by
      rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ i, f i ∈ s := fun i => Finset.mem_image_of_mem f (Finset.mem_univ i)
    let g : Fin h → Fin h := fun i => (s.orderIsoOfFin hcard).symm ⟨f i, hmem i⟩
    have hg : ∀ i, s.orderEmbOfFin hcard (g i) = f i := by
      intro i
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp [g]
    have ginj : Function.Injective g := by
      intro i j e
      apply hinj
      rw [← hg i, ← hg j, e]
    let σ : Equiv.Perm (Fin h) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj)
    refine ⟨(s.orderEmbOfFin hcard, σ), Finset.mem_univ _, ?_, ?_⟩
    · have hfi : ∀ i, (s.orderEmbOfFin hcard) (σ i) = f i := fun i => by simp [σ, hg]
      have : ((s.orderEmbOfFin hcard : Fin h ↪o Fin N) : Fin h → Fin N) ∘ σ = f := by
        funext i; exact hfi i
      rw [this]; dsimp only; simp only [hfi]; exact hf
    · funext i; simp [σ, hg]
end PI.IsoInvMetricW
