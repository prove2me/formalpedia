-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeSheetParam_proof_f2fd37214912
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:29.529144+00:00
-- url     : https://prove2.me/submissions/0a66ad2f-2e08-447d-94bd-aaec6f5b447f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetParam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSheetCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_pblk_apply_242008ed2609
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_pblk_injective_89845f6e18bb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_segre_pblk_smul_500f4e0514cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_complexFibreIdeal_of_forall_e9fcbb433878
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_forall_eval_of_complexFibreIdeal_f6b70a4a7738
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre mcPts
  IsMultiHomogIdeal mcPts_smul)
namespace GroundTheory.Heights₂.Heights
namespace ConeSheetParam
theorem _root_.solution (hCov : ConeSheetCover.Statement)
    (hHyp : ConeProjHyperplaneNull.Statement) : ConeSheetParam.Statement := by
  classical
  intro n e S hS P Ψ hP hΨ
  obtain ⟨U, D, N, s, hUD, hdisj, hnull, hfib, hrest⟩ := hCov n e P Ψ hP hΨ
  have hhyp := hHyp n e P Ψ hP hΨ
  have hMH : IsMultiHomogIdeal P := hP.2.1.2.1
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS

  have hval : ∀ k j x, x ∈ U k → Ψ (segre (s k j x)) = Fin.cons 1 x ∧ s k j x ∈ mcPts P := by
    intro k j x hx
    have h2 := (((hfib k x hx).2.2 j).1).2.self_of_nhds
    exact ⟨h2.2.2, h2.2.1⟩

  have hpt : ∀ (t : ℂ) (v : Fin n → ℂ),
      (ObjectsHeight.ofPointMatrix S hS).pointOf (t • WithLp.toLp 2 (S *ᵥ v)) = t • v := by
    intro t v
    simp only [HermNorm.pointOf, ObjectsHeight.ofPointMatrix, transpose_transpose]
    change S⁻¹ *ᵥ (t • (S *ᵥ v)) = t • v
    rw [mulVec_smul, mulVec_mulVec, nonsing_inv_mul S hdet, one_mulVec]
  refine ⟨U, D, N, s, hUD, hdisj, hnull, hfib, ?_, ?_, ?_⟩
  ·
    rintro ⟨⟨k, j⟩, x, t⟩ ⟨hx, ht⟩ ⟨⟨k', j'⟩, x', t'⟩ ⟨hx', ht'⟩ heq
    simp only at hx ht hx' ht' heq
    have hv := congrArg (ObjectsHeight.ofPointMatrix S hS).pointOf heq
    rw [hpt, hpt] at hv
    have hz : (fun p : Σ k, PBlk n k => t * s k j x p) = fun p => t' * s k' j' x' p := by
      funext p
      obtain ⟨⟨⟩, i⟩ := p
      exact congrFun hv i
    have hΨz := congrArg (fun z => Ψ (segre z)) hz
    simp only [segre_pblk_smul, map_smul, (hval k j x ((hUD k).2.2.1 hx)).1,
      (hval k' j' x' ((hUD k').2.2.1 hx')).1] at hΨz
    have htt : t = t' := by simpa using congrFun hΨz 0
    subst htt
    have hxx : x = x' := by
      funext i
      have := congrFun hΨz i.succ
      simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul] at this
      exact mul_left_cancel₀ ht this
    subst hxx
    have hss : s k j x = s k' j' x := by
      funext p
      exact mul_left_cancel₀ ht (congrFun hz p)
    have hkk : k = k' := by
      by_contra hk
      exact Set.disjoint_left.1 (hdisj hk) hx hx'
    subst hkk
    have hjj : j = j' := (hfib k x ((hUD k).2.2.1 hx)).2.1 (congrArg segre hss)
    subst hjj
    rfl
  ·
    rintro y ⟨⟨⟨k, j⟩, x, t⟩, ⟨hx, ht⟩, rfl⟩
    simp only at hx ht
    intro q hq
    rw [hpt]
    have hm : (fun p : Σ k, PBlk n k => t * s k j x p) ∈ mcPts P :=
      mcPts_smul hMH (fun _ => t) (fun _ => ht) (hval k j x ((hUD k).2.2.1 hx)).2
    exact eval_complexFibreIdeal_of_forall hm.2 q hq
  ·
    set F := fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
      q.2.2 • WithLp.toLp 2 (S *ᵥ fun i => s q.1.1 q.1.2 q.2.1 ⟨(), i⟩) with hF
    let Lₗ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
      { toFun := fun z => WithLp.toLp 2 (S *ᵥ fun i => z i)
        map_add' := by
          intro a b
          change WithLp.toLp 2 (S *ᵥ (fun i => a i + b i)) = _
          rw [show (fun i => a i + b i) = (fun i => a i) + fun i => b i from rfl, mulVec_add]
          rfl
        map_smul' := by
          intro c a
          change WithLp.toLp 2 (S *ᵥ (c • fun i => a i)) = _
          rw [mulVec_smul]
          rfl }
    let L := LinearMap.toContinuousLinearMap Lₗ
    set A1 := {z : EuclideanSpace ℂ (Fin n) |
      (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧
        Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 = 0} with hA1
    set A2 := {z : EuclideanSpace ℂ (Fin n) |
      (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧
        Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 ≠ 0 ∧
        (Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0)⁻¹ •
            Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) ∉ ⋃ k, D k} with hA2
    have hsub : coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) \ F ''
        {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆ L '' (A1 ∪ A2) := by
      rintro y ⟨hyC, hyF⟩
      set z : Fin n → ℂ := S⁻¹ *ᵥ fun i => y i with hz
      have hyz : y = L (WithLp.toLp 2 z) := by
        change y = WithLp.toLp 2 (S *ᵥ (S⁻¹ *ᵥ fun i => y i))
        rw [mulVec_mulVec, mul_nonsing_inv S hdet, one_mulVec]
      have hzC : ∀ q ∈ complexFibreIdeal P, eval z q = 0 := by
        intro q hq
        have := hyC q hq
        simpa [HermNorm.pointOf, ObjectsHeight.ofPointMatrix, transpose_transpose] using this
      refine ⟨WithLp.toLp 2 z, ?_, hyz.symm⟩
      by_cases h0 : Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 = 0
      · exact Or.inl ⟨hzC, h0⟩
      by_cases hxD : (Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0)⁻¹ •
          Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) ∈ ⋃ k, D k
      swap
      · exact Or.inr ⟨hzC, h0, hxD⟩
      exfalso
      apply hyF

      have hzm : (fun p : Σ k, PBlk n k => z p.2) ∈ mcPts P := by
        refine ⟨fun _ => ?_, forall_eval_of_complexFibreIdeal hzC⟩
        by_contra hne
        push Not at hne
        apply h0
        have : (fun p : Σ k, PBlk n k => z p.2) = 0 := by
          funext p
          obtain ⟨⟨⟩, i⟩ := p
          exact hne i
        rw [this]
        have hs0 : segre (0 : (Σ k, PBlk n k) → ℂ) = 0 := by
          funext i
          simp [segre_pblk_apply]
        rw [hs0, map_zero]
        rfl
      set t := Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 with ht
      set x := t⁻¹ • Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) with hx
      obtain ⟨k, hk⟩ := mem_iUnion.1 hxD

      have hwm : (fun p : Σ k, PBlk n k => t⁻¹ * z p.2) ∈ mcPts P :=
        mcPts_smul hMH (fun _ => t⁻¹) (fun _ => inv_ne_zero h0) hzm
      have hwΨ : Ψ (segre fun p : Σ k, PBlk n k => t⁻¹ * z p.2) = Fin.cons 1 x := by
        rw [segre_pblk_smul, map_smul]
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul]
          exact inv_mul_cancel₀ h0
        · simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul, hx, Fin.tail]
      have hwf : segre (fun p : Σ k, PBlk n k => t⁻¹ * z p.2) ∈ fibre P Ψ x :=
        ⟨_, hwm, rfl, hwΨ⟩
      rw [(hfib k x ((hUD k).2.2.1 hk)).1] at hwf
      obtain ⟨j, hj⟩ := hwf
      have hsj : s k j x = fun p : Σ k, PBlk n k => t⁻¹ * z p.2 := segre_pblk_injective hj
      refine ⟨⟨⟨k, j⟩, x, t⟩, ⟨hk, h0⟩, ?_⟩
      rw [hyz]
      simp only [hF, hsj]
      change t • WithLp.toLp 2 (S *ᵥ (t⁻¹ • z)) = WithLp.toLp 2 (S *ᵥ z)
      rw [mulVec_smul, WithLp.toLp_smul, smul_smul, mul_inv_cancel₀ h0, one_smul]
    have hA : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (A1 ∪ A2) = 0 :=
      measure_union_null hhyp hrest
    refine measure_mono_null hsub ?_
    refine le_antisymm ?_ zero_le
    calc Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (L '' (A1 ∪ A2))
        ≤ (‖L‖₊ : ENNReal) ^ (((2 * (e + 1) : ℕ) : ℝ)) *
            Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (A1 ∪ A2) :=
          L.lipschitz.hausdorffMeasure_image_le (Nat.cast_nonneg _) _
      _ = 0 := by rw [hA, mul_zero]
end ConeSheetParam
end GroundTheory.Heights₂.Heights
