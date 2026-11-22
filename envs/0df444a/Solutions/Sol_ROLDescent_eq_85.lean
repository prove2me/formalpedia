-- Prove2me | solution 1 for ROLDescent.eq_85
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:25:26.586826+00:00
-- url     : https://prove2.me/submissions/d9a7e713-6fc0-403a-aee8-b3da6904e5fb

import Mathlib
import Definitions.Def_ROLDescent_WeightedComplex
import Definitions.Def_ROLDescent_facetMass
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_remRank
import Definitions.Def_ROLDescent_outProb
import Definitions.Def_ROLDescent_linkWalk
import Definitions.Def_ROLDescent_IsSubspaceHierarchy
import Definitions.Def_ROLDescent_gramNorm


set_option autoImplicit false
namespace ROLDescent

lemma norm_lt_one_of_strict_contraction
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) (h : ∀ x : E, x ≠ 0 → ‖T x‖ < ‖x‖) : ‖T‖ < 1 := by
  obtain ⟨x,hx,hm⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn
    (show (Metric.closedBall (0 : E) 1).Nonempty from ⟨0,by simp⟩)
    T.continuous.norm.continuousOn
  have hb : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hop : ‖T‖ ≤ ‖T x‖ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _)
    intro y hy
    exact hm (by simpa only [Metric.mem_closedBall, dist_zero_right, hy] using (le_refl (1 : ℝ)))
  apply lt_of_le_of_lt hop
  by_cases hx0 : x = 0
  · simp only [hx0,map_zero,norm_zero]
    norm_num
  · exact (h x hx0).trans_le hb

end ROLDescent


set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace ROLDescent
open scoped InnerProductSpace
noncomputable section

def removedAverage {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Submodule ℂ E) (W : ι → Submodule ℂ E)
    (s : Finset ι) (p : ι → ℝ) : U →L[ℂ] E :=
  (∑ i ∈ s, (p i : ℂ) • (U.starProjection - (W i).starProjection)) ∘L U.subtypeL

lemma removedAverage_apply {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Submodule ℂ E) (W : ι → Submodule ℂ E)
    (s : Finset ι) (p : ι → ℝ) (b : U) :
    removedAverage U W s p b = ∑ i ∈ s, (p i : ℂ) • ((b : E) - (W i).starProjection b) := by
  simp only [removedAverage, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, Submodule.subtypeL_apply,
    Submodule.starProjection_eq_self_iff.mpr b.property]

lemma projection_residual_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (W : Submodule ℂ E) (b : E) :
    ‖b - W.starProjection b‖ ≤ ‖b‖ := by
  simpa only [Submodule.starProjection_orthogonal_val] using Wᗮ.norm_starProjection_apply_le b

lemma projection_residual_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (W : Submodule ℂ E) (b : E) (hb : W.starProjection b ≠ 0) :
    ‖b - W.starProjection b‖ < ‖b‖ := by
  have hs := W.norm_sq_eq_add_norm_sq_starProjection b
  rw [Submodule.starProjection_orthogonal_val] at hs
  have hp : 0 < ‖W.starProjection b‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hb)
  have he := norm_nonneg (b - W.starProjection b)
  have he' := norm_nonneg b
  nlinarith

lemma exists_nonzero_child_projection {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (U : Submodule ℂ E) (W : ι → Submodule ℂ E) (s : Finset ι)
    (hspan : (⨆ i ∈ s,W i) = U) (b : U) (hb : b ≠ 0) :
    ∃ i ∈ s,(W i).starProjection (b : E) ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  have ho : (⨆ i ∈ s,W i) ≤ (ℂ ∙ (b : E))ᗮ := by
    refine iSup_le (fun i => iSup_le (fun hi => ?_))
    intro v hv
    apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
    exact ((W i).starProjection_apply_eq_zero_iff.mp (hn i hi)) v hv
  have hbmem : (b : E) ∈ (⨆ i ∈ s,W i) := by rw [hspan]; exact b.property
  have he : ⟪(b : E),(b : E)⟫_ℂ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (ho hbmem)
  apply hb
  apply Subtype.ext
  exact inner_self_eq_zero.mp he

theorem removedAverage_norm_lt_one {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (U : Submodule ℂ E) (W : ι → Submodule ℂ E) (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s,0 < p i) (hsum : ∑ i ∈ s,p i = 1)
    (hspan : (⨆ i ∈ s,W i) = U) : ‖removedAverage U W s p‖ < 1 := by
  classical
  apply norm_lt_one_of_strict_contraction
  intro b hb
  obtain ⟨i,hi,hn⟩ := exists_nonzero_child_projection U W s hspan b hb
  have hstrict : (∑ i ∈ s,p i * ‖(b : E) - (W i).starProjection b‖) <
      ∑ i ∈ s,p i * ‖(b : E)‖ := by
    apply Finset.sum_lt_sum
    · intro j hj
      exact mul_le_mul_of_nonneg_left (projection_residual_le (W j) b) (hp j hj).le
    · exact ⟨i,hi,mul_lt_mul_of_pos_left (projection_residual_lt (W i) b hn) (hp i hi)⟩
  rw [← Finset.sum_mul,hsum,one_mul] at hstrict
  rw [removedAverage_apply]
  calc
    _ ≤ ∑ i ∈ s,‖(p i : ℂ) • ((b : E) - (W i).starProjection b)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s,p i * ‖(b : E) - (W i).starProjection b‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp i hi)]
    _ < ‖b‖ := hstrict

end
end ROLDescent


set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace ROLDescent
open scoped InnerProductSpace
noncomputable section

lemma residual_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (W : Submodule ℂ E) (b : E) :
    RCLike.re ⟪b,b - W.starProjection b⟫_ℂ = ‖b - W.starProjection b‖^2 := by
  have hc : ⟪W.starProjection b,b - W.starProjection b⟫_ℂ = 0 :=
    inner_eq_zero_symm.mp (W.starProjection_inner_eq_zero b _ (W.starProjection_apply_mem b))
  have he : ⟪b - W.starProjection b,b - W.starProjection b⟫_ℂ =
      ⟪b,b - W.starProjection b⟫_ℂ := by rw [inner_sub_left,hc,sub_zero]
  rw [← he,inner_self_eq_norm_sq]

lemma removedAverage_inner {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Submodule ℂ E) (W : ι → Submodule ℂ E)
    (s : Finset ι) (p : ι → ℝ) (b : U) :
    RCLike.re ⟪(b : E),removedAverage U W s p b⟫_ℂ =
      ∑ i ∈ s,p i * ‖(b : E) - (W i).starProjection b‖^2 := by
  rw [removedAverage_apply,inner_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_smul_right]
  change ( (p i : ℂ) * ⟪(b : E),(b : E) - (W i).starProjection b⟫_ℂ).re = _
  rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change p i * RCLike.re ⟪(b : E),(b : E) - (W i).starProjection b⟫_ℂ = _
  rw [residual_inner]

lemma weighted_projection_pythagoras {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (W : ι → Submodule ℂ E) (s : Finset ι) (p : ι → ℝ)
    (hsum : ∑ i ∈ s,p i = 1) (b : E) :
    ∑ i ∈ s,p i * ‖(W i).starProjection b‖^2 =
      ‖b‖^2 - ∑ i ∈ s,p i * ‖b - (W i).starProjection b‖^2 := by
  have he (i : ι) : p i * ‖b‖^2 =
      p i * ‖(W i).starProjection b‖^2 +
        p i * ‖b - (W i).starProjection b‖^2 := by
    have h := (W i).norm_sq_eq_add_norm_sq_starProjection b
    rw [Submodule.starProjection_orthogonal_val] at h
    rw [h,mul_add]
  have hs := Finset.sum_congr (s₁ := s) rfl (fun i hi => he i)
  rw [← Finset.sum_mul,hsum,one_mul,Finset.sum_add_distrib] at hs
  linarith

theorem removedAverage_retention {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (U : Submodule ℂ E) (W : ι → Submodule ℂ E) (s : Finset ι) (p : ι → ℝ)
    (hsum : ∑ i ∈ s,p i = 1) (b : U) :
    (∑ i ∈ s,p i * ‖(W i).starProjection (b : E)‖^2 =
        ‖(b : E)‖^2 - ∑ i ∈ s,p i *
          ‖((U.starProjection - (W i).starProjection) (b : E))‖^2) ∧
      (1 - ‖removedAverage U W s p‖) * ‖(b : E)‖^2 ≤
        ‖(b : E)‖^2 - ∑ i ∈ s,p i *
          ‖((U.starProjection - (W i).starProjection) (b : E))‖^2 := by
  have hproj : U.starProjection (b : E) = b :=
    Submodule.starProjection_eq_self_iff.mpr b.property
  simp only [ContinuousLinearMap.sub_apply,hproj]
  constructor
  · exact weighted_projection_pythagoras W s p hsum b
  · have hi := removedAverage_inner U W s p b
    have hle := re_inner_le_norm (𝕜 := ℂ) (b : E) (removedAverage U W s p b)
    have hop := mul_le_mul_of_nonneg_left
      ((removedAverage U W s p).le_opNorm b) (norm_nonneg (b : E))
    rw [hi] at hle
    have he : ‖(b : E)‖ * (‖removedAverage U W s p‖ * ‖b‖) =
        ‖removedAverage U W s p‖ * ‖(b : E)‖^2 := by
      simp only [Submodule.coe_norm]
      ring
    rw [he] at hop
    nlinarith

end
end ROLDescent


open ROLDescent
open scoped BigOperators


namespace ROLDescent.Eq85WeightProof

private theorem mass_nonneg {V : Type*} [DecidableEq V]
    {X : Finset (Finset V)} {d : ℕ} {w : Finset V → ℝ}
    (hX : WeightedComplex X d w) (τ : Finset V) : 0 ≤ facetMass X d w τ := by
  exact Finset.sum_nonneg (fun F hF => (hX.2.2.2 F (Finset.mem_filter.mp hF).1).le)

private theorem mass_pos {V : Type*} [DecidableEq V]
    {X : Finset (Finset V)} {d : ℕ} {w : Finset V → ℝ}
    (hX : WeightedComplex X d w) {τ : Finset V} (hτ : τ ∈ X) : 0 < facetMass X d w τ := by
  let candidates := X.filter (fun F => τ ⊆ F)
  obtain ⟨F, hF, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨τ, Finset.mem_filter.mpr ⟨hτ, le_rfl⟩⟩
  have hF' := Finset.mem_filter.mp hF
  have hcard : F.card = d := hX.2.1.2 F hF'.1 (by
    intro G hG hFG
    have hG' : G ∈ candidates := Finset.mem_filter.mpr ⟨hG, hF'.2.trans hFG⟩
    exact (Finset.eq_of_subset_of_card_le hFG (hmax G hG')).symm)
  have hf : F ∈ SteurerHDX.faces X d := Finset.mem_filter.mpr ⟨hF'.1, hcard⟩
  unfold facetMass
  refine lt_of_lt_of_le (hX.2.2.2 F hf) (Finset.single_le_sum ?_ (Finset.mem_filter.mpr ⟨hf,hF'.2⟩))
  exact fun G hG => (hX.2.2.2 G (Finset.mem_filter.mp hG).1).le

private theorem degree_identity {V : Type*} [DecidableEq V]
    {X : Finset (Finset V)} {d : ℕ} {w : Finset V → ℝ}
    (τ S : Finset V) (hS : ∀ v ∈ S, v ∉ τ)
    (hCover : ∀ F ∈ SteurerHDX.faces X d, τ ⊆ F → F \ τ ⊆ S) :
    ∑ i ∈ S, facetMass X d w (insert i τ) = (remRank d τ : ℝ) * facetMass X d w τ := by
  classical
  simp only [facetMass, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F hF
  by_cases hτF : τ ⊆ F
  · have hFS : S.filter (fun i => insert i τ ⊆ F) = F \ τ := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.insert_subset_iff, hτF, and_true]
      exact ⟨fun h => ⟨h.2, hS v h.1⟩, fun h => ⟨hCover F hF hτF (Finset.mem_sdiff.mpr h), h.1⟩⟩
    rw [← Finset.sum_filter, hFS, Finset.sum_const, nsmul_eq_mul,
      Finset.card_sdiff_of_subset hτF, (Finset.mem_filter.mp hF).2]
    simp [remRank, hτF]
  · have hnone : ∀ i ∈ S, ¬ insert i τ ⊆ F := by
      intro i _ hi
      exact hτF (Finset.subset_insert i τ |>.trans hi)
    simp [hτF, Finset.sum_eq_zero (fun i hi => if_neg (hnone i hi))]

private theorem link_mem {V : Type*} [Fintype V] [DecidableEq V]
    {X : Finset (Finset V)} {τ : Finset V} {i : V} :
    i ∈ HDXConc.linkVerts X τ ↔ i ∉ τ ∧ insert i τ ∈ X := by
  simp [HDXConc.linkVerts]


theorem outProb_pos_sum {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (hX : WeightedComplex X d w)
    (τ : Finset V) (hτ : τ ∈ X) (hτd : τ.card + 2 ≤ d) :
    (∀ i ∈ HDXConc.linkVerts X τ, 0 < outProb X d w τ i) ∧
      ∑ i ∈ HDXConc.linkVerts X τ, outProb X d w τ i = 1 := by
  classical
  have hr : (0 : ℝ) < (remRank d τ : ℝ) := by
    exact_mod_cast (show 0 < remRank d τ from by unfold remRank; omega)
  have hden : 0 < (remRank d τ : ℝ) * facetMass X d w τ :=
    mul_pos hr (mass_pos hX hτ)
  have hd1 : ∑ i ∈ HDXConc.linkVerts X τ, facetMass X d w (insert i τ) =
      (remRank d τ : ℝ) * facetMass X d w τ := by
    refine degree_identity τ _ (fun i hi => (link_mem.mp hi).1) ?_
    intro F hF hτF i hi
    obtain ⟨hiF, hiτ⟩ := Finset.mem_sdiff.mp hi
    exact link_mem.mpr ⟨hiτ, hX.2.1.1 F (Finset.mem_filter.mp hF).1 _
      (Finset.insert_subset_iff.mpr ⟨hiF, hτF⟩)⟩
  constructor
  · intro i hi
    exact div_pos (mass_pos hX (link_mem.mp hi).2) hden
  · unfold outProb
    rw [← Finset.sum_div,hd1,div_self hden.ne']

end ROLDescent.Eq85WeightProof

open ROLDescent

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (hX : WeightedComplex X d w)
    (I : Finset V → Submodule ℂ K) (hI : IsSubspaceHierarchy X d I)
    (τ : Finset V) (hτ : τ ∈ X) (hτd : τ.card + 2 ≤ d) :
    (∀ b : ↥(I τ),
      ∑ i ∈ HDXConc.linkVerts X τ, outProb X d w τ i * ‖(I (insert i τ)).starProjection (b : K)‖ ^ 2 =
        ‖(b : K)‖ ^ 2 - ∑ i ∈ HDXConc.linkVerts X τ, outProb X d w τ i *
          ‖((I τ).starProjection - (I (insert i τ)).starProjection) (b : K)‖ ^ 2 ∧
      (1 - gramNorm X d w I τ) * ‖(b : K)‖ ^ 2 ≤
        ‖(b : K)‖ ^ 2 - ∑ i ∈ HDXConc.linkVerts X τ, outProb X d w τ i *
          ‖((I τ).starProjection - (I (insert i τ)).starProjection) (b : K)‖ ^ 2) ∧
    gramNorm X d w I τ < 1 := by
  obtain ⟨hp,hsum⟩ := Eq85WeightProof.outProb_pos_sum X d w hX τ hτ hτd
  constructor
  · intro b
    simpa only [removedAverage,gramNorm] using
      removedAverage_retention (I τ) (fun i => I (insert i τ))
        (HDXConc.linkVerts X τ) (outProb X d w τ) hsum b
  · simpa only [removedAverage,gramNorm] using
      removedAverage_norm_lt_one (I τ) (fun i => I (insert i τ))
        (HDXConc.linkVerts X τ) (outProb X d w τ) hp hsum (hI τ hτ hτd).2

