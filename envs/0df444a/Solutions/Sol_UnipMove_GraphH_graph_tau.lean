-- Prove2me | solution 1 for UnipMove.GraphH.graph_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:38:43.248067+00:00
-- url     : https://prove2.me/submissions/6691bc33-fca2-47cc-b870-f7ee4de5953a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Theorems.Thm_UnipMove_GraphH_en_nonneg
import Theorems.Thm_UnipMove_GraphH_en_sq
import Theorems.Thm_UnipMove_GraphH_en_eq_sqrt
import Theorems.Thm_UnipMove_GraphH_en_add_le
import Theorems.Thm_UnipMove_GraphH_en_sub_le
import Theorems.Thm_UnipMove_GraphH_eq_zero_of_en
import Theorems.Thm_UnipMove_GraphH_en_pos
import Theorems.Thm_UnipMove_GraphH_en_le_of_nsq
import Theorems.Thm_UnipMove_GraphH_opN_le
import Theorems.Thm_UnipMove_GraphH_nsq_split
import Theorems.Thm_UnipMove_GraphH_en_top_le
import Theorems.Thm_UnipMove_GraphH_en_bot_le
import Theorems.Thm_UnipMove_GraphH_top_mulVec_ext
import Theorems.Thm_UnipMove_GraphH_bot_mulVec_ext
import Theorems.Thm_UnipMove_GraphH_blkA_low
import Theorems.Thm_UnipMove_GraphH_blkB_low
import Theorems.Thm_UnipMove_GraphH_fin_split
import Theorems.Thm_UnipMove_GraphH_span_cols_eq
import Theorems.Thm_UnipMove_GraphH_maj_ortho
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
section Blocks
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
end Blocks
section Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma nsq_mulVec_le_sum_norm_sq_mul_nsq {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    nsq (W *ᵥ v) ≤ (∑ i, ∑ j, ‖W i j‖ ^ 2) * nsq v := by
  unfold nsq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have h1 : ‖(W *ᵥ v) i‖ ≤ ∑ j, ‖W i j‖ * ‖v j‖ := by
    calc ‖(W *ᵥ v) i‖ = ‖∑ j, W i j * v j‖ := rfl
      _ ≤ ∑ j, ‖W i j * v j‖ := norm_sum_le _ _
      _ = ∑ j, ‖W i j‖ * ‖v j‖ := Finset.sum_congr rfl fun j _ => norm_mul _ _
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖W i j‖) (fun j => ‖v j‖)
  calc ‖(W *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖W i j‖ * ‖v j‖) ^ 2 := by gcongr
    _ ≤ _ := h2
private lemma en_mulVec_le_opN_mul_en {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    en (W *ᵥ v) ≤ Data.opN W * en v := by
  by_cases hv : v = 0
  · subst hv
    simp [en_eq_sqrt, nsq, Matrix.mulVec_zero]
  · have hpos := en_pos hv
    have hF : 0 ≤ ∑ i, ∑ j, ‖W i j‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hC : ∀ u, en (W *ᵥ u) ≤ Real.sqrt (∑ i, ∑ j, ‖W i j‖ ^ 2) * en u := fun u =>
      en_le_of_nsq _ _ (Real.sqrt_nonneg _) (by rw [Real.sq_sqrt hF]; exact nsq_mulVec_le_sum_norm_sq_mul_nsq W u)
    have hmem : en (W *ᵥ v) / en v ∈ {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        t = Real.sqrt (∑ i, ‖Matrix.mulVec W v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} :=
      ⟨v, hv, by rw [en_eq_sqrt, en_eq_sqrt]; rfl⟩
    have hbdd : BddAbove {t | ∃ v : Fin n → ℂ, v ≠ 0 ∧
        t = Real.sqrt (∑ i, ‖Matrix.mulVec W v i‖ ^ 2) / Real.sqrt (∑ j, ‖v j‖ ^ 2)} := by
      refine ⟨Real.sqrt (∑ i, ∑ j, ‖W i j‖ ^ 2), ?_⟩
      rintro t ⟨u, hu, rfl⟩
      have h1 := hC u
      have hup := en_pos hu
      rw [en_eq_sqrt, en_eq_sqrt] at h1
      rw [en_eq_sqrt] at hup
      change Real.sqrt (nsq (W *ᵥ u)) / Real.sqrt (nsq u) ≤ _
      rw [div_le_iff₀ hup]
      exact h1
    have h2 := le_csSup hbdd hmem
    rw [div_le_iff₀ hpos] at h2
    unfold Data.opN
    exact h2
end Frames
end
end UnipMove.GraphH
namespace UnipMove
open ReciprocityTheory.ChartRestriction.G.FD NumberField
end UnipMove
end

set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace UnipMove.GraphH
theorem _root_.solution {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) (ho : X.IsOrtho x0) (τ : X.Ψ)
    (nτ : Matrix (Fin r) (Fin r) ℂ) (Z1 : X.Coord) {η z : ℝ} (hη : 0 ≤ η) (hz : 0 ≤ z)
    (hZ1 : X.zN Z1 ≤ z) (hs : η * (1 + z) < 1)
    (hn : ∀ v, X.maj x0 τ ((nτ - 1) *ᵥ v) ≤ η ^ 2 * X.maj x0 τ v) :
    ∃ W : Matrix (Fin (r - X.p0)) (Fin X.p0) ℂ,
      Data.opN W ≤ (z + η * (1 + z)) / (1 - η * (1 + z)) ∧
      ∀ Z : X.Coord, Matrix.of (Z τ) = W →
        Submodule.span ℂ (Set.range fun a : Fin X.p0 =>
            col (nτ * (mat x0 τ * X.lowBlock Z1 τ)) (Fin.castLE X.p0_le a)) =
          Submodule.span ℂ (Set.range fun a : Fin X.p0 =>
            col (mat x0 τ * X.lowBlock Z τ) (Fin.castLE X.p0_le a)) := by
  have hker : ∀ c : Fin r → ℂ, mat x0 τ *ᵥ c = 0 → c = 0 := by
    intro c hMc
    have h0 : nsq c = nsq (0 : Fin r → ℂ) := by
      rw [← maj_ortho X ho τ c, ← maj_ortho X ho τ 0, hMc, Matrix.mulVec_zero]
    apply eq_zero_of_en c
    rw [en_eq_sqrt, h0]
    simp [nsq]
  have hMu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr fun h0 => by
    obtain ⟨c, hc, hMc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hc (hker c hMc)
  have hMMi : mat x0 τ * (mat x0 τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hMu
  obtain ⟨N', hN'⟩ : ∃ N' : Matrix (Fin r) (Fin r) ℂ, N' = (mat x0 τ)⁻¹ * nτ * mat x0 τ :=
    ⟨_, rfl⟩
  have hMN : mat x0 τ * N' = nτ * mat x0 τ := by
    rw [hN', ← mul_assoc, ← mul_assoc, hMMi, one_mul]
  have hN1 : ∀ c, en ((N' - 1) *ᵥ c) ≤ η * en c := by
    intro c
    apply en_le_of_nsq _ _ hη
    have hMN1 : mat x0 τ * (N' - 1) = (nτ - 1) * mat x0 τ := by
      rw [mul_sub, mul_one, hMN, sub_mul, one_mul]
    rw [← maj_ortho X ho τ ((N' - 1) *ᵥ c), ← maj_ortho X ho τ c, Matrix.mulVec_mulVec, hMN1,
      ← Matrix.mulVec_mulVec]
    exact hn (mat x0 τ *ᵥ c)
  have hZτ : Data.opN (Matrix.of (Z1 τ)) ≤ z := by
    have hb : BddAbove (Set.range fun τ' : X.Ψ => Data.opN (Matrix.of (Z1 τ'))) :=
      (Set.finite_range _).bddAbove
    exact (le_ciSup hb τ).trans hZ1
  have hsplit : ∀ w : Fin r → ℂ, en w ≤ en (top X w) + en (bot X w) := by
    intro w
    rw [en_eq_sqrt w]
    calc Real.sqrt (nsq w) ≤ Real.sqrt ((en (top X w) + en (bot X w)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [nsq_split X w, ← en_sq (top X w), ← en_sq (bot X w)]
          nlinarith [mul_nonneg (en_nonneg (top X w)) (en_nonneg (bot X w))]
      _ = en (top X w) + en (bot X w) := Real.sqrt_sq (add_nonneg (en_nonneg _) (en_nonneg _))
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Fin r) (Fin r) ℂ, K = N' * X.lowBlock Z1 τ := ⟨_, rfl⟩
  have hyt : ∀ d, top X (X.lowBlock Z1 τ *ᵥ ext X d) = d := fun d => by
    rw [top_mulVec_ext, blkA_low, Matrix.one_mulVec]
  have hyb : ∀ d, bot X (X.lowBlock Z1 τ *ᵥ ext X d) = Matrix.of (Z1 τ) *ᵥ d := fun d => by
    rw [bot_mulVec_ext, blkB_low]
  have hyen : ∀ d, en (X.lowBlock Z1 τ *ᵥ ext X d) ≤ (1 + z) * en d := fun d => by
    have h1 := hsplit (X.lowBlock Z1 τ *ᵥ ext X d)
    rw [hyt, hyb] at h1
    have h2 := en_mulVec_le_opN_mul_en (Matrix.of (Z1 τ)) d
    have h3 := mul_le_mul_of_nonneg_right hZτ (en_nonneg d)
    linarith
  have hKd : ∀ d, K *ᵥ ext X d = X.lowBlock Z1 τ *ᵥ ext X d +
      (N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d) := fun d => by
    rw [hK, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hed : ∀ d, en ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)) ≤ η * (1 + z) * en d :=
    fun d => by
      have h1 := hN1 (X.lowBlock Z1 τ *ᵥ ext X d)
      have h2 := mul_le_mul_of_nonneg_left (hyen d) hη
      nlinarith
  have htadd : ∀ u v : Fin r → ℂ, top X (u + v) = top X u + top X v := fun _ _ => rfl
  have hbadd : ∀ u v : Fin r → ℂ, bot X (u + v) = bot X u + bot X v := fun _ _ => rfl
  have hAe : ∀ d, blkA X K *ᵥ d = d + top X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)) :=
    fun d => by rw [← top_mulVec_ext, hKd, htadd, hyt]
  have hBe : ∀ d, blkB X K *ᵥ d =
      Matrix.of (Z1 τ) *ᵥ d + bot X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)) :=
    fun d => by rw [← bot_mulVec_ext, hKd, hbadd, hyb]
  have hs0 : 0 ≤ η * (1 + z) := mul_nonneg hη (by linarith)
  have hAl : ∀ d, (1 - η * (1 + z)) * en d ≤ en (blkA X K *ᵥ d) := fun d => by
    have h1 := en_top_le X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d))
    have h2 := hed d
    have hd : d = blkA X K *ᵥ d - top X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)) := by
      rw [hAe d]
      abel
    have h3 := en_sub_le (blkA X K *ᵥ d) (top X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)))
    rw [← hd] at h3
    nlinarith
  have hBu : ∀ d, en (blkB X K *ᵥ d) ≤ (z + η * (1 + z)) * en d := fun d => by
    rw [hBe d]
    have h1 := en_add_le (Matrix.of (Z1 τ) *ᵥ d)
      (bot X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d)))
    have h2 := en_mulVec_le_opN_mul_en (Matrix.of (Z1 τ)) d
    have h3 := mul_le_mul_of_nonneg_right hZτ (en_nonneg d)
    have h4 := en_bot_le X ((N' - 1) *ᵥ (X.lowBlock Z1 τ *ᵥ ext X d))
    have h5 := hed d
    nlinarith
  have h1s : 0 < 1 - η * (1 + z) := by linarith
  have hAu : IsUnit (blkA X K).det := isUnit_iff_ne_zero.mpr fun h0 => by
    obtain ⟨d, hd, hAd⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 := hAl d
    rw [hAd] at h1
    have h2 : en (0 : Fin X.p0 → ℂ) = 0 := by
      rw [en_eq_sqrt]
      simp [nsq]
    rw [h2] at h1
    have h3 := en_pos hd
    nlinarith [mul_pos h1s h3]
  refine ⟨blkB X K * (blkA X K)⁻¹, ?_, fun Z hZW => ?_⟩
  · apply opN_le _ (div_nonneg (by linarith) h1s.le)
    intro v
    have hAd : blkA X K *ᵥ ((blkA X K)⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
    have hWv : (blkB X K * (blkA X K)⁻¹) *ᵥ v = blkB X K *ᵥ ((blkA X K)⁻¹ *ᵥ v) := by
      rw [Matrix.mulVec_mulVec]
    rw [hWv]
    have hB := hBu ((blkA X K)⁻¹ *ᵥ v)
    have hA := hAl ((blkA X K)⁻¹ *ᵥ v)
    rw [hAd] at hA
    rw [div_mul_eq_mul_div, le_div_iff₀ h1s]
    have hzs : 0 ≤ z + η * (1 + z) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hA hzs, mul_le_mul_of_nonneg_left hB h1s.le]
  · have hMK : nτ * (mat x0 τ * X.lowBlock Z1 τ) = mat x0 τ * K := by
      rw [hK, ← mul_assoc (mat x0 τ), hMN, mul_assoc]
    have hcol : ∀ (i : Fin r) (a : Fin X.p0), K i (Fin.castLE X.p0_le a) =
        ∑ b, X.lowBlock Z τ i (Fin.castLE X.p0_le b) * blkA X K b a := by
      intro i a
      rcases fin_split X i with ⟨i', rfl⟩ | ⟨m, rfl⟩
      · have h1 : (blkA X (X.lowBlock Z τ) * blkA X K) i' a = blkA X K i' a := by
          rw [blkA_low, Matrix.one_mul]
        rw [Matrix.mul_apply] at h1
        exact h1.symm
      · have h2 : (blkB X (X.lowBlock Z τ) * blkA X K) m a = blkB X K m a := by
          rw [blkB_low, hZW, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.mul_one]
        rw [Matrix.mul_apply] at h2
        exact h2.symm
    refine span_cols_eq _ _ (blkA X K) hAu (fun a => ?_)
    funext i
    show col (nτ * (mat x0 τ * X.lowBlock Z1 τ)) (Fin.castLE X.p0_le a) i =
      (∑ b, blkA X K b a • col (mat x0 τ * X.lowBlock Z τ) (Fin.castLE X.p0_le b)) i
    have lhs : col (mat x0 τ * K) (Fin.castLE X.p0_le a) i =
        ∑ b, ∑ k, mat x0 τ i k * (X.lowBlock Z τ k (Fin.castLE X.p0_le b) * blkA X K b a) := by
      show (mat x0 τ * K) i (Fin.castLE X.p0_le a) = _
      rw [Matrix.mul_apply]
      simp only [hcol, Finset.mul_sum]
      exact Finset.sum_comm
    have rhs : (∑ b, blkA X K b a • col (mat x0 τ * X.lowBlock Z τ) (Fin.castLE X.p0_le b)) i =
        ∑ b, ∑ k, blkA X K b a * (mat x0 τ i k * X.lowBlock Z τ k (Fin.castLE X.p0_le b)) := by
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      show blkA X K b a * (mat x0 τ * X.lowBlock Z τ) i (Fin.castLE X.p0_le b) = _
      rw [Matrix.mul_apply, Finset.mul_sum]
    rw [hMK, lhs, rhs]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end UnipMove.GraphH
