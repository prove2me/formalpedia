-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.elementary_divisor_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:04:59.222394+00:00
-- url     : https://prove2.me/submissions/79c89492-a76a-4d60-b78d-a09d3fcf3401

import Definitions.Def_ReciprocityTheory_DualLattices_DotSingle
import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroupStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLengthProductStatementHolds
import Definitions.Def_ReciprocityTheory_DualLattices_ElementaryDivisorStatement
import Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_fg_range
import Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_finrank_split
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up__T_E_26bb633a7916
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_ht__T_b6fe05e89010
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_block
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Tot_sum_fromBlocks_diag
import Theorems.Thm_ReciprocityTheory_PGsh_Up_cj_cj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_E
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_cp_ne
import Theorems.Thm_ReciprocityTheory_PGsh_Up_htd_domain
import Theorems.Thm_ReciprocityTheory_PGsh_Up_isLocal_of_integers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
open ED
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution : EigenElementaryDivisorStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U X hX
  classical
  have hv := hS.integers
  haveI := htd_domain hS
  haveI := isLocal_of_integers hv
  have hcp0 := htd_cp_ne hS
  have hEu : IsUnit (H.E.map (algebraMap ℤ_[p] R)).det := (htd_E H).2.2
  have hTT : ∀ i, U.εT i * U.εT i = U.εT i := fun i => by rw [U.εT_orth i i, if_pos rfl]
  have hLL : ∀ i, U.εL i * U.εL i = U.εL i := fun i => by rw [U.εL_orth i i, if_pos rfl]
  have hbt_r : ∀ i, bt2 H U * U.εT i = U.εL i * H.Bt * U.εT i := by
    intro i
    unfold bt2
    rw [Matrix.sum_mul, Finset.sum_eq_single i]
    · rw [Matrix.mul_assoc, hTT]
    · intro j _ hj
      rw [Matrix.mul_assoc, U.εT_orth j i, if_neg hj, Matrix.mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hbt_l : ∀ i, U.εL i * bt2 H U = U.εL i * H.Bt * U.εT i := by
    intro i
    unfold bt2
    rw [Matrix.mul_sum, Finset.sum_eq_single i]
    · simp only [← Matrix.mul_assoc, hLL]
    · intro j _ hj
      simp only [← Matrix.mul_assoc, U.εL_orth i j, if_neg (Ne.symm hj), Matrix.zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hLt : ∀ j, (U.εL j)ᵀ * H.Ht = H.Ht * U.εT (U.cj j) := by
    intro j
    rw [ht_εT hS H U (U.cj j), cj_cj hS U j]

  have hform : (bt2 H U)ᵀ * H.Ht - H.Htᵀ * bt2 H U = cp • H.E.map (algebraMap ℤ_[p] R) := by
    have h1 : (bt2 H U)ᵀ * H.Ht = ∑ j, (U.εT j)ᵀ * (H.Btᵀ * H.Ht) * U.εT (U.cj j) := by
      unfold bt2
      rw [Matrix.transpose_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Matrix.transpose_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
      rw [hLt j]
    have h2 : H.Htᵀ * bt2 H U = ∑ j, (U.εT j)ᵀ * (H.Htᵀ * H.Bt) * U.εT (U.cj j) := by
      calc H.Htᵀ * bt2 H U = ∑ j, H.Htᵀ * (U.εL j * H.Bt * U.εT j) := by
            unfold bt2; rw [Matrix.mul_sum]
        _ = ∑ j, H.Htᵀ * (U.εL (U.cj j) * H.Bt * U.εT (U.cj j)) :=
            (Equiv.sum_comp U.cj (fun j => H.Htᵀ * (U.εL j * H.Bt * U.εT j))).symm
        _ = _ := Finset.sum_congr rfl (fun j _ => by
            have hx : H.Htᵀ * U.εL (U.cj j) = (U.εT j)ᵀ * H.Htᵀ := by
              have h0 := hLt (U.cj j)
              rw [cj_cj hS U j] at h0
              simpa [Matrix.transpose_mul] using congrArg Matrix.transpose h0
            simp only [← Matrix.mul_assoc]
            rw [hx])
    have h3 : ∀ j, (U.εT j)ᵀ * (H.Btᵀ * H.Ht) * U.εT (U.cj j) - (U.εT j)ᵀ * (H.Htᵀ * H.Bt) * U.εT (U.cj j) =
        cp • (H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj j)) := by
      intro j
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, H.form_eq_alt, Matrix.mul_smul, Matrix.smul_mul, εT_E hS H U j,
        Matrix.mul_assoc, hTT]
    have hsT : ∑ j, U.εT (U.cj j) = ∑ j, U.εT j := Equiv.sum_comp U.cj U.εT
    rw [h1, h2, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun j _ => h3 j), ← Finset.smul_sum,
      ← Matrix.mul_sum, hsT, U.εT_sum, Matrix.mul_one]

  have hΦinj : ∀ x, (Matrix.fromRows H.Ht (bt2 H U)) *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hHt : H.Ht *ᵥ x = 0 := by funext k; exact congrFun hx (Sum.inl k)
    have hBt : bt2 H U *ᵥ x = 0 := by funext k; exact congrFun hx (Sum.inr k)
    have hE0 : cp • ((H.E.map (algebraMap ℤ_[p] R)) *ᵥ x) = 0 := by
      have hsv : (cp • (H.E.map (algebraMap ℤ_[p] R))) *ᵥ x = cp • ((H.E.map (algebraMap ℤ_[p] R)) *ᵥ x) := by
        funext k
        simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [← hsv, ← hform, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hHt, hBt]
      simp
    have hE1 : (H.E.map (algebraMap ℤ_[p] R)) *ᵥ x = 0 := (smul_eq_zero.1 hE0).resolve_left hcp0
    calc x = ((H.E.map (algebraMap ℤ_[p] R))⁻¹ * (H.E.map (algebraMap ℤ_[p] R))) *ᵥ x := by rw [Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hE1, Matrix.mulVec_zero]

  have hcpi : ∀ i (w : Ix g → R), w ᵥ* U.εT i = w →
      ∃ u : Ix g → R, cp • w = u ᵥ* ((Matrix.fromRows H.Ht (bt2 H U)) * U.εT i) := by
    intro i w hw
    have hz : (w ᵥ* (H.E.map (algebraMap ℤ_[p] R))⁻¹) ᵥ* (H.E.map (algebraMap ℤ_[p] R)) = w := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hEu, Matrix.vecMul_one]
    refine ⟨Sum.elim (bt2 H U *ᵥ (w ᵥ* (H.E.map (algebraMap ℤ_[p] R))⁻¹)) (-(H.Ht *ᵥ (w ᵥ* (H.E.map (algebraMap ℤ_[p] R))⁻¹))), ?_⟩
    have hu : Sum.elim (bt2 H U *ᵥ (w ᵥ* (H.E.map (algebraMap ℤ_[p] R))⁻¹)) (-(H.Ht *ᵥ (w ᵥ* (H.E.map (algebraMap ℤ_[p] R))⁻¹))) ᵥ* (Matrix.fromRows H.Ht (bt2 H U)) =
        (w ᵥ* (H.E.map (algebraMap ℤ_[p] R))⁻¹) ᵥ* ((bt2 H U)ᵀ * H.Ht - H.Htᵀ * bt2 H U) := by
      rw [Matrix.vecMul_sub, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose,
        Matrix.vecMul_transpose]
      funext l
      simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg, Finset.sum_neg_distrib]
    have hsm : (w ᵥ* (H.E.map (algebraMap ℤ_[p] R))⁻¹) ᵥ* (cp • (H.E.map (algebraMap ℤ_[p] R))) = cp • ((w ᵥ* (H.E.map (algebraMap ℤ_[p] R))⁻¹) ᵥ* (H.E.map (algebraMap ℤ_[p] R))) := by
      funext k
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    calc cp • w = cp • (w ᵥ* U.εT i) := by rw [hw]
      _ = ((w ᵥ* (H.E.map (algebraMap ℤ_[p] R))⁻¹) ᵥ* (cp • (H.E.map (algebraMap ℤ_[p] R)))) ᵥ* U.εT i := by
          rw [hsm, hz]
          funext k
          simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = (Sum.elim (bt2 H U *ᵥ (w ᵥ* (H.E.map (algebraMap ℤ_[p] R))⁻¹)) (-(H.Ht *ᵥ (w ᵥ* (H.E.map (algebraMap ℤ_[p] R))⁻¹))) ᵥ* (Matrix.fromRows H.Ht (bt2 H U))) ᵥ* U.εT i := by
          rw [hu, hform]
      _ = _ := Matrix.vecMul_vecMul _ _ _

  let Pq : Fin U.m → Matrix (Ix g) (Ix g) R := fun i => Matrix.fromBlocks (U.εL (U.cj i))ᵀ 0 0 (U.εL i)
  have hPqmv : ∀ i (w : Ix g → R),
      Pq i *ᵥ w = Sum.elim ((U.εL (U.cj i))ᵀ *ᵥ (w ∘ Sum.inl)) (U.εL i *ᵥ (w ∘ Sum.inr)) := by
    intro i w
    funext s
    rcases s with k | k <;> simp [Pq, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hPqmem : ∀ i w, Pq i *ᵥ w ∈ qE U.εL i (U.cj i) := by
    intro i w
    rw [hPqmv]
    refine Submodule.mem_inf.2 ⟨Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨w ∘ Sum.inl, ?_⟩),
      Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨w ∘ Sum.inr, ?_⟩)⟩ <;> rfl
  have hPqid : ∀ i, ∀ w ∈ qE U.εL i (U.cj i), Pq i *ᵥ w = w := by
    intro i w hw
    obtain ⟨y1, hy1⟩ := LinearMap.mem_range.1 (Submodule.mem_comap.1 (Submodule.mem_inf.1 hw).1)
    obtain ⟨y2, hy2⟩ := LinearMap.mem_range.1 (Submodule.mem_comap.1 (Submodule.mem_inf.1 hw).2)
    have e1 : w ∘ Sum.inl = (U.εL (U.cj i))ᵀ *ᵥ y1 := hy1.symm
    have e2 : w ∘ Sum.inr = U.εL i *ᵥ y2 := hy2.symm
    rw [hPqmv, e1, e2, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hLL, hLL]
    funext s
    rcases s with k | k
    · exact (congrFun e1 k).symm
    · exact (congrFun e2 k).symm
  have hcomm : ∀ i, (Matrix.fromRows H.Ht (bt2 H U)) * U.εT i = Pq i * (Matrix.fromRows H.Ht (bt2 H U)) := by
    intro i
    have e1 := ht_εT hS H U i
    have e2 : bt2 H U * U.εT i = U.εL i * bt2 H U := (hbt_r i).trans (hbt_l i).symm
    ext s l
    rcases s with k | k
    · have h0 := congrFun (congrFun e1 k) l
      simpa [Pq, Matrix.mul_apply, Fintype.sum_sum_type] using h0
    · have h0 := congrFun (congrFun e2 k) l
      simpa [Pq, Matrix.mul_apply, Fintype.sum_sum_type] using h0

  have hPorth : ∀ i j, Pq i * Pq j = if i = j then Pq i else 0 := by
    intro i j
    simp only [Pq, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, ← Matrix.transpose_mul, hLL, hLL]
    · have hc : U.cj j ≠ U.cj i := fun e => h (U.cj.injective e).symm
      rw [if_neg h, ← Matrix.transpose_mul, U.εL_orth, if_neg hc, U.εL_orth, if_neg h, Matrix.transpose_zero,
        Matrix.fromBlocks_zero]
  have hPsum : ∑ i, Pq i = 1 := by
    have hsL : ∑ i, (U.εL (U.cj i))ᵀ = ∑ i, (U.εL i)ᵀ := Equiv.sum_comp U.cj (fun j => (U.εL j)ᵀ)
    simp only [Pq]
    rw [Tot.sum_fromBlocks_diag, hsL, ← Matrix.transpose_sum, U.εL_sum, Matrix.transpose_one,
      Matrix.fromBlocks_one]
  have hfT := finrank_split hv U.εT U.εT_orth U.εT_sum
  have hfQ := finrank_split hv Pq hPorth hPsum
  have hQrange : ∀ i, LinearMap.range (Matrix.mulVecLin (Pq i)) = qE U.εL i (U.cj i) := by
    intro i
    ext w
    constructor
    · rintro ⟨y, rfl⟩
      exact hPqmem i y
    · intro hw
      exact ⟨w, hPqid i w hw⟩
  have hle : ∀ i, Module.finrank R (LinearMap.range (Matrix.mulVecLin (U.εT i))) ≤
      Module.finrank R (qE U.εL i (U.cj i)) := by
    intro i
    haveI : Module.Finite R (qE U.εL i (U.cj i)) := by
      rw [← hQrange i]
      exact Module.Finite.iff_fg.2 (fg_range _)
    let f : LinearMap.range (Matrix.mulVecLin (U.εT i)) →ₗ[R] qE U.εL i (U.cj i) :=
      { toFun := fun x => ⟨(Matrix.fromRows H.Ht (bt2 H U)) *ᵥ (x : Ix g → R), by
          obtain ⟨y, hy⟩ := LinearMap.mem_range.1 x.2
          rw [← hy, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hcomm i, ← Matrix.mulVec_mulVec]
          exact hPqmem i _⟩
        map_add' := fun x y => by
          apply Subtype.ext
          simp [Matrix.mulVec_add]
        map_smul' := fun c x => by
          apply Subtype.ext
          simp [Matrix.mulVec_smul] }
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have h1 : (Matrix.fromRows H.Ht (bt2 H U)) *ᵥ ((x : Ix g → R) - y) = 0 := by
        rw [Matrix.mulVec_sub]
        exact sub_eq_zero.2 (congrArg Subtype.val hxy)
      exact sub_eq_zero.1 (hΦinj _ h1)
    exact LinearMap.finrank_le_finrank_of_injective hf
  have hnQ : ∀ i, Module.finrank R (qE U.εL i (U.cj i)) =
      Module.finrank R (LinearMap.range (Matrix.mulVecLin (U.εT i))) := by
    have hsumeq : ∑ i, Module.finrank R (LinearMap.range (Matrix.mulVecLin (U.εT i))) =
        ∑ i, Module.finrank R (qE U.εL i (U.cj i)) := by
      rw [hfT, ← hfQ]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hQrange i]
    intro i
    exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).1 hsumeq i (Finset.mem_univ i)).symm

  choose lam a y hlam hy horth hcpd hprod hspan using fun i =>
    block hv (Matrix.fromRows H.Ht (bt2 H U)) (U.εT i) (hTT i) (Pq i) (qE U.εL i (U.cj i)) (hPqmem i) (hPqid i) (hcomm i)
      (Module.finrank R (LinearMap.range (Matrix.mulVecLin (U.εT i)))) rfl (hnQ i) (X i) (hX i) cp (hcpi i)

  let n : Fin U.m → ℕ := fun i => Module.finrank R (LinearMap.range (Matrix.mulVecLin (U.εT i)))
  have hcard : Fintype.card (Ix g) = Fintype.card (Σ i, Fin (n i)) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact hfT.symm
  let e : Ix g ≃ Σ i, Fin (n i) := Fintype.equivOfCardEq hcard
  have hdot : ∀ s s' : Σ i, Fin (n i), lam s.1 s.2 ⬝ᵥ y s'.1 s'.2 = if s = s' then 1 else 0 := by
    rintro ⟨i, l⟩ ⟨i', l'⟩
    by_cases h : i = i'
    · subst h
      rw [horth i l l']
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    · have hne : (⟨i, l⟩ : Σ i, Fin (n i)) ≠ ⟨i', l'⟩ := fun hh => h (congrArg Sigma.fst hh)
      rw [if_neg hne]
      show lam i l ⬝ᵥ y i' l' = 0
      rw [← hlam i l, ← hy i' l', ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, U.εT_orth, if_neg h]
      simp
  have himg : ∀ i, Finset.univ.filter (fun j => (e j).1 = i) =
      Finset.univ.image (fun l : Fin (n i) => e.symm ⟨i, l⟩) := by
    intro i
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      generalize hs : e j = s at hj
      obtain ⟨i', l⟩ := s
      simp only at hj
      subst hj
      exact ⟨l, by rw [← hs, Equiv.symm_apply_apply]⟩
    · rintro ⟨l, rfl⟩
      simp
  have hinj : ∀ i, Function.Injective (fun l : Fin (n i) => e.symm ⟨i, l⟩) := by
    intro i l l' h
    have h' := congrArg e h
    simp only [Equiv.apply_symm_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h'
    exact h'
  have hae : ∀ s, a (e (e.symm s)).1 (e (e.symm s)).2 = a s.1 s.2 := fun s =>
    congrArg (fun t : Σ i, Fin (n i) => a t.1 t.2) (e.apply_symm_apply s)
  have hal : ∀ s, a (e (e.symm s)).1 (e (e.symm s)).2 • lam (e (e.symm s)).1 (e (e.symm s)).2 =
      a s.1 s.2 • lam s.1 s.2 := fun s =>
    congrArg (fun t : Σ i, Fin (n i) => a t.1 t.2 • lam t.1 t.2) (e.apply_symm_apply s)
  refine ⟨fun j => (e j).1, Matrix.of fun j => lam (e j).1 (e j).2, fun j => a (e j).1 (e j).2,
    ?_, fun j => hlam _ _, fun j => hcpd _ _, ?_, ?_, ?_⟩
  · apply Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun k j' => y (e j').1 (e j').2 k)
    ext j j'
    show lam (e j).1 (e j).2 ⬝ᵥ y (e j').1 (e j').2 = _
    rw [hdot, Matrix.one_apply]
    exact if_congr e.injective.eq_iff rfl rfl
  · intro i
    beta_reduce
    rw [himg i, Finset.prod_image (fun l _ l' _ h => hinj i h)]
    simp only [hae]
    exact hprod i
  · rintro i n' ⟨f⟩
    beta_reduce
    rw [himg i, Finset.card_image_of_injective _ (hinj i), Finset.card_univ, Fintype.card_fin]
    show Module.finrank R (LinearMap.range (Matrix.mulVecLin (U.εT i))) = n'
    rw [f.finrank_eq, Module.finrank_fin_fun]
  · intro i
    rw [hspan i]
    congr 1
    ext w
    simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq, Matrix.of_apply]
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨e.symm ⟨i, l⟩, by simp, hal ⟨i, l⟩⟩
    · rintro ⟨j, hj, rfl⟩
      change ∃ l', a i l' • lam i l' = a (e j).1 (e j).2 • lam (e j).1 (e j).2
      generalize e j = s at hj ⊢
      obtain ⟨i', l⟩ := s
      simp only at hj
      subst hj
      exact ⟨l, rfl⟩
end ReciprocityTheory.PGsh.Up
