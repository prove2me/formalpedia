-- Prove2me | solution 1 for SoSLinAlg.WeakRank.upper_bound_sec_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:19:27.351192+00:00
-- url     : https://prove2.me/submissions/bbc9834d-ac67-4270-a5a8-3c576de6d1e0

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_SoSRefutable
import Definitions.Def_SoSLinAlg_WeakRank_WRank

section
namespace SoSLinAlg.Dev.Minor

theorem exists_indep_cols {α β : Type*} [Fintype α] [Fintype β] {r : ℕ}
    (B : Matrix α β ℝ) (hB : r + 1 ≤ B.rank) :
    ∃ J : Fin (r + 1) → β, Function.Injective J ∧ LinearIndependent ℝ (fun j => B.col (J j)) := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ B.col
  have : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ = B.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, ← hspan]
    exact linearIndependent_iff_card_eq_finrank_span.mp hli
  have hle : r + 1 ≤ Fintype.card κ := hcard ▸ hB
  let e : Fin (r + 1) ↪ κ := (Fin.castLEEmb (by simpa using hle)).trans (Fintype.equivFin κ).symm.toEmbedding
  exact ⟨a ∘ e, ha.comp e.injective, hli.comp e e.injective⟩

theorem exists_minor {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : r + 1 ≤ A.rank) :
    ∃ (I J : Fin (r + 1) → Fin n), Function.Injective I ∧ Function.Injective J ∧
      (A.submatrix I J).det ≠ 0 := by
  obtain ⟨J, hJ, hli⟩ := exists_indep_cols A hA
  set C : Matrix (Fin n) (Fin (r + 1)) ℝ := A.submatrix id J with hC
  have hrank : C.transpose.rank = r + 1 := by
    have : LinearIndependent ℝ C.transpose.row := by
      convert hli using 1
      funext j; rfl
    simpa using this.rank_matrix
  obtain ⟨I, hI, hli2⟩ := exists_indep_cols C.transpose (by rw [hrank])
  refine ⟨I, J, hI, hJ, ?_⟩
  have h2 : LinearIndependent ℝ (C.submatrix I id).row := by
    convert hli2 using 1
    funext j; rfl
  have := Matrix.linearIndependent_rows_iff_isUnit.mp h2
  have h3 := (Matrix.isUnit_iff_isUnit_det _).mp this
  exact h3.ne_zero

end SoSLinAlg.Dev.Minor
end

section
noncomputable section

namespace SoSLinAlg.Dev.Cert

open MvPolynomial

theorem det_deg_aux {σ : Type*} {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n (MvPolynomial σ ℝ)) (d : n → ℕ)
    (h : ∀ a b, (N a b).totalDegree ≤ d a) : N.det.totalDegree ≤ ∑ a, d a := by
  rw [Matrix.det_apply]
  refine totalDegree_finsetSum_le (fun p _ => ?_)
  refine (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (N (p i) i).totalDegree ≤ ∑ i, d (p i) := Finset.sum_le_sum (fun i _ => h _ _)
    _ = ∑ a, d a := Equiv.sum_comp p d

theorem det_certificate {σ : Type*} {k : ℕ} (M : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ))
    (B : Matrix (Fin k) (Fin k) ℝ) (hM : ∀ a b, (M a b).totalDegree ≤ 2) :
    ∃ H : Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ),
      (∀ a b, (H a b).totalDegree ≤ 2 * (k - 1)) ∧
      M.det - C (B.det) = ∑ a, ∑ b, H a b * (M a b - C (B a b)) := by
  let Mj : ℕ → Matrix (Fin k) (Fin k) (MvPolynomial σ ℝ) :=
    fun j => Matrix.of fun a b => if b.val < j then M a b else C (B a b)
  have hdeg : ∀ j a b, (Mj j a b).totalDegree ≤ 2 := by
    intro j a b
    simp only [Mj, Matrix.of_apply]
    split_ifs
    · exact hM a b
    · simp
  refine ⟨fun a c => (Mj c.val).adjugate c a, ?_, ?_⟩
  · intro a c
    show ((Mj c.val).adjugate c a).totalDegree ≤ _
    rw [Matrix.adjugate_apply]
    refine (det_deg_aux _ (fun x => if x = a then 0 else 2) ?_).trans ?_
    · intro x y
      by_cases hx : x = a
      · subst hx
        simp only [Matrix.updateRow_self, if_true]
        simp [Pi.single_apply]
        split_ifs <;> simp
      · rw [Matrix.updateRow_ne hx]
        simp only [hx, if_false]
        exact hdeg _ _ _
    · have : ∑ x : Fin k, (if x = a then 0 else 2) = 2 * (k - 1) := by
        rw [← Finset.sum_erase _ (f := fun x => if x = a then 0 else 2) (a := a) (by simp)]
        rw [Finset.sum_congr rfl (g := fun _ => 2) (fun x hx => by simp [Finset.ne_of_mem_erase hx])]
        simp [Finset.card_erase_of_mem, mul_comm]
      exact this.le
  · have step : ∀ c : Fin k, (Mj (c.val + 1)).det - (Mj c.val).det
        = ∑ a, (Mj c.val).adjugate c a * (M a c - C (B a c)) := by
      intro c
      have e1 : Mj (c.val + 1) = (Mj c.val).updateCol c (fun a => M a c) := by
        ext a b
        by_cases hb : b = c
        · subst hb; simp [Mj]
        · have : b.val ≠ c.val := fun h => hb (Fin.ext h)
          simp only [Mj, Matrix.of_apply, Matrix.updateCol_ne hb]
          have : (b.val < c.val + 1) ↔ b.val < c.val := by omega
          simp [this]
      have e2 : Mj c.val = (Mj c.val).updateCol c (fun a => C (B a c)) := by
        ext a b
        by_cases hb : b = c
        · subst hb; simp [Mj]
        · simp [Matrix.updateCol_ne hb]
      have h1 : ∀ v : Fin k → MvPolynomial σ ℝ,
          ((Mj c.val).updateCol c v).det = (Matrix.mulVec (Mj c.val).adjugate v) c := by
        intro v
        rw [← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
      have h3 := h1 (fun a => C (B a c))
      rw [← e2] at h3
      rw [e1, h1, h3]
      simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
    have hk : Mj k = M := by
      ext a b; simp [Mj, b.isLt]
    have h0 : (Mj 0).det = C B.det := by
      have : Mj 0 = (C : ℝ →+* MvPolynomial σ ℝ).mapMatrix B := by
        ext a b; simp [Mj]
      rw [this, ← RingHom.map_det]
    rw [Finset.sum_comm]
    have := Finset.sum_range_sub (fun j => (Mj j).det) k
    rw [hk, h0] at this
    rw [← this, ← Fin.sum_univ_eq_sum_range (fun j => (Mj (j + 1)).det - (Mj j).det) k]
    exact Finset.sum_congr rfl (fun c _ => step c)

end SoSLinAlg.Dev.Cert
end
end

section
noncomputable section

namespace SoSLinAlg.Dev.Upper

open MvPolynomial SoSLinAlg.WeakRank

theorem xy_deg {n r : ℕ} (i j : Fin n) : (xy (r := r) i j).totalDegree ≤ 2 := by
  refine totalDegree_finsetSum_le fun k _ => (totalDegree_mul _ _).trans ?_
  simp [x, y, totalDegree_X]

theorem upper {n r : ℕ} (hr : 0 < r) (hrn : r < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : r + 1 ≤ A.rank) :
    SoSRefutable (WRank r A) (2 * r + 2) := by
  classical
  obtain ⟨I, J, hI, hJ, hdet⟩ := SoSLinAlg.Dev.Minor.exists_minor A hA
  set B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := A.submatrix I J with hB
  set M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Poly n r) := fun a b => xy (I a) (J b) with hM
  have hMdeg : ∀ a b, (M a b).totalDegree ≤ 2 := fun a b => xy_deg _ _
  -- det M = 0
  have hdM : M.det = 0 := by
    let P : Matrix (Fin (r + 1)) (Fin (r + 1)) (Poly n r) :=
      fun a c => if h : c.val < r then x (I a) ⟨c, h⟩ else 0
    let Q : Matrix (Fin (r + 1)) (Fin (r + 1)) (Poly n r) :=
      fun c b => if h : c.val < r then y (J b) ⟨c, h⟩ else 0
    have hPQ : M = P * Q := by
      refine Matrix.ext fun a b => ?_
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      simp [hM, xy, P, Q]
    have hP : P.det = 0 := by
      refine Matrix.det_eq_zero_of_column_eq_zero (Fin.last r) fun a => ?_
      simp [P]
    rw [hPQ, Matrix.det_mul, hP, zero_mul]
  obtain ⟨H, hHdeg, hH⟩ := SoSLinAlg.Dev.Cert.det_certificate M B hMdeg
  rw [hdM, zero_sub] at hH
  set db := B.det with hdb
  set F : Fin (r + 1) × Fin (r + 1) → Poly n r := fun p => C (db⁻¹) * H p.1 p.2 with hF
  have hFeq : (-1 : Poly n r) = ∑ p, F p * WRank r A (I p.1, J p.2) := by
    have : (-1 : Poly n r) = C (db⁻¹) * (- C db) := by
      rw [← map_neg, ← map_mul, mul_neg, inv_mul_cancel₀ hdet]; simp
    rw [this, hH, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hF, WRank, hM, hB, Matrix.submatrix_apply]
    ring
  let e : Fin (r + 1) × Fin (r + 1) → Fin n × Fin n := fun p => (I p.1, J p.2)
  have he : Function.Injective e := by
    intro p q h
    simp only [e, Prod.mk.injEq] at h
    exact Prod.ext (hI h.1) (hJ h.2)
  set G : Fin n × Fin n → Poly n r := Function.extend e F 0 with hG
  have hGe : ∀ p, G (e p) = F p := fun p => he.extend_apply _ _ _
  have hGdeg : ∀ q, G q = 0 ∨ (G q).totalDegree ≤ 2 * r := by
    intro q
    by_cases hq : ∃ p, e p = q
    · obtain ⟨p, rfl⟩ := hq
      right
      rw [hGe]
      refine (totalDegree_mul _ _).trans ?_
      have := hHdeg p.1 p.2
      simp [totalDegree_C]
      omega
    · left
      rw [hG, Function.extend_apply' _ _ _ hq]; rfl
  refine ⟨0, G, IsSumSq.zero, by simp, fun q => ?_, ?_⟩
  · rcases hGdeg q with h0 | h0
    · simp [h0]
    · refine (totalDegree_mul _ _).trans ?_
      have : (WRank r A q).totalDegree ≤ 2 := by
        refine (totalDegree_sub _ _).trans (max_le (xy_deg _ _) (by simp [totalDegree_C]))
      omega
  · rw [zero_add, hFeq]
    symm
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e))]
    · rw [Finset.sum_image (fun p _ q _ h => he h)]
      exact Finset.sum_congr rfl fun p _ => by rw [hGe]
    · intro q _ hq
      have : ¬ ∃ p, e p = q := by simpa using hq
      rw [hG, Function.extend_apply' _ _ _ this]; simp

end SoSLinAlg.Dev.Upper
end
end

section
namespace SoSLinAlg.WeakRank

theorem chk_upper_bound_sec_4_1 {n r : ℕ} (hr : 0 < r) (hrn : r < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : r + 1 ≤ A.rank) :
    SoSRefutable (WRank r A) (2 * r + 2) :=
  SoSLinAlg.Dev.Upper.upper hr hrn A hA

end SoSLinAlg.WeakRank
end

theorem solution : type_of% @SoSLinAlg.WeakRank.chk_upper_bound_sec_4_1 := @SoSLinAlg.WeakRank.chk_upper_bound_sec_4_1
