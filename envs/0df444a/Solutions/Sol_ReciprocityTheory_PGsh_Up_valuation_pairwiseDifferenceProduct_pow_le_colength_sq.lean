-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.valuation_pairwiseDifferenceProduct_pow_le_colength_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:22:29.249259+00:00
-- url     : https://prove2.me/submissions/67cf081b-695d-4021-8480-8e2733dbc2d7

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS
import Theorems.Thm_ReciprocityTheory_PGsh_Up_DeterminantValuationBounds_exists_generic
import Theorems.Thm_ReciprocityTheory_PGsh_Up_DeterminantValuationBounds_pow_stable
import Theorems.Thm_ReciprocityTheory_PGsh_Up_DeterminantValuationBounds_v_det_le_of_cols
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_Lat_isUnit_det
import Theorems.Thm_ReciprocityTheory_PGsh_Lat_v_det_eq_of_pts_eq
import Theorems.Thm_ReciprocityTheory_PGsh_isIntegralVec_single


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
open DeterminantValuationBounds
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (n : ℕ)
    (a : Fin n → C) (s : ℕ) (M S : Lat v (Fin n × Fin s)) (Mτ : Fin n → Lat v (Fin s))
    (hM : IsLaStable a M) (hτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ) (hS : S.pts = sumPts Mτ) :
    v (discr a) ^ s ≤ colen M S ^ 2 := by
  classical
  have v_discr : v (discr a) = v (Matrix.vandermonde a).det ^ 2 := by
    rw [Matrix.det_vandermonde, discr, sq]
    simp only [map_prod]
    have hsplit : ∀ τ : Fin n, ∏ τ' ∈ Finset.univ.erase τ, v (a τ - a τ') =
        (∏ τ' ∈ Finset.Ioi τ, v (a τ' - a τ)) * ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') := by
      intro τ
      have hu : Finset.univ.erase τ = Finset.Ioi τ ∪ Finset.Iio τ := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
          Finset.mem_Iio]
        constructor
        · intro h
          rcases lt_or_gt_of_ne h with h | h
          · exact Or.inr h
          · exact Or.inl h
        · rintro (h | h)
          · exact ne_of_gt h
          · exact ne_of_lt h
      rw [hu, Finset.prod_union (Finset.disjoint_left.mpr fun x h1 h2 => by
        simp only [Finset.mem_Ioi, Finset.mem_Iio] at h1 h2
        exact lt_asymm h1 h2)]
      congr 1
      exact Finset.prod_congr rfl fun x _ => Valuation.map_sub_swap _ _ _
    rw [Finset.prod_congr rfl fun τ _ => hsplit τ, Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_comm' (by intro x y; simp only [Finset.mem_univ, Finset.mem_Iio,
      Finset.mem_Ioi, true_and, and_true])
  have v_det_sum : v S.B.det = ∏ τ, v (Mτ τ).B.det := by
    let Bb : Matrix (Fin n × Fin s) (Fin n × Fin s) C :=
      Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
        (Matrix.blockDiagonal fun τ => (Mτ τ).B)
    have hdet : Bb.det = ∏ τ, (Mτ τ).B.det := by
      simp only [Bb, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    let Sb : Lat v (Fin n × Fin s) :=
      ⟨Bb, by rw [hdet]; exact Finset.prod_ne_zero_iff.mpr fun τ _ => (Mτ τ).det_ne⟩
    have hmv : ∀ (c : Fin n × Fin s → C) (τ : Fin n) (i : Fin s),
        (Bb *ᵥ c) (τ, i) = ((Mτ τ).B *ᵥ fun j => c (τ, j)) i := by
      intro c τ i
      simp only [Bb, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.reindex_apply,
        Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
        Matrix.blockDiagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_eq_single τ (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    have hpts : Sb.pts = sumPts Mτ := by
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩ τ
        refine ⟨fun j => c (τ, j), fun j => hc (τ, j), ?_⟩
        ext i
        exact hmv c τ i
      · intro hx
        choose cτ hcτ hxτ using hx
        refine ⟨fun p => cτ p.1 p.2, fun p => hcτ p.1 p.2, ?_⟩
        ext ⟨τ, i⟩
        show x (τ, i) = (Bb *ᵥ fun p => cτ p.1 p.2) (τ, i)
        rw [hmv]
        exact congrFun (hxτ τ) i
    calc v S.B.det = v Sb.B.det := Lat.v_det_eq_of_pts_eq (hS.trans hpts.symm)
      _ = ∏ τ, v (Mτ τ).B.det := by
        show v Bb.det = _
        rw [hdet, map_prod]
  let R : Fin n → Matrix (Fin s) (Fin n × Fin s) C := fun τ => Matrix.of fun i y => M.B (τ, i) y
  let Q : Fin n → Matrix (Fin s) (Fin n × Fin s) C := fun τ => (Mτ τ).B⁻¹ * R τ
  have hB : ∀ τ, (Mτ τ).B⁻¹ * (Mτ τ).B = 1 := fun τ => Matrix.nonsing_inv_mul _ (Mτ τ).isUnit_det
  have hB' : ∀ τ, (Mτ τ).B * (Mτ τ).B⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (Mτ τ).isUnit_det
  have hproj : ∀ τ (w : Fin n × Fin s → C), w ∈ M.pts → (fun i => w (τ, i)) ∈ (Mτ τ).pts := by
    intro τ w hw
    rw [hτ τ]
    exact ⟨w, hw, rfl⟩
  have hcolM : ∀ (c : Fin n × Fin s → C), IsIntegralVec v c → M.B *ᵥ c ∈ M.pts :=
    fun c hc => ⟨c, hc, rfl⟩
  have hQint : ∀ τ i y, v (Q τ i y) ≤ 1 := by
    intro τ i y
    have hcol : M.B *ᵥ Pi.single y 1 ∈ M.pts := hcolM _ (isIntegralVec_single y)
    obtain ⟨c, hc, hce⟩ := hproj τ _ hcol
    have hQc : (fun i => Q τ i y) = c := by
      have h1 : (fun i => Q τ i y) = (Mτ τ).B⁻¹ *ᵥ (fun i => (M.B *ᵥ Pi.single y 1) (τ, i)) := by
        ext i
        simp [Q, R, Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [h1, hce, Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
    have := hc i
    rw [← hQc] at this
    exact this
  have hsec : ∀ τ, ∃ d : Matrix (Fin n × Fin s) (Fin s) C, (∀ r i, v (d r i) ≤ 1) ∧ Q τ * d = 1 := by
    intro τ
    have hmem : ∀ j, (fun i => (Mτ τ).B i j) ∈ projPts M.pts τ := by
      intro j
      rw [← hτ τ]
      refine ⟨Pi.single j 1, isIntegralVec_single j, ?_⟩
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    choose w hw hwe using hmem
    choose d hd hde using hw
    refine ⟨Matrix.of fun r j => d j r, fun r j => hd j r, ?_⟩
    have hRd : R τ * (Matrix.of fun r j => d j r) = (Mτ τ).B := by
      ext i j
      have h1 : w j (τ, i) = (Mτ τ).B i j := congrFun (hwe j) i
      rw [hde j] at h1
      rw [← h1]
      simp [R, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    show (Mτ τ).B⁻¹ * R τ * _ = 1
    rw [Matrix.mul_assoc, hRd, hB]
  obtain ⟨c, hcint, hcdet⟩ := exists_generic Q (fun τ i y => hQint τ i y) hsec
  let X : Matrix (Fin n × Fin s) (Fin n × Fin s) C :=
    Matrix.of fun x y => a x.1 ^ (y.1 : ℕ) * (M.B * c) x y.2
  have hXcols : ∀ y, (fun x => X x y) ∈ M.pts := by
    intro y
    have hw : (fun x => (M.B * c) x y.2) ∈ M.pts := by
      refine ⟨fun r => c r y.2, fun r => hcint r y.2, ?_⟩
      ext x
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    exact pow_stable hM y.1 hw
  have hle : v X.det ≤ v M.B.det := v_det_le_of_cols M X hXcols
  let G : Fin n → Matrix (Fin s) (Fin s) C := fun τ => (Mτ τ).B * (Q τ * c)
  have hG : ∀ τ i j, (M.B * c) (τ, i) j = G τ i j := by
    intro τ i j
    show _ = ((Mτ τ).B * ((Mτ τ).B⁻¹ * R τ * c)) i j
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hB', Matrix.one_mul]
    simp [R, Matrix.mul_apply]
  have hfree : freeMat a s = Matrix.blockDiagonal fun _ : Fin s => Matrix.vandermonde a := by
    ext x y
    simp [freeMat, Matrix.blockDiagonal_apply, Matrix.vandermonde_apply]
  have hXfac : X = Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (Matrix.blockDiagonal G) * freeMat a s := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [X, Matrix.of_apply, hG, freeMat, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap, Matrix.blockDiagonal_apply]
    simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    ring
  have hGdet : ∀ τ, v (G τ).det = v (Mτ τ).B.det := by
    intro τ
    simp only [G, Matrix.det_mul, map_mul, hcdet τ, mul_one]
  have hdetX : v X.det = (∏ τ, v (Mτ τ).B.det) * v (Matrix.vandermonde a).det ^ s := by
    rw [hXfac, Matrix.det_mul, Matrix.det_reindex_self, Matrix.det_blockDiagonal, hfree,
      Matrix.det_blockDiagonal, map_mul, map_prod, map_prod]
    simp only [hGdet, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hSdet := v_det_sum
  have hSpos : 0 < v S.B.det := by
    rw [pos_iff_ne_zero, Ne, map_eq_zero]
    exact S.det_ne
  have hcol : v (Matrix.vandermonde a).det ^ s ≤ colen M S := by
    rw [colen, le_div_iff₀ hSpos, hSdet, mul_comm, ← hdetX]
    exact hle
  rw [v_discr, ← pow_mul, mul_comm 2 s, pow_mul]
  exact pow_le_pow_left₀ zero_le hcol 2
end ReciprocityTheory.PGsh.Up
