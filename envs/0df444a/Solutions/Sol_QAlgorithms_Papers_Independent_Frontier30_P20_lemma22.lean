-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P20.lemma22
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:47:22.542704+00:00
-- url     : https://prove2.me/submissions/3a7827ed-301d-44dd-8ea0-1f8adba3b692

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P20
noncomputable section
set_option linter.unusedSimpArgs false

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer)

open QAlgorithms.Papers.Independent.Dependency50.P14 (Super)

lemma S200L_two_apply (K L X : Mat 2) : twoSidedMap K L X = K * X * L := by
  simp [twoSidedMap, QAlgorithms.Papers.Independent.Dependency50.P16.sandwich, Matrix.mul_assoc]

lemma S200L_cc_outer (a b v : Fin 2 → ℂ) (x : ℝ) :
    canonicalChannel a b x (outer v v) =
      outer ![conj (a 0) * v 0 + conj (a 1) * v 1, 0] ![conj (a 0) * v 0 + conj (a 1) * v 1, 0] +
      outer ![conj (b 0) * v 0 + conj (b 1) * v 1, (x : ℂ) * v 1]
        ![conj (b 0) * v 0 + conj (b 1) * v 1, (x : ℂ) * v 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalChannel, S200L_two_apply, outer, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring


lemma S200L_cp_two (K : Mat 2) :
    QAlgorithms.Entanglement.IsCompletelyPositive (twoSidedMap K Kᴴ).toLinearMap := by
  intro r Xb hXb
  have h : QAlgorithms.idTensorSuperop (⇑((twoSidedMap K Kᴴ : Super 2) : Mat 2 →ₗ[ℂ] Mat 2)) Xb =
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin r) (Fin r) ℂ) K * Xb *
        (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin r) (Fin r) ℂ) K)ᴴ := by
    ext p q
    simp only [QAlgorithms.idTensorSuperop, ContinuousLinearMap.coe_coe, S200L_two_apply,
      Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Matrix.conjTranspose_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, star_mul', apply_ite star, star_one, star_zero,
      mul_ite, mul_one, mul_zero]
    simp [Finset.sum_mul]
  rw [h]
  exact hXb.mul_mul_conjTranspose_same _

lemma S200L_cp_add (Φ Ψ : Mat 2 →ₗ[ℂ] Mat 2)
    (hΦ : QAlgorithms.Entanglement.IsCompletelyPositive Φ)
    (hΨ : QAlgorithms.Entanglement.IsCompletelyPositive Ψ) :
    QAlgorithms.Entanglement.IsCompletelyPositive (Φ + Ψ) := by
  intro r X hX
  have : QAlgorithms.idTensorSuperop (⇑(Φ + Ψ)) X =
      QAlgorithms.idTensorSuperop Φ X + QAlgorithms.idTensorSuperop Ψ X := by
    ext p q; rfl
  rw [this]; exact (hΦ r X hX).add (hΨ r X hX)

lemma S200L_channel (a b : Fin 2 → ℂ) (x : ℝ) (h : CanonicalData a b x) :
    Channel (canonicalChannel a b x) := by
  refine ⟨?_, ?_⟩
  · simp only [Cone, if_true]
    exact S200L_cp_add _ _ (S200L_cp_two _) (S200L_cp_two _)
  · obtain ⟨-, -, h⟩ := h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp [outer] at h00 h01 h10 h11
    intro X
    simp [canonicalChannel, S200L_two_apply, outer, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.trace_fin_two]
    linear_combination X 0 0 * h00 + X 0 1 * h10 + X 1 0 * h01 + X 1 1 * h11

def S200L_V (a b : Fin 2 → ℂ) (x : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ := fun p k =>
    (![outer ![1,0] a, outer ![1,0] b + (x : ℂ) • outer ![0,1] ![0,1]] k) p.1 p.2

lemma S200L_rank (a b : Fin 2 → ℂ) (x : ℝ) (ha : a 0 ≠ 0) (hx : x ≠ 0) :
    krausRank (canonicalChannel a b x) = 2 := by
  set V := S200L_V a b x with hV
  have hJ : jamiolkowskiState (canonicalChannel a b x) = ((2 : ℂ)⁻¹ • V) * Vᴴ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [jamiolkowskiState, QAlgorithms.Papers.Independent.Information100.P50.choiMatrix,
        canonicalChannel, S200L_two_apply, outer, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, V, S200L_V, Fintype.sum_prod_type, Matrix.single_apply] <;> ring
  unfold krausRank
  apply le_antisymm
  · rw [hJ]
    calc _ ≤ ((2 : ℂ)⁻¹ • V).rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin 2) := Matrix.rank_le_card_width _
      _ = 2 := by simp
  · let f : Fin 2 → Fin 2 × Fin 2 := ![(0,0), (1,1)]
    have hsub := Matrix.rank_submatrix_le (jamiolkowskiState (canonicalChannel a b x)) f f
    refine le_trans (le_of_eq ?_) hsub
    rw [Matrix.rank_of_isUnit]
    · simp
    · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_two, hJ]
      simp [f, V, S200L_V, Matrix.mul_apply, Fin.sum_univ_two, outer, Matrix.conjTranspose_apply,
        Fintype.sum_prod_type]
      have hc : (starRingEnd ℂ) (a 0) * a 0 ≠ 0 := mul_ne_zero ((map_ne_zero _).2 ha) ha
      have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
      intro h0
      apply mul_ne_zero (mul_ne_zero hc (mul_ne_zero hx' hx')) (by norm_num : (4 : ℂ)⁻¹ ≠ 0)
      linear_combination h0


def S200L_a (p s c1 : ℝ) (ω : ℂ) : Fin 2 → ℂ := ![(p : ℂ), -(p : ℂ) * s * conj ω / c1]

def S200L_b (s t c1 : ℝ) (ω : ℂ) : Fin 2 → ℂ := ![((s / t : ℝ) : ℂ), ((t : ℂ) - s * s / t) * conj ω / c1]

lemma S200L_cd (p s t c1 x : ℝ) (ω : ℂ) (hω : conj ω * ω = 1) (hc : c1 ≠ 0) (ht : t ≠ 0)
    (hs2 : s ^ 2 = 1 - c1 ^ 2) (ht2 : t ^ 2 = 1 - (x * c1) ^ 2) (hp2 : p ^ 2 * t ^ 2 = t ^ 2 - s ^ 2) :
    CanonicalData (S200L_a p s c1 ω) (S200L_b s t c1 ω) x := by
  have hc' : (c1 : ℂ) ≠ 0 := by exact_mod_cast hc
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hs2' : (s : ℂ) ^ 2 = 1 - (c1 : ℂ) ^ 2 := by exact_mod_cast hs2
  have ht2' : (t : ℂ) ^ 2 = 1 - ((x : ℂ) * c1) ^ 2 := by exact_mod_cast ht2
  have hp2' : (p : ℂ) ^ 2 * t ^ 2 = t ^ 2 - s ^ 2 := by exact_mod_cast hp2
  refine ⟨by simp [S200L_a], by simp [S200L_b], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S200L_a, S200L_b, outer] <;> field_simp
  · linear_combination hp2'
  · linear_combination (-((s : ℂ) * ω)) * hp2'
  · linear_combination (-((s : ℂ) * conj ω)) * hp2'
  · linear_combination ((p : ℂ) ^ 2 * s ^ 2 * t ^ 2 + (t ^ 2 - s ^ 2) ^ 2) * hω + (s : ℂ) ^ 2 * hp2' +
      (t : ℂ) ^ 2 * (ht2' - hs2')

lemma S200L_out (p s t c1 x : ℝ) (ω : ℂ) (hc : c1 ≠ 0) (ht : t ≠ 0) :
    canonicalChannel (S200L_a p s c1 ω) (S200L_b s t c1 ω) x (outer ![(s : ℂ) * ω, (c1 : ℂ)] ![(s : ℂ) * ω, (c1 : ℂ)]) =
      outer ![(t : ℂ) * ω, ((x * c1 : ℝ) : ℂ)] ![(t : ℂ) * ω, ((x * c1 : ℝ) : ℂ)] := by
  have hc' : (c1 : ℂ) ≠ 0 := by exact_mod_cast hc
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [S200L_cc_outer]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h1 : conj (S200L_a p s c1 ω 0) * ((s : ℂ) * ω) + conj (S200L_a p s c1 ω 1) * c1 = 0 := by
    simp [S200L_a]; field_simp; ring
  have h2 : conj (S200L_b s t c1 ω 0) * ((s : ℂ) * ω) + conj (S200L_b s t c1 ω 1) * c1 = t * ω := by
    simp [S200L_b]; field_simp; ring
  rw [h1, h2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [outer]

lemma S200L_neg (a b : Fin 2 → ℂ) (x : ℝ) : canonicalChannel (-a) b x = canonicalChannel a b x := by
  refine ContinuousLinearMap.ext fun X => ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalChannel, S200L_two_apply, outer, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring


lemma S200L_uniq (p s t c1 x x' : ℝ) (ω : ℂ) (a b : Fin 2 → ℂ) (hω : conj ω * ω = 1)
    (hc : 0 < c1) (ht : 0 < t) (hx : 0 < x) (hx' : 0 < x') (_hp : 0 < p)
    (hp2 : p ^ 2 * t ^ 2 = t ^ 2 - s ^ 2)
    (hcd : CanonicalData a b x')
    (heq : canonicalChannel a b x' (outer ![(s : ℂ) * ω, (c1 : ℂ)] ![(s : ℂ) * ω, (c1 : ℂ)]) =
      outer ![(t : ℂ) * ω, ((x * c1 : ℝ) : ℂ)] ![(t : ℂ) * ω, ((x * c1 : ℝ) : ℂ)]) :
    canonicalChannel a b x' = canonicalChannel (S200L_a p s c1 ω) (S200L_b s t c1 ω) x := by
  rw [S200L_cc_outer] at heq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at heq
  set α := conj (a 0) * ((s : ℂ) * ω) + conj (a 1) * c1 with hα
  set β := conj (b 0) * ((s : ℂ) * ω) + conj (b 1) * c1 with hβ
  have e00 := congrFun (congrFun heq 0) 0
  have e01 := congrFun (congrFun heq 0) 1
  have e11 := congrFun (congrFun heq 1) 1
  simp [outer] at e00 e01 e11
  have hc' : (c1 : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hxx : x' = x := by
    have h1 : ((x' * c1) ^ 2 : ℝ) = (x * c1) ^ 2 := by
      have : (((x' * c1) ^ 2 : ℝ) : ℂ) = (((x * c1) ^ 2 : ℝ) : ℂ) := by
        push_cast; linear_combination e11
      exact_mod_cast this
    have h2 : x' * c1 = x * c1 :=
      (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 h1
    exact mul_right_cancel₀ hc.ne' h2
  subst hxx
  have hxc : (x' : ℂ) * c1 ≠ 0 := mul_ne_zero (by exact_mod_cast hx'.ne') hc'
  have hb : β = t * ω := mul_right_cancel₀ hxc e01
  have ha : α = 0 := by
    have h : α * conj α = 0 := by
      rw [hb, map_mul, Complex.conj_ofReal] at e00
      linear_combination e00
    rw [Complex.mul_conj] at h
    exact_mod_cast (Complex.normSq_eq_zero.1 (by exact_mod_cast h))
  obtain ⟨ha0, hb0, hM⟩ := hcd
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  simp [outer] at h00 h01
  set u := (a 0).re
  set v := (b 0).re
  have hu : a 0 = u := Complex.ext rfl (by simpa using ha0)
  have hv : b 0 = v := Complex.ext rfl (by simpa using hb0)
  rw [hu, hv] at h00 h01
  rw [hα, hu] at ha
  rw [hβ, hv] at hb
  simp at ha hb h00 h01
  have hω0 : ω ≠ 0 := by
    rintro rfl; simp at hω
  have hvt : (v : ℂ) * t = s := by
    have : ω * ((v : ℂ) * t - s) = 0 := by
      linear_combination (c1 : ℂ) * h01 - (u : ℂ) * ha - (v : ℂ) * hb + (s : ℂ) * ω * h00
    have := (mul_eq_zero.1 this).resolve_left hω0
    linear_combination this
  have hvr : v = s / t := by
    have : v * t = s := by exact_mod_cast hvt
    field_simp; linarith
  have hur : u = p ∨ u = -p := by
    have h00r : u * u + v * v = 1 := by exact_mod_cast h00
    have : u ^ 2 = p ^ 2 := by
      have : u ^ 2 * t ^ 2 = p ^ 2 * t ^ 2 := by
        rw [hp2, hvr] at *; field_simp at h00r ⊢; linarith
      exact mul_right_cancel₀ (by positivity) this
    exact sq_eq_sq_iff_eq_or_eq_neg.1 this
  have ha' := congrArg conj ha
  have hb' := congrArg conj hb
  simp at ha' hb'
  have hbS : b = S200L_b s t c1 ω := by
    funext i; fin_cases i
    · simp [S200L_b, hv, hvr]
    · simp [S200L_b]
      field_simp
      rw [hvr] at hb'
      push_cast at hb'
      field_simp at hb'
      linear_combination hb'
  rw [hbS]
  rcases hur with hup | hun
  · have haS : a = S200L_a p s c1 ω := by
      funext i; fin_cases i
      · simp [S200L_a, hu, hup]
      · simp [S200L_a]
        field_simp
        rw [hup] at ha'
        linear_combination ha'
    rw [haS]
  · have haS : a = -S200L_a p s c1 ω := by
      funext i; fin_cases i
      · simp [S200L_a, hu, hun]
      · simp [S200L_a]
        field_simp
        rw [hun] at ha'
        push_cast at ha'
        linear_combination ha'
    rw [haS, S200L_neg]

end QAlgorithms.Papers.Independent.Frontier30.P20

open QAlgorithms.Papers.Independent.Frontier30.P20 in
open QAlgorithms.Papers.Independent.Information100.P26 (Mat outer) in
open QAlgorithms.Papers.Independent.Dependency50.P14 (Super) in
theorem solution (c1 x phi : ℝ) (hc0 : 0 < c1) (hc1 : c1 < 1)
    (hx0 : 0 < x) (hx1 : x < 1) (hphi0 : 0 ≤ phi) (hphi1 : phi < 2 * Real.pi) :
    ∃! T : Super 2, ClassThree T ∧
      T (outer (classInput c1 phi) (classInput c1 phi)) =
        outer (classOutput c1 x phi) (classOutput c1 x phi) := by
  set s := Real.sqrt (1 - c1 ^ 2) with hs_def
  set t := Real.sqrt (1 - (x * c1) ^ 2) with ht_def
  set p := Real.sqrt (1 - (s / t) ^ 2) with hp_def
  set ω := Complex.exp (Complex.I * (phi : ℂ)) with hω_def
  have hxc : x * c1 < 1 := by nlinarith
  have hxc0 : 0 < x * c1 := mul_pos hx0 hc0
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - c1 ^ 2 := Real.sq_sqrt (by nlinarith)
  have ht2 : t ^ 2 = 1 - (x * c1) ^ 2 := Real.sq_sqrt (by nlinarith [mul_pos hxc0 hxc0])
  have ht : 0 < t := Real.sqrt_pos.2 (by nlinarith [mul_pos hxc0 hxc0])
  have hst : s ^ 2 < t ^ 2 := by
    rw [hs2, ht2]; nlinarith [mul_pos hc0 hc0, mul_pos (mul_pos hc0 hc0) (sub_pos.2 hx1)]
  have hlt : (s / t) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity)]; exact hst
  have hp : 0 < p := Real.sqrt_pos.2 (by linarith)
  have hp2 : p ^ 2 * t ^ 2 = t ^ 2 - s ^ 2 := by
    rw [hp_def, Real.sq_sqrt (by linarith)]
    field_simp
  have hω : conj ω * ω = 1 := by
    rw [Complex.conj_mul']
    simp [hω_def, Complex.norm_exp]
  have hin : classInput c1 phi = ![(s : ℂ) * ω, (c1 : ℂ)] := rfl
  have hout : classOutput c1 x phi = ![(t : ℂ) * ω, ((x * c1 : ℝ) : ℂ)] := rfl
  rw [hin, hout]
  have hcd := S200L_cd p s t c1 x ω hω hc0.ne' ht.ne' hs2 ht2 hp2
  have ha0 : S200L_a p s c1 ω 0 ≠ 0 := by
    simp [S200L_a]; exact hp.ne'
  refine ⟨canonicalChannel (S200L_a p s c1 ω) (S200L_b s t c1 ω) x,
    ⟨⟨S200L_channel _ _ _ hcd, S200L_rank _ _ _ ha0 hx0.ne',
      S200L_a p s c1 ω, S200L_b s t c1 ω, x, hcd, rfl, ha0, hx0, hx1⟩,
      S200L_out p s t c1 x ω hc0.ne' ht.ne'⟩, ?_⟩
  rintro T ⟨⟨-, -, a, b, x', hcd', rfl, -, hx'0, -⟩, heq⟩
  exact S200L_uniq p s t c1 x x' ω a b hω hc0 ht hx0 hx'0 hp hp2 hcd' heq

end
