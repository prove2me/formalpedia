-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P12.gkls_notFullyInvariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:48:20.27763+00:00
-- url     : https://prove2.me/submissions/199e86eb-b8d1-40bb-af8f-60491cd9e283

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P12
open scoped Matrix ComplexOrder Matrix.Norms.Frobenius
open Set
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Classical.propDecidable Classical.decEq
open Coordinates
open QAlgorithms.Papers.Independent.Information100
attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.inheritedSubalgebraTopologicalAddGroup

lemma S170bO_app {d : ℕ} (t : Super d) (Y : P59.Operator d) (i j : Fin d) :
    P26.applyMap t Y i j = ∑ q : Fin d × Fin d, t (i, j) q * Y q.1 q.2 := by
  simp [P26.applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

lemma S170bO_sup {d : ℕ} (f : P59.Operator d →ₗ[ℂ] P59.Operator d) :
    P26.applyMap (superOfAction f) = f := by
  funext Y
  ext i j
  have hY : Y = ∑ q : Fin d × Fin d, Y q.1 q.2 • Matrix.single q.1 q.2 (1 : ℂ) := by
    conv_lhs => rw [Y.matrix_eq_sum_single]
    rw [Fintype.sum_prod_type]
    simp
  calc P26.applyMap (superOfAction f) Y i j = ∑ q : Fin d × Fin d, f (Matrix.single q.1 q.2 1) i j * Y q.1 q.2 := by
        rw [S170bO_app]; rfl
    _ = f Y i j := by
        conv_rhs => rw [hY]
        simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

lemma S170bO_supapp {d : ℕ} (M : Super d) : superOfAction (P26.applyMap M) = M := by
  ext p q
  simp only [superOfAction, S170bO_app]
  rw [Finset.sum_eq_single q]
  · simp
  · intro r _ hr
    have : ¬(q.1 = r.1 ∧ q.2 = r.2) := fun h => hr (Prod.ext h.1.symm h.2.symm)
    simp [Matrix.single_apply, this]
  · simp

lemma S170bO_mul {d : ℕ} (A B : Super d) (Y : P59.Operator d) :
    P26.applyMap (A * B) Y = P26.applyMap A (P26.applyMap B Y) := by
  ext i j
  show ((A * B) *ᵥ _) (i, j) = (A *ᵥ (B *ᵥ _)) (i, j)
  rw [Matrix.mulVec_mulVec]

lemma S170bO_add {d : ℕ} (A B : Super d) (Y : P59.Operator d) :
    P26.applyMap (A + B) Y = P26.applyMap A Y + P26.applyMap B Y := by
  ext i j; simp [S170bO_app, add_mul, Finset.sum_add_distrib]

lemma S170bO_sub {d : ℕ} (A B : Super d) (Y : P59.Operator d) :
    P26.applyMap (A - B) Y = P26.applyMap A Y - P26.applyMap B Y := by
  ext i j; simp [S170bO_app, sub_mul, Finset.sum_sub_distrib]

lemma S170bO_zero {d : ℕ} (A : Super d) : P26.applyMap A 0 = 0 := by
  ext i j; simp [S170bO_app]

lemma S170bO_smulR {d : ℕ} (r : ℝ) (A : Super d) (Y : P59.Operator d) :
    P26.applyMap (r • A) Y = (r : ℂ) • P26.applyMap A Y := by
  ext i j; simp [S170bO_app, Finset.mul_sum, mul_assoc]

lemma S170bO_pos {d : ℕ} (F : Fin (d^2-1) → P59.Operator d) (H : P59.Operator d)
    (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) (hK : K.PosSemidef) (i0 i1 : Fin d) (h01 : i0 ≠ i1) :
    0 ≤ P59.kossakowskiAction F H K (Matrix.single i0 i0 1) i1 i1 := by
  set b : Fin (d^2-1) → ℂ := fun k => star (F k i1 i0)
  have hv : P59.kossakowskiAction F H K (Matrix.single i0 i0 1) i1 i1 = star b ⬝ᵥ (K *ᵥ b) := by
    simp only [P59.kossakowskiAction, P59.coherent, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, smul_eq_mul]
    simp [h01, dotProduct, Matrix.mulVec, b, Finset.mul_sum, ite_and, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hv]; exact hK.dotProduct_mulVec_nonneg b


theorem solution {d : ℕ} (hd : 2 ≤ d)
    (F : Fin (d^2-1) → P59.Operator d) (hF : P59.IsTracelessHermitianBasis F)
    (horth : P59.gramMatrix F = 1) :
    ∃ X L : Super d, LK X ∧ P59.IsPhysicalAction F (P26.applyMap L) ∧ ¬ P59.IsPhysicalAction F (P26.applyMap (expAd X L)) := by
  set i0 : Fin d := ⟨0, by omega⟩
  set i1 : Fin d := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  set E : Fin d → Fin d → P59.Operator d := fun a b => Matrix.single a b 1 with hE
  set Sx := E i0 i1 + E i1 i0
  set Sz := E i0 i0 - E i1 i1
  set Sy := (-Complex.I) • E i0 i1 + Complex.I • E i1 i0
  have htr : ∀ a b : Fin d, (E a b).trace = if a = b then 1 else 0 := by
    intro a b
    by_cases h : a = b
    · subst h; simp [hE, Matrix.trace, Matrix.single_apply]
    · simp [hE, Matrix.trace, Matrix.single_apply, h, Ne.symm h]
  have hmul : ∀ a b c e : Fin d, E a b * E c e = if b = c then E a e else 0 := by
    intro a b c e
    by_cases h : b = c
    · subst h; simp [hE]
    · simp [hE, h]
  have hct : ∀ a b : Fin d, (E a b)ᴴ = E b a := by
    intro a b; simp [hE]
  have hSx : Sxᴴ = Sx := by simp only [Sx, Matrix.conjTranspose_add, hct]; abel
  have hSz : Szᴴ = Sz := by simp only [Sz, Matrix.conjTranspose_sub, hct]
  have hSy : Syᴴ = Sy := by
    simp only [Sy, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hct]
    simp only [star_neg, Complex.star_def, Complex.conj_I, neg_neg]
    abel
  have tSzSx : (Sz * Sx).trace = 0 := by
    simp [Sz, Sx, Matrix.sub_mul, Matrix.mul_add, hmul, htr, h01, Ne.symm h01]
  have tSxSx : (Sx * Sx).trace = 2 := by
    simp [Sx, Matrix.add_mul, Matrix.mul_add, hmul, htr, h01, Ne.symm h01]; norm_num
  have tE0Sx : (E i0 i0 * Sx).trace = 0 := by
    simp [Sx, Matrix.mul_add, hmul, htr, h01, Ne.symm h01]
  have tSz : Sz.trace = 0 := by simp [Sz, htr]
  have hcoh : P59.coherent Sy (E i0 i0) = Sx := by
    simp only [P59.coherent, Sy, Sx, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hmul,
      if_pos rfl, if_neg h01, if_neg (Ne.symm h01), smul_zero, zero_add, add_zero, smul_sub, smul_smul]
    rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg],
      show -Complex.I * -Complex.I = -1 by rw [neg_mul_neg, Complex.I_mul_I]]
    simp only [one_smul, neg_smul, sub_neg_eq_add]
    exact add_comm _ _
  have hcoh0 : P59.coherent Sy 0 = 0 := by simp [P59.coherent]
  let fX : P59.Operator d →ₗ[ℂ] P59.Operator d :=
    { toFun := fun Y => (Y * Sx).trace • Sz
      map_add' := fun A B => by simp [Matrix.add_mul, Matrix.trace_add, add_smul]
      map_smul' := fun c A => by simp [Matrix.smul_mul, Matrix.trace_smul, smul_smul] }
  let fL : P59.Operator d →ₗ[ℂ] P59.Operator d :=
    { toFun := P59.coherent Sy
      map_add' := fun A B => by simp only [P59.coherent, Matrix.mul_add, Matrix.add_mul]; module
      map_smul' := fun c A => by
        simp only [P59.coherent, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]; module }
  set X := superOfAction fX with hXdef
  set L := superOfAction fL with hLdef
  have hX : ∀ Y, P26.applyMap X Y = (Y * Sx).trace • Sz := fun Y => congrFun (S170bO_sup fX) Y
  have hL : ∀ Y, P26.applyMap L Y = P59.coherent Sy Y := fun Y => congrFun (S170bO_sup fL) Y
  have hXX : X * X = 0 := by
    rw [← S170bO_supapp (X * X)]
    have : P26.applyMap (X * X) = fun _ => 0 := funext fun Y => by
      rw [S170bO_mul, hX, hX, Matrix.smul_mul, Matrix.trace_smul, tSzSx, smul_zero, zero_smul]
    rw [this]; ext p q; simp [superOfAction]
  have had : ∀ Y, adMap X Y = X * Y - Y * X := fun Y => by
    simp [adMap, LieAlgebra.ad_apply, Ring.lie_def]
  have key : ∀ A : Super d, X * (X * A) = 0 := fun A => by rw [← mul_assoc, hXX, zero_mul]
  have h2 : (adMap X ^ 2) L = X * (X * L - L * X) - (X * L - L * X) * X := by
    rw [pow_two, Module.End.mul_apply, had, had]
  have h3 : (adMap X ^ 3) L = 0 := by
    rw [pow_succ', Module.End.mul_apply, h2, had]
    simp only [mul_sub, sub_mul, mul_assoc, key, hXX, mul_zero, zero_mul, sub_self, sub_zero, zero_sub, neg_zero,
      mul_neg, neg_mul, neg_neg]
  have hn : ∀ n ≥ 3, (adMap X ^ n) L = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [pow_add, Module.End.mul_apply, h3, map_zero]
  have hexp : expAd X L = L + (X * L - L * X) + (2⁻¹ : ℝ) • (X * (X * L - L * X) - (X * L - L * X) * X) := by
    unfold expAd
    rw [tsum_eq_sum (s := Finset.range 3) (fun n hm => by
      rw [Finset.mem_range, not_lt] at hm; rw [hn n hm, smul_zero])]
    simp [Finset.sum_range_succ, h2, had, Nat.factorial]
  refine ⟨X, L, ⟨⟨fX, funext fun Y => hX Y⟩, fun Y hY => ?_, fun Y => ?_⟩, ⟨Sy, 0, hSy, Matrix.PosSemidef.zero,
    funext fun Y => ?_⟩, ?_⟩
  · rw [hX]
    have hc : star ((Y * Sx).trace) = (Y * Sx).trace := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hY.eq, hSx, Matrix.trace_mul_comm]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hc, hSz]
  · rw [hX, Matrix.trace_smul, tSz, smul_zero]
  · rw [hL]; simp [P59.kossakowskiAction]
  · rintro ⟨H, K, hH, hK, heq⟩
    have hpos := S170bO_pos F H K hK i0 i1 h01
    rw [← congrFun heq] at hpos
    have hval : P26.applyMap (expAd X L) (Matrix.single i0 i0 1) = Sx + (2 : ℂ) • Sz := by
      change P26.applyMap (expAd X L) (E i0 i0) = _
      rw [hexp]
      simp only [S170bO_add, S170bO_sub, S170bO_smulR, S170bO_mul, hX, hL, hcoh, tE0Sx, zero_smul,
        hcoh0, S170bO_zero, Matrix.smul_mul, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_smul, tSzSx, tSxSx,
        smul_zero, sub_zero, smul_eq_mul, mul_zero, zero_smul, add_zero]
    rw [hval] at hpos
    simp [Sx, Sz, hE, Matrix.single_apply, h01, Ne.symm h01, Complex.le_def] at hpos
    norm_num at hpos

end
