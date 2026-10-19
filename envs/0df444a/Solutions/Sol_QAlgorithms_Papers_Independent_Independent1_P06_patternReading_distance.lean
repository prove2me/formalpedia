-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P06.patternReading_distance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:38:58.205097+00:00
-- url     : https://prove2.me/submissions/93dc3721-da14-4399-86b6-19bd47178165

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
import Mathlib.LinearAlgebra.Matrix.ToLin

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P06
open Finset

noncomputable section

namespace PatternDistanceO19

variable {c r n mx mz : ℕ}

private def old (v : ReadingData c r n mx → F2) : Matrix (Fin c) (Fin n) F2 :=
  fun b j => v (.inl (b,j))
private def anc (v : ReadingData c r n mx → F2) : Matrix (Fin r) (Fin mx) F2 :=
  fun b j => v (.inr (b,j))

private lemma rx (H : Matrix (Fin mx) (Fin n) F2) (P : Matrix (Fin r) (Fin c) F2)
    (v : ReadingData c r n mx → F2) (b : Fin c) (i : Fin mx) :
    (readingX H P).mulVec v (b,i) =
      (old v * H.transpose + P.transpose * anc v) b i := by
  simp [Matrix.mulVec, dotProduct, readingX, old, anc, Matrix.mul_apply,
    Fintype.sum_sum_type, Fintype.sum_prod_type, mul_comm]

private lemma rz_old (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2) (P : Matrix (Fin r) (Fin c) F2)
    (v : ReadingData c r n mx → F2) (b : Fin c) (i : Fin mz) :
    (readingZ H Z P).mulVec v (.inl (b,i)) = (old v * Z.transpose) b i := by
  simp [Matrix.mulVec, dotProduct, readingZ, old, Matrix.mul_apply,
    Fintype.sum_sum_type, Fintype.sum_prod_type, mul_comm]

private lemma rz_new (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2) (P : Matrix (Fin r) (Fin c) F2)
    (v : ReadingData c r n mx → F2) (b : Fin r) (j : Fin n) :
    (readingZ H Z P).mulVec v (.inr (b,j)) = (P * old v + anc v * H) b j := by
  simp [Matrix.mulVec, dotProduct, readingZ, old, anc, Matrix.mul_apply,
    Fintype.sum_sum_type, Fintype.sum_prod_type, mul_comm]

private lemma z_boundary (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2) (P : Matrix (Fin r) (Fin c) F2)
    (C : Matrix (Fin c) (Fin mz) F2) (T : Matrix (Fin r) (Fin n) F2) :
    let w := (readingZ H Z P).transpose.mulVec (Sum.elim (fun q => C q.1 q.2) (fun q => T q.1 q.2))
    old w = C * Z + P.transpose * T ∧ anc w = T * H.transpose := by
  constructor <;> ext b j <;>
    simp [Matrix.mulVec, dotProduct, readingZ, old, anc, Matrix.mul_apply,
      Fintype.sum_sum_type, Fintype.sum_prod_type, mul_comm]

private lemma x_boundary (H : Matrix (Fin mx) (Fin n) F2) (P : Matrix (Fin r) (Fin c) F2)
    (U : Matrix (Fin c) (Fin mx) F2) :
    let w := (readingX H P).transpose.mulVec (fun q => U q.1 q.2)
    old w = U * H ∧ anc w = P * U := by
  constructor <;> ext b j <;>
    simp [Matrix.mulVec, dotProduct, readingX, old, anc, Matrix.mul_apply,
      Fintype.sum_prod_type, mul_comm]

private lemma ext_data (v w : ReadingData c r n mx → F2)
    (ha : old v = old w) (hb : anc v = anc w) : v = w := by
  funext x
  cases x with
  | inl q => exact congrFun (congrFun ha q.1) q.2
  | inr q => exact congrFun (congrFun hb q.1) q.2

private lemma commute (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2) (P : Matrix (Fin r) (Fin c) F2)
    (h : H * Z.transpose = 0) : readingX H P * (readingZ H Z P).transpose = 0 := by
  have hz : Z * H.transpose = 0 := by
    simpa using congrArg Matrix.transpose h
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  let C : Matrix (Fin c) (Fin mz) F2 := fun q j => w (.inl (q,j))
  let T : Matrix (Fin r) (Fin n) F2 := fun q j => w (.inr (q,j))
  have hw : Sum.elim (fun q => C q.1 q.2) (fun q => T q.1 q.2) = w := by
    funext x; cases x <;> rfl
  have hb := z_boundary H Z P C T
  dsimp only at hb
  rw [hw] at hb
  ext ⟨b,i⟩
  rw [rx, hb.1, hb.2]
  simp [Matrix.add_mul, Matrix.mul_assoc, hz, CharTwo.add_self_eq_zero]

private lemma left_inverse (P : Matrix (Fin r) (Fin c) F2)
    (hp : Function.Injective P.transpose.mulVec) :
    ∃ L : Matrix (Fin r) (Fin c) F2, L * P.transpose = 1 := by
  obtain ⟨g,hg⟩ := P.transpose.mulVecLin.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hp)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  rw [LinearMap.toMatrix'_mulVec]
  change g (P.transpose.mulVec v) = v
  exact LinearMap.congr_fun hg v

private lemma weight_combination (v : ReadingData c r n mx → F2) (a : Fin c → F2) :
    hammingNorm ((old v).transpose.mulVec a) ≤ hammingNorm v := by
  classical
  by_cases hc : c = 0
  · subst c
    simp
  have hc' : 0 < c := Nat.pos_of_ne_zero hc
  have hs : ∀ j, (old v).transpose.mulVec a j ≠ 0 → ∃ b, v (.inl (b,j)) ≠ 0 := by
    intro j hj
    by_contra! hh
    apply hj
    simp [Matrix.mulVec, dotProduct, old, hh]
  let f : Fin n → ReadingData c r n mx := fun j =>
    .inl ((if h : ∃ b, v (.inl (b,j)) ≠ 0 then h.choose else ⟨0,hc'⟩),j)
  unfold hammingNorm
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hj ⊢
    dsimp [f]
    rw [dif_pos (hs j hj)]
    exact (hs j hj).choose_spec
  · intro j hj k hk he
    exact congrArg Prod.snd (Sum.inl.inj he)

private lemma row_mul {a b e : ℕ} (M : Matrix (Fin a) (Fin b) F2)
    (N : Matrix (Fin b) (Fin e) F2) (i : Fin a) :
    (M * N) i = N.transpose.mulVec (M i) := by
  ext j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

private lemma weight_row (v : ReadingData c r n mx → F2) (b : Fin c) :
    hammingNorm (old v b) ≤ hammingNorm v := by
  simpa only [Matrix.mulVec_single_one, Matrix.col, Matrix.transpose_transpose] using
    weight_combination v (Pi.single b 1)

private lemma rows_boundary {a : ℕ} (Z : Matrix (Fin mz) (Fin n) F2)
    (A : Matrix (Fin a) (Fin n) F2)
    (h : ∀ b, A b ∈ LinearMap.range Z.transpose.mulVecLin) :
    ∃ C : Matrix (Fin a) (Fin mz) F2, C * Z = A := by
  classical
  choose C hC using h
  refine ⟨C, ?_⟩
  ext b j
  exact congrFun ((row_mul C Z b).trans (hC b)) j

private lemma z_small (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2) (P : Matrix (Fin r) (Fin c) F2)
    (L : Matrix (Fin r) (Fin c) F2) (hL : L * P.transpose = 1)
    {d : ℕ} (hd : HasCSSDistance H Z d)
    (v : ReadingData c r n mx → F2) (hv : (readingX H P).mulVec v = 0)
    (hw : hammingNorm v < d) :
    v ∈ LinearMap.range (readingZ H Z P).transpose.mulVecLin := by
  classical
  have hcycle : old v * H.transpose = P.transpose * anc v := by
    ext b i
    apply CharTwo.add_eq_zero.mp
    simpa only [rx, Pi.zero_apply, Matrix.add_apply] using congrFun hv (b,i)
  let K : Matrix (Fin c) (Fin c) F2 := 1 + P.transpose * L
  let D := K * old v
  let T := L * old v
  have hKP : K * P.transpose = 0 := by
    simp only [K, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hL, Matrix.mul_one]
    ext b i
    exact CharTwo.add_self_eq_zero _
  have hD : D * H.transpose = 0 := by
    rw [show D = K * old v from rfl, Matrix.mul_assoc, hcycle,
      ← Matrix.mul_assoc, hKP, Matrix.zero_mul]
  have hT : T * H.transpose = anc v := by
    rw [show T = L * old v from rfl, Matrix.mul_assoc, hcycle,
      ← Matrix.mul_assoc, hL, Matrix.one_mul]
  obtain ⟨C,hC⟩ := rows_boundary Z D (by
    intro b
    by_contra hb
    have hz : H.mulVec (D b) = 0 := by
      have he := congrFun hD b
      rw [row_mul] at he
      exact he
    have hweight : hammingNorm (D b) ≤ hammingNorm v := by
      rw [show D = K * old v from rfl, row_mul]
      exact weight_combination v (K b)
    exact (Nat.not_le_of_lt (lt_of_le_of_lt hweight hw)) (hd.2.1 _ hz hb))
  refine ⟨Sum.elim (fun q => C q.1 q.2) (fun q => T q.1 q.2), ?_⟩
  change (readingZ H Z P).transpose.mulVec _ = v
  apply ext_data
  · rw [(z_boundary H Z P C T).1, hC]
    simp only [D, K, T, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
    ext b j
    simp [Matrix.add_apply, add_assoc, CharTwo.add_self_eq_zero]
  · rw [(z_boundary H Z P C T).2, hT]

private lemma x_small (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2) (P : Matrix (Fin r) (Fin c) F2)
    (L : Matrix (Fin r) (Fin c) F2) (hL : L * P.transpose = 1)
    {d : ℕ} (hd : HasCSSDistance H Z d)
    (v : ReadingData c r n mx → F2) (hv : (readingZ H Z P).mulVec v = 0)
    (hw : hammingNorm v < d) :
    v ∈ LinearMap.range (readingX H P).transpose.mulVecLin := by
  classical
  have hright : P * L.transpose = 1 := by
    simpa using congrArg Matrix.transpose hL
  have hold : old v * Z.transpose = 0 := by
    ext b i
    simpa only [rz_old, Pi.zero_apply, Matrix.zero_apply] using congrFun hv (.inl (b,i))
  have hnew : P * old v + anc v * H = 0 := by
    ext b j
    simpa only [rz_new, Pi.zero_apply, Matrix.zero_apply] using congrFun hv (.inr (b,j))
  obtain ⟨U,hU⟩ := rows_boundary H (old v) (by
    intro b
    by_contra hb
    have hz : Z.mulVec (old v b) = 0 := by
      have he := congrFun hold b
      rw [row_mul] at he
      exact he
    exact (Nat.not_le_of_lt (lt_of_le_of_lt (weight_row v b) hw)) (hd.2.2 _ hz hb))
  let R := anc v + P * U
  have hR : R * H = 0 := by
    dsimp only [R]
    rw [Matrix.add_mul, Matrix.mul_assoc, hU, add_comm, hnew]
  let W := U + L.transpose * R
  have hWH : W * H = old v := by
    simp [W, Matrix.add_mul, Matrix.mul_assoc, hR, hU]
  have hPW : P * W = anc v := by
    simp only [W, Matrix.mul_add, ← Matrix.mul_assoc, hright, Matrix.one_mul, R]
    ext b i
    change (P * U) b i + (anc v b i + (P * U) b i) = anc v b i
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  refine ⟨fun q => W q.1 q.2, ?_⟩
  change (readingX H P).transpose.mulVec _ = v
  apply ext_data
  · rw [(x_boundary H P W).1, hWH]
  · rw [(x_boundary H P W).2, hPW]

end PatternDistanceO19

theorem solution {c r n mx mz d : ℕ}
    (HX : Matrix (Fin mx) (Fin n) F2) (HZ : Matrix (Fin mz) (Fin n) F2)
    (P : Matrix (Fin r) (Fin c) F2)
    (fullRowRank : Function.Injective P.transpose.mulVec)
    (_rowWeight : ∀ i, 1 < hammingNorm (P i))
    (distance : HasCSSDistance HX HZ d) :
    HasCSSDistance (readingX HX P) (readingZ HX HZ P) d := by
  obtain ⟨L,hL⟩ := PatternDistanceO19.left_inverse P fullRowRank
  refine ⟨PatternDistanceO19.commute HX HZ P distance.1, ?_, ?_⟩
  · intro v hv hn
    by_contra! hw
    exact hn (PatternDistanceO19.z_small HX HZ P L hL distance v hv hw)
  · intro v hv hn
    by_contra! hw
    exact hn (PatternDistanceO19.x_small HX HZ P L hL distance v hv hw)

#print axioms solution

