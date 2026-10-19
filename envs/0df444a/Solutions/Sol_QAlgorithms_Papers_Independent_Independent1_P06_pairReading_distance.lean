-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P06.pairReading_distance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:19:10.045012+00:00
-- url     : https://prove2.me/submissions/ad1ba550-9b3c-4288-9bf5-4b61523d04e0

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model

open QAlgorithms
open QAlgorithms.Papers.Independent.Independent1.P06
open Finset

namespace PairDistanceO19

variable {n mx mz : ℕ}

private lemma rx (H : Matrix (Fin mx) (Fin n) F2)
    (v : ReadingData 2 1 n mx → F2) (b : Fin 2) (i : Fin mx) :
    (readingX H pairPattern).mulVec v (b,i) =
      H.mulVec (fun j => v (.inl (b,j))) i + v (.inr (0,i)) := by
  simp [Matrix.mulVec, dotProduct, readingX, pairPattern,
    Fintype.sum_sum_type, Fintype.sum_prod_type]

private lemma rz_old (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2)
    (v : ReadingData 2 1 n mx → F2) (b : Fin 2) (i : Fin mz) :
    (readingZ H Z pairPattern).mulVec v (.inl (b,i)) =
      Z.mulVec (fun j => v (.inl (b,j))) i := by
  simp [Matrix.mulVec, dotProduct, readingZ,
    Fintype.sum_sum_type, Fintype.sum_prod_type]

private lemma rz_new (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2)
    (v : ReadingData 2 1 n mx → F2) (j : Fin n) :
    (readingZ H Z pairPattern).mulVec v (.inr (0,j)) =
      v (.inl (0,j)) + v (.inl (1,j)) +
        H.transpose.mulVec (fun i => v (.inr (0,i))) j := by
  simp [Matrix.mulVec, dotProduct, readingZ, pairPattern,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]

private lemma rzt_old (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2)
    (w : (Fin 2 × Fin mz) ⊕ (Fin 1 × Fin n) → F2) (b : Fin 2) (j : Fin n) :
    (readingZ H Z pairPattern).transpose.mulVec w (.inl (b,j)) =
      Z.transpose.mulVec (fun i => w (.inl (b,i))) j + w (.inr (0,j)) := by
  simp [Matrix.mulVec, dotProduct, readingZ, pairPattern, Matrix.transpose_apply,
    Fintype.sum_sum_type, Fintype.sum_prod_type]

private lemma rzt_new (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2)
    (w : (Fin 2 × Fin mz) ⊕ (Fin 1 × Fin n) → F2) (i : Fin mx) :
    (readingZ H Z pairPattern).transpose.mulVec w (.inr (0,i)) =
      H.mulVec (fun j => w (.inr (0,j))) i := by
  simp [Matrix.mulVec, dotProduct, readingZ, Matrix.transpose_apply,
    Fintype.sum_sum_type, Fintype.sum_prod_type]

private lemma rxt_old (H : Matrix (Fin mx) (Fin n) F2)
    (w : Fin 2 × Fin mx → F2) (b : Fin 2) (j : Fin n) :
    (readingX H pairPattern).transpose.mulVec w (.inl (b,j)) =
      H.transpose.mulVec (fun i => w (b,i)) j := by
  simp [Matrix.mulVec, dotProduct, readingX, Matrix.transpose_apply,
    Fintype.sum_prod_type]

private lemma rxt_new (H : Matrix (Fin mx) (Fin n) F2)
    (w : Fin 2 × Fin mx → F2) (i : Fin mx) :
    (readingX H pairPattern).transpose.mulVec w (.inr (0,i)) =
      w (0,i) + w (1,i) := by
  simp [Matrix.mulVec, dotProduct, readingX, pairPattern, Matrix.transpose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]

private lemma commute (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2) (h : H * Z.transpose = 0) :
    readingX H pairPattern * (readingZ H Z pairPattern).transpose = 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro w
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  ext ⟨b,i⟩
  rw [rx]
  have he : (fun j => (readingZ H Z pairPattern).transpose.mulVec w (.inl (b,j))) =
      Z.transpose.mulVec (fun k => w (.inl (b,k))) + (fun j => w (.inr (0,j))) := by
    funext j; exact rzt_old H Z w b j
  rw [he, Matrix.mulVec_add, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec, rzt_new]
  simp [CharTwo.add_self_eq_zero]

private lemma weight_single (v : ReadingData 2 1 n mx → F2) :
    hammingNorm (fun j => v (.inl (0,j))) ≤ hammingNorm v := by
  unfold hammingNorm
  apply Finset.card_le_card_of_injOn (fun j => Sum.inl (0,j))
  · intro j hj
    simpa using hj
  · intro j hj k hk he
    exact congrArg Prod.snd (Sum.inl.inj he)

private lemma weight_sum (v : ReadingData 2 1 n mx → F2) :
    hammingNorm (fun j => v (.inl (0,j)) + v (.inl (1,j))) ≤ hammingNorm v := by
  unfold hammingNorm
  let f : Fin n → ReadingData 2 1 n mx := fun j =>
    .inl (if v (.inl (0,j)) = 0 then (1,j) else (0,j))
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hj ⊢
    dsimp [f]
    split_ifs with h
    · simpa [h] using hj
    · exact h
  · intro j hj k hk he
    have : (fun x : ReadingData 2 1 n mx =>
        match x with | .inl a => a.2 | .inr _ => j) (f j) =
      (fun x : ReadingData 2 1 n mx =>
        match x with | .inl a => a.2 | .inr _ => j) (f k) :=
      congrArg (fun x : ReadingData 2 1 n mx =>
        match x with | .inl a => a.2 | .inr _ => j) he
    simpa [f, apply_ite] using this

private lemma z_cycle (H : Matrix (Fin mx) (Fin n) F2)
    (v : ReadingData 2 1 n mx → F2) (hv : (readingX H pairPattern).mulVec v = 0) :
    H.mulVec (fun j => v (.inl (0,j)) + v (.inl (1,j))) = 0 := by
  rw [show (fun j => v (.inl (0,j)) + v (.inl (1,j))) =
    (fun j => v (.inl (0,j))) + (fun j => v (.inl (1,j))) from rfl, Matrix.mulVec_add]
  ext i
  have h0 := congrFun hv (0,i)
  have h1 := congrFun hv (1,i)
  simp only [rx, Pi.zero_apply] at h0 h1
  change H.mulVec (fun j => v (.inl (0,j))) i + H.mulVec (fun j => v (.inl (1,j))) i = 0
  apply CharTwo.add_eq_zero.mpr
  exact (CharTwo.add_eq_zero.mp h0).trans (CharTwo.add_eq_zero.mp h1).symm

private lemma z_nontrivial (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2)
    (v : ReadingData 2 1 n mx → F2) (hv : (readingX H pairPattern).mulVec v = 0)
    (hn : v ∉ LinearMap.range (readingZ H Z pairPattern).transpose.mulVecLin) :
    (fun j => v (.inl (0,j)) + v (.inl (1,j))) ∉ LinearMap.range Z.transpose.mulVecLin := by
  rintro ⟨z,hz⟩
  apply hn
  refine ⟨Sum.elim (fun bi => if bi.1 = 0 then z bi.2 else 0)
    (fun q => v (.inl (1,q.2))), ?_⟩
  change (readingZ H Z pairPattern).transpose.mulVec _ = v
  ext x
  cases x with
  | inl q =>
    rcases q with ⟨b,j⟩
    rw [rzt_old]
    fin_cases b
    · change Z.transpose.mulVec z j + v (.inl (1,j)) = v (.inl (0,j))
      have he := congrFun hz j
      change Z.transpose.mulVec z j = v (.inl (0,j)) + v (.inl (1,j)) at he
      rw [he]
      simp [add_assoc, CharTwo.add_self_eq_zero]
    · change Z.transpose.mulVec 0 j + v (.inl (1,j)) = v (.inl (1,j))
      simp only [Matrix.mulVec_zero, Pi.zero_apply, zero_add]
  | inr q =>
    rcases q with ⟨b,i⟩
    have hb : b = 0 := Subsingleton.elim _ _
    subst b
    rw [rzt_new]
    have he := congrFun hv (1,i)
    simp only [rx, Pi.zero_apply] at he
    change H.mulVec (fun j => v (.inl (1,j))) i = v (.inr (0,i))
    exact CharTwo.add_eq_zero.mp he

private lemma x_cycle (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2)
    (v : ReadingData 2 1 n mx → F2) (hv : (readingZ H Z pairPattern).mulVec v = 0) :
    Z.mulVec (fun j => v (.inl (0,j))) = 0 := by
  ext i
  have he := congrFun hv (.inl (0,i))
  simpa only [rz_old, Pi.zero_apply] using he

private lemma x_nontrivial (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2)
    (v : ReadingData 2 1 n mx → F2) (hv : (readingZ H Z pairPattern).mulVec v = 0)
    (hn : v ∉ LinearMap.range (readingX H pairPattern).transpose.mulVecLin) :
    (fun j => v (.inl (0,j))) ∉ LinearMap.range H.transpose.mulVecLin := by
  rintro ⟨u,hu⟩
  apply hn
  refine ⟨fun bi => if bi.1 = 0 then u bi.2 else u bi.2 + v (.inr (0,bi.2)), ?_⟩
  change (readingX H pairPattern).transpose.mulVec _ = v
  ext x
  cases x with
  | inl q =>
    rcases q with ⟨b,j⟩
    rw [rxt_old]
    fin_cases b
    · change H.transpose.mulVec u j = v (.inl (0,j))
      exact congrFun hu j
    · change H.transpose.mulVec (u + fun i => v (.inr (0,i))) j = v (.inl (1,j))
      rw [Matrix.mulVec_add]
      have he := congrFun hv (.inr (0,j))
      simp only [rz_new, Pi.zero_apply] at he
      have he0 := congrFun hu j
      change H.transpose.mulVec u j = v (.inl (0,j)) at he0
      change H.transpose.mulVec u j + H.transpose.mulVec (fun i => v (.inr (0,i))) j = _
      rw [he0, ← CharTwo.add_eq_zero.mp he]
      simp [← add_assoc, CharTwo.add_self_eq_zero]
  | inr q =>
    rcases q with ⟨b,i⟩
    have hb : b = 0 := Subsingleton.elim _ _
    subst b
    rw [rxt_new]
    simp [CharTwo.add_self_eq_zero, ← add_assoc]

end PairDistanceO19

theorem solution {n mx mz d : ℕ}
    (HX : Matrix (Fin mx) (Fin n) F2) (HZ : Matrix (Fin mz) (Fin n) F2)
    (distance : HasCSSDistance HX HZ d) :
    HasCSSDistance (readingX HX pairPattern) (readingZ HX HZ pairPattern) d := by
  refine ⟨PairDistanceO19.commute HX HZ distance.1, ?_, ?_⟩
  · intro v hv hn
    exact (distance.2.1 _ (PairDistanceO19.z_cycle HX v hv)
      (PairDistanceO19.z_nontrivial HX HZ v hv hn)).trans (PairDistanceO19.weight_sum v)
  · intro v hv hn
    exact (distance.2.2 _ (PairDistanceO19.x_cycle HX HZ v hv)
      (PairDistanceO19.x_nontrivial HX HZ v hv hn)).trans (PairDistanceO19.weight_single v)
