-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P06.pairReading_noAdditionalLogicals
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:28:35.536146+00:00
-- url     : https://prove2.me/submissions/c184db74-e4de-4ca8-9506-81e14de7ccd6

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model

open QAlgorithms
open QAlgorithms.Papers.Independent.Independent1.P06
open Finset

namespace PairLogicalsO19

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


private noncomputable def quotientEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module F2 A] [Module F2 B]
    (p : Submodule F2 A) (q : Submodule F2 B) (f : A →ₗ[F2] B)
    (hs : Function.Surjective f) (hm : ∀ x, f x ∈ q ↔ x ∈ p) :
    (A ⧸ p) ≃ₗ[F2] (B ⧸ q) := by
  let g := p.mapQ q f (fun x hx => (hm x).mpr hx)
  apply LinearEquiv.ofBijective g
  constructor
  · intro x y he
    induction x using Submodule.Quotient.induction_on with | _ x =>
    induction y using Submodule.Quotient.induction_on with | _ y =>
    apply (Submodule.Quotient.eq p).mpr
    apply (hm (x-y)).mp
    rw [map_sub]
    exact (Submodule.Quotient.eq q).mp he
  · intro y
    induction y using Submodule.Quotient.induction_on with | _ y =>
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨Submodule.Quotient.mk x, rfl⟩

private def zMap (H : Matrix (Fin mx) (Fin n) F2) :
    LinearMap.ker (readingX H pairPattern).mulVecLin →ₗ[F2] LinearMap.ker H.mulVecLin where
  toFun v := ⟨fun j => v.val (.inl (0,j)) + v.val (.inl (1,j)), z_cycle H v.val v.property⟩
  map_add' v w := by
    apply Subtype.ext
    funext j
    change (v.val (.inl (0,j)) + w.val (.inl (0,j))) +
      (v.val (.inl (1,j)) + w.val (.inl (1,j))) = _
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c v := by
    apply Subtype.ext
    funext j
    change c • v.val (.inl (0,j)) + c • v.val (.inl (1,j)) =
      c • (v.val (.inl (0,j)) + v.val (.inl (1,j)))
    exact (smul_add c _ _).symm

private def xMap (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2) :
    LinearMap.ker (readingZ H Z pairPattern).mulVecLin →ₗ[F2] LinearMap.ker Z.mulVecLin where
  toFun v := ⟨fun j => v.val (.inl (0,j)), x_cycle H Z v.val v.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma z_surj (H : Matrix (Fin mx) (Fin n) F2) : Function.Surjective (zMap H) := by
  intro u
  let v : ReadingData 2 1 n mx → F2 := Sum.elim (fun bj => if bj.1 = 0 then u.val bj.2 else 0) (fun _ => 0)
  have hv : (readingX H pairPattern).mulVec v = 0 := by
    ext ⟨b,i⟩
    rw [rx]
    fin_cases b
    · change H.mulVec u.val i + 0 = 0
      exact (add_zero _).trans (congrFun u.property i)
    · change H.mulVec 0 i + 0 = 0
      simp only [Matrix.mulVec_zero, Pi.zero_apply, add_zero]
  refine ⟨⟨v,hv⟩, ?_⟩
  apply Subtype.ext
  funext j
  simp [zMap, v]

private lemma x_surj (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2) : Function.Surjective (xMap H Z) := by
  intro u
  let v : ReadingData 2 1 n mx → F2 := Sum.elim (fun bj => u.val bj.2) (fun _ => 0)
  have hv : (readingZ H Z pairPattern).mulVec v = 0 := by
    ext q
    cases q with
    | inl q =>
      rw [rz_old]
      change Z.mulVec u.val q.2 = 0
      exact congrFun u.property q.2
    | inr q =>
      have hb : q.1 = 0 := Subsingleton.elim _ _
      rcases q with ⟨b,j⟩
      dsimp at hb
      subst b
      rw [rz_new]
      change u.val j + u.val j + H.transpose.mulVec 0 j = 0
      simp only [CharTwo.add_self_eq_zero, Matrix.mulVec_zero, Pi.zero_apply]
  exact ⟨⟨v,hv⟩, rfl⟩

private lemma z_boundary (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2)
    (v : LinearMap.ker (readingX H pairPattern).mulVecLin) :
    (zMap H v).val ∈ LinearMap.range Z.transpose.mulVecLin ↔
      v.val ∈ LinearMap.range (readingZ H Z pairPattern).transpose.mulVecLin := by
  constructor
  · intro h
    by_contra hn
    exact z_nontrivial H Z v.val v.property hn h
  · rintro ⟨w,hw⟩
    refine ⟨fun i => w (.inl (0,i)) + w (.inl (1,i)), ?_⟩
    change Z.transpose.mulVec _ = _
    rw [show (fun i => w (.inl (0,i)) + w (.inl (1,i))) =
      (fun i => w (.inl (0,i))) + (fun i => w (.inl (1,i))) from rfl,
      Matrix.mulVec_add]
    ext j
    have h0 := congrFun hw (.inl (0,j))
    have h1 := congrFun hw (.inl (1,j))
    change (readingZ H Z pairPattern).transpose.mulVec w (.inl (0,j)) = _ at h0
    change (readingZ H Z pairPattern).transpose.mulVec w (.inl (1,j)) = _ at h1
    rw [rzt_old] at h0 h1
    change _ = v.val (.inl (0,j)) + v.val (.inl (1,j))
    rw [← h0, ← h1]
    rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]
    rfl

private lemma x_boundary (H : Matrix (Fin mx) (Fin n) F2)
    (Z : Matrix (Fin mz) (Fin n) F2)
    (v : LinearMap.ker (readingZ H Z pairPattern).mulVecLin) :
    (xMap H Z v).val ∈ LinearMap.range H.transpose.mulVecLin ↔
      v.val ∈ LinearMap.range (readingX H pairPattern).transpose.mulVecLin := by
  constructor
  · intro h
    by_contra hn
    exact x_nontrivial H Z v.val v.property hn h
  · rintro ⟨w,hw⟩
    refine ⟨fun i => w (0,i), ?_⟩
    ext j
    have he := congrFun hw (.inl (0,j))
    change (readingX H pairPattern).transpose.mulVec w (.inl (0,j)) = _ at he
    exact (rxt_old H w 0 j).symm.trans he

end PairLogicalsO19

theorem solution {n mx mz : ℕ}
    (HX : Matrix (Fin mx) (Fin n) F2) (HZ : Matrix (Fin mz) (Fin n) F2)
    (_css : HX * HZ.transpose = 0) :
    Nonempty (logicalSpace (readingX HX pairPattern) (readingZ HX HZ pairPattern) ≃ₗ[F2]
      logicalSpace HX HZ) ∧
    Nonempty (logicalSpace (readingZ HX HZ pairPattern) (readingX HX pairPattern) ≃ₗ[F2]
      logicalSpace HZ HX) := by
  constructor
  · exact ⟨PairLogicalsO19.quotientEquiv _ _ (PairLogicalsO19.zMap HX)
      (PairLogicalsO19.z_surj HX) (PairLogicalsO19.z_boundary HX HZ)⟩
  · exact ⟨PairLogicalsO19.quotientEquiv _ _ (PairLogicalsO19.xMap HX HZ)
      (PairLogicalsO19.x_surj HX HZ) (PairLogicalsO19.x_boundary HX HZ)⟩

#print axioms solution
