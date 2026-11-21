-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P43.lower_rank_attainment
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-21T00:57:42.861631+00:00
-- url     : https://prove2.me/submissions/e2fc9ff6-6173-4223-ab57-277baeef5dcc

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P43
noncomputable section

set_option maxHeartbeats 800000
open scoped BigOperators Matrix ComplexConjugate Classical
open Matrix

namespace QAlgorithms.Papers.Independent.Intake100.P43

open QAlgorithms.Papers.Independent.Dependency50.P50 (Bipartite schmidtNumber)
open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

/-! Totally nonsingular matrices, copied from the accepted P43.totally_nonsingular_exists proof. -/

theorem AuxLRA_minor_ne {n k : ℕ} (rows cols : Fin k ↪ Fin n) :
    ((Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℂ)).submatrix
      rows cols).det ≠ 0 := by
  classical
  intro h
  set f : Fin n × Fin n → ℂ := fun p => if ∃ a, rows a = p.1 ∧ cols a = p.2 then 1 else 0
  have h2 := congrArg (MvPolynomial.eval f) h
  rw [RingHom.map_det, map_zero] at h2
  have hM : (MvPolynomial.eval f).mapMatrix
      ((Matrix.of fun i j => (MvPolynomial.X (i, j) : MvPolynomial (Fin n × Fin n) ℂ)).submatrix
        rows cols) = 1 := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.of_apply,
      MvPolynomial.eval_X, f, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg, if_neg hab]
      rintro ⟨c, hc1, hc2⟩
      exact hab ((rows.injective hc1).symm.trans (cols.injective hc2))
  rw [hM, Matrix.det_one] at h2
  exact one_ne_zero h2

theorem AuxLRA_tns_exists (n : ℕ) : ∃ M : Matrix (Fin n) (Fin n) ℂ, TotallyNonsingular M := by
  classical
  set X : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℂ) :=
    Matrix.of fun i j => MvPolynomial.X (i, j) with hX
  let ι := Σ k : Fin (n + 1), (Fin k ↪ Fin n) × (Fin k ↪ Fin n)
  let p : ι → MvPolynomial (Fin n × Fin n) ℂ := fun s => (X.submatrix s.2.1 s.2.2).det
  have hp : ∀ s, p s ≠ 0 := fun s => AuxLRA_minor_ne s.2.1 s.2.2
  have hP : ∏ s, p s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s _ => hp s
  obtain ⟨f, hf⟩ : ∃ f : Fin n × Fin n → ℂ, MvPolynomial.eval f (∏ s, p s) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hP
    exact MvPolynomial.funext fun x => by simpa using hcon x
  refine ⟨Matrix.of fun i j => f (i, j), fun k rows cols => ?_⟩
  have hk : k < n + 1 := by
    have := Fintype.card_le_of_embedding rows
    simp at this; omega
  have hne : MvPolynomial.eval f (p ⟨⟨k, hk⟩, rows, cols⟩) ≠ 0 := by
    rw [map_prod] at hf
    exact (Finset.prod_ne_zero_iff.mp hf) _ (Finset.mem_univ _)
  simp only [p, RingHom.map_det] at hne
  convert hne using 2
  ext a b
  simp [X]

def AuxLRA_tns (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Classical.choose (AuxLRA_tns_exists n)

theorem AuxLRA_tns_spec (n : ℕ) : TotallyNonsingular (AuxLRA_tns n) :=
  Classical.choose_spec (AuxLRA_tns_exists n)

/-- Lemma 9: a nonzero combination of `t` columns of a TNS matrix has fewer than `t` zeros. -/
theorem AuxLRA_few_zeros {L t : ℕ} (ht : t ≤ L) (c : Fin t → ℂ)
    (hvzeros : t ≤ (Finset.univ.filter
      (fun i : Fin L => (∑ j : Fin t, c j * AuxLRA_tns L i (Fin.castLE ht j)) = 0)).card) :
    c = 0 := by
  classical
  let v : Fin L → ℂ := fun i => ∑ j : Fin t, c j * AuxLRA_tns L i (Fin.castLE ht j)
  obtain ⟨s, hsZ, hsc⟩ := Finset.exists_subset_card_eq hvzeros
  let iso := s.orderIsoOfFin hsc
  let rows : Fin t ↪ Fin L := iso.toEmbedding.trans (Function.Embedding.subtype _)
  let cols : Fin t ↪ Fin L := Fin.castLEEmb ht
  have hmul : ((AuxLRA_tns L).submatrix rows cols).mulVec c = 0 := by
    ext a
    have ha : rows a ∈ s := (iso a).2
    have hv : v (rows a) = 0 := by
      have := hsZ ha
      simpa [v, Finset.mem_filter] using this
    change ∑ j, AuxLRA_tns L (rows a) (cols j) * c j = 0
    simpa [v, cols, Fin.castLEEmb, mul_comm] using hv
  have hdet : ((AuxLRA_tns L).submatrix rows cols).det ≠ 0 :=
    AuxLRA_tns_spec L t rows cols
  have hinj := Matrix.mulVec_injective_of_det_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hdet)
  exact hinj (by rw [hmul, mulVec_zero])


/-! Diagonals of a rectangular matrix, indexed from lower-left to upper-right. -/

def AuxLRA_off (dA dB : ℕ) (k : Fin (dA + dB - 1)) : ℤ :=
  (k : ℤ) - (dA - 1 : ℤ)

def AuxLRA_iMin (dA dB : ℕ) (s : ℤ) : ℤ := max (0 : ℤ) (-s)
def AuxLRA_iMax (dA dB : ℕ) (s : ℤ) : ℤ := min (dA - 1 : ℤ) ((dB : ℤ) - 1 - s)

def AuxLRA_len (dA dB : ℕ) (s : ℤ) : ℕ :=
  Int.toNat (AuxLRA_iMax dA dB s - AuxLRA_iMin dA dB s + 1)

theorem AuxLRA_imin_le_imax {dA dB : ℕ} {s : ℤ} (p : Fin (AuxLRA_len dA dB s)) :
    AuxLRA_iMin dA dB s ≤ AuxLRA_iMax dA dB s := by
  have hpos : 0 < AuxLRA_len dA dB s := Nat.zero_lt_of_lt p.isLt
  have hz : ¬ AuxLRA_iMax dA dB s - AuxLRA_iMin dA dB s + 1 ≤ 0 := by
    intro h
    have := Int.toNat_of_nonpos h
    simp [AuxLRA_len] at hpos
    omega
  linarith

theorem AuxLRA_len_eq {dA dB : ℕ} {s : ℤ}
    (hle : AuxLRA_iMin dA dB s ≤ AuxLRA_iMax dA dB s) :
    (AuxLRA_len dA dB s : ℤ) = AuxLRA_iMax dA dB s - AuxLRA_iMin dA dB s + 1 := by
  unfold AuxLRA_len
  rw [Int.toNat_of_nonneg (by linarith)]

theorem AuxLRA_row_int_nonneg {dA dB : ℕ} {s : ℤ} (p : Fin (AuxLRA_len dA dB s)) :
    0 ≤ AuxLRA_iMin dA dB s + (p : ℕ) := by
  have : 0 ≤ AuxLRA_iMin dA dB s := le_max_left _ _
  linarith

theorem AuxLRA_row_int_le_imax {dA dB : ℕ} {s : ℤ} (p : Fin (AuxLRA_len dA dB s)) :
    AuxLRA_iMin dA dB s + (p : ℕ) ≤ AuxLRA_iMax dA dB s := by
  have hle := AuxLRA_imin_le_imax p
  have hlen := AuxLRA_len_eq hle
  have hp : (p : ℕ) + 1 ≤ AuxLRA_len dA dB s := Nat.succ_le_iff.mpr p.isLt
  have : (p : ℤ) + 1 ≤ (AuxLRA_len dA dB s : ℤ) := by exact_mod_cast hp
  linarith

theorem AuxLRA_row_int_lt_dA {dA dB : ℕ} {s : ℤ} (_hdA : 0 < dA)
    (p : Fin (AuxLRA_len dA dB s)) :
    AuxLRA_iMin dA dB s + (p : ℕ) < (dA : ℤ) := by
  have := AuxLRA_row_int_le_imax p
  have himax : AuxLRA_iMax dA dB s ≤ (dA : ℤ) - 1 := min_le_left _ _
  linarith

def AuxLRA_row (dA dB : ℕ) (s : ℤ) (hdA : 0 < dA)
    (p : Fin (AuxLRA_len dA dB s)) : Fin dA :=
  ⟨(AuxLRA_iMin dA dB s + (p : ℕ)).toNat, by
    have hnn := AuxLRA_row_int_nonneg p
    have hlt := AuxLRA_row_int_lt_dA hdA p
    have : ((AuxLRA_iMin dA dB s + (p : ℕ)).toNat : ℤ) < (dA : ℤ) := by
      rwa [Int.toNat_of_nonneg hnn]
    exact Nat.cast_lt.mp this⟩

def AuxLRA_colInt (dA dB : ℕ) (s : ℤ) (p : Fin (AuxLRA_len dA dB s)) : ℤ :=
  AuxLRA_iMin dA dB s + (p : ℕ) + s

theorem AuxLRA_colInt_nonneg {dA dB : ℕ} {s : ℤ} (p : Fin (AuxLRA_len dA dB s)) :
    0 ≤ AuxLRA_colInt dA dB s p := by
  unfold AuxLRA_colInt AuxLRA_iMin
  have : -s ≤ max (0 : ℤ) (-s) := le_max_right _ _
  linarith

theorem AuxLRA_colInt_lt {dA dB : ℕ} {s : ℤ} (p : Fin (AuxLRA_len dA dB s)) :
    AuxLRA_colInt dA dB s p < (dB : ℤ) := by
  have := AuxLRA_row_int_le_imax p
  have himax : AuxLRA_iMax dA dB s ≤ (dB : ℤ) - 1 - s := min_le_right _ _
  unfold AuxLRA_colInt
  linarith

def AuxLRA_col (dA dB : ℕ) (s : ℤ) (_hdA : 0 < dA) (_hdB : 0 < dB)
    (p : Fin (AuxLRA_len dA dB s)) : Fin dB :=
  ⟨(AuxLRA_colInt dA dB s p).toNat, by
    have hnn := AuxLRA_colInt_nonneg p
    have hlt := AuxLRA_colInt_lt p
    have : ((AuxLRA_colInt dA dB s p).toNat : ℤ) < (dB : ℤ) := by
      rwa [Int.toNat_of_nonneg hnn]
    exact Nat.cast_lt.mp this⟩

theorem AuxLRA_row_val {dA dB : ℕ} {s : ℤ} (hdA : 0 < dA)
    (p : Fin (AuxLRA_len dA dB s)) :
    ((AuxLRA_row dA dB s hdA p : ℕ) : ℤ) = AuxLRA_iMin dA dB s + (p : ℕ) := by
  simp [AuxLRA_row, Int.toNat_of_nonneg (AuxLRA_row_int_nonneg p)]

theorem AuxLRA_col_val {dA dB : ℕ} {s : ℤ} (hdA : 0 < dA) (hdB : 0 < dB)
    (p : Fin (AuxLRA_len dA dB s)) :
    ((AuxLRA_col dA dB s hdA hdB p : ℕ) : ℤ) = AuxLRA_iMin dA dB s + (p : ℕ) + s := by
  simp [AuxLRA_col]
  rw [max_eq_left (AuxLRA_colInt_nonneg p)]
  rfl

theorem AuxLRA_row_strictMono {dA dB : ℕ} {s : ℤ} (hdA : 0 < dA)
    {p q : Fin (AuxLRA_len dA dB s)} (hpq : p < q) :
    AuxLRA_row dA dB s hdA p < AuxLRA_row dA dB s hdA q := by
  rw [Fin.lt_def]
  have : ((AuxLRA_row dA dB s hdA p : ℕ) : ℤ) <
      ((AuxLRA_row dA dB s hdA q : ℕ) : ℤ) := by
    rw [AuxLRA_row_val, AuxLRA_row_val]
    have : (p : ℕ) < (q : ℕ) := hpq
    exact_mod_cast (by linarith)
  exact_mod_cast this

theorem AuxLRA_col_strictMono {dA dB : ℕ} {s : ℤ} (hdA : 0 < dA) (hdB : 0 < dB)
    {p q : Fin (AuxLRA_len dA dB s)} (hpq : p < q) :
    AuxLRA_col dA dB s hdA hdB p < AuxLRA_col dA dB s hdA hdB q := by
  rw [Fin.lt_def]
  have : ((AuxLRA_col dA dB s hdA hdB p : ℕ) : ℤ) <
      ((AuxLRA_col dA dB s hdA hdB q : ℕ) : ℤ) := by
    rw [AuxLRA_col_val, AuxLRA_col_val]
    have : (p : ℕ) < (q : ℕ) := hpq
    exact_mod_cast (by linarith)
  exact_mod_cast this

theorem AuxLRA_row_injective {dA dB : ℕ} {s : ℤ} (hdA : 0 < dA) :
    Function.Injective (AuxLRA_row dA dB s hdA) := by
  intro p q h
  rcases eq_or_ne p q with h | hne
  · exact h
  · rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (ne_of_lt (AuxLRA_row_strictMono hdA hlt) h).elim
    · exact (ne_of_lt (AuxLRA_row_strictMono hdA hlt) h.symm).elim

theorem AuxLRA_col_injective {dA dB : ℕ} {s : ℤ} (hdA : 0 < dA) (hdB : 0 < dB) :
    Function.Injective (AuxLRA_col dA dB s hdA hdB) := by
  intro p q h
  rcases eq_or_ne p q with h | hne
  · exact h
  · rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (ne_of_lt (AuxLRA_col_strictMono hdA hdB hlt) h).elim
    · exact (ne_of_lt (AuxLRA_col_strictMono hdA hdB hlt) h.symm).elim

theorem AuxLRA_off_row_col {dA dB : ℕ} {s : ℤ} (hdA : 0 < dA) (hdB : 0 < dB)
    (p q : Fin (AuxLRA_len dA dB s)) :
    ((AuxLRA_col dA dB s hdA hdB q : ℕ) : ℤ) -
      ((AuxLRA_row dA dB s hdA p : ℕ) : ℤ) =
        s + ((q : ℕ) : ℤ) - (p : ℕ) := by
  rw [AuxLRA_col_val, AuxLRA_row_val]
  ring

def AuxLRA_kOf (dA dB : ℕ) (hdA : 0 < dA) (hdB : 0 < dB)
    (i : Fin dA) (j : Fin dB) : Fin (dA + dB - 1) :=
  ⟨j.val + (dA - 1) - i.val, by
    have hi : i.val ≤ dA - 1 := Nat.le_pred_of_lt i.isLt
    have : i.val ≤ j.val + (dA - 1) := le_trans hi (Nat.le_add_left _ _)
    omega⟩

theorem AuxLRA_off_kOf {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (i : Fin dA) (j : Fin dB) :
    AuxLRA_off dA dB (AuxLRA_kOf dA dB hdA hdB i j) = (j : ℕ) - (i : ℕ) := by
  unfold AuxLRA_off AuxLRA_kOf
  have hi : i.val ≤ dA - 1 := Nat.le_pred_of_lt i.isLt
  have hle : i.val ≤ j.val + (dA - 1) := le_trans hi (Nat.le_add_left _ _)
  have hsub : ((j.val + (dA - 1) - i.val : ℕ) : ℤ) =
      (j : ℕ) + ((dA - 1 : ℕ) : ℤ) - (i : ℕ) := by
    rw [Nat.cast_sub hle, Nat.cast_add]
  have hd : ((dA - 1 : ℕ) : ℤ) = (dA : ℤ) - 1 := by
    rw [Nat.cast_sub hdA, Nat.cast_one]
  rw [hsub, hd]
  ring

def AuxLRA_diagVec {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (M : Matrix (Fin dA) (Fin dB) ℂ) (s : ℤ) :
    Fin (AuxLRA_len dA dB s) → ℂ :=
  fun p => M (AuxLRA_row dA dB s hdA p) (AuxLRA_col dA dB s hdA hdB p)

def AuxLRA_put {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (s : ℤ) (v : Fin (AuxLRA_len dA dB s) → ℂ) :
    Matrix (Fin dA) (Fin dB) ℂ :=
  fun i j => ∑ p : Fin (AuxLRA_len dA dB s),
    if i = AuxLRA_row dA dB s hdA p ∧ j = AuxLRA_col dA dB s hdA hdB p then v p else 0

theorem AuxLRA_put_apply {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (s : ℤ) (v : Fin (AuxLRA_len dA dB s) → ℂ)
    (p : Fin (AuxLRA_len dA dB s)) :
    AuxLRA_put hdA hdB s v (AuxLRA_row dA dB s hdA p)
      (AuxLRA_col dA dB s hdA hdB p) = v p := by
  unfold AuxLRA_put
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hqp
    split_ifs with hif
    · exact (hqp (AuxLRA_row_injective hdA hif.1.symm)).elim
    · rfl
  · intro hp; exact (hp (Finset.mem_univ p)).elim

theorem AuxLRA_put_off {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (s : ℤ) (v : Fin (AuxLRA_len dA dB s) → ℂ)
    (i : Fin dA) (j : Fin dB)
    (h : ((j : ℕ) : ℤ) - (i : ℕ) ≠ s) :
    AuxLRA_put hdA hdB s v i j = 0 := by
  unfold AuxLRA_put
  apply Finset.sum_eq_zero
  intro p _
  split_ifs with hif
  · rcases hif with ⟨hi, hj⟩
    have := AuxLRA_off_row_col (s := s) hdA hdB p p
    simp at this
    subst hi; subst hj
    exact (h this).elim
  · rfl

theorem AuxLRA_ht {L r : ℕ} (hr : 1 ≤ r) (h : r ≤ L) : L - r + 1 ≤ L := by omega

def AuxLRA_embed (L r : ℕ) (hr : 1 ≤ r) (h : r ≤ L) :
    (Fin (L - r + 1) → ℂ) →ₗ[ℂ] (Fin L → ℂ) where
  toFun c i := ∑ j : Fin (L - r + 1), c j * AuxLRA_tns L i (Fin.castLE (AuxLRA_ht hr h) j)
  map_add' x y := by
    ext i
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp [mul_assoc, Finset.mul_sum, smul_eq_mul, smul_eq_mul]

theorem AuxLRA_embed_injective {L r : ℕ} (hr : 1 ≤ r) (h : r ≤ L) :
    Function.Injective (AuxLRA_embed L r hr h) := by
  intro c₁ c₂ hc
  apply sub_eq_zero.mp
  refine AuxLRA_few_zeros (AuxLRA_ht hr h) (c₁ - c₂) ?_
  have hfun : AuxLRA_embed L r hr h (c₁ - c₂) = 0 := by
    rw [map_sub, hc, sub_self]
  have hall :
      (Finset.univ.filter (fun i : Fin L =>
        (∑ j : Fin (L - r + 1),
          (c₁ - c₂) j * AuxLRA_tns L i (Fin.castLE (AuxLRA_ht hr h) j)) = 0)) =
        Finset.univ := by
    ext i
    have hi := congrFun hfun i
    simp [AuxLRA_embed] at hi ⊢
    exact hi
  rw [hall, Finset.card_univ, Fintype.card_fin]
  exact AuxLRA_ht hr h


abbrev AuxLRA_κ (dA dB r : ℕ) :=
  {k : Fin (dA + dB - 1) // r ≤ AuxLRA_len dA dB (AuxLRA_off dA dB k)}

theorem AuxLRA_put_add {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (s : ℤ) (v w : Fin (AuxLRA_len dA dB s) → ℂ) :
    AuxLRA_put hdA hdB s (v + w) =
      AuxLRA_put hdA hdB s v + AuxLRA_put hdA hdB s w := by
  ext i j
  simp only [AuxLRA_put, Pi.add_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext p
  split_ifs <;> ring

theorem AuxLRA_put_smul {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (s : ℤ) (a : ℂ) (v : Fin (AuxLRA_len dA dB s) → ℂ) :
    AuxLRA_put hdA hdB s (a • v) = a • AuxLRA_put hdA hdB s v := by
  ext i j
  simp only [AuxLRA_put, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  ext p
  split_ifs <;> ring

def AuxLRA_toMatrix (dA dB r : ℕ) (hdA : 0 < dA) (hdB : 0 < dB) (hr : 1 ≤ r) :
    ((k : AuxLRA_κ dA dB r) →
      Fin (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1) → ℂ) →ₗ[ℂ]
      Matrix (Fin dA) (Fin dB) ℂ where
  toFun c := ∑ k : AuxLRA_κ dA dB r,
    AuxLRA_put hdA hdB (AuxLRA_off dA dB k.1)
      (AuxLRA_embed (AuxLRA_len dA dB (AuxLRA_off dA dB k.1)) r hr k.2 (c k))
  map_add' x y := by
    ext i j
    simp only [Pi.add_apply, AuxLRA_put_add, map_add, Finset.sum_add_distrib, Matrix.add_apply]
  map_smul' a x := by
    simp only [Finset.smul_sum, RingHom.id_apply]
    congr 1
    ext k
    simp [Pi.smul_apply, map_smul, AuxLRA_put_smul]

theorem AuxLRA_diagVec_put {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (s : ℤ) (v : Fin (AuxLRA_len dA dB s) → ℂ) :
    AuxLRA_diagVec hdA hdB (AuxLRA_put hdA hdB s v) s = v := by
  ext p
  exact AuxLRA_put_apply hdA hdB s v p

theorem AuxLRA_diagVec_put_ne {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    {s s' : ℤ} (hss : s ≠ s') (v : Fin (AuxLRA_len dA dB s') → ℂ) :
    AuxLRA_diagVec hdA hdB (AuxLRA_put hdA hdB s' v) s = 0 := by
  ext p
  have hoff : ((AuxLRA_col dA dB s hdA hdB p : ℕ) : ℤ) -
      ((AuxLRA_row dA dB s hdA p : ℕ) : ℤ) = s := by
    simpa using AuxLRA_off_row_col hdA hdB p p
  exact AuxLRA_put_off hdA hdB s' v _ _ (fun he => hss (hoff.symm.trans he))

theorem AuxLRA_off_mono {dA dB : ℕ} {k k' : Fin (dA + dB - 1)} (h : k < k') :
    AuxLRA_off dA dB k < AuxLRA_off dA dB k' := by
  unfold AuxLRA_off
  have : (k : ℤ) < (k' : ℤ) := by exact_mod_cast h
  linarith

theorem AuxLRA_off_inj (dA dB : ℕ) : Function.Injective (AuxLRA_off dA dB) := by
  intro k k' h
  have : (k : ℤ) = (k' : ℤ) := by
    have := congrArg (fun z => z + (dA - 1 : ℤ)) h
    simpa [AuxLRA_off] using this
  exact Fin.ext (by exact_mod_cast this)

theorem AuxLRA_kOf_unique {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (i : Fin dA) (j : Fin dB) {k : Fin (dA + dB - 1)}
    (h : AuxLRA_off dA dB k = (j : ℕ) - (i : ℕ)) :
    k = AuxLRA_kOf dA dB hdA hdB i j :=
  AuxLRA_off_inj dA dB (h.trans (AuxLRA_off_kOf hdA hdB i j).symm)

theorem AuxLRA_diagVec_sum {dA dB : ℕ} {ι : Type*} [Fintype ι]
    (hdA : 0 < dA) (hdB : 0 < dB) (s : ℤ)
    (f : ι → Matrix (Fin dA) (Fin dB) ℂ) :
    AuxLRA_diagVec hdA hdB (∑ i, f i) s =
      ∑ i, AuxLRA_diagVec hdA hdB (f i) s := by
  ext p
  simp only [AuxLRA_diagVec]
  rw [Matrix.sum_apply (AuxLRA_row dA dB s hdA p)
    (AuxLRA_col dA dB s hdA hdB p) Finset.univ f, Finset.sum_apply]
  simp [AuxLRA_diagVec]

theorem AuxLRA_diagVec_toMatrix {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hr : 1 ≤ r) (c : (k : AuxLRA_κ dA dB r) →
      Fin (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1) → ℂ)
    (k : AuxLRA_κ dA dB r) :
    AuxLRA_diagVec hdA hdB (AuxLRA_toMatrix dA dB r hdA hdB hr c)
      (AuxLRA_off dA dB k.1) =
      AuxLRA_embed (AuxLRA_len dA dB (AuxLRA_off dA dB k.1)) r hr k.2 (c k) := by
  rw [show AuxLRA_toMatrix dA dB r hdA hdB hr c =
      ∑ k' : AuxLRA_κ dA dB r,
        AuxLRA_put hdA hdB (AuxLRA_off dA dB k'.1)
          (AuxLRA_embed (AuxLRA_len dA dB (AuxLRA_off dA dB k'.1)) r hr k'.2 (c k'))
      from rfl]
  rw [AuxLRA_diagVec_sum]
  rw [Finset.sum_eq_single k]
  · exact AuxLRA_diagVec_put hdA hdB _ _
  · intro k' _ hk'
    exact AuxLRA_diagVec_put_ne hdA hdB
      (fun h => hk' (Subtype.ext (AuxLRA_off_inj dA dB h.symm))) _
  · intro hk; exact (hk (Finset.mem_univ k)).elim

theorem AuxLRA_toMatrix_injective {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hr : 1 ≤ r) :
    Function.Injective (AuxLRA_toMatrix dA dB r hdA hdB hr) := by
  intro c₁ c₂ hc
  ext k p
  have h1 := AuxLRA_diagVec_toMatrix hdA hdB hr c₁ k
  have h2 := AuxLRA_diagVec_toMatrix hdA hdB hr c₂ k
  have : AuxLRA_embed (AuxLRA_len dA dB (AuxLRA_off dA dB k.1)) r hr k.2 (c₁ k) =
      AuxLRA_embed (AuxLRA_len dA dB (AuxLRA_off dA dB k.1)) r hr k.2 (c₂ k) := by
    rw [← h1, ← h2, hc]
  exact congrFun (AuxLRA_embed_injective hr k.2 this) p

/- Window counting: (dA-r+1)(dB-r+1) parameter pairs label the long diagonals. -/

def AuxLRA_iXY {dA r : ℕ} (hdA : 0 < dA) (hr : 1 ≤ r) (hrA : r ≤ dA)
    (x : Fin (dA - r + 1)) : Fin dA :=
  ⟨x.val, by have := x.isLt; omega⟩

def AuxLRA_jXY {dA dB r : ℕ} (hdA : 0 < dA) (hAB : dA ≤ dB) (hr : 1 ≤ r)
    (hrA : r ≤ dA) (y : Fin (dB - r + 1)) : Fin dB :=
  ⟨y.val, by have := y.isLt; omega⟩

theorem AuxLRA_imin_le_x {dA dB r : ℕ} (hdA : 0 < dA) (hAB : dA ≤ dB)
    (hr : 1 ≤ r) (hrA : r ≤ dA)
    (x : Fin (dA - r + 1)) (y : Fin (dB - r + 1)) :
    AuxLRA_iMin dA dB ((y : ℕ) - (x : ℕ)) ≤ (x : ℕ) := by
  unfold AuxLRA_iMin
  apply max_le
  · exact Nat.cast_nonneg _
  · have : -((y : ℕ) - (x : ℕ) : ℤ) ≤ (x : ℕ) := by
      have : 0 ≤ (y : ℤ) := Nat.cast_nonneg _
      linarith
    exact this

theorem AuxLRA_xr_le_imax {dA dB r : ℕ} (hdA : 0 < dA) (hAB : dA ≤ dB)
    (hr : 1 ≤ r) (hrA : r ≤ dA)
    (x : Fin (dA - r + 1)) (y : Fin (dB - r + 1)) :
    (x : ℕ) + r - 1 ≤ AuxLRA_iMax dA dB ((y : ℕ) - (x : ℕ)) := by
  unfold AuxLRA_iMax
  apply le_min
  · have : (x : ℤ) + r - 1 ≤ (dA : ℤ) - 1 := by
      have hx : (x : ℕ) ≤ dA - r := by
        have := x.isLt
        omega
      have : ((dA - r : ℕ) : ℤ) = (dA : ℤ) - r := by
        rw [Nat.cast_sub hrA]
      have : (x : ℤ) ≤ (dA : ℤ) - r := by
        exact_mod_cast (by
          have : (x : ℕ) ≤ dA - r := hx
          exact this)
      linarith
    exact this
  · have hy : (y : ℕ) ≤ dB - r := by
      have := y.isLt
      omega
    have : (x : ℤ) + r - 1 ≤ (dB : ℤ) - 1 - ((y : ℕ) - (x : ℕ)) := by
      have : ((dB - r : ℕ) : ℤ) = (dB : ℤ) - r := by
        have : r ≤ dB := le_trans hrA hAB
        rw [Nat.cast_sub this]
      linarith
    exact this

theorem AuxLRA_window_len {dA dB r : ℕ} (hdA : 0 < dA) (hAB : dA ≤ dB)
    (hr : 1 ≤ r) (hrA : r ≤ dA)
    (x : Fin (dA - r + 1)) (y : Fin (dB - r + 1)) :
    r ≤ AuxLRA_len dA dB ((y : ℕ) - (x : ℕ)) := by
  have h1 := AuxLRA_imin_le_x (dB := dB) hdA hAB hr hrA x y
  have h2 := AuxLRA_xr_le_imax (dB := dB) hdA hAB hr hrA x y
  have hle : AuxLRA_iMin dA dB ((y : ℕ) - (x : ℕ)) ≤
      AuxLRA_iMax dA dB ((y : ℕ) - (x : ℕ)) := by linarith
  have hlen := AuxLRA_len_eq hle
  have : (r : ℤ) ≤ (AuxLRA_len dA dB ((y : ℕ) - (x : ℕ)) : ℤ) := by
    linarith
  exact_mod_cast this

theorem AuxLRA_window_p_lt {dA dB r : ℕ} (hdA : 0 < dA) (hAB : dA ≤ dB)
    (hr : 1 ≤ r) (hrA : r ≤ dA)
    (x : Fin (dA - r + 1)) (y : Fin (dB - r + 1)) :
    Int.toNat ((x : ℕ) - AuxLRA_iMin dA dB ((y : ℕ) - (x : ℕ))) <
      AuxLRA_len dA dB ((y : ℕ) - (x : ℕ)) - r + 1 := by
  have h1 := AuxLRA_imin_le_x (dB := dB) hdA hAB hr hrA x y
  have h2 := AuxLRA_xr_le_imax (dB := dB) hdA hAB hr hrA x y
  have hle : AuxLRA_iMin dA dB ((y : ℕ) - (x : ℕ)) ≤
      AuxLRA_iMax dA dB ((y : ℕ) - (x : ℕ)) := by linarith
  have hlen := AuxLRA_len_eq hle
  have hnn : 0 ≤ (x : ℕ) - AuxLRA_iMin dA dB ((y : ℕ) - (x : ℕ)) := sub_nonneg.mpr h1
  have hrL : r ≤ AuxLRA_len dA dB ((y : ℕ) - (x : ℕ)) :=
    AuxLRA_window_len hdA hAB hr hrA x y
  have hcast : ((AuxLRA_len dA dB ((y : ℕ) - (x : ℕ)) - r + 1 : ℕ) : ℤ) =
      (AuxLRA_len dA dB ((y : ℕ) - (x : ℕ)) : ℤ) - r + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hrL, Nat.cast_one]
  have : (Int.toNat ((x : ℕ) - AuxLRA_iMin dA dB ((y : ℕ) - (x : ℕ))) : ℤ) <
      ((AuxLRA_len dA dB ((y : ℕ) - (x : ℕ)) - r + 1 : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg hnn, hcast, hlen]
    linarith
  exact Nat.cast_lt.mp this

/-! Window bijection between parameter pairs and long-diagonal slots. -/

theorem AuxLRA_len_le_dA (dA dB : ℕ) (s : ℤ) :
    AuxLRA_len dA dB s ≤ dA := by
  by_cases hle : AuxLRA_iMin dA dB s ≤ AuxLRA_iMax dA dB s
  · have hlen := AuxLRA_len_eq hle
    have : (AuxLRA_len dA dB s : ℤ) ≤ (dA : ℤ) := by
      have himax : AuxLRA_iMax dA dB s ≤ (dA : ℤ) - 1 := min_le_left _ _
      have himin : (0 : ℤ) ≤ AuxLRA_iMin dA dB s := le_max_left _ _
      linarith
    exact_mod_cast this
  · have : AuxLRA_iMax dA dB s - AuxLRA_iMin dA dB s + 1 ≤ 0 := by linarith
    have hz : AuxLRA_len dA dB s = 0 := Int.toNat_of_nonpos this
    omega

theorem AuxLRA_len_le_dB (dA dB : ℕ) (s : ℤ) :
    AuxLRA_len dA dB s ≤ dB := by
  by_cases hle : AuxLRA_iMin dA dB s ≤ AuxLRA_iMax dA dB s
  · have hlen := AuxLRA_len_eq hle
    have : (AuxLRA_len dA dB s : ℤ) ≤ (dB : ℤ) := by
      have himax : AuxLRA_iMax dA dB s ≤ (dB : ℤ) - 1 - s := min_le_right _ _
      have himin : -s ≤ AuxLRA_iMin dA dB s := le_max_right _ _
      linarith
    exact_mod_cast this
  · have : AuxLRA_iMax dA dB s - AuxLRA_iMin dA dB s + 1 ≤ 0 := by linarith
    have hz : AuxLRA_len dA dB s = 0 := Int.toNat_of_nonpos this
    omega

theorem AuxLRA_κ_imin_le_imax {dA dB r : ℕ} (hr : 1 ≤ r) (k : AuxLRA_κ dA dB r) :
    AuxLRA_iMin dA dB (AuxLRA_off dA dB k.1) ≤
      AuxLRA_iMax dA dB (AuxLRA_off dA dB k.1) := by
  have hpos : 0 < AuxLRA_len dA dB (AuxLRA_off dA dB k.1) :=
    Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hr) k.2
  have hz : ¬ AuxLRA_iMax dA dB (AuxLRA_off dA dB k.1) -
      AuxLRA_iMin dA dB (AuxLRA_off dA dB k.1) + 1 ≤ 0 := by
    intro h
    have := Int.toNat_of_nonpos h
    simp [AuxLRA_len] at hpos
    omega
  linarith

abbrev AuxLRA_idx (dA dB r : ℕ) :=
  (k : AuxLRA_κ dA dB r) ×
    Fin (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1)

def AuxLRA_fromWindow_k0 {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA)
    (x : Fin (dA - r + 1)) (y : Fin (dB - r + 1)) : Fin (dA + dB - 1) :=
  AuxLRA_kOf dA dB hdA hdB (AuxLRA_iXY hdA hr hrA x)
    (AuxLRA_jXY (dA := dA) hdA hAB hr hrA y)

theorem AuxLRA_fromWindow_off_eq {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA)
    (x : Fin (dA - r + 1)) (y : Fin (dB - r + 1)) :
    AuxLRA_off dA dB (AuxLRA_fromWindow_k0 hdA hdB hAB hr hrA x y) =
      (y : ℕ) - (x : ℕ) := by
  simpa [AuxLRA_fromWindow_k0, AuxLRA_iXY, AuxLRA_jXY] using
    AuxLRA_off_kOf hdA hdB (AuxLRA_iXY hdA hr hrA x)
      (AuxLRA_jXY (dA := dA) hdA hAB hr hrA y)

theorem AuxLRA_fromWindow_mem {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA)
    (x : Fin (dA - r + 1)) (y : Fin (dB - r + 1)) :
    r ≤ AuxLRA_len dA dB
      (AuxLRA_off dA dB (AuxLRA_fromWindow_k0 hdA hdB hAB hr hrA x y)) := by
  rw [AuxLRA_fromWindow_off_eq]
  exact AuxLRA_window_len hdA hAB hr hrA x y

def AuxLRA_fromWindow_p {dA dB r : ℕ}
    (x : Fin (dA - r + 1)) (y : Fin (dB - r + 1)) : ℕ :=
  Int.toNat ((x : ℕ) - AuxLRA_iMin dA dB ((y : ℕ) - (x : ℕ)))

def AuxLRA_fromWindow {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA)
    (xy : Fin (dA - r + 1) × Fin (dB - r + 1)) : AuxLRA_idx dA dB r :=
  ⟨⟨AuxLRA_fromWindow_k0 hdA hdB hAB hr hrA xy.1 xy.2,
      AuxLRA_fromWindow_mem hdA hdB hAB hr hrA xy.1 xy.2⟩,
    ⟨AuxLRA_fromWindow_p (dA := dA) (dB := dB) (r := r) xy.1 xy.2, by
      have hp := AuxLRA_window_p_lt (dB := dB) hdA hAB hr hrA xy.1 xy.2
      simpa [AuxLRA_fromWindow_p, AuxLRA_fromWindow_off_eq] using hp⟩⟩

theorem AuxLRA_toWindow_x_nonneg {dA dB r : ℕ} {k : AuxLRA_κ dA dB r}
    (p : Fin (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1)) :
    0 ≤ AuxLRA_iMin dA dB (AuxLRA_off dA dB k.1) + (p : ℕ) := by
  have : 0 ≤ AuxLRA_iMin dA dB (AuxLRA_off dA dB k.1) := le_max_left _ _
  linarith

theorem AuxLRA_toWindow_y_nonneg {dA dB r : ℕ} {k : AuxLRA_κ dA dB r}
    (p : Fin (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1)) :
    0 ≤ AuxLRA_iMin dA dB (AuxLRA_off dA dB k.1) + (p : ℕ) +
      AuxLRA_off dA dB k.1 := by
  have : -AuxLRA_off dA dB k.1 ≤ AuxLRA_iMin dA dB (AuxLRA_off dA dB k.1) :=
    le_max_right _ _
  linarith

theorem AuxLRA_toWindow_x_lt {dA dB r : ℕ} (hdA : 0 < dA) (hr : 1 ≤ r)
    (hrA : r ≤ dA) (k : AuxLRA_κ dA dB r)
    (p : Fin (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1)) :
    AuxLRA_iMin dA dB (AuxLRA_off dA dB k.1) + (p : ℕ) <
      ((dA - r + 1 : ℕ) : ℤ) := by
  have hle := AuxLRA_κ_imin_le_imax hr k
  have hlen := AuxLRA_len_eq hle
  have hrL : r ≤ AuxLRA_len dA dB (AuxLRA_off dA dB k.1) := k.2
  have hp : (p : ℕ) + 1 ≤ AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1 :=
    Nat.succ_le_iff.mpr p.isLt
  have hpZ : (p : ℤ) + 1 ≤
      ((AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1 : ℕ) : ℤ) := by
    exact_mod_cast hp
  have hcastL :
      ((AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1 : ℕ) : ℤ) =
        (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) : ℤ) - (r : ℤ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hrL, Nat.cast_one]
  have himax : AuxLRA_iMax dA dB (AuxLRA_off dA dB k.1) ≤ (dA : ℤ) - 1 :=
    min_le_left _ _
  have hDA : ((dA - r + 1 : ℕ) : ℤ) = (dA : ℤ) - (r : ℤ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hrA, Nat.cast_one]
  linarith

theorem AuxLRA_toWindow_y_lt {dA dB r : ℕ} (hAB : dA ≤ dB) (hr : 1 ≤ r)
    (hrA : r ≤ dA) (k : AuxLRA_κ dA dB r)
    (p : Fin (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1)) :
    AuxLRA_iMin dA dB (AuxLRA_off dA dB k.1) + (p : ℕ) +
      AuxLRA_off dA dB k.1 < ((dB - r + 1 : ℕ) : ℤ) := by
  have hle := AuxLRA_κ_imin_le_imax hr k
  have hlen := AuxLRA_len_eq hle
  have hrL : r ≤ AuxLRA_len dA dB (AuxLRA_off dA dB k.1) := k.2
  have hp : (p : ℕ) + 1 ≤ AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1 :=
    Nat.succ_le_iff.mpr p.isLt
  have hpZ : (p : ℤ) + 1 ≤
      ((AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1 : ℕ) : ℤ) := by
    exact_mod_cast hp
  have hcastL :
      ((AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1 : ℕ) : ℤ) =
        (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) : ℤ) - (r : ℤ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hrL, Nat.cast_one]
  have himax : AuxLRA_iMax dA dB (AuxLRA_off dA dB k.1) ≤
      (dB : ℤ) - 1 - AuxLRA_off dA dB k.1 := min_le_right _ _
  have hrB : r ≤ dB := le_trans hrA hAB
  have hDB : ((dB - r + 1 : ℕ) : ℤ) = (dB : ℤ) - (r : ℤ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hrB, Nat.cast_one]
  linarith

def AuxLRA_toWindow {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA)
    (kp : AuxLRA_idx dA dB r) : Fin (dA - r + 1) × Fin (dB - r + 1) :=
  let k := kp.1
  let p := kp.2
  let s := AuxLRA_off dA dB k.1
  let xint := AuxLRA_iMin dA dB s + (p : ℕ)
  let yint := xint + s
  have hxnn := AuxLRA_toWindow_x_nonneg (k := k) p
  have hynn := AuxLRA_toWindow_y_nonneg (k := k) p
  have hxl := AuxLRA_toWindow_x_lt hdA hr hrA k p
  have hyl := AuxLRA_toWindow_y_lt hAB hr hrA k p
  (⟨xint.toNat, Nat.cast_lt.mp (by rwa [Int.toNat_of_nonneg hxnn])⟩,
    ⟨yint.toNat, Nat.cast_lt.mp (by rwa [Int.toNat_of_nonneg hynn])⟩)

theorem AuxLRA_toWindow_fst_int {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) (kp : AuxLRA_idx dA dB r) :
    (((AuxLRA_toWindow hdA hdB hAB hr hrA kp).1 : ℕ) : ℤ) =
      AuxLRA_iMin dA dB (AuxLRA_off dA dB kp.1.1) + (kp.2 : ℕ) := by
  simp [AuxLRA_toWindow, Int.toNat_of_nonneg (AuxLRA_toWindow_x_nonneg kp.2)]

theorem AuxLRA_toWindow_snd_int {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) (kp : AuxLRA_idx dA dB r) :
    (((AuxLRA_toWindow hdA hdB hAB hr hrA kp).2 : ℕ) : ℤ) =
      AuxLRA_iMin dA dB (AuxLRA_off dA dB kp.1.1) + (kp.2 : ℕ) +
        AuxLRA_off dA dB kp.1.1 := by
  simp [AuxLRA_toWindow, Int.toNat_of_nonneg (AuxLRA_toWindow_y_nonneg kp.2)]

theorem AuxLRA_fromWindow_left {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA)
    (xy : Fin (dA - r + 1) × Fin (dB - r + 1)) :
    AuxLRA_toWindow hdA hdB hAB hr hrA (AuxLRA_fromWindow hdA hdB hAB hr hrA xy) =
      xy := by
  ext
  · have hoff := AuxLRA_fromWindow_off_eq hdA hdB hAB hr hrA xy.1 xy.2
    have h1 := AuxLRA_imin_le_x (dB := dB) hdA hAB hr hrA xy.1 xy.2
    have hnn : 0 ≤ (xy.1 : ℕ) - AuxLRA_iMin dA dB ((xy.2 : ℕ) - (xy.1 : ℕ)) :=
      sub_nonneg.mpr h1
    have hfst := AuxLRA_toWindow_fst_int hdA hdB hAB hr hrA
      (AuxLRA_fromWindow hdA hdB hAB hr hrA xy)
    have : (((AuxLRA_toWindow hdA hdB hAB hr hrA
        (AuxLRA_fromWindow hdA hdB hAB hr hrA xy)).1 : ℕ) : ℤ) = (xy.1 : ℕ) := by
      rw [hfst]
      simp [AuxLRA_fromWindow, AuxLRA_fromWindow_p, hoff, Int.toNat_of_nonneg hnn]
    exact_mod_cast this
  · have hoff := AuxLRA_fromWindow_off_eq hdA hdB hAB hr hrA xy.1 xy.2
    have h1 := AuxLRA_imin_le_x (dB := dB) hdA hAB hr hrA xy.1 xy.2
    have hnn : 0 ≤ (xy.1 : ℕ) - AuxLRA_iMin dA dB ((xy.2 : ℕ) - (xy.1 : ℕ)) :=
      sub_nonneg.mpr h1
    have hsnd := AuxLRA_toWindow_snd_int hdA hdB hAB hr hrA
      (AuxLRA_fromWindow hdA hdB hAB hr hrA xy)
    have : (((AuxLRA_toWindow hdA hdB hAB hr hrA
        (AuxLRA_fromWindow hdA hdB hAB hr hrA xy)).2 : ℕ) : ℤ) = (xy.2 : ℕ) := by
      rw [hsnd]
      simp [AuxLRA_fromWindow, AuxLRA_fromWindow_p, hoff, Int.toNat_of_nonneg hnn]
    exact_mod_cast this

theorem AuxLRA_fromWindow_right {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA)
    (kp : AuxLRA_idx dA dB r) :
    AuxLRA_fromWindow hdA hdB hAB hr hrA
      (AuxLRA_toWindow hdA hdB hAB hr hrA kp) = kp := by
  set xy := AuxLRA_toWindow hdA hdB hAB hr hrA kp
  have hfst := AuxLRA_toWindow_fst_int hdA hdB hAB hr hrA kp
  have hsnd := AuxLRA_toWindow_snd_int hdA hdB hAB hr hrA kp
  have hyx : ((xy.2 : ℕ) : ℤ) - ((xy.1 : ℕ) : ℤ) = AuxLRA_off dA dB kp.1.1 := by
    rw [hfst, hsnd]; ring
  have hk : (AuxLRA_fromWindow hdA hdB hAB hr hrA xy).1 = kp.1 := by
    apply Subtype.ext
    have hoff : AuxLRA_off dA dB
        (AuxLRA_fromWindow_k0 hdA hdB hAB hr hrA xy.1 xy.2) =
        AuxLRA_off dA dB kp.1.1 := by
      rw [AuxLRA_fromWindow_off_eq, hyx]
    exact AuxLRA_off_inj dA dB hoff
  have hnn := AuxLRA_toWindow_x_nonneg (k := kp.1) kp.2
  have hpv : ((AuxLRA_fromWindow hdA hdB hAB hr hrA xy).2 : ℕ) = (kp.2 : ℕ) := by
    simp [AuxLRA_fromWindow, AuxLRA_fromWindow_p, AuxLRA_fromWindow_off_eq, hyx]
    have hx : ((xy.1 : ℕ) : ℤ) =
        AuxLRA_iMin dA dB (AuxLRA_off dA dB kp.1.1) + (kp.2 : ℕ) := hfst
    rw [hx, add_sub_cancel_left, Int.toNat_natCast]
  refine Sigma.ext hk ?_
  refine (Fin.heq_ext_iff ?_).mpr hpv
  simp [hk]

theorem AuxLRA_fromWindow_bijective {dA dB r : ℕ} (hdA : 0 < dA)
    (hdB : 0 < dB) (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) :
    Function.Bijective (AuxLRA_fromWindow hdA hdB hAB hr hrA) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨AuxLRA_toWindow hdA hdB hAB hr hrA,
      AuxLRA_fromWindow_left hdA hdB hAB hr hrA,
      AuxLRA_fromWindow_right hdA hdB hAB hr hrA⟩

theorem AuxLRA_param_card {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) :
    Fintype.card (AuxLRA_idx dA dB r) = (dA - r + 1) * (dB - r + 1) := by
  classical
  have h := Fintype.card_congr
    (Equiv.ofBijective _ (AuxLRA_fromWindow_bijective hdA hdB hAB hr hrA))
  simpa [Fintype.card_prod, Fintype.card_fin] using h.symm

def AuxLRA_paramEquiv (dA dB r : ℕ) :
    ((k : AuxLRA_κ dA dB r) →
      Fin (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1) → ℂ) ≃ₗ[ℂ]
      (AuxLRA_idx dA dB r → ℂ) where
  toFun c kp := c kp.1 kp.2
  invFun f k p := f ⟨k, p⟩
  left_inv c := rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem AuxLRA_put_zero {dA dB : ℕ} (hdA : 0 < dA) (hdB : 0 < dB) (s : ℤ) :
    AuxLRA_put hdA hdB s 0 = 0 := by
  ext i j
  simp [AuxLRA_put]

theorem AuxLRA_toMatrix_gt {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hr : 1 ≤ r)
    (c : (k : AuxLRA_κ dA dB r) →
      Fin (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1) → ℂ)
    (smax : ℤ)
    (hmax : ∀ k : AuxLRA_κ dA dB r,
      smax < AuxLRA_off dA dB k.1 → c k = 0)
    (i : Fin dA) (j : Fin dB)
    (hgt : smax < (j : ℕ) - (i : ℕ)) :
    AuxLRA_toMatrix dA dB r hdA hdB hr c i j = 0 := by
  unfold AuxLRA_toMatrix
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hoff : AuxLRA_off dA dB k.1 = (j : ℕ) - (i : ℕ)
  · have : smax < AuxLRA_off dA dB k.1 := by rwa [hoff]
    have hc : c k = 0 := hmax k this
    simp [hc, map_zero, AuxLRA_put_zero]
  · exact AuxLRA_put_off hdA hdB _ _ i j (Ne.symm hoff)

theorem AuxLRA_finrank_param {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) :
    Module.finrank ℂ ((k : AuxLRA_κ dA dB r) →
      Fin (AuxLRA_len dA dB (AuxLRA_off dA dB k.1) - r + 1) → ℂ) =
      (dA - r + 1) * (dB - r + 1) := by
  rw [LinearEquiv.finrank_eq (AuxLRA_paramEquiv dA dB r), Module.finrank_pi,
    AuxLRA_param_card hdA hdB hAB hr hrA]

theorem AuxLRA_schmidt {dA dB : ℕ} (v : Bipartite dA dB) :
    schmidtNumber v = Matrix.rank (coefficientEquiv v) :=
  rfl

theorem AuxLRA_range_dim {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) :
    Module.finrank ℂ
      ((LinearMap.range (AuxLRA_toMatrix dA dB r hdA hdB hr)).map
        coefficientEquiv.symm.toLinearMap) =
      (dA - r + 1) * (dB - r + 1) := by
  rw [LinearEquiv.finrank_map_eq coefficientEquiv.symm,
    LinearMap.finrank_range_of_inj (AuxLRA_toMatrix_injective hdA hdB hr),
    AuxLRA_finrank_param hdA hdB hAB hr hrA]

theorem AuxLRA_range_lower {dA dB r : ℕ} (hdA : 0 < dA) (hdB : 0 < dB)
    (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) :
    HasLowerSchmidtRank
      ((LinearMap.range (AuxLRA_toMatrix dA dB r hdA hdB hr)).map
        coefficientEquiv.symm.toLinearMap) r := by
  classical
  intro v hv hne
  obtain ⟨M, hMmem, hMv⟩ := Submodule.mem_map.mp hv
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hMmem
  have hMne : M ≠ 0 := by
    intro hZ
    apply hne
    rw [← hMv, hZ, map_zero]
  have hcne : c ≠ 0 := by
    intro hZ
    apply hMne
    rw [← hc, hZ, map_zero]
  let supp : Finset (AuxLRA_κ dA dB r) :=
    Finset.univ.filter (fun k => c k ≠ 0)
  have hsupp : supp.Nonempty := by
    by_contra hempty
    have : c = 0 := by
      ext k p
      have : k ∉ supp := fun h => hempty ⟨k, h⟩
      simp [supp, Finset.mem_filter] at this
      simp [this]
    exact hcne this
  let ks := supp.image (fun k => k.1)
  have hks : ks.Nonempty := hsupp.image _
  let kmax_val := ks.max' hks
  obtain ⟨kmax, hkmax_mem, hkmax_eq⟩ := Finset.mem_image.mp (ks.max'_mem hks)
  have hck : c kmax ≠ 0 := by
    have : kmax ∈ supp := hkmax_mem
    simpa [supp, Finset.mem_filter] using this
  have hmax : ∀ k : AuxLRA_κ dA dB r,
      AuxLRA_off dA dB kmax.1 < AuxLRA_off dA dB k.1 → c k = 0 := by
    intro k hkoff
    by_contra hck'
    have hkmem : k ∈ supp := by simp [supp, hck']
    have : k.1 ∈ ks := Finset.mem_image_of_mem _ hkmem
    have hle : k.1 ≤ kmax_val := Finset.le_max' ks k.1 this
    have hlt : kmax.1 < k.1 := by
      by_cases hcmp : kmax.1 < k.1
      · exact hcmp
      · have hge : k.1 ≤ kmax.1 := le_of_not_gt hcmp
        rcases eq_or_lt_of_le hge with heq | hlt'
        · simpa [heq] using hkoff
        · exact (not_lt_of_gt (AuxLRA_off_mono hlt') hkoff).elim
    rw [hkmax_eq] at hlt
    exact (not_lt_of_ge hle hlt).elim
  let s := AuxLRA_off dA dB kmax.1
  let L := AuxLRA_len dA dB (AuxLRA_off dA dB kmax.1)
  let vdiag : Fin L → ℂ := AuxLRA_embed L r hr kmax.2 (c kmax)
  have hvne : vdiag ≠ 0 := by
    intro h
    apply hck
    apply AuxLRA_embed_injective hr kmax.2
    have : AuxLRA_embed L r hr kmax.2 (c kmax) = 0 := h
    rw [this, map_zero]
  have hzeros :
      (Finset.univ.filter (fun i : Fin L => vdiag i = 0)).card < L - r + 1 := by
    by_contra h
    apply hck
    refine AuxLRA_few_zeros (AuxLRA_ht hr kmax.2) (c kmax) ?_
    have hle : L - r + 1 ≤
        (Finset.univ.filter (fun i : Fin L => vdiag i = 0)).card :=
      Nat.le_of_not_lt h
    simpa [vdiag, AuxLRA_embed, L] using hle
  let zeros := Finset.univ.filter (fun i : Fin L => vdiag i = 0)
  let nz := Finset.univ.filter (fun i : Fin L => vdiag i ≠ 0)
  have hnz : r ≤ nz.card := by
    have hsum : zeros.card + nz.card = L := by
      rw [← Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter_not (s := Finset.univ) (t := Finset.univ)
            (fun i : Fin L => vdiag i = 0)),
        Finset.filter_union_filter_not_eq, Finset.card_univ, Fintype.card_fin]
    have hrL : r ≤ L := kmax.2
    have : zeros.card < L - r + 1 := hzeros
    omega
  obtain ⟨spos, hs_sub, hsc⟩ := Finset.exists_subset_card_eq hnz
  let iso := spos.orderIsoOfFin hsc
  let pEmb : Fin r ↪ Fin L :=
    iso.toEmbedding.trans (Function.Embedding.subtype _)
  let rows : Fin r ↪ Fin dA :=
    pEmb.trans ⟨AuxLRA_row dA dB s hdA, AuxLRA_row_injective hdA⟩
  let cols : Fin r ↪ Fin dB :=
    pEmb.trans ⟨AuxLRA_col dA dB s hdA hdB, AuxLRA_col_injective hdA hdB⟩
  have hpEmb_mono {a b : Fin r} (hab : a < b) : pEmb a < pEmb b := by
    have : iso a < iso b := iso.strictMono hab
    exact this
  have hMeq : M = AuxLRA_toMatrix dA dB r hdA hdB hr c := hc.symm
  have htri' : (M.submatrix rows cols).IsLowerTriangular := by
    intro a b hab
    have hab' : a < b := by
      simpa [OrderDual.toDual_lt_toDual] using hab
    have hp : (pEmb a : ℕ) < (pEmb b : ℕ) := hpEmb_mono hab'
    have hoff : ((cols b : ℕ) : ℤ) - ((rows a : ℕ) : ℤ) =
        s + ((pEmb b : ℕ) : ℤ) - (pEmb a : ℕ) := by
      simp only [rows, cols, Function.Embedding.trans_apply,
        Function.Embedding.coeFn_mk]
      simpa [s] using AuxLRA_off_row_col hdA hdB (pEmb a) (pEmb b)
    have hgt : s < ((cols b : ℕ) : ℤ) - ((rows a : ℕ) : ℤ) := by
      have : ((pEmb a : ℕ) : ℤ) < (pEmb b : ℕ) := by exact_mod_cast hp
      linarith
    change M (rows a) (cols b) = 0
    rw [hMeq]
    exact AuxLRA_toMatrix_gt hdA hdB hr c s hmax (rows a) (cols b) hgt
  have hdiag_ne (a : Fin r) : M (rows a) (cols a) ≠ 0 := by
    have hval :
        M (AuxLRA_row dA dB s hdA (pEmb a))
          (AuxLRA_col dA dB s hdA hdB (pEmb a)) = vdiag (pEmb a) := by
      rw [hMeq]
      have hdv := congrFun (AuxLRA_diagVec_toMatrix hdA hdB hr c kmax) (pEmb a)
      simpa [AuxLRA_diagVec, vdiag, s] using hdv
    have ha : pEmb a ∈ spos := (iso a).2
    have hmem : pEmb a ∈ nz := hs_sub ha
    have : vdiag (pEmb a) ≠ 0 := by
      simpa [nz, Finset.mem_filter] using hmem
    -- rows a = AuxLRA_row (pEmb a)
    have hrw : M (rows a) (cols a) =
        M (AuxLRA_row dA dB s hdA (pEmb a))
          (AuxLRA_col dA dB s hdA hdB (pEmb a)) := by
      simp [rows, cols, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    rwa [hrw, hval]
  have hdet : (M.submatrix rows cols).det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular _ htri']
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hdiag_ne a
  have hsub : (M.submatrix rows cols).rank = r := by
    simpa [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hdet
  have : r ≤ M.rank := by
    rw [← hsub]
    exact Matrix.rank_submatrix_le M rows cols
  have hsch : schmidtNumber v = M.rank := by
    have hvM : v = coefficientEquiv.symm M := by
      simpa using hMv.symm
    rw [hvM, AuxLRA_schmidt, LinearEquiv.apply_symm_apply]
  rwa [hsch]

theorem _root_.solution (dA dB r : ℕ)
    (hA : 0 < dA) (hAB : dA ≤ dB) (hr : 1 ≤ r) (hrA : r ≤ dA) :
    ∃ S : Submodule ℂ (Bipartite dA dB), HasLowerSchmidtRank S r ∧
      Module.finrank ℂ S = (dA - r + 1) * (dB - r + 1) := by
  have hdB : 0 < dB := lt_of_lt_of_le hA hAB
  refine ⟨(LinearMap.range (AuxLRA_toMatrix dA dB r hA hdB hr)).map
      coefficientEquiv.symm.toLinearMap, ?_, ?_⟩
  · exact AuxLRA_range_lower hA hdB hAB hr hrA
  · exact AuxLRA_range_dim hA hdB hAB hr hrA

end QAlgorithms.Papers.Independent.Intake100.P43
end
