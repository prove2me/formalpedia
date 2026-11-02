-- Prove2me | solution 1 for TensorNP.Eigen.colorTensor_encoding_transfer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:14:04.595101+00:00
-- url     : https://prove2.me/submissions/be157a7f-27f7-4235-8718-cf85ec60ae1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_TensorNP_Eigen_colorTensor_canonical_encoder
import Definitions.Def_TensorNP_Eigen_Construction

open ProjSchedTW.Complexity

/-- Read the binary digits of the first separator-terminated code.  This is a
    mathematical decoder, not yet a stack or Turing-machine program. -/
private def readFirstBits : List BSym → List Bool
  | .zero :: rest => false :: readFirstBits rest
  | .one :: rest => true :: readFirstBits rest
  | _ => []

private theorem readFirstBits_digits (digits : List Bool) (tail : List BSym) :
    readFirstBits ((digits.map fun b ↦ if b then BSym.one else BSym.zero) ++ BSym.sep :: tail) =
      digits := by
  induction digits with
  | nil => rfl
  | cons b digits ih =>
    cases b <;> simp [readFirstBits, ih]

private theorem readFirstBits_encNat (n : ℕ) (tail : List BSym) :
    readFirstBits (encNat n ++ tail) = n.bits := by
  simpa [encNat, List.append_assoc] using readFirstBits_digits n.bits tail

private theorem encNat_not_nil (n : ℕ) : encNat n ≠ [] := by
  simp [encNat]

/-- Canonical binary natural-number codes are uniquely decodable from the front,
    even in the presence of arbitrary trailing input. -/
theorem tensor_encNat_prefix_unique (m n : ℕ) (s t : List BSym)
    (h : encNat m ++ s = encNat n ++ t) : m = n ∧ s = t := by
  have hb : m.bits = n.bits := by
    have he := congrArg readFirstBits h
    simpa only [readFirstBits_encNat] using he
  have hmn : m = n := by
    apply Nat.eq_of_testBit_eq
    intro i
    simpa only [Nat.testBit_eq_inth] using congrArg (fun bs : List Bool ↦ bs.getI i) hb
  subst n
  exact ⟨rfl, (List.append_right_inj (encNat m)).mp h⟩

/-- A canonical sequence of separator-terminated natural-number codes uniquely
    determines the encoded natural-number list. -/
theorem tensor_encNats_injective : Function.Injective encNats := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys =>
      have h' : encNat y ++ encNats ys = [] := by simpa [encNats] using h.symm
      exact False.elim (encNat_not_nil y (List.append_eq_nil_iff.mp h').1)
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have h' : encNat x ++ encNats xs = [] := by simpa [encNats] using h
      exact False.elim (encNat_not_nil x (List.append_eq_nil_iff.mp h').1)
    | cons y ys =>
      have h' : encNat x ++ encNats xs = encNat y ++ encNats ys := by
        simpa [encNats] using h
      obtain ⟨hxy, htail⟩ := tensor_encNat_prefix_unique x y (encNats xs) (encNats ys) h'
      have hxs : xs = ys := ih htail
      simp [hxy, hxs]


private theorem encNat_head_ne_minus (n : ℕ) (tail : List BSym) :
    (encNat n ++ tail).head? ≠ some BSym.minus := by
  unfold encNat
  cases hb : n.bits with
  | nil => simp [hb]
  | cons b bs => cases b <;> simp [hb]

/-- Signed binary integer codes are also prefix-unique, including their
    optional leading minus sign and the remaining input. -/
theorem tensor_encInt_prefix_unique (m n : ℤ) (s t : List BSym)
    (h : encInt m ++ s = encInt n ++ t) : m = n ∧ s = t := by
  by_cases hm : m < 0
  · by_cases hn : n < 0
    · have h' : encNat m.natAbs ++ s = encNat n.natAbs ++ t := by
        simpa [encInt, hm, hn, List.append_assoc] using h
      obtain ⟨ha, ht⟩ := tensor_encNat_prefix_unique m.natAbs n.natAbs s t h'
      have hz := congrArg (fun x : ℕ ↦ (x : ℤ)) ha
      rw [Int.ofNat_natAbs_of_nonpos (le_of_lt hm),
        Int.ofNat_natAbs_of_nonpos (le_of_lt hn)] at hz
      have heq : m = n := by omega
      exact ⟨heq, ht⟩
    · have hh := congrArg List.head? h
      have hbad : (encNat n.natAbs ++ t).head? = some BSym.minus := by
        simpa [encInt, hm, hn, List.append_assoc] using hh.symm
      exact False.elim (encNat_head_ne_minus n.natAbs t hbad)
  · by_cases hn : n < 0
    · have hh := congrArg List.head? h
      have hbad : (encNat m.natAbs ++ s).head? = some BSym.minus := by
        simpa [encInt, hm, hn, List.append_assoc] using hh
      exact False.elim (encNat_head_ne_minus m.natAbs s hbad)
    · have h' : encNat m.natAbs ++ s = encNat n.natAbs ++ t := by
        simpa [encInt, hm, hn, List.append_assoc] using h
      obtain ⟨ha, ht⟩ := tensor_encNat_prefix_unique m.natAbs n.natAbs s t h'
      have hz := congrArg (fun x : ℕ ↦ (x : ℤ)) ha
      rw [Int.ofNat_natAbs_of_nonneg (le_of_not_gt hm),
        Int.ofNat_natAbs_of_nonneg (le_of_not_gt hn)] at hz
      exact ⟨hz, ht⟩

/-- The exact numerator/denominator encoding used by tensorCode is
    prefix-unique for rationals and preserves the unconsumed suffix. -/
theorem tensor_encRat_prefix_unique (q r : ℚ) (s t : List BSym)
    (h : TensorNP.Eigen.encRat q ++ s = TensorNP.Eigen.encRat r ++ t) : q = r ∧ s = t := by
  have h' : encInt q.num ++ (encNat q.den ++ s) = encInt r.num ++ (encNat r.den ++ t) := by
    simpa [TensorNP.Eigen.encRat, List.append_assoc] using h
  obtain ⟨hnum, hrest⟩ := tensor_encInt_prefix_unique q.num r.num _ _ h'
  obtain ⟨hden, htail⟩ := tensor_encNat_prefix_unique q.den r.den s t hrest
  exact ⟨Rat.ext hnum hden, htail⟩


private theorem encRat_not_nil (q : ℚ) : TensorNP.Eigen.encRat q ≠ [] := by
  intro h
  have h' : encInt q.num = [] ∧ encNat q.den = [] := by
    apply List.append_eq_nil_iff.mp
    simpa [TensorNP.Eigen.encRat] using h
  exact encNat_not_nil q.den h'.2

private def encodeRatList (xs : List ℚ) : List BSym := xs.flatMap TensorNP.Eigen.encRat

/-- A concatenation of canonical rational codes uniquely determines the
    entire rational list. -/
theorem tensor_encRatList_injective : Function.Injective encodeRatList := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys =>
      have h' : TensorNP.Eigen.encRat y ++ encodeRatList ys = [] := by
        simpa [encodeRatList] using h.symm
      exact False.elim (encRat_not_nil y (List.append_eq_nil_iff.mp h').1)
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil =>
      have h' : TensorNP.Eigen.encRat x ++ encodeRatList xs = [] := by
        simpa [encodeRatList] using h
      exact False.elim (encRat_not_nil x (List.append_eq_nil_iff.mp h').1)
    | cons y ys =>
      have h' : TensorNP.Eigen.encRat x ++ encodeRatList xs =
          TensorNP.Eigen.encRat y ++ encodeRatList ys := by
        simpa [encodeRatList] using h
      obtain ⟨hxy, htail⟩ := tensor_encRat_prefix_unique x y (encodeRatList xs) (encodeRatList ys) h'
      have hxs : xs = ys := ih htail
      simp [hxy, hxs]


/-- A row-major flattening of a fixed rectangular matrix determines every
    entry, even when one of its dimensions is zero. -/
theorem tensor_matrix_flatten_injective {α : Type} {r c : ℕ}
    (f g : Fin r → Fin c → α)
    (h : (List.ofFn fun i ↦ List.ofFn (f i)).flatten =
      (List.ofFn fun i ↦ List.ofFn (g i)).flatten) : f = g := by
  induction r with
  | zero =>
    funext i
    exact Fin.elim0 i
  | succ r ih =>
    have h' : List.ofFn (f 0) ++ (List.ofFn fun i : Fin r ↦ List.ofFn (f i.succ)).flatten =
        List.ofFn (g 0) ++ (List.ofFn fun i : Fin r ↦ List.ofFn (g i.succ)).flatten := by
      simpa [List.ofFn_succ] using h
    have hrow : f 0 = g 0 := List.ofFn_injective (List.append_inj_left h' (by simp))
    have htail := List.append_inj_right h' (by simp)
    have hs : (fun i : Fin r ↦ f i.succ) = (fun i : Fin r ↦ g i.succ) := ih _ _ htail
    funext i
    refine Fin.cases ?_ ?_ i
    · exact hrow
    · intro j
      exact congrFun hs j



/-- Flattening equal-length blocks is injective on their ordered family. -/
private theorem equal_blocks_flatten_injective {α : Type} {n L : ℕ}
    (f g : Fin n → List α) (hf : ∀ i, (f i).length = L) (hg : ∀ i, (g i).length = L)
    (h : (List.ofFn f).flatten = (List.ofFn g).flatten) : f = g := by
  induction n with
  | zero =>
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    have h' : f 0 ++ (List.ofFn fun i : Fin n ↦ f i.succ).flatten =
        g 0 ++ (List.ofFn fun i : Fin n ↦ g i.succ).flatten := by
      simpa [List.ofFn_succ] using h
    have hlen : (f 0).length = (g 0).length := by rw [hf 0, hg 0]
    have hhead : f 0 = g 0 := List.append_inj_left h' hlen
    have htail := List.append_inj_right h' hlen
    have hs : (fun i : Fin n ↦ f i.succ) = (fun i : Fin n ↦ g i.succ) :=
      ih _ _ (fun i ↦ hf i.succ) (fun i ↦ hg i.succ) htail
    funext i
    refine Fin.cases ?_ ?_ i
    · exact hhead
    · intro j
      exact congrFun hs j

private def tensorEntries {n : ℕ} (A : Fin n → Fin n → Fin n → ℚ) : List ℚ :=
  (List.ofFn fun i : Fin n ↦ (List.ofFn fun j : Fin n ↦ List.ofFn (A i j)).flatten).flatten

private theorem tensorCode_as_entries {n : ℕ} (A : Fin n → Fin n → Fin n → ℚ) :
    TensorNP.Eigen.tensorCode A = encNat n ++ encodeRatList (tensorEntries A) := by
  simp [TensorNP.Eigen.tensorCode, encodeRatList, tensorEntries, List.flatMap_def,
    List.map_flatten, List.flatten_flatten, List.map_ofFn, Function.comp_def]

/-- Canonical rational tensor encoding is injective at fixed dimension. -/
theorem tensor_tensorCode_injective_fixed {n : ℕ} :
    Function.Injective (TensorNP.Eigen.tensorCode (n := n)) := by
  intro A B h
  rw [tensorCode_as_entries, tensorCode_as_entries] at h
  have hentry : tensorEntries A = tensorEntries B :=
    tensor_encRatList_injective ((List.append_right_inj (encNat n)).mp h)
  let rowA : Fin n → List ℚ := fun i ↦ (List.ofFn fun j : Fin n ↦ List.ofFn (A i j)).flatten
  let rowB : Fin n → List ℚ := fun i ↦ (List.ofFn fun j : Fin n ↦ List.ofFn (B i j)).flatten
  have hlenA (i : Fin n) : (rowA i).length = n * n := by
    simp [rowA, List.length_flatten, List.map_ofFn, Function.comp_def,
      List.length_ofFn, List.ofFn_const, List.sum_replicate_nat]
  have hlenB (i : Fin n) : (rowB i).length = n * n := by
    simp [rowB, List.length_flatten, List.map_ofFn, Function.comp_def,
      List.length_ofFn, List.ofFn_const, List.sum_replicate_nat]
  have hrows : rowA = rowB := equal_blocks_flatten_injective rowA rowB hlenA hlenB hentry
  funext i
  apply tensor_matrix_flatten_injective
  exact congrFun hrows i


/-- The first canonical natural-number block determines the tensor dimension. -/
theorem tensor_tensorCode_dimension_unique {m n : ℕ}
    (A : Fin m → Fin m → Fin m → ℚ) (B : Fin n → Fin n → Fin n → ℚ)
    (h : TensorNP.Eigen.tensorCode A = TensorNP.Eigen.tensorCode B) : m = n := by
  rw [tensorCode_as_entries, tensorCode_as_entries] at h
  exact (tensor_encNat_prefix_unique m n _ _ h).1

/-- Canonical tensor codes cannot represent two distinct rational tensors,
    even when their dimensions are initially allowed to differ. -/
theorem tensor_tensorCode_unique {m n : ℕ}
    (A : Fin m → Fin m → Fin m → ℚ) (B : Fin n → Fin n → Fin n → ℚ)
    (h : TensorNP.Eigen.tensorCode A = TensorNP.Eigen.tensorCode B) : m = n ∧ HEq A B := by
  have hmn := tensor_tensorCode_dimension_unique A B h
  constructor
  · exact hmn
  · subst n
    exact heq_of_eq (tensor_tensorCode_injective_fixed h)



open ProjSchedTW.Complexity TensorNP.Eigen

/-- The empty string is not a tensor code, hence can be the reduction's
    fixed negative output when the input is not a canonical graph code. -/
theorem tensor_empty_not_zeroEig : ([] : List BSym) ∉ tensorZeroEigLangR := by
  rintro ⟨n, A, heig, hcode⟩
  have hn : 0 < (encNat n).length := by simp [encNat]
  have hl : 0 < (tensorCode A).length := by
    simp only [tensorCode, List.length_append]
    omega
  have : (tensorCode A).length = 0 := by simpa using congrArg List.length hcode.symm
  omega

/-- Exact graph-to-tensor mapping on valid inputs plus the empty-string
    fallback yields the semantic soundness clause of the machine-transfer
    obligation. No running-time property is assumed here. -/
theorem tensor_encoding_soundness_of_fallback
    (f : List BSym → List BSym)
    (hmap : ∀ (v : ℕ) (G : SimpleGraph (Fin v)),
      f (TensorNP.Eigen.graphCode G) = TensorNP.Eigen.tensorCode (TensorNP.Eigen.colorTensor G))
    (hbad : ∀ w, (¬ ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = TensorNP.Eigen.graphCode G) →
      f w = []) :
    ∀ w, f w ∈ TensorNP.Eigen.tensorZeroEigLangR →
      ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = TensorNP.Eigen.graphCode G ∧
        TensorNP.Eigen.IsEigenvalue (TensorNP.Eigen.castTensor ℝ (TensorNP.Eigen.colorTensor G)) 0 := by
  classical
  intro w hout
  have hvalid : ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = TensorNP.Eigen.graphCode G := by
    by_contra hn
    rw [hbad w hn] at hout
    exact tensor_empty_not_zeroEig hout
  obtain ⟨v, G, rfl⟩ := hvalid
  rw [hmap v G] at hout
  obtain ⟨n, A, heig, hcode⟩ := hout
  have hcode' : TensorNP.Eigen.tensorCode (TensorNP.Eigen.colorTensor G) =
      TensorNP.Eigen.tensorCode A := hcode
  obtain ⟨hn, hA⟩ := tensor_tensorCode_unique (TensorNP.Eigen.colorTensor G) A hcode'
  subst n
  have heq : TensorNP.Eigen.colorTensor G = A := eq_of_heq hA
  subst A
  exact ⟨v, G, rfl, by simpa using heig⟩


/-- An exact canonical encoder, with empty output on invalid input, suffices
    for the full graph-to-tensor encoding-transfer obligation. -/
theorem tensor_transfer_of_canonical_encoder
    (henc : ∃ f : List BSym → List BSym, CookPvsNP.PolyTimeComputable f ∧
      (∀ (v : ℕ) (G : SimpleGraph (Fin v)),
        f (TensorNP.Eigen.graphCode G) = TensorNP.Eigen.tensorCode (TensorNP.Eigen.colorTensor G)) ∧
      (∀ w, (¬ ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = TensorNP.Eigen.graphCode G) → f w = [])) :
    ∃ f : List BSym → List BSym, CookPvsNP.PolyTimeComputable f ∧
      (∀ (v : ℕ) (G : SimpleGraph (Fin v)),
        f (TensorNP.Eigen.graphCode G) = TensorNP.Eigen.tensorCode (TensorNP.Eigen.colorTensor G)) ∧
      (∀ w, f w ∈ TensorNP.Eigen.tensorZeroEigLangR →
        ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = TensorNP.Eigen.graphCode G ∧
          TensorNP.Eigen.IsEigenvalue (TensorNP.Eigen.castTensor ℝ (TensorNP.Eigen.colorTensor G)) 0) := by
  obtain ⟨f, hpoly, hmap, hbad⟩ := henc
  exact ⟨f, hpoly, hmap, tensor_encoding_soundness_of_fallback f hmap hbad⟩


/-- Source-specific graph-to-tensor transfer, conditional on the executable
    canonical encoder with empty fallback. -/
theorem solution :
    ∃ f : List BSym → List BSym, CookPvsNP.PolyTimeComputable f ∧
      (∀ (v : ℕ) (G : SimpleGraph (Fin v)),
        f (TensorNP.Eigen.graphCode G) = TensorNP.Eigen.tensorCode (TensorNP.Eigen.colorTensor G)) ∧
      (∀ w, f w ∈ TensorNP.Eigen.tensorZeroEigLangR →
        ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = TensorNP.Eigen.graphCode G ∧
          TensorNP.Eigen.IsEigenvalue (TensorNP.Eigen.castTensor ℝ (TensorNP.Eigen.colorTensor G)) 0) := by
  exact tensor_transfer_of_canonical_encoder TensorNP.Eigen.colorTensor_canonical_encoder
