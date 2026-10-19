-- Prove2me | solution 1 for QAlgorithms.Childs.compressedPhaseOracle_local_action
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:55:14.197764+00:00
-- url     : https://prove2.me/submissions/155c33be-f6aa-4959-aec0-b8da299d1520

import Definitions.Def_QAlgorithms_Defs_CompressedOracle

open QAlgorithms Matrix
namespace CompressedLocal

private noncomputable def c (m : ℕ) : ℝ := (Real.sqrt 2)⁻¹ ^ m
private def sig (b : Bool) : ℂ := if b then -1 else 1
private def phase (m : ℕ) (z : Qubits m) : Matrix (Option (Qubits m)) (Option (Qubits m)) ℂ :=
  Matrix.diagonal fun t => match t with | none => 1 | some v => sig (dotBits z v)
private noncomputable def loc (m : ℕ) (z : Qubits m) :=
  compressionUnitary m * phase m z * compressionUnitary m

private lemma cnorm (m : ℕ) : c m ^ 2 * (2 : ℝ) ^ m = 1 := by
  have h : ((Real.sqrt 2)⁻¹)^2 * 2 = (1 : ℝ) := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hn := (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)).ne'
    field_simp
    nlinarith
  unfold c
  rw [← pow_mul, Nat.mul_comm m 2, pow_mul, ← mul_pow, h, one_pow]

private lemma sig_add (a b : Bool) : sig (a + b) = sig a * sig b := by
  cases a <;> cases b <;> norm_num [sig, Bool.add_eq_xor, Bool.zero_eq_false]

private lemma sig_sum {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    sig (∑ i ∈ s, f i) = ∏ i ∈ s, sig (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sig, Bool.zero_eq_false]
  | @insert a s ha ih => simp [ha, sig_add, ih]

private lemma Centry (m : ℕ) (a b : Option (Qubits m)) :
    compressionUnitary m a b = match a,b with
      | none,none => 0
      | none,some _ => (c m : ℂ)
      | some _,none => (c m : ℂ)
      | some v,some w => (if v = w then 1 else 0) - (c m : ℂ)^2 := by
  cases a <;> cases b <;> simp [compressionUnitary,c]

private lemma Csq (m : ℕ) : compressionUnitary m * compressionUnitary m = 1 := by
  classical
  have hc : ((c m : ℂ)^2 * (2 : ℂ)^m) = 1 := by exact_mod_cast cnorm m
  have hc2 : (2 : ℂ)^m * (c m : ℂ)^2 = 1 := by linear_combination hc
  have hc4 : (c m : ℂ)^4 * (2 : ℂ)^m = (c m : ℂ)^2 := by
    calc _ = (c m : ℂ)^2 * ((c m : ℂ)^2 * (2 : ℂ)^m) := by ring
         _ = _ := by rw [hc]; ring
  ext a b
  cases a with
  | none => cases b <;> simp [Matrix.mul_apply, Fintype.sum_option, Centry,
       ← Finset.mul_sum, ← pow_two, hc2]
  | some a =>
    cases b with
    | none => simp [Matrix.mul_apply, Fintype.sum_option, Centry,
        ← Finset.sum_mul, hc2]
    | some b =>
      simp only [Matrix.mul_apply, Fintype.sum_option, Centry]
      change (c m : ℂ) * c m + ∑ v : Qubits m,
        ((if a = v then 1 else 0) - (c m : ℂ)^2) *
        ((if v = b then 1 else 0) - (c m : ℂ)^2) = _
      simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
      simp [← pow_two, Matrix.one_apply, eq_comm]
      split_ifs <;> linear_combination -hc4

private lemma char_orth (n : ℕ) (a b : Qubits n) :
    (∑ i : Qubits n, sig (dotBits a i) * sig (dotBits b i)) =
      if a = b then (2 : ℂ)^n else 0 := by
  classical
  simp_rw [dotBits, sig_sum, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun k v => sig (a k && v) * sig (b k && v))]
  have h (k : Fin n) :
      (∑ v : Bool, sig (a k && v) * sig (b k && v)) =
        if a k = b k then (2 : ℂ) else 0 := by
    cases a k <;> cases b k <;> norm_num [sig, Bool.add_eq_xor, Bool.zero_eq_false]
  simp_rw [h]
  by_cases hab : a = b
  · subst b; simp
  · rw [if_neg hab]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

private lemma dot_add {m : ℕ} (a b v : Qubits m) :
    dotBits a (b + v) = dotBits a b + dotBits a v := by
  have h (i : Fin m) : (a i && (b i + v i)) = (a i && b i) + (a i && v i) := by
    cases a i <;> cases b i <;> cases v i <;> decide
  simp only [dotBits, Pi.add_apply, h, Finset.sum_add_distrib]

private lemma Hentry (m : ℕ) (a b : Qubits m) :
    hadamardN m a b = (c m : ℂ) * sig (dotBits a b) := by
  have hc : dotBits b a = dotBits a b := by simp only [dotBits, Bool.and_comm]
  simp only [hadamardN, Matrix.of_apply, sig, c, hc]
  split_ifs <;> ring

private lemma Hshift (m : ℕ) (a b v : Qubits m) :
    (∑ u : Qubits m, hadamardN m a (u + v) * hadamardN m u b) =
      if a = b then sig (dotBits a v) else 0 := by
  classical
  have hc : (c m : ℂ)^2 * (2 : ℂ)^m = 1 := by exact_mod_cast cnorm m
  have hd (u : Qubits m) : dotBits u b = dotBits b u := by
    simp only [dotBits, Bool.and_comm]
  simp_rw [Hentry, dot_add, sig_add, hd]
  simp_rw [show ∀ p q r : ℂ, (c m : ℂ) * (p*q) * ((c m : ℂ)*r) =
    (c m : ℂ)^2 * q * (p*r) by intros; ring]
  rw [← Finset.mul_sum, char_orth]
  by_cases hab : a = b
  · subst b; simp only [ite_true]; linear_combination sig (dotBits a v) * hc
  · simp [hab]

private def shift {m : ℕ} (o : Option (Qubits m)) (z : Qubits m) : Qubits m :=
  match o with | none => z | some v => z + v

private lemma HshiftOption (m : ℕ) (a b : Qubits m) (o : Option (Qubits m)) :
    (∑ u : Qubits m, hadamardN m a (shift o u) * hadamardN m u b) =
      if a = b then (match o with | none => (1 : ℂ) | some v => sig (dotBits a v)) else 0 := by
  cases o with
  | some v => exact Hshift m a b v
  | none =>
    have h := Hshift m a b 0
    have hz : dotBits a 0 = false := by
      simp only [dotBits, Pi.zero_apply, Bool.zero_eq_false, Bool.and_false]
      change (∑ _ : Fin m, (0 : Bool)) = 0
      simp
    simpa [shift, hz, sig] using h

private abbrev Reg (n m : ℕ) (W : Type*) :=
  (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m)))

private noncomputable def B (n m : ℕ) (W : Type*) [Fintype W] [DecidableEq W] :
    Matrix (Reg n m W) (Reg n m W) ℂ :=
  Matrix.kronecker (Matrix.kronecker (Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ)
    (hadamardN m)) (1 : Matrix W W ℂ)) (compressAll n m)

private lemma lookup_entry {n m : ℕ} {W : Type*} [DecidableEq W]
    (p q : Reg n m W) : lookupUnitary n m W p q =
      if p = (((q.1.1.1, shift (q.2 q.1.1.1) q.1.1.2), q.1.2), q.2) then 1 else 0 := by
  simp only [lookupUnitary, Matrix.of_apply, Prod.ext_iff, shift]
  congr 1
  apply propext
  cases q.2 q.1.1.1 <;> tauto

private lemma mul_lookup {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (A : Matrix (Reg n m W) (Reg n m W) ℂ) (p q : Reg n m W) :
    (A * lookupUnitary n m W) p q =
      A p (((q.1.1.1, shift (q.2 q.1.1.1) q.1.1.2), q.1.2), q.2) := by
  classical
  simp [Matrix.mul_apply, lookup_entry]

private lemma Bentry {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (p q : Reg n m W) : B n m W p q =
      if p.1.1.1 = q.1.1.1 ∧ p.1.2 = q.1.2 then
        hadamardN m p.1.1.2 q.1.1.2 * compressAll n m p.2 q.2 else 0 := by
  classical
  change ((if p.1.1.1 = q.1.1.1 then 1 else 0) * hadamardN m p.1.1.2 q.1.1.2 *
    (if p.1.2 = q.1.2 then 1 else 0)) * compressAll n m p.2 q.2 = _
  split_ifs <;> simp_all

private lemma phase_entry {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (p q : Reg n m W) : compressedPhaseOracle n m W p q =
      if p.1 = q.1 then
        ∑ t : Fin n → Option (Qubits m),
          compressAll n m p.2 t *
          (match t p.1.1.1 with | none => (1 : ℂ) | some v => sig (dotBits p.1.1.2 v)) *
          compressAll n m t q.2 else 0 := by
  classical
  change (B n m W * lookupUnitary n m W * B n m W) p q = _
  rw [Matrix.mul_apply]
  simp_rw [mul_lookup, Bentry]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  -- Collapse the unchanged query index and workspace.
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  simp only [ite_and, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  by_cases hx : p.1.1.1 = q.1.1.1
  · by_cases hw : p.1.2 = q.1.2
    · simp only [hx, hw, if_true]
      rw [Finset.sum_comm]
      simp_rw [show ∀ (u : Qubits m) (t : Fin n → Option (Qubits m)),
        hadamardN m p.1.1.2 (shift (t q.1.1.1) u) * compressAll n m p.2 t *
          (hadamardN m u q.1.1.2 * compressAll n m t q.2) =
        (compressAll n m p.2 t * compressAll n m t q.2) *
          (hadamardN m p.1.1.2 (shift (t q.1.1.1) u) * hadamardN m u q.1.1.2) by
          intros; ring]
      simp_rw [← Finset.mul_sum, HshiftOption]
      by_cases hz : p.1.1.2 = q.1.1.2
      · simp only [hz, if_true, Prod.ext_iff, hx, hw, and_self]
        apply Finset.sum_congr rfl
        intro t _
        rw [← hx]
        ring
      · simp [hz, Prod.ext_iff, hx, hw]
    · simp [hw, Prod.ext_iff]
  · simp [hx, Prod.ext_iff]

private lemma tensor_conj {n m : ℕ} (x : Fin n) (z : Qubits m)
    (y y' : Fin n → Option (Qubits m)) :
    (∑ t : Fin n → Option (Qubits m), compressAll n m y t *
      (match t x with | none => (1 : ℂ) | some v => sig (dotBits z v)) *
      compressAll n m t y') =
    if ∀ i, i ≠ x → y i = y' i then loc m z (y x) (y' x) else 0 := by
  classical
  let d : Option (Qubits m) → ℂ := fun o =>
    match o with | none => 1 | some v => sig (dotBits z v)
  let f : Fin n → Option (Qubits m) → ℂ := fun i o =>
    compressionUnitary m (y i) o * compressionUnitary m o (y' i)
  let g : Fin n → Option (Qubits m) → ℂ := fun i o =>
    f i o * if i = x then d o else 1
  have hexp (t : Fin n → Option (Qubits m)) :
      compressAll n m y t * d (t x) * compressAll n m t y' = ∏ i, g i (t i) := by
    have hp : (∏ i : Fin n, if i = x then d (t i) else (1 : ℂ)) = d (t x) := by simp
    simp only [g, Finset.prod_mul_distrib, hp, f, compressAll, Matrix.of_apply]
    ring
  change (∑ t, compressAll n m y t * d (t x) * compressAll n m t y') = _
  simp_rw [hexp]
  rw [← Fintype.prod_sum]
  have hne (i : Fin n) (hi : i ≠ x) : (∑ o, g i o) = if y i = y' i then 1 else 0 := by
    have h := congrArg (fun A : Matrix (Option (Qubits m)) (Option (Qubits m)) ℂ => A (y i) (y' i)) (Csq m)
    simpa [g, f, hi, Matrix.mul_apply, Matrix.one_apply] using h
  have heq : (∑ o, g x o) = loc m z (y x) (y' x) := by
    unfold loc phase
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_diagonal]
    simp only [g, f]
    apply Finset.sum_congr rfl
    intro o _
    cases o <;> dsimp [d] <;> ring
  by_cases hy : ∀ i, i ≠ x → y i = y' i
  · rw [if_pos hy]
    calc (∏ i, ∑ o, g i o) = ∑ o, g x o := by
          apply Finset.prod_eq_single x
          · intro i _ hi; rw [hne i hi, if_pos (hy i hi)]
          · simp
         _ = _ := heq
  · rw [if_neg hy]
    obtain ⟨i, hi, hyy⟩ := not_forall.mp hy |>.imp fun i h => by simpa using h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hne i hi, if_neg hyy])

private lemma fiber_sum {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (x : Fin n) (y : Fin n → A) (F : (Fin n → A) → ℂ) :
    (∑ y' : Fin n → A, if ∀ i, i ≠ x → y i = y' i then F y' else 0) =
      ∑ o : A, F (Function.update y x o) := by
  classical
  let e := Equiv.funSplitAt x A
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hcond (o : A) (r : {i : Fin n // i ≠ x} → A) :
      (∀ i, i ≠ x → y i = e.symm (o,r) i) ↔ r = fun i => y i.1 := by
    constructor
    · intro h; ext i
      simpa [e, Equiv.funSplitAt, Equiv.piSplitAt, i.2] using (h i.1 i.2).symm
    · intro h i hi
      subst r
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hi]
  simp_rw [hcond]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro o _
  congr 1

end CompressedLocal

open CompressedLocal

theorem solution {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (ψ : EuclideanSpace ℂ (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))))
    (a : (Fin n × Qubits m) × W) (y : Fin n → Option (Qubits m)) :
    act (compressedPhaseOracle n m W) ψ (a, y) =
      ∑ o : Option (Qubits m),
        (compressionUnitary m * Matrix.diagonal (fun t : Option (Qubits m) =>
          match t with
          | none => (1 : ℂ)
          | some v => if dotBits a.1.2 v then -1 else 1) * compressionUnitary m)
            (y a.1.1) o * ψ (a, Function.update y a.1.1 o) := by
  classical
  change (∑ q : Reg n m W, compressedPhaseOracle n m W (a,y) q * ψ q) = _
  simp_rw [phase_entry]
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [tensor_conj, ite_mul, zero_mul]
  rw [fiber_sum]
  simp only [Function.update_self]
  rfl
