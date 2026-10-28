-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P40.timeSharing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:08:54.853688+00:00
-- url     : https://prove2.me/submissions/97abb8ac-9f6c-4495-a10d-bbe59340565c

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40
noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

open scoped ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

namespace T40T

section Mat
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma sqrt_psd (Y : Matrix n n ℂ) : (cfc Real.sqrt Y).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg (fun t _ => Real.sqrt_nonneg t)

lemma sqrt_mul_sqrt {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma psd_decomp {Q : Matrix n n ℂ} (hQ : Q.PosSemidef) :
    ∃ S : Matrix n n ℂ, Q = Sᴴ * S :=
  ⟨cfc Real.sqrt Q, by rw [(sqrt_psd Q).1.eq, sqrt_mul_sqrt hQ]⟩

lemma sum_psd {ι : Type*} (s : Finset ι) (A : ι → Matrix n n ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a).add ih

lemma tr_psd_mul {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (P * Q).trace := by
  have hR : (cfc Real.sqrt Q)ᴴ = cfc Real.sqrt Q := (sqrt_psd Q).1.eq
  have h := (hP.conjTranspose_mul_mul_same (cfc Real.sqrt Q)).trace_nonneg
  rw [hR, Matrix.trace_mul_comm, ← Matrix.mul_assoc, sqrt_mul_sqrt hQ, Matrix.trace_mul_comm] at h
  exact h
end Mat

/-- tensor product of `k` matrices, indexed by functions. -/
def T {k : ℕ} {ι : Type*} (A : Fin k → Matrix ι ι ℂ) : Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  Matrix.of fun y y' => ∏ i, A i (y i) (y' i)

lemma T_mul {k : ℕ} {ι : Type*} [Fintype ι] (A B : Fin k → Matrix ι ι ℂ) :
    T A * T B = T (fun i => A i * B i) := by
  ext y y'
  simp only [T, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.prod_sum]
  simp_rw [Finset.prod_mul_distrib]

lemma T_conj {k : ℕ} {ι : Type*} (A : Fin k → Matrix ι ι ℂ) :
    (T A)ᴴ = T (fun i => (A i)ᴴ) := by
  ext y y'
  simp [T, Matrix.conjTranspose_apply]

lemma T_psd {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Fin k → Matrix ι ι ℂ)
    (h : ∀ i, (A i).PosSemidef) : (T A).PosSemidef := by
  choose S hS using fun i => psd_decomp (h i)
  have : T A = (T S)ᴴ * T S := by
    rw [T_conj, T_mul]; congr 1; funext i; exact hS i
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma tr_pi {k : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (Φ : Superop ι κ) (X : Matrix (Fin k → ι) (Fin k → ι) ℂ) (σ : Fin k → Matrix κ κ ℂ) :
    (piSuperop (fun _ : Fin k => Φ) X * T σ).trace =
      ∑ x : Fin k → ι, ∑ x' : Fin k → ι, X x x' * ∏ i, (Φ (Matrix.single (x i) (x' i) 1) * σ i).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, piSuperop, T, Matrix.of_apply]
  simp_rw [Fintype.prod_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, y]; rw [Finset.sum_comm]
  conv_lhs => enter [2, y, 2, x]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.prod_mul_distrib]; ring

section Acc
variable {s : ℕ} {C : ClassicalChannel s}

lemma single_inBlocks {d : ℕ} (block : Fin d → ℕ) {a b : Fin d} (h : block a = block b) :
    InBlocks block (Matrix.single a b (1 : ℂ)) := by
  intro c e hce
  rw [Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'; exact (hce h).elim
  · rfl

/-- a canonical representative of the block of `y`. -/
def rep (A : Access C) (y : Fin A.dim) : Fin A.dim :=
  @Classical.epsilon (Fin A.dim) ⟨⟨0, A.dim_pos⟩⟩ (fun z => A.block z = A.block y)

lemma rep_spec (A : Access C) (y : Fin A.dim) : A.block (rep A y) = A.block y :=
  @Classical.epsilon_spec (Fin A.dim) (fun z => A.block z = A.block y) ⟨y, rfl⟩

lemma rep_eq (A : Access C) {y y' : Fin A.dim} (h : A.block y = A.block y') :
    rep A y = rep A y' := by
  unfold rep; rw [h]

def E (A : Access C) (a b : Fin A.dim) : Matrix (Fin C.output) (Fin C.output) ℂ :=
  A.embed (Matrix.single a b 1)

lemma E_conj (A : Access C) {a b : Fin A.dim} (h : A.block a = A.block b) :
    (E A a b)ᴴ = E A b a := by
  unfold E
  rw [← A.preserves_star _ (single_inBlocks _ h), Matrix.conjTranspose_single, star_one]

lemma E_mul (A : Access C) {a b c : Fin A.dim} (h : A.block a = A.block b)
    (h' : A.block b = A.block c) : E A a b * E A b c = E A a c := by
  unfold E
  rw [← A.preserves_mul _ _ (single_inBlocks _ h) (single_inBlocks _ h'),
    Matrix.single_mul_single_same, one_mul]

def K (A : Access C) {k : ℕ} (x x' : Fin k → Fin A.dim) :
    Matrix (Fin k → Fin C.output) (Fin k → Fin C.output) ℂ :=
  T (fun i => E A (x i) (x' i))

def L (A : Access C) {k : ℕ} (x : Fin k → Fin A.dim) :
    Matrix (Fin k → Fin C.output) (Fin k → Fin C.output) ℂ :=
  K A x (fun i => rep A (x i))

lemma K_eq (A : Access C) {k : ℕ} {x x' : Fin k → Fin A.dim}
    (h : ∀ i, A.block (x i) = A.block (x' i)) : K A x x' = L A x * (L A x')ᴴ := by
  unfold L K
  rw [T_conj, T_mul]
  congr 1; funext i
  dsimp only
  rw [E_conj A (rep_spec A _).symm, rep_eq A (h i)]
  exact (E_mul A ((rep_spec A _).trans (h i).symm).symm (rep_spec A _)).symm

lemma pi_expand (A : Access C) {k : ℕ} (X : Matrix (Fin k → Fin A.dim) (Fin k → Fin A.dim) ℂ) :
    piSuperop (fun _ : Fin k => fun T => A.embed T) X = ∑ x, ∑ x', X x x' • K A x x' := by
  ext y y'
  simp [piSuperop, K, T, E, Matrix.sum_apply]

lemma pi_psd (A : Access C) {k : ℕ} (D : Matrix (Fin k → Fin A.dim) (Fin k → Fin A.dim) ℂ)
    (hD : D.PosSemidef) (hB : InBlockPower A.block k D) :
    (piSuperop (fun _ : Fin k => fun T => A.embed T) D).PosSemidef := by
  obtain ⟨B, hBD⟩ := psd_decomp hD
  rw [pi_expand]
  have h1 : ∑ x, ∑ x', D x x' • K A x x' = ∑ x, ∑ x', D x x' • (L A x * (L A x')ᴴ) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    by_cases h : ∀ i, A.block (x i) = A.block (x' i)
    · rw [K_eq A h]
    · push Not at h
      rw [hB x x' h, zero_smul, zero_smul]
  have h2 : ∑ x, ∑ x', D x x' • (L A x * (L A x')ᴴ) =
      ∑ q, (∑ x, star (B q x) • L A x) * (∑ x, star (B q x) • L A x)ᴴ := by
    simp_rw [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_star, Finset.sum_mul,
      Finset.mul_sum, smul_mul_smul, hBD, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.sum_smul]
    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, x]; rw [Finset.sum_comm]
  rw [h1, h2]
  exact sum_psd _ _ fun q => Matrix.posSemidef_self_mul_conjTranspose _

end Acc

section Kron
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m n : ℕ}

def kr (P : Matrix (Fin m → ι) (Fin m → ι) ℂ) (Q : Matrix (Fin n → ι) (Fin n → ι) ℂ) :
    Matrix (Fin (m + n) → ι) (Fin (m + n) → ι) ℂ :=
  Matrix.of fun a b => P (fun k => a (Fin.castAdd n k)) (fun k => b (Fin.castAdd n k)) *
    Q (fun k => a (Fin.natAdd m k)) (fun k => b (Fin.natAdd m k))

lemma kr_psd {P : Matrix (Fin m → ι) (Fin m → ι) ℂ} {Q : Matrix (Fin n → ι) (Fin n → ι) ℂ}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : (kr P Q).PosSemidef := by
  obtain ⟨SP, rfl⟩ := psd_decomp hP
  obtain ⟨SQ, rfl⟩ := psd_decomp hQ
  let W : Matrix ((Fin m → ι) × (Fin n → ι)) (Fin (m + n) → ι) ℂ :=
    Matrix.of fun p a => SP p.1 (fun k => a (Fin.castAdd n k)) * SQ p.2 (fun k => a (Fin.natAdd m k))
  have : kr (SPᴴ * SP) (SQᴴ * SQ) = Wᴴ * W := by
    ext a b
    simp only [kr, W, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Finset.sum_mul_sum, star_mul']
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma split_eq {a b : Fin (m + n) → ι} :
    ((fun k => a (Fin.castAdd n k)) = (fun k => b (Fin.castAdd n k)) ∧
      (fun k => a (Fin.natAdd m k)) = (fun k => b (Fin.natAdd m k))) ↔ a = b := by
  constructor
  · rintro ⟨h1, h2⟩
    funext k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · exact congrFun h1 i
    · exact congrFun h2 i
  · rintro rfl; exact ⟨rfl, rfl⟩

lemma sum_split (X : Matrix (Fin m → ι) (Fin m → ι) ℂ) (Y : Matrix (Fin n → ι) (Fin n → ι) ℂ)
    (t : Fin (m + n) → ι → ι → ℂ) :
    ∑ x : Fin (m + n) → ι, ∑ x' : Fin (m + n) → ι, kr X Y x x' * ∏ i, t i (x i) (x' i) =
      (∑ u : Fin m → ι, ∑ u' : Fin m → ι, X u u' * ∏ i, t (Fin.castAdd n i) (u i) (u' i)) *
      (∑ v : Fin n → ι, ∑ v' : Fin n → ι, Y v v' * ∏ i, t (Fin.natAdd m i) (v i) (v' i)) := by
  rw [← (Fin.appendEquiv m n).sum_comp]
  refine (Finset.sum_congr rfl fun x _ => ((Fin.appendEquiv m n).sum_comp _).symm).trans ?_
  simp only [Fintype.sum_prod_type, Fin.appendEquiv_apply, kr, Matrix.of_apply, Fin.append_left,
    Fin.append_right, Fin.prod_univ_add, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

end Kron

section Tup
variable {s : ℕ} (a b : Fin s → ℕ)

def tupEquiv : (∀ i, Fin (a i * b i)) ≃ (∀ i, Fin (a i)) × (∀ i, Fin (b i)) where
  toFun mu := (fun i => (finProdFinEquiv.symm (mu i)).1, fun i => (finProdFinEquiv.symm (mu i)).2)
  invFun p := fun i => finProdFinEquiv (p.1 i, p.2 i)
  left_inv mu := by funext i; simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv p := by ext i <;> simp

lemma sum_tup {R : Type*} [AddCommMonoid R] (f : (∀ i, Fin (a i)) → (∀ i, Fin (b i)) → R) :
    ∑ mu : (∀ i, Fin (a i * b i)),
      f (fun i => (finProdFinEquiv.symm (mu i)).1) (fun i => (finProdFinEquiv.symm (mu i)).2) =
      ∑ u, ∑ v, f u v := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (tupEquiv a b) _ _ (fun _ => rfl)

end Tup

section Code
variable {s r : ℕ} {C : ClassicalChannel s} {N : Network C r} {m n : ℕ}

lemma blockOutput_eq (k : ℕ) (w : ∀ i, Fin k → Fin (C.alphabet i)) :
    blockOutput C k w = T (fun t => C.state (fun i => w i t)) := rfl

def tr (c : MultiwayBlockCode N m) (j : Fin r) (mu : ∀ i, Fin (c.messages i)) : ℂ :=
  (piSuperop (fun _ : Fin m => fun T => (N.access j).embed T) (c.decode j mu) *
    blockOutput C m (fun i => c.encode i (mu i))).trace

lemma tr_nonneg (c : MultiwayBlockCode N m) (j : Fin r) (mu : ∀ i, Fin (c.messages i)) :
    0 ≤ tr c j mu :=
  tr_psd_mul (pi_psd _ _ ((c.povm j).1 mu) (c.in_algebra j mu))
    (by rw [blockOutput_eq]; exact T_psd _ fun _ => (C.normalized _).1)

lemma err_eq (c : MultiwayBlockCode N m) (j : Fin r) : averageTupleError c j =
    1 - (Fintype.card (∀ i, Fin (c.messages i)) : ℝ)⁻¹ * ∑ mu, (tr c j mu).re := rfl

def cat (c : MultiwayBlockCode N m) (d : MultiwayBlockCode N n) : MultiwayBlockCode N (m + n) where
  length_pos := Nat.add_pos_left c.length_pos _
  messages i := c.messages i * d.messages i
  messages_pos i := Nat.mul_pos (c.messages_pos i) (d.messages_pos i)
  encode i mu := Fin.addCases (c.encode i (finProdFinEquiv.symm mu).1)
    (d.encode i (finProdFinEquiv.symm mu).2)
  decode j mu := kr (c.decode j (fun i => (finProdFinEquiv.symm (mu i)).1))
    (d.decode j (fun i => (finProdFinEquiv.symm (mu i)).2))
  povm j := ⟨fun _ => kr_psd ((c.povm j).1 _) ((d.povm j).1 _), by
    ext a b
    rw [Matrix.sum_apply]
    simp only [kr, Matrix.of_apply]
    rw [sum_tup c.messages d.messages (fun u v =>
      c.decode j u (fun k => a (Fin.castAdd n k)) (fun k => b (Fin.castAdd n k)) *
      d.decode j v (fun k => a (Fin.natAdd m k)) (fun k => b (Fin.natAdd m k)))]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, ← Matrix.sum_apply, (c.povm j).2, (d.povm j).2,
      Matrix.one_apply]
    by_cases h1 : (fun k => a (Fin.castAdd n k)) = (fun k => b (Fin.castAdd n k)) <;>
    by_cases h2 : (fun k => a (Fin.natAdd m k)) = (fun k => b (Fin.natAdd m k))
    · simp [h1, h2, split_eq.mp ⟨h1, h2⟩]
    · have hab : a ≠ b := fun h => h2 (split_eq.mpr h).2
      simp [h1, h2, hab]
    · have hab : a ≠ b := fun h => h1 (split_eq.mpr h).1
      simp [h1, h2, hab]
    · have hab : a ≠ b := fun h => h1 (split_eq.mpr h).1
      simp [h1, h2, hab]⟩
  in_algebra j mu := by
    rintro a b ⟨k, hk⟩
    simp only [kr, Matrix.of_apply]
    induction k using Fin.addCases with
    | left i => rw [c.in_algebra j _ _ _ ⟨i, hk⟩, zero_mul]
    | right i => rw [d.in_algebra j _ _ _ ⟨i, hk⟩, mul_zero]

lemma tr_cat (c : MultiwayBlockCode N m) (d : MultiwayBlockCode N n) (j : Fin r)
    (mu : ∀ i, Fin ((cat c d).messages i)) :
    tr (cat c d) j mu = tr c j (fun i => (finProdFinEquiv.symm (mu i)).1) *
      tr d j (fun i => (finProdFinEquiv.symm (mu i)).2) := by
  unfold tr
  rw [blockOutput_eq, blockOutput_eq, blockOutput_eq, tr_pi, tr_pi, tr_pi]
  show ∑ x, ∑ x', kr _ _ x x' * _ = _
  rw [sum_split (t := fun k a b => ((N.access j).embed (Matrix.single a b 1) *
    C.state fun i_1 => (cat c d).encode i_1 (mu i_1) k).trace)]
  simp only [cat, Fin.addCases_left, Fin.addCases_right]

lemma tr_real (c : MultiwayBlockCode N m) (j : Fin r) (mu : ∀ i, Fin (c.messages i)) :
    tr c j mu = ((tr c j mu).re : ℂ) := by
  have h := Complex.nonneg_iff.mp (tr_nonneg c j mu)
  exact Complex.ext (by simp) (by simp [← h.2])

lemma err_cat (c : MultiwayBlockCode N m) (d : MultiwayBlockCode N n) (eps : ℝ)
    (hc : ∀ j, averageTupleError c j ≤ eps) (hd : ∀ j, averageTupleError d j ≤ eps) (j : Fin r) :
    averageTupleError (cat c d) j ≤ 2 * eps := by
  have hc := hc j
  have hd := hd j
  rw [err_eq] at hc hd ⊢
  have hsum : ∑ mu, (tr (cat c d) j mu).re =
      (∑ u, (tr c j u).re) * ∑ v, (tr d j v).re := by
    simp_rw [tr_cat]
    refine (sum_tup c.messages d.messages (fun u v => (tr c j u * tr d j v).re)).trans ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [tr_real c j u, tr_real d j v, ← Complex.ofReal_mul, Complex.ofReal_re]; simp
  have hcard : (Fintype.card (∀ i, Fin ((cat c d).messages i)) : ℝ) =
      (Fintype.card (∀ i, Fin (c.messages i)) : ℝ) * Fintype.card (∀ i, Fin (d.messages i)) := by
    rw [← Nat.cast_mul, ← Fintype.card_prod]
    exact_mod_cast Fintype.card_congr (tupEquiv c.messages d.messages)
  rw [hsum, hcard]
  set Kc := (Fintype.card (∀ i, Fin (c.messages i)) : ℝ)
  set Kd := (Fintype.card (∀ i, Fin (d.messages i)) : ℝ)
  have hSc : 0 ≤ ∑ u, (tr c j u).re := Finset.sum_nonneg fun u _ =>
    (Complex.nonneg_iff.mp (tr_nonneg c j u)).1
  have hSd : 0 ≤ ∑ v, (tr d j v).re := Finset.sum_nonneg fun v _ =>
    (Complex.nonneg_iff.mp (tr_nonneg d j v)).1
  have hx : 0 ≤ Kc⁻¹ * ∑ u, (tr c j u).re := mul_nonneg (by positivity) hSc
  have hy : 0 ≤ Kd⁻¹ * ∑ v, (tr d j v).re := mul_nonneg (by positivity) hSd
  have heq : (Kc * Kd)⁻¹ * ((∑ u, (tr c j u).re) * ∑ v, (tr d j v).re) =
      (Kc⁻¹ * ∑ u, (tr c j u).re) * (Kd⁻¹ * ∑ v, (tr d j v).re) := by
    rw [mul_inv]; ring
  rw [heq]
  set x := Kc⁻¹ * ∑ u, (tr c j u).re
  set y := Kd⁻¹ * ∑ v, (tr d j v).re
  rcases le_or_gt 1 eps with he | he
  · nlinarith [mul_nonneg hx hy]
  · nlinarith [mul_le_mul (show 1 - eps ≤ x by linarith) (show 1 - eps ≤ y by linarith)
      (by linarith) hx, sq_nonneg eps]

lemma rate_cat (c : MultiwayBlockCode N m) (d : MultiwayBlockCode N n) (i : Fin s) :
    codeRate (cat c d) i =
      (m : ℝ) / (m + n) * codeRate c i + (n : ℝ) / (m + n) * codeRate d i := by
  have hm : (0 : ℝ) < m := by exact_mod_cast c.length_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast d.length_pos
  have hc : (c.messages i : ℝ) ≠ 0 := by exact_mod_cast (c.messages_pos i).ne'
  have hd : (d.messages i : ℝ) ≠ 0 := by exact_mod_cast (d.messages_pos i).ne'
  simp only [codeRate, cat]
  push_cast
  rw [Real.logb_mul hc hd]
  field_simp

lemma concat (c : MultiwayBlockCode N m) (d : MultiwayBlockCode N n) (eps : ℝ)
    (hc : ∀ j, averageTupleError c j ≤ eps) (hd : ∀ j, averageTupleError d j ≤ eps) :
    ∃ e : MultiwayBlockCode N (m + n), IsConcatenation c d e ∧
      (∀ j, averageTupleError e j ≤ 2 * eps) ∧
      ∀ i, codeRate e i =
        (m : ℝ) / (m + n) * codeRate c i + (n : ℝ) / (m + n) * codeRate d i :=
  ⟨cat c d, ⟨fun _ => finProdFinEquiv.symm, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩,
    err_cat c d eps hc hd, rate_cat c d⟩

end Code

lemma convex_cap {s r : ℕ} {C : ClassicalChannel s} (N : Network C r) :
    Convex ℝ (capacityRegion N) := by
  intro x hx y hy a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    subst this; simpa using hy
  rcases hb.eq_or_lt with rfl | hb'
  · have : a = 1 := by linarith
    subst this; simpa using hx
  obtain ⟨hx0, hxc⟩ := hx
  obtain ⟨hy0, hyc⟩ := hy
  refine ⟨fun i => ?_, fun eps delta he hd => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx0 i; have := hy0 i; positivity
  obtain ⟨n1, hn1, hc⟩ := hxc (eps / 2) (delta / 2) (by positivity) (by positivity)
  obtain ⟨n2, hn2, hd'⟩ := hyc (eps / 2) (delta / 2) (by positivity) (by positivity)
  set M := ∑ i, x i with hMdef
  have hM : ∀ i, x i ≤ M := fun i =>
    Finset.single_le_sum (f := x) (fun j _ => hx0 j) (Finset.mem_univ i)
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => hx0 j
  refine ⟨⌈((n1 : ℝ) + 1) / a + (n2 : ℝ) / b + 2 * M / delta⌉₊ + 1, by omega, fun n hn => ?_⟩
  have t1 : 0 ≤ ((n1 : ℝ) + 1) / a := by positivity
  have t2 : 0 ≤ (n2 : ℝ) / b := by positivity
  have t3 : 0 ≤ 2 * M / delta := by positivity
  have hnR : ((n1 : ℝ) + 1) / a + (n2 : ℝ) / b + 2 * M / delta < n := by
    have h1 := Nat.le_ceil (((n1 : ℝ) + 1) / a + (n2 : ℝ) / b + 2 * M / delta)
    have h2 : ((⌈((n1 : ℝ) + 1) / a + (n2 : ℝ) / b + 2 * M / delta⌉₊ : ℕ) : ℝ) + 1 ≤ n := by
      exact_mod_cast hn
    linarith
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, (k : ℝ) ≤ a * n ∧ a * n < k + 1 :=
    ⟨⌊a * n⌋₊, Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  have hb1 : b = 1 - a := by linarith
  have hkn1 : n1 ≤ k := by
    have : ((n1 : ℝ) + 1) < a * n := by
      have h := (div_lt_iff₀ ha').mp (show ((n1 : ℝ) + 1) / a < n by linarith)
      linarith
    have : (n1 : ℝ) < k := by linarith
    exact_mod_cast this.le
  have hln2 : n2 + k < n := by
    have h := (div_lt_iff₀ hb').mp (show (n2 : ℝ) / b < n by linarith)
    have : ((n2 + k : ℕ) : ℝ) < n := by push_cast; nlinarith
    exact_mod_cast this
  obtain ⟨l, hl⟩ : ∃ l, l = n - k := ⟨_, rfl⟩
  have hn2l : n2 ≤ l := by omega
  have hnkl : n = k + l := by omega
  subst hnkl
  obtain ⟨c, hcE, hcR⟩ := hc k hkn1
  obtain ⟨d, hdE, hdR⟩ := hd' l hn2l
  obtain ⟨e, -, heE, heR⟩ := concat c d (eps / 2) hcE hdE
  refine ⟨e, fun j => by have := heE j; linarith, fun i => ?_⟩
  rw [heR i]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast at hnR hnpos hk1 hk2
  set Nn : ℝ := (k : ℝ) + l with hNn
  set p := (k : ℝ) / Nn with hp
  set q := (l : ℝ) / Nn with hq
  have hpq : p + q = 1 := by rw [hp, hq, ← add_div, div_self hnpos.ne']
  have hp0 : 0 ≤ p := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hap : a - p ≤ 1 / Nn := by
    rw [hp, sub_le_iff_le_add, ← add_div, le_div_iff₀ hnpos]; linarith
  have hpa : p ≤ a := by rw [hp, div_le_iff₀ hnpos]; linarith
  have hxM : x i / Nn ≤ delta / 2 := by
    have h := (div_lt_iff₀ hd).mp (show 2 * M / delta < Nn by linarith)
    rw [div_le_iff₀ hnpos]; nlinarith [hM i]
  have hm1 : (a - p) * x i ≤ delta / 2 := by
    have := mul_le_mul_of_nonneg_right hap (hx0 i)
    rw [one_div, inv_mul_eq_div] at this; linarith
  have hm2 : 0 ≤ (a - p) * y i := mul_nonneg (by linarith) (hy0 i)
  have hc1 := mul_le_mul_of_nonneg_left (hcR i) hp0
  have hd1 := mul_le_mul_of_nonneg_left (hdR i) hq0
  have e1 : p * (x i - delta / 2) + q * (y i - delta / 2) = p * x i + q * y i - delta / 2 := by
    linear_combination (-delta / 2) * hpq
  have e2 : a * x i + b * y i - (p * x i + q * y i) = (a - p) * x i - (a - p) * y i := by
    linear_combination (y i) * hab - (y i) * hpq
  linarith

end T40T

theorem solution {s r : ℕ} {C : ClassicalChannel s} (N : Network C r) :
    Convex ℝ (capacityRegion N) ∧
    ∀ {m n : ℕ} (c : MultiwayBlockCode N m) (d : MultiwayBlockCode N n) (epsilon : ℝ),
      (∀ j, averageTupleError c j ≤ epsilon) → (∀ j, averageTupleError d j ≤ epsilon) →
      ∃ e : MultiwayBlockCode N (m + n), IsConcatenation c d e ∧
        (∀ j, averageTupleError e j ≤ 2 * epsilon) ∧
        ∀ i, codeRate e i =
          (m : ℝ) / (m + n) * codeRate c i + (n : ℝ) / (m + n) * codeRate d i :=
  ⟨T40T.convex_cap N, fun c d epsilon hc hd => T40T.concat c d epsilon hc hd⟩
