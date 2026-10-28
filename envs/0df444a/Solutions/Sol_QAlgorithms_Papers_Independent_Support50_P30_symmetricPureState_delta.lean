-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P30.symmetricPureState_delta
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T14:24:32.584931+00:00
-- url     : https://prove2.me/submissions/52397c79-7d0a-4cf5-9d2f-46d630c17ec8

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

open scoped Matrix ComplexConjugate
open Finset

namespace X8SY

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P30

variable {n : ℕ}

lemma ps1_apply (χ : Matrix Bool Bool ℂ) (j : Fin n) (x y : Qubits n) :
    pauliString n χ {j} x y = if y = Function.update x j (y j) then χ (x j) (y j) else 0 := by
  unfold pauliString
  rw [Fintype.prod_eq_mul_prod_compl j]
  simp only [mem_singleton, if_true]
  split_ifs with h
  · rw [prod_eq_one, mul_one]
    intro k hk
    have hk' : k ≠ j := by simpa using hk
    rw [if_neg hk']
    have : y k = x k := by rw [h]; simp [hk']
    simp [this]
  · obtain ⟨k, hk⟩ : ∃ k, k ≠ j ∧ x k ≠ y k := by
      by_contra hc; push Not at hc
      apply h; funext i
      by_cases hi : i = j
      · subst hi; simp
      · rw [Function.update_of_ne hi]; exact (hc i hi).symm
    rw [prod_eq_zero (i := k) (by simpa using hk.1)]
    · ring
    · rw [if_neg hk.1, if_neg hk.2]

lemma sum_update (x : Qubits n) (j : Fin n) (h : Qubits n → ℂ) :
    ∑ y, (if y = Function.update x j (y j) then h y else 0) = ∑ b, h (Function.update x j b) := by
  have e1 : ∀ b, h (Function.update x j b) = ∑ y, if y = Function.update x j b then h y else 0 := by
    intro b; rw [sum_ite_eq']; simp
  simp_rw [e1]
  rw [sum_comm]
  apply sum_congr rfl; intro y _
  by_cases hy : y = Function.update x j (y j)
  · rw [if_pos hy]
    have : ∀ b, (y = Function.update x j b ↔ b = y j) := by
      intro b; constructor
      · intro h'; rw [h']; simp
      · intro h'; rw [h']; exact hy
    simp_rw [this]; simp
  · rw [if_neg hy]
    apply (sum_eq_zero _).symm
    intro b _
    rw [if_neg]
    intro h'; apply hy; conv_lhs => rw [h']
    rw [h']; simp

lemma site_mulVec (χ : Matrix Bool Bool ℂ) (j : Fin n) (v : Qubits n → ℂ) (x : Qubits n) :
    (pauliString n χ {j} *ᵥ v) x = ∑ b, χ (x j) b * v (Function.update x j b) := by
  simp only [Matrix.mulVec, dotProduct, ps1_apply]
  have := sum_update x j (fun y => χ (x j) (y j) * v y)
  simp only [ite_mul, zero_mul] at this ⊢
  rw [this]
  simp

lemma coll1_mulVec (χ : Matrix Bool Bool ℂ) (v : Qubits n → ℂ) (x : Qubits n) :
    (collective n χ 1 *ᵥ v) x = ∑ j, ∑ b, χ (x j) b * v (Function.update x j b) := by
  unfold collective
  rw [powersetCard_one, sum_map, Matrix.sum_mulVec, Finset.sum_apply]
  apply sum_congr rfl; intro j _
  exact site_mulVec χ j v x

lemma pid (a b e c : Bool) :
    pauliX a b * pauliX e c + pauliY a b * pauliY e c + pauliZ a b * pauliZ e c =
      2 * (if a = c then 1 else 0) * (if e = b then 1 else 0) -
        (if a = b then 1 else 0) * (if e = c then 1 else 0) := by
  cases a <;> cases b <;> cases e <;> cases c <;>
    simp [pauliX, pauliY, pauliZ, Matrix.diagonal] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma cas_mulVec (v : Qubits n → ℂ) (x : Qubits n) :
    (spinCasimir n *ᵥ v) x = ∑ j, ∑ k, ∑ b, ∑ c,
      (pauliX (x j) b * pauliX (Function.update x j b k) c +
        pauliY (x j) b * pauliY (Function.update x j b k) c +
        pauliZ (x j) b * pauliZ (Function.update x j b k) c) *
        v (Function.update (Function.update x j b) k c) := by
  unfold spinCasimir
  simp only [sq, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Pi.add_apply, coll1_mulVec]
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro j _
  rw [sum_comm]
  apply sum_congr rfl; intro k _
  apply sum_congr rfl; intro b _
  apply sum_congr rfl; intro c _
  ring

lemma swap_eq (x : Qubits n) {j k : Fin n} (h : j ≠ k) :
    (fun i => x (Equiv.swap j k i)) = Function.update (Function.update x j (x k)) k (x j) := by
  funext i
  by_cases hi : i = k
  · subst hi; simp [Equiv.swap_apply_right]
  · rw [Function.update_of_ne hi]
    by_cases hj : i = j
    · subst hj; simp [Equiv.swap_apply_left]
    · rw [Function.update_of_ne hj, Equiv.swap_apply_of_ne_of_ne hj hi]

theorem cas_eig (v : Qubits n → ℂ) (hv : ∀ (j k : Fin n) (x : Qubits n), v (fun i => x (Equiv.swap j k i)) = v x) :
    spinCasimir n *ᵥ v = ((n : ℂ) * ((n : ℂ) + 2)) • v := by
  funext x
  rw [cas_mulVec]
  have inner : ∀ j k, ∑ b, ∑ c,
      (pauliX (x j) b * pauliX (Function.update x j b k) c +
        pauliY (x j) b * pauliY (Function.update x j b k) c +
        pauliZ (x j) b * pauliZ (Function.update x j b k) c) *
        v (Function.update (Function.update x j b) k c) = if k = j then 3 * v x else v x := by
    intro j k
    split_ifs with hkj
    · subst hkj
      simp only [Function.update_self, Function.update_idem]
      rw [sum_comm]
      simp only [← sum_mul]
      have : ∀ c, ∑ b, (pauliX (x k) b * pauliX b c + pauliY (x k) b * pauliY b c +
          pauliZ (x k) b * pauliZ b c) = 3 * (if x k = c then 1 else 0) := by
        intro c; simp only [pid]; cases x k <;> cases c <;> simp <;> norm_num
      simp only [this]
      simp [ite_mul]
    · simp only [Function.update_of_ne hkj, pid]
      simp only [sub_mul, sum_sub_distrib, mul_assoc]
      simp [ite_mul]
      rw [← swap_eq x (Ne.symm hkj), hv]
      ring
  simp only [inner]
  simp only [Pi.smul_apply, smul_eq_mul]
  have : ∀ j : Fin n, ∑ k, (if k = j then 3 * v x else v x) = ((n : ℂ) + 2) * v x := by
    intro j
    rw [← Finset.add_sum_erase _ _ (mem_univ j), if_pos rfl]
    rw [sum_congr rfl (fun k hk => if_neg (ne_of_mem_erase hk))]
    rw [sum_const, card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact j.elim0
    · push_cast [Nat.cast_sub hn]; ring
  simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end X8SY


open scoped Matrix ComplexConjugate
open Finset

namespace X8SY

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P30

variable {n : ℕ}

lemma bd_scalar (c : Sector n → ℂ) (x y : QnnSchurIndex n) :
    qnnSchurBlockDiagonal (fun m => c m • (1 : Matrix (Fin (blockDim n m)) (Fin (blockDim n m)) ℂ)) x y =
      if x = y then c x.1 else 0 := by
  obtain ⟨m, nu, j⟩ := x
  obtain ⟨m', nu', j'⟩ := y
  unfold qnnSchurBlockDiagonal
  by_cases h : m = m'
  · subst h
    simp only [dif_pos rfl]
    by_cases hnu : nu = nu'
    · subst hnu
      simp [Matrix.one_apply]
    · have : nu.val ≠ nu'.val := fun e => hnu (Fin.ext e)
      simp [this, hnu]
  · simp [h]

lemma perm_sym (psi : EuclideanSpace ℂ (Qubits n))
    (hsym : ∀ p : Equiv.Perm (Fin n), act (qubitPermutationMatrix n p) psi = psi) :
    ∀ (j k : Fin n) (x : Qubits n), (WithLp.ofLp psi) (fun i => x (Equiv.swap j k i)) = (WithLp.ofLp psi) x := by
  intro j k x
  have h := congrArg (fun w : EuclideanSpace ℂ (Qubits n) => w x) (hsym (Equiv.swap j k))
  simp only [act] at h
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, qubitPermutationMatrix, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (fun i => x (Equiv.swap j k i))]
  · rw [if_pos]; funext i; simp [Equiv.symm_swap]
  · intro y _ hy
    rw [if_neg]; intro hx; apply hy; funext i; rw [hx]; simp [Equiv.symm_swap]
  · simp

lemma cval_ne {m : Sector n} (hm : m.val ≠ 0) :
    (((n - 2 * m.val : ℕ) : ℂ) * (((n - 2 * m.val : ℕ) : ℂ) + 2)) ≠ (n : ℂ) * ((n : ℂ) + 2) := by
  have hm2 : 2 * m.val ≤ n := by have := m.2; omega
  have hlt : n - 2 * m.val < n := by omega
  intro h
  have h' : ((n - 2 * m.val) * (n - 2 * m.val + 2) : ℕ) = n * (n + 2) := by exact_mod_cast h
  have : (n - 2 * m.val) * (n - 2 * m.val + 2) < n * (n + 2) :=
    Nat.mul_lt_mul'' hlt (by omega)
  omega

/-- components of `W f` outside the symmetric sector vanish. -/
lemma vanish (S : SchurFrame n) (f : Qubits n → ℂ)
    (hf : spinCasimir n *ᵥ f = ((n : ℂ) * ((n : ℂ) + 2)) • f) (x : QnnSchurIndex n) (hx : x.1.val ≠ 0) :
    (S.matrix *ᵥ f) x = 0 := by
  have key : (S.matrix * spinCasimir n * S.matrix.conjTranspose) *ᵥ (S.matrix *ᵥ f) =
      ((n : ℂ) * ((n : ℂ) + 2)) • (S.matrix *ᵥ f) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, S.columns, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hf, Matrix.mulVec_smul]
  rw [S.spin] at key
  have := congrFun key x
  simp only [Matrix.mulVec, dotProduct, bd_scalar, ite_mul, zero_mul, sum_ite_eq, mem_univ, if_true,
    Pi.smul_apply, smul_eq_mul] at this
  have hne := cval_ne hx
  have : ((((n - 2 * x.1.val : ℕ) : ℂ) * (((n - 2 * x.1.val : ℕ) : ℂ) + 2)) - (n : ℂ) * ((n : ℂ) + 2)) *
      (S.matrix *ᵥ f) x = 0 := by
    simp only [Matrix.mulVec, dotProduct]; rw [sub_mul, this]; ring
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact h

end X8SY


open scoped Matrix ComplexConjugate
open Finset

namespace X8SY

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P30

variable {n : ℕ}

lemma gen_entry {ι κ : Type*} [Fintype κ] (R : Matrix ι κ ℂ) (f : κ → ℂ) (i j : ι) :
    (R * Matrix.of (fun a b => f a * conj (f b)) * Rᴴ) i j = (R *ᵥ f) i * conj ((R *ᵥ f) j) := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct,
    map_sum, map_mul, RCLike.star_def]
  simp only [sum_mul, mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma comp_entry (S : SchurFrame n) (m : Sector n) (nu : Fin (qnnSectorMultiplicity n m))
    (psi : EuclideanSpace ℂ (Qubits n)) (i j : Fin (blockDim n m)) :
    schurCompression S m nu (pureDensity psi) i j =
      (S.matrix *ᵥ WithLp.ofLp psi) ⟨m, (nu, i)⟩ * conj ((S.matrix *ᵥ WithLp.ofLp psi) ⟨m, (nu, j)⟩) := by
  unfold schurCompression pureDensity
  rw [gen_entry]
  rfl

lemma mult0 : qnnSectorMultiplicity n (symmetricSector n) = 1 := by
  simp [qnnSectorMultiplicity, symmetricSector]

lemma sum_mult0 {α : Type*} [AddCommMonoid α] (g : Fin (qnnSectorMultiplicity n (symmetricSector n)) → α) :
    ∑ nu, g nu = g ⟨0, by rw [mult0]; norm_num⟩ := by
  apply Finset.sum_eq_single_of_mem _ (mem_univ _)
  intro b _ hb; exfalso; apply hb
  have h2 : b.val < qnnSectorMultiplicity n (symmetricSector n) := b.2
  have h1 := mult0 (n := n)
  exact Fin.ext (by simp; omega)

lemma bdim0 : blockDim n (symmetricSector n) = n + 1 := by
  simp [blockDim, symmetricSector]

theorem x8_main {n : ℕ} (hn : 1 ≤ n) (S : SchurFrame n)
    (psi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi)
    (hsym : ∀ p : Equiv.Perm (Fin n), act (qubitPermutationMatrix n p) psi = psi) :
    centeredDelta (aggregate S (symmetricSector n) (pureDensity psi)) = 1 - 1 / ((n : ℝ) + 1) ∧
    (1 / 2 : ℝ) ≤ centeredDelta (aggregate S (symmetricSector n) (pureDensity psi)) ∧
    centeredDelta (aggregate S (symmetricSector n) (pureDensity psi)) ≤ 1 := by
  set f := WithLp.ofLp psi with hfdef
  set v := S.matrix *ᵥ f with hv
  set m0 := symmetricSector n
  set nu0 : Fin (qnnSectorMultiplicity n m0) := ⟨0, by rw [mult0]; norm_num⟩
  have hf := cas_eig f (perm_sym psi hsym)
  have hvan : ∀ x : QnnSchurIndex n, x.1 ≠ m0 → v x = 0 := by
    intro x hx
    apply vanish S f hf x
    intro h0; apply hx; exact Fin.ext (by simp [m0, symmetricSector, h0])
  -- total norm
  have hN : ∑ i : Fin (blockDim n m0), conj (v ⟨m0, (nu0, i)⟩) * v ⟨m0, (nu0, i)⟩ = 1 := by
    have h1 : ∑ x : QnnSchurIndex n, conj (v x) * v x = 1 := by
      have e : ∑ x : QnnSchurIndex n, conj (v x) * v x = star v ⬝ᵥ v := by
        simp [dotProduct]
      rw [e, hv, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, S.columns,
        Matrix.one_mulVec]
      have hp : ‖psi‖ ^ 2 = 1 := by rw [hpsi]; norm_num
      rw [EuclideanSpace.norm_sq_eq] at hp
      have : star f ⬝ᵥ f = ((∑ x, ‖psi x‖ ^ 2 : ℝ) : ℂ) := by
        simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.ofReal_sum]
        apply sum_congr rfl; intro x _
        rw [Complex.conj_mul', hfdef]; push_cast; rfl
      rw [this, hp]; simp
    rw [← h1, Fintype.sum_sigma, Finset.sum_eq_single m0]
    · rw [Fintype.sum_prod_type, sum_mult0]
    · intro m _ hm
      apply sum_eq_zero; intro p _
      rw [hvan ⟨m, p⟩ hm]; simp
    · simp
  have hagg : ∀ i j, aggregate S m0 (pureDensity psi) i j =
      v ⟨m0, (nu0, i)⟩ * conj (v ⟨m0, (nu0, j)⟩) := by
    intro i j
    unfold aggregate
    rw [Matrix.sum_apply, sum_mult0, comp_entry]
  set M := aggregate S m0 (pureDensity psi)
  have htr : M.trace = 1 := by
    rw [Matrix.trace]; simp only [Matrix.diag, hagg]
    rw [← hN]; apply sum_congr rfl; intro i _; ring
  have htr2 : (M * M).trace = 1 := by
    rw [Matrix.trace]; simp only [Matrix.diag, Matrix.mul_apply, hagg]
    have : ∀ i, ∑ j, v ⟨m0, (nu0, i)⟩ * conj (v ⟨m0, (nu0, j)⟩) * (v ⟨m0, (nu0, j)⟩ * conj (v ⟨m0, (nu0, i)⟩)) =
        conj (v ⟨m0, (nu0, i)⟩) * v ⟨m0, (nu0, i)⟩ *
          ∑ j : Fin (blockDim n m0), conj (v ⟨m0, (nu0, j)⟩) * v ⟨m0, (nu0, j)⟩ := by
      intro i; rw [mul_sum]; apply sum_congr rfl; intro j _; ring
    simp only [this, hN, mul_one]
  have hval : centeredDelta M = 1 - 1 / ((n : ℝ) + 1) := by
    unfold centeredDelta deltaPair
    rw [htr2, htr]
    have hd : ((blockDim n m0 : ℕ) : ℂ) = ((n : ℝ) + 1 : ℝ) := by
      rw [bdim0]; push_cast; ring
    rw [hd]
    have : (1 : ℂ) - 1 * 1 / (((n : ℝ) + 1 : ℝ) : ℂ) = ((1 - 1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
  refine ⟨hval, ?_, ?_⟩
  · rw [hval]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)] at *
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    linarith
  · rw [hval]
    have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith

end X8SY

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P30 in
theorem solution {n : ℕ} (hn : 1 ≤ n) (S : SchurFrame n)
    (psi : EuclideanSpace ℂ (Qubits n)) (hpsi : IsState psi)
    (hsym : ∀ p : Equiv.Perm (Fin n), act (qubitPermutationMatrix n p) psi = psi) :
    centeredDelta (aggregate S (symmetricSector n) (pureDensity psi)) = 1 - 1 / ((n : ℝ) + 1) ∧
    (1 / 2 : ℝ) ≤ centeredDelta (aggregate S (symmetricSector n) (pureDensity psi)) ∧
    centeredDelta (aggregate S (symmetricSector n) (pureDensity psi)) ≤ 1 :=
  X8SY.x8_main hn S psi hpsi hsym
