-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P34.weyl_twirl_projectors
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:05:50.374012+00:00
-- url     : https://prove2.me/submissions/c80c5556-033b-4acd-b1e3-7130b5a1a0aa

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

variable {d : ℕ} [NeZero d]

private lemma x8_cp (x : ZMod d) : cyclicPhase d x = ZMod.stdAddChar x := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, cyclicPhase]

private lemma x8_conj (x : ZMod d) :
    conj (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, Circle.coe_inv]

private lemma x8_esum (c : ZMod d) :
    ∑ x : ZMod d, (ZMod.stdAddChar (x * c) : ℂ) = if c = 0 then (d : ℂ) else 0 := by
  rw [AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar d), ZMod.card]
  split_ifs <;> simp

private lemma x8_shift_pow (k : ℕ) (a b : ZMod d) :
    ((Matrix.of fun a b : ZMod d => if a = b + 1 then (1 : ℂ) else 0) ^ k) a b =
      if a = b + k then 1 else 0 := by
  induction k generalizing a b with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [ih, Matrix.of_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (b + 1)]
    · simp; congr 1; apply propext; constructor <;> intro h <;> rw [h] <;> ring
    · intro c _ hc; simp [hc]
    · simp

private lemma x8_weyl (n m a b : ZMod d) :
    weyl n m a b = if a = b + n then (ZMod.stdAddChar (b * m) : ℂ) else 0 := by
  simp only [weyl, Matrix.diagonal_pow, Matrix.mul_diagonal, x8_shift_pow, ZMod.natCast_zmod_val]
  split_ifs <;> simp [x8_cp, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, mul_comm]

private lemma x8_cf (j k : ZMod d) :
    cyclicFourier d j k = (ZMod.stdAddChar (j * k) : ℂ) / (Real.sqrt d : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  simp only [cyclicFourier, Matrix.submatrix_apply, qftMatrix, Matrix.of_apply]
  rw [ZMod.stdAddChar_apply, ← ZMod.natCast_zmod_val (j * k), ZMod.toCircle_natCast]
  rw [← ZMod.toCircle_natCast, ← ZMod.toCircle_natCast]
  have h : ((((ZMod.finEquiv n.succ).symm j : ℕ) * ((ZMod.finEquiv n.succ).symm k : ℕ) : ℕ) :
      ZMod n.succ) = (((j * k).val : ℕ) : ZMod n.succ) := by
    rw [ZMod.natCast_zmod_val]; push_cast
    congr 1
    · exact ZMod.natCast_zmod_val (n := n.succ) j
    · exact ZMod.natCast_zmod_val (n := n.succ) k
  rw [h]

private lemma x8_sqrt_sq : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = d := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp

private lemma x8_d_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)

private lemma x8_jp (k l a b a' b' : ZMod d) :
    jointProjector k l (a, b) (a', b') =
      (ZMod.stdAddChar (a * (b - k) - l * b - (a' * (b' - k) - l * b')) : ℂ) / (d : ℂ) ^ 2 := by
  simp only [jointProjector, pureDensity, jointKet, Matrix.of_apply, x8_cp, map_div₀, x8_conj,
    Complex.conj_natCast]
  rw [sub_eq_add_neg _ (_ - _), AddChar.map_add_eq_mul]
  ring

private lemma x8_fk (c b b' : ZMod d) :
    pureDensity (fourierKet c) b b' = (ZMod.stdAddChar (b * c - b' * c) : ℂ) / (d : ℂ) := by
  simp only [pureDensity, fourierKet, Matrix.of_apply, x8_cp, map_div₀, x8_conj,
    Complex.conj_ofReal]
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, ← x8_sqrt_sq]
  ring

private lemma x8_left (l a b a' b' : ZMod d) :
    leftProjector l (a, b) (a', b') =
      if a = a' then (ZMod.stdAddChar (b * (a - l) - b' * (a - l)) : ℂ) / (d : ℂ) else 0 := by
  simp only [leftProjector, Matrix.sum_apply, Matrix.kronecker_apply, Matrix.single_apply, x8_fk]
  split_ifs with h
  · subst h; rw [Finset.sum_eq_single a] <;> simp_all [x8_fk, Matrix.single_apply]
  · apply Finset.sum_eq_zero; intro c _
    have : Matrix.single c c (1 : ℂ) a a' = 0 := by
      rw [Matrix.single_apply, if_neg]; rintro ⟨h1, h2⟩; exact h (h1.symm.trans h2)
    simp [this]

private lemma x8_right (k a b a' b' : ZMod d) :
    rightProjector k (a, b) (a', b') =
      if b = b' then (ZMod.stdAddChar (a * (b - k) - a' * (b - k)) : ℂ) / (d : ℂ) else 0 := by
  simp only [rightProjector, Matrix.sum_apply, Matrix.kronecker_apply, Matrix.single_apply, x8_fk]
  split_ifs with h
  · subst h; rw [Finset.sum_eq_single b] <;> simp_all [x8_fk, Matrix.single_apply]
  · apply Finset.sum_eq_zero; intro c _
    have : Matrix.single c c (1 : ℂ) b b' = 0 := by
      rw [Matrix.single_apply, if_neg]; rintro ⟨h1, h2⟩; exact h (h1.symm.trans h2)
    simp [this]

private lemma x8_em (x y : ZMod d) :
    (ZMod.stdAddChar x : ℂ) * ZMod.stdAddChar y = ZMod.stdAddChar (x + y) :=
  (AddChar.map_add_eq_mul _ _ _).symm

private lemma x8_inner (n m : ZMod d) :
    cyclicFourier d * (weyl n m).map conj * (cyclicFourier d)ᴴ =
      (ZMod.stdAddChar (n * m) : ℂ) • weyl m n := by
  ext j k
  rw [Matrix.mul_apply]
  have inner : ∀ b, (cyclicFourier d * (weyl n m).map conj) j b =
      (ZMod.stdAddChar (j * (b + n)) : ℂ) / (Real.sqrt d : ℂ) * ZMod.stdAddChar (-(b * m)) := by
    intro b
    simp only [Matrix.mul_apply, Matrix.map_apply, x8_weyl, x8_cf, apply_ite conj, map_zero,
      x8_conj, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [inner, Matrix.conjTranspose_apply, x8_cf, Matrix.smul_apply, x8_weyl, smul_eq_mul]
  have term : ∀ b : ZMod d, (ZMod.stdAddChar (j * (b + n)) : ℂ) / (Real.sqrt d : ℂ) *
      ZMod.stdAddChar (-(b * m)) * star ((ZMod.stdAddChar (k * b) : ℂ) / (Real.sqrt d : ℂ)) =
      (ZMod.stdAddChar (j * n) : ℂ) / d * ZMod.stdAddChar (b * (j - m - k)) := by
    intro b
    rw [star_div₀, Complex.star_def, Complex.conj_ofReal, x8_conj]
    have : (ZMod.stdAddChar (j * (b + n)) : ℂ) * ZMod.stdAddChar (-(b * m)) *
        ZMod.stdAddChar (-(k * b)) = ZMod.stdAddChar (j * n) * ZMod.stdAddChar (b * (j - m - k)) := by
      rw [x8_em, x8_em, x8_em]; congr 1; ring
    have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (Nat.cast_pos.2 (NeZero.pos d)))
    rw [← x8_sqrt_sq]
    field_simp
    linear_combination this
  simp only [term, ← Finset.mul_sum, x8_esum]
  have hd := x8_d_ne (d := d)
  by_cases h : j = k + m
  · subst h
    rw [if_pos (by ring), if_pos rfl, x8_em]
    field_simp
    congr 1; ring
  · rw [if_neg, if_neg h]
    · simp
    · intro h'; apply h; linear_combination h'

private lemma x8_esum2 (C : ℂ) (c1 c2 : ZMod d) :
    ∑ k : ZMod d, ∑ l : ZMod d, C * ((ZMod.stdAddChar (k * c1) : ℂ) * ZMod.stdAddChar (l * c2)) =
      C * ((if c1 = 0 then (d : ℂ) else 0) * (if c2 = 0 then (d : ℂ) else 0)) := by
  rw [← x8_esum c1, ← x8_esum c2, Finset.sum_mul_sum, Finset.mul_sum]
  simp_rw [Finset.mul_sum]

private lemma x8_kron {I J : Type*} (A : Matrix I I ℂ) (B : Matrix J J ℂ) (a a' : I) (b b' : J) :
    Matrix.kronecker A B (a, b) (a', b') = A a a' * B b b' := rfl

private lemma x8_pairA (n m : ZMod d) :
    weylPair n m = cyclicPhase d (n * m) • Matrix.kronecker (weyl n m) (weyl m n) := by
  unfold weylPair
  rw [x8_inner, x8_cp]
  ext p q
  simp [Matrix.kronecker_apply]
  ring

private lemma x8_pairB (n m : ZMod d) :
    weylPair n m = ∑ k : ZMod d, ∑ l : ZMod d, cyclicPhase d (n * k + l * m) • jointProjector k l := by
  rw [x8_pairA]
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [Matrix.smul_apply, Matrix.sum_apply, x8_kron, x8_weyl, x8_cp, x8_jp,
    smul_eq_mul]
  have term : ∀ k l : ZMod d, (ZMod.stdAddChar (n * k + l * m) : ℂ) *
      ((ZMod.stdAddChar (a * (b - k) - l * b - (a' * (b' - k) - l * b')) : ℂ) / (d : ℂ) ^ 2) =
      (ZMod.stdAddChar (a * b - a' * b') : ℂ) / (d : ℂ) ^ 2 *
        ((ZMod.stdAddChar (k * (n - a + a')) : ℂ) * ZMod.stdAddChar (l * (m - b + b'))) := by
    intro k l
    rw [x8_em, mul_div_assoc', div_mul_eq_mul_div, x8_em, x8_em]; congr 2; ring
  simp only [term, x8_esum2]
  have hd := x8_d_ne (d := d)
  have e1 : (n - a + a' = 0) = (a = a' + n) :=
    propext ⟨fun h => by linear_combination -h, fun h => by rw [h]; ring⟩
  have e2 : (m - b + b' = 0) = (b = b' + m) :=
    propext ⟨fun h => by linear_combination -h, fun h => by rw [h]; ring⟩
  simp only [e1, e2]
  split_ifs with h1 h2
  · subst h1 h2
    rw [x8_em, x8_em, ← sq, div_mul_eq_mul_div, mul_div_cancel_right₀ _ (pow_ne_zero 2 hd)]
    congr 1; ring
  all_goals simp

private lemma x8_pd_herm {I : Type*} (ψ : EuclideanSpace ℂ I) : (pureDensity ψ).IsHermitian := by
  ext i j; simp [pureDensity, mul_comm]

private lemma x8_pd_mul {I : Type*} [Fintype I] (ψ φ : EuclideanSpace ℂ I) (p r : I) :
    (pureDensity ψ * pureDensity φ) p r = ψ p * (∑ q, conj (ψ q) * φ q) * conj (φ r) := by
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => by ring

private lemma x8_jk_inner (k l k' l' : ZMod d) :
    ∑ q, conj (jointKet k l q) * jointKet k' l' q = if k = k' ∧ l = l' then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [jointKet, x8_cp, map_div₀, x8_conj, Complex.conj_natCast]
  have term : ∀ a b : ZMod d, (ZMod.stdAddChar (-(a * (b - k) - l * b)) : ℂ) / d *
      ((ZMod.stdAddChar (a * (b - k') - l' * b) : ℂ) / d) =
      1 / (d : ℂ) ^ 2 * ((ZMod.stdAddChar (a * (k - k')) : ℂ) * ZMod.stdAddChar (b * (l - l'))) := by
    intro a b
    rw [div_mul_div_comm, x8_em, x8_em, one_div, ← div_eq_inv_mul, sq]; congr 2; ring
  simp only [term, x8_esum2]
  have hd := x8_d_ne (d := d)
  by_cases h1 : k = k'
  · by_cases h2 : l = l'
    · subst h1 h2; simp; field_simp
    · rw [if_neg (sub_ne_zero.2 h2)]; simp [h2]
  · rw [if_neg (sub_ne_zero.2 h1)]; simp [h1]

private lemma x8_esum1 (C : ℂ) (c : ZMod d) :
    ∑ t : ZMod d, C * (ZMod.stdAddChar (t * c) : ℂ) = C * (if c = 0 then (d : ℂ) else 0) := by
  rw [← Finset.mul_sum, x8_esum]

private lemma x8_joint_CO : CompleteOrthogonal (fun kl : ZMod d × ZMod d => jointProjector kl.1 kl.2) := by
  refine ⟨fun kl => ⟨x8_pd_herm _, ?_⟩, fun kl kl' hne => ?_, ?_⟩
  · ext p r
    unfold jointProjector
    rw [x8_pd_mul, x8_jk_inner, if_pos ⟨rfl, rfl⟩]
    simp [pureDensity]
  · ext p r
    unfold jointProjector
    rw [x8_pd_mul, x8_jk_inner, if_neg]
    · simp
    · rintro ⟨h1, h2⟩; exact hne (Prod.ext h1 h2)
  · ext ⟨a, b⟩ ⟨a', b'⟩
    rw [Matrix.sum_apply, Fintype.sum_prod_type]
    simp only [x8_jp]
    have term : ∀ k l : ZMod d,
        (ZMod.stdAddChar (a * (b - k) - l * b - (a' * (b' - k) - l * b')) : ℂ) / (d : ℂ) ^ 2 =
        (ZMod.stdAddChar (a * b - a' * b') : ℂ) / (d : ℂ) ^ 2 *
          ((ZMod.stdAddChar (k * (a' - a)) : ℂ) * ZMod.stdAddChar (l * (b' - b))) := by
      intro k l
      rw [x8_em, show a * (b - k) - l * b - (a' * (b' - k) - l * b') =
        (a * b - a' * b') + (k * (a' - a) + l * (b' - b)) by ring, AddChar.map_add_eq_mul]; ring
    simp only [term, x8_esum2, Matrix.one_apply, Prod.mk.injEq]
    have hd := x8_d_ne (d := d)
    by_cases h1 : a = a'
    · by_cases h2 : b = b'
      · subst h1 h2; simp; field_simp
      · rw [if_neg (sub_ne_zero.2 (Ne.symm h2))]; simp [h2]
    · rw [if_neg (sub_ne_zero.2 (Ne.symm h1))]; simp [h1]

private lemma x8_left_mul (l l' : ZMod d) (a b a'' b'' : ZMod d) :
    (leftProjector l * leftProjector l') (a, b) (a'', b'') =
      if l = l' then leftProjector l (a, b) (a'', b'') else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [x8_left, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single a]
  · simp only [if_true]
    by_cases ha : a = a''
    · subst ha
      simp only [if_true]
      have term : ∀ e : ZMod d,
          (ZMod.stdAddChar (b * (a - l) - e * (a - l)) : ℂ) / d *
            ((ZMod.stdAddChar (e * (a - l') - b'' * (a - l')) : ℂ) / d) =
          (ZMod.stdAddChar (b * (a - l) - b'' * (a - l')) : ℂ) / (d : ℂ) ^ 2 *
            ZMod.stdAddChar (e * (l - l')) := by
        intro e
        rw [div_mul_div_comm, x8_em, show b * (a - l) - e * (a - l) + (e * (a - l') - b'' * (a - l')) =
          (b * (a - l) - b'' * (a - l')) + e * (l - l') by ring, AddChar.map_add_eq_mul]; ring
      simp only [term, x8_esum1]
      have hd := x8_d_ne (d := d)
      by_cases hl : l = l'
      · subst hl; simp; field_simp
      · rw [if_neg (sub_ne_zero.2 hl), if_neg hl]; simp
    · simp [ha]
  · intro c _ hc; simp [Ne.symm hc]
  · simp

private lemma x8_right_mul (k k' : ZMod d) (a b a'' b'' : ZMod d) :
    (rightProjector k * rightProjector k') (a, b) (a'', b'') =
      if k = k' then rightProjector k (a, b) (a'', b'') else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [x8_right, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_eq_single b]
  · simp only [if_true]
    by_cases hb : b = b''
    · subst hb
      simp only [if_true]
      have term : ∀ e : ZMod d,
          (ZMod.stdAddChar (a * (b - k) - e * (b - k)) : ℂ) / d *
            ((ZMod.stdAddChar (e * (b - k') - a'' * (b - k')) : ℂ) / d) =
          (ZMod.stdAddChar (a * (b - k) - a'' * (b - k')) : ℂ) / (d : ℂ) ^ 2 *
            ZMod.stdAddChar (e * (k - k')) := by
        intro e
        rw [div_mul_div_comm, x8_em, show a * (b - k) - e * (b - k) + (e * (b - k') - a'' * (b - k')) =
          (a * (b - k) - a'' * (b - k')) + e * (k - k') by ring, AddChar.map_add_eq_mul]; ring
      simp only [term, x8_esum1]
      have hd := x8_d_ne (d := d)
      by_cases hk : k = k'
      · subst hk; simp; field_simp
      · rw [if_neg (sub_ne_zero.2 hk), if_neg hk]; simp
    · simp [hb]
  · intro c _ hc; simp [Ne.symm hc]
  · simp

private lemma x8_left_CO : CompleteOrthogonal (leftProjector (d := d)) := by
  refine ⟨fun l => ⟨?_, ?_⟩, fun l l' hne => ?_, ?_⟩
  · ext ⟨a, b⟩ ⟨a', b'⟩
    rw [Matrix.conjTranspose_apply, x8_left, x8_left]
    by_cases h : a = a'
    · subst h; simp only [if_true, star_div₀, Complex.star_def, x8_conj, Complex.conj_natCast]
      congr 2; ring
    · rw [if_neg (Ne.symm h), if_neg h]; simp
  · ext ⟨a, b⟩ ⟨a', b'⟩; rw [x8_left_mul, if_pos rfl]
  · ext ⟨a, b⟩ ⟨a', b'⟩; rw [x8_left_mul, if_neg hne]; rfl
  · ext ⟨a, b⟩ ⟨a', b'⟩
    rw [Matrix.sum_apply]
    simp only [x8_left, Matrix.one_apply, Prod.mk.injEq]
    by_cases h : a = a'
    · subst h
      simp only [if_true, true_and]
      have term : ∀ l : ZMod d, (ZMod.stdAddChar (b * (a - l) - b' * (a - l)) : ℂ) / d =
          (ZMod.stdAddChar (a * (b - b')) : ℂ) / d * ZMod.stdAddChar (l * (b' - b)) := by
        intro l
        rw [show b * (a - l) - b' * (a - l) = a * (b - b') + l * (b' - b) by ring,
          AddChar.map_add_eq_mul]; ring
      simp only [term, x8_esum1]
      have hd := x8_d_ne (d := d)
      by_cases h2 : b = b'
      · subst h2; simp
      · rw [if_neg (sub_ne_zero.2 (Ne.symm h2)), if_neg h2]; simp
    · simp [h]

private lemma x8_right_CO : CompleteOrthogonal (rightProjector (d := d)) := by
  refine ⟨fun k => ⟨?_, ?_⟩, fun k k' hne => ?_, ?_⟩
  · ext ⟨a, b⟩ ⟨a', b'⟩
    rw [Matrix.conjTranspose_apply, x8_right, x8_right]
    by_cases h : b = b'
    · subst h; simp only [if_true, star_div₀, Complex.star_def, x8_conj, Complex.conj_natCast]
      congr 2; ring
    · rw [if_neg (Ne.symm h), if_neg h]; simp
  · ext ⟨a, b⟩ ⟨a', b'⟩; rw [x8_right_mul, if_pos rfl]
  · ext ⟨a, b⟩ ⟨a', b'⟩; rw [x8_right_mul, if_neg hne]; rfl
  · ext ⟨a, b⟩ ⟨a', b'⟩
    rw [Matrix.sum_apply]
    simp only [x8_right, Matrix.one_apply, Prod.mk.injEq]
    by_cases h : b = b'
    · subst h
      simp only [if_true, and_true]
      have term : ∀ k : ZMod d, (ZMod.stdAddChar (a * (b - k) - a' * (b - k)) : ℂ) / d =
          (ZMod.stdAddChar (b * (a - a')) : ℂ) / d * ZMod.stdAddChar (k * (a' - a)) := by
        intro k
        rw [show a * (b - k) - a' * (b - k) = b * (a - a') + k * (a' - a) by ring,
          AddChar.map_add_eq_mul]; ring
      simp only [term, x8_esum1]
      have hd := x8_d_ne (d := d)
      by_cases h2 : a = a'
      · subst h2; simp
      · rw [if_neg (sub_ne_zero.2 (Ne.symm h2)), if_neg h2]; simp
    · simp [h]

private lemma x8_deph (k l : ZMod d) :
    dephaseInput (jointProjector k l) = (1 / (d : ℂ)) • leftProjector l ∧
    leftProjector l = ∑ t : ZMod d, jointProjector t l ∧
    dephaseOutput (jointProjector k l) = (1 / (d : ℂ)) • rightProjector k ∧
    rightProjector k = ∑ t : ZMod d, jointProjector k t := by
  have hd := x8_d_ne (d := d)
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [dephaseInput, Matrix.smul_apply, x8_left, x8_jp, smul_eq_mul]
    by_cases h : a = a'
    · subst h; simp only [if_true]
      rw [show a * (b - k) - l * b - (a * (b' - k) - l * b') = b * (a - l) - b' * (a - l) by ring]
      field_simp
    · simp [h]
  · ext ⟨a, b⟩ ⟨a', b'⟩
    rw [Matrix.sum_apply]
    simp only [x8_left, x8_jp]
    have term : ∀ t : ZMod d,
        (ZMod.stdAddChar (a * (b - t) - l * b - (a' * (b' - t) - l * b')) : ℂ) / (d : ℂ) ^ 2 =
        (ZMod.stdAddChar (a * b - l * b - (a' * b' - l * b')) : ℂ) / (d : ℂ) ^ 2 *
          ZMod.stdAddChar (t * (a' - a)) := by
      intro t
      rw [show a * (b - t) - l * b - (a' * (b' - t) - l * b') =
        (a * b - l * b - (a' * b' - l * b')) + t * (a' - a) by ring, AddChar.map_add_eq_mul]; ring
    simp only [term, x8_esum1]
    by_cases h : a = a'
    · subst h; simp only [if_true, sub_self]
      rw [show a * b - l * b - (a * b' - l * b') = b * (a - l) - b' * (a - l) by ring]
      field_simp
    · rw [if_neg h, if_neg (sub_ne_zero.2 (Ne.symm h))]; simp
  · ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [dephaseOutput, Matrix.smul_apply, x8_right, x8_jp, smul_eq_mul]
    by_cases h : b = b'
    · subst h; simp only [if_true]
      rw [show a * (b - k) - l * b - (a' * (b - k) - l * b) = a * (b - k) - a' * (b - k) by ring]
      field_simp
    · simp [h]
  · ext ⟨a, b⟩ ⟨a', b'⟩
    rw [Matrix.sum_apply]
    simp only [x8_right, x8_jp]
    have term : ∀ t : ZMod d,
        (ZMod.stdAddChar (a * (b - k) - t * b - (a' * (b' - k) - t * b')) : ℂ) / (d : ℂ) ^ 2 =
        (ZMod.stdAddChar (a * (b - k) - a' * (b' - k)) : ℂ) / (d : ℂ) ^ 2 *
          ZMod.stdAddChar (t * (b' - b)) := by
      intro t
      rw [show a * (b - k) - t * b - (a' * (b' - k) - t * b') =
        (a * (b - k) - a' * (b' - k)) + t * (b' - b) by ring, AddChar.map_add_eq_mul]; ring
    simp only [term, x8_esum1]
    by_cases h : b = b'
    · subst h; simp only [if_true, sub_self]
      field_simp
    · rw [if_neg h, if_neg (sub_ne_zero.2 (Ne.symm h))]; simp

theorem x8_main (d : ℕ) [NeZero d] :
    (∀ n m : ZMod d,
      weylPair n m = cyclicPhase d (n*m) • Matrix.kronecker (weyl n m) (weyl m n) ∧
      weylPair n m = ∑ k : ZMod d, ∑ l : ZMod d,
        cyclicPhase d (n*k + l*m) • jointProjector k l) ∧
    CompleteOrthogonal (fun kl : ZMod d × ZMod d => jointProjector kl.1 kl.2) ∧
    CompleteOrthogonal (leftProjector (d := d)) ∧
    CompleteOrthogonal (rightProjector (d := d)) ∧
    (∀ k l : ZMod d,
      dephaseInput (jointProjector k l) = (1 / (d : ℂ)) • leftProjector l ∧
      leftProjector l = ∑ t : ZMod d, jointProjector t l ∧
      dephaseOutput (jointProjector k l) = (1 / (d : ℂ)) • rightProjector k ∧
      rightProjector k = ∑ t : ZMod d, jointProjector k t) :=
  ⟨fun n m => ⟨x8_pairA n m, x8_pairB n m⟩, x8_joint_CO, x8_left_CO, x8_right_CO, x8_deph⟩

end QAlgorithms.Papers.Independent.Information100.P34

open QAlgorithms.Papers.Independent.Information100.P34 in
theorem solution (d : ℕ) [NeZero d] :
    (∀ n m : ZMod d,
      weylPair n m = cyclicPhase d (n*m) • Matrix.kronecker (weyl n m) (weyl m n) ∧
      weylPair n m = ∑ k : ZMod d, ∑ l : ZMod d,
        cyclicPhase d (n*k + l*m) • jointProjector k l) ∧
    CompleteOrthogonal (fun kl : ZMod d × ZMod d => jointProjector kl.1 kl.2) ∧
    CompleteOrthogonal (leftProjector (d := d)) ∧
    CompleteOrthogonal (rightProjector (d := d)) ∧
    (∀ k l : ZMod d,
      dephaseInput (jointProjector k l) = (1 / (d : ℂ)) • leftProjector l ∧
      leftProjector l = ∑ t : ZMod d, jointProjector t l ∧
      dephaseOutput (jointProjector k l) = (1 / (d : ℂ)) • rightProjector k ∧
      rightProjector k = ∑ t : ZMod d, jointProjector k t) := x8_main d
