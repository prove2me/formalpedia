-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P40.bellProtocol_averageFidelity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T03:42:40.821055+00:00
-- url     : https://prove2.me/submissions/644aafb7-76a9-4e8d-ba7f-a0fe6c51ced6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P40
import Theorems.Thm_QAlgorithms_Papers_RoadmapX07_averageFidelity_eq_entanglementFidelity
noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P40

namespace G65P

lemma shift_pow (n : ℕ) (t : ℕ) (i j : Fin n) :
    (cyclicShift n ^ t) i j = if i.val = (j.val + t) % n then 1 else 0 := by
  induction t generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, add_zero, Nat.mod_eq_of_lt j.isLt]
    simp [Fin.ext_iff]
  | succ t ih =>
    have hn : 0 < n := Fin.pos i
    rw [pow_succ, Matrix.mul_apply]
    have hk : ∀ k : Fin n, (cyclicShift n ^ t) i k * cyclicShift n k j =
        if k = ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩ then
          (if i.val = (k.val + t) % n then 1 else 0) else 0 := by
      intro k
      rw [ih]
      simp only [cyclicShift, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> simp_all
    simp_rw [hk]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [Nat.mod_add_mod, show j.val + 1 + t = j.val + (t + 1) by ring]

lemma clock_pow (n : ℕ) (s : ℕ) (i j : Fin n) :
    (negativePhaseClock n ^ s) i j = if i = j then clockRoot n ^ (j.val * s) else 0 := by
  induction s generalizing i j with
  | zero => simp [Matrix.one_apply]
  | succ s ih =>
    rw [pow_succ, Matrix.mul_apply]
    have hk : ∀ k : Fin n, (negativePhaseClock n ^ s) i k * negativePhaseClock n k j =
        if k = j then (if i = j then clockRoot n ^ (j.val * (s + 1)) else 0) else 0 := by
      intro k
      rw [ih]
      simp only [negativePhaseClock, Matrix.of_apply]
      by_cases h1 : k = j
      · subst h1
        by_cases h2 : i = k
        · subst h2; simp [pow_add, mul_add]
        · simp [h2]
      · simp [h1]
    simp_rw [hk]
    rw [Finset.sum_ite_eq']
    simp

lemma weyl_apply {n : ℕ} (m : BellLabel n) (i j : Fin n) :
    bellWeyl m i j = if i.val = (j.val + m.2.val) % n then clockRoot n ^ (j.val * m.1.val) else 0 := by
  unfold bellWeyl
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [shift_pow, clock_pow]; simp
  · intro b _ hb; rw [clock_pow, if_neg hb, mul_zero]
  · simp

lemma clock_norm (n : ℕ) (hn : 0 < n) : ‖clockRoot n‖ = 1 := by
  unfold clockRoot
  rw [Complex.norm_exp]
  have : (-(2 * (Real.pi : ℂ) * Complex.I) / (n : ℂ)).re = 0 := by
    rw [Complex.div_re]; simp
  rw [this, Real.exp_zero]

lemma clock_prim (n : ℕ) (hn : 0 < n) : IsPrimitiveRoot (clockRoot n) n := by
  have h := Complex.isPrimitiveRoot_exp n (by omega)
  have : clockRoot n = (Complex.exp (2 * Real.pi * Complex.I / n))⁻¹ := by
    unfold clockRoot; rw [← Complex.exp_neg]; congr 1; ring
  rw [this]; exact h.inv


lemma shift_iff {n : ℕ} [NeZero n] (p1 p2 t : Fin n) :
    p2.val = (p1.val + t.val) % n ↔ t = p2 - p1 := by
  rw [← Fin.val_add, ← Fin.ext_iff, eq_sub_iff_add_eq, add_comm, eq_comm]

lemma conj_clock (n : ℕ) (hn : 0 < n) : conj (clockRoot n) = clockRoot n ^ (n - 1) := by
  have h1 : ‖clockRoot n‖ = 1 := clock_norm n hn
  have hp := clock_prim n hn
  have hne : clockRoot n ≠ 0 := by intro h; rw [h] at h1; simp at h1
  have hc : conj (clockRoot n) * clockRoot n = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  have hp2 : clockRoot n ^ (n - 1) * clockRoot n = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hn, hp.pow_eq_one]
  exact mul_right_cancel₀ hne (hc.trans hp2.symm)

lemma clock_sum (n : ℕ) (hn : 0 < n) (p q : Fin n) :
    ∑ s : Fin n, conj (clockRoot n ^ (p.val * s.val)) * clockRoot n ^ (q.val * s.val) =
      if p = q then (n : ℂ) else 0 := by
  have hp := clock_prim n hn
  set ζ := clockRoot n ^ ((n - 1) * p.val + q.val) with hζ
  have hterm : ∀ s : Fin n, conj (clockRoot n ^ (p.val * s.val)) * clockRoot n ^ (q.val * s.val) =
      ζ ^ s.val := by
    intro s
    rw [map_pow, conj_clock n hn, hζ, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1; ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun s => ζ ^ s)]
  by_cases hpq : p = q
  · subst hpq
    have : ζ = 1 := by
      have e : (n - 1) * p.val + p.val = n * p.val := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      rw [hζ, e, pow_mul, hp.pow_eq_one, one_pow]
    simp [this]
  · rw [if_neg hpq]
    have hz1 : ζ ^ n = 1 := by rw [hζ, ← pow_mul, mul_comm, pow_mul, hp.pow_eq_one, one_pow]
    have hz : ζ ≠ 1 := by
      intro h
      rw [hζ, hp.pow_eq_one_iff_dvd] at h
      apply hpq
      have h2 : (n : ℤ) ∣ ((n - 1 : ℕ) : ℤ) * p.val + q.val := by exact_mod_cast h
      have h3 : (n : ℤ) ∣ (q.val : ℤ) - p.val := by
        have : ((n - 1 : ℕ) : ℤ) * p.val + q.val = (n : ℤ) * p.val + ((q.val : ℤ) - p.val) := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
        rw [this] at h2
        exact (dvd_add_right (dvd_mul_right _ _)).1 h2
      have hb : |(q.val : ℤ) - p.val| < n := by
        rw [abs_lt]; constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd h3 hb
      ext; omega
    have := geom_sum_mul ζ n
    rw [hz1, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hz)

lemma bv_apply (n : ℕ) (hn : 0 < n) (m : BellLabel n) (i j : Fin n) :
    generalizedBellVector n hn m (i, j) = conj (bellWeyl m j i) * ((Real.sqrt n)⁻¹ : ℂ) := by
  unfold generalizedBellVector maximallyEntangledVector finiteMaxEntangled act
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Matrix.map_apply, Fintype.card_fin, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma bv_complete (n : ℕ) (hn : 0 < n) (p q : Fin n × Fin n) :
    ∑ m : BellLabel n, generalizedBellVector n hn m p * conj (generalizedBellVector n hn m q) =
      if p = q then 1 else 0 := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  have hsq : ((Real.sqrt n)⁻¹ : ℂ) * conj ((Real.sqrt n)⁻¹ : ℂ) = (n : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg n)]; push_cast; rfl
  have key : ∀ m : BellLabel n, generalizedBellVector n hn m (p1, p2) *
      conj (generalizedBellVector n hn m (q1, q2)) =
      (n : ℂ)⁻¹ * ((if m.2 = p2 - p1 then 1 else 0) * (if m.2 = q2 - q1 then 1 else 0) *
        (conj (clockRoot n ^ (p1.val * m.1.val)) * clockRoot n ^ (q1.val * m.1.val))) := by
    intro m
    rw [bv_apply, bv_apply, weyl_apply, weyl_apply, ← hsq]
    simp only [shift_iff]
    split_ifs <;> simp [map_mul] <;> ring
  simp_rw [key]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  have h1 : ∀ s : Fin n, ∑ t : Fin n, (if t = p2 - p1 then (1 : ℂ) else 0) *
      (if t = q2 - q1 then 1 else 0) *
        (conj (clockRoot n ^ (p1.val * s.val)) * clockRoot n ^ (q1.val * s.val)) =
      if p2 - p1 = q2 - q1 then
        conj (clockRoot n ^ (p1.val * s.val)) * clockRoot n ^ (q1.val * s.val) else 0 := by
    intro s
    rw [Finset.sum_eq_single (p2 - p1)]
    · split_ifs <;> simp_all
    · intro b _ hb; simp [hb]
    · simp
  simp only [h1]
  by_cases h : p2 - p1 = q2 - q1
  · simp only [h, if_true]
    rw [clock_sum n hn]
    by_cases hp : p1 = q1
    · subst hp
      have : p2 = q2 := by simpa using h
      subst this
      simp only [if_true]
      have : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      field_simp
    · rw [if_neg hp, if_neg (fun e => hp (Prod.mk.inj e).1)]; simp
  · rw [if_neg (fun e => h (by rw [(Prod.mk.inj e).1, (Prod.mk.inj e).2]))]
    simp [h]


lemma weyl_col {n : ℕ} (hn : 0 < n) (m : BellLabel n) (i : Fin n) :
    ∑ j : Fin n, conj (bellWeyl m j i) * bellWeyl m j i = 1 := by
  haveI : NeZero n := ⟨by omega⟩
  have : ∀ j : Fin n, conj (bellWeyl m j i) * bellWeyl m j i = if j = i + m.2 then 1 else 0 := by
    intro j
    rw [weyl_apply, ← Fin.val_add]
    split_ifs with h h'
    · rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow,
        clock_norm n hn]; simp
    · exact absurd (Fin.ext h) h'
    · exact absurd (congrArg Fin.val ‹j = i + m.2›) h
    · simp
  simp_rw [this]; simp

lemma bv_norm (n : ℕ) (hn : 0 < n) (m : BellLabel n) :
    ∑ x : Fin n × Fin n, generalizedBellVector n hn m x * conj (generalizedBellVector n hn m x) = 1 := by
  have hsq : ((Real.sqrt n)⁻¹ : ℂ) * conj ((Real.sqrt n)⁻¹ : ℂ) = (n : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg n)]; push_cast; rfl
  rw [Fintype.sum_prod_type]
  have : ∀ i j : Fin n, generalizedBellVector n hn m (i, j) * conj (generalizedBellVector n hn m (i, j)) =
      (n : ℂ)⁻¹ * (conj (bellWeyl m j i) * bellWeyl m j i) := by
    intro i j; rw [bv_apply, ← hsq]; simp only [map_mul, Complex.conj_conj]; ring
  simp_rw [this, ← Finset.mul_sum, weyl_col hn]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

lemma sum4 {α : Type*} [Fintype α] (f : α → α → α → α → ℂ) :
    ∑ c, ∑ d, ∑ a, ∑ b, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := by
  calc ∑ c, ∑ d, ∑ a, ∑ b, f a b c d = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm

lemma branch_apply {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n) (m : BellLabel n)
    (rho : QuditMatrix n) (k l : Fin n) :
    unnormalizedBellBranch hn chi m rho k l =
      ∑ y : Fin n × Fin n, ∑ z : Fin n × Fin n,
        conj (generalizedBellVector n hn m y) * generalizedBellVector n hn m z *
          rho y.1 z.1 * chi (y.2, k) (z.2, l) := by
  simp only [unnormalizedBellBranch, traceLeft, conjSuperop, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    generalizedBellProjector, pureDensity, initialJoint, Fintype.sum_prod_type]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, apply_ite (star : ℂ → ℂ), star_zero, Finset.sum_ite_eq']
  have hN := bv_norm n hn m
  rw [Fintype.sum_prod_type] at hN
  have e : ∀ x y x1 x2,
      (∑ x4, ∑ x5, generalizedBellVector n hn m (x, y) * conj (generalizedBellVector n hn m (x4, x5)) *
        (rho x4 x1 * chi (x5, k) (x2, l))) *
        star (generalizedBellVector n hn m (x, y) * conj (generalizedBellVector n hn m (x1, x2))) =
      (generalizedBellVector n hn m (x, y) * conj (generalizedBellVector n hn m (x, y))) * ∑ x4, ∑ x5,
        conj (generalizedBellVector n hn m (x4, x5)) * generalizedBellVector n hn m (x1, x2) *
          rho x4 x1 * chi (x5, k) (x2, l) := by
    intro x y x1 x2
    simp only [Finset.sum_mul, Finset.mul_sum, star_mul', Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [e, ← Finset.mul_sum, ← Finset.sum_mul, hN, one_mul]
  exact sum4 (fun a b c d => conj (generalizedBellVector n hn m (a, b)) *
    generalizedBellVector n hn m (c, d) * rho a c * chi (b, k) (d, l))


lemma sum4' {α β : Type*} [Fintype α] [Fintype β] (f : α → α → β → β → ℂ) :
    ∑ a, ∑ b, ∑ p, ∑ q, f a b p q = ∑ p, ∑ q, ∑ a, ∑ b, f a b p q := by
  calc ∑ a, ∑ b, ∑ p, ∑ q, f a b p q = ∑ a, ∑ p, ∑ b, ∑ q, f a b p q :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ p, ∑ a, ∑ b, ∑ q, f a b p q := Finset.sum_comm
    _ = ∑ p, ∑ a, ∑ q, ∑ b, f a b p q :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ a, ∑ b, f a b p q := Finset.sum_congr rfl fun p _ => Finset.sum_comm

lemma coef_apply {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n) (a b : BellLabel n) :
    resourceBellCoefficient hn chi a b = ∑ p, ∑ q,
      conj (generalizedBellVector n hn a p) * chi p q * generalizedBellVector n hn b q := by
  unfold resourceBellCoefficient act
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Matrix.mulVec, Finset.mul_sum,
    Pi.star_apply, RCLike.star_def, WithLp.ofLp_toLp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma chi_exp {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n) (p q : Fin n × Fin n) :
    chi p q = ∑ a, ∑ b, resourceBellCoefficient hn chi a b *
      generalizedBellVector n hn a p * conj (generalizedBellVector n hn b q) := by
  simp only [coef_apply, Finset.sum_mul]
  rw [sum4' (fun a b p' q' => conj (generalizedBellVector n hn a p') * chi p' q' *
      generalizedBellVector n hn b q' * generalizedBellVector n hn a p *
        conj (generalizedBellVector n hn b q))]
  have e : ∀ p' q', ∑ a, ∑ b, conj (generalizedBellVector n hn a p') * chi p' q' *
      generalizedBellVector n hn b q' * generalizedBellVector n hn a p *
        conj (generalizedBellVector n hn b q) =
      chi p' q' * (∑ a, generalizedBellVector n hn a p * conj (generalizedBellVector n hn a p')) *
        (∑ b, generalizedBellVector n hn b q' * conj (generalizedBellVector n hn b q)) := by
    intro p' q'
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
  simp_rw [e, bv_complete]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, eq_comm]

lemma L1 {n : ℕ} (hn : 0 < n) (a m : BellLabel n) (k y1 : Fin n) :
    ((bellWeyl a).map conj * bellWeyl m) k y1 =
      (n : ℂ) * ∑ y2, conj (generalizedBellVector n hn m (y1, y2)) * generalizedBellVector n hn a (y2, k) := by
  have hsq : ((Real.sqrt n)⁻¹ : ℂ) * ((Real.sqrt n)⁻¹ : ℂ) = (n : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg n)]; push_cast; rfl
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [Matrix.mul_apply, Matrix.map_apply, bv_apply, map_mul, Complex.conj_conj,
    Complex.conj_ofReal, ← Complex.ofReal_inv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y2 _ => ?_
  have : ((Real.sqrt n)⁻¹ : ℝ) * ((Real.sqrt n)⁻¹ : ℝ) = (n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  have h2 : ((n : ℂ)) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [mul_assoc, ← Complex.ofReal_mul, this]; push_cast; field_simp
  linear_combination (bellWeyl m y2 y1 * conj (bellWeyl a k y2)) * h2.symm

lemma L2 {n : ℕ} (hn : 0 < n) (b m : BellLabel n) (z1 l : Fin n) :
    ((bellWeyl m)ᴴ * ((bellWeyl b).map conj)ᴴ) z1 l =
      (n : ℂ) * ∑ z2, generalizedBellVector n hn m (z1, z2) * conj (generalizedBellVector n hn b (z2, l)) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply, bv_apply, map_mul,
    Complex.conj_conj, Complex.conj_ofReal, ← Complex.ofReal_inv, Complex.star_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z2 _ => ?_
  have : ((Real.sqrt n)⁻¹ : ℝ) * ((Real.sqrt n)⁻¹ : ℝ) = (n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  have h2 : ((n : ℂ)) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [mul_assoc, ← Complex.ofReal_mul, this]; push_cast; field_simp
  linear_combination (conj (bellWeyl m z2 z1) * bellWeyl b l z2) * h2.symm


lemma branch_exp {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n) (m : BellLabel n)
    (rho : QuditMatrix n) :
    unnormalizedBellBranch hn chi m rho = ((n : ℂ) ^ 2)⁻¹ •
      ∑ a : BellLabel n, ∑ b : BellLabel n, resourceBellCoefficient hn chi a b •
        ((bellWeyl a).map conj * bellWeyl m * rho * (bellWeyl m)ᴴ * ((bellWeyl b).map conj)ᴴ) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  ext k l
  set Φ := fun c : BellLabel n => generalizedBellVector n hn c with hΦ
  set c := resourceBellCoefficient hn chi with hc
  set F : BellLabel n → BellLabel n → ℂ := fun a b => ∑ y : Fin n × Fin n, ∑ z : Fin n × Fin n,
    conj (Φ m y) * Φ a (y.2, k) * rho y.1 z.1 * Φ m z * conj (Φ b (z.2, l)) with hF
  have hL : unnormalizedBellBranch hn chi m rho k l = ∑ a, ∑ b, c a b * F a b := by
    rw [branch_apply]
    simp_rw [chi_exp hn chi, Finset.mul_sum]
    rw [sum4 (fun a b y z => conj (generalizedBellVector n hn m y) * generalizedBellVector n hn m z *
      rho y.1 z.1 * (resourceBellCoefficient hn chi a b * generalizedBellVector n hn a (y.2, k) *
        conj (generalizedBellVector n hn b (z.2, l))))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    simp only [hΦ, hc]; ring
  rw [hL]
  have e5 : ∀ a b : BellLabel n, (bellWeyl a).map conj * bellWeyl m * rho * (bellWeyl m)ᴴ *
      ((bellWeyl b).map conj)ᴴ = ((bellWeyl a).map conj * bellWeyl m) * rho *
        ((bellWeyl m)ᴴ * ((bellWeyl b).map conj)ᴴ) := by
    intro a b; simp only [Matrix.mul_assoc]
  simp only [e5, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.mul_apply, L1 hn, L2 hn, hF, hΦ, hc, Fintype.sum_prod_type]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [sum4 (fun y1 y2 z1 z2 => ((n : ℂ) ^ 2)⁻¹ * (resourceBellCoefficient hn chi a b *
    ((n : ℂ) * (conj (generalizedBellVector n hn m (y1, y2)) * generalizedBellVector n hn a (y2, k)) *
      rho y1 z1 * ((n : ℂ) * (generalizedBellVector n hn m (z1, z2) *
        conj (generalizedBellVector n hn b (z2, l)))))))]
  refine Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ =>
    Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
  field_simp


lemma tele_eq {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n) (T : BellLabel n → QuditMatrix n)
    (rho : QuditMatrix n) : teleportation hn chi T rho = bellExpansion hn chi T rho := by
  unfold teleportation bellExpansion
  simp only [branch_exp, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m _ => ?_
  simp only [Matrix.mul_assoc]

lemma sum5 {α β : Type*} [Fintype α] [Fintype β] (f : β → α → α → α → α → ℂ) :
    ∑ r, ∑ z1, ∑ y1, ∑ y2, ∑ z2, f r y1 y2 z1 z2 = ∑ y1, ∑ y2, ∑ z1, ∑ z2, ∑ r, f r y1 y2 z1 z2 := by
  calc ∑ r, ∑ z1, ∑ y1, ∑ y2, ∑ z2, f r y1 y2 z1 z2
      = ∑ r, ∑ y1, ∑ y2, ∑ z1, ∑ z2, f r y1 y2 z1 z2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y1 _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ y1, ∑ r, ∑ y2, ∑ z1, ∑ z2, f r y1 y2 z1 z2 := Finset.sum_comm
    _ = ∑ y1, ∑ y2, ∑ r, ∑ z1, ∑ z2, f r y1 y2 z1 z2 :=
        Finset.sum_congr rfl fun y1 _ => Finset.sum_comm
    _ = ∑ y1, ∑ y2, ∑ z1, ∑ r, ∑ z2, f r y1 y2 z1 z2 :=
        Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ => Finset.sum_comm
    _ = ∑ y1, ∑ y2, ∑ z1, ∑ z2, ∑ r, f r y1 y2 z1 z2 :=
        Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ =>
          Finset.sum_congr rfl fun z1 _ => Finset.sum_comm

/-- Kraus operators of a Bell branch, from a factorization chi = Bᴴ B -/
def K {n : ℕ} (hn : 0 < n) (B : ResourceMatrix n) (m : BellLabel n) (r : Fin n × Fin n) :
    QuditMatrix n :=
  Matrix.of fun k y1 => ∑ y2, conj (generalizedBellVector n hn m (y1, y2)) * conj (B r (y2, k))

lemma branch_kraus {n : ℕ} (hn : 0 < n) (B : ResourceMatrix n) (m : BellLabel n)
    (rho : QuditMatrix n) :
    unnormalizedBellBranch hn (Bᴴ * B) m rho = ∑ r, K hn B m r * rho * (K hn B m r)ᴴ := by
  ext k l
  have hchi : ∀ p q, (Bᴴ * B) p q = ∑ r, conj (B r p) * B r q := by
    intro p q; simp [Matrix.mul_apply]
  rw [branch_apply]
  simp_rw [hchi, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun y _ => Finset.sum_comm), Finset.sum_comm, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, K, Matrix.of_apply,
    star_sum, star_mul', Complex.star_def, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul,
    Fintype.sum_prod_type]
  rw [sum4 (fun y1 y2 z1 z2 => conj (generalizedBellVector n hn m (y1, y2)) * conj (B r (y2, k)) *
    rho y1 z1 * (generalizedBellVector n hn m (z1, z2) * B r (z2, l)))]
  refine Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ =>
    Finset.sum_congr rfl fun z1 _ => Finset.sum_congr rfl fun z2 _ => ?_
  ring


lemma swap32 {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype ε]
    (f : α → β → γ → δ → ε → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ d, ∑ e, ∑ a, ∑ b, ∑ c, f a b c d e := by
  have h1 : ∀ a b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ d, ∑ e, ∑ c, f a b c d e := by
    intro a b
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_comm
  have h2 : ∀ a, ∑ b, ∑ d, ∑ e, ∑ c, f a b c d e = ∑ d, ∑ e, ∑ b, ∑ c, f a b c d e := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_comm
  simp_rw [h1, h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_comm

lemma kraus_sum {n : ℕ} (hn : 0 < n) (B : ResourceMatrix n) (htr : (Bᴴ * B).trace = 1) :
    ∑ m, ∑ r, (K hn B m r)ᴴ * K hn B m r = 1 := by
  ext y1 z1
  have hchi : ∀ p q, (Bᴴ * B) p q = ∑ r, conj (B r p) * B r q := by
    intro p q; simp [Matrix.mul_apply]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, K, Matrix.of_apply,
    star_sum, star_mul', Complex.star_def, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  rw [swap32 (fun m r k z2 y2 => generalizedBellVector n hn m (y1, y2) * B r (y2, k) *
    (conj (generalizedBellVector n hn m (z1, z2)) * conj (B r (z2, k))))]
  have e : ∀ z2 y2, ∑ m, ∑ r, ∑ k, generalizedBellVector n hn m (y1, y2) * B r (y2, k) *
      (conj (generalizedBellVector n hn m (z1, z2)) * conj (B r (z2, k))) =
      (∑ m, generalizedBellVector n hn m (y1, y2) * conj (generalizedBellVector n hn m (z1, z2))) *
        ∑ k, (Bᴴ * B) (z2, k) (y2, k) := by
    intro z2 y2
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hchi, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun (k : Fin n) _ => Finset.sum_congr rfl fun (r : Fin n × Fin n) _ => by ring
  simp_rw [e, bv_complete]
  by_cases h : y1 = z1
  · subst h
    simp only [Prod.mk.injEq, true_and, Matrix.one_apply_eq, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← htr, Matrix.trace, Fintype.sum_prod_type]
    simp only [Matrix.diag]
  · simp [h, Matrix.one_apply_ne h]

end G65P


namespace G65P

lemma psi_apply (n : ℕ) (hn : 0 < n) (W : QuditMatrix n) (p : Fin n × Fin n) :
    act (Matrix.kronecker (1 : QuditMatrix n) W) (maximallyEntangledVector n hn) p =
      W p.2 p.1 * ((Real.sqrt n)⁻¹ : ℂ) := by
  obtain ⟨a, b⟩ := p
  unfold maximallyEntangledVector finiteMaxEntangled act
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.card_fin, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  · intro c _ hc; simp [Ne.symm hc]
  · simp

lemma sqn (n : ℕ) (hn : 0 < n) : ((Real.sqrt n)⁻¹ : ℂ) * ((Real.sqrt n)⁻¹ : ℂ) = (n : ℂ)⁻¹ := by
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt (Nat.cast_nonneg n)]; push_cast; rfl

lemma overlap_C (n : ℕ) (hn : 0 < n) (chi : ResourceMatrix n) (W : QuditMatrix n) :
    entangledOverlap hn chi W = ((n : ℂ)⁻¹ * ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
      W p.2 p.1 * conj (W q.2 q.1) * chi q p).re := by
  unfold entangledOverlap effectProb
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply, psi_apply,
    map_mul, Complex.conj_ofReal, ← Complex.ofReal_inv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have := sqn n hn
  rw [← Complex.ofReal_inv] at this
  linear_combination (W p.2 p.1 * conj (W q.2 q.1) * chi q p) * this

lemma tele_entry {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n) (T : BellLabel n → QuditMatrix n)
    (rho : QuditMatrix n) (i j : Fin n) :
    teleportation hn chi T rho i j = ∑ m, ∑ l, ∑ k,
      conj (T m k i) * unnormalizedBellBranch hn chi m rho k l * T m l j := by
  unfold teleportation
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    Complex.star_def]

lemma TPhi {n : ℕ} (hn : 0 < n) (T : BellLabel n → QuditMatrix n) (m : BellLabel n) (l z2 : Fin n) :
    ∑ x, T m l x * generalizedBellVector n hn m (x, z2) =
      ((Real.sqrt n)⁻¹ : ℂ) * (T m * (bellWeyl m)ᴴ) l z2 := by
  simp only [bv_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

lemma TPhic {n : ℕ} (hn : 0 < n) (T : BellLabel n → QuditMatrix n) (m : BellLabel n) (k y2 : Fin n) :
    ∑ x, conj (T m k x) * conj (generalizedBellVector n hn m (x, y2)) =
      ((Real.sqrt n)⁻¹ : ℂ) * conj ((T m * (bellWeyl m)ᴴ) k y2) := by
  have h := congrArg conj (TPhi hn T m k y2)
  simp only [map_sum, map_mul, Complex.conj_ofReal, ← Complex.ofReal_inv] at h ⊢
  rw [h]

def Mx (n : ℕ) (b a : Fin n) : QuditMatrix n :=
  Matrix.of fun i i' => (if b = i then ((Real.sqrt n)⁻¹ : ℂ) else 0) *
    conj (if a = i' then ((Real.sqrt n)⁻¹ : ℂ) else 0)

lemma ent_gen (n : ℕ) (hn : 0 < n) (E : Superop (Fin n) (Fin n)) :
    QuditFidelity.entanglementFidelity n hn E = (∑ x, ∑ x2, ((Real.sqrt n)⁻¹ : ℂ) *
      ((Real.sqrt n)⁻¹ : ℂ) * E (Mx n x2 x) x2 x).re := by
  unfold QuditFidelity.entanglementFidelity effectProb
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
    idTensorSuperop, finiteMaxEntangled, Fintype.card_fin, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · refine Finset.sum_congr rfl fun x2 _ => ?_
    rw [Finset.sum_eq_single x2]
    · simp only [if_true, Complex.conj_ofReal, ← Complex.ofReal_inv, Mx]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma branch_M {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n) (m : BellLabel n) (b a k l : Fin n) :
    unnormalizedBellBranch hn chi m (Mx n b a) k l = ((Real.sqrt n)⁻¹ : ℂ) * ((Real.sqrt n)⁻¹ : ℂ) *
      ∑ y2, ∑ z2, conj (generalizedBellVector n hn m (b, y2)) *
        generalizedBellVector n hn m (a, z2) * chi (y2, k) (z2, l) := by
  rw [branch_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single b]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y2 _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z2 _ => ?_
      simp only [Mx, Matrix.of_apply, if_true, Complex.conj_ofReal, ← Complex.ofReal_inv]
      ring
    · intro c _ hc; refine Finset.sum_eq_zero fun z2 _ => ?_; simp [Mx, Ne.symm hc]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun y2 _ => Finset.sum_eq_zero fun z _ => ?_
    simp [Mx, Ne.symm hc]
  · simp

lemma pass5 {B C D E F G : Type*} [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype F]
    [Fintype G] (f : B → C → D → E → F → G → ℂ) :
    ∑ b, ∑ c, ∑ d, ∑ e, ∑ x, ∑ g, f b c d e x g = ∑ c, ∑ d, ∑ e, ∑ x, ∑ g, ∑ b, f b c d e x g := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]

lemma ent_core {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n) (T : BellLabel n → QuditMatrix n) :
    ∑ x, ∑ x2, ((Real.sqrt n)⁻¹ : ℂ) * ((Real.sqrt n)⁻¹ : ℂ) *
      teleportation hn chi T (Mx n x2 x) x2 x =
    ∑ m, ∑ l, ∑ k, ∑ y2, ∑ z2, ((Real.sqrt n)⁻¹ : ℂ) ^ 4 *
      ((∑ x2, conj (T m k x2) * conj (generalizedBellVector n hn m (x2, y2))) *
        (∑ x, T m l x * generalizedBellVector n hn m (x, z2)) * chi (y2, k) (z2, l)) := by
  simp only [tele_entry, branch_M, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, a]; rw [pass5]
  rw [pass5]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl
    fun k _ => Finset.sum_congr rfl fun y2 _ => Finset.sum_congr rfl fun z2 _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma perm4 {α : Type*} [Fintype α] (f : α → α → α → α → ℂ) :
    ∑ l, ∑ k, ∑ y, ∑ z, f l k y z = ∑ z, ∑ l, ∑ y, ∑ k, f l k y z := by
  calc ∑ l, ∑ k, ∑ y, ∑ z, f l k y z = ∑ l, ∑ k, ∑ z, ∑ y, f l k y z :=
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ l, ∑ z, ∑ k, ∑ y, f l k y z := Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ z, ∑ l, ∑ k, ∑ y, f l k y z := Finset.sum_comm
    _ = ∑ z, ∑ l, ∑ y, ∑ k, f l k y z :=
        Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm

lemma ent_tele {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n) (T : BellLabel n → QuditMatrix n) :
    QuditFidelity.entanglementFidelity n hn (teleportation hn chi T) =
      ((n : ℝ) ^ 2)⁻¹ * ∑ m, entangledOverlap hn chi (T m * (bellWeyl m)ᴴ) := by
  rw [ent_gen, ent_core]
  simp_rw [TPhi, TPhic, overlap_C]
  rw [← Complex.re_sum, ← Complex.re_ofReal_mul]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Fintype.sum_prod_type]
  rw [perm4 (fun l k y2 z2 => ((Real.sqrt n)⁻¹ : ℂ) ^ 4 *
    (((Real.sqrt n)⁻¹ : ℂ) * conj ((T m * (bellWeyl m)ᴴ) k y2) *
      (((Real.sqrt n)⁻¹ : ℂ) * (T m * (bellWeyl m)ᴴ) l z2) * chi (y2, k) (z2, l)))]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z2 _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun y2 _ => Finset.sum_congr rfl fun k _ => ?_
  have h := sqn n hn
  have e6 : ((Real.sqrt n)⁻¹ : ℂ) ^ 4 * ((Real.sqrt n)⁻¹ : ℂ) * ((Real.sqrt n)⁻¹ : ℂ) =
      ((n : ℂ) ^ 2)⁻¹ * (n : ℂ)⁻¹ := by
    have : ((Real.sqrt n)⁻¹ : ℂ) ^ 4 * ((Real.sqrt n)⁻¹ : ℂ) * ((Real.sqrt n)⁻¹ : ℂ) =
        (((Real.sqrt n)⁻¹ : ℂ) * ((Real.sqrt n)⁻¹ : ℂ)) ^ 3 := by ring
    rw [this, h]; field_simp
  linear_combination (conj ((T m * (bellWeyl m)ᴴ) k y2) * (T m * (bellWeyl m)ᴴ) l z2 *
    chi (y2, k) (z2, l)) * e6

end G65P

namespace G65P
lemma tele_channel {n : ℕ} (hn : 0 < n) (chi : ResourceMatrix n)
    (hchi : IsDensityMatrix chi) (T : BellLabel n → QuditMatrix n)
    (hT : IsCorrectionFamily T) : IsChannel (teleportation hn chi T) := by
  obtain ⟨B, hB⟩ : ∃ B : ResourceMatrix n, chi = Bᴴ * B := by
    open scoped MatrixOrder in
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hchi.1.nonneg
    exact ⟨B, hB⟩
  have htr : (Bᴴ * B).trace = 1 := hB ▸ hchi.2
  subst hB
  let ι := BellLabel n × (Fin n × Fin n)
  let e := Fintype.equivFin ι
  let E : Fin (Fintype.card ι) → QuditMatrix n := fun i =>
    (T (e.symm i).1)ᴴ * K hn B (e.symm i).1 (e.symm i).2
  have hTT : ∀ m, T m * (T m)ᴴ = 1 := fun m => Matrix.mem_unitaryGroup_iff.mp (hT m)
  refine ⟨Fintype.card ι, E, ?_, fun rho => ?_⟩
  · unfold IsKrausFamily
    rw [show (∑ j, (E j)ᴴ * E j) = ∑ x : ι, ((T x.1)ᴴ * K hn B x.1 x.2)ᴴ * ((T x.1)ᴴ * K hn B x.1 x.2)
      from e.symm.sum_comp (fun x : ι => ((T x.1)ᴴ * K hn B x.1 x.2)ᴴ * ((T x.1)ᴴ * K hn B x.1 x.2))]
    rw [Fintype.sum_prod_type]
    have : ∀ m r, ((T m)ᴴ * K hn B m r)ᴴ * ((T m)ᴴ * K hn B m r) = (K hn B m r)ᴴ * K hn B m r := by
      intro m r
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc (T m), hTT, Matrix.one_mul]
    simp_rw [this]
    exact kraus_sum hn B htr
  · unfold krausApply
    rw [show (∑ j, E j * rho * (E j)ᴴ) = ∑ x : ι, ((T x.1)ᴴ * K hn B x.1 x.2) * rho *
        ((T x.1)ᴴ * K hn B x.1 x.2)ᴴ
      from e.symm.sum_comp (fun x : ι => ((T x.1)ᴴ * K hn B x.1 x.2) * rho *
        ((T x.1)ᴴ * K hn B x.1 x.2)ᴴ)]
    rw [Fintype.sum_prod_type]
    unfold teleportation
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [branch_kraus, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
end G65P

open G65P in
theorem solution (n : ℕ) (hn : 0 < n) (chi : ResourceMatrix n)
    (hchi : IsDensityMatrix chi) (T : BellLabel n → QuditMatrix n)
    (hT : IsCorrectionFamily T) :
    QuditFidelity.averageFidelity n hn (teleportation hn chi T) =
      (1 / ((n : ℝ) * ((n : ℝ) + 1))) *
        (∑ m : BellLabel n, entangledOverlap hn chi (T m * (bellWeyl m)ᴴ)) +
          1 / ((n : ℝ) + 1) := by
  rw [QAlgorithms.Papers.RoadmapX07.averageFidelity_eq_entanglementFidelity n hn _
    (tele_channel hn chi hchi T hT), ent_tele]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
