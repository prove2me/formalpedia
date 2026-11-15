-- Prove2me | solution 1 for RatFunc.artinSchreier_lowerRamificationGroup_infty_eq_and_swan_eq_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T09:33:50.198825+00:00
-- url     : https://prove2.me/submissions/5dacd935-2763-495a-a380-c0f73ca38f7f

import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace SwanLpsiAux

theorem val_sum_eq_max {L : Type} [Field L] (V : Valuation L (WithZero (Multiplicative ℤ))) {ι : Type} [DecidableEq ι]
    (s : Finset ι) (t : ι → L) (hne : ∃ j ∈ s, t j ≠ 0)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, t i ≠ 0 → t j ≠ 0 → V (t i) = V (t j) → i = j) :
    ∃ j ∈ s, t j ≠ 0 ∧ V (∑ i ∈ s, t i) = V (t j) ∧ ∀ i ∈ s, i ≠ j → V (t i) < V (t j) := by
  have hs : s.Nonempty := by obtain ⟨j, hj, -⟩ := hne; exact ⟨j, hj⟩
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => V (t i)) hs
  have htj : t j ≠ 0 := by
    obtain ⟨k, hk, htk⟩ := hne
    intro h0
    have h1 := hmax k hk
    rw [h0, map_zero] at h1
    exact htk ((Valuation.zero_iff V).1 (le_antisymm h1 zero_le))
  have hlt : ∀ i ∈ s, i ≠ j → V (t i) < V (t j) := by
    intro i hi hij
    rcases eq_or_ne (t i) 0 with h0 | h0
    · rw [h0, map_zero]; exact (Valuation.pos_iff V).2 htj
    · exact lt_of_le_of_ne (hmax i hi) (fun h => hij (hinj i hi j hj h0 htj h))
  refine ⟨j, hj, htj, ?_, hlt⟩
  exact Valuation.map_sum_eq_of_lt V hj (fun i hi => by
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    exact hlt i hi.1 hi.2)

theorem valK_eq {Fq : Type} [Field Fq] [DecidableEq (RatFunc Fq)] {L : Type} [Field L]
    [Algebra (RatFunc Fq) L] (V : Valuation L (WithZero (Multiplicative ℤ)))
    (hO : ∀ a : RatFunc Fq, RatFunc.inftyValuation Fq a ≤ 1 → V (algebraMap (RatFunc Fq) L a) ≤ 1)
    {a : RatFunc Fq} (ha : a ≠ 0) :
    V (algebraMap (RatFunc Fq) L a) =
      WithZero.exp (WithZero.log (V (algebraMap (RatFunc Fq) L RatFunc.X)) * a.intDegree) := by
  have hX0 : (RatFunc.X : RatFunc Fq) ≠ 0 := RatFunc.X_ne_zero
  set k := a.intDegree with hk
  set u : RatFunc Fq := a * RatFunc.X ^ (-k) with hu
  have hvu : RatFunc.inftyValuation Fq u = 1 := by
    rw [hu, map_mul, map_zpow₀, RatFunc.inftyValuation_apply, RatFunc.inftyValuation_apply,
      RatFunc.inftyValuation_of_nonzero _ ha, RatFunc.inftyValuation_of_nonzero _ hX0, RatFunc.intDegree_X,
      ← WithZero.exp_zsmul, ← WithZero.exp_add, ← hk]
    simp
  have hVu : V (algebraMap (RatFunc Fq) L u) = 1 := by
    apply le_antisymm (hO u hvu.le)
    have h2 := hO u⁻¹ (by rw [map_inv₀, hvu, inv_one])
    have hu0 : algebraMap (RatFunc Fq) L u ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (algebraMap (RatFunc Fq) L).injective, hu]
      exact mul_ne_zero ha (zpow_ne_zero _ hX0)
    rw [map_inv₀, map_inv₀] at h2
    exact (inv_le_one₀ ((Valuation.pos_iff V).2 hu0)).1 h2
  have ha' : a = u * RatFunc.X ^ k := by
    rw [hu, mul_assoc, ← zpow_add₀ hX0, neg_add_cancel, zpow_zero, mul_one]
  have hXV : V (algebraMap (RatFunc Fq) L RatFunc.X) ≠ 0 := by
    rw [Valuation.ne_zero_iff, ne_eq, map_eq_zero_iff _ (algebraMap (RatFunc Fq) L).injective]; exact hX0
  rw [ha', map_mul, map_zpow₀, map_mul, map_zpow₀, hVu, one_mul]
  conv_lhs => rw [← WithZero.exp_log hXV]
  rw [← WithZero.exp_zsmul, smul_eq_mul, mul_comm]

theorem exists_algebraMap_eq_of_pow_card (Fq : Type) [Field Fq] [Fintype Fq] {F : Type} [Field F]
    [Algebra Fq F] {z : F} (hz : z ^ Fintype.card Fq = z) : ∃ c : Fq, algebraMap Fq F c = z := by
  classical
  by_contra h
  push_neg at h
  set P : F[X] := X ^ Fintype.card Fq - X with hPdef
  have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F Fintype.one_lt_card
  have hroot : ∀ w : F, w ^ Fintype.card Fq = w → w ∈ P.roots.toFinset := by
    intro w hw
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, hPdef]
    simp [hw]
  have hsub : insert z (Finset.univ.image (algebraMap Fq F)) ⊆ P.roots.toFinset := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | ⟨c, -, rfl⟩
    · exact hroot _ hz
    · exact hroot _ (by rw [← map_pow, FiniteField.pow_card])
  have hz' : z ∉ Finset.univ.image (algebraMap Fq F) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact h
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hz', Finset.card_image_of_injective _ (algebraMap Fq F).injective,
    Finset.card_univ] at hcard
  have h2 := (Multiset.toFinset_card_le P.roots).trans (card_roots' P)
  have hdeg : P.natDegree = Fintype.card Fq :=
    FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card
  omega

/-- `V((y+c)^i - y^i) V(y) ≤ V(y)^i` when `V c ≤ 1 < V y`. -/
theorem val_shift_le {L : Type} [Field L] (V : Valuation L (WithZero (Multiplicative ℤ))) {y c : L} (hy : 1 < V y)
    (hc : V c ≤ 1) (i : ℕ) : V ((y + c) ^ i - y ^ i) * V y ≤ V y ^ i := by
  have hyc : V (y + c) = V y := by
    rw [add_comm]; exact Valuation.map_add_eq_of_lt_right V (lt_of_le_of_lt hc hy)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [← geom_sum₂_mul, add_sub_cancel_left, map_mul, pow_succ]
  have hS : V (∑ k ∈ Finset.range (j + 1), (y + c) ^ k * y ^ (j + 1 - 1 - k)) ≤ V y ^ j := by
    apply Valuation.map_sum_le
    intro k hk
    rw [Finset.mem_range] at hk
    rw [map_mul, map_pow, map_pow, hyc, ← pow_add]
    apply le_of_eq; congr 1; omega
  calc V (∑ k ∈ Finset.range (j + 1), (y + c) ^ k * y ^ (j + 1 - 1 - k)) * V c * V y
      ≤ V y ^ j * 1 * V y := by gcongr
    _ = V y ^ j * V y := by rw [mul_one]

/-- Exactness: `V((y+c)^i - y^i) V(y) = V(y)^i` when `V c = 1 < V y` and `V (i : L) = 1`. -/
theorem val_shift_eq {L : Type} [Field L] (V : Valuation L (WithZero (Multiplicative ℤ))) {y c : L} (hy : 1 < V y)
    (hc : V c = 1) {i : ℕ} (hi : V (i : L) = 1) : V ((y + c) ^ i - y ^ i) * V y = V y ^ i := by
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hy0 : V y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
  rw [← geom_sum₂_mul, add_sub_cancel_left, map_mul, hc, mul_one, pow_succ]
  congr 1
  have hsplit : (∑ k ∈ Finset.range (j + 1), (y + c) ^ k * y ^ (j + 1 - 1 - k)) =
      ((j + 1 : ℕ) : L) * y ^ j + ∑ k ∈ Finset.range (j + 1), ((y + c) ^ k - y ^ k) * y ^ (j - k) := by
    have h1 : ∀ k ∈ Finset.range (j + 1), (y + c) ^ k * y ^ (j + 1 - 1 - k) =
        y ^ j + ((y + c) ^ k - y ^ k) * y ^ (j - k) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have : y ^ j = y ^ k * y ^ (j - k) := by rw [← pow_add]; congr 1; omega
      rw [this, show j + 1 - 1 - k = j - k by omega]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsplit]
  have hfirst : V (((j + 1 : ℕ) : L) * y ^ j) = V y ^ j := by rw [map_mul, hi, one_mul, map_pow]
  rw [Valuation.map_add_eq_of_lt_left V, hfirst]
  rw [hfirst]
  apply lt_of_le_of_lt (Valuation.map_sum_le V (g := V y ^ j / V y) _)
  · rw [div_lt_iff₀ ((Valuation.pos_iff V).2 ?_)]
    · calc V y ^ j = V y ^ j * 1 := (mul_one _).symm
        _ < V y ^ j * V y := by
          apply mul_lt_mul_of_pos_left hy (pow_pos (lt_trans zero_lt_one hy) j)
    · intro h0; rw [h0, map_zero] at hy; exact (not_lt.2 zero_le hy)
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [map_mul, map_pow, le_div_iff₀ (lt_of_le_of_ne zero_le hy0.symm)]
    have h2 := val_shift_le V hy hc.le k
    calc V ((y + c) ^ k - y ^ k) * V y ^ (j - k) * V y
        = V ((y + c) ^ k - y ^ k) * V y * V y ^ (j - k) := mul_right_comm _ _ _
      _ ≤ V y ^ k * V y ^ (j - k) := by gcongr
      _ = V y ^ j := by rw [← pow_add]; congr 1; omega



theorem exp_mul_pow (m n : ℤ) (k : ℕ) :
    WithZero.exp m * WithZero.exp n ^ k = (WithZero.exp (m + k * n) : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_nsmul, ← WithZero.exp_add, nsmul_eq_mul]

theorem exp_inj {m n : ℤ} (h : (WithZero.exp m : WithZero (Multiplicative ℤ)) = WithZero.exp n) :
    m = n := by
  have := congrArg WithZero.log h
  rwa [WithZero.log_exp, WithZero.log_exp] at this

theorem le_of_mul_exp_le {z : WithZero (Multiplicative ℤ)} {m n : ℤ}
    (h : z * WithZero.exp n ≤ WithZero.exp m) : z ≤ WithZero.exp (m - n) := by
  have h2 : z * WithZero.exp n * WithZero.exp (-n) ≤ WithZero.exp m * WithZero.exp (-n) := by gcongr
  rwa [mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, mul_one, ← WithZero.exp_add,
    ← sub_eq_add_neg] at h2

theorem lt_of_mul_exp_lt {z : WithZero (Multiplicative ℤ)} {m n : ℤ}
    (h : z * WithZero.exp n < WithZero.exp m) : z < WithZero.exp (m - n) := by
  by_contra h'
  have h2 : WithZero.exp (m - n) * WithZero.exp n ≤ z * WithZero.exp n := by gcongr; exact not_lt.1 h'
  rw [← WithZero.exp_add, sub_add_cancel] at h2
  exact absurd h (not_lt.2 h2)

theorem eq_of_mul_exp_eq {z : WithZero (Multiplicative ℤ)} {m n : ℤ}
    (h : z * WithZero.exp n = WithZero.exp m) : z = WithZero.exp (m - n) := by
  have h2 := congrArg (· * WithZero.exp (-n)) h
  rwa [mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, mul_one, ← WithZero.exp_add,
    ← sub_eq_add_neg] at h2

theorem distinct_aux {q N : ℕ} (hcop : Nat.Coprime N q) {i j : ℕ} (hi : i < q) (hj : j < q) {k l : ℤ}
    (h : (q : ℤ) * k + i * N = q * l + j * N) : i = j := by
  have hdvd : (q : ℤ) ∣ ((j : ℤ) - i) * N := ⟨k - l, by linear_combination -h⟩
  have hc : IsCoprime (q : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
  have h2 := hc.dvd_of_dvd_mul_right hdvd
  have h3 := Int.eq_zero_of_abs_lt_dvd h2 (by rw [abs_lt]; constructor <;> omega)
  omega

theorem ne_zero_aux {q N : ℕ} (hcop : Nat.Coprime N q) {i : ℕ} (hi0 : 0 < i) (hi : i < q) (k : ℤ) :
    (q : ℤ) * k + i * N ≠ 0 := by
  intro h
  have := distinct_aux hcop hi (show 0 < q by omega) (k := k) (l := 0) (by rw [h]; simp)
  omega

section PB

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] {L : Type} [Field L]
  [Algebra (RatFunc Fq) L]

theorem sub_eq_sum (pb : PowerBasis (RatFunc Fq) L) (σ : L →ₐ[RatFunc Fq] L) {c : L}
    (hσ : σ pb.gen = pb.gen + c) (x : L) :
    σ x - x = ∑ i : Fin pb.dim, pb.basis.repr x i • ((pb.gen + c) ^ (i : ℕ) - pb.gen ^ (i : ℕ)) := by
  conv_lhs => rw [← pb.basis.sum_repr x]
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [map_smul, PowerBasis.coe_basis, map_pow, hσ, smul_sub]

theorem val_term (V : Valuation L (WithZero (Multiplicative ℤ)))
    (hVK : ∀ a : RatFunc Fq, a ≠ 0 →
      V (algebraMap (RatFunc Fq) L a) = WithZero.exp ((Fintype.card Fq : ℤ) * a.intDegree))
    {y : L} {N : ℕ} (hVy : V y = WithZero.exp (N : ℤ)) {a : RatFunc Fq} (ha : a ≠ 0) (i : ℕ) :
    V (a • y ^ i) = WithZero.exp ((Fintype.card Fq : ℤ) * a.intDegree + i * N) := by
  rw [Algebra.smul_def, map_mul, map_pow, hVK a ha, hVy, exp_mul_pow]

theorem repr_max (V : Valuation L (WithZero (Multiplicative ℤ)))
    (pb : PowerBasis (RatFunc Fq) L) (hdim : pb.dim = Fintype.card Fq) {N : ℕ}
    (hcop : Nat.Coprime N (Fintype.card Fq))
    (hVK : ∀ a : RatFunc Fq, a ≠ 0 →
      V (algebraMap (RatFunc Fq) L a) = WithZero.exp ((Fintype.card Fq : ℤ) * a.intDegree))
    (hVy : V pb.gen = WithZero.exp (N : ℤ)) {x : L} (hx0 : x ≠ 0) :
    ∃ j0 : Fin pb.dim, pb.basis.repr x j0 ≠ 0 ∧
      V x = V (pb.basis.repr x j0 • pb.gen ^ (j0 : ℕ)) ∧
      ∀ i, i ≠ j0 → V (pb.basis.repr x i • pb.gen ^ (i : ℕ)) <
        V (pb.basis.repr x j0 • pb.gen ^ (j0 : ℕ)) := by
  classical
  have hxt : x = ∑ i, pb.basis.repr x i • pb.gen ^ (i : ℕ) := by
    conv_lhs => rw [← pb.basis.sum_repr x]
    simp only [PowerBasis.coe_basis]
  have hne : ∃ j ∈ Finset.univ, pb.basis.repr x j • pb.gen ^ (j : ℕ) ≠ 0 := by
    by_contra h
    simp only [Finset.mem_univ, true_and, not_exists, not_not] at h
    exact hx0 (by rw [hxt]; exact Finset.sum_eq_zero (fun i _ => h i))
  have hinj : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, pb.basis.repr x i • pb.gen ^ (i : ℕ) ≠ 0 →
      pb.basis.repr x j • pb.gen ^ (j : ℕ) ≠ 0 →
      V (pb.basis.repr x i • pb.gen ^ (i : ℕ)) = V (pb.basis.repr x j • pb.gen ^ (j : ℕ)) → i = j := by
    intro i _ j _ hi hj hij
    have hai : pb.basis.repr x i ≠ 0 := fun h => hi (by rw [h, zero_smul])
    have haj : pb.basis.repr x j ≠ 0 := fun h => hj (by rw [h, zero_smul])
    rw [val_term V hVK hVy hai, val_term V hVK hVy haj] at hij
    exact Fin.ext (distinct_aux hcop (lt_of_lt_of_eq i.2 hdim) (lt_of_lt_of_eq j.2 hdim) (exp_inj hij))
  obtain ⟨j0, -, hj0ne, hj0, hmax⟩ := val_sum_eq_max V Finset.univ _ hne hinj
  refine ⟨j0, fun h => hj0ne (by rw [h, zero_smul]), by rw [← hxt] at hj0; exact hj0,
    fun i hi => hmax i (Finset.mem_univ _) hi⟩

theorem claimA (V : Valuation L (WithZero (Multiplicative ℤ)))
    (pb : PowerBasis (RatFunc Fq) L) (hdim : pb.dim = Fintype.card Fq) {N : ℕ}
    (hcop : Nat.Coprime N (Fintype.card Fq))
    (hVK : ∀ a : RatFunc Fq, a ≠ 0 →
      V (algebraMap (RatFunc Fq) L a) = WithZero.exp ((Fintype.card Fq : ℤ) * a.intDegree))
    (hVy : V pb.gen = WithZero.exp (N : ℤ)) (hN : 1 ≤ N)
    (σ : L →ₐ[RatFunc Fq] L) {c : L} (hσ : σ pb.gen = pb.gen + c) (hc : V c ≤ 1)
    {x : L} (hx : V x ≤ 1) : V (σ x - x) ≤ WithZero.exp (-((N : ℤ) + 1)) := by
  classical
  have hy1 : 1 < V pb.gen := by rw [hVy, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  obtain ⟨j0, -, hj0, hmax⟩ := repr_max V pb hdim hcop hVK hVy hx0
  have hle : ∀ i, V (pb.basis.repr x i • pb.gen ^ (i : ℕ)) ≤ V x := by
    intro i
    rw [hj0]
    rcases eq_or_ne i j0 with rfl | h
    · exact le_rfl
    · exact (hmax i h).le
  rw [sub_eq_sum pb σ hσ x]
  apply Valuation.map_sum_le
  intro i _
  rcases eq_or_ne (pb.basis.repr x i) 0 with ha | ha
  · rw [ha, zero_smul, map_zero]; exact zero_le
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hi0
  · rw [hi0, pow_zero, pow_zero, sub_self, smul_zero, map_zero]; exact zero_le
  have hti := val_term V hVK hVy ha (i : ℕ)
  have hneg : (Fintype.card Fq : ℤ) * (pb.basis.repr x i).intDegree + (i : ℕ) * N ≤ -1 := by
    have h1 := (hle i).trans hx
    rw [hti, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    have h2 := ne_zero_aux hcop hi0 (lt_of_lt_of_eq i.2 hdim) (pb.basis.repr x i).intDegree
    omega
  have hD : V (pb.basis.repr x i • ((pb.gen + c) ^ (i : ℕ) - pb.gen ^ (i : ℕ))) *
      WithZero.exp (N : ℤ) ≤ WithZero.exp (-1) := by
    rw [Algebra.smul_def, map_mul, mul_assoc, ← hVy]
    calc V (algebraMap (RatFunc Fq) L (pb.basis.repr x i)) *
          (V ((pb.gen + c) ^ (i : ℕ) - pb.gen ^ (i : ℕ)) * V pb.gen)
        ≤ V (algebraMap (RatFunc Fq) L (pb.basis.repr x i)) * V pb.gen ^ (i : ℕ) := by
          gcongr; exact val_shift_le V hy1 hc _
      _ = V (pb.basis.repr x i • pb.gen ^ (i : ℕ)) := by rw [Algebra.smul_def, map_mul, map_pow]
      _ ≤ WithZero.exp (-1) := by rw [hti, WithZero.exp_le_exp]; exact hneg
  calc _ ≤ WithZero.exp (-1 - (N : ℤ)) := le_of_mul_exp_le hD
    _ = WithZero.exp (-((N : ℤ) + 1)) := by congr 1; ring

theorem claimB (V : Valuation L (WithZero (Multiplicative ℤ)))
    (pb : PowerBasis (RatFunc Fq) L) (hdim : pb.dim = Fintype.card Fq) {N : ℕ}
    (hcop : Nat.Coprime N (Fintype.card Fq))
    (hVK : ∀ a : RatFunc Fq, a ≠ 0 →
      V (algebraMap (RatFunc Fq) L a) = WithZero.exp ((Fintype.card Fq : ℤ) * a.intDegree))
    (hVy : V pb.gen = WithZero.exp (N : ℤ)) (hN : 1 ≤ N)
    (σ : L →ₐ[RatFunc Fq] L) {c0 : Fq} (hc0 : c0 ≠ 0)
    (hσ : σ pb.gen = pb.gen + algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) c0))
    {x : L} (hx : V x = WithZero.exp (-1)) : V (σ x - x) = WithZero.exp (-((N : ℤ) + 1)) := by
  classical
  have hconst : ∀ d : Fq, d ≠ 0 → V (algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) d)) = 1 := by
    intro d hd
    rw [hVK _ ((_root_.map_ne_zero _).2 hd),
      show (algebraMap Fq (RatFunc Fq) d).intDegree = 0 from RatFunc.intDegree_C d, mul_zero,
      WithZero.exp_zero]
  have hy1 : 1 < V pb.gen := by rw [hVy, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero] at hx; exact WithZero.exp_ne_zero hx.symm
  obtain ⟨j0, ha0, hj0, hmax⟩ := repr_max V pb hdim hcop hVK hVy hx0
  have hval : (Fintype.card Fq : ℤ) * (pb.basis.repr x j0).intDegree + (j0 : ℕ) * N = -1 := by
    rw [hx, val_term V hVK hVy ha0] at hj0; exact (exp_inj hj0).symm
  have hj0F : ((j0 : ℕ) : Fq) ≠ 0 := by
    intro h
    have h1 : ringChar Fq ∣ (j0 : ℕ) := (CharP.cast_eq_zero_iff Fq (ringChar Fq) _).1 h
    have h2 : ringChar Fq ∣ Fintype.card Fq :=
      (CharP.cast_eq_zero_iff Fq (ringChar Fq) _).1 (FiniteField.cast_card_eq_zero Fq)
    have h3 : (ringChar Fq : ℤ) ∣ (Fintype.card Fq : ℤ) * (pb.basis.repr x j0).intDegree + (j0 : ℕ) * N :=
      dvd_add (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 h2) _)
        (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.2 h1) _)
    rw [hval, dvd_neg] at h3
    have h4 : ringChar Fq ∣ 1 := by exact_mod_cast h3
    exact CharP.ringChar_ne_one (Nat.dvd_one.1 h4)
  have hj0L : V (((j0 : ℕ) : L)) = 1 := by
    have : (((j0 : ℕ) : L)) =
        algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) ((j0 : ℕ) : Fq)) := by simp
    rw [this]; exact hconst _ hj0F
  have hc1 := hconst c0 hc0
  rw [sub_eq_sum pb σ hσ x]
  have hterm : ∀ i : Fin pb.dim, V (pb.basis.repr x i • ((pb.gen + algebraMap (RatFunc Fq) L
      (algebraMap Fq (RatFunc Fq) c0)) ^ (i : ℕ) - pb.gen ^ (i : ℕ))) * V pb.gen ≤
      V (pb.basis.repr x i • pb.gen ^ (i : ℕ)) := by
    intro i
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, mul_assoc, map_pow]
    gcongr
    exact val_shift_le V hy1 hc1.le _
  have hDj0 : V (pb.basis.repr x j0 • ((pb.gen + algebraMap (RatFunc Fq) L
      (algebraMap Fq (RatFunc Fq) c0)) ^ (j0 : ℕ) - pb.gen ^ (j0 : ℕ))) =
      WithZero.exp (-((N : ℤ) + 1)) := by
    have h1 : V (pb.basis.repr x j0 • ((pb.gen + algebraMap (RatFunc Fq) L
        (algebraMap Fq (RatFunc Fq) c0)) ^ (j0 : ℕ) - pb.gen ^ (j0 : ℕ))) * WithZero.exp (N : ℤ) =
        WithZero.exp (-1) := by
      rw [← hVy, ← hx, hj0, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, mul_assoc, map_pow,
        val_shift_eq V hy1 hc1 hj0L]
    rw [eq_of_mul_exp_eq h1]; congr 1; ring
  rw [Valuation.map_sum_eq_of_lt V (Finset.mem_univ j0), hDj0]
  intro i hi
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
  rw [hDj0]
  have h1 : V (pb.basis.repr x i • ((pb.gen + algebraMap (RatFunc Fq) L
      (algebraMap Fq (RatFunc Fq) c0)) ^ (i : ℕ) - pb.gen ^ (i : ℕ))) * WithZero.exp (N : ℤ) <
      WithZero.exp (-1) := by
    rw [← hVy, ← hx, hj0]; exact lt_of_le_of_lt (hterm i) (hmax i hi.2)
  calc _ < WithZero.exp (-1 - (N : ℤ)) := lt_of_mul_exp_lt h1
    _ = WithZero.exp (-((N : ℤ) + 1)) := by congr 1; ring

end PB


section VF

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)] {L : Type} [Field L]
  [Algebra (RatFunc Fq) L]

theorem val_term' (V : Valuation L (WithZero (Multiplicative ℤ))) (m : ℤ)
    (hVK : ∀ a : RatFunc Fq, a ≠ 0 →
      V (algebraMap (RatFunc Fq) L a) = WithZero.exp (m * ((Fintype.card Fq : ℤ) * a.intDegree)))
    {y : L} {N : ℕ} (hVy : V y = WithZero.exp (m * N)) {a : RatFunc Fq} (ha : a ≠ 0) (i : ℕ) :
    V (a • y ^ i) = WithZero.exp (m * ((Fintype.card Fq : ℤ) * a.intDegree + i * N)) := by
  rw [Algebra.smul_def, map_mul, map_pow, hVK a ha, hVy, exp_mul_pow]
  congr 1; ring

theorem repr_max' (V : Valuation L (WithZero (Multiplicative ℤ)))
    (pb : PowerBasis (RatFunc Fq) L) (hdim : pb.dim ≤ Fintype.card Fq) {N : ℕ}
    (hcop : Nat.Coprime N (Fintype.card Fq)) (m : ℤ) (hm : m ≠ 0)
    (hVK : ∀ a : RatFunc Fq, a ≠ 0 →
      V (algebraMap (RatFunc Fq) L a) = WithZero.exp (m * ((Fintype.card Fq : ℤ) * a.intDegree)))
    (hVy : V pb.gen = WithZero.exp (m * N)) {x : L} (hx0 : x ≠ 0) :
    ∃ j0 : Fin pb.dim, pb.basis.repr x j0 ≠ 0 ∧
      V x = WithZero.exp (m * ((Fintype.card Fq : ℤ) * (pb.basis.repr x j0).intDegree + (j0 : ℕ) * N)) := by
  classical
  have hxt : x = ∑ i, pb.basis.repr x i • pb.gen ^ (i : ℕ) := by
    conv_lhs => rw [← pb.basis.sum_repr x]
    simp only [PowerBasis.coe_basis]
  have hne : ∃ j ∈ Finset.univ, pb.basis.repr x j • pb.gen ^ (j : ℕ) ≠ 0 := by
    by_contra h
    simp only [Finset.mem_univ, true_and, not_exists, not_not] at h
    exact hx0 (by rw [hxt]; exact Finset.sum_eq_zero (fun i _ => h i))
  have hinj : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, pb.basis.repr x i • pb.gen ^ (i : ℕ) ≠ 0 →
      pb.basis.repr x j • pb.gen ^ (j : ℕ) ≠ 0 →
      V (pb.basis.repr x i • pb.gen ^ (i : ℕ)) = V (pb.basis.repr x j • pb.gen ^ (j : ℕ)) → i = j := by
    intro i _ j _ hi hj hij
    have hai : pb.basis.repr x i ≠ 0 := fun h => hi (by rw [h, zero_smul])
    have haj : pb.basis.repr x j ≠ 0 := fun h => hj (by rw [h, zero_smul])
    rw [val_term' V m hVK hVy hai, val_term' V m hVK hVy haj] at hij
    exact Fin.ext (distinct_aux hcop (lt_of_lt_of_le i.2 hdim) (lt_of_lt_of_le j.2 hdim)
      (mul_left_cancel₀ hm (exp_inj hij)))
  obtain ⟨j0, -, hj0ne, hj0, -⟩ := val_sum_eq_max V Finset.univ _ hne hinj
  have ha0 : pb.basis.repr x j0 ≠ 0 := fun h => hj0ne (by rw [h, zero_smul])
  refine ⟨j0, ha0, ?_⟩
  rw [← hxt] at hj0
  rw [hj0, val_term' V m hVK hVy ha0]

theorem val_facts (V : Valuation L (WithZero (Multiplicative ℤ)))
    (pb : PowerBasis (RatFunc Fq) L) (hdim : pb.dim ≤ Fintype.card Fq) (f : Fq[X])
    (hN : 1 ≤ f.natDegree) (hcop : Nat.Coprime f.natDegree (Fintype.card Fq))
    (hy : pb.gen ^ Fintype.card Fq - pb.gen +
      algebraMap (RatFunc Fq) L (algebraMap Fq[X] (RatFunc Fq) f) = 0)
    (hO : ∀ a : RatFunc Fq, RatFunc.inftyValuation Fq a ≤ 1 → V (algebraMap (RatFunc Fq) L a) ≤ 1)
    (hz : ∃ a : RatFunc Fq, a ≠ 0 ∧ V (algebraMap (RatFunc Fq) L a) < 1)
    {ϖ : L} (hϖ : V ϖ = WithZero.exp (-1)) :
    (∀ a : RatFunc Fq, a ≠ 0 →
      V (algebraMap (RatFunc Fq) L a) = WithZero.exp ((Fintype.card Fq : ℤ) * a.intDegree)) ∧
    V pb.gen = WithZero.exp (f.natDegree : ℤ) ∧ pb.dim = Fintype.card Fq := by
  classical
  have hq1 : 1 < Fintype.card Fq := Fintype.one_lt_card
  have hq2 : (2 : ℤ) ≤ Fintype.card Fq := by exact_mod_cast hq1
  have hX0 : (RatFunc.X : RatFunc Fq) ≠ 0 := RatFunc.X_ne_zero
  have hXV : V (algebraMap (RatFunc Fq) L RatFunc.X) ≠ 0 := by
    rw [Valuation.ne_zero_iff, ne_eq, map_eq_zero_iff _ (algebraMap (RatFunc Fq) L).injective]; exact hX0
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = WithZero.log (V (algebraMap (RatFunc Fq) L RatFunc.X)) := ⟨_, rfl⟩
  have hVK0 : ∀ a : RatFunc Fq, a ≠ 0 →
      V (algebraMap (RatFunc Fq) L a) = WithZero.exp (e * a.intDegree) := by
    intro a ha; rw [he]; exact valK_eq V hO ha
  have he0 : 0 ≤ e := by
    have h1 : RatFunc.inftyValuation Fq (RatFunc.X⁻¹) ≤ 1 := by
      rw [map_inv₀, RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero _ hX0, RatFunc.intDegree_X,
        ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]
      norm_num
    have h2 := hO _ h1
    rw [map_inv₀, map_inv₀, ← WithZero.exp_log hXV, ← he, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h2
    linarith
  have he1 : e ≠ 0 := by
    obtain ⟨a, ha0, ha⟩ := hz
    intro h
    rw [hVK0 a ha0, h, zero_mul, WithZero.exp_zero] at ha
    exact lt_irrefl _ ha
  have hepos : 0 < e := lt_of_le_of_ne he0 (Ne.symm he1)
  have hf0 : f ≠ 0 := by rintro rfl; simp at hN
  have hfK : algebraMap Fq[X] (RatFunc Fq) f ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Fq[X] (RatFunc Fq))).2 hf0
  have hyeq : pb.gen ^ Fintype.card Fq - pb.gen =
      -algebraMap (RatFunc Fq) L (algebraMap Fq[X] (RatFunc Fq) f) := by
    linear_combination hy
  have hVyq : V (pb.gen ^ Fintype.card Fq - pb.gen) = WithZero.exp (e * f.natDegree) := by
    rw [hyeq, Valuation.map_neg, hVK0 _ hfK, RatFunc.intDegree_polynomial]
  have hfbig : 1 < WithZero.exp (e * f.natDegree) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    have : (1 : ℤ) ≤ f.natDegree := by exact_mod_cast hN
    nlinarith
  have hy1 : 1 < V pb.gen := by
    by_contra h
    push_neg at h
    have h3 : V (pb.gen ^ Fintype.card Fq - pb.gen) ≤ 1 := by
      apply le_trans (Valuation.map_sub V _ _)
      apply max_le
      · rw [map_pow]; exact pow_le_one₀ zero_le h
      · exact h
    rw [hVyq] at h3
    exact absurd hfbig (not_lt.2 h3)
  have hy0 : V pb.gen ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy1)
  obtain ⟨s, hs⟩ : ∃ s : ℤ, s = WithZero.log (V pb.gen) := ⟨_, rfl⟩
  have hVs : V pb.gen = WithZero.exp s := by rw [hs, WithZero.exp_log hy0]
  have hs0 : 0 < s := by
    have h1 := hy1
    rw [hVs, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    exact h1
  have hqs : (Fintype.card Fq : ℤ) * s = e * f.natDegree := by
    have h1 : V (pb.gen ^ Fintype.card Fq - pb.gen) = V pb.gen ^ Fintype.card Fq := by
      rw [Valuation.map_sub_eq_of_lt_left, map_pow]
      rw [map_pow, hVs, ← WithZero.exp_nsmul, WithZero.exp_lt_exp, nsmul_eq_mul]
      nlinarith
    rw [hVyq, hVs, ← WithZero.exp_nsmul, nsmul_eq_mul] at h1
    exact (exp_inj h1).symm
  have hqe : (Fintype.card Fq : ℤ) ∣ e := by
    have hc : IsCoprime (Fintype.card Fq : ℤ) (f.natDegree : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
    exact hc.dvd_of_dvd_mul_right ⟨s, hqs.symm⟩
  obtain ⟨m, hm⟩ := hqe
  have hq0 : (Fintype.card Fq : ℤ) ≠ 0 := by omega
  have hsm : s = m * f.natDegree := by
    apply mul_left_cancel₀ hq0
    rw [hqs, hm]; ring
  have hmpos : 0 < m := by
    by_contra h
    push_neg at h
    have : (Fintype.card Fq : ℤ) * m ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) h
    linarith
  have hVKm : ∀ a : RatFunc Fq, a ≠ 0 →
      V (algebraMap (RatFunc Fq) L a) = WithZero.exp (m * ((Fintype.card Fq : ℤ) * a.intDegree)) := by
    intro a ha; rw [hVK0 a ha, hm]; congr 1; ring
  have hVym : V pb.gen = WithZero.exp (m * f.natDegree) := by rw [hVs, hsm]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hm1 : m = 1 := by
    obtain ⟨j0, -, hj0⟩ := repr_max' V pb hdim hcop m hmpos.ne' hVKm hVym hϖ0
    rw [hϖ] at hj0
    obtain ⟨t, ht⟩ : ∃ t : ℤ, m * t = -1 := ⟨_, (exp_inj hj0).symm⟩
    exact Int.eq_one_of_mul_eq_one_right hmpos.le (b := -t) (by rw [mul_neg, ht, neg_neg])
  subst hm1
  refine ⟨fun a ha => by rw [hVKm a ha, one_mul], by rw [hVym, one_mul], le_antisymm hdim ?_⟩
  have hpow : ∀ j : Fin (Fintype.card Fq), ∃ i : Fin pb.dim, ∃ k : ℤ,
      -((j : ℕ) : ℤ) = (Fintype.card Fq : ℤ) * k + ((i : ℕ) : ℤ) * f.natDegree := by
    intro j
    obtain ⟨i, -, hi⟩ := repr_max' V pb hdim hcop 1 one_ne_zero hVKm hVym (pow_ne_zero (j : ℕ) hϖ0)
    refine ⟨i, (pb.basis.repr (ϖ ^ (j : ℕ)) i).intDegree, ?_⟩
    rw [map_pow, hϖ, ← WithZero.exp_nsmul] at hi
    have h1 := exp_inj hi
    rw [nsmul_eq_mul] at h1
    linear_combination h1
  choose g k hgk using hpow
  have hginj : Function.Injective g := by
    intro j1 j2 h
    have h1 := hgk j1
    have h2 := hgk j2
    rw [h] at h1
    have hj1 := j1.2
    have hj2 := j2.2
    apply Fin.ext
    have hd : (Fintype.card Fq : ℤ) ∣ ((j2 : ℕ) : ℤ) - ((j1 : ℕ) : ℤ) :=
      ⟨k j1 - k j2, by linear_combination h1 - h2⟩
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    omega
  simpa using Fintype.card_le_of_injective g hginj

end VF

end SwanLpsiAux

open scoped Classical

theorem solution
    (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
    (f : Fq[X]) (hN : 1 ≤ f.natDegree) (hcop : Nat.Coprime f.natDegree (Fintype.card Fq))
    (L : Type) [Field L] [Algebra (RatFunc Fq) L] (y : L)
    (hy : y ^ Fintype.card Fq - y + algebraMap (RatFunc Fq) L (algebraMap Fq[X] (RatFunc Fq) f) = 0)
    (hgen : IntermediateField.adjoin (RatFunc Fq) {y} = ⊤)
    (P : Ideal (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L)) [P.IsPrime]
    (hP : P ≠ ⊥) :
    Nat.card (L ≃ₐ[RatFunc Fq] L) = Fintype.card Fq ∧
    (∀ σ : L ≃ₐ[RatFunc Fq] L, σ ≠ 1 →
      (∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L,
          ∃ c ∈ P ^ (f.natDegree + 1), (c : L) = σ b - b) ∧
      ∃ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L,
          ∀ c ∈ P ^ (f.natDegree + 2), (c : L) ≠ σ b - b) ∧
    ∀ {k : Type} [Field k] (ψ : AddChar Fq k), (∃ a, ψ a ≠ 1) →
      ∀ χ : (L ≃ₐ[RatFunc Fq] L) → k,
        (∀ (σ : L ≃ₐ[RatFunc Fq] L) (c : Fq),
          σ y = y + algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) c) → χ σ = ψ c) →
        ∑ᶠ i : ℕ,
            (Nat.card {σ : L ≃ₐ[RatFunc Fq] L //
                ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L,
                  ∃ c ∈ P ^ (i + 2), (c : L) = σ b - b} : ℚ) /
              (Nat.card {σ : L ≃ₐ[RatFunc Fq] L //
                ∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L,
                  ∃ c ∈ P, (c : L) = σ b - b} : ℚ) *
            (if ∀ σ : L ≃ₐ[RatFunc Fq] L,
                (∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L,
                  ∃ c ∈ P ^ (i + 2), (c : L) = σ b - b) → χ σ = 1 then 0 else 1) =
          (f.natDegree : ℚ) := by
  classical
  have hq1 : 1 < Fintype.card Fq := Fintype.one_lt_card
  -- the Artin-Schreier polynomial
  obtain ⟨p, hpdef⟩ : ∃ p : (RatFunc Fq)[X],
      p = X ^ Fintype.card Fq + (C (algebraMap Fq[X] (RatFunc Fq) f) - X) := ⟨_, rfl⟩
  have hlow0 : (C (algebraMap Fq[X] (RatFunc Fq) f) - X : (RatFunc Fq)[X]).degree <
      (Fintype.card Fq : WithBot ℕ) := by
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast (by omega : 0 < Fintype.card Fq))
    · rw [degree_X]; exact_mod_cast hq1
  have hpmonic : p.Monic := by rw [hpdef]; exact monic_X_pow_add hlow0
  have hpdeg : p.natDegree = Fintype.card Fq := by
    rw [hpdef, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact hlow0), natDegree_X_pow]
  have hpy : aeval y p = 0 := by
    rw [hpdef]
    simp only [map_add, map_sub, map_pow, aeval_X, aeval_C]
    linear_combination hy
  have hp0 : p ≠ 0 := hpmonic.ne_zero
  have hint : IsIntegral (RatFunc Fq) y := ⟨p, hpmonic, by rw [← aeval_def]; exact hpy⟩
  have hmin_dvd : minpoly (RatFunc Fq) y ∣ p := minpoly.dvd _ _ hpy
  -- separability
  have hqK : ((Fintype.card Fq : ℕ) : RatFunc Fq) = 0 := by
    rw [← map_natCast (algebraMap Fq (RatFunc Fq)), FiniteField.cast_card_eq_zero, map_zero]
  have hqKX : ((Fintype.card Fq : ℕ) : (RatFunc Fq)[X]) = 0 := by
    rw [← C_eq_natCast, hqK, C_0]
  have hder : derivative p = -1 := by
    rw [hpdef]; simp [derivative_X_pow, hqK, hqKX]
  have hpsep : p.Separable := (separable_def' p).2 ⟨0, -1, by rw [hder]; ring⟩
  have hysep : IsSeparable (RatFunc Fq) y := hpsep.of_dvd hmin_dvd
  -- a power basis with generator y
  obtain ⟨pb, hpbgen, hpbdim⟩ : ∃ pb : PowerBasis (RatFunc Fq) L,
      pb.gen = y ∧ pb.dim = (minpoly (RatFunc Fq) y).natDegree :=
    ⟨(IntermediateField.adjoin.powerBasis hint).map
        ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv),
      by rw [PowerBasis.map_gen, IntermediateField.adjoin.powerBasis_gen]; rfl,
      by rw [PowerBasis.map_dim, IntermediateField.adjoin.powerBasis_dim]⟩
  haveI : FiniteDimensional (RatFunc Fq) L := pb.finite
  haveI : Algebra.IsSeparable (RatFunc Fq) (IntermediateField.adjoin (RatFunc Fq) {y}) :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hysep
  haveI : Algebra.IsSeparable (RatFunc Fq) L :=
    Algebra.IsSeparable.of_algHom (RatFunc Fq) _
      ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv).symm.toAlgHom
  have hdimle : pb.dim ≤ Fintype.card Fq := by
    rw [hpbdim, ← hpdeg]; exact natDegree_le_of_dvd hmin_dvd hp0
  subst hpbgen
  -- Dedekind setup at infinity
  haveI : IsDedekindDomain (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L) :=
    integralClosure.isDedekindDomain (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq) L
  haveI : IsFractionRing (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L) L :=
    integralClosure.isFractionRing_of_finite_extension (RatFunc Fq) L
  obtain ⟨v, hv⟩ : ∃ v : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L), v.asIdeal = P :=
    ⟨⟨P, inferInstance, hP⟩, rfl⟩
  subst hv
  have hO : ∀ a : RatFunc Fq, RatFunc.inftyValuation Fq a ≤ 1 →
      v.valuation L (algebraMap (RatFunc Fq) L a) ≤ 1 := by
    intro a ha
    have hmem : a ∈ (RatFunc.inftyValuation Fq).valuationSubring :=
      (Valuation.mem_valuationSubring_iff _ _).2 ha
    have hb : algebraMap (RatFunc Fq) L a ∈
        integralClosure (RatFunc.inftyValuation Fq).valuationSubring L := by
      rw [show algebraMap (RatFunc Fq) L a =
          algebraMap (RatFunc.inftyValuation Fq).valuationSubring L ⟨a, hmem⟩ from
        (IsScalarTower.algebraMap_apply (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq) L
          ⟨a, hmem⟩).symm]
      exact Subalgebra.algebraMap_mem _ _
    exact v.valuation_le_one ⟨_, hb⟩
  have hz : ∃ a : RatFunc Fq, a ≠ 0 ∧ v.valuation L (algebraMap (RatFunc Fq) L a) < 1 := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hcomap := Ideal.comap_ne_bot_of_integral_mem hx0 hxP (integralClosure.isIntegral x)
    obtain ⟨z, hzP, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
    refine ⟨(z : RatFunc Fq), fun h => hz0 (Subtype.ext h), ?_⟩
    have h1 := (v.valuation_lt_one_iff_mem (K := L) _).2 (Ideal.mem_comap.1 hzP)
    have h2 : algebraMap (integralClosure (RatFunc.inftyValuation Fq).valuationSubring L) L
        (algebraMap (RatFunc.inftyValuation Fq).valuationSubring _ z) =
        algebraMap (RatFunc Fq) L z := by
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (RatFunc.inftyValuation Fq).valuationSubring (RatFunc Fq) L]
      rfl
    rw [← h2]
    exact h1
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hϖ : v.valuation L (π : L) = WithZero.exp (-1) := by
    rw [show (π : L) = algebraMap _ L π from rfl, v.valuation_of_algebraMap, hπ]
  obtain ⟨hVK, hVy, hdim⟩ := SwanLpsiAux.val_facts (v.valuation L) pb hdimle f hN hcop hy hO hz hϖ
  have hconst : ∀ d : Fq,
      v.valuation L (algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) d)) ≤ 1 := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · rw [hVK _ ((_root_.map_ne_zero _).2 hd),
        show (algebraMap Fq (RatFunc Fq) d).intDegree = 0 from RatFunc.intDegree_C d, mul_zero,
        WithZero.exp_zero]
  have hminp : minpoly (RatFunc Fq) pb.gen = p :=
    (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpmonic hmin_dvd
      (le_of_eq (by rw [hpdeg, ← hpbdim, hdim]))).symm
  -- Frobenius
  have hfrob : ∀ u w : L, (u + w) ^ Fintype.card Fq = u ^ Fintype.card Fq + w ^ Fintype.card Fq := by
    letI : Algebra Fq L := ((algebraMap (RatFunc Fq) L).comp (algebraMap Fq (RatFunc Fq))).toAlgebra
    intro u w
    have h1 := map_add (FiniteField.frobeniusAlgHom Fq L) u w
    simpa only [FiniteField.coe_frobeniusAlgHom] using h1
  have hconstpow : ∀ d : Fq,
      (algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) d)) ^ Fintype.card Fq =
        algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) d) := by
    intro d; rw [← map_pow, ← map_pow, FiniteField.pow_card]
  -- every automorphism is a translation y ↦ y + c
  have hσc : ∀ σ : L ≃ₐ[RatFunc Fq] L, ∃ c : Fq,
      σ pb.gen = pb.gen + algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) c) := by
    intro σ
    letI : Algebra Fq L := ((algebraMap (RatFunc Fq) L).comp (algebraMap Fq (RatFunc Fq))).toAlgebra
    have hσy : (σ pb.gen) ^ Fintype.card Fq - σ pb.gen +
        algebraMap (RatFunc Fq) L (algebraMap Fq[X] (RatFunc Fq) f) = 0 := by
      have h1 := congrArg σ hy
      rwa [map_add, map_sub, map_pow, AlgEquiv.commutes, map_zero] at h1
    have hzq : (σ pb.gen - pb.gen) ^ Fintype.card Fq = σ pb.gen - pb.gen := by
      have h1 := map_sub (FiniteField.frobeniusAlgHom Fq L) (σ pb.gen) pb.gen
      simp only [FiniteField.coe_frobeniusAlgHom] at h1
      rw [h1]; linear_combination hσy - hy
    obtain ⟨c, hc⟩ := SwanLpsiAux.exists_algebraMap_eq_of_pow_card Fq hzq
    refine ⟨c, ?_⟩
    have hc' : algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) c) = σ pb.gen - pb.gen := hc
    rw [hc']; ring
  have hroot : ∀ c : Fq, aeval (pb.gen + algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) c))
      (minpoly (RatFunc Fq) pb.gen) = 0 := by
    intro c
    rw [hminp, hpdef]
    simp only [map_add, map_sub, map_pow, aeval_X, aeval_C]
    rw [hfrob, hconstpow]
    linear_combination hy
  let sig : Fq → (L ≃ₐ[RatFunc Fq] L) := fun c =>
    AlgEquiv.ofBijective (pb.lift _ (hroot c)) (Algebra.IsAlgebraic.algHom_bijective _)
  have hsig : ∀ c, sig c pb.gen = pb.gen + algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) c) :=
    fun c => pb.lift_gen _ (hroot c)
  have hext : ∀ σ τ : L ≃ₐ[RatFunc Fq] L, σ pb.gen = τ pb.gen → σ = τ := by
    intro σ τ h
    exact AlgEquiv.coe_algHom_injective (pb.algHom_ext h)
  have hsig_inj : Function.Injective sig := by
    intro c d h
    have h1 := hsig c
    rw [h, hsig d] at h1
    have h2 := add_left_cancel h1
    exact ((algebraMap Fq (RatFunc Fq)).injective ((algebraMap (RatFunc Fq) L).injective h2)).symm
  have hsig_surj : Function.Surjective sig := by
    intro σ
    obtain ⟨c, hc⟩ := hσc σ
    exact ⟨c, hext _ _ (by rw [hsig, hc])⟩
  have hcard : Nat.card (L ≃ₐ[RatFunc Fq] L) = Fintype.card Fq := by
    rw [← Nat.card_eq_of_bijective sig ⟨hsig_inj, hsig_surj⟩, Nat.card_eq_fintype_card]
  -- ramification
  have hint_σ : ∀ (σ : L ≃ₐ[RatFunc Fq] L)
      (b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L),
      σ b ∈ integralClosure (RatFunc.inftyValuation Fq).valuationSubring L := by
    intro σ b
    exact (b.2).map ((σ : L →ₐ[RatFunc Fq] L).restrictScalars
      (RatFunc.inftyValuation Fq).valuationSubring)
  have hmemPow : ∀ (x : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L) (n : ℕ),
      x ∈ v.asIdeal ^ n ↔ v.valuation L (x : L) ≤ WithZero.exp (-(n : ℤ)) := by
    intro x n
    rw [show (x : L) = algebraMap _ L x from rfl, v.valuation_of_algebraMap,
      v.intValuation_le_pow_iff_dvd, Ideal.dvd_span_singleton]
  have hlow : ∀ (σ : L ≃ₐ[RatFunc Fq] L)
      (b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L),
      ∃ c ∈ v.asIdeal ^ (f.natDegree + 1), (c : L) = σ b - b := by
    intro σ b
    obtain ⟨c0, hc0⟩ := hσc σ
    refine ⟨⟨σ b, hint_σ σ b⟩ - b, ?_, rfl⟩
    rw [hmemPow]
    have h1 := SwanLpsiAux.claimA (v.valuation L) pb hdim hcop hVK hVy hN σ.toAlgHom hc0 (hconst c0)
      (v.valuation_le_one b)
    push_cast
    exact h1
  have hnot : ∀ σ : L ≃ₐ[RatFunc Fq] L, σ ≠ 1 →
      ∀ c ∈ v.asIdeal ^ (f.natDegree + 2), (c : L) ≠ σ (π : L) - (π : L) := by
    intro σ hσ1 c hc hceq
    obtain ⟨c0, hc0⟩ := hσc σ
    have hc00 : c0 ≠ 0 := by
      rintro rfl
      apply hσ1
      apply hext
      rw [hc0]
      simp
    have hB : v.valuation L (σ (π : L) - (π : L)) = WithZero.exp (-((f.natDegree : ℤ) + 1)) :=
      SwanLpsiAux.claimB (v.valuation L) pb hdim hcop hVK hVy hN σ.toAlgHom hc00 hc0 hϖ
    rw [hmemPow, hceq, hB, WithZero.exp_le_exp] at hc
    push_cast at hc
    omega
  refine ⟨hcard, fun σ hσ1 => ⟨hlow σ, π, hnot σ hσ1⟩, ?_⟩
  -- the Swan conductor
  intro k _ ψ hψ χ hχ
  have hall : ∀ n : ℕ, n ≤ f.natDegree + 1 → ∀ (σ : L ≃ₐ[RatFunc Fq] L)
      (b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L),
      ∃ c ∈ v.asIdeal ^ n, (c : L) = σ b - b := by
    intro n hn σ b
    obtain ⟨c, hc, hceq⟩ := hlow σ b
    exact ⟨c, Ideal.pow_le_pow_right hn hc, hceq⟩
  have hone : ∀ n : ℕ, f.natDegree + 2 ≤ n → ∀ σ : L ≃ₐ[RatFunc Fq] L,
      (∀ b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L,
        ∃ c ∈ v.asIdeal ^ n, (c : L) = σ b - b) → σ = 1 := by
    intro n hn σ h
    by_contra hσ1
    obtain ⟨c, hc, hceq⟩ := h π
    exact hnot σ hσ1 c (Ideal.pow_le_pow_right hn hc) hceq
  have hall1 : ∀ (σ : L ≃ₐ[RatFunc Fq] L)
      (b : integralClosure (RatFunc.inftyValuation Fq).valuationSubring L),
      ∃ c ∈ v.asIdeal, (c : L) = σ b - b := by
    intro σ b
    obtain ⟨c, hc, hceq⟩ := hall 1 (by omega) σ b
    exact ⟨c, by rwa [pow_one] at hc, hceq⟩
  have hχ1 : χ 1 = 1 := by
    rw [hχ 1 0 (by simp), AddChar.map_zero_eq_one]
  obtain ⟨a, ha⟩ := hψ
  have hcardQ : (Nat.card (L ≃ₐ[RatFunc Fq] L) : ℚ) ≠ 0 := by
    rw [hcard]; exact Nat.cast_ne_zero.2 (by omega)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range f.natDegree) ?_]
  · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℚ)) ?_]
    · simp
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (hall (i + 2) (by omega))),
        Nat.card_congr (Equiv.subtypeUnivEquiv hall1), div_self hcardQ, one_mul, if_neg]
      push_neg
      exact ⟨sig a, hall (i + 2) (by omega) (sig a), by rw [hχ (sig a) a (hsig a)]; exact ha⟩
  · intro i hi
    rw [Function.mem_support] at hi
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hiN
    push_neg at hiN
    apply hi
    rw [if_pos, mul_zero]
    intro σ hσ
    rw [hone (i + 2) (by omega) σ hσ, hχ1]
