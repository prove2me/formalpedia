-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P36.local_unitary_mixtures_preserve_sharing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:29:59.428192+00:00
-- url     : https://prove2.me/submissions/6cdf72bd-6a7e-41d1-9093-1d17da62c2a4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36
noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

end QAlgorithms.Papers.Independent.Extend50.P36

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P36
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem lu_site_sum {I : Type*} [Fintype I] {m : ℕ} (i : Fin m) (U : Matrix I I ℂ)
    (hU : ∀ s t, ∑ z, U z s * star (U z t) = if s = t then 1 else 0) (a b : I)
    (s t : Fin m → I) :
    ∑ x : Fin m → I, (if x i = a then (∏ k, U (x k) (s k)) *
        star (∏ k, U (Function.update x i b k) (t k)) else 0)
      = U a (s i) * star (U b (t i)) * (if ∀ k, k ≠ i → s k = t k then 1 else 0) := by
  set g : Fin m → I → ℂ := fun k z => if k = i then (if z = a then U a (s i) * star (U b (t i)) else 0)
    else U z (s k) * star (U z (t k)) with hg
  have hpt : ∀ x : Fin m → I, (if x i = a then (∏ k, U (x k) (s k)) *
        star (∏ k, U (Function.update x i b k) (t k)) else 0) = ∏ k, g k (x k) := by
    intro x
    by_cases hx : x i = a
    · rw [if_pos hx, star_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases hk : k = i
      · subst hk; simp [hg, hx]
      · simp [hg, hk, Function.update_of_ne hk]
    · rw [if_neg hx]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hg, hx])).symm
  rw [Finset.sum_congr rfl fun x _ => hpt x, ← Fintype.prod_sum g]
  rw [Fintype.prod_eq_mul_prod_compl i]
  congr 1
  · simp [hg]
  · calc _ = ∏ k ∈ ({i}ᶜ : Finset (Fin m)), (if s k = t k then (1 : ℂ) else 0) := by
          refine Finset.prod_congr rfl fun k hk => ?_
          have hk' : k ≠ i := by simpa using hk
          simp only [hg, if_neg hk', hU]
      _ = _ := by
          convert Finset.prod_boole using 2
          simp

theorem lu_agree_sum {I : Type*} [Fintype I] {m : ℕ} (i : Fin m) (s : Fin m → I)
    (F : (Fin m → I) → ℂ) :
    ∑ t : Fin m → I, (if ∀ k, k ≠ i → s k = t k then F t else 0) =
      ∑ d : I, F (Function.update s i d) := by
  have h : ∀ t : Fin m → I, (if ∀ k, k ≠ i → s k = t k then F t else 0) =
      ∑ d : I, if t = Function.update s i d then F t else 0 := by
    intro t
    by_cases ht : ∀ k, k ≠ i → s k = t k
    · rw [if_pos ht, Finset.sum_eq_single (t i)]
      · rw [if_pos]
        funext k; by_cases hk : k = i
        · subst hk; simp
        · simp [Function.update_of_ne hk, ht k hk]
      · intro d _ hd; rw [if_neg]; intro h; apply hd; rw [h]; simp
      · simp
    · rw [if_neg ht]; symm
      refine Finset.sum_eq_zero fun d _ => if_neg ?_
      rintro rfl; apply ht; intro k hk; simp [Function.update_of_ne hk]
  rw [Finset.sum_congr rfl fun t _ => h t, Finset.sum_comm]
  simp

theorem lu_swap4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

def luW {I J : Type*} [Fintype I] [Fintype J] (m n : ℕ) (U : Op I) (V : Op J) :
    Op (SharingIndex I J m n) :=
  Matrix.of fun p q => (∏ k, U (p.1 k) (q.1 k)) * ∏ l, V (p.2 l) (q.2 l)

theorem lu_marg_lhs {I J : Type*} [Fintype I] [Fintype J] {m n : ℕ} (U : Op I) (V : Op J)
    (X : Op (SharingIndex I J m n)) (i : Fin m) (j : Fin n) (a b : I × J) :
    sharingMarginal (luW m n U V * X * (luW m n U V)ᴴ) i j a b =
      ∑ r : SharingIndex I J m n, ∑ s : SharingIndex I J m n, X r s *
        (∑ x : Fin m → I, if x i = a.1 then (∏ k, U (x k) (r.1 k)) *
          star (∏ k, U (Function.update x i b.1 k) (s.1 k)) else 0) *
        (∑ y : Fin n → J, if y j = a.2 then (∏ l, V (y l) (r.2 l)) *
          star (∏ l, V (Function.update y j b.2 l) (s.2 l)) else 0) := by
  simp only [sharingMarginal, Matrix.mul_apply, Matrix.conjTranspose_apply, luW, Matrix.of_apply]
  have hpt : ∀ (x : Fin m → I) (y : Fin n → J),
      (if x i = a.1 ∧ y j = a.2 then
          ∑ s : SharingIndex I J m n, (∑ r : SharingIndex I J m n,
            ((∏ k, U (x k) (r.1 k)) * ∏ l, V (y l) (r.2 l)) * X r s) *
              star ((∏ k, U (Function.update x i b.1 k) (s.1 k)) *
                ∏ l, V (Function.update y j b.2 l) (s.2 l))
        else 0) =
      ∑ r : SharingIndex I J m n, ∑ s : SharingIndex I J m n, X r s *
        (if x i = a.1 then (∏ k, U (x k) (r.1 k)) *
          star (∏ k, U (Function.update x i b.1 k) (s.1 k)) else 0) *
        (if y j = a.2 then (∏ l, V (y l) (r.2 l)) *
          star (∏ l, V (Function.update y j b.2 l) (s.2 l)) else 0) := by
    intro x y
    by_cases h1 : x i = a.1 <;> by_cases h2 : y j = a.2 <;>
      simp only [h1, h2, and_true, true_and, and_false, false_and, if_true, if_false, mul_zero,
        zero_mul, Finset.sum_const_zero, and_self]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [star_mul']
    ring
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hpt x y, lu_swap4]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring


theorem lu_marg_rhs {I J : Type*} [Fintype I] [Fintype J] {m n : ℕ} (U : Op I) (V : Op J)
    (X : Op (SharingIndex I J m n)) (i : Fin m) (j : Fin n) (a b : I × J) :
    localConjugate U V (sharingMarginal X i j) a b =
      ∑ x : Fin m → I, ∑ y : Fin n → J, ∑ d1 : I, ∑ d2 : J,
        X (x, y) (Function.update x i d1, Function.update y j d2) *
          (U a.1 (x i) * star (U b.1 d1)) * (V a.2 (y j) * star (V b.2 d2)) := by
  simp only [localConjugate, Matrix.mul_apply, Matrix.conjTranspose_apply, sharingMarginal]
  have hc : ∀ d : I × J, (∑ c : I × J, Matrix.kronecker U V a c *
      ∑ x : Fin m → I, ∑ y : Fin n → J, if x i = c.1 ∧ y j = c.2 then
        X (x, y) (Function.update x i d.1, Function.update y j d.2) else 0) =
      ∑ x : Fin m → I, ∑ y : Fin n → J, U a.1 (x i) * V a.2 (y j) *
        X (x, y) (Function.update x i d.1, Function.update y j d.2) := by
    intro d
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : ∀ c : I × J, (Matrix.kronecker U V a c * if x i = c.1 ∧ y j = c.2 then
        X (x, y) (Function.update x i d.1, Function.update y j d.2) else 0) =
        if (x i, y j) = c then Matrix.kronecker U V a c *
          X (x, y) (Function.update x i d.1, Function.update y j d.2) else 0 := by
      intro c
      by_cases h : (x i, y j) = c
      · subst h; simp
      · rw [if_neg h, if_neg, mul_zero]
        rintro ⟨h1, h2⟩; exact h (Prod.ext h1 h2)
    rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_ite_eq]
    simp [Matrix.kronecker_apply]
  simp only [hc, Finset.sum_mul]
  rw [Fintype.sum_prod_type, lu_swap4]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun d1 _ => Finset.sum_congr rfl fun d2 _ => ?_
  have hk : Matrix.kronecker U V b (d1, d2) = U b.1 d1 * V b.2 d2 := by
    obtain ⟨b1, b2⟩ := b; rfl
  rw [hk, star_mul']
  ring

theorem lu_marg {I J : Type*} [Fintype I] [Fintype J] {m n : ℕ} (U : Op I) (V : Op J)
    (hU : ∀ s t, ∑ z, U z s * star (U z t) = if s = t then 1 else 0)
    (hV : ∀ s t, ∑ z, V z s * star (V z t) = if s = t then 1 else 0)
    (X : Op (SharingIndex I J m n)) (i : Fin m) (j : Fin n) :
    sharingMarginal (luW m n U V * X * (luW m n U V)ᴴ) i j =
      localConjugate U V (sharingMarginal X i j) := by
  ext a b
  rw [lu_marg_lhs, lu_marg_rhs]
  simp only [lu_site_sum i U hU, lu_site_sum j V hV]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Fintype.sum_prod_type]
  have hpt : ∀ (s1 : Fin m → I) (s2 : Fin n → J),
      X (x, y) (s1, s2) * (U a.1 ((x, y).1 i) * star (U b.1 ((s1, s2).1 i)) *
          (if ∀ k, k ≠ i → (x, y).1 k = (s1, s2).1 k then 1 else 0)) *
        (V a.2 ((x, y).2 j) * star (V b.2 ((s1, s2).2 j)) *
          (if ∀ k, k ≠ j → (x, y).2 k = (s1, s2).2 k then 1 else 0)) =
      if ∀ k, k ≠ i → x k = s1 k then
        (if ∀ k, k ≠ j → y k = s2 k then
          X (x, y) (s1, s2) * (U a.1 (x i) * star (U b.1 (s1 i))) *
            (V a.2 (y j) * star (V b.2 (s2 j))) else 0) else 0 := by
    intro s1 s2
    dsimp only
    split_ifs <;> simp
  simp only [hpt]
  have h2 : ∀ s1 : Fin m → I, (∑ s2 : Fin n → J, if ∀ k, k ≠ i → x k = s1 k then
        (if ∀ k, k ≠ j → y k = s2 k then
          X (x, y) (s1, s2) * (U a.1 (x i) * star (U b.1 (s1 i))) *
            (V a.2 (y j) * star (V b.2 (s2 j))) else 0) else 0) =
      if ∀ k, k ≠ i → x k = s1 k then ∑ d2 : J,
          X (x, y) (s1, Function.update y j d2) * (U a.1 (x i) * star (U b.1 (s1 i))) *
            (V a.2 (y j) * star (V b.2 d2)) else 0 := by
    intro s1
    split_ifs
    · rw [lu_agree_sum j y (fun s2 => X (x, y) (s1, s2) * (U a.1 (x i) * star (U b.1 (s1 i))) *
            (V a.2 (y j) * star (V b.2 (s2 j))))]
      simp
    · simp
  simp only [h2]
  rw [lu_agree_sum i x (fun s1 => ∑ d2 : J,
          X (x, y) (s1, Function.update y j d2) * (U a.1 (x i) * star (U b.1 (s1 i))) *
            (V a.2 (y j) * star (V b.2 d2)))]
  simp

theorem lu_marg_sum {I J : Type*} [Fintype I] [Fintype J] {m n q : ℕ}
    (c : Fin q → ℂ) (Y : Fin q → Op (SharingIndex I J m n)) (i : Fin m) (j : Fin n) :
    sharingMarginal (∑ t, c t • Y t) i j = ∑ t, c t • sharingMarginal (Y t) i j := by
  ext a b
  simp only [sharingMarginal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  have : ∀ (x : Fin m → I) (y : Fin n → J),
      (if x i = a.1 ∧ y j = a.2 then ∑ t, c t * Y t (x, y)
          (Function.update x i b.1, Function.update y j b.2) else 0) =
        ∑ t, (c t * if x i = a.1 ∧ y j = a.2 then Y t (x, y)
          (Function.update x i b.1, Function.update y j b.2) else 0) := by
    intro x y; split_ifs <;> simp
  simp only [this]
  exact (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm

theorem lu_trace_marg {I J : Type*} [Fintype I] [Fintype J] {m n : ℕ}
    (Y : Op (SharingIndex I J m n)) (i : Fin m) (j : Fin n) :
    (sharingMarginal Y i j).trace = Y.trace := by
  simp only [Matrix.trace, Matrix.diag, sharingMarginal]
  rw [Fintype.sum_prod_type (fun p : SharingIndex I J m n => Y p p)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have : ∀ a : I × J, (if x i = a.1 ∧ y j = a.2 then
      Y (x, y) (Function.update x i a.1, Function.update y j a.2) else 0) =
      if (x i, y j) = a then Y (x, y) (x, y) else 0 := by
    intro a
    by_cases h : (x i, y j) = a
    · subst h; simp
    · rw [if_neg h, if_neg]; rintro ⟨h1, h2⟩; exact h (Prod.ext h1 h2)
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem lu_col {I : Type*} [Fintype I] (U : Matrix.unitaryGroup I ℂ) (s t : I) :
    ∑ z, (U : Op I) z s * star ((U : Op I) z t) = if s = t then 1 else 0 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 U.2) t) s
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
  calc _ = ∑ z, star ((U : Op I) z t) * (U : Op I) z s :=
        Finset.sum_congr rfl fun z _ => mul_comm _ _
    _ = _ := h
    _ = _ := by by_cases hst : s = t <;> simp [hst, Ne.symm]

theorem lu_trace_conj {I J : Type*} [Fintype I] [Fintype J] (U : Matrix.unitaryGroup I ℂ)
    (V : Matrix.unitaryGroup J ℂ) (rho : Op (I × J)) :
    (localConjugate (U : Op I) (V : Op J) rho).trace = rho.trace := by
  simp only [localConjugate]
  have hk : ∀ (A : Op I) (B : Op J), Matrix.kronecker A B = Matrix.kroneckerMap (· * ·) A B :=
    fun _ _ => rfl
  rw [hk, Matrix.trace_mul_cycle, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  have hU : (U : Op I)ᴴ * (U : Op I) = 1 := Matrix.mem_unitaryGroup_iff'.1 U.2
  have hV : (V : Op J)ᴴ * (V : Op J) = 1 := Matrix.mem_unitaryGroup_iff'.1 V.2
  rw [hU, hV, Matrix.one_kronecker_one, one_mul]

open scoped ComplexOrder in
theorem solution {I J : Type*}
    [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (m n q : ℕ) (hm : 0 < m) (hn : 0 < n) (rho : Op (I × J))
    (hrho : IsDensityMatrix rho) (hshare : Sharable m n rho)
    (p : Fin q → ℝ) (hp : ∀ i, 0 ≤ p i) (hpSum : (∑ i, p i) = 1)
    (U : Fin q → Matrix.unitaryGroup I ℂ) (V : Fin q → Matrix.unitaryGroup J ℂ) :
    Sharable m n (∑ i, (p i : ℂ) • localConjugate (U i : Op I) (V i : Op J) rho) := by
  obtain ⟨X, ⟨hpsd, -⟩, hmarg⟩ := hshare
  have hM : ∀ i j, sharingMarginal (∑ t, (p t : ℂ) •
      (luW m n (U t : Op I) (V t : Op J) * X * (luW m n (U t : Op I) (V t : Op J))ᴴ)) i j =
      ∑ t, (p t : ℂ) • localConjugate (U t : Op I) (V t : Op J) rho := by
    intro i j
    rw [lu_marg_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [lu_marg _ _ (lu_col (U t)) (lu_col (V t)), hmarg]
  refine ⟨_, ⟨?_, ?_⟩, hM⟩
  · refine Matrix.posSemidef_sum _ fun t _ => ?_
    exact (hpsd.mul_mul_conjTranspose_same _).smul (by exact_mod_cast hp t)
  · rw [← lu_trace_marg _ ⟨0, hm⟩ ⟨0, hn⟩, hM, Matrix.trace_sum]
    simp only [Matrix.trace_smul, lu_trace_conj, hrho.2, smul_eq_mul, mul_one]
    exact_mod_cast hpSum
