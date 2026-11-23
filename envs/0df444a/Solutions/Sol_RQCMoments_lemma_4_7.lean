-- Prove2me | solution 1 for RQCMoments.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T05:09:21.470928+00:00
-- url     : https://prove2.me/submissions/50ee5fc4-4454-490d-986b-6ef06022edee

import Mathlib

set_option autoImplicit false

open Polynomial

namespace RQCMoments

lemma prod_form (f : ℝ[X]) (n : ℕ) (r : ℕ → ℝ) (hr : ∀ a b, a < b → b < n → r a < r b)
    (hroot : ∀ m, m < n → f.eval (r m) = 0) (hdeg : f.natDegree ≤ n) :
    ∃ a : ℝ, f = C a * ∏ m ∈ Finset.range n, (X - C (r m)) := by
  by_cases hf : f = 0
  · exact ⟨0, by simp [hf]⟩
  have hinj : Set.InjOn r (Finset.range n : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hab (hr a b h hb).ne
    · exact absurd hab (hr b a h ha).ne'
  set T := (Finset.range n).image r with hT
  have hdvd : (∏ a ∈ T, (X - C a)) ∣ f := by
    have : (T.val.map (fun a => X - C a)).prod ∣ f := by
      rw [Multiset.prod_X_sub_C_dvd_iff_le_roots hf]
      rw [Multiset.le_iff_subset T.nodup]
      intro a ha
      have ha' : a ∈ T := ha
      rw [hT, Finset.mem_image] at ha'
      obtain ⟨m, hm, rfl⟩ := ha'
      rw [mem_roots hf]
      exact hroot m (Finset.mem_range.1 hm)
    exact this
  rw [hT, Finset.prod_image hinj] at hdvd
  obtain ⟨g, hg⟩ := hdvd
  have hQm : (∏ m ∈ Finset.range n, (X - C (r m))).Monic :=
    monic_prod_of_monic _ _ (fun m _ => monic_X_sub_C _)
  have hQd : (∏ m ∈ Finset.range n, (X - C (r m))).natDegree = n := by
    rw [natDegree_prod_of_monic _ _ (fun m _ => monic_X_sub_C _)]
    simp
  have hQ0 : (∏ m ∈ Finset.range n, (X - C (r m))) ≠ 0 := hQm.ne_zero
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hf (by simpa using hg)
  have hgd : g.natDegree = 0 := by
    have := natDegree_mul hQ0 hg0
    rw [← hg, hQd] at this
    omega
  refine ⟨g.coeff 0, ?_⟩
  rw [hg, mul_comm, ← eq_C_of_natDegree_eq_zero hgd]

lemma uniq_herm (ℓ : ℕ) (x : Fin ℓ → ℝ) (hx : StrictMono x) (i : Fin ℓ) (D : ℝ[X])
    (hdeg : D.natDegree ≤ 2 * ℓ - 2) (h0 : ∀ j, D.eval (x j) = 0)
    (h1 : ∀ j, j ≠ i → (derivative D).eval (x j) = 0) : D = 0 := by
  by_contra hD
  let g : Fin ℓ → ℝ[X] := fun j => if j = i then X - C (x j) else (X - C (x j)) ^ 2
  have hcop : Set.Pairwise (Finset.univ : Finset (Fin ℓ)) (Function.onFun IsCoprime g) := by
    intro a _ b _ hab
    have hc : IsCoprime (X - C (x a)) (X - C (x b)) :=
      pairwise_coprime_X_sub_C hx.injective hab
    simp only [Function.onFun, g]
    split_ifs
    · exact hc
    · exact hc.pow_right
    · exact hc.pow_left
    · exact hc.pow
  have hdv : ∀ j ∈ (Finset.univ : Finset (Fin ℓ)), g j ∣ D := by
    intro j _
    simp only [g]
    split_ifs with h
    · have : 1 ≤ rootMultiplicity (x j) D := (rootMultiplicity_pos hD).2 (h0 j)
      simpa using (le_rootMultiplicity_iff hD).1 this
    · have : 2 ≤ rootMultiplicity (x j) D :=
        (one_lt_rootMultiplicity_iff_isRoot hD).2 ⟨h0 j, h1 j h⟩
      exact (le_rootMultiplicity_iff hD).1 this
  have hP := Finset.prod_dvd_of_coprime hcop hdv
  have hdeg2 := natDegree_le_of_dvd (hP.trans (dvd_refl D)) hD
  have hm : ∀ j ∈ (Finset.univ : Finset (Fin ℓ)), (g j).Monic := by
    intro j _
    simp only [g]
    split_ifs
    · exact monic_X_sub_C _
    · exact (monic_X_sub_C _).pow _
  rw [natDegree_prod_of_monic _ _ hm] at hdeg2
  have hs : ∑ j : Fin ℓ, (g j).natDegree = 2 * ℓ - 1 := by
    have : ∀ j : Fin ℓ, (g j).natDegree = if j = i then 1 else 2 := by
      intro j
      simp only [g]
      split_ifs
      · simp
      · rw [natDegree_pow, natDegree_X_sub_C]
    simp only [this]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [Finset.sum_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
    have hc : (Finset.univ.erase i).card = ℓ - 1 := by simp
    simp [hc]
    have : 0 < ℓ := Fin.pos i
    omega
  rw [hs] at hdeg2
  have : 0 < ℓ := Fin.pos i
  omega


lemma exist_herm (ℓ : ℕ) (x : Fin ℓ → ℝ) (hx : StrictMono x) (i : Fin ℓ) :
    ∃ L : ℝ[X], L.natDegree ≤ 2 * ℓ - 2 ∧ (∀ j, L.eval (x j) = if j < i then 1 else 0) ∧
      (∀ j, j ≠ i → (derivative L).eval (x j) = 0) := by
  have hℓ : 0 < ℓ := Fin.pos i
  let Φ : degreeLT ℝ (2 * ℓ - 1) →ₗ[ℝ] (Fin ℓ ⊕ {j : Fin ℓ // j ≠ i}) → ℝ :=
    LinearMap.pi (fun c => Sum.elim
      (fun j : Fin ℓ => (leval (x j)).comp (degreeLT ℝ (2 * ℓ - 1)).subtype)
      (fun j : {j : Fin ℓ // j ≠ i} =>
        (leval (x j.1)).comp ((derivative (R := ℝ)).comp (degreeLT ℝ (2 * ℓ - 1)).subtype)) c)
  have hΦ : ∀ p, Φ p = fun c => Sum.elim (fun j : Fin ℓ => (p : ℝ[X]).eval (x j))
      (fun j : {j : Fin ℓ // j ≠ i} => (derivative (p : ℝ[X])).eval (x j.1)) c := by
    intro p; funext c; rcases c with c | c <;> simp [Φ]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have h := hΦ p ▸ hp
    have h0 : ∀ j, (p : ℝ[X]).eval (x j) = 0 := fun j => congrFun h (Sum.inl j)
    have h1 : ∀ j, j ≠ i → (derivative (p : ℝ[X])).eval (x j) = 0 :=
      fun j hj => congrFun h (Sum.inr ⟨j, hj⟩)
    have hd : (p : ℝ[X]).natDegree ≤ 2 * ℓ - 2 := by
      have := mem_degreeLT.1 p.2
      by_cases hp0 : (p : ℝ[X]) = 0
      · simp [hp0]
      · rw [degree_eq_natDegree hp0] at this
        have : (p : ℝ[X]).natDegree < 2 * ℓ - 1 := by exact_mod_cast this
        omega
    exact Subtype.ext (uniq_herm ℓ x hx i p hd h0 h1)
  have hfr : Module.finrank ℝ (degreeLT ℝ (2 * ℓ - 1)) =
      Module.finrank ℝ ((Fin ℓ ⊕ {j : Fin ℓ // j ≠ i}) → ℝ) := by
    rw [(degreeLTEquiv ℝ (2 * ℓ - 1)).finrank_eq, Module.finrank_fin_fun,
      Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_subtype_compl]
    simp
    omega
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  obtain ⟨p, hp⟩ := hsurj (Sum.elim (fun j : Fin ℓ => if j < i then (1 : ℝ) else 0)
    (fun _ => 0))
  have h := hΦ p ▸ hp
  refine ⟨p, ?_, fun j => congrFun h (Sum.inl j), fun j hj => congrFun h (Sum.inr ⟨j, hj⟩)⟩
  have := mem_degreeLT.1 p.2
  by_cases hp0 : (p : ℝ[X]) = 0
  · simp [hp0]
  · rw [degree_eq_natDegree hp0] at this
    have : (p : ℝ[X]).natDegree < 2 * ℓ - 1 := by exact_mod_cast this
    omega

lemma sign_prod (n c : ℕ) (r : ℕ → ℝ) (t : ℝ) (hc : c ≤ n) (h1 : ∀ m, m < c → r m < t)
    (h2 : ∀ m, c ≤ m → m < n → t < r m) :
    ∃ P : ℝ, 0 < P ∧ ∏ m ∈ Finset.range n, (t - r m) = (-1) ^ (n - c) * P := by
  rw [← Finset.prod_range_mul_prod_Ico _ hc]
  have hA : 0 < ∏ m ∈ Finset.range c, (t - r m) :=
    Finset.prod_pos (fun m hm => sub_pos.2 (h1 m (Finset.mem_range.1 hm)))
  have hB : 0 < ∏ m ∈ Finset.Ico c n, (r m - t) :=
    Finset.prod_pos (fun m hm => sub_pos.2 (h2 m (Finset.mem_Ico.1 hm).1 (Finset.mem_Ico.1 hm).2))
  have : ∏ m ∈ Finset.Ico c n, (t - r m) = (-1) ^ (n - c) * ∏ m ∈ Finset.Ico c n, (r m - t) := by
    have : ∀ m ∈ Finset.Ico c n, t - r m = (-1) * (r m - t) := fun m _ => by ring
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
  rw [this]
  exact ⟨_, mul_pos hA hB, by ring⟩

lemma main_minorant (ℓ i : ℕ) (hi1 : 1 ≤ i) (hiℓ : i < ℓ) (z : ℕ → ℝ)
    (hz : ∀ a b, a < b → b < ℓ → z a < z b) (L : ℝ[X]) (hdeg : L.natDegree ≤ 2 * ℓ - 2)
    (hval : ∀ j, j < ℓ → L.eval (z j) = if j < i then 1 else 0)
    (hder : ∀ j, j < ℓ → j ≠ i → (derivative L).eval (z j) = 0) :
    ∀ t, L.eval t ≤ if t ≤ z i then 1 else 0 := by
  have hrolle : ∀ j, ∃ y : ℝ, (j + 1 < ℓ → (j + 1 < i ∨ i ≤ j) →
      z j < y ∧ y < z (j + 1) ∧ (derivative L).eval y = 0) := by
    intro j
    by_cases h : j + 1 < ℓ ∧ (j + 1 < i ∨ i ≤ j)
    · obtain ⟨h1, h2⟩ := h
      have hLeq : L.eval (z j) = L.eval (z (j + 1)) := by
        rw [hval j (by omega), hval (j + 1) h1]
        rcases h2 with h2 | h2
        · simp [show j < i by omega, show j + 1 < i by omega]
        · simp [show ¬ j < i by omega, show ¬ j + 1 < i by omega]
      obtain ⟨c, hc, hc0⟩ := exists_deriv_eq_zero (f := fun t => L.eval t)
        (hz j (j + 1) (by omega) h1) L.continuous.continuousOn hLeq
      refine ⟨c, fun _ _ => ⟨hc.1, hc.2, ?_⟩⟩
      rw [← Polynomial.deriv]; exact hc0
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose y hy using hrolle
  let n : ℕ := 2 * ℓ - 3
  let r : ℕ → ℝ := fun m => if m < 2 * i - 1 then (if m % 2 = 0 then z (m / 2) else y (m / 2))
      else (if (m - (2 * i - 1)) % 2 = 0 then y (i + (m - (2 * i - 1)) / 2)
        else z (i + 1 + (m - (2 * i - 1)) / 2))
  have hstep : ∀ m, m + 1 < n → r m < r (m + 1) := by
    intro m hm
    have hm' : m + 1 < 2 * ℓ - 3 := hm
    by_cases hA : m + 1 < 2 * i - 1
    · have hA0 : m < 2 * i - 1 := by omega
      by_cases hp : m % 2 = 0
      · have hq : ¬ (m + 1) % 2 = 0 := by omega
        have hj := hy (m / 2) (by omega) (by omega)
        simp only [r, if_pos hA0, if_pos hA, if_pos hp, if_neg hq]
        have : (m + 1) / 2 = m / 2 := by omega
        rw [this]; exact hj.1
      · have hq : (m + 1) % 2 = 0 := by omega
        have hj := hy (m / 2) (by omega) (by omega)
        simp only [r, if_pos hA0, if_pos hA, if_neg hp, if_pos hq]
        have : (m + 1) / 2 = m / 2 + 1 := by omega
        rw [this]; exact hj.2.1
    · by_cases hB : m < 2 * i - 1
      · have hp : m % 2 = 0 := by omega
        have hj := hy i (by omega) (by omega)
        have e1 : m + 1 - (2 * i - 1) = 0 := by omega
        have e2 : m / 2 = i - 1 := by omega
        simp only [r, if_pos hB, if_neg hA, if_pos hp, e1]
        simp only [Nat.zero_mod, if_pos, Nat.zero_div, add_zero]
        rw [e2]
        have : z (i - 1) < z i := hz _ _ (by omega) (by omega)
        exact this.trans hj.1
      · have hA' : ¬ m < 2 * i - 1 := hB
        by_cases hp : (m - (2 * i - 1)) % 2 = 0
        · have hq : ¬ (m + 1 - (2 * i - 1)) % 2 = 0 := by omega
          have hj := hy (i + (m - (2 * i - 1)) / 2) (by omega) (by omega)
          simp only [r, if_neg hA, if_neg hA', if_pos hp, if_neg hq]
          have e : (m + 1 - (2 * i - 1)) / 2 = (m - (2 * i - 1)) / 2 := by omega
          have e2 : i + 1 + (m - (2 * i - 1)) / 2 = i + (m - (2 * i - 1)) / 2 + 1 := by omega
          rw [e, e2]; exact hj.2.1
        · have hq : (m + 1 - (2 * i - 1)) % 2 = 0 := by omega
          have hj := hy (i + (m - (2 * i - 1)) / 2 + 1) (by omega) (by omega)
          simp only [r, if_neg hA, if_neg hA', if_neg hp, if_pos hq]
          have e : (m + 1 - (2 * i - 1)) / 2 = (m - (2 * i - 1)) / 2 + 1 := by omega
          have e2 : i + 1 + (m - (2 * i - 1)) / 2 = i + (m - (2 * i - 1)) / 2 + 1 := by omega
          rw [e, e2]
          have e3 : i + ((m - (2 * i - 1)) / 2 + 1) = i + (m - (2 * i - 1)) / 2 + 1 := by omega
          rw [e3]; exact hj.1
  have hmono : ∀ a b, a < b → b < n → r a < r b := by
    have : ∀ d a, a + d + 1 < n → r a < r (a + d + 1) := by
      intro d
      induction d with
      | zero => intro a ha; exact hstep a (by omega)
      | succ d ih =>
        intro a ha
        exact (ih a (by omega)).trans (hstep (a + d + 1) (by omega))
    intro a b hab hb
    have := this (b - a - 1) a (by omega)
    rwa [show a + (b - a - 1) + 1 = b by omega] at this
  have hmono' : ∀ a b, a ≤ b → b < n → r a ≤ r b := by
    intro a b hab hb
    rcases hab.eq_or_lt with h | h
    · rw [h]
    · exact (hmono a b h hb).le
  have hroot : ∀ m, m < n → (derivative L).eval (r m) = 0 := by
    intro m hm
    have hm' : m < 2 * ℓ - 3 := hm
    by_cases hA : m < 2 * i - 1
    · by_cases hp : m % 2 = 0
      · simp only [r, if_pos hA, if_pos hp]
        exact hder _ (by omega) (by omega)
      · simp only [r, if_pos hA, if_neg hp]
        exact (hy (m / 2) (by omega) (by omega)).2.2
    · by_cases hp : (m - (2 * i - 1)) % 2 = 0
      · simp only [r, if_neg hA, if_pos hp]
        exact (hy (i + (m - (2 * i - 1)) / 2) (by omega) (by omega)).2.2
      · simp only [r, if_neg hA, if_neg hp]
        exact hder _ (by omega) (by omega)
  have hfdeg : (derivative L).natDegree ≤ n := by
    have := natDegree_derivative_le L
    show _ ≤ 2 * ℓ - 3
    omega
  obtain ⟨a, hfa⟩ := prod_form (derivative L) n r hmono hroot hfdeg
  have hev : ∀ t, (derivative L).eval t = a * ∏ m ∈ Finset.range n, (t - r m) := by
    intro t; rw [hfa]; simp [eval_prod]
  have hr2 : r (2 * i - 2) = z (i - 1) := by
    have : 2 * i - 2 < 2 * i - 1 := by omega
    simp only [r, if_pos this]
    have e : (2 * i - 2) % 2 = 0 := by omega
    have e2 : (2 * i - 2) / 2 = i - 1 := by omega
    rw [if_pos e, e2]
  have hr_left : ∀ m, m < 2 * i - 1 → r m ≤ z (i - 1) := by
    intro m hm
    rw [← hr2]; exact hmono' _ _ (by omega) (by omega)
  have hr_right : ∀ m, 2 * i - 1 ≤ m → m < n → z i < r m := by
    intro m hm1 hm2
    have hn : 2 * i - 1 < n := by omega
    have hj := hy i (by omega) (by omega)
    have : r (2 * i - 1) = y i := by
      have h1 : ¬ 2 * i - 1 < 2 * i - 1 := by omega
      simp only [r, if_neg h1]
      have : 2 * i - 1 - (2 * i - 1) = 0 := by omega
      rw [this]; simp
    have h3 := hmono' _ _ hm1 hm2
    rw [this] at h3
    exact hj.1.trans_le h3
  -- the sign of the leading coefficient
  have ha : a < 0 := by
    obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope (f := fun t => L.eval t)
      (hz (i - 1) i (by omega) hiℓ) L.continuous.continuousOn
      (fun t _ => (Polynomial.differentiableAt L).differentiableWithinAt)
    rw [Polynomial.deriv] at hc'
    have hgap : 0 < z i - z (i - 1) := sub_pos.2 (hz (i - 1) i (by omega) hiℓ)
    rw [hval i hiℓ, hval (i - 1) (by omega), if_neg (by omega), if_pos (by omega)] at hc'
    have hneg : (derivative L).eval c < 0 := by
      rw [hc']; exact div_neg_of_neg_of_pos (by norm_num) hgap
    have hc1 : z (i - 1) < c := hc.1
    have hc2 : c < z i := hc.2
    obtain ⟨P, hP, hP'⟩ := sign_prod n (2 * i - 1) r c (by omega)
      (fun m hm => (hr_left m hm).trans_lt hc1)
      (fun m hm1 hm2 => hc2.trans (hr_right m hm1 hm2))
    have : Even (n - (2 * i - 1)) := ⟨ℓ - 1 - i, by show 2 * ℓ - 3 - (2 * i - 1) = _; omega⟩
    rw [hev, hP', this.neg_one_pow, one_mul] at hneg
    by_contra hh
    push_neg at hh
    exact absurd hneg (not_lt.2 (mul_nonneg hh hP.le))
  have hsign : ∀ t k, k < n → r k < t → (k + 1 < n → t < r (k + 1)) →
      (k % 2 = 0 → (derivative L).eval t < 0) ∧ (k % 2 = 1 → 0 < (derivative L).eval t) := by
    intro t k hk hrk hnext
    obtain ⟨P, hP, hP'⟩ := sign_prod n (k + 1) r t (by omega)
      (fun m hm => (hmono' m k (by omega) hk).trans_lt hrk)
      (fun m hm1 hm2 => by
        have := hnext (by omega)
        exact this.trans_le (hmono' _ _ hm1 hm2))
    rw [hev, hP']
    constructor
    · intro h
      have : Even (n - (k + 1)) := ⟨(n - (k + 1)) / 2, by show 2 * ℓ - 3 - (k + 1) = _; omega⟩
      rw [this.neg_one_pow, one_mul]
      exact mul_neg_of_neg_of_pos ha hP
    · intro h
      have : Odd (n - (k + 1)) := ⟨(n - (k + 1)) / 2, by show 2 * ℓ - 3 - (k + 1) = _; omega⟩
      rw [this.neg_one_pow]
      have : a * (-1 * P) = (-a) * P := by ring
      rw [this]
      exact mul_pos (neg_pos.2 ha) hP
  have hsignL : ∀ t, t < r 0 → 0 < (derivative L).eval t := by
    intro t ht
    obtain ⟨P, hP, hP'⟩ := sign_prod n 0 r t (by omega) (fun m hm => absurd hm (by omega))
      (fun m _ hm2 => ht.trans_le (hmono' _ _ (by omega) hm2))
    rw [hev, hP']
    have : Odd (n - 0) := ⟨ℓ - 2, by show 2 * ℓ - 3 - 0 = _; omega⟩
    rw [this.neg_one_pow]
    have : a * (-1 * P) = (-a) * P := by ring
    rw [this]
    exact mul_pos (neg_pos.2 ha) hP
  -- monotonicity facts
  have hanti : ∀ k, k < n → k % 2 = 0 → ∀ a b : ℝ, r k ≤ a → a ≤ b →
      (k + 1 < n → b ≤ r (k + 1)) → L.eval b ≤ L.eval a := by
    intro k hk he a b ha1 hab hb
    by_cases hk1 : k + 1 < n
    · have hanti : StrictAntiOn (fun t => L.eval t) (Set.Icc (r k) (r (k + 1))) := by
        refine strictAntiOn_of_deriv_neg (convex_Icc _ _) L.continuous.continuousOn ?_
        intro t ht
        rw [interior_Icc] at ht
        rw [Polynomial.deriv]
        exact (hsign t k hk ht.1 (fun _ => ht.2)).1 he
      exact hanti.antitoneOn ⟨ha1, hab.trans (hb hk1)⟩ ⟨ha1.trans hab, hb hk1⟩ hab
    · have hanti : StrictAntiOn (fun t => L.eval t) (Set.Ici (r k)) := by
        refine strictAntiOn_of_deriv_neg (convex_Ici _) L.continuous.continuousOn ?_
        intro t ht
        rw [interior_Ici] at ht
        rw [Polynomial.deriv]
        exact (hsign t k hk ht (fun h => absurd h hk1)).1 he
      exact hanti.antitoneOn (show a ∈ Set.Ici (r k) from ha1)
        (show b ∈ Set.Ici (r k) from ha1.trans hab) hab
  have hmon : ∀ k, k + 1 < n → k % 2 = 1 → ∀ a b : ℝ, r k ≤ a → a ≤ b → b ≤ r (k + 1) →
      L.eval a ≤ L.eval b := by
    intro k hk1 ho a b ha1 hab hb
    have hmon : StrictMonoOn (fun t => L.eval t) (Set.Icc (r k) (r (k + 1))) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc _ _) L.continuous.continuousOn ?_
      intro t ht
      rw [interior_Icc] at ht
      rw [Polynomial.deriv]
      exact (hsign t k (by omega) ht.1 (fun _ => ht.2)).2 ho
    exact hmon.monotoneOn ⟨ha1, hab.trans hb⟩ ⟨ha1.trans hab, hb⟩ hab
  have hleft : ∀ a b : ℝ, b ≤ r 0 → a ≤ b → L.eval a ≤ L.eval b := by
    intro a b hb hab
    have hmon : StrictMonoOn (fun t => L.eval t) (Set.Iic (r 0)) := by
      refine strictMonoOn_of_deriv_pos (convex_Iic _) L.continuous.continuousOn ?_
      intro t ht
      rw [interior_Iic] at ht
      rw [Polynomial.deriv]
      exact hsignL t ht
    exact hmon.monotoneOn (show a ∈ Set.Iic (r 0) from hab.trans hb)
      (show b ∈ Set.Iic (r 0) from hb) hab
  have hr0 : r 0 = z 0 := by
    have : 0 < 2 * i - 1 := by omega
    simp [r, this]
  have hLr : ∀ m, m < n → m % 2 = 0 →
      L.eval (r m) = if m ≤ 2 * i - 2 then 1 else 0 := by
    intro m hm he
    have hm' : m < 2 * ℓ - 3 := hm
    by_cases hA : m < 2 * i - 1
    · simp only [r, if_pos hA, if_pos he]
      rw [hval _ (by omega), if_pos (by omega), if_pos (by omega)]
    · simp only [r, if_neg hA]
      have : ¬ (m - (2 * i - 1)) % 2 = 0 := by omega
      simp only [if_neg this]
      rw [hval _ (by omega), if_neg (by omega), if_neg (by omega)]
  have hzi : z (i - 1) < z i := hz _ _ (by omega) hiℓ
  have hz0 : z 0 < z i := hz _ _ (by omega) hiℓ
  have hLzi : L.eval (z i) = 0 := by rw [hval i hiℓ]; simp
  intro t
  by_cases ht0 : t ≤ r 0
  · have h1 := hleft t (r 0) le_rfl ht0
    rw [hLr 0 (by omega) rfl, if_pos (by omega)] at h1
    rw [if_pos (by rw [hr0] at ht0; exact ht0.trans hz0.le)]
    exact h1
  push Not at ht0
  have hex : ∃ k, k < n ∧ r k < t ∧ (k + 1 < n → t ≤ r (k + 1)) := by
    have : ∀ d j, n - 1 - j = d → j < n → r j < t →
        ∃ k, k < n ∧ r k < t ∧ (k + 1 < n → t ≤ r (k + 1)) := by
      intro d
      induction d with
      | zero => intro j hj hjn hrj; exact ⟨j, hjn, hrj, fun h => by omega⟩
      | succ d ih =>
        intro j hj hjn hrj
        by_cases h : t ≤ r (j + 1)
        · exact ⟨j, hjn, hrj, fun _ => h⟩
        · exact ih (j + 1) (by omega) (by omega) (not_le.1 h)
    exact this _ 0 rfl (by omega) ht0
  obtain ⟨k, hk, hrk, hnext⟩ := hex
  have hnn : n = 2 * ℓ - 3 := rfl
  rcases Nat.mod_two_eq_zero_or_one k with he | ho
  · have hLt := hanti k hk he (r k) t le_rfl hrk.le hnext
    rw [hLr k hk he] at hLt
    by_cases hk2 : k + 2 ≤ 2 * i - 2
    · have : t ≤ z (i - 1) := (hnext (by omega)).trans (hr2 ▸ hmono' _ _ (by omega) (by omega))
      rw [if_pos (this.trans hzi.le)]
      rwa [if_pos (by omega)] at hLt
    · by_cases hk3 : k ≤ 2 * i - 2
      · by_cases hti : t ≤ z i
        · rw [if_pos hti]; rwa [if_pos hk3] at hLt
        · push Not at hti
          rw [if_neg (not_le.2 hti)]
          have hrk' : r k ≤ z i := by
            have : k = 2 * i - 2 := by omega
            rw [this, hr2]; exact hzi.le
          have := hanti k hk he (z i) t hrk' hti.le hnext
          rwa [hLzi] at this
      · have := hr_right k (by omega) hk
        rw [if_neg (not_le.2 (this.trans hrk))]
        rwa [if_neg hk3] at hLt
  · have hk1 : k + 1 < n := by omega
    have hLt := hmon k hk1 ho t (r (k + 1)) hrk.le (hnext hk1) le_rfl
    rw [hLr (k + 1) hk1 (by omega)] at hLt
    by_cases hk2 : k + 1 ≤ 2 * i - 2
    · have : t ≤ z (i - 1) := (hnext hk1).trans (hr2 ▸ hmono' _ _ hk2 (by omega))
      rw [if_pos (this.trans hzi.le)]
      rwa [if_pos hk2] at hLt
    · have := hr_right k (by omega) hk
      rw [if_neg (not_le.2 (this.trans hrk))]
      rwa [if_neg hk2] at hLt

end RQCMoments

open RQCMoments in
theorem solution (ℓ : ℕ) (hℓ : 1 < ℓ) (x : Fin ℓ → ℝ) (hx : StrictMono x) (i : Fin ℓ) :
    ∃ L : Polynomial ℝ, L.natDegree ≤ 2 * ℓ - 2 ∧
      (∀ t : ℝ, L.eval t ≤ if t ≤ x i then (1 : ℝ) else 0) ∧
      (∀ j, L.eval (x j) = if j < i then 1 else 0) ∧
      (∀ j, j ≠ i → (Polynomial.derivative L).eval (x j) = 0) ∧
      ∀ U : Polynomial ℝ, U.natDegree ≤ 2 * ℓ - 2 →
        (∀ t : ℝ, (if t ≤ x i then (1 : ℝ) else 0) ≤ U.eval t) →
        (∀ j, U.eval (x j) = if j ≤ i then 1 else 0) →
        (∀ j, j ≠ i → (Polynomial.derivative U).eval (x j) = 0) →
        L = U - (Lagrange.basis Finset.univ x i) ^ 2 := by
  obtain ⟨L, hdeg, hval, hder⟩ := exist_herm ℓ x hx i
  refine ⟨L, hdeg, ?_, hval, hder, ?_⟩
  · by_cases hi0 : i.val = 0
    · have hL : L = 0 := by
        refine uniq_herm ℓ x hx i L hdeg (fun j => ?_) hder
        rw [hval j]
        have : ¬ j < i := by rw [Fin.lt_def]; omega
        simp [this]
      intro t
      subst hL
      simp only [eval_zero]
      split_ifs <;> norm_num
    · let z : ℕ → ℝ := fun n => if h : n < ℓ then x ⟨n, h⟩ else 0
      have hzx : ∀ j : Fin ℓ, z j.val = x j := fun j => by simp [z]
      have key := main_minorant ℓ i.val (by omega) i.2 z
        (fun a b hab hb => by
          have := hx (show (⟨a, by omega⟩ : Fin ℓ) < ⟨b, hb⟩ from hab)
          simpa [z, hb, show a < ℓ by omega] using this)
        L hdeg (fun j hj => by simpa [hzx ⟨j, hj⟩, Fin.lt_def] using hval ⟨j, hj⟩)
        (fun j hj hji => by
          simpa [hzx ⟨j, hj⟩] using hder ⟨j, hj⟩ (fun h => hji (by simpa using congrArg Fin.val h)))
      intro t
      have := key t
      rwa [hzx i] at this
  · intro U hUd _ hU0 hU1
    have hb : (Lagrange.basis Finset.univ x i).natDegree = ℓ - 1 := by
      rw [Lagrange.natDegree_basis hx.injective.injOn (Finset.mem_univ i)]; simp
    have hbd : ((Lagrange.basis Finset.univ x i) ^ 2).natDegree ≤ 2 * ℓ - 2 := by
      refine (natDegree_pow_le).trans ?_; rw [hb]; omega
    have hbv : ∀ j, (Lagrange.basis Finset.univ x i).eval (x j) = if j = i then 1 else 0 := by
      intro j
      by_cases h : j = i
      · subst h; simp [Lagrange.eval_basis_self hx.injective.injOn (Finset.mem_univ j)]
      · simp [h, Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ j)]
    have := uniq_herm ℓ x hx i (L - (U - (Lagrange.basis Finset.univ x i) ^ 2))
      ((natDegree_sub_le _ _).trans (max_le hdeg ((natDegree_sub_le _ _).trans (max_le hUd hbd))))
      (fun j => by
        simp only [eval_sub, eval_pow, hval j, hU0 j, hbv j]
        by_cases h1 : j < i
        · have : j ≤ i := h1.le
          have : j ≠ i := h1.ne
          simp [h1, *]
        · by_cases h2 : j = i
          · subst h2; simp
          · have : ¬ j ≤ i := fun h => h2 (le_antisymm h (not_lt.1 h1))
            simp [h1, h2, this])
      (fun j hj => by
        simp only [derivative_sub, derivative_pow, eval_sub, eval_mul, eval_pow, hder j hj,
          hU1 j hj, hbv j, if_neg hj]
        simp)
    exact sub_eq_zero.1 this

