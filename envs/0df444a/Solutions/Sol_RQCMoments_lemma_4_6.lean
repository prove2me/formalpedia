-- Prove2me | solution 1 for RQCMoments.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T04:52:30.382361+00:00
-- url     : https://prove2.me/submissions/202d24b1-3956-437d-bca5-58cb8f25aef7

import Mathlib

set_option autoImplicit false
namespace RQCMoments
open Polynomial Finset

/-- product of prescribed powers of linear factors divides f -/
lemma prod_pow_dvd (f : ℝ[X]) (T : Finset ℝ) (m : ℝ → ℕ)
    (hm : ∀ t ∈ T, m t ≤ f.rootMultiplicity t) :
    (∏ t ∈ T, (X - C t) ^ m t) ∣ f := by
  by_cases hf : f = 0
  · simp [hf]
  refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_) (fun t ht => ?_)
  · exact (isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.2 (sub_ne_zero.2 hab))).pow
  · exact (pow_dvd_pow _ (hm t ht)).trans (pow_rootMultiplicity_dvd f t)

lemma sum_mult_le (f : ℝ[X]) (hf : f ≠ 0) (T : Finset ℝ) (m : ℝ → ℕ)
    (hm : ∀ t ∈ T, m t ≤ f.rootMultiplicity t) :
    ∑ t ∈ T, m t ≤ f.natDegree := by
  have h := prod_pow_dvd f T m hm
  have h2 := natDegree_le_of_dvd h hf
  have h3 : (∏ t ∈ T, (X - C t) ^ m t).natDegree = ∑ t ∈ T, m t := by
    rw [natDegree_prod_of_monic]
    · simp [natDegree_pow]
    · intro t _; exact (monic_X_sub_C t).pow _
  omega

lemma rolle_poly (q : ℝ[X]) (a b : ℝ) (hab : a < b) (h : q.eval a = q.eval b) :
    ∃ e, a < e ∧ e < b ∧ (derivative q).eval e = 0 := by
  obtain ⟨c, hc, hc2⟩ := exists_deriv_eq_zero hab q.continuousOn h
  exact ⟨c, hc.1, hc.2, by rwa [← Polynomial.deriv]⟩

lemma slope_poly (q : ℝ[X]) (a b : ℝ) (hab : a < b) :
    ∃ e, a < e ∧ e < b ∧ (derivative q).eval e = (q.eval b - q.eval a) / (b - a) := by
  obtain ⟨c, hc, hc2⟩ := exists_deriv_eq_slope (fun x => q.eval x) hab q.continuousOn
    (fun x _ => q.differentiableAt.differentiableWithinAt)
  exact ⟨c, hc.1, hc.2, by rwa [Polynomial.deriv] at hc2⟩

lemma pos_of_noroot_right (q : ℝ[X]) (a : ℝ) (h0 : 0 < q.eval a)
    (hr : ∀ t, a ≤ t → q.eval t ≠ 0) : ∀ t, a ≤ t → 0 < q.eval t := by
  intro t ht
  by_contra hneg
  have hneg : q.eval t ≤ 0 := not_lt.1 hneg
  obtain ⟨c, hc, hc2⟩ := intermediate_value_Icc' ht q.continuousOn ⟨hneg, h0.le⟩
  exact hr c hc.1 hc2

lemma neg_of_noroot_left (q : ℝ[X]) (b : ℝ) (h0 : q.eval b < 0)
    (hr : ∀ t, t ≤ b → q.eval t ≠ 0) : ∀ t, t ≤ b → q.eval t < 0 := by
  intro t ht
  by_contra hneg
  have hneg : 0 ≤ q.eval t := not_lt.1 hneg
  obtain ⟨c, hc, hc2⟩ := intermediate_value_Icc' ht q.continuousOn ⟨h0.le, hneg⟩
  exact hr c hc.2 hc2


structure Setup (n i : ℕ) (xs : ℕ → ℝ) (U : ℝ[X]) : Prop where
  hi : i < n
  mono : ∀ a b, a < b → b ≤ n → xs a < xs b
  deg : U.natDegree ≤ 2 * n
  val : ∀ j ≤ n, U.eval (xs j) = if j ≤ i then 1 else 0
  der : ∀ j ≤ n, j ≠ i → (derivative U).eval (xs j) = 0

lemma Setup.deriv_ne_zero {n i : ℕ} {xs : ℕ → ℝ} {U : ℝ[X]} (h : Setup n i xs U) :
    derivative U ≠ 0 := by
  intro h0
  have hc := eq_C_of_derivative_eq_zero h0
  have h1 := h.val 0 (by have := h.hi; omega)
  have h2 := h.val n le_rfl
  rw [hc] at h1 h2
  simp only [eval_C] at h1 h2
  have := h.hi
  rw [if_pos (Nat.zero_le _)] at h1
  rw [if_neg (by omega)] at h2
  rw [h1] at h2
  exact one_ne_zero h2

lemma Setup.root_structure {n i : ℕ} {xs : ℕ → ℝ} {U : ℝ[X]} (h : Setup n i xs U) :
    ∃ ρ : ℕ → ℝ, (∀ k < n, k ≠ i → xs k < ρ k ∧ ρ k < xs (k + 1) ∧
        (derivative U).eval (ρ k) = 0) ∧
      (∀ s, (derivative U).eval s = 0 →
        (∃ j ≤ n, j ≠ i ∧ s = xs j) ∨ (∃ k < n, k ≠ i ∧ s = ρ k)) ∧
      (∀ s, (derivative U).rootMultiplicity s ≤ 1) := by
  classical
  have hi := h.hi
  have hne := h.deriv_ne_zero
  have hd : (derivative U).natDegree ≤ 2 * n - 1 := by
    have := natDegree_derivative_le U
    have := h.deg
    omega
  have hex : ∀ k, ∃ y, k < n → k ≠ i → xs k < y ∧ y < xs (k + 1) ∧ (derivative U).eval y = 0 := by
    intro k
    by_cases hk : k < n ∧ k ≠ i
    · obtain ⟨hk1, hk2⟩ := hk
      have hv : U.eval (xs k) = U.eval (xs (k + 1)) := by
        rw [h.val k hk1.le, h.val (k + 1) hk1]
        by_cases hki : k < i
        · rw [if_pos hki.le, if_pos (by omega)]
        · rw [if_neg (by omega), if_neg (by omega)]
      obtain ⟨e, he1, he2, he3⟩ := rolle_poly U _ _ (h.mono k (k + 1) (by omega) hk1) hv
      exact ⟨e, fun _ _ => ⟨he1, he2, he3⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose ρ hρ using hex
  have hρlt : ∀ k k', k < k' → k' < n → k ≠ i → k' ≠ i → ρ k < ρ k' := by
    intro k k' hkk hk' hki hk'i
    have a1 := (hρ k (by omega) hki).2.1
    have a2 := (hρ k' hk' hk'i).1
    have a3 : xs (k + 1) ≤ xs k' := by
      rcases Nat.eq_or_lt_of_le (show k + 1 ≤ k' by omega) with e | e
      · rw [e]
      · exact (h.mono _ _ e hk'.le).le
    linarith
  have hdisj : ∀ j k, j ≤ n → k < n → k ≠ i → xs j ≠ ρ k := by
    intro j k hj hk hki he
    have a1 := (hρ k hk hki).1
    have a2 := (hρ k hk hki).2.1
    rcases le_or_gt j k with c | c
    · rcases Nat.eq_or_lt_of_le c with e | e
      · rw [e] at he; linarith
      · have := h.mono _ _ e hk.le; linarith
    · rcases Nat.eq_or_lt_of_le (show k + 1 ≤ j by omega) with e | e
      · rw [← e] at he; linarith
      · have := h.mono _ _ e hj; linarith
  set A := ((range (n + 1)).erase i).image xs with hA
  set B := ((range n).erase i).image ρ with hB
  have hAc : A.card = n := by
    rw [hA, card_image_of_injOn, card_erase_of_mem (by simp; omega)]
    · simp
    · intro a ha b hb hab
      simp only [coe_erase, Set.mem_sdiff, mem_coe, mem_range] at ha hb
      by_contra hne
      rcases lt_or_gt_of_ne hne with c | c
      · have := h.mono a b c (by omega); linarith
      · have := h.mono b a c (by omega); linarith
  have hBc : B.card = n - 1 := by
    rw [hB, card_image_of_injOn, card_erase_of_mem (by simp; omega)]
    · simp
    · intro a ha b hb hab
      simp only [coe_erase, Set.mem_sdiff, mem_coe, mem_range, Set.mem_singleton_iff] at ha hb
      by_contra hne
      rcases lt_or_gt_of_ne hne with c | c
      · have := hρlt a b c hb.1 ha.2 hb.2; linarith
      · have := hρlt b a c ha.1 hb.2 ha.2; linarith
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro s hsA hsB
    simp only [hA, hB, mem_image, mem_erase, mem_range] at hsA hsB
    obtain ⟨j, ⟨_, hj⟩, rfl⟩ := hsA
    obtain ⟨k, ⟨hki, hk⟩, hk2⟩ := hsB
    exact hdisj j k (by omega) hk hki hk2.symm
  set T0 := A ∪ B with hT0
  have hT0c : T0.card = 2 * n - 1 := by
    rw [hT0, card_union_of_disjoint hAB, hAc, hBc]; omega
  have hT0root : ∀ t ∈ T0, (derivative U).eval t = 0 := by
    intro t ht
    simp only [hT0, hA, hB, mem_union, mem_image, mem_erase, mem_range] at ht
    rcases ht with ⟨j, ⟨hj1, hj2⟩, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩
    · exact h.der j (by omega) hj1
    · exact (hρ k hk2 hk1).2.2
  have hT0mult : ∀ t ∈ T0, 1 ≤ (derivative U).rootMultiplicity t := fun t ht =>
    (rootMultiplicity_pos hne).2 (hT0root t ht)
  have hwhere : ∀ s, (derivative U).eval s = 0 → s ∈ T0 := by
    intro s hs
    by_contra hnot
    have := sum_mult_le (derivative U) hne (insert s T0) (fun _ => 1) (by
      intro t ht
      rcases mem_insert.1 ht with rfl | ht
      · exact (rootMultiplicity_pos hne).2 hs
      · exact hT0mult t ht)
    rw [sum_const, smul_eq_mul, mul_one, card_insert_of_notMem hnot, hT0c] at this
    omega
  refine ⟨ρ, fun k hk hki => hρ k hk hki, ?_, ?_⟩
  · intro s hs
    have := hwhere s hs
    simp only [hT0, hA, hB, mem_union, mem_image, mem_erase, mem_range] at this
    rcases this with ⟨j, ⟨hj1, hj2⟩, rfl⟩ | ⟨k, ⟨hk1, hk2⟩, rfl⟩
    · exact Or.inl ⟨j, by omega, hj1, rfl⟩
    · exact Or.inr ⟨k, hk2, hk1, rfl⟩
  · intro s
    by_contra hbig
    have hbig : 2 ≤ (derivative U).rootMultiplicity s := by omega
    have hs : (derivative U).eval s = 0 := by
      by_contra hn0
      rw [rootMultiplicity_eq_zero hn0] at hbig; omega
    have hsT := hwhere s hs
    have := sum_mult_le (derivative U) hne T0 (fun t => if t = s then 2 else 1) (by
      intro t ht
      by_cases hts : t = s
      · subst hts; simpa using hbig
      · simp only [hts, if_false]; exact hT0mult t ht)
    have hsum : ∑ t ∈ T0, (if t = s then 2 else 1) = T0.card + 1 := by
      have : ∀ t ∈ T0, (if t = s then 2 else 1) = 1 + (if t = s then 1 else 0) := by
        intro t _; by_cases hts : t = s <;> simp [hts]
      rw [sum_congr rfl this, sum_add_distrib, sum_const, smul_eq_mul, mul_one,
        sum_ite_eq' T0 s (fun _ => 1)]
      simp [hsT]
    rw [hsum, hT0c] at this
    omega


lemma Setup.xs_le {n i : ℕ} {xs : ℕ → ℝ} {U : ℝ[X]} (h : Setup n i xs U) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ n) : xs a ≤ xs b := by
  rcases Nat.eq_or_lt_of_le hab with e | e
  · rw [e]
  · exact (h.mono _ _ e hb).le

lemma Setup.gap_all {n i : ℕ} {xs : ℕ → ℝ} {U : ℝ[X]} (h : Setup n i xs U) :
    ∃ ρ : ℕ → ℝ, ∀ a < n, ∀ s, xs a < s → s < xs (a + 1) → (derivative U).eval s = 0 →
      a ≠ i ∧ s = ρ a := by
  obtain ⟨ρ, h1, h2, -⟩ := h.root_structure
  refine ⟨ρ, fun a ha s hs1 hs2 hs => ?_⟩
  rcases h2 s hs with ⟨j, hj, hji, rfl⟩ | ⟨k, hk, hki, rfl⟩
  · exfalso
    rcases le_or_gt j a with c | c
    · have := h.xs_le c ha.le; linarith
    · have := h.xs_le (show a + 1 ≤ j by omega) hj; linarith
  · obtain ⟨b1, b2, -⟩ := h1 k hk hki
    have hka : k = a := by
      rcases lt_trichotomy k a with c | c | c
      · exfalso
        have := h.xs_le (show k + 1 ≤ a by omega) ha.le; linarith
      · exact c
      · exfalso
        have := h.xs_le (show a + 1 ≤ k by omega) hk.le; linarith
    subst hka
    exact ⟨hki, rfl⟩

lemma Setup.out_nonroot {n i : ℕ} {xs : ℕ → ℝ} {U : ℝ[X]} (h : Setup n i xs U) :
    (∀ s, (derivative U).eval s = 0 → xs 0 ≤ s ∧ s ≤ xs n) ∧
      (derivative U).eval (xs i) ≠ 0 := by
  obtain ⟨ρ, h1, h2, -⟩ := h.root_structure
  have hi := h.hi
  have hout : ∀ s, (derivative U).eval s = 0 → xs 0 ≤ s ∧ s ≤ xs n := by
    intro s hs
    rcases h2 s hs with ⟨j, hj, hji, rfl⟩ | ⟨k, hk, hki, rfl⟩
    · exact ⟨h.xs_le (Nat.zero_le _) hj, h.xs_le hj le_rfl⟩
    · obtain ⟨b1, b2, -⟩ := h1 k hk hki
      exact ⟨by have := h.xs_le (Nat.zero_le k) hk.le; linarith,
        by have := h.xs_le (show k + 1 ≤ n by omega) le_rfl; linarith⟩
  refine ⟨hout, fun hs => ?_⟩
  rcases h2 _ hs with ⟨j, hj, hji, he⟩ | ⟨k, hk, hki, he⟩
  · rcases lt_or_gt_of_ne hji with c | c
    · have := h.mono _ _ c hi.le; linarith
    · have := h.mono _ _ c hj; linarith
  · obtain ⟨b1, b2, -⟩ := h1 k hk hki
    rcases lt_or_gt_of_ne hki with c | c
    · have := h.xs_le (show k + 1 ≤ i by omega) hi.le; linarith
    · have := h.xs_le (show i ≤ k by omega) hk.le; linarith

lemma Setup.left_roots {n i : ℕ} {xs : ℕ → ℝ} {U : ℝ[X]} (h : Setup n i xs U) :
    ∀ r, r < xs i → (U - 1).eval r = 0 → ∃ k < i, r = xs k := by
  classical
  intro r hr hAr
  by_contra hno
  push Not at hno
  have hi := h.hi
  obtain ⟨ρ, hρ⟩ := h.gap_all
  obtain ⟨hout, -⟩ := h.out_nonroot
  have hA : ∀ j ≤ i, (U - 1).eval (xs j) = 0 := by
    intro j hj
    rw [eval_sub, h.val j (by omega), if_pos hj]; simp
  have hAr' : U.eval r = 1 := by simpa [sub_eq_zero] using hAr
  have hd : derivative (U - 1) = derivative U := by simp
  rcases lt_or_ge r (xs 0) with c | c
  · obtain ⟨e, he1, he2, he3⟩ := rolle_poly (U - 1) r (xs 0) c (by rw [hAr, hA 0 (Nat.zero_le _)])
    rw [hd] at he3
    have := (hout e he3).1; linarith
  · have c : xs 0 < r := lt_of_le_of_ne c (fun e => hno 0 (by rcases Nat.eq_zero_or_pos i with h0 | h0 <;> [(subst h0; rw [← e] at hr; linarith); exact h0]) e.symm)
    have P0 : (fun k => xs k < r) 0 := c
    set m := Nat.findGreatest (fun k => xs k < r) i with hm
    have hm1 : xs m < r := Nat.findGreatest_spec (P := fun k => xs k < r) (Nat.zero_le _) P0
    have hm2 : m ≤ i := Nat.findGreatest_le i
    have hmi : m ≠ i := by
      intro e; rw [e] at hm1; linarith
    have hmi : m < i := by omega
    have hm3 : r ≤ xs (m + 1) := by
      have := Nat.findGreatest_is_greatest (P := fun k => xs k < r) (n := i)
        (show m < m + 1 by omega) (by omega)
      exact not_lt.1 this
    have hm4 : r < xs (m + 1) := by
      refine lt_of_le_of_ne hm3 (fun e => ?_)
      by_cases hmm : m + 1 = i
      · rw [hmm] at e; linarith
      · exact hno (m + 1) (by omega) e
    obtain ⟨e1, a1, a2, a3⟩ := rolle_poly (U - 1) (xs m) r hm1
      (by rw [hA m hmi.le, hAr])
    obtain ⟨e2, b1, b2, b3⟩ := rolle_poly (U - 1) r (xs (m + 1)) hm4
      (by rw [hA (m + 1) (by omega), hAr])
    rw [hd] at a3 b3
    obtain ⟨-, k1⟩ := hρ m (by omega) e1 a1 (by linarith) a3
    obtain ⟨-, k2⟩ := hρ m (by omega) e2 (by linarith) b2 b3
    linarith

lemma Setup.right_roots {n i : ℕ} {xs : ℕ → ℝ} {U : ℝ[X]} (h : Setup n i xs U) :
    ∀ r, xs i < r → U.eval r = 0 → ∃ j, i < j ∧ j ≤ n ∧ r = xs j := by
  classical
  intro r hr hUr
  by_contra hno
  push Not at hno
  have hi := h.hi
  obtain ⟨ρ, hρ⟩ := h.gap_all
  obtain ⟨hout, -⟩ := h.out_nonroot
  have hU : ∀ j ≤ n, i < j → U.eval (xs j) = 0 := by
    intro j hj hij
    rw [h.val j hj, if_neg (by omega)]
  have P0 : (fun k => xs k < r) i := hr
  set m := Nat.findGreatest (fun k => xs k < r) n with hm
  have hm1 : xs m < r := Nat.findGreatest_spec (P := fun k => xs k < r) hi.le P0
  have hm2 : m ≤ n := Nat.findGreatest_le n
  have hm0 : i ≤ m := Nat.le_findGreatest (P := fun k => xs k < r) hi.le P0
  rcases Nat.eq_or_lt_of_le hm2 with e | e
  · rw [e] at hm1
    obtain ⟨e1, a1, a2, a3⟩ := rolle_poly U (xs n) r hm1 (by rw [hU n le_rfl hi, hUr])
    have := (hout e1 a3).2; linarith
  · have hm3 : r ≤ xs (m + 1) := by
      have := Nat.findGreatest_is_greatest (P := fun k => xs k < r) (n := n)
        (show m < m + 1 by omega) (by omega)
      exact not_lt.1 this
    have hm4 : r < xs (m + 1) := lt_of_le_of_ne hm3 (fun e => hno (m + 1) (by omega) (by omega) e)
    obtain ⟨e2, b1, b2, b3⟩ := rolle_poly U r (xs (m + 1)) hm4
      (by rw [hU (m + 1) (by omega) (by omega), hUr])
    rcases Nat.eq_or_lt_of_le hm0 with e0 | e0
    · obtain ⟨hne, -⟩ := hρ m e e2 (by rw [← e0]; linarith) b2 b3
      exact hne e0.symm
    · obtain ⟨e1, a1, a2, a3⟩ := rolle_poly U (xs m) r hm1
        (by rw [hU m hm2 e0, hUr])
      obtain ⟨-, k1⟩ := hρ m e e1 a1 (by linarith) a3
      obtain ⟨-, k2⟩ := hρ m e e2 (by linarith) b2 b3
      linarith


lemma triple_mult (F G W : ℝ[X]) (a : ℝ) (hF : F ≠ 0) (hFGW : F = G * W)
    (hG : (X - C a) ^ 2 ∣ G) (hW : W.eval a = 0) : 3 ≤ F.rootMultiplicity a := by
  rw [le_rootMultiplicity_iff hF, hFGW]
  have h1 : (X - C a) ∣ W := dvd_iff_isRoot.2 hW
  have := mul_dvd_mul hG h1
  rwa [← pow_succ] at this

lemma deriv_mult (F : ℝ[X]) (a : ℝ) (h3 : 3 ≤ F.rootMultiplicity a) :
    2 ≤ (derivative F).rootMultiplicity a := by
  have hF : F ≠ 0 := by
    intro h0; rw [h0, rootMultiplicity_zero] at h3; omega
  have hr : F.IsRoot a := (rootMultiplicity_pos hF).1 (by omega)
  rw [derivative_rootMultiplicity_of_root hr]; omega

lemma Setup.left_ge {n i : ℕ} {xs : ℕ → ℝ} {U : ℝ[X]} (h : Setup n i xs U) :
    ∀ t, t ≤ xs i → 1 ≤ U.eval t := by
  classical
  have hi := h.hi
  obtain ⟨ρ, hρ⟩ := h.gap_all
  obtain ⟨hout, hnode⟩ := h.out_nonroot
  obtain ⟨-, -, -, hsimple⟩ := h.root_structure
  have hd : derivative (U - 1) = derivative U := by simp
  have hA : ∀ j ≤ i, (U - 1).eval (xs j) = 0 := by
    intro j hj
    rw [eval_sub, h.val j (by omega), if_pos hj]; simp
  have hA0 : U - 1 ≠ 0 := by
    intro h0
    have := h.val n le_rfl
    have h2 : (U - 1).eval (xs n) = 0 := by rw [h0]; simp
    rw [eval_sub, this, if_neg (by omega)] at h2
    simp at h2
  have hinj : ∀ a b, a ≤ n → b ≤ n → xs a = xs b → a = b := by
    intro a b ha hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with c | c
    · have := h.mono a b c hb; linarith
    · have := h.mono b a c ha; linarith
  set m : ℝ → ℕ := fun t => if t = xs i then 1 else 2 with hmdef
  set T := (range (i + 1)).image xs with hT
  have hdvd := prod_pow_dvd (U - 1) T m (by
    intro t ht
    simp only [hT, mem_image, mem_range] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    by_cases hki : k = i
    · subst hki
      simp only [hmdef, if_true]
      exact (rootMultiplicity_pos hA0).2 (hA k le_rfl)
    · have : xs k ≠ xs i := fun e => hki (hinj _ _ (by omega) (by omega) e)
      simp only [hmdef, if_neg this]
      exact (one_lt_rootMultiplicity_iff_isRoot hA0).2 ⟨hA k (by omega), by
        rw [hd]; exact h.der k (by omega) hki⟩)
  obtain ⟨W, hW⟩ := hdvd
  set G := ∏ t ∈ T, (X - C t) ^ m t with hG
  have hGeval : ∀ t, G.eval t = ∏ s ∈ T, (t - s) ^ m s := by
    intro t; rw [hG, eval_prod]; simp
  have hxsiT : xs i ∈ T := mem_image.2 ⟨i, by simp, rfl⟩
  have hG1 : ∀ t, t ≤ xs i → G.eval t ≤ 0 := by
    intro t ht
    rw [hGeval, ← Finset.mul_prod_erase T _ hxsiT]
    apply mul_nonpos_of_nonpos_of_nonneg
    · simp only [hmdef, if_true, pow_one]; linarith
    · apply Finset.prod_nonneg
      intro s hs
      rw [mem_erase] at hs
      simp only [hmdef, if_neg hs.1]
      exact sq_nonneg _
  have hG2 : 0 < G.eval (xs (i + 1)) := by
    rw [hGeval]
    apply Finset.prod_pos
    intro s hs
    simp only [hT, mem_image, mem_range] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact pow_pos (by have := h.mono k (i + 1) (by omega) (by omega); linarith) _
  have hW0 : (W.eval (xs (i + 1))) < 0 := by
    have h1 := congrArg (fun p => p.eval (xs (i + 1))) hW
    simp only [eval_mul] at h1
    rw [eval_sub, h.val (i + 1) (by omega), if_neg (by omega)] at h1
    simp only [eval_one] at h1
    by_contra hc
    have : 0 ≤ G.eval (xs (i + 1)) * W.eval (xs (i + 1)) :=
      mul_nonneg hG2.le (not_lt.1 hc)
    linarith
  have hWne : ∀ t, t ≤ xs (i + 1) → W.eval t ≠ 0 := by
    intro t ht hWt
    have hAt : (U - 1).eval t = 0 := by
      have h1 := congrArg (fun p => p.eval t) hW
      simp only [eval_mul] at h1
      rw [h1, hWt, mul_zero]
    rcases lt_trichotomy t (xs i) with c | c | c
    · obtain ⟨k, hk, rfl⟩ := h.left_roots t c hAt
      have hkT : xs k ∈ T := by simp only [hT, mem_image, mem_range]; exact ⟨k, by omega, rfl⟩
      have hk2 : xs k ≠ xs i := fun e => by have := hinj _ _ (by omega) (by omega) e; omega
      have hdv : (X - C (xs k)) ^ 2 ∣ G := by
        have := Finset.dvd_prod_of_mem (fun t => (X - C t) ^ m t) hkT
        have hm : m (xs k) = 2 := by simp [hmdef, hk2]
        simp only [hm] at this
        exact this
      have h3 := triple_mult (U - 1) G W (xs k) hA0 hW hdv hWt
      have h4 := deriv_mult _ _ h3
      rw [hd] at h4
      have := hsimple (xs k); omega
    · subst c
      have hdv : (X - C (xs i)) ^ 2 ∣ U - 1 := by
        rw [hW]
        have h1 := Finset.dvd_prod_of_mem (fun t => (X - C t) ^ m t) hxsiT
        have hm : m (xs i) = 1 := by simp [hmdef]
        simp only [hm, pow_one] at h1
        have h2 : (X - C (xs i)) ∣ W := dvd_iff_isRoot.2 hWt
        have := mul_dvd_mul h1 h2
        rw [← pow_two] at this
        exact this
      have h2 : 2 ≤ (U - 1).rootMultiplicity (xs i) := (le_rootMultiplicity_iff hA0).2 hdv
      have := ((one_lt_rootMultiplicity_iff_isRoot hA0).1 h2).2
      rw [IsRoot, hd] at this
      exact hnode this
    · have hU1 : U.eval t = 1 := by
        have := hAt; simp only [eval_sub, eval_one, sub_eq_zero] at this; exact this
      obtain ⟨e, e1, e2, e3⟩ := rolle_poly U (xs i) t c (by rw [hU1, h.val i hi.le]; simp)
      have := (hρ i hi e e1 (by
        rcases Nat.eq_or_lt_of_le (show i + 1 ≤ n by omega) with _ | _ <;>
          linarith [h.mono i (i + 1) (by omega) (by omega)]) e3).1
      exact this rfl
  have hWneg := neg_of_noroot_left W (xs (i + 1)) hW0 hWne
  intro t ht
  have h1 := congrArg (fun p => p.eval t) hW
  simp only [eval_mul, eval_sub, eval_one] at h1
  have h2 : 0 ≤ G.eval t * W.eval t :=
    mul_nonneg_of_nonpos_of_nonpos (hG1 t ht)
      (hWneg t (by have := h.mono i (i + 1) (by omega) (by omega); linarith)).le
  linarith


lemma Setup.right_nonneg {n i : ℕ} {xs : ℕ → ℝ} {U : ℝ[X]} (h : Setup n i xs U) :
    ∀ t, xs i ≤ t → 0 ≤ U.eval t := by
  classical
  have hi := h.hi
  obtain ⟨-, -, -, hsimple⟩ := h.root_structure
  have hU0 : U ≠ 0 := by
    intro h0
    have := h.val 0 (by omega)
    rw [h0, if_pos (Nat.zero_le _)] at this
    simp at this
  have hinj : ∀ a b, a ≤ n → b ≤ n → xs a = xs b → a = b := by
    intro a b ha hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with c | c
    · have := h.mono a b c hb; linarith
    · have := h.mono b a c ha; linarith
  set T := (Ioc i n).image xs with hT
  have hdvd := prod_pow_dvd U T (fun _ => 2) (by
    intro t ht
    simp only [hT, mem_image, mem_Ioc] at ht
    obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := ht
    exact (one_lt_rootMultiplicity_iff_isRoot hU0).2 ⟨by
      rw [IsRoot, h.val k hk2, if_neg (by omega)], h.der k hk2 (by omega)⟩)
  obtain ⟨V, hV⟩ := hdvd
  set P := ∏ t ∈ T, (X - C t) ^ 2 with hP
  have hPeval : ∀ t, P.eval t = ∏ s ∈ T, (t - s) ^ 2 := by
    intro t; rw [hP, eval_prod]; simp
  have hP0 : ∀ t, 0 ≤ P.eval t := fun t => by
    rw [hPeval]; exact Finset.prod_nonneg (fun s _ => sq_nonneg _)
  have hP1 : 0 < P.eval (xs i) := by
    rw [hPeval]
    apply Finset.prod_pos
    intro s hs
    simp only [hT, mem_image, mem_Ioc] at hs
    obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := hs
    have : xs i - xs k ≠ 0 := by have := h.mono i k hk1 hk2; linarith
    positivity
  have hV0 : 0 < V.eval (xs i) := by
    have h1 := congrArg (fun p => p.eval (xs i)) hV
    simp only [eval_mul] at h1
    rw [h.val i hi.le, if_pos le_rfl] at h1
    by_contra hc
    have : P.eval (xs i) * V.eval (xs i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP1.le (not_lt.1 hc)
    linarith
  have hVne : ∀ t, xs i ≤ t → V.eval t ≠ 0 := by
    intro t ht hVt
    rcases eq_or_lt_of_le ht with c | c
    · subst c; exact hV0.ne' hVt
    · have hUt : U.eval t = 0 := by
        have h1 := congrArg (fun p => p.eval t) hV
        simp only [eval_mul] at h1
        rw [h1, hVt, mul_zero]
      obtain ⟨j, hj1, hj2, rfl⟩ := h.right_roots t c hUt
      have hjT : xs j ∈ T := by simp only [hT, mem_image, mem_Ioc]; exact ⟨j, ⟨hj1, hj2⟩, rfl⟩
      have hdv : (X - C (xs j)) ^ 2 ∣ P := by
        have := Finset.dvd_prod_of_mem (fun t => (X - C t) ^ 2) hjT
        exact this
      have h3 := triple_mult U P V (xs j) hU0 hV hdv hVt
      have h4 := deriv_mult _ _ h3
      have := hsimple (xs j); omega
  have hVpos := pos_of_noroot_right V (xs i) hV0 hVne
  intro t ht
  have h1 := congrArg (fun p => p.eval t) hV
  simp only [eval_mul] at h1
  rw [h1]
  exact mul_nonneg (hP0 t) (hVpos t ht).le


lemma exists_hermite (n i : ℕ) (xs : ℕ → ℝ) (hi : i < n)
    (mono : ∀ a b, a < b → b ≤ n → xs a < xs b) : ∃ U : ℝ[X], Setup n i xs U := by
  classical
  let δ : Fin n → ℕ := fun b => if b.val < i then b.val else b.val + 1
  let Φ : degreeLT ℝ (2 * n + 1) →ₗ[ℝ] (Fin (n + 1) ⊕ Fin n → ℝ) :=
    { toFun := fun p => Sum.elim (fun a => (p : ℝ[X]).eval (xs a))
        (fun b => (derivative (p : ℝ[X])).eval (xs (δ b)))
      map_add' := by
        intro p q; ext a; cases a <;> simp
      map_smul' := by
        intro c p; ext a; cases a <;> simp }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    by_contra hp0
    have hp0' : (p : ℝ[X]) ≠ 0 := fun e => hp0 (Subtype.ext e)
    have hv : ∀ a, a ≤ n → (p : ℝ[X]).eval (xs a) = 0 := by
      intro a ha
      have := congrFun hp (Sum.inl ⟨a, by omega⟩)
      simpa [Φ] using this
    have hdv : ∀ a, a ≤ n → a ≠ i → (derivative (p : ℝ[X])).eval (xs a) = 0 := by
      intro a ha hai
      have := congrFun hp (Sum.inr ⟨if a < i then a else a - 1, by split_ifs <;> omega⟩)
      have e : δ ⟨if a < i then a else a - 1, by split_ifs <;> omega⟩ = a := by
        simp only [δ]; split_ifs <;> omega
      simpa [Φ, e] using this
    have hinjx : ∀ a b, a ≤ n → b ≤ n → xs a = xs b → a = b := by
      intro a b ha hb hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with c | c
      · have := mono a b c hb; linarith
      · have := mono b a c ha; linarith
    set m : ℝ → ℕ := fun t => if t = xs i then 1 else 2 with hmdef
    have hsum := sum_mult_le (p : ℝ[X]) hp0' ((range (n + 1)).image xs) m (by
      intro t ht
      simp only [mem_image, mem_range] at ht
      obtain ⟨k, hk, rfl⟩ := ht
      by_cases hki : k = i
      · subst hki
        simp only [hmdef, if_true]
        exact (rootMultiplicity_pos hp0').2 (hv k (by omega))
      · have : xs k ≠ xs i := fun e => hki (hinjx _ _ (by omega) (by omega) e)
        simp only [hmdef, if_neg this]
        exact (one_lt_rootMultiplicity_iff_isRoot hp0').2 ⟨hv k (by omega), hdv k (by omega) hki⟩)
    rw [sum_image (fun a ha b hb hab => hinjx a b (by simp at ha; omega) (by simp at hb; omega) hab)] at hsum
    have hs2 : ∑ a ∈ range (n + 1), m (xs a) = 2 * n + 1 := by
      rw [← Finset.add_sum_erase _ _ (show i ∈ range (n + 1) by simp; omega)]
      have : ∀ a ∈ (range (n + 1)).erase i, m (xs a) = 2 := by
        intro a ha
        rw [mem_erase] at ha
        have : xs a ≠ xs i := fun e => ha.1 (hinjx _ _ (by have := ha.2; simp at this; omega) (by omega) e)
        simp [hmdef, this]
      rw [sum_congr rfl this]
      simp [hmdef]
      rw [card_erase_of_mem (by simp; omega)]
      simp; omega
    have hdeg := mem_degreeLT.1 p.2
    have : (p : ℝ[X]).natDegree < 2 * n + 1 := by
      rw [natDegree_lt_iff_degree_lt hp0']; exact_mod_cast hdeg
    omega
  have hfr : Module.finrank ℝ (degreeLT ℝ (2 * n + 1)) = Module.finrank ℝ (Fin (n + 1) ⊕ Fin n → ℝ) := by
    rw [(degreeLTEquiv ℝ (2 * n + 1)).finrank_eq]
    simp; omega
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  obtain ⟨p, hp⟩ := hsurj (Sum.elim (fun a => if (a : ℕ) ≤ i then (1 : ℝ) else 0) (fun _ => 0))
  have hv : ∀ a, a ≤ n → (p : ℝ[X]).eval (xs a) = if a ≤ i then 1 else 0 := by
    intro a ha
    have := congrFun hp (Sum.inl ⟨a, by omega⟩)
    simpa [Φ] using this
  have hdv : ∀ a, a ≤ n → a ≠ i → (derivative (p : ℝ[X])).eval (xs a) = 0 := by
    intro a ha hai
    have := congrFun hp (Sum.inr ⟨if a < i then a else a - 1, by split_ifs <;> omega⟩)
    have e : δ ⟨if a < i then a else a - 1, by split_ifs <;> omega⟩ = a := by
      simp only [δ]; split_ifs <;> omega
    simpa [Φ, e] using this
  refine ⟨p, ⟨hi, mono, ?_, hv, hdv⟩⟩
  have hdeg := mem_degreeLT.1 p.2
  by_cases hp0 : (p : ℝ[X]) = 0
  · rw [hp0]; simp
  · have : (p : ℝ[X]).natDegree < 2 * n + 1 := by
      rw [natDegree_lt_iff_degree_lt hp0]; exact_mod_cast hdeg
    omega


theorem lemma_4_6_aux (ℓ : ℕ) (hℓ : 1 < ℓ) (x : Fin ℓ → ℝ) (hx : StrictMono x) (i : Fin ℓ) :
    ∃ U : Polynomial ℝ, U.natDegree ≤ 2 * ℓ - 2 ∧
      (∀ t : ℝ, (if t ≤ x i then (1 : ℝ) else 0) ≤ U.eval t) ∧
      (∀ j, U.eval (x j) = if j ≤ i then 1 else 0) ∧
      (∀ j, j ≠ i → (Polynomial.derivative U).eval (x j) = 0) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, by omega⟩
  by_cases hin : i.val = n
  · refine ⟨1, by simp, ?_, ?_, by simp⟩
    · intro t; simp only [eval_one]; split_ifs <;> norm_num
    · intro j
      have : j ≤ i := by rw [Fin.le_def]; have := j.2; omega
      simp [this]
  · have hi : i.val < n := by have := i.2; omega
    let xs : ℕ → ℝ := fun j => x ⟨min j n, by omega⟩
    have hxs : ∀ j (hj : j ≤ n), xs j = x ⟨j, by omega⟩ := by
      intro j hj; simp only [xs]; congr 2; omega
    obtain ⟨U, hU⟩ := exists_hermite n i.val xs hi (by
      intro a b hab hb
      rw [hxs a (by omega), hxs b hb]
      exact hx (by rw [Fin.lt_def]; exact hab))
    have hxj : ∀ j : Fin (n + 1), x j = xs j.val := by
      intro j; rw [hxs j.val (by omega)]
    refine ⟨U, by have := hU.deg; omega, ?_, ?_, ?_⟩
    · intro t
      rw [hxj i]
      by_cases ht : t ≤ xs i.val
      · rw [if_pos ht]; exact hU.left_ge t ht
      · rw [if_neg ht]; exact hU.right_nonneg t (not_le.1 ht).le
    · intro j
      rw [hxj j, hU.val j.val (by have := j.2; omega)]
      by_cases hji : j ≤ i
      · rw [if_pos (Fin.le_def.1 hji), if_pos hji]
      · rw [if_neg (fun e => hji (Fin.le_def.2 e)), if_neg hji]
    · intro j hj
      rw [hxj j]
      exact hU.der j.val (by have := j.2; omega) (fun e => hj (Fin.ext e))

end RQCMoments

theorem solution (ℓ : ℕ) (hℓ : 1 < ℓ) (x : Fin ℓ → ℝ) (hx : StrictMono x) (i : Fin ℓ) :
    ∃ U : Polynomial ℝ, U.natDegree ≤ 2 * ℓ - 2 ∧
      (∀ t : ℝ, (if t ≤ x i then (1 : ℝ) else 0) ≤ U.eval t) ∧
      (∀ j, U.eval (x j) = if j ≤ i then 1 else 0) ∧
      (∀ j, j ≠ i → (Polynomial.derivative U).eval (x j) = 0) :=
  RQCMoments.lemma_4_6_aux ℓ hℓ x hx i
