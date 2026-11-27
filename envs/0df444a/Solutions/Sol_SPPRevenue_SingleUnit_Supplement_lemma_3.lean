-- Prove2me | solution 1 for SPPRevenue.SingleUnit.Supplement.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:11:52.963898+00:00
-- url     : https://prove2.me/submissions/09b71190-e45e-4b8e-8713-b0dd3d4042d6

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_MultiUnit

open SPPRevenue
open SPPRevenue.SingleUnit
open SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

theorem solution (H : ℕ) (hH : 1 ≤ H) {n : ℕ} (hn : 1 ≤ n) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (t : Fin n → (Fin n → ℝ) → ℝ)
    (ht : IsMultiThresholdMech H μ t) (τ : ℝ) (hτ : 0 ≤ τ) :
    ENNReal.ofReal ((H : ℝ) - ∑ i ∈ Finset.range H,
        ((H : ℝ) - i) * (n.choose i : ℝ) * ((sStar μ t τ).toReal ^ i / (n : ℝ) ^ i) *
          (1 - (sStar μ t τ).toReal / n) ^ (n - i)) ≤ mH H μ t τ := by
            classical
            have hE : ∀ i, ((Measure.pi μ).prod (μ i)) {y : (Fin n → ℝ) × ℝ | t i y.1 ≤ y.2 ∧ τ ≤ t i y.1} = sStarI μ t i τ := by
              intro i
              have hmeas : Measurable (fun y : (Fin n → ℝ) × ℝ => Function.update y.1 i y.2) := by fun_prop
              have hmap : ((Measure.pi μ).prod (μ i)).map (fun y : (Fin n → ℝ) × ℝ => Function.update y.1 i y.2)
                  = Measure.pi μ := by
                refine (Measure.pi_eq ?_).symm
                intro A hA
                rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hA)]
                have hpre : (fun y : (Fin n → ℝ) × ℝ => Function.update y.1 i y.2) ⁻¹' (Set.univ.pi A)
                    = (Set.univ.pi (Function.update A i Set.univ)) ×ˢ A i := by
                  ext ⟨w, y⟩
                  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
                  constructor
                  · intro h
                    refine ⟨fun j => ?_, by simpa using h i⟩
                    by_cases hj : j = i
                    · subst hj; simp
                    · have := h j; rw [Function.update_of_ne hj] at this; rw [Function.update_of_ne hj]; exact this
                  · rintro ⟨h1, h2⟩ j
                    by_cases hj : j = i
                    · subst hj; simpa using h2
                    · have := h1 j; rw [Function.update_of_ne hj] at this; rw [Function.update_of_ne hj]; exact this
                rw [hpre, Measure.prod_prod, Measure.pi_pi]
                rw [← Finset.mul_prod_erase Finset.univ (fun j => μ j (A j)) (Finset.mem_univ i),
                  ← Finset.mul_prod_erase Finset.univ (fun j => μ j (Function.update A i Set.univ j)) (Finset.mem_univ i)]
                simp only [Function.update_self, measure_univ, one_mul]
                rw [mul_comm]
                congr 1
                refine Finset.prod_congr rfl (fun j hj => ?_)
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
              have hS : MeasurableSet {v : Fin n → ℝ | t i v ≤ v i ∧ τ ≤ t i v} := by
                have := ht.measurable i
                exact (measurableSet_le this (measurable_pi_apply i)).inter (measurableSet_le measurable_const this)
              unfold sStarI
              have hh := Measure.map_apply (μ := (Measure.pi μ).prod (μ i)) hmeas hS
              rw [hmap] at hh
              rw [hh]
              congr 1
              refine Set.ext (fun x => ?_)
              obtain ⟨w, y⟩ := x
              simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.update_self]
              have : t i (Function.update w i y) = t i w :=
                ht.indep_own i _ _ (fun j hj => Function.update_of_ne hj _ _)
              rw [this]
            let w : ℕ → ℝ := fun k => if k < H then (H : ℝ) - k else 0
            let L : Polynomial ℝ →ₗ[ℝ] ℝ := ∑ j ∈ Finset.range H, ((H : ℝ) - j) • Polynomial.lcoeff ℝ j
            have hLapp : ∀ P : Polynomial ℝ, L P = ∑ j ∈ Finset.range H, ((H : ℝ) - j) * P.coeff j := by
              intro P
              simp [L, LinearMap.sum_apply]
            have hLX : ∀ (m : ℕ) (c : ℝ), L (Polynomial.C c * Polynomial.X ^ m) = c * w m := by
              intro m c
              rw [hLapp]
              simp only [Polynomial.coeff_C_mul_X_pow, mul_ite, mul_zero]
              rw [Finset.sum_ite_eq' (Finset.range H) m]
              simp only [Finset.mem_range, w]
              split_ifs <;> ring
            let PS : (Fin n → ℝ) → Finset (Fin n) → ℝ := fun p S =>
              (∏ i ∈ S, p i) * ∏ i ∈ Finset.univ \ S, (1 - p i)
            let F : (Fin n → ℝ) → Polynomial ℝ := fun p => ∏ i, (1 + Polynomial.C (p i) * (Polynomial.X - 1))
            have hexp : ∀ p, F p = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, Polynomial.C (PS p S) * Polynomial.X ^ S.card := by
              intro p
              have h1 : ∀ i, (1 + Polynomial.C (p i) * (Polynomial.X - 1) : Polynomial ℝ) = Polynomial.C (p i) * Polynomial.X + Polynomial.C (1 - p i) := by
                intro i; simp only [map_sub, map_one]; ring
              simp only [F, h1]
              rw [Finset.prod_add]
              refine Finset.sum_congr rfl (fun S _ => ?_)
              simp only [PS, Finset.prod_mul_distrib, Finset.prod_const, map_mul, map_prod]
              ring
            have hLF : ∀ p, L (F p) = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, PS p S * w S.card := by
              intro p
              rw [hexp, map_sum]
              exact Finset.sum_congr rfl (fun S _ => hLX _ _)
            have hsum1 : ∀ p, ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, PS p S = 1 := by
              intro p
              have := Finset.prod_add (fun i => p i) (fun i => 1 - p i) (Finset.univ : Finset (Fin n))
              simp only [add_sub_cancel, Finset.prod_const_one] at this
              exact this.symm
            have hnn : ∀ (p : Fin n → ℝ), (∀ i, 0 ≤ p i ∧ p i ≤ 1) → ∀ (T : Finset (Fin n)) (k : ℕ),
                0 ≤ (∏ i ∈ T, (1 + Polynomial.C (p i) * (Polynomial.X - 1) : Polynomial ℝ)).coeff k := by
              intro p hp T
              induction T using Finset.induction_on with
              | empty => intro k; simp [Polynomial.coeff_one]; split_ifs <;> norm_num
              | insert a T ha ih =>
                intro k
                rw [Finset.prod_insert ha, Polynomial.coeff_mul]
                refine Finset.sum_nonneg (fun x _ => mul_nonneg ?_ (ih _))
                have h1 : (1 + Polynomial.C (p a) * (Polynomial.X - 1) : Polynomial ℝ) = Polynomial.C (p a) * Polynomial.X + Polynomial.C (1 - p a) := by
                  simp only [map_sub, map_one]; ring
                rw [h1, Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
                have := hp a
                split_ifs <;> linarith
            have hconv : ∀ Q : Polynomial ℝ, (∀ k, 0 ≤ Q.coeff k) → 0 ≤ L (Q * (Polynomial.X - 1) ^ 2) := by
              intro Q hQ
              rw [Q.as_sum_range_C_mul_X_pow, Finset.sum_mul, map_sum]
              refine Finset.sum_nonneg (fun k _ => ?_)
              have : Polynomial.C (Q.coeff k) * Polynomial.X ^ k * (Polynomial.X - 1) ^ 2 =
                  Polynomial.C (Q.coeff k) * Polynomial.X ^ (k + 2) - Polynomial.C (2 * Q.coeff k) * Polynomial.X ^ (k + 1) + Polynomial.C (Q.coeff k) * Polynomial.X ^ k := by
                simp only [map_mul, map_ofNat]; ring
              rw [this, map_add, map_sub, hLX, hLX, hLX]
              have hq := hQ k
              have : 0 ≤ w (k + 2) - 2 * w (k + 1) + w k := by
                simp only [w]
                split_ifs with h1 h2 h3 h3 h2 h3 h3
                all_goals push_cast
                all_goals first
                  | linarith
                  | (exfalso; omega)
                  | (have hk : (k:ℝ) + 2 = H := by exact_mod_cast (show k + 2 = H by omega)
                     linarith)
                  | (have hk : (k:ℝ) < H := by exact_mod_cast (show k < H by omega)
                     linarith)
              nlinarith [mul_nonneg hq this]
            have hLsmul : ∀ (c : ℝ) (P : Polynomial ℝ), L (Polynomial.C c * P) = c * L P := by
              intro c P; rw [Polynomial.C_mul', map_smul, smul_eq_mul]
            have hpair : ∀ (p p' : Fin n → ℝ) (i j : Fin n), i ≠ j → (∀ k, k ≠ i → k ≠ j → p' k = p k) →
                p' i + p' j = p i + p j → p i * p j ≤ p' i * p' j → (∀ k, 0 ≤ p k ∧ p k ≤ 1) →
                L (F p) ≤ L (F p') := by
              intro p p' i j hij hrest hsum hprod hp
              have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩
              have hdec : ∀ q : Fin n → ℝ, F q = (1 + Polynomial.C (q i) * (Polynomial.X - 1)) * ((1 + Polynomial.C (q j) * (Polynomial.X - 1)) *
                  ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, (1 + Polynomial.C (q k) * (Polynomial.X - 1))) := by
                intro q
                simp only [F]
                rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), ← Finset.mul_prod_erase _ _ hj]
              have hQ : ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, (1 + Polynomial.C (p' k) * (Polynomial.X - 1))
                  = ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, (1 + Polynomial.C (p k) * (Polynomial.X - 1)) := by
                refine Finset.prod_congr rfl (fun k hk => ?_)
                have h1 := Finset.ne_of_mem_erase hk
                have h2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
                rw [hrest k h2 h1]
              set Q := ∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, (1 + Polynomial.C (p k) * (Polynomial.X - 1)) with hQdef
              have hform : ∀ a b : ℝ, (1 + Polynomial.C a * (Polynomial.X - 1)) * ((1 + Polynomial.C b * (Polynomial.X - 1)) * Q) =
                  Q + Polynomial.C (a + b) * (Q * (Polynomial.X - 1)) + Polynomial.C (a * b) * (Q * (Polynomial.X - 1) ^ 2) := by
                intro a b; simp only [map_add, map_mul]; ring
              rw [hdec p, hdec p', hQ, hform, hform, map_add L, map_add L, map_add L, map_add L, hLsmul, hLsmul,
                hLsmul, hLsmul, hsum]
              have := hconv Q (hnn p hp _)
              nlinarith
            have hsmooth : ∀ (c : ℝ) (m : ℕ) (p : Fin n → ℝ), (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
                ∑ i, p i = n * c → (Finset.univ.filter (fun i => p i ≠ c)).card ≤ m →
                L (F p) ≤ L (F (fun _ => c)) := by
              intro c m
              induction m with
              | zero =>
                intro p hp hs hc
                have h0 := Finset.card_eq_zero.mp (Nat.le_zero.mp hc)
                rw [Finset.filter_eq_empty_iff] at h0
                have : p = fun _ => c := funext (fun i => by have := h0 (Finset.mem_univ i); push Not at this; exact this)
                rw [this]
              | succ m ih =>
                intro p hp hs hc
                by_cases hall : ∀ i, p i = c
                · have : p = fun _ => c := funext hall
                  rw [this]
                push Not at hall
                obtain ⟨i0, hi0⟩ := hall
                have hz : ∑ i, (p i - c) = 0 := by
                  rw [Finset.sum_sub_distrib, hs]; simp
                obtain ⟨i, hi⟩ : ∃ i, p i < c := by
                  by_contra h; push Not at h
                  have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sub_nonneg.2 (h k))).1 hz i0 (Finset.mem_univ _)
                  exact hi0 (by linarith)
                obtain ⟨j, hj⟩ : ∃ j, c < p j := by
                  by_contra h; push Not at h
                  have := (Finset.sum_eq_zero_iff_of_nonpos (fun k _ => sub_nonpos.2 (h k))).1 hz i0 (Finset.mem_univ _)
                  exact hi0 (by linarith)
                have hij : i ≠ j := by rintro rfl; linarith
                set p' := Function.update (Function.update p i c) j (p i + p j - c) with hp'
                have hp'j : p' j = p i + p j - c := by simp [hp']
                have hp'i : p' i = c := by simp [hp', Function.update_of_ne hij]
                have hp'k : ∀ k, k ≠ i → k ≠ j → p' k = p k := by
                  intro k hki hkj; simp [hp', Function.update_of_ne hki, Function.update_of_ne hkj]
                have hjm : j ∈ (Finset.univ : Finset (Fin n)).erase i := Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩
                have hsplit : ∀ g : Fin n → ℝ, ∑ k, g k = g i + (g j + ∑ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, g k) := by
                  intro g
                  rw [Finset.add_sum_erase _ _ hjm, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
                have hrest : ∑ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, p' k
                    = ∑ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, p k := by
                  refine Finset.sum_congr rfl (fun k hk => ?_)
                  exact hp'k k (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)) (Finset.ne_of_mem_erase hk)
                refine le_trans (hpair p p' i j hij hp'k (by rw [hp'i, hp'j]; ring)
                  (by rw [hp'i, hp'j]; nlinarith) hp) (ih p' ?_ ?_ ?_)
                · intro k
                  by_cases hki : k = i
                  · subst hki; rw [hp'i]; constructor <;> linarith [hp k, hp j]
                  by_cases hkj : k = j
                  · subst hkj; rw [hp'j]; constructor <;> linarith [hp k, hp i]
                  rw [hp'k k hki hkj]; exact hp k
                · rw [hsplit, hrest, hp'i, hp'j, ← hs, hsplit p]; ring
                · have hsub : Finset.univ.filter (fun k => p' k ≠ c) ⊆ (Finset.univ.filter (fun k => p k ≠ c)).erase i := by
                    intro k hk
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
                    have hki : k ≠ i := by rintro rfl; exact hk hp'i
                    refine Finset.mem_erase.2 ⟨hki, ?_⟩
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                    by_cases hkj : k = j
                    · subst hkj; exact ne_of_gt hj
                    · rwa [hp'k k hki hkj] at hk
                  have hmem : i ∈ Finset.univ.filter (fun k => p k ≠ c) := by simp [ne_of_lt hi]
                  have := Finset.card_le_card hsub
                  rw [Finset.card_erase_of_mem hmem] at this
                  omega
            have hbin : ∀ c : ℝ, L (F (fun _ => c)) = ∑ k ∈ Finset.range H, ((H : ℝ) - k) * (n.choose k : ℝ) * c ^ k * (1 - c) ^ (n - k) := by
              intro c
              rw [hLF]
              have h1 : ∀ S : Finset (Fin n), PS (fun _ => c) S * w S.card = (fun k => c ^ k * (1 - c) ^ (n - k) * w k) S.card := by
                intro S
                simp only [PS, Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
              rw [Finset.sum_congr rfl (fun S _ => h1 S), Finset.sum_powerset_apply_card (fun k => c ^ k * (1 - c) ^ (n - k) * w k)]
              simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              have hA : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (c ^ k * (1 - c) ^ (n - k) * w k)
                  = ∑ k ∈ Finset.range (n + 1 + H), (n.choose k : ℝ) * (c ^ k * (1 - c) ^ (n - k) * w k) := by
                apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
                intro k _ hk
                simp only [Finset.mem_range, not_lt] at hk
                rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
              have hB : ∑ k ∈ Finset.range H, ((H : ℝ) - k) * (n.choose k : ℝ) * c ^ k * (1 - c) ^ (n - k)
                  = ∑ k ∈ Finset.range (n + 1 + H), (n.choose k : ℝ) * (c ^ k * (1 - c) ^ (n - k) * w k) := by
                rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : H ≤ n + 1 + H))]
                · refine Finset.sum_congr rfl (fun k hk => ?_)
                  simp only [Finset.mem_range] at hk
                  simp only [w, if_pos hk]; ring
                · intro k _ hk
                  simp only [Finset.mem_range, not_lt] at hk
                  simp only [w, if_neg (by omega : ¬ k < H)]; ring
              rw [hA, hB]
            have hfinal : ∀ p : Fin n → ℝ, (∀ i, 0 ≤ p i ∧ p i ≤ 1) → (1 ≤ n) →
                (H : ℝ) - ∑ k ∈ Finset.range H, ((H : ℝ) - k) * (n.choose k : ℝ) * ((∑ i, p i) / n) ^ k * (1 - (∑ i, p i) / n) ^ (n - k)
                  ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, PS p S * ((min S.card H : ℕ) : ℝ) := by
              intro p hp hn
              have hnr : (n : ℝ) ≠ 0 := by have : (0:ℝ) < n := by exact_mod_cast hn
                                           exact ne_of_gt this
              have h1 := hsmooth ((∑ i, p i) / n) n p hp (by field_simp) (by
                calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
                  _ = n := by simp)
              rw [hbin] at h1
              have h2 : ∀ S : Finset (Fin n), PS p S * ((min S.card H : ℕ) : ℝ) = H * PS p S - PS p S * w S.card := by
                intro S
                simp only [w]
                split_ifs with h
                · rw [Nat.min_eq_left h.le]; ring
                · rw [Nat.min_eq_right (by omega)]; ring
              rw [Finset.sum_congr rfl (fun S _ => h2 S), Finset.sum_sub_distrib, ← Finset.mul_sum, hsum1, ← hLF]
              linarith
            have hcomb : ∀ p v : Fin n → ℝ, min (Finset.univ.filter (fun i => p i ≤ v i ∧ τ ≤ p i)).card H ≤
                ((sppHWinners H p v).filter (fun i => τ ≤ p i)).card := by
              intro p v
              set A := Finset.univ.filter (fun i => p i ≤ v i ∧ τ ≤ p i) with hA
              let key : Fin n → ℝ ×ₗ Fin n := fun k => toLex (-p k, k)
              have hkey : ∀ k i, key k < key i ↔ (p i < p k ∨ (p k = p i ∧ k < i)) := by
                intro k i
                simp only [key, Prod.Lex.toLex_lt_toLex, neg_lt_neg_iff, neg_inj]
              let r : Fin n → ℕ := fun i => (A.filter (fun k => key k < key i)).card
              have hr_lt : ∀ i ∈ A, r i < A.card := by
                intro i hi
                apply Finset.card_lt_card
                rw [Finset.filter_ssubset]
                exact ⟨i, hi, lt_irrefl _⟩
              have hr_mono : ∀ i ∈ A, ∀ j ∈ A, key i < key j → r i < r j := by
                intro i hi j hj hij
                apply Finset.card_lt_card
                rw [Finset.ssubset_iff_of_subset]
                · exact ⟨i, Finset.mem_filter.2 ⟨hi, hij⟩, fun h => lt_irrefl _ (Finset.mem_filter.1 h).2⟩
                · intro k hk
                  rw [Finset.mem_filter] at hk ⊢
                  exact ⟨hk.1, lt_trans hk.2 hij⟩
              have hinj : Set.InjOn r A := by
                intro i hi j hj hrij
                rcases lt_trichotomy (key i) (key j) with h | h | h
                · exact absurd hrij (ne_of_lt (hr_mono i hi j hj h))
                · have : (ofLex (key i)).2 = (ofLex (key j)).2 := by rw [h]
                  simpa [key] using this
                · exact absurd hrij (ne_of_gt (hr_mono j hj i hi h))
              have himg : A.image r = Finset.range A.card := by
                apply Finset.eq_of_subset_of_card_le
                · intro x hx
                  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
                  exact Finset.mem_range.2 (hr_lt i hi)
                · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
              have hsub : A.filter (fun i => r i < H) ⊆ (sppHWinners H p v).filter (fun i => τ ≤ p i) := by
                intro i hi
                rw [Finset.mem_filter] at hi
                have hiA := Finset.mem_filter.1 hi.1
                have hrank : (Finset.univ.filter (fun k => p k ≤ v k ∧ (p i < p k ∨ (p k = p i ∧ k < i)))) =
                    A.filter (fun k => key k < key i) := by
                  ext k
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA, hkey]
                  constructor
                  · rintro ⟨h1, h2⟩
                    refine ⟨⟨h1, ?_⟩, h2⟩
                    rcases h2 with h2 | ⟨h2, _⟩
                    · linarith [hiA.2.2]
                    · rw [h2]; exact hiA.2.2
                  · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
                unfold sppHWinners
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                refine ⟨⟨hiA.2.1, ?_⟩, hiA.2.2⟩
                rw [hrank]; exact hi.2
              have hcard : (A.filter (fun i => r i < H)).card ≥ min A.card H := by
                have h1 := Finset.card_image_le (s := A.filter (fun i => r i < H)) (f := r)
                have h2 : (A.filter (fun i => r i < H)).image r = (Finset.range A.card).filter (· < H) := by
                  rw [← himg, Finset.filter_image]
                have h3 : ((Finset.range A.card).filter (· < H)) = Finset.range (min A.card H) := by
                  ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
                rw [h2, h3, Finset.card_range] at h1
                exact h1
              exact le_trans hcard (Finset.card_le_card hsub)
            -- the per-buyer probabilities
            set e : Fin n → ℝ≥0∞ := fun i => sStarI μ t i τ with he
            have he1 : ∀ i, e i ≤ 1 := fun i => prob_le_one
            have hene : ∀ i, e i ≠ ⊤ := fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (he1 i)
            set s : Fin n → ℝ := fun i => (e i).toReal with hs
            have hs01 : ∀ i, 0 ≤ s i ∧ s i ≤ 1 := fun i =>
              ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using he1 i)⟩
            have hsStar : (sStar μ t τ).toReal = ∑ i, s i := by
              unfold sStar; rw [ENNReal.toReal_sum (fun i _ => hene i)]
            let E : Fin n → Set ((Fin n → ℝ) × ℝ) := fun i => {y | t i y.1 ≤ y.2 ∧ τ ≤ t i y.1}
            have hEm : ∀ i, MeasurableSet (E i) := fun i =>
              (measurableSet_le ((ht.measurable i).comp measurable_fst) measurable_snd).inter
                (measurableSet_le measurable_const ((ht.measurable i).comp measurable_fst))
            let Ax : (Fin n → Fin n → ℝ) × (Fin n → ℝ) → Finset (Fin n) := fun x =>
              Finset.univ.filter (fun i => t i (x.1 i) ≤ x.2 i ∧ τ ≤ t i (x.1 i))
            let eq := MeasurableEquiv.arrowProdEquivProdArrow (Fin n → ℝ) ℝ (Fin n)
            have hmp := measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) ℝ (Fin n)
              (fun _ => Measure.pi μ) μ
            have hmap : resampleLaw μ = Measure.map eq (Measure.pi fun i => (Measure.pi μ).prod (μ i)) := by
              unfold resampleLaw; exact hmp.map_eq.symm
            have hpre : ∀ S : Finset (Fin n), eq ⁻¹' {x | Ax x = S} =
                Set.univ.pi (fun i => if i ∈ S then E i else (E i)ᶜ) := by
              intro S
              ext y
              simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
              change Finset.univ.filter (fun i => t i ((y i).1) ≤ (y i).2 ∧ τ ≤ t i ((y i).1)) = S ↔ _
              rw [Finset.ext_iff]
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h i
                by_cases hi : i ∈ S
                · rw [if_pos hi]; exact (h i).2 hi
                · rw [if_neg hi]; exact fun hh => hi ((h i).1 hh)
              · intro h i
                have := h i
                by_cases hi : i ∈ S
                · rw [if_pos hi] at this; exact ⟨fun _ => hi, fun _ => this⟩
                · rw [if_neg hi] at this; exact ⟨fun hh => absurd hh this, fun hh => absurd hh hi⟩
            have hmeasS : ∀ S : Finset (Fin n), MeasurableSet {x | Ax x = S} := by
              intro S
              rw [← eq.measurableSet_preimage, hpre]
              exact MeasurableSet.univ_pi (fun i => by split_ifs; exacts [hEm i, (hEm i).compl])
            have hprob : ∀ S : Finset (Fin n), resampleLaw μ {x | Ax x = S} =
                ∏ i, (if i ∈ S then e i else 1 - e i) := by
              intro S
              rw [hmap, MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
              refine Finset.prod_congr rfl (fun i _ => ?_)
              split_ifs
              · exact hE i
              · rw [prob_compl_eq_one_sub (hEm i), hE i]
            have hPS : ∀ S : Finset (Fin n), ENNReal.ofReal (PS s S) = ∏ i, (if i ∈ S then e i else 1 - e i) := by
              intro S
              simp only [PS]
              rw [ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => (hs01 i).1)),
                ENNReal.ofReal_prod_of_nonneg (fun i _ => (hs01 i).1),
                ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [(hs01 i).2]), Finset.prod_ite]
              have hf1 : Finset.univ.filter (fun i => i ∈ S) = S := by ext; simp
              have hf2 : Finset.univ.filter (fun i => i ∉ S) = Finset.univ \ S := by ext; simp
              rw [hf1, hf2]
              congr 1
              · exact Finset.prod_congr rfl (fun i _ => ENNReal.ofReal_toReal (hene i))
              · refine Finset.prod_congr rfl (fun i _ => ?_)
                rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal (hene i)]
            have hint : ∫⁻ x, ((min (Ax x).card H : ℕ) : ℝ≥0∞) ∂(resampleLaw μ) =
                ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
                  ((min S.card H : ℕ) : ℝ≥0∞) * resampleLaw μ {x | Ax x = S} := by
              have hpt : ∀ x, ((min (Ax x).card H : ℕ) : ℝ≥0∞) = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
                  {x | Ax x = S}.indicator (fun _ => ((min S.card H : ℕ) : ℝ≥0∞)) x := by
                intro x
                rw [Finset.sum_eq_single (Ax x)]
                · simp [Set.indicator]
                · intro b _ hb
                  simp only [Set.indicator, Set.mem_setOf_eq]
                  rw [if_neg (fun h => hb h.symm)]
                · intro h; exact absurd (Finset.mem_powerset.2 (Finset.subset_univ _)) h
              rw [lintegral_congr hpt, lintegral_finsetSum _ (fun S _ => measurable_const.indicator (hmeasS S))]
              exact Finset.sum_congr rfl (fun S _ => lintegral_indicator_const (hmeasS S) _)
            have hmono : ∫⁻ x, ((min (Ax x).card H : ℕ) : ℝ≥0∞) ∂(resampleLaw μ) ≤ mH H μ t τ := by
              unfold mH
              apply lintegral_mono
              intro x
              exact Nat.cast_le.mpr (hcomb (fun i => t i (x.1 i)) x.2)
            have hreal := hfinal s hs01 hn
            simp only [div_pow] at hreal
            rw [hsStar]
            calc ENNReal.ofReal _ ≤ ENNReal.ofReal (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
                  PS s S * ((min S.card H : ℕ) : ℝ)) := ENNReal.ofReal_le_ofReal hreal
              _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
                  ((min S.card H : ℕ) : ℝ≥0∞) * resampleLaw μ {x | Ax x = S} := by
                rw [ENNReal.ofReal_sum_of_nonneg]
                · refine Finset.sum_congr rfl (fun S _ => ?_)
                  rw [ENNReal.ofReal_mul, hPS, hprob, ENNReal.ofReal_natCast, mul_comm]
                  exact mul_nonneg (Finset.prod_nonneg (fun i _ => (hs01 i).1))
                    (Finset.prod_nonneg (fun i _ => by linarith [(hs01 i).2]))
                · intro S _
                  exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _ => (hs01 i).1))
                    (Finset.prod_nonneg (fun i _ => by linarith [(hs01 i).2]))) (Nat.cast_nonneg _)
              _ = ∫⁻ x, ((min (Ax x).card H : ℕ) : ℝ≥0∞) ∂(resampleLaw μ) := hint.symm
              _ ≤ mH H μ t τ := hmono
