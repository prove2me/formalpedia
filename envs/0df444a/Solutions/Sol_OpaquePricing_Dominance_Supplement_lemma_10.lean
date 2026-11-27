-- Prove2me | solution 1 for OpaquePricing.Dominance.Supplement.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:22:25.651814+00:00
-- url     : https://prove2.me/submissions/47820b1c-d163-4019-83b9-85535bf1664d

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_FiniteTypes

open MeasureTheory

open OpaquePricing
open OpaquePricing.Dominance
open OpaquePricing.Dominance.Supplement

/-- Equal-price utility ties are resolved towards the smallest index, preserving revenue. -/
theorem solution {N m : ℕ} (hN : 2 ≤ N) (F : FiniteTypes N m)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsort : ∀ i k, i ≤ k → p k ≤ p i)
    (hopt : ∀ q : Fin N → ℝ, (∀ i, 0 ≤ q i) → finiteRevenue F q ≤ finiteRevenue F p) :
    ∀ i, (∃ j, p i = F.values j i - cheaperUtility p (F.values j) i) ∨
      (∀ j, ¬ buys p (F.values j) i) := by
        classical
        intro i
        by_contra hcon
        push_neg at hcon
        obtain ⟨hne, j0, hj0⟩ := hcon
        have mr_ge : ∀ (u r : Fin N → ℝ) (o : Fin N), 0 ≤ u o → (∀ o', u o' ≤ u o) →
            r o ≤ menuRevenue Finset.univ u r := by
          intro u r o h0 hmax
          unfold menuRevenue
          dsimp only
          rw [dif_pos ⟨o, by simp [h0, hmax]⟩]
          exact Finset.le_sup' r (by simp [h0, hmax])
        have mr_nonneg : ∀ (u r : Fin N → ℝ), (∀ o, 0 ≤ r o) →
            0 ≤ menuRevenue Finset.univ u r := by
          intro u r hr
          unfold menuRevenue
          dsimp only
          split_ifs with h
          · obtain ⟨o, ho⟩ := h
            exact le_trans (hr o) (Finset.le_sup' r ho)
          · exact le_rfl
        have mr_cases : ∀ (u r : Fin N → ℝ), menuRevenue Finset.univ u r = 0 ∨
            ∃ o, 0 ≤ u o ∧ (∀ o', u o' ≤ u o) ∧ menuRevenue Finset.univ u r = r o := by
          intro u r
          unfold menuRevenue
          dsimp only
          split_ifs with h
          · right
            obtain ⟨o, ho, he⟩ := Finset.exists_mem_eq_sup' h r
            simp at ho
            exact ⟨o, ho.1, ho.2, he⟩
          · left; rfl
        have cu_le : ∀ v : Fin N → ℝ, 0 ≤ v i - p i → (∀ k, v k - p k ≤ v i - p i) →
            cheaperUtility p v i ≤ v i - p i := by
          intro v h0 hk
          unfold cheaperUtility
          apply Finset.max'_le
          intro y hy
          simp at hy
          rcases hy with rfl | ⟨k, hk', rfl⟩
          · exact h0
          · exact max_le (hk k) h0
        have cu_ge : ∀ v : Fin N → ℝ, ∀ k, i < k → max (v k - p k) 0 ≤ cheaperUtility p v i := by
          intro v k hk
          unfold cheaperUtility
          apply Finset.le_max'
          simp
          right; exact ⟨k, hk, rfl⟩
        have cu_nonneg : ∀ v, 0 ≤ cheaperUtility p v i := by
          intro v; unfold cheaperUtility; apply Finset.le_max'; simp
        have gap : ∀ j, buys p (F.values j) i → ∀ k, k ≠ i →
            max (F.values j k - p k) 0 < F.values j i - p i := by
          intro j hb k hk
          obtain ⟨h0, hmax, hprice, hidx⟩ := hb
          have hC : cheaperUtility p (F.values j) i < F.values j i - p i := by
            have := cu_le _ h0 hmax
            have hn := hne j
            rcases lt_or_eq_of_le this with h | h
            · exact h
            · exact absurd (by linarith) hn
          rcases lt_or_gt_of_ne hk with hlt | hgt
          · have hk1 : F.values j k - p k < F.values j i - p i := by
              rcases lt_or_eq_of_le (hmax k) with h | h
              · exact h
              · exfalso
                have h1 := hprice k h
                have h2 := hsort k i hlt.le
                have h3 := hidx k h (le_antisymm h1 h2)
                exact absurd h3 (not_le.mpr hlt)
            have := cu_nonneg (F.values j)
            exact max_lt hk1 (by linarith)
          · exact lt_of_le_of_lt (cu_ge _ k hgt) hC
        set g : Fin m × Fin N → ℝ := fun jk => if buys p (F.values jk.1) i ∧ jk.2 ≠ i then
          (F.values jk.1 i - p i) - max (F.values jk.1 jk.2 - p jk.2) 0 else 1 with hg
        have hgpos : ∀ jk, 0 < g jk := by
          intro jk
          simp only [hg]
          split_ifs with h
          · have := gap jk.1 h.1 jk.2 h.2; linarith
          · exact one_pos
        have hne' : (Finset.univ : Finset (Fin m × Fin N)).Nonempty := ⟨(j0, i), Finset.mem_univ _⟩
        set ε := Finset.univ.inf' hne' g with hε
        have hεpos : 0 < ε := (Finset.lt_inf'_iff hne').2 (fun jk _ => hgpos jk)
        have hεle : ∀ j, buys p (F.values j) i → ∀ k, k ≠ i →
            max (F.values j k - p k) 0 ≤ F.values j i - p i - ε := by
          intro j hb k hk
          have h1 : ε ≤ g (j, k) := Finset.inf'_le _ (Finset.mem_univ _)
          have h2 : g (j, k) = (F.values j i - p i) - max (F.values j k - p k) 0 := by
            simp only [hg]; rw [if_pos ⟨hb, hk⟩]
          linarith
        obtain ⟨k0, hk0⟩ : ∃ k : Fin N, k ≠ i := by
          by_cases h : i.val = 0
          · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
          · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
        set q := Function.update p i (p i + ε) with hq
        have hqi : q i = p i + ε := by simp [hq]
        have hqk : ∀ k, k ≠ i → q k = p k := by intro k hk; simp [hq, hk]
        have hpq : ∀ k, p k ≤ q k := by
          intro k
          by_cases hk : k = i
          · subst hk; rw [hqi]; linarith
          · rw [hqk k hk]
        have hq_nonneg : ∀ k, 0 ≤ q k := fun k => le_trans (hp k) (hpq k)
        have hbuyer : ∀ j, buys p (F.values j) i →
            dpRevenue p (F.values j) < dpRevenue q (F.values j) := by
          intro j hb
          have hup : dpRevenue p (F.values j) ≤ p i := by
            unfold dpRevenue
            rcases mr_cases (fun k => F.values j k - p k) p with h | ⟨o, ho0, homax, he⟩
            · rw [h]; exact hp i
            · rw [he]
              have : F.values j o - p o = F.values j i - p i := le_antisymm (hb.2.1 o) (homax i)
              exact hb.2.2.1 o this
          have hdown : p i + ε ≤ dpRevenue q (F.values j) := by
            unfold dpRevenue
            rw [← hqi]
            apply mr_ge
            · simp only [hqi]
              have := hεle j hb k0 hk0
              have := le_max_right (F.values j k0 - p k0) 0
              linarith
            · intro o'
              by_cases ho : o' = i
              · subst ho; exact le_rfl
              · simp only [hqk o' ho, hqi]
                have := hεle j hb o' ho
                have := le_max_left (F.values j o' - p o') 0
                linarith
          linarith
        have hnb_aux : ∀ j o, o ≠ i → 0 ≤ F.values j o - p o →
            (∀ o', F.values j o' - p o' ≤ F.values j o - p o) → p o ≤ dpRevenue q (F.values j) := by
          intro j o ho h0 hmax
          unfold dpRevenue
          rw [← hqk o ho]
          apply mr_ge
          · simp only [hqk o ho]; exact h0
          · intro o'
            simp only [hqk o ho]
            have := hpq o'
            have := hmax o'
            linarith
        have hle : ∀ j, dpRevenue p (F.values j) ≤ dpRevenue q (F.values j) := by
          intro j
          by_cases hb : buys p (F.values j) i
          · exact (hbuyer j hb).le
          · have hcases := mr_cases (fun k => F.values j k - p k) p
            unfold dpRevenue
            rcases hcases with h | ⟨o, ho0, homax, he⟩
            · rw [h]; exact mr_nonneg _ _ hq_nonneg
            · rw [he]
              by_cases hoi : o = i
              · subst hoi
                unfold buys at hb
                push_neg at hb
                by_cases hC : ∀ (k : Fin N), F.values j k - p k = F.values j o - p o → p k ≤ p o
                · obtain ⟨k, hk1, hk2, hk3⟩ := hb ho0 homax hC
                  have hki : k ≠ o := fun e => by rw [e] at hk3; exact lt_irrefl _ hk3
                  have := hnb_aux j k hki (by linarith) (fun o' => by linarith [homax o'])
                  unfold dpRevenue at this
                  linarith
                · push_neg at hC
                  obtain ⟨k, hk1, hk2⟩ := hC
                  exfalso
                  have := mr_ge (fun k => F.values j k - p k) p k (show 0 ≤ F.values j k - p k by linarith)
                    (fun o' => show F.values j o' - p o' ≤ F.values j k - p k by linarith [homax o'])
                  rw [he] at this
                  linarith
              · exact hnb_aux j o hoi ho0 homax
        have hlt : finiteRevenue F p < finiteRevenue F q := by
          unfold finiteRevenue
          apply Finset.sum_lt_sum
          · intro j _
            exact mul_le_mul_of_nonneg_left (hle j) (F.weight_pos j).le
          · exact ⟨j0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hbuyer j0 hj0) (F.weight_pos j0)⟩
        have := hopt q hq_nonneg
        linarith
