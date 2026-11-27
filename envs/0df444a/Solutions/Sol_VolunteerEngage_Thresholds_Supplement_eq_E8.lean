-- Prove2me | solution 1 for VolunteerEngage.Thresholds.Supplement.eq_E8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:28.669811+00:00
-- url     : https://prove2.me/submissions/3b5f6636-0056-499c-a064-80db9c5bbcaa

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_Psi

open VolunteerEngage
open VolunteerEngage.Thresholds
open VolunteerEngage.Thresholds.Supplement

/-- (E8), Online Supplement p. 12. Every branch, with the least maximizer
at each kink. The first conjunct also certifies the infimum as a minimum. -/
theorem solution (M : Model) (hM : M.Standing) :
    ∀ y : ℝ,
      IsLeast {x : ℝ | x ∈ Set.Icc M.θ0 (M.θ M.L) ∧ y * x - cost M x = phi M y}
        (psi M y) ∧
      (y ≤ M.c 1 → psi M y = M.θ0) ∧
      (∀ m ∈ Finset.Icc 2 M.L, M.c (m - 1) < y → y ≤ M.c m → psi M y = M.θ (m - 1)) ∧
      (M.c M.L < y → psi M y = M.θ M.L) := by
        obtain ⟨hL, hθ0, hη, hc1, hcinc, hcLp, hp, hκ, hσ⟩ := hM
        have hθ0' : M.θ 0 = M.θ0 := by simp [Model.θ]
        have hθsucc : ∀ n : ℕ, M.θ (n+1) = M.θ n + M.η (n+1) := by
          intro n
          simp only [Model.θ]
          rw [Finset.sum_Icc_succ_top (by omega)]
          ring
        have hθstep : ∀ n : ℕ, n + 1 ≤ M.L → M.θ n < M.θ (n+1) := by
          intro n hn
          rw [hθsucc n]
          have := hη (n+1) (Finset.mem_Icc.mpr ⟨by omega, hn⟩)
          linarith
        have hθlt : ∀ l : ℕ, 1 ≤ l → l ≤ M.L → M.θ (l - 1) < M.θ l := by
          intro l h1 h2
          have := hθstep (l-1) (by omega)
          rwa [Nat.sub_add_cancel h1] at this
        have hθmono : ∀ i j : ℕ, i ≤ j → j ≤ M.L → M.θ i ≤ M.θ j := by
          intro i j hij hj
          induction j, hij using Nat.le_induction with
          | base => exact le_refl _
          | succ n hin ih =>
            have := hθstep n hj
            have := ih (by omega)
            linarith
        have hcmono : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ M.L → M.c i ≤ M.c j := by
          intro i j hi hij hj
          induction j, hij using Nat.le_induction with
          | base => exact le_refl _
          | succ n hin ih =>
            have := hcinc n (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
            have := ih (by omega)
            linarith
        have hcost : ∀ x, cost M x = ∑ l ∈ Finset.Icc 1 M.L,
            M.c l * (min (M.θ l) (max (M.θ (l - 1)) x) - M.θ (l - 1)) := fun x => rfl
        have htele : ∀ n : ℕ, n ≤ M.L → ∀ x : ℝ, ∑ l ∈ Finset.Icc 1 n,
            (min (M.θ l) (max (M.θ (l - 1)) x) - M.θ (l - 1)) = min (M.θ n) (max M.θ0 x) - M.θ0 := by
          intro n
          induction n with
          | zero => intro _ x; simp [hθ0']
          | succ n ih =>
            intro hn x
            rw [Finset.sum_Icc_succ_top (by omega), ih (by omega) x]
            simp only [Nat.add_sub_cancel]
            have h1 := hθstep n hn
            have h2 := hθmono 0 n (Nat.zero_le _) (by omega)
            rw [hθ0'] at h2
            rcases le_total x M.θ0 with h | h <;> rcases le_total x (M.θ n) with h' | h' <;>
              rcases le_total x (M.θ (n+1)) with h'' | h'' <;>
              simp only [min_def, max_def] <;> split_ifs <;> linarith
        have hf : ∀ y x : ℝ, x ∈ Set.Icc M.θ0 (M.θ M.L) → y * x - cost M x = y * M.θ0 +
            ∑ l ∈ Finset.Icc 1 M.L, (y - M.c l) * (min (M.θ l) (max (M.θ (l - 1)) x) - M.θ (l - 1)) := by
          intro y x hx
          have ht := htele M.L le_rfl x
          have hm : min (M.θ M.L) (max M.θ0 x) = x := by
            rw [max_eq_right hx.1, min_eq_right hx.2]
          rw [hm] at ht
          rw [hcost]
          simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, ht]
          ring
        have key : ∀ y : ℝ, ∀ k : ℕ, k ≤ M.L → (∀ l ∈ Finset.Icc 1 M.L, l ≤ k → M.c l < y) →
            (∀ l ∈ Finset.Icc 1 M.L, k < l → y ≤ M.c l) →
            IsLeast {x : ℝ | x ∈ Set.Icc M.θ0 (M.θ M.L) ∧ y * x - cost M x = phi M y} (M.θ k) ∧
              psi M y = M.θ k := by
          intro y k hk H1 H2
          have hkA : M.θ k ∈ Set.Icc M.θ0 (M.θ M.L) :=
            ⟨by rw [← hθ0']; exact hθmono 0 k (Nat.zero_le _) hk, hθmono k M.L hk le_rfl⟩
          have hdiff : ∀ x ∈ Set.Icc M.θ0 (M.θ M.L), (y * x - cost M x) - (y * M.θ k - cost M (M.θ k))
              = ∑ l ∈ Finset.Icc 1 M.L, (y - M.c l) * ((min (M.θ l) (max (M.θ (l - 1)) x) - M.θ (l - 1))
                - (min (M.θ l) (max (M.θ (l - 1)) (M.θ k)) - M.θ (l - 1))) := by
            intro x hx
            rw [hf y x hx, hf y _ hkA, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl (fun l _ => by ring)
          have hterm : ∀ x ∈ Set.Icc M.θ0 (M.θ M.L), ∀ l ∈ Finset.Icc 1 M.L,
              (y - M.c l) * ((min (M.θ l) (max (M.θ (l - 1)) x) - M.θ (l - 1))
                - (min (M.θ l) (max (M.θ (l - 1)) (M.θ k)) - M.θ (l - 1))) ≤ 0 := by
            intro x hx l hl
            have hl' := Finset.mem_Icc.mp hl
            have hlθ := hθlt l hl'.1 hl'.2
            rcases le_or_gt l k with hlk | hlk
            · have hc := H1 l hl hlk
              have heq : min (M.θ l) (max (M.θ (l - 1)) (M.θ k)) = M.θ l :=
                min_eq_left (le_max_of_le_right (hθmono l k hlk hk))
              have hle : min (M.θ l) (max (M.θ (l - 1)) x) ≤ M.θ l := min_le_left _ _
              rw [heq]
              exact mul_nonpos_iff.mpr (Or.inl ⟨by linarith, by linarith⟩)
            · have hc := H2 l hl hlk
              have hk' := hθmono k (l - 1) (by omega) (by omega)
              have heq : min (M.θ l) (max (M.θ (l - 1)) (M.θ k)) = M.θ (l - 1) := by
                rw [max_eq_left hk', min_eq_right hlθ.le]
              have hge : M.θ (l - 1) ≤ min (M.θ l) (max (M.θ (l - 1)) x) :=
                le_min hlθ.le (le_max_left _ _)
              rw [heq]
              exact mul_nonpos_iff.mpr (Or.inr ⟨by linarith, by linarith⟩)
          have hle : ∀ x ∈ Set.Icc M.θ0 (M.θ M.L), y * x - cost M x ≤ y * M.θ k - cost M (M.θ k) := by
            intro x hx
            have h1 := hdiff x hx
            have h2 := Finset.sum_nonpos (hterm x hx)
            linarith
          have hstrict : ∀ x ∈ Set.Icc M.θ0 (M.θ M.L), x < M.θ k →
              y * x - cost M x < y * M.θ k - cost M (M.θ k) := by
            intro x hx hxk
            have hk1 : 1 ≤ k := by
              rcases Nat.eq_zero_or_pos k with h | h
              · subst h; rw [hθ0'] at hxk; linarith [hx.1]
              · exact h
            have hkmem : k ∈ Finset.Icc 1 M.L := Finset.mem_Icc.mpr ⟨hk1, hk⟩
            have hlt : (y - M.c k) * ((min (M.θ k) (max (M.θ (k - 1)) x) - M.θ (k - 1))
                - (min (M.θ k) (max (M.θ (k - 1)) (M.θ k)) - M.θ (k - 1))) < 0 := by
              have hc := H1 k hkmem le_rfl
              have hlθ := hθlt k hk1 hk
              have heq : min (M.θ k) (max (M.θ (k - 1)) (M.θ k)) = M.θ k := by
                rw [max_eq_right hlθ.le, min_self]
              have hlt' : min (M.θ k) (max (M.θ (k - 1)) x) < M.θ k :=
                lt_of_le_of_lt (min_le_right _ _) (max_lt hlθ hxk)
              rw [heq]
              exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
            have h2 := Finset.sum_lt_sum (hterm x hx) ⟨k, hkmem, hlt⟩
            rw [Finset.sum_const_zero] at h2
            have h1 := hdiff x hx
            linarith
          have hphi : phi M y = y * M.θ k - cost M (M.θ k) := by
            unfold phi
            apply IsGreatest.csSup_eq
            refine ⟨⟨M.θ k, hkA, rfl⟩, ?_⟩
            rintro _ ⟨x, hx, rfl⟩
            exact hle x hx
          have hLeast : IsLeast {x : ℝ | x ∈ Set.Icc M.θ0 (M.θ M.L) ∧ y * x - cost M x = phi M y}
              (M.θ k) := by
            refine ⟨⟨hkA, hphi.symm⟩, ?_⟩
            rintro x ⟨hx, hfx⟩
            by_contra h
            have := hstrict x hx (not_le.mp h)
            rw [hfx, hphi] at this
            exact lt_irrefl _ this
          refine ⟨hLeast, ?_⟩
          unfold psi
          exact hLeast.csInf_eq
        intro y
        classical
        have hex : ∃ k : ℕ, k = M.L ∨ y ≤ M.c (k+1) := ⟨M.L, Or.inl rfl⟩
        have hkspec := Nat.find_spec hex
        have hkmin : ∀ j < Nat.find hex, ¬ (j = M.L ∨ y ≤ M.c (j+1)) := fun j hj => Nat.find_min hex hj
        have hkL : Nat.find hex ≤ M.L := Nat.find_min' hex (Or.inl rfl)
        refine ⟨?_, ?_, ?_, ?_⟩
        · have H1 : ∀ l ∈ Finset.Icc 1 M.L, l ≤ Nat.find hex → M.c l < y := by
            intro l hl hlk
            have := Finset.mem_Icc.mp hl
            have h := hkmin (l - 1) (by omega)
            rw [Nat.sub_add_cancel this.1] at h
            push Not at h
            exact h.2
          have H2 : ∀ l ∈ Finset.Icc 1 M.L, Nat.find hex < l → y ≤ M.c l := by
            intro l hl hlk
            have := Finset.mem_Icc.mp hl
            rcases hkspec with h | h
            · omega
            · linarith [hcmono (Nat.find hex + 1) l (by omega) (by omega) this.2]
          have hK := key y (Nat.find hex) hkL H1 H2
          rw [hK.2]
          exact hK.1
        · intro hy
          rw [(key y 0 (Nat.zero_le _) ?_ ?_).2, hθ0']
          · intro l hl hl0
            have := (Finset.mem_Icc.mp hl).1
            omega
          · intro l hl _
            have := Finset.mem_Icc.mp hl
            linarith [hcmono 1 l le_rfl this.1 this.2]
        · intro m hm hlo hhi
          have hm' := Finset.mem_Icc.mp hm
          refine (key y (m - 1) (by omega) ?_ ?_).2
          · intro l hl hlk
            have := Finset.mem_Icc.mp hl
            linarith [hcmono l (m - 1) this.1 hlk (by omega)]
          · intro l hl hlk
            have := Finset.mem_Icc.mp hl
            linarith [hcmono m l (by omega) (by omega) this.2]
        · intro hy
          refine (key y M.L le_rfl ?_ ?_).2
          · intro l hl _
            have := Finset.mem_Icc.mp hl
            linarith [hcmono l M.L this.1 this.2 le_rfl]
          · intro l hl hlk
            have := Finset.mem_Icc.mp hl
            omega
