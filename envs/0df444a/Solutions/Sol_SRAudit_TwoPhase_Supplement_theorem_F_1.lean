-- Prove2me | solution 1 for SRAudit.TwoPhase.Supplement.theorem_F_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:48.540107+00:00
-- url     : https://prove2.me/submissions/0d5ccd0e-716f-46b8-b045-4fbf8826230b

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
import Definitions.Def_SRAudit_TwoPhase_Supplement_Heterogeneous

open SRAudit
open SRAudit.TwoPhase
open SRAudit.TwoPhase.Supplement

open SRAudit.TwoPhase

theorem solution {ι : Type} [DecidableEq ι] (P : ParamsF) (hP : P.Standing)
    (π : Network ι → ℝ) :
    ∃ ξ : Policy ι, IsOptimalF P π ξ ∧
      -- an `ar` action belongs to the rp subphase: it rectifies a supplier of a tier `k` with
      -- `a + ur ≤ uwz_k`, every such supplier may be rectified next, and afterwards the policy
      -- keeps rectifying while such a supplier remains unaudited, then proceeds to production
      (∀ (γ : State ι) (i : Supplier ι), ξ γ = .ar i →
        P.a + P.u * P.r ≤ P.u * P.w * P.zOf i ∧
        ∀ j ∈ γ.U, P.a + P.u * P.r ≤ P.u * P.w * P.zOf j →
          QstarF P π γ (.ar j) = VstarF P π γ ∧
          ((∃ k ∈ (vet γ j).U, P.a + P.u * P.r ≤ P.u * P.w * P.zOf k) →
            ∃ k, ξ (vet γ j) = .ar k) ∧
          ((∀ k ∈ (vet γ j).U, P.u * P.w * P.zOf k < P.a + P.u * P.r) →
            ξ (vet γ j) = .pp)) ∧
      -- `pp` leaves unaudited only suppliers of tiers `k` with `a + ur > uwz_k`
      (∀ γ : State ι, ξ γ = .pp → ∀ j ∈ γ.U, P.u * P.w * P.zOf j < P.a + P.u * P.r) := by
        classical
        obtain ⟨ha, hr, hu0, hu1, hw0, hw1, hz1, hz2⟩ := hP
        have hV : ∀ γ, VstarF P π γ = Vgen P.a (P.u * P.r) P.u (ppValueF P π) γ := fun γ => rfl
        have Vge_pp : ∀ γ : State ι, ppValueF P π γ ≤ VstarF P π γ := by
          intro γ
          rw [hV, Vgen.eq_def]
          split_ifs with h
          · exact le_max_left _ _
          · exact le_rfl
        have Vge_ar : ∀ (γ : State ι) (i : Supplier ι), i ∈ γ.U →
            -P.a - P.u * P.r + VstarF P π (vet γ i) ≤ VstarF P π γ := by
          intro γ i hi
          rw [hV γ, Vgen.eq_def]
          split_ifs with h
          · refine le_max_of_le_right (le_trans (le_max_left _ _)
              (Finset.le_sup' (fun i : {x // x ∈ γ.U} => max (-P.a - P.u * P.r + Vgen P.a (P.u * P.r) P.u (ppValueF P π) (vet γ i.val))
                  (-P.a + (1 - P.u) * Vgen P.a (P.u * P.r) P.u (ppValueF P π) (vet γ i.val) + P.u * Vgen P.a (P.u * P.r) P.u (ppValueF P π) (drop γ i.val))) (Finset.mem_attach _ ⟨i, hi⟩)))
          · exact absurd ⟨i, hi⟩ h
        have Vge_ad : ∀ (γ : State ι) (i : Supplier ι), i ∈ γ.U →
            -P.a + (1 - P.u) * VstarF P π (vet γ i) + P.u * VstarF P π (drop γ i) ≤ VstarF P π γ := by
          intro γ i hi
          rw [hV γ, Vgen.eq_def]
          split_ifs with h
          · refine le_max_of_le_right (le_trans (le_max_right _ _)
              (Finset.le_sup' (fun i : {x // x ∈ γ.U} => max (-P.a - P.u * P.r + Vgen P.a (P.u * P.r) P.u (ppValueF P π) (vet γ i.val))
                  (-P.a + (1 - P.u) * Vgen P.a (P.u * P.r) P.u (ppValueF P π) (vet γ i.val) + P.u * Vgen P.a (P.u * P.r) P.u (ppValueF P π) (drop γ i.val))) (Finset.mem_attach _ ⟨i, hi⟩)))
          · exact absurd ⟨i, hi⟩ h
        have Vcases : ∀ γ : State ι, VstarF P π γ = ppValueF P π γ ∨ ∃ i ∈ γ.U,
            VstarF P π γ = -P.a - P.u * P.r + VstarF P π (vet γ i) ∨
            VstarF P π γ = -P.a + (1 - P.u) * VstarF P π (vet γ i) + P.u * VstarF P π (drop γ i) := by
          intro γ
          rw [hV γ, Vgen.eq_def]
          split_ifs with h
          · rcases max_choice (ppValueF P π γ) (γ.U.attach.sup' (by simpa using h) (fun i : {x // x ∈ γ.U} => max (-P.a - P.u * P.r + Vgen P.a (P.u * P.r) P.u (ppValueF P π) (vet γ i.val))
                  (-P.a + (1 - P.u) * Vgen P.a (P.u * P.r) P.u (ppValueF P π) (vet γ i.val) + P.u * Vgen P.a (P.u * P.r) P.u (ppValueF P π) (drop γ i.val)))) with h1 | h1
            · left; exact h1
            · right
              rw [h1]
              obtain ⟨⟨i, hi⟩, -, h2⟩ := Finset.exists_mem_eq_sup' (γ.U.attach_nonempty_iff.mpr h) (fun i : {x // x ∈ γ.U} => max (-P.a - P.u * P.r + Vgen P.a (P.u * P.r) P.u (ppValueF P π) (vet γ i.val))
                  (-P.a + (1 - P.u) * Vgen P.a (P.u * P.r) P.u (ppValueF P π) (vet γ i.val) + P.u * Vgen P.a (P.u * P.r) P.u (ppValueF P π) (drop γ i.val)))
              refine ⟨i, hi, ?_⟩
              rw [h2]
              exact max_choice _ _
          · left; rfl
        have zeta_nn : ∀ i : Supplier ι, 0 ≤ P.u * P.w * P.zOf i := by
          intro i; cases i <;> simp only [ParamsF.zOf] <;> positivity
        have stEq : ∀ s t : State ι, s.g = t.g → s.U = t.U → s = t := by
          rintro ⟨g, U, h⟩ ⟨g', U', h'⟩ hg hU
          simp only at hg hU
          subst hg; subst hU; rfl
        have zsum : ∀ γ : State ι, zetaF P γ = ∑ j ∈ γ.U, P.u * P.w * P.zOf j := by
          intro γ
          rw [← Finset.sum_filter_add_sum_filter_not γ.U IsTier1]
          unfold zetaF
          congr 1
          · rw [Finset.sum_congr rfl (g := fun _ => P.u * P.w * P.z1), Finset.sum_const, nsmul_eq_mul]
            intro j hj
            simp only [Finset.mem_filter] at hj
            cases j with
            | t1 x => rfl
            | t2 x => exact absurd hj.2 (by simp [IsTier1])
          · rw [Finset.sum_congr rfl (g := fun _ => P.u * P.w * P.z2), Finset.sum_const, nsmul_eq_mul]
            intro j hj
            simp only [Finset.mem_filter] at hj
            cases j with
            | t1 x => exact absurd hj.2 (by simp [IsTier1])
            | t2 x => rfl
        have T_vet : ∀ (γ : State ι) (i : Supplier ι), i ∈ γ.U →
            ppValueF P π (vet γ i) = ppValueF P π γ + P.u * P.w * P.zOf i := by
          intro γ i hi
          unfold ppValueF
          rw [zsum, zsum, ← Finset.add_sum_erase γ.U _ hi]
          simp only [vet]
          ring
        have vet_U : ∀ (γ : State ι) (i : Supplier ι), (vet γ i).U = γ.U.erase i := fun γ i => rfl
        have drop_U : ∀ (γ : State ι) (k : Supplier ι), (drop γ k).U = γ.U \ γ.g.dependents k := fun γ k => rfl
        have vet_vet : ∀ (γ : State ι) (i j : Supplier ι), vet (vet γ i) j = vet (vet γ j) i := by
          intro γ i j
          exact stEq _ _ rfl (by simp only [vet_U]; exact Finset.erase_right_comm)
        have drop_vet_in : ∀ (γ : State ι) (i k : Supplier ι), i ∈ γ.g.dependents k →
            drop (vet γ i) k = drop γ k := by
          intro γ i k hik
          refine stEq _ _ rfl ?_
          rw [drop_U, drop_U, vet_U]
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_erase]
          constructor
          · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨fun h => h2 (h ▸ hik), h1⟩, h2⟩
        have drop_vet_out : ∀ (γ : State ι) (i k : Supplier ι), i ∉ γ.g.dependents k →
            drop (vet γ i) k = vet (drop γ k) i := by
          intro γ i k hik
          refine stEq _ _ rfl ?_
          rw [drop_U, vet_U, vet_U, drop_U]
          rw [Finset.erase_sdiff_comm]; rfl
        have vet_g : ∀ (γ : State ι) (i : Supplier ι), (vet γ i).g = γ.g := fun γ i => rfl
        have LA : ∀ n, ∀ γ : State ι, γ.U.card = n → ∀ i ∈ γ.U,
            VstarF P π (vet γ i) ≤ VstarF P π γ + P.u * P.w * P.zOf i := by
          intro n
          induction n using Nat.strong_induction_on with
          | _ n ih =>
          intro γ hn i hi
          rcases Vcases (vet γ i) with h | ⟨k, hk, h | h⟩
          · rw [h, T_vet γ i hi]; linarith [Vge_pp γ]
          · rw [vet_U] at hk
            obtain ⟨hki, hkU⟩ := Finset.mem_erase.mp hk
            have h1 := ih _ (hn ▸ vet_U_card_lt γ k hkU) (vet γ k) rfl i
              (by rw [vet_U]; exact Finset.mem_erase.mpr ⟨Ne.symm hki, hi⟩)
            rw [vet_vet] at h; rw [h]; linarith [Vge_ar γ k hkU]
          · rw [vet_U] at hk
            obtain ⟨hki, hkU⟩ := Finset.mem_erase.mp hk
            have h1 := ih _ (hn ▸ vet_U_card_lt γ k hkU) (vet γ k) rfl i
              (by rw [vet_U]; exact Finset.mem_erase.mpr ⟨Ne.symm hki, hi⟩)
            have h2 : VstarF P π (drop (vet γ i) k) ≤ VstarF P π (drop γ k) + P.u * P.w * P.zOf i := by
              by_cases hd : i ∈ γ.g.dependents k
              · rw [drop_vet_in γ i k hd]; linarith [zeta_nn i]
              · rw [drop_vet_out γ i k hd]
                exact ih _ (hn ▸ drop_U_card_lt γ k hkU) _ rfl i
                  (by rw [drop_U]; exact Finset.mem_sdiff.mpr ⟨hi, hd⟩)
            rw [vet_vet] at h; rw [h]
            have h3 := Vge_ad γ k hkU
            have h4 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hu1.le)
            have h5 := mul_le_mul_of_nonneg_left h2 hu0.le
            nlinarith
        obtain ⟨R, hR⟩ : ∃ R : State ι → ℝ, ∀ γ, R γ = ppValueF P π γ +
            ∑ j ∈ γ.U.filter (fun j => P.a + P.u * P.r ≤ P.u * P.w * P.zOf j),
              (P.u * P.w * P.zOf j - (P.a + P.u * P.r)) := ⟨_, fun γ => rfl⟩
        have R_vet : ∀ (γ : State ι) (i : Supplier ι), i ∈ γ.U → P.a + P.u * P.r ≤ P.u * P.w * P.zOf i →
            R (vet γ i) = R γ + (P.a + P.u * P.r) := by
          intro γ i hi hq
          rw [hR, hR, T_vet γ i hi, vet_U, Finset.filter_erase,
            ← Finset.add_sum_erase (γ.U.filter _) _ (Finset.mem_filter.mpr ⟨hi, hq⟩)]
          ring
        have T_le_R : ∀ γ : State ι, ppValueF P π γ ≤ R γ := by
          intro γ
          rw [hR]
          have : 0 ≤ ∑ j ∈ γ.U.filter (fun j => P.a + P.u * P.r ≤ P.u * P.w * P.zOf j),
              (P.u * P.w * P.zOf j - (P.a + P.u * P.r)) := by
            apply Finset.sum_nonneg
            intro j hj
            have := (Finset.mem_filter.mp hj).2
            linarith
          linarith
        have R_noq : ∀ γ : State ι, (∀ j ∈ γ.U, ¬ P.a + P.u * P.r ≤ P.u * P.w * P.zOf j) →
            R γ = ppValueF P π γ := by
          intro γ h
          rw [hR, Finset.filter_eq_empty_iff.mpr h, Finset.sum_empty, add_zero]
        have R_le_V : ∀ n, ∀ γ : State ι, γ.U.card = n → R γ ≤ VstarF P π γ := by
          intro n
          induction n using Nat.strong_induction_on with
          | _ n ih =>
          intro γ hn
          by_cases hq : ∃ j ∈ γ.U, P.a + P.u * P.r ≤ P.u * P.w * P.zOf j
          · obtain ⟨j, hj, hq⟩ := hq
            have h1 := ih _ (hn ▸ vet_U_card_lt γ j hj) (vet γ j) rfl
            rw [R_vet γ j hj hq] at h1
            linarith [Vge_ar γ j hj]
          · rw [R_noq γ (fun j hj hqj => hq ⟨j, hj, hqj⟩)]
            exact Vge_pp γ
        have LI : ∀ (γ : State ι) (i k : Supplier ι), i ∈ γ.U → k ∈ γ.U → i ≠ k →
            -P.a + (1 - P.u) * VstarF P π (vet (vet γ i) k) + P.u * VstarF P π (drop (vet γ i) k)
              - (P.a + P.u * P.r) ≤
            -P.a + (1 - P.u) * VstarF P π (vet γ k) + P.u * VstarF P π (drop γ k) := by
          intro γ i k hi hk hik
          have h1 := Vge_ar (vet γ k) i (by rw [vet_U]; exact Finset.mem_erase.mpr ⟨hik, hi⟩)
          rw [vet_vet] at h1
          have h2 : VstarF P π (drop (vet γ i) k) - (P.a + P.u * P.r) ≤ VstarF P π (drop γ k) := by
            by_cases hd : i ∈ γ.g.dependents k
            · rw [drop_vet_in γ i k hd]
              have : 0 ≤ P.u * P.r := mul_nonneg hu0.le hr
              linarith
            · rw [drop_vet_out γ i k hd]
              have := Vge_ar (drop γ k) i (by rw [drop_U]; exact Finset.mem_sdiff.mpr ⟨hi, hd⟩)
              linarith
          have h4 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hu1.le)
          have h5 := mul_le_mul_of_nonneg_left h2 hu0.le
          nlinarith
        have LC : ∀ n, ∀ γ : State ι, γ.U.card = n → R γ < VstarF P π γ → ∃ k ∈ γ.U,
            -P.a + (1 - P.u) * VstarF P π (vet γ k) + P.u * VstarF P π (drop γ k) = VstarF P π γ := by
          intro n
          induction n using Nat.strong_induction_on with
          | _ n ih =>
          intro γ hn hlt
          rcases Vcases γ with h | ⟨i, hi, h | h⟩
          · linarith [T_le_R γ]
          · by_cases hq : P.a + P.u * P.r ≤ P.u * P.w * P.zOf i
            · have h1 : R (vet γ i) < VstarF P π (vet γ i) := by
                rw [R_vet γ i hi hq]; linarith
              obtain ⟨k, hk, h2⟩ := ih _ (hn ▸ vet_U_card_lt γ i hi) (vet γ i) rfl h1
              rw [vet_U] at hk
              obtain ⟨hki, hkU⟩ := Finset.mem_erase.mp hk
              refine ⟨k, hkU, le_antisymm (Vge_ad γ k hkU) ?_⟩
              have := LI γ i k hi hkU (Ne.symm hki)
              linarith
            · have := LA _ γ rfl i hi
              linarith
          · exact ⟨i, hi, h.symm⟩
        have D0 : ∀ γ : State ι, ¬ (∃ k ∈ γ.U,
            -P.a + (1 - P.u) * VstarF P π (vet γ k) + P.u * VstarF P π (drop γ k) = VstarF P π γ) →
            VstarF P π γ = R γ := by
          intro γ hG
          refine le_antisymm ?_ (R_le_V _ γ rfl)
          by_contra hlt
          exact hG (LC _ γ rfl (lt_of_not_ge hlt))
        have D1 : ∀ γ : State ι, ¬ (∃ k ∈ γ.U,
            -P.a + (1 - P.u) * VstarF P π (vet γ k) + P.u * VstarF P π (drop γ k) = VstarF P π γ) →
            ∀ j ∈ γ.U, P.a + P.u * P.r ≤ P.u * P.w * P.zOf j →
            -P.a - P.u * P.r + VstarF P π (vet γ j) = VstarF P π γ ∧
            ¬ (∃ k ∈ (vet γ j).U,
            -P.a + (1 - P.u) * VstarF P π (vet (vet γ j) k) + P.u * VstarF P π (drop (vet γ j) k)
              = VstarF P π (vet γ j)) := by
          intro γ hG j hj hq
          have e1 := D0 γ hG
          have e2 := R_le_V _ (vet γ j) rfl
          rw [R_vet γ j hj hq] at e2
          have e3 : -P.a - P.u * P.r + VstarF P π (vet γ j) = VstarF P π γ :=
            le_antisymm (Vge_ar γ j hj) (by linarith)
          refine ⟨e3, ?_⟩
          rintro ⟨k, hk, hk2⟩
          rw [vet_U] at hk
          obtain ⟨hkj, hkU⟩ := Finset.mem_erase.mp hk
          have := LI γ j k hj hkU (Ne.symm hkj)
          exact hG ⟨k, hkU, le_antisymm (Vge_ad γ k hkU) (by linarith)⟩
        obtain ⟨ξ, hξ⟩ : ∃ ξ : Policy ι, ∀ γ, ξ γ =
            if h : ∃ k ∈ γ.U, -P.a + (1 - P.u) * VstarF P π (vet γ k) + P.u * VstarF P π (drop γ k)
                = VstarF P π γ then Action.ad h.choose
            else if h2 : ∃ j ∈ γ.U, P.a + P.u * P.r ≤ P.u * P.w * P.zOf j then Action.ar h2.choose
            else Action.pp := ⟨_, fun _ => rfl⟩
        refine ⟨ξ, ?_, ?_, ?_⟩
        · unfold IsOptimalF IsOptimalGen
          refine ⟨?_, ?_⟩
          · intro γ
            rw [hξ γ]
            split_ifs with h1 h2
            · exact h1.choose_spec.1
            · exact h2.choose_spec.1
            · trivial
          · intro γ
            rw [hξ γ]
            split_ifs with h1 h2
            · simp only [Qgen, if_pos h1.choose_spec.1]
              exact h1.choose_spec.2
            · simp only [Qgen, if_pos h2.choose_spec.1]
              exact (D1 γ h1 _ h2.choose_spec.1 h2.choose_spec.2).1
            · simp only [Qgen]
              rw [← hV, D0 γ h1, R_noq γ (fun j hj hqj => h2 ⟨j, hj, hqj⟩)]
        · intro γ i hξi
          rw [hξ γ] at hξi
          split_ifs at hξi with h1 h2
          · cases hξi
            refine ⟨h2.choose_spec.2, ?_⟩
            intro j hj hq
            obtain ⟨e1, hG'⟩ := D1 γ h1 j hj hq
            refine ⟨?_, ?_, ?_⟩
            · simp only [QstarF, Qgen, if_pos hj]
              exact e1
            · rintro ⟨k, hk, hqk⟩
              rw [hξ (vet γ j), dif_neg hG', dif_pos ⟨k, hk, hqk⟩]
              exact ⟨_, rfl⟩
            · intro hall
              rw [hξ (vet γ j), dif_neg hG', dif_neg]
              rintro ⟨k, hk, hqk⟩
              linarith [hall k hk]
        · intro γ hp j hj
          rw [hξ γ] at hp
          split_ifs at hp with h1 h2
          exact lt_of_not_ge (fun hq => h2 ⟨j, hj, hq⟩)
