-- Prove2me | solution 1 for SRAudit.TwoPhase.Supplement.proposition_F_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:39.955244+00:00
-- url     : https://prove2.me/submissions/63689f66-0bdb-439c-8328-bc182fd4ad81

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
import Definitions.Def_SRAudit_TwoPhase_Supplement_Heterogeneous

open SRAudit
open SRAudit.TwoPhase
open SRAudit.TwoPhase.Supplement

open SRAudit.TwoPhase

theorem solution {ι : Type} [DecidableEq ι] (P : ParamsF) (hP : P.Standing)
    (π : Network ι → ℝ) (γ : State ι) :
    -- (F.1)
    VarF P π γ = π γ.g - min (P.u * P.w * P.z1) (P.a + P.u * P.r) * (γ.U.filter IsTier1).card -
      min (P.u * P.w * P.z2) (P.a + P.u * P.r) * (γ.U.filter (fun i => ¬ IsTier1 i)).card ∧
    -- (a)
    (P.a + P.u * P.r ≤ P.u * P.w * P.z1 → P.a + P.u * P.r ≤ P.u * P.w * P.z2 →
      ∀ i ∈ γ.U, QarF P π γ (.ar i) = VarF P π γ) ∧
    -- (b)
    (P.a + P.u * P.r ≤ P.u * P.w * P.z1 → P.u * P.w * P.z2 < P.a + P.u * P.r →
      (∀ i ∈ γ.U, IsTier1 i → QarF P π γ (.ar i) = VarF P π γ) ∧
      ((∀ i ∈ γ.U, ¬ IsTier1 i) → QarF P π γ .pp = VarF P π γ)) ∧
    -- (c)
    (P.u * P.w * P.z1 < P.a + P.u * P.r → P.a + P.u * P.r ≤ P.u * P.w * P.z2 →
      (∀ i ∈ γ.U, ¬ IsTier1 i → QarF P π γ (.ar i) = VarF P π γ) ∧
      ((∀ i ∈ γ.U, IsTier1 i) → QarF P π γ .pp = VarF P π γ)) ∧
    -- (d)
    (P.u * P.w * P.z1 < P.a + P.u * P.r → P.u * P.w * P.z2 < P.a + P.u * P.r →
      QarF P π γ .pp = VarF P π γ) := by
        set m1 := min (P.u * P.w * P.z1) (P.a + P.u * P.r) with hm1
        set m2 := min (P.u * P.w * P.z2) (P.a + P.u * P.r) with hm2
        have hm1le : m1 ≤ P.u * P.w * P.z1 := min_le_left _ _
        have hm2le : m2 ≤ P.u * P.w * P.z2 := min_le_left _ _
        have hm1le' : m1 ≤ P.a + P.u * P.r := min_le_right _ _
        have hm2le' : m2 ≤ P.a + P.u * P.r := min_le_right _ _
        -- removing one supplier
        have hstep : ∀ (δ : State ι), ∀ i ∈ δ.U,
            π (vet δ i).g - m1 * ((vet δ i).U.filter IsTier1).card -
              m2 * ((vet δ i).U.filter (fun i => ¬ IsTier1 i)).card =
            π δ.g - m1 * (δ.U.filter IsTier1).card -
              m2 * (δ.U.filter (fun i => ¬ IsTier1 i)).card + (if IsTier1 i then m1 else m2) := by
          intro δ i hi
          have hg : (vet δ i).g = δ.g := rfl
          have hU : (vet δ i).U = δ.U.erase i := rfl
          rw [hg, hU, Finset.filter_erase, Finset.filter_erase]
          by_cases ht : IsTier1 i
          · have h1 : i ∈ δ.U.filter IsTier1 := Finset.mem_filter.mpr ⟨hi, ht⟩
            have h2 : i ∉ δ.U.filter (fun i => ¬ IsTier1 i) := by simp [ht]
            rw [Finset.erase_eq_of_notMem h2, if_pos ht]
            have := Finset.card_erase_add_one h1
            have hc : (((δ.U.filter IsTier1).erase i).card : ℝ) + 1 = (δ.U.filter IsTier1).card := by
              exact_mod_cast this
            linear_combination (-m1) * hc
          · have h1 : i ∈ δ.U.filter (fun i => ¬ IsTier1 i) := Finset.mem_filter.mpr ⟨hi, ht⟩
            have h2 : i ∉ δ.U.filter IsTier1 := by simp [ht]
            rw [Finset.erase_eq_of_notMem h2, if_neg ht]
            have := Finset.card_erase_add_one h1
            have hc : (((δ.U.filter (fun i => ¬ IsTier1 i)).erase i).card : ℝ) + 1 =
                (δ.U.filter (fun i => ¬ IsTier1 i)).card := by
              exact_mod_cast this
            linear_combination (-m2) * hc
        have key : ∀ n, ∀ δ : State ι, δ.U.card = n →
            Vargen P.a (P.u * P.r) (ppValueF P π) δ = π δ.g - m1 * (δ.U.filter IsTier1).card -
              m2 * (δ.U.filter (fun i => ¬ IsTier1 i)).card := by
          intro n
          induction n using Nat.strong_induction_on with
          | _ n ih =>
          intro δ hn
          rw [Vargen]
          split_ifs with h
          · have hrec : ∀ i ∈ δ.U, Vargen P.a (P.u * P.r) (ppValueF P π) (vet δ i) =
                π (vet δ i).g - m1 * ((vet δ i).U.filter IsTier1).card -
                  m2 * ((vet δ i).U.filter (fun i => ¬ IsTier1 i)).card := fun i hi =>
              ih _ (hn ▸ vet_U_card_lt δ i hi) (vet δ i) rfl
            have hterm : ppValueF P π δ = π δ.g - (δ.U.filter IsTier1).card * (P.u * P.w * P.z1) -
                (δ.U.filter (fun i => ¬ IsTier1 i)).card * (P.u * P.w * P.z2) := by
              simp only [ppValueF, zetaF]; ring
            have hn1 : (0:ℝ) ≤ (δ.U.filter IsTier1).card := Nat.cast_nonneg _
            have hn2 : (0:ℝ) ≤ (δ.U.filter (fun i => ¬ IsTier1 i)).card := Nat.cast_nonneg _
            apply le_antisymm
            · apply max_le
              · rw [hterm]; nlinarith
              · apply Finset.sup'_le
                intro i _
                rw [hrec i.1 i.2, hstep δ i.1 i.2]
                split_ifs <;> linarith
            · by_cases hex : ∃ i ∈ δ.U, (if IsTier1 i then m1 else m2) = P.a + P.u * P.r
              · obtain ⟨i, hi, hie⟩ := hex
                apply le_max_of_le_right
                apply Finset.le_sup'_of_le _ (Finset.mem_attach _ ⟨i, hi⟩)
                simp only
                rw [hrec i hi, hstep δ i hi, hie]; linarith
              · push Not at hex
                apply le_max_of_le_left
                rw [hterm]
                have e1 : m1 * ((δ.U.filter IsTier1).card : ℝ) =
                    (δ.U.filter IsTier1).card * (P.u * P.w * P.z1) := by
                  rcases min_choice (P.u * P.w * P.z1) (P.a + P.u * P.r) with hc | hc
                  · rw [← hm1] at hc; rw [hc]; ring
                  · rw [← hm1] at hc
                    have : δ.U.filter IsTier1 = ∅ := by
                      rw [Finset.filter_eq_empty_iff]
                      intro i hi ht
                      have := hex i hi
                      rw [if_pos ht] at this
                      exact this hc
                    rw [this]; simp
                have e2 : m2 * ((δ.U.filter (fun i => ¬ IsTier1 i)).card : ℝ) =
                    (δ.U.filter (fun i => ¬ IsTier1 i)).card * (P.u * P.w * P.z2) := by
                  rcases min_choice (P.u * P.w * P.z2) (P.a + P.u * P.r) with hc | hc
                  · rw [← hm2] at hc; rw [hc]; ring
                  · rw [← hm2] at hc
                    have : δ.U.filter (fun i => ¬ IsTier1 i) = ∅ := by
                      rw [Finset.filter_eq_empty_iff]
                      intro i hi ht
                      have := hex i hi
                      rw [if_neg ht] at this
                      exact this hc
                    rw [this]; simp
                linarith
          · rw [Finset.not_nonempty_iff_eq_empty] at h
            simp [ppValueF, zetaF, h]
        have hV : VarF P π γ = π γ.g - m1 * (γ.U.filter IsTier1).card -
              m2 * (γ.U.filter (fun i => ¬ IsTier1 i)).card := key _ γ rfl
        have hQ : ∀ i ∈ γ.U, QarF P π γ (.ar i) = VarF P π γ - P.a - P.u * P.r +
            (if IsTier1 i then m1 else m2) := by
          intro i hi
          have : QarF P π γ (.ar i) = -P.a - P.u * P.r +
              Vargen P.a (P.u * P.r) (ppValueF P π) (vet γ i) := by
            simp only [QarF, Qargen, if_pos hi]
          rw [this, key _ (vet γ i) rfl, hstep γ i hi, hV]; ring
        have hpp : QarF P π γ .pp = π γ.g - (γ.U.filter IsTier1).card * (P.u * P.w * P.z1) -
                (γ.U.filter (fun i => ¬ IsTier1 i)).card * (P.u * P.w * P.z2) := by
          simp only [QarF, Qargen, ppValueF, zetaF]; ring
        refine ⟨hV, ?_, ?_, ?_, ?_⟩
        · intro h1 h2 i hi
          have e1 : m1 = P.a + P.u * P.r := min_eq_right h1
          have e2 : m2 = P.a + P.u * P.r := min_eq_right h2
          rw [hQ i hi]; split_ifs <;> linarith
        · intro h1 h2
          have e1 : m1 = P.a + P.u * P.r := min_eq_right h1
          have e2 : m2 = P.u * P.w * P.z2 := min_eq_left h2.le
          refine ⟨fun i hi ht => ?_, fun hall => ?_⟩
          · rw [hQ i hi, if_pos ht]; linarith
          · have : γ.U.filter IsTier1 = ∅ := Finset.filter_eq_empty_iff.mpr hall
            rw [hpp, hV, this, e2]; simp; ring
        · intro h1 h2
          have e1 : m1 = P.u * P.w * P.z1 := min_eq_left h1.le
          have e2 : m2 = P.a + P.u * P.r := min_eq_right h2
          refine ⟨fun i hi ht => ?_, fun hall => ?_⟩
          · rw [hQ i hi, if_neg ht]; linarith
          · have : γ.U.filter (fun i => ¬ IsTier1 i) = ∅ :=
              Finset.filter_eq_empty_iff.mpr (fun i hi ht => ht (hall i hi))
            rw [hpp, hV, this, e1]; simp; ring
        · intro h1 h2
          have e1 : m1 = P.u * P.w * P.z1 := min_eq_left h1.le
          have e2 : m2 = P.u * P.w * P.z2 := min_eq_left h2.le
          rw [hpp, hV, e1, e2]; ring
