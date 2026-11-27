-- Prove2me | solution 1 for SRAudit.TwoPhase.Supplement.proposition_G_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:38:04.469404+00:00
-- url     : https://prove2.me/submissions/ddbbadea-0bb3-4d4f-bb0e-5eb7717842cc

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
import Definitions.Def_SRAudit_TwoPhase_Supplement_Inaccurate

open SRAudit
open SRAudit.TwoPhase
open SRAudit.TwoPhase.Supplement

open SRAudit.TwoPhase

theorem solution {ι : Type} [DecidableEq ι] (P : Params) (d : ℝ) (hP : StandingG P d)
    (π : Network ι → ℝ) (γ : State ι) :
    VarG P d ∅ π γ = π γ.g - uhat P d * P.w * P.z * γ.g.suppliers.card -
      min (P.a + P.u * d * P.r) ((P.u - uhat P d) * P.w * P.z) * γ.U.card ∧
    (P.a + P.u * d * P.r ≤ (P.u - uhat P d) * P.w * P.z →
      ∀ i ∈ γ.U, QarG P d ∅ π γ (.ar i) = VarG P d ∅ π γ) ∧
    ((P.u - uhat P d) * P.w * P.z ≤ P.a + P.u * d * P.r →
      QarG P d ∅ π γ .pp = VarG P d ∅ π γ) := by
        classical
        let A := P.a + P.u * d * P.r
        let B := (P.u - uhat P d) * P.w * P.z
        let m := min A B
        let K := fun δ : State ι => π δ.g - uhat P d * P.w * P.z * δ.g.suppliers.card
        have hpp (δ : State ι) : ppValueG P d ∅ π δ = K δ - B * δ.U.card := by
          have hc : (((δ.g.suppliers \ δ.U).card : ℕ) : ℝ) + δ.U.card =
              δ.g.suppliers.card := by
            exact_mod_cast Finset.card_sdiff_add_card_eq_card δ.hU
          have hc' : (((δ.g.suppliers \ δ.U).card : ℕ) : ℝ) =
              δ.g.suppliers.card - δ.U.card := by linarith
          simp only [ppValueG, zetaG, Finset.sdiff_empty]
          rw [hc']
          dsimp [K, B]
          ring
        have hvalue : ∀ n (δ : State ι), δ.U.card = n →
            VarG P d ∅ π δ = K δ - m * δ.U.card := by
          intro n
          induction n using Nat.strong_induction_on with
          | h n ih =>
            intro δ hn
            rw [VarG, Vargen.eq_def]
            by_cases hne : δ.U.Nonempty
            · rw [dif_pos hne, hpp]
              have haudit (i : Supplier ι) (hi : i ∈ δ.U) :
                  -P.a - P.u * d * P.r + VarG P d ∅ π (vet δ i) =
                    K δ - A - m * ((δ.U.card : ℝ) - 1) := by
                have hv := ih (vet δ i).U.card (by rw [← hn]; exact vet_U_card_lt δ i hi)
                  (vet δ i) rfl
                have hc : ((vet δ i).U.card : ℝ) + 1 = δ.U.card := by
                  exact_mod_cast Finset.card_erase_add_one hi
                have hk : K (vet δ i) = K δ := rfl
                rw [hv, hk]
                have hc' : ((vet δ i).U.card : ℝ) = (δ.U.card : ℝ) - 1 := by linarith
                rw [hc']
                dsimp [A]
                ring
              have hs : δ.U.attach.sup' (by simpa using hne)
                  (fun i => -P.a - P.u * d * P.r +
                    Vargen P.a (P.u * d * P.r) (ppValueG P d ∅ π) (vet δ i.val)) =
                    K δ - A - m * ((δ.U.card : ℝ) - 1) := by
                apply Finset.sup'_eq_of_forall
                intro i hi
                exact haudit i.val i.property
              rw [hs]
              have hc0 : (0 : ℝ) ≤ δ.U.card := Nat.cast_nonneg _
              rcases le_total A B with hab | hba
              · have hm : m = A := min_eq_left hab
                rw [hm]
                have hh : K δ - A - A * ((δ.U.card : ℝ) - 1) =
                    K δ - A * δ.U.card := by ring
                rw [hh, max_eq_right]
                nlinarith [mul_le_mul_of_nonneg_right hab hc0]
              · have hm : m = B := min_eq_right hba
                rw [hm]
                apply max_eq_left
                nlinarith
            · rw [dif_neg hne, hpp]
              have hz : δ.U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
              simp [hz]
        have hv (δ : State ι) := hvalue δ.U.card δ rfl
        refine ⟨hv γ, ?_, ?_⟩
        · intro hab i hi
          change (if i ∈ γ.U then -P.a - P.u * d * P.r +
            VarG P d ∅ π (vet γ i) else 0) = VarG P d ∅ π γ
          rw [if_pos hi, hv, hv]
          have hc : ((vet γ i).U.card : ℝ) + 1 = γ.U.card := by
            exact_mod_cast Finset.card_erase_add_one hi
          have hk : K (vet γ i) = K γ := rfl
          have hm : m = A := min_eq_left hab
          rw [hk, hm]
          have hc' : ((vet γ i).U.card : ℝ) = (γ.U.card : ℝ) - 1 := by linarith
          rw [hc']
          dsimp [A]
          ring
        · intro hba
          change ppValueG P d ∅ π γ = VarG P d ∅ π γ
          rw [hpp, hv]
          have hm : m = B := min_eq_right hba
          rw [hm]
