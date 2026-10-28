-- Prove2me | solution 1 for PayAsBid.SoftReserve.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:14:47.069761+00:00
-- url     : https://prove2.me/submissions/045eb6e9-ae0b-4166-8344-0f4d0e1a4a03

import Mathlib
import Definitions.Def_PayAsBid_SoftReserve_Model

open PayAsBid.SoftReserve in
theorem solution {n : ℕ} (hn : 1 ≤ n) (q : AssortFn n) (r : ℝ) (hq : IsEquitable q)
    (hRP : ReserveRP1 q r) (hTD : TotalDemandOne q r) :
    (∀ b : ℝ, 0 ≤ b → b ≤ r → q (fun _ => b) = fun _ => true) ∧
    (∀ b : Fin n → ℝ, Nonneg b → ∀ i, b i ≤ r → (∀ j, j ≠ i → b i ≤ b j) → q b i = true) := by
  obtain ⟨hAn, hMon⟩ := hq
  have P1 : ∀ b : ℝ, 0 ≤ b → b ≤ r → q (fun _ => b) = fun _ => true := by
    intro b hb0 hbr
    have hnn : Nonneg (fun _ : Fin n => b) := fun _ => hb0
    obtain ⟨i, hi⟩ := hTD (fun _ => b) hnn ⟨⟨0, by omega⟩, hbr⟩
    funext j
    have h := hAn (Equiv.swap i j) (fun _ => b) hnn
    have hc : ((fun _ : Fin n => b) ∘ (Equiv.swap i j)) = fun _ => b := rfl
    rw [hc] at h
    have := congrFun h j
    simp only [Function.comp_apply, Equiv.swap_apply_right] at this
    rw [this, hi]
  refine ⟨P1, ?_⟩
  intro b hb i hbi hmin
  let v : Finset (Fin n) → Fin n → ℝ := fun S k => if k ∈ S then b k else b i
  have hvnn : ∀ S, Nonneg (v S) := by
    intro S k
    simp only [v]
    split_ifs
    · exact hb k
    · exact hb i
  have key : ∀ S : Finset (Fin n), q (v S) i = true := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : v ∅ = fun _ => b i := by funext k; simp [v]
      rw [this, P1 (b i) (hb i) hbi]
    | insert j S hjS ih =>
      by_cases hji : j = i
      · have : v (insert j S) = v S := by
          funext k
          simp only [v, Finset.mem_insert]
          by_cases hk : k = j
          · subst hk; subst hji; simp
          · simp [hk]
        rw [this]; exact ih
      · rcases eq_or_lt_of_le (hmin j hji) with heq | hlt
        · have : v (insert j S) = v S := by
            funext k
            simp only [v, Finset.mem_insert]
            by_cases hk : k = j
            · subst hk; simp [hjS, heq]
            · simp [hk]
          rw [this]; exact ih
        · have hw : v (insert j S) j = b j := by simp [v]
          have hupd : Function.update (v (insert j S)) j (b i) = v S := by
            funext k
            by_cases hk : k = j
            · subst hk; simp [v, hjS]
            · rw [Function.update_of_ne hk]; simp [v, hk]
          have hm := (hMon (v (insert j S)) (hvnn _) j (b i) (hb i) (by rw [hw]; exact hlt)).2 i
            (Ne.symm hji)
          rw [hupd, ih] at hm
          cases h' : q (v (insert j S)) i
          · rw [h'] at hm; exact absurd hm (by decide)
          · rfl
  have : v Finset.univ = b := by funext k; simp [v]
  rw [← this]
  exact key _
