-- Prove2me | solution 1 for SubspaceEvasion312.Explicit.zero_error_recovery
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:05:32.433817+00:00
-- url     : https://prove2.me/submissions/a6a0c695-b9e7-4ebf-9072-a72cad454746
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SubspaceEvasion312_Explicit_algebra
import Theorems.Thm_SubspaceEvasion312_Explicit_design_list_recovery

section
set_option autoImplicit false

namespace SubspaceEvasion312.Explicit.Dev.Cond
open SubspaceEvasion312.Explicit

theorem rec_mem {F : Type} [Field F] {s m : ℕ} (C : Code F s m)
    (U : Submodule F (Blocks F s m)) (S : Fin m → Finset (Vec F s))
    {c : Blocks F s m} (hc : c ∈ recovered C U S 0) : c ∈ C ∧ c ∈ U ∧ ∀ i, c i ∈ S i := by
  obtain ⟨h1, h2, y, hy, hh⟩ := hc
  refine ⟨h1, h2, fun i => ?_⟩
  have h0 : hamming c y = 0 := by
    have : (hamming c y : ℝ) ≤ 0 := by simpa using hh
    exact_mod_cast le_antisymm (by exact_mod_cast this) (Nat.zero_le _)
  have : c i = y i := by
    by_contra hne
    have : 0 < hamming c y := by
      unfold hamming
      classical
      exact Finset.card_pos.mpr ⟨i, by simp [hne]⟩
    omega
  rw [this]; exact hy i

end SubspaceEvasion312.Explicit.Dev.Cond

namespace SubspaceEvasion312.Explicit
end SubspaceEvasion312.Explicit
end

section
set_option autoImplicit false

namespace SubspaceEvasion312.Explicit.Dev.Zero
open SubspaceEvasion312.Explicit
open scoped ENNReal

theorem lr_zero {F : Type} [Field F] {s m r : ℕ} (hm : 0 < m) (C : Code F s m) :
    ListRecoverable C r 0 0 0 := by
  intro U hU S hS T hT
  have : T = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro c hc
    have h := (Dev.Cond.rec_mem C U S (hT hc)).2.2 ⟨0, hm⟩
    have h0 : S ⟨0, hm⟩ = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (hS _))
    simp [h0] at h
  simp [this]

theorem lr_one {F : Type} [Field F] {s m r : ℕ} (C : Code F s m) :
    ListRecoverable C r 0 1 2 := by
  intro U hU S hS T hT
  have h1 : T.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    funext i
    have h1 := (Dev.Cond.rec_mem C U S (hT ha)).2.2 i
    have h2 := (Dev.Cond.rec_mem C U S (hT hb)).2.2 i
    exact Finset.card_le_one.mp (hS i) _ h1 _ h2
  calc (T.card : ℝ≥0∞) ≤ 1 := by exact_mod_cast h1
    _ ≤ 2 := by norm_num

theorem lr_mono {F : Type} [Field F] {s m r ℓ : ℕ} {C : Code F s m} {L L' : ℝ≥0∞}
    (h : ListRecoverable C r 0 ℓ L) (hle : L ≤ L') : ListRecoverable C r 0 ℓ L' :=
  fun U hU S hS T hT => (h U hU S hS T hT).trans hle

theorem main {F : Type} [Field F] [Fintype F] {s m r : ℕ} (hm : 0 < m) (C : Code F s m) (τ : ℕ → ℝ)
    (hC : SubspaceDesign C τ) (ℓ : ℕ) : ListRecoverable C r 0 ℓ (zeroErrorBound ℓ (τ r)) := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    simpa [zeroErrorBound] using lr_zero (r := r) hm C
  · unfold zeroErrorBound
    simp only [hℓ, if_false]
    by_cases hτ : τ r < 1
    · simp only [hτ, if_true]
      have h := design_list_recovery (r := r) (ℓ := ℓ) hm C τ hC (1 - τ r) (by linarith) (by linarith)
      have e1 : 1 - τ r - (1 - τ r) = 0 := by ring
      have e2 : τ r + (1 - τ r) = 1 := by ring
      rw [e1, e2, div_one] at h
      exact h
    · simp only [hτ, if_false]
      exact fun U hU S hS T hT => le_top

theorem bound_two {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (t : ℝ) (ht : t ≤ 1 / (1 + log₂ (ℓ : ℝ))) :
    t < 1 ∧ (ℓ : ℝ) ^ (1 / (1 - t)) ≤ 2 * ℓ := by
  have hl : (1 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hl2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL : 1 ≤ log₂ (ℓ : ℝ) := by
    unfold log₂
    rw [le_div_iff₀ (Real.log_pos (by norm_num))]
    simpa using Real.log_le_log (by norm_num) hl2
  have hLpos : 0 < log₂ (ℓ : ℝ) := by linarith
  have h1 : 0 < 1 + log₂ (ℓ : ℝ) := by linarith
  have ht1 : t ≤ 1 / (1 + log₂ (ℓ : ℝ)) := ht
  have hlt : 1 / (1 + log₂ (ℓ : ℝ)) < 1 := by
    rw [div_lt_one h1]; linarith
  refine ⟨lt_of_le_of_lt ht1 hlt, ?_⟩
  set L := log₂ (ℓ : ℝ) with hLdef
  have hpos : 0 < 1 - t := by linarith [lt_of_le_of_lt ht1 hlt]
  have hexp : 1 / (1 - t) ≤ 1 + 1 / L := by
    rw [div_le_iff₀ hpos]
    have : t ≤ 1 / (1 + L) := ht1
    have h2 : t * (1 + L) ≤ 1 := by
      calc t * (1 + L) ≤ 1 / (1 + L) * (1 + L) := mul_le_mul_of_nonneg_right this h1.le
        _ = 1 := by field_simp
    have h3 : (1 + 1 / L) * (1 - t) = (1 + 1 / L) - (1 + 1/L) * t := by ring
    have h4 : (1 + 1 / L) * t = (1 / L) * (t * (1 + L)) := by field_simp; ring
    have h5 : (1 / L) * (t * (1 + L)) ≤ 1 / L := by
      calc (1 / L) * (t * (1 + L)) ≤ (1 / L) * 1 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 1 / L := by ring
    nlinarith
  have hpow : (ℓ : ℝ) ^ (1 + 1 / L) = 2 * ℓ := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
    have : (ℓ : ℝ) ^ (1 / L) = 2 := by
      rw [hLdef]; unfold log₂
      rw [one_div, inv_div, Real.rpow_def_of_pos (by linarith)]
      have hl0 : Real.log (ℓ : ℝ) ≠ 0 := (Real.log_pos hl).ne'
      rw [mul_div_cancel₀ _ hl0, Real.exp_log (by norm_num)]
    rw [this]; ring
  calc (ℓ : ℝ) ^ (1 / (1 - t)) ≤ (ℓ : ℝ) ^ (1 + 1 / L) :=
        Real.rpow_le_rpow_of_exponent_le hl.le hexp
    _ = 2 * ℓ := hpow

end SubspaceEvasion312.Explicit.Dev.Zero

namespace SubspaceEvasion312.Explicit
open scoped ENNReal
open SubspaceEvasion312.Explicit.Dev.Zero in
theorem chk_zero_error_recovery {F : Type} [Field F] [Fintype F]
    {s m r : ℕ} (hm : 0 < m) (C : Code F s m) (τ : ℕ → ℝ)
    (hC : SubspaceDesign C τ) :
    ∀ ℓ : ℕ, ListRecoverable C r 0 ℓ (zeroErrorBound ℓ (τ r)) ∧
      (ℓ = 0 → ListRecoverable C r 0 ℓ 0) ∧
      (0 < ℓ → τ r ≤ 1 / (1 + log₂ (ℓ : ℝ)) → ListRecoverable C r 0 ℓ (2*ℓ)) := by
  intro ℓ
  refine ⟨main hm C τ hC ℓ, ?_, ?_⟩
  · intro h; subst h; exact lr_zero hm C
  · intro hpos ht
    by_cases h1 : ℓ = 1
    · subst h1
      simpa using lr_one (r := r) C
    · have h2 : 2 ≤ ℓ := by omega
      obtain ⟨hlt, hb⟩ := bound_two h2 (τ r) ht
      refine lr_mono (main hm C τ hC ℓ) ?_
      have : zeroErrorBound ℓ (τ r) = ENNReal.ofReal ((ℓ : ℝ) ^ (1 / (1 - τ r))) := by
        unfold zeroErrorBound
        have : ℓ ≠ 0 := by omega
        simp [this, hlt]
      rw [this]
      calc ENNReal.ofReal ((ℓ : ℝ) ^ (1 / (1 - τ r))) ≤ ENNReal.ofReal (2 * ℓ) :=
            ENNReal.ofReal_le_ofReal hb
        _ = 2 * ℓ := by
            rw [ENNReal.ofReal_mul (by norm_num)]; simp
end SubspaceEvasion312.Explicit
end

theorem solution : type_of% @SubspaceEvasion312.Explicit.chk_zero_error_recovery := @SubspaceEvasion312.Explicit.chk_zero_error_recovery
