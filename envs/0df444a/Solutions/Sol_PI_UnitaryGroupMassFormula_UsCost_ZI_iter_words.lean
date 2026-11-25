-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.iter_words
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:52.410903+00:00
-- url     : https://prove2.me/submissions/3a07c7af-7f57-4c87-bf85-4002d03a25f5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_ZI_norm_smulRightL_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped ContDiff
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
section quad
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
end quad
section words
variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]
private theorem one_le_pow_of_one_le_real {x : ℝ} (hx : 1 ≤ x) (n : ℕ) : 1 ≤ x ^ n := by
  exact one_le_pow₀ hx
private theorem pow_le_pow_right_of_one_le {x : ℝ} (hx : 1 ≤ x) {m n : ℕ} (h : m ≤ n) :
    x ^ m ≤ x ^ n := by
  exact pow_le_pow_right₀ hx h
private theorem mul_pow_mul_le_mul_pow_succ {Kc R β lam M : ℝ} {b j : ℕ} (hj : j ≤ b) (hKc : 0 ≤ Kc)
    (hR : 1 ≤ R) (hβ : 0 ≤ β) (hlam : 1 ≤ lam) (hM : 1 ≤ M) :
    Kc * M ^ (j + 1) * (R ^ (b - j) * (β * lam) * (lam * M) ^ (b - j)) ≤
      Kc * R ^ b * β * (lam * M) ^ (b + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left]
  have hM0 : 0 ≤ M := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hlam0 : 0 ≤ lam := by linarith
  have hL : 0 ≤ Kc * M ^ (j + 1) * (R ^ k * (β * lam) * (lam * M) ^ k) :=
    mul_nonneg (mul_nonneg hKc (pow_nonneg hM0 _))
      (mul_nonneg (mul_nonneg (pow_nonneg hR0 _) (mul_nonneg hβ hlam0))
        (pow_nonneg (mul_nonneg hlam0 hM0) _))
  have hX : 1 ≤ R ^ j * lam ^ j :=
    one_le_mul_of_one_le_of_one_le (one_le_pow_of_one_le_real hR j)
      (one_le_pow_of_one_le_real hlam j)
  calc _ ≤ Kc * M ^ (j + 1) * (R ^ k * (β * lam) * (lam * M) ^ k) * (R ^ j * lam ^ j) :=
        le_mul_of_one_le_right hL hX
    _ = _ := by ring
end words
end PI.UnitaryGroupMassFormula.UsCost.ZI
end
end

set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
theorem _root_.solution (q : ℕ) (Kc : ℝ) (hKc : 0 ≤ Kc) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {α E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Cls : ℕ → (α → E) → Prop)
      (Dop : I → (α → E) → (α → E)) (Γ : V → α) (U : Set V) (c : I → V → (V →L[ℝ] ℝ)) (z₀ : V)
      (M lam : ℝ),
      IsOpen U → z₀ ∈ U → 1 ≤ M → 1 ≤ lam →
      (∀ b H, Cls (b + 1) H → Cls b H) →
      (∀ b H i, Cls (b + 1) H → Cls b (Dop i H)) →
      (∀ b H, Cls b H → ∀ z ∈ U, ContDiffAt ℝ b (fun z => H (Γ z)) z) →
      (∀ b H, Cls (b + 1) H → ∀ z ∈ U,
        fderiv ℝ (fun z => H (Γ z)) z = ∑ i, (c i z).smulRight (Dop i H (Γ z))) →
      (∀ i (n : ℕ), ContDiffOn ℝ n (c i) U) →
      (∀ i, ∀ a ≤ q, ‖iteratedFDeriv ℝ a (c i) z₀‖ ≤ Kc * M ^ (a + 1)) →
      ∀ b ≤ q, ∀ (H : α → E) (β : ℝ), Cls b H →
        (∀ w : List I, w.length ≤ b → ‖w.foldr Dop H (Γ z₀)‖ ≤ β * lam ^ w.length) →
        ‖iteratedFDeriv ℝ b (fun z => H (Γ z)) z₀‖ ≤ C * β * (lam * M) ^ b := by
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ((Fintype.card I : ℝ) * Kc + 1) * 2 ^ q := ⟨_, rfl⟩
  have hNK : 0 ≤ (Fintype.card I : ℝ) * Kc := mul_nonneg (Nat.cast_nonneg _) hKc
  have hR : 1 ≤ R := by
    rw [hRdef]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow_of_one_le_real (by norm_num) q)
  have hR0 : 0 ≤ R := by linarith
  refine ⟨R ^ q, one_le_pow_of_one_le_real hR q, ?_⟩
  intro α E _ _ Cls Dop Γ U c z₀ M lam hU hz₀ hM hlam hdown hDop hsmooth hderiv hc hcb
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  have hmono : ∀ a b (H : α → E), a ≤ b → Cls b H → Cls a H := by
    intro a b H hab
    induction hab with
    | refl => exact id
    | step _ ih => exact fun h => ih (hdown _ _ h)
  have key : ∀ b, b ≤ q → ∀ (H : α → E) (β : ℝ), Cls b H →
      (∀ w : List I, w.length ≤ b → ‖w.foldr Dop H (Γ z₀)‖ ≤ β * lam ^ w.length) →
      ‖iteratedFDeriv ℝ b (fun z => H (Γ z)) z₀‖ ≤ R ^ b * β * (lam * M) ^ b := by
    intro b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
    intro hb H β hH hw
    have hβ0 : ‖H (Γ z₀)‖ ≤ β := by simpa using hw [] (Nat.zero_le _)
    have hβ : 0 ≤ β := (norm_nonneg _).trans hβ0
    rcases b with _ | b
    · simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, mul_one]
      exact hβ0
    · obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Kc * R ^ b * β * (lam * M) ^ (b + 1) := ⟨_, rfl⟩
      have hG : ∀ i, ContDiffOn ℝ b (fun z => Dop i H (Γ z)) U := fun i z hz =>
        (hsmooth b (Dop i H) (hDop b H i hH) z hz).contDiffWithinAt
      have hf : ∀ i, ContDiffOn ℝ b
          (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U := fun i =>
        ((ContinuousLinearMap.smulRightL ℝ V E).contDiff.comp_contDiffOn (hc i b)).clm_apply (hG i)
      have heq : Set.EqOn (fderiv ℝ (fun z => H (Γ z)))
          (∑ i, fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U := by
        intro z hz
        rw [Finset.sum_apply, hderiv b H hH z hz]
        rfl
      have hfi : ∀ i, ‖iteratedFDerivWithin ℝ b
          (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U z₀‖ ≤
            2 ^ b * T := by
        intro i
        refine ((ContinuousLinearMap.smulRightL ℝ V E).norm_iteratedFDerivWithin_le_of_bilinear
          (hc i b) (hG i) hU.uniqueDiffOn hz₀ le_rfl).trans ?_
        have hsum : ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) *
            ‖iteratedFDerivWithin ℝ j (c i) U z₀‖ *
            ‖iteratedFDerivWithin ℝ (b - j) (fun z => Dop i H (Γ z)) U z₀‖ ≤
              ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * T := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Finset.mem_range.1 hj
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hcj : ‖iteratedFDerivWithin ℝ j (c i) U z₀‖ ≤ Kc * M ^ (j + 1) := by
            rw [iteratedFDerivWithin_of_isOpen j hU hz₀]
            exact hcb i j (by omega)
          have hGj : ‖iteratedFDerivWithin ℝ (b - j) (fun z => Dop i H (Γ z)) U z₀‖ ≤
              R ^ (b - j) * (β * lam) * (lam * M) ^ (b - j) := by
            rw [iteratedFDerivWithin_of_isOpen (b - j) hU hz₀]
            refine ih (b - j) (by omega) (by omega) (Dop i H) (β * lam)
              (hmono _ _ _ (Nat.sub_le b j) (hDop b H i hH)) fun w hw' => ?_
            have h := hw (w ++ [i]) (by rw [List.length_append, List.length_singleton]; omega)
            simp only [List.foldr_append, List.foldr_cons, List.foldr_nil, List.length_append,
              List.length_singleton] at h
            calc _ ≤ β * lam ^ (w.length + 1) := h
              _ = β * lam * lam ^ w.length := by ring
          calc ‖iteratedFDerivWithin ℝ j (c i) U z₀‖ *
                ‖iteratedFDerivWithin ℝ (b - j) (fun z => Dop i H (Γ z)) U z₀‖
              ≤ (Kc * M ^ (j + 1)) * (R ^ (b - j) * (β * lam) * (lam * M) ^ (b - j)) :=
                mul_le_mul hcj hGj (norm_nonneg _) (mul_nonneg hKc (pow_nonneg hM0 _))
            _ ≤ T := by
                rw [hT]
                exact mul_pow_mul_le_mul_pow_succ (by omega) hKc hR hβ hlam hM
        calc _ ≤ 1 * ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * T :=
              mul_le_mul (norm_smulRightL_le E) hsum
                (Finset.sum_nonneg fun j _ => by positivity) zero_le_one
          _ = 2 ^ b * T := by
              rw [one_mul, ← Finset.sum_mul]
              congr 1
              exact_mod_cast Nat.sum_range_choose b
      have hN : (Fintype.card I : ℝ) * Kc * 2 ^ b ≤ R := by
        have h2 : (2 : ℝ) ^ b ≤ 2 ^ q := pow_le_pow_right_of_one_le (by norm_num) (by omega)
        calc _ ≤ (Fintype.card I : ℝ) * Kc * 2 ^ q := mul_le_mul_of_nonneg_left h2 hNK
          _ ≤ R := by
              rw [hRdef, add_mul, one_mul]
              exact le_add_of_nonneg_right (pow_nonneg (by norm_num) q)
      have hX : 0 ≤ R ^ b * β * (lam * M) ^ (b + 1) :=
        mul_nonneg (mul_nonneg (pow_nonneg hR0 _) hβ) (pow_nonneg (mul_nonneg hlam0 hM0) _)
      calc ‖iteratedFDeriv ℝ (b + 1) (fun z => H (Γ z)) z₀‖
          = ‖iteratedFDerivWithin ℝ b
              (∑ i, fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z)))
              U z₀‖ := by
            rw [← norm_iteratedFDeriv_fderiv,
              ← (iteratedFDerivWithin_of_isOpen b hU hz₀ :
                iteratedFDerivWithin ℝ b (fderiv ℝ (fun z => H (Γ z))) U z₀ =
                  iteratedFDeriv ℝ b (fderiv ℝ (fun z => H (Γ z))) z₀),
              iteratedFDerivWithin_congr heq hz₀]
        _ = ‖∑ i, iteratedFDerivWithin ℝ b
              (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U z₀‖ := by
            rw [iteratedFDerivWithin_sum_apply hU.uniqueDiffOn hz₀ fun i _ => hf i z₀ hz₀]
        _ ≤ ∑ i, ‖iteratedFDerivWithin ℝ b
              (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U z₀‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _i : I, 2 ^ b * T := Finset.sum_le_sum fun i _ => hfi i
        _ = (Fintype.card I : ℝ) * (2 ^ b * T) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ((Fintype.card I : ℝ) * Kc * 2 ^ b) * (R ^ b * β * (lam * M) ^ (b + 1)) := by
            rw [hT]; ring
        _ ≤ R * (R ^ b * β * (lam * M) ^ (b + 1)) := mul_le_mul_of_nonneg_right hN hX
        _ = R ^ (b + 1) * β * (lam * M) ^ (b + 1) := by ring
  intro b hb H β hH hw
  have h0 : ‖H (Γ z₀)‖ ≤ β := by simpa using hw [] (Nat.zero_le _)
  have hβ : 0 ≤ β := (norm_nonneg _).trans h0
  calc _ ≤ R ^ b * β * (lam * M) ^ b := key b hb H β hH hw
    _ ≤ R ^ q * β * (lam * M) ^ b :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right_of_one_le hR hb) hβ)
          (pow_nonneg (mul_nonneg hlam0 hM0) _)
end PI.UnitaryGroupMassFormula.UsCost.ZI
