-- Prove2me | solution 1 for PhiDivRobust.Counterpart.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:22:58.518984+00:00
-- url     : https://prove2.me/submissions/54f0c171-b69b-430f-8617-f421a538da6f

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_IsPhiDivergenceFunction
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_PhiDivRobust_Counterpart_dualFunction
open Matrix

namespace PhiDivRobust.Counterpart

theorem aux_wd_phiDiv_ne_bot {m : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (p q : Fin m → ℝ) (hq : ∀ i, 0 < q i) : phiDiv φ p q ≠ ⊥ := by
  unfold phiDiv
  refine Finset.sum_induction _ (fun z : EReal => z ≠ ⊥) ?_ ?_ ?_
  · intro a b ha hb
    exact EReal.add_ne_bot_iff.mpr ⟨ha, hb⟩
  · exact EReal.zero_ne_bot
  · intro i _
    rw [EReal.mul_ne_bot]
    have hqi : (0 : EReal) < (q i : EReal) := EReal.coe_pos.mpr (hq i)
    refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (hφ.ne_bot _), Or.inl (EReal.coe_ne_top _),
      Or.inl hqi.le⟩

end PhiDivRobust.Counterpart

open PhiDivRobust.Counterpart
open Matrix

theorem solution {n m k : ℕ} (φ : ℝ → EReal) (hφ : IsPhiDivergenceFunction φ)
    (a : Fin n → ℝ) (B : Matrix (Fin n) (Fin m) ℝ) (β : ℝ) (C : Matrix (Fin k) (Fin m) ℝ)
    (d : Fin k → ℝ) (q : Fin m → ℝ) (ρ : ℝ) (hq : ∀ i, 0 < q i) (hρ : 0 < ρ)
    (hqU : q ∈ uncertaintySet φ C d q ρ) (x : Fin n → ℝ)
    (h : ∃ lam : ℝ, ∃ η : Fin k → ℝ, 0 ≤ lam ∧ 0 ≤ η ∧
      dualFunction φ a B C d q ρ x lam η ≤ (β : EReal)) :
    ∀ p ∈ uncertaintySet φ C d q ρ, (a + B *ᵥ p) ⬝ᵥ x ≤ β := by
  intro p hp
  obtain ⟨lam, η, hlam, hη, hg⟩ := h
  obtain ⟨hp0, hCp, hD⟩ := hp
  have hbot : phiDiv φ p q ≠ ⊥ := aux_wd_phiDiv_ne_bot φ hφ p q hq
  have htop : phiDiv φ p q ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top ρ) hD
  set r : ℝ := (phiDiv φ p q).toReal with hr
  have hrD : ((r : ℝ) : EReal) = phiDiv φ p q := EReal.coe_toReal htop hbot
  have hrρ : r ≤ ρ := by
    have : ((r : ℝ) : EReal) ≤ (ρ : EReal) := by rw [hrD]; exact hD
    exact EReal.coe_le_coe_iff.mp this
  have hL : lagrangian φ a B C d q ρ x p lam η ≤ dualFunction φ a B C d q ρ x lam η := by
    unfold dualFunction
    exact le_iSup₂ (f := fun p (_ : p ∈ {p : Fin m → ℝ | 0 ≤ p}) =>
      lagrangian φ a B C d q ρ x p lam η) p hp0
  have hL2 := hL.trans hg
  unfold lagrangian at hL2
  rw [← hrD, ← EReal.coe_mul, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hL2
  have hE : 0 ≤ η ⬝ᵥ (d - C *ᵥ p) := by
    apply dotProduct_nonneg_of_nonneg hη
    intro i
    have := hCp i
    simp only [Pi.sub_apply, Pi.zero_apply]
    linarith
  have hm : 0 ≤ lam * (ρ - r) := mul_nonneg hlam (by linarith)
  nlinarith
