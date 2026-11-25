-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CRH.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:07.788595+00:00
-- url     : https://prove2.me/submissions/0af5a685-cb84-4866-8f5c-836e05612de0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cs_append
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cs_perm
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_Adm_sub
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cd_iter
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cd_ofReal
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_chain
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cd_Dx
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_leibB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
namespace PI.UnitaryCorollaryDerivatives.CRH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
private lemma Dw_append_singleton (w : List (Bool × Mat k r)) (x : Bool × Mat k r) (f : Mat k r → ℂ) :
    Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl
end PI.UnitaryCorollaryDerivatives.CRH
end
end

set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open PI PI.UnitaryCorollaryDerivatives PI.UnitaryCorollaryDerivatives.CRH
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI.UnitaryCorollaryDerivatives.CRH
theorem _root_.solution (ψ : Mat k r → ℝ) (h : ℝ → ℝ) (cost : Mat k r → ℕ) (n : ℕ) (C₀ : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hh : ContDiff ℝ ∞ h) (hb : ∀ q : ℕ, ∃ c : ℝ, ∀ x, ‖iteratedDeriv q h x‖ ≤ c)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ GV k r,
      ‖Dw w (fun g => ((ψ g : ℝ) : ℂ)) g‖ ≤ C₀ * gN g ^ cs cost w) :
    ∀ m q : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ w, admitted n w → w.length ≤ m → ∀ g ∈ GV k r,
      ‖Dw w (fun g => ((iteratedDeriv q h (ψ g) : ℝ) : ℂ)) g‖ ≤ K * gN g ^ cs cost w := by
  have hgN : ∀ g : Mat k r, 0 ≤ gN g := by
    intro g
    first
    | (unfold gN; positivity)
    | (simp only [gN]; positivity)
  intro m
  induction m with
  | zero =>
    intro q
    obtain ⟨c, hc⟩ := hb q
    refine ⟨max c 0, le_max_right _ _, fun w _ hw g _ => ?_⟩
    have : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hw)
    subst this
    simp only [Dw, List.foldr_nil, cs, List.map_nil, List.sum_nil, pow_zero, mul_one, Complex.norm_real]
    exact (hc _).trans (le_max_left _ _)
  | succ m ih =>
    intro q
    obtain ⟨K₁, hK₁, h₁⟩ := ih q
    obtain ⟨K₂, hK₂, h₂⟩ := ih (q + 1)
    refine ⟨max K₁ (2 ^ m * (K₂ * max C₀ 0)), le_max_of_le_left hK₁, fun w hw hlen g hg => ?_⟩
    rcases Nat.lt_or_ge w.length (m + 1) with hlt | hge
    · exact (h₁ w hw (by omega) g hg).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hgN g) _))
    · obtain ⟨w', x, rfl⟩ : ∃ w' x, w = w' ++ [x] := by
        rcases List.eq_nil_or_concat w with h0 | ⟨w', x, hx⟩
        · subst h0; simp at hge
        · exact ⟨w', x, by rw [hx, List.concat_eq_append]⟩
      have hlen' : w'.length = m := by simp at hlen hge; omega
      rw [Dw_append_singleton, chain x hψ hh q]
      have hyp : ∀ w₁ w₂, Spl w' w₁ w₂ →
          ‖Dw w₁ (fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ)) g‖ *
            ‖Dw w₂ (Dx x fun g => ((ψ g : ℝ) : ℂ)) g‖ ≤ K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x]) := by
        rintro w₁ w₂ ⟨s1, s2, hp⟩
        have hA1 : admitted n w₁ := Adm_sub (s1.trans (List.sublist_append_left _ _)) hw
        have hA2 : admitted n (w₂ ++ [x]) := Adm_sub (s2.append (List.Sublist.refl _)) hw
        have hl1 : w₁.length ≤ m := by have := s1.length_le; omega
        have e1 := h₂ w₁ hA1 hl1 g hg
        have e2 := H (w₂ ++ [x]) hA2 (by simp) g hg
        rw [Dw_append_singleton] at e2
        have hcs : cs cost w₁ + cs cost (w₂ ++ [x]) = cs cost (w' ++ [x]) := by
          rw [← cs_append]
          exact cs_perm cost (by rw [← List.append_assoc]; exact hp.append_right [x])
        calc _ ≤ (K₂ * gN g ^ cs cost w₁) * (max C₀ 0 * gN g ^ cs cost (w₂ ++ [x])) :=
              mul_le_mul e1 (e2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
                (pow_nonneg (hgN g) _))) (norm_nonneg _) (mul_nonneg hK₂ (pow_nonneg (hgN g) _))
          _ = K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x]) := by rw [← hcs, pow_add]; ring
      have hM := leibB g (K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x])) w'
        (fun g => ((iteratedDeriv (q + 1) h (ψ g) : ℝ) : ℂ)) (Dx x fun g => ((ψ g : ℝ) : ℂ))
        (cd_ofReal ((cd_iter hh (q + 1)).comp hψ)) (cd_Dx x (cd_ofReal hψ)) hyp
      calc _ ≤ 2 ^ w'.length * (K₂ * max C₀ 0 * gN g ^ cs cost (w' ++ [x])) := hM
        _ = (2 ^ m * (K₂ * max C₀ 0)) * gN g ^ cs cost (w' ++ [x]) := by rw [hlen']; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (hgN g) _)
end PI.UnitaryCorollaryDerivatives.CRH
