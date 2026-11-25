-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.CRH.leibB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:36:08.466256+00:00
-- url     : https://prove2.me/submissions/279a7cc3-7fc8-4751-a756-2f777f388042

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRA
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_dif
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_cd_Dx
import Theorems.Thm_P2M_PI_UnitaryCorollaryDerivatives_CRH_Dw_add__d7ab365c3e76
import Theorems.Thm_P2M_PI_UnitaryCorollaryDerivatives_CRH_Dx_mul__a2efff259162
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
theorem _root_.solution (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) :
    ∀ a b : Mat k r → ℂ, ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      (∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g * b g) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb hM
    simpa [Dw, norm_mul] using hM [] [] (by unfold Spl; simp)
  | append_singleton w x ih =>
    intro a b ha hb hM
    rw [Dw_append_singleton, Dx_mul' x (dif ha) (dif hb),
      Dw_add' w ((cd_Dx x ha).mul hb) (ha.mul (cd_Dx x hb))]
    have h1 := ih (Dx x a) b (cd_Dx x ha) hb (fun w₁ w₂ hs => by
      obtain ⟨s1, s2, p⟩ := hs
      have e : w₁ ++ [x] ++ w₂ = w₁ ++ x :: w₂ := by simp
      have hp : (w₁ ++ [x] ++ w₂).Perm (w ++ [x]) := by
        rw [e]
        exact List.perm_middle.trans ((p.cons x).trans (List.perm_append_singleton x w).symm)
      have := hM (w₁ ++ [x]) w₂ (by
        unfold Spl
        exact ⟨s1.append (List.Sublist.refl _), s2.trans (List.sublist_append_left _ _), hp⟩)
      rwa [Dw_append_singleton] at this)
    have h2 := ih a (Dx x b) ha (cd_Dx x hb) (fun w₁ w₂ hs => by
      obtain ⟨s1, s2, p⟩ := hs
      have hp : (w₁ ++ (w₂ ++ [x])).Perm (w ++ [x]) := by
        rw [← List.append_assoc]
        exact p.append_right [x]
      have := hM w₁ (w₂ ++ [x]) (by
        unfold Spl
        exact ⟨s1.trans (List.sublist_append_left _ _), s2.append (List.Sublist.refl _), hp⟩)
      rwa [Dw_append_singleton] at this)
    calc _ ≤ ‖Dw w (fun g => Dx x a g * b g) g‖ + ‖Dw w (fun g => a g * Dx x b g) g‖ := norm_add_le _ _
      _ ≤ 2 ^ w.length * M + 2 ^ w.length * M := add_le_add h1 h2
      _ = 2 ^ (w ++ [x]).length * M := by
        rw [List.length_append, List.length_singleton, pow_succ]
        ring
end PI.UnitaryCorollaryDerivatives.CRH
