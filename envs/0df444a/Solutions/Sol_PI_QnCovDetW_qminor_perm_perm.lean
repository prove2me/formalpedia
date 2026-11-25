-- Prove2me | solution 1 for PI.QnCovDetW.qminor_perm_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:32.929465+00:00
-- url     : https://prove2.me/submissions/1e815f19-9834-4f9b-85ca-b1e02b7ea6a3

import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantDeterminantScaling_IntCastMulEqSmul
import Theorems.Thm_PI_QnCovDetW_intCast_mul_eq_smul
import Theorems.Thm_Formalism_REAL_quantumMinor_adjacent_col_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
noncomputable section
namespace PI.QnCovDetW
open Formalism.REAL Formalism.FourierDecayAlt.Q
private theorem qminor_rowperm_lemma {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) (π : Equiv.Perm (Fin t)) :
    qminor E (a ∘ π) b u = ((Equiv.Perm.sign π : ℤ) : A) * qminor E a b u := by
  unfold qminor
  rw [Finset.mul_sum]
  have hs : ((Equiv.Perm.sign π : ℤ) : A) * ((Equiv.Perm.sign π : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  refine Fintype.sum_equiv (Equiv.mulLeft π) _ _ (fun σ => ?_)
  simp only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply, Function.comp_apply]
  rw [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, ← mul_assoc, ← mul_assoc, hs, one_mul]
private theorem qminor_colperm_lemma_2 {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (a : Fin (m + 1) → Fin n) (u : ℂ) (τ : Equiv.Perm (Fin (m + 1))) :
    ∀ b : Fin (m + 1) → Fin n, qminor E a (b ∘ τ) u = ((Equiv.Perm.sign τ : ℤ) : A) * qminor E a b u := by
  have hcl : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top τ
  induction hcl using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    intro b
    rw [quantumMinor_adjacent_col_swap E hE a b i u, Equiv.Perm.sign_swap (show i.castSucc < i.succ from Fin.castSucc_lt_succ).ne]
    simp
  | one =>
    intro b
    simp
  | mul x y _ _ hx hy =>
    intro b
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hy, hx, Equiv.Perm.sign_mul,
      mul_comm (Equiv.Perm.sign x), Units.val_mul, Int.cast_mul, mul_assoc]
end PI.QnCovDetW
end
end

set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnCovDetW
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovDetW
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (σ τ : Equiv.Perm (Fin n)) (u : ℂ) :
    qminor E σ τ u =
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) • qdet E u := by
  rcases n with _ | m
  · have hσ : σ = 1 := Equiv.ext fun i => i.elim0
    have hτ : τ = 1 := Equiv.ext fun i => i.elim0
    subst hσ hτ
    simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, mul_one, one_smul, Equiv.Perm.coe_one]
    rfl
  · have h1 := qminor_rowperm_lemma E id (⇑τ) u σ
    have h2 := qminor_colperm_lemma_2 E hE id u τ id
    simp only [Function.id_comp] at h1 h2
    rw [h1, h2, intCast_mul_eq_smul, intCast_mul_eq_smul, smul_smul]
    rfl
end PI.QnCovDetW
