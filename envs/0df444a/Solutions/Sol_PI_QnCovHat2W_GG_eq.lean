-- Prove2me | solution 1 for PI.QnCovHat2W.GG_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:49.307521+00:00
-- url     : https://prove2.me/submissions/080bd9aa-6d42-4f20-8c87-259f17c7f7a9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_GGEq
import Theorems.Thm_PI_QnCovHat2W_one_side

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {m : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (F : (Fin m → Fin (m + 2)) → (Fin m → Fin (m + 2)) → M)
    (hR : ∀ (x y : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F (x ∘ π) y = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x y)
    (hC : ∀ (x y : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      F x (y ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • F x y)
    (β β' a a' : Fin (m + 2) → ℂ) :
    GG F β β' a a' = ((m.factorial : ℂ) * m.factorial) •
      ∑ i : Fin (m + 2), ∑ i' : Fin (m + 2), ∑ j : Fin (m + 2), ∑ j' : Fin (m + 2),
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (β i * β' i' - β i' * β' i) *
            (a j * a' j' - a j' * a' j)) • F (skip2 i i') (skip2 j j')
        else 0 := by
  let Φ : (Fin m → Fin (m + 2)) → M := fun x =>
    ∑ d : Fin (m + 2) → Fin (m + 2), sgnL d id • ((a (d 0) * a' (d 1)) • F x (fun k => d k.succ.succ))
  have hΦ : ∀ (x : Fin m → Fin (m + 2)) (π : Equiv.Perm (Fin m)),
      Φ (x ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • Φ x := by
    intro x π
    simp only [Φ, hR, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_comm _ (sgnL d id), smul_comm ((Equiv.Perm.sign π : ℤ) : ℂ) (a (d 0) * a' (d 1))]
  have h1 : GG F β β' a a' =
      ∑ c : Fin (m + 2) → Fin (m + 2), sgnL c id • ((β (c 0) * β' (c 1)) • Φ (fun k => c k.succ.succ)) := by
    unfold GG
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Φ, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    ring
  have h2 : ∀ i i' : Fin (m + 2), Φ (skip2 i i') = (m.factorial : ℂ) • ∑ j : Fin (m + 2), ∑ j' : Fin (m + 2),
      if j < j' then ((-1 : ℂ) ^ ((j : ℕ) + (j' : ℕ)) * (a j' * a' j - a j * a' j')) •
        F (skip2 i i') (skip2 j j') else 0 := by
    intro i i'
    exact one_side (fun y => F (skip2 i i') y) (fun y π => hC _ y π) a a'
  rw [h1, one_side Φ hΦ β β', Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i' _ => ?_
  by_cases hi : i < i'
  · simp only [hi, if_true, true_and, h2, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun j' _ => ?_
    by_cases hj : j < j'
    · simp only [hj, if_true, smul_smul]
      congr 1
      rw [pow_add, pow_add, pow_add, pow_add]
      ring
    · simp [hj]
  · simp [hi]
end PI.QnCovHat2W
