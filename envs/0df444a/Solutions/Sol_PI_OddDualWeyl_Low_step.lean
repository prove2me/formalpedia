-- Prove2me | solution 1 for PI.OddDualWeyl.Low.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:29.252054+00:00
-- url     : https://prove2.me/submissions/d6e3202e-f6cd-4caa-9366-d996688917f0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Theorems.Thm_PI_OddDualWeyl_Low_coeff_lin_pow
import Theorems.Thm_PI_OddDualWeyl_Low_stepA
import Theorems.Thm_PI_OddDualWeyl_Low_stepB
import Theorems.Thm_PI_OddDualWeyl_Low_stepC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.Low
theorem _root_.solution {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) (ν : Fin (n + 1) → ℕ) :
    ∃ c : R, pw R (σ * Equiv.swap i.castSucc i.succ) ν =
      c • rowDiv R (σ i.succ) (σ i.castSucc) (ν i.castSucc - nuNext ν i.castSucc) (pw R σ ν) := by
  classical
  let m : Fin (n + 1) → MvPolynomial (Fin (n + 1) × Fin (n + 1)) R :=
    fun s => pMinor R σ (s.val + 1) s.isLt
  let m' : Fin (n + 1) → MvPolynomial (Fin (n + 1) × Fin (n + 1)) R :=
    fun s => pMinor R (σ * Equiv.swap i.castSucc i.succ) (s.val + 1) s.isLt
  let c : Fin (n + 1) → ℕ := fun s => ν s - nuNext ν s
  let ε : Fin (n + 1) → R := fun s => if i.val < s.val then -1 else 1
  have hne : ∀ s, s ≠ i.castSucc → rowGen R (σ i.succ) (σ i.castSucc) (m s) = Polynomial.C (m s) ∧
      m' s = MvPolynomial.C (ε s) * m s := by
    intro s hs
    have : s.val ≠ i.val := fun e => hs (Fin.ext (by simp [e]))
    rcases Nat.lt_or_gt_of_ne this with h | h
    · obtain ⟨h1, h2⟩ := stepA (R := R) σ i s h
      refine ⟨h1, ?_⟩
      simp only [m', m, ε, h2, if_neg (by omega : ¬ i.val < s.val), map_one, one_mul]
    · obtain ⟨h1, h2⟩ := stepC (R := R) σ i s h
      refine ⟨h1, ?_⟩
      simp only [m', m, ε, h2, if_pos h, map_neg, map_one, neg_one_mul]
  have hI : rowGen R (σ i.succ) (σ i.castSucc) (m i.castSucc) =
      Polynomial.C (m i.castSucc) + Polynomial.X * Polynomial.C (m' i.castSucc) :=
    stepB (R := R) σ i i.castSucc (by simp)
  have hrd : rowDiv R (σ i.succ) (σ i.castSucc) (c i.castSucc) (pw R σ ν) =
      m' i.castSucc ^ c i.castSucc * ∏ s ∈ Finset.univ.erase i.castSucc, m s ^ c s := by
    show (rowGen R (σ i.succ) (σ i.castSucc) (∏ s, m s ^ c s)).coeff (c i.castSucc) = _
    rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i.castSucc)]
    rw [Finset.prod_congr rfl (fun s hs => by
      rw [map_pow, (hne s (Finset.ne_of_mem_erase hs)).1])]
    rw [map_pow, hI, show ∏ s ∈ Finset.univ.erase i.castSucc, (Polynomial.C (m s)) ^ c s =
      Polynomial.C (∏ s ∈ Finset.univ.erase i.castSucc, m s ^ c s) by simp [map_prod, map_pow],
      Polynomial.coeff_mul_C, coeff_lin_pow]
  refine ⟨∏ s ∈ Finset.univ.erase i.castSucc, ε s ^ c s, ?_⟩
  rw [show ν i.castSucc - nuNext ν i.castSucc = c i.castSucc from rfl, hrd, ← MvPolynomial.C_mul']
  show ∏ s, m' s ^ c s = _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i.castSucc)]
  rw [Finset.prod_congr rfl (fun s hs => by rw [(hne s (Finset.ne_of_mem_erase hs)).2])]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  ring
end PI.OddDualWeyl.Low
