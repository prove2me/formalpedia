-- Prove2me | solution 1 for PI.FJMB.col_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:22.225002+00:00
-- url     : https://prove2.me/submissions/2889b952-a8b4-4b74-837e-0168150fd72f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurChain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Theorems.Thm_PI_FJMB_bCol_apply
import Theorems.Thm_PI_FJMB_translate_pairs
import Theorems.Thm_P2M_PI_FJMB_fill___d91e4e7a1ca5
import Theorems.Thm_PI_FJMB_fill_not

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (c d : Fin n) (hcd : c ≠ d)
    (f : MvPolynomial σ ℂ) (hf : PI.FJM.bCol ι c d f = 0) {K : Type*} [Field K] [CharZero K] [Algebra ℂ K]
    (M : Fin m → Fin n → K) (p : σ → K) (t : K) :
    aeval (fill ι (colAddM M c d t) p) f = aeval (fill ι M p) f := by
  classical
  have key := translate_pairs (R := ℂ) (fun i : Fin m => ι (i, c)) (fun i => ι (i, d))
    (fun i i' e => by have := hι e; simp at this; exact this)
    (fun i i' e => hcd (by have := hι e; simp at this; exact this.2)) f (by rw [← bCol_apply]; exact hf)
    (fill ι M p) t
  refine Eq.trans ?_ key
  congr 1
  congr 1
  funext v
  by_cases hv : ∃ x, ι x = v
  · obtain ⟨⟨i, k⟩, rfl⟩ := hv
    rw [fill_ι hι, fill_ι hι]
    simp only [colAddM]
    have hs : (∑ i', if ι (i', d) = ι (i, k) then fill ι M p (ι (i', c)) else 0) = if k = d then M i c else 0 := by
      simp only [hι.eq_iff, Prod.mk.injEq, fill_ι hι]
      by_cases hkd : k = d
      · subst hkd; simp
      · simp [Ne.symm hkd, hkd]
    rw [hs]; split_ifs <;> simp
  · push Not at hv
    rw [fill_not _ _ _ _ hv, fill_not _ _ _ _ hv]
    have : (∑ i', if ι (i', d) = v then fill ι M p (ι (i', c)) else 0) = 0 :=
      Finset.sum_eq_zero (fun i' _ => by simp [hv (i', d)])
    rw [this, mul_zero, add_zero]
end PI.FJMB
