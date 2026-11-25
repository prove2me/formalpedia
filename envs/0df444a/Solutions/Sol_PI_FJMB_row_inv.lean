-- Prove2me | solution 1 for PI.FJMB.row_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:24.705484+00:00
-- url     : https://prove2.me/submissions/0c5d3b39-f01c-4c23-88b3-49e54db6a4f5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurChain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Theorems.Thm_PI_FJMB_bRow_apply
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
theorem _root_.solution {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (a b : Fin m) (hab : a ≠ b)
    (f : MvPolynomial σ ℂ) (hf : PI.FJM.bRow ι a b f = 0) {K : Type*} [Field K] [CharZero K] [Algebra ℂ K]
    (M : Fin m → Fin n → K) (p : σ → K) (t : K) :
    aeval (fill ι (rowAddM M a b t) p) f = aeval (fill ι M p) f := by
  classical
  have key := translate_pairs (R := ℂ) (fun k : Fin n => ι (a, k)) (fun k => ι (b, k))
    (fun k k' e => by have := hι e; simp at this; exact this)
    (fun k k' e => hab (by have := hι e; simp at this; exact this.1)) f (by rw [← bRow_apply]; exact hf)
    (fill ι M p) t
  refine Eq.trans ?_ key
  congr 1
  congr 1
  funext v
  by_cases hv : ∃ x, ι x = v
  · obtain ⟨⟨i, k⟩, rfl⟩ := hv
    rw [fill_ι hι, fill_ι hι]
    simp only [rowAddM]
    have hs : (∑ k', if ι (b, k') = ι (i, k) then fill ι M p (ι (a, k')) else 0) = if i = b then M a k else 0 := by
      simp only [hι.eq_iff, Prod.mk.injEq, fill_ι hι]
      by_cases hib : i = b
      · subst hib; simp
      · simp [Ne.symm hib, hib]
    rw [hs]; split_ifs <;> simp
  · push Not at hv
    rw [fill_not _ _ _ _ hv, fill_not _ _ _ _ hv]
    have : (∑ k', if ι (b, k') = v then fill ι M p (ι (a, k')) else 0) = 0 :=
      Finset.sum_eq_zero (fun k' _ => by simp [hv (b, k')])
    rw [this, mul_zero, add_zero]
end PI.FJMB
