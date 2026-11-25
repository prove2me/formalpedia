-- Prove2me | solution 1 for PI.PolynomialProperness.CB.sum_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:40.3352+00:00
-- url     : https://prove2.me/submissions/f69b95e9-172b-48e7-be36-8a7cbe4ee7b0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_SecondOrderNormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.CB
namespace PI.PolynomialProperness.CB
theorem _root_.solution {m n : ℕ} (h : n ≤ m) (f : Fin m → ℂ) (hf : ∀ l : Fin m, n ≤ l.val → f l = 0) :
    ∑ l, f l = ∑ t : Fin n, f (Fin.castLE h t) := by
  have hs := Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb h))) (f := f)
    (fun x _ hx => hf x (by
      by_contra hlt
      rw [not_le] at hlt
      exact hx (Finset.mem_map.2 ⟨⟨x.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)))
  rw [← hs, Finset.sum_map]
  rfl
end PI.PolynomialProperness.CB
