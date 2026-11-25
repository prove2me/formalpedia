-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.divBy_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:33:43.169548+00:00
-- url     : https://prove2.me/submissions/98722370-065c-43b2-b8a5-d457b9ded453

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
section Ring
variable {ι : Type}
end Ring
section OneVar
private theorem norm_natCast_le_one_unramified_integrals (n : ℕ) : ‖(n : K)‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih (by simp))
end OneVar
section Subst
variable {ι : Type}
end Subst
section Frob
variable {l : ℕ} {σ : K →+* K} {ι : Type}
end Frob
end ReciprocityTheory.ChartRestriction.L1
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {x : K} {f : PowerSeries K} (hf : DivBy x f) :
    DivBy x (derivative K f) := by
  unfold DivBy at hf ⊢
  intro n
  rw [PowerSeries.coeff_derivative, norm_mul]
  have h1 : ‖((n : K) + 1)‖ ≤ 1 := by
    have := norm_natCast_le_one_unramified_integrals (K := K) (n + 1)
    push_cast at this
    exact this
  calc ‖coeff (n + 1) f‖ * ‖((n : K) + 1)‖ ≤ ‖x‖ * 1 :=
        mul_le_mul (hf _) h1 (norm_nonneg _) (norm_nonneg _)
    _ = ‖x‖ := mul_one _
end ReciprocityTheory.ChartRestriction.L1
