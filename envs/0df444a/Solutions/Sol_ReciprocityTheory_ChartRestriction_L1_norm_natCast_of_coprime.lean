-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.norm_natCast_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:29:06.246337+00:00
-- url     : https://prove2.me/submissions/3aed7e4c-5719-45f0-a54b-94d6e3159e86

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
variable {l : ℕ} {σ : K →+* K} {ι : Type}
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (m : ℕ) (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = 1 := by
  have hint : ∀ a : ℤ, ‖(a : K)‖ ≤ 1 := by
    intro a
    rcases Int.eq_nat_or_neg a with ⟨n, rfl | rfl⟩
    · push_cast
      exact norm_natCast_le_one_unramified_integrals n
    · push_cast
      rw [norm_neg]
      exact norm_natCast_le_one_unramified_integrals n
  have hcop : Nat.gcd m l = 1 := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm).symm
  have hb := Nat.gcd_eq_gcd_ab m l
  rw [hcop] at hb
  have hbK : (1 : K) = (m : K) * (Nat.gcdA m l : K) + (l : K) * (Nat.gcdB m l : K) := by
    have := congrArg (fun z : ℤ => (z : K)) hb
    push_cast at this
    exact this
  refine le_antisymm (norm_natCast_le_one_unramified_integrals m) ?_
  by_contra hlt
  push_neg at hlt
  have h1 := IsUltrametricDist.norm_add_le_max ((m : K) * (Nat.gcdA m l : K))
    ((l : K) * (Nat.gcdB m l : K))
  rw [← hbK, norm_one] at h1
  have h2 : ‖(m : K) * (Nat.gcdA m l : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(m : K)‖ * ‖((Nat.gcdA m l : ℤ) : K)‖ ≤ ‖(m : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hint _) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hlt
  have h3 : ‖(l : K) * (Nat.gcdB m l : K)‖ < 1 := by
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖((Nat.gcdB m l : ℤ) : K)‖ ≤ ‖(l : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hint _) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hl1
  exact lt_irrefl _ (lt_of_le_of_lt h1 (max_lt h2 h3))
end ReciprocityTheory.ChartRestriction.L1
