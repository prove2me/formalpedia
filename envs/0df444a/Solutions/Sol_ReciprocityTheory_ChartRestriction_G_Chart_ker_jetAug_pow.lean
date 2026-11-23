-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.ker_jetAug_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:20.866901+00:00
-- url     : https://prove2.me/submissions/1913ca02-cdea-4436-816c-5cfe50771b74

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_sub_const_mem_span_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
open MvPolynomial
variable (R : Type) [CommRing R]
variable {R}
variable (R)
variable {R}
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (κ : Type) (m : ℕ) : (RingHom.ker (jetAug R κ m)) ^ (m + 1) = ⊥ := by
  have hle : RingHom.ker (jetAug R κ m) ≤
      (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hp : MvPolynomial.aeval (fun _ : κ => (0 : R)) p = 0 := hx
    have := sub_const_mem_span_X (R := R) p
    rw [hp, map_zero, sub_zero] at this
    exact Ideal.mem_map_of_mem _ this
  rw [← le_bot_iff]
  calc (RingHom.ker (jetAug R κ m)) ^ (m + 1)
      ≤ ((Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))).map (Ideal.Quotient.mk _)) ^ (m + 1) :=
        Ideal.pow_right_mono hle _
    _ = ((Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))) ^ (m + 1)).map (Ideal.Quotient.mk _) :=
        (Ideal.map_pow _ _ _).symm
    _ = ⊥ := Ideal.map_quotient_self _
end ReciprocityTheory.ChartRestriction.G.Chart
