-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.ValAt.periodic_const_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:43.553735+00:00
-- url     : https://prove2.me/submissions/0ebe22f1-5609-4f2a-8a76-34a12898e803

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_ValAt_periodic_const

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.ValAt
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X : Scheme.{0}}
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.ValAt
theorem _root_.solution {La : Type} [AddCommGroup La] (P : La →+ (Fin g → ℂ))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (f : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z a, f (z + P a) = f z) (z w : Fin g → ℂ) : f z = f w := by
  classical
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℝ (Set.range P)
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ((↑) : b → Fin g → ℂ)) := by
    rw [Subtype.range_coe, hbspan, hspan]
  let B : Module.Basis b ℝ (Fin g → ℂ) := Module.Basis.mk hbli hsp
  have : Fintype b := FiniteDimensional.fintypeBasisIndex B
  let K := (fun t : b → ℝ => ∑ i, t i • B i) '' Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (continuous_finsetSum _ fun i _ =>
      (continuous_apply i).smul continuous_const)
  have hB : ∀ i, ∃ a, P a = B i := fun i => by
    rw [Module.Basis.mk_apply]; exact hbs i.2
  refine periodic_const f hf P.range K hK (fun z => ?_) (fun z l hl => ?_) z w
  · refine ⟨∑ i, Int.fract (B.repr z i) • B i, ⟨fun i => Int.fract (B.repr z i),
      fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩, ?_⟩
    have hz : z - ∑ i, Int.fract (B.repr z i) • B i = ∑ i, ((⌊B.repr z i⌋ : ℤ) : ℝ) • B i := by
      set c := B.repr z with hc
      nth_rewrite 1 [← B.sum_repr z]
      rw [← hc]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_smul, Int.self_sub_fract]
    rw [hz]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := hB i
    rw [← ha, Int.cast_smul_eq_zsmul ℝ, ← map_zsmul]
    exact ⟨_, rfl⟩
  · obtain ⟨a, rfl⟩ := hl
    exact hper z a
end ReciprocityTheory.ChartRestriction.G.TB.ValAt
