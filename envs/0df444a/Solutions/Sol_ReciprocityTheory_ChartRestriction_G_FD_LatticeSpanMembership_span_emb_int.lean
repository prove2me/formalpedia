-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership.span_emb_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:40.083541+00:00
-- url     : https://prove2.me/submissions/47c6fc0a-cf5a-40ad-b5bd-6d90866bb601

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantOperators
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
namespace ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
theorem _root_.solution (hD3 : IntegerApproximationCount (E := E)) :
    Submodule.span ℝ (Set.range fun α : 𝓞 E => fun τ : X.Ψ => τ.1 (α : E)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfW⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (LinearMap.ext h)
  let g := LinearMap.toContinuousLinearMap f
  set ρ : ℝ := 2 * (fdeg E : ℝ) ^ 2 * rdE E with hρ
  have hρ0 : 0 ≤ ρ := by
    have : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
    positivity
  set t : ℝ := (‖g‖ * ρ + 1) / f v with ht
  obtain ⟨α, hα⟩ := (hD3 r X).1 (t • v)
  have hfα : f (fun τ : X.Ψ => τ.1 (α : E)) = 0 := by
    have hmem : f (fun τ : X.Ψ => τ.1 (α : E)) ∈ Submodule.map f (Submodule.span ℝ
        (Set.range fun α : 𝓞 E => fun τ : X.Ψ => τ.1 (α : E))) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨α, rfl⟩)
    rw [hfW] at hmem
    exact hmem
  have hnorm : ‖(fun τ : X.Ψ => τ.1 (α : E)) - t • v‖ ≤ ρ := by
    refine (pi_norm_le_iff_of_nonneg hρ0).mpr fun τ => ?_
    exact hα τ
  have hle := g.le_opNorm ((fun τ : X.Ψ => τ.1 (α : E)) - t • v)
  have hg : g ((fun τ : X.Ψ => τ.1 (α : E)) - t • v) = -(‖g‖ * ρ + 1) := by
    show f ((fun τ : X.Ψ => τ.1 (α : E)) - t • v) = _
    rw [map_sub, map_smul, hfα, smul_eq_mul, ht, div_mul_cancel₀ _ hv, zero_sub]
  rw [hg, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)] at hle
  nlinarith [norm_nonneg g, mul_le_mul_of_nonneg_left hnorm (norm_nonneg g)]
end ReciprocityTheory.ChartRestriction.G.FD.LatticeSpanMembership
