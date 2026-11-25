-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.ip_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:13.472685+00:00
-- url     : https://prove2.me/submissions/b44661a5-9fa1-4d47-927a-3eca42b7808b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_ip_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
open Matrix NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
theorem _root_.solution {u : X.Ψ → Fin r → ℂ} (hu : u ≠ 0) : 0 < ip X u u := by
  rw [ip_self]
  obtain ⟨τ, hτ⟩ : ∃ τ, u τ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (funext h)
  obtain ⟨a, ha⟩ : ∃ a, u τ a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hτ (funext h)
  apply Finset.sum_pos' (fun i _ => mul_nonneg (c_pos X i).le
    (Finset.sum_nonneg fun b _ => sq_nonneg _))
  refine ⟨τ, Finset.mem_univ _, mul_pos (c_pos X τ) ?_⟩
  apply Finset.sum_pos' (fun b _ => sq_nonneg _)
  exact ⟨a, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr ha) 2⟩
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
