-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.closure_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:39:39.973101+00:00
-- url     : https://prove2.me/submissions/caf1105f-e4bd-406b-b94f-ae66c703cd71

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution (x : κ → Ω) (e : Fin (D + 1) → κ) (m : Ω)
    (hm : m ∈ Submonoid.closure (Set.range fun i => x i / x (e 0))) :
    ∃ d, ∃ s ∈ sec ℤ x d, m = s / x (e 0) ^ d := by
  induction hm using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    refine ⟨1, x i, ?_, by rw [pow_one]⟩
    unfold sec
    exact Submodule.mem_map.2 ⟨MvPolynomial.X i,
      (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X ℤ i), by simp⟩
  | one =>
    refine ⟨0, 1, ?_, by simp⟩
    unfold sec
    exact Submodule.mem_map.2 ⟨1,
      (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_one κ ℤ), by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨d1, s1, hs1, rfl⟩ := ha
    obtain ⟨d2, s2, hs2, rfl⟩ := hb
    unfold sec at hs1 hs2
    obtain ⟨p1, hp1, rfl⟩ := Submodule.mem_map.1 hs1
    obtain ⟨p2, hp2, rfl⟩ := Submodule.mem_map.1 hs2
    refine ⟨d1 + d2, (MvPolynomial.aeval x).toLinearMap (p1 * p2), ?_, ?_⟩
    · unfold sec
      exact Submodule.mem_map.2 ⟨p1 * p2, (MvPolynomial.mem_homogeneousSubmodule _ _).2
        (((MvPolynomial.mem_homogeneousSubmodule _ _).1 hp1).mul
          ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hp2)), rfl⟩
    · simp only [AlgHom.toLinearMap_apply, map_mul]
      rw [div_mul_div_comm, pow_add]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
