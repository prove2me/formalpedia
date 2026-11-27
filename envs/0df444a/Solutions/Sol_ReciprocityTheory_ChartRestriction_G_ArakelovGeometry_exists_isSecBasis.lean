-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_isSecBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:25:53.181232+00:00
-- url     : https://prove2.me/submissions/b6d1ee9d-0f0b-4516-a4df-ae6819b766de

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (x : Ix κ → Ω) (n : ℕ) :
    ∃ b : Fin (finrank ℤ (sec ℤ x n)) → MvPolynomial (Ix κ) ℚ, IsSecBasis x n b := by
  classical
  haveI : Module.Finite ℤ (sec ℤ x n) := by
    rw [Module.finite_def, Submodule.fg_top]
    exact (homogeneousSubmodule_fg (Ix κ) ℤ n).map _
  haveI : Module.Free ℤ (sec ℤ x n) := Module.free_of_finite_type_torsion_free'
  let bas := Module.finBasis ℤ (sec ℤ x n)
  have hmem : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ aeval x f = ((bas k : sec ℤ x n) : Ω) := by
    intro k
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.1 (bas k).2
    exact ⟨f, (mem_homogeneousSubmodule n f).1 hf, hfx⟩
  choose f hfh hfx using hmem
  have hcast : ∀ g : MvPolynomial (Ix κ) ℤ, aeval x (map (Int.castRingHom ℚ) g) = aeval x g := by
    intro g
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  have hval : (fun k => aeval x (map (Int.castRingHom ℚ) (f k))) = (sec ℤ x n).subtype ∘ bas := by
    funext k
    rw [hcast, hfx]
    rfl
  refine ⟨fun k => map (Int.castRingHom ℚ) (f k), fun k => ⟨f k, hfh k, rfl⟩, ?_, ?_⟩
  · rw [hval]
    exact bas.linearIndependent.map' (sec ℤ x n).subtype (Submodule.ker_subtype _)
  · rw [hval, Set.range_comp, Submodule.span_image, bas.span_eq, Submodule.map_subtype_top]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
