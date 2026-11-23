-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.sum_castLE_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:28.1708+00:00
-- url     : https://prove2.me/submissions/320c8400-e028-4585-882f-03f207bf7657

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
theorem _root_.solution {n : ℕ} (h : n ≤ r) (g : Fin r → ℝ) :
    ∑ a : Fin n, g (Fin.castLE h a) = ∑ b ∈ Finset.univ.filter (fun b : Fin r => (b : ℕ) < n), g b := by
  classical
  refine Finset.sum_bij (fun a _ => Fin.castLE h a) (fun a _ => by simp) (fun a _ b _ hab => Fin.castLE_injective h hab)
    (fun b hb => ⟨⟨b, by simpa using hb⟩, Finset.mem_univ _, Fin.ext rfl⟩) (fun a _ => rfl)
end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
