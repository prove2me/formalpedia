-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.fnTrace_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:37:47.715411+00:00
-- url     : https://prove2.me/submissions/60aaf496-f104-4ce5-b587-d9ba683237b8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module IntermediateField
variable {Ω : Type*} [Field Ω] [CharZero Ω] {ι : Type} [Fintype ι] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
theorem _root_.solution (x : ι → Ω) (e : Fin (D + 1) → ι) (s : Lx x e) :
    fnTrace x e (s : Ω) =
      ((Algebra.trace (fnField (x ∘ e)) (Lx x e) s : fnField (x ∘ e)) : Ω) := by
  have hs : (s : Ω) ∈ fnField x := (IntermediateField.mem_extendScalars _).mp s.2
  unfold fnTrace
  rw [dif_pos hs]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
