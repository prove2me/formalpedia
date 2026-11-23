-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf.sum_shift_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:06.337822+00:00
-- url     : https://prove2.me/submissions/06c007f8-f64f-4a63-8cb6-bf86cab35fb1

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
theorem _root_.solution {n m : ℕ} (hn : n ≤ r) (hm : m = r - n) (g : Fin r → ℝ) (f : Fin m → Fin r)
    (hf : ∀ a, (f a : ℕ) = n + a) :
    ∑ a : Fin m, g (f a) = ∑ b ∈ Finset.univ.filter (fun b : Fin r => ¬ (b : ℕ) < n), g b := by
  classical
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := congrArg Fin.val hab
    rw [hf, hf] at h1
    exact Fin.ext (by omega)
  refine Finset.sum_bij (fun a _ => f a) (fun a _ => by simp [hf]) (fun a _ b _ hab => hinj hab)
    (fun b hb => ?_) (fun a _ => rfl)
  have hb' : ¬ (b : ℕ) < n := by simpa using hb
  refine ⟨⟨b - n, by have := b.isLt; omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
  rw [hf]
  simp only
  omega
end ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
