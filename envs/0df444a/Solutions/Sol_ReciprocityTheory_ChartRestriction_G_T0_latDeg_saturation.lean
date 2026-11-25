-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.latDeg_saturation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:39:19.099256+00:00
-- url     : https://prove2.me/submissions/0e168ea4-f742-49f5-a0c2-ebf5c10d2e0b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Definitions.Def_ReciprocityTheory_SemistableReduction_DegAddHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_standardLattice_fg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_latDeg_standard_basis
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_degAdd_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {m : ℕ} (h : k + m = r) {b : Fin k → Fin r → K}
    (hbL : ∀ j, b j ∈ hStd K r) (c : Fin m → Fin r → K) (hc : ∀ j, c j ∈ hStd K r)
    (hli : LinearIndependent K (Fin.append b c))
    (hsp : ∀ x, x ∈ Submodule.span K (Set.range (Fin.append b c))) :
    ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b) b =
      -ReciprocityTheory.MultiplicativeHeights.quotDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (hStd K r) b c := by
  have hadd := ReciprocityTheory.MultiplicativeHeights.degAdd_holds K r k m (fun _ => 1) (hStd K r) b c (fun _ => PosDef.one)
    standardLattice_fg hbL hc hli (fun x _ => hsp x)
  have hmem : ∀ i, Fin.append b c i ∈ hStd K r := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hbL i
    · rw [Fin.append_right]; exact hc j
  have h0 := latDeg_standard_basis h (Fin.append b c) ⟨hmem, hli, fun x _ => hsp x⟩
  linarith
end ReciprocityTheory.ChartRestriction.G.T0
