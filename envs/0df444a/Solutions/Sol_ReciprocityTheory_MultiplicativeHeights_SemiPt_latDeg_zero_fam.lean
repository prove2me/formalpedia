-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.latDeg_zero_fam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:25.183092+00:00
-- url     : https://prove2.me/submissions/ce107f54-38e5-45cd-930c-ecaba9d6559b

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin 0 → Fin r → K) (hb : IsKBasisIn B b) : latDeg H B b = 0 := by
  obtain ⟨-, -, hspan⟩ := hb
  have hB : B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h := hspan x hx
    simpa [Set.range_eq_empty] using h
  subst hB
  simp [latDeg, Set.range_eq_empty]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
