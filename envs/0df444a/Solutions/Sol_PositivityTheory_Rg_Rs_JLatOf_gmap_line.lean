-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.gmap_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:04.28839+00:00
-- url     : https://prove2.me/submissions/9e2c6227-9da7-4977-b2ed-c1bec52d22a9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.JLatOf
open PositivityTheory.Rg.Rs
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.Rg.Rs.JLatOf
theorem _root_.solution (g : GL (Fin N) k) (i₀ : Fin N) (h0 : ∀ a, a ≠ i₀ → (g : Matrix (Fin N) (Fin N) k) a i₀ = 0) :
    gmap g (Submodule.span k {(Pi.single i₀ (1 : k) : Fin N → k)}) =
      Submodule.span k {(Pi.single i₀ (1 : k) : Fin N → k)} := by
  have hcol : (g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i₀ 1 =
      (g : Matrix (Fin N) (Fin N) k) i₀ i₀ • (Pi.single i₀ 1 : Fin N → k) := by
    ext a
    by_cases ha : a = i₀
    · subst ha
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply, ha, h0 a ha]
  have hc : (g : Matrix (Fin N) (Fin N) k) i₀ i₀ ≠ 0 := by
    intro hc
    rw [hc, zero_smul] at hcol
    have hinj : Function.Injective (fun v : Fin N → k => (g : Matrix (Fin N) (Fin N) k) *ᵥ v) := by
      intro x y hxy
      have h2 := congrArg (fun v => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ v) hxy
      simpa [Matrix.mulVec_mulVec] using h2
    have h3 : (Pi.single i₀ (1 : k) : Fin N → k) = 0 := hinj (by
      show (g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i₀ 1 = (g : Matrix (Fin N) (Fin N) k) *ᵥ 0
      rw [hcol, Matrix.mulVec_zero])
    have h4 := congrFun h3 i₀
    simp at h4
  delta gmap
  rw [Submodule.map_span, Set.image_singleton, Matrix.toLin'_apply, hcol,
    Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc)]
end PositivityTheory.Rg.Rs.JLatOf
