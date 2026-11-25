-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.two_le_krullDim_of_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:35.396561+00:00
-- url     : https://prove2.me/submissions/8962d09d-03b6-41d1-aece-b23abd97bfe9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution (p₀ p₁ p₂ : Ideal R) [p₀.IsPrime]
    [p₁.IsPrime] [p₂.IsPrime] (h₀ : p₀ < p₁) (h₁ : p₁ < p₂) :
    ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p₀) := by
  rw [ringKrullDim_quotient]
  let a : PrimeSpectrum.zeroLocus (R := R) p₀ :=
    ⟨⟨p₀, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 (le_refl _)⟩
  let b : PrimeSpectrum.zeroLocus (R := R) p₀ :=
    ⟨⟨p₁, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 h₀.le⟩
  let c : PrimeSpectrum.zeroLocus (R := R) p₀ :=
    ⟨⟨p₂, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 (h₀.le.trans h₁.le)⟩
  have hab : a < b := h₀
  have hbc : b < c := h₁
  let s : LTSeries (PrimeSpectrum.zeroLocus (R := R) p₀) :=
    ⟨2, ![a, b, c], fun i => by fin_cases i <;> simpa⟩
  have := Order.LTSeries.length_le_krullDim s
  exact_mod_cast this
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
