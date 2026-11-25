-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.comp_le_Qy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:33:19.047246+00:00
-- url     : https://prove2.me/submissions/5bf55951-287c-456a-b474-b2354df2a8c6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
open Matrix NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
theorem _root_.solution (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) (p : Fin r → E) (b : Fin r) :
    X.c τ * ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) b‖ ^ 2 ≤ QuadraticLatticeForms.Qy X y p := by
  unfold QuadraticLatticeForms.Qy
  have hc : ∀ τ' : X.Ψ, 0 ≤ X.c τ' := fun τ' => by unfold Data.c; positivity
  calc X.c τ * ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) b‖ ^ 2
      ≤ X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum
          (f := fun a => ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2) (fun a _ => by positivity)
          (Finset.mem_univ b)) (hc τ)
    _ ≤ _ := Finset.single_le_sum
          (f := fun τ' => X.c τ' * ∑ a, ‖((y τ')⁻¹ *ᵥ Data.emb τ'.1 p) a‖ ^ 2)
          (fun τ' _ => mul_nonneg (hc τ') (by positivity)) (Finset.mem_univ τ)
end ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
