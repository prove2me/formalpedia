-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.sq_le_Qy_of_le_firstMinimum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:41.497794+00:00
-- url     : https://prove2.me/submissions/9fe6abbf-d09c-45ad-93b9-20f9ba8a98e1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPsiBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
open Matrix NumberField Complex QuadraticLatticeForms
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
theorem _root_.solution {x : Frame X.Ψ r} {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ}
    (hm : ∀ τ u, X.maj x τ u = ∑ a, ‖((y τ)⁻¹ *ᵥ u) a‖ ^ 2) {ε : ℝ} (hε : 0 < ε) (hl : ε ≤ X.la1 x)
    {v : Fin r → E} (hv : v ∈ X.Λ) (hv0 : v ≠ 0) : ε ^ 2 ≤ Qy X y v := by
  have hQ : ∀ w : Fin r → E, ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 w) = Qy X y w := by
    intro w
    unfold Qy
    simp only [hm]
  have hnn : ∀ t ∈ {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)}, 0 ≤ t := by
    rintro t ⟨w, -, -, rfl⟩
    rw [hQ]
    unfold Qy
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (by unfold Data.c; positivity)
      (Finset.sum_nonneg fun _ _ => by positivity)
  have hmem : Qy X y v ∈ {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v)} :=
    ⟨v, hv, hv0, (hQ v).symm⟩
  have h1 : X.firstMinimumSq x ≤ Qy X y v := csInf_le ⟨0, hnn⟩ hmem
  have h0 : 0 ≤ X.firstMinimumSq x := Real.sInf_nonneg hnn
  have h2 : ε ^ 2 ≤ X.la1 x ^ 2 := by nlinarith
  rw [Data.la1, Real.sq_sqrt h0] at h2
  linarith
end ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
