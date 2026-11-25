-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DataX.LZ_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:41:55.601293+00:00
-- url     : https://prove2.me/submissions/6880b8e7-9b86-4402-baf3-e0b8d637b960

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_DataX_exists_gamma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DataX
theorem _root_.solution (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (hmem : ∀ i, u i ∈ X.Λ)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P)
    (hχ : ∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : b ∈ X.LZ X.g) (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    P (X.Zb u b x) = P x := by
  obtain ⟨γ, hγΓ, hγc, hmap⟩ := X.exists_gamma u hu hmem b hb
  have e1 : X.Zb u b x = lact γ x := funext fun τ => by
    show X.zmat u b τ * mat x τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
    rw [hmap]
  rw [e1, hP.2.2 γ hγΓ x hx, hχ γ hγΓ hγc, one_mul]
end ReciprocityTheory.ChartRestriction.G.FD.DataX
