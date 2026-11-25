-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalPerpBasis_hC_sum_right__1bac482c7394
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:55:55.779851+00:00
-- url     : https://prove2.me/submissions/fc9fc565-51a3-49d8-ae10-ce37b4433d1f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OnbPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosCoordNe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HCSumRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
theorem _root_.solution (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (u : Fin r → ℂ) (f : ι → Fin r → ℂ) : hermC τ G u (∑ i ∈ s, f i) = ∑ i ∈ s, hermC τ G u (f i) := by
  simp only [hermC, Finset.sum_apply, map_sum, Finset.mul_sum]
  calc (∑ a, ∑ b, ∑ i ∈ s, u a * τ (G a b) * conj (f i b))
      = ∑ a, ∑ i ∈ s, ∑ b, u a * τ (G a b) * conj (f i b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ a, ∑ b, u a * τ (G a b) * conj (f i b) := Finset.sum_comm
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
