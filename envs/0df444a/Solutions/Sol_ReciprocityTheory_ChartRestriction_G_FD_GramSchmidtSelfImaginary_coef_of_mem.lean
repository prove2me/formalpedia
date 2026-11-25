-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary.coef_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:00.440444+00:00
-- url     : https://prove2.me/submissions/e59405e0-3041-4d3e-9b08-7c36f53dee7f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpSpanRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
theorem _root_.solution {n : ℕ} (Y : Fin n → Fin r → ℂ) (S : Set (Fin n)) {v : Fin r → ℂ}
    (hv : v ∈ Submodule.span ℂ (Y '' S)) :
    ∃ w : Fin n → ℂ, (∀ j, j ∉ S → w j = 0) ∧ v = ∑ j, w j • Y j := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨Pi.single j 1, fun i hi => ?_, ?_⟩
    · have hij : i ≠ j := fun e => hi (e ▸ hj)
      simp [Pi.single_apply, hij]
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    refine ⟨w + w', fun i hi => by simp [hw i hi, hw' i hi], ?_⟩
    simp [add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨c • w, fun i hi => by simp [hw i hi], ?_⟩
    simp [Finset.smul_sum, smul_smul]
end ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
