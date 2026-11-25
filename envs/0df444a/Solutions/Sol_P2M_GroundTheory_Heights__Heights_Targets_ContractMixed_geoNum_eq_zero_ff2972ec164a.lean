-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_geoNum_eq_zero_ff2972ec164a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:20:58.391095+00:00
-- url     : https://prove2.me/submissions/31edcfd6-3e83-47eb-aaee-b156eec36950

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ContractMixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Targets.ContractMixed
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.Targets.ContractMixed
theorem _root_.solution (hVert : PFVert.Statement) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d₀ n : ℕ} (hP' : IsArithVar P' (n + 1))
    (hQ : IsArithVar (imageZ v P') d₀) {L' : Fin n → HermLine ι'} (hpre : PrefixPull κ v d₀ L')
    {s : MRing ι'} {a : K' → ℕ} (hs : IsMultiHomog s a) (hsP : s ∉ P') {W : Ideal (MRing ι')}
    (hW : W ∈ divSupp P' s) (hh : ¬ IsHorizontal W) : geoNum n W (fun j => (L' j).a) = 0 := by
  obtain ⟨h, L, -, hLL⟩ := hpre
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fin.append_castAdd_natAdd (f := L')]
  exact hVert K ι K' ι' κ v P' d₀ m L _ _ s a W hv hP' hQ hLL hs hsP hW hh
end GroundTheory.Heights₂.Heights.Targets.ContractMixed
