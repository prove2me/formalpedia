-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_arInt_eq_zero_ed61f4170dad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:20:37.295119+00:00
-- url     : https://prove2.me/submissions/aaced6e1-32f8-43ca-b392-6bca3c1ad9e7

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
theorem _root_.solution (hInt : PFIntZero.Statement) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {P' : Ideal (MRing ι')} {d₀ n : ℕ} (hP' : IsArithVar P' (n + 1))
    (hQ : IsArithVar (imageZ v P') d₀) {L' : Fin n → HermLine ι'} (hpre : PrefixPull κ v d₀ L')
    (A : HermLine ι') (s : MRing ι') : arInt P' s A L' = 0 := by
  obtain ⟨h, L, hL, hLL⟩ := hpre
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Fin.append_castAdd_natAdd (f := L')]
  exact hInt K ι K' ι' κ v P' d₀ m L _ _ A s hv hP' hQ hL hLL
end GroundTheory.Heights₂.Heights.Targets.ContractMixed
