-- Prove2me | solution 1 for P2M_GlobalTheory_LagSplit_beta_secH_secL__253c2586de05
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:31:40.450877+00:00
-- url     : https://prove2.me/submissions/6eef32d8-0599-4096-858b-50775085e539

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_secH_apply
import Theorems.Thm_GlobalTheory_LagSplit_dot_mulVec_symm
import Theorems.Thm_GlobalTheory_LagSplit_two_I_imC_inv
import Theorems.Thm_GlobalTheory_LagSplit_beta_secL
import Theorems.Thm_ReciprocityTheory_PTheta_dot_mulVec_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Key.Chi
open GlobalTheory GlobalTheory.LagSplit
variable {g : ℕ}
namespace GlobalTheory.LagSplit
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hY : IsUnit (τ.map Complex.im).det) (z w : Fin g → ℂ) :
    beta (omegaCx g) (secH τ) (secL g) z w = -(2 * I)⁻¹ * (z ⬝ᵥ (imC τ)⁻¹ *ᵥ w) := by
  have hs : (imC τ).IsSymm := (hτ.map _).map _
  rw [beta_secL, secH_apply, Sum.elim_comp_inr, two_I_imC_inv hY, Matrix.smul_mulVec,
    smul_dotProduct, dot_mulVec_symm hs.inv, smul_eq_mul, neg_mul]
end GlobalTheory.LagSplit
