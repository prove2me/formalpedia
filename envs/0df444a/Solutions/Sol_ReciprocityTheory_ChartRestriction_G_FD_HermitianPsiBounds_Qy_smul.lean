-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds.Qy_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:36.129202+00:00
-- url     : https://prove2.me/submissions/369bb3a7-5a9b-471f-9a27-d86362d4cd8d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPsiBounds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_c_pos


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
theorem _root_.solution (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (α : E) (p : Fin r → E) :
    Qy X y (α • p) ≤ (∑ τ : X.Ψ, ‖τ.1 α‖ ^ 2) * Qy X y p := by
  unfold Qy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have e : Data.emb τ.1 (α • p) = τ.1 α • Data.emb τ.1 p := by
    funext a; simp [Data.emb]
  have e2 : ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (α • p)) a‖ ^ 2 =
      ‖τ.1 α‖ ^ 2 * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 := by
    rw [e, Matrix.mulVec_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [e2]
  have h1 : ‖τ.1 α‖ ^ 2 ≤ ∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2 :=
    Finset.single_le_sum (f := fun σ : X.Ψ => ‖σ.1 α‖ ^ 2) (fun σ _ => by positivity)
      (Finset.mem_univ τ)
  have h2 : 0 ≤ X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 :=
    mul_nonneg (c_pos X τ).le (Finset.sum_nonneg fun a _ => by positivity)
  calc X.c τ * (‖τ.1 α‖ ^ 2 * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2)
      = ‖τ.1 α‖ ^ 2 * (X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2) := by ring
    _ ≤ (∑ σ : X.Ψ, ‖σ.1 α‖ ^ 2) * (X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2) :=
      mul_le_mul_of_nonneg_right h1 h2
end ReciprocityTheory.ChartRestriction.G.FD.HermitianPsiBounds
