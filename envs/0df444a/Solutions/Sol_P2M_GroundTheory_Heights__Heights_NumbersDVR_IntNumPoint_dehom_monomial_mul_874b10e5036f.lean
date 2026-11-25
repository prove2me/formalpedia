-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_monomial_mul_874b10e5036f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:16.914923+00:00
-- url     : https://prove2.me/submissions/e8c58bdb-34e6-4d73-94f7-c045a22c15bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_xc_ne_zero_ee20e72cfa3f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
variable (V : Ideal (MRing ι F)) [V.IsPrime]
variable {V}
variable (i : ∀ k, ι k) (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
include hi
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
theorem _root_.solution (m : (Σ k, ι k) →₀ ℕ) :
    dehom V i (monomial m 1) * ∏ k, xc V ⟨k, i k⟩ ^ (Finsupp.weight (blockWeight ι) m k) =
      cls V (monomial m 1) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' =>
    rw [← mul_one (1 : F), ← monomial_mul, map_mul, map_mul, map_add, ← hm, ← hm']
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  | single p n =>
    have hy : xc V ⟨p.1, i p.1⟩ ≠ 0 := xc_ne_zero (hi p.1)
    rw [← X_pow_eq_monomial, map_pow, map_pow, Finsupp.weight_single,
      Fintype.prod_eq_single p.1 (fun k hk => by simp [blockWeight, hk])]
    simp only [dehom, aeval_X, blockWeight, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, div_pow]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hy)]
    rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
