-- Prove2me | solution 1 for PI.GGMatBoundW.gamProd_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:29:16.633131+00:00
-- url     : https://prove2.me/submissions/27ed520c-e5a0-4b4f-98a5-89b4d305e128

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_MatrixCoefficientEquation
import Theorems.Thm_PI_GGMatBoundW_psiNat_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
namespace PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
section General
variable {G : Type} [Group G] {X : Type} [MulAction Gᵐᵒᵖ X]
end General
section Prod
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
private theorem gam_inv_eq_conj {F : Type} [Field F] [Fintype F] {k : ℕ} (ψ₀ : AddChar F ℂ)
    (x : GL (Fin k) F) : gam ψ₀ x⁻¹ = conj (gam ψ₀ x) := by
  unfold gam
  simp only [map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← psiNat_inv]
  congr 1
  group
end Prod
end PI.GGMatBoundW
end
end

set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
namespace PI.GGMatBoundW
theorem _root_.solution (ψ : ∀ v, AddChar (Fq v) ℂ) (x : ∀ v, GL (Fin k) (Fq v)) :
    gamProd ψ x⁻¹ = conj (gamProd ψ x) := by
  unfold gamProd
  rw [map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Pi.inv_apply, gam_inv_eq_conj]
end PI.GGMatBoundW
