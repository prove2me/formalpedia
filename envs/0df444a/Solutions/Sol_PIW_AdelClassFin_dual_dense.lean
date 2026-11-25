-- Prove2me | solution 1 for PIW.AdelClassFin.dual_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:32.408809+00:00
-- url     : https://prove2.me/submissions/4a93a983-b797-41a1-9967-9adf13a66013

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_DedekindLFunctions
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Theorems.Thm_PIW_AdelClassFin_DictRing_af_approx
import Theorems.Thm_PIW_AdelClassFin_DictRing_tmul_mem
import Theorems.Thm_PIW_AdelClassFin_DictRing_incl_mem
import Theorems.Thm_PIW_AdelClassFin_DictRing_incl_add
import Theorems.Thm_PIW_AdelClassFin_DictRing_incl_mul
import Theorems.Thm_PIW_AdelClassFin_DictRing_incl_neg
import Theorems.Thm_PIW_AdelClassFin_DictRing_incl_zero
import Theorems.Thm_PIW_AdelClassFin_DictRing_incl_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution : DDense := by
  intro F E _ _ _ _ _ N hN r hr
  have hr' : r ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
      Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) := hr
  clear hr
  induction hr' using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨e, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact ⟨a, 0, zero_mem _, by rw [mul_zero, add_zero]; rfl⟩
    · obtain ⟨β, y', hy', hyeq⟩ := DictRing.af_approx y hy N hN
      let b : 𝓞 E := ⟨algebraMap F E (algebraMap (𝓞 F) F β), (RingOfIntegers.isIntegral_coe β).algebraMap⟩
      refine ⟨b, (1 : E) ⊗ₜ[F] y', DictRing.tmul_mem (one_mem _) hy', ?_⟩
      show (1 : E) ⊗ₜ[F] y = algebraMap F E (algebraMap (𝓞 F) F β) ⊗ₜ[F] (1 : Af F) +
        (N : E ⊗[F] Af F) * ((1 : E) ⊗ₜ[F] y')
      rw [hyeq, TensorProduct.tmul_add, Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, IsScalarTower.algebraMap_apply (𝓞 F) F (Af F), Algebra.algebraMap_eq_smul_one (R := F) (A := Af F),
        Algebra.algebraMap_eq_smul_one (R := F) (A := E), TensorProduct.smul_tmul]
  | zero => exact ⟨0, 0, zero_mem _, by rw [DictRing.incl_zero, mul_zero, add_zero]⟩
  | one => exact ⟨1, 0, zero_mem _, by rw [DictRing.incl_one, mul_zero, add_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨a₁, r₁, hr₁, e₁⟩ := hx
    obtain ⟨a₂, r₂, hr₂, e₂⟩ := hy
    exact ⟨a₁ + a₂, r₁ + r₂, add_mem hr₁ hr₂, by rw [e₁, e₂, DictRing.incl_add]; ring⟩
  | neg x _ hx =>
    obtain ⟨a₁, r₁, hr₁, e₁⟩ := hx
    exact ⟨-a₁, -r₁, neg_mem hr₁, by rw [e₁, DictRing.incl_neg]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, r₁, hr₁, e₁⟩ := hx
    obtain ⟨a₂, r₂, hr₂, e₂⟩ := hy
    refine ⟨a₁ * a₂, r₁ * Formalism.UG.inclE (F := F) (Af F) (a₂ : E) + Formalism.UG.inclE (F := F) (Af F) (a₁ : E) * r₂ +
      (N : E ⊗[F] Af F) * r₁ * r₂, ?_, by rw [e₁, e₂, DictRing.incl_mul]; ring⟩
    exact add_mem (add_mem (mul_mem hr₁ (DictRing.incl_mem a₂)) (mul_mem (DictRing.incl_mem a₁) hr₂))
      (mul_mem (mul_mem (natCast_mem _ N) hr₁) hr₂)
end PIW.AdelClassFin
