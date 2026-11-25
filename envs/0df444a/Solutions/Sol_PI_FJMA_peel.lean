-- Prove2me | solution 1 for PI.FJMA.peel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:05:35.797858+00:00
-- url     : https://prove2.me/submissions/ff2606a2-216c-41a4-9618-83ca1d8bd654

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_VarsZeroOfSupported
import Theorems.Thm_PI_FJMA_exists_support_mul
import Theorems.Thm_PI_FJMA_bRow_mul
import Theorems.Thm_PI_FJMA_bCol_mul
import Theorems.Thm_PI_FJMX_pderiv_eq_zero_of_supported


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMA
open PI.FJM
variable {σ : Type}
namespace PI.FJMA
theorem _root_.solution (hC : CauchyHW) {m n : ℕ} (ι : Fin m × Fin n → σ) (hι : Function.Injective ι)
    (α : Fin m → ℕ) (β : Fin n → ℕ) (S : Set σ) (F G : MvPolynomial σ ℂ) (hF : F ∈ supported ℂ S)
    (hF0 : F ≠ 0) (hG : FreeOf S G) (hS : ∀ x, ι x ∉ S) (hG0 : G ≠ 0) (hP : IsBlockHighestWeight ι α β (F * G)) :
    SqFacts α β ∧ ∃ Q, FreeOf (Set.range ι) Q ∧
      G = shapeProd (Matrix.of fun i k => (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α) * Q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  have hFd : ∀ x, pderiv (ι x) F = 0 := fun x => PI.FJMX.pderiv_eq_zero_of_supported hF (hS x)
  have g1 : ∀ a b : Fin m, a < b → bRow ι a b G = 0 := by
    intro a b hab
    have := h1 a b hab
    rw [bRow_mul ι a b F G hFd] at this
    exact (mul_eq_zero.1 this).resolve_left hF0
  have g2 : ∀ c d : Fin n, c < d → bCol ι c d G = 0 := by
    intro c d hcd
    have := h2 c d hcd
    rw [bCol_mul ι c d F G hFd] at this
    exact (mul_eq_zero.1 this).resolve_left hF0
  have g3 : ∀ e ∈ G.support, (∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) ∧ (∀ k, ∑ i : Fin m, e (ι (i, k)) = β k) := by
    intro e' he'
    obtain ⟨e, he, hee⟩ := exists_support_mul hF hF0 hG he'
    obtain ⟨k1, k2⟩ := h3 e he
    refine ⟨fun i => ?_, fun k => ?_⟩
    · rw [← k1 i]; exact Finset.sum_congr rfl (fun k _ => (hee _ (hS _)).symm)
    · rw [← k2 k]; exact Finset.sum_congr rfl (fun i _ => (hee _ (hS _)).symm)
  obtain ⟨r1, r2, r3, Q, hQ, hGQ⟩ := hC σ m n ι hι α β G hG0 g1 g2 g3 h4 h5
  refine ⟨⟨r1, r2, r3⟩, Q, ?_, hGQ⟩
  intro e he v hv
  obtain ⟨x, rfl⟩ := hv
  exact hQ e he x
end PI.FJMA
