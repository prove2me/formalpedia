-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapPs.qdet_eq_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:38:11.235796+00:00
-- url     : https://prove2.me/submissions/9adad74e-679b-4739-ba4f-3b1c3f46f38e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ProdOfFnSmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ChainHSlice
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capEntry_apply_end
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CapPhi_fold_eqOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapPs
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
local notation "𝕄" => Matrix (Fin n) (Fin n) ℂ
local notation "𝕋" => Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ} [CompactSpace (KG ε)]
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapPs
theorem _root_.solution (Eop : Fin n → Fin n → (𝕄 → ℂ) → (𝕄 → ℂ)) (A : Fin n → Fin n → Module.End ℂ (smoothS n))
    (hA : ∀ a b (F : 𝕄 → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn (Eop a b F) ((A a b G : smoothS n) : 𝕄 → ℂ) (OmegaSet n))
    (u : ℂ) (F : 𝕄 → ℂ) (G : smoothS n) (h : Set.EqOn F G (OmegaSet n)) {z : 𝕄} (hz : z ∈ OmegaSet n) :
    Formalism.QuantumDeterminants.qdetOp Eop u F z = ((capelliC A u G : smoothS n) : 𝕄 → ℂ) z := by
  have htop : ∀ (x : ℂ) (a b : Fin n) (F : 𝕄 → ℂ) (G : smoothS n), Set.EqOn F G (OmegaSet n) →
      Set.EqOn (Formalism.QuantumDeterminants.Top Eop x a b F) ((capEntry A x a b G : smoothS n) : 𝕄 → ℂ) (OmegaSet n) := by
    intro x a b F G h z hz
    rw [capEntry_apply_end]
    show (if a = b then x • F z else 0) + Eop a b F z =
      ((A a b G : smoothS n) : 𝕄 → ℂ) z + ((if a = b then x • G else 0 : smoothS n) : 𝕄 → ℂ) z
    rw [hA a b F G h hz, h hz]
    split_ifs <;> simp [add_comm]
  unfold Formalism.QuantumDeterminants.qdetOp Formalism.QuantumDeterminants.qminorOp capelliC cminor
  rw [Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply, LinearMap.smul_apply, Submodule.coe_smul_of_tower, Pi.smul_apply, zsmul_eq_mul, smul_eq_mul]
  congr 1
  exact CapPhi.fold_eqOn n (fun k => Formalism.QuantumDeterminants.Top Eop (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k))
    (fun j => capEntry A (u - ((j : ℕ) : ℂ)) (id (σ j)) (id j))
    (fun i F' G' h' => htop _ _ _ F' G' h') F G h hz
end ReciprocityTheory.ChartRestriction.DS.S7.CapPs
