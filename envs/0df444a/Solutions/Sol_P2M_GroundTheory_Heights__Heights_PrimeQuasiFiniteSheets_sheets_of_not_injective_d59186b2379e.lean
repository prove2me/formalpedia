-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_sheets_of_not_injective_d59186b2379e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:45.009816+00:00
-- url     : https://prove2.me/submissions/48652471-9a4b-49e6-aaef-bced44d04079

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsPrimeQuasiFiniteSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFiniteFibresDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSimpleRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPrimeQuasiFiniteSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PrimeQuasiFiniteSheets_eval_pullback_877f341acccc

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
theorem _root_.solution (Q : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hinj : ¬ Function.Injective (ComplexSets.projHom Q A)) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y c ≠ 0 →
      ∃ (U : Set (Fin d → ℂ)) (N : ℕ) (s : Fin N → (Fin d → ℂ) → Fin n → ℂ),
        IsOpen U ∧ y ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
        ∀ y' ∈ U, (∀ j, s j y' ∈ ComplexSets.fibre Q A y') ∧
          Function.Injective (fun j => s j y') ∧
          ComplexSets.fibre Q A y' ⊆ Set.range (fun j => s j y') := by
  rw [injective_iff_map_eq_zero] at hinj
  push Not at hinj
  obtain ⟨g, hg, hg0⟩ := hinj
  have hQ : ComplexSets.pullback A g ∈ Q := Ideal.Quotient.eq_zero_iff_mem.mp hg
  have hempty : ∀ y' : Fin d → ℂ, eval y' g ≠ 0 → ComplexSets.fibre Q A y' = ∅ := by
    intro y' hy'
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx, rfl⟩
    exact hy' (by rw [← eval_pullback]; exact hx _ hQ)
  refine ⟨g, hg0, fun y hy => ⟨{w | eval w g ≠ 0}, 0, fun j => j.elim0,
    isOpen_ne_fun (MvPolynomial.continuous_eval g) continuous_const, hy, fun j => j.elim0,
    fun y' hy' => ⟨fun j => j.elim0, fun i => i.elim0, ?_⟩⟩⟩
  rw [hempty y' hy']
  exact Set.empty_subset _
end GroundTheory.Heights₂.Heights.PrimeQuasiFiniteSheets
