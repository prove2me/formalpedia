-- Prove2me | solution 1 for P2M_GlobalTheory_RowTriangular_eval__unip_450ff3a92c12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:46.77903+00:00
-- url     : https://prove2.me/submissions/592e744d-8ede-44f4-bb38-c560fadb7b9e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Theorems.Thm_P2M_GlobalTheory_RowTriangular_eval__shift_2e105f77a3c7
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one


section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.RowTriangular
section Poly
open MvPolynomial
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k T : Type} [Field k] [CommRing T]
private theorem eval₂Hom_unipotent_substitution_eq [Infinite k] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowInv r n k P) (σ : Ty) (i : Fin (r σ))
    [DecidablePred fun ℓ : Letter Ty r n => ∃ b, ℓ = ⟨σ, (i, b)⟩] (N : Fin (r σ) → T) (hN : ∀ j, i ≤ j → N j = 0)
    (y : Letter Ty r n → T) [DecidableEq (Fin (r σ))] (S : Finset (Fin (r σ))) :
    eval₂Hom φ (fun ℓ : Letter Ty r n =>
      if ∃ b, ℓ = ⟨σ, (i, b)⟩ then y ℓ + ∑ j ∈ S, N j * y ⟨σ, (j, ℓ.2.2)⟩ else y ℓ) P = eval₂Hom φ y P := by
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro j S hj ih
    rw [← ih]
    by_cases hji : j < i
    · refine eval₂_shift φ hP σ i j hji (N j) _ _ ?_ ?_
      · intro b
        have hb : ∃ b', (⟨σ, (i, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ := ⟨b, rfl⟩
        have hb' : ¬ ∃ b', (⟨σ, (j, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ := by
          rintro ⟨b', h⟩
          simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
          exact hji.ne h.1
        simp only [if_pos hb, if_neg hb', Finset.sum_insert hj]
        ring
      · intro ℓ hℓ
        simp only [if_neg hℓ]
    · have h0 : N j = 0 := hN j (not_lt.1 hji)
      refine congrArg (fun g => eval₂Hom φ g P) (funext fun ℓ => ?_)
      split_ifs <;> simp [Finset.sum_insert hj, h0]
private theorem eval₂Hom_unipotent_block_substitution_eq [Infinite k] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowInv r n k P) (N : ∀ σ, Fin (r σ) → Fin (r σ) → T) (hN : ∀ σ i j, i ≤ j → N σ i j = 0)
    [DecidableEq (Σ σ : Ty, Fin (r σ))] (R : Finset (Σ σ : Ty, Fin (r σ))) :
    ∀ y : Letter Ty r n → T, eval₂Hom φ (fun ℓ : Letter Ty r n => y ℓ +
      if (⟨ℓ.1, ℓ.2.1⟩ : Σ σ : Ty, Fin (r σ)) ∈ R then ∑ j, N ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, (j, ℓ.2.2)⟩ else 0) P =
      eval₂Hom φ y P := by
  refine Finset.induction_on_max_value (fun p : (Σ σ : Ty, Fin (r σ)) => (p.2 : ℕ)) R ?_ ?_
  · intro y
    simp
  · intro p R hp hmax ih y
    obtain ⟨σ, i⟩ := p
    classical
    have hA := eval₂Hom_unipotent_substitution_eq φ hP σ i (N σ i) (hN σ i) y Finset.univ
    refine Eq.trans ?_ ((ih _).trans hA)
    refine congrArg (fun g => eval₂Hom φ g P) (funext fun ℓ => ?_)
    rcases ℓ with ⟨σ', i', b⟩
    by_cases hrow : (⟨σ', i'⟩ : Σ σ : Ty, Fin (r σ)) = ⟨σ, i⟩
    · cases hrow
      dsimp only
      rw [if_pos (Finset.mem_insert_self _ _), if_neg hp,
        if_pos (show ∃ b', (⟨σ, (i, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ from ⟨b, rfl⟩), add_zero]
    · have hne : ∀ j : Fin (r σ'), (⟨σ', j⟩ : Σ σ : Ty, Fin (r σ)) ≠ ⟨σ, i⟩ →
          ¬ ∃ b', (⟨σ', (j, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ := by
        rintro j hj ⟨b', h⟩
        apply hj
        cases h
        rfl
      dsimp only
      rw [if_neg (hne i' hrow)]
      by_cases hR : (⟨σ', i'⟩ : Σ σ : Ty, Fin (r σ)) ∈ R
      · rw [if_pos (Finset.mem_insert_of_mem hR), if_pos hR]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : i' ≤ j
        · rw [hN σ' i' j hj, zero_mul, zero_mul]
        · rw [if_neg (hne j ?_)]
          intro hji
          cases hji
          exact hj (Fin.le_iff_val_le_val.2 (hmax _ hR))
      · have hI : (⟨σ', i'⟩ : Σ σ : Ty, Fin (r σ)) ∉ insert ⟨σ, i⟩ R := by
          rw [Finset.mem_insert]
          rintro (h | h)
          exacts [hrow h, hR h]
        rw [if_neg hI, if_neg hR]
end Poly
section Op
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open scoped TensorProduct
variable {S : Type} [CommRing S] {d : ℕ}
end Op
end GlobalTheory.RowTriangular
namespace GlobalTheory
end GlobalTheory
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RowTriangular
open MvPolynomial
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k T : Type} [Field k] [CommRing T]
namespace GlobalTheory.RowTriangular
theorem _root_.solution [Infinite k] [Fintype Ty] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k}
    (hP : RowInv r n k P) (N : ∀ σ, Fin (r σ) → Fin (r σ) → T) (hN : ∀ σ i j, i ≤ j → N σ i j = 0)
    (y : Letter Ty r n → T) :
    eval₂Hom φ (fun ℓ : Letter Ty r n => y ℓ + ∑ j, N ℓ.1 ℓ.2.1 j * y ⟨ℓ.1, j, ℓ.2.2⟩) P = eval₂Hom φ y P := by
  classical
  have h := eval₂Hom_unipotent_block_substitution_eq φ hP N hN Finset.univ y
  simpa only [Finset.mem_univ, ↓reduceIte] using h
end GlobalTheory.RowTriangular
