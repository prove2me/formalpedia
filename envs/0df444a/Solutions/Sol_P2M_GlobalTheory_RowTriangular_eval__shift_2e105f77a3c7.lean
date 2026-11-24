-- Prove2me | solution 1 for P2M_GlobalTheory_RowTriangular_eval__shift_2e105f77a3c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:16:31.097011+00:00
-- url     : https://prove2.me/submissions/ddd1063d-474a-46cf-bd7d-a3162c12bf7b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one



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
theorem _root_.solution [Infinite k] (φ : k →+* T) {P : MvPolynomial (Letter Ty r n) k} (hP : RowInv r n k P)
    (σ : Ty) (i i' : Fin (r σ)) (hi : i' < i) (t : T) (y y' : Letter Ty r n → T)
    (h₁ : ∀ b, y' ⟨σ, i, b⟩ = y ⟨σ, i, b⟩ + t * y ⟨σ, i', b⟩)
    (h₂ : ∀ ℓ, (¬ ∃ b, ℓ = ⟨σ, i, b⟩) → y' ℓ = y ℓ) :
    eval₂Hom φ y' P = eval₂Hom φ y P := by
  classical
  let _ : Algebra k T := φ.toAlgebra
  let G : Letter Ty r n → MvPolynomial (Option (Letter Ty r n)) k := fun ℓ =>
    if ∃ b, ℓ = ⟨σ, (i, b)⟩ then X (some ℓ) + X none * X (some ⟨σ, (i', ℓ.snd.2)⟩) else X (some ℓ)
  have hQ : aeval G P = rename some P := by
    apply MvPolynomial.funext
    intro x
    have h1 := congrArg (aeval (x ∘ some)) (hP σ i i' hi (x none))
    unfold rowShift at h1
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h1
    change aeval x (aeval G P) = aeval x (rename some P)
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, aeval_rename, ← h1]
    congr 2
    funext ℓ
    by_cases hℓ : ∃ b, ℓ = ⟨σ, (i, b)⟩
    · simp [G, hℓ]
    · simp [G, hℓ]
  let g : Option (Letter Ty r n) → T := fun o => o.elim t y
  have e1 : (fun ℓ => aeval g (G ℓ)) = y' := by
    funext ℓ
    by_cases hℓ : ∃ b, ℓ = ⟨σ, (i, b)⟩
    · obtain ⟨b, rfl⟩ := hℓ
      simp only [G, if_pos (show ∃ b', (⟨σ, (i, b)⟩ : Letter Ty r n) = ⟨σ, (i, b')⟩ from ⟨b, rfl⟩)]
      simp [g, h₁]
    · simp only [G, if_neg hℓ]
      simp [g, h₂ ℓ hℓ]
  have e2 := congrArg (aeval g) hQ
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, aeval_rename, e1] at e2
  exact e2
end GlobalTheory.RowTriangular
