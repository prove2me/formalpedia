-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.rowInv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:50.004127+00:00
-- url     : https://prove2.me/submissions/4b7018db-9b8d-4c77-8b1f-91740c8f7c5a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Mathlib.Algebra.MvPolynomial.Funext
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_FFVMap
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_eval_aeval__5dda70722a7a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open NumberField IsDedekindDomain Formalism.L2.Pj MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k K : Type} [Field k] [Field K]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution [Infinite k] (io : k →+* K) {P : MvPolynomial (Letter Ty r n) k} (hP : RowInv r n k P) :
    RowInv r n K (P.map io) := by
  classical
  intro σ i i' hi t
  let g : Letter Ty r n → MvPolynomial (Option (Letter Ty r n)) k := fun ℓ =>
    if ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ then X (some ℓ) + X none * X (some ⟨σ, i', ℓ.2.2⟩) else X (some ℓ)
  let ψ : Option (Letter Ty r n) → MvPolynomial (Letter Ty r n) K := fun o => Option.elim o (C t) X
  have hΦ : aeval g P = rename some P := by
    refine MvPolynomial.funext fun x => ?_
    have e := congrArg (eval (x ∘ some)) (hP σ i i' hi (x none))
    rw [eval_rename, ← e, eval_aeval', rowShift, eval_aeval']
    refine congrArg (fun f => eval f P) (funext fun ℓ => ?_)
    by_cases hc : ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ <;> simp [g, hc]
  have h1 : ∀ Q : MvPolynomial (Letter Ty r n) k,
      rowShift r n K σ i i' t (Q.map io) = aeval ψ ((aeval g Q).map io) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a => simp [ψ]
    | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq]
    | mul_X p ℓ hp =>
      simp only [map_mul, hp, map_X, aeval_X]
      congr 1
      by_cases hc : ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ <;> simp [rowShift, g, ψ, hc]
  have h2 : aeval ψ ((rename some P).map io) = P.map io := by
    rw [map_rename, aeval_rename]
    have : (ψ ∘ some) = X := rfl
    rw [this, aeval_X_left_apply]
  rw [h1, hΦ, h2]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
