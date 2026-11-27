-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pieriSt_count_inhabited
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:23:55.89924+00:00
-- url     : https://prove2.me/submissions/1be4172a-750d-45ae-a3a3-cac57af3b4ee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_StTest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) :
    Continuous (fun k : KG ε =>
      (((1 : KG ε →* unitary (Matrix Unit Unit ℂ)) k : unitary (Matrix Unit Unit ℂ)) : Matrix Unit Unit ℂ)) ∧
    (∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ =>
        (((1 : KG ε →* unitary (Matrix Unit Unit ℂ)) (γ t) : unitary (Matrix Unit Unit ℂ)) :
          Matrix Unit Unit ℂ) i j)
        ((0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) X i j) 0) ∧
    Formalism.REAL.KRel ε (fun a b => (0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a b 1)) ∧
    (∀ a, (0 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix Unit Unit ℂ) (Matrix.single a a 1) =
      Matrix.diagonal fun i => (((fun _ : Unit => (0 : Fin n → ℝ)) i a : ℝ) : ℂ)) ∧
    Function.Injective (fun _ : Unit => (0 : Fin n → ℝ)) ∧
    (∑ i : Unit, weylK ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) =
      (Fintype.card Unit : ℝ) * weylK ε 0) ∧
    (∀ i : Unit, ¬ KDom ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) →
      weylK ε ((0 : Fin n → ℝ) + (fun _ : Unit => (0 : Fin n → ℝ)) i) = 0) ∧
    Nonempty (KType ε 0) := by
  refine ⟨?_, ?_, ?_, ?_, fun a b _ => Subsingleton.elim a b, ?_, ?_, ⟨trivialKType ε⟩⟩
  · simp only [MonoidHom.one_apply]; exact continuous_const
  · intro X _ γ _ i j
    simp only [MonoidHom.one_apply, LinearMap.zero_apply]
    exact hasDerivAt_const _ _
  · intro a b c d _ _; simp
  · intro a; ext i j; simp
  · simp
  · intro i h
    exact absurd (fun a b _ _ => by simp) h
end ReciprocityTheory.ChartRestriction.DS.HW
