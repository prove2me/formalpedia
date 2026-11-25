-- Prove2me | solution 1 for QuarticPairing.conjecture12_inconsistent_of_defect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:16.212669+00:00
-- url     : https://prove2.me/submissions/890dced5-3999-412a-99a5-005841855d45

module
public import Definitions.Def_QuarticPairing
public import Definitions.Def_QuarticPairing_Solution
public import Theorems.Thm_QuarticPairing_not_conjecture12_of_defect


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Asymptotics
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g : GaussianInt → ℂ) (Λ : GaussianInt → ℝ)
    (β : GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1) (E : GaussianInt → Prop)
    (h12 : ∀ c, ¬ E c → Λ c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c)
    (hE : ∀ ε : ℝ, 0 < ε →
      (fun X : ℕ => defectSum g Λ β E X) =O[Filter.atTop] (fun X : ℕ => (X : ℝ) ^ ((1 : ℝ) / 2 + ε))) :
    ¬ Conjecture12 g Λ β :=
  not_conjecture12_of_defect g Λ β hκ E h12 hE
end QuarticPairing
