-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_block_chain_f2c1248d48d1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:15.734105+00:00
-- url     : https://prove2.me/submissions/7fe65de3-bb3f-4549-8e88-eaf5f8acb899

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible

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
open GroundTheory.Heights₂.Heights.AntisymDivisible
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution {N j : ℕ} (R : Fin N → Fin N → Prop)
    (hadj : ∀ a b : Fin N, b.val = a.val + 1 → (b.val < j ∨ j ≤ a.val) → R a b)
    (hstep : ∀ a c b : Fin N, a.val < c.val → c.val + 1 = b.val → (b.val < j ∨ j ≤ a.val) →
      R a c → R c b → R a b) :
    ∀ a b : Fin N, a.val < b.val → (b.val < j ∨ j ≤ a.val) → R a b := by
  suffices H : ∀ k : ℕ, ∀ a b : Fin N, b.val = a.val + 1 + k → (b.val < j ∨ j ≤ a.val) → R a b by
    intro a b hab hbl
    exact H (b.val - a.val - 1) a b (by omega) hbl
  intro k
  induction k with
  | zero => intro a b hb hbl; exact hadj a b (by omega) hbl
  | succ k ih =>
    intro a b hb hbl
    have hcN : a.val + 1 + k < N := by omega
    let c : Fin N := ⟨a.val + 1 + k, hcN⟩
    exact hstep a c b (by simp only [c]; omega) (by simp only [c]; omega) hbl
      (ih a c rfl (by simp only [c]; omega)) (hadj c b (by simp only [c]; omega) (by simp only [c]; omega))
end GroundTheory.Heights₂.Heights.AntisymDivisible
