-- Prove2me | solution 1 for P2M_Formalism_REAL_sum_sum_sum_sum_comm__604324486430
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:47:29.934796+00:00
-- url     : https://prove2.me/submissions/0037f778-714a-41ce-915e-66b7dbc4d21b

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {A : Type*} [Ring A] {m n : ℕ} (B P : Fin m → Fin n → A)
variable {B P}
variable (hBP : ∀ i j a b, B i a * P j b - P j b * B i a = if i = j ∧ a = b then 1 else 0)
  (hBB : ∀ i j a b, B i a * B j b = B j b * B i a)
  (hPP : ∀ i j a b, P i a * P j b = P j b * P i a)
include hBP hBB hPP
omit hBP hBB hPP
namespace Formalism.REAL
theorem _root_.solution {α β : Type*} [Fintype α] [Fintype β] (f : α → α → β → β → A) :
    ∑ x, ∑ y, ∑ i, ∑ j, f i j x y = ∑ i, ∑ j, ∑ x, ∑ y, f i j x y := by
  have h1 : ∀ x, ∑ y, ∑ i, ∑ j, f i j x y = ∑ i, ∑ j, ∑ y, f i j x y := by
    intro x
    calc ∑ y, ∑ i, ∑ j, f i j x y = ∑ i, ∑ y, ∑ j, f i j x y := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ y, f i j x y := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have h2 : ∀ i, ∑ x, ∑ j, ∑ y, f i j x y = ∑ j, ∑ x, ∑ y, f i j x y := fun i => Finset.sum_comm
  calc ∑ x, ∑ y, ∑ i, ∑ j, f i j x y = ∑ x, ∑ i, ∑ j, ∑ y, f i j x y :=
        Finset.sum_congr rfl fun x _ => h1 x
    _ = ∑ i, ∑ x, ∑ j, ∑ y, f i j x y := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ x, ∑ y, f i j x y := Finset.sum_congr rfl fun i _ => h2 i
end Formalism.REAL
