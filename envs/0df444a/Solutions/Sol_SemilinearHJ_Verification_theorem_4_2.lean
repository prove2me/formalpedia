-- Prove2me | solution 1 for SemilinearHJ.Verification.theorem_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:38:03.828036+00:00
-- url     : https://prove2.me/submissions/60b0340b-fde2-4e52-a85a-406a62112981
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SemilinearHJ_Verification_Setting
import Theorems.Thm_SemilinearHJ_Verification_proposition_4_4

open SemilinearHJ.Verification
open scoped ENNReal MeasureTheory

theorem solution {n : ℕ} (X : Set (E n)) (hX : IsPolytope X)
    (Ψ : E n → E n) (hΨL : ∃ K : NNReal, LipschitzOnWith K Ψ X) (hΨ0 : ∀ x ∈ X, ∀ i, 0 ≤ Ψ x i)
    (r : ℝ) (hr : 0 < r)
    (X0 : Set (E n)) (hX0c : IsCompact X0) (hX0X : X0 ⊆ X) (hX0 : X0.Nonempty) :
    (∀ x ∈ X, srcVal X Ψ r X0 x ≠ ⊤) ∧
      IsMaxViscSol X Ψ r X0 (fun x => (srcVal X Ψ r X0 x).toReal) ∧
      ∀ V' : E n → ℝ, IsMaxViscSol X Ψ r X0 V' →
        ∀ x ∈ X, V' x = (srcVal X Ψ r X0 x).toReal := by
  obtain ⟨hfin, hmax⟩ := proposition_4_4 X hX Ψ hΨL hΨ0 r hr X0 hX0c hX0X hX0
  refine ⟨hfin, hmax, fun V' hV' x hx => le_antisymm (hmax.2 V' hV'.1 x hx) (hV'.2 _ hmax.1 x hx)⟩
