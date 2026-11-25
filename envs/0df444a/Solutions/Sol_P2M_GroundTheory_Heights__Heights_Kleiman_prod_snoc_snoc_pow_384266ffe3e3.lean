-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_prod_snoc_snoc_pow_384266ffe3e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:35:14.336016+00:00
-- url     : https://prove2.me/submissions/326016bd-1cdb-45bd-a5ff-6f6abf3932fc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StSubsetDiffConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PSubsetDiffConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (n : ℕ) (T : Finset (Fin n)) (m : ℕ) (c : ℤ) (e : Fin (n + 1 + 1) → ℕ) :
    ∏ j, (Fin.snoc (α := fun _ => ℚ)
        (fun j => ((Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m j : ℕ) : ℚ))
        (c : ℚ) j) ^ e j =
      (∏ i : Fin n, (if i ∈ T then (1 : ℚ) else 0) ^ e i.castSucc.castSucc) *
        (m : ℚ) ^ e (Fin.last n).castSucc * (c : ℚ) ^ e (Fin.last (n + 1)) := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  congr 2
  refine prod_congr rfl fun i _ => ?_
  split_ifs <;> simp
end GroundTheory.Heights₂.Heights.Kleiman
