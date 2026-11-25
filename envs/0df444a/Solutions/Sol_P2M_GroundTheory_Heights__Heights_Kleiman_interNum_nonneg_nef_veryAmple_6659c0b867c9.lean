-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_nef_veryAmple_6659c0b867c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:41.121776+00:00
-- url     : https://prove2.me/submissions/71e6b0be-cab6-4d8a-9abf-44339d06cf7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLeadingCoeffPos
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosCut
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_sec_not_mem_625a28c0b3ac


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
open MvPolynomial Filter
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (hR : GenericPointSectionInput.Statement.{u, w})
include hR
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : ∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin (n + 1) → LineBundle k x),
    IsSubvar x pp (n + 1) → Nef (L 0).toSubSystem → (∀ i, i ≠ 0 → IsVeryAmple (L i).toSubSystem) →
      0 ≤ interNum pp (fun i => (L i).toSubSystem) := by
  intro n
  induction n with
  | zero =>
    intro pp L hW hnef _
    have h1 : (fun i => (L i).toSubSystem) = ![(L 0).toSubSystem] := by
      funext i; fin_cases i; rfl
    rw [h1]
    exact hnef pp bot_le hW
  | succ n ih =>
    intro pp L hW hnef hL
    have hlast : Fin.last (n + 1) ≠ 0 := fun h => by simpa using congrArg Fin.val h
    obtain ⟨s, hs, hsI⟩ := exists_sec_not_mem (L (Fin.last (n + 1))) (hL _ hlast) hW
    have hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun i : Fin (n + 1) => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last (n + 1))).toSubSystem :=
      (Fin.snoc_init_self _).symm
    rw [hsplit, (hR k Ω N x).2.2.2.1 (n + 1) pp (fun i => L (Fin.castSucc i)) (L (Fin.last (n + 1))) s hW hs
      hsI]
    refine finsum_nonneg fun qq => ?_
    split_ifs with h
    · refine mul_nonneg (Nat.cast_nonneg _) (ih qq (fun i => L (Fin.castSucc i)) h.2 hnef fun i hi => ?_)
      exact hL _ fun h0 => hi (Fin.castSucc_injective _ (by rw [h0]; rfl))
    · exact le_rfl
end GroundTheory.Heights₂.Heights.Kleiman
