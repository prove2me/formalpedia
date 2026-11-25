-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_interNum_nonneg_of_veryAmple_68e58f10b840
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:34.338858+00:00
-- url     : https://prove2.me/submissions/e77df609-d830-4b48-8d7d-814a9bc76c6f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
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
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (hR : GenericPointSectionInput.Statement.{u, w})
include hR
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : ∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x),
    IsSubvar x pp n → (∀ i, IsVeryAmple (L i).toSubSystem) →
      0 ≤ interNum pp (fun i => (L i).toSubSystem) := by
  intro n
  induction n with
  | zero =>
    intro pp L hW _
    have h0 : (fun i => (L i).toSubSystem) = (![] : Fin 0 → SubSystem k x Ω) :=
      funext fun i => i.elim0
    rw [h0, (hR k Ω N x).2.2.2.2 pp hW]
    exact Nat.cast_nonneg _
  | succ n ih =>
    intro pp L hW hL
    obtain ⟨s, hs, hsI⟩ := exists_sec_not_mem (L (Fin.last n)) (hL _) hW
    have hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun i : Fin n => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last n)).toSubSystem :=
      (Fin.snoc_init_self _).symm
    rw [hsplit, (hR k Ω N x).2.2.2.1 n pp (fun i => L (Fin.castSucc i)) (L (Fin.last n)) s hW hs hsI]
    refine finsum_nonneg fun qq => ?_
    split_ifs with h
    · exact mul_nonneg (Nat.cast_nonneg _) (ih qq _ h.2 fun i => hL _)
    · exact le_rfl
end GroundTheory.Heights₂.Heights.Kleiman
