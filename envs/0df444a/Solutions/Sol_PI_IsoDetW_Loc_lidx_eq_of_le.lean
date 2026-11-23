-- Prove2me | solution 1 for PI.IsoDetW.Loc.lidx_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:50.14114+00:00
-- url     : https://prove2.me/submissions/b0a9b852-971f-454b-b53f-5795491be624

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm
import Theorems.Thm_PI_IsoDetW_Loc_rlen_add
import Theorems.Thm_PI_IsoDetW_Loc_localization_mono
import Theorems.Thm_PI_IsoDetW_Loc_lidx_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs
variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
variable (p : Ideal R) [p.IsPrime]
namespace PI.IsoDetW.Loc
theorem _root_.solution {A B D : Submodule R W} (hD : D ≤ A ⊓ B)
    (hA : relative₂ (localization₂ p D) (localization₂ p A) ≠ ⊤) (hB : relative₂ (localization₂ p D) (localization₂ p B) ≠ ⊤) :
    lidx p A B = ((relative₂ (localization₂ p D) (localization₂ p A)).toNat : ℤ) - (relative₂ (localization₂ p D) (localization₂ p B)).toNat := by
  have e1 := rlen_add (localization_mono p hD) (localization_mono p (inf_le_left : A ⊓ B ≤ A))
  have e2 := rlen_add (localization_mono p hD) (localization_mono p (inf_le_right : A ⊓ B ≤ B))
  rw [e1] at hA ⊢
  rw [e2] at hB ⊢
  rw [lidx_eq]
  have l1 : ∀ a b : ℕ∞, a + b ≠ ⊤ → a ≠ ⊤ := fun a b h ha => h (by simp [ha])
  have l2 : ∀ a b : ℕ∞, a + b ≠ ⊤ → b ≠ ⊤ := fun a b h hb => h (by simp [hb])
  rw [ENat.toNat_add (l1 _ _ hA) (l2 _ _ hA), ENat.toNat_add (l1 _ _ hB) (l2 _ _ hB)]
  push_cast
  ring
end PI.IsoDetW.Loc
