-- Prove2me | solution 1 for P2M_GlobalTheory_Cris_SqExt___val_f4635455550d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:09.114824+00:00
-- url     : https://prove2.me/submissions/b05302ba-3b19-444d-90ad-448862c97ae0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_Cris_ev_comp
import Theorems.Thm_GlobalTheory_Cris_SqExt_val_apply

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
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {I : Ideal R} {I' : Ideal R'}
  {I'' : Ideal R''} {X X' X'' : Scheme.{0}}
attribute [instance] Thick.ring Thick.alg Thick.ring₀
attribute [instance] SqExt.ringC SqExt.ringB SqExt.algC SqExt.algB
open GlobalTheory.Cris.SqExt
variable {s : X ⟶ Sp R} (E E' : SqExt R)
namespace GlobalTheory.Cris.SqExt
theorem _root_.solution (y : Sp E.C ⟶ X) (hy : y ≫ s = spMap (algebraMap R E.C)) (f : Form s) :
    E.π (E.val y hy f.1) = 0 := by
  let ρ : E.thick (spMap (E.π : E.C →+* E.B) ≫ y) (E.red_w hy) ⟶
      Thick.triv E.B (spMap (E.π : E.C →+* E.B) ≫ y) (E.red_w hy) :=
    { φ := E.π
      φ₀ := RingHom.id _
      comm := fun _ ↦ rfl
      dp := by
        refine (isDPMorphism_iff _ _ _).2
          ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_, fun n hn a ha ↦ ?_⟩
        · exact Ideal.mem_bot.2 (RingHom.mem_ker.1 ha)
        · rw [RingHom.mem_ker.1 ha, (dp0 E.B).dpow_eval_zero hn]
          rcases Nat.lt_or_ge n 2 with h2 | h2
          · obtain rfl : n = 1 := by omega
            rw [(divided₂ E.sq).dpow_one ha, RingHom.mem_ker.1 ha]
          · rw [squareZeroDividedPowers_dpow E.sq h2, map_zero]
      pt := by
        change spMap (RingHom.id E.B) ≫ spMap (E.π : E.C →+* E.B) ≫ y =
          spMap (E.π : E.C →+* E.B) ≫ y
        rw [spMap_id, Category.id_comp] }
  have k1 : ev f.1 (E.secHom (E.red_w hy) E.i E.π_i ≫ ρ) = 0 :=
    f.2 (E.secHom (E.red_w hy) E.i E.π_i ≫ ρ) rfl rfl
  have k2 : ev f.1 (E.idHom hy ≫ ρ) = 0 := f.2 (E.idHom hy ≫ ρ) rfl rfl
  rw [ev_comp] at k1 k2
  rw [val_apply, map_sub]
  exact sub_eq_zero.2 (add_right_cancel (k1.trans k2.symm))
end GlobalTheory.Cris.SqExt
