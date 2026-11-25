-- Prove2me | solution 1 for P2M_GlobalTheory_QuotientMapComposition_map_mk__of_comp_160cf9274fad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:31:14.230453+00:00
-- url     : https://prove2.me/submissions/77a21aa8-391e-4550-996d-402d9c60793d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapMkOfComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.QuotientMapComposition
namespace GlobalTheory.QuotientMapComposition
theorem _root_.solution {A R LA LR : Type} [CommRing A] [CommRing R] [CommRing LA] [CommRing LR]
    [Algebra A LA] [Algebra R LR] (f : A →+* R) (F : LA →+* LR)
    (h : F.comp (algebraMap A LA) = (algebraMap R LR).comp f) (M : Submonoid A) [IsLocalization M LA]
    (N : Submonoid R) [IsLocalization N LR] (a : A) (m : M) (n : N) (hn : (n : R) = f m) :
    F (IsLocalization.mk' LA a m) = IsLocalization.mk' LR (f a) n := by
  have hx : ∀ x, F (algebraMap A LA x) = algebraMap R LR (f x) := fun x => RingHom.congr_fun h x
  rw [IsLocalization.eq_mk'_iff_mul_eq, hn, ← hx, ← hx, ← map_mul, IsLocalization.mk'_spec]
end GlobalTheory.QuotientMapComposition
