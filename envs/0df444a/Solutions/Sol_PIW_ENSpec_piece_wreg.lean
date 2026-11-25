-- Prove2me | solution 1 for PIW.ENSpec.piece_wreg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:44:00.356406+00:00
-- url     : https://prove2.me/submissions/82fd4f0f-b252-4298-acaa-d26c8071dd30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton
import Theorems.Thm_PIW_ENSpec_wreg_neg
import Theorems.Thm_P2M_PIW_ENSpec_forall__ofFn_a8a2da7e4e0d
import Theorems.Thm_PIW_ENSpec_free_homog
import Theorems.Thm_PIW_ENSpec_emb_injective
import Theorems.Thm_PIW_ENSpec_emb_surjective
import Theorems.Thm_PIW_ENSpec_emb_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open PIW PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
variable {R : Type u} [CommRing R] {D : ℕ}
local notation "𝔛" => Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))
namespace PIW.ENSpec
theorem _root_.solution (a : ℕ) (x : Fin D → R) (hx : IsWeaklyRegular R (List.ofFn x)) :
    IsWeaklyRegular (LinearMap.ker (gmap (R := R) (D := D) a)) (tl x) := by
  have hneg : IsWeaklyRegular R (List.ofFn fun i => -x i) := by
    have := (wreg_neg (M := R) (List.ofFn x)).2 hx
    simpa [List.map_ofFn, Function.comp_def] using this
  have := free_homog (R := R) (D := D) a
  have ht := hneg.isWeaklyRegular_lTensor (M₂ := homogeneousSubmodule (Fin D) R a)
  have hH := ((TensorProduct.rid R (homogeneousSubmodule (Fin D) R a)).isWeaklyRegular_congr _).1 ht
  exact ((AddEquiv.ofBijective (emb a) ⟨emb_injective a, emb_surjective a⟩).isWeaklyRegular_congr
    (forall₂_ofFn _ _ fun i h => emb_smul a x i h)).1 hH
end PIW.ENSpec
