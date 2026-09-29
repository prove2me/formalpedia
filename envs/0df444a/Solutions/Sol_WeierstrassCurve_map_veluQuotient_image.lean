-- Prove2me | solution 1 for WeierstrassCurve.map_veluQuotient_image
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/acc6ff0e-f1fb-5cbe-b75d-e355a297e12f

import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_map_veluQuotient_image
open WeierstrassCurve

private theorem aux_map_veluT {R R' : Type*} [CommRing R] [CommRing R']
    (W : WeierstrassCurve R) (f : R →+* R') (x y : R) :
    (W.map f).veluT (f x) (f y) = f (W.veluT x y) := by
  simp only [veluT_eq, map_b₂, map_b₄, map_ofNat, map_add, map_mul, map_pow]

private theorem aux_map_veluW {R R' : Type*} [CommRing R] [CommRing R']
    (W : WeierstrassCurve R) (f : R →+* R') (x y : R) :
    (W.map f).veluW (f x) (f y) = f (W.veluW x y) := by
  simp only [veluW, veluU, veluGy, map_a₁, map_a₃, aux_map_veluT, map_ofNat, map_neg, map_add,
    map_mul, map_pow]

private theorem aux_map_veluTSum_image {R R' : Type*} [CommRing R] [CommRing R']
    [DecidableEq R'] (W : WeierstrassCurve R) (f : R →+* R') (S : Finset (R × R))
    (hinj : (S.image (Prod.map f f)).card = S.card) :
    (W.map f).veluTSum (S.image (Prod.map f f)) = f (W.veluTSum S) := by
  have hinj' : Set.InjOn (Prod.map f f) S := Finset.card_image_iff.mp hinj
  rw [veluTSum, veluTSum, Finset.sum_image hinj', map_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simp only [Prod.map_fst, Prod.map_snd, aux_map_veluT]

private theorem aux_map_veluWSum_image {R R' : Type*} [CommRing R] [CommRing R']
    [DecidableEq R'] (W : WeierstrassCurve R) (f : R →+* R') (S : Finset (R × R))
    (hinj : (S.image (Prod.map f f)).card = S.card) :
    (W.map f).veluWSum (S.image (Prod.map f f)) = f (W.veluWSum S) := by
  have hinj' : Set.InjOn (Prod.map f f) S := Finset.card_image_iff.mp hinj
  rw [veluWSum, veluWSum, Finset.sum_image hinj', map_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simp only [Prod.map_fst, Prod.map_snd, aux_map_veluW]

theorem solution
    {R R' : Type*} [CommRing R] [CommRing R'] [DecidableEq R'] (W : WeierstrassCurve R)
    (f : R →+* R') (S : Finset (R × R))
    (hinj : (S.image (Prod.map f f)).card = S.card) :
    (W.map f).veluQuotient (S.image (Prod.map f f)) = (W.veluQuotient S).map f := by
  ext
  · simp only [veluQuotient_a₁, map_a₁]
  · simp only [veluQuotient_a₂, map_a₂]
  · simp only [veluQuotient_a₃, map_a₃]
  · simp only [veluQuotient_a₄, map_a₄, aux_map_veluTSum_image W f S hinj, map_ofNat, map_sub,
      map_mul]
  · simp only [veluQuotient_a₆, map_a₆, map_b₂, aux_map_veluTSum_image W f S hinj,
      aux_map_veluWSum_image W f S hinj, map_ofNat, map_sub, map_mul]

end S_WeierstrassCurve_map_veluQuotient_image
end P2MW
export P2MW.S_WeierstrassCurve_map_veluQuotient_image (solution)
