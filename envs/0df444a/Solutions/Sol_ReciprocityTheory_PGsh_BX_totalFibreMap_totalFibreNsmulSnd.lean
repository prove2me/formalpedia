-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.totalFibreMap_totalFibreNsmulSnd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:26:09.900435+00:00
-- url     : https://prove2.me/submissions/b82d2328-780b-4196-9543-fbcca168c010

import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_SmKerSurj
import Definitions.Def_ReciprocityTheory_DualLattices_TangentPairingStatement
import Definitions.Def_ReciprocityTheory_DualLattices_TotalFibreMapTotalFibreNsmulSnd
import Theorems.Thm_ReciprocityTheory_PGsh_BX_tot_ext
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open TensorProduct
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
namespace BX
variable (B : BX R₀)
private lemma pmap_tr2_heq {R S : LAlg R₀} (f : LHom R S) {x y y' : B.G R} (h : y = y')
    (v : B.P R x y) : HEq (B.pmap f (B.tr2 h v)) (B.pmap f v) := by
  subst h
  exact HEq.rfl
private lemma tr2_heq {R : LAlg R₀} {x y y' : B.G R} (h : y = y') (v : B.P R x y) :
    HEq (B.tr2 h v) v := by
  subst h
  exact HEq.rfl
private lemma add2_heq_of_heq {R : LAlg R₀} {x y₁ y₂ z : B.G R} (h : y₁ = y₂) {a : B.P R x y₁}
    {a' : B.P R x y₂} (b : B.P R x z) (e : HEq a a') : HEq (B.add2 a b) (B.add2 a' b) := by
  subst h
  cases e
  exact HEq.rfl
private lemma pmap_nsmul2_heq {R S : LAlg R₀} (f : LHom R S) {x y : B.G R} (u : B.P R x y)
    (n : ℕ) : HEq (B.pmap f (B.nsmul2 u n)) (B.nsmul2 (B.pmap f u) n) := by
  induction n with
  | zero =>
    change HEq (B.pmap f (B.tr2 _ (B.zero2 x))) (B.tr2 _ (B.zero2 (B.map f x)))
    exact ((pmap_tr2_heq B f _ _).trans (B.zeroSnd_nat f x)).trans (tr2_heq B _ _).symm
  | succ n ih =>
    change HEq (B.pmap f (B.tr2 _ (B.add2 (B.nsmul2 u n) u)))
      (B.tr2 _ (B.add2 (B.nsmul2 (B.pmap f u) n) (B.pmap f u)))
    refine (pmap_tr2_heq B f _ _).trans ((B.addSnd_nat f _ _).trans ?_)
    exact (add2_heq_of_heq B (map_nsmul (B.map f) n y) (B.pmap f u) ih).trans
      (tr2_heq B _ _).symm
section Fibre
variable {F R₁ R₂ R : LAlg R₀} {p₁ : LHom F R₁} {p₂ : LHom F R₂} {f₁ : LHom R₁ R}
  {f₂ : LHom R₂ R}
end Fibre
end BX
end ReciprocityTheory.PGsh
end
end

set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀)
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {R S : LAlg R₀} (f : LHom R S) (N : ℕ) (t : B.Tot R) :
    B.Tmap f (B.totalFibreNsmulSnd N t) = B.totalFibreNsmulSnd N (B.Tmap f t) :=
  B.tot_ext rfl (map_nsmul (B.map f) N t.2.1) (pmap_nsmul2_heq B f t.2.2 N)
end ReciprocityTheory.PGsh.BX
