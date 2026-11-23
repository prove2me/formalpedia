-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.pairing_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:34.392858+00:00
-- url     : https://prove2.me/submissions/0d07ff3e-277b-4a36-89bc-9d76ab140e44

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Theorems.Thm_ReciprocityTheory_PGsh_BX_castFst_eq_iff
import Theorems.Thm_ReciprocityTheory_PGsh_BX_castSnd_eq_iff
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pmap_nsmul1
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pmap_nsmul2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {S : LAlg R₀} (f : LHom R S) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ)
    (h : B.IsPairing N x y z) :
    B.IsPairing N (B.map f x) (B.map f y) (Units.map (f.1 : R →* S) z) := by
  obtain ⟨hx, hy, u, l₁, l₂, e₁, e₂, rfl⟩ := h
  have hx' : N • B.map f x = 0 := by rw [← map_nsmul, hx, map_zero]
  have hy' : N • B.map f y = 0 := by rw [← map_nsmul, hy, map_zero]

  have hsm1 : ∀ (c : (S : Type u)ˣ) {a b b' : B.G S} (e : b = b') (v : B.P S b a) (v' : B.P S b' a), HEq v v' →
      HEq (B.smul c v) (B.smul c v') := by
    intro c a b b' e v v' hv
    subst e
    rw [eq_of_heq hv]
  have hsm2 : ∀ (c : (S : Type u)ˣ) {a b b' : B.G S} (e : b = b') (v : B.P S a b) (v' : B.P S a b'), HEq v v' →
      HEq (B.smul c v) (B.smul c v') := by
    intro c a b b' e v v' hv
    subst e
    rw [eq_of_heq hv]
  have hpm1 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R b a) (v' : B.P R b' a), HEq v v' →
      HEq (B.pmap f v) (B.pmap f v') := by
    intro a b b' e v v' hv
    subst e
    rw [eq_of_heq hv]
  have hpm2 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R a b) (v' : B.P R a b'), HEq v v' →
      HEq (B.pmap f v) (B.pmap f v') := by
    intro a b b' e v v' hv
    subst e
    rw [eq_of_heq hv]
  have htr1 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R b a), HEq v (B.tr1 e v) := by
    intro a b b' e v
    subst e
    rfl
  have htr2 : ∀ {a b b' : B.G R} (e : b = b') (v : B.P R a b), HEq v (B.tr2 e v) := by
    intro a b b' e v
    subst e
    rfl
  refine ⟨hx', hy', B.pmap f u, Units.map _ l₁, Units.map _ l₂, ?_, ?_, map_div _ _ _⟩
  · rw [B.castFst_eq_iff]
    refine Sigma.ext hx' ?_
    refine (B.pmap_nsmul1 f u N).symm.trans ?_
    refine (hpm1 hx _ _ (htr1 hx _)).trans ?_
    rw [e₁, B.pmap_smul]
    exact hsm1 _ (map_zero _) _ _ (B.zeroFst_nat f y)
  · rw [B.castSnd_eq_iff]
    refine Sigma.ext hy' ?_
    refine (B.pmap_nsmul2 f u N).symm.trans ?_
    refine (hpm2 hy _ _ (htr2 hy _)).trans ?_
    rw [e₂, B.pmap_smul]
    exact hsm2 _ (map_zero _) _ _ (B.zeroSnd_nat f x)
end ReciprocityTheory.PGsh.BX
