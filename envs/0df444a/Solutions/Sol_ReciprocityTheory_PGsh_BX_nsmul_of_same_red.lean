-- Prove2me | solution 1 for ReciprocityTheory.PGsh.BX.nsmul_of_same_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:01:19.99197+00:00
-- url     : https://prove2.me/submissions/0dac1d7c-efa2-45a2-9ed7-d155181cbd9c

import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NilSurjOfSqZero
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulTensorEqZero
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul1_smul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_nsmul2_smul
import Theorems.Thm_ReciprocityTheory_PGsh_DualPair_natCast_D
import Theorems.Thm_ReciprocityTheory_PGsh_FP_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀} (Dp : DualPair R)
namespace ReciprocityTheory.PGsh.BX
theorem _root_.solution {N : ℕ} (hN : (N : (R : Type u)) = 0) {x y : B.G Dp.D}
    {x₀ y₀ : B.G R} (e : B.P R x₀ y₀) (u v : B.P Dp.D x y) (hu : HEq (B.pmap Dp.π u) e)
    (hv : HEq (B.pmap Dp.π v) e) : B.nsmul1 u N = B.nsmul1 v N ∧ B.nsmul2 u N = B.nsmul2 v N := by
  obtain ⟨l, hl⟩ := B.exists_smul u v
  have hπl : Units.map (Dp.π.1 : (Dp.D : Type u) →* (R : Type u)) l = 1 := by
    have h1 : B.pmap Dp.π v = B.smul (Units.map (Dp.π.1 : (Dp.D : Type u) →* (R : Type u)) l) (B.pmap Dp.π u) := by
      rw [← hl, B.pmap_smul]
    have h2 : B.pmap Dp.π u = B.pmap Dp.π v := eq_of_heq (hu.trans hv.symm)
    rw [h2] at h1
    exact B.smul_eq_self h1.symm
  have hπl' : Dp.π.1 (l : (Dp.D : Type u)) = 1 := by
    have := congrArg Units.val hπl
    simpa using this
  set d : (Dp.D : Type u) := (l : (Dp.D : Type u)) - 1 with hd
  have hdk : Dp.π.1 d = 0 := by rw [hd, map_sub, hπl', map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Dp.mem_span_of_π d hdk)
  have hdd : d * d = 0 := by
    rw [← ha]
    calc a * Dp.η * (a * Dp.η) = a * a * (Dp.η * Dp.η) := by ring
      _ = 0 := by rw [Dp.η_sq, mul_zero]
  have hNd : (N : (Dp.D : Type u)) * d = 0 := by
    rw [Dp.natCast_D hN, zero_mul]
  have hpow : ∀ n : ℕ, (1 + d) ^ n = 1 + (n : (Dp.D : Type u)) * d := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      have : (1 + (k : (Dp.D : Type u)) * d) * (1 + d) = 1 + ((k : (Dp.D : Type u)) + 1) * d + k * (d * d) := by
        ring
      rw [this, hdd]
      push_cast
      ring
  have hlN : l ^ N = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, show (l : (Dp.D : Type u)) = 1 + d by rw [hd]; ring, hpow, hNd,
      add_zero]
  constructor
  · rw [← hl, B.nsmul1_smul, hlN, B.one_smul]
  · rw [← hl, B.nsmul2_smul, hlN, B.one_smul]
end ReciprocityTheory.PGsh.BX
