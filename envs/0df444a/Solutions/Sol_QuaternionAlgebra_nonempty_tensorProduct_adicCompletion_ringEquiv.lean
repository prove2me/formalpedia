-- Prove2me | solution 1 for QuaternionAlgebra.nonempty_tensorProduct_adicCompletion_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2e119263-76e6-55b8-a145-f596daac5126

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_nonempty_tensorProduct_adicCompletion_ringEquiv

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace E1bChi

section General

variable {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K] (a b : R)

local notation "a'" => algebraMap R K a
local notation "b'" => algebraMap R K b

def basisRK : QuaternionAlgebra.Basis (R := R) ℍ[K, a', b'] a 0 b where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, 0, 1⟩
  i_mul_i := by
    ext <;> simp [Algebra.smul_def, QuaternionAlgebra.algebraMap_eq] <;>
      simp [Algebra.algebraMap_eq_smul_one]
  j_mul_j := by
    ext <;> simp [Algebra.smul_def, QuaternionAlgebra.algebraMap_eq] <;>
      simp [Algebra.algebraMap_eq_smul_one]
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

def toK : ℍ[R, a, b] →ₐ[R] ℍ[K, a', b'] := (basisRK a b).liftHom

theorem algebraMap_apply' (s : R) : algebraMap R ℍ[K, a', b'] s = ((algebraMap R K s : K) : ℍ[K, a', b']) := rfl

theorem toK_apply (x : ℍ[R, a, b]) :
    toK a b x = ⟨algebraMap R K x.re, algebraMap R K x.imI, algebraMap R K x.imJ, algebraMap R K x.imK⟩ := by
  show (basisRK a b).lift x = _
  rw [QuaternionAlgebra.Basis.lift]
  ext <;> simp [basisRK, algebraMap_apply', Algebra.smul_def]

def ofK : K →ₐ[R] ℍ[K, a', b'] := (Algebra.ofId K ℍ[K, a', b']).restrictScalars R

theorem ofK_apply (t : K) : ofK a b t = (t : ℍ[K, a', b']) := rfl

def fwd : ℍ[R, a, b] ⊗[R] K →ₐ[R] ℍ[K, a', b'] :=
  Algebra.TensorProduct.lift (toK a b) (ofK a b) fun x t => by
    rw [ofK_apply]; exact (QuaternionAlgebra.coe_commute t (toK a b x)).symm

theorem fwd_tmul (x : ℍ[R, a, b]) (t : K) :
    fwd a b (x ⊗ₜ t) = ⟨t * algebraMap R K x.re, t * algebraMap R K x.imI, t * algebraMap R K x.imJ, t * algebraMap R K x.imK⟩ := by
  rw [fwd, Algebra.TensorProduct.lift_tmul, toK_apply, ofK_apply, ← QuaternionAlgebra.coe_commutes, QuaternionAlgebra.coe_mul_eq_smul]
  ext <;> simp

def bwd (y : ℍ[K, a', b']) : ℍ[R, a, b] ⊗[R] K :=
  (1 : ℍ[R, a, b]) ⊗ₜ y.re + (⟨0, 1, 0, 0⟩ : ℍ[R, a, b]) ⊗ₜ y.imI + (⟨0, 0, 1, 0⟩ : ℍ[R, a, b]) ⊗ₜ y.imJ +
    (⟨0, 0, 0, 1⟩ : ℍ[R, a, b]) ⊗ₜ y.imK

theorem bwd_add (y z : ℍ[K, a', b']) : bwd a b (y + z) = bwd a b y + bwd a b z := by
  simp only [bwd]
  show (1 : ℍ[R, a, b]) ⊗ₜ[R] (y.re + z.re) + (⟨0, 1, 0, 0⟩ : ℍ[R, a, b]) ⊗ₜ[R] (y.imI + z.imI) +
      (⟨0, 0, 1, 0⟩ : ℍ[R, a, b]) ⊗ₜ[R] (y.imJ + z.imJ) + (⟨0, 0, 0, 1⟩ : ℍ[R, a, b]) ⊗ₜ[R] (y.imK + z.imK) = _
  simp only [TensorProduct.tmul_add]
  abel

theorem fwd_bwd (y : ℍ[K, a', b']) : fwd a b (bwd a b y) = y := by
  simp only [bwd, map_add, fwd_tmul]
  ext <;> simp

theorem bwd_fwd_tmul (x : ℍ[R, a, b]) (t : K) : bwd a b (fwd a b (x ⊗ₜ t)) = x ⊗ₜ t := by
  rw [fwd_tmul]
  simp only [bwd]

  have hx : x = x.re • (1 : ℍ[R, a, b]) + x.imI • (⟨0, 1, 0, 0⟩ : ℍ[R, a, b]) + x.imJ • (⟨0, 0, 1, 0⟩ : ℍ[R, a, b]) +
      x.imK • (⟨0, 0, 0, 1⟩ : ℍ[R, a, b]) := by
    ext <;> simp
  rw [mul_comm t, mul_comm t, mul_comm t, mul_comm t]
  conv_rhs => rw [hx]
  simp only [TensorProduct.add_tmul, TensorProduct.smul_tmul]
  simp only [Algebra.smul_def]

theorem bwd_fwd (z : ℍ[R, a, b] ⊗[R] K) : bwd a b (fwd a b z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [bwd]
  | tmul x t => exact bwd_fwd_tmul a b x t
  | add u w hu hw => rw [map_add, bwd_add, hu, hw]

def equiv : ℍ[R, a, b] ⊗[R] K ≃+* ℍ[K, a', b'] :=
  { toFun := fwd a b
    invFun := bwd a b
    left_inv := bwd_fwd a b
    right_inv := fwd_bwd a b
    map_mul' := map_mul (fwd a b)
    map_add' := map_add (fwd a b) }

end General

theorem main (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nonempty (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, (a : v.adicCompletion ℚ), (b : v.adicCompletion ℚ)]) := by
  have ha : algebraMap ℚ (v.adicCompletion ℚ) a = (a : v.adicCompletion ℚ) := eq_ratCast _ a
  have hb : algebraMap ℚ (v.adicCompletion ℚ) b = (b : v.adicCompletion ℚ) := eq_ratCast _ b
  have e := equiv (K := v.adicCompletion ℚ) a b
  rw [ha, hb] at e
  exact ⟨e⟩

end E1bChi

theorem solution
    (a b : ℚ) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Nonempty (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, (a : v.adicCompletion ℚ), (b : v.adicCompletion ℚ)]) :=
  E1bChi.main a b v

end S_QuaternionAlgebra_nonempty_tensorProduct_adicCompletion_ringEquiv
end P2MW
export P2MW.S_QuaternionAlgebra_nonempty_tensorProduct_adicCompletion_ringEquiv (solution)
