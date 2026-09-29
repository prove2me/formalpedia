-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/29d348eb-3da8-5761-9935-913dc57ef8ba

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ModuliPlace
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace RamMaxIdele

section Places

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

variable (q : ℕ) (hq : q.Prime)

theorem primesEquiv_place : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) (place q hq) = ⟨q, hq⟩ := by
  simp [place]

theorem natGenerator_place : Rat.HeightOneSpectrum.natGenerator (place q hq) = q :=
  congrArg Subtype.val (primesEquiv_place q hq)

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem q_mem_asIdeal : (q : 𝓞 ℚ) ∈ (place q hq).asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

theorem eq_place_of_mem (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : w = place q hq := by
  rw [natCast_mem_asIdeal_iff] at hw
  have : Rat.HeightOneSpectrum.natGenerator w = q :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).mp hw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [primesEquiv_place]
  exact Subtype.ext this

theorem q_notMem_asIdeal_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ place q hq) : (q : 𝓞 ℚ) ∉ w.asIdeal :=
  fun h => hw (eq_place_of_mem q hq w h)

theorem valuation_natCast_eq_one_of_notMem (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 hn

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

end Places

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem tmul_one_mem_localBox {z : D} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v :=
  tmul_mem_localBox Λ v hz (one_mem _)

theorem one_tmul_mul_mem_localBox {x : D ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v)
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ) :
    ((1 : D) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_mem_localBox Λ v hz (mul_mem hc hc')
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => exact (mul_neg _ x).symm ▸ neg_mem hx

omit Λ in
theorem ratCast_smul_eq_one_tmul_mul (r : ℚ) (x : D ⊗[ℚ] v.adicCompletion ℚ) :
    r • x = ((1 : D) ⊗ₜ[ℚ] (algebraMap ℚ (v.adicCompletion ℚ) r)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z c =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem ratCast_smul_mem_localBox {x : D ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (r : ℚ)
    (hr : v.valuation ℚ r ≤ 1) : r • x ∈ Submodule.localBox Λ v := by
  rw [ratCast_smul_eq_one_tmul_mul]
  refine one_tmul_mul_mem_localBox Λ v hx ?_
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
  exact hr

theorem mem_finiteAdeleBox_iff (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (x : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :
    x ∈ Submodule.finiteAdeleBox Λ ↔ ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Submodule.finiteAdeleEvalAt D w x ∈ Submodule.localBox Λ w :=
  Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hfg hspan x

theorem mem_iff_forall_tmul_one_mem_localBox (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) (z : D) :
    z ∈ Λ ↔ ∀ w : HeightOneSpectrum (𝓞 ℚ), z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  constructor
  · intro hz w; exact tmul_one_mem_localBox Λ w hz
  · intro h
    have hbox : z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ := by
      rw [mem_finiteAdeleBox_iff Λ hfg hspan]
      intro w
      rw [Submodule.finiteAdeleEvalAt_tmul]
      exact h w
    have : z ∈ Submodule.ofFiniteIdele Λ 1 := by
      rw [Submodule.mem_ofFiniteIdele_iff]
      exact ⟨_, hbox, by simp⟩
    rwa [Submodule.ofFiniteIdele_one Λ hfg hspan] at this

omit Λ in
theorem finiteAdeleEvalAt_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : D) :
    Submodule.finiteAdeleEvalAt D w (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) = z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Submodule.finiteAdeleEvalAt_tmul]; rfl

theorem mem_ofFiniteIdele_iff_forall (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (z : D) :
    z ∈ Submodule.ofFiniteIdele Λ g ↔
      ∀ w : HeightOneSpectrum (𝓞 ℚ), Submodule.finiteAdeleEvalAt D w
        ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) *
        (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ Submodule.localBox Λ w := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨t, ht, hgt⟩ w
    rw [AddMonoidHom.coe_mulLeft] at hgt
    have ht' : t = ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) *
        (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
      rw [← hgt, Units.inv_mul_cancel_left]
    have := (mem_finiteAdeleBox_iff Λ hfg hspan t).mp ht w
    rwa [ht', map_mul, finiteAdeleEvalAt_tmul_one] at this
  · intro h
    refine ⟨((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) *
      (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)), ?_, ?_⟩
    · rw [mem_finiteAdeleBox_iff Λ hfg hspan]
      intro w
      rw [map_mul, finiteAdeleEvalAt_tmul_one]
      exact h w
    · rw [AddMonoidHom.coe_mulLeft, Units.mul_inv_cancel_left]

abbrev unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (D ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
  Units.map (Submodule.finiteAdeleEvalAt D w).toRingHom.toMonoidHom g

omit Λ in
theorem coe_unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((unitAt w g : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) : D ⊗[ℚ] w.adicCompletion ℚ) =
      Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := rfl

omit Λ in
theorem unitAt_mul (w : HeightOneSpectrum (𝓞 ℚ)) (g h : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    unitAt w (g * h) = unitAt w g * unitAt w h :=
  map_mul _ _ _

omit Λ in
theorem unitAt_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    unitAt w g⁻¹ = (unitAt w g)⁻¹ :=
  map_inv _ _

omit Λ in
theorem coe_inv_unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((unitAt w g)⁻¹ : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) =
      Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        D ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  rw [← map_inv]; rfl

end Box

section Q

open QuaternionAlgebra

variable {K L : Type*} [CommRing K] [CommRing L]

def qmapEquiv (e : K ≃+* L) (α β : K) : ℍ[K, α, β] ≃+* ℍ[L, e α, e β] where
  toFun x := ⟨e x.re, e x.imI, e x.imJ, e x.imK⟩
  invFun y := ⟨e.symm y.re, e.symm y.imI, e.symm y.imJ, e.symm y.imK⟩
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp
  map_mul' x y := by
    obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
    ext <;> simp [map_add, map_sub, map_mul]
  map_add' x y := by ext <;> simp

theorem qmapEquiv_apply (e : K ≃+* L) (α β : K) (x : ℍ[K, α, β]) :
    qmapEquiv e α β x = ⟨e x.re, e x.imI, e x.imJ, e x.imK⟩ := rfl

theorem nrd_qmapEquiv (e : K ≃+* L) (α β : K) (x : ℍ[K, α, β]) :
    nrd (qmapEquiv e α β x) = e (nrd x) := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp [qmapEquiv_apply, nrd_mk, map_add, map_sub, map_mul, map_pow]

theorem nrd_mul' {α β : K} (x y : ℍ[K, α, β]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]; ring

theorem nrd_smul' {α β : K} (c : K) (x : ℍ[K, α, β]) : nrd (c • x) = c ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, nrd_mk, smul_eq_mul]; ring

end Q

namespace Tr

open Rat.HeightOneSpectrum QuaternionAlgebra

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "pv" => (primesEquiv (R := 𝓞 ℚ) v : ℕ)

scoped instance factPrime : Fact (Nat.Prime pv) := ⟨(primesEquiv (R := 𝓞 ℚ) v).2⟩

def eK : v.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[pv] := (adicCompletion.padicEquiv (R := 𝓞 ℚ) v).toAlgEquiv

theorem eK_mem_iff (x : v.adicCompletion ℚ) : ‖eK v x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers ℚ := by
  have hb := adicCompletion.padicEquiv_bijOn (R := 𝓞 ℚ) v
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := hb.surjOn (show eK v x ∈ PadicInt.subring pv from hx)
    have : y = x := (adicCompletion.padicEquiv (R := 𝓞 ℚ) v).injective hyx
    rw [← this]; exact hy
  · intro hx
    exact hb.mapsTo hx

theorem eK_algebraMap (r : ℚ) : eK v (algebraMap ℚ (v.adicCompletion ℚ) r) = (r : ℚ_[pv]) := by
  rw [AlgEquiv.commutes, eq_ratCast]

variable {a b : ℚ}
variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])
  (hφ : ∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re, algebraMap ℚ (v.adicCompletion ℚ) z.imI,
        algebraMap ℚ (v.adicCompletion ℚ) z.imJ, algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))

include hφ in
theorem φ_one_tmul (c : v.adicCompletion ℚ) :
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) =
      c • (1 : ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]) := by
  rw [hφ]; congr 1

include hφ in
theorem nrd_φ_tmul (z : ℍ[ℚ, a, b]) (c : v.adicCompletion ℚ) :
    nrd (φ (z ⊗ₜ[ℚ] c)) = c ^ 2 * algebraMap ℚ (v.adicCompletion ℚ) (nrd z) := by
  rw [hφ, nrd_smul']
  congr 1
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  simp only [nrd_mk, map_add, map_sub, map_mul, map_pow]

def Θ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
    ℍ[ℚ_[pv], eK v (algebraMap ℚ (v.adicCompletion ℚ) a), eK v (algebraMap ℚ (v.adicCompletion ℚ) b)] :=
  φ.trans (qmapEquiv (eK v).toRingEquiv (algebraMap ℚ (v.adicCompletion ℚ) a) (algebraMap ℚ (v.adicCompletion ℚ) b))

theorem nrd_Θ (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : nrd (Θ v φ x) = eK v (nrd (φ x)) := by
  show nrd (qmapEquiv (eK v).toRingEquiv _ _ (φ x)) = _
  rw [nrd_qmapEquiv]; rfl

include hφ in
theorem Θ_one_tmul (c : v.adicCompletion ℚ) :
    Θ v φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) =
      (eK v c) • (1 : ℍ[ℚ_[pv], eK v (algebraMap ℚ (v.adicCompletion ℚ) a), eK v (algebraMap ℚ (v.adicCompletion ℚ) b)]) := by
  show qmapEquiv (eK v).toRingEquiv _ _ (φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c)) = _
  rw [φ_one_tmul v φ hφ, qmapEquiv_apply]
  ext <;> simp

def N (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : ℝ := ‖nrd (Θ v φ x)‖

theorem N_mul (x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : N v φ (x * y) = N v φ x * N v φ y := by
  unfold N; rw [map_mul, nrd_mul', norm_mul]

theorem N_one : N v φ 1 = 1 := by
  unfold N; rw [map_one, nrd_one, norm_one]

theorem N_val_mul_N_inv (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    N v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * N v φ ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = 1 := by
  rw [← N_mul, Units.mul_inv, N_one]

theorem N_unit_ne_zero (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    N v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ≠ 0 := by
  intro h; have := N_val_mul_N_inv v φ u; rw [h, zero_mul] at this; exact zero_ne_one this

theorem N_inv (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    N v φ ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = (N v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))⁻¹ :=
  eq_inv_of_mul_eq_one_right (N_val_mul_N_inv v φ u)

theorem N_nonneg (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : 0 ≤ N v φ x := norm_nonneg _

include hφ in
theorem N_one_tmul (c : v.adicCompletion ℚ) : N v φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = ‖eK v c‖ ^ 2 := by
  unfold N; rw [Θ_one_tmul v φ hφ, nrd_smul', nrd_one, mul_one, norm_pow]

include hφ in
theorem N_ratCast_smul (r : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    N v φ (r • x) = ‖(r : ℚ_[pv])‖ ^ 2 * N v φ x := by
  rw [ratCast_smul_eq_one_tmul_mul, N_mul, N_one_tmul v φ hφ, eK_algebraMap]

include hφ in
theorem N_tmul_one (z : ℍ[ℚ, a, b]) : N v φ (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = ‖((nrd z : ℚ) : ℚ_[pv])‖ := by
  unfold N; rw [nrd_Θ, nrd_φ_tmul v φ hφ, one_pow, one_mul, eK_algebraMap]

theorem norm_eq_inv_of_lt_of_lt (p : ℕ) [Fact p.Prime] (t : ℚ_[p]) (ht : t ≠ 0)
    (h1 : ((p : ℝ) ^ (2 : ℕ))⁻¹ < ‖t‖) (h2 : ‖t‖ < 1) : ‖t‖ = (p : ℝ)⁻¹ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  rw [Padic.norm_eq_zpow_neg_valuation ht] at h1 h2 ⊢
  rw [show (1 : ℝ) = (p : ℝ) ^ (0 : ℤ) from (zpow_zero _).symm, zpow_lt_zpow_iff_right₀ hp] at h2
  rw [show ((p : ℝ) ^ (2 : ℕ))⁻¹ = (p : ℝ) ^ (-2 : ℤ) by rw [zpow_neg, zpow_ofNat], zpow_lt_zpow_iff_right₀ hp] at h1
  have : -t.valuation = -1 := by omega
  rw [this, zpow_neg_one]

theorem mem_localBoxUnits_iff_N (S : Submodule ℤ ℍ[ℚ, a, b])
    (hSv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ∈ Submodule.localBox S v ↔ N v φ x ≤ 1)
    (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    u ∈ Submodule.localBoxUnits S v ↔ N v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = 1 := by
  rw [Submodule.mem_localBoxUnits_iff, SetLike.mem_coe, SetLike.mem_coe, hSv, hSv, N_inv]
  have hpos : 0 < N v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
    lt_of_le_of_ne (N_nonneg v φ _) (N_unit_ne_zero v φ u).symm
  constructor
  · rintro ⟨h1, h2⟩
    have := (inv_le_one₀ hpos).mp h2
    linarith
  · intro h; rw [h, inv_one]; exact ⟨le_rfl, le_rfl⟩

end Tr
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one.RamMaxIdele.Tr"

section Main

open QuaternionAlgebra Tr Rat.HeightOneSpectrum

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem nrd_eq_zero_iff {a b : ℚ} (ha : a < 0) (hb : b < 0) (h : ℍ[ℚ, a, b]) : nrd h = 0 ↔ h = 0 := by
  constructor
  · intro h0
    obtain ⟨h₀, h₁, h₂, h₃⟩ := h
    simp only [nrd_mk] at h0
    have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
    have hnn1 : 0 ≤ -a * h₁ ^ 2 := mul_nonneg (neg_nonneg.mpr ha.le) (sq_nonneg _)
    have hnn2 : 0 ≤ -b * h₂ ^ 2 := mul_nonneg (neg_nonneg.mpr hb.le) (sq_nonneg _)
    have hnn3 : 0 ≤ a * b * h₃ ^ 2 := mul_nonneg hab.le (sq_nonneg _)
    have e0 : h₀ ^ 2 = 0 := by linarith [sq_nonneg h₀]
    have e1 : -a * h₁ ^ 2 = 0 := by linarith [sq_nonneg h₀]
    have e2 : -b * h₂ ^ 2 = 0 := by linarith [sq_nonneg h₀]
    have e3 : a * b * h₃ ^ 2 = 0 := by linarith [sq_nonneg h₀]
    have f0 : h₀ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp e0
    have f1 : h₁ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp e1).resolve_left (by linarith))
    have f2 : h₂ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp e2).resolve_left (by linarith))
    have f3 : h₃ = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp e3).resolve_left hab.ne')
    ext <;> simp [f0, f1, f2, f3]
  · rintro rfl; exact nrd_zero

theorem main {a b : ℚ} (q' : ℕ) (hq' : q'.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    (hm : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m))
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m)
    (π : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (hπ : π ∈ primeHeckeSet R q')
    (hπv : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (π : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1) :
    (∀ h : ℍ[ℚ, a, b], h ∈ Submodule.ofFiniteIdele Λ₁ π ↔
      h ∈ Λ₁ ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h))) ∧
    (∀ x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ,
      Submodule.ofFiniteIdele Λ₁ (x * π * m) = Submodule.ofFiniteIdele Λ₁ (x * m * π)) := by

  set v : HeightOneSpectrum (𝓞 ℚ) := place q' hq' with hvdef
  have hpv : (primesEquiv (R := 𝓞 ℚ) v : ℕ) = q' := natGenerator_place q' hq'
  haveI : Fact (Nat.Prime (primesEquiv (R := 𝓞 ℚ) v : ℕ)) := ⟨(primesEquiv (R := 𝓞 ℚ) v).2⟩
  have hqv : ((q' : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := q_mem_asIdeal q' hq'
  have hnotMem_of : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal :=
    fun w hw => q_notMem_asIdeal_of_ne q' hq' w hw
  set K := v.adicCompletion ℚ with hKdef
  set P : ℝ := ((primesEquiv (R := 𝓞 ℚ) v : ℕ) : ℝ) with hPdef
  have hP1 : (1 : ℝ) < P := by
    rw [hPdef]; exact_mod_cast (Fact.out : Nat.Prime (primesEquiv (R := 𝓞 ℚ) v : ℕ)).one_lt
  have hP0 : (0 : ℝ) < P := by linarith
  have hPne : P ≠ 0 := hP0.ne'
  have hq0 : (q' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq'.ne_zero

  have hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] K, x ≠ 0 → IsUnit x := (hdef.2.2 v).mpr hqv

  have hΛo : IsOrder Λ₁ := hΛ₁.isOrder
  have hMo : IsOrder (Submodule.conjByFiniteIdele Λ₁ m) := hm.isOrder
  have hRo : IsOrder R := by rw [hR]; exact hΛo.inf hMo

  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b) (d₁ := algebraMap ℚ K a) (d₂ := (0 : K))
    (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl
    (AlgEquiv.refl : ℍ[K, algebraMap ℚ K a, algebraMap ℚ K b] ≃ₐ[K] ℍ[K, algebraMap ℚ K a, algebraMap ℚ K b])
  have hφ' : ∀ (z : ℍ[ℚ, a, b]) (r : K),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ K z.re, algebraMap ℚ K z.imI, algebraMap ℚ K z.imJ, algebraMap ℚ K z.imK⟩ :
        ℍ[K, algebraMap ℚ K a, algebraMap ℚ K b]) := by
    intro z r; rw [hφ]; rfl

  have hΛv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] K, x ∈ Submodule.localBox Λ₁ v ↔ N v φ x ≤ 1 := by
    intro x
    rw [QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit hΛ₁ v hdiv
        φ hφ' x, ← eK_mem_iff, ← nrd_Θ]
    rfl

  have hRv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] K, x ∈ Submodule.localBox R v ↔ N v φ x ≤ 1 := by
    intro x
    rw [hR, Submodule.localBox_inf Λ₁ _ hΛo.fg hΛo.spanTop hMo.fg hMo.spanTop v,
      ← QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit v hdiv hΛ₁ hm, inf_idem]
    exact hΛv x

  have mem_boxR : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f, x ∈ Submodule.finiteAdeleBox R ↔
      ∀ w, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x ∈ Submodule.localBox R w :=
    fun x => mem_finiteAdeleBox_iff R hRo.fg hRo.spanTop x
  have mem_boxΛ : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f, x ∈ Submodule.finiteAdeleBox Λ₁ ↔
      ∀ w, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x ∈ Submodule.localBox Λ₁ w :=
    fun x => mem_finiteAdeleBox_iff Λ₁ hΛo.fg hΛo.spanTop x
  have mem_U : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ, u ∈ Submodule.finiteIdeleStabilizer Λ₁ ↔
      ∀ w, unitAt w u ∈ Submodule.localBoxUnits Λ₁ w :=
    fun u => QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ₁ hΛo u
  have ev_val : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
        ((unitAt w x : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : _) :=
    fun w x => rfl
  have ev_inv : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
        (((unitAt w x)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : _) :=
    fun w x => (coe_inv_unitAt w x).symm
  have unit_v : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ, u ∈ Submodule.localBoxUnits Λ₁ v ↔ N v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] K) = 1 :=
    fun u => mem_localBoxUnits_iff_N v φ Λ₁ hΛv u

  have hq_w : ∀ w, w ≠ v → w.valuation ℚ ((q' : ℚ)⁻¹) ≤ 1 := by
    intro w hw
    rw [map_inv₀, valuation_natCast_eq_one_of_notMem w q' (hnotMem_of w hw), inv_one]
  have ev_smul : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (r • x) = r • Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x :=
    fun w r x => map_smul _ r x
  have normqi : ‖(((q' : ℚ)⁻¹ : ℚ) : ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)])‖ = P := by
    have hcast : ((q' : ℕ) : ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)]) =
        ((primesEquiv (R := 𝓞 ℚ) v : ℕ) : ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)]) :=
      congrArg (Nat.cast : ℕ → ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)]) hpv.symm
    rw [Rat.cast_inv, norm_inv, Rat.cast_natCast, hcast, Padic.norm_p, inv_inv]

  have hπw1 : ∀ w, w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (π : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 :=
    fun w hw => hπv w (hnotMem_of w hw)
  have hπunit_w : ∀ w, w ≠ v → unitAt w π = 1 := fun w hw => Units.ext (hπw1 w hw)
  have h1R : ∀ w : HeightOneSpectrum (𝓞 ℚ), (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox R w :=
    fun w => tmul_one_mem_localBox R w hRo.one_mem
  have h1Λ : ∀ w : HeightOneSpectrum (𝓞 ℚ), (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox Λ₁ w :=
    fun w => tmul_one_mem_localBox Λ₁ w hΛo.one_mem
  have hNπ : N v φ ((unitAt v π : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) = P⁻¹ := by
    have hπ' := hπ
    rw [QuaternionAlgebra.mem_primeHeckeSet_iff] at hπ'
    obtain ⟨-, -, h3, h4⟩ := hπ'
    rw [mem_boxR] at h3 h4
    have Nh_pos : 0 < N v φ ((unitAt v π : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) :=
      lt_of_le_of_ne (N_nonneg v φ _) (N_unit_ne_zero v φ _).symm

    have hv3 : ¬ N v φ (((unitAt v π)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) ≤ 1 := by
      intro hle; apply h3; intro w
      by_cases hw' : w = v
      · subst hw'; rw [ev_inv, hRv]; exact hle
      · rw [ev_inv, hπunit_w w hw', inv_one, Units.val_one]; exact h1R w

    have hv4 : ¬ N v φ ((q' : ℚ)⁻¹ • ((unitAt v π : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K)) ≤ 1 := by
      intro hle; apply h4; intro w
      by_cases hw' : w = v
      · subst hw'; rw [ev_smul, ev_val, hRv]; exact hle
      · rw [ev_smul, hπw1 w hw']; exact ratCast_smul_mem_localBox R w (h1R w) _ (hq_w w hw')
    rw [N_inv, not_le] at hv3
    rw [N_ratCast_smul v φ hφ', normqi, not_le] at hv4
    have hlt1 : N v φ ((unitAt v π : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) < 1 :=
      (one_lt_inv₀ Nh_pos).mp hv3
    have hgt : (P ^ (2 : ℕ))⁻¹ < N v φ ((unitAt v π : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) :=
      (inv_lt_iff_one_lt_mul₀' (by positivity)).mpr hv4
    have hne : nrd (Θ v φ ((unitAt v π : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K)) ≠ 0 := by
      intro h0; apply (N_unit_ne_zero v φ (unitAt v π)); unfold N; rw [h0, norm_zero]
    exact norm_eq_inv_of_lt_of_lt _ _ hne hgt hlt1
  refine ⟨?_, ?_⟩

  · intro h
    have step1 := mem_ofFiniteIdele_iff_forall Λ₁ hΛo.fg hΛo.spanTop π h
    have hΛ_iff := mem_iff_forall_tmul_one_mem_localBox Λ₁ hΛo.fg hΛo.spanTop h

    have hNh : N v φ (h ⊗ₜ[ℚ] (1 : K)) = ‖((nrd h : ℚ) : ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)])‖ := N_tmul_one v φ hφ' h
    have hdef0 : nrd h = 0 ↔ h = 0 := nrd_eq_zero_iff hdef.1 hdef.2.1 h

    have step2 : N v φ ((((unitAt v π)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) * (h ⊗ₜ[ℚ] (1 : K))) ≤ 1 ↔
        (h = 0 ∨ 1 ≤ padicValRat q' (nrd h)) := by
      rw [N_mul, N_inv, hNπ, inv_inv, hNh]
      by_cases h0 : h = 0
      · simp [h0, nrd_zero]
      · have hn0 : nrd h ≠ 0 := fun e => h0 (hdef0.mp e)
        have hval : ‖((nrd h : ℚ) : ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)])‖ = P ^ (-padicValRat q' (nrd h)) := by
          rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero hn0, hPdef]
          push_cast
          rw [hpv]
        rw [hval, or_iff_right h0,
          show P * P ^ (-padicValRat q' (nrd h)) = P ^ (1 - padicValRat q' (nrd h)) by
            rw [sub_eq_add_neg, zpow_add₀ hPne, zpow_one],
          show (1 : ℝ) = P ^ (0 : ℤ) from (zpow_zero P).symm, zpow_le_zpow_iff_right₀ hP1]
        omega
    rw [step1, hΛ_iff, ← step2]
    constructor
    · intro hall
      have hv' := hall v
      rw [ev_inv, hΛv] at hv'
      refine ⟨fun w => ?_, hv'⟩
      by_cases hw : w = v
      · subst hw
        rw [hΛv]
        have hle : N v φ (h ⊗ₜ[ℚ] (1 : K)) ≤
            N v φ ((((unitAt v π)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) * (h ⊗ₜ[ℚ] (1 : K))) := by
          rw [N_mul, N_inv, hNπ, inv_inv]
          exact le_mul_of_one_le_left (N_nonneg v φ _) hP1.le
        exact hle.trans hv'
      · have := hall w
        rwa [ev_inv, hπunit_w w hw, inv_one, Units.val_one, one_mul] at this
    · rintro ⟨hall, hv'⟩ w
      rw [ev_inv]
      by_cases hw : w = v
      · subst hw; rw [hΛv]; exact hv'
      · rw [hπunit_w w hw, inv_one, Units.val_one, one_mul]; exact hall w

  · intro x
    rw [Submodule.ofFiniteIdele_eq_ofFiniteIdele_iff Λ₁ hΛo.fg hΛo.spanTop]
    have hgrp : (x * π * m)⁻¹ * (x * m * π) = m⁻¹ * π⁻¹ * m * π := by group
    rw [hgrp, mem_U]
    intro w
    rw [unitAt_mul, unitAt_mul, unitAt_mul, unitAt_inv, unitAt_inv]
    by_cases hw : w = v
    · subst hw
      have hm0 := N_unit_ne_zero v φ (unitAt v m)
      have hp0 := N_unit_ne_zero v φ (unitAt v π)
      rw [unit_v, Units.val_mul, Units.val_mul, Units.val_mul, N_mul, N_mul, N_mul, N_inv, N_inv,
        show (N v φ ((unitAt v m : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K))⁻¹ *
            (N v φ ((unitAt v π : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K))⁻¹ *
            N v φ ((unitAt v m : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) *
            N v φ ((unitAt v π : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) =
          ((N v φ ((unitAt v m : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K))⁻¹ *
            N v φ ((unitAt v m : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K)) *
          ((N v φ ((unitAt v π : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K))⁻¹ *
            N v φ ((unitAt v π : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K)) by ring,
        inv_mul_cancel₀ hm0, inv_mul_cancel₀ hp0, one_mul]
    · rw [hπunit_w w hw, inv_one, mul_one, mul_one, inv_mul_cancel, Submodule.mem_localBoxUnits_iff, inv_one,
        Units.val_one]
      exact ⟨h1Λ w, h1Λ w⟩

end Main
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one.RamMaxIdele.Tr"

end RamMaxIdele
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one.RamMaxIdele.Tr P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one.RamMaxIdele"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one.RamMaxIdele.Tr P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one.RamMaxIdele"

open QuaternionAlgebra CerednikDrinfeld ModularCurve AlgebraicCurve in
theorem solution
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ₁ : IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hm : IsMaximalOrder (Submodule.conjByFiniteIdele Λ₁ m))
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : R = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m)
    (hRN : R.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (π : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hπ : π ∈ primeHeckeSet R q')
    (hπv : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
        (π : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) :
    (∀ h : ℍ[ℚ, a, b], h ∈ Submodule.ofFiniteIdele Λ₁ π ↔
      h ∈ Λ₁ ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h))) ∧
    (∀ x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      Submodule.ofFiniteIdele Λ₁ (x * π * m) = Submodule.ofFiniteIdele Λ₁ (x * m * π)) :=
  RamMaxIdele.main q' Fact.out hdef Λ₁ hΛ₁ m hm R hR π hπ hπv

end S_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_mem_ofFiniteIdele_iff_and_ofFiniteIdele_mul_mul_eq_of_mem_primeHeckeSet_of_finiteAdeleEvalAt_eq_one (solution)
