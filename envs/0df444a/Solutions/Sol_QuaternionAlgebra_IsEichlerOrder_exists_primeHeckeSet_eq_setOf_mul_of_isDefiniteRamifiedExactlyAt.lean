-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9d0f48f2-9f35-5b73-bb81-554ca9fca8b8

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_Padic_exists_ternary_isotropic_of_norm_eq_one_of_ne_two
import Theorems.Thm_Padic_exists_ternary_isotropic_iff_of_norm_eq_one_two
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt
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

namespace RamHecke

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

theorem algebraMap_natCast (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ) = (n : w.adicCompletion ℚ) := map_natCast _ n

theorem natCast_valuation_le_one (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) : w.valuation ℚ (n : ℚ) ≤ 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one w _

theorem natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← algebraMap_natCast, valued_algebraMap]
  exact natCast_valuation_le_one w n

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

theorem mul_mem_localBox (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    {x y : D ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  induction hy using AddSubgroup.closure_induction with
  | mem y' hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox Λ v (hmul _ _ hz' hz) (mul_mem hc' hc)
    | zero => rw [zero_mul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | neg x _ hx => exact (neg_mul x _).symm ▸ neg_mem hx
  | zero => rw [mul_zero]; exact zero_mem _
  | add x' y' _ _ hx' hy' => rw [mul_add]; exact add_mem hx' hy'
  | neg x' _ hx' => exact (mul_neg _ x').symm ▸ neg_mem hx'

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

theorem eq_zero_of_nrd_eq_zero {F : Type*} [Field F] {α β : F} (hdiv : ∀ x : ℍ[F, α, β], x ≠ 0 → IsUnit x)
    (x : ℍ[F, α, β]) (hx : nrd x = 0) : x = 0 := by
  by_contra h
  obtain ⟨u, rfl⟩ := hdiv x h
  have h1 : (u : ℍ[F, α, β]) * star (u : ℍ[F, α, β]) = 0 := by
    rw [mul_star_eq_coe_nrd, hx, QuaternionAlgebra.coe_zero]
  have h2 : star (u : ℍ[F, α, β]) = 0 := by
    have := congrArg (fun y => ((u⁻¹ : (ℍ[F, α, β])ˣ) : ℍ[F, α, β]) * y) h1
    simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] using this
  exact h (star_eq_zero.mp h2)

end Q

namespace RamTransport

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

include φ in

theorem hdiv_padic (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) :
    ∀ y : ℍ[ℚ_[pv], eK v (algebraMap ℚ (v.adicCompletion ℚ) a), eK v (algebraMap ℚ (v.adicCompletion ℚ) b)],
      y ≠ 0 → IsUnit y := by
  intro y hy
  have h0 : (Θ v φ).symm y ≠ 0 := by
    intro h; apply hy; rw [← (Θ v φ).apply_symm_apply y, h, map_zero]
  obtain ⟨u, hu⟩ := hdiv _ h0
  refine ⟨Units.map (Θ v φ).toRingHom.toMonoidHom u, ?_⟩
  rw [Units.coe_map, hu]
  exact (Θ v φ).apply_symm_apply y

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

theorem N_conj (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    N v φ ((u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * x * ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _)) =
      N v φ x := by
  rw [N_mul, N_mul, mul_comm (N v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)), mul_assoc, N_val_mul_N_inv, mul_one]

theorem N_unit_eq_zpow (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    ∃ n : ℤ, N v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = ((pv : ℕ) : ℝ) ^ n := by
  have hne : nrd (Θ v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) ≠ 0 := by
    intro h; apply N_unit_ne_zero v φ u; unfold N; rw [h, norm_zero]
  exact ⟨_, Padic.norm_eq_zpow_neg_valuation hne⟩

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

end RamTransport
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt.RamHecke.RamTransport"

namespace RamUnif

open QuaternionAlgebra

theorem exists_zpow_norm (p : ℕ) [Fact p.Prime] (α : ℚ_[p]) (hα : α ≠ 0) :
    ∃ m : ℤ, ‖α * (p : ℚ_[p]) ^ (-(2 * m))‖ = 1 ∨ ‖α * (p : ℚ_[p]) ^ (-(2 * m))‖ = (p : ℝ)⁻¹ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set n := α.valuation with hn
  refine ⟨n / 2, ?_⟩
  rw [norm_mul, Padic.norm_p_zpow, Padic.norm_eq_zpow_neg_valuation hα, ← zpow_add₀ hp0.ne', neg_neg]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    have : -α.valuation + 2 * (n / 2) = 0 := by omega
    rw [this, zpow_zero]
  · right
    have : -α.valuation + 2 * (n / 2) = -1 := by omega
    rw [this, zpow_neg_one]

theorem nrd_mk' {K : Type*} [CommRing K] {a b : K} (x₀ x₁ x₂ x₃ : K) :
    nrd (⟨x₀, x₁, x₂, x₃⟩ : ℍ[K, a, b]) = x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 := by
  simp [nrd_mk]

theorem norm_sub_one_lt_one_two (α : ℚ_[2]) (hα : ‖α‖ = 1) : ‖α - 1‖ < 1 := by
  set z : ℤ_[2] := ⟨α, le_of_eq hα⟩ with hz
  have hzu : IsUnit z := PadicInt.isUnit_iff.mpr hα
  have h1 : PadicInt.toZMod z = 1 := by
    obtain ⟨u, hu⟩ := hzu.map PadicInt.toZMod
    have : ∀ w : (ZMod 2)ˣ, (w : ZMod 2) = 1 := by decide
    rw [← hu, this]
  have hmem : z - 1 ∈ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [RingHom.mem_ker, map_sub, map_one, h1, sub_self]
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hmem
  simp [hz] at hmem
  exact hmem

theorem exists_norm_nrd_eq_inv (p : ℕ) [Fact p.Prime] (α β : ℚ_[p])
    (han : ∀ x₀ x₁ x₂ x₃ : ℚ_[p], x₀ ^ 2 - α * x₁ ^ 2 - β * x₂ ^ 2 + α * β * x₃ ^ 2 = 0 →
      x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) :
    ∃ y : ℍ[ℚ_[p], α, β], ‖nrd y‖ = (p : ℝ)⁻¹ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpQ : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hα : α ≠ 0 := by
    intro h; have := (han 0 1 0 0 (by rw [h]; ring)).2.1; exact one_ne_zero this
  have hβ : β ≠ 0 := by
    intro h; have := (han 0 0 1 0 (by rw [h]; ring)).2.2.1; exact one_ne_zero this
  obtain ⟨m, hm⟩ := exists_zpow_norm p α hα
  obtain ⟨n, hn⟩ := exists_zpow_norm p β hβ
  set s : ℚ_[p] := (p : ℚ_[p]) ^ (-m) with hs
  set t : ℚ_[p] := (p : ℚ_[p]) ^ (-n) with ht
  have hs0 : s ≠ 0 := zpow_ne_zero _ hpQ
  have ht0 : t ≠ 0 := zpow_ne_zero _ hpQ
  have hs2 : s ^ 2 = (p : ℚ_[p]) ^ (-(2 * m)) := by
    rw [hs, ← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have ht2 : t ^ 2 = (p : ℚ_[p]) ^ (-(2 * n)) := by
    rw [ht, ← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  set α₁ := α * (p : ℚ_[p]) ^ (-(2 * m)) with hα₁
  set β₁ := β * (p : ℚ_[p]) ^ (-(2 * n)) with hβ₁

  have nrd_i : nrd (⟨0, s, 0, 0⟩ : ℍ[ℚ_[p], α, β]) = -α₁ := by
    rw [nrd_mk', hα₁, ← hs2]; ring
  have nrd_j : nrd (⟨0, 0, t, 0⟩ : ℍ[ℚ_[p], α, β]) = -β₁ := by
    rw [nrd_mk', hβ₁, ← ht2]; ring
  rcases hm with hm | hm
  swap
  · exact ⟨⟨0, s, 0, 0⟩, by rw [nrd_i, norm_neg, hm]⟩
  rcases hn with hn | hn
  swap
  · exact ⟨⟨0, 0, t, 0⟩, by rw [nrd_j, norm_neg, hn]⟩

  have noiso : ¬ ∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - α₁ * x ^ 2 - β₁ * y ^ 2 = 0 := by
    rintro ⟨z, x, y, hne, hzero⟩
    have hq : z ^ 2 - α * (x * s) ^ 2 - β * (y * t) ^ 2 + α * β * (0 : ℚ_[p]) ^ 2 =
        z ^ 2 - α₁ * x ^ 2 - β₁ * y ^ 2 := by
      rw [hα₁, hβ₁, ← hs2, ← ht2]; ring
    have h := han z (x * s) (y * t) 0 (by rw [hq, hzero])
    exact hne ⟨h.1, (mul_eq_zero.mp h.2.1).resolve_right hs0, (mul_eq_zero.mp h.2.2.1).resolve_right ht0⟩
  by_cases hp2 : p = 2
  · subst hp2
    have hiff := Padic.exists_ternary_isotropic_iff_of_norm_eq_one_two α₁ β₁ hm hn
    have hnot : ¬ (‖α₁ - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ)) := fun h => noiso (hiff.mpr (Or.inl h))

    refine ⟨⟨1, s, 0, 0⟩, ?_⟩
    have hval : nrd (⟨1, s, 0, 0⟩ : ℍ[ℚ_[2], α, β]) = -(α₁ - 1) := by
      rw [nrd_mk', hα₁, ← hs2]; ring
    rw [hval, norm_neg]
    have hlt : ‖α₁ - 1‖ < 1 := norm_sub_one_lt_one_two α₁ hm
    have hne : α₁ - 1 ≠ 0 := by
      intro h; apply hnot; rw [h, norm_zero]; positivity
    rw [Padic.norm_eq_zpow_neg_valuation hne] at hlt hnot ⊢
    push_cast at hlt hnot ⊢
    have h2 : (1 : ℝ) < 2 := by norm_num
    rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) from (zpow_zero _).symm, zpow_lt_zpow_iff_right₀ h2] at hlt
    rw [not_le, zpow_lt_zpow_iff_right₀ h2] at hnot
    have : -(α₁ - 1).valuation = -1 := by omega
    rw [this, zpow_neg_one]
  · exact absurd (Padic.exists_ternary_isotropic_of_norm_eq_one_of_ne_two p hp2 α₁ β₁ hm hn) noiso

end RamUnif
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt.RamHecke.RamTransport"

section Frame

open QuaternionAlgebra RamTransport Rat.HeightOneSpectrum

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])
  (hφ : ∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re, algebraMap ℚ (v.adicCompletion ℚ) z.imI,
        algebraMap ℚ (v.adicCompletion ℚ) z.imJ, algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))
  (hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x)
  (S : Submodule ℤ ℍ[ℚ, a, b])
  (hSv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ∈ Submodule.localBox S v ↔ N v φ x ≤ 1)

include hdiv in

theorem exists_uniformiser :
    ∃ ϖ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
      N v φ (ϖ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = ((primesEquiv (R := 𝓞 ℚ) v : ℕ) : ℝ)⁻¹ := by
  have hdiv' := hdiv_padic v φ hdiv
  have han : ∀ x₀ x₁ x₂ x₃ : ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)],
      x₀ ^ 2 - eK v (algebraMap ℚ (v.adicCompletion ℚ) a) * x₁ ^ 2 - eK v (algebraMap ℚ (v.adicCompletion ℚ) b) * x₂ ^ 2 +
        eK v (algebraMap ℚ (v.adicCompletion ℚ) a) * eK v (algebraMap ℚ (v.adicCompletion ℚ) b) * x₃ ^ 2 = 0 →
      x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
    intro x₀ x₁ x₂ x₃ h
    have := eq_zero_of_nrd_eq_zero hdiv' ⟨x₀, x₁, x₂, x₃⟩ (by rw [RamUnif.nrd_mk']; exact h)
    exact ⟨congrArg QuaternionAlgebra.re this, congrArg QuaternionAlgebra.imI this,
      congrArg QuaternionAlgebra.imJ this, congrArg QuaternionAlgebra.imK this⟩
  obtain ⟨y, hy⟩ := RamUnif.exists_norm_nrd_eq_inv (primesEquiv (R := 𝓞 ℚ) v : ℕ) _ _ han
  have hy0 : (Θ v φ).symm y ≠ 0 := by
    intro h
    have : y = 0 := by rw [← (Θ v φ).apply_symm_apply y, h, map_zero]
    rw [this, nrd_zero, norm_zero] at hy
    exact (inv_ne_zero (by exact_mod_cast (Fact.out : Nat.Prime (primesEquiv (R := 𝓞 ℚ) v : ℕ)).ne_zero)) hy.symm
  obtain ⟨ϖ, hϖ⟩ := hdiv _ hy0
  refine ⟨ϖ, ?_⟩
  unfold N; rw [hϖ, (Θ v φ).apply_symm_apply, hy]

include hSv in

theorem mem_localBoxUnits_iff_N (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    u ∈ Submodule.localBoxUnits S v ↔ N v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = 1 := by
  rw [Submodule.mem_localBoxUnits_iff, SetLike.mem_coe, SetLike.mem_coe, hSv, hSv, N_inv]
  have hpos : 0 < N v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
    lt_of_le_of_ne (N_nonneg v φ _) (N_unit_ne_zero v φ u).symm
  constructor
  · rintro ⟨h1, h2⟩
    have := (inv_le_one₀ hpos).mp h2
    linarith
  · intro h; rw [h, inv_one]; exact ⟨le_rfl, le_rfl⟩

end Frame
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt.RamHecke.RamTransport"

section Coset

open QuaternionAlgebra CerednikDrinfeld

variable {a b : ℚ}

theorem natCard_heckeIncidence_coset
    (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (T : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hT : T = {h | ∃ u ∈ U, h = π * u})
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (y : ClassSet U) [Decidable (ClassSet.mk U (x * π) = y)] :
    (Nat.card (HeckeIncidence U T x y) : ℤ) = if ClassSet.mk U (x * π) = y then 1 else 0 := by
  have key : ∀ c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U,
      (∃ h ∈ T, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = c ∧ ClassSet.mk U (x * h) = y) ↔
        (c = (π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) ∧ ClassSet.mk U (x * π) = y) := by
    intro c
    constructor
    · rintro ⟨h, hh, hc, hy⟩
      rw [hT] at hh
      obtain ⟨u, hu, rfl⟩ := hh
      refine ⟨?_, ?_⟩
      · rw [← hc]; symm
        exact QuotientGroup.eq.mpr (by rwa [inv_mul_cancel_left])
      · rw [← hy, ← mul_assoc, ClassSet.mk_mul_of_mem _ _ hu]
    · rintro ⟨rfl, hy⟩
      exact ⟨π, by rw [hT]; exact ⟨1, one_mem _, (mul_one π).symm⟩, rfl, hy⟩
  unfold HeckeIncidence
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  split_ifs with hP
  · haveI : Nonempty {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U //
        c = (π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) ∧ ClassSet.mk U (x * π) = y} := ⟨⟨_, rfl, hP⟩⟩
    haveI : Subsingleton {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U //
        c = (π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) ∧ ClassSet.mk U (x * π) = y} :=
      ⟨fun c d => Subtype.ext (c.2.1.trans d.2.1.symm)⟩
    rw [Nat.card_unique, Nat.cast_one]
  · haveI : IsEmpty {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U //
        c = (π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) ∧ ClassSet.mk U (x * π) = y} :=
      ⟨fun c => hP c.2.2⟩
    rw [Nat.card_of_isEmpty, Nat.cast_zero]

theorem classSetHeckeMatrix_coset
    (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (T : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hT : T = {h | ∃ u ∈ U, h = π * u})
    [DecidableEq (ClassSet U)] :
    classSetHeckeMatrix U T = Matrix.of (fun i j : ClassSet U => if classSetShift U π j = i then (1 : ℤ) else 0) := by
  ext i j
  simp only [classSetHeckeMatrix, Matrix.of_apply, heckeKernel, classSetShift]
  exact natCard_heckeIncidence_coset U π T hT j.out i

end Coset
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt.RamHecke.RamTransport"

section Main

open QuaternionAlgebra CerednikDrinfeld RamTransport Rat.HeightOneSpectrum

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem main {a b : ℚ} {q' : ℕ} (hq' : q'.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {S : Submodule ℤ ℍ[ℚ, a, b]} {Nl : ℕ} (hS : IsEichlerOrder S Nl)
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer S))] :
    ∃ π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      π ∈ primeHeckeSet S q' ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (π : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      (∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
        u ∈ Submodule.finiteIdeleStabilizer S ↔ π * u * π⁻¹ ∈ Submodule.finiteIdeleStabilizer S) ∧
      (∃ u ∈ Submodule.finiteIdeleStabilizer S,
        π * π = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) (Nat.cast_ne_zero.mpr hq'.ne_zero))) * u) ∧
      primeHeckeSet S q' = {h | ∃ u ∈ Submodule.finiteIdeleStabilizer S, h = π * u} ∧
      classSetHeckeMatrix (Submodule.finiteIdeleStabilizer S) (primeHeckeSet S q') =
        Matrix.of (fun i j : ClassSet (Submodule.finiteIdeleStabilizer S) =>
          if classSetShift (Submodule.finiteIdeleStabilizer S) π j = i then (1 : ℤ) else 0) ∧
      (∀ h : ℍ[ℚ, a, b], h ∈ Submodule.ofFiniteIdele S π ↔
        h ∈ S ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h))) := by

  set v : HeightOneSpectrum (𝓞 ℚ) := place q' hq' with hvdef
  have hpv : (primesEquiv (R := 𝓞 ℚ) v : ℕ) = q' := natGenerator_place q' hq'
  haveI : Fact (Nat.Prime (primesEquiv (R := 𝓞 ℚ) v : ℕ)) := ⟨(primesEquiv (R := 𝓞 ℚ) v).2⟩
  have hqv : ((q' : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := q_mem_asIdeal q' hq'
  have hne_of : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → w ≠ v :=
    fun w hw h => hw (h ▸ hqv)
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

  have hSo : IsOrder S := hS.isOrder
  obtain ⟨Λ₁, Λ₂, hΛ₁, hΛ₂, hS12, -⟩ := hS

  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b) (d₁ := algebraMap ℚ K a) (d₂ := (0 : K))
    (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl
    (AlgEquiv.refl : ℍ[K, algebraMap ℚ K a, algebraMap ℚ K b] ≃ₐ[K] ℍ[K, algebraMap ℚ K a, algebraMap ℚ K b])
  have hφ' : ∀ (z : ℍ[ℚ, a, b]) (r : K),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ K z.re, algebraMap ℚ K z.imI, algebraMap ℚ K z.imJ, algebraMap ℚ K z.imK⟩ :
        ℍ[K, algebraMap ℚ K a, algebraMap ℚ K b]) := by
    intro z r; rw [hφ]; rfl

  have hSv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] K, x ∈ Submodule.localBox S v ↔ N v φ x ≤ 1 := by
    intro x
    rw [hS12, Submodule.localBox_inf Λ₁ Λ₂ hΛ₁.isOrder.fg hΛ₁.isOrder.spanTop hΛ₂.isOrder.fg hΛ₂.isOrder.spanTop v,
      ← QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit v hdiv hΛ₁ hΛ₂, inf_idem,
      QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit hΛ₁ v hdiv
        φ hφ' x, ← eK_mem_iff, ← nrd_Θ]
    rfl

  obtain ⟨ϖ, hϖ⟩ := exists_uniformiser v φ hdiv
  have hϖP : N v φ (ϖ : ℍ[ℚ, a, b] ⊗[ℚ] K) = P⁻¹ := hϖ

  have hcast : ((q' : ℕ) : ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)]) =
      ((primesEquiv (R := 𝓞 ℚ) v : ℕ) : ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)]) :=
    congrArg (Nat.cast : ℕ → ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)]) hpv.symm
  have normq : ‖((q' : ℚ) : ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)])‖ = P⁻¹ := by
    rw [Rat.cast_natCast, hcast, Padic.norm_p]
  have normqi : ‖(((q' : ℚ)⁻¹ : ℚ) : ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)])‖ = P := by
    rw [Rat.cast_inv, norm_inv, normq, inv_inv]

  have mem_box : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f, x ∈ Submodule.finiteAdeleBox S ↔
      ∀ w, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x ∈ Submodule.localBox S w :=
    fun x => mem_finiteAdeleBox_iff S hSo.fg hSo.spanTop x
  have mem_U : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ, u ∈ Submodule.finiteIdeleStabilizer S ↔
      ∀ w, unitAt w u ∈ Submodule.localBoxUnits S w :=
    fun u => QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits S hSo u
  have hmulS : ∀ w, ∀ {x y : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ w},
      x ∈ Submodule.localBox S w → y ∈ Submodule.localBox S w → x * y ∈ Submodule.localBox S w :=
    by intro w x y hx hy; exact mul_mem_localBox S w (fun _ _ h1 h2 => hSo.mul_mem h1 h2) hx hy
  have ev_val : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
        ((unitAt w x : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : _) :=
    fun w x => rfl
  have ev_inv : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
        (((unitAt w x)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : _) :=
    fun w x => (coe_inv_unitAt w x).symm

  have unit_w : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ),
      unitAt w x ∈ Submodule.localBoxUnits S w ↔
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈
            Submodule.localBox S w ∧
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈
            Submodule.localBox S w := by
    intro w x; rw [Submodule.mem_localBoxUnits_iff, ev_val, ev_inv]; rfl
  have unit_v : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ, u ∈ Submodule.localBoxUnits S v ↔ N v φ (u : ℍ[ℚ, a, b] ⊗[ℚ] K) = 1 :=
    fun u => mem_localBoxUnits_iff_N v φ S hSv u

  have hq_w : ∀ w, w ≠ v → w.valuation ℚ ((q' : ℚ)⁻¹) ≤ 1 := by
    intro w hw
    rw [map_inv₀, valuation_natCast_eq_one_of_notMem w q' (hnotMem_of w hw), inv_one]
  have hq_le : ∀ w : HeightOneSpectrum (𝓞 ℚ), w.valuation ℚ (q' : ℚ) ≤ 1 := fun w => natCast_valuation_le_one w q'
  have ev_smul : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (r • x) = r • Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x :=
    fun w r x => map_smul _ r x

  have heckeChar : ∀ h : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ, h ∈ primeHeckeSet S q' ↔
      (∀ w, w ≠ v → unitAt w h ∈ Submodule.localBoxUnits S w) ∧
        N v φ ((unitAt v h : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) = P⁻¹ := by
    intro h
    rw [QuaternionAlgebra.mem_primeHeckeSet_iff, mem_box, mem_box, mem_box, mem_box]
    have Nh_pos : 0 < N v φ ((unitAt v h : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) :=
      lt_of_le_of_ne (N_nonneg v φ _) (N_unit_ne_zero v φ _).symm
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have hw : ∀ w, w ≠ v → unitAt w h ∈ Submodule.localBoxUnits S w := by
        intro w hw
        rw [unit_w]
        refine ⟨h1 w, ?_⟩
        have := ratCast_smul_mem_localBox S w (h2 w) ((q' : ℚ)⁻¹) (hq_w w hw)
        rwa [ev_smul, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hq'.ne_zero : (q' : ℚ) ≠ 0), one_smul] at this
      refine ⟨hw, ?_⟩

      have hv1 : N v φ ((unitAt v h : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) ≤ 1 := by
        rw [← hSv, ← ev_val]; exact h1 v
      have hv3 : ¬ N v φ (((unitAt v h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) ≤ 1 := by
        intro hle; apply h3; intro w
        by_cases hw' : w = v
        · subst hw'; rw [ev_inv, hSv]; exact hle
        · exact ((unit_w w h).mp (hw w hw')).2
      have hv4 : ¬ N v φ ((q' : ℚ)⁻¹ • ((unitAt v h : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K)) ≤ 1 := by
        intro hle; apply h4; intro w
        by_cases hw' : w = v
        · subst hw'; rw [ev_smul, ev_val, hSv]; exact hle
        · rw [ev_smul]; exact ratCast_smul_mem_localBox S w (h1 w) _ (hq_w w hw')
      rw [N_inv, not_le] at hv3
      rw [N_ratCast_smul v φ hφ', normqi, not_le] at hv4
      have hlt1 : N v φ ((unitAt v h : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) < 1 :=
        (one_lt_inv₀ Nh_pos).mp hv3
      have hgt : (P ^ (2 : ℕ))⁻¹ < N v φ ((unitAt v h : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) :=
        (inv_lt_iff_one_lt_mul₀' (by positivity)).mpr hv4
      have hne : nrd (Θ v φ ((unitAt v h : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K)) ≠ 0 := by
        intro h0; apply (N_unit_ne_zero v φ (unitAt v h)); unfold N; rw [h0, norm_zero]
      exact norm_eq_inv_of_lt_of_lt _ _ hne hgt hlt1
    · rintro ⟨hw, hv⟩
      have hvi : N v φ (((unitAt v h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) = P := by
        rw [N_inv, hv, inv_inv]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro w
        by_cases hw' : w = v
        · subst hw'; rw [ev_val, hSv, hv]; exact inv_le_one_of_one_le₀ hP1.le
        · exact ((unit_w w h).mp (hw w hw')).1
      · intro w
        rw [ev_smul]
        by_cases hw' : w = v
        · subst hw'
          rw [ev_inv, hSv, N_ratCast_smul v φ hφ', normq, hvi, inv_pow,
            show (P ^ 2)⁻¹ * P = P⁻¹ by field_simp]
          exact inv_le_one_of_one_le₀ hP1.le
        · exact ratCast_smul_mem_localBox S w ((unit_w w h).mp (hw w hw')).2 _ (hq_le w)
      · intro hall
        have := hall v
        rw [ev_inv, hSv, hvi] at this
        linarith
      · intro hall
        have := hall v
        rw [ev_smul, ev_val, hSv, N_ratCast_smul v φ hφ', normqi, hv, show P ^ 2 * P⁻¹ = P by field_simp] at this
        linarith

  obtain ⟨π, hπv, hπvi, hπw⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq_of_forall_ne S hSo.fg hSo.spanTop v
    (ϖ : ℍ[ℚ, a, b] ⊗[ℚ] K) ((ϖ⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) (by rw [Units.mul_inv])
    (by rw [Units.inv_mul]) 1 (by
      intro w hw
      rw [inv_one, Units.val_one, map_one]
      have h1 : (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox S w :=
        tmul_one_mem_localBox S w hSo.one_mem
      exact ⟨h1, h1⟩)
  have hπw1 : ∀ w, w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (π : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 := by
    intro w hw; rw [(hπw w hw).1, Units.val_one, map_one]
  have hπwi1 : ∀ w, w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((π⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 := by
    intro w hw; rw [(hπw w hw).2, inv_one, Units.val_one, map_one]
  have hπunit_v : unitAt v π = ϖ := Units.ext hπv
  have hπunit_w : ∀ w, w ≠ v → unitAt w π = 1 := fun w hw => Units.ext (hπw1 w hw)
  have hπU_w : ∀ w, w ≠ v → unitAt w π ∈ Submodule.localBoxUnits S w := by
    intro w hw
    rw [hπunit_w w hw, Submodule.mem_localBoxUnits_iff, inv_one, Units.val_one]
    exact ⟨tmul_one_mem_localBox S w hSo.one_mem, tmul_one_mem_localBox S w hSo.one_mem⟩

  have c1 : π ∈ primeHeckeSet S q' := by
    rw [heckeChar]
    exact ⟨hπU_w, by rw [hπunit_v, hϖP]⟩

  have c2 : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (π : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 :=
    fun w hw => hπw1 w (hne_of w hw)

  have c3 : ∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ,
      u ∈ Submodule.finiteIdeleStabilizer S ↔ π * u * π⁻¹ ∈ Submodule.finiteIdeleStabilizer S := by
    intro u
    rw [mem_U, mem_U]
    refine forall_congr' fun w => ?_
    change unitAt w u ∈ _ ↔ unitAt w (π * u * π⁻¹) ∈ _
    rw [unitAt_mul, unitAt_mul, unitAt_inv]
    by_cases hw : w = v
    · subst hw
      rw [unit_v, unit_v, Units.val_mul, Units.val_mul, N_conj]
    · rw [hπunit_w w hw, one_mul, inv_one, mul_one]

  set δ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
    (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) (Nat.cast_ne_zero.mpr hq'.ne_zero)))
    with hδdef
  have hδcoe : ((Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) hq0) : (ℍ[ℚ, a, b])ˣ) :
      ℍ[ℚ, a, b]) = (q' : ℚ) • 1 :=
    Algebra.algebraMap_eq_smul_one (q' : ℚ)
  have hδcoei : (((Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) hq0))⁻¹ : (ℍ[ℚ, a, b])ˣ) :
      ℍ[ℚ, a, b]) = (q' : ℚ)⁻¹ • 1 := by
    rw [Units.coe_map_inv]
    show algebraMap ℚ ℍ[ℚ, a, b] (((Units.mk0 (q' : ℚ) hq0)⁻¹ : ℚˣ) : ℚ) = _
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, Algebra.algebraMap_eq_smul_one]
  have hδval : ∀ w, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (δ : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
      (q' : ℚ) • (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := by
    intro w
    rw [hδdef, Submodule.val_finiteIdeleDiagonal_apply, hδcoe, Submodule.finiteAdeleEvalAt_tmul,
      ← TensorProduct.smul_tmul']
    rfl
  have hδinv : ∀ w, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((δ⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
      (q' : ℚ)⁻¹ • (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := by
    intro w
    rw [hδdef, ← map_inv, Submodule.val_finiteIdeleDiagonal_apply, hδcoei, Submodule.finiteAdeleEvalAt_tmul,
      ← TensorProduct.smul_tmul']
    rfl
  have c4 : ∃ u ∈ Submodule.finiteIdeleStabilizer S, π * π = δ * u := by
    refine ⟨δ⁻¹ * (π * π), ?_, by rw [mul_inv_cancel_left]⟩
    rw [mem_U]
    intro w
    by_cases hw : w = v
    · subst hw
      rw [unit_v, coe_unitAt, Units.val_mul, Units.val_mul, map_mul, map_mul, hδinv, N_mul, N_mul,
        N_ratCast_smul v φ hφ', N_one, normqi, hπv, hϖP]
      field_simp
    · rw [unit_w]
      simp only [mul_inv_rev, inv_inv, Units.val_mul, map_mul, hδinv, hδval, hπw1 w hw, hπwi1 w hw, mul_one,
        one_mul]
      exact ⟨ratCast_smul_mem_localBox S w (tmul_one_mem_localBox S w hSo.one_mem) _ (hq_w w hw),
        ratCast_smul_mem_localBox S w (tmul_one_mem_localBox S w hSo.one_mem) _ (hq_le w)⟩

  have c5 : primeHeckeSet S q' = {h | ∃ u ∈ Submodule.finiteIdeleStabilizer S, h = π * u} := by
    ext h
    simp only [Set.mem_setOf_eq]
    rw [heckeChar]
    have key : ((∀ w, w ≠ v → unitAt w h ∈ Submodule.localBoxUnits S w) ∧
        N v φ ((unitAt v h : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) = P⁻¹) ↔
        π⁻¹ * h ∈ Submodule.finiteIdeleStabilizer S := by
      rw [mem_U]
      constructor
      · rintro ⟨hw, hv⟩ w
        rw [unitAt_mul, unitAt_inv]
        by_cases hw' : w = v
        · subst hw'
          rw [unit_v, hπunit_v, Units.val_mul, N_mul, N_inv, hϖP, hv, inv_inv, mul_inv_cancel₀ hPne]
        · rw [hπunit_w w hw', inv_one, one_mul]; exact hw w hw'
      · intro hu
        refine ⟨fun w hw' => ?_, ?_⟩
        · have := hu w
          change unitAt w (π⁻¹ * h) ∈ _ at this
          rwa [unitAt_mul, unitAt_inv, hπunit_w w hw', inv_one, one_mul] at this
        · have := hu v
          change unitAt v (π⁻¹ * h) ∈ _ at this
          rw [unitAt_mul, unitAt_inv, unit_v, hπunit_v, Units.val_mul, N_mul, N_inv, hϖP, inv_inv] at this
          rw [← mul_inv_cancel₀ hPne] at this
          exact mul_left_cancel₀ hPne this
    rw [key]
    constructor
    · intro hu; exact ⟨π⁻¹ * h, hu, by rw [mul_inv_cancel_left]⟩
    · rintro ⟨u, hu, rfl⟩; rwa [inv_mul_cancel_left]

  have c6 := classSetHeckeMatrix_coset (Submodule.finiteIdeleStabilizer S) π (primeHeckeSet S q') c5

  have c7 : ∀ h : ℍ[ℚ, a, b], h ∈ Submodule.ofFiniteIdele S π ↔
      h ∈ S ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h)) := by
    intro h

    have step1 : h ∈ Submodule.ofFiniteIdele S π ↔
        ((π⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * (h ⊗ₜ[ℚ] (1 : 𝔸f)) ∈ Submodule.finiteAdeleBox S := by
      rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyh⟩
        rw [AddMonoidHom.coe_mulLeft] at hyh
        rw [← hyh, ← mul_assoc, Units.inv_mul, one_mul]; exact hy
      · intro hy
        exact ⟨_, hy, by rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.mul_inv, one_mul]⟩
    have hS_iff := mem_iff_forall_tmul_one_mem_localBox S hSo.fg hSo.spanTop h

    have hNh : N v φ (h ⊗ₜ[ℚ] (1 : K)) = ‖((nrd h : ℚ) : ℚ_[(primesEquiv (R := 𝓞 ℚ) v : ℕ)])‖ := N_tmul_one v φ hφ' h

    have hdef0 : nrd h = 0 ↔ h = 0 := by
      constructor
      · intro h0
        obtain ⟨h₀, h₁, h₂, h₃⟩ := h
        simp only [nrd_mk] at h0
        have ha := hdef.1; have hb := hdef.2.1
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

    have step2 : N v φ (((ϖ⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) * (h ⊗ₜ[ℚ] (1 : K))) ≤ 1 ↔
        (h = 0 ∨ 1 ≤ padicValRat q' (nrd h)) := by
      rw [N_mul, N_inv, hϖP, inv_inv, hNh]
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
    rw [step1, mem_box, hS_iff, ← step2]
    constructor
    · intro hall
      have hv' := hall v
      rw [map_mul, ev_inv, hπunit_v, Submodule.finiteAdeleEvalAt_tmul, hSv] at hv'
      refine ⟨fun w => ?_, hv'⟩
      by_cases hw : w = v
      · subst hw
        rw [hSv]
        have hle : N v φ (h ⊗ₜ[ℚ] (1 : K)) ≤
            N v φ (((ϖ⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] K)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] K) * (h ⊗ₜ[ℚ] (1 : K))) := by
          rw [N_mul, N_inv, hϖP, inv_inv]
          exact le_mul_of_one_le_left (N_nonneg v φ _) hP1.le
        exact hle.trans hv'
      · have := hall w
        rwa [map_mul, ev_inv, hπunit_w w hw, inv_one, Units.val_one, one_mul, Submodule.finiteAdeleEvalAt_tmul] at this
    · rintro ⟨hall, hv'⟩ w
      rw [map_mul, ev_inv, Submodule.finiteAdeleEvalAt_tmul]
      by_cases hw : w = v
      · subst hw; rw [hπunit_v, hSv]; exact hv'
      · rw [hπunit_w w hw, inv_one, Units.val_one, one_mul]; exact hall w
  exact ⟨π, c1, c2, c3, c4, c5, c6, c7⟩

end Main
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt.RamHecke.RamTransport"

end RamHecke
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt.RamHecke.RamTransport P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt.RamHecke"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt.RamHecke.RamTransport P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt.RamHecke"

open QuaternionAlgebra CerednikDrinfeld in
theorem solution
    {a b : ℚ} {q' : ℕ} (hq' : q'.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {S : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hS : IsEichlerOrder S N)
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer S))] :
    ∃ π : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      π ∈ primeHeckeSet S q' ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (π : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      (∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
        u ∈ Submodule.finiteIdeleStabilizer S ↔ π * u * π⁻¹ ∈ Submodule.finiteIdeleStabilizer S) ∧
      (∃ u ∈ Submodule.finiteIdeleStabilizer S,
        π * π = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (q' : ℚ) (Nat.cast_ne_zero.mpr hq'.ne_zero))) * u) ∧
      primeHeckeSet S q' = {h | ∃ u ∈ Submodule.finiteIdeleStabilizer S, h = π * u} ∧
      classSetHeckeMatrix (Submodule.finiteIdeleStabilizer S) (primeHeckeSet S q') =
        Matrix.of (fun i j : ClassSet (Submodule.finiteIdeleStabilizer S) =>
          if classSetShift (Submodule.finiteIdeleStabilizer S) π j = i then (1 : ℤ) else 0) ∧
      (∀ h : ℍ[ℚ, a, b], h ∈ Submodule.ofFiniteIdele S π ↔
        h ∈ S ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h))) :=
  RamHecke.main hq' hdef hS

end S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_primeHeckeSet_eq_setOf_mul_of_isDefiniteRamifiedExactlyAt (solution)
