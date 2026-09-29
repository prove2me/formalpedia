-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/54cf1366-2a81-5fa2-bd23-d552ebf96a02

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_QuaternionAlgebra_BaseChange
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_QuaternionAlgebra_IsDefiniteRamifiedExactlyAt_exists_nrd_eq_of_pos
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace QuaternionAlgebra
p2m_export "QuaternionAlgebra" "re smul_mk mk_mul_mk imK mk imJ imI IsMaximalOrder IsEichlerOrder IsDefiniteRamifiedExactlyAt IsOrder ClassSet ClassSet.mk ClassSet.mk_mul_of_mem ClassSet.mk_diagonal_mul primeHeckeSet nrd nrd_mk nrd_one mul_star_eq_coe_nrd star_mul_eq_coe_nrd baseChangeRight baseChangeRight_tmul IsDefiniteRamifiedExactlyAt.exists_nrd_eq_of_pos IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits"
namespace RamAL
p2m_open "QuaternionAlgebra"

variable {a b : ℚ}

local notation "𝔸ℍ" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" w => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w

theorem isMaximal_span_natCast_of_prime {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsMaximal := by
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpO : _root_.Prime (p : 𝓞 ℚ) := by
    have : (p : 𝓞 ℚ) = e.symm (p : ℤ) := by rw [map_natCast]
    rw [this]
    exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ
  have hprime : (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsPrime := (Ideal.span_singleton_prime hpO.ne_zero).mpr hpO
  refine hprime.isMaximal ?_
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

theorem eq_of_natCast_prime_mem {p : ℕ} (hp : p.Prime) {v v' : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) (hv' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have hmax := isMaximal_span_natCast_of_prime hp
  have h1 : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)).symm
  have h2 : v'.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v'.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv')).symm
  exact HeightOneSpectrum.ext (h1.trans h2.symm)

theorem v_algebraMap_natCast_eq_one {p : ℕ} {w : HeightOneSpectrum (𝓞 ℚ)} (hw : ((p : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (p : ℚ)) = 1 := by
  rw [show Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (p : ℚ)) = w.valuation ℚ (p : ℚ) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _]
  have : (p : ℚ) = algebraMap (𝓞 ℚ) ℚ (p : 𝓞 ℚ) := by simp
  rw [this, HeightOneSpectrum.valuation_of_algebraMap]
  have hle := w.intValuation_le_one (p : 𝓞 ℚ)
  have hnlt : ¬ w.intValuation (p : 𝓞 ℚ) < 1 := by
    rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact hw
  exact le_antisymm hle (not_lt.mp hnlt)

theorem v_natCast_lt_one {p : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) < 1 := by
  rw [show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) = v.valuation ℚ (p : ℚ) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _]
  have : (p : ℚ) = algebraMap (𝓞 ℚ) ℚ (p : 𝓞 ℚ) := by simp
  rw [this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact hv

theorem algebraMap_natCast_mem {p : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) :
    algebraMap ℚ (w.adicCompletion ℚ) (p : ℚ) ∈ w.adicCompletionIntegers ℚ := by
  rw [map_natCast]; exact natCast_mem _ _

theorem algebraMap_inv_natCast_not_mem {p : ℕ} [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    algebraMap ℚ (v.adicCompletion ℚ) ((p : ℚ)⁻¹) ∉ v.adicCompletionIntegers ℚ := by
  intro h
  have hp0 : algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap ℚ (v.adicCompletion ℚ)).injective]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀] at h
  have hlt := v_natCast_lt_one v hv
  have hv0 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hp0
  have h1 : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) * (Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)))⁻¹ = 1 :=
    mul_inv_cancel₀ hv0
  have : (1 : WithZero (Multiplicative ℤ)) ≤ Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) :=
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h1.symm
      _ ≤ Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) * 1 := mul_le_mul_right h _
      _ = _ := mul_one _
  exact not_lt.mpr this hlt

theorem algebraMap_inv_natCast_mem_of_not_mem {p : ℕ} {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : ((p : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) :
    algebraMap ℚ (w.adicCompletion ℚ) ((p : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, v_algebraMap_natCast_eq_one hw, inv_one]

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem tmul_one_mul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c * c', mul_mem hc hc', ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem ratSmul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (w : HeightOneSpectrum (𝓞 ℚ)) {c : ℚ}
    (hc : algebraMap ℚ (w.adicCompletion ℚ) c ∈ w.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ w) : c • x ∈ Submodule.localBox Λ w := by
  have e : c • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) * x := by
    have e1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) = c • (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rw [e1, smul_mul_assoc, one_mul]
  rw [e]
  exact tmul_one_mul_mem_localBox w hc hx

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  unfold Submodule.localBox
  rw [Algebra.TensorProduct.one_def]
  exact AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩

def coord (w : HeightOneSpectrum (𝓞 ℚ)) :
    ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b] :=
  (QuaternionAlgebra.baseChangeRight (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    rfl (map_zero _) rfl).toRingEquiv

theorem coord_formula (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ) :
    coord w (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
      algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) := by
  show QuaternionAlgebra.baseChangeRight _ _ _ (z ⊗ₜ[ℚ] r) = _
  rw [QuaternionAlgebra.baseChangeRight_tmul]
  ext <;> simp [smul_eq_mul]

def locNrd (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : w.adicCompletion ℚ :=
  QuaternionAlgebra.nrd (coord w x)

theorem nrd_mul' {K : Type*} [CommRing K] {a' b' : K} (x y : ℍ[K, a', b']) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem locNrd_mul (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    locNrd w (x * y) = locNrd w x * locNrd w y := by
  unfold locNrd
  rw [(coord w).map_mul, nrd_mul']

theorem locNrd_one (w : HeightOneSpectrum (𝓞 ℚ)) : locNrd w (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 1 := by
  unfold locNrd
  have h1 : coord w (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = 1 := map_one (coord w)
  rw [h1, QuaternionAlgebra.nrd_one]

theorem locNrd_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    locNrd w (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd z) := by
  unfold locNrd
  rw [coord_formula, one_smul, QuaternionAlgebra.nrd_mk, QuaternionAlgebra.nrd]
  simp only [map_sub, map_add, map_mul, map_pow]

theorem locNrd_one_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (t : w.adicCompletion ℚ) :
    locNrd w ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t ^ 2 := by
  unfold locNrd
  rw [coord_formula, QuaternionAlgebra.smul_mk, QuaternionAlgebra.nrd_mk]
  simp only [show (1 : ℍ[ℚ, a, b]).re = 1 from rfl, show (1 : ℍ[ℚ, a, b]).imI = 0 from rfl,
    show (1 : ℍ[ℚ, a, b]).imJ = 0 from rfl, show (1 : ℍ[ℚ, a, b]).imK = 0 from rfl, map_one, map_zero,
    smul_eq_mul, mul_one, mul_zero]
  ring

theorem ratSmul_eq (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    c • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) * x := by
  have e1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) c) = c • (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := by
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rw [e1, smul_mul_assoc, one_mul]

theorem locNrd_ratSmul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    locNrd w (c • x) = algebraMap ℚ (w.adicCompletion ℚ) c ^ 2 * locNrd w x := by
  rw [ratSmul_eq, locNrd_mul, locNrd_one_tmul]

theorem locNrd_conj (w : HeightOneSpectrum (𝓞 ℚ)) {g gi : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hg : gi * g = 1)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) : locNrd w (gi * x * g) = locNrd w x := by
  rw [locNrd_mul, locNrd_mul, mul_comm (locNrd w gi), mul_assoc, ← locNrd_mul, hg, locNrd_one, mul_one]

section Div
variable {p : ℕ} [Fact p.Prime]

theorem mem_localBox_iff_locNrd (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox R v ↔ locNrd v x ∈ v.adicCompletionIntegers ℚ := by
  have hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y := (hdef.2.2 v).mpr hv
  obtain ⟨Λ₁, Λ₂, h₁, h₂, hRdef, -⟩ := hR
  have hbox : Submodule.localBox R v = Submodule.localBox Λ₁ v := by
    rw [hRdef, Submodule.localBox_inf Λ₁ Λ₂ h₁.isOrder.fg h₁.isOrder.spanTop h₂.isOrder.fg h₂.isOrder.spanTop,
      ← QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit v hdiv h₁ h₂, inf_idem]
  rw [hbox]
  exact QuaternionAlgebra.IsMaximalOrder.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit h₁ v hdiv
    (coord v) (coord_formula v) x

end Div

def unitOfNrd (x : ℍ[ℚ, a, b]) (hx : QuaternionAlgebra.nrd x ≠ 0) : (ℍ[ℚ, a, b])ˣ where
  val := x
  inv := (QuaternionAlgebra.nrd x)⁻¹ • star x
  val_inv := by
    rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe_nrd]
    ext <;> simp [hx]
  inv_val := by
    rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd]
    ext <;> simp [hx]

@[scoped simp] theorem val_unitOfNrd (x : ℍ[ℚ, a, b]) (hx : QuaternionAlgebra.nrd x ≠ 0) :
    ((unitOfNrd x hx : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = x := rfl

theorem nrd_val_inv (B : (ℍ[ℚ, a, b])ˣ) :
    QuaternionAlgebra.nrd ((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]))⁻¹ := by
  have h : QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]) * QuaternionAlgebra.nrd ((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 := by
    rw [← nrd_mul', Units.mul_inv, QuaternionAlgebra.nrd_one]
  exact eq_inv_of_mul_eq_one_right h

theorem mem_iff_tmul_one_mem_box {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) (z : ℍ[ℚ, a, b]) :
    z ∈ X ↔ z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox X := by
  have key := Submodule.ofFiniteIdele_one X hX.fg hX.spanTop
  constructor
  · intro hz
    unfold Submodule.finiteAdeleBox
    refine AddSubgroup.subset_closure ⟨z, hz, 1, fun w => ?_, rfl⟩
    exact one_mem _
  · intro hz
    rw [← key]
    show z ∈ Submodule.ofFiniteIdele X 1
    unfold Submodule.ofFiniteIdele
    rw [Submodule.mem_comap]
    show z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
      (Submodule.finiteAdeleBox X).map (AddMonoidHom.mulLeft (((1 : (𝔸ℍ)ˣ)) : 𝔸ℍ))
    rw [AddSubgroup.mem_map]
    refine ⟨_, hz, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, Units.val_one, one_mul]

theorem mem_conjByFiniteIdele_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (𝔸ℍ)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      ((g⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : 𝔸ℍ) ∈ Submodule.finiteAdeleBox Λ := by
  show z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ (Submodule.finiteAdeleBox Λ).map _ ↔ _
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨u, hu, h⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight] at h
    have : ((g⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : 𝔸ℍ) = u := by
      rw [← h, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact hu
  · intro h
    refine ⟨_, h, ?_⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    show (g : 𝔸ℍ) * (((g⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : 𝔸ℍ)) * ((g⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = _
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem evU_mul (w : HeightOneSpectrum (𝓞 ℚ)) (x y : (𝔸ℍ)ˣ) :
    Units.map (ev w).toRingHom.toMonoidHom (x * y) =
      Units.map (ev w).toRingHom.toMonoidHom x * Units.map (ev w).toRingHom.toMonoidHom y :=
  MonoidHom.map_mul _ x y

theorem evU_inv (w : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℍ)ˣ) :
    Units.map (ev w).toRingHom.toMonoidHom x⁻¹ = (Units.map (ev w).toRingHom.toMonoidHom x)⁻¹ :=
  MonoidHom.map_inv _ x

theorem ev_mul (w : HeightOneSpectrum (𝓞 ℚ)) (x y : 𝔸ℍ) : (ev w) (x * y) = (ev w) x * (ev w) y := map_mul _ x y

theorem ev_ratSmul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : 𝔸ℍ) : (ev w) (c • x) = c • (ev w) x :=
  map_smul (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w) c x

def pU (p : ℕ) [Fact p.Prime] : (ℍ[ℚ, a, b])ˣ :=
  Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

theorem val_diag_pU (p : ℕ) [Fact p.Prime] :
    ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p) : (𝔸ℍ)ˣ) : 𝔸ℍ) = (p : ℚ) • (1 : 𝔸ℍ) := by
  rw [Submodule.val_finiteIdeleDiagonal_apply]
  show ((algebraMap ℚ ℍ[ℚ, a, b] (p : ℚ)) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) = _
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul', ← Algebra.TensorProduct.one_def]

theorem val_diag_pU_inv (p : ℕ) [Fact p.Prime] :
    (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p))⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = (p : ℚ)⁻¹ • (1 : 𝔸ℍ) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have h : (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p) : 𝔸ℍ) * ((p : ℚ)⁻¹ • (1 : 𝔸ℍ)) = 1 := by
    rw [val_diag_pU, smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hp0, one_smul]
  exact Units.inv_eq_of_mul_eq_one_right h

theorem diag_pU_comm (p : ℕ) [Fact p.Prime] (x : (𝔸ℍ)ˣ) :
    x * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p) =
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p) * x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_diag_pU, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem ev_inv_mul_ev (w : HeightOneSpectrum (𝓞 ℚ)) (m : (𝔸ℍ)ˣ) :
    (ev w) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (ev w) (m : 𝔸ℍ) = 1 := by
  rw [← ev_mul, Units.inv_mul, map_one]

theorem conj_mem_localBox_of_conj_eq {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) {m : (𝔸ℍ)ˣ}
    (hmX : Submodule.conjByFiniteIdele X m = X) (w : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hx : x ∈ Submodule.localBox X w) :
    (ev w) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * x * (ev w) (m : 𝔸ℍ) ∈ Submodule.localBox X w := by
  have hx' : x ∈ Submodule.localBox (Submodule.conjByFiniteIdele X m) w := by rw [hmX]; exact hx
  obtain ⟨y, hy, hxy⟩ := (Submodule.mem_localBox_conjByFiniteIdele_iff X hX.fg hX.spanTop m w x).mp hx'
  rw [hxy, show (ev w) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * ((ev w) (m : 𝔸ℍ) * y * (ev w) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) * (ev w) (m : 𝔸ℍ) =
      ((ev w) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (ev w) (m : 𝔸ℍ)) * y * ((ev w) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (ev w) (m : 𝔸ℍ)) by
      noncomm_ring, ev_inv_mul_ev w m, one_mul, mul_one]
  exact hy

theorem normalises_stab_of_conj_eq {X : Submodule ℤ ℍ[ℚ, a, b]} (hX : IsOrder X) {m : (𝔸ℍ)ˣ}
    (hmX : Submodule.conjByFiniteIdele X m = X) (s : (𝔸ℍ)ˣ) (hs : s ∈ Submodule.finiteIdeleStabilizer X) :
    m⁻¹ * s * m ∈ Submodule.finiteIdeleStabilizer X := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits X hX] at hs ⊢
  intro w
  obtain ⟨h1, h2⟩ := hs w
  refine ⟨?_, ?_⟩
  · show (ev w) ((m⁻¹ * s * m : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ (Submodule.localBox X w : Set _)
    rw [SetLike.mem_coe, Units.val_mul, Units.val_mul, ev_mul, ev_mul]
    exact conj_mem_localBox_of_conj_eq hX hmX w h1
  · show (ev w) (((m⁻¹ * s * m)⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ (Submodule.localBox X w : Set _)
    rw [SetLike.mem_coe, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul, ev_mul, ev_mul]
    exact conj_mem_localBox_of_conj_eq hX hmX w h2

theorem mk_out_mul_eq_of_norm (U : Subgroup (𝔸ℍ)ˣ) {g : (𝔸ℍ)ˣ} (hnorm : ∀ s ∈ U, g⁻¹ * s * g ∈ U) (z : (𝔸ℍ)ˣ) :
    ClassSet.mk U ((ClassSet.mk U z).out * g) = ClassSet.mk U (z * g) := by
  have hmk : ClassSet.mk U (ClassSet.mk U z).out = ClassSet.mk U z := Quotient.out_eq _
  obtain ⟨δ', hδ', s, hs, hout⟩ := (DoubleCoset.eq _ _ _ _).mp hmk.symm
  obtain ⟨δ, hδ⟩ := MonoidHom.mem_range.mp hδ'
  rw [hout, ← hδ, show Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * z * s * g =
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * ((z * g) * (g⁻¹ * s * g)) by group,
    ClassSet.mk_diagonal_mul, ClassSet.mk_mul_of_mem _ _ (hnorm s hs)]

theorem mk_mul_shift_shift (U : Subgroup (𝔸ℍ)ˣ) {g u : (𝔸ℍ)ˣ} {d : (ℍ[ℚ, a, b])ˣ}
    (hnorm : ∀ s ∈ U, g⁻¹ * s * g ∈ U) (hu : u ∈ U)
    (hsq : g * g = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * u)
    (hdc : ∀ x : (𝔸ℍ)ˣ, x * Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] d * x)
    (z : (𝔸ℍ)ˣ) :
    ClassSet.mk U ((ClassSet.mk U (z * g)).out * g) = ClassSet.mk U z := by
  rw [mk_out_mul_eq_of_norm U hnorm, mul_assoc, hsq, ← mul_assoc, hdc z, mul_assoc, ClassSet.mk_diagonal_mul,
    ClassSet.mk_mul_of_mem _ _ hu]

theorem mk_shift_comm (U : Subgroup (𝔸ℍ)ˣ) {g m c : (𝔸ℍ)ˣ}
    (hnormg : ∀ s ∈ U, g⁻¹ * s * g ∈ U) (hnormm : ∀ s ∈ U, m⁻¹ * s * m ∈ U) (hc : c ∈ U)
    (hcomm : m * g = g * m * c) (z : (𝔸ℍ)ˣ) :
    ClassSet.mk U ((ClassSet.mk U (z * m)).out * g) = ClassSet.mk U ((ClassSet.mk U (z * g)).out * m) := by
  rw [mk_out_mul_eq_of_norm U hnormg, mk_out_mul_eq_of_norm U hnormm, mul_assoc, hcomm, ← mul_assoc, ← mul_assoc,
    ClassSet.mk_mul_of_mem _ _ hc]

section PerX

variable {p : ℕ} [Fact p.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b p)
  {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
  (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
  (B : (ℍ[ℚ, a, b])ˣ) (hB : QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]) = (p : ℚ))
  (ϖ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  (hϖv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (ϖ : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
    (B : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))
  (hϖiv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((ϖ⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = ((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ))
  (hϖw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (ϖ : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 ∧
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((ϖ⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
  (X : Submodule ℤ ℍ[ℚ, a, b]) (hX : IsOrder X) (hXbox : Submodule.localBox X v = Submodule.localBox R v)

include hdef hR hv hXbox in
theorem crit (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox X v ↔ locNrd v x ∈ v.adicCompletionIntegers ℚ := by
  rw [hXbox]; exact mem_localBox_iff_locNrd hdef hR v hv x

include hB hϖv in
theorem ny : locNrd v ((ev v) (ϖ : 𝔸ℍ)) = algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ) := by
  rw [hϖv, locNrd_tmul_one, hB]

include hB hϖiv in
theorem nyi : locNrd v ((ev v) ((ϖ⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) = algebraMap ℚ (v.adicCompletion ℚ) ((p : ℚ)⁻¹) := by
  rw [hϖiv, locNrd_tmul_one, nrd_val_inv, hB]

theorem hyyi : (ev v) (ϖ : 𝔸ℍ) * (ev v) ((ϖ⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = 1 := by
  rw [← ev_mul, Units.mul_inv, map_one]

theorem hyiy : (ev v) ((ϖ⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (ev v) (ϖ : 𝔸ℍ) = 1 := by
  rw [← ev_mul, Units.inv_mul, map_one]

include hdef hR hv hϖw hXbox in

theorem conj_loc (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    (ev w) ((ϖ⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * x * (ev w) (ϖ : 𝔸ℍ) ∈ Submodule.localBox X w ↔ x ∈ Submodule.localBox X w := by
  have conj_v : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      (ev v) ((ϖ⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * y * (ev v) (ϖ : 𝔸ℍ) ∈ Submodule.localBox X v ↔ y ∈ Submodule.localBox X v :=
    fun y => by rw [crit hdef hR v hv X hXbox, crit hdef hR v hv X hXbox, locNrd_conj v (hyiy v ϖ)]
  by_cases hw : w = v
  · subst hw; exact conj_v x
  · rw [(hϖw w hw).1, (hϖw w hw).2, one_mul, mul_one]

include hdef hR hv hϖw hX hXbox in

theorem normU (s : (𝔸ℍ)ˣ) (hs : s ∈ Submodule.finiteIdeleStabilizer X) : ϖ⁻¹ * s * ϖ ∈ Submodule.finiteIdeleStabilizer X := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits X hX] at hs ⊢
  intro w
  obtain ⟨h1, h2⟩ := hs w
  refine ⟨?_, ?_⟩
  · show (ev w) ((ϖ⁻¹ * s * ϖ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ (Submodule.localBox X w : Set _)
    rw [SetLike.mem_coe, Units.val_mul, Units.val_mul, ev_mul, ev_mul]
    exact (conj_loc hdef hR v hv ϖ hϖw X hXbox w _).mpr h1
  · show (ev w) (((ϖ⁻¹ * s * ϖ)⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ (Submodule.localBox X w : Set _)
    rw [SetLike.mem_coe, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul, ev_mul, ev_mul]
    exact (conj_loc hdef hR v hv ϖ hϖw X hXbox w _).mpr h2

include hdef hR hv hB hϖv hϖiv hϖw hX hXbox in

theorem hu : ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p))⁻¹ * (ϖ * ϖ) : (𝔸ℍ)ˣ) ∈
    Submodule.finiteIdeleStabilizer X := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpO : ∀ w : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (w.adicCompletion ℚ) (p : ℚ) ∈ w.adicCompletionIntegers ℚ :=
    fun w => algebraMap_natCast_mem w
  have hu_v : (p : ℚ)⁻¹ • (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * ((ev v) (ϖ : 𝔸ℍ) * (ev v) (ϖ : 𝔸ℍ)) ∈
      Submodule.localBox X v := by
    rw [crit hdef hR v hv X hXbox, smul_mul_assoc, one_mul, locNrd_ratSmul, locNrd_mul, ny v B hB ϖ hϖv, ← map_pow,
      ← map_mul, ← map_mul, show ((p : ℚ)⁻¹) ^ 2 * ((p : ℚ) * (p : ℚ)) = 1 by field_simp, map_one]
    exact one_mem _
  have hu_v' : (ev v) ((ϖ⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (ev v) ((ϖ⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * ((p : ℚ) • (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) ∈
      Submodule.localBox X v := by
    rw [crit hdef hR v hv X hXbox, mul_smul_comm, mul_one, locNrd_ratSmul, locNrd_mul, nyi v B hB ϖ hϖiv, ← map_pow,
      ← map_mul, ← map_mul, show (p : ℚ) ^ 2 * ((p : ℚ)⁻¹ * (p : ℚ)⁻¹) = 1 by field_simp, map_one]
    exact one_mem _
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits X hX]
  intro w
  refine ⟨?_, ?_⟩
  · show (ev w) (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU p))⁻¹ * (ϖ * ϖ) : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ (Submodule.localBox X w : Set _)
    rw [SetLike.mem_coe, Units.val_mul, Units.val_mul, val_diag_pU_inv, ev_mul, ev_mul, ev_ratSmul, map_one]
    by_cases hw : w = v
    · subst hw; exact hu_v
    · rw [(hϖw w hw).1, mul_one, smul_mul_assoc, one_mul]
      exact ratSmul_mem_localBox w (algebraMap_inv_natCast_mem_of_not_mem fun h => hw (eq_of_natCast_prime_mem hp h hv))
        (one_mem_localBox hX w)
  · show (ev w) ((((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU p))⁻¹ * (ϖ * ϖ))⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ (Submodule.localBox X w : Set _)
    rw [SetLike.mem_coe, mul_inv_rev, inv_inv, mul_inv_rev, Units.val_mul, Units.val_mul, val_diag_pU, ev_mul, ev_mul,
      ev_ratSmul, map_one]
    by_cases hw : w = v
    · subst hw; exact hu_v'
    · rw [(hϖw w hw).2, mul_one, mul_smul_comm, mul_one]
      exact ratSmul_mem_localBox w (hpO w) (one_mem_localBox hX w)

theorem hsq' : ϖ * ϖ = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p) *
    ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p))⁻¹ * (ϖ * ϖ)) := by
  rw [mul_inv_cancel_left]

include hdef hR hv hB hϖv hϖiv hϖw hX hXbox in

theorem hH : ϖ ∈ primeHeckeSet X p := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpO : ∀ w : HeightOneSpectrum (𝓞 ℚ), algebraMap ℚ (w.adicCompletion ℚ) (p : ℚ) ∈ w.adicCompletionIntegers ℚ :=
    fun w => algebraMap_natCast_mem w
  have boxX := fun x => Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox X hX.fg hX.spanTop x
  have h1v : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (ϖ : 𝔸ℍ) ∈ Submodule.localBox X v := by
    rw [crit hdef hR v hv X hXbox, ny v B hB ϖ hϖv]; exact hpO _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [boxX]
    intro w
    by_cases hw : w = v
    · subst hw; exact h1v
    · rw [(hϖw w hw).1]; exact one_mem_localBox hX w
  · have h2v : (p : ℚ) • (ev v) ((ϖ⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ Submodule.localBox X v := by
      rw [crit hdef hR v hv X hXbox, locNrd_ratSmul, nyi v B hB ϖ hϖiv, ← map_pow, ← map_mul,
        show (p : ℚ) ^ 2 * (p : ℚ)⁻¹ = p by field_simp]
      exact hpO _
    rw [boxX]
    intro w
    rw [ev_ratSmul]
    by_cases hw : w = v
    · subst hw; exact h2v
    · rw [(hϖw w hw).2]
      exact ratSmul_mem_localBox w (hpO w) (one_mem_localBox hX w)
  · intro h
    rw [boxX] at h
    have := h v
    rw [crit hdef hR v hv X hXbox, nyi v B hB ϖ hϖiv] at this
    exact algebraMap_inv_natCast_not_mem v hv this
  · intro h
    rw [boxX] at h
    have := h v
    rw [ev_ratSmul, crit hdef hR v hv X hXbox, locNrd_ratSmul, ny v B hB ϖ hϖv, ← map_pow, ← map_mul,
      show ((p : ℚ)⁻¹) ^ 2 * (p : ℚ) = (p : ℚ)⁻¹ by field_simp] at this
    exact algebraMap_inv_natCast_not_mem v hv this

include hdef hR hv hϖw hX hXbox in

theorem hnorm : Submodule.conjByFiniteIdele X ϖ = X := by
  have boxX := fun x => Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox X hX.fg hX.spanTop x
  ext z
  rw [mem_conjByFiniteIdele_iff, mem_iff_tmul_one_mem_box hX, boxX, boxX]
  refine forall_congr' fun w => ?_
  rw [ev_mul, ev_mul]
  exact conj_loc hdef hR v hv ϖ hϖw X hXbox w _

include hdef hR hv hB hϖv hϖiv hϖw hX hXbox in

theorem hinv (x : ClassSet (Submodule.finiteIdeleStabilizer X)) :
    CerednikDrinfeld.classSetShift _ ϖ (CerednikDrinfeld.classSetShift _ ϖ x) = x := by
  unfold CerednikDrinfeld.classSetShift
  have hx : ClassSet.mk (Submodule.finiteIdeleStabilizer X) x.out = x := Quotient.out_eq _
  have key := mk_mul_shift_shift (Submodule.finiteIdeleStabilizer X) (normU hdef hR v hv ϖ hϖw X hX hXbox)
    (hu hdef hR v hv B hB ϖ hϖv hϖiv hϖw X hX hXbox) (hsq' ϖ) (diag_pU_comm (a := a) (b := b) p) x.out
  rw [hx] at key
  exact key

include hdef hR hv hB hϖv hϖiv hϖw hX hXbox in

theorem hc (m : (𝔸ℍ)ˣ) : m⁻¹ * ϖ⁻¹ * m * ϖ ∈ Submodule.finiteIdeleStabilizer X := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hmm : locNrd v ((ev v) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) * locNrd v ((ev v) (m : 𝔸ℍ)) = 1 := by
    rw [← locNrd_mul, ← ev_mul, Units.inv_mul, map_one, locNrd_one]
  have hpp : algebraMap ℚ (v.adicCompletion ℚ) ((p : ℚ)⁻¹) * algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hp0, map_one]
  have comm_v1 : (ev v) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (ev v) ((ϖ⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (ev v) (m : 𝔸ℍ) * (ev v) (ϖ : 𝔸ℍ) ∈
      Submodule.localBox X v := by
    rw [crit hdef hR v hv X hXbox, locNrd_mul, locNrd_mul, locNrd_mul, nyi v B hB ϖ hϖiv, ny v B hB ϖ hϖv,
      show locNrd v ((ev v) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) * algebraMap ℚ (v.adicCompletion ℚ) ((p : ℚ)⁻¹) *
          locNrd v ((ev v) (m : 𝔸ℍ)) * algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ) =
        (locNrd v ((ev v) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) * locNrd v ((ev v) (m : 𝔸ℍ))) *
          (algebraMap ℚ (v.adicCompletion ℚ) ((p : ℚ)⁻¹) * algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) by ring,
      hmm, hpp, one_mul]
    exact one_mem _
  have comm_v2 : (ev v) ((ϖ⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (ev v) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (ev v) (ϖ : 𝔸ℍ) * (ev v) (m : 𝔸ℍ) ∈
      Submodule.localBox X v := by
    rw [crit hdef hR v hv X hXbox, locNrd_mul, locNrd_mul, locNrd_mul, nyi v B hB ϖ hϖiv, ny v B hB ϖ hϖv,
      show algebraMap ℚ (v.adicCompletion ℚ) ((p : ℚ)⁻¹) * locNrd v ((ev v) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) *
          algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ) * locNrd v ((ev v) (m : 𝔸ℍ)) =
        (locNrd v ((ev v) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) * locNrd v ((ev v) (m : 𝔸ℍ))) *
          (algebraMap ℚ (v.adicCompletion ℚ) ((p : ℚ)⁻¹) * algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) by ring,
      hmm, hpp, one_mul]
    exact one_mem _
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits X hX]
  intro w
  refine ⟨?_, ?_⟩
  · show (ev w) ((m⁻¹ * ϖ⁻¹ * m * ϖ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ (Submodule.localBox X w : Set _)
    rw [SetLike.mem_coe, Units.val_mul, Units.val_mul, Units.val_mul, ev_mul, ev_mul, ev_mul]
    by_cases hw : w = v
    · subst hw; exact comm_v1
    · rw [(hϖw w hw).1, (hϖw w hw).2, mul_one, mul_one, ← ev_mul, Units.inv_mul, map_one]
      exact one_mem_localBox hX w
  · show (ev w) (((m⁻¹ * ϖ⁻¹ * m * ϖ)⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ (Submodule.localBox X w : Set _)
    rw [SetLike.mem_coe, show (m⁻¹ * ϖ⁻¹ * m * ϖ)⁻¹ = ϖ⁻¹ * m⁻¹ * ϖ * m by group,
      Units.val_mul, Units.val_mul, Units.val_mul, ev_mul, ev_mul, ev_mul]
    by_cases hw : w = v
    · subst hw; exact comm_v2
    · rw [(hϖw w hw).1, (hϖw w hw).2, one_mul, mul_one, ← ev_mul, Units.inv_mul, map_one]
      exact one_mem_localBox hX w

include hdef hR hv hB hϖv hϖiv hϖw hX hXbox in

theorem perX :
    (((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p))⁻¹ * (ϖ * ϖ) : (𝔸ℍ)ˣ) ∈
        Submodule.finiteIdeleStabilizer X) ∧
    ϖ ∈ primeHeckeSet X p ∧
    Submodule.conjByFiniteIdele X ϖ = X ∧
    (∀ x : ClassSet (Submodule.finiteIdeleStabilizer X),
      CerednikDrinfeld.classSetShift _ ϖ (CerednikDrinfeld.classSetShift _ ϖ x) = x) ∧
    ∀ m : (𝔸ℍ)ˣ,
      Units.map (ev v).toRingHom.toMonoidHom m ∈ Submodule.localBoxUnits R v →
      (∃ c ∈ Submodule.finiteIdeleStabilizer X, m * ϖ = ϖ * m * c) ∧
      (Submodule.conjByFiniteIdele X m = X →
        ∀ x : ClassSet (Submodule.finiteIdeleStabilizer X),
          CerednikDrinfeld.classSetShift _ ϖ (CerednikDrinfeld.classSetShift _ m x) =
            CerednikDrinfeld.classSetShift _ m (CerednikDrinfeld.classSetShift _ ϖ x)) := by
  refine ⟨hu hdef hR v hv B hB ϖ hϖv hϖiv hϖw X hX hXbox, hH hdef hR v hv B hB ϖ hϖv hϖiv hϖw X hX hXbox,
    hnorm hdef hR v hv ϖ hϖw X hX hXbox, hinv hdef hR v hv B hB ϖ hϖv hϖiv hϖw X hX hXbox, fun m _ => ⟨?_, fun hmX x => ?_⟩⟩
  · exact ⟨m⁻¹ * ϖ⁻¹ * m * ϖ, hc hdef hR v hv B hB ϖ hϖv hϖiv hϖw X hX hXbox m, by group⟩
  · unfold CerednikDrinfeld.classSetShift
    exact mk_shift_comm (Submodule.finiteIdeleStabilizer X) (normU hdef hR v hv ϖ hϖw X hX hXbox)
      (normalises_stab_of_conj_eq hX hmX) (hc hdef hR v hv B hB ϖ hϖv hϖiv hϖw X hX hXbox m) (by group) x.out

end PerX

theorem main {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ ϖ : (𝔸ℍ)ˣ,
      (∀ w : HeightOneSpectrum (𝓞 ℚ), ((p : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → (ev w) (ϖ : 𝔸ℍ) = 1) ∧
      (∃ u : (𝔸ℍ)ˣ,
        ϖ * ϖ = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))) * u ∧
        ∀ X : Submodule ℤ ℍ[ℚ, a, b], IsOrder X → Submodule.localBox X v = Submodule.localBox R v →
          u ∈ Submodule.finiteIdeleStabilizer X) ∧
      ∀ X : Submodule ℤ ℍ[ℚ, a, b], IsOrder X → Submodule.localBox X v = Submodule.localBox R v →
        ϖ ∈ primeHeckeSet X p ∧
        Submodule.conjByFiniteIdele X ϖ = X ∧
        (∀ x : ClassSet (Submodule.finiteIdeleStabilizer X),
          CerednikDrinfeld.classSetShift _ ϖ (CerednikDrinfeld.classSetShift _ ϖ x) = x) ∧
        ∀ m : (𝔸ℍ)ˣ,
          Units.map (ev v).toRingHom.toMonoidHom m ∈ Submodule.localBoxUnits R v →
          (∃ c ∈ Submodule.finiteIdeleStabilizer X, m * ϖ = ϖ * m * c) ∧
          (Submodule.conjByFiniteIdele X m = X →
            ∀ x : ClassSet (Submodule.finiteIdeleStabilizer X),
              CerednikDrinfeld.classSetShift _ ϖ (CerednikDrinfeld.classSetShift _ m x) =
                CerednikDrinfeld.classSetShift _ m (CerednikDrinfeld.classSetShift _ ϖ x)) := by
  have hp : p.Prime := Fact.out
  have hRo : IsOrder R := hR.isOrder

  obtain ⟨β, hβ⟩ := QuaternionAlgebra.IsDefiniteRamifiedExactlyAt.exists_nrd_eq_of_pos hp2 hdef (p : ℚ)
    (by exact_mod_cast hp.pos)
  have hβ0 : QuaternionAlgebra.nrd β ≠ 0 := by rw [hβ]; exact_mod_cast hp.ne_zero
  set B : (ℍ[ℚ, a, b])ˣ := unitOfNrd β hβ0 with hBdef
  have hB : QuaternionAlgebra.nrd (B : ℍ[ℚ, a, b]) = (p : ℚ) := hβ

  have hy : ((B : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) * (((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.mul_inv, ← Algebra.TensorProduct.one_def]
  have hy' : (((B⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) * ((B : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.inv_mul, ← Algebra.TensorProduct.one_def]
  obtain ⟨ϖ, hϖv, hϖiv, hϖw⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq_of_forall_ne R hRo.fg hRo.spanTop v _ _ hy hy' 1
    (fun w _ => ⟨by rw [Units.val_one, map_one]; exact one_mem_localBox hRo w,
      by rw [inv_one, Units.val_one, map_one]; exact one_mem_localBox hRo w⟩)
  have hϖw' : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → (ev w) (ϖ : 𝔸ℍ) = 1 ∧ (ev w) ((ϖ⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = 1 := by
    intro w hw
    obtain ⟨h1, h2⟩ := hϖw w hw
    rw [Units.val_one, map_one] at h1
    rw [inv_one, Units.val_one, map_one] at h2
    exact ⟨h1, h2⟩
  refine ⟨ϖ, fun w hw => (hϖw' w (fun h => hw (h ▸ hv))).1,
    ⟨(Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU (a := a) (b := b) p))⁻¹ * (ϖ * ϖ), ?_, fun X hX hXbox => ?_⟩,
    fun X hX hXbox => ?_⟩
  · show ϖ * ϖ = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] (pU p) * _
    rw [mul_inv_cancel_left]
  · exact (perX hdef hR v hv B hB ϖ hϖv hϖiv hϖw' X hX hXbox).1
  · exact (perX hdef hR v hv B hB ϖ hϖv hϖiv hϖw' X hX hXbox).2

end QuaternionAlgebra.RamAL
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive.QuaternionAlgebra P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive.QuaternionAlgebra.RamAL"
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive.QuaternionAlgebra"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive.QuaternionAlgebra P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive.QuaternionAlgebra.RamAL"

open _root_.QuaternionAlgebra _root_.P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive.QuaternionAlgebra CerednikDrinfeld in
theorem solution
    {a b : ℚ} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hdef : IsDefiniteRamifiedExactlyAt a b p)
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : ((p : ℕ) : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal) :
    ∃ ϖ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        ((p : ℕ) : NumberField.RingOfIntegers ℚ) ∉ w.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
          (ϖ : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) = 1) ∧
      (∃ u : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
        ϖ * ϖ = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))) * u ∧
        ∀ X : Submodule ℤ ℍ[ℚ, a, b], IsOrder X → Submodule.localBox X v = Submodule.localBox R v →
          u ∈ Submodule.finiteIdeleStabilizer X) ∧
      ∀ X : Submodule ℤ ℍ[ℚ, a, b], IsOrder X → Submodule.localBox X v = Submodule.localBox R v →
        ϖ ∈ primeHeckeSet X p ∧
        Submodule.conjByFiniteIdele X ϖ = X ∧
        (∀ x : ClassSet (Submodule.finiteIdeleStabilizer X),
          classSetShift _ ϖ (classSetShift _ ϖ x) = x) ∧
        ∀ m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
          Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m ∈ Submodule.localBoxUnits R v →
          (∃ c ∈ Submodule.finiteIdeleStabilizer X, m * ϖ = ϖ * m * c) ∧
          (Submodule.conjByFiniteIdele X m = X →
            ∀ x : ClassSet (Submodule.finiteIdeleStabilizer X),
              classSetShift _ ϖ (classSetShift _ m x) = classSetShift _ m (classSetShift _ ϖ x)) :=
  QuaternionAlgebra.RamAL.main hp2 hdef hR v hv

end S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_primeHeckeSet_ramified_conjByFiniteIdele_eq_classSetShift_involutive (solution)
