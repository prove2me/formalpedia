-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1ff742a1-d6df-5f3b-bfcf-b9fa97d0cd3b

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion NumberField Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace RamShift

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

section Places

open Rat.HeightOneSpectrum

theorem natCast_mem_asIdeal_iff (w : HOS) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ natGenerator w ∣ n := by
  rw [natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_eq_of_mem {q : ℕ} (hq : q.Prime) (w : HOS) (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) :
    natGenerator w = q :=
  (Nat.prime_dvd_prime_iff_eq (prime_natGenerator w) hq).mp ((natCast_mem_asIdeal_iff w q).mp hw)

theorem eq_of_natCast_mem {q : ℕ} (hq : q.Prime) {v w : HOS} (hv : (q : 𝓞 ℚ) ∈ v.asIdeal)
    (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : w = v := by
  apply (primesEquiv (R := 𝓞 ℚ)).injective
  apply Subtype.ext
  show natGenerator w = natGenerator v
  rw [natGenerator_eq_of_mem hq w hw, natGenerator_eq_of_mem hq v hv]

theorem natCast_notMem_of_ne {q : ℕ} (hq : q.Prime) {v : HOS} (hv : (q : 𝓞 ℚ) ∈ v.asIdeal) {w : HOS}
    (hw : w ≠ v) : (q : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (eq_of_natCast_mem hq hv h)

theorem valued_natCast_eq_one {n : ℕ} (w : HOS) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    Valued.v (n : w.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w)).mpr hn] at h
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = 1 at h
  rwa [map_natCast] at h

theorem natCast_inv_mem_integers {n : ℕ} (w : HOS) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    (n : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one w hn, inv_one]

theorem natCast_mem_integers (w : HOS) (n : ℕ) : (n : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = _ at h
  rw [map_natCast] at h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, h]
  exact HeightOneSpectrum.valuation_le_one w _

variable (v : HOS)

theorem asIdeal_eq_span : v.asIdeal = Ideal.span {(natGenerator v : 𝓞 ℚ)} := by
  have h := span_natGenerator (R := 𝓞 ℚ) v
  have h2 : v.asIdeal = Ideal.map ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ)
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) v.asIdeal) := by
    rw [Ideal.map_map]
    have : ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ).comp
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) = RingHom.id _ := by
      ext x; simp
    rw [this, Ideal.map_id]
  rw [h2]
  erw [← h]
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  simp

theorem valuation_natGenerator : v.valuation ℚ (natGenerator v : ℚ) = WithZero.exp (-1) := by
  rw [show (natGenerator v : ℚ) = algebraMap (𝓞 ℚ) ℚ (natGenerator v) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast (prime_natGenerator v).ne_zero)
    (asIdeal_eq_span v)

theorem valued_algebraMap (r : ℚ) : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) r) = v.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r

theorem valuation_eq_exp_neg_padicValRat {q : ℕ} [hq : Fact q.Prime] (hvq : natGenerator v = q) (r : ℚ) (hr : r ≠ 0) :
    v.valuation ℚ r = WithZero.exp (-padicValRat q r) := by

  have hpe : primesEquiv (R := 𝓞 ℚ) v = ⟨q, hq.out⟩ := Subtype.ext hvq
  have hiso : (v.valuation ℚ).IsEquiv (Rat.padicValuation q) := by
    have h := valuation_equiv_padicValuation (R := 𝓞 ℚ) v
    rw [hpe] at h
    exact h
  have hVq : v.valuation ℚ (q : ℚ) = WithZero.exp (-1) := by rw [← hvq]; exact valuation_natGenerator v
  have hPq : Rat.padicValuation q (q : ℚ) = WithZero.exp (-1) := Rat.padicValuation_self q
  have hP : Rat.padicValuation q r = WithZero.exp (-padicValRat q r) := by
    simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hr]
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.out.ne_zero
  have hVpow : ∀ j : ℤ, v.valuation ℚ ((q : ℚ) ^ j) = WithZero.exp (-j) := fun j => by
    rw [map_zpow₀, hVq, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]
  have hPpow : ∀ j : ℤ, Rat.padicValuation q ((q : ℚ) ^ j) = WithZero.exp (-j) := fun j => by
    rw [map_zpow₀, hPq, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]
  have hV0 : v.valuation ℚ r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  set m := WithZero.log (v.valuation ℚ r) with hm
  have hVr : v.valuation ℚ r = WithZero.exp m := (WithZero.exp_log hV0).symm
  set t := padicValRat q r

  have h1 : -t ≤ m := by
    have := (hiso.le_iff_le (x := r) (y := (q : ℚ) ^ (-m))).mp (by rw [hVr, hVpow, neg_neg])
    rw [hP, hPpow, neg_neg, WithZero.exp_le_exp] at this
    exact this
  have h2 : m ≤ -t := by
    have := (hiso.le_iff_le (x := r) (y := (q : ℚ) ^ t)).mpr (by rw [hP, hPpow])
    rw [hVr, hVpow, WithZero.exp_le_exp] at this
    exact this
  rw [hVr, le_antisymm h2 h1]

end Places

section PlaceDef

open Rat.HeightOneSpectrum

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

variable (q : ℕ) (hq : q.Prime)

local notation "𝔳" => place q hq

theorem primesEquiv_place : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) 𝔳 = ⟨q, hq⟩ := by
  simp [place]

theorem natGenerator_place : Rat.HeightOneSpectrum.natGenerator 𝔳 = q :=
  congrArg Subtype.val (primesEquiv_place q hq)

theorem q_mem_asIdeal_place : (q : 𝓞 ℚ) ∈ (𝔳).asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

end PlaceDef

section LocalBox

variable {D : Type*} [Ring D] [Algebra ℚ D]

theorem tmul_one_mem_localBox {Λ : Submodule ℤ D} {z : D} (hz : z ∈ Λ) (w : HOS) :
    z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w :=
  AddSubgroup.subset_closure ⟨z, hz, 1, (w.adicCompletionIntegers ℚ).one_mem, rfl⟩

theorem gen_mul_mem_localBox (Λ : Submodule ℤ D)
    (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ) (w : HOS)
    {z : D} (hz : z ∈ Λ) {c : w.adicCompletion ℚ} (hc : c ∈ w.adicCompletionIntegers ℚ)
    {y : D ⊗[ℚ] w.adicCompletion ℚ} (hy : y ∈ Submodule.localBox Λ w) :
    (z ⊗ₜ[ℚ] c) * y ∈ Submodule.localBox Λ w := by
  unfold Submodule.localBox at hy ⊢
  refine AddSubgroup.closure_induction (p := fun y _ => (z ⊗ₜ[ℚ] c) * y ∈ _) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z', hz', c', hc', rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure ⟨z * z', hmul z z' hz hz', c * c', mul_mem hc hc', rfl⟩
  · show z ⊗ₜ[ℚ] c * 0 ∈ _
    rw [mul_zero]; exact AddSubgroup.zero_mem _
  · intro x y _ _ hx hy
    rw [mul_add]; exact AddSubgroup.add_mem _ hx hy
  · intro x _ hx
    convert AddSubgroup.neg_mem _ hx using 1
    exact mul_neg (z ⊗ₜ[ℚ] c) x

theorem rat_smul_eq_one_tmul_mul (w : HOS) (q : ℚ) (x : D ⊗[ℚ] w.adicCompletion ℚ) :
    q • x = ((1 : D) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) q)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z s =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

variable (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : 𝕂} (hc : c ∈ 𝓞v) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem one_tmul_mul_mem_localBox {x : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) {c : 𝕂}
    (hc : c ∈ 𝓞v) : ((1 : D) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_mem_localBox Λ v hz (mul_mem hc hc')
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => exact (mul_neg _ x).symm ▸ neg_mem hx

theorem mul_mem_localBox (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    {x y : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
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

omit [Algebra ℚ D] in

theorem one_tmul_comm' {S : Type*} [CommRing S] [Algebra ℚ S] [Algebra ℚ D] (c : S) (x : D ⊗[ℚ] S) :
    ((1 : D) ⊗ₜ[ℚ] c) * x = x * ((1 : D) ⊗ₜ[ℚ] c) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | tmul z d => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

end LocalBox

section Quaternion

variable {a b : ℚ}

theorem mem_iff_forall_tmul_one_mem_localBox (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (z : ℍ[ℚ, a, b]) : z ∈ Λ ↔ ∀ w : HOS, z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ w := by
  have h1 := Submodule.ofFiniteIdele_one Λ hΛ.fg hΛ.spanTop
  constructor
  · intro hz w; exact tmul_one_mem_localBox hz w
  · intro hz
    rw [← h1, Submodule.mem_ofFiniteIdele_iff]
    refine ⟨z ⊗ₜ[ℚ] (1 : 𝔸f), ?_, by simp⟩
    rw [SetLike.mem_coe, Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop]
    intro w
    rw [Submodule.finiteAdeleEvalAt_tmul]
    exact hz w

theorem finiteAdeleEvalAt_tmul_one (w : HOS) (z : ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z ⊗ₜ[ℚ] (1 : 𝔸f)) = z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Submodule.finiteAdeleEvalAt_tmul]; rfl

theorem mem_finiteAdeleBox_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (t : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) :
    t ∈ Submodule.finiteAdeleBox Λ ↔
      ∀ w : HOS, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w t ∈ Submodule.localBox Λ w :=
  Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop t

theorem mem_ofFiniteIdele_iff_forall (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele Λ g ↔
      ∀ w : HOS, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) *
        (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ Submodule.localBox Λ w := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨t, ht, hgt⟩ w
    rw [AddMonoidHom.coe_mulLeft] at hgt
    have ht' : t = ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) := by
      rw [← hgt, Units.inv_mul_cancel_left]
    have := (mem_finiteAdeleBox_iff Λ hΛ t).mp ht w
    rwa [ht', map_mul, finiteAdeleEvalAt_tmul_one] at this
  · intro h
    refine ⟨((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * (z ⊗ₜ[ℚ] (1 : 𝔸f)), ?_, ?_⟩
    · rw [mem_finiteAdeleBox_iff Λ hΛ]
      intro w
      rw [map_mul, finiteAdeleEvalAt_tmul_one]
      exact h w
    · rw [AddMonoidHom.coe_mulLeft, Units.mul_inv_cancel_left]

section RamifiedPlace

open QuaternionAlgebra Rat.HeightOneSpectrum

theorem nrd_mul' {K : Type*} [CommRing K] {α β : K} (x y : ℍ[K, α, β]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]; ring

theorem nrd_smul' {K : Type*} [CommRing K] {α β : K} (c : K) (x : ℍ[K, α, β]) : nrd (c • x) = c ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, nrd_mk, smul_eq_mul]; ring

variable (v : HeightOneSpectrum (𝓞 ℚ))
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])
  (hφ : ∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re, algebraMap ℚ (v.adicCompletion ℚ) z.imI,
        algebraMap ℚ (v.adicCompletion ℚ) z.imJ, algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))

include hφ in
theorem nrd_φ_tmul (z : ℍ[ℚ, a, b]) (c : v.adicCompletion ℚ) :
    nrd (φ (z ⊗ₜ[ℚ] c)) = c ^ 2 * algebraMap ℚ (v.adicCompletion ℚ) (nrd z) := by
  rw [hφ, nrd_smul']
  congr 1
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  simp only [nrd_mk, map_add, map_sub, map_mul, map_pow]

include hφ in
theorem nrd_φ_one_tmul (c : v.adicCompletion ℚ) : nrd (φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c)) = c ^ 2 := by
  rw [nrd_φ_tmul v φ hφ, nrd_one, map_one, mul_one]

theorem nrd_φ_mul (x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : nrd (φ (x * y)) = nrd (φ x) * nrd (φ y) := by
  rw [map_mul, nrd_mul']

abbrev VN (y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : WithZero (Multiplicative ℤ) := Valued.v (nrd (φ y))

theorem VN_mul (x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) : VN v φ (x * y) = VN v φ x * VN v φ y := by
  rw [VN, nrd_φ_mul, map_mul]

theorem VN_one : VN v φ 1 = 1 := by
  rw [VN, map_one, nrd_one, map_one]

theorem VN_units_ne_zero (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : VN v φ (u : _) ≠ 0 := by
  have h : VN v φ (u : _) * VN v φ ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = 1 := by
    rw [← VN_mul, Units.mul_inv, VN_one]
  exact left_ne_zero_of_mul_eq_one h

theorem VN_units_inv (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    VN v φ ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = (VN v φ (u : _))⁻¹ := by
  have h : VN v φ (u : _) * VN v φ ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) = 1 := by
    rw [← VN_mul, Units.mul_inv, VN_one]
  exact (eq_inv_of_mul_eq_one_right h)

include hφ in
theorem VN_one_tmul (c : v.adicCompletion ℚ) : VN v φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) = (Valued.v c) ^ 2 := by
  rw [VN, nrd_φ_one_tmul v φ hφ, map_pow]

include hφ in

theorem VN_tmul_one {q : ℕ} [Fact q.Prime] (hvq : natGenerator v = q) (z : ℍ[ℚ, a, b]) (hz : nrd z ≠ 0) :
    VN v φ (z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = WithZero.exp (-padicValRat q (nrd z)) := by
  rw [VN, nrd_φ_tmul v φ hφ, one_pow, one_mul, valued_algebraMap, valuation_eq_exp_neg_padicValRat v hvq _ hz]

include hφ in
theorem VN_one_tmul_algebraMap (r : ℚ) : VN v φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) r) =
    (v.valuation ℚ r) ^ 2 := by
  rw [VN_one_tmul v φ hφ, valued_algebraMap]

end RamifiedPlace

theorem nrd_ne_zero_of_ne_zero (ha : a < 0) (hb : b < 0) {h : ℍ[ℚ, a, b]} (h0 : h ≠ 0) :
    QuaternionAlgebra.nrd h ≠ 0 := by
  intro hn
  apply h0
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h
  simp only [QuaternionAlgebra.nrd_mk] at hn
  have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  have s0 := sq_nonneg h₀
  have s1 : 0 ≤ -a * h₁ ^ 2 := mul_nonneg (by linarith) (sq_nonneg h₁)
  have s2 : 0 ≤ -b * h₂ ^ 2 := mul_nonneg (by linarith) (sq_nonneg h₂)
  have s3 : 0 ≤ a * b * h₃ ^ 2 := mul_nonneg hab.le (sq_nonneg h₃)
  have e0 : h₀ ^ 2 = 0 := by linarith
  have e1 : -a * h₁ ^ 2 = 0 := by linarith
  have e2 : -b * h₂ ^ 2 = 0 := by linarith
  have e3 : a * b * h₃ ^ 2 = 0 := by linarith
  have f0 : h₀ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e0
  have f1 : h₁ = 0 := by
    rcases mul_eq_zero.mp e1 with h | h
    · linarith
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  have f2 : h₂ = 0 := by
    rcases mul_eq_zero.mp e2 with h | h
    · linarith
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  have f3 : h₃ = 0 := by
    rcases mul_eq_zero.mp e3 with h | h
    · linarith
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  subst f0; subst f1; subst f2; subst f3
  rfl

theorem natCast_tmul_one {S : Type*} [CommRing S] [Algebra ℚ S] (M : ℕ) :
    ((M : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : S)) = ((M : ℕ) : ℍ[ℚ, a, b] ⊗[ℚ] S) := by
  rw [Algebra.TensorProduct.natCast_def]

theorem star_mem_of_isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {t : ℍ[ℚ, a, b]}
    (ht : t ∈ Λ) : star t ∈ Λ := by
  obtain ⟨-, tt, htt⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ ht
  have h1 : star t = ((QuaternionAlgebra.trd t : ℚ) : ℍ[ℚ, a, b]) - t := by
    rw [← QuaternionAlgebra.add_star_eq_coe_trd t]; abel
  have h2 : ((tt : ℤ) : ℍ[ℚ, a, b]) = ((tt : ℚ) : ℍ[ℚ, a, b]) := by ext <;> simp
  rw [h1, ← htt, ← h2, ← zsmul_one]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hΛ.one_mem) ht

section Main

open QuaternionAlgebra Rat.HeightOneSpectrum

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem tmul_one_mul_tmul_one {S : Type*} [CommRing S] [Algebra ℚ S] (z t : ℍ[ℚ, a, b]) :
    (z ⊗ₜ[ℚ] (1 : S)) * (t ⊗ₜ[ℚ] (1 : S)) = (z * t) ⊗ₜ[ℚ] (1 : S) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem smul_tmul_one {S : Type*} [CommRing S] [Algebra ℚ S] (r : ℚ) (z : ℍ[ℚ, a, b]) :
    ((r • z) ⊗ₜ[ℚ] (1 : S)) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ S r) * (z ⊗ₜ[ℚ] (1 : S)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.smul_tmul]

theorem main (q' : ℕ) [hq : Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (π : (ℍ𝔸)ˣ)
    (hπv : ∀ w : HOS, ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (π : ℍ𝔸) = 1)
    (hπP : ∀ h : ℍ[ℚ, a, b], h ∈ Submodule.ofFiniteIdele Λ π ↔
      h ∈ Λ ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h)))
    (x : (ℍ𝔸)ˣ) :
    Submodule.ofFiniteIdele Λ (x * π) = Submodule.ofFiniteIdele Λ x * Submodule.ofFiniteIdele Λ π ∧
    (∀ z : ℍ[ℚ, a, b], z ∈ Submodule.ofFiniteIdele Λ (x * π * π) ↔
      ∃ y ∈ Submodule.ofFiniteIdele Λ x, z = (q' : ℚ) • y) := by
  classical
  have hqp : q'.Prime := hq.out
  have hq0 : (q' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqp.ne_zero
  have hq1 : 1 < q' := hqp.one_lt
  have hO : IsOrder Λ := hΛ.1
  have ha : a < 0 := hdef.1
  have hb : b < 0 := hdef.2.1
  have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ → y ∈ Λ → x * y ∈ Λ := fun _ _ h1 h2 => hO.mul_mem h1 h2

  set v : HOS := place q' hqp with hvdef
  have hvq : natGenerator v = q' := natGenerator_place q' hqp
  have hqv : (q' : 𝓞 ℚ) ∈ v.asIdeal := q_mem_asIdeal_place q' hqp
  set K := v.adicCompletion ℚ with hK
  have hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] K, y ≠ 0 → IsUnit y := (hdef.2.2 v).mpr hqv

  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := K) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ K a) (d₂ := (0 : K)) (d₃ := algebraMap ℚ K b) rfl (map_zero _) rfl AlgEquiv.refl
  have hφ' : ∀ (z : ℍ[ℚ, a, b]) (r : K),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ K z.re, algebraMap ℚ K z.imI, algebraMap ℚ K z.imJ, algebraMap ℚ K z.imK⟩ :
          ℍ[K, algebraMap ℚ K a, algebraMap ℚ K b]) :=
    fun z r => by rw [hφ]; simp only [AlgEquiv.coe_refl, id_eq]
  have hVle : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] K, y ∈ Submodule.localBox Λ v ↔ VN v φ y ≤ 1 := fun y => by
    rw [hΛ.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit v hdiv φ hφ' y,
      HeightOneSpectrum.mem_adicCompletionIntegers]

  have hVq : Valued.v (algebraMap ℚ K (q' : ℚ)) = WithZero.exp (-1 : ℤ) := by
    rw [valued_algebraMap, valuation_eq_exp_neg_padicValRat v hvq _ hq0, padicValRat.self hq1]
  have hVqi : Valued.v (algebraMap ℚ K (q' : ℚ)⁻¹) = WithZero.exp (1 : ℤ) := by
    rw [map_inv₀, map_inv₀, hVq, ← WithZero.exp_neg, neg_neg]
  have hVNq : VN v φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ K (q' : ℚ)) = WithZero.exp (-2 : ℤ) := by
    rw [VN_one_tmul v φ hφ', hVq, pow_two, ← WithZero.exp_add]; rfl
  have hVNqi : VN v φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ K (q' : ℚ)⁻¹) = WithZero.exp (2 : ℤ) := by
    rw [VN_one_tmul v φ hφ', hVqi, pow_two, ← WithZero.exp_add]; rfl
  have hqw : ∀ w : HOS, w ≠ v → algebraMap ℚ (w.adicCompletion ℚ) (q' : ℚ) ∈ w.adicCompletionIntegers ℚ ∧
      algebraMap ℚ (w.adicCompletion ℚ) (q' : ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := fun w hw => by
    have hn := natCast_notMem_of_ne hqp hqv hw
    rw [map_inv₀, map_natCast]
    exact ⟨natCast_mem_integers w q', natCast_inv_mem_integers w hn⟩

  set E : ∀ w : HOS, ℍ𝔸 →ₐ[ℚ] ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ := fun w => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
    with hE
  have hπw : ∀ w : HOS, w ≠ v → E w (π : ℍ𝔸) = 1 := fun w hw => hπv w (natCast_notMem_of_ne hqp hqv hw)
  have hπiw : ∀ w : HOS, w ≠ v → E w ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = 1 := fun w hw => by
    have h1 : E w ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * E w (π : ℍ𝔸) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    rwa [hπw w hw, mul_one] at h1
  set pv := E v (π : ℍ𝔸) with hpv
  set piv := E v ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) with hpiv
  have hpp : pv * piv = 1 := by rw [hpv, hpiv, ← map_mul, Units.mul_inv, map_one]
  have hpp' : piv * pv = 1 := by rw [hpv, hpiv, ← map_mul, Units.inv_mul, map_one]
  have hVprod : VN v φ pv * VN v φ piv = 1 := by rw [← VN_mul, hpp, VN_one]
  have hVpv0 : VN v φ pv ≠ 0 := left_ne_zero_of_mul_eq_one hVprod
  have hVpiv : VN v φ piv = (VN v φ pv)⁻¹ := eq_inv_of_mul_eq_one_right hVprod

  have memL : ∀ (g : (ℍ𝔸)ˣ) (z : ℍ[ℚ, a, b]), z ∈ Submodule.ofFiniteIdele Λ g ↔
      ∀ w : HOS, E w ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ Submodule.localBox Λ w :=
    fun g z => mem_ofFiniteIdele_iff_forall Λ hO g z

  have hVNz : ∀ z : ℍ[ℚ, a, b], z ≠ 0 → VN v φ (z ⊗ₜ[ℚ] (1 : K)) = WithZero.exp (-padicValRat q' (nrd z)) :=
    fun z hz => VN_tmul_one v φ hφ' hvq z (nrd_ne_zero_of_ne_zero ha hb hz)

  obtain ⟨k, hk⟩ : ∃ k : ℤ, VN v φ pv = WithZero.exp k := ⟨WithZero.log _, (WithZero.exp_log hVpv0).symm⟩
  obtain ⟨h₀, hh₀Λ, hh₀0, hh₀v⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_mem_padicValRat_nrd_eq_one_of_isDefiniteRamifiedExactlyAt q' hdef Λ hΛ
  have hh₀L : h₀ ∈ Submodule.ofFiniteIdele Λ π := (hπP h₀).mpr ⟨hh₀Λ, Or.inr (by rw [hh₀v])⟩
  have hVh₀ : VN v φ (h₀ ⊗ₜ[ℚ] (1 : K)) = WithZero.exp (-1 : ℤ) := by rw [hVNz h₀ hh₀0, hh₀v]
  have hk1 : -1 ≤ k := by
    have h1 : piv * (h₀ ⊗ₜ[ℚ] (1 : K)) ∈ Submodule.localBox Λ v := (memL π h₀).mp hh₀L v
    rw [hVle, VN_mul, hVpiv, hk, hVh₀, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h1
    omega
  have hk2 : k < 0 := by
    have h1notin : (1 : ℍ[ℚ, a, b]) ∉ Submodule.ofFiniteIdele Λ π := by
      intro h
      obtain ⟨-, hc⟩ := (hπP 1).mp h
      rcases hc with h0 | h1
      · exact one_ne_zero h0
      · rw [nrd_one, padicValRat.one] at h1
        exact absurd h1 (by norm_num)
    have h2 : ¬ piv ∈ Submodule.localBox Λ v := by
      intro hmem
      apply h1notin
      rw [memL π 1]
      intro w
      by_cases hw : w = v
      · subst hw
        rw [← Algebra.TensorProduct.one_def, mul_one]
        exact hmem
      · rw [hπiw w hw, one_mul]
        exact tmul_one_mem_localBox hO.one_mem w
    rw [hVle, hVpiv, hk, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp, not_le] at h2
    omega
  have hkv : k = -1 := by omega
  have hVpvv : VN v φ pv = WithZero.exp (-1 : ℤ) := by rw [hk, hkv]
  have hVpivv : VN v φ piv = WithZero.exp (1 : ℤ) := by rw [hVpiv, hVpvv, ← WithZero.exp_neg, neg_neg]

  have rd : ∀ (g : (ℍ𝔸)ˣ) (z : ℍ[ℚ, a, b]), z ∈ Submodule.ofFiniteIdele Λ g →
      ∀ w : HOS, E w ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) ∈ Submodule.localBox Λ w :=
    fun g z hz => (memL g z).mp hz

  have inv_xπ : (((x * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
    rw [mul_inv_rev, Units.val_mul]
  have inv_xππ : (((x * π * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
      ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
    rw [mul_inv_rev, mul_inv_rev, Units.val_mul, Units.val_mul, mul_assoc]
  have x_inv_eq : ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (π : ℍ𝔸) * (((x * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
    rw [inv_xπ, ← mul_assoc, Units.mul_inv, one_mul]
  have x_inv_eq2 : ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (π : ℍ𝔸) * (π : ℍ𝔸) * (((x * π * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
    rw [inv_xππ, show (π : ℍ𝔸) * (π : ℍ𝔸) * (((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))
      = (π : ℍ𝔸) * ((π : ℍ𝔸) * ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) by
        simp only [mul_assoc], Units.mul_inv, mul_one, Units.mul_inv, one_mul]

  have hLxπ_le : ∀ z ∈ Submodule.ofFiniteIdele Λ (x * π), z ∈ Submodule.ofFiniteIdele Λ x := by
    intro z hz
    rw [memL x z]
    intro w
    have hC := rd (x * π) z hz w
    rw [x_inv_eq, map_mul, mul_assoc]
    by_cases hw : w = v
    · subst hw
      rw [hVle, VN_mul, hVpvv]
      rw [hVle] at hC
      calc WithZero.exp (-1 : ℤ) * VN v φ (E v (((x * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : K)))
          ≤ 1 * 1 := mul_le_mul' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num) hC
        _ = 1 := mul_one 1
    · rw [hπw w hw, one_mul]
      exact hC

  have hqΛ : (q' : ℍ[ℚ, a, b]) ∈ Λ := by
    have h1 : (q' : ℍ[ℚ, a, b]) = (q' : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one, Int.cast_natCast]
    rw [h1]; exact Submodule.smul_mem _ _ hO.one_mem
  have hqL : (q' : ℍ[ℚ, a, b]) ∈ Submodule.ofFiniteIdele Λ π := by
    refine (hπP _).mpr ⟨hqΛ, Or.inr ?_⟩
    rw [← QuaternionAlgebra.coe_natCast, nrd_coe, padicValRat.pow _, padicValRat.self hq1]
    norm_num

  have hsup : Submodule.ofFiniteIdele Λ x * Submodule.ofFiniteIdele Λ π ≤ Submodule.ofFiniteIdele Λ (x * π) := by
    rw [Submodule.mul_le]
    intro s hs t ht
    rw [memL (x * π) (s * t)]
    intro w
    have hA := rd x s hs w
    have hB := rd π t ht w
    rw [inv_xπ, ← tmul_one_mul_tmul_one, map_mul, show
      E w ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * E w ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) *
          (s ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) * t ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) =
        E w ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((E w ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * s ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) *
          t ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) by simp only [mul_assoc]]
    by_cases hw : w = v
    · subst hw
      rw [hVle, VN_mul, VN_mul, hVpivv]
      rw [hVle] at hA hB
      rw [VN_mul, hVpivv] at hB

      calc WithZero.exp (1 : ℤ) * (VN v φ (E v ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * s ⊗ₜ[ℚ] (1 : K)) * VN v φ (t ⊗ₜ[ℚ] (1 : K)))
          = VN v φ (E v ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * s ⊗ₜ[ℚ] (1 : K)) * (WithZero.exp (1 : ℤ) * VN v φ (t ⊗ₜ[ℚ] (1 : K))) :=
            mul_left_comm _ _ _
        _ ≤ 1 * 1 := mul_le_mul' hA hB
        _ = 1 := mul_one 1
    · rw [hπiw w hw, one_mul]
      exact mul_mem_localBox Λ w hmul hA (tmul_one_mem_localBox ((hπP t).mp ht).1 w)

  obtain ⟨⟨N₀, hN₀⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hO hh₀Λ
  have hN₀0 : N₀ ≠ 0 := by
    intro h0; apply nrd_ne_zero_of_ne_zero ha hb hh₀0; rw [← hN₀, h0, Int.cast_zero]
  have hvalN : padicValInt q' N₀ = 1 := by
    have := hh₀v; rw [← hN₀, padicValRat.of_int] at this; exact_mod_cast this
  have hdvd : (q' : ℤ) ∣ N₀ := by
    have := (padicValInt_dvd_iff 1 N₀).mpr (Or.inr (by rw [hvalN])); rwa [pow_one] at this
  obtain ⟨c₀, hc₀⟩ := hdvd
  have hndvd : ¬ (q' : ℤ) ∣ c₀ := by
    rintro ⟨c₁, rfl⟩
    have h2 : (q' : ℤ) ^ 2 ∣ N₀ := ⟨c₁, by rw [hc₀]; ring⟩
    rcases (padicValInt_dvd_iff 2 N₀).mp h2 with h | h
    · exact hN₀0 h
    · rw [hvalN] at h; norm_num at h
  have hcop : IsCoprime c₀ (q' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Nat.Coprime q' c₀.natAbs := (Nat.Prime.coprime_iff_not_dvd hqp).mpr (by
      intro h; exact hndvd (Int.natCast_dvd.mpr h))
    rw [Int.gcd_comm]
    exact h1
  obtain ⟨α, β, hαβ⟩ := hcop
  have hstar : star h₀ ∈ Λ := star_mem_of_isOrder hO hh₀Λ
  have hVsh₀ : VN v φ (star h₀ ⊗ₜ[ℚ] (1 : K)) = WithZero.exp (-1 : ℤ) := by
    rw [hVNz (star h₀) (by rwa [ne_eq, star_eq_zero]), nrd_star, hh₀v]
  have hsub : ∀ z ∈ Submodule.ofFiniteIdele Λ (x * π), z ∈ Submodule.ofFiniteIdele Λ x * Submodule.ofFiniteIdele Λ π := by
    intro z hz
    have hzx : z ∈ Submodule.ofFiniteIdele Λ x := hLxπ_le z hz

    set y : ℍ[ℚ, a, b] := (q' : ℚ)⁻¹ • (z * star h₀) with hy
    have hyL : y ∈ Submodule.ofFiniteIdele Λ x := by
      rw [memL x y]
      intro w
      have hC := rd (x * π) z hz w
      rw [hy, smul_tmul_one, ← tmul_one_mul_tmul_one, ← mul_assoc, ← one_tmul_comm', mul_assoc, x_inv_eq, map_mul,
        show E w (π : ℍ𝔸) * E w (((x * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) *
            (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) * star h₀ ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) =
          E w (π : ℍ𝔸) * ((E w (((x * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) *
            star h₀ ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) by simp only [mul_assoc]]
      by_cases hw : w = v
      · subst hw
        rw [hVle, VN_mul, VN_mul, VN_mul, hVNqi, hVpvv, hVsh₀]
        rw [hVle] at hC
        calc WithZero.exp (2 : ℤ) * (WithZero.exp (-1 : ℤ) *
              (VN v φ (E v (((x * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * z ⊗ₜ[ℚ] (1 : K)) * WithZero.exp (-1 : ℤ)))
            = VN v φ (E v (((x * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * z ⊗ₜ[ℚ] (1 : K)) := by
              rw [mul_comm (VN v φ _) (WithZero.exp (-1 : ℤ))]
              simp only [← mul_assoc, ← WithZero.exp_add]
              norm_num
          _ ≤ 1 := hC
      · rw [hπw w hw, one_mul]
        exact one_tmul_mul_mem_localBox Λ w
          (mul_mem_localBox Λ w hmul hC (tmul_one_mem_localBox hstar w)) (hqw w hw).2

    have hyh₀ : y * h₀ = (c₀ : ℤ) • z := by
      rw [hy, smul_mul_assoc, mul_assoc, star_mul_eq_coe_nrd, ← hN₀, hc₀, ← QuaternionAlgebra.coe_commutes,
        QuaternionAlgebra.coe_mul_eq_smul, smul_smul, Int.cast_mul, Int.cast_natCast, ← mul_assoc,
        inv_mul_cancel₀ hq0, one_mul, Int.cast_smul_eq_zsmul]

    have h1 : z * (q' : ℍ[ℚ, a, b]) ∈ Submodule.ofFiniteIdele Λ x * Submodule.ofFiniteIdele Λ π :=
      Submodule.mul_mem_mul hzx hqL
    have h2 : y * h₀ ∈ Submodule.ofFiniteIdele Λ x * Submodule.ofFiniteIdele Λ π :=
      Submodule.mul_mem_mul hyL hh₀L
    have hz_eq : z = α • (y * h₀) + β • (z * (q' : ℍ[ℚ, a, b])) := by
      rw [hyh₀, smul_smul, show z * (q' : ℍ[ℚ, a, b]) = ((q' : ℤ)) • z by
        rw [zsmul_eq_mul, Int.cast_natCast, Nat.cast_comm], smul_smul, ← add_smul, hαβ, one_smul]
    rw [hz_eq]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h2) (Submodule.smul_mem _ _ h1)
  refine ⟨le_antisymm (fun z hz => hsub z hz) hsup, fun z => ⟨fun hz => ?_, ?_⟩⟩

  · refine ⟨(q' : ℚ)⁻¹ • z, ?_, by rw [smul_smul, mul_inv_cancel₀ hq0, one_smul]⟩
    rw [memL x]
    intro w
    have hC := rd (x * π * π) z hz w
    rw [smul_tmul_one, ← mul_assoc, ← one_tmul_comm', mul_assoc, x_inv_eq2, map_mul, map_mul,
      show E w (π : ℍ𝔸) * E w (π : ℍ𝔸) * E w (((x * π * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) =
        E w (π : ℍ𝔸) * E w (π : ℍ𝔸) * (E w (((x * π * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) by
          simp only [mul_assoc]]
    by_cases hw : w = v
    · subst hw
      rw [hVle, VN_mul, VN_mul, VN_mul, hVNqi, hVpvv]
      rw [hVle] at hC
      calc WithZero.exp (2 : ℤ) * (WithZero.exp (-1 : ℤ) * WithZero.exp (-1 : ℤ) *
            VN v φ (E v (((x * π * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * z ⊗ₜ[ℚ] (1 : K)))
          = VN v φ (E v (((x * π * π)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * z ⊗ₜ[ℚ] (1 : K)) := by
            rw [← mul_assoc, ← WithZero.exp_add, ← WithZero.exp_add]; norm_num
        _ ≤ 1 := hC
    · rw [hπw w hw, one_mul, one_mul]
      exact one_tmul_mul_mem_localBox Λ w hC (hqw w hw).2

  · rintro ⟨y, hy, rfl⟩
    rw [memL (x * π * π)]
    intro w
    have hC := rd x y hy w
    rw [smul_tmul_one, ← mul_assoc, ← one_tmul_comm', mul_assoc, inv_xππ, map_mul, map_mul,
      show E w ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * E w ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * E w ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) *
          y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) =
        E w ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * E w ((π⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) *
          (E w ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) by simp only [mul_assoc]]
    by_cases hw : w = v
    · subst hw
      rw [hVle, VN_mul, VN_mul, VN_mul, hVNq, hVpivv]
      rw [hVle] at hC
      calc WithZero.exp (-2 : ℤ) * (WithZero.exp (1 : ℤ) * WithZero.exp (1 : ℤ) *
            VN v φ (E v ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y ⊗ₜ[ℚ] (1 : K)))
          = VN v φ (E v ((x⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y ⊗ₜ[ℚ] (1 : K)) := by
            rw [← mul_assoc, ← WithZero.exp_add, ← WithZero.exp_add]; norm_num
        _ ≤ 1 := hC
    · rw [hπiw w hw, one_mul, one_mul]
      exact one_tmul_mul_mem_localBox Λ w hC (hqw w hw).1

end Main

end Quaternion

end RamShift

open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra

theorem solution
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (π : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hπv : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ((q' : ℕ) : 𝓞 ℚ) ∉ w.asIdeal →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
        (π : ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (hπP : ∀ h : ℍ[ℚ, a, b], h ∈ Submodule.ofFiniteIdele Λ π ↔
      h ∈ Λ ∧ (h = 0 ∨ 1 ≤ padicValRat q' (QuaternionAlgebra.nrd h)))
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Submodule.ofFiniteIdele Λ (x * π) = Submodule.ofFiniteIdele Λ x * Submodule.ofFiniteIdele Λ π ∧
    (∀ z : ℍ[ℚ, a, b], z ∈ Submodule.ofFiniteIdele Λ (x * π * π) ↔
      ∃ y ∈ Submodule.ofFiniteIdele Λ x, z = (q' : ℚ) • y) :=
  RamShift.main q' hdef Λ hΛ π hπv hπP x

end
end S_QuaternionAlgebra_IsMaximalOrder_ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_ofFiniteIdele_mul_eq_mul_and_mem_ofFiniteIdele_mul_mul_iff_of_isDefiniteRamifiedExactlyAt (solution)
