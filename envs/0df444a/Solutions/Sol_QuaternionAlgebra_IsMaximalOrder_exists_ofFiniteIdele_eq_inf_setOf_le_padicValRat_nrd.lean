-- Prove2me | solution 1 for QuaternionAlgebra.IsMaximalOrder.exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/5c3201f6-50c2-5487-b4fa-168afb4c60f4

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_WeierstrassCurve_RationalEnd
import Definitions.Def_WeierstrassCurve_KernelIdeal
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_Submodule_finiteAdeleBox_ofFiniteIdele
import Theorems.Thm_Submodule_exists_ne_zero_natCast_smul_mem_finiteAdeleBox
import Theorems.Thm_Submodule_exists_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_eventually_finiteAdeleEvalAt_mem_localBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct Quaternion NumberField Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace K3cSplit

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

theorem mul_mem_finiteAdeleBox_of_le (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (hx : Submodule.ofFiniteIdele Λ x ≤ Λ)
    {t : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f} (ht : t ∈ Submodule.finiteAdeleBox Λ) :
    (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * t ∈ Submodule.finiteAdeleBox Λ := by
  have h1 := Submodule.finiteAdeleBox_ofFiniteIdele Λ hΛ.fg hΛ.spanTop x
  have h2 : Submodule.finiteAdeleBox (Submodule.ofFiniteIdele Λ x) ≤ Submodule.finiteAdeleBox Λ :=
    AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, h⟩ => ⟨z, hx hz, c, hc, h⟩
  have h3 : (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * t ∈
      (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) := ⟨t, ht, rfl⟩
  rw [← h1] at h3
  exact h2 h3

theorem exists_mem_finiteAdeleBox_finiteAdeleEvalAt_eq (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HOS) {y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ}
    (hy : y ∈ Submodule.localBox Λ w) :
    ∃ t ∈ Submodule.finiteAdeleBox Λ, Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w t = y := by
  classical
  let c : ∀ w' : HOS, ℍ[ℚ, a, b] ⊗[ℚ] w'.adicCompletion ℚ :=
    Function.update (fun w' => (0 : ℍ[ℚ, a, b] ⊗[ℚ] w'.adicCompletion ℚ)) w y
  have hc : ∀ w', c w' ∈ Submodule.localBox Λ w' := fun w' => by
    by_cases h : w' = w
    · subst h; simp only [c, Function.update_self]; exact hy
    · simp only [c, Function.update_of_ne h]; exact zero_mem _
  obtain ⟨t, ht⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq Λ hΛ.fg hΛ.spanTop c
    (Filter.Eventually.of_forall hc)
  refine ⟨t, (mem_finiteAdeleBox_iff Λ hΛ t).mpr fun w' => by rw [ht]; exact hc w', ?_⟩
  rw [ht]; simp only [c, Function.update_self]

theorem finiteAdeleEvalAt_mul_mem_localBox (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (hx : Submodule.ofFiniteIdele Λ x ≤ Λ) (w : HOS)
    {y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ} (hy : y ∈ Submodule.localBox Λ w) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * y ∈ Submodule.localBox Λ w := by
  obtain ⟨t, ht, rfl⟩ := exists_mem_finiteAdeleBox_finiteAdeleEvalAt_eq Λ hΛ w hy
  rw [← map_mul]
  exact (mem_finiteAdeleBox_iff Λ hΛ _).mp (mul_mem_finiteAdeleBox_of_le Λ hΛ x hx ht) w

theorem exists_units_finiteAdeleEvalAt_eq_one (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) (v : HOS) :
    ∃ x₀ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ,
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (x₀ : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 ∧
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((x₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 ∧
      ∀ w : HOS, w ≠ v →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x₀ : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∧
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((x₀⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) := by
  classical
  let E := fun (w : HOS) => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
  let c : ∀ w : HOS, ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
    Function.update (fun w => E w (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) v 1
  let d : ∀ w : HOS, ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
    Function.update (fun w => E w ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) v 1
  have hcv : c v = 1 := by simp only [c, Function.update_self]
  have hdv : d v = 1 := by simp only [d, Function.update_self]
  have hcw : ∀ w, w ≠ v → c w = E w (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) := fun w hw => by
    simp only [c, Function.update_of_ne hw]
  have hdw : ∀ w, w ≠ v → d w = E w ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) := fun w hw => by
    simp only [d, Function.update_of_ne hw]
  have h1v : (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
    rw [Algebra.TensorProduct.one_def]; exact tmul_one_mem_localBox hΛ.one_mem v
  have hc : ∀ᶠ w in Filter.cofinite, c w ∈ Submodule.localBox Λ w :=
    (Submodule.eventually_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop (x : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)).mono
      fun w hw => by
        by_cases h : w = v
        · subst h; rw [hcv]; exact h1v
        · rw [hcw w h]; exact hw
  have hd : ∀ᶠ w in Filter.cofinite, d w ∈ Submodule.localBox Λ w :=
    (Submodule.eventually_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop
      ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)).mono fun w hw => by
        by_cases h : w = v
        · subst h; rw [hdv]; exact h1v
        · rw [hdw w h]; exact hw
  obtain ⟨y₀, hy₀⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq Λ hΛ.fg hΛ.spanTop c hc
  obtain ⟨y₁, hy₁⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq Λ hΛ.fg hΛ.spanTop d hd
  have hcd : ∀ w, c w * d w = 1 := fun w => by
    by_cases h : w = v
    · subst h; rw [hcv, hdv, mul_one]
    · rw [hcw w h, hdw w h, ← map_mul, Units.mul_inv, map_one]
  have hdc : ∀ w, d w * c w = 1 := fun w => by
    by_cases h : w = v
    · subst h; rw [hcv, hdv, mul_one]
    · rw [hcw w h, hdw w h, ← map_mul, Units.inv_mul, map_one]
  have h01 : y₀ * y₁ = 1 :=
    Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun w => by rw [map_mul, hy₀, hy₁, hcd, map_one]
  have h10 : y₁ * y₀ = 1 :=
    Submodule.eq_of_forall_finiteAdeleEvalAt_eq _ _ fun w => by rw [map_mul, hy₀, hy₁, hdc, map_one]
  refine ⟨⟨y₀, y₁, h01, h10⟩, ?_, ?_, fun w hw => ⟨?_, ?_⟩⟩
  · show E v y₀ = 1
    rw [hy₀, hcv]
  · show E v y₁ = 1
    rw [hy₁, hdv]
  · show E w y₀ = _
    rw [hy₀, hcw w hw]
  · show E w y₁ = _
    rw [hy₁, hdw w hw]

section RamifiedPlace

open QuaternionAlgebra Rat.HeightOneSpectrum

variable (v : HOS)
variable (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+*
      ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b])
  (hφ : ∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re, algebraMap ℚ (v.adicCompletion ℚ) z.imI,
        algebraMap ℚ (v.adicCompletion ℚ) z.imJ, algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]))

theorem nrd_mul' {K : Type*} [CommRing K] {α β : K} (x y : ℍ[K, α, β]) : nrd (x * y) = nrd x * nrd y := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x; obtain ⟨y₀, y₁, y₂, y₃⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, nrd_mk]; ring

theorem nrd_smul' {K : Type*} [CommRing K] {α β : K} (c : K) (x : ℍ[K, α, β]) : nrd (c • x) = c ^ 2 * nrd x := by
  obtain ⟨x₀, x₁, x₂, x₃⟩ := x
  simp only [QuaternionAlgebra.smul_mk, nrd_mk, smul_eq_mul]; ring

include hφ in
theorem nrd_φ_tmul (z : ℍ[ℚ, a, b]) (c : v.adicCompletion ℚ) :
    nrd (φ (z ⊗ₜ[ℚ] c)) = c ^ 2 * algebraMap ℚ (v.adicCompletion ℚ) (nrd z) := by
  rw [hφ, nrd_smul']
  congr 1
  obtain ⟨z₀, z₁, z₂, z₃⟩ := z
  simp only [nrd_mk, map_add, map_sub, map_mul, map_pow]

include hφ in

theorem exists_nat_forall_nrd_mem_iff {q : ℕ} [Fact q.Prime] (hvq : natGenerator v = q)
    (u u' : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (huu' : u * u' = 1)
    (hu : nrd (φ u) ∈ v.adicCompletionIntegers ℚ) :
    ∃ k : ℕ, ∀ h : ℍ[ℚ, a, b], nrd h ≠ 0 →
      (nrd (φ (u' * (h ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)))) ∈ v.adicCompletionIntegers ℚ ↔
        (k : ℤ) ≤ padicValRat q (nrd h)) := by

  have hprod : Valued.v (nrd (φ u)) * Valued.v (nrd (φ u')) = 1 := by
    rw [← map_mul, ← nrd_mul', ← map_mul, huu', map_one, nrd_one, map_one]
  have hν0 : Valued.v (nrd (φ u)) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  set n := WithZero.log (Valued.v (nrd (φ u))) with hn
  have hνn : Valued.v (nrd (φ u)) = WithZero.exp n := (WithZero.exp_log hν0).symm
  have hn0 : n ≤ 0 := by
    have h1 : Valued.v (nrd (φ u)) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 ℚ) ℚ v).mp hu
    rw [hνn, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact h1
  have hν' : Valued.v (nrd (φ u')) = WithZero.exp (-n) := by
    rw [WithZero.exp_neg, ← hνn]
    exact eq_inv_of_mul_eq_one_right hprod
  refine ⟨(-n).toNat, fun h hh => ?_⟩
  have hk : (((-n).toNat : ℕ) : ℤ) = -n := Int.toNat_of_nonneg (by omega)
  have hval : v.valuation ℚ (nrd h) = WithZero.exp (-padicValRat q (nrd h)) :=
    valuation_eq_exp_neg_padicValRat v hvq (nrd h) hh
  rw [map_mul, nrd_mul', nrd_φ_tmul v φ hφ, one_pow, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers,
    map_mul, hν', valued_algebraMap, hval, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp, hk]
  omega

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

end Quaternion

end K3cSplit

end

open K3cSplit in
theorem solution
    {a b : ℚ} (q' : ℕ) [Fact q'.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hx : Submodule.ofFiniteIdele Λ x ≤ Λ) :
    ∃ (k : ℕ) (x₀ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ),
      Submodule.ofFiniteIdele Λ x₀ ≤ Λ ∧
      (∃ h ∈ Submodule.ofFiniteIdele Λ x₀, padicValRat q' (QuaternionAlgebra.nrd h) = 0 ∧ h ≠ 0) ∧
      (Submodule.ofFiniteIdele Λ x : Set ℍ[ℚ, a, b]) =
        (Submodule.ofFiniteIdele Λ x₀ : Set ℍ[ℚ, a, b]) ∩
          {h | h ∈ Λ ∧ (h = 0 ∨ (k : ℤ) ≤ padicValRat q' (QuaternionAlgebra.nrd h))} := by
  classical
  have hq : q'.Prime := Fact.out
  have hord : QuaternionAlgebra.IsOrder Λ := hΛ.1

  let E := fun (w : HeightOneSpectrum (𝓞 ℚ)) => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w

  let v : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q', hq⟩
  have hpv : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v = ⟨q', hq⟩ := Equiv.apply_symm_apply _ _
  have hvq : Rat.HeightOneSpectrum.natGenerator v = q' := congrArg Subtype.val hpv
  have hqv : (q' : 𝓞 ℚ) ∈ v.asIdeal := by rw [natCast_mem_asIdeal_iff, hvq]
  have hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y := (hdef.2.2 v).mpr hqv

  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := v.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (v.adicCompletion ℚ) a) (d₂ := (0 : v.adicCompletion ℚ))
    (d₃ := algebraMap ℚ (v.adicCompletion ℚ) b) rfl (map_zero _) rfl AlgEquiv.refl
  have hφ' : ∀ (z : ℍ[ℚ, a, b]) (r : v.adicCompletion ℚ),
      φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (v.adicCompletion ℚ) z.re, algebraMap ℚ (v.adicCompletion ℚ) z.imI,
        algebraMap ℚ (v.adicCompletion ℚ) z.imJ, algebraMap ℚ (v.adicCompletion ℚ) z.imK⟩ :
          ℍ[v.adicCompletion ℚ, algebraMap ℚ (v.adicCompletion ℚ) a, algebraMap ℚ (v.adicCompletion ℚ) b]) :=
    fun z r => by rw [hφ]; simp only [AlgEquiv.coe_refl, id_eq]

  have hVal : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ∈ Submodule.localBox Λ v ↔
      QuaternionAlgebra.nrd (φ y) ∈ v.adicCompletionIntegers ℚ := fun y =>
    hΛ.mem_localBox_iff_nrd_mem_adicCompletionIntegers_of_forall_isUnit v hdiv φ hφ' y

  obtain ⟨x₀, hx₀v, hx₀v', hx₀w⟩ := exists_units_finiteAdeleEvalAt_eq_one Λ hord x v

  set u := E v (x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) with hu_def
  set u' := E v ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
    with hu'_def
  have huu' : u * u' = 1 := by rw [hu_def, hu'_def, ← map_mul, Units.mul_inv, map_one]
  have h1v : (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
    rw [Algebra.TensorProduct.one_def]; exact tmul_one_mem_localBox hord.one_mem v
  have hu : u ∈ Submodule.localBox Λ v := by
    have := finiteAdeleEvalAt_mul_mem_localBox Λ hord x hx v h1v
    rwa [mul_one] at this

  obtain ⟨k, hk⟩ := exists_nat_forall_nrd_mem_iff v φ hφ' hvq u u' huu' ((hVal u).mp hu)

  have hkey : ∀ h : ℍ[ℚ, a, b], h ≠ 0 →
      (u' * (h ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) ∈ Submodule.localBox Λ v ↔
        (k : ℤ) ≤ padicValRat q' (QuaternionAlgebra.nrd h)) := fun h hh => by
    rw [hVal]
    exact hk h (nrd_ne_zero_of_ne_zero hdef.neg_left hdef.neg_right hh)

  have hI := mem_ofFiniteIdele_iff_forall Λ hord x
  have hI₀ := mem_ofFiniteIdele_iff_forall Λ hord x₀

  have hI₀Λ : Submodule.ofFiniteIdele Λ x₀ ≤ Λ := by
    intro z hz
    rw [hI₀] at hz
    rw [mem_iff_forall_tmul_one_mem_localBox Λ hord]
    intro w
    by_cases hw : w = v
    · subst hw
      have := hz v
      rwa [hx₀v', one_mul] at this
    · have h1 := hz w
      rw [(hx₀w w hw).2] at h1
      have h2 := finiteAdeleEvalAt_mul_mem_localBox Λ hord x hx w h1
      rwa [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul] at h2

  have hII₀ : Submodule.ofFiniteIdele Λ x ≤ Submodule.ofFiniteIdele Λ x₀ := by
    intro z hz
    have hzΛ : z ∈ Λ := hx hz
    rw [hI] at hz
    rw [hI₀]
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hx₀v', one_mul]
      exact tmul_one_mem_localBox hzΛ v
    · rw [(hx₀w w hw).2]
      exact hz w
  refine ⟨k, x₀, hI₀Λ, ?_, ?_⟩
  ·
    obtain ⟨N, hN0, hN⟩ := Submodule.exists_ne_zero_natCast_smul_mem_finiteAdeleBox Λ hord.spanTop
      ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
    obtain ⟨e, M, hM, hNeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 q' hq.ne_one
    have hM0 : M ≠ 0 := by rintro rfl; rw [mul_zero] at hNeq; exact hN0 hNeq
    refine ⟨(M : ℍ[ℚ, a, b]), ?_, ?_, ?_⟩
    ·
      rw [hI₀]
      intro w
      by_cases hw : w = v
      · subst hw
        rw [hx₀v', one_mul, ← nsmul_one M, ← Nat.cast_smul_eq_nsmul ℤ]
        exact tmul_one_mem_localBox (Submodule.smul_mem _ _ hord.one_mem) _
      · rw [(hx₀w w hw).2, natCast_tmul_one, ← Nat.cast_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ]

        have hNw : (N : ℚ) • E w ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
            ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.localBox Λ w := by
          rw [← map_smul]
          exact (mem_finiteAdeleBox_iff Λ hord _).mp hN w
        have hq'w : (q' : 𝓞 ℚ) ∉ w.asIdeal := natCast_notMem_of_ne hq hqv hw
        have hqinv : ((q' : w.adicCompletion ℚ)⁻¹) ^ e ∈ w.adicCompletionIntegers ℚ :=
          pow_mem (natCast_inv_mem_integers w hq'w) e
        have hq0 : ((q' : ℚ) ^ e) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hq.ne_zero)
        have hMN : (M : ℚ) = ((q' : ℚ) ^ e)⁻¹ * (N : ℚ) := by
          rw [hNeq]; push_cast; field_simp
        rw [hMN, mul_smul, rat_smul_eq_one_tmul_mul w, map_inv₀, map_pow, map_natCast, ← inv_pow]
        exact gen_mul_mem_localBox Λ (fun x y hx hy => hord.mul_mem hx hy) w hord.one_mem hqinv hNw
    ·
      rw [← QuaternionAlgebra.coe_natCast, QuaternionAlgebra.nrd_coe,
        padicValRat.pow _, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hM]
      simp
    ·
      intro hM'
      have := congrArg QuaternionAlgebra.re hM'
      rw [QuaternionAlgebra.re_natCast, QuaternionAlgebra.re_zero] at this
      exact hM0 (Nat.cast_eq_zero.mp this)
  ·
    ext z
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hz
      refine ⟨hII₀ hz, hx hz, ?_⟩
      by_cases hz0 : z = 0
      · exact Or.inl hz0
      · right
        rw [← hkey z hz0]
        rw [hI] at hz
        exact hz v
    · rintro ⟨hz₀, hzΛ, hz⟩
      rcases hz with rfl | hzk
      · exact zero_mem _
      · by_cases hz0 : z = 0
        · rw [hz0]; exact zero_mem _
        rw [hI]
        intro w
        by_cases hw : w = v
        · subst hw
          exact (hkey z hz0).mpr hzk
        · rw [hI₀] at hz₀
          have := hz₀ w
          rwa [(hx₀w w hw).2] at this

end S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd
end P2MW
export P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd (solution)
