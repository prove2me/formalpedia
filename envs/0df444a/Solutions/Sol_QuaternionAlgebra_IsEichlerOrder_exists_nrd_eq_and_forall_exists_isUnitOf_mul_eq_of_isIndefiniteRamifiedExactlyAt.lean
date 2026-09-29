-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9d891465-7530-5daf-a85d-c2749dd90188

import Mathlib
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_not_forall_isUnit
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one_of_forall_isUnit
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul QuaternionAlgebra.ClassSet.map_mk LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

noncomputable section

namespace ALRAMN

section NrdAlgebra

variable {K : Type*} [CommRing K] {c₁ c₃ : K}

theorem nrd_mul' (x y : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (x * y) = QuaternionAlgebra.nrd x * QuaternionAlgebra.nrd y := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.nrd_mk]
  ring

theorem nrd_smul' (r : K) (x : ℍ[K, c₁, c₃]) :
    QuaternionAlgebra.nrd (r • x) = r ^ 2 * QuaternionAlgebra.nrd x := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  simp only [QuaternionAlgebra.smul_mk, QuaternionAlgebra.nrd_mk, smul_eq_mul]
  ring

end NrdAlgebra

section Places

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

def placeOf (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

theorem natGenerator_placeOf (p : ℕ) (hp : p.Prime) :
    Rat.HeightOneSpectrum.natGenerator (placeOf p hp) = p := by
  have := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩
  exact congrArg Subtype.val this

theorem natCast_mem_placeOf (p : ℕ) (hp : p.Prime) : (p : 𝓞 ℚ) ∈ (placeOf p hp).asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_placeOf]

theorem eq_placeOf_of_mem {p : ℕ} (hp : p.Prime) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    w = placeOf p hp := by
  rw [natCast_mem_asIdeal_iff] at hw
  have h1 := (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hp).mp hw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [placeOf, Equiv.apply_symm_apply]
  exact Subtype.ext h1

theorem notMem_of_ne_placeOf {p : ℕ} (hp : p.Prime) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ placeOf p hp) :
    (p : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (eq_placeOf_of_mem hp h)

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem valued_natCast_eq_one_of_notMem (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ)) = 1 := by
  rw [valued_algebraMap, show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 hn

theorem inv_natCast_mem_adicCompletionIntegers (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ)
    (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    algebraMap ℚ (w.adicCompletion ℚ) ((n : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, valued_natCast_eq_one_of_notMem w n hn,
    inv_one]

end Places

section Coord

variable {a b : ℚ}

def IsCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]) : Prop :=
  ∀ (z : ℍ[ℚ, a, b]) (r : w.adicCompletion ℚ),
    φ (z ⊗ₜ[ℚ] r) = r • (⟨algebraMap ℚ (w.adicCompletion ℚ) z.re,
      algebraMap ℚ (w.adicCompletion ℚ) z.imI, algebraMap ℚ (w.adicCompletion ℚ) z.imJ,
      algebraMap ℚ (w.adicCompletion ℚ) z.imK⟩ :
        ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b])

theorem exists_isCoord (a b : ℚ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
      IsCoord a b w φ := by
  obtain ⟨φ, -, hφ⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := w.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b)
    (d₁ := algebraMap ℚ (w.adicCompletion ℚ) a) (d₂ := (0 : w.adicCompletion ℚ))
    (d₃ := algebraMap ℚ (w.adicCompletion ℚ) b) rfl (map_zero _) rfl AlgEquiv.refl
  exact ⟨φ, fun z r => by rw [hφ]; rfl⟩

theorem IsCoord.nrd_tmul {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (γ : ℍ[ℚ, a, b]) (s : w.adicCompletion ℚ) :
    QuaternionAlgebra.nrd (φ (γ ⊗ₜ[ℚ] s)) =
      s ^ 2 * algebraMap ℚ (w.adicCompletion ℚ) (QuaternionAlgebra.nrd γ) := by
  rw [hφ, nrd_smul', QuaternionAlgebra.nrd_mk, QuaternionAlgebra.nrd]
  simp only [map_add, map_sub, map_mul, map_pow]

theorem IsCoord.eq_zero_of_tmul_one {w : HeightOneSpectrum (𝓞 ℚ)}
    {φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
      ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b]}
    (hφ : IsCoord a b w φ) (γ : ℍ[ℚ, a, b]) (h0 : φ (γ ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = 0) : γ = 0 := by
  rw [hφ, one_smul] at h0
  have hinj := (algebraMap ℚ (w.adicCompletion ℚ)).injective
  have hre := congrArg QuaternionAlgebra.re h0
  have hi := congrArg QuaternionAlgebra.imI h0
  have hj := congrArg QuaternionAlgebra.imJ h0
  have hk := congrArg QuaternionAlgebra.imK h0
  simp only [QuaternionAlgebra.re_zero, QuaternionAlgebra.imI_zero, QuaternionAlgebra.imJ_zero,
    QuaternionAlgebra.imK_zero] at hre hi hj hk
  ext
  · apply hinj; rw [hre]; simp
  · apply hinj; rw [hi]; simp
  · apply hinj; rw [hj]; simp
  · apply hinj; rw [hk]; simp

end Coord

section Division

variable {a b : ℚ}

theorem isUnit_of_nrd_ne_zero (x : ℍ[ℚ, a, b]) (hx : QuaternionAlgebra.nrd x ≠ 0) : IsUnit x := by
  set c : ℚ := QuaternionAlgebra.nrd x with hc
  have h1 : x * (c⁻¹ • star x) = 1 := by
    rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe_nrd, ← hc]
    ext <;> simp [hx]
  have h2 : (c⁻¹ • star x) * x = 1 := by
    rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd, ← hc]
    ext <;> simp [hx]
  exact ⟨⟨x, c⁻¹ • star x, h1, h2⟩, rfl⟩

theorem forall_isUnit_of_local (v : HeightOneSpectrum (𝓞 ℚ))
    (hdiv : ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, y ≠ 0 → IsUnit y) :
    ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x := by
  intro x hx0
  by_cases hn : QuaternionAlgebra.nrd x = 0
  · exfalso
    obtain ⟨φ, hφ⟩ := exists_isCoord a b v
    have hx1 : x ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ≠ 0 := fun h =>
      hx0 (hφ.eq_zero_of_tmul_one x (by rw [h, map_zero]))
    have hsx0 : star x ≠ 0 := fun h => hx0 (by rw [← star_star x, h, star_zero])
    have hsx1 : (star x) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ≠ 0 := fun h =>
      hsx0 (hφ.eq_zero_of_tmul_one (star x) (by rw [h, map_zero]))
    have hprod : (x ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) * ((star x) ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ)) = 0 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, QuaternionAlgebra.mul_star_eq_coe_nrd, hn]
      simp
    obtain ⟨u, hu⟩ := hdiv _ hx1
    apply hsx1
    have := congrArg (fun z => ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * z) hprod
    simpa only [← hu, ← mul_assoc, Units.inv_mul, one_mul, mul_zero] using this
  · exact isUnit_of_nrd_ne_zero x hn

end Division

section Boxes

variable {a b : ℚ}

theorem tmul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (v : HeightOneSpectrum (𝓞 ℚ)) {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ}
    (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by

  have key : ∀ x' ∈ Submodule.localBox Λ v, ∀ z ∈ Λ, ∀ c ∈ v.adicCompletionIntegers ℚ,
      x' * (z ⊗ₜ[ℚ] c) ∈ Submodule.localBox Λ v := by
    intro x' hx' z hz c hc
    induction hx' using AddSubgroup.closure_induction with
    | mem x'' hx'' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx''
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox (hΛ.mul_mem hz' hz) v (mul_mem hc' hc)
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | neg x₁ _ h₁ =>
      have h' := neg_mem h₁
      convert h' using 1
      exact neg_mul x₁ (z ⊗ₜ[ℚ] c)
  induction hy using AddSubgroup.closure_induction with
  | mem y' hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    exact key x hx z hz c hc
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | neg y₁ _ h₁ =>
    have h' := neg_mem h₁
    convert h' using 1
    exact mul_neg x y₁

theorem mem_localBox_inf_iff {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]}
    (h₁ : QuaternionAlgebra.IsOrder Λ₁) (h₂ : QuaternionAlgebra.IsOrder Λ₂)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    x ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) v ↔ x ∈ Submodule.localBox Λ₁ v ∧ x ∈ Submodule.localBox Λ₂ v := by
  rw [Submodule.localBox_inf Λ₁ Λ₂ h₁.fg h₁.spanTop h₂.fg h₂.spanTop v, AddSubgroup.mem_inf]

theorem star_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {x : ℍ[ℚ, a, b]}
    (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨⟨t, n, ht, -⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hΛ hx
  have h : star x = (t : ℤ) • (1 : ℍ[ℚ, a, b]) - x := by
    have := QuaternionAlgebra.add_star_eq_coe_trd x
    rw [ht] at this
    rw [eq_sub_iff_add_eq, add_comm, this]
    ext <;> simp
  rw [h]
  exact Λ.sub_mem (Λ.smul_mem _ hΛ.one_mem) hx

end Boxes

section Uniqueness

variable {a b : ℚ}

def unitOfNrd (s : ℍ[ℚ, a, b]) (r : ℚ) (hs : QuaternionAlgebra.nrd s = r) (hr : r ≠ 0) : (ℍ[ℚ, a, b])ˣ where
  val := s
  inv := r⁻¹ • star s
  val_inv := by
    rw [mul_smul_comm, QuaternionAlgebra.mul_star_eq_coe_nrd, hs]
    ext <;> simp [hr]
  inv_val := by
    rw [smul_mul_assoc, QuaternionAlgebra.star_mul_eq_coe_nrd, hs]
    ext <;> simp [hr]

@[scoped simp] theorem val_unitOfNrd (s : ℍ[ℚ, a, b]) (r : ℚ) (hs : QuaternionAlgebra.nrd s = r) (hr : r ≠ 0) :
    ((unitOfNrd s r hs hr : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = s := rfl

theorem val_inv_unitOfNrd (s : ℍ[ℚ, a, b]) (r : ℚ) (hs : QuaternionAlgebra.nrd s = r) (hr : r ≠ 0) :
    (((unitOfNrd s r hs hr)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = r⁻¹ • star s := rfl

theorem uniqueness {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂)
    (r : ℕ) (hr : r = q ∨ r = q')
    (s s' : ℍ[ℚ, a, b]) (hs : s ∈ Λ₁ ⊓ Λ₂) (hs' : s' ∈ Λ₁ ⊓ Λ₂)
    (hns : QuaternionAlgebra.nrd s = (r : ℚ)) (hns' : QuaternionAlgebra.nrd s' = (r : ℚ)) :
    ∃ u : ℍ[ℚ, a, b], QuaternionAlgebra.IsUnitOf (Λ₁ ⊓ Λ₂) u ∧ QuaternionAlgebra.nrd u = 1 ∧ u * s = s' := by
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hrp.ne_zero
  obtain ⟨-, h1⟩ := QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
    hqq' hB Λ₁ hΛ₁ r hr
  obtain ⟨-, h2⟩ := QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
    hqq' hB Λ₂ hΛ₂ r hr
  obtain ⟨u₁, ⟨hu₁, v₁, hv₁, huv₁, hvu₁⟩, hn₁, hus₁⟩ := h1 s s' hs.1 hs'.1 hns hns'
  obtain ⟨u₂, ⟨hu₂, v₂, hv₂, huv₂, hvu₂⟩, hn₂, hus₂⟩ := h2 s s' hs.2 hs'.2 hns hns'

  set sU := unitOfNrd s (r : ℚ) hns hr0 with hsU
  have hu12 : u₁ = u₂ := by
    have : u₁ * s * ((sU⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = u₂ * s * ((sU⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := by
      rw [hus₁, hus₂]
    rwa [show s = (sU : ℍ[ℚ, a, b]) from rfl, mul_assoc, mul_assoc, Units.mul_inv, mul_one, mul_one] at this

  have hv12 : v₁ = v₂ := by
    calc v₁ = v₁ * (u₂ * v₂) := by rw [huv₂, mul_one]
      _ = (v₁ * u₁) * v₂ := by rw [hu12, mul_assoc]
      _ = v₂ := by rw [hvu₁, one_mul]
  refine ⟨u₁, ⟨⟨hu₁, hu12 ▸ hu₂⟩, v₁, ⟨hv₁, hv12 ▸ hv₂⟩, huv₁, hvu₁⟩, hn₁, hus₁⟩

end Uniqueness

section Existence

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem patch_one {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : QuaternionAlgebra.IsOrder Λ₁)
    (v : HeightOneSpectrum (𝓞 ℚ)) (g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ)
    (hg : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.localBox Λ₁ w ∧
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈
        Submodule.localBox Λ₁ w) :
    ∃ g' : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ,
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (g' : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g' : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)) ∧
      (∀ w : HeightOneSpectrum (𝓞 ℚ),
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g' : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.localBox Λ₁ w ∧
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((g'⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈
          Submodule.localBox Λ₁ w) := by
  obtain ⟨g', h1, h2, h3⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq_of_forall_ne Λ₁ hΛ₁.fg hΛ₁.spanTop v
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) 1 (one_mul _) (one_mul _) g hg
  refine ⟨g', h1, fun w hw => (h3 w hw).1, fun w => ?_⟩
  by_cases hw : w = v
  · subst hw
    rw [h1, h2]
    have h1mem : (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) ∈ Submodule.localBox Λ₁ w :=
      tmul_mem_localBox hΛ₁.one_mem w (one_mem _)
    exact ⟨h1mem, h1mem⟩
  · rw [(h3 w hw).1, (h3 w hw).2]
    exact hg w hw

theorem existence {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]}
    (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁) (hΛ₂ : QuaternionAlgebra.IsMaximalOrder Λ₂)
    {N : ℕ} (hRN : (Λ₁ ⊓ Λ₂).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (r : ℕ) (hr : r = q ∨ r = q') :
    ∃ x ∈ Λ₁ ⊓ Λ₂, QuaternionAlgebra.nrd x = (r : ℚ) := by
  classical
  have hqp : q.Prime := Fact.out
  have hq'p : q'.Prime := Fact.out
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> assumption
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hrp.ne_zero
  set R : Submodule ℤ ℍ[ℚ, a, b] := Λ₁ ⊓ Λ₂ with hRdef
  have hRE : QuaternionAlgebra.IsEichlerOrder R N := ⟨Λ₁, Λ₂, hΛ₁, hΛ₂, rfl, hRN⟩
  have hRO : QuaternionAlgebra.IsOrder R := hΛ₁.isOrder.inf hΛ₂.isOrder
  have hRle : R ≤ Λ₁ := inf_le_left

  set vq := placeOf q hqp with hvq
  set vq' := placeOf q' hq'p with hvq'
  set vr := placeOf r hrp with hvr
  have hvr_mem : vr = vq ∨ vr = vq' := by
    rcases hr with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hvqq' : vq ≠ vq' := fun h => hqq' (by
    have := congrArg Rat.HeightOneSpectrum.natGenerator h
    rw [hvq, hvq', natGenerator_placeOf, natGenerator_placeOf] at this
    exact this.symm)

  have hdiv : ∀ w : HeightOneSpectrum (𝓞 ℚ), (w = vq ∨ w = vq') →
      ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, y ≠ 0 → IsUnit y := by
    rintro w (rfl | rfl)
    · exact (hB.2 _).2 (Or.inl (natCast_mem_placeOf q hqp))
    · exact (hB.2 _).2 (Or.inr (natCast_mem_placeOf q' hq'p))
  have hsplit : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ vq → w ≠ vq' →
      ¬ ∀ y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, y ≠ 0 → IsUnit y := by
    intro w h1 h2 h
    rcases (hB.2 w).1 h with hm | hm
    · exact h1 (eq_placeOf_of_mem hqp hm)
    · exact h2 (eq_placeOf_of_mem hq'p hm)
  have hD : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x := forall_isUnit_of_local vq (hdiv vq (Or.inl rfl))

  have hRbox : ∀ w : HeightOneSpectrum (𝓞 ℚ), (w = vq ∨ w = vq') →
      Submodule.localBox R w = Submodule.localBox Λ₁ w := by
    intro w hw
    rw [hRdef, Submodule.localBox_inf Λ₁ Λ₂ hΛ₁.isOrder.fg hΛ₁.isOrder.spanTop hΛ₂.isOrder.fg hΛ₂.isOrder.spanTop w,
      ← QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit w (hdiv w hw) hΛ₁ hΛ₂, inf_idem]

  obtain ⟨⟨s, hsΛ₁, hns⟩, -⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
      hqq' hB Λ₁ hΛ₁ r hr
  obtain ⟨sU, hsUval, hsUinv⟩ : ∃ sU : (ℍ[ℚ, a, b])ˣ, (sU : ℍ[ℚ, a, b]) = s ∧
      (((sU⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = (r : ℚ)⁻¹ • star s) :=
    ⟨unitOfNrd s (r : ℚ) hns hr0, rfl, rfl⟩

  set ε : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ := fun w =>
    if Valued.v (algebraMap ℚ (w.adicCompletion ℚ) (r : ℚ)) = 1 then algebraMap ℚ (w.adicCompletion ℚ) (r : ℚ) else 1
    with hεdef
  have hε : ∀ w, Valued.v (ε w) = 1 := by
    intro w
    simp only [hεdef]
    split_ifs with h
    · exact h
    · exact map_one _
  have hεr : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ vr → ε w = algebraMap ℚ (w.adicCompletion ℚ) (r : ℚ) := by
    intro w hw
    simp only [hεdef]
    rw [if_pos (valued_natCast_eq_one_of_notMem w r (notMem_of_ne_placeOf hrp hw))]
  obtain ⟨t, htR, htn⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_mem_finiteIdeleStabilizer_forall_nrd_eq_of_not_forall_isUnit hRE ε hε
  have htloc := (QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
    R hRO t).1 htR
  have ht_int : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (t : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.localBox R w ∧
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((t⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈
        Submodule.localBox R w := by
    intro w
    have := (Submodule.mem_localBoxUnits_iff R w _).1 (htloc w)
    rw [Units.coe_map, Units.coe_map_inv] at this
    exact this

  set g : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ := (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] sU)⁻¹ * t with hgdef
  have hsinv_tmul : (((sU⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝔸f)) =
      ((Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] sU)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) := by
    rw [← map_inv, Submodule.val_finiteIdeleDiagonal_apply]
  have hg_val : (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
      (((sU⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝔸f)) * (t : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) := by
    rw [hgdef, Units.val_mul, hsinv_tmul]
  have hginv_val : ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
      ((t⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * ((s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝔸f)) := by
    rw [hgdef, mul_inv_rev, inv_inv, Units.val_mul, Submodule.val_finiteIdeleDiagonal_apply, hsUval]
  have hev_tmul : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z ⊗ₜ[ℚ] (1 : 𝔸f)) = z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
    intro w z
    rw [Submodule.finiteAdeleEvalAt_tmul]
    rfl
  have hsinv_eq : (((sU⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝔸f)) =
      (star s) ⊗ₜ[ℚ] (algebraMap ℚ 𝔸f ((r : ℚ)⁻¹)) := by
    rw [hsUinv, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have hev_sinv : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((((sU⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝔸f))) =
        (star s) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) ((r : ℚ)⁻¹)) := by
    intro w
    rw [hsinv_eq, Submodule.finiteAdeleEvalAt_tmul, IsDedekindDomain.FiniteAdeleRing.algebraMap_apply]
    rfl
  have hg_int : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ vr →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (g : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈ Submodule.localBox Λ₁ w ∧
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈
        Submodule.localBox Λ₁ w := by
    intro w hw
    constructor
    · rw [hg_val, map_mul, hev_sinv]
      refine mul_mem_localBox hΛ₁.isOrder w ?_ (localBox_mono hRle w (ht_int w).1)
      exact tmul_mem_localBox (star_mem hΛ₁.isOrder hsΛ₁) w
        (inv_natCast_mem_adicCompletionIntegers w r (notMem_of_ne_placeOf hrp hw))
    · rw [hginv_val, map_mul, hev_tmul]
      exact mul_mem_localBox hΛ₁.isOrder w (localBox_mono hRle w (ht_int w).2)
        (tmul_mem_localBox hsΛ₁ w (one_mem _))

  obtain ⟨g₁, -, hg₁w, hg₁int⟩ := patch_one hΛ₁.isOrder vr g hg_int
  obtain ⟨g₂, hg₂v, hg₂w, hg₂int⟩ := patch_one hΛ₁.isOrder vq g₁ (fun w _ => hg₁int w)
  obtain ⟨y, hyv, hyw, -⟩ := patch_one hΛ₁.isOrder vq' g₂ (fun w _ => hg₂int w)
  have hy_one : ∀ w : HeightOneSpectrum (𝓞 ℚ), (w = vq ∨ w = vq') →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) = 1 := by
    rintro w (rfl | rfl)
    · rw [hyw _ hvqq', hg₂v]
    · exact hyv
  have hy_gen : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ vq → w ≠ vq' →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) =
        (star s) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) ((r : ℚ)⁻¹)) *
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (t : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) := by
    intro w h1 h2
    have hwr : w ≠ vr := by
      rcases hvr_mem with h | h
      · rw [h]; exact h1
      · rw [h]; exact h2
    rw [hyw w h2, hg₂w w h1, hg₁w w hwr, hg_val, map_mul, hev_sinv]

  have hy_nrd : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      ∀ φ : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ ≃+*
          ℍ[w.adicCompletion ℚ, algebraMap ℚ (w.adicCompletion ℚ) a, algebraMap ℚ (w.adicCompletion ℚ) b],
        IsCoord a b w φ →
        QuaternionAlgebra.nrd (φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f))) = 1 := by
    intro w φ hφ
    by_cases h1 : w = vq
    · rw [hy_one w (Or.inl h1), map_one, QuaternionAlgebra.nrd_one]
    by_cases h2 : w = vq'
    · rw [hy_one w (Or.inr h2), map_one, QuaternionAlgebra.nrd_one]
    have hwr : w ≠ vr := by
      rcases hvr_mem with h | h
      · rw [h]; exact h1
      · rw [h]; exact h2
    rw [hy_gen w h1 h2, map_mul, nrd_mul', hφ.nrd_tmul, QuaternionAlgebra.nrd_star, hns,
      htn w (hsplit w h1 h2) φ hφ, hεr w hwr]
    have hr0' : algebraMap ℚ (w.adicCompletion ℚ) (r : ℚ) ≠ 0 := (map_ne_zero _).2 hr0
    rw [map_inv₀]
    field_simp

  obtain ⟨β, u, hβ, hu, hyβu⟩ :=
    QuaternionAlgebra.IsOrder.exists_nrd_eq_one_and_eq_finiteIdeleDiagonal_mul_mul_of_forall_nrd_eq_one_of_forall_isUnit
      hB.1 hD hRO y (fun w φ hφ => hy_nrd w φ hφ)
  have huloc := (QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
    R hRO u).1 hu
  have hu_int : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) ∈
        Submodule.localBox R w := by
    intro w
    have := (Submodule.mem_localBoxUnits_iff R w _).1 (huloc w)
    rw [Units.coe_map_inv] at this
    exact this.2

  set x : ℍ[ℚ, a, b] := s * (β : ℍ[ℚ, a, b]) with hxdef
  have hx_tmul : x ⊗ₜ[ℚ] (1 : 𝔸f) =
      ((s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝔸f)) * (y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) *
        ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) := by
    have hd : Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] β = y * u⁻¹ := eq_mul_inv_of_mul_eq hyβu.symm
    have hβ' : ((β : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝔸f)) =
        (y : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) * ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] 𝔸f) := by
      have := congrArg Units.val hd
      rwa [Submodule.val_finiteIdeleDiagonal_apply, Units.val_mul] at this
    have hsplit_tmul : x ⊗ₜ[ℚ] (1 : 𝔸f) =
        ((s : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝔸f)) * (((β : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (1 : 𝔸f)) := by
      rw [hxdef, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit_tmul, hβ', mul_assoc]
  have hx_loc : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (x ⊗ₜ[ℚ] (1 : 𝔸f)) ∈ Submodule.localBox R w := by
    intro w
    rw [hx_tmul, map_mul, map_mul, hev_tmul]
    refine mul_mem_localBox hRO w ?_ (hu_int w)
    by_cases h12 : w = vq ∨ w = vq'
    · rw [hy_one w h12, mul_one, hRbox w h12]
      exact tmul_mem_localBox hsΛ₁ w (one_mem _)
    · push Not at h12
      rw [hy_gen w h12.1 h12.2, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        QuaternionAlgebra.mul_star_eq_coe_nrd, hns]
      have hsc : (((r : ℚ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) ((r : ℚ)⁻¹))) =
          (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) := by
        rw [show ((r : ℚ) : ℍ[ℚ, a, b]) = (r : ℚ) • (1 : ℍ[ℚ, a, b]) by ext <;> simp,
          TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hr0, map_one]
        rfl
      rw [hsc, one_mul]
      exact (ht_int w).1

  have hx_box : x ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox R :=
    (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox R hRO.fg hRO.spanTop _).2 hx_loc
  have hxR : x ∈ R := by
    rw [← Submodule.ofFiniteIdele_one R hRO.fg hRO.spanTop, Submodule.mem_ofFiniteIdele_iff]
    refine ⟨x ⊗ₜ[ℚ] (1 : 𝔸f), hx_box, ?_⟩
    simp
  refine ⟨x, hxR, ?_⟩
  rw [hxdef, nrd_mul', hns, hβ, mul_one]

end Existence

theorem main
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ)
    {N : ℕ} [NeZero N] (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : QuaternionAlgebra.IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :
    (∃ s ∈ R, QuaternionAlgebra.nrd s = (r : ℚ)) ∧
    (∀ s s' : ℍ[ℚ, a, b], s ∈ R → s' ∈ R → QuaternionAlgebra.nrd s = (r : ℚ) → QuaternionAlgebra.nrd s' = (r : ℚ) →
      ∃ u : ℍ[ℚ, a, b], QuaternionAlgebra.IsUnitOf R u ∧ QuaternionAlgebra.nrd u = 1 ∧ u * s = s') := by
  obtain ⟨Λ₁, Λ₂, hΛ₁, hΛ₂, hReq, hRN⟩ := hR
  subst hReq
  exact ⟨existence hqq' hB hΛ₁ hΛ₂ hRN r hr,
    fun s s' hs hs' hns hns' => uniqueness hqq' hB hΛ₁ hΛ₂ r hr s s' hs hs' hns hns'⟩

end ALRAMN
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt.ALRAMN"

end
p2m_reactivate "P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt.ALRAMN"

open scoped Quaternion MatrixGroups Pointwise in
open QuaternionAlgebra in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    {N : ℕ} [NeZero N] (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (r : ℕ) (hr : r = q ∨ r = q') :
    (∃ s ∈ R, nrd s = (r : ℚ)) ∧
    (∀ s s' : ℍ[ℚ, a, b], s ∈ R → s' ∈ R → nrd s = (r : ℚ) → nrd s' = (r : ℚ) →
      ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * s = s') :=
  ALRAMN.main hqq' hB Λ hΛ R hR hRΛ r hr

end S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt (solution)
