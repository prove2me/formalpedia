-- Prove2me | solution 1 for QuaternionAlgebra.IsEichlerOrder.not_dvd_of_isDefiniteRamifiedExactlyAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3d631b4c-d16b-599b-862b-0f6a7b8170b2

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBox_eq_localBox_of_forall_isUnit
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_not_dvd_of_isDefiniteRamifiedExactlyAt
p2m_attr_erase "simp" "QuaternionAlgebra.nrd_coe QuaternionAlgebra.nrd_one QuaternionAlgebra.trd_mk QuaternionAlgebra.nrd_mk QuaternionAlgebra.nrd_neg QuaternionAlgebra.nrd_zero QuaternionAlgebra.nrd_star QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

namespace NotDvdLevel

variable {a b : ℚ}

theorem exists_forall_smul_mem {R Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R) (hΛ₁ : IsOrder Λ₁) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ x ∈ Λ₁, ((m : ℕ) : ℤ) • x ∈ R := by
  classical
  obtain ⟨s, hs⟩ := hΛ₁.fg
  have h : ∀ g : ℍ[ℚ, a, b], ∃ n : ℕ, n ≠ 0 ∧ ((n : ℕ) : ℤ) • g ∈ R := fun g =>
    exists_natCast_smul_mem_of_mem_span (by rw [hR.spanTop]; exact Submodule.mem_top)
  choose n hn0 hn using h
  refine ⟨∏ g ∈ s, n g, Finset.prod_ne_zero_iff.mpr (fun g _ => hn0 g), fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, hk⟩ : n g ∣ ∏ g' ∈ s, n g' := Finset.dvd_prod_of_mem n hg
      rw [hk, Nat.cast_mul, mul_comm, mul_smul]
      exact R.smul_mem _ (hn g)
  | zero => rw [smul_zero]; exact R.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact R.add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact R.smul_mem c hx

theorem inv_natCast_mem_adicCompletionIntegers {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) :
    algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) = v.valuation ℚ ((ℓ : ℚ)⁻¹) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _, map_inv₀]
  have h1 : v.valuation ℚ (ℓ : ℚ) = 1 := by
    have : (ℓ : ℚ) = algebraMap (𝓞 ℚ) ℚ (ℓ : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    have hle := v.intValuation_le_one (ℓ : 𝓞 ℚ)
    have hnlt : ¬ v.intValuation (ℓ : 𝓞 ℚ) < 1 := by
      rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hv
    exact le_antisymm hle (not_lt.mp hnlt)
  rw [h1, inv_one]

theorem mem_inf_of_smul_mem {q' : ℕ} (hq' : q'.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : IsMaximalOrder Λ₁) (hΛ₂ : IsMaximalOrder Λ₂)
    {y : ℍ[ℚ, a, b]} (hy : y ∈ Λ₁) (hqy : (q' : ℤ) • y ∈ Λ₁ ⊓ Λ₂) : y ∈ Λ₁ ⊓ Λ₂ := by
  have hR : IsOrder (Λ₁ ⊓ Λ₂) := hΛ₁.isOrder.inf hΛ₂.isOrder

  have hloc : ∀ w : HeightOneSpectrum (𝓞 ℚ),
      y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox (Λ₁ ⊓ Λ₂) w := by
    intro w
    by_cases hw : ((q' : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    ·
      have hdiv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, x ≠ 0 → IsUnit x := (hdef.2.2 w).mpr hw
      have heq := QuaternionAlgebra.IsMaximalOrder.localBox_eq_localBox_of_forall_isUnit w hdiv hΛ₁ hΛ₂
      have hy₁ : y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox Λ₁ w :=
        AddSubgroup.subset_closure ⟨y, hy, 1, one_mem _, rfl⟩
      rw [Submodule.localBox_inf Λ₁ Λ₂ hΛ₁.isOrder.fg hΛ₁.isOrder.spanTop hΛ₂.isOrder.fg hΛ₂.isOrder.spanTop w]
      exact ⟨hy₁, heq ▸ hy₁⟩
    ·
      have hq0 : (q' : ℚ) ≠ 0 := by exact_mod_cast hq'.ne_zero
      have hc := inv_natCast_mem_adicCompletionIntegers hq'.ne_zero hw
      have hgen : ((q' : ℤ) • y) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) ((q' : ℚ)⁻¹)) ∈
          Submodule.localBox (Λ₁ ⊓ Λ₂) w :=
        AddSubgroup.subset_closure ⟨(q' : ℤ) • y, hqy, _, hc, rfl⟩
      have he : ((q' : ℤ) • y) ⊗ₜ[ℚ] (algebraMap ℚ (w.adicCompletion ℚ) ((q' : ℚ)⁻¹)) =
          y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
        rw [show ((q' : ℤ) • y) = (q' : ℚ) • y by
              rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast],
          TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hq0, map_one]
      rwa [he] at hgen

  rw [← Submodule.ofFiniteIdele_one (Λ₁ ⊓ Λ₂) hR.fg hR.spanTop, Submodule.mem_ofFiniteIdele_iff]
  rw [AddSubgroup.mem_map]
  refine ⟨y ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ), ?_, ?_⟩
  · rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox _ hR.fg hR.spanTop]
    intro w
    rw [Submodule.finiteAdeleEvalAt_tmul]
    exact hloc w
  · rw [Units.val_one, AddMonoidHom.coe_mulLeft, one_mul]

theorem main {q' : ℕ} (hq' : q'.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N) : ¬ q' ∣ N := by
  classical
  obtain ⟨Λ₁, Λ₂, hΛ₁, hΛ₂, rfl, hidx⟩ := hR
  haveI : Fact q'.Prime := ⟨hq'⟩
  intro hdvd
  set K : AddSubgroup ↥(Λ₁.toAddSubgroup) := (Λ₁ ⊓ Λ₂).toAddSubgroup.addSubgroupOf Λ₁.toAddSubgroup
    with hKdef
  have hK : ∀ u : ↥(Λ₁.toAddSubgroup), u ∈ K ↔ (u : ℍ[ℚ, a, b]) ∈ Λ₁ ⊓ Λ₂ := fun u =>
    AddSubgroup.mem_addSubgroupOf
  have hidx' : K.index = N := hidx

  obtain ⟨m, hm0, hm⟩ := exists_forall_smul_mem (hΛ₁.isOrder.inf hΛ₂.isOrder) hΛ₁.isOrder
  haveI : AddGroup.FG ↥(Λ₁.toAddSubgroup) :=
    (AddGroup.fg_iff_addSubgroup_fg _).mpr ((Submodule.fg_iff_addSubgroup_fg _).mp hΛ₁.isOrder.fg)
  haveI : Finite (↥(Λ₁.toAddSubgroup) ⧸ K) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨m, Nat.pos_of_ne_zero hm0, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hK, AddSubgroupClass.coe_nsmul]
    have := hm x x.2
    rwa [natCast_zsmul] at this
  letI : Fintype (↥(Λ₁.toAddSubgroup) ⧸ K) := Fintype.ofFinite _
  have hcard : q' ∣ Fintype.card (↥(Λ₁.toAddSubgroup) ⧸ K) := by
    rw [← Nat.card_eq_fintype_card, ← AddSubgroup.index, hidx']
    exact hdvd
  obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card q' hcard
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z

  have hqy : (q' : ℤ) • (y : ℍ[ℚ, a, b]) ∈ Λ₁ ⊓ Λ₂ := by
    have h0 : ((q' • y : ↥(Λ₁.toAddSubgroup)) : ↥(Λ₁.toAddSubgroup) ⧸ K) = 0 := by
      rw [QuotientAddGroup.mk_nsmul, ← hz]
      exact addOrderOf_nsmul_eq_zero _
    rw [QuotientAddGroup.eq_zero_iff, hK, AddSubgroupClass.coe_nsmul] at h0
    rw [natCast_zsmul]
    exact h0
  have hyR : (y : ℍ[ℚ, a, b]) ∈ Λ₁ ⊓ Λ₂ := mem_inf_of_smul_mem hq' hdef hΛ₁ hΛ₂ y.2 hqy

  have hy0 : (y : ↥(Λ₁.toAddSubgroup) ⧸ K) = 0 := by
    rw [QuotientAddGroup.eq_zero_iff, hK]
    exact hyR
  rw [hy0, addOrderOf_zero] at hz
  exact hq'.ne_one hz.symm

end NotDvdLevel

theorem solution
    {a b : ℚ} {q' : ℕ} (hq' : q'.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N) :
    ¬ q' ∣ N :=
  NotDvdLevel.main hq' hdef hR

end S_QuaternionAlgebra_IsEichlerOrder_not_dvd_of_isDefiniteRamifiedExactlyAt
end P2MW
export P2MW.S_QuaternionAlgebra_IsEichlerOrder_not_dvd_of_isDefiniteRamifiedExactlyAt (solution)
