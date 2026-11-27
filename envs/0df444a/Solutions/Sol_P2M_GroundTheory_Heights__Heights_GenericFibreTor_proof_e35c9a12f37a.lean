-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFibreTor_proof_e35c9a12f37a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:54:59.854826+00:00
-- url     : https://prove2.me/submissions/770a735c-a213-438a-b3f3-df7be87f7310

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreTor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFreeness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFibreTor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFibreTor_mem_of_smul_mem_2be63fe3ed26

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace GenericFibreTor
theorem _root_.solution (hGF : GenericFreeness.Statement.{0, 0, 0}) :
    GenericFibreTor.Statement := by
  classical
  intro σ _ ι _ L
  obtain ⟨F, hF0, hfree⟩ := hGF (MvPolynomial σ ℂ) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
    (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
  refine ⟨F, hF0, fun t ht x hx => ?_⟩
  rw [MvPolynomial.ker_map] at hx ⊢
  obtain ⟨hxL, hxI⟩ := Ideal.mem_inf.1 hx
  rw [MvPolynomial.mem_map_C_iff] at hxI
  have hflat' : Module.Flat (Localization.Away F)
      (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)) :=
    @Module.Flat.of_free _ _ _ _ _ hfree
  have hflatS : Module.Flat (MvPolynomial σ ℂ) (Localization.Away F) := IsLocalization.flat _ (Submonoid.powers F)
  have : Module.Flat (MvPolynomial σ ℂ)
      (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)) :=
    Module.Flat.trans (MvPolynomial σ ℂ) (Localization.Away F) _
  let g := LocalizedModule.mkLinearMap (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
  let π := (Ideal.Quotient.mkₐ (MvPolynomial σ ℂ) L).toLinearMap
  let a : x.support → MvPolynomial σ ℂ := fun m => coeff m.1 x
  let e : x.support → MvPolynomial ι (MvPolynomial σ ℂ) := fun m => monomial m.1 1
  have hsum : ∑ m, a m • e m = x := by
    calc ∑ m, a m • e m = ∑ m : x.support, monomial m.1 (coeff m.1 x) :=
          Finset.sum_congr rfl fun m _ => by simp [a, e, smul_monomial]
      _ = x := by
          rw [Finset.sum_coe_sort x.support (fun v => monomial v (coeff v x))]
          exact (MvPolynomial.as_sum x).symm
  have hrel : ∑ m, a m • g (π (e m)) = 0 := by
    simp_rw [← map_smul, ← map_sum, hsum]
    simp [g, π, Ideal.Quotient.eq_zero_iff_mem.2 hxL]
  have htriv : Module.IsTrivialRelation a (fun m => g (π (e m))) :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨k, A, y, hy, hA⟩ := htriv
  obtain ⟨b, hb⟩ := IsLocalizedModule.exist_integer_multiples_of_finite (Submonoid.powers F) g y
  choose q hq using hb
  choose r hr using fun j => Ideal.Quotient.mk_surjective (q j)
  have hm : ∀ m, ∃ c : Submonoid.powers F,
      c • π ((b : MvPolynomial σ ℂ) • e m) = c • π (∑ j, A m j • r j) := by
    intro m
    apply IsLocalizedModule.exists_of_eq (S := Submonoid.powers F) (f := g)
    rw [map_smul, map_smul, show g (π (e m)) = ∑ j, A m j • y j from hy m, Finset.smul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm, ← hq j, ← hr j, map_smul, map_smul]
    rfl
  choose c hc using hm
  set V : MvPolynomial σ ℂ := ∏ m, (c m : MvPolynomial σ ℂ)
  have hD : ∀ m, (V * b) • e m - ∑ j, (V * A m j) • r j ∈ L := by
    intro m
    have h1 := hc m
    rw [← sub_eq_zero, ← smul_sub, ← map_sub, Submonoid.smul_def, ← map_smul] at h1
    have h2 : (c m : MvPolynomial σ ℂ) • ((b : MvPolynomial σ ℂ) • e m - ∑ j, A m j • r j) ∈ L :=
      Ideal.Quotient.eq_zero_iff_mem.1 h1
    have h3 := Submodule.smul_of_tower_mem L (∏ m' ∈ Finset.univ.erase m, (c m' : MvPolynomial σ ℂ)) h2
    convert h3 using 1
    rw [smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ m), smul_sub, smul_smul,
      Finset.smul_sum]
    simp_rw [smul_smul]
    rfl
  have hzero : ∑ m, a m • ∑ j, (V * A m j) • r j = 0 := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul]
    have : ∑ m, a m * (V * A m j) = V * ∑ m, a m * A m j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_; ring
    rw [this, hA j, mul_zero, zero_smul]
  have hkey : (V * b) • x = ∑ m, a m • ((V * b) • e m - ∑ j, (V * A m j) • r j) := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, hzero, sub_zero, ← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_comm]
  have hJ : (V * b) • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L := by
    rw [hkey]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [smul_eq_C_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hxI m.1)) (hD m)
  have hpow : ∀ u ∈ Submonoid.powers F, eval t u ≠ 0 := by
    rintro u ⟨n, rfl⟩
    rw [map_pow]
    exact pow_ne_zero n ht
  have hVb : V * b ∈ Submonoid.powers F :=
    (Submonoid.powers F).mul_mem (Submonoid.prod_mem _ fun m _ => (c m).2) b.2
  exact GenericFibreTor.mem_of_smul_mem t L hxL (hpow _ hVb) hJ
end GenericFibreTor
end GroundTheory.Heights₂.Heights
