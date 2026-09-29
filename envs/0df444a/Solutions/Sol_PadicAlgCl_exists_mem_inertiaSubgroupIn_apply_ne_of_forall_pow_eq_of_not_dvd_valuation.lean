-- Prove2me | solution 1 for PadicAlgCl.exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fe83c4f8-46b8-5eca-a57c-ab7229dda536

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Theorems.Thm_Field_exists_prod_pow_mul_pow_eq_of_root_mem_adjoin_roots
import Theorems.Thm_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime
import Theorems.Thm_PadicAlgCl_exists_nnnorm_pow_sub_one_eq_zpow_of_mem_adjoin_rootsOfUnity_coprime_sup_cyclotomicTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped NNReal

theorem solution
    (p : ℕ) [Fact p.Prime] {n : ℕ} (u β : Fin n → PadicAlgCl p)
    (hu : ∀ i, ‖u i‖₊ = 1)
    (huI : ∀ i, ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], τ (u i) = u i)
    (hβ : ∀ i, β i ^ p = u i)
    (x : ℚ_[p]) (hx : ¬ (p : ℤ) ∣ Padic.valuation x)
    (γ : PadicAlgCl p) (hγ : γ ^ p = algebraMap ℚ_[p] (PadicAlgCl p) x) :
    ∃ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p],
      (∀ ζ : PadicAlgCl p, ζ ^ p = 1 → τ ζ = ζ) ∧ (∀ i, τ (β i) = β i) ∧ τ γ ≠ γ := by
  classical
  have hp : p.Prime := Fact.out
  by_contra hcon
  push Not at hcon

  set I : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :=
    (padicIntegers p).inertiaSubgroupIn ℚ_[p] with hIdef
  set F : IntermediateField ℚ_[p] (PadicAlgCl p) :=
    IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1} with hFdef

  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp)

  obtain ⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ p := by
    have hdeg : (Polynomial.cyclotomic p (PadicAlgCl p)).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.mpr hp.pos).ne'
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
    exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff_charZero hp.pos).mp hζ⟩
  have hζall : ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, τ ζ = ζ →
      ∀ ζ' : PadicAlgCl p, ζ' ^ p = 1 → τ ζ' = ζ' := by
    haveI : NeZero p := ⟨hp.ne_zero⟩
    intro τ hτ ζ' hζ'
    obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hζ'
    rw [map_pow, hτ]

  set S : Set (PadicAlgCl p) := insert ζ (Set.range β) with hSdef
  set E : IntermediateField ℚ_[p] (PadicAlgCl p) := F ⊔ IntermediateField.adjoin ℚ_[p] S with hEdef
  have hFfix : F.fixingSubgroup = I := by
    rw [hFdef, hIdef]
    exact PadicAlgCl.fixingSubgroup_adjoin_rootsOfUnity_coprime p
  have hEfix : ∀ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, τ ∈ E.fixingSubgroup →
      τ ∈ I ∧ τ ζ = ζ ∧ ∀ i, τ (β i) = β i := by
    intro τ hτ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hS : S ⊆ (E : Set (PadicAlgCl p)) := fun s hs =>
      (le_sup_right : IntermediateField.adjoin ℚ_[p] S ≤ E) (IntermediateField.subset_adjoin _ _ hs)
    refine ⟨?_, hτ ζ (hS (Set.mem_insert _ _)), fun i => hτ (β i) (hS (Set.mem_insert_of_mem _ ⟨i, rfl⟩))⟩
    rw [← hFfix, IntermediateField.mem_fixingSubgroup_iff]
    exact fun y hy => hτ y ((le_sup_left : F ≤ E) hy)
  have hγE : γ ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro τ hτ
    obtain ⟨hτI, hτζ, hτβ⟩ := hEfix τ hτ
    exact hcon τ hτI (hζall τ hτζ) hτβ

  set K₀ : IntermediateField ℚ_[p] (PadicAlgCl p) := F ⊔ PadicAlgCl.cyclotomicTower p 1 with hK₀def
  have huF : ∀ i, u i ∈ F := by
    intro i
    rw [← InfiniteGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff, hFfix]
    exact fun τ hτ => huI i τ hτ
  have huK : ∀ i, u i ∈ K₀ := fun i => (le_sup_left : F ≤ K₀) (huF i)
  have hζK : ζ ∈ K₀ := (le_sup_right : PadicAlgCl.cyclotomicTower p 1 ≤ K₀)
    (PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p (by rw [pow_one]; exact hζ.pow_eq_one))
  have hxK : algebraMap ℚ_[p] (PadicAlgCl p) x ∈ K₀ := K₀.algebraMap_mem x
  have hmem : γ ∈ IntermediateField.adjoin K₀ (Set.range β) := by
    have hK₀le : ∀ y ∈ K₀, y ∈ IntermediateField.adjoin K₀ (Set.range β) := fun y hy =>
      (IntermediateField.adjoin K₀ (Set.range β)).algebraMap_mem ⟨y, hy⟩
    have hE : E ≤ (IntermediateField.adjoin K₀ (Set.range β)).restrictScalars ℚ_[p] := by
      refine sup_le ?_ ?_
      · intro y hy
        rw [IntermediateField.mem_restrictScalars]
        exact hK₀le y ((le_sup_left : F ≤ K₀) hy)
      · rw [IntermediateField.adjoin_le_iff]
        intro s hs
        change s ∈ IntermediateField.adjoin K₀ (Set.range β)
        rcases hs with rfl | ⟨i, rfl⟩
        · exact hK₀le _ hζK
        · exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    exact (IntermediateField.mem_restrictScalars ℚ_[p]).mp (hE hγE)

  have hζK' : IsPrimitiveRoot (⟨ζ, hζK⟩ : K₀) p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap K₀ (PadicAlgCl p))
      (show IsPrimitiveRoot ζ p from hζ) (algebraMap K₀ (PadicAlgCl p)).injective
  have hu0 : ∀ i, (⟨u i, huK i⟩ : K₀) ≠ 0 := by
    intro i h0
    have : u i = 0 := congrArg Subtype.val h0
    have h1 := hu i
    rw [this, nnnorm_zero] at h1
    exact zero_ne_one h1
  have hxK0 : (⟨algebraMap ℚ_[p] (PadicAlgCl p) x, hxK⟩ : K₀) ≠ 0 := by
    intro h0
    have : algebraMap ℚ_[p] (PadicAlgCl p) x = 0 := congrArg Subtype.val h0
    exact hx0 ((map_eq_zero _).1 this)
  obtain ⟨a, w, hw⟩ :=
    Field.exists_prod_pow_mul_pow_eq_of_root_mem_adjoin_roots (K := K₀) (L := PadicAlgCl p) p hp
      ⟨ζ, hζK⟩ hζK' (fun i => ⟨u i, huK i⟩) hu0 β (fun i => hβ i)
      ⟨algebraMap ℚ_[p] (PadicAlgCl p) x, hxK⟩ hxK0 γ hγ hmem

  have hw' : algebraMap ℚ_[p] (PadicAlgCl p) x = (∏ i, u i ^ a i) * (w : PadicAlgCl p) ^ p := by
    have h := congrArg (algebraMap K₀ (PadicAlgCl p)) hw
    rw [map_mul, map_pow, map_prod] at h
    simp only [map_pow] at h
    exact h
  have hw0 : (w : PadicAlgCl p) ≠ 0 := by
    intro h0
    apply hx0
    have : algebraMap ℚ_[p] (PadicAlgCl p) x = 0 := by
      rw [hw', h0, zero_pow hp.ne_zero, mul_zero]
    exact (map_eq_zero _).1 this
  have hnormx : ‖algebraMap ℚ_[p] (PadicAlgCl p) x‖₊ = ‖(w : PadicAlgCl p)‖₊ ^ p := by
    rw [hw', nnnorm_mul, nnnorm_pow, nnnorm_prod]
    simp only [nnnorm_pow, hu, one_pow, Finset.prod_const_one, one_mul]
  obtain ⟨m, hm⟩ :=
    PadicAlgCl.exists_nnnorm_pow_sub_one_eq_zpow_of_mem_adjoin_rootsOfUnity_coprime_sup_cyclotomicTower
      p (w : PadicAlgCl p) hw0 w.2

  have hnx : ‖algebraMap ℚ_[p] (PadicAlgCl p) x‖₊ = (p : ℝ≥0) ^ (-Padic.valuation x) := by
    rw [← NNReal.coe_inj, coe_nnnorm, NNReal.coe_zpow, NNReal.coe_natCast,
      show algebraMap ℚ_[p] (PadicAlgCl p) x = (x : PadicAlgCl p) from rfl,
      PadicAlgCl.norm_extends, Padic.norm_eq_zpow_neg_valuation hx0]
  have hexp : (-(Padic.valuation x)) * ((p : ℤ) - 1) = (m : ℤ) * p := by
    have hp1 : (1 : ℝ≥0) < (p : ℝ≥0) := by exact_mod_cast hp.one_lt
    have hwp : ‖(w : PadicAlgCl p)‖₊ ^ p = (p : ℝ≥0) ^ (-Padic.valuation x) := by
      rw [← hnormx, hnx]
    have key : (p : ℝ≥0) ^ ((-Padic.valuation x) * ((p : ℤ) - 1)) = (p : ℝ≥0) ^ ((m : ℤ) * p) := by
      have hcast : ((p : ℤ) - 1) = ((p - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hp.one_le, Nat.cast_one]
      rw [hcast, zpow_mul, zpow_natCast, ← hwp, ← pow_mul, mul_comm p (p - 1), pow_mul, hm,
        zpow_mul, zpow_natCast]
    exact (zpow_right_strictMono₀ hp1).injective key
  have hdvd : (p : ℤ) ∣ Padic.valuation x * ((p : ℤ) - 1) := by
    refine ⟨-m, ?_⟩
    have := hexp
    linarith
  have hcop : IsCoprime (p : ℤ) ((p : ℤ) - 1) := by
    refine ⟨1, -1, by ring⟩
  exact hx (hcop.dvd_of_dvd_mul_right hdvd)

end S_PadicAlgCl_exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation
end P2MW
export P2MW.S_PadicAlgCl_exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation (solution)
