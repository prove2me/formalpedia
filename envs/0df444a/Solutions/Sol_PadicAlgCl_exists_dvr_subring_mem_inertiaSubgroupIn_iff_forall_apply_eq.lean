-- Prove2me | solution 1 for PadicAlgCl.exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/68bb423d-3565-5ee9-b99a-e2918332ed98

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime
import Theorems.Thm_PadicAlgCl_fixingSubgroup_fixedField_inertiaSubgroupIn
import Theorems.Thm_PadicAlgCl_finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

open scoped NNReal

namespace S17ShRing

variable (p : ℕ) [Fact p.Prime]

theorem isGalois_padicAlgCl : IsGalois ℚ_[p] (PadicAlgCl p) := by
  haveI : Normal ℚ_[p] (PadicAlgCl p) := IsAlgClosure.normal ℚ_[p] (PadicAlgCl p)
  exact IsGalois.mk

theorem exists_norm_eq_zpow_of_forall_inertia_fix (x : PadicAlgCl p)
    (hfix : ∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], σ x = x) (hx0 : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = (p : ℝ) ^ k := by
  classical
  haveI := isGalois_padicAlgCl p
  set S : Set (PadicAlgCl p) := {ζ : PadicAlgCl p | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1} with hS

  have hxF : x ∈ IntermediateField.adjoin ℚ_[p] S := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin ℚ_[p] S),
      PadicAlgCl.fixingSubgroup_adjoin_rootsOfUnity_coprime, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact hfix σ hσ

  obtain ⟨T, hTS, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin hxF
  have hT : ∀ ζ ∈ T, ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1 := fun ζ hζ => hTS (Finset.mem_coe.mpr hζ)
  choose! Nf hNf using hT
  set N : ℕ := ∏ ζ ∈ T, Nf ζ with hNdef
  have hpN : ¬ p ∣ N :=
    Prime.not_dvd_finsetProd (Nat.prime_iff.mp Fact.out) (fun ζ hζ => (hNf ζ hζ).1)
  have hN0 : N ≠ 0 := fun h => hpN (h ▸ dvd_zero p)
  have hζN : ∀ ζ ∈ T, ζ ^ N = 1 := by
    intro ζ hζ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Nf hζ
    rw [show N = Nf ζ * c from hc, pow_mul, (hNf ζ hζ).2, one_pow]

  set n : ℕ := Nat.totient N with hn
  have hnpos : 0 < n := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN
  have hdvd : N ∣ p ^ n - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow n p (Nat.Prime.pos Fact.out))).mp
      (Nat.ModEq.pow_totient hcop).symm
  have hζpn : ∀ ζ ∈ T, ζ ^ (p ^ n - 1) = 1 := by
    intro ζ hζ
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hζN ζ hζ, one_pow]
  have hle : IntermediateField.adjoin ℚ_[p] (T : Set (PadicAlgCl p)) ≤
      IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (p ^ n - 1) = 1} :=
    IntermediateField.adjoin.mono _ _ _ (fun ζ hζ => hζpn ζ (Finset.mem_coe.mp hζ))
  exact (PadicAlgCl.finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow p n hnpos).2.2.1
    x (hle hxT) hx0

theorem norm_natCast_p : ‖((p : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  change ‖((p : ℚ_[p]) : PadicAlgCl p)‖ = _
  rw [PadicAlgCl.norm_extends, Padic.norm_p]

theorem nnnorm_le_of_lt_one (x : PadicAlgCl p)
    (hfix : ∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], σ x = x) (hlt : ‖x‖₊ < 1) :
    ‖x‖₊ ≤ ‖((p : ℕ) : PadicAlgCl p)‖₊ := by
  by_cases hx0 : x = 0
  · subst hx0; simp
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow_of_forall_inertia_fix p x hfix hx0
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hlt' : ‖x‖ < 1 := hlt
  have hk0 : k ≤ -1 := by
    by_contra hcon
    push Not at hcon
    have : (1 : ℝ) ≤ (p : ℝ) ^ k := one_le_zpow₀ hp1 (by omega)
    rw [← hk] at this
    exact absurd hlt' (not_lt.mpr this)
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, hk, norm_natCast_p, ← zpow_neg_one]
  exact zpow_le_zpow_right₀ hp1 hk0

noncomputable def Oring : Subring (PadicAlgCl p) :=
  (IntermediateField.fixedField ((padicIntegers p).inertiaSubgroupIn ℚ_[p])).toSubring ⊓
    (padicIntegers p).toSubring

theorem mem_Oring_iff (x : PadicAlgCl p) :
    x ∈ Oring p ↔ (∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], σ x = x) ∧ ‖x‖₊ ≤ 1 := by
  unfold Oring
  rw [Subring.mem_inf]
  exact and_congr (IntermediateField.mem_fixedField_iff _ _) Iff.rfl

theorem isUnit_of_nnnorm_eq_one {x : PadicAlgCl p} (hx : x ∈ Oring p) (hv : ‖x‖₊ = 1) :
    IsUnit (⟨x, hx⟩ : Oring p) := by
  obtain ⟨hxI, hxA⟩ := (mem_Oring_iff p x).mp hx
  have hx0 : x ≠ 0 := by
    intro h; subst h; simp at hv
  have hxinvA : ‖x⁻¹‖₊ ≤ 1 := by rw [nnnorm_inv, hv, inv_one]
  have hxinvI : ∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], σ x⁻¹ = x⁻¹ := fun σ hσ => by
    rw [map_inv₀, hxI σ hσ]
  have hxinv : x⁻¹ ∈ Oring p := (mem_Oring_iff p _).mpr ⟨hxinvI, hxinvA⟩
  exact ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hxinv⟩,
    Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem nnnorm_eq_one_of_isUnit {x : Oring p} (hu : IsUnit x) : ‖(x : PadicAlgCl p)‖₊ = 1 := by
  obtain ⟨u, rfl⟩ := hu
  have h1 : ‖((u : Oring p) : PadicAlgCl p)‖₊ ≤ 1 := ((mem_Oring_iff p _).mp (u : Oring p).2).2
  have h2 : ‖((u⁻¹ : (Oring p)ˣ) : Oring p)‖₊ ≤ 1 :=
    ((mem_Oring_iff p _).mp ((u⁻¹ : (Oring p)ˣ) : Oring p).2).2
  have hprod : ((u : Oring p) : PadicAlgCl p) * (((u⁻¹ : (Oring p)ˣ) : Oring p) : PadicAlgCl p) = 1 := by
    have h := congrArg (fun z : Oring p => (z : PadicAlgCl p)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h
    exact h
  have hmul : ‖((u : Oring p) : PadicAlgCl p)‖₊ * ‖(((u⁻¹ : (Oring p)ˣ) : Oring p) : PadicAlgCl p)‖₊ = 1 := by
    rw [← nnnorm_mul, hprod, nnnorm_one]
  apply le_antisymm h1
  by_contra hcon
  push Not at hcon
  have : ‖((u : Oring p) : PadicAlgCl p)‖₊ * ‖(((u⁻¹ : (Oring p)ˣ) : Oring p) : PadicAlgCl p)‖₊ < 1 * 1 :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos hcon h2 (by positivity) one_pos
  rw [hmul, one_mul] at this
  exact lt_irrefl _ this

theorem exists_mul_eq_of_nnnorm_lt_one {x : PadicAlgCl p} (hx : x ∈ Oring p) (hvx : ‖x‖₊ < 1) :
    ∃ y ∈ Oring p, x = ((p : ℕ) : PadicAlgCl p) * y := by
  obtain ⟨hxI, hxA⟩ := (mem_Oring_iff p x).mp hx
  have hvle := nnnorm_le_of_lt_one p x hxI hvx
  have hp0 : ((p : ℕ) : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hvppos : 0 < ‖((p : ℕ) : PadicAlgCl p)‖₊ := nnnorm_pos.mpr hp0
  refine ⟨x / ((p : ℕ) : PadicAlgCl p), ?_, (mul_div_cancel₀ x hp0).symm⟩
  refine (mem_Oring_iff p _).mpr ⟨fun σ hσ => ?_, ?_⟩
  · rw [map_div₀, hxI σ hσ, map_natCast]
  · rw [nnnorm_div]
    exact div_le_one_of_le₀ hvle (by positivity)

theorem irreducible_p : Irreducible (((p : ℕ) : Oring p)) := by
  have hp0 : ((p : ℕ) : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hvp : ‖((p : ℕ) : PadicAlgCl p)‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, norm_natCast_p, NNReal.coe_one]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hvppos : 0 < ‖((p : ℕ) : PadicAlgCl p)‖₊ := nnnorm_pos.mpr hp0
  have hcoe : (((p : ℕ) : Oring p) : PadicAlgCl p) = ((p : ℕ) : PadicAlgCl p) := by simp
  constructor
  · intro hunit
    have := nnnorm_eq_one_of_isUnit p hunit
    rw [hcoe] at this
    rw [this] at hvp
    exact lt_irrefl _ hvp
  · rintro ⟨a, haO⟩ ⟨b, hbO⟩ hab
    have hab' : ((p : ℕ) : PadicAlgCl p) = a * b := by
      have := congrArg (Subtype.val (p := (· ∈ Oring p))) hab
      simpa using this
    have hvab : ‖((p : ℕ) : PadicAlgCl p)‖₊ = ‖a‖₊ * ‖b‖₊ := by rw [hab', nnnorm_mul]
    have ha0 : a ≠ 0 := by rintro rfl; exact hp0 (by simp [hab'])
    have hb0 : b ≠ 0 := by rintro rfl; exact hp0 (by simp [hab'])
    obtain ⟨haI, haA⟩ := (mem_Oring_iff p a).mp haO
    obtain ⟨hbI, hbA⟩ := (mem_Oring_iff p b).mp hbO
    rcases lt_or_eq_of_le haA with hva | hva
    · have hvale := nnnorm_le_of_lt_one p a haI hva
      have hvb1 : ‖b‖₊ = 1 := by
        apply le_antisymm hbA
        have hineq : ‖((p : ℕ) : PadicAlgCl p)‖₊ * 1 ≤ ‖((p : ℕ) : PadicAlgCl p)‖₊ * ‖b‖₊ := by
          calc ‖((p : ℕ) : PadicAlgCl p)‖₊ * 1 = ‖a‖₊ * ‖b‖₊ := by rw [mul_one, hvab]
            _ ≤ ‖((p : ℕ) : PadicAlgCl p)‖₊ * ‖b‖₊ := mul_le_mul_of_nonneg_right hvale (by positivity)
        exact le_of_mul_le_mul_left hineq hvppos
      exact Or.inr (isUnit_of_nnnorm_eq_one p hbO hvb1)
    · exact Or.inl (isUnit_of_nnnorm_eq_one p haO hva)

theorem associated_pow_of_ne_zero :
    ∀ x : Oring p, (x : PadicAlgCl p) ≠ 0 → ∃ n : ℕ, Associated (((p : ℕ) : Oring p) ^ n) x := by

  have hp0 : ((p : ℕ) : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hvp : ‖((p : ℕ) : PadicAlgCl p)‖₊ < 1 := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm, norm_natCast_p, NNReal.coe_one]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hvppos : 0 < ‖((p : ℕ) : PadicAlgCl p)‖₊ := nnnorm_pos.mpr hp0

  have hbound : ∀ x : PadicAlgCl p, x ≠ 0 → ∃ M : ℕ, ‖((p : ℕ) : PadicAlgCl p)‖₊ ^ M ≤ ‖x‖₊ := by
    intro x hx
    have hxpos : 0 < ‖x‖₊ := nnnorm_pos.mpr hx
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hxpos hvp
    exact ⟨M, hM.le⟩
  suffices h : ∀ (M : ℕ) (x : Oring p), (x : PadicAlgCl p) ≠ 0 →
      ‖((p : ℕ) : PadicAlgCl p)‖₊ ^ M ≤ ‖(x : PadicAlgCl p)‖₊ →
      ∃ n : ℕ, Associated (((p : ℕ) : Oring p) ^ n) x by
    intro x hx
    obtain ⟨M, hM⟩ := hbound x hx
    exact h M x hx hM
  intro M
  induction M with
  | zero =>
      intro x hx0 hM
      rw [pow_zero] at hM
      have hv1 : ‖(x : PadicAlgCl p)‖₊ = 1 := le_antisymm ((mem_Oring_iff p _).mp x.2).2 hM
      refine ⟨0, ?_⟩
      rw [pow_zero]
      exact (associated_one_iff_isUnit.mpr (isUnit_of_nnnorm_eq_one p x.2 hv1)).symm
  | succ M ih =>
      intro x hx0 hM
      rcases lt_or_eq_of_le ((mem_Oring_iff p _).mp x.2).2 with hvx | hvx
      · obtain ⟨y, hyO, hxy⟩ := exists_mul_eq_of_nnnorm_lt_one p x.2 hvx
        have hy0 : y ≠ 0 := by rintro rfl; exact hx0 (by simp [hxy])
        have hMy : ‖((p : ℕ) : PadicAlgCl p)‖₊ ^ M ≤ ‖y‖₊ := by
          have h1 : ‖(x : PadicAlgCl p)‖₊ = ‖((p : ℕ) : PadicAlgCl p)‖₊ * ‖y‖₊ := by
            rw [hxy, nnnorm_mul]
          rw [pow_succ', h1] at hM
          exact le_of_mul_le_mul_left hM hvppos
        obtain ⟨n, hn⟩ := ih ⟨y, hyO⟩ hy0 hMy
        refine ⟨n + 1, ?_⟩
        have hxy' : x = ((p : ℕ) : Oring p) * ⟨y, hyO⟩ :=
          Subtype.ext (by push_cast; exact hxy)
        rw [hxy', pow_succ']
        exact (Associated.refl _).mul_mul hn
      · exact ⟨0, by
          rw [pow_zero]
          exact (associated_one_iff_isUnit.mpr (isUnit_of_nnnorm_eq_one p x.2 hvx)).symm⟩

theorem isDVR : IsDiscreteValuationRing (Oring p) := by
  have : IsDomain (Oring p) := inferInstance
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨((p : ℕ) : Oring p), irreducible_p p, ?_⟩
  intro x hx
  exact associated_pow_of_ne_zero p x (fun h => hx (Subtype.ext h))

theorem mem_inertia_of_forall_fix (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hfix : ∀ x ∈ Oring p, σ x = x) : σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] := by
  rw [← PadicAlgCl.fixingSubgroup_fixedField_inertiaSubgroupIn]
  rw [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff]
  rintro y hy
  have hyI : ∀ τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], τ y = y :=
    (IntermediateField.mem_fixedField_iff _ _).mp hy
  change σ y = y
  by_cases hy1 : ‖y‖₊ ≤ 1
  · exact hfix y ((mem_Oring_iff p y).mpr ⟨hyI, hy1⟩)
  · push Not at hy1
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
    have hinv : y⁻¹ ∈ Oring p := by
      refine (mem_Oring_iff p _).mpr ⟨fun τ hτ => by rw [map_inv₀, hyI τ hτ], ?_⟩
      rw [nnnorm_inv]
      exact inv_le_one_of_one_le₀ hy1.le
    have h := hfix _ hinv
    rw [map_inv₀] at h
    exact inv_injective h

end S17ShRing

open S17ShRing in

theorem solution (p : ℕ) [Fact p.Prime] :
    ∃ O : Subring (PadicAlgCl p),
      (O : Set (PadicAlgCl p)) ⊆ padicIntegers p ∧
      (∀ x : ℤ_[p], algebraMap ℤ_[p] (PadicAlgCl p) x ∈ O) ∧
      IsDiscreteValuationRing ↥O ∧ Irreducible ((p : ℕ) : ↥O) ∧
      (∀ x : ↥O, ‖(x : PadicAlgCl p)‖₊ < 1 → ¬ IsUnit x) ∧
      (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
        σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ↔ ∀ x ∈ O, σ x = x) ∧
      ∀ y ∈ padicIntegers p,
        (∀ σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p], σ y = y) → y ∈ O := by
  refine ⟨Oring p, ?_, ?_, isDVR p, irreducible_p p, ?_, ?_, ?_⟩
  · intro x hx
    exact ((mem_Oring_iff p x).mp hx).2
  · intro x
    refine (mem_Oring_iff p _).mpr ⟨fun σ _ => ?_, ?_⟩
    · rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), AlgEquiv.commutes]
    · rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p)]
      change ‖((x : ℚ_[p]) : PadicAlgCl p)‖₊ ≤ 1
      rw [← NNReal.coe_le_coe, coe_nnnorm, PadicAlgCl.norm_extends, NNReal.coe_one]
      exact PadicInt.norm_le_one x
  · intro x hvx hunit
    have := nnnorm_eq_one_of_isUnit p hunit
    rw [this] at hvx
    exact lt_irrefl _ hvx
  · intro σ
    constructor
    · intro hσ x hx
      exact ((mem_Oring_iff p x).mp hx).1 σ hσ
    · exact mem_inertia_of_forall_fix p σ
  · intro y hy hfix
    exact (mem_Oring_iff p y).mpr ⟨hfix, hy⟩

#print axioms solution

end S_PadicAlgCl_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq
end P2MW
export P2MW.S_PadicAlgCl_exists_dvr_subring_mem_inertiaSubgroupIn_iff_forall_apply_eq (solution)
