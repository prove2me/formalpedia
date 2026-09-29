-- Prove2me | solution 1 for PadicAlgCl.exists_unramified_level_char_of_sq_sub_one_mem_span_socle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c26da1dd-0026-571f-bf9a-83daa448d6fa

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime
import Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
import Theorems.Thm_PadicAlgCl_exists_apply_eq_pow_pow_of_pow_eq_one_of_not_dvd
import Theorems.Thm_PadicAlgCl_finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow
import Theorems.Thm_PadicAlgCl_exists_algEquiv_apply_eq_pow_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_unramified_level_char_of_sq_sub_one_mem_span_socle
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

namespace PadicAlgCl
p2m_export "PadicAlgCl" "fixingSubgroup_adjoin_rootsOfUnity_coprime exists_apply_eq_pow_pow_of_pow_eq_one_of_not_dvd finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow exists_algEquiv_apply_eq_pow_of_pow_eq_one"
namespace U2DeviationAux
p2m_open "PadicAlgCl"

theorem pow_pow_mul_eq_self {L : Type} [Monoid L] {w : L} {q a : ℕ} (hw : w ^ q ^ a = w) (j : ℕ) :
    w ^ q ^ (a * j) = w := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hw]

theorem pow_pow_eq_self_of_pow_sub_one {L : Type} [Monoid L] {w : L} {q a : ℕ} (hq : 0 < q)
    (hw : w ^ (q ^ a - 1) = 1) : w ^ q ^ a = w := by
  have h1 : q ^ a = (q ^ a - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)).symm
  rw [h1, pow_succ, hw, one_mul]

theorem pow_sub_one_eq_one_of_pow_pow_eq_self {L : Type} [GroupWithZero L] {w : L} {q a : ℕ}
    (hq : 0 < q) (hw0 : w ≠ 0) (hw : w ^ q ^ a = w) : w ^ (q ^ a - 1) = 1 := by
  have h1 : q ^ a = (q ^ a - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)).symm
  rw [h1, pow_succ] at hw
  exact mul_right_cancel₀ hw0 (hw.trans (one_mul w).symm)

theorem pow_pow_eq_pow_pow_of_modEq {L : Type} [Monoid L] {w : L} {q a : ℕ} (hw : w ^ q ^ a = w)
    {x y : ℕ} (h : x ≡ y [MOD a]) : w ^ q ^ x = w ^ q ^ y := by
  have key : ∀ x : ℕ, w ^ q ^ x = w ^ q ^ (x % a) := fun x => by
    conv_lhs => rw [← Nat.div_add_mod x a, pow_add, pow_mul, pow_pow_mul_eq_self hw]
  rw [key x, key y, h]

theorem pow_pred_lt_pow_sub_one {q a : ℕ} (hq : 2 ≤ q) (ha : 2 ≤ a) : q ^ (a - 1) < q ^ a - 1 := by
  have h1 : q ^ a = q * q ^ (a - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ a)]
  have h2 : 2 ≤ q ^ (a - 1) := le_trans hq (Nat.le_self_pow (by omega) q)
  have h3 : 2 * q ^ (a - 1) ≤ q ^ a := h1 ▸ Nat.mul_le_mul_right _ hq
  omega

theorem modEq_of_pow_pow_eq_pow_pow {L : Type} [CommMonoid L] {ζ : L} {q a : ℕ} (hq : 2 ≤ q)
    (ha : 2 ≤ a) (hζ : IsPrimitiveRoot ζ (q ^ a - 1)) {x y : ℕ} (h : ζ ^ q ^ x = ζ ^ q ^ y) :
    x ≡ y [MOD a] := by
  have hζa : ζ ^ q ^ a = ζ := pow_pow_eq_self_of_pow_sub_one (by omega) hζ.pow_eq_one
  have hx : ζ ^ q ^ x = ζ ^ q ^ (x % a) := pow_pow_eq_pow_pow_of_modEq hζa (Nat.mod_modEq x a).symm
  have hy : ζ ^ q ^ y = ζ ^ q ^ (y % a) := pow_pow_eq_pow_pow_of_modEq hζa (Nat.mod_modEq y a).symm
  rw [hx, hy] at h
  have hlt : ∀ z : ℕ, q ^ (z % a) < q ^ a - 1 := fun z =>
    lt_of_le_of_lt
      (Nat.pow_le_pow_right (by omega) (Nat.le_sub_one_of_lt (Nat.mod_lt z (by omega))))
      (pow_pred_lt_pow_sub_one hq ha)
  have heq : q ^ (x % a) = q ^ (y % a) := hζ.pow_inj (hlt x) (hlt y) h
  exact Nat.pow_right_injective hq heq

theorem exists_common_exponent {L : Type} [Monoid L] {p : ℕ} (hp : p.Prime) (T : Finset L)
    (hT : ∀ w ∈ T, ∃ N : ℕ, ¬ p ∣ N ∧ w ^ N = 1) :
    ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ ∀ w ∈ T, w ^ N = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, hp.not_dvd_one, by simp⟩
  | @insert a T ha ih =>
    obtain ⟨N, hN0, hNp, hN⟩ := ih fun w hw => hT w (Finset.mem_insert_of_mem hw)
    obtain ⟨Na, hNap, hNa⟩ := hT a (Finset.mem_insert_self a T)
    have hNa0 : 0 < Na := Nat.pos_of_ne_zero fun h => hNap (h ▸ dvd_zero p)
    refine ⟨N * Na, Nat.mul_pos hN0 hNa0, fun h => (hp.dvd_mul.mp h).elim hNp hNap, ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rw [mul_comm, pow_mul, hNa, one_pow]
    · rw [pow_mul, hN w hw, one_pow]

theorem pow_pow_totient_sub_one_eq_one {L : Type} [Monoid L] {p N : ℕ} (hp : p.Prime) (hN : ¬ p ∣ N)
    {w : L} (hw : w ^ N = 1) : w ^ (p ^ (p * Nat.totient N) - 1) = 1 := by
  have h1 : p ^ Nat.totient N ≡ 1 [MOD N] := Nat.ModEq.pow_totient (hp.coprime_iff_not_dvd.mpr hN)
  have h2 : p ^ (p * Nat.totient N) ≡ 1 [MOD N] := by
    rw [mul_comm, pow_mul]
    simpa using h1.pow p
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp h2.symm
  rw [hk, pow_mul, hw, one_pow]

theorem exists_intermediateField_le_fixingSubgroup_eq {K L : Type} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (S : Subgroup (L ≃ₐ[K] L)) (K₁ L₀ : IntermediateField K L)
    [FiniteDimensional K K₁] (h₁ : K₁.fixingSubgroup ≤ S) (h₀ : L₀.fixingSubgroup ≤ S) :
    ∃ M : IntermediateField K L, M ≤ K₁ ∧ M ≤ L₀ ∧ M.fixingSubgroup = S := by
  have hopen : IsOpen (S : Set (L ≃ₐ[K] L)) := Subgroup.isOpen_mono h₁ K₁.fixingSubgroup_isOpen
  let Sc : ClosedSubgroup (L ≃ₐ[K] L) := ⟨S, S.isClosed_of_isOpen hopen⟩
  refine ⟨IntermediateField.fixedField S, ?_, ?_, ?_⟩
  · calc IntermediateField.fixedField S ≤ IntermediateField.fixedField K₁.fixingSubgroup :=
          IntermediateField.fixedField_antitone h₁
      _ = K₁ := InfiniteGalois.fixedField_fixingSubgroup K₁
  · calc IntermediateField.fixedField S ≤ IntermediateField.fixedField L₀.fixingSubgroup :=
          IntermediateField.fixedField_antitone h₀
      _ = L₀ := InfiniteGalois.fixedField_fixingSubgroup L₀
  · exact InfiniteGalois.fixingSubgroup_fixedField Sc

theorem mem_fixingSubgroup_adjoin_of_forall_eq {K L : Type} [Field K] [Field L] [Algebra K L]
    {T : Set L} {g : L ≃ₐ[K] L} (hg : ∀ w ∈ T, g w = w) :
    g ∈ (IntermediateField.adjoin K T).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  refine IntermediateField.adjoin_induction K (p := fun x _ => g x = x) ?_ ?_ ?_ ?_ ?_ hx
  · exact hg
  · intro x; exact g.commutes x
  · intro x y _ _ hx hy; rw [map_add, hx, hy]
  · intro x _ hx; rw [map_inv₀, hx]
  · intro x y _ _ hx hy; rw [map_mul, hx, hy]

theorem exists_finset_le_adjoin {K L : Type} [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L) [FiniteDimensional K M] {T : Set L}
    (hM : M ≤ IntermediateField.adjoin K T) :
    ∃ T₀ : Finset L, ↑T₀ ⊆ T ∧ M ≤ IntermediateField.adjoin K (↑T₀ : Set L) := by
  classical
  let b := Module.finBasis K M
  choose Tf hTf hbTf using fun i => IntermediateField.exists_finset_of_mem_adjoin (hM (b i).2)
  refine ⟨Finset.univ.biUnion Tf, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hw
    exact hTf i hi
  · intro x hx
    have hrepr := b.sum_repr ⟨x, hx⟩
    have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • ((b i : M) : L) := by
      have := congrArg (fun y : M => (y : L)) hrepr
      simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using this.symm
    rw [hx']
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def]
    refine mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    exact IntermediateField.adjoin.mono K _ _
      (fun w hw => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hw⟩) (hbTf i)

end PadicAlgCl.U2DeviationAux

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime]
    (hpB : (p : B) ∈ IsLocalRing.maximalIdeal B)
    (z : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → Bˣ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : FiniteDimensional ℚ F)
    (hzmul : ∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), z (g * h) = z g * z h)
    (hzlev : ∀ s : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), localGaloisToGlobal p s ∈ F.fixingSubgroup → z s = 1)
    (hzI : ∀ τ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] → z τ = 1)
    (t : B) (htm : t ∈ IsLocalRing.maximalIdeal B)
    (htk : ∀ m ∈ IsLocalRing.maximalIdeal B, t * m = 0)
    (hsq : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) - 1 ∈ Ideal.span {t})
    (hne : ∃ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) ≠ 1) :
    ∃ (η : B) (χ : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → ℤ), IsUnit η ∧
      groupCohomology.IsLevelConstant₁ (localGaloisToGlobal p) χ ∧
      (∀ g h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (p : ℤ) ∣ χ g + χ h - χ (g * h)) ∧
      (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (∀ w : PadicAlgCl p, w ^ (p ^ p - 1) = 1 → g w = w) ↔ (p : ℤ) ∣ χ g) ∧
      (∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), (z g : B) * (z g : B) = 1 + t * η * (χ g : B)) := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  haveI : NeZero (p ^ p - 1) := ⟨Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hp.ne_zero hp.one_lt)⟩
  haveI : CharP (IsLocalRing.ResidueField B) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
    rw [← map_natCast (IsLocalRing.residue B), IsLocalRing.residue_eq_zero_iff]; exact hpB)

  obtain ⟨g₀, hg₀⟩ := hne
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hg₀
    have h := hsq g₀
    rwa [Ideal.mem_span_singleton, zero_dvd_iff, sub_eq_zero] at h
  have hsoc : ∀ b : B, t * b = 0 → b ∈ IsLocalRing.maximalIdeal B := by
    intro b hb
    by_contra hbu
    have hu : IsUnit b := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hbu
    apply ht0
    calc t = t * b * ((hu.unit⁻¹ : Bˣ) : B) := by rw [mul_assoc, hu.mul_val_inv, mul_one]
      _ = 0 := by rw [hb, zero_mul]
  have htt : t * t = 0 := htk t htm

  choose hh hhh using fun g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) =>
    Ideal.mem_span_singleton'.mp (hsq g)
  have hzsq : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      (z g : B) * (z g : B) = 1 + t * hh g := fun g => by
    linear_combination -(hhh g)

  set h : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) → IsLocalRing.ResidueField B :=
    fun g => IsLocalRing.residue B (hh g) with hhdef
  have hadd : ∀ g g' : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), h (g * g') = h g + h g' := by
    intro g g'
    show IsLocalRing.residue B (hh (g * g')) =
      IsLocalRing.residue B (hh g) + IsLocalRing.residue B (hh g')
    rw [← map_add, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply hsoc
    have e1 := hzsq (g * g')
    have e2 := hzsq g
    have e3 := hzsq g'
    rw [hzmul, Units.val_mul] at e1
    linear_combination -e1 + ((z g' : B) * (z g' : B)) * e2 + (1 + t * hh g) * e3 +
      (hh g * hh g') * htt
  have hz1 : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), z g = 1 → h g = 0 := fun g hg => by
    show IsLocalRing.residue B (hh g) = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    apply hsoc
    have e := hzsq g
    rw [hg, Units.val_one, mul_one] at e
    linear_combination -e

  set H : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) →* Multiplicative (IsLocalRing.ResidueField B) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (h g)) (fun a b => by
      show Multiplicative.ofAdd (h (a * b)) =
        Multiplicative.ofAdd (h a) * Multiplicative.ofAdd (h b)
      rw [hadd, ofAdd_add]) with hHdef
  set S : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) := H.ker with hS
  have hmemS : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), g ∈ S ↔ h g = 0 := fun g => by
    simp only [hS, hHdef, MonoidHom.mem_ker, MonoidHom.mk'_apply, ofAdd_eq_one]
  have hIS : (padicIntegers p).inertiaSubgroupIn ℚ_[p] ≤ S := fun τ hτ =>
    (hmemS τ).mpr (hz1 τ (hzI τ hτ))
  have hL0S : (IntermediateField.adjoin ℚ_[p]
      {ζ : PadicAlgCl p | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1}).fixingSubgroup ≤ S := by
    rw [PadicAlgCl.fixingSubgroup_adjoin_rootsOfUnity_coprime p]
    exact hIS
  obtain ⟨K₁, hK₁fd, hK₁S⟩ :=
    (exists_finiteDimensional_comap_localGaloisToGlobal_iff p (fun U => U ≤ S)
      (fun U V hVU hU => le_trans hVU hU)).mp
      ⟨F, hF, fun s hs => (hmemS s).mpr (hz1 s (hzlev s hs))⟩
  haveI := hK₁fd

  obtain ⟨M, hMK₁, hML₀, hMS⟩ :=
    PadicAlgCl.U2DeviationAux.exists_intermediateField_le_fixingSubgroup_eq S K₁ _ hK₁S hL0S
  haveI : FiniteDimensional ℚ_[p] M :=
    Module.Finite.of_injective (IntermediateField.inclusion hMK₁).toLinearMap
      (IntermediateField.inclusion hMK₁).injective
  obtain ⟨T₀, hT₀, hMT₀⟩ := PadicAlgCl.U2DeviationAux.exists_finset_le_adjoin M hML₀
  obtain ⟨N, hN0, hNp, hNT⟩ :=
    PadicAlgCl.U2DeviationAux.exists_common_exponent hp T₀ (fun w hw => hT₀ hw)
  set f : ℕ := p * Nat.totient N with hf
  have hf0 : 0 < f := Nat.mul_pos hp.pos (Nat.totient_pos.mpr hN0)
  have hMf : M ≤ IntermediateField.adjoin ℚ_[p] {w : PadicAlgCl p | w ^ (p ^ f - 1) = 1} :=
    hMT₀.trans (IntermediateField.adjoin.mono _ _ _ fun w hw =>
      PadicAlgCl.U2DeviationAux.pow_pow_totient_sub_one_eq_one hp hNp (hNT w hw))
  have hA : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      (∀ w : PadicAlgCl p, w ^ (p ^ f - 1) = 1 → g w = w) → h g = 0 := by
    intro g hg
    apply (hmemS g).mp
    rw [← hMS]
    exact IntermediateField.fixingSubgroup_antitone hMf
      (PadicAlgCl.U2DeviationAux.mem_fixingSubgroup_adjoin_of_forall_eq hg)

  have hpf_dvd : ∀ w : PadicAlgCl p, w ^ (p ^ p - 1) = 1 → w ^ (p ^ f - 1) = 1 := by
    intro w hw
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne (p ^ p - 1))] at hw
      exact zero_ne_one hw
    have h1 : w ^ p ^ p = w := PadicAlgCl.U2DeviationAux.pow_pow_eq_self_of_pow_sub_one hp.pos hw
    have h2 : w ^ p ^ f = w := by
      rw [hf]; exact PadicAlgCl.U2DeviationAux.pow_pow_mul_eq_self h1 _
    exact PadicAlgCl.U2DeviationAux.pow_sub_one_eq_one_of_pow_pow_eq_self hp.pos hw0 h2

  obtain ⟨φ, hφ⟩ := PadicAlgCl.exists_algEquiv_apply_eq_pow_of_pow_eq_one p f hf0
  have hpf : ¬ p ∣ p ^ f - 1 := by
    intro hd
    have h1 : p ∣ p ^ f := dvd_pow_self p hf0.ne'
    have h2 : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub h1 hd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  choose kk hkk using fun g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) =>
    PadicAlgCl.exists_apply_eq_pow_pow_of_pow_eq_one_of_not_dvd p (p ^ f - 1) hpf g
  have hφpow : ∀ n : ℕ, ∀ w : PadicAlgCl p, w ^ (p ^ f - 1) = 1 → (φ ^ n) w = w ^ p ^ n := by
    intro n
    induction n with
    | zero => intro w _; simp
    | succ n ih =>
      intro w hw
      rw [pow_succ, AlgEquiv.mul_apply, hφ w hw, map_pow, ih w hw, ← pow_mul, ← pow_succ]

  have hhg : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      h g = (kk g : IsLocalRing.ResidueField B) * h φ := by
    intro g
    have hu : h ((φ ^ kk g)⁻¹ * g) = 0 := by
      apply hA
      intro w hw
      rw [AlgEquiv.mul_apply, hkk g w hw, ← hφpow (kk g) w hw, AlgEquiv.aut_inv,
        AlgEquiv.symm_apply_apply]
    have h1 : h g = h (φ ^ kk g) + h ((φ ^ kk g)⁻¹ * g) := by
      rw [← hadd, mul_inv_cancel_left]
    have h2 : ∀ n : ℕ, h (φ ^ n) = (n : IsLocalRing.ResidueField B) * h φ := by
      intro n
      induction n with
      | zero =>
        have e := hadd 1 1
        rw [mul_one] at e
        rw [pow_zero, Nat.cast_zero, zero_mul]
        linear_combination -e
      | succ n ih => rw [pow_succ, hadd, ih]; push_cast; ring
    rw [h1, h2, hu, add_zero]
  have hφne : h φ ≠ 0 := by
    intro h0
    apply hg₀
    have e : h g₀ = 0 := by rw [hhg g₀, h0, mul_zero]
    have hm : hh g₀ ∈ IsLocalRing.maximalIdeal B := (IsLocalRing.residue_eq_zero_iff _).mp e
    rw [hzsq g₀, htk _ hm, add_zero]

  have hex : ∀ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      ∃ n : ℕ, ∀ w : PadicAlgCl p, w ^ (p ^ p - 1) = 1 → g w = w ^ p ^ n :=
    fun g => ⟨kk g, fun w hw => hkk g w (hpf_dvd w hw)⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ p - 1)
  have hζR : ζ₀ ^ (p ^ p - 1) = 1 := hζ₀.pow_eq_one

  have hKpfd : FiniteDimensional ℚ_[p]
      (IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (p ^ p - 1) = 1}) := by
    obtain ⟨-, hfin, -, -⟩ :=
      PadicAlgCl.finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow p p hp.pos
    exact Module.finite_of_finrank_pos (by rw [hfin]; exact hp.pos)
  refine ⟨hh φ, fun g => ((Nat.find (hex g) : ℕ) : ℤ),
    (IsLocalRing.residue_ne_zero_iff_isUnit (hh φ)).mp hφne, ?_, ?_, ?_, ?_⟩
  ·
    obtain ⟨F', hF', hF'le⟩ := (exists_finiteDimensional_comap_localGaloisToGlobal_iff p
        (fun U => U ≤ (IntermediateField.adjoin ℚ_[p]
          {ζ : PadicAlgCl p | ζ ^ (p ^ p - 1) = 1}).fixingSubgroup)
        (fun U V hVU hU => le_trans hVU hU)).mpr ⟨_, hKpfd, le_rfl⟩
    refine ⟨F', hF', fun g s hs => ?_⟩
    have hsw : ∀ w : PadicAlgCl p, w ^ (p ^ p - 1) = 1 → s w = w := fun w hw =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp (hF'le hs) w
        (IntermediateField.subset_adjoin _ _ hw)
    have heq : Nat.find (hex (g * s)) = Nat.find (hex g) := by
      apply le_antisymm
      · exact Nat.find_min' _ fun w hw => by
          rw [AlgEquiv.mul_apply, hsw w hw]; exact Nat.find_spec (hex g) w hw
      · exact Nat.find_min' _ fun w hw => by
          calc g w = (g * s) w := by rw [AlgEquiv.mul_apply, hsw w hw]
            _ = w ^ p ^ Nat.find (hex (g * s)) := Nat.find_spec (hex (g * s)) w hw
    simp only [heq]
  ·
    intro g g'
    show (p : ℤ) ∣ ((Nat.find (hex g) : ℕ) : ℤ) + ((Nat.find (hex g') : ℕ) : ℤ) -
      ((Nat.find (hex (g * g')) : ℕ) : ℤ)
    rw [← Nat.cast_add]
    refine Nat.modEq_iff_dvd.mp ?_
    apply PadicAlgCl.U2DeviationAux.modEq_of_pow_pow_eq_pow_pow hp2 hp2 hζ₀
    rw [← Nat.find_spec (hex (g * g')) ζ₀ hζR, AlgEquiv.mul_apply, Nat.find_spec (hex g') ζ₀ hζR,
      map_pow, Nat.find_spec (hex g) ζ₀ hζR, ← pow_mul, ← pow_add]
  ·
    intro g
    show (∀ w : PadicAlgCl p, w ^ (p ^ p - 1) = 1 → g w = w) ↔
      (p : ℤ) ∣ ((Nat.find (hex g) : ℕ) : ℤ)
    rw [Int.natCast_dvd_natCast]
    constructor
    · intro hg
      have h0 : Nat.find (hex g) = 0 := by
        rw [Nat.find_eq_zero]
        intro w hw
        rw [pow_zero, pow_one]
        exact hg w hw
      rw [h0]
      exact dvd_zero p
    · rintro ⟨j, hj⟩ w hw
      rw [Nat.find_spec (hex g) w hw, hj]
      exact PadicAlgCl.U2DeviationAux.pow_pow_mul_eq_self
        (PadicAlgCl.U2DeviationAux.pow_pow_eq_self_of_pow_sub_one hp.pos hw) j
  ·
    intro g
    show (z g : B) * (z g : B) = 1 + t * hh φ * (((Nat.find (hex g) : ℕ) : ℤ) : B)
    rw [Int.cast_natCast, hzsq g]
    have hkn : kk g ≡ Nat.find (hex g) [MOD p] := by
      apply PadicAlgCl.U2DeviationAux.modEq_of_pow_pow_eq_pow_pow hp2 hp2 hζ₀
      rw [← hkk g ζ₀ (hpf_dvd ζ₀ hζR), Nat.find_spec (hex g) ζ₀ hζR]
    have hres : IsLocalRing.residue B (hh g - hh φ * (Nat.find (hex g) : B)) = 0 := by
      have e1 : IsLocalRing.residue B (hh g) =
          (kk g : IsLocalRing.ResidueField B) * IsLocalRing.residue B (hh φ) := hhg g
      rw [map_sub, map_mul, map_natCast, e1, CharP.natCast_eq_natCast' _ p hkn]
      ring
    have hm : hh g - hh φ * (Nat.find (hex g) : B) ∈ IsLocalRing.maximalIdeal B :=
      (IsLocalRing.residue_eq_zero_iff _).mp hres
    linear_combination htk _ hm

end S_PadicAlgCl_exists_unramified_level_char_of_sq_sub_one_mem_span_socle
end P2MW
export P2MW.S_PadicAlgCl_exists_unramified_level_char_of_sq_sub_one_mem_span_socle (solution)
