-- Prove2me | solution 1 for PadicAlgCl.exists_nnnorm_pow_sub_one_eq_zpow_of_mem_adjoin_rootsOfUnity_coprime_sup_cyclotomicTower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d82c385c-539d-52fa-b61a-c22dde73fce7

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_PadicAlgCl_CyclotomicTower
import Theorems.Thm_PadicAlgCl_finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow
import Theorems.Thm_PadicAlgCl_finrank_sup_cyclotomicTower_of_forall_norm_eq_zpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_nnnorm_pow_sub_one_eq_zpow_of_mem_adjoin_rootsOfUnity_coprime_sup_cyclotomicTower
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"
p2m_attr_erase "simp" "ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 6400000

open scoped NNReal
open IntermediateField

namespace E87L2P

variable (p : ℕ) [Fact p.Prime]

local notation "Qpb" => PadicAlgCl p

theorem norm_apply_eq (K : IntermediateField ℚ_[p] Qpb) (E : IntermediateField K Qpb)
    (σ : E →ₐ[K] Qpb) (x : E) : ‖σ x‖ = ‖(x : Qpb)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  congr 1
  have h1 : minpoly ℚ_[p] (σ x) = minpoly ℚ_[p] x :=
    minpoly.algHom_eq (σ.restrictScalars ℚ_[p]) (σ.restrictScalars ℚ_[p]).injective x
  haveI : Module.Free K E := Module.Free.of_divisionRing K E
  have h2 : minpoly ℚ_[p] ((x : Qpb)) = minpoly ℚ_[p] x :=
    minpoly.algHom_eq ((IsScalarTower.toAlgHom K E Qpb).restrictScalars ℚ_[p]) Subtype.val_injective x
  rw [h1, h2]

theorem finite_layer (n : ℕ) (hn : 0 < n) (w : Qpb) (hw0 : w ≠ 0)
    (hw : w ∈ IntermediateField.adjoin ℚ_[p] {ζ : Qpb | ζ ^ (p ^ n - 1) = 1}
      ⊔ PadicAlgCl.cyclotomicTower p 1) :
    ∃ m : ℤ, ‖w‖ ^ (p - 1) = (p : ℝ) ^ m := by
  have hp := (Fact.out : p.Prime)
  set K : IntermediateField ℚ_[p] Qpb := IntermediateField.adjoin ℚ_[p] {ζ : Qpb | ζ ^ (p ^ n - 1) = 1}
    with hKdef
  obtain ⟨-, hKrank, hKval, -⟩ := PadicAlgCl.finrank_adjoin_rootsOfUnity_eq_and_forall_norm_eq_zpow p n hn
  rw [← hKdef] at hKrank hKval
  haveI : FiniteDimensional ℚ_[p] K := Module.finite_of_finrank_pos (by rw [hKrank]; exact hn)

  set E : IntermediateField K Qpb := IntermediateField.adjoin K {ζ : Qpb | ζ ^ (p ^ 1) = 1} with hEdef
  have hE : E.restrictScalars ℚ_[p] = K ⊔ PadicAlgCl.cyclotomicTower p 1 := by
    rw [hEdef, hKdef, IntermediateField.adjoin_adjoin_left, IntermediateField.adjoin_union]
    rfl
  have hwE : w ∈ E := by
    have : w ∈ E.restrictScalars ℚ_[p] := by rw [hE]; exact hw
    exact this

  have hsup := PadicAlgCl.finrank_sup_cyclotomicTower_of_forall_norm_eq_zpow p K hKval 1 one_pos
  rw [← hE] at hsup
  have hrs : Module.finrank ℚ_[p] (E.restrictScalars ℚ_[p]) = Module.finrank ℚ_[p] E := rfl
  rw [hrs, hKrank] at hsup
  simp only [Nat.sub_self, pow_zero, mul_one] at hsup
  haveI : Module.Free K E := Module.Free.of_divisionRing K E
  have htower := Module.finrank_mul_finrank ℚ_[p] K E
  rw [hKrank, hsup] at htower
  have hdeg : Module.finrank K E = p - 1 := by
    have := Nat.eq_of_mul_eq_mul_left hn htower
    exact this
  haveI : FiniteDimensional ℚ_[p] E := Module.finite_of_finrank_pos (by
    rw [hsup]; exact Nat.mul_pos hn (Nat.sub_pos_of_lt hp.one_lt))
  haveI : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ_[p] K E

  set x : E := ⟨w, hwE⟩ with hxdef
  have hx0 : x ≠ 0 := by
    intro h; apply hw0; simpa [hxdef] using congrArg Subtype.val h
  have hprod := Algebra.norm_eq_prod_embeddings K Qpb x
  have hnormval : ‖algebraMap K Qpb (Algebra.norm K x)‖ = ‖w‖ ^ (p - 1) := by
    rw [hprod, norm_prod, Finset.prod_congr rfl (fun σ _ => norm_apply_eq p K E σ x)]
    rw [Finset.prod_const, Finset.card_univ, AlgHom.card, hdeg]

  have hmem : algebraMap K Qpb (Algebra.norm K x) ∈ K := (Algebra.norm K x).2
  have hne : algebraMap K Qpb (Algebra.norm K x) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap K Qpb).injective]
    exact Algebra.norm_ne_zero_iff.mpr hx0
  obtain ⟨k, hk⟩ := hKval _ hmem hne
  exact ⟨k, by rw [← hnormval, hk]⟩

theorem main (w : Qpb) (hw0 : w ≠ 0)
    (hw : w ∈ IntermediateField.adjoin ℚ_[p] {ζ : Qpb | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1}
      ⊔ PadicAlgCl.cyclotomicTower p 1) :
    ∃ m : ℤ, ‖w‖₊ ^ (p - 1) = (p : ℝ≥0) ^ m := by
  have hp := (Fact.out : p.Prime)
  classical

  have hunion : IntermediateField.adjoin ℚ_[p]
      ({ζ : Qpb | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1} ∪ {ζ : Qpb | ζ ^ (p ^ 1) = 1})
      = IntermediateField.adjoin ℚ_[p] {ζ : Qpb | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1}
        ⊔ PadicAlgCl.cyclotomicTower p 1 := by
    rw [IntermediateField.adjoin_union]; rfl
  have hw' := hw
  rw [← hunion] at hw'
  obtain ⟨T, hT, hwT⟩ := IntermediateField.exists_finset_of_mem_adjoin hw'
  have key : ∀ t : Qpb, ∃ N : ℕ, ¬ p ∣ N ∧ ((∃ N' : ℕ, ¬ p ∣ N' ∧ t ^ N' = 1) → t ^ N = 1) := by
    intro t
    by_cases h : ∃ N' : ℕ, ¬ p ∣ N' ∧ t ^ N' = 1
    · obtain ⟨N', h1, h2⟩ := h
      exact ⟨N', h1, fun _ => h2⟩
    · exact ⟨1, hp.not_dvd_one, fun h' => (h h').elim⟩
  choose Nf hNf1 hNf2 using key
  set N := ∏ t ∈ T, Nf t with hNdef
  have hpN : Nat.Coprime p N :=
    Nat.Coprime.prod_right fun t _ => (Nat.Prime.coprime_iff_not_dvd hp).mpr (hNf1 t)
  have hNpos : 0 < N :=
    Finset.prod_pos fun t _ => Nat.pos_of_ne_zero fun h0 => hNf1 t (h0 ▸ dvd_zero p)
  set n := Nat.totient N with hndef
  have hn : 0 < n := Nat.totient_pos.mpr hNpos
  have hmod : N ∣ p ^ n - 1 := by
    have h1 : p ^ n ≡ 1 [MOD N] := Nat.ModEq.pow_totient hpN
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp h1.symm
  have hTsub : (↑T : Set Qpb) ⊆
      ((IntermediateField.adjoin ℚ_[p] {ζ : Qpb | ζ ^ (p ^ n - 1) = 1}
        ⊔ PadicAlgCl.cyclotomicTower p 1 : IntermediateField ℚ_[p] Qpb) : Set Qpb) := by
    intro t ht
    rcases hT ht with h0 | h1
    · apply SetLike.le_def.mp (le_sup_left (b := PadicAlgCl.cyclotomicTower p 1))
      apply IntermediateField.subset_adjoin
      show t ^ (p ^ n - 1) = 1
      obtain ⟨k, hk⟩ := hmod
      obtain ⟨j, hj⟩ := Finset.dvd_prod_of_mem Nf ht
      rw [hk, hNdef, hj, mul_assoc, pow_mul, hNf2 t h0, one_pow]
    · apply SetLike.le_def.mp (le_sup_right (a := IntermediateField.adjoin ℚ_[p] {ζ : Qpb | ζ ^ (p ^ n - 1) = 1}))
      exact PadicAlgCl.mem_cyclotomicTower_of_pow_eq_one p h1
  have hwmem : w ∈ IntermediateField.adjoin ℚ_[p] {ζ : Qpb | ζ ^ (p ^ n - 1) = 1}
      ⊔ PadicAlgCl.cyclotomicTower p 1 :=
    (IntermediateField.adjoin_le_iff.mpr hTsub) hwT
  obtain ⟨m, hm⟩ := finite_layer p n hn w hw0 hwmem
  refine ⟨m, ?_⟩
  rw [← NNReal.coe_inj, NNReal.coe_pow, coe_nnnorm, hm, NNReal.coe_zpow, NNReal.coe_natCast]

end E87L2P

theorem solution
    (p : ℕ) [Fact p.Prime] (w : PadicAlgCl p) (hw0 : w ≠ 0)
    (hw : w ∈ IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ∃ N : ℕ, ¬ p ∣ N ∧ ζ ^ N = 1}
      ⊔ PadicAlgCl.cyclotomicTower p 1) :
    ∃ m : ℤ, ‖w‖₊ ^ (p - 1) = (p : ℝ≥0) ^ m :=
  E87L2P.main p w hw0 hw

end S_PadicAlgCl_exists_nnnorm_pow_sub_one_eq_zpow_of_mem_adjoin_rootsOfUnity_coprime_sup_cyclotomicTower
end P2MW
export P2MW.S_PadicAlgCl_exists_nnnorm_pow_sub_one_eq_zpow_of_mem_adjoin_rootsOfUnity_coprime_sup_cyclotomicTower (solution)
