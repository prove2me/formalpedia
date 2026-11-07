-- Prove2me | solution 1 for QEC.Coding.KT19ReedSolomon.puncturedComplementaryReedSolomon_minimumDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:57:17.243564+00:00
-- url     : https://prove2.me/submissions/c4f671c9-28be-430b-be8c-6ade257efb27

import Definitions.Def_QEC_Coding_ReedSolomon_FullLength
import Definitions.Def_QEC_Coding_ReedSolomon_Punctured
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_evaluation_mem_reedSolomonCode
import Theorems.Thm_QEC_Coding_KT19ReedSolomon_mem_reedSolomonCode
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.KT19ReedSolomon.mem_reedSolomonCode
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
namespace KT19ReedSolomon
open scoped BigOperators
private theorem keptPunctureLocation_card (p k : Nat) [Fact p.Prime]
    (hkp : k ≤ p) :
    Fintype.card (KeptPunctureLocation p k) = p - k := by
  simpa using keptPunctureLocations_card p k hkp
private theorem puncturedComplementaryReedSolomon_weight_lower_bound
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    MinimumDistanceAtLeast (puncturedReedSolomonCode p (p - l) k) (l + 1 - k) := by
  rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkp : k ≤ p := hkl.trans hlp
  intro word hword hwordNe
  rcases (mem_puncturedReedSolomonCode word).1 hword with
    ⟨full, hfull, hrestrict⟩
  rcases (mem_reedSolomonCode p (p - l) full).1 hfull with ⟨polynomial, hpoly⟩
  have hpolynomialNe : polynomial.1 ≠ 0 := by
    intro hzero
    apply hwordNe
    rw [← hrestrict, ← hpoly]
    ext point
    simp [evaluationLinearMap_apply, hzero]
  let zeroCoordinates : Finset (KeptPunctureLocation p k) :=
    Finset.univ.filter fun point => word point = 0
  let zeroImage : Finset (ZMod p) :=
    zeroCoordinates.map ⟨Subtype.val, Subtype.val_injective⟩
  have hroots : zeroImage.val ⊆ polynomial.1.roots := by
    intro point hpoint
    rcases Finset.mem_map.1 hpoint with ⟨kept, hkept, rfl⟩
    rw [Polynomial.mem_roots hpolynomialNe]
    change polynomial.1.eval kept.1 = 0
    have hzero := (Finset.mem_filter.1 hkept).2
    simpa [zeroCoordinates, ← hrestrict, ← hpoly] using hzero
  have hzeroCard : zeroCoordinates.card ≤ polynomial.1.natDegree := by
    rw [← Finset.card_map]
    exact Polynomial.card_le_degree_of_subset_roots hroots
  have hdegree : polynomial.1.natDegree < p - l := by
    have hdegree' := Polynomial.mem_degreeLT.mp polynomial.2
    rw [Polynomial.degree_eq_natDegree hpolynomialNe] at hdegree'
    exact_mod_cast hdegree'
  have hkeptCard : Fintype.card (KeptPunctureLocation p k) = p - k :=
    keptPunctureLocation_card p k hkp
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun point : KeptPunctureLocation p k => word point ≠ 0)
  have hweightPartition : HammingWeight word + zeroCoordinates.card =
      Fintype.card (KeptPunctureLocation p k) := by
    simpa [HammingWeight, hammingSupport, zeroCoordinates] using hpartition
  rw [hkeptCard] at hweightPartition
  omega
private theorem complementaryWitnessRoots_subset
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    complementaryWitnessRoots p l k h ⊆ keptPunctureLocations p k :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := keptPunctureLocations p k) (n := p - l - 1) (by
      rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
      rw [keptPunctureLocations_card p k (hkl.trans hlp)]
      omega))).1
private theorem complementaryWitness_evaluation_zero_iff
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k)
    (point : KeptPunctureLocation p k) :
    evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k h) point.1 = 0 ↔
      point.1 ∈ complementaryWitnessRoots p l k h := by
  constructor
  · intro hzero
    by_contra hnot
    have hne : ∀ root ∈ complementaryWitnessRoots p l k h, point.1 ≠ root := by
      intro root hroot heq
      apply hnot
      simpa [heq] using hroot
    have hnodalNe :
        (Lagrange.nodal (complementaryWitnessRoots p l k h)
          (fun root : ZMod p => root)).eval point.1 ≠ 0 :=
      Lagrange.eval_nodal_not_at_node
        (s := complementaryWitnessRoots p l k h)
        (v := fun root : ZMod p => root) (x := point.1) hne
    apply hnodalNe
    simpa only [evaluationLinearMap_apply, complementaryWitnessPolynomial] using hzero
  · intro hroot
    simpa [evaluationLinearMap_apply, complementaryWitnessPolynomial] using
      (Lagrange.eval_nodal_at_node
        (s := complementaryWitnessRoots p l k h)
        (v := fun root : ZMod p => root) (i := point.1) hroot)
private theorem complementaryWitness_weight
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    HammingWeight
      (restrictKept p k
        (evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k h))) =
      l + 1 - k := by
  rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkp : k ≤ p := hkl.trans hlp
  let word := restrictKept p k
    (evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k
      ⟨hp, hk, hkl, hlp, hproduct⟩))
  let zeroCoordinates : Finset (KeptPunctureLocation p k) :=
    Finset.univ.filter fun point => word point = 0
  let zeroImage : Finset (ZMod p) :=
    zeroCoordinates.map ⟨Subtype.val, Subtype.val_injective⟩
  have hzeroImage : zeroImage = complementaryWitnessRoots p l k
      ⟨hp, hk, hkl, hlp, hproduct⟩ := by
    ext point
    constructor
    · intro hpoint
      rcases Finset.mem_map.1 hpoint with ⟨kept, hkept, rfl⟩
      have hzero := (Finset.mem_filter.1 hkept).2
      exact (complementaryWitness_evaluation_zero_iff p l k
        ⟨hp, hk, hkl, hlp, hproduct⟩ kept).1 (by simpa [word] using hzero)
    · intro hpoint
      have hkept : point ∈ keptPunctureLocations p k :=
        complementaryWitnessRoots_subset p l k ⟨hp, hk, hkl, hlp, hproduct⟩ hpoint
      refine Finset.mem_map.2 ⟨⟨point, hkept⟩, ?_, rfl⟩
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (complementaryWitness_evaluation_zero_iff p l k
        ⟨hp, hk, hkl, hlp, hproduct⟩ ⟨point, hkept⟩).2 hpoint
  have hmapCard : zeroImage.card = zeroCoordinates.card := by
    simp only [zeroImage, Finset.card_map]
  have hzeroCard : zeroCoordinates.card = p - l - 1 := by
    calc
      zeroCoordinates.card = zeroImage.card := hmapCard.symm
      _ = (complementaryWitnessRoots p l k
          ⟨hp, hk, hkl, hlp, hproduct⟩).card :=
        congrArg Finset.card hzeroImage
      _ = p - l - 1 := complementaryWitnessRoots_card p l k
        ⟨hp, hk, hkl, hlp, hproduct⟩
  have hkeptCard : Fintype.card (KeptPunctureLocation p k) = p - k :=
    keptPunctureLocation_card p k hkp
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun point : KeptPunctureLocation p k => word point ≠ 0)
  have hweightPartition : HammingWeight word + zeroCoordinates.card =
      Fintype.card (KeptPunctureLocation p k) := by
    simpa [HammingWeight, hammingSupport, zeroCoordinates] using hpartition
  rw [hkeptCard] at hweightPartition
  change HammingWeight word = _
  omega
private theorem complementaryWitness_nonzero
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    restrictKept p k
      (evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k h)) ≠ 0 := by
  have hweight := complementaryWitness_weight p l k h
  intro hzero
  have hweightZero : 0 = l + 1 - k := by
    simpa [hzero] using hweight
  have : l + 1 - k = 0 := hweightZero.symm
  rcases h with ⟨hp, hk, hkl, hlp, hproduct⟩
  omega
end KT19ReedSolomon
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.KT19ReedSolomon
open scoped BigOperators
attribute [local instance] QEC.Coding.KT19ReedSolomon.instNeZeroOfPrime
namespace QEC.Coding.KT19ReedSolomon
theorem _root_.solution
    (p l k : Nat) [Fact p.Prime] (h : Admissible p l k) :
    MinimumDistance (puncturedReedSolomonCode p (p - l) k) (l + 1 - k) := by
  let witness := restrictKept p k
    (evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k h))
  have hwitness : witness ∈ (puncturedReedSolomonCode p (p - l) k).carrier := by
    apply (mem_puncturedReedSolomonCode witness).2
    refine ⟨evaluationLinearMap p (p - l) (complementaryWitnessPolynomial p l k h),
      evaluation_mem_reedSolomonCode p (p - l) (complementaryWitnessPolynomial p l k h), rfl⟩
  have hwitnessNe : witness ≠ 0 := by
    exact complementaryWitness_nonzero p l k h
  have hwitnessWeight : HammingWeight witness = l + 1 - k := by
    exact complementaryWitness_weight p l k h
  refine ⟨witness, hwitness, hwitnessNe, hwitnessWeight, ?_⟩
  exact puncturedComplementaryReedSolomon_weight_lower_bound p l k h
end QEC.Coding.KT19ReedSolomon
