-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_ker_eq_d460a27c2b3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:36:42.79086+00:00
-- url     : https://prove2.me/submissions/a93eb823-3321-45a8-aac6-3068817633a2

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecKer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_genPar_algIndep_175e337cdc44
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_coeff_mem_of_sum_a9b6b01ae01d
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_exists_ringKrullDim_eq_trdeg
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mono
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimStrictDrop_proof_15777780f510


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial Cardinal
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecKer
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecKer
theorem _root_.solution {k L : Type} [Field k] [CommRing L] (hL : IsField L) [Algebra k L] {n e : ℕ}
    [Algebra (GenParField k e n) L] [IsScalarTower k (GenParField k e n) L]
    (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime]
    (hdim : ringKrullDim (MvPolynomial (Fin n) k ⧸ Q) = ((e + 1 : ℕ) : WithBot ℕ∞)) (x : Fin n → L)
    (hgen : ∀ z : L, ∃ p : MvPolynomial (Fin n) (GenParField k e n), aeval x p = z)
    (hR1 : ∀ i : Fin e, ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * x j = 0)
    (hR2 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * x j = 1)
    (hQ : ∀ q ∈ Q, aeval x q = 0) :
    RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L) = Q := by
  classical
  letI : Field L := hL.toField
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * x j = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [h j, mul_zero]
    exact one_ne_zero (hR2.symm.trans h0)
  let y : Par e n → L := fun p => algebraMap (GenParField k e n) L (genPar k e n p)
  let col : Par e n → Fin n := fun p => Sum.elim Prod.snd id p
  let t : Set L := Set.range x ∪ y '' {p | col p = j₀}ᶜ
  have hxK : ∀ j, x j ∈ IntermediateField.adjoin k t :=
    fun j => IntermediateField.subset_adjoin k t (Or.inl ⟨j, rfl⟩)
  have hyK' : ∀ p, col p ≠ j₀ → y p ∈ IntermediateField.adjoin k t :=
    fun p hp => IntermediateField.subset_adjoin k t (Or.inr ⟨p, hp, rfl⟩)
  have hyK : ∀ p, y p ∈ IntermediateField.adjoin k t := by
    rintro (⟨i, j⟩ | j)
    · by_cases hj : j = j₀
      · rw [hj]
        exact coeff_mem_of_sum _ x (fun j => y (.inl (i, j))) 0 j₀ hxK hj₀ (hR1 i) (zero_mem _)
          (fun j' hj' => hyK' _ hj')
      · exact hyK' _ hj
    · by_cases hj : j = j₀
      · rw [hj]
        exact coeff_mem_of_sum _ x (fun j => y (.inr j)) 1 j₀ hxK hj₀ hR2 (one_mem _)
          (fun j' hj' => hyK' _ hj')
      · exact hyK' _ hj
  have hpoly : ∀ a : MvPolynomial (Par e n) k,
      algebraMap (GenParField k e n) L (algebraMap _ (GenParField k e n) a) ∈
        IntermediateField.adjoin k t := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C c =>
      rw [← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply k (MvPolynomial (Par e n) k) (GenParField k e n),
        ← IsScalarTower.algebraMap_apply k (GenParField k e n) L]
      exact IntermediateField.algebraMap_mem _ c
    | add a b ha hb =>
      rw [map_add, map_add]
      exact add_mem ha hb
    | mul_X a p ha =>
      rw [map_mul, map_mul]
      exact mul_mem ha (hyK p)
  have hF : ∀ f, algebraMap (GenParField k e n) L f ∈ IntermediateField.adjoin k t := by
    intro f
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Par e n) k) f
    rw [map_div₀]
    exact div_mem (hpoly a) (hpoly b)
  have hall : ∀ p : MvPolynomial (Fin n) (GenParField k e n),
      aeval x p ∈ IntermediateField.adjoin k t := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [aeval_C]
      exact hF c
    | add a b ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | mul_X a j ha =>
      rw [map_mul, aeval_X]
      exact mul_mem ha (hxK j)
  have htop : IntermediateField.adjoin k t = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨p, rfl⟩ := hgen z
    exact hall p
  have : Algebra.IsAlgebraic (Algebra.adjoin k t) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, htop, Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  have : FaithfulSMul k L :=
    (faithfulSMul_iff_algebraMap_injective k L).2 (algebraMap k L).injective
  obtain ⟨u, hut, hu⟩ := exists_isTranscendenceBasis_subset (R := k) t
  have hyind : AlgebraicIndependent k y :=
    (genPar_algIndep k e n).map' (f := IsScalarTower.toAlgHom k (GenParField k e n) L)
      (algebraMap (GenParField k e n) L).injective
  have hPar : #(Par e n) ≤ Algebra.trdeg k L := hyind.cardinalMk_le_trdeg
  have hucard : #u = Algebra.trdeg k L := hu.cardinalMk_eq_trdeg
  have hQP : Q ≤ RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L) :=
    fun q hq => (RingHom.mem_ker).2 (hQ q hq)
  have : (RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L)).IsPrime := RingHom.ker_isPrime _
  refine le_antisymm ?_ hQP
  by_contra hle
  have hlt : Q < RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L) := lt_of_le_not_ge hQP hle
  have hdrop := NumbersDVR.DimStrictDrop.proof _ Q _ hlt
  rw [hdim] at hdrop
  have : Algebra.FiniteType k
      (MvPolynomial (Fin n) k ⧸ RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L)) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _)
      (Ideal.Quotient.mkₐ_surjective k _)
  obtain ⟨m, hm, htr⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg k
    (A := MvPolynomial (Fin n) k ⧸ RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L))
  rw [hm] at hdrop
  have hme : m ≤ e := by
    have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := by
      push_cast
      exact hdrop
    have := (Nat.cast_le (α := WithBot ℕ∞)).1 h'
    omega

  have hu1 : AlgebraicIndependent k ((↑) : (u ∩ Set.range x : Set L) → L) :=
    hu.1.mono Set.inter_subset_left
  let v : (u ∩ Set.range x : Set L) → MvPolynomial (Fin n) k ⧸
      RingHom.ker (aeval x : MvPolynomial (Fin n) k →ₐ[k] L) :=
    fun z => Ideal.Quotient.mk _ (X z.2.2.choose)
  have hcomp : ⇑(Ideal.kerLiftAlg (aeval x : MvPolynomial (Fin n) k →ₐ[k] L)) ∘ v =
      ((↑) : (u ∩ Set.range x : Set L) → L) := by
    funext z
    simp only [Function.comp_apply, v, Ideal.kerLiftAlg_mk, aeval_X]
    exact z.2.2.choose_spec
  have hv : AlgebraicIndependent k v :=
    AlgebraicIndependent.of_comp (Ideal.kerLiftAlg _) (by rw [hcomp]; exact hu1)
  have hcard1 : #(u ∩ Set.range x : Set L) ≤ m := htr ▸ hv.cardinalMk_le_trdeg
  have hsub : u ⊆ (u ∩ Set.range x) ∪ y '' {p | col p = j₀}ᶜ := fun z hz =>
    (hut hz).elim (fun h => Or.inl ⟨hz, h⟩) Or.inr
  obtain ⟨a, ha⟩ := Cardinal.lt_aleph0.1 (Cardinal.lt_aleph0_of_finite {p : Par e n | col p = j₀})
  obtain ⟨b, hb⟩ := Cardinal.lt_aleph0.1
    (Cardinal.lt_aleph0_of_finite ({p : Par e n | col p = j₀}ᶜ : Set (Par e n)))
  have hE0 : #(Fin e ⊕ Unit) ≤ #{p : Par e n | col p = j₀} := by
    refine Cardinal.mk_le_of_injective (f := fun s => match s with
      | .inl i => ⟨.inl (i, j₀), rfl⟩
      | .inr _ => ⟨.inr j₀, rfl⟩) ?_
    rintro (i | u) (i' | u') h
    · have h' := congrArg Subtype.val h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h'
      exact congrArg Sum.inl h'.1
    · exact (Sum.inl_ne_inr (congrArg Subtype.val h)).elim
    · exact (Sum.inr_ne_inl (congrArg Subtype.val h)).elim
    · exact congrArg Sum.inr (Subsingleton.elim _ _)
  have hea : e + 1 ≤ a := by
    rw [ha, Cardinal.mk_fintype, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at hE0
    exact_mod_cast hE0
  have hchain : ((a + b : ℕ) : Cardinal) ≤ ((m + b : ℕ) : Cardinal) := by
    push_cast
    calc (a : Cardinal) + b = #(Par e n) := by rw [← ha, ← hb]; exact Cardinal.mk_sum_compl _
      _ ≤ Algebra.trdeg k L := hPar
      _ = #u := hucard.symm
      _ ≤ #((u ∩ Set.range x) ∪ y '' {p | col p = j₀}ᶜ : Set L) := Cardinal.mk_le_mk_of_subset hsub
      _ ≤ #(u ∩ Set.range x : Set L) + #(y '' {p | col p = j₀}ᶜ : Set L) := Cardinal.mk_union_le _ _
      _ ≤ m + b := add_le_add hcard1 (Cardinal.mk_image_le.trans hb.le)
  have : a + b ≤ m + b := by exact_mod_cast hchain
  omega
end GroundTheory.Heights₂.Heights.Vertical.GenSecKer
