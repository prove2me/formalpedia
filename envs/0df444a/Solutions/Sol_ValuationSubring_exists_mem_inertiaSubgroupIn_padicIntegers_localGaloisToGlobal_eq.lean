-- Prove2me | solution 1 for ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fcd26ef5-9e1d-5e6a-9e1f-4b861478c603

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_ValuationSubring_decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq

set_option autoImplicit false

noncomputable section

open scoped NNReal Pointwise Topology
open Polynomial

namespace SURJI

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

variable (q : ℕ) [Fact q.Prime]

local notation "Qbar" => AlgebraicClosure ℚ
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "Γq" => (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q)

section Inertia

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mem_inertiaSubgroupIn_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.inertiaSubgroupIn K ↔
      σ ∈ A.decompositionSubgroup K ∧ ∀ a : L, a ∈ A → σ a - a ∈ A.nonunits := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d.2, fun a ha => ?_⟩
    have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) d = 1 :=
      hd
    have h2 : d • IsLocalRing.residue A ⟨a, ha⟩ = IsLocalRing.residue A ⟨a, ha⟩ := by
      have := RingEquiv.congr_fun h1 (IsLocalRing.residue A ⟨a, ha⟩)
      exact this
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff] at h2
    have h3 : ((d • (⟨a, ha⟩ : A) - ⟨a, ha⟩ : A) : L) ∈ A.nonunits :=
      (A.coe_mem_nonunits_iff).2 h2
    exact h3
  · rintro ⟨hσ, h⟩
    refine ⟨⟨σ, hσ⟩, ?_, rfl⟩
    show MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) ⟨σ, hσ⟩ = 1
    apply RingEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    show (⟨σ, hσ⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ← A.coe_mem_nonunits_iff]
    exact h a a.2

end Inertia

theorem mem_nonunits_padicIntegers_iff {x : PadicAlgCl q} :
    x ∈ (padicIntegers q).nonunits ↔ ‖x‖₊ < 1 := by
  rw [ValuationSubring.mem_nonunits_iff]
  exact ((Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one).symm

theorem mem_nonunits_padicPlace_iff {a : AlgebraicClosure ℚ} :
    a ∈ (padicPlace q).nonunits ↔ ‖padicEmbedding q a‖₊ < 1 := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases ha : a = 0
  · subst ha; simp
  · have hne : padicEmbedding q a ≠ 0 := fun h => ha ((map_eq_zero _).mp h)
    rw [padicPlace, ValuationSubring.mem_comap, mem_padicIntegers_iff, map_inv₀, nnnorm_inv]
    simp only [ha, false_or, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, not_le]
    rw [one_lt_inv_iff₀]
    exact ⟨fun h => h.2, fun h => ⟨pos_iff_ne_zero.mpr (nnnorm_ne_zero_iff.mpr hne), h⟩⟩

theorem mem_decompositionSubgroup_padicIntegers (τ : Γq) :
    τ ∈ (padicIntegers q).decompositionSubgroup ℚ_[q] := by
  rw [MulAction.mem_stabilizer_iff]
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, mem_padicIntegers_iff,
    mem_padicIntegers_iff, nnnorm_padicAlgCl_algEquiv]

private lemma nnnorm_multiset_prod {K : Type*} [NormedField K] (s : Multiset K) :
    ‖s.prod‖₊ = (s.map (fun x => ‖x‖₊)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

private lemma algebraMap_rat_padicAlgCl_eq :
    algebraMap ℚ (PadicAlgCl q) = (padicEmbedding q).toRingHom.comp (algebraMap ℚ (AlgebraicClosure ℚ)) :=
  Subsingleton.elim _ _

lemma aeval_eq_prod_aroots_padicEmbedding (h : ℚ[X]) (hm : h.Monic) (α : PadicAlgCl q) :
    Polynomial.aeval α h
      = ((h.aroots (AlgebraicClosure ℚ)).map (fun r => α - padicEmbedding q r)).prod := by
  classical
  have hsplit : (h.map (algebraMap ℚ (AlgebraicClosure ℚ))).Splits :=
    IsAlgClosed.splits _
  have hfac : h.map (algebraMap ℚ (AlgebraicClosure ℚ))
      = ((h.aroots (AlgebraicClosure ℚ)).map (fun r => X - C r)).prod := by
    simpa [Polynomial.aroots] using
      hsplit.eq_prod_roots_of_monic (hm.map (algebraMap ℚ (AlgebraicClosure ℚ)))
  have hmapmap : h.map (algebraMap ℚ (PadicAlgCl q))
      = (h.map (algebraMap ℚ (AlgebraicClosure ℚ))).map (padicEmbedding q).toRingHom := by
    rw [Polynomial.map_map, ← algebraMap_rat_padicAlgCl_eq]
  calc Polynomial.aeval α h
      = Polynomial.eval α (h.map (algebraMap ℚ (PadicAlgCl q))) := by
        rw [Polynomial.eval_map_algebraMap]
    _ = Polynomial.eval α
          (((h.aroots (AlgebraicClosure ℚ)).map (fun r => X - C r)).prod.map
            (padicEmbedding q).toRingHom) := by rw [hmapmap, hfac]
    _ = Polynomial.eval α
          (((h.aroots (AlgebraicClosure ℚ)).map
            (fun r => X - C (padicEmbedding q r))).prod) := by
        simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def,
          Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe]
    _ = ((h.aroots (AlgebraicClosure ℚ)).map (fun r => α - padicEmbedding q r)).prod := by
        simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
          Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

lemma card_aroots_rat (h : ℚ[X]) (hm : h.Monic) :
    (h.aroots (AlgebraicClosure ℚ)).card = h.natDegree := by
  have hsplit : (h.map (algebraMap ℚ (AlgebraicClosure ℚ))).Splits :=
    IsAlgClosed.splits _
  have := Polynomial.splits_iff_card_roots.mp hsplit
  rwa [hm.natDegree_map] at this

theorem denseRange_padicEmbedding : DenseRange (padicEmbedding q) := by
  classical
  rw [Metric.denseRange_iff]
  intro α ε hε
  set εnn : ℝ≥0 := ⟨ε, hε.le⟩ with hεnn
  have hεnn0 : 0 < εnn := by exact_mod_cast hε
  have halg : Algebra.IsAlgebraic ℚ_[q] (PadicAlgCl q) := inferInstance
  have hint : IsIntegral ℚ_[q] α := (halg.isAlgebraic α).isIntegral
  set f : ℚ_[q][X] := minpoly ℚ_[q] α with hf
  have hfm : f.Monic := minpoly.monic hint
  set n : ℕ := f.natDegree with hn
  set M : ℝ≥0 := max 1 ‖α‖₊ with hM
  have hM1 : (1 : ℝ≥0) ≤ M := le_max_left _ _
  set δ : ℝ≥0 := εnn ^ n / (((n : ℝ≥0) + 1) * M ^ n + 1) with hδ
  have hden0 : ((n : ℝ≥0) + 1) * M ^ n + 1 ≠ 0 := by positivity
  have hδ0 : 0 < δ := by
    have hnum : (0 : ℝ≥0) < εnn ^ n := pow_pos hεnn0 n
    rw [hδ, pos_iff_ne_zero]
    exact div_ne_zero hnum.ne' hden0
  have hkey : ((n : ℝ≥0) + 1) * δ * M ^ n < εnn ^ n := by
    have h1 : δ * (((n : ℝ≥0) + 1) * M ^ n) < δ * (((n : ℝ≥0) + 1) * M ^ n + 1) :=
      mul_lt_mul_of_pos_left (lt_add_one _) hδ0
    have h2 : δ * (((n : ℝ≥0) + 1) * M ^ n + 1) = εnn ^ n := by
      rw [hδ, div_mul_cancel₀]
      exact hden0
    calc ((n : ℝ≥0) + 1) * δ * M ^ n = δ * (((n : ℝ≥0) + 1) * M ^ n) := by ring
      _ < εnn ^ n := h2 ▸ h1
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  set r : ℕ → ℚ := fun i => Classical.choose (Padic.rat_dense (p := q) (f.coeff i) hδR) with hr
  have hrspec : ∀ i, ‖f.coeff i - (r i : ℚ_[q])‖ < (δ : ℝ) := fun i =>
    Classical.choose_spec (Padic.rat_dense (p := q) (f.coeff i) hδR)
  set g : ℚ[X] := X ^ n + ∑ j ∈ Finset.range n, C (r j) * X ^ j with hg
  have hgcoeff_lt : ∀ i, i < n → g.coeff i = r i := by
    intro i hi
    rw [hg, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg hi.ne,
      Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single i (fun j _ hj => by
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (fun h => hj h.symm),
          mul_zero])
      (fun h => absurd (Finset.mem_range.mpr hi) h)]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one, zero_add]
  have hgcoeff_n : g.coeff n = 1 := by
    rw [hg, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl,
      Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_zero fun j hj => by
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (Finset.mem_range.mp hj).ne', mul_zero]]
    rw [add_zero]
  have hgdegsum : (∑ j ∈ Finset.range n, C (r j) * X ^ j).degree < (n : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
    intro j hj
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
      (by exact_mod_cast Finset.mem_range.mp hj)
  have hgm : g.Monic := by
    rw [hg]
    exact Polynomial.monic_X_pow_add hgdegsum
  have hgdeg_le : g.natDegree ≤ n := by
    have : g.degree ≤ (n : WithBot ℕ) := by
      rw [hg]
      refine le_trans (Polynomial.degree_add_le _ _) (max_le ?_ (le_of_lt hgdegsum))
      exact Polynomial.degree_X_pow_le n
    exact Polynomial.natDegree_le_iff_degree_le.mpr this
  have hgdeg : g.natDegree = n :=
    le_antisymm hgdeg_le (Polynomial.le_natDegree_of_ne_zero (by rw [hgcoeff_n]; exact one_ne_zero))
  set G : (PadicAlgCl q)[X] := g.map (algebraMap ℚ (PadicAlgCl q)) with hG
  set F : (PadicAlgCl q)[X] := f.map (algebraMap ℚ_[q] (PadicAlgCl q)) with hF
  have hFeval : Polynomial.eval α F = 0 := by
    rw [hF, Polynomial.eval_map_algebraMap, hf, minpoly.aeval]
  have hGFdeg : (G - F).natDegree < n + 1 := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
    rw [Nat.lt_succ_iff, max_le_iff]
    constructor
    · exact le_trans (Polynomial.natDegree_map_le) (le_of_eq hgdeg)
    · exact le_trans (Polynomial.natDegree_map_le) (le_of_eq rfl)
  have hcoeffbound : ∀ i, ‖(G - F).coeff i‖₊ ≤ δ := by
    intro i
    rw [Polynomial.coeff_sub, hG, hF, Polynomial.coeff_map, Polynomial.coeff_map]
    rcases lt_trichotomy i n with hi | hi | hi
    · rw [hgcoeff_lt i hi]
      have h1 : (algebraMap ℚ (PadicAlgCl q)) (r i)
          = (algebraMap ℚ_[q] (PadicAlgCl q)) ((r i : ℚ_[q])) := by
        rw [eq_ratCast, map_ratCast]
      rw [h1, ← map_sub]
      have h2 : ‖(algebraMap ℚ_[q] (PadicAlgCl q)) ((r i : ℚ_[q]) - f.coeff i)‖
          = ‖(r i : ℚ_[q]) - f.coeff i‖ := PadicAlgCl.norm_extends q _
      have h3 : ‖(r i : ℚ_[q]) - f.coeff i‖ < (δ : ℝ) := by
        rw [norm_sub_rev]; exact hrspec i
      have : ‖(algebraMap ℚ_[q] (PadicAlgCl q)) ((r i : ℚ_[q]) - f.coeff i)‖₊ < δ := by
        rw [← NNReal.coe_lt_coe, coe_nnnorm, h2]
        exact h3
      exact this.le
    · subst hi
      rw [hgcoeff_n, hf]
      have : (minpoly ℚ_[q] α).coeff (minpoly ℚ_[q] α).natDegree = 1 := hfm.coeff_natDegree
      rw [hn] at *
      rw [this, map_one, map_one, sub_self, nnnorm_zero]
      exact zero_le
    · have hgz : g.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (hgdeg ▸ hi)
      have hfz : f.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (hn ▸ hi)
      rw [hgz, hfz, map_zero, map_zero, sub_self, nnnorm_zero]
      exact zero_le
  have hGsmall : ‖Polynomial.eval α G‖₊ < εnn ^ n := by
    have heq : Polynomial.eval α G = Polynomial.eval α (G - F) := by
      rw [Polynomial.eval_sub, hFeval, sub_zero]
    rw [heq, Polynomial.eval_eq_sum_range' hGFdeg]
    refine lt_of_le_of_lt ?_ hkey
    refine le_trans (nnnorm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range (n + 1),
        ‖(G - F).coeff i * α ^ i‖₊ ≤ δ * M ^ n := by
      intro i hi
      rw [nnnorm_mul, nnnorm_pow]
      refine mul_le_mul' (hcoeffbound i) ?_
      calc ‖α‖₊ ^ i ≤ M ^ i := pow_le_pow_left' (le_max_right _ _) i
        _ ≤ M ^ n := pow_le_pow_right' hM1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine le_of_eq ?_
    push_cast
    ring
  by_contra hcon
  push Not at hcon
  have hall : ∀ ρ ∈ g.aroots (AlgebraicClosure ℚ), εnn ≤ ‖α - padicEmbedding q ρ‖₊ := by
    intro ρ _
    by_contra hlt
    push Not at hlt
    refine absurd ?_ (not_lt.mpr (hcon ρ))
    rw [dist_eq_norm, ← coe_nnnorm]
    exact_mod_cast hlt
  have hprodge : εnn ^ n ≤ ‖Polynomial.aeval α g‖₊ := by
    rw [aeval_eq_prod_aroots_padicEmbedding q g hgm, nnnorm_multiset_prod, Multiset.map_map]
    have hcard : ((g.aroots (AlgebraicClosure ℚ)).map
        (fun ρ => ‖α - padicEmbedding q ρ‖₊)).card = n := by
      rw [Multiset.card_map, card_aroots_rat g hgm, hgdeg]
    calc εnn ^ n
        = εnn ^ ((g.aroots (AlgebraicClosure ℚ)).map
            (fun ρ => ‖α - padicEmbedding q ρ‖₊)).card := by rw [hcard]
      _ ≤ _ := Multiset.pow_card_le_prod (by
          intro x hx
          obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.mp hx
          exact hall ρ hρ)
  have haevalG : Polynomial.aeval α g = Polynomial.eval α G := by
    rw [hG, Polynomial.eval_map_algebraMap]
  rw [haevalG] at hprodge
  exact absurd (lt_of_le_of_lt hprodge hGsmall) (lt_irrefl _)

theorem mem_inertia_padicIntegers_of_localGaloisToGlobal (τ : Γq)
    (hτ : localGaloisToGlobal q τ ∈ (padicPlace q).inertiaSubgroupIn ℚ) :
    τ ∈ (padicIntegers q).inertiaSubgroupIn ℚ_[q] := by
  rw [mem_inertiaSubgroupIn_iff] at hτ ⊢
  refine ⟨mem_decompositionSubgroup_padicIntegers q τ, fun y hy => ?_⟩
  rw [mem_padicIntegers_iff] at hy
  rw [mem_nonunits_padicIntegers_iff]

  have hd := denseRange_padicEmbedding q
  rw [Metric.denseRange_iff] at hd
  obtain ⟨a, ha⟩ := hd y 1 one_pos
  have ha' : ‖y - padicEmbedding q a‖₊ < 1 := by
    rw [dist_eq_norm] at ha
    have : ((‖y - padicEmbedding q a‖₊ : ℝ)) < 1 := by rwa [coe_nnnorm]
    exact_mod_cast this
  have haint : ‖padicEmbedding q a‖₊ ≤ 1 := by
    have h1 : padicEmbedding q a = y + -(y - padicEmbedding q a) := by ring
    rw [h1]
    refine le_trans (IsUltrametricDist.nnnorm_add_le_max _ _) (max_le hy ?_)
    rw [nnnorm_neg]; exact ha'.le
  have hmove : ‖τ (padicEmbedding q a) - padicEmbedding q a‖₊ < 1 := by
    have h := hτ.2 a haint
    rw [mem_nonunits_padicPlace_iff, map_sub, padicEmbedding_localGaloisToGlobal] at h
    exact h
  have h2 : τ y - y = τ (y - padicEmbedding q a) + ((τ (padicEmbedding q a) - padicEmbedding q a) +
      -(y - padicEmbedding q a)) := by
    rw [map_sub]; ring
  rw [h2]
  refine lt_of_le_of_lt (IsUltrametricDist.nnnorm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [nnnorm_padicAlgCl_algEquiv]; exact ha'
  · refine lt_of_le_of_lt (IsUltrametricDist.nnnorm_add_le_max _ _) (max_lt hmove ?_)
    rw [nnnorm_neg]; exact ha'

theorem continuous_localGaloisToGlobal : Continuous (localGaloisToGlobal q) := by
  classical
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hEfd, hEs⟩ := hs

  haveI := hEfd
  let b := Module.finBasis ℚ E
  let S : Set (PadicAlgCl q) := Set.range fun i => padicEmbedding q (b i : AlgebraicClosure ℚ)
  haveI : Finite S := Set.finite_range _ |>.to_subtype
  let E' : IntermediateField ℚ_[q] (PadicAlgCl q) := IntermediateField.adjoin ℚ_[q] S
  haveI : FiniteDimensional ℚ_[q] E' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((E'.fixingSubgroup_isOpen).mem_nhds (one_mem _)) fun τ hτ => ?_
  show localGaloisToGlobal q τ ∈ s
  apply hEs
  show localGaloisToGlobal q τ ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx

  have hτ' : ∀ i, τ (padicEmbedding q (b i : AlgebraicClosure ℚ)) = padicEmbedding q (b i : AlgebraicClosure ℚ) :=
    fun i => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  apply (padicEmbedding q).toRingHom.injective
  show padicEmbedding q (localGaloisToGlobal q τ x) = padicEmbedding q x
  rw [padicEmbedding_localGaloisToGlobal]
  have hrepr := b.sum_repr ⟨x, hx⟩
  have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • ((b i : E) : AlgebraicClosure ℚ) := by
    have h1 := congrArg (E.val) hrepr
    rw [map_sum] at h1
    exact h1.symm
  rw [hx']
  simp only [map_sum, map_rat_smul, hτ']

theorem exists_localGaloisToGlobal_eq_of_mem_decompositionSubgroup (σ : Γ)
    (hσ : σ ∈ (padicPlace q).decompositionSubgroup ℚ) :
    ∃ τ : Γq, localGaloisToGlobal q τ = σ := by
  haveI : T2Space Γ := krullTopology_t2
  have hclosed : IsClosed ((localGaloisToGlobal q).range : Set Γ) := by
    have : ((localGaloisToGlobal q).range : Set Γ) = Set.range (localGaloisToGlobal q) := rfl
    rw [this]
    exact (isCompact_range (continuous_localGaloisToGlobal q)).isClosed
  have hle := ValuationSubring.decompositionSubgroup_padicPlace_le_closure_range_localGaloisToGlobal q
  have hle' : (localGaloisToGlobal q).range.topologicalClosure ≤ (localGaloisToGlobal q).range :=
    Subgroup.topologicalClosure_minimal _ le_rfl hclosed
  obtain ⟨τ, hτ⟩ := hle' (hle hσ)
  exact ⟨τ, hτ⟩

end SURJI

open SURJI in
theorem solution
    (p : ℕ) [Fact p.Prime] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ (padicPlace p).inertiaSubgroupIn ℚ) :
    ∃ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      τ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] ∧ localGaloisToGlobal p τ = σ := by
  have hD : σ ∈ (padicPlace p).decompositionSubgroup ℚ := ((mem_inertiaSubgroupIn_iff _ _).1 hσ).1
  obtain ⟨τ, rfl⟩ := exists_localGaloisToGlobal_eq_of_mem_decompositionSubgroup p σ hD
  exact ⟨τ, mem_inertia_padicIntegers_of_localGaloisToGlobal p τ hσ, rfl⟩

end
end S_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
end P2MW
export P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq (solution)
