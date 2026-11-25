-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_jacobian_cut__05331927f463
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:26.747269+00:00
-- url     : https://prove2.me/submissions/2ce5e091-e1af-47d5-99f3-f36099f20c3c

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartB
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_finrank_cot_eq
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_locRing_isLocalRing_isNoetherian__d126a3dea4d3
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_exists_mul_mem_of_algebraMap_mem
import Theorems.Thm_ReciprocityTheory_AnForm_R_JacobianCriterionAlt_le_ptIdeal_of_nontrivial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.JacobianCriterionAlt
open MvPolynomial IsLocalRing
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (e : ℕ)
    [IsRegularLocalRing (locR K p)] (he : ringKrullDim (locR K p) = e) :
    e ≤ n ∧ ∃ F : Fin (n - e) → MvPolynomial (Fin n) ℂ, (∀ i, F i ∈ K) ∧
      LinearIndependent ℂ (fun i => gradP p (F i)) ∧
      ∃ h : MvPolynomial (Fin n) ℂ, eval p h ≠ 0 ∧ ∀ g ∈ K, h * g ∈ Ideal.span (Set.range F) := by
  have hK := le_ptIdeal_of_nontrivial (p := p) K
  have hcot : Module.finrank (ResidueField (locR K p)) (CotangentSpace (locR K p)) = e := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace (locR K p)).mp inferInstance
    rw [he] at this
    exact_mod_cast this
  have h2 := finrank_cot_eq p K
  rw [hcot] at h2
  refine ⟨by omega, ?_⟩

  obtain ⟨κ, a, -, hspan, hli⟩ :=
    exists_linearIndependent' ℂ (fun k : K => gradP p (k : MvPolynomial (Fin n) ℂ))
  have : Finite κ := hli.finite
  have : Fintype κ := Fintype.ofFinite κ
  have hj : Submodule.span ℂ (Set.range fun k : K => gradP p (k : MvPolynomial (Fin n) ℂ)) =
      jacS K p := by
    rw [jacS]; congr 1; ext v; simp
  have hcard : Fintype.card κ = n - e := by
    have := finrank_span_eq_card hli
    rw [hspan, hj] at this
    omega
  let σ : Fin (n - e) ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let F : Fin (n - e) → MvPolynomial (Fin n) ℂ := fun i => (a (σ i) : MvPolynomial (Fin n) ℂ)
  have hFK : ∀ i, F i ∈ K := fun i => (a (σ i)).2
  have hFli : LinearIndependent ℂ (fun i => gradP p (F i)) := hli.comp σ σ.injective
  refine ⟨F, hFK, hFli, ?_⟩

  set J : Ideal (MvPolynomial (Fin n) ℂ) := Ideal.span (Set.range F) with hJ
  have hJK : J ≤ K := Ideal.span_le.mpr (Set.range_subset_iff.mpr hFK)
  obtain ⟨hJloc, hJnoeth⟩ := locRing_isLocalRing_isNoetherian' J p
    (fun h hh => mem_ptIdeal.mp (hK (hJK hh)))
  have hJcot := finrank_cot_eq p J
  have hJrank : n - e ≤ Module.finrank ℂ (jacS J p) := by
    let v : Fin (n - e) → jacS J p := fun i =>
      ⟨gradP p (F i), Submodule.subset_span ⟨F i, Ideal.subset_span ⟨i, rfl⟩, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp (jacS J p).subtype hFli
    simpa using hv.fintype_card_le_finrank
  have hmapJK : Ideal.map (algebraMap _ (localization₂ p)) J ≤ Ideal.map (algebraMap _ (localization₂ p)) K :=
    Ideal.map_mono hJK
  have hdimKJ : ringKrullDim (locR K p) ≤ ringKrullDim (locR J p) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hmapJK)
  have hdimJ : ringKrullDim (locR J p) ≤
      Module.finrank (ResidueField (locR J p)) (CotangentSpace (locR J p)) := by
    rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact ringKrullDim_le_spanFinrank_maximalIdeal _
  have hcotJ : Module.finrank (ResidueField (locR J p)) (CotangentSpace (locR J p)) ≤ e := by
    omega
  have hDJ : ringKrullDim (locR J p) = e := by
    apply le_antisymm
    · exact hdimJ.trans (by exact_mod_cast hcotJ)
    · rw [← he]; exact hdimKJ
  have hreg : IsRegularLocalRing (locR J p) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hDJ]
    exact_mod_cast hcotJ
  have hdom : IsDomain (locR J p) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _

  have hmapEq : Ideal.map (algebraMap _ (localization₂ p)) K = Ideal.map (algebraMap _ (localization₂ p)) J := by
    by_contra hne
    set 𝔞 : Ideal (locR J p) :=
      (Ideal.map (algebraMap _ (localization₂ p)) K).map (Ideal.Quotient.mk _) with h𝔞
    have h𝔞ne : 𝔞 ≠ ⊥ := by
      intro hbot
      rw [h𝔞, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hbot
      exact hne (le_antisymm hbot hmapJK)
    obtain ⟨x, hx𝔞, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞ne
    have hxnz : x ∈ nonZeroDivisors (locR J p) := mem_nonZeroDivisors_of_ne_zero hx0
    have hd1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hxnz
    have hle𝔞 : Ideal.span {x} ≤ 𝔞 := (Ideal.span_singleton_le_iff_mem _).mpr hx𝔞
    have hd2 : ringKrullDim (locR J p ⧸ 𝔞) ≤ ringKrullDim (locR J p ⧸ Ideal.span {x}) :=
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle𝔞)
    have hd3 : ringKrullDim (locR J p ⧸ 𝔞) = ringKrullDim (locR K p) :=
      ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hmapJK)
    rw [hd3, he] at hd2
    rw [hDJ] at hd1
    have : ((e : WithBot ℕ∞) + 1 ≤ e) := (add_le_add hd2 le_rfl).trans hd1
    have h' : (((e + 1 : ℕ) : WithBot ℕ∞) ≤ ((e : ℕ) : WithBot ℕ∞)) := by exact_mod_cast this
    have := WithBot.coe_le_coe.mp h'
    norm_cast at this
    omega

  have hloc : ∀ g ∈ K, ∃ s, s ∉ ptI p ∧ s * g ∈ J := fun g hg =>
    exists_mul_mem_of_algebraMap_mem p (hmapEq ▸ Ideal.mem_map_of_mem _ hg)
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian K : K.FG)
  have hG' : ∀ g ∈ G, ∃ s, s ∉ ptI p ∧ s * g ∈ J := fun g hg =>
    hloc g (hG ▸ Ideal.subset_span hg)
  choose! t ht using hG'
  refine ⟨∏ g ∈ G, t g, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun g hg h0 => (ht g hg).1 (mem_ptIdeal.mpr h0)
  · intro g hg
    rw [← hG] at hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase G t hx, mul_comm (t x), mul_assoc]
      exact J.mul_mem_left _ (ht x hx).2
    | zero => rw [mul_zero]; exact J.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact J.add_mem hx hy
    | smul c x _ hx => rw [smul_eq_mul, mul_left_comm]; exact J.mul_mem_left _ hx
end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
