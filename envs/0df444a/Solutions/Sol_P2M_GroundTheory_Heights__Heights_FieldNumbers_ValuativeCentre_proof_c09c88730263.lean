-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ValuativeCentre_proof_c09c88730263
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:27.782621+00:00
-- url     : https://prove2.me/submissions/b4025709-65ce-4196-be5d-2caf1b67de5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartDehomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PValuativeCentre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_blockSpecial_c3169932ef6b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartDehomog_proof_bb4a81b4cd4b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_proof_0aacacc92e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RelevantPrimeDimGe_proof_f3a1f51a2659


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace ValuativeCentre
theorem _root_.solution : ValuativeCentre.Statement.{u} := by
  intro F _ K _ _ ι _ P hP
  have := hP.isPrime
  intro R hF
  set L := FractionRing (MRing ι F ⧸ P)
  let φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hφ : ∀ p, φ p = 0 ↔ p ∈ P := fun p => by
    simp only [φ, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

  have hmax : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι F) ∉ P ∧
      ∀ j, R.valuation (φ (X ⟨k, j⟩)) ≤ R.valuation (φ (X ⟨k, i⟩)) := by
    intro k
    classical
    obtain ⟨i₀, hi₀⟩ := hP.relevant k
    obtain ⟨i, hi, hmx⟩ := Finset.exists_max_image
      (Finset.univ.filter fun j => (X ⟨k, j⟩ : MRing ι F) ∉ P)
      (fun j => R.valuation (φ (X ⟨k, j⟩))) ⟨i₀, by simp [hi₀]⟩
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun j => ?_⟩
    by_cases hj : (X ⟨k, j⟩ : MRing ι F) ∈ P
    · rw [(hφ _).mpr hj, map_zero]; exact zero_le
    · exact hmx j (by simp [hj])
  choose c hcP hcmax using hmax

  have hchart : ∀ p, chartMap P c p ∈ R := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [chartMap, aeval_C]; exact hF a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [chartMap, aeval_X, ← R.valuation_le_one_iff, map_div₀]
      have h0 : R.valuation (φ (X ⟨v.1, c v.1⟩)) ≠ 0 := by
        rw [Ne, Valuation.zero_iff, hφ]; exact hcP v.1
      exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hcmax v.1 v.2)
  let χ : MRing ι F →+* R := (chartMap P c).toRingHom.codRestrict R hchart
  have hχ : ∀ p, (χ p : L) = chartMap P c p := fun p => rfl
  let ρ : MRing ι F →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp χ
  let θ : MRing ι F →+* MvPolynomial K (IsLocalRing.ResidueField R) := blockSpecial ρ
  have hdeh : ∀ f b, IsMultiHomog f b → chartMap P c f = φ f / φ (chartMonomial c b) :=
    fun f b hf => MChartDehomog.proof F K ι P c hcP f b hf
  have hmon : ∀ b, φ (chartMonomial c b) ≠ 0 := fun b => by
    simp only [chartMonomial, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (fun h => hcP k ((hφ _).mp h))

  have hy : ∀ f, f ∈ RingHom.ker θ ↔
      ∀ b : K → ℕ, ρ (weightedHomogeneousComponent (blockWeight ι) b f) = 0 := by
    intro f
    rw [RingHom.mem_ker]
    constructor
    · intro h b
      have := congrArg (coeff (Finsupp.equivFunOnFinite.symm b)) h
      rwa [coeff_blockSpecial, coeff_zero, Finsupp.coe_equivFunOnFinite_symm] at this
    · intro h
      ext e
      rw [coeff_blockSpecial, coeff_zero, h]
  have hyform : ∀ f b, IsMultiHomog f b → (f ∈ RingHom.ker θ ↔ ρ f = 0) := by
    intro f b hf
    rw [hy]
    constructor
    · intro h
      have := h b
      rwa [IsWeightedHomogeneous.weightedHomogeneousComponent_same hf] at this
    · intro h b'
      by_cases hb : b' = b
      · rw [hb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hf]; exact h
      · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hf hb, map_zero]
  refine ⟨RingHom.ker θ, ⟨RingHom.ker_isPrime θ, ?_, ?_⟩, ?_, ?_⟩
  ·
    intro f hf b
    rw [hy] at hf ⊢
    intro b'
    have hb := weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f
    by_cases hbb : b' = b
    · rw [hbb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hb]; exact hf b
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hb hbb, map_zero]
  ·
    intro k
    refine ⟨c k, fun h => ?_⟩
    have hX := isWeightedHomogeneous_X F (blockWeight ι) (⟨k, c k⟩ : Σ k, ι k)
    rw [hyform _ _ hX] at h
    have h1 : χ (X ⟨k, c k⟩) = 1 := by
      apply Subtype.ext
      rw [hχ, chartMap, aeval_X]
      exact div_self (fun h' => hcP k ((hφ _).mp h'))
    simp only [ρ, RingHom.comp_apply, h1, map_one] at h
    exact one_ne_zero h
  ·
    intro f hf
    rw [hy]
    intro b
    have hb := weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f
    have h0 : χ (weightedHomogeneousComponent (blockWeight ι) b f) = 0 := by
      apply Subtype.ext
      rw [hχ, hdeh _ _ hb, (hφ _).mpr (hP.multiHomog f hf b), zero_div]
      rfl
    simp only [ρ, RingHom.comp_apply, h0, map_zero]
  ·
    intro b f g hf hg hgy
    change φ f / φ g ∈ R ∧ (f ∈ RingHom.ker θ ↔ φ f / φ g ∈ R.nonunits)
    have hgu : IsUnit (χ g) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      exact fun h => hgy ((hyform g b hg).mpr h)
    have hg0 : (χ g : L) ≠ 0 := fun h => hgu.ne_zero (Subtype.ext h)
    have hquot : φ f / φ g = ((χ f * ↑hgu.unit⁻¹ : R) : L) := by
      have e1 : φ f / φ g = (χ f : L) / (χ g : L) := by
        rw [hχ, hχ, hdeh f b hf, hdeh g b hg, div_div_div_cancel_right₀ (hmon b)]
      have e2 : (χ g : L) * ((↑hgu.unit⁻¹ : R) : L) = 1 := by
        rw [← Subring.coe_mul, IsUnit.mul_val_inv]; rfl
      rw [e1, div_eq_iff hg0, Subring.coe_mul, mul_assoc, mul_comm _ (χ g : L), e2, mul_one]
    rw [hquot, ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_mul,
      hyform f b hf]
    refine ⟨Subtype.mem _, ?_⟩
    have hu : IsLocalRing.residue R (↑hgu.unit⁻¹ : R) ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (Units.isUnit _)
    simp only [ρ, RingHom.comp_apply, mul_eq_zero]
    exact ⟨Or.inl, fun h => h.resolve_right hu⟩
end ValuativeCentre
end GroundTheory.Heights₂.Heights.FieldNumbers
