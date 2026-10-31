-- Prove2me | solution 1 for RiskFunctionals.Duality.acceptability_representation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:53:56.122993+00:00
-- url     : https://prove2.me/submissions/58a838f9-16a2-4b4f-9be2-3c2dbe07442b

import Mathlib
import Definitions.Def_RiskFunctionals_Duality_Functionals
import Definitions.Def_RiskFunctionals_Duality_Conjugates
import Theorems.Thm_RiskFunctionals_Duality_fenchel_moreau
import Theorems.Thm_RiskFunctionals_Duality_conjugate_necessary

namespace AccRepAux
open MeasureTheory ProbabilityTheory RiskFunctionals.Duality

lemma ereal_neg_iInf {ι : Sort*} (g : ι → EReal) : -(⨅ i, g i) = ⨆ i, -g i := by
  apply le_antisymm
  · rw [EReal.neg_le]
    exact le_iInf fun i => by rw [EReal.neg_le]; exact le_iSup (fun i => -g i) i
  · exact iSup_le fun i => EReal.neg_le_neg_iff.2 (iInf_le g i)

lemma ereal_iInf_add_coe {ι : Sort*} (g : ι → EReal) (c : ℝ) :
    ⨅ i, (g i + c) = (⨅ i, g i) + c := by
  apply le_antisymm
  · have h : (⨅ i, (g i + c)) - c ≤ ⨅ i, g i := le_iInf fun i => by
      calc (⨅ i, (g i + c)) - c ≤ (g i + c) - c := EReal.sub_le_sub (iInf_le _ i) le_rfl
        _ = g i := EReal.add_sub_cancel_right
    calc (⨅ i, (g i + c)) = (⨅ i, (g i + c)) - c + c := EReal.sub_add_cancel.symm
      _ ≤ (⨅ i, g i) + c := by gcongr
  · exact le_iInf fun i => by gcongr; exact iInf_le _ i

lemma coe_add_sub (a c : ℝ) (b : EReal) : ((a + c : ℝ) : EReal) - b = ((a : EReal) - b) + c := by
  induction b using EReal.rec with
  | bot => simp [EReal.coe_sub_bot]
  | coe b => norm_cast; ring
  | top => simp

lemma coe_neg_sub (a : ℝ) (x : EReal) : ((-a : ℝ) : EReal) - (-x) = -((a : EReal) - x) := by
  induction x using EReal.rec with
  | bot => simp [EReal.coe_sub_bot]
  | coe b => norm_cast; ring
  | top => simp

lemma affine_le (lam a1 a2 : ℝ) (c : EReal) (hc : c ≠ ⊤) :
    (lam : EReal) * ((a1 : EReal) - c) + ((1 - lam : ℝ) : EReal) * ((a2 : EReal) - c)
      ≤ ((lam * a1 + (1 - lam) * a2 : ℝ) : EReal) - c := by
  induction c using EReal.rec with
  | bot => rw [EReal.coe_sub_bot]; exact le_top
  | coe b =>
    apply le_of_eq
    norm_cast; ring
  | top => exact absurd rfl hc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {p q : ENNReal} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

lemma pairing_eq (Y : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing Y Z = (ContinuousLinearMap.mul ℝ ℝ).lpPairing P p q Y Z := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]; rfl

lemma pairing_add_left (Y₁ Y₂ : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing (Y₁ + Y₂) Z = pairing Y₁ Z + pairing Y₂ Z := by
  simp only [pairing_eq, map_add, ContinuousLinearMap.add_apply]

lemma pairing_sub_left (Y₁ Y₂ : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing (Y₁ - Y₂) Z = pairing Y₁ Z - pairing Y₂ Z := by
  simp only [pairing_eq, map_sub, ContinuousLinearMap.sub_apply]

lemma pairing_smul_left (c : ℝ) (Y : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing (c • Y) Z = c * pairing Y Z := by
  simp only [pairing_eq, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma pairing_neg_right (Y : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing Y (-Z) = -pairing Y Z := by
  simp only [pairing_eq, map_neg]

lemma pairing_const_left (c : ℝ) (Z : Lp ℝ q P) :
    pairing (Lp.const p P c) Z = c * expectation Z := by
  unfold pairing expectation
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (p := p) (μ := P) c] with ω hω
  rw [hω]; rfl

lemma continuous_pairing_left (Z : Lp ℝ q P) : Continuous (fun Y : Lp ℝ p P => pairing Y Z) := by
  simp only [pairing_eq]
  exact ((ContinuousLinearMap.mul ℝ ℝ).lpPairing P p q).flip Z |>.continuous

lemma pairing_mono {Y₁ Y₂ : Lp ℝ p P} {Z : Lp ℝ q P} (h : ∀ᵐ ω ∂P, Y₁ ω ≤ Y₂ ω)
    (hZ : ∀ᵐ ω ∂P, 0 ≤ Z ω) : pairing Y₁ Z ≤ pairing Y₂ Z := by
  have : 0 ≤ pairing (Y₂ - Y₁) Z := by
    unfold pairing
    apply integral_nonneg_of_ae
    filter_upwards [Lp.coeFn_sub Y₂ Y₁, h, hZ] with ω h1 h2 h3
    rw [h1]
    exact mul_nonneg (sub_nonneg.2 h2) h3
  rw [pairing_sub_left] at this
  linarith

lemma continuous_term (Z : Lp ℝ q P) (c : EReal) (hc : c ≠ ⊤) :
    Continuous (fun Y : Lp ℝ p P => ((pairing Y Z : ℝ) : EReal) - c) := by
  induction c using EReal.rec with
  | bot => simp only [EReal.coe_sub_bot]; exact continuous_const
  | coe b =>
    have : (fun Y : Lp ℝ p P => ((pairing Y Z : ℝ) : EReal) - (b : EReal))
        = fun Y => (((pairing Y Z - b : ℝ)) : EReal) := by
      funext Y; norm_cast
    rw [this]
    exact continuous_coe_real_ereal.comp ((continuous_pairing_left Z).sub continuous_const)
  | top => exact absurd rfl hc

theorem part2 (A : Lp ℝ p P → EReal) (Aplus : Lp ℝ q P → EReal) (hAp : IsProperConcave Aplus)
    (hrep : ∀ Y : Lp ℝ p P, A Y = ⨅ Z ∈ {Z : Lp ℝ q P | expectation Z = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
        ((pairing Y Z : ℝ) : EReal) - Aplus Z) :
    UpperSemicontinuous A ∧ IsAcceptabilityFunctional P A := by
  set S := {Z : Lp ℝ q P | expectation Z = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω} with hS
  have hA : A = fun Y => ⨅ Z ∈ S, ((pairing Y Z : ℝ) : EReal) - Aplus Z := funext hrep
  refine ⟨?_, ⟨?_, ?_, ?_⟩⟩
  · rw [hA]
    exact upperSemicontinuous_iInf fun Z => upperSemicontinuous_iInf fun _ =>
      (continuous_term Z (Aplus Z) (hAp.1 Z)).upperSemicontinuous
  · intro Y c
    rw [hrep, hrep]
    have : ∀ Z ∈ S, ((pairing (Y + Lp.const p P c) Z : ℝ) : EReal) - Aplus Z
        = (((pairing Y Z : ℝ) : EReal) - Aplus Z) + c := by
      intro Z hZ
      rw [pairing_add_left, pairing_const_left, hZ.1, mul_one, coe_add_sub]
    rw [iInf_congr fun Z => iInf_congr fun hZ => this Z hZ]
    rw [← ereal_iInf_add_coe]
    exact iInf_congr fun Z => ereal_iInf_add_coe _ _
  · intro Y₁ Y₂ lam hl0 hl1
    rw [hrep (lam • Y₁ + (1 - lam) • Y₂)]
    refine le_iInf₂ fun Z hZ => ?_
    have h1 : A Y₁ ≤ ((pairing Y₁ Z : ℝ) : EReal) - Aplus Z := by rw [hrep]; exact iInf₂_le Z hZ
    have h2 : A Y₂ ≤ ((pairing Y₂ Z : ℝ) : EReal) - Aplus Z := by rw [hrep]; exact iInf₂_le Z hZ
    calc (lam : EReal) * A Y₁ + ((1 - lam : ℝ) : EReal) * A Y₂
        ≤ (lam : EReal) * (((pairing Y₁ Z : ℝ) : EReal) - Aplus Z)
          + ((1 - lam : ℝ) : EReal) * (((pairing Y₂ Z : ℝ) : EReal) - Aplus Z) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (EReal.coe_nonneg.2 hl0))
            (mul_le_mul_of_nonneg_left h2 (EReal.coe_nonneg.2 (by linarith)))
      _ ≤ ((lam * pairing Y₁ Z + (1 - lam) * pairing Y₂ Z : ℝ) : EReal) - Aplus Z :=
          affine_le _ _ _ _ (hAp.1 Z)
      _ = ((pairing (lam • Y₁ + (1 - lam) • Y₂) Z : ℝ) : EReal) - Aplus Z := by
          rw [pairing_add_left, pairing_smul_left, pairing_smul_left]
  · intro Y₁ Y₂ h
    rw [hrep, hrep]
    exact iInf₂_mono fun Z hZ =>
      EReal.sub_le_sub (EReal.coe_le_coe_iff.2 (pairing_mono h hZ.2)) le_rfl


theorem part1 (hP : IsNonAtomic P) (hp : p ≠ ⊤) (A : Lp ℝ p P → EReal) (hprop : IsProperConcave A)
    (husc : UpperSemicontinuous A) (hacc : IsAcceptabilityFunctional P A) (Y : Lp ℝ p P) :
    A Y = ⨅ Z ∈ {Z : Lp ℝ q P | expectation Z = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
        ((pairing Y Z : ℝ) : EReal) - concaveConj q A Z := by
  set h : Lp ℝ p P → EReal := fun Y => -A Y with hh
  have hproper : IsProperConvex h := by
    refine ⟨fun y => ?_, ?_⟩
    · simp only [hh, ne_eq, EReal.neg_eq_bot_iff]; exact hprop.1 y
    · obtain ⟨y, hy⟩ := hprop.2
      exact ⟨y, by simp only [hh, ne_eq, EReal.neg_eq_top_iff]; exact hy⟩
  have hlsc : LowerSemicontinuous h := by
    intro x y hy
    have : A x < -y := EReal.lt_neg_comm.1 hy
    filter_upwards [husc x (-y) this] with x' hx'
    exact EReal.lt_neg_comm.1 hx'
  have hconv : ConvexEpi h := by
    rintro ⟨Y₁, r₁⟩ h1 ⟨Y₂, r₂⟩ h2 a b ha hb hab
    simp only [epigraph, Set.mem_setOf_eq, hh] at h1 h2 ⊢
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    have h1' : ((-r₁ : ℝ) : EReal) ≤ A Y₁ := by
      rw [EReal.coe_neg]; exact EReal.neg_le.1 h1
    have h2' : ((-r₂ : ℝ) : EReal) ≤ A Y₂ := by
      rw [EReal.coe_neg]; exact EReal.neg_le.1 h2
    have hc := hacc.concave Y₁ Y₂ a ha (by linarith)
    have key : ((-(a * r₁ + (1 - a) * r₂) : ℝ) : EReal) ≤ A (a • Y₁ + (1 - a) • Y₂) := by
      calc ((-(a * r₁ + (1 - a) * r₂) : ℝ) : EReal)
          = (a : EReal) * ((-r₁ : ℝ) : EReal) + ((1 - a : ℝ) : EReal) * ((-r₂ : ℝ) : EReal) := by
            norm_cast; ring
        _ ≤ (a : EReal) * A Y₁ + ((1 - a : ℝ) : EReal) * A Y₂ :=
            add_le_add (mul_le_mul_of_nonneg_left h1' (EReal.coe_nonneg.2 ha))
              (mul_le_mul_of_nonneg_left h2' (EReal.coe_nonneg.2 hb))
        _ ≤ _ := hc
    rw [EReal.neg_le, ← EReal.coe_neg]
    exact key
  have hfm := fenchel_moreau P hP p q hp h hproper hlsc hconv
  -- conjugate relation
  have hconj : ∀ Z : Lp ℝ q P, convexConj q h (-Z) = -concaveConj q A Z := by
    intro Z
    simp only [convexConj, concaveConj, ereal_neg_iInf, hh, pairing_neg_right, coe_neg_sub]
  have hall : ∀ Y : Lp ℝ p P, A Y = ⨅ Z : Lp ℝ q P, ((pairing Y Z : ℝ) : EReal) - concaveConj q A Z := by
    intro Y
    have e := congrFun hfm Y
    simp only [convexBiconj] at e
    rw [← (Equiv.neg (Lp ℝ q P)).iSup_comp] at e
    simp only [Equiv.neg_apply, hconj, pairing_neg_right, coe_neg_sub] at e
    rw [← ereal_neg_iInf] at e
    exact neg_injective (e.trans (by rw [hh]))|>.symm
  have hnec := (conjugate_necessary P hP p q hp).1 A hacc.concave hprop hall
  rw [hall Y]
  apply le_antisymm
  · exact le_iInf₂ fun Z _ => iInf_le _ Z
  · refine le_iInf fun Z => ?_
    by_cases hZ : Z ∈ {Z : Lp ℝ q P | expectation Z = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω}
    · exact iInf₂_le Z hZ
    · have hbot : concaveConj q A Z = ⊥ := by
        by_cases hE : expectation Z = 1
        · have hnot : ¬ ∀ᵐ ω ∂P, 0 ≤ Z ω := fun h => hZ ⟨hE, h⟩
          rw [ae_iff] at hnot
          apply hnec.2.2.1 hacc.monotone
          rw [pos_iff_ne_zero]
          simpa only [not_le] using hnot
        · by_contra hne
          exact hE (hnec.1 hacc.translationEquivariant Z (bot_lt_iff_ne_bot.2 hne))
      rw [hbot, EReal.coe_sub_bot]
      exact le_top

end AccRepAux

open MeasureTheory ProbabilityTheory RiskFunctionals.Duality in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P) (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] :
    (∀ A : Lp ℝ p P → EReal, IsProperConcave A → UpperSemicontinuous A →
      IsAcceptabilityFunctional P A →
      ∀ Y : Lp ℝ p P, A Y = ⨅ Z ∈ {Z : Lp ℝ q P | expectation Z = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
        ((pairing Y Z : ℝ) : EReal) - concaveConj q A Z) ∧
    (∀ (A : Lp ℝ p P → EReal) (Aplus : Lp ℝ q P → EReal), IsProperConcave Aplus →
      (∀ Y : Lp ℝ p P, A Y = ⨅ Z ∈ {Z : Lp ℝ q P | expectation Z = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
        ((pairing Y Z : ℝ) : EReal) - Aplus Z) →
      UpperSemicontinuous A ∧ IsAcceptabilityFunctional P A) := by
  haveI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  exact ⟨fun A hprop husc hacc Y => AccRepAux.part1 hP hp A hprop husc hacc Y,
    fun A Aplus hAp hrep => AccRepAux.part2 A Aplus hAp hrep⟩
