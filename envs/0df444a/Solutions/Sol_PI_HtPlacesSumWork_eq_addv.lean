-- Prove2me | solution 1 for PI.HtPlacesSumWork.eq_addv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:17:52.961655+00:00
-- url     : https://prove2.me/submissions/06256e95-29ad-4348-9da7-648c3d6e9062

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_ValPlWtAddEqZero
import Theorems.Thm_PI_HtPlacesSumWork_valPl_mem_vRing
import Theorems.Thm_PI_HtPlacesSumWork_addv_nonneg
import Theorems.Thm_PI_HtPlacesSumWork_addv_pos_iff
import Theorems.Thm_PI_HtPlacesSumWork_addv_isNormDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
section Addv
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)
private theorem eq_addv_lemma (w : AddValuation L (WithTop ℤ))
    (h0 : ∀ s : S, 0 ≤ w (algebraMap S L s))
    (hQ : ∀ s : S, 0 < w (algebraMap S L s) ↔ s ∈ v.asIdeal) (hne : ∃ π : L, w π = 1) :
    vRing w = HeightOneSpectrum.valuationSubringAtPrime L v := by
  set D := HeightOneSpectrum.valuationSubringAtPrime L v
  have hDle : D ≤ vRing w := by
    intro x hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl (⟨x, hx⟩ : D)
    have hspec := IsLocalization.mk'_spec D a b
    dsimp only at hab
    rw [hab] at hspec
    have hL := congrArg (algebraMap D L) hspec
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hL
    have hw := congrArg w hL
    rw [AddValuation.map_mul] at hw
    have hb0 : w (algebraMap S L b) = 0 :=
      le_antisymm (not_lt.1 (fun h => b.2 ((hQ b).1 h))) (h0 b)
    rw [hb0, add_zero] at hw
    rw [valPl_mem_vRing]
    show 0 ≤ w (algebraMap D L ⟨x, hx⟩)
    rw [hw]
    exact h0 a
  have hP := ValuationSubring.ofPrime_idealOfLE D (vRing w) hDle
  by_cases hbot : D.idealOfLE (vRing w) hDle = ⊥
  · simp only [hbot, ValuationSubring.ofPrime_bot] at hP
    exfalso
    obtain ⟨π, hπ⟩ := hne
    have hm : π⁻¹ ∈ vRing w := by
      rw [← hP]
      exact ValuationSubring.mem_top _
    rw [valPl_mem_vRing, AddValuation.map_inv, hπ] at hm
    exact absurd hm (by decide)
  · have hmax : (D.idealOfLE (vRing w) hDle).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hbot
    simp only [IsLocalRing.eq_maximalIdeal hmax, ValuationSubring.ofPrime_top] at hP
    exact hP.symm
private theorem eq_addv_lemma_2 {Φ : Type*} [Field Φ] (u1 u2 : AddValuation Φ (WithTop ℤ))
    (h1 : IsNormDiscrete u1) (h2 : IsNormDiscrete u2) (he : ∀ x, 0 ≤ u1 x ↔ 0 ≤ u2 x) : u1 = u2 := by
  have fin : ∀ u : AddValuation Φ (WithTop ℤ), IsNormDiscrete u → ∀ x : Φ, x ≠ 0 →
      ∃ k : ℤ, u x = k := by
    intro u hu x hx
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (hu.1 x hx)
    exact ⟨k, hk.symm⟩
  have hpow : ∀ (u : AddValuation Φ (WithTop ℤ)) (π : Φ), u π = 1 → ∀ n : ℕ,
      u (π ^ n) = ((n : ℤ) : WithTop ℤ) := by
    intro u π h n
    rw [AddValuation.map_pow, h, nsmul_one]
    simp
  have hinv : ∀ (u : AddValuation Φ (WithTop ℤ)) (x : Φ) (k : ℤ), x ≠ 0 → u x = k →
      u x⁻¹ = ((-k : ℤ) : WithTop ℤ) := by
    intro u x k hx hk
    have h := congrArg u (mul_inv_cancel₀ hx)
    rw [AddValuation.map_mul, AddValuation.map_one, hk] at h
    have hne : u x⁻¹ ≠ ⊤ := by
      intro ht
      rw [ht] at h
      simp at h
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hj] at h ⊢
    norm_cast at h ⊢
    omega
  obtain ⟨π1, hπ1⟩ := h1.2
  obtain ⟨π2, hπ2⟩ := h2.2
  have hπ10 : π1 ≠ 0 := by
    rintro rfl
    simp at hπ1
  have hπ20 : π2 ≠ 0 := by
    rintro rfl
    simp at hπ2
  have hπ1' : u1 π1 = ((1 : ℤ) : WithTop ℤ) := by simpa using hπ1
  have hπ2' : u2 π2 = ((1 : ℤ) : WithTop ℤ) := by simpa using hπ2
  obtain ⟨c, hc⟩ := fin u2 h2 π1 hπ10
  obtain ⟨d, hd⟩ := fin u1 h1 π2 hπ20
  have hcpos : 0 < c := by
    have e := he π1⁻¹
    rw [hinv u1 π1 1 hπ10 hπ1', hinv u2 π1 c hπ10 hc] at e
    norm_cast at e
    omega
  have hdpos : 0 < d := by
    have e := he π2⁻¹
    rw [hinv u1 π2 d hπ20 hd, hinv u2 π2 1 hπ20 hπ2'] at e
    norm_cast at e
    omega
  have hc1 : c = 1 := by
    have e := he (π2 * π1⁻¹)
    rw [AddValuation.map_mul, AddValuation.map_mul, hd, hinv u1 π1 1 hπ10 hπ1', hπ2',
      hinv u2 π1 c hπ10 hc] at e
    norm_cast at e
    omega
  have hπ1u2 : u2 π1 = 1 := by rw [hc, hc1]; rfl
  ext x
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨m, hm⟩ := fin u1 h1 x hx
  obtain ⟨a, ha⟩ := fin u2 h2 x hx
  have key : ∀ n : ℕ, (0 ≤ m + n ↔ 0 ≤ a + n) ∧ (0 ≤ -m + n ↔ 0 ≤ -a + n) := by
    intro n
    have e1 := he (x * π1 ^ n)
    rw [AddValuation.map_mul, AddValuation.map_mul, hm, ha, hpow u1 π1 hπ1 n, hpow u2 π1 hπ1u2 n] at e1
    have e2 := he (x⁻¹ * π1 ^ n)
    rw [AddValuation.map_mul, AddValuation.map_mul, hinv u1 x m hx hm, hinv u2 x a hx ha,
      hpow u1 π1 hπ1 n, hpow u2 π1 hπ1u2 n] at e2
    norm_cast at e1 e2
    all_goals exact ⟨e1, e2⟩
  have k1 := key (-m).toNat
  have k2 := key ((-m).toNat - 1)
  have k3 := key m.toNat
  have k4 := key (m.toNat - 1)
  rw [hm, ha]
  norm_cast
  omega
end Addv
section Places
variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
variable {O F L}
variable [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
  [FaithfulSMul O L]
end Places
section Main
variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]
end Main
end PI.HtPlacesSumWork
end

set_option autoImplicit false
open PI PI.HtPlacesSumWork
open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)
namespace PI.HtPlacesSumWork
theorem _root_.solution (w : AddValuation L (WithTop ℤ)) (hw : IsNormDiscrete w)
    (h0 : ∀ s : S, 0 ≤ w (algebraMap S L s))
    (hQ : ∀ s : S, 0 < w (algebraMap S L s) ↔ s ∈ v.asIdeal) : w = addv L v := by
  have hA := eq_addv_lemma v w h0 hQ hw.2
  have hB := eq_addv_lemma v (addv L v) (addv_nonneg v) (addv_pos_iff v) (addv_isNormDiscrete v).2
  apply eq_addv_lemma_2 w (addv L v) hw (addv_isNormDiscrete v)
  intro x
  rw [← valPl_mem_vRing, ← valPl_mem_vRing, hA, hB]
end PI.HtPlacesSumWork
