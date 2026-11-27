-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_proof_95eab4bf0883
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:41.651632+00:00
-- url     : https://prove2.me/submissions/5e2368ff-93cc-425d-886f-d8b12b31aa37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsRestLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ResidOfMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_of_mem_862f94617fb4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_zero_67858c6b9a36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_add_fecc8d372056
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_RestrictGen_resid_mul_8e9d9f227e6b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twist_twistSys_iff_89a1717ba8b8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
noncomputable section
open RestrictGen
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace RestrictGen
theorem _root_.solution : RestrictGen.Statement := by
  intro F _ N Ω _ _ x K' _ _ x' hxy R σ hσ Q Q' c H ρ w w' hw' hQ hQ' hH
  classical
  have hσ' : ∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 →
      aeval x f / aeval x g ∈ R ∧ resid R σ (aeval x f / aeval x g) = aeval x' f / aeval x' g := by
    intro f g m hf hg hg'
    obtain ⟨h, e⟩ := hσ f g m hf hg hg'
    exact ⟨h, by rw [resid_of_mem R σ h, e]⟩
  by_cases hx' : ∃ j, x' j ≠ 0
  swap
  · simp only [not_exists, not_not] at hx'
    have hI : IsEmpty (Kleiman.Chart x') := ⟨fun I => by
      obtain ⟨i, hi⟩ := I.2.1
      exact (Kleiman.mem_support x').mp (I.2.2 hi) (hx' i)⟩
    exact ⟨0, ⟨fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I⟩⟩
  obtain ⟨j, hj⟩ := hx'
  have hxj : x j ≠ 0 := hxy j hj
  set r : Ω → K' := fun q => resid R σ (q * x j ^ c * w) / (x' j ^ c * w') with hr

  have hrat : ∀ i, x' i ≠ 0 → (x j / x i) ^ c ∈ R ∧ resid R σ ((x j / x i) ^ c) = (x' j / x' i) ^ c := by
    intro i hi
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have := hσ' (X j ^ n) (X i ^ n) n (isHomogeneous_X_pow (R := F) j n) (isHomogeneous_X_pow (R := F) i n)
        (by simpa using pow_ne_zero n hi)
      simp only [map_pow, aeval_X] at this
      simpa [zpow_natCast, div_pow] using this
    · have := hσ' (X i ^ n) (X j ^ n) n (isHomogeneous_X_pow (R := F) i n) (isHomogeneous_X_pow (R := F) j n)
        (by simpa using pow_ne_zero n hj)
      simp only [map_pow, aeval_X] at this
      simpa [zpow_neg, zpow_natCast, div_pow, inv_div] using this

  have hchart : ∀ (I : Kleiman.Chart x') (a : Ω), a ∈ Kleiman.chartRing F x (Kleiman.liftChart hxy I) →
      a ∈ R ∧ resid R σ a ∈ Kleiman.chartRing F x' I := by
    rintro I a ⟨f, s, e, hs, hf, hse, rfl⟩
    obtain ⟨h1, h2⟩ := hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)
    exact ⟨h1, h2 ▸ ⟨f, s, e, hs, hf, hse, rfl⟩⟩

  have hspan : ∀ (I : Kleiman.Chart x') (z : Ω),
      z ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H →
      z * w ∈ R ∧ resid R σ (z * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
    intro I z hz
    induction hz using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨hm, e⟩ := hH h hh
      refine ⟨hm, ?_⟩
      rw [resid_of_mem R σ hm, e, mul_div_cancel_right₀ _ hw']
      exact Submodule.subset_span ⟨h, hh, rfl⟩
    | zero =>
      rw [zero_mul, resid_zero, zero_div]
      exact ⟨zero_mem R, zero_mem _⟩
    | add a b _ _ ha hb =>
      refine ⟨by rw [add_mul]; exact add_mem ha.1 hb.1, ?_⟩
      rw [add_mul, resid_add R σ ha.1 hb.1, add_div]
      exact add_mem ha.2 hb.2
    | smul a z _ hz =>
      obtain ⟨ha1, ha2⟩ := hchart I a a.2
      rw [Kleiman.chartRing_smul_def, mul_assoc]
      refine ⟨mul_mem ha1 hz.1, ?_⟩
      rw [resid_mul R σ ha1 hz.1, mul_div_assoc]
      exact Submodule.smul_mem _ (⟨_, ha2⟩ : Kleiman.chartRing F x' I) hz.2

  have hkey : ∀ (I : Kleiman.Chart x') (i : Fin (N + 1)), i ∈ I.1 → ∀ q ∈ Q.sub (Kleiman.liftChart hxy I),
      q * x j ^ c * w ∈ R ∧ r q * x' i ^ c = resid R σ (x i ^ c * q * w) / w' ∧
      resid R σ (x i ^ c * q * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
    intro I i hi q hq
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    have hxi : x i ≠ 0 := hxy i hx'i
    have hz : x i ^ c * q ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H := by
      rw [← hQ (Kleiman.liftChart hxy I)]
      exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mpr ⟨q, hq, rfl⟩
    obtain ⟨hz1, hz2⟩ := hspan I _ hz
    obtain ⟨hr1, hr2⟩ := hrat i hx'i
    have heq : q * x j ^ c * w = (x j / x i) ^ c * (x i ^ c * q * w) := by
      rw [div_zpow]
      field_simp
    refine ⟨heq ▸ mul_mem hr1 hz1, ?_, hz2⟩
    rw [hr]
    dsimp only
    rw [heq, resid_mul R σ hr1 hz1, hr2, div_zpow]
    field_simp
  have hmem : ∀ (I : Kleiman.Chart x'), ∀ q ∈ Q.sub (Kleiman.liftChart hxy I), r q ∈ Q'.sub I := by
    intro I q hq
    obtain ⟨i, hi⟩ := I.2.1
    obtain ⟨-, e, hm⟩ := hkey I i hi q hq
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    rw [← hQ' I] at hm
    obtain ⟨y, hy, hy'⟩ := (TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mp hm
    have h' : r q * x' i ^ c = y * x' i ^ c := by
      rw [e, hy', smul_eq_mul, mul_comm]
    rw [mul_right_cancel₀ (zpow_ne_zero c hx'i) h']
    exact hy
  refine ⟨r, ⟨hmem, ?_, ?_, ?_⟩⟩
  · intro I q hq q' hq'
    obtain ⟨i, hi⟩ := I.2.1
    have h1 := (hkey I i hi q hq).1
    have h2 := (hkey I i hi q' hq').1
    rw [hr]
    dsimp only
    rw [add_mul, add_mul, resid_add R σ h1 h2, add_div]
  · intro I q hq f s e hs hf hse
    obtain ⟨i, hi⟩ := I.2.1
    have h1 := (hkey I i hi q hq).1
    obtain ⟨ha1, ha2⟩ := hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)
    have hm : aeval x f / aeval x s * q * x j ^ c * w = aeval x f / aeval x s * (q * x j ^ c * w) := by ring
    rw [hr]
    dsimp only
    rw [hm, resid_mul R σ ha1 h1, ha2, mul_div_assoc]
  · intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      exact hmem I q hq
    · intro t ht
      have ht' : x' i ^ c * t ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
        rw [← hQ' I]
        exact (TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mpr ⟨t, ht, rfl⟩
      have hall : ∀ u ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H),
          x' i ^ (-c) * u ∈ Submodule.span (Kleiman.chartRing F x' I) (r '' Q.sub (Kleiman.liftChart hxy I)) := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨h, hh, rfl⟩ := hu
          have hh' : h ∈ (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub (Kleiman.liftChart hxy I) := by
            rw [hQ]
            exact Submodule.subset_span hh
          obtain ⟨y, hy, rfl⟩ :=
            (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mp hh'
          obtain ⟨hm, e⟩ := hH _ hh
          obtain ⟨-, e', -⟩ := hkey I i hi y hy
          have e'' : resid R σ (x i ^ c * y * w) = ρ (x i ^ c • y) * w' := (resid_of_mem R σ hm).trans e
          rw [e'', mul_div_cancel_right₀ _ hw'] at e'
          have : x' i ^ (-c) * ρ (x i ^ c • y) = r y := by
            rw [← e', zpow_neg]
            field_simp
          rw [this]
          exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero => rw [mul_zero]; exact zero_mem _
        | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
        | smul a u _ hu =>
          rw [Kleiman.chartRing_smul_def, mul_left_comm]
          exact Submodule.smul_mem _ a hu
      have := hall _ ht'
      rwa [← mul_assoc, ← zpow_add₀ hx'i, neg_add_cancel, zpow_zero, one_mul] at this
end RestrictGen
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
