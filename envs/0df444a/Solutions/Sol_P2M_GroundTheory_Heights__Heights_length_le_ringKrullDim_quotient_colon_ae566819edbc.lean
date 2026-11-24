-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_length_le_ringKrullDim_quotient_colon_ae566819edbc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:11.799117+00:00
-- url     : https://prove2.me/submissions/3e2b89c3-a5a2-41b3-96f7-007575b0d9cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing RingTheory.Sequence Pointwise
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (rs : List R) : ∀ {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (y : M), y ≠ 0 →
      (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular M rs →
        (rs.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R M) {y}) := by
  induction rs with
  | nil =>
    intro M _ _ _ y hy _ _
    have hne : Submodule.colon (⊥ : Submodule R M) {y} ≠ ⊤ := by
      intro h
      have h1 : (1 : R) ∈ Submodule.colon (⊥ : Submodule R M) {y} := h ▸ Submodule.mem_top
      rw [Submodule.mem_colon_singleton, one_smul] at h1
      exact hy ((Submodule.mem_bot R).mp h1)
    have := Ideal.Quotient.nontrivial_iff.mpr hne
    simpa using (ringKrullDim_nonneg_of_nontrivial : 0 ≤ ringKrullDim (R ⧸ _))
  | cons x rs ih =>
    intro M _ _ _ y hy hmem hreg
    have hx : x ∈ maximalIdeal R := hmem x List.mem_cons_self
    have hmem' : ∀ r ∈ rs, r ∈ maximalIdeal R := fun r hr => hmem r (List.mem_cons_of_mem x hr)
    obtain ⟨hxreg, hrs⟩ := (isWeaklyRegular_cons_iff M x rs).mp hreg

    have hspan : Ideal.span {x} ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ (Ideal.span_le.mpr (by simpa using hx))))
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (Ideal.span {x}) hspan
    have hpow : ∀ k : ℕ, (Ideal.span {x} ^ k • ⊤ : Submodule R M) = x ^ k • ⊤ := fun k => by
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul]
    have hex : ∃ n : ℕ, y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M) := by
      by_contra! h
      exact hy ((Submodule.mem_bot R).mp (hK ▸ Submodule.mem_iInf _ |>.mpr h))
    classical
    let n := Nat.find hex
    have hn : y ∉ (Ideal.span {x} ^ n • ⊤ : Submodule R M) := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h0
      apply hn
      rw [h0, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact Submodule.mem_top
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hyk : y ∈ (Ideal.span {x} ^ k • ⊤ : Submodule R M) := by
      have := Nat.find_min hex (show k < n by omega)
      simpa using this
    rw [hpow] at hyk hn
    obtain ⟨y₁, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hyk
    have hy₁ : y₁ ∉ (x • ⊤ : Submodule R M) := by
      intro h
      obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h
      apply hn
      rw [hk, smul_smul, ← pow_succ]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have hcolon : Submodule.colon (⊥ : Submodule R M) {x ^ k • y₁} =
        Submodule.colon (⊥ : Submodule R M) {y₁} := by
      ext r
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
      rw [smul_comm]
      constructor
      · intro h
        exact (hxreg.pow k) (show x ^ k • r • y₁ = x ^ k • 0 by rw [h, smul_zero])
      · intro h
        rw [h, smul_zero]
    rw [hcolon]

    set I := Submodule.colon (⊥ : Submodule R M) {y₁} with hI
    set ybar : QuotSMulTop x M := Submodule.Quotient.mk y₁ with hybar
    have hybar0 : ybar ≠ 0 := by
      rw [hybar, Ne, Submodule.Quotient.mk_eq_zero]
      exact hy₁
    have hih := ih ybar hybar0 hmem' hrs

    have hle : I ⊔ Ideal.span {x} ≤ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar} := by
      refine sup_le ?_ ?_
      · intro r hr
        rw [hI, Submodule.mem_colon_singleton, Submodule.mem_bot] at hr
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, hr,
          Submodule.Quotient.mk_zero]
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_colon_singleton,
          Submodule.mem_bot, hybar, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    have hd1 : ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}) ≤
        ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) :=
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)

    have hnzd : Ideal.Quotient.mk I x ∈ nonZeroDivisors (R ⧸ I) := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hz
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton,
        Submodule.mem_bot, mul_smul, smul_comm] at hz
      rw [Ideal.Quotient.eq_zero_iff_mem, hI, Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact hxreg (show x • r • y₁ = x • 0 by rw [hz, smul_zero])
    have hd2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
    have heq : (R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x} ≃+* R ⧸ (I ⊔ Ideal.span {x}) := by
      have : Ideal.span {Ideal.Quotient.mk I x} = (Ideal.span {x}).map (Ideal.Quotient.mk I) := by
        rw [Ideal.map_span, Set.image_singleton]
      rw [this]
      exact DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {x})
    rw [ringKrullDim_eq_of_ringEquiv heq] at hd2
    calc ((x :: rs).length : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (R ⧸ Submodule.colon (⊥ : Submodule R (QuotSMulTop x M)) {ybar}) + 1 := by
          gcongr
      _ ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) + 1 := by gcongr
      _ ≤ ringKrullDim (R ⧸ I) := hd2
end GroundTheory.Heights₂.Heights
