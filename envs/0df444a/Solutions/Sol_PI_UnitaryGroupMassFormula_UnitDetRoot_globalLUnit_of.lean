-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.globalLUnit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:07:28.460579+00:00
-- url     : https://prove2.me/submissions/275eb0eb-6e2c-4c11-926a-f25385360b84

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobTop
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_lunit_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_ne_bot_of_smul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_nsmul_relIdx_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_span_single_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_span_single_pow
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_sub_pow_le
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_sub_pow_principal
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI Submodule NumberField
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution
    (hV1 : ∀ (F : IntermediateField ℚ ℂ) (m : Type) [Fintype m] [DecidableEq m] (Λ Λ' : AddSubgroup (m → ℂ))
      (c : ℂ), (∀ x ∈ Λ, c • x ∈ Λ') → span (𝓞 F) {c ^ Fintype.card m} * vol F Λ ≤ vol F Λ')
    (hV2 : ∀ (F : IntermediateField ℚ ℂ) (m : Type) [Fintype m] [DecidableEq m]
      (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)),
      vol F (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ) =
        span (𝓞 F) {LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))} * vol F Λ)
    (hV3 : ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
      (m : Type) [Fintype m] [DecidableEq m], UnitDetRootDefs.CmOK a b c d →
      vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≤ span (𝓞 (KF b d)) {lam ^ Fintype.card m})
    (hV4 : ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
      (m : Type) [Fintype m] [DecidableEq m], UnitDetRootDefs.CmOK a b c d →
      vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ ⊥) :
    GlobalLUnit := by
  intro a b c d ha hd lam hlam m _ _ Λa hH
  obtain ⟨hok, -, -, hi1, hi2⟩ := hH
  have : FiniteDimensional ℚ (KF b d) := IntermediateField.adjoin.finiteDimensional (theta_isIntegral hok)
  have : NumberField (KF b d) := { }
  set F := KF b d with hFdef
  set Lt := UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m with hLt
  set N1 := UnitDetRootDefs.relIdx Lt Λa with hN1
  set N2 := UnitDetRootDefs.relIdx Λa Lt with hN2
  set e := Fintype.card m with he
  set h := hF F with hh
  have hN10 : (N1 : ℂ) ≠ 0 := by exact_mod_cast hi1
  have hN20 : (N2 : ℂ) ≠ 0 := by exact_mod_cast hi2
  have hL0 : vol F Lt ≠ ⊥ := hV4 a b c d ha hd lam hlam m hok
  have hLle : vol F Lt ≤ span (𝓞 F) {lam ^ e} := hV3 a b c d ha hd lam hlam m hok
  have hA1 : span (𝓞 F) {(N1 : ℂ) ^ e} * vol F Λa ≤ vol F Lt :=
    hV1 F m Λa Lt _ fun x hx => by rw [Nat.cast_smul_eq_nsmul]; exact nsmul_relIdx_mem Lt Λa hx
  have hA2 : span (𝓞 F) {(N2 : ℂ) ^ e} * vol F Lt ≤ vol F Λa :=
    hV1 F m Lt Λa _ fun x hx => by rw [Nat.cast_smul_eq_nsmul]; exact nsmul_relIdx_mem Λa Lt hx
  have hA0 : vol F Λa ≠ ⊥ := ne_bot_of_smul (pow_ne_zero _ hN20) hA2 hL0
  have hAle : vol F Λa ≤ span (𝓞 F) {lam ^ e / (N1 : ℂ) ^ e} := by
    intro x hx
    obtain ⟨o, ho⟩ := mem_span_singleton.mp (hLle (hA1 (mul_mem_mul (mem_span_singleton_self _) hx)))
    rw [mem_span_singleton]
    refine ⟨o, ?_⟩
    rw [Algebra.smul_def] at ho ⊢
    rw [mul_div_assoc', div_eq_iff (pow_ne_zero _ hN10)]
    linear_combination ho
  obtain ⟨y1, hy1, e1⟩ := sub_pow_principal F (vol F Lt) hL0 (lam ^ e) (pow_ne_zero _ hlam) hLle
  obtain ⟨y2, hy2, e2⟩ := sub_pow_principal F (vol F Λa) hA0 (lam ^ e / (N1 : ℂ) ^ e)
    (div_ne_zero (pow_ne_zero _ hlam) (pow_ne_zero _ hN10)) hAle
  have hy1' : (y1 : ℂ) ≠ 0 := fun h0 => hy1 (Subtype.ext h0)
  have hy2' : (y2 : ℂ) ≠ 0 := fun h0 => hy2 (Subtype.ext h0)
  set α := (lam ^ e) ^ h * (y1 : ℂ) with hα
  set β := (lam ^ e / (N1 : ℂ) ^ e) ^ h * (y2 : ℂ) with hβ
  have hα0 : α ≠ 0 := mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hlam)) hy1'
  have hβ0 : β ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (div_ne_zero (pow_ne_zero _ hlam) (pow_ne_zero _ hN10))) hy2'
  have hγ : α / β = (N1 : ℂ) ^ (e * h) * (y1 : ℂ) / (y2 : ℂ) := by
    rw [hα, hβ, div_pow, pow_mul]
    field_simp
  have hγmem : α / β ∈ KF b d := by
    rw [hγ]
    exact div_mem (mul_mem (pow_mem (IntermediateField.natCast_mem _ N1) _) y1.2) y2.2
  have hpos : 0 < h := Fintype.card_pos
  refine ⟨α / β, hγmem, div_ne_zero hα0 hβ0, h, hpos, ?_⟩
  intro l _ δ _ hE
  obtain ⟨k, hk, hk1, hk2⟩ := hE
  set u := LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) with hu
  have hu0 : u ≠ 0 := (LinearEquiv.isUnit_det' δ).ne_zero
  have hvi := hV2 F m δ Λa
  have i1 : span (𝓞 F) {(k : ℂ) ^ e} * vol F Lt ≤ span (𝓞 F) {u} * vol F Λa :=
    hvi ▸ hV1 F m _ _ _ hk1
  have i2 : span (𝓞 F) {(k : ℂ) ^ e} * (span (𝓞 F) {u} * vol F Λa) ≤ vol F Lt :=
    hvi ▸ hV1 F m _ _ _ hk2
  have j1 := sub_pow_le F i1 h
  have j2 := sub_pow_le F i2 h
  rw [mul_pow, mul_pow, span_single_pow, span_single_pow, e1, e2, span_single_mul,
    span_single_mul] at j1
  rw [mul_pow, mul_pow, span_single_pow, span_single_pow, e1, e2, span_single_mul,
    span_single_mul] at j2
  have hkc : ((k : ℂ) ^ e) ^ h = ((k ^ (e * h) : ℕ) : ℂ) := by push_cast; rw [pow_mul]
  rw [hkc] at j1 j2
  have hl : ¬ l ∣ k ^ (e * h) := fun hd' => hk ((Fact.out : l.Prime).dvd_of_dvd_pow hd')
  exact lunit_of F hα0 hβ0 (pow_ne_zero _ hu0) hl j1 j2
end PI.UnitaryGroupMassFormula.UnitDetRoot
