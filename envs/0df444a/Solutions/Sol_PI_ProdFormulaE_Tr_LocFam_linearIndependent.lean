-- Prove2me | solution 1 for PI.ProdFormulaE.Tr.LocFam.linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:17:10.37637+00:00
-- url     : https://prove2.me/submissions/061cde40-31ed-4728-b2fe-f5227ee11258

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_TrBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ExistsEqEllMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_InjectiveOfLinearIndependent
import Theorems.Thm_P2M_PI_ProdFormulaE_Tr_vle_iff__d845e1513a70
import Theorems.Thm_PI_ProdFormulaE_Tr_LocFam_valuation_algebraMap_le_one
import Theorems.Thm_P2M_PI_ProdFormulaE_Tr_LocFam_valuation__F_le_one_d2c007035a50
import Theorems.Thm_P2M_PI_ProdFormulaE_Tr_LocFam___tmul_c045d1bf3d1e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField TensorProduct ValuativeRel
open PI PI.ProdFormulaE PI.ProdFormulaE.Tr
variable {F : Type} [Field F] [NumberField F] {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type}
namespace PI.ProdFormulaE.Tr
namespace LocFam
theorem _root_.solution [Fintype ι] (D : LocFam F ℓ ι) (hD : D.Over)
    (hA : ∀ X : 𝓞 F, (∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal →
      v.valuation F (X : F) ≤ v.valuation F (ℓ : F)) → ∃ Z : 𝓞 F, X = ℓ * Z)
    (hB : ∀ c : ℚ_[ℓ], ‖c‖ ≤ 1 → ∃ m : ℤ, ‖(c - m) / ℓ‖ ≤ 1) :
    LinearIndependent ℚ_[ℓ] (fun k => D.Φ (1 ⊗ₜ integralBasis F k)) := by
  classical
  set b := integralBasis F with hb_def
  set bZ := RingOfIntegers.basis F with hbZ
  have hbb : ∀ k, b k = algebraMap (𝓞 F) F (bZ k) := fun k => by
    rw [hb_def, hbZ, integralBasis_apply]
  have hw : ∀ k i, D.Φ (1 ⊗ₜ b k) i = D.ιF i (b k) := fun k i => by
    rw [LocFam.Φ_tmul, map_one, one_mul]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨k1, hk1⟩ := hne
  obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image Finset.univ (fun k => ‖g k‖) ⟨k1, Finset.mem_univ _⟩
  have hg0 : g k0 ≠ 0 := by
    intro h
    have h' := hk0 k1 (Finset.mem_univ _)
    rw [h, norm_zero] at h'
    exact hk1 (norm_le_zero_iff.1 h')
  set c : _ → ℚ_[ℓ] := fun k => g k / g k0 with hc_def
  have hc1 : ∀ k, ‖c k‖ ≤ 1 := fun k => by
    simp only [hc_def, norm_div]
    exact div_le_one_of_le₀ (hk0 k (Finset.mem_univ _)) (norm_nonneg _)
  have hck0 : c k0 = 1 := div_self hg0
  have hrel : ∀ i, ∑ k, algebraMap ℚ_[ℓ] (D.K i) (c k) * D.ιF i (b k) = 0 := by
    intro i
    have h := congrFun hg i
    simp only [Finset.sum_apply, Pi.smul_apply, hw, Pi.zero_apply] at h
    have h2 := congrArg (fun y => algebraMap ℚ_[ℓ] (D.K i) (g k0)⁻¹ * y) h
    simp only [mul_zero, Finset.mul_sum, Algebra.smul_def] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hc_def, div_eq_inv_mul, map_mul, mul_assoc]
  choose m hm using fun k => hB (c k) (hc1 k)
  set d : _ → ℚ_[ℓ] := fun k => (c k - m k) / ℓ with hd_def
  have hd1 : ∀ k, ‖d k‖ ≤ 1 := hm
  have hℓ0 : (ℓ : ℚ_[ℓ]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero
  have hcd : ∀ k, c k - m k = ℓ * d k := fun k => by
    simp only [hd_def]
    field_simp
  set X : 𝓞 F := ∑ k, m k • bZ k with hX_def
  have hXF : ((X : 𝓞 F) : F) = ∑ k, (m k : F) * b k := by
    first
    | (rw [hX_def]; simp [hbb, zsmul_eq_mul])
    | (push_cast [hX_def, hbb, zsmul_eq_mul]; rfl)
  have hval : ∀ v : HeightOneSpectrum (𝓞 F), (ℓ : 𝓞 F) ∈ v.asIdeal →
      v.valuation F (X : F) ≤ v.valuation F (ℓ : F) := by
    intro v hv
    obtain ⟨i, rfl⟩ := (hD.2 v).2 hv
    rw [← D.val i, vle_iff']
    have hterm : ∀ k, D.ιF i ((m k : F) * b k) = algebraMap ℚ_[ℓ] (D.K i) (c k) * D.ιF i (b k)
        - (ℓ : D.K i) * (algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k)) := by
      intro k
      have e : (m k : ℚ_[ℓ]) = c k - ℓ * d k := by rw [← hcd]; ring
      have e' : ((m k : ℤ) : D.K i) = algebraMap ℚ_[ℓ] (D.K i) (c k)
          - (ℓ : D.K i) * algebraMap ℚ_[ℓ] (D.K i) (d k) := by
        rw [← map_intCast (algebraMap ℚ_[ℓ] (D.K i)), e, map_sub, map_mul, map_natCast]
      rw [map_mul, map_intCast, e']
      ring
    have hιX : D.ιF i (X : F) =
        -((ℓ : D.K i) * ∑ k, algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k)) := by
      rw [hXF, map_sum, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib, hrel i,
        Finset.mul_sum]
      ring
    have hsum : valuation (D.K i) (∑ k, algebraMap ℚ_[ℓ] (D.K i) (d k) * D.ιF i (b k)) ≤ 1 := by
      refine Valuation.map_sum_le _ fun k _ => ?_
      rw [map_mul, hbb]
      exact mul_le_one' (LocFam.valuation_algebraMap_le_one D i _ (hd1 k))
        (LocFam.valuation_ιF_le_one D i (bZ k))
    rw [hιX, Valuation.map_neg, map_mul, map_natCast (D.ιF i) ℓ]
    first
    | exact mul_le_of_le_one_right' hsum
    | exact mul_le_of_le_one_right₀ hsum
    | (calc _ ≤ valuation (D.K i) (ℓ : D.K i) * 1 := by gcongr
        _ = _ := mul_one _)
  obtain ⟨Z, hZ⟩ := hA X hval
  have hrepr : ∀ k, bZ.repr X k = m k := fun k => by
    rw [hX_def, bZ.repr_sum_self]
  have hmk : m k0 = ℓ * bZ.repr Z k0 := by
    have h := congrArg (fun y => bZ.repr y k0) hZ
    simp only [hrepr] at h
    rw [h]
    have e : ((ℓ : 𝓞 F) * Z) = (ℓ : ℤ) • Z := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [e, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e := hcd k0
  rw [hck0, hmk] at e
  push_cast at e
  have h1 : (1 : ℚ_[ℓ]) = ℓ * (((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0) := by linear_combination e
  have hn := congrArg norm h1
  rw [norm_one, norm_mul] at hn
  have hlt : ‖(ℓ : ℚ_[ℓ])‖ < 1 := Padic.norm_p_lt_one
  have hle : ‖((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0‖ ≤ 1 :=
    (Padic.nonarchimedean _ _).trans (max_le (Padic.norm_int_le_one _) (hd1 k0))
  nlinarith [norm_nonneg (ℓ : ℚ_[ℓ]), norm_nonneg (((bZ.repr Z k0 : ℤ) : ℚ_[ℓ]) + d k0)]
end LocFam
end PI.ProdFormulaE.Tr
