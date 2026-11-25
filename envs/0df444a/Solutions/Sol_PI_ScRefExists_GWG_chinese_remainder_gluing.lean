-- Prove2me | solution 1 for PI.ScRefExists.GWG.chinese_remainder_gluing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:25.851667+00:00
-- url     : https://prove2.me/submissions/9333ecaf-42d9-4600-9292-41a2bb3ad123

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
import Theorems.Thm_PI_ScRefExists_GWG_hG_add_right
import Theorems.Thm_PI_ScRefExists_GWG_hG_zsmul_right
import Theorems.Thm_PI_ScRefExists_GWG_hG_comb
import Theorems.Thm_PI_ScRefExists_GWG_hG_int
import Theorems.Thm_PI_ScRefExists_GWG_theta_mem
import Theorems.Thm_PI_ScRefExists_GWG_ite_mem
import Theorems.Thm_PI_ScRefExists_GWG_crt_ge
import Theorems.Thm_PI_ScRefExists_GWG_side_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_ScRefExists_GlueA_hG_int
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
namespace PI.ScRefExists.GWG
open PI.ScRefExists.Sk
section Lemmas
variable (I : Formalism.MainNotions.S.AutInst)
private theorem star_coe_mem_range_algebraMap (θ : 𝓞 I.E) :
    star (θ : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := by
  have h : IsIntegral ℤ (star (θ : I.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom
  exact ⟨⟨star (θ : I.E), h⟩, rfl⟩
end Lemmas
end PI.ScRefExists.GWG
end
end

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
namespace PI.ScRefExists.GWG
theorem _root_.solution : GWcrt := by
  intro I g₁ g₂ r k θ e f M hcop _ hC1 hC2
  obtain ⟨A, B, hAB⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨za, ba, bda, hza, hbaL, hoza, hoba, hGa, hTa, hTTa, hspa⟩ := hC1
  obtain ⟨zb, bb, bdb, hzb, hbbL, hozb, hobb, hGb, hTb, hTTb, hspb⟩ := hC2
  set qa : ℤ := (g₂ : ℤ) * B with hqa
  set qb : ℤ := (g₁ : ℤ) * A with hqb
  have hsumZ : qa + qb = 1 := by rw [hqa, hqb]; linarith
  have hsum : (qa : I.E) + (qb : I.E) = 1 := by exact_mod_cast hsumZ
  have hprod : (qa : I.E) * (qb : I.E) = ((g₁ * g₂ : ℕ) : I.E) * ((A * B : ℤ) : I.E) := by
    rw [hqa, hqb]; push_cast; ring
  have hga : (qa : I.E) * (g₁ : I.E) = ((g₁ * g₂ : ℕ) : I.E) * (B : I.E) := by
    rw [hqa]; push_cast; ring
  have hgb : (qb : I.E) * (g₂ : I.E) = ((g₁ * g₂ : ℕ) : I.E) * (A : I.E) := by
    rw [hqb]; push_cast; ring
  have hsum' : (qb : I.E) + (qa : I.E) = 1 := by rw [add_comm]; exact hsum
  have hprod' : (qb : I.E) * (qa : I.E) = ((g₁ * g₂ : ℕ) : I.E) * ((A * B : ℤ) : I.E) := by
    rw [mul_comm]; exact hprod
  have two_mem : (2 : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := ⟨2, map_ofNat _ 2⟩
  refine ⟨qa • za + qb • zb, fun i => qa • ba i + qb • bb i, fun i => qa • bda i + qb • bdb i,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact I.L.add_mem (zsmul_mem hza qa) (zsmul_mem hzb qb)
  · exact fun i => ⟨I.L.add_mem (zsmul_mem (hbaL i).1 qa) (zsmul_mem (hbbL i).1 qb),
      I.L.add_mem (zsmul_mem (hbaL i).2 qa) (zsmul_mem (hbbL i).2 qb)⟩
  · intro a
    obtain ⟨h1, h2⟩ := hoza a
    obtain ⟨h3, h4⟩ := hozb a
    constructor <;> simp only [hG_add_right, hG_zsmul_right, h1, h2, h3, h4, mul_zero, add_zero]
  · intro a i
    obtain ⟨h1, h2, h3, h4⟩ := hoba a i
    obtain ⟨h5, h6, h7, h8⟩ := hobb a i
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [hG_add_right, hG_zsmul_right, h1, h2, h3, h4, h5, h6, h7, h8, mul_zero, add_zero]
  · refine crt_ge I hqa hqb hGa hGb
      (add_mem (add_mem (hG_int I hza hzb) (hG_int I hzb hza)) two_mem) ?_
    rw [hG_comb]
    linear_combination (-((qa : I.E) + qb + 1)) * hsum
  · intro i
    constructor
    · refine crt_ge I hqa hqb (hTa i).1 (hTb i).1
        (mul_mem (theta_mem I θ) (add_mem (hG_int I hza (hbbL i).1) (hG_int I hzb (hbaL i).1))) ?_
      beta_reduce
      rw [hG_comb]
      ring
    · refine crt_ge I hqa hqb (hTa i).2 (hTb i).2
        (mul_mem (star_coe_mem_range_algebraMap I θ)
          (add_mem (hG_int I hza (hbbL i).2) (hG_int I hzb (hbaL i).2))) ?_
      beta_reduce
      rw [hG_comb]
      ring
  · intro i j
    refine crt_ge I hqa hqb (hTTa i j) (hTTb i j)
      (mul_mem (theta_mem I θ) (sub_mem (add_mem (hG_int I (hbaL i).2 (hbbL j).1)
        (hG_int I (hbbL i).2 (hbaL j).1)) (mul_mem two_mem (ite_mem I (p := i = j))))) ?_
    beta_reduce
    rw [hG_comb]
    linear_combination ((θ : I.E) * (if i = j then (1 : I.E) else 0) * ((qa : I.E) + qb + 1)) * hsum
  · intro y hy
    have h1 := side_mem I e f θ (g₁ * g₂) g₁ qa qb B (A * B) (qa • za + qb • zb) za zb
      (fun i => qa • ba i + qb • bb i) ba bb (fun i => qa • bda i + qb • bdb i) bda bdb hza hzb
      (fun i => ⟨(hbaL i).1, (hbbL i).1, (hbaL i).2, (hbbL i).2⟩) hsum hprod hga rfl
      (fun i => rfl) (fun i => rfl) (hspa y hy)
    have h2 := side_mem I e f θ (g₁ * g₂) g₂ qb qa A (A * B) (qa • za + qb • zb) zb za
      (fun i => qa • ba i + qb • bb i) bb ba (fun i => qa • bda i + qb • bdb i) bdb bda hzb hza
      (fun i => ⟨(hbbL i).1, (hbaL i).1, (hbbL i).2, (hbaL i).2⟩) hsum' hprod' hgb (add_comm _ _)
      (fun i => add_comm _ _) (fun i => add_comm _ _) (hspb y hy)
    have hy' : y = qa • y + qb • y := by rw [← add_smul, hsumZ, one_smul]
    rw [hy']
    exact add_mem h1 h2
end PI.ScRefExists.GWG
