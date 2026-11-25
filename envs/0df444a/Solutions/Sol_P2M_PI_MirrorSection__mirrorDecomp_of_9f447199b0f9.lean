-- Prove2me | solution 1 for P2M_PI_MirrorSection__mirrorDecomp_of_9f447199b0f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:13.097244+00:00
-- url     : https://prove2.me/submissions/384e5f62-4fad-4593-83ff-b80181e12247

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_HpkRowEsI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_MirrorDecompOf
import Theorems.Thm_P2M_PI_MirrorSection__frame_inv_c135116a64e8
import Theorems.Thm_P2M_PI_MirrorSection__uw_frame_2381ece0c326
import Theorems.Thm_P2M_PI_MirrorSection__pair_lt_5ab1db9d22d9
import Theorems.Thm_P2M_PI_MirrorSection__pair_of_lt_a26c1bd2bfcb
import Theorems.Thm_P2M_PI_MirrorSection__conj_n_ea3c2f1eea26
import Theorems.Thm_P2M_PI_MirrorSection__det_ut_7f3e5f0304a5
import Theorems.Thm_P2M_PI_MirrorSection__n_inv_2b0268f7044c
import Theorems.Thm_P2M_PI_MirrorSection__n_mul_f9b46a5d1768
import Theorems.Thm_P2M_PI_MirrorSection__split_exists_d066fd052d45
import Theorems.Thm_P2M_PI_MirrorSection__split_unique_901b42c7598e
import Theorems.Thm_P2M_PI_MirrorSection__uh_inv_11c75eae1df9
import Theorems.Thm_P2M_PI_MirrorSection__ut_inv_c3f594f8935a
import Theorems.Thm_P2M_PI_MirrorSection__uw_inv_20d23c57ffe1
import Theorems.Thm_P2M_PI_MirrorSection__uw_mul_58b4297bf430
import Theorems.Thm_PI_StabPairsW_Sset_frame
import Theorems.Thm_PI_StabPairsW_det_Zhat_ne
import Theorems.Thm_PI_StabPairsW_isUnit_det_of_mem_GV
import Theorems.Thm_PI_StabPairsW_mul_of_col
import Theorems.Thm_PI_StabPairsW_rho_conj
import Theorems.Thm_PI_StabPairsW_uMap_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW
variable {k r : ℕ}
namespace PI.MirrorSection₂
theorem _root_.solution (hC : CurvatureConditionOneClauseThree) (hT : TauMem) (hLS : LowSplit) : MirrorDecomp := by
  intro k r z z' γ hS hP hmono s' hs'
  have hz' : StdZ k r z' := hS.2.2
  have hγ : γ ∈ B.GV k r := hP.1
  have hPd : IsUnit (Zhat k r z z' γ).det := isUnit_iff_ne_zero.mpr (det_Zhat_ne z z' hS γ hP)
  obtain ⟨hbij, -, hinj⟩ := hC k r z z' γ hS hP

  have hRS : ∀ ρ ∈ Rst k r z z' γ, γ⁻¹ * ρ * γ ∈ Sset k r z' := by
    intro ρ hρ
    obtain ⟨s0, hs0, he⟩ := hρ.1.2
    rw [(rho_conj γ hγ ρ s0 he).1]; exact hs0
  have hRL : ∀ ρ ∈ Rst k r z z' γ,
      Zhat k r z z' γ * uMap k r z' (γ⁻¹ * ρ * γ) * (Zhat k r z z' γ)⁻¹ ∈ LTset (r + 1) := by
    intro ρ hρ
    obtain ⟨hb, -, he⟩ := hbij.1 hρ
    exact pair_lt hb he hPd

  have hSgF : ∀ σ ∈ Sg' k r z z' γ, ∃ v, v ∈ UTset (r + 1) ∧
      Zhat k r z z' γ * v * (Zhat k r z z' γ)⁻¹ ∈ UTset (r + 1) ∧ σ * Ff k r z' = Ff k r z' * v := by
    rintro σ ⟨n0, hn0, v, hv, hvP, h, hh, rfl⟩
    obtain ⟨-, hn0F, -⟩ := Sset_frame z' hz' n0 ⟨1, ⟨by show (1 : B.Mat k r)ᴴ * Hpk k r * 1 = Hpk k r; simp,
      fun a => ⟨by simp, by simp⟩, by simp⟩, n0, hn0.1, (Matrix.one_mul _).symm⟩
    rw [hn0.2, Matrix.mul_one] at hn0F
    have hτ := hT k r z' hz' v hv
    have hτF : tauM k r z' v * Ff k r z' = Ff k r z' * v := mul_of_col z' _ v hτ.2.1
    refine ⟨v, hv, hvP, ?_⟩
    calc n0 * tauM k r z' v * h * Ff k r z' = n0 * (tauM k r z' v * (h * Ff k r z')) := by
          simp only [Matrix.mul_assoc]
      _ = Ff k r z' * v := by rw [uw_frame hh, hτF, ← Matrix.mul_assoc, hn0F]

  have hdata : ∀ ρ σ, ρ ∈ Rst k r z z' γ → σ ∈ Sg' k r z z' γ → s' = γ⁻¹ * ρ * γ * σ →
      ∃ v, Zhat k r z z' γ * v * (Zhat k r z z' γ)⁻¹ ∈ UTset (r + 1) ∧
        uMap k r z' s' = uMap k r z' (γ⁻¹ * ρ * γ) * v := by
    intro ρ σ hρ hσ he
    obtain ⟨v, -, hvP, hσF⟩ := hSgF σ hσ
    obtain ⟨-, hxF, -⟩ := Sset_frame z' hz' _ (hRS ρ hρ)
    refine ⟨v, hvP, uMap_eq z' hz' s' _ ?_⟩
    rw [he]
    calc γ⁻¹ * ρ * γ * σ * Ff k r z' = (γ⁻¹ * ρ * γ) * (σ * Ff k r z') := by rw [Matrix.mul_assoc]
      _ = Ff k r z' * (uMap k r z' (γ⁻¹ * ρ * γ) * v) := by
          rw [hσF, ← Matrix.mul_assoc, hxF, Matrix.mul_assoc]

  have huniq : ∀ ρ₁ σ₁ ρ₂ σ₂, ρ₁ ∈ Rst k r z z' γ → σ₁ ∈ Sg' k r z z' γ → s' = γ⁻¹ * ρ₁ * γ * σ₁ →
      ρ₂ ∈ Rst k r z z' γ → σ₂ ∈ Sg' k r z z' γ → s' = γ⁻¹ * ρ₂ * γ * σ₂ → ρ₁ = ρ₂ ∧ σ₁ = σ₂ := by
    intro ρ₁ σ₁ ρ₂ σ₂ h1 h1' e1 h2 h2' e2
    obtain ⟨v₁, hv₁, hu₁⟩ := hdata ρ₁ σ₁ h1 h1' e1
    obtain ⟨v₂, hv₂, hu₂⟩ := hdata ρ₂ σ₂ h2 h2' e2
    have ha := split_unique hPd (hRL ρ₁ h1) (hRL ρ₂ h2) hv₁ hv₂ (hu₁.symm.trans hu₂)
    have hρ : ρ₁ = ρ₂ := hinj h1 h2 ha
    subst hρ
    refine ⟨rfl, ?_⟩
    have hx : IsUnit (γ⁻¹ * ρ₁ * γ).det := isUnit_det_of_mem_GV (Sset_frame z' hz' _ (hRS ρ₁ h1)).1
    have e3 := e1.symm.trans e2
    calc σ₁ = (γ⁻¹ * ρ₁ * γ)⁻¹ * (γ⁻¹ * ρ₁ * γ * σ₁) := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hx, Matrix.one_mul]
      _ = (γ⁻¹ * ρ₁ * γ)⁻¹ * (γ⁻¹ * ρ₁ * γ * σ₂) := by rw [e3]
      _ = σ₂ := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hx, Matrix.one_mul]

  obtain ⟨h, hh, m, hm, hsm⟩ := hs'
  obtain ⟨-, hs'F, huUT⟩ := Sset_frame z' hz' s' ⟨h, hh, m, hm, hsm⟩
  obtain ⟨a, v, haU, hvU, haL, hvP, hsplit⟩ := split_exists hLS hmono hPd huUT
  obtain ⟨b, hbU, hbP⟩ := pair_of_lt hPd haL
  have hmem : ((b, a) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ × Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) ∈
      {p : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ × Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ |
        p.1 ∈ UTset (r + 1) ∧ p.2 ∈ UTset (r + 1) ∧ p.1ᴴ * Zhat k r z z' γ * p.2 = Zhat k r z z' γ} :=
    ⟨hbU, haU, hbP⟩
  obtain ⟨ρ, hρ, hρe⟩ := hbij.2.2 hmem
  have hxa : uMap k r z' (γ⁻¹ * ρ * γ) = a := (Prod.ext_iff.mp hρe).2
  obtain ⟨x, hxdef⟩ : ∃ x, x = γ⁻¹ * ρ * γ := ⟨_, rfl⟩
  have hxS : x ∈ Sset k r z' := by rw [hxdef]; exact hRS ρ hρ
  obtain ⟨h₂, hh₂, m₂, hm₂, hx2⟩ := id hxS
  obtain ⟨hxG, hxF, -⟩ := Sset_frame z' hz' x hxS
  rw [hxdef, hxa, ← hxdef] at hxF
  have hxU := isUnit_det_of_mem_GV hxG
  have iA := ut_inv haU
  have hxiF : x⁻¹ * Ff k r z' = Ff k r z' * a⁻¹ :=
    frame_inv hxU (by rw [det_ut haU]; exact isUnit_one) hxF
  obtain ⟨h₃, hh3def⟩ : ∃ h₃, h₃ = h₂⁻¹ * h := ⟨_, rfl⟩
  have hh₃ : h₃ ∈ UWset k r z' := by rw [hh3def]; exact uw_mul (uw_inv hh₂) hh
  have ih₃ := uh_inv hh₃.1
  have hcm : h₃ * m * h₃⁻¹ ∈ Nset k r := by
    have := conj_n (uw_inv hh₃) hm
    rwa [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GV hh₃.1)] at this
  obtain ⟨n, hndef⟩ : ∃ n, n = m₂⁻¹ * (h₃ * m * h₃⁻¹) := ⟨_, rfl⟩
  have hn : n ∈ Nset k r := by rw [hndef]; exact n_mul (n_inv hm₂) hcm
  have hσ_eq : x⁻¹ * s' = n * h₃ := by
    have e1 : x⁻¹ * s' = m₂⁻¹ * (h₃ * m) := by
      rw [hx2, hsm, Matrix.mul_inv_rev, hh3def]; simp only [Matrix.mul_assoc]
    rw [e1, hndef]
    simp only [Matrix.mul_assoc]
    rw [ih₃.2.1, Matrix.mul_one]
  have hσF : x⁻¹ * s' * Ff k r z' = Ff k r z' * v := by
    rw [Matrix.mul_assoc, hs'F, hsplit, ← Matrix.mul_assoc, hxiF, Matrix.mul_assoc, ← Matrix.mul_assoc a⁻¹,
      iA.2.1, Matrix.one_mul]
  have hnF : n * Ff k r z' = Ff k r z' * v := by
    calc n * Ff k r z' = n * (h₃ * Ff k r z') := by rw [uw_frame hh₃]
      _ = x⁻¹ * s' * Ff k r z' := by rw [← Matrix.mul_assoc, hσ_eq]
      _ = Ff k r z' * v := hσF
  have hτ := hT k r z' hz' v hvU
  have hτF : tauM k r z' v * Ff k r z' = Ff k r z' * v := mul_of_col z' _ v hτ.2.1
  have iτ := uh_inv hτ.1.1
  have hvd : IsUnit v.det := by rw [det_ut hvU]; exact isUnit_one
  have hτiF : (tauM k r z' v)⁻¹ * Ff k r z' = Ff k r z' * v⁻¹ :=
    frame_inv (isUnit_det_of_mem_GV hτ.1.1) hvd hτF
  have hn0 : n * (tauM k r z' v)⁻¹ ∈ Nset k r := n_mul hn (n_inv hτ.1)
  have hn0F : n * (tauM k r z' v)⁻¹ * Ff k r z' = Ff k r z' * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) := by
    rw [Matrix.mul_assoc, hτiF, ← Matrix.mul_assoc, hnF, Matrix.mul_assoc, (ut_inv hvU).1]
  have hn0u : uMap k r z' (n * (tauM k r z' v)⁻¹) = 1 := uMap_eq z' hz' _ _ hn0F
  have hσmem : x⁻¹ * s' ∈ Sg' k r z z' γ := by
    refine ⟨n * (tauM k r z' v)⁻¹, ⟨hn0, hn0u⟩, v, hvU, hvP, h₃, hh₃, ?_⟩
    rw [hσ_eq, Matrix.mul_assoc n, iτ.2.1, Matrix.mul_one]
  have heq : s' = γ⁻¹ * ρ * γ * (x⁻¹ * s') := by
    rw [← hxdef, ← Matrix.mul_assoc, mul_nonsing_inv _ hxU, Matrix.one_mul]
  refine ⟨(ρ, x⁻¹ * s'), ⟨hρ, hσmem, heq⟩, ?_⟩
  rintro ⟨ρ', σ'⟩ ⟨h1, h2, h3⟩
  obtain ⟨e1, e2⟩ := huniq ρ' σ' ρ _ h1 h2 h3 hρ hσmem heq
  exact Prod.ext e1 e2
end PI.MirrorSection₂
