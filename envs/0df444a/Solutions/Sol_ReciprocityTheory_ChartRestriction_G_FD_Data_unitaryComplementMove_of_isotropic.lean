-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.unitaryComplementMove_of_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:03:56.672847+00:00
-- url     : https://prove2.me/submissions/696f40f5-f12f-4437-bc34-3c46c77b72e5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gram_unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_unitary
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_col_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_emb_herm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution : UnitaryComplementMove (E := E) := by
  intro r X ξ hξ x hx h1 hu hfix _hU
  have hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0 := fun τ => by
    rw [← emb_herm, hξ.2.1, map_zero]
  set x' := X.lmulC h1 x with hx'
  have hloc : ∀ τ : X.Ψ, X.lmulC h1 x = X.lmulC (fun _ => h1 τ) x ∨ True := fun _ => Or.inr trivial

  have hmat : ∀ τ, mat x' τ = h1 τ * mat x τ := fun τ => rfl
  have hgramτ : ∀ τ, gram τ.1 X.Gm (mat x' τ) = gram τ.1 X.Gm (mat x τ) := fun τ => by
    rw [hmat]; exact gram_unitary X x τ (h1 τ) (hu τ)

  have hfe : ∀ τ, Matrix.mulVec (h1 τ) (emb τ.1 ξ) = emb τ.1 ξ := by
    intro τ
    have h := congrFun (hfix (fun _ => 1) (fun _ => 0)) τ
    simp only [applyV, lineV, Jz, Pi.add_apply, one_smul, zero_smul, ppos_zero, smul_zero,
      sub_zero, add_zero] at h
    exact h
  have hfJ : ∀ τ, Matrix.mulVec (h1 τ) ((2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ) =
      (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
    intro τ
    have h := congrFun (hfix (fun _ => 0) (fun _ => -I)) τ
    simp only [applyV, lineV, Jz, Pi.add_apply, zero_smul, zero_add, ppos_smul, smul_smul] at h
    have e1 : I • (((2 : ℂ) * -I) • X.ppos x τ (emb τ.1 ξ) - -I • emb τ.1 ξ) =
        (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
      rw [smul_sub, smul_smul, smul_smul, show I * (2 * -I) = (2 : ℂ) by
        linear_combination (-2 : ℂ) * Complex.I_mul_I, show I * -I = (1 : ℂ) by
        linear_combination (-1 : ℂ) * Complex.I_mul_I, one_smul]
    rw [e1] at h
    exact h

  have hdom : x' ∈ X.dom := by
    intro τ
    refine ⟨?_, fun i => ?_⟩
    · rw [hmat, Matrix.det_mul]
      refine mul_ne_zero ?_ (hx τ).1
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0

      have hrad : ∀ w, hermC τ.1 X.Gm v w = 0 := fun w => by rw [← hu τ v w, hv]; simp [hermC]
      have hG : (Matrix.map X.Gm τ.1).det ≠ 0 := by
        have h := RingHom.map_det τ.1 X.Gm
        rw [show τ.1.mapMatrix X.Gm = X.Gm.map τ.1 from rfl] at h
        rw [← h]; exact (map_ne_zero _).mpr X.Gm_det
      by_contra hne
      apply hG
      apply Matrix.exists_vecMul_eq_zero_iff.mp
      refine ⟨v, hne, ?_⟩
      funext b
      have := hrad (Pi.single b 1)
      simpa [hermC, Matrix.vecMul, dotProduct, Pi.single_apply, Matrix.map_apply] using this
    · have : dmin X.Gm x' τ i = dmin X.Gm x τ i := by
        simp only [dmin]; rw [hgramτ]
      rw [this]; exact (hx τ).2 i
  refine ⟨hdom, ?_, ?_, ?_⟩
  ·
    intro u _
    funext τ
    have hJe : (2 : ℂ) • X.ppos x' τ (emb τ.1 ξ) - emb τ.1 ξ =
        (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
      have hp := ppos_unitary X x τ (h1 τ) (hu τ) hx (emb τ.1 ξ)
      rw [hfe τ] at hp
      rw [show X.ppos x' τ (emb τ.1 ξ) = X.ppos (X.lmulC (fun _ => h1 τ) x) τ (emb τ.1 ξ) from rfl, hp]
      rw [← Matrix.mulVec_smul, ← hfe τ, ← Matrix.mulVec_sub, hfe τ, hfJ τ]
    simp only [aproj, lineV]
    rw [Hf_eq X x' hdom, Hf_eq X x' hdom, Hf_eq X x hx, Hf_eq X x hx, hJe]
  · intro τ

    have hpp : X.posPart x' τ (emb τ.1 ξ) = X.posPart x τ (emb τ.1 ξ) := by
      have hgp : X.gramPos x' τ = X.gramPos x τ := by simp only [gramPos]; rw [hgramτ]
      simp only [posPart]
      rw [hgp]
      have hc : ∀ a : Fin X.p0, hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x' τ) (Fin.castLE X.p0_le a)) =
          hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x τ) (Fin.castLE X.p0_le a)) := by
        intro a
        rw [hmat, col_mul]
        conv_lhs => rw [← hfe τ]
        rw [hu τ]
      simp only [hc]
    simp only [maj, hpp]
  · intro u _
    funext τ
    simp only [Jz, applyV]
    have hp := ppos_unitary X x τ (h1 τ) (hu τ) hx (u τ)
    rw [show X.ppos x' τ (Matrix.mulVec (h1 τ) (u τ)) =
      X.ppos (X.lmulC (fun _ => h1 τ) x) τ (Matrix.mulVec (h1 τ) (u τ)) from rfl, hp]
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul]
end ReciprocityTheory.ChartRestriction.G.FD.Data
