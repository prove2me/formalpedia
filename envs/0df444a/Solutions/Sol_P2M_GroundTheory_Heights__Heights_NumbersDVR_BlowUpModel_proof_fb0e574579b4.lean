-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpModel_proof_fb0e574579b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:37:16.888623+00:00
-- url     : https://prove2.me/submissions/e240ecd0-7ee7-4a43-b173-097d7d10a316

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_blowUpOf_82c52e9c4e5f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace BlowUpModel
theorem _root_.solution (h₁ : ReesAlgebraDim.Statement.{u}) : BlowUpModel.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P d hP N u hu hne
  have : P.IsPrime := hP.multiProj.isPrime
  set φ : MRing (extIdx ι J) O →ₐ[O] Polynomial (MRing ι O ⧸ P) := aeval (blowUpSubst P u)
  refine ⟨⟨RingHom.ker_isPrime φ, isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu, ?_⟩,
    ?_, ?_⟩
  ·
    intro o
    cases o with
    | none =>
      obtain ⟨j, hj⟩ := hne
      refine ⟨j, ?_⟩
      rw [blowUpOf, RingHom.mem_ker]
      change aeval (blowUpSubst P u) (X ⟨none, j⟩) ≠ 0
      rw [aeval_X]
      simpa [blowUpSubst, Ideal.Quotient.eq_zero_iff_mem] using hj
    | some k =>
      obtain ⟨i, hi⟩ := hP.multiProj.relevant k
      refine ⟨i, ?_⟩
      rw [blowUpOf, RingHom.mem_ker]
      change aeval (blowUpSubst P u) (X ⟨some k, i⟩) ≠ 0
      rw [aeval_X]
      simpa [blowUpSubst, Ideal.Quotient.eq_zero_iff_mem] using hi
  ·
    ext c
    rw [Ideal.mem_comap, blowUpOf, RingHom.mem_ker, Ideal.mem_bot]
    change aeval (blowUpSubst P u) (C c) = 0 ↔ c = 0
    rw [aeval_C, Polynomial.algebraMap_apply, Polynomial.C_eq_zero,
      show algebraMap O (MRing ι O ⧸ P) c = Ideal.Quotient.mk P (C c) from rfl,
      Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hP.noTorsion, Ideal.mem_bot]
  ·
    set I : Ideal (MRing ι O ⧸ P) := Ideal.span (Set.range fun j => Ideal.Quotient.mk P (u j))
    have hI : I ≠ ⊥ := by
      obtain ⟨j, hj⟩ := hne
      intro h
      apply hj
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_bot, ← h]
      exact Ideal.subset_span ⟨j, rfl⟩
    have hC : ∀ c : MRing ι O ⧸ P, Polynomial.C c ∈ φ.range := by
      intro c
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact ⟨liftForm (J := J) q, aeval_blowUpSubst_liftForm P u q⟩
    have hrange : φ.range.toSubring = (reesAlgebra I).toSubring := by
      ext x
      simp only [Subalgebra.mem_toSubring]
      constructor
      · rintro ⟨p, rfl⟩
        induction p using MvPolynomial.induction_on with
        | C a =>
          change aeval (blowUpSubst P u) (C a) ∈ reesAlgebra I
          rw [aeval_C, Polynomial.algebraMap_apply]
          exact (reesAlgebra I).algebraMap_mem _
        | add p q hp hq =>
          rw [map_add]
          exact add_mem hp hq
        | mul_X p v hp =>
          rw [map_mul]
          refine mul_mem hp ?_
          change aeval (blowUpSubst P u) (X v) ∈ reesAlgebra I
          rw [aeval_X]
          obtain ⟨o, i⟩ := v
          cases o with
          | none =>
            change Polynomial.C (Ideal.Quotient.mk P (u i)) * Polynomial.X ∈ reesAlgebra I
            rw [Polynomial.C_mul_X_eq_monomial]
            exact reesAlgebra.monomial_mem.mpr (by rw [pow_one]; exact Ideal.subset_span ⟨i, rfl⟩)
          | some k =>
            exact (reesAlgebra I).algebraMap_mem _
      · intro hx
        rw [← adjoin_monomial_eq_reesAlgebra] at hx
        induction hx using Algebra.adjoin_induction with
        | mem x hx =>
          obtain ⟨a, ha, rfl⟩ := hx
          induction ha using Submodule.span_induction with
          | mem a ha =>
            obtain ⟨j, rfl⟩ := ha
            refine ⟨X ⟨none, j⟩, ?_⟩
            change aeval (blowUpSubst P u) (X ⟨none, j⟩) = _
            rw [aeval_X]
            exact Polynomial.C_mul_X_eq_monomial
          | zero =>
            rw [map_zero]
            exact zero_mem _
          | add a b _ _ ha hb =>
            rw [map_add]
            exact add_mem ha hb
          | smul c a _ ha =>
            rw [LinearMap.map_smul, Polynomial.smul_eq_C_mul]
            exact mul_mem (hC c) ha
        | algebraMap a =>
          rw [Polynomial.algebraMap_eq]
          exact hC a
        | add x y _ _ hx hy => exact add_mem hx hy
        | mul x y _ _ hx hy => exact mul_mem hx hy
    have e : (MRing (extIdx ι J) O ⧸ blowUpOf P u) ≃+* reesAlgebra I :=
      (Ideal.quotientKerEquivRange φ).toRingEquiv.trans (RingEquiv.subringCongr hrange)
    rw [ringKrullDim_eq_of_ringEquiv e, h₁ (MRing ι O ⧸ P) I hI _ hP.dim, Fintype.card_option]
    rfl
end BlowUpModel
end GroundTheory.Heights₂.Heights.NumbersDVR
