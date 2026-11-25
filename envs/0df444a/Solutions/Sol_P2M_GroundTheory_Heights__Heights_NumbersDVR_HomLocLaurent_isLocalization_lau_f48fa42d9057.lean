-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_isLocalization_lau_f48fa42d9057
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:30.300073+00:00
-- url     : https://prove2.me/submissions/98f63674-f106-42f6-95af-a9ebe1883632

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_exists_frac_9c6adeb809ef
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_tpow_add_bb09fa77dd00
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_psiQ_mk_c419026b54a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_psiQ_injective_00f1ce3be874

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
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime] (T : ∀ k, ι k)
  (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
theorem _root_.solution (hPh : IsMultiHomogIdeal P) :
    letI := (psiQ T hPW hT hPh).toAlgebra
    IsLocalization (homSub (K := K) P W) (Lau P W) := by
  let := (psiQ T hPW hT hPh).toAlgebra
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero fun h => hg (hPW h)
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, b, f, hf, hfW, rfl⟩
    change IsUnit (psiQ T hPW hT hPh (Ideal.Quotient.mk P f))
    rw [psiQ_mk, psi_homog T hPW hT hf]
    refine IsUnit.of_mul_eq_one (AddMonoidAlgebra.single (-nz b)
      ⟨fr P (tpow T b) / fr P f, frac_mem (isMultiHomog_tpow T b) hf hfW⟩) ?_
    rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, AddMonoidAlgebra.one_def]
    congr 1
    apply Subtype.ext
    have h1 := hne hfW
    have h2 := hne (tpow_not_mem T hT b)
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
    field_simp
  · intro p
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => exact ⟨⟨0, 1⟩, by simp⟩
    | add p q hp hq =>
      obtain ⟨⟨r, h⟩, hr⟩ := hp
      obtain ⟨⟨r', h'⟩, hr'⟩ := hq
      refine ⟨⟨r * h' + r' * h, h * h'⟩, ?_⟩
      simp only [Submonoid.coe_mul, map_mul, map_add] at hr hr' ⊢
      rw [← hr, ← hr']
      ring
    | single d a =>
      obtain ⟨b, f, g, hf, hg, hgW, ha⟩ := exists_frac hPW a.2
      set dp : K → ℕ := fun k => (d k).toNat
      set dm : K → ℕ := fun k => (-d k).toNat
      refine ⟨⟨Ideal.Quotient.mk P (f * tpow T dp), ⟨_, b + dm, g * tpow T dm,
        isMultiHomog_mul hg (isMultiHomog_tpow T dm),
        fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hgW (tpow_not_mem T hT dm), rfl⟩⟩, ?_⟩
      change AddMonoidAlgebra.single d a * psiQ T hPW hT hPh (Ideal.Quotient.mk P (g * tpow T dm)) =
        psiQ T hPW hT hPh (Ideal.Quotient.mk P (f * tpow T dp))
      rw [psiQ_mk, psiQ_mk, psi_homog T hPW hT (isMultiHomog_mul hg (isMultiHomog_tpow T dm)),
        psi_homog T hPW hT (isMultiHomog_mul hf (isMultiHomog_tpow T dp)),
        AddMonoidAlgebra.single_mul_single]
      congr 1
      · ext k
        simp only [Pi.add_apply, map_add, dp, dm]
        simp only [AddMonoidHom.compLeft_apply, Function.comp_apply, Nat.coe_castAddMonoidHom]
        omega
      · apply Subtype.ext
        have h1 := hne hgW
        have h2 := hne (tpow_not_mem T hT b)
        have h3 := hne (tpow_not_mem T hT dm)
        have h4 := hne (tpow_not_mem T hT dp)
        simp only [MulMemClass.coe_mul, ha, tpow_add, map_mul]
        field_simp
  · intro x y h
    exact ⟨1, by simpa using psiQ_injective T hPW hT hPh h⟩
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
