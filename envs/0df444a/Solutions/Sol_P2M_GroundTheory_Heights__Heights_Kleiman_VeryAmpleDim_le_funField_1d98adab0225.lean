-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_le_funField_1d98adab0225
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:21:11.313797+00:00
-- url     : https://prove2.me/submissions/84ded863-fed3-45b1-9aa7-fa3438fe7c25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_mem_sub_of_mem_secs_9323478d1234
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDim_ampleBase_le_funField_3c18574d4cd9
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_pow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mul_chartRatio_21e198efb704
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_exists_pow_mul_mem_866e61ad51fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_mem_ampleSubalg_of_mem_chartRing_9358b4af0d94
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_pow_mul_cancel_b1d87a2248dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_subset_unionChart_right_b54617500f30


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial AmpleAffineGen
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim
theorem _root_.solution (Nb : LineBundle k x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hv : IsVeryAmpleBy Nb.toSubSystem h) {j₀ : Fin (r + 1)} (hj₀ : h j₀ ≠ 0) :
    funField (k := k) x ≤ funField (k := k) h := by
  classical
  obtain ⟨n, a, b, J, -, hb, hsum, hloc⟩ := hv.affine j₀ hj₀
  obtain ⟨t, ht⟩ : ∃ t, b t ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at hsum
  have hh : ∀ I : Chart x, h j₀ ∈ (Nb.toSubSystem.pow 1).sub I := fun I =>
    Submodule.subset_span ⟨h j₀, mem_sub_of_mem_secs (hv.mem_secs j₀) I, 1,
      one_mem_twistMod_zero (S := k) I, by rw [smul_eq_mul, mul_one]⟩
  have hF : ∀ z ∈ ampleRing Nb.toSubSystem 1 (h j₀), z ∈ funField (k := k) h := fun z hz =>
    ampleBase_le_funField h hj₀ (hv.closed j₀ hj₀ hz)
  obtain ⟨c, hc⟩ := (J t).2.1
  have hxc : x c ≠ 0 := (mem_support x).mp ((J t).2.2 hc)
  have key : ∀ l, x l / x c ∈ funField (k := k) h := by
    intro l
    have hA : x l / x c ∈ chartRing k x (J t) :=
      ⟨X l, X c, 1, X_mem_monos hc, isHomogeneous_X k l, isHomogeneous_X k c, by simp⟩
    have hE : ∀ I : Chart x, ∃ E : ℕ,
        b t ^ E * (x l / x c) ∈ ampleChart Nb.toSubSystem 1 (h j₀) I := by
      intro I
      obtain ⟨e, he⟩ := hloc t I
      obtain ⟨D, hD⟩ := exists_pow_mul_mem I (J t)
        (chartRing_mono (subset_unionChart_right I (J t)) hA)
      refine ⟨e * D, ?_⟩
      rw [← pow_mul_cancel (u := b t) (y := x l / x c) (chartRatio_mul_chartRatio I (J t)) e D]
      exact (ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem
        (pow_mem (show _ ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from he) D)
        (mem_ampleSubalg_of_mem_chartRing (hh I) hD)
    choose E hE using hE
    have hmem : b t ^ (∑ I, E I) * (x l / x c) ∈ ampleRing Nb.toSubSystem 1 (h j₀) := by
      refine Set.mem_iInter.mpr fun I => ?_
      have hle : E I ≤ ∑ I, E I := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ I)
      have e : b t ^ (∑ I, E I) * (x l / x c) = b t ^ ((∑ I, E I) - E I) * (b t ^ E I * (x l / x c)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [e]
      exact (ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I)).mul_mem
        (pow_mem (show b t ∈ ampleSubalg Nb.toSubSystem 1 (h j₀) I (hh I) from Set.mem_iInter.mp (hb t) I) _)
        (hE I)
    rw [← mul_div_cancel_left₀ (x l / x c) (pow_ne_zero (∑ I, E I) ht)]
    exact div_mem (hF _ hmem) (pow_mem (hF _ (hb t)) _)
  show IntermediateField.adjoin k _ ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨i, l, hi, rfl⟩
  have e : x l / x i = (x l / x c) / (x i / x c) := by field_simp
  rw [e]
  exact div_mem (key l) (key i)
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleDim
