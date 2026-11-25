-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_idealMod_le_e980b8caa17f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:22:43.210667+00:00
-- url     : https://prove2.me/submissions/0404a268-ffc2-4cd8-888d-8116af111fc2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltKernelSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropFiltKernel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Filt_Kernel_aeval_div_mem_chartRing_ffb6a96329ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_mem_primeOf_077b7ab281b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Kernel
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Kernel
theorem _root_.solution (j : Fin (N + 1)) (b : ℕ) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    idealMod (primeOf (S := S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b)) I ≤
      Submodule.span (chartRing S x I) {x j ^ b / x i ^ b} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set M := Submodule.span (chartRing S x I) {x j ^ b / x i ^ b}
  let K : Ideal (Poly S N) :=
    { carrier := {f | aeval (fun l => x l / x i) f ∈ M}
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq, map_add] at *; exact M.add_mem hf hg
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact M.zero_mem
      smul_mem' := fun r f hf => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
        exact M.smul_mem ⟨_, aeval_div_mem_chartRing I hi r⟩ hf }
  have hK : primeOf (S := S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b) ≤ K := by
    refine sup_le (fun f hf => ?_) (Ideal.span_le.mpr ?_)
    · change aeval (fun l => x l / x i) f ∈ M
      rw [← sum_homogeneousComponent f, map_sum]
      convert M.zero_mem
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [aeval_div_of_isHomogeneous (homogeneousComponent_isHomogeneous d f) i,
        (mem_primeOf_of_isHomogeneous x (homogeneousComponent_isHomogeneous d f)).mp
          (homogeneousComponent_mem_primeOf x hf d), zero_div]
    · rintro g ⟨c, hg, hz⟩
      have hδ : x i ^ b ∈ (twistSys S x (b : ℤ)).sub I := by
        change x i ^ b ∈ twistMod S x (b : ℤ) I
        rw [twistMod_eq_span _ I hi, zpow_natCast]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨o, ho, he⟩ := hz I _ hδ
      rw [twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton] at ho
      obtain ⟨a, rfl⟩ := ho
      change aeval (fun l => x l / x i) g ∈ M
      rw [aeval_div_of_isHomogeneous hg i, Submodule.mem_span_singleton]
      refine ⟨a, ?_⟩
      rw [chartRing_smul_def] at he ⊢
      field_simp
      linear_combination -he
  rw [idealMod, Submodule.span_le]
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hm : aeval (fun l => x l / x i) f ∈ M := hK hf
  rw [aeval_div_of_isHomogeneous hfe i] at hm
  have h := M.smul_mem (⟨x i ^ e / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow _ _, hse,
    by simp⟩ : chartRing S x I) hm
  rw [chartRing_smul_def] at h
  rw [SetLike.mem_coe]
  convert h using 1
  change _ = x i ^ e / aeval x s * (aeval x f / x i ^ e)
  have : x i ^ e ≠ 0 := pow_ne_zero _ hxi
  field_simp
end GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Filt.Kernel
