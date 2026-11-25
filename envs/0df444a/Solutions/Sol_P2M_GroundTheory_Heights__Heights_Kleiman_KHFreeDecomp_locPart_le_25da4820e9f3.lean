-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_locPart_le_25da4820e9f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:44:53.132276+00:00
-- url     : https://prove2.me/submissions/bb3ddb81-5114-4a55-b625-cf36e7e85a82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHFreeDecompSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHFreeDecomp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_cellMon_monomial_80cf923a0fe8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_overDen_apply_c50c6731e4a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_quot_mk_smul_5069f6e57820
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHFreeDecomp_mk_monomial_eq_1fcfa5cefa4b

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
theorem _root_.solution (I : ∀ k, Finset (ι k)) (c d : K → ℤ) :
    KH.locPart ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) (KH.cellMon S I) c ≤
      Submodule.span S (monoFrac S I '' {a | blockSum a = c + d}) := by
  classical
  rcases subsingleton_or_nontrivial S with hS | hS
  · intro x _
    have hx : x = 0 := by rw [← one_smul S x, Subsingleton.elim (1 : S) 0, zero_smul]
    rw [hx]
    exact zero_mem _
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, ⟨t, ht⟩, b, htb, hm, rfl⟩
  obtain ⟨u, rfl, huI⟩ := cellMon_monomial ht
  have hub : ∀ k, ∑ i, u ⟨k, i⟩ = b k := by
    intro k
    refine htb u ?_ k
    rw [support_monomial, if_neg one_ne_zero]
    exact Finset.mem_singleton_self u
  have hle : KH.quotPart S (⊥ : Ideal (MRingOver S ι)) ((c + fun k => (b k : ℤ)) + d) ≤
      (Submodule.span S (monoFrac S I '' {a | blockSum a = c + d})).comap
        (overDen (KH.cellMon S I) ⟨monomial u 1, ht⟩) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, ⟨hpos, hp⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have hsum : p = ∑ v ∈ p.support, coeff v p • (monomial v 1 : MRingOver S ι) := by
      conv_lhs => rw [p.as_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hsum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    rw [quot_mk_smul, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun q => (v q : ℤ) - u q, ?_, ?_⟩)
    · have hv' := hp v hv
      show blockSum _ = c + d
      funext k
      simp only [blockSum, Finset.sum_sub_distrib]
      have h1 : ∑ i, ((v ⟨k, i⟩ : ℕ) : ℤ) = ((((c + fun k => (b k : ℤ)) + d) k).toNat : ℤ) := by
        exact_mod_cast hv' k
      have h2 : ∑ i, ((u ⟨k, i⟩ : ℕ) : ℤ) = b k := by exact_mod_cast hub k
      have h3 := hpos k
      simp only [Pi.add_apply] at h1 h3 ⊢
      omega
    · rw [overDen_apply, mk_monomial_eq I u v huI ht]
  exact hle hm
end GroundTheory.Heights₂.Heights.Kleiman.KHFreeDecomp
