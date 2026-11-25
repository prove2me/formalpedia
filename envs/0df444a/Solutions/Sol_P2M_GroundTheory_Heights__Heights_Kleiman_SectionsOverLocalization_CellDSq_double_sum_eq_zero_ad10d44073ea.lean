-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_double_sum_eq_zero_ad10d44073ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:14:28.220021+00:00
-- url     : https://prove2.me/submissions/3e439b34-8f67-4c6d-bb61-b2ee429ad062

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sigma_rem_783ced986bac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_rem_comm_6b3e204c1d90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_4c00e12af7e2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
theorem _root_.solution {Ω : Type} [AddCommGroup Ω] (I : ∀ k, Finset (ι k))
    (g : (∀ k, Finset (ι k)) → Ω) (hg : ∀ J, g J ≠ 0 → ∀ l, (J l).Nonempty) :
    ∑ k, ∑ i ∈ I k, faceSign I k i • ∑ k', ∑ i' ∈ rem I ⟨k, i⟩ k',
      faceSign (rem I ⟨k, i⟩) k' i' • g (rem (rem I ⟨k, i⟩) ⟨k', i'⟩) = 0 := by
  let f : (Σ _ : (Σ k, ι k), Σ k, ι k) → Ω := fun x =>
    (faceSign I x.1.1 x.1.2 * faceSign (rem I x.1) x.2.1 x.2.2) • g (rem (rem I x.1) x.2)
  have step : ∀ k, ∀ i ∈ I k, faceSign I k i • ∑ k', ∑ i' ∈ rem I ⟨k, i⟩ k',
      faceSign (rem I ⟨k, i⟩) k' i' • g (rem (rem I ⟨k, i⟩) ⟨k', i'⟩) =
        ∑ q ∈ (Finset.univ.sigma I).erase ⟨k, i⟩, f ⟨⟨k, i⟩, q⟩ := by
    intro k i _
    rw [← sigma_rem, Finset.sum_sigma, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [smul_smul]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl (step k),
    ← Finset.sum_sigma Finset.univ I (fun p => ∑ q ∈ (Finset.univ.sigma I).erase p, f ⟨p, q⟩),
    Finset.sum_sigma' (Finset.univ.sigma I) (fun p => (Finset.univ.sigma I).erase p) (fun p q => f ⟨p, q⟩)]
  refine Finset.sum_involution (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ hx
    obtain ⟨hp, hq⟩ := Finset.mem_sigma.1 hx
    obtain ⟨hne, hq⟩ := Finset.mem_erase.1 hq
    simp only [f]
    rw [rem_rem_comm I q p]
    by_cases h0 : g (rem (rem I p) q) = 0
    · rw [h0, smul_zero, smul_zero, add_zero]
    · rw [sign_swap (Finset.mem_sigma.1 hp).2 (Finset.mem_sigma.1 hq).2 hne (hg _ h0), neg_smul]
      exact neg_add_cancel _
  · rintro ⟨p, q⟩ hx - h
    obtain ⟨hne, -⟩ := Finset.mem_erase.1 (Finset.mem_sigma.1 hx).2
    exact hne (congrArg Sigma.fst h)
  · rintro ⟨p, q⟩ hx
    obtain ⟨hp, hq⟩ := Finset.mem_sigma.1 hx
    obtain ⟨hne, hq⟩ := Finset.mem_erase.1 hq
    exact Finset.mem_sigma.2 ⟨hq, Finset.mem_erase.2 ⟨hne.symm, hp⟩⟩
  · rintro ⟨p, q⟩ -
    rfl
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
