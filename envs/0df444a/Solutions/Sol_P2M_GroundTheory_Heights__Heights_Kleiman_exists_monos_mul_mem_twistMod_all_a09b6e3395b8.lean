-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_mul_mem_twistMod_all_a09b6e3395b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:03.491194+00:00
-- url     : https://prove2.me/submissions/e1e9600f-d2af-427b-9fef-8487bf1d7c50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutDimLowerSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PZeroIdealChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutDimLower
import Theorems.Thm_GroundTheory_Arith_Toric_IsRationalPolyhedral_fg
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mono
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mem_twistMod_11b60f1db303
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_mul_mem_twistMod_65efbe4a3982
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mul_mem_chartRing_union_c0103708ece5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_mem_2cda6caafd1a


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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (L : LineBundle S x) (I : Chart x) (y : Ω)
    (hy : ∀ δ ∈ L.sub I, y * δ ∈ chartRing S x I) :
    ∃ U ∈ monos (S := S) I.1, ∃ dU : ℕ, U.IsHomogeneous dU ∧
      ∀ (K : Chart x), ∀ δ ∈ L.sub K, aeval x U * (y * δ) ∈ twistMod S x (dU : ℤ) K := by
  classical
  have hyU := mul_mem_chartRing_union L.toSubFamily I
  choose G hG using fun K => L.fg K
  have hgen : ∀ p : Σ K : Chart x, (G K : Set Ω),
      y * (p.2 : Ω) ∈ chartRing S x (chartUnion I p.1) := fun p =>
    hyU p.1 y hy _ (L.mono p.1 (chartUnion I p.1)
      (show p.1.1 ⊆ (chartUnion I p.1).1 from Finset.subset_union_right) _
      (by rw [← hG p.1]; exact Submodule.subset_span p.2.2))
  choose u hu d hd hud using fun p : (Σ K : Chart x, (G K : Set Ω)) =>
    exists_monos_mul_mem_twistMod (S := S) I p.1 (y * (p.2 : Ω)) (hgen p)
  obtain ⟨U, hUdef⟩ : ∃ U : Poly S N, U = ∏ p, u p := ⟨_, rfl⟩
  obtain ⟨dU, hdUdef⟩ : ∃ dU : ℕ, dU = ∑ p, d p := ⟨_, rfl⟩
  have hUm : U ∈ monos (S := S) I.1 := hUdef ▸ prod_mem fun p _ => hu p
  have hUh : U.IsHomogeneous dU := hUdef ▸ hdUdef ▸ IsHomogeneous.prod _ _ _ fun p _ => hd p
  have key : ∀ p : Σ K : Chart x, (G K : Set Ω),
      aeval x U * (y * (p.2 : Ω)) ∈ twistMod S x (dU : ℤ) p.1 := by
    intro p
    have hsplit : U = u p * ∏ q ∈ Finset.univ.erase p, u q := by
      rw [hUdef, Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
    have hdsplit : dU = d p + ∑ q ∈ Finset.univ.erase p, d q := by
      rw [hdUdef, Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have h2 := aeval_mem_twistMod (x := x)
      (IsHomogeneous.prod _ _ _ fun q _ => hd q : (∏ q ∈ Finset.univ.erase p, u q).IsHomogeneous _) p.1
    have h3 := twistMod_mul_mem (hud p) h2
    rw [hsplit, hdsplit, map_mul, Nat.cast_add]
    convert h3 using 1
    ring
  refine ⟨U, hUm, dU, hUh, fun K δ hδ => ?_⟩
  rw [← hG K] at hδ
  induction hδ using Submodule.span_induction with
  | mem δ hδ => exact key ⟨K, ⟨δ, hδ⟩⟩
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, mul_add]; exact add_mem ha hb
  | smul a b _ hb =>
    rw [chartRing_smul_def, show aeval x U * (y * ((a : Ω) * b)) = (a : Ω) * (aeval x U * (y * b)) by ring,
      ← chartRing_smul_def]
    exact Submodule.smul_mem _ a hb
end GroundTheory.Heights₂.Heights.Kleiman
