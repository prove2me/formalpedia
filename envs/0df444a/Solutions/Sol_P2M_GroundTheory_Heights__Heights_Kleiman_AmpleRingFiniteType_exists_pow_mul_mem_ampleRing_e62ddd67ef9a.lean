-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_AmpleRingFiniteType_exists_pow_mul_mem_ampleRing_e62ddd67ef9a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:58:46.07649+00:00
-- url     : https://prove2.me/submissions/d5958937-09ae-427d-8721-ad09fb34f85f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AmpleRingFiniteTypeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleAffineGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PAmpleRingFiniteType
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_loc_85755dd0965c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_ampleChart_mono_6765e17e9241
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_AmpleAffineGen_chartRatio_mul_chartRatio_21e198efb704
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
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
theorem _root_.solution (H : LineBundle S x) {m : ℕ} {h : Ω}
    (hh : ∀ I, h ∈ (H.pow m).sub I) {c : Ω} (hc : c ∈ ampleRing H.toSubSystem m h) (J : Chart x)
    (hrat : ∀ I : Chart x, ∃ e : ℕ,
      c ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H.toSubSystem m h I)
    {y : Ω} (hy : y ∈ chartRing S x J) : ∃ M : ℕ, c ^ M * y ∈ ampleRing H.toSubSystem m h := by
  classical
  have hI : ∀ I : Chart x, ∃ M, c ^ M * y ∈ ampleChart H.toSubSystem m h I := by
    intro I
    have h1 : y ∈ ampleChart H.toSubSystem m h (AmpleAffineGen.unionChart I J) :=
      AmpleAffineGen.ampleChart_mono (AmpleAffineGen.subset_unionChart_right I J)
        (AmpleAffineGen.mem_ampleSubalg_of_mem_chartRing (hh J) hy)
    obtain ⟨D, hD⟩ := AmpleAffineGen.ampleChart_loc H I J h1
    obtain ⟨e, he⟩ := hrat I
    refine ⟨e * D, ?_⟩
    have := mul_mem
      (pow_mem (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from he) D)
      (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from hD)
    rwa [show c ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) =
        c ^ e * AmpleAffineGen.chartRatio J I from rfl,
      AmpleAffineGen.pow_mul_cancel (AmpleAffineGen.chartRatio_mul_chartRatio I J)] at this
  choose M hM using hI
  refine ⟨Finset.univ.sup M, Set.mem_iInter.mpr fun I => ?_⟩
  have hle : M I ≤ Finset.univ.sup M := Finset.le_sup (Finset.mem_univ I)
  have e1 : c ^ Finset.univ.sup M * y = c ^ (Finset.univ.sup M - M I) * (c ^ M I * y) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  rw [e1]
  exact mul_mem
    (pow_mem (show c ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from
      Set.mem_iInter.mp hc I) _)
    (show _ ∈ AmpleAffineGen.ampleSubalg H.toSubSystem m h I (hh I) from hM I)
end GroundTheory.Heights₂.Heights.Kleiman.AmpleRingFiniteType
