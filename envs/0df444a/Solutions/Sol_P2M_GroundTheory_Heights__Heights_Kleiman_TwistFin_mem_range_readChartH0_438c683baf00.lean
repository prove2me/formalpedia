-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_mem_range_readChartH0_438c683baf00
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:26.583279+00:00
-- url     : https://prove2.me/submissions/64a1fd44-3537-4101-b3f2-f61b4841b030

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_Graded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_IsUnitPhiOfMemMonos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_injective_0670b52721eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_locL_locRes_269addb87c40
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_subsingleton_loc_6c2981eed93b

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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω) (S : Type u) [CommRing S] [Algebra S Ω]
variable (n0 : ℕ) (d0 : Fin n0 → ℤ) (g0 : Fin n0 → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution (i0 : Fin (N + 1)) (hi0 : x i0 ≠ 0) (t : Amb x η)
    (ht : ∀ (I : StdCell N) (hI : ∀ i ∈ I.1, x i ≠ 0), ∃ z ∈ degLoc (tgraded x η S n0 d0 g0) 0 I,
      locL x η S n0 d0 g0 I.1 hI z = t) :
    t ∈ LinearMap.range (readChartH0 x η S n0 d0 g0 i0 hi0) := by
  classical
  let v : ∀ I : StdCell N, LocMod (Sy S r) N (TMod x η S n0 d0 g0) I.1 := fun I =>
    if hI : ∀ i ∈ I.1, x i ≠ 0 then (ht I hI).choose else 0
  have hv : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1), locResS I J h (v I) = v J := by
    intro I J h
    by_cases hJ : ∀ i ∈ J.1, x i ≠ 0
    · have hI : ∀ i ∈ I.1, x i ≠ 0 := fun i hi => hJ i (h hi)
      apply locL_injective x η S n0 d0 g0 J.1 hJ
      change locL x η S n0 d0 g0 J.1 hJ (locRes h (v I)) = locL x η S n0 d0 g0 J.1 hJ (v J)
      rw [locL_locRes]
      simp only [v, dif_pos hI, dif_pos hJ]
      rw [(ht I hI).choose_spec.2, (ht J hJ).choose_spec.2]
    · push Not at hJ
      obtain ⟨i, hi, hx⟩ := hJ
      have := subsingleton_loc x η S n0 d0 g0 hi hx
      exact Subsingleton.elim _ _
  have hcoc : (fun I : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 => v I.1) ∈
      Cech.cocyDeg (locSys (Sy S r) N (TMod x η S n0 d0 g0)) (degLoc (tgraded x η S n0 d0 g0) 0)
        locResS 0 := by
    refine ⟨Cech.d_zero_of_compat v hv, fun I _ => ?_⟩
    by_cases hI : ∀ i ∈ I.1.1, x i ≠ 0
    · simp only [v, dif_pos hI]; exact (ht I.1 hI).choose_spec.1
    · simp only [v, dif_neg hI]; exact zero_mem _
  refine ⟨Submodule.Quotient.mk ⟨_, hcoc⟩, ?_⟩
  change evalIdx x η S n0 d0 g0 i0 hi0 ⟨_, hcoc⟩ = t
  change locL x η S n0 d0 g0 (idx0 i0).1.1 (mem_chartCell_ne_zero x hi0) (v (idx0 i0).1) = t
  simp only [v, dif_pos (mem_chartCell_ne_zero x hi0)]
  exact (ht _ (mem_chartCell_ne_zero x hi0)).choose_spec.2
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
