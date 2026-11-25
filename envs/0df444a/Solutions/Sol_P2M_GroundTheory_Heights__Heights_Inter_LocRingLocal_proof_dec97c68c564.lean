-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_LocRingLocal_proof_dec97c68c564
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:31.010553+00:00
-- url     : https://prove2.me/submissions/578f3445-b96d-4732-aa22-d8252d7b0b52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingLocal_isMultiHomog_add_08ecdd1ec297
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_mul_92fa4aba8533


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace LocRingLocal
theorem _root_.solution (hF : LocRingFrac.Statement) : LocRingLocal.Statement := by
  intro K _ ι _ P W hP hW hPW
  have := hP
  set F := FractionRing (MRing ι ⧸ P)
  have hnzd : ∀ w : MRing ι, w ∉ W → Ideal.Quotient.mk P w ∈ nonZeroDivisors (MRing ι ⧸ P) := fun w hw =>
    mem_nonZeroDivisors_of_ne_zero fun h => hw (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hne : ∀ w : MRing ι, w ∉ W → algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P w) ≠ 0 := fun w hw =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hnzd w hw)
  have key : ∀ (y : locRing P W) (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a → IsMultiHomog v a → v ∉ W →
      (y : F) * algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P u) →
      (IsUnit y ↔ u ∉ W) := by
    intro y u v a hu hv hvW hy
    constructor
    · rintro hunit huW
      obtain ⟨y', hyy'⟩ := hunit.exists_right_inv
      obtain ⟨u', v', a', -, -, hv'W, hy'⟩ := hF K ι P W hP hW hPW y' y'.2
      have h1 : ((y * y' : locRing P W) : F) = 1 := by rw [hyy']; rfl
      have h2 : algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (v * v')) =
          algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (u * u')) := by
        rw [map_mul, map_mul, map_mul, map_mul, ← hy, ← hy']
        rw [Subring.coe_mul] at h1
        linear_combination (-(algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v) *
          algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P v'))) * h1
      have h3 := Ideal.Quotient.eq.mp (IsFractionRing.injective (MRing ι ⧸ P) F h2)
      have h4 : v * v' ∈ W := by
        have := W.add_mem (hPW h3) (W.mul_mem_right u' huW)
        simpa using this
      rcases hW.mem_or_mem h4 with h | h
      · exact hvW h
      · exact hv'W h
    · intro huW
      have hz : IsLocalization.mk' F (Ideal.Quotient.mk P v) (⟨_, hnzd u huW⟩ : nonZeroDivisors (MRing ι ⧸ P)) ∈
          locRing P W := Subring.subset_closure ⟨v, u, a, hnzd u huW, huW, hv, hu, rfl⟩
      refine IsUnit.of_mul_eq_one (a := y) ⟨_, hz⟩ (Subtype.ext ?_)
      have hspec := IsLocalization.mk'_spec F (Ideal.Quotient.mk P v)
        (⟨_, hnzd u huW⟩ : nonZeroDivisors (MRing ι ⧸ P))
      simp only [Subring.coe_mul, Subring.coe_one]
      apply mul_right_cancel₀ (hne u huW)
      rw [one_mul, mul_assoc, hspec, hy]
  refine ⟨?_, key⟩
  refine IsLocalRing.of_nonunits_add fun x y hx hy => ?_
  obtain ⟨u, v, a, hu, hv, hvW, hxe⟩ := hF K ι P W hP hW hPW x x.2
  obtain ⟨u', v', a', hu', hv', hv'W, hye⟩ := hF K ι P W hP hW hPW y y.2
  have huW : u ∈ W := by
    by_contra h
    exact hx ((key x u v a hu hv hvW hxe).mpr h)
  have hu'W : u' ∈ W := by
    by_contra h
    exact hy ((key y u' v' a' hu' hv' hv'W hye).mpr h)
  have hvv' : v * v' ∉ W := fun h => (hW.mem_or_mem h).elim hvW hv'W
  have hsum : ((x + y : locRing P W) : F) * algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (v * v')) =
      algebraMap (MRing ι ⧸ P) F (Ideal.Quotient.mk P (u * v' + u' * v)) := by
    simp only [Subring.coe_add, map_mul, map_add]
    rw [← hxe, ← hye]
    ring
  have hnum : IsMultiHomog (u * v' + u' * v) (a + a') :=
    LocRingLocal.isMultiHomog_add (AvoidRing.isMultiHomog_mul hu hv')
      (add_comm a' a ▸ AvoidRing.isMultiHomog_mul hu' hv)
  intro hunit
  exact (key (x + y) _ _ (a + a') hnum (AvoidRing.isMultiHomog_mul hv hv') hvv' hsum).mp hunit
    (W.add_mem (W.mul_mem_right v' huW) (W.mul_mem_right v hu'W))
end LocRingLocal
end GroundTheory.Heights₂.Heights.Inter
