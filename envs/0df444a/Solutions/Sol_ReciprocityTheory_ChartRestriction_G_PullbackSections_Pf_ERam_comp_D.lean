-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.comp_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:39:10.445203+00:00
-- url     : https://prove2.me/submissions/5fa5e48b-a0e6-42ca-8f70-1b44609d1f00

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_IdemDataBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamData
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_trace_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_one_eq_sum_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution {k : Type} [Field k] [CharZero k] {Ty : Type} [Fintype Ty] (ψ : Ty → E →+* k)
    (htr : ∀ x : E, ∑ t, ψ t x = algebraMap ℚ k (Algebra.trace ℚ E x)) (N : ℕ) (hN : N ≠ 0)
    (hδ : ∀ i, IsIntegral ℤ (((N : 𝓞 E) : E) * omDF (E := E) i)) {d : ℕ} (M : 𝓞 E →+* Matrix (Fin d) (Fin d) k) :
    ∑ t, actD M (bD (N : 𝓞 E) hδ) (cD (ψ t) (N : 𝓞 E)) = 1 := by
  classical
  choose z hz using fun i : Fin (nI E) => trace_int (E := E) (omF i)
  have hN' : (N : k) ≠ 0 := Nat.cast_ne_zero.2 hN

  have hsum : ∑ i, (z i : 𝓞 E) * bD (N : 𝓞 E) hδ i = (N : 𝓞 E) := by
    apply RingOfIntegers.ext
    show algebraMap (𝓞 E) E (∑ i, (z i : 𝓞 E) * bD (N : 𝓞 E) hδ i) = algebraMap (𝓞 E) E (N : 𝓞 E)
    rw [map_sum, map_natCast]
    have h1 := one_eq_sum_trace (E := E)
    have e : ∀ i, algebraMap (𝓞 E) E ((z i : 𝓞 E) * bD (N : 𝓞 E) hδ i) =
        (N : E) * (Algebra.trace ℚ E (omF i : E) • omDF (E := E) i) := by
      intro i
      rw [map_mul, map_intCast, ← hz i, Rat.smul_def, Rat.cast_intCast]
      show (z i : E) * (((N : 𝓞 E) : E) * omDF (E := E) i) = _
      push_cast
      ring
    rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum, ← h1, mul_one]
  have hM : ∑ i, (z i : k) • M (bD (N : 𝓞 E) hδ i) = (N : k) • (1 : Matrix (Fin d) (Fin d) k) := by
    have := congrArg M hsum
    rw [map_sum, map_natCast] at this
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one, ← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
  have htr : ∀ i, ∑ t, ψ t (omF i : E) = (z i : k) := by
    intro i
    rw [htr, ← hz i]
    simp
  unfold actD cD
  rw [Finset.sum_comm]
  calc ∑ i, ∑ t, (ψ t (omF i : E) / ψ t ((N : 𝓞 E) : E)) • M (bD (N : 𝓞 E) hδ i)
      = ∑ i, ((N : k)⁻¹ * (z i : k)) • M (bD (N : 𝓞 E) hδ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp only [map_natCast, div_eq_mul_inv]
        rw [← Finset.sum_mul, htr, mul_comm]
    _ = (N : k)⁻¹ • ∑ i, (z i : k) • M (bD (N : 𝓞 E) hδ i) := by
        rw [Finset.smul_sum]
        simp [mul_smul]
    _ = 1 := by rw [hM, smul_smul, inv_mul_cancel₀ hN', one_smul]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
