-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.trace_gram_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:31:27.28475+00:00
-- url     : https://prove2.me/submissions/679a4a11-e28a-4701-9b21-cd4fce9b0282

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscBDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TraceGramDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {F : Type} [Field F] [CharZero F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {E : κ → Type} [∀ c, Field (E c)] [∀ c, Algebra F (E c)] [∀ c, FiniteDimensional F (E c)]
    {n : ℕ} (b : Fin n → ∀ c, E c)
    (hind : ∀ v : Fin n → F, (∀ c, ∑ l, v l • b l c = 0) → v = 0)
    (hspan : ∀ y : ∀ c, E c, ∃ μ : Fin n → F, ∀ c, y c = ∑ k, μ k • b k c) :
    (Matrix.of fun k l : Fin n => ∑ c, Algebra.trace F (E c) (b k c * b l c)).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set y : ∀ c, E c := fun c => ∑ l, v l • b l c with hy
  have hk : ∀ k, ∑ c, Algebra.trace F (E c) (b k c * y c) = 0 := by
    intro k
    have h1 := congrFun hv k
    have h2 : ∑ c, Algebra.trace F (E c) (b k c * y c) =
        ∑ l, (∑ c, Algebra.trace F (E c) (b k c * b l c)) * v l := by
      simp only [hy, Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [h2]
    simpa [Matrix.mulVec, dotProduct] using h1
  have hall : ∀ x : ∀ c, E c, ∑ c, Algebra.trace F (E c) (x c * y c) = 0 := by
    intro x
    obtain ⟨μ, hμ⟩ := hspan x
    have hx : ∀ c, x c * y c = ∑ k, μ k • (b k c * y c) := by
      intro c
      rw [hμ c, Finset.sum_mul]
      simp [smul_mul_assoc]
    simp only [hx, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, hk]
  have hy0 : y = 0 := by
    by_contra hne
    obtain ⟨c0, hc0⟩ := Function.ne_iff.mp hne
    have hc0' : y c0 ≠ 0 := by simpa using hc0
    have ht := hall (Pi.single c0 (y c0)⁻¹)
    rw [Finset.sum_eq_single c0] at ht
    · have h1 : (1 : E c0) = algebraMap F (E c0) 1 := (map_one _).symm
      rw [Pi.single_eq_same, inv_mul_cancel₀ hc0', h1, Algebra.trace_algebraMap, nsmul_eq_mul,
        mul_one] at ht
      exact (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := F) (M := E c0)).ne') ht
    · intro c _ hc
      simp [Pi.single_apply, hc]
    · intro h
      exact absurd (Finset.mem_univ c0) h
  exact hv0 (hind v fun c => by simpa [hy] using congrFun hy0 c)
end ReciprocityTheory.ChartRestriction.G.T0
