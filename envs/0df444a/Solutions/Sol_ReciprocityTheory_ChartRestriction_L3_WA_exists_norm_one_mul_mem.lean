-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L3.WA.exists_norm_one_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:19.350868+00:00
-- url     : https://prove2.me/submissions/f84eef50-582f-4a01-b544-2f9ebeec84a5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_ExistsNormOneOfPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K}
namespace ReciprocityTheory.ChartRestriction.L3.WA
theorem _root_.solution (hS : IsHermSemilocal S) {a : K} (ha : star a * a ∈ S) :
    ∃ b : K, star b * b = 1 ∧ a * b ∈ S := by
  let A : AddSubgroup K :=
    { carrier := {z | ∃ x ∈ S, ∃ y ∈ S, z = x + y * a}
      zero_mem' := ⟨0, S.zero_mem, 0, S.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
        exact ⟨x + x', S.add_mem hx hx', y + y', S.add_mem hy hy', by ring⟩
      neg_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact ⟨-x, S.neg_mem hx, -y, S.neg_mem hy, by ring⟩ }
  have h1A : (1 : K) ∈ A := ⟨1, S.one_mem, 0, S.zero_mem, by simp⟩
  have haA : a ∈ A := ⟨0, S.zero_mem, 1, S.one_mem, by simp⟩
  have hAS : ∀ s ∈ S, ∀ z ∈ A, s * z ∈ A := by
    rintro s hs _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨s * x, S.mul_mem hs hx, s * y, S.mul_mem hs hy, by ring⟩
  obtain ⟨t, htS, ht0, hta⟩ := hS.frac a
  have htA : ∀ z ∈ A, t * z ∈ S := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have : t * (x + y * a) = t * x + y * (t * a) := by ring
    rw [this]
    exact S.add_mem (S.mul_mem htS hx) (S.mul_mem hy hta)
  obtain ⟨δ, ⟨x, hx, y, hy, hδ⟩, hδ0, hdiv⟩ :=
    hS.principal A hAS ⟨1, h1A, one_ne_zero⟩ ⟨t, ht0, htA⟩
  have hsS : δ⁻¹ ∈ S := by simpa using hdiv 1 h1A
  have hrS : a * δ⁻¹ ∈ S := hdiv a haA
  generalize hsdef : δ⁻¹ = s at hsS hrS
  have hs0 : s ≠ 0 := by rw [← hsdef]; exact inv_ne_zero hδ0
  have h1 : x * s + y * (a * s) = 1 := by
    rw [← mul_assoc, ← add_mul, ← hδ, ← hsdef]
    exact mul_inv_cancel₀ hδ0
  have hss0 : star s ≠ 0 := star_ne_zero.mpr hs0
  refine ⟨s / star s, ?_, ?_⟩
  · rw [star_div₀, star_star]
    field_simp
  · have hq : (x * star (a * s) + y * (star a * a) * star s) * s = star (a * s) := by
      calc (x * star (a * s) + y * (star a * a) * star s) * s
          = star (a * s) * (x * s + y * (a * s)) := by rw [star_mul']; ring
        _ = star (a * s) := by rw [h1, mul_one]
    have : a * (s / star s) = star (x * star (a * s) + y * (star a * a) * star s) := by
      rw [← mul_div_assoc, div_eq_iff hss0, ← star_mul', hq, star_star]
    rw [this]
    exact hS.star_mem _ (S.add_mem (S.mul_mem hx (hS.star_mem _ hrS))
      (S.mul_mem (S.mul_mem hy ha) (hS.star_mem _ hsS)))
end ReciprocityTheory.ChartRestriction.L3.WA
