-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.HCFR.valued_eq_exp_of_isUniformiserAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:54.609358+00:00
-- url     : https://prove2.me/submissions/dc7de502-ce80-4192-b484-e31fddacc065

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HilbertClassFieldA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_HCFFromRecipA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors
namespace ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
private theorem isUnit_of_valued_eq_one (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletionIntegers K)
    (hy : Valued.v (y : v.adicCompletion K) = 1) : IsUnit y := by
  have hy0 : (y : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact zero_ne_one hy
  have hinv : (y : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hy, inv_one]
  have h1 : y * ⟨_, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hy0)
  exact ⟨⟨y, ⟨_, hinv⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
private theorem valued_eq_one_of_isUnit' (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletionIntegers K)
    (hy : IsUnit y) : Valued.v (y : v.adicCompletion K) = 1 := by
  obtain ⟨u, rfl⟩ := hy
  have h1 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (u : v.adicCompletionIntegers K).2
  have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2
  have h3 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
      Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
    rw [← map_mul]
    exact (congrArg (fun t : v.adicCompletionIntegers K => Valued.v (t : v.adicCompletion K)) u.mul_inv).trans (map_one _)
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ _ := mul_le_of_le_one_right' h2
end ReciprocityTheory.Neutral.Bridge.HCFR
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge ReciprocityTheory.Neutral.Bridge.HCFR
variable (K : Type) [Field K] [NumberField K]
namespace ReciprocityTheory.Neutral.Bridge.HCFR
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K)
    (hx : IsUniformiserAt K v x) : Valued.v x = WithZero.exp (-1 : ℤ) := by
  obtain ⟨hxO, hirr⟩ := hx
  have hle : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp hxO
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hirr.ne_zero (Subtype.ext rfl)
  have hne1 : Valued.v x ≠ 1 := fun h => hirr.not_isUnit (isUnit_of_valued_eq_one K v _ h)
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer v
  have hy' := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) v π
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hπ] at hy'
  obtain ⟨y, hy⟩ : ∃ y : v.adicCompletion K, Valued.v y = WithZero.exp (-1 : ℤ) := ⟨_, hy'⟩
  have hw0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have hlog : WithZero.log (Valued.v x) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hw0, WithZero.exp_zero]
    exact hle
  have hlog1 : WithZero.log (Valued.v x) ≠ 0 := by
    intro h
    apply hne1
    rw [← WithZero.exp_log hw0, h, WithZero.exp_zero]
  rw [← WithZero.exp_log hw0]
  congr 1
  by_contra hne
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  have hyO : y ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hy, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hzO : x / y ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hy, ← WithZero.exp_log hw0, ← WithZero.exp_sub,
      ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hsplit : (⟨x, hxO⟩ : v.adicCompletionIntegers K) = ⟨y, hyO⟩ * ⟨x / y, hzO⟩ := by
    apply Subtype.ext
    show x = y * (x / y)
    field_simp
  rcases hirr.isUnit_or_isUnit hsplit with h | h
  · have h1 := valued_eq_one_of_isUnit' K v _ h
    change Valued.v y = 1 at h1
    rw [hy] at h1
    have h2 := congrArg WithZero.log h1
    simp at h2
  · have h1 := valued_eq_one_of_isUnit' K v _ h
    change Valued.v (x / y) = 1 at h1
    rw [map_div₀, hy, ← WithZero.exp_log hw0, ← WithZero.exp_sub] at h1
    have h2 := congrArg WithZero.log h1
    simp only [WithZero.log_exp, WithZero.log_one] at h2
    omega
end ReciprocityTheory.Neutral.Bridge.HCFR
