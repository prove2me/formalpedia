-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.rel_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:40:39.504936+00:00
-- url     : https://prove2.me/submissions/a3134f17-96f1-41ec-9050-43820c77e916

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JInjCore
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_mem_bot_of_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution {K F C Pt : Type} [Field K] [Field F] [Algebra K F] [IsGalois K F]
    [AddCommGroup C] [Module K C] (v : C →ₗ[K] (Pt → F)) (act : (F ≃ₐ[K] F) → Pt → Pt)
    (hbij : ∀ g, Function.Bijective (act g)) (heq : ∀ g f y, v f (act g y) = g (v f y))
    (hinj : Function.Injective v) {n : ℕ} (b : Fin n → C) (hb : LinearIndependent K b) :
    ∀ (s : Finset (Fin n)) (a : Fin n → F), (∀ y, ∑ i ∈ s, a i * v (b i) y = 0) → ∀ i ∈ s, a i = 0 := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro a ha i0 hi0
  by_contra hne
  obtain ⟨a', ha'⟩ : ∃ a' : Fin n → F, ∀ i, a' i = (a i0)⁻¹ * a i := ⟨_, fun _ => rfl⟩
  have ha'rel : ∀ y, ∑ i ∈ s, a' i * v (b i) y = 0 := by
    intro y
    simp only [ha', mul_assoc]
    rw [← Finset.mul_sum, ha y, mul_zero]
  have ha'1 : a' i0 = 1 := by rw [ha']; exact inv_mul_cancel₀ hne
  have hfix : ∀ i ∈ s, ∀ g : F ≃ₐ[K] F, g (a' i) = a' i := by
    intro i hi g
    have hrel_g : ∀ y, ∑ j ∈ s, g (a' j) * v (b j) y = 0 := by
      intro y
      obtain ⟨x, rfl⟩ := (hbij g).2 y
      have h1 := congrArg g (ha'rel x)
      rw [map_sum, map_zero] at h1
      simp only [map_mul, ← heq] at h1
      exact h1
    have hdiff : ∀ y, ∑ j ∈ s.erase i0, (g (a' j) - a' j) * v (b j) y = 0 := by
      intro y
      rw [Finset.sum_erase]
      · simp only [sub_mul, Finset.sum_sub_distrib, hrel_g y, ha'rel y, sub_zero]
      · rw [ha'1, map_one, sub_self, zero_mul]
    by_cases hii : i = i0
    · rw [hii, ha'1, map_one]
    · have h2 := ih (s.erase i0) (Finset.erase_ssubset hi0) (fun j => g (a' j) - a' j) hdiff i
        (Finset.mem_erase.mpr ⟨hii, hi⟩)
      exact sub_eq_zero.mp h2
  have hK : ∀ i ∈ s, ∃ c : K, algebraMap K F c = a' i := fun i hi =>
    IntermediateField.mem_bot.mp (mem_bot_of_fixed (a' i) (hfix i hi))
  choose! c hc using hK
  have hv0 : v (∑ i ∈ s, c i • b i) = 0 := by
    funext y
    rw [map_sum, Finset.sum_apply, Pi.zero_apply, ← ha'rel y]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [map_smul, Pi.smul_apply, Algebra.smul_def, hc i hi]
  have hsum0 : ∑ i ∈ s, c i • b i = 0 := hinj (by rw [hv0, map_zero])
  have hc0 := (linearIndependent_iff'.mp hb) s c hsum0 i0 hi0
  rw [← hc i0 hi0, hc0, map_zero] at ha'1
  exact zero_ne_one ha'1
end ReciprocityTheory.ChartRestriction.G.TB
