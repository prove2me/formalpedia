-- Prove2me | solution 1 for PI.VolStabW.addIntF_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:13.01631+00:00
-- url     : https://prove2.me/submissions/e97394a8-5299-4af3-9893-2a6b8a0c495f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensSAInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open PI PI.VolStabW
namespace PI.VolStabW
theorem _root_.solution : AddIntF := by
  intro F _ _ Λ ⟨c0, hc0, hc0Λ⟩ hb g hg
  classical

  have hrat1 : ∀ x : F, ∃ q : ℚ, g (c0 * x) = q := by
    intro x
    have hn : ∀ i, ∃ n : ℤ, g (c0 * integralBasis F i) = n := fun i => by
      apply hg
      rw [integralBasis_apply, mul_comm, ← Algebra.smul_def]
      exact Λ.smul_mem _ hc0Λ
    choose n hn using hn
    refine ⟨∑ i, (integralBasis F).repr x i * n i, ?_⟩
    conv_lhs => rw [← (integralBasis F).sum_repr x]
    rw [Finset.mul_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_smul_comm, map_rat_smul, hn i, Rat.smul_def]
  have hrat : ∀ a : F, ∃ q : ℚ, g a = q := fun a => by
    obtain ⟨q, hq⟩ := hrat1 (a / c0)
    exact ⟨q, by rwa [mul_div_cancel₀ _ hc0] at hq⟩
  choose q hq using hrat
  let g' : F →ₗ[ℚ] ℚ :=
    { toFun := q
      map_add' := fun a b => by
        have := g.map_add a b
        rw [hq, hq, hq] at this
        exact_mod_cast this
      map_smul' := fun c a => by
        have := map_rat_smul g c a
        rw [hq, hq] at this
        have h : ((q (c • a) : ℚ) : ℂ) = ((c * q a : ℚ) : ℂ) := by
          rw [this, Rat.smul_def]; norm_cast
        simp only [RingHom.id_apply, smul_eq_mul]
        exact_mod_cast h }
  have hg' : ∀ a, g a = (g' a : ℂ) := hq
  let β := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).symm g'
  have hβ : ∀ a, Algebra.traceForm ℚ F β a = g' a := fun a =>
    LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate ℚ F) g' a
  have hβ0 : β = 0 := by
    by_contra hβne
    obtain ⟨d, hdS, hd⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).isFractional
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdS
    have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
    apply hb (β * algebraMap (𝓞 F) F d)⁻¹ (inv_ne_zero (mul_ne_zero hβne hdF))
    intro a ha
    have h1 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      intro h
      have hm : (1 : F) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) :=
        (FractionalIdeal.mem_one_iff (𝓞 F)⁰).2 ⟨1, map_one _⟩
      rw [h, FractionalIdeal.mem_zero_iff] at hm
      exact one_ne_zero hm
    have hmem : β * a ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mem_dual h1]
      intro b hb1
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 F)⁰).1 hb1
      have hra : algebraMap (𝓞 F) F r * a ∈ Λ := by
        rw [← Algebra.smul_def]; exact Λ.smul_mem r ha
      obtain ⟨n, hn⟩ := hg _ hra
      refine ⟨n, ?_⟩
      rw [Algebra.traceForm_apply,
        show β * a * algebraMap (𝓞 F) F r = β * (algebraMap (𝓞 F) F r * a) by ring,
        ← Algebra.traceForm_apply, hβ]
      have h1 : ((g' (algebraMap (𝓞 F) F r * a) : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
        rw [← hg', hn]; push_cast; rfl
      have h2 : g' (algebraMap (𝓞 F) F r * a) = (n : ℚ) := by exact_mod_cast h1
      rw [h2]
      simp
    obtain ⟨r, hr⟩ := hd _ hmem
    refine ⟨r, ?_⟩
    rw [show (r : F) = algebraMap (𝓞 F) F r from rfl, hr, Algebra.smul_def]
    field_simp
  intro a
  rw [hg', ← hβ, hβ0]
  simp
end PI.VolStabW
