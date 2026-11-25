-- Prove2me | solution 1 for PIW.AdelicOrbitU.uc_rp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:20:46.316424+00:00
-- url     : https://prove2.me/submissions/e2acf377-9a0d-4d52-80e2-31dd46b6bc31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_LocalSum
import Theorems.Thm_PIW_AdelicOrbitU_uc_coeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped RestrictedProduct
namespace PIW.AdelicOrbitU
theorem _root_.solution {ι : Type} (K : ι → Type) [∀ v, Field (K v)] {S : ι → Type} [∀ v, SetLike (S v) (K v)]
    [∀ v, SubringClass (S v) (K v)] (B : ∀ v, S v) (𝓕 : Filter ι)
    (hloc : ∀ v (k : ℕ) (a f : Fin k → B v), ∑ i, a i * f i = 1 → ∃ i, IsUnit (f i)) :
    UnitChoice (Πʳ v, [K v, B v]_[𝓕]) := by
  intro k f hf
  obtain ⟨a, ha⟩ := uc_coeffs hf
  have hev : ∀ (x : Fin k → Πʳ v, [K v, B v]_[𝓕]) (v : ι), (∑ i, x i) v = ∑ i, x i v :=
    fun x v => map_sum (RestrictedProduct.evalRingHom K v) x Finset.univ
  have hcomp : ∀ v, ∑ i, a i v * f i v = 1 := by
    intro v
    have h := congrArg (fun x : Πʳ v, [K v, B v]_[𝓕] => x v) ha
    simp only [hev, RestrictedProduct.mul_apply] at h
    exact h
  have hex : ∀ v, ∃ i, f i v ≠ 0 ∧ ((∀ j, a j v ∈ B v ∧ f j v ∈ B v) → (f i v)⁻¹ ∈ B v) := by
    intro v
    by_cases hg : ∀ j, a j v ∈ B v ∧ f j v ∈ B v
    · have hsum : ∑ j, (⟨a j v, (hg j).1⟩ : B v) * ⟨f j v, (hg j).2⟩ = 1 := by
        apply Subtype.ext
        have h1 := map_sum (SubringClass.subtype (B v))
          (fun j => (⟨a j v, (hg j).1⟩ : B v) * ⟨f j v, (hg j).2⟩) Finset.univ
        simp only [map_mul] at h1
        exact h1.trans (hcomp v)
      obtain ⟨i, hi⟩ := hloc v k (fun j => ⟨a j v, (hg j).1⟩) (fun j => ⟨f j v, (hg j).2⟩) hsum
      obtain ⟨b, hb⟩ := hi.exists_right_inv
      have hb' : f i v * (b : K v) = 1 := congrArg Subtype.val hb
      refine ⟨i, ?_, fun _ => ?_⟩
      · intro h0
        rw [h0, zero_mul] at hb'
        exact zero_ne_one hb'
      · rw [inv_eq_of_mul_eq_one_right hb']
        exact b.2
    · obtain ⟨i, hi⟩ : ∃ i, f i v ≠ 0 := by
        by_contra hne
        push_neg at hne
        have h := hcomp v
        simp [hne] at h
      exact ⟨i, hi, fun h => absurd h hg⟩
  choose c hc using hex
  classical
  let e : Fin k → Πʳ v, [K v, B v]_[𝓕] := fun i =>
    RestrictedProduct.mk (fun v => if c v = i then (1 : K v) else 0)
      (Filter.Eventually.of_forall fun v => by
        show (if c v = i then (1 : K v) else 0) ∈ B v
        split_ifs
        exacts [one_mem (B v), zero_mem (B v)])
  have he : ∀ i v, e i v = if c v = i then (1 : K v) else 0 := fun i v => rfl
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro i
    apply RestrictedProduct.ext
    intro v
    rw [RestrictedProduct.mul_apply, he]
    split_ifs <;> simp
  · intro i j hij
    apply RestrictedProduct.ext
    intro v
    rw [RestrictedProduct.mul_apply, he, he,
      show ((0 : Πʳ v, [K v, B v]_[𝓕]) v) = 0 from rfl]
    split_ifs with h1 h2 <;> simp_all
  · apply RestrictedProduct.ext
    intro v
    rw [hev, show ((1 : Πʳ v, [K v, B v]_[𝓕]) v) = 1 from rfl]
    simp [he]
  · have hgood : ∀ᶠ v in 𝓕, ∀ j, a j v ∈ B v ∧ f j v ∈ B v := by
      rw [Filter.eventually_all]
      intro j
      exact (a j).2.and (f j).2
    let z : Πʳ v, [K v, B v]_[𝓕] := RestrictedProduct.mk (fun v => (f (c v) v)⁻¹)
      (hgood.mono fun v hv => (hc v).2 hv)
    refine isUnit_iff_exists_inv.mpr ⟨z, ?_⟩
    apply RestrictedProduct.ext
    intro v
    rw [RestrictedProduct.mul_apply, hev]
    have hs : ∑ i, (e i * f i) v = f (c v) v := by
      rw [Finset.sum_eq_single (c v)]
      · rw [RestrictedProduct.mul_apply, he, if_pos rfl, one_mul]
      · intro b _ hb
        rw [RestrictedProduct.mul_apply, he, if_neg (Ne.symm hb), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hs]
    exact mul_inv_cancel₀ (hc v).1
end PIW.AdelicOrbitU
