-- Prove2me | solution 1 for UpperTheory.exists_splitIdempotent_of_splitAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:54.501892+00:00
-- url     : https://prove2.me/submissions/d4d01dc4-b4d1-446d-9f05-7fa27801ac31

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_Places
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ExistsSplitIdempotentOfSplitAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth
namespace UpperTheory.Depth.SplitIdem
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
private theorem cmHost_bar_halfIntegerGenerator (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  have hsq : H.bar H.rt ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq]; simp
  have hrt : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exfalso
      have h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h2 := IsCMField.complexEmbedding_complexConj E τ (H.rt : E)
      rw [h1] at h2
      have h3 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        rw [← map_pow]
        have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
        simpa using this
      have h4 : (τ (H.rt : E)).im = 0 := Complex.conj_eq_iff_im.1 h2.symm
      have h5 := congrArg Complex.re h3
      simp [sq, h4] at h5
      have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    · exact h
  apply mul_left_cancel₀ (by norm_num : (2 : 𝓞 E) ≠ 0)
  have := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, hrt, map_ofNat] at this
  linear_combination this + H.two_weight_eq_one_add_root
private theorem exists_root_two (k : ℕ) : ∃ β γ : ℤ_[2], β * β = β - 2 * k ∧ γ * (1 - 2 * β) = 1 := by
  have h2 : ‖(2 : ℤ_[2])‖ < 1 := by
    have := PadicInt.norm_p (p := 2)
    simp only [Nat.cast_ofNat] at this
    rw [this]; norm_num
  have hlt : ∀ x : ℤ_[2], ‖2 * x‖ < 1 := fun x => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one x)) h2
  obtain ⟨β, hβ, -⟩ := hensels_lemma (p := 2) (R := ℤ_[2])
    (F := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * (k : ℤ_[2]))) (a := 0) (by
      simpa using hlt k)
  have hu : IsUnit (1 - 2 * β) := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    rw [PadicInt.mem_nonunits]
    exact hlt β
  obtain ⟨γ, hγ⟩ := hu.exists_left_inv
  refine ⟨β, γ, ?_, hγ⟩
  simp only [map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply] at hβ
  linear_combination hβ
private theorem exists_root (p : ℕ) [hp : Fact p.Prime] (d k : ℕ) (hk : d + 1 = 8 * k) (hs : SplitAt d p) :
    ∃ β γ : ℤ_[p], β * β = β - 2 * k ∧ γ * (1 - 2 * β) = 1 := by
  by_cases h2 : p = 2
  · subst h2
    exact exists_root_two k
  have hj : jacobiSym (-(d : ℤ)) p = 1 := hs.resolve_left h2
  have hne : ((-(d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro h
    rw [← jacobiSym.legendreSym.to_jacobiSym, (legendreSym.eq_zero_iff p _).2 h] at hj
    exact zero_ne_one hj
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective r
  have ha : (a : ZMod p) ≠ 0 := fun h => hne (by rw [hr, h, mul_zero])
  have h2' : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  have hunit : ∀ n : ℤ, (n : ZMod p) ≠ 0 → ‖(n : ℤ_[p])‖ = 1 := fun n hn => by
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hn ?_)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact (PadicInt.norm_int_lt_one_iff_dvd n).1 h
  have hlt : ‖((a ^ 2 + d : ℤ) : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    linear_combination -hr
  have hder : ‖((2 * a : ℤ) : ℤ_[p])‖ = 1 := hunit _ (by
    rw [Int.cast_mul]; exact mul_ne_zero h2' ha)
  obtain ⟨α, hα, -⟩ := hensels_lemma (p := p) (R := ℤ_[p])
    (F := Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[p])) (a := (a : ℤ_[p])) (by
      push_cast at hlt hder
      have e1 : Polynomial.aeval (a : ℤ_[p]) (Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[p])) = (a : ℤ_[p]) ^ 2 + d := by
        simp
      have e2 : Polynomial.aeval (a : ℤ_[p])
          (Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.C (d : ℤ_[p]))) = 2 * (a : ℤ_[p]) := by
        simp [one_add_one_eq_two]
      rw [e1, e2, hder, one_pow]
      exact hlt)
  simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply] at hα
  obtain ⟨u, hu⟩ := (PadicInt.isUnit_iff.2 (hunit 2 h2')).exists_left_inv
  obtain ⟨v, hv⟩ := (PadicInt.isUnit_iff.2 (hunit _ hne)).exists_left_inv
  push_cast at hu hv
  have hk' : (d : ℤ_[p]) + 1 = 8 * k := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[p]) hk
  refine ⟨u * (1 - α), v * α, ?_, ?_⟩
  · linear_combination u ^ 2 * hα - u ^ 2 * hk' + (u * (1 - α) - 2 * k * (2 * u + 1)) * hu
  · linear_combination hv + v * hα - v * α * (1 - α) * hu
end UpperTheory.Depth.SplitIdem
end

set_option autoImplicit false
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth
namespace UpperTheory
theorem _root_.solution :
    ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), SplitAt H.d p →
      letI := H.starRing; ∃ (e : ℤ_[p] ⊗[ℤ] 𝓞 E) (α : ℤ_[p]), e * e = e ∧ e ≠ 0 ∧ e ≠ 1 ∧ e + sig p (𝓞 E) e = 1 ∧ α ^ 2 = -(H.d : ℤ_[p]) ∧
        ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Algebra ℤ_[p] O] (σ : 𝓞 E →+* O),
          (σ ∈ Emb (O := O) e ↔ σ H.rt = algebraMap ℤ_[p] O α) ∧ (σ ∈ Emb (O := O) (1 - e) ↔ σ H.rt = - algebraMap ℤ_[p] O α) := by
  intro p _ E _ _ _ H hs
  letI := H.starRing
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d + 1 = 8 * k := ⟨(H.d + 1) / 8, by have := H.d_mod; omega⟩
  obtain ⟨β, γ, hβ, hγ⟩ := UpperTheory.Depth.SplitIdem.exists_root p H.d k hk hs
  have hw : H.w0 * H.w0 = H.w0 - 2 * k := by
    apply mul_left_cancel₀ (by norm_num : (4 : 𝓞 E) ≠ 0)
    have hk' : (H.d : 𝓞 E) + 1 = 8 * k := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) hk
    linear_combination (2 * H.w0 - 1 + H.rt) * H.two_weight_eq_one_add_root + H.rt_sq - hk'
  let ι : ℤ_[p] →+* ℤ_[p] ⊗[ℤ] 𝓞 E := algebraMap _ _
  let j : 𝓞 E →+* ℤ_[p] ⊗[ℤ] 𝓞 E :=
    (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom
  have hβ' : ι β * ι β = ι β - 2 * k := by
    have := congrArg ι hβ
    simpa only [map_mul, map_sub, map_ofNat, map_natCast] using this
  have hγ' : ι γ * (1 - 2 * ι β) = 1 := by
    have := congrArg ι hγ
    simpa only [map_mul, map_sub, map_ofNat, map_one] using this
  have hw' : j H.w0 * j H.w0 = j H.w0 - 2 * k := by
    have := congrArg j hw
    simpa only [map_mul, map_sub, map_ofNat, map_natCast] using this
  have hsι : ∀ x, sig p (𝓞 E) (ι x) = ι x := fun x => (sig p (𝓞 E)).commutes x
  have hsj : sig p (𝓞 E) (j H.w0) = 1 - j H.w0 := by
    have h1 : sig p (𝓞 E) (j H.w0) = j (H.bar H.w0) := by
      show sig p (𝓞 E) (1 ⊗ₜ H.w0) = 1 ⊗ₜ (H.bar H.w0)
      unfold sig
      rw [Algebra.TensorProduct.map_tmul]
      rfl
    rw [h1, UpperTheory.Depth.SplitIdem.cmHost_bar_halfIntegerGenerator, map_sub, map_one]
  have hsum : ι γ * (j H.w0 - ι β) + sig p (𝓞 E) (ι γ * (j H.w0 - ι β)) = 1 := by
    rw [map_mul, map_sub, hsι, hsι, hsj]
    linear_combination hγ'
  haveI : Nontrivial (ℤ_[p] ⊗[ℤ] 𝓞 E) := Module.FaithfullyFlat.rTensor_nontrivial ℤ (𝓞 E) ℤ_[p]
  refine ⟨ι γ * (j H.w0 - ι β), 1 - 2 * β, ?_, ?_, ?_, hsum, ?_, ?_⟩
  · linear_combination (ι γ) ^ 2 * hw' - (ι γ) ^ 2 * hβ' + ι γ * (j H.w0 - ι β) * hγ'
  · intro h
    rw [h, map_zero, add_zero] at hsum
    exact zero_ne_one hsum
  · intro h
    rw [h, map_one] at hsum
    exact one_ne_zero (add_left_cancel (hsum.trans (add_zero _).symm))
  · have hk' : (H.d : ℤ_[p]) + 1 = 8 * k := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[p]) hk
    linear_combination 4 * hβ + hk'
  · intro O _ _ _ _ σ
    have hτ : tauExt (p := p) σ (ι γ * (j H.w0 - ι β)) =
        algebraMap ℤ_[p] O γ * (σ H.w0 - algebraMap ℤ_[p] O β) := by
      have h1 : ∀ x, tauExt (p := p) σ (ι x) = algebraMap ℤ_[p] O x := fun x => (tauExt σ).commutes x
      have h2 : tauExt (p := p) σ (j H.w0) = σ H.w0 := by
        show tauExt (p := p) σ (1 ⊗ₜ H.w0) = _
        unfold tauExt
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rfl
      rw [map_mul, map_sub, h1, h1, h2]
    have hg : algebraMap ℤ_[p] O γ * (1 - 2 * algebraMap ℤ_[p] O β) = 1 := by
      have := congrArg (algebraMap ℤ_[p] O) hγ
      simpa only [map_mul, map_sub, map_ofNat, map_one] using this
    have hr : 2 * σ H.w0 = 1 + σ H.rt := by
      have := congrArg σ H.two_weight_eq_one_add_root
      simpa only [map_mul, map_add, map_ofNat, map_one] using this
    have ha : algebraMap ℤ_[p] O (1 - 2 * β) = 1 - 2 * algebraMap ℤ_[p] O β := by
      simp only [map_mul, map_sub, map_ofNat, map_one]
    have h2 : (2 : O) ≠ 0 := two_ne_zero
    simp only [Emb, Set.mem_setOf_eq]
    rw [map_sub (tauExt σ) 1, map_one, hτ, ha]
    set g := algebraMap ℤ_[p] O γ
    set b := algebraMap ℤ_[p] O β
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
    · linear_combination 2 * (1 - 2 * b) * h - 2 * (σ H.w0 - b) * hg - hr
    · apply mul_left_cancel₀ h2
      linear_combination g * hr + g * h + 2 * hg
    · linear_combination -2 * (1 - 2 * b) * h - 2 * (σ H.w0 - b) * hg - hr
    · apply mul_left_cancel₀ h2
      linear_combination - g * hr - g * h
end UpperTheory
