-- Prove2me | solution 1 for UpperTheory.splitPlaces_discriminantDepth_of_splitAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:23:47.629202+00:00
-- url     : https://prove2.me/submissions/2ababc87-e313-4735-990b-c8d9078af084

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_Places
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ExistsPrimitiveOrthogonalIdempotentsSumEqOfNoeth
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ExistsSplitIdempotentOfSplitAt
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_TraceFormDecompositionCMDatum
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_DiscrCMDatumEqProdPlaces
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_SplitPlacesDiscriminantDepthOfSplitAt
import Theorems.Thm_UpperTheory_discr_CMDatum_eq_prod_places
import Theorems.Thm_UpperTheory_exists_primitive_orthogonal_idempotents_sum_eq_of_noetherian
import Theorems.Thm_UpperTheory_exists_splitIdempotent_of_splitAt
import Theorems.Thm_UpperTheory_trace_form_decomposition_CMDatum

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
namespace UpperTheory.Depth.SplitPl
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
private theorem exists_inPsi (H : Host E) : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hE]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h.trans H.sqrt_neg_disc_sq.symm) with h1 | h1
  · exact ⟨τ, h1⟩
  · refine ⟨ComplexEmbedding.conjugate τ, ?_⟩
    rw [ComplexEmbedding.conjugate_coe_eq, h1]
    have hre := congrArg Complex.re H.sqrt_neg_disc_sq
    have him := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [pow_two] at hre him
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h0 : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
    apply Complex.ext <;> simp [h0]
private theorem existsUnique_one {A O : Type} [CommRing A] [CommRing O] [IsDomain O] {F : Type} [FunLike F A O]
    [RingHomClass F A O] (φ : F) {s : ℕ} (g : Fin s → A) (h1 : ∀ i, g i * g i = g i)
    (h2 : ∀ i j, i ≠ j → g i * g j = 0) (h : φ (∑ i, g i) = 1) : ∃! i, φ (g i) = 1 := by
  have hex : ∃ i, φ (g i) ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [map_sum, Finset.sum_eq_zero fun i _ => hc i] at h
    exact zero_ne_one h
  obtain ⟨i, hi⟩ := hex
  have hi1 : φ (g i) = 1 := by
    apply mul_left_cancel₀ hi
    rw [← map_mul, h1, mul_one]
  refine ⟨i, hi1, fun j hj => ?_⟩
  by_contra hne
  have := congrArg φ (h2 j i hne)
  rw [map_mul, hj, hi1, mul_one, map_zero] at this
  exact one_ne_zero this
end UpperTheory.Depth.SplitPl
end

set_option autoImplicit false
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth
open UpperTheory.Depth.SplitPl
namespace UpperTheory
theorem _root_.solution :
    ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), SplitAt H.d p →
      ∀ f : ℕ, Module.finrank ℚ E = 2 * f → SplitPlaces p H f ((padicValInt p (NumberField.discr E) : ℝ) / (Module.finrank ℚ E : ℝ)) := by
  intro p _ E _ _ _ H hsp f hf
  letI := H.starRing
  intro C _ _ _ v O _ _ hv _ _ τO hinj hrt
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : CharZero O := (algebraMap O C).charZero
  obtain ⟨τ₀, hτ₀⟩ := exists_inPsi H
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hsq : ∀ σ : 𝓞 E →+* O, σ H.rt ^ 2 = -(H.d : O) := fun σ => by
    rw [← map_pow, H.rt_sq]; simp
  have hsurj : Function.Surjective τO := by
    have hc := (UpperTheory.trace_form_decomposition_CMDatum E p C v O hv 0 (by simp)).2
    haveI : Finite (𝓞 E →+* O) := Nat.finite_of_card_ne_zero (by omega)
    refine (hinj.bijective_of_nat_card_le ?_).2
    rw [hc, Nat.card_eq_fintype_card, Embeddings.card E ℂ]
  have hpsi : ∀ τ, InPsi H τ ↔ τO τ H.rt = τO τ₀ H.rt := fun τ => by
    rw [← hrt, hτ₀]; rfl
  have hneg : ∀ τ, τO τ H.rt = - τO τ₀ H.rt → ¬ InPsi H τ := by
    intro τ h h'
    rw [hpsi] at h'
    have h3 : τO τ₀ H.rt = 0 := by
      have : (2 : O) * τO τ₀ H.rt = 0 := by linear_combination h - h'
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    have h4 := hsq (τO τ₀)
    rw [h3] at h4
    have : (H.d : O) = 0 := by linear_combination h4
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  haveI : IsNoetherianRing (ℤ_[p] ⊗[ℤ] 𝓞 E) :=
    IsNoetherianRing.of_finite ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E)
  obtain ⟨e, he, hs, hp, hm⟩ : ∃ e : ℤ_[p] ⊗[ℤ] 𝓞 E, e * e = e ∧ e + sig p (𝓞 E) e = 1 ∧
      (∀ σ : 𝓞 E →+* O, σ ∈ Emb (O := O) e ↔ σ H.rt = τO τ₀ H.rt) ∧
      (∀ σ : 𝓞 E →+* O, σ ∈ Emb (O := O) (1 - e) ↔ σ H.rt = - τO τ₀ H.rt) := by
    obtain ⟨e, α, he, -, -, hs, hα, hemb⟩ := UpperTheory.exists_splitIdempotent_of_splitAt p E H hsp
    have hα' : algebraMap ℤ_[p] O α ^ 2 = -(H.d : O) := by rw [← map_pow, hα]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 ((hsq (τO τ₀)).trans hα'.symm) with h | h
    · refine ⟨e, he, hs, fun σ => ?_, fun σ => ?_⟩
      · rw [h]; exact (hemb O σ).1
      · rw [h]; exact (hemb O σ).2
    · refine ⟨1 - e, by linear_combination he, ?_, fun σ => ?_, fun σ => ?_⟩
      · rw [map_sub, map_one]; linear_combination -hs
      · rw [h]; exact (hemb O σ).2
      · rw [h, neg_neg, sub_sub_cancel]; exact (hemb O σ).1
  have hbar : sig p (𝓞 E) e = 1 - e := by linear_combination hs
  obtain ⟨s, g, hg, horth, hsum⟩ := UpperTheory.exists_primitive_orthogonal_idempotents_sum_eq_of_noetherian _ e he
  have hge : ∀ i, g i * e = g i := fun i => by
    rw [← hsum, Finset.mul_sum, Finset.sum_eq_single i]
    · exact (hg i).1
    · intro j _ hj
      exact horth i j (Ne.symm hj)
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hsge : ∀ i, sig p (𝓞 E) (g i) * (1 - e) = sig p (𝓞 E) (g i) := fun i => by
    rw [← hbar, ← map_mul, hge]
  have hcross : ∀ i j, g i * sig p (𝓞 E) (g j) = 0 := fun i j => by
    rw [← hge i, ← hsge j]
    linear_combination (- (g i * sig p (𝓞 E) (g j))) * he
  have hsplit : ∀ i, sig p (𝓞 E) (g i) ≠ g i := fun i h => by
    have := hcross i i
    rw [h, (hg i).1] at this
    exact (hg i).2.1 this
  let w : Fin s → Place p (𝓞 E) := fun i => ⟨g i, (hg i).1, (hg i).2.1, (hg i).2.2, hsplit i⟩
  have hone : (∑ i, (w i).e) + (∑ i, (w i).bar) = 1 := by
    show (∑ i, g i) + (∑ i, sig p (𝓞 E) (g i)) = 1
    rw [← map_sum, hsum, hs]
  obtain ⟨hn, hvd⟩ := UpperTheory.discr_CMDatum_eq_prod_places E p C v O hv s w horth hone hcross
  have t : ∀ i, Fin (w i).n ≃ Emb (O := O) (w i).e := fun i =>
    (UpperTheory.trace_form_decomposition_CMDatum E p C v O hv (g i) (hg i).1).1.some
  obtain ⟨vdi, hv1, hv2⟩ := hvd t
  have hup : ∀ (x y : ℤ_[p] ⊗[ℤ] 𝓞 E) (σ : 𝓞 E →+* O), x * y = x → σ ∈ Emb (O := O) x → σ ∈ Emb (O := O) y := by
    intro x y σ hxy hx
    have hx' : tauExt σ x = 1 := hx
    have := congrArg (tauExt (p := p) σ) hxy
    rw [map_mul, hx', one_mul] at this
    exact this
  refine ⟨s, w, vdi, by omega, ?_, fun i σ h => ?_, fun τ hτ => ?_, fun i σ h => ?_, fun i => ⟨t i, hv1 i⟩⟩
  · have hf0 : (f : ℝ) ≠ 0 := by
      have : f ≠ 0 := by omega
      exact_mod_cast this
    rw [hv2, hf]
    push_cast
    field_simp
  · obtain ⟨τ, rfl⟩ := hsurj σ
    exact ⟨τ, (hpsi τ).2 ((hp _).1 (hup _ _ _ (hge i) h)), rfl⟩
  · have h : tauExt (p := p) (τO τ) (∑ i, g i) = 1 := by
      rw [hsum]
      exact (hp _).2 ((hpsi τ).1 hτ)
    exact existsUnique_one (tauExt (p := p) (τO τ)) g (fun i => (hg i).1) horth h
  · obtain ⟨τ, rfl⟩ := hsurj σ
    exact ⟨τ, hneg τ ((hm _).1 (hup _ _ _ (hsge i) h)), rfl⟩
end UpperTheory
