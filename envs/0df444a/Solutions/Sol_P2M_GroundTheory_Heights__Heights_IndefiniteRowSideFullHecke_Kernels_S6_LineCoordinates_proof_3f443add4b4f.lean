-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_LineCoordinates_proof_3f443add4b4f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:33.778179+00:00
-- url     : https://prove2.me/submissions/d74a13e3-d313-4649-a872-7eccff1cb536

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulEqSmulOfFinrankOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_self_b6b367d8e3db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_lineCoef_eq_zero_5d407d771e30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_fibreVec_lineCoef_72af0e9a7beb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_fibreVec_finset_sum_fc36c4e9987d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.LineCoordinates
theorem _root_.solution : S6.LineCoordinates.Statement := by
  intro K _ _ E X _ _ L hI hr ho
  set n := Fintype.card X
  let e : Fin n ≃ X := (Fintype.equivFin X).symm
  have hne : ∀ x, ∃ l ∈ L x, l ≠ 0 := by
    intro x
    have hb : L x ≠ ⊥ := by
      intro h
      have h1 := hr x
      rw [h] at h1
      simp [HermitianBundle.rank] at h1
    exact (Submodule.ne_bot_iff _).mp hb
  choose l hl hl0 using hne
  let α : ∀ x, L x →ₗ[𝓞 K] K := fun x => lineCoef (hr x) (hl x) (hl0 x)
  let Φ := LinearEquiv.ofBijective (DirectSum.coeLinearMap L) hI
  let comp : ∀ x, E.carrier →ₗ[𝓞 K] L x := fun x =>
    (DirectSum.component (𝓞 K) X (fun x => L x) x).comp Φ.symm.toLinearMap
  have hcomp_same : ∀ x (w : E.carrier) (hw : w ∈ L x), comp x w = ⟨w, hw⟩ := fun x w hw =>
    hI.ofBijective_coeLinearMap_of_mem hw
  have hcomp_ne : ∀ x y (w : E.carrier), w ∈ L x → x ≠ y → comp y w = 0 := fun x y w hw hxy =>
    hI.ofBijective_coeLinearMap_of_mem_ne hxy hw
  have hsum : ∀ v : E.carrier, ∑ x, (comp x v : E.carrier) = v := by
    intro v
    conv_rhs => rw [← Φ.apply_symm_apply v, ← DirectSum.sum_univ_of (Φ.symm v)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show _ = DirectSum.coeLinearMap L (DirectSum.of (fun i => L i) x (Φ.symm v x))
    rw [DirectSum.coeLinearMap_of]
    rfl
  let ψ : E.carrier →ₗ[𝓞 K] (Fin n → K) := LinearMap.pi fun i => (α (e i)).comp (comp (e i))
  have hψ_apply : ∀ v i, ψ v i = α (e i) (comp (e i) v) := fun _ _ => rfl
  have hψ_line : ∀ i (w : E.carrier) (hw : w ∈ L (e i)),
      ψ w = Pi.single i (α (e i) ⟨w, hw⟩) := by
    intro i w hw
    funext j
    rw [hψ_apply]
    by_cases hj : j = i
    · subst hj
      rw [hcomp_same _ w hw, Pi.single_eq_same]
    · rw [hcomp_ne _ _ w hw (e.injective.ne (Ne.symm hj)), map_zero, Pi.single_eq_of_ne hj]

  have hfrac : ∀ i, IsFractional (𝓞 K)⁰ (LinearMap.range (α (e i))) := fun i =>
    FractionalIdeal.isFractional_of_fg (by
      rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _)
  let a : Fin n → FractionalIdeal (𝓞 K)⁰ K := fun i => ⟨LinearMap.range (α (e i)), hfrac i⟩
  have ha : ∀ i, a i ≠ 0 := by
    intro i h
    have h1 : (1 : K) ∈ (a i : Submodule (𝓞 K) K) :=
      LinearMap.mem_range.mpr ⟨⟨l (e i), hl (e i)⟩, lineCoef_self _ _ _⟩
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at h1
    exact one_ne_zero h1

  have hψl : ∀ i, ψ (l (e i)) = Pi.single i 1 := fun i => by
    rw [hψ_line i _ (hl (e i))]
    exact congrArg (Pi.single i) (lineCoef_self _ _ _)
  have hlin : LinearIndependent (𝓞 K) (fun i => l (e i)) := by
    apply LinearIndependent.of_comp ψ
    have h1 : (ψ ∘ fun i => l (e i)) = fun i => Pi.basisFun K (Fin n) i := by
      funext i
      simp only [Function.comp_apply, hψl, Pi.basisFun_apply]
    rw [h1, LinearIndependent.iff_fractionRing (𝓞 K) K]
    exact (Pi.basisFun K (Fin n)).linearIndependent
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hc : ∀ i, comp (e i) v = 0 := by
      intro i
      have h := congrFun hv i
      rw [hψ_apply, Pi.zero_apply] at h
      exact Subtype.ext (lineCoef_eq_zero _ _ _ h)
    rw [← hsum v]
    refine Finset.sum_eq_zero fun x _ => ?_
    obtain ⟨i, rfl⟩ := e.surjective x
    rw [hc i, Submodule.coe_zero]
  have hrange : LinearMap.range ψ = idealLattice a := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [idealLattice, Submodule.mem_pi]
      intro i _
      exact LinearMap.mem_range.mpr ⟨comp (e i) v, rfl⟩
    · intro f hf
      rw [idealLattice, Submodule.mem_pi] at hf
      have h1 : ∀ i, ∃ w : L (e i), α (e i) w = f i := fun i =>
        LinearMap.mem_range.mp (hf i (Set.mem_univ i))
      choose w hw using h1
      refine ⟨∑ i, (w i : E.carrier), ?_⟩
      have h2 : ∀ i, ψ (w i) = Pi.single i (f i) := fun i => by
        rw [hψ_line i _ (w i).2, ← hw i]
      rw [map_sum]
      simp only [h2]
      exact Finset.univ_sum_single f
  have hfin : Module.finrank (𝓞 K) E.carrier = n := by
    apply le_antisymm
    · obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := E.carrier) le_rfl
      have h1 : LinearIndependent K (ψ ∘ f) := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp
        (hf.map' ψ (LinearMap.ker_eq_bot.mpr hinj))
      simpa using h1.fintype_card_le_finrank
    · simpa using hlin.fintype_card_le_finrank
  have hlines : ∀ i, (L (e i)).map ψ = idealLattice a ⊓
      (Submodule.span K {(Pi.single i 1 : Fin n → K)}).restrictScalars (𝓞 K) := by
    intro i
    ext f
    simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.restrictScalars_mem,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨hrange ▸ LinearMap.mem_range_self ψ w, α (e i) ⟨w, hw⟩, ?_⟩
      rw [hψ_line i w hw]
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
    · rintro ⟨hf1, c, rfl⟩
      have hmem : (c • Pi.single i 1 : Fin n → K) i ∈ (a i : Submodule (𝓞 K) K) := by
        rw [idealLattice, Submodule.mem_pi] at hf1
        exact hf1 i (Set.mem_univ _)
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
      refine ⟨w, w.2, ?_⟩
      rw [hψ_line i w w.2]
      rw [show α (e i) ⟨(w : E.carrier), w.2⟩ = α (e i) w from rfl, hw]
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]

  have hinnerF : ∀ σ (v w : E.carrier), inner ℂ (fibreVec E.metric σ v) (fibreVec E.metric σ w) =
      (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) :=
    fun _ _ _ => rfl
  let d : (K →+* ℂ) → Fin n → ℝ := fun σ i =>
    (inner ℂ (fibreVec E.metric σ (l (e i))) (fibreVec E.metric σ (l (e i)))).re
  have hF0 : ∀ σ i, fibreVec E.metric σ (l (e i)) ≠ 0 := fun σ i =>
    (linearIndependent_fibreVec E.metric σ hlin).ne_zero i
  have hd : ∀ σ i, 0 < d σ i := fun σ i => by
    have h := (re_inner_self_pos (𝕜 := ℂ)).mpr (hF0 σ i)
    rw [RCLike.re_to_complex] at h
    exact h
  have hc : ∀ σ i, d (conjugate σ) i = d σ i := fun σ i => by
    simp only [d, hinnerF]
    have h := E.metric.form_conj σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l (e i))
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l (e i))
    rw [conjMap_tmul, map_one] at h
    rw [h, Complex.conj_re]
  have hdi : ∀ σ i, inner ℂ (fibreVec E.metric σ (l (e i))) (fibreVec E.metric σ (l (e i))) =
      ((d σ i : ℝ) : ℂ) := fun σ i => by
    apply Complex.ext
    · simp [d]
    · simp only [Complex.ofReal_im, hinnerF]
      exact core_inner_self_im _ _

  have hexp : ∀ σ (v : E.carrier),
      fibreVec E.metric σ v = ∑ i, σ (ψ v i) • fibreVec E.metric σ (l (e i)) := by
    intro σ v
    conv_lhs => rw [← hsum v]
    rw [fibreVec_finset_sum, ← e.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact fibreVec_lineCoef (hr (e i)) (hl (e i)) (hl0 (e i)) σ (comp (e i) v)
  have hmet : ∀ (σ : K →+* ℂ) (v w : E.carrier),
      (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
        star (embVec σ (ψ v)) ⬝ᵥ (diagMetric d σ *ᵥ embVec σ (ψ w)) := by
    intro σ v w
    rw [← hinnerF, hexp σ v, hexp σ w, sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right]
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [hdi]
      simp only [diagMetric, mulVec_diagonal, embVec, Pi.star_apply, starRingEnd_apply]
      ring
    · intro j _ hji
      rw [hinnerF, ho σ (e i) (e j) (e.injective.ne (Ne.symm hji)) _ (hl _) _ (hl _), mul_zero,
        mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  exact ⟨n, e, a, d, ψ, ha, hd, hc, hinj, hrange, hfin, hlines, hmet⟩
end S6.LineCoordinates
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
