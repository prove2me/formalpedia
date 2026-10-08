-- Prove2me | solution 1 for WassDDRO.Extremal.program12f_eq_program13
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T11:40:06.044988+00:00
-- url     : https://prove2.me/submissions/22d272f5-0bb8-4368-9a03-9000a2ce8128

import Definitions.Def_WassDDRO_Extremal_Setting
import Definitions.Def_WassDDRO_Reduction_Setting
import Mathlib
set_option autoImplicit false
section
set_option autoImplicit false
namespace WassExtremalCodex

theorem perspective_kernel_mix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : StrongDual ℝ E) (C : EReal) (sample q r : E) (α β a b : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((z ((a • q+b • r)-(a*α+b*β) • sample) : ℝ) : EReal)+((a*α+b*β : ℝ) : EReal)*C =
      (a : EReal)*(((z (q-α • sample) : ℝ) : EReal)+(α : EReal)*C)+
      (b : EReal)*(((z (r-β • sample) : ℝ) : EReal)+(β : EReal)*C) := by
  have hv : (a • q+b • r)-(a*α+b*β) • sample=a • (q-α • sample)+b • (r-β • sample) := by module
  have hz : z ((a • q+b • r)-(a*α+b*β) • sample)=a*z (q-α • sample)+b*z (r-β • sample) := by
    rw [hv,map_add,map_smul,map_smul]
    rfl
  have haE : (0 : EReal)≤(a : EReal) := by exact_mod_cast ha
  have hbE : (0 : EReal)≤(b : EReal) := by exact_mod_cast hb
  have hαE : (0 : EReal)≤(α : EReal) := by exact_mod_cast hα
  have hβE : (0 : EReal)≤(β : EReal) := by exact_mod_cast hβ
  rw [hz,EReal.coe_add,EReal.coe_mul,EReal.coe_mul,EReal.coe_add,EReal.coe_mul,EReal.coe_mul,
    EReal.right_distrib_of_nonneg (EReal.mul_nonneg haE hαE) (EReal.mul_nonneg hbE hβE),
    EReal.left_distrib_of_nonneg_of_ne_top haE (EReal.coe_ne_top a),
    EReal.left_distrib_of_nonneg_of_ne_top hbE (EReal.coe_ne_top b)]
  simp only [mul_assoc]
  exact add_add_add_comm _ _ _ _

theorem perspective_kernel_height_mix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : StrongDual ℝ E) (C : EReal) (sample q r : E) (α β a b t u : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : (t : EReal)≤((z (q-α • sample) : ℝ) : EReal)+(α : EReal)*C)
    (hu : (u : EReal)≤((z (r-β • sample) : ℝ) : EReal)+(β : EReal)*C) :
    ((a*t+b*u : ℝ) : EReal)≤((z ((a • q+b • r)-(a*α+b*β) • sample) : ℝ) : EReal)+
      ((a*α+b*β : ℝ) : EReal)*C := by
  rw [perspective_kernel_mix z C sample q r α β a b hα hβ ha hb,EReal.coe_add,EReal.coe_mul,EReal.coe_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left ht (by exact_mod_cast ha))
    (mul_le_mul_of_nonneg_left hu (by exact_mod_cast hb))
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

noncomputable def finitePerspectiveValues {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (ξhat : Fin N → E) : Set (ℝ×ℝ) :=
  {v | ∃ (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) (t : Fin N → Fin K → ℝ),
    (∀ i, ∑ k, α i k=1) ∧ (∀ i k, 0≤α i k) ∧
    (1/(N : ℝ))*(∑ i, ∑ k, ‖q i k‖)≤v.1 ∧
    v.2≤(1/(N : ℝ))*(∑ i, ∑ k, t i k) ∧
    ∀ i k (z : StrongDual ℝ E), (t i k : EReal)≤((z (q i k-α i k • ξhat i) : ℝ) : EReal)+
      (α i k : EReal)*conjOn Ξ (fun x => -ℓ k x) z}

theorem finitePerspectiveValues_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (ξhat : Fin N → E) :
    Convex ℝ (finitePerspectiveValues Ξ ℓ ξhat) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨α,q,t,hαs,hα,hq,ht,hφ⟩ := hx
  obtain ⟨β,r,u,hβs,hβ,hr,hu,hψ⟩ := hy
  refine ⟨(fun i k => a*α i k+b*β i k),(fun i k => a • q i k+b • r i k),
    (fun i k => a*t i k+b*u i k),?_,?_,?_,?_,?_⟩
  · intro i
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,hαs,hβs,mul_one,hab]
  · intro i k
    exact add_nonneg (mul_nonneg ha (hα i k)) (mul_nonneg hb (hβ i k))
  · change (1/(N : ℝ))*(∑ i, ∑ k, ‖a • q i k+b • r i k‖)≤a*x.1+b*y.1
    have hn : ∀ i k, ‖a • q i k+b • r i k‖≤a*‖q i k‖+b*‖r i k‖ := by
      intro i k
      have hh := norm_add_le (a • q i k) (b • r i k)
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] using hh
    have hs : (∑ i, ∑ k, ‖a • q i k+b • r i k‖)≤
        a*(∑ i, ∑ k, ‖q i k‖)+b*(∑ i, ∑ k, ‖r i k‖) := by
      calc
        _ ≤ ∑ i, ∑ k, (a*‖q i k‖+b*‖r i k‖) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => hn i k))
        _ = _ := by simp_rw [Finset.sum_add_distrib,←Finset.mul_sum]
    calc
      _ ≤ (1/(N : ℝ))*(a*(∑ i, ∑ k, ‖q i k‖)+b*(∑ i, ∑ k, ‖r i k‖)) :=
        mul_le_mul_of_nonneg_left hs (one_div_nonneg.mpr (Nat.cast_nonneg N))
      _ = a*((1/(N : ℝ))*(∑ i, ∑ k, ‖q i k‖))+b*((1/(N : ℝ))*(∑ i, ∑ k, ‖r i k‖)) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hq ha) (mul_le_mul_of_nonneg_left hr hb)
  · change a*x.2+b*y.2≤(1/(N : ℝ))*(∑ i, ∑ k, (a*t i k+b*u i k))
    have hs : (1/(N : ℝ))*(∑ i, ∑ k, (a*t i k+b*u i k)) =
        a*((1/(N : ℝ))*(∑ i, ∑ k, t i k))+b*((1/(N : ℝ))*(∑ i, ∑ k, u i k)) := by
      simp_rw [Finset.sum_add_distrib,←Finset.mul_sum]
      ring
    rw [hs]
    exact add_le_add (mul_le_mul_of_nonneg_left ht ha) (mul_le_mul_of_nonneg_left hu hb)
  · intro i k z
    exact perspective_kernel_height_mix z (conjOn Ξ (fun x => -ℓ k x) z)
      (ξhat i) (q i k) (r i k) (α i k) (β i k) a b (t i k) (u i k)
      (hα i k) (hβ i k) ha hb (hφ i k z) (hψ i k z)
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

noncomputable def oneHotWeights {N K : ℕ} (j : Fin N → Fin K) : Fin N → Fin K → ℝ :=
  fun i k => if k=j i then 1 else 0

noncomputable def oneHotDisplacements {E : Type*} [Sub E] [Zero E] {N K : ℕ}
    (sample x : Fin N → E) (j : Fin N → Fin K) : Fin N → Fin K → E :=
  fun i k => if k=j i then sample i-x i else 0

noncomputable def oneHotHeights {N K : ℕ} (j : Fin N → Fin K) (v : Fin N → ℝ) : Fin N → Fin K → ℝ :=
  fun i k => if k=j i then v i else 0

theorem oneHot_row_sum {N K : ℕ} (j : Fin N → Fin K) (i : Fin N) :
    (∑ k, oneHotWeights j i k)=1 := by simp [oneHotWeights]

theorem oneHot_nonneg {N K : ℕ} (j : Fin N → Fin K) (i : Fin N) (k : Fin K) :
    0≤oneHotWeights j i k := by simp [oneHotWeights];split <;> norm_num

theorem oneHot_perspective_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (ξhat x : Fin N → E) (j : Fin N → Fin K)
    (v : Fin N → ℝ) (hx : ∀ i, x i∈Ξ) (hv : ∀ i, (v i : EReal)≤ℓ (j i) (x i)) :
    (((1/(N : ℝ))*(∑ i, ‖x i-ξhat i‖)),((1/(N : ℝ))*(∑ i, v i)))∈
      finitePerspectiveValues Ξ ℓ ξhat := by
  refine ⟨oneHotWeights j,oneHotDisplacements ξhat x j,oneHotHeights j v,
    oneHot_row_sum j,oneHot_nonneg j,?_,?_,?_⟩
  · have hs : ∀ i, (∑ k, ‖oneHotDisplacements ξhat x j i k‖)=‖x i-ξhat i‖ := by
      intro i
      simp [oneHotDisplacements,apply_ite,norm_sub_rev]
    simp only [hs]
    exact le_rfl
  · simp [oneHotHeights]
  · intro i k z
    by_cases hk : k=j i
    · subst k
      simp only [oneHotWeights,oneHotDisplacements,oneHotHeights,ite_true,one_smul,EReal.coe_one,one_mul]
      have hp : (ξhat i-x i)-ξhat i= -x i := by abel
      rw [hp,map_neg]
      have hc : (((z (x i)+v i : ℝ) : EReal))≤conjOn Ξ (fun y => -ℓ (j i) y) z := by
        calc
          _ = ((z (x i) : ℝ) : EReal)-(-(v i : EReal)) := by
            rw [←EReal.coe_neg,←EReal.coe_sub]
            congr 1
            ring
          _ ≤ ((z (x i) : ℝ) : EReal)-(-ℓ (j i) (x i)) :=
            EReal.sub_le_sub le_rfl (EReal.neg_le_neg_iff.mpr (hv i))
          _ ≤ _ := le_iSup₂_of_le (x i) (hx i) le_rfl
      calc
        (v i : EReal) = (((-z (x i) : ℝ) : EReal))+(((z (x i)+v i : ℝ) : EReal)) := by
          rw [←EReal.coe_add]
          congr 1
          ring
        _ ≤ _ := add_le_add le_rfl hc
    · simp [oneHotWeights,oneHotDisplacements,oneHotHeights,hk]
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem maxLoss_piece_attains {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {K : ℕ}
    (hK : 0 < K) (ℓ : Fin K → E → EReal) (x : E) : ∃ k, ℓ k x=maxLoss ℓ x := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  exact exists_eq_ciSup_of_finite

theorem finite_points_perspective_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (Ξ : Set E) (ℓ : Fin K → E → EReal) (ξhat x : Fin N → E)
    (hx : ∀ i, x i∈Ξ) (htop : ∀ k y, ℓ k y≠⊤) (hbot : ∀ i, maxLoss ℓ (x i)≠⊥) :
    (((1/(N : ℝ))*(∑ i, ‖x i-ξhat i‖)),((1/(N : ℝ))*(∑ i, (maxLoss ℓ (x i)).toReal)))∈
      finitePerspectiveValues Ξ ℓ ξhat := by
  classical
  have hp : ∀ i, ∃ k, ℓ k (x i)=maxLoss ℓ (x i) := fun i => maxLoss_piece_attains hK ℓ (x i)
  choose j hj using hp
  have hv : ∀ i, (((maxLoss ℓ (x i)).toReal : ℝ) : EReal)≤ℓ (j i) (x i) := by
    intro i
    rw [hj i]
    exact (EReal.coe_toReal (iSup_ne_top (fun k => htop k (x i))) (hbot i)).le
  exact oneHot_perspective_mem Ξ ℓ ξhat x j (fun i => (maxLoss ℓ (x i)).toReal) hx hv
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency

lemma expect_mono {Z : Type*} [MeasurableSpace Z] (Q : Measure Z)
    (f g : Z → EReal) (hfg : f ≤ᵐ[Q] g) :
    expect Q f ≤ expect Q g := by
  have hpos : (∫⁻ z, (f z).toENNReal ∂Q) ≤ ∫⁻ z, (g z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal hz)
  have hneg : (∫⁻ z, (-g z).toENNReal ∂Q) ≤ ∫⁻ z, (-f z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hz))
  unfold expect
  by_cases hgtop : (∫⁻ z, (g z).toENNReal ∂Q) = ⊤
  · rw [if_pos hgtop]
    exact le_top
  · have hftop : (∫⁻ z, (f z).toENNReal ∂Q) ≠ ⊤ :=
      (lt_of_le_of_lt hpos (lt_top_iff_ne_top.mpr hgtop)).ne
    rw [if_neg hgtop, if_neg hftop]
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpos)
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hneg)

end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency
lemma expect_eq_integral {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (l : E → ℝ) (hl : Integrable l Q) :
    expect Q (fun x => (l x : EReal)) = (∫ x, l x ∂Q : ℝ) := by
  have hp : (∫⁻ x, ENNReal.ofReal (l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm l).trans_lt hl.2).ne
  have hn : (∫⁻ x, ENNReal.ofReal (-l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm (fun x => -l x)).trans_lt hl.neg.2).ne
  unfold expect
  rw [if_neg (show (∫⁻ x, ((l x : EReal)).toENNReal ∂Q) ≠ ⊤ from hp)]
  simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
  rw [ ← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hl]


end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency
 theorem expect_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Q : Measure α) (g : α → β) (f : β → EReal) (hg : Measurable g) (hf : Measurable f) :
    expect (Q.map g) f=expect Q (fun x => f (g x)) := by
  have hp : (∫⁻ y, (f y).toENNReal ∂Q.map g) = ∫⁻ x, (f (g x)).toENNReal ∂Q :=
    lintegral_map (by fun_prop) hg
  have hn : (∫⁻ y, (-f y).toENNReal ∂Q.map g) = ∫⁻ x, (-f (g x)).toENNReal ∂Q :=
    lintegral_map (by fun_prop) hg
  unfold expect
  rw [hp,hn]
 theorem expect_le_integrable_upper {α : Type*} [MeasurableSpace α]
    (Q : Measure α) (f : α → EReal) (g : α → ℝ) (hg : Integrable g Q)
    (hfg : f ≤ᵐ[Q] fun x => (g x : EReal)) :
    expect Q f ≤ ((∫ x, g x ∂Q : ℝ) : EReal) := by
  rw [← expect_eq_integral Q g hg]
  exact expect_mono Q f _ hfg
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassersteinDRO.Duality
 theorem wasserstein_one_eq {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Q P : Measure E) : wassersteinDistance 1 Q P =
      ⨅ (π : Measure (E×E)) (_ : π.map Prod.fst=Q ∧ π.map Prod.snd=P),
        ∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π := by simp [wassersteinDistance]
 theorem exists_coupling_lt_budget_add {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Q P : Measure E) (ε η : ℝ) (hε : 0≤ε) (hη : 0<η)
    (hbudget : wassersteinDistance 1 Q P≤ENNReal.ofReal ε) :
    ∃ π : Measure (E×E), (π.map Prod.fst=Q ∧ π.map Prod.snd=P) ∧
      (∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π)<ENNReal.ofReal (ε+η) := by
  have hlt : wassersteinDistance 1 Q P<ENNReal.ofReal (ε+η) :=
    lt_of_le_of_lt hbudget ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε).mpr (by linarith))
  rw [wasserstein_one_eq,iInf_lt_iff] at hlt
  obtain ⟨π,hπ⟩ := hlt
  rw [iInf_lt_iff] at hπ
  obtain ⟨hm,hc⟩ := hπ
  exact ⟨π,hm,hc⟩
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex

lemma finite_probability_mixture {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (hπ : IsProbabilityMeasure π) (hρ : IsProbabilityMeasure ρ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    IsProbabilityMeasure (ENNReal.ofReal a • π+ENNReal.ofReal b • ρ) := by
  letI := hπ
  letI := hρ
  constructor
  simp only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_add ha hb,hab]
  norm_num

lemma finite_mixture_second_marginal {E : Type*} [MeasurableSpace E]
    (π ρ : Measure (E×E)) (P : Measure E) (hπ : π.map Prod.snd=P)
    (hρ : ρ.map Prod.snd=P) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (ENNReal.ofReal a • π+ENNReal.ofReal b • ρ).map Prod.snd=P := by
  rw [Measure.map_add _ _ measurable_snd,Measure.map_smul,Measure.map_smul,
    hπ,hρ,←add_smul,←ENNReal.ofReal_add ha hb,hab]
  simp

lemma finite_mixture_integral {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (f : Z → ℝ) (hπ : Integrable f π) (hρ : Integrable f ρ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ z, f z ∂(ENNReal.ofReal a • π+ENNReal.ofReal b • ρ)) =
      a*(∫ z, f z ∂π)+b*(∫ z, f z ∂ρ) := by
  rw [integral_add_measure (hπ.smul_measure ENNReal.ofReal_ne_top)
    (hρ.smul_measure ENNReal.ofReal_ne_top),integral_smul_measure,integral_smul_measure]
  simp only [ENNReal.toReal_ofReal ha,ENNReal.toReal_ofReal hb,smul_eq_mul]

/-- Cost/reward pairs from couplings on the finite-loss domain; no condition is
imposed on loss values outside the coupling's almost-everywhere support. -/
def finiteCouplingValues {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Ξ : Set E) (P : Measure E) (L : E → EReal) : Set (ℝ×ℝ) :=
  {v | ∃ π : Measure (E×E), IsProbabilityMeasure π ∧ π.map Prod.snd=P ∧
    (∀ᵐ w ∂π, w.1∈Ξ ∧ L w.1≠⊤ ∧ L w.1≠⊥) ∧
    Integrable (fun w : E×E => ‖w.1-w.2‖) π ∧
    Integrable (fun w : E×E => (L w.1).toReal) π ∧
    v=((∫ w, ‖w.1-w.2‖ ∂π),(∫ w, (L w.1).toReal ∂π))}

theorem finiteCouplingValues_convex {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Ξ : Set E) (P : Measure E) (L : E → EReal) : Convex ℝ (finiteCouplingValues Ξ P L) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨π,hπ,hπP,hπae,hπc,hπL,rfl⟩ := hx
  obtain ⟨ρ,hρ,hρP,hρae,hρc,hρL,rfl⟩ := hy
  refine ⟨ENNReal.ofReal a • π+ENNReal.ofReal b • ρ,
    finite_probability_mixture π ρ hπ hρ a b ha hb hab,
    finite_mixture_second_marginal π ρ P hπP hρP a b ha hb hab,
    ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure hπae _,Measure.ae_smul_measure hρae _⟩,
    (hπc.smul_measure ENNReal.ofReal_ne_top).add_measure (hρc.smul_measure ENNReal.ofReal_ne_top),
    (hπL.smul_measure ENNReal.ofReal_ne_top).add_measure (hρL.smul_measure ENNReal.ofReal_ne_top),?_⟩
  rw [finite_mixture_integral π ρ _ hπc hρc a b ha hb,
    finite_mixture_integral π ρ _ hπL hρL a b ha hb]
  rfl

theorem finiteCouplingValues_cost_nonneg {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (Ξ : Set E) (P : Measure E) (L : E → EReal) (v : ℝ×ℝ)
    (hv : v∈finiteCouplingValues Ξ P L) : 0 ≤ v.1 := by
  obtain ⟨π,_,_,_,_,_,rfl⟩ := hv
  exact integral_nonneg (fun w => norm_nonneg _)
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality DupacovaWets.Consistency

theorem expect_eq_integral_toReal_of_finite_ae {Z : Type*} [MeasurableSpace Z]
    (π : Measure Z) (L : Z → EReal) (hi : Integrable (fun z => (L z).toReal) π)
    (hf : ∀ᵐ z ∂π, L z≠⊤ ∧ L z≠⊥) :
    expect π L = ((∫ z, (L z).toReal ∂π : ℝ) : EReal) := by
  have hae : L =ᵐ[π] (fun z => ((L z).toReal : EReal)) :=
    hf.mono (fun z hz => (EReal.coe_toReal hz.1 hz.2).symm)
  have he : expect π L=expect π (fun z => ((L z).toReal : EReal)) := by
    apply le_antisymm
    · exact expect_mono π _ _ (hae.mono fun z hz => hz.le)
    · exact expect_mono π _ _ (hae.mono fun z hz => hz.ge)
  rw [he,expect_eq_integral π _ hi]

theorem finite_coupling_project_budget {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Ξ : Set E) (hΞ : MeasurableSet Ξ) (P : Measure E) (L : E → EReal)
    (hL : Measurable L) (v : ℝ×ℝ) (hv : v∈finiteCouplingValues Ξ P L)
    (ε : ℝ) (hvε : v.1 ≤ ε) :
    ∃ Q : Measure E, Q∈ambiguitySet ε 1 Ξ P ∧ expect Q L=(v.2 : EReal) := by
  obtain ⟨π,hπ,hπP,hπae,hπc,hπL,rfl⟩ := hv
  letI := hπ
  let Q : Measure E := π.map Prod.fst
  have hQ : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI := hQ
  have hs : Q Ξᶜ=0 := by
    change (π.map Prod.fst) Ξᶜ=0
    rw [Measure.map_apply measurable_fst hΞ.compl]
    have hax : ∀ᵐ w ∂π, w.1∈Ξ := hπae.mono (fun w hw => hw.1)
    rw [ae_iff] at hax
    exact hax
  have hc : wassersteinDistance 1 Q P ≤ ENNReal.ofReal ε := by
    rw [wasserstein_one_eq]
    apply le_trans (iInf_le _ π)
    apply le_trans (iInf_le _ ⟨rfl,hπP⟩)
    rw [←ofReal_integral_eq_lintegral_ofReal hπc (Filter.Eventually.of_forall fun w => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hvε
  refine ⟨Q,⟨measure_univ,hs,hc⟩,?_⟩
  have he := expect_map π Prod.fst L measurable_fst hL
  rw [he]
  exact expect_eq_integral_toReal_of_finite_ae π (fun w => L w.1) hπL
    (hπae.mono (fun w hw => hw.2))

theorem finiteCouplingValues_le_worstCase {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (Ξ : Set E) (hΞ : MeasurableSet Ξ) (L : E → EReal) (hL : Measurable L)
    (ξhat : Fin N → E) (v : ℝ×ℝ)
    (hv : v∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L)
    (ε : ℝ) (hvε : v.1 ≤ ε) : (v.2 : EReal) ≤ worstCaseExpectation ε Ξ ξhat L := by
  obtain ⟨Q,hQ,he⟩ := finite_coupling_project_budget Ξ hΞ (empiricalDistribution ξhat) L hL v hv ε hvε
  rw [←he]
  exact le_iSup₂_of_le Q hQ le_rfl
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
theorem finite_supporting_multiplier (C : Set (ℝ × ℝ)) (hC : Convex ℝ C)
    (δ V c0 L : ℝ) (hδ : c0 < δ) (hbase : (c0, L) ∈ C)
    (hbudget : ∀ z ∈ C, z.1 < δ → z.2 ≤ V) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∀ z ∈ C, z.2 ≤ V + γ * (z.1 - δ) := by
  let D : Set (ℝ × ℝ) := Set.Iio δ ×ˢ Set.Ioi V
  have hDconv : Convex ℝ D := (convex_Iio δ).prod (convex_Ioi V)
  have hDopen : IsOpen D := isOpen_Iio.prod isOpen_Ioi
  have hdisj : Disjoint D C := Set.disjoint_left.mpr (by
    intro z hzD hzC
    exact not_lt_of_ge (hbudget z hzC hzD.1) hzD.2)
  obtain ⟨f, k, hD, hCbound⟩ := geometric_hahn_banach_open hDconv hDopen hC hdisj
  let a := f (1, 0)
  let b := f (0, 1)
  have hf (x y : ℝ) : f (x, y) = a * x + b * y := by
    have he : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
    rw [he, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    dsimp [a, b]
    ring
  have ha : 0 ≤ a := by
    by_contra ha
    have han : 0 < -a := neg_pos.mpr (lt_of_not_ge ha)
    let t := (|k - (a * δ + b * (V + 1))| + 1) / (-a)
    have ht : 0 < t := div_pos (by positivity) han
    have hm : (-a) * t = |k - (a * δ + b * (V + 1))| + 1 := by
      dsimp [t]
      exact mul_div_cancel₀ _ han.ne'
    have hd := hD (δ - t, V + 1) (show (δ - t, V + 1) ∈ D from ⟨by change δ - t < δ; linarith, by change V < V + 1; linarith⟩)
    rw [hf] at hd
    nlinarith [le_abs_self (k - (a * δ + b * (V + 1)))]
  have hb : b ≤ 0 := by
    by_contra hb
    have hbp : 0 < b := lt_of_not_ge hb
    let t := (|k - (a * (δ - 1) + b * V)| + 1) / b
    have ht : 0 < t := div_pos (by positivity) hbp
    have hm : b * t = |k - (a * (δ - 1) + b * V)| + 1 := by
      dsimp [t]
      exact mul_div_cancel₀ _ hbp.ne'
    have hd := hD (δ - 1, V + t) (show (δ - 1, V + t) ∈ D from ⟨by change δ - 1 < δ; linarith, by change V < V + t; linarith⟩)
    rw [hf] at hd
    nlinarith [le_abs_self (k - (a * (δ - 1) + b * V))]
  have hbneg : b < 0 := by
    by_contra hbneg
    have hbzero : b = 0 := le_antisymm hb (le_of_not_gt hbneg)
    have hd := hD ((δ+c0) / 2, V + 1) (show ((δ+c0) / 2, V + 1) ∈ D from ⟨by change (δ+c0) / 2 < δ; linarith, by change V < V + 1; linarith⟩)
    have hc := hCbound (c0, L) hbase
    rw [hf, hbzero] at hd hc
    nlinarith
  have hboundary : a * δ + b * V ≤ k := by
    by_contra hle
    have hgap : 0 < a * δ + b * V - k := sub_pos.mpr (lt_of_not_ge hle)
    obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt hgap (a - b)
    have hd := hD (δ - ε, V + ε) (show (δ - ε, V + ε) ∈ D from ⟨by change δ - ε < δ; linarith, by change V < V + ε; linarith⟩)
    rw [hf] at hd
    nlinarith
  refine ⟨a / (-b), div_nonneg ha (neg_nonneg.mpr hb), ?_⟩
  intro z hz
  have hc := hboundary.trans (hCbound z hz)
  have hzeta : (z.1, z.2) = z := Prod.mk.eta
  rw [← hzeta, hf] at hc
  have hn : 0 < -b := neg_pos.mpr hbneg
  have he : V + a / (-b) * (z.1 - δ) = (a * (z.1 - δ) + (-b) * V) / (-b) := by
    field_simp [ne_of_lt hbneg]
    ring
  rw [he]
  apply (le_div_iff₀ hn).mpr
  nlinarith

end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open MeasureTheory WassersteinDRO.Duality
lemma empirical_probability {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (hn : 0 < n) (X : Fin n → Z) : IsProbabilityMeasure (empiricalDistribution X) := by
  constructor
  simp [empiricalDistribution, Measure.smul_apply, Measure.finsetSum_apply]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

lemma empirical_map {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W] {n : ℕ}
    (X : Fin n → Z) (f : Z → W) (hf : Measurable f) :
    (empiricalDistribution X).map f = empiricalDistribution (fun i => f (X i)) := by
  unfold empiricalDistribution
  rw [Measure.map_smul, Measure.map_finset_sum' hf.aemeasurable]
  simp only [Measure.map_dirac' hf]

lemma empirical_lintegral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (f : Z → ENNReal) :
    (∫⁻ z, f z ∂empiricalDistribution X) = (n : ENNReal)⁻¹ * ∑ i, f (X i) := by
  unfold empiricalDistribution
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac]
  rfl

lemma empirical_coupling {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (Y : Fin n → W) :
    IsProbabilityMeasure (empiricalDistribution (fun i => (X i, Y i))) ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.fst = empiricalDistribution X ∧
    (empiricalDistribution (fun i => (X i, Y i))).map Prod.snd = empiricalDistribution Y := by
  refine ⟨empirical_probability hn _, ?_, ?_⟩
  · exact empirical_map _ Prod.fst measurable_fst
  · exact empirical_map _ Prod.snd measurable_snd

lemma empirical_integrable {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Z) (l : Z → ℝ) :
    Integrable l (empiricalDistribution X) := by
  unfold empiricalDistribution
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i hi
    exact integrable_dirac (by simp)
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hn.ne')

lemma empirical_integral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (X : Fin n → Z) (l : Z → ℝ) :
    (∫ z, l z ∂empiricalDistribution X) = (n : ℝ)⁻¹ * ∑ i, l (X i) := by
  unfold empiricalDistribution
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  · intro i hi
    exact integrable_dirac (by simp)


end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassersteinDRO.Duality DupacovaWets.Consistency

theorem empirical_ae_of_samples {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {N : ℕ} (ξhat : Fin N → E)
    (p : E → Prop) (hp : ∀ i, p (ξhat i)) : ∀ᵐ x ∂empiricalDistribution ξhat, p x := by
  unfold empiricalDistribution
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i hi
  rw [ae_dirac_eq]
  exact hp i

theorem empirical_expect_eq_of_finite_samples {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (L : E → EReal) (htop : ∀ i, L (ξhat i) ≠ ⊤) (hbot : ∀ i, L (ξhat i) ≠ ⊥) :
    expect (empiricalDistribution ξhat) L =
      ((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, L (ξhat i)) := by
  let f : E → ℝ := fun x => (L x).toReal
  have hae : L =ᵐ[empiricalDistribution ξhat] (fun x => (f x : EReal)) := by
    apply empirical_ae_of_samples
    intro i
    exact (EReal.coe_toReal (htop i) (hbot i)).symm
  have he : expect (empiricalDistribution ξhat) L =
      expect (empiricalDistribution ξhat) (fun x => (f x : EReal)) := by
    apply le_antisymm
    · exact expect_mono _ _ _ (hae.mono fun x hx => hx.le)
    · exact expect_mono _ _ _ (hae.mono fun x hx => hx.ge)
  rw [he, expect_eq_integral _ f (empirical_integrable hN ξhat f),empirical_integral]
  have hs : (∑ i, L (ξhat i)) = ((∑ i, f (ξhat i) : ℝ) : EReal) := by
    have hh : ∀ i, L (ξhat i) = (f (ξhat i) : EReal) :=
      fun i => (EReal.coe_toReal (htop i) (hbot i)).symm
    simp only [hh]
    exact (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) _ _).symm
  rw [hs,←EReal.coe_mul,one_div]
theorem empirical_expect_eq_of_ne_top_samples {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E)
    (L : E → EReal) (htop : ∀ i, L (ξhat i) ≠ ⊤) :
    expect (empiricalDistribution ξhat) L =
      ((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, L (ξhat i)) := by
  by_cases hb : ∃ i, L (ξhat i) = ⊥
  · obtain ⟨i,hi⟩ := hb
    have hpos : (∫⁻ x, (L x).toENNReal ∂empiricalDistribution ξhat) ≠ ⊤ := by
      rw [empirical_lintegral]
      apply ENNReal.mul_ne_top
      · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne')
      · exact ENNReal.sum_ne_top.mpr (fun j _ => EReal.toENNReal_ne_top_iff.mpr (htop j))
    have hneg : (∫⁻ x, (-L x).toENNReal ∂empiricalDistribution ξhat) = ⊤ := by
      rw [empirical_lintegral]
      have hs : (∑ j : Fin N, (-L (ξhat j)).toENNReal) = ⊤ := by
        apply top_le_iff.mp
        have hh := Finset.single_le_sum (f:=fun j : Fin N => (-L (ξhat j)).toENNReal) (fun j _ => (bot_le : (0 : ENNReal) ≤ (-L (ξhat j)).toENNReal)) (Finset.mem_univ i)
        simpa [hi] using hh
      rw [hs,ENNReal.mul_top]
      simp
    have hs : (∑ j : Fin N, L (ξhat j)) = ⊥ := by
      rw [←Finset.add_sum_erase _ _ (Finset.mem_univ i),hi,EReal.bot_add]
    rw [expect,if_neg hpos,hneg,EReal.coe_ennreal_top,EReal.sub_top,hs]
    symm
    exact EReal.mul_bot_of_pos (by exact_mod_cast (one_div_pos.mpr (Nat.cast_pos.mpr hN)))
  · apply empirical_expect_eq_of_finite_samples hN ξhat L htop
    intro i hi
    exact hb ⟨i,hi⟩

end WassReductionCodex


end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassersteinDRO.Duality

theorem finite_empirical_coupling_mem {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (L : E → EReal) (ξhat x : Fin N → E)
    (hx : ∀ i, x i∈Ξ ∧ L (x i)≠⊤ ∧ L (x i)≠⊥) :
    (((1/(N : ℝ))*∑ i, ‖x i-ξhat i‖),((1/(N : ℝ))*∑ i, (L (x i)).toReal)) ∈
      finiteCouplingValues Ξ (empiricalDistribution ξhat) L := by
  let π := empiricalDistribution (fun i => (x i,ξhat i))
  refine ⟨π,empirical_probability hN _,?_,?_,empirical_integrable hN _ _,empirical_integrable hN _ _,?_⟩
  · exact empirical_map _ Prod.snd measurable_snd
  · exact empirical_ae_of_samples _ _ hx
  · dsimp [π]
    rw [empirical_integral,empirical_integral]
    simp only [one_div]

theorem finiteCouplingValues_nonempty_of_finite_point {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (L : E → EReal) (ξhat : Fin N → E) (x0 : E)
    (hx0 : x0∈Ξ ∧ L x0≠⊤ ∧ L x0≠⊥) :
    (finiteCouplingValues Ξ (empiricalDistribution ξhat) L).Nonempty :=
  ⟨_,finite_empirical_coupling_mem hN Ξ L ξhat (fun _ => x0) (fun _ => hx0)⟩
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality

theorem exists_multiplier_of_strict_finite_coupling {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (Ξ : Set E) (hΞ : MeasurableSet Ξ) (L : E → EReal) (hL : Measurable L)
    (ξhat : Fin N → E) (ε V : ℝ)
    (hupper : worstCaseExpectation ε Ξ ξhat L ≤ (V : EReal))
    (v0 : ℝ×ℝ) (hv0 : v0∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L)
    (hstrict : v0.1 < ε) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ v∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L,
      v.2 ≤ V+lam*(v.1-ε) := by
  apply finite_supporting_multiplier _ (finiteCouplingValues_convex Ξ _ L) ε V v0.1 v0.2 hstrict
  · simpa using hv0
  · intro v hv hc
    have hh := (finiteCouplingValues_le_worstCase Ξ hΞ L hL ξhat v hv ε hc.le).trans hupper
    exact EReal.coe_le_coe_iff.mp hh

theorem finite_tuple_bound_of_multiplier {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (L : E → EReal) (ξhat : Fin N → E) (ε V lam : ℝ)
    (hsupport : ∀ v∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L,
      v.2 ≤ V+lam*(v.1-ε))
    (x : Fin N → E) (hx : ∀ i, x i∈Ξ ∧ L (x i)≠⊤ ∧ L (x i)≠⊥) :
    (∑ i, ((L (x i)).toReal-lam*‖x i-ξhat i‖)) ≤ (N : ℝ)*(V-lam*ε) := by
  have hv := finite_empirical_coupling_mem hN Ξ L ξhat x hx
  have hh := hsupport _ hv
  dsimp only at hh
  have hsum : (∑ i, ((L (x i)).toReal-lam*‖x i-ξhat i‖)) =
      (∑ i, (L (x i)).toReal)-lam*(∑ i, ‖x i-ξhat i‖) := by
    rw [Finset.sum_sub_distrib,Finset.mul_sum]
  rw [hsum]
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hc := mul_le_mul_of_nonneg_left hh hn.le
  have hcalc : (N : ℝ)*((1/(N : ℝ))*∑ i, (L (x i)).toReal) = ∑ i, (L (x i)).toReal := by
    field_simp
  have hcalc2 : (N : ℝ)*(V+lam*((1/(N : ℝ))*∑ i, ‖x i-ξhat i‖-ε)) =
      (N : ℝ)*(V-lam*ε)+lam*∑ i, ‖x i-ξhat i‖ := by
    field_simp
    ring
  rw [hcalc,hcalc2] at hc
  linarith
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex

/-- A finite Cartesian family with a uniform sum bound has coordinatewise
finite upper bounds whose sum preserves that same bound. -/
theorem rectangular_scores_of_sum_bound {N : ℕ} (hN : 0 < N)
    (T : Fin N → Set ℝ) (hne : ∀ i, (T i).Nonempty) (B : ℝ)
    (hbound : ∀ r : Fin N → ℝ, (∀ i, r i∈T i) → (∑ i, r i) ≤ B) :
    ∃ s : Fin N → ℝ, (∀ i r, r∈T i → r ≤ s i) ∧ (∑ i, s i) ≤ B := by
  classical
  choose r0 hr0 using hne
  have hbdd : ∀ i, BddAbove (T i) := by
    intro i
    refine ⟨B-(∑ j ∈ Finset.univ.erase i, r0 j),?_⟩
    intro r hr
    have hu : ∀ j, Function.update r0 i r j ∈ T j := by
      intro j
      by_cases hji : j=i
      · subst j
        simpa using hr
      · simpa [Function.update_of_ne hji] using hr0 j
    have hh := hbound (Function.update r0 i r) hu
    rw [←Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hh
    have hs : (∑ j ∈ Finset.univ.erase i, Function.update r0 i r j) =
        ∑ j ∈ Finset.univ.erase i, r0 j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
    rw [Function.update_self,hs] at hh
    linarith
  let s : Fin N → ℝ := fun i => sSup (T i)
  refine ⟨s,fun i r hr => le_csSup (hbdd i) hr,?_⟩
  by_contra hh
  have hgap : 0 < (∑ i, s i)-B := sub_pos.mpr (lt_of_not_ge hh)
  let η := ((∑ i, s i)-B)/(2*(N : ℝ))
  have hη : 0 < η := by dsimp [η];exact div_pos hgap (by positivity)
  have happ : ∀ i, ∃ r∈T i, s i-η<r := by
    intro i
    exact exists_lt_of_lt_csSup ⟨r0 i,hr0 i⟩ (by dsimp [s];linarith)
  choose r hr hrap using happ
  have hsum : (∑ i, (s i-η)) ≤ ∑ i, r i := Finset.sum_le_sum (fun i _ => (hrap i).le)
  have hu := hbound r hr
  have hcalc : (∑ i, (s i-η)) = (∑ i, s i)-(N : ℝ)*η := by
    rw [Finset.sum_sub_distrib]
    simp
  have hηeq : (2*(N : ℝ))*η = (∑ i, s i)-B := by
    dsimp [η]
    field_simp
  rw [hcalc] at hsum
  nlinarith
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality

theorem program12c_le_of_finite_multiplier {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (L : E → EReal) (ξhat : Fin N → E) (ε V lam : ℝ)
    (hlam : 0 ≤ lam) (hne_top : ∀ x∈Ξ, L x≠⊤)
    (hfinite : ∃ x∈Ξ, L x≠⊥)
    (hsupport : ∀ v∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L,
      v.2 ≤ V+lam*(v.1-ε)) :
    program12cValue ε Ξ ξhat L ≤ (V : EReal) := by
  classical
  let T : Fin N → Set ℝ := fun i =>
    {r | ∃ x∈Ξ, L x≠⊥ ∧ r=(L x).toReal-lam*‖x-ξhat i‖}
  obtain ⟨x0,hx0,hL0⟩ := hfinite
  have hne : ∀ i, (T i).Nonempty := by
    intro i
    exact ⟨_,x0,hx0,hL0,rfl⟩
  have hb : ∀ r : Fin N → ℝ, (∀ i, r i∈T i) →
      (∑ i, r i) ≤ (N : ℝ)*(V-lam*ε) := by
    intro r hr
    choose x hx hbot hval using hr
    have hh := finite_tuple_bound_of_multiplier hN Ξ L ξhat ε V lam hsupport x
      (fun i => ⟨hx i,hne_top (x i) (hx i),hbot i⟩)
    simpa only [hval] using hh
  obtain ⟨s,hupper,hsum⟩ := rectangular_scores_of_sum_bound hN T hne _ hb
  have he : ∀ i, (⨆ x∈Ξ, L x-((lam*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
    intro i
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    by_cases hbot : L x=⊥
    · simp [hbot]
    · have hm : (L x).toReal-lam*‖x-ξhat i‖∈T i := ⟨x,hx,hbot,rfl⟩
      have hh := EReal.coe_le_coe_iff.mpr (hupper i _ hm)
      rw [EReal.coe_sub,EReal.coe_toReal (hne_top x hx) hbot] at hh
      exact hh
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hobj : lam*ε+(1/(N : ℝ))*∑ i, s i ≤ V := by
    have hh := mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hn.le)
    have hc : (1/(N : ℝ))*((N : ℝ)*(V-lam*ε))=V-lam*ε := by field_simp
    rw [hc] at hh
    linarith
  unfold program12cValue
  exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le he
    (iInf_le_of_le hlam (EReal.coe_le_coe_iff.mpr hobj))))
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex

/-- A linearly bounded upper semicontinuous extended-real loss has exact
zero-radius penalized envelopes, including value minus infinity at the sample. -/
theorem envelope_small_of_linear_upper {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat : E) (C A r : ℝ)
    (husc : UpperSemicontinuousAt L xhat)
    (hupper : ∀ x ∈ Ξ, L x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal))
    (hr : L xhat < (r : EReal)) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      (⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal)) ≤ (r : EReal) := by
  have hn : ∀ᶠ x in 𝓝 xhat, L x < (r : EReal) := husc r hr
  obtain ⟨δ,hδ,hlocal⟩ := Metric.eventually_nhds_iff.mp hn
  let B := max 0 ((C-r)/δ)
  let lam := max 0 A+B
  have hB : 0 ≤ B := le_max_left _ _
  have hlam : 0 ≤ lam := add_nonneg (le_max_left _ _) hB
  refine ⟨lam,hlam,?_⟩
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  by_cases hd : ‖x-xhat‖ < δ
  · have hl : L x ≤ (r : EReal) := (hlocal (by simpa [dist_eq_norm] using hd)).le
    have hp : (0 : EReal) ≤ ((lam*‖x-xhat‖ : ℝ) : EReal) := by
      exact EReal.coe_nonneg.mpr (mul_nonneg hlam (norm_nonneg _))
    exact le_trans (by simpa using EReal.sub_le_sub le_rfl hp) hl
  · have hdist : δ ≤ ‖x-xhat‖ := le_of_not_gt hd
    have hfrac : (C-r)/δ ≤ B := le_max_right _ _
    have hCd : C-r ≤ B*δ := (div_le_iff₀ hδ).mp hfrac
    have hBd : B*δ ≤ B*‖x-xhat‖ := mul_le_mul_of_nonneg_left hdist hB
    have hAd : A*‖x-xhat‖ ≤ max 0 A*‖x-xhat‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    have hb : C+A*‖x-xhat‖-lam*‖x-xhat‖ ≤ r := by
      dsimp [lam]
      nlinarith
    have hh := EReal.sub_le_sub (hupper x hx) (le_refl ((lam*‖x-xhat‖ : ℝ) : EReal))
    rw [←EReal.coe_sub] at hh
    exact hh.trans (EReal.coe_le_coe_iff.mpr hb)

theorem envelope_limit_of_linear_upper {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat : E) (hxhat : xhat ∈ Ξ) (C A : ℝ)
    (husc : UpperSemicontinuousAt L xhat)
    (hupper : ∀ x ∈ Ξ, L x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal)) :
    Tendsto (fun lam : ℝ => ⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal))
      atTop (𝓝 (L xhat)) := by
  let F : ℝ → EReal := fun lam => ⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal)
  have hanti : Antitone F := by
    intro a b hab
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply le_trans _ (le_iSup₂_of_le x hx le_rfl)
    apply EReal.sub_le_sub le_rfl
    exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hab (norm_nonneg _))
  have hle : L xhat ≤ ⨅ lam, F lam := by
    apply le_iInf
    intro lam
    have hh : L xhat-((lam*‖xhat-xhat‖ : ℝ) : EReal) ≤ F lam :=
      le_iSup₂_of_le xhat hxhat le_rfl
    simpa [F] using hh
  have hge : (⨅ lam, F lam) ≤ L xhat := by
    by_contra hh
    obtain ⟨r,hr,hri⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
    obtain ⟨lam,_,hlam⟩ := envelope_small_of_linear_upper Ξ L xhat C A r husc hupper hr
    exact (not_le_of_gt hri) ((iInf_le F lam).trans hlam)
  have he : (⨅ lam, F lam)=L xhat := le_antisymm hge hle
  rw [←he]
  exact tendsto_atTop_iInf hanti
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem ereal_neg_upper {α : Type*} [TopologicalSpace α] (f : α → EReal)
    (hf : LowerSemicontinuous f) : UpperSemicontinuous (fun x => -f x) := by
  change LowerSemicontinuous (fun x => OrderDual.toDual (-f x))
  have hg : Continuous (fun t : EReal => OrderDual.toDual (-t)) := continuous_neg
  have hm : Monotone (fun t : EReal => OrderDual.toDual (-t)) := fun x y h => EReal.neg_le_neg_iff.mpr h
  simpa only [Function.comp_def] using hg.comp_lowerSemicontinuous hf hm
 theorem shifted_upperSemicontinuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (k : Fin K) (z : StrongDual ℝ E) (xhat : E) :
    UpperSemicontinuous (fun ξ => ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) := by
  have hl : UpperSemicontinuous (ℓ k) := by
    simpa only [neg_neg] using ereal_neg_upper (fun ξ => -ℓ k ξ) (hA.lsc k)
  have hc : Continuous (fun ξ => ((-z (ξ-xhat) : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp (z.continuous.comp (continuous_id.sub continuous_const)).neg
  have hs := hl.add' hc.upperSemicontinuous (fun ξ =>
    EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _)))
  simpa only [sub_eq_add_neg, EReal.coe_neg] using hs
 theorem shifted_dual_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (L : EReal) : Continuous (fun z : StrongDual ℝ E => L-((z v : ℝ) : EReal)) := by
  have hc : Continuous (fun z : StrongDual ℝ E => ((-z v : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp ((ContinuousLinearMap.apply ℝ ℝ v).continuous.neg)
  have hs : Continuous (fun z : StrongDual ℝ E => L+((-z v : ℝ) : EReal)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (EReal.continuousAt_add (.inr (EReal.coe_ne_bot _)) (.inr (EReal.coe_ne_top _))).comp
      (continuousAt_const.prodMk hc.continuousAt)
  simpa only [sub_eq_add_neg,EReal.coe_neg] using hs
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex

theorem linear_upper_of_convex_epigraph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E → EReal)
    (hne_top : ∀ x, L x ≠ ⊤)
    (hconvex : Convex ℝ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)})
    (x0 : E) (a : ℝ) (ha : L x0=(a : EReal))
    (husc : UpperSemicontinuousAt L x0) :
    ∃ C A : ℝ, 0 ≤ A ∧ ∀ x, L x ≤ ((C+A*‖x-x0‖ : ℝ) : EReal) := by
  have hn : ∀ᶠ x in 𝓝 x0, L x < ((a+1 : ℝ) : EReal) := by
    apply husc
    rw [ha]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨δ,hδ,hlocal⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨a+1,2/δ,by positivity,?_⟩
  intro x
  cases hx : L x using EReal.rec with
  | bot => exact bot_le
  | top => exact False.elim (hne_top x hx)
  | coe b =>
    by_cases hd : ‖x-x0‖ < δ
    · have hb : b < a+1 := EReal.coe_lt_coe_iff.mp (by
        rw [←hx]
        exact hlocal (by simpa [dist_eq_norm] using hd))
      apply EReal.coe_le_coe_iff.mpr
      have hp : 0 ≤ (2/δ)*‖x-x0‖ := by positivity
      linarith
    · have hd0 : 0 < ‖x-x0‖ := lt_of_lt_of_le hδ (le_of_not_gt hd)
      let t : ℝ := δ/(2*‖x-x0‖)
      have ht : 0 < t := by dsimp [t];positivity
      have ht1 : t ≤ 1 := by
        dsimp [t]
        apply (div_le_iff₀ (by positivity)).mpr
        linarith [le_of_not_gt hd]
      have hp0 : (x0,-a) ∈ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)} := by
        change -L x0 ≤ ((-a : ℝ) : EReal)
        simp [ha, EReal.coe_neg]
      have hpx : (x,-b) ∈ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)} := by
        change -L x ≤ ((-b : ℝ) : EReal)
        simp [hx, EReal.coe_neg]
      have hc := hconvex hp0 hpx (sub_nonneg.mpr ht1) ht.le (by ring : (1-t)+t=1)
      change -L ((1-t) • x0+t • x) ≤ (((1-t)*(-a)+t*(-b) : ℝ) : EReal) at hc
      have hvec : (1-t) • x0+t • x-x0 = t • (x-x0) := by module
      have hnorm : ‖(1-t) • x0+t • x-x0‖ = δ/2 := by
        rw [hvec,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
        dsimp [t]
        field_simp
      have hu := (hlocal (y:=(1-t) • x0+t • x) (by
        rw [dist_eq_norm,hnorm];linarith)).le
      have hlow : (((1-t)*a+t*b : ℝ) : EReal) ≤ L ((1-t) • x0+t • x) := by
        have hc' : -L ((1-t) • x0+t • x) ≤ -(((1-t)*a+t*b : ℝ) : EReal) := by
          convert hc using 1 <;> simp only [←EReal.coe_neg] <;> congr 1 <;> ring
        exact EReal.neg_le_neg_iff.mp hc'
      have hb : (1-t)*a+t*b ≤ a+1 := by
        have hh := hlow.trans hu
        exact EReal.coe_le_coe_iff.mp hh
      have htd : t*((2/δ)*‖x-x0‖)=1 := by dsimp [t];field_simp <;> ring
      apply EReal.coe_le_coe_iff.mpr
      have hbx : b ≤ a+(2/δ)*‖x-x0‖ := by nlinarith
      linarith
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex
open WassDDRO.Reduction

theorem maxLoss_upperSemicontinuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ) :
    UpperSemicontinuous (maxLoss ℓ) := by
  intro x r hr
  obtain ⟨q,hq,hqr⟩ := exists_between hr
  have he : ∀ k, ∀ᶠ y in 𝓝 x, ℓ k y < q := by
    intro k
    have hu : UpperSemicontinuous (ℓ k) := by
      simpa only [neg_neg] using ereal_neg_upper (fun y => -ℓ k y) (hA.lsc k)
    exact hu x q (lt_of_le_of_lt (le_iSup (fun k => ℓ k x) k) hq)
  filter_upwards [eventually_all.mpr he] with y hy
  exact lt_of_le_of_lt (iSup_le (fun k => (hy k).le)) hqr

theorem maxLoss_linear_upper {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ) (xhat : E) :
    ∃ C A : ℝ, 0 ≤ A ∧ ∀ x, maxLoss ℓ x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal) := by
  classical
  have hp : ∀ k, ∃ C A : ℝ, 0 ≤ A ∧ ∀ x, ℓ k x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal) := by
    intro k
    obtain ⟨x0,_,hx0⟩ := hA.not_bot_on k
    have ha := EReal.coe_toReal (hA.ne_top k x0) hx0
    have hu : UpperSemicontinuous (ℓ k) := by
      simpa only [neg_neg] using ereal_neg_upper (fun y => -ℓ k y) (hA.lsc k)
    obtain ⟨C,A,hA0,hbound⟩ := linear_upper_of_convex_epigraph (ℓ k) (hA.ne_top k)
      (hA.convex_epigraph k) x0 (ℓ k x0).toReal ha.symm (hu x0)
    refine ⟨C+A*‖xhat-x0‖,A,hA0,?_⟩
    intro x
    have hd : ‖x-x0‖ ≤ ‖x-xhat‖+‖xhat-x0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    apply (hbound x).trans
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_left hd hA0]
  choose C A hA0 hbound using hp
  refine ⟨∑ k, |C k|, ∑ k, A k,Finset.sum_nonneg (fun k _ => hA0 k),?_⟩
  intro x
  apply iSup_le
  intro k
  have hc : C k ≤ ∑ j, |C j| := (le_abs_self _).trans
    (Finset.single_le_sum (f:=fun j : Fin K => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ k))
  have ha : A k ≤ ∑ j, A j := Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_univ k)
  apply (hbound k x).trans
  exact EReal.coe_le_coe_iff.mpr (add_le_add hc (mul_le_mul_of_nonneg_right ha (norm_nonneg _)))

theorem maxLoss_envelope_limit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (xhat : E) (hxhat : xhat ∈ Ξ) :
    Tendsto (fun lam : ℝ => ⨆ x ∈ Ξ, maxLoss ℓ x-((lam*‖x-xhat‖ : ℝ) : EReal))
      atTop (𝓝 (maxLoss ℓ xhat)) := by
  obtain ⟨C,A,_,hupper⟩ := maxLoss_linear_upper Ξ ℓ hA xhat
  exact envelope_limit_of_linear_upper Ξ (maxLoss ℓ) xhat hxhat C A
    (maxLoss_upperSemicontinuous Ξ ℓ hA xhat) (fun x _ => hupper x)
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency
 theorem coupling_upper {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (Q P : Measure E) (π : Measure (E×E)) (L : E → EReal) (ψ : E → ℝ) (lam : ℝ)
    (hL : Measurable L) (hψ : Integrable ψ P)
    (hm : π.map Prod.fst=Q ∧ π.map Prod.snd=P)
    (hcost : (∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π) ≠ ⊤)
    (hbound : ∀ᵐ w ∂π, L w.1 ≤ ((lam*‖w.1-w.2‖+ψ w.2 : ℝ) : EReal)) :
    expect Q L ≤ ((lam*(∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π).toReal+
      ∫ y, ψ y ∂P : ℝ) : EReal) := by
  have hc : Measurable (fun w : E×E => ‖w.1-w.2‖) := (measurable_fst.sub measurable_snd).norm
  have hi : Integrable (fun w : E×E => ‖w.1-w.2‖) π :=
    (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => norm_nonneg (w.1-w.2))).mp hcost
  have hp : Integrable ψ (π.map Prod.snd) := by rw [hm.2];exact hψ
  have hs : Integrable (fun w : E×E => ψ w.2) π := hp.comp_measurable measurable_snd
  have hb : Integrable (fun w : E×E => lam*‖w.1-w.2‖+ψ w.2) π := (hi.const_mul lam).add hs
  have he : expect Q L=expect π (fun w => L w.1) := by
    rw [←hm.1]
    exact expect_map π Prod.fst L measurable_fst hL
  rw [he]
  have hup := expect_le_integrable_upper π (fun w => L w.1) _ hb hbound
  have hsnd : (∫ w : E×E, ψ w.2 ∂π) = ∫ y, ψ y ∂P := by
    rw [←hm.2]
    symm
    exact integral_map measurable_snd.aemeasurable hp.aestronglyMeasurable
  have hreal : (∫ w : E×E, lam*‖w.1-w.2‖+ψ w.2 ∂π) =
      lam*(∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π).toReal+∫ y, ψ y ∂P := by
    rw [integral_add (hi.const_mul lam) hs, integral_const_mul, hsnd,
      integral_eq_lintegral_of_nonneg_ae (f:=fun w : E×E => ‖w.1-w.2‖)
        (Filter.Eventually.of_forall fun w => norm_nonneg (w.1-w.2)) hc.aestronglyMeasurable]
  rwa [hreal] at hup
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
 theorem exists_sample_barrier {E : Type*} {N : ℕ} (ξhat : Fin N → E) (s : Fin N → ℝ) :
    ∃ ψ : E → ℝ, (∀ i, ψ (ξhat i)≤ s i) ∧
      ∀ y ∈ Set.range ξhat, ∃ i, ξhat i=y ∧ ψ y=s i := by
  classical
  have hchoose (y : E) (hy : y ∈ Set.range ξhat) :
      ∃ i, ξhat i=y ∧ ∀ j, ξhat j=y → s i≤ s j := by
    obtain ⟨j,hj⟩ := hy
    have hn : (Finset.univ.filter (fun i => ξhat i=y)).Nonempty := ⟨j,by simp [hj]⟩
    obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun i => ξhat i=y)) s hn
    refine ⟨i,(Finset.mem_filter.mp hi).2,?_⟩
    intro j hj
    exact hmin j (by simp [hj])
  choose idx hi hmin using hchoose
  let ψ := fun y => if hy : y ∈ Set.range ξhat then s (idx y hy) else 0
  refine ⟨ψ,?_,?_⟩
  · intro i
    have hy : ξhat i ∈ Set.range ξhat := Set.mem_range_self i
    simp only [ψ,dif_pos hy]
    exact hmin (ξhat i) hy i rfl
  · intro y hy
    refine ⟨idx y hy,hi y hy,?_⟩
    simp only [ψ,dif_pos hy]
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality DupacovaWets.Consistency
 theorem transport_epigraph_upper {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {N : ℕ} (hN : 0<N)
    (Ξ : Set E) (L : E → EReal) (hL : Measurable L) (ξhat : Fin N → E)
    (ε lam : ℝ) (hε : 0≤ε) (hlam : 0≤lam) (s : Fin N → ℝ)
    (he : ∀ i, (⨆ ξ ∈ Ξ, L ξ-((lam*‖ξ-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal))
    (Q : Measure E) (hQ : Q Ξᶜ=0)
    (hbudget : wassersteinDistance 1 Q (empiricalDistribution ξhat)≤ENNReal.ofReal ε) :
    expect Q L ≤ ((lam*ε+(1/(N : ℝ))*∑ i, s i : ℝ) : EReal) := by
  obtain ⟨ψ,hψ,hsel⟩ := exists_sample_barrier ξhat s
  have hiψ := empirical_integrable hN ξhat ψ
  have hav : (∫ y, ψ y ∂empiricalDistribution ξhat) ≤ (1/(N : ℝ))*∑ i, s i := by
    rw [empirical_integral,one_div]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hψ i)) (by positivity)
  have hsupport : (empiricalDistribution ξhat) (Set.range ξhat)ᶜ=0 := by
    simp [empiricalDistribution,Measure.smul_apply,Measure.finsetSum_apply,Measure.dirac_apply',Set.mem_range_self]
  have hupper (η : ℝ) (hη : 0<η) :
      expect Q L ≤ ((lam*(ε+η)+(1/(N : ℝ))*∑ i, s i : ℝ) : EReal) := by
    obtain ⟨π,hm,hc⟩ := exists_coupling_lt_budget_add Q (empiricalDistribution ξhat) ε η hε hη hbudget
    have hcfin : (∫⁻ w, ENNReal.ofReal ‖w.1-w.2‖ ∂π) ≠ ⊤ := (lt_of_lt_of_le hc le_top).ne
    have hx : ∀ᵐ w ∂π, w.1∈Ξ := by
      rw [ae_iff]
      change π (Prod.fst ⁻¹' Ξᶜ)=0
      have ht := π.le_map_apply measurable_fst.aemeasurable Ξᶜ
      rw [hm.1,hQ] at ht
      exact le_antisymm ht bot_le
    have hy : ∀ᵐ w ∂π, w.2∈Set.range ξhat := by
      rw [ae_iff]
      change π (Prod.snd ⁻¹' (Set.range ξhat)ᶜ)=0
      have ht := π.le_map_apply measurable_snd.aemeasurable (Set.range ξhat)ᶜ
      rw [hm.2,hsupport] at ht
      exact le_antisymm ht bot_le
    have hb : ∀ᵐ w ∂π, L w.1≤((lam*‖w.1-w.2‖+ψ w.2 : ℝ) : EReal) := by
      filter_upwards [hx,hy] with w hwx hwy
      obtain ⟨i,hiy,hψy⟩ := hsel w.2 hwy
      have hp : L w.1-((lam*‖w.1-ξhat i‖ : ℝ) : EReal) ≤ (s i : EReal) :=
        le_trans (le_iSup₂_of_le w.1 hwx le_rfl) (he i)
      rw [hiy] at hp
      have hu := (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mp hp
      simpa only [hψy,← EReal.coe_add,add_comm] using hu
    have hg := coupling_upper Q (empiricalDistribution ξhat) π L ψ lam hL hiψ hm hcfin hb
    have hr := mul_le_mul_of_nonneg_left (ENNReal.toReal_lt_of_lt_ofReal hc).le hlam
    exact le_trans hg (EReal.coe_le_coe_iff.mpr (add_le_add hr hav))
  have hη : Tendsto (fun n : ℕ => (1 : ℝ)/(n+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have htR : Tendsto (fun n : ℕ => lam*(ε+(1 : ℝ)/(n+1))+(1/(N : ℝ))*∑ i, s i)
      atTop (𝓝 (lam*ε+(1/(N : ℝ))*∑ i, s i)) := by
    have heR : Tendsto (fun n : ℕ => ε+(1 : ℝ)/(n+1)) atTop (𝓝 ε) := by
      simpa using tendsto_const_nhds.add hη
    exact (tendsto_const_nhds.mul heR).add tendsto_const_nhds
  have ht := (continuous_coe_real_ereal.tendsto (lam*ε+(1/(N : ℝ))*∑ i, s i)).comp htR
  exact isClosed_Ici.mem_of_tendsto ht
    (Eventually.of_forall fun n => hupper ((1 : ℝ)/(n+1)) (by positivity))

end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
 theorem dual_ball_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (lam : ℝ) (hlam : 0≤lam) :
    ∃ z : StrongDual ℝ E, ‖z‖≤lam ∧ z v=lam*‖v‖ ∧
      ∀ w : StrongDual ℝ E, ‖w‖≤lam → w v≤lam*‖v‖ := by
  obtain ⟨g,hg,hv⟩ := exists_dual_vector'' ℝ v
  refine ⟨lam • g, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
    nlinarith [mul_le_mul_of_nonneg_left hg hlam]
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hv, RCLike.ofReal_real_eq_id, id_eq]
  · intro w hw
    calc
      w v ≤ |w v| := le_abs_self _
      _ ≤ ‖w‖*‖v‖ := by simpa only [Real.norm_eq_abs] using w.le_opNorm v
      _ ≤ lam*‖v‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg v)
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
 theorem pointwise_dual_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (lam : ℝ) (hlam : 0≤lam) (L : EReal) :
    L-((lam*‖v‖ : ℝ) : EReal) =
      (⨅ z ∈ {z : StrongDual ℝ E | ‖z‖≤lam}, L-((z v : ℝ) : EReal)) ∧
    ∃ z : StrongDual ℝ E, ‖z‖≤lam ∧ L-((z v : ℝ) : EReal)=L-((lam*‖v‖ : ℝ) : EReal) := by
  obtain ⟨z,hz,he,hbound⟩ := dual_ball_support v lam hlam
  refine ⟨?_,z,hz,?_⟩
  · apply le_antisymm
    · apply le_iInf
      intro w
      apply le_iInf
      intro hw
      exact EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr (hbound w hw))
    · apply iInf_le_of_le z
      apply iInf_le_of_le hz
      rw [he]
  · rw [he]
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem finite_threshold_iff (L : EReal) (r d : ℝ) :
    -L ≤ ((-r-d : ℝ) : EReal) ↔ (r : EReal) ≤ L-(d : EReal) := by
  cases L using EReal.rec <;> simp only [EReal.neg_bot, EReal.neg_top,
    EReal.bot_sub, EReal.top_sub (EReal.coe_ne_top _), top_le_iff, le_bot_iff,
    EReal.coe_ne_top, EReal.coe_ne_bot, not_false_eq_true, false_iff, iff_false,
    ← EReal.coe_neg, ← EReal.coe_sub, EReal.coe_le_coe_iff, bot_le, le_top]
  constructor <;> intro h <;> linarith
 theorem shifted_quasiconcave {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (k : Fin K) (z : StrongDual ℝ E) (xhat : E) :
    QuasiconcaveOn ℝ Ξ (fun ξ => ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) := by
  intro r
  cases r using EReal.rec with
  | bot => simpa using hA.convex
  | top =>
    have he : Ξ ∩ {ξ | (⊤ : EReal) ≤ ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ξ hx
      have hn : ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal) ≠ ⊤ := by
        cases h : ℓ k ξ using EReal.rec
        · simp
        · simp [← EReal.coe_sub]
        · exact False.elim (hA.ne_top k ξ h)
      exact hn (top_le_iff.mp hx.2)
    change Convex ℝ (Ξ ∩ {ξ | (⊤ : EReal) ≤ ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)})
    rw [he]
    exact convex_empty
  | coe r =>
    intro x hx y hy a b ha hb hab
    refine ⟨hA.convex hx.1 hy.1 ha hb hab, ?_⟩
    have hx' : (x,-r-z (x-xhat)) ∈ {p : E×ℝ | -ℓ k p.1 ≤ (p.2 : EReal)} :=
      (finite_threshold_iff (ℓ k x) r (z (x-xhat))).mpr hx.2
    have hy' : (y,-r-z (y-xhat)) ∈ {p : E×ℝ | -ℓ k p.1 ≤ (p.2 : EReal)} :=
      (finite_threshold_iff (ℓ k y) r (z (y-xhat))).mpr hy.2
    have hc := hA.convex_epigraph k hx' hy' ha hb hab
    change -ℓ k (a • x+b • y) ≤
      ((a*(-r-z (x-xhat))+b*(-r-z (y-xhat)) : ℝ) : EReal) at hc
    have hd : a*(-r-z (x-xhat))+b*(-r-z (y-xhat)) = -r-z (a • x+b • y-xhat) := by
      simp only [map_sub,map_add,map_smul,smul_eq_mul]
      linear_combination (-r+z xhat)*hab
    rw [hd] at hc
    exact (finite_threshold_iff (ℓ k (a • x+b • y)) r (z (a • x+b • y-xhat))).mp hc
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem shifted_dual_quasiconvex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set (StrongDual ℝ E)) (hC : Convex ℝ C) (v : E) (L : EReal) :
    QuasiconvexOn ℝ C (fun z => L-((z v : ℝ) : EReal)) := by
  cases L using EReal.rec with
  | bot => intro r;simpa only [EReal.bot_sub,bot_le,Set.sep_true] using hC
  | top =>
    intro r
    by_cases hr : (⊤ : EReal)≤r
    · simpa only [EReal.top_sub (EReal.coe_ne_top _),hr,Set.sep_true] using hC
    · simpa only [EReal.top_sub (EReal.coe_ne_top _),hr,Set.sep_false] using
        (show Convex ℝ (∅ : Set (StrongDual ℝ E)) from convex_empty)
  | coe r =>
    have hc : ConvexOn ℝ C (fun z : StrongDual ℝ E => r-z v) := by
      refine ⟨hC, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hr := congrArg (fun t : ℝ => t*r) hab
      nlinarith
    have hm : Monotone (fun r : ℝ => (r : EReal)) := fun a b h => EReal.coe_le_coe_iff.mpr h
    simpa only [Function.comp_def, ← EReal.coe_sub] using hc.quasiconvexOn.monotone_comp hm

 theorem minimax_dual_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) (xhat : E) (lam : ℝ) (hlam : 0≤lam) :
    (⨆ ξ ∈ Ξ, ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal)) =
      (⨅ z ∈ {z : StrongDual ℝ E | ‖z‖≤lam},
        ⨆ ξ ∈ Ξ, ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) ∧
    ∃ z : StrongDual ℝ E, ‖z‖≤lam ∧
      (⨆ ξ ∈ Ξ, ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)) =
        (⨆ ξ ∈ Ξ, ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal)) := by
  let B := {z : StrongDual ℝ E | ‖z‖≤lam}
  let F := fun (z : StrongDual ℝ E) (ξ : E) => ℓ k ξ-((z (ξ-xhat) : ℝ) : EReal)
  have hB : B=Metric.closedBall (0 : StrongDual ℝ E) lam := by
    ext z
    simp only [B,Set.mem_setOf_eq,Metric.mem_closedBall,dist_zero_right]
  have hne : B.Nonempty := ⟨0,by simpa only [B,Set.mem_setOf_eq,norm_zero] using hlam⟩
  have hc : Convex ℝ B := by rw [hB];exact convex_closedBall 0 lam
  have hk : IsCompact B := by rw [hB];exact isCompact_closedBall 0 lam
  have hsion := Sion.minimax' (f:=F) hne hc hk
    (fun ξ _ => (shifted_dual_continuous (ξ-xhat) (ℓ k ξ)).lowerSemicontinuous.lowerSemicontinuousOn B)
    (fun ξ _ => shifted_dual_quasiconvex B hc (ξ-xhat) (ℓ k ξ)) hA.convex
    (fun z _ => (shifted_upperSemicontinuous Ξ ℓ hA k z xhat).upperSemicontinuousOn Ξ)
    (fun z _ => shifted_quasiconcave Ξ ℓ hA k z xhat)
  have hp (ξ : E) : (⨅ z ∈ B, F z ξ)=ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal) :=
    (pointwise_dual_ball (ξ-xhat) lam hlam (ℓ k ξ)).1.symm
  have he : (⨆ ξ ∈ Ξ, ℓ k ξ-((lam*‖ξ-xhat‖ : ℝ) : EReal)) = ⨅ z ∈ B, ⨆ ξ ∈ Ξ, F z ξ := by
    simpa only [hp] using hsion.symm
  have hlow : LowerSemicontinuous (fun z => ⨆ ξ ∈ Ξ, F z ξ) :=
    lowerSemicontinuous_iSup (fun ξ => lowerSemicontinuous_iSup (fun _ =>
      (shifted_dual_continuous (ξ-xhat) (ℓ k ξ)).lowerSemicontinuous))
  obtain ⟨z,hz,hmin⟩ := hlow.lowerSemicontinuousOn B |>.exists_isMinOn hne hk
  have hv : (⨅ w ∈ B, ⨆ ξ ∈ Ξ, F w ξ) = ⨆ ξ ∈ Ξ, F z ξ := by
    apply le_antisymm
    · exact iInf_le_of_le z (iInf_le_of_le hz le_rfl)
    · exact le_iInf₂ hmin
  refine ⟨he,z,hz,?_⟩
  rw [he,hv]
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem iSup_sub_real {α : Sort*} (f : α → EReal) (c : ℝ) :
    (⨆ i, f i)-(c : EReal) = ⨆ i, f i-(c : EReal) := by
  have hs {a b : EReal} : a-(c : EReal)≤b ↔ a≤b+(c : EReal) :=
    EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c)) (.inl (EReal.coe_ne_top c))
  apply le_antisymm
  · apply hs.mpr
    apply iSup_le
    intro i
    exact hs.mp (le_iSup (fun i => f i-(c : EReal)) i)
  · apply iSup_le
    intro i
    exact EReal.sub_le_sub (le_iSup f i) le_rfl
 theorem conjugate_neg_sign {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (Ξ : Set E) (ℓ : E → EReal) (z : StrongDual ℝ E) (xhat : E) :
    conjOn Ξ (fun ξ => -ℓ ξ) (-z) - (((-z) xhat : ℝ) : EReal) =
      ⨆ ξ ∈ Ξ, ℓ ξ-((z (ξ-xhat) : ℝ) : EReal) := by
  rw [conjOn,iSup_sub_real]
  congr 1
  funext ξ
  rw [iSup_sub_real]
  congr 1
  funext hξ
  cases h : ℓ ξ using EReal.rec <;>
    simp only [neg_apply, map_sub, EReal.neg_bot, EReal.neg_top,
      EReal.sub_top, EReal.sub_bot (EReal.coe_ne_bot _), EReal.top_sub (EReal.coe_ne_top _), EReal.bot_sub,
      ← EReal.coe_neg, ← EReal.coe_sub]
  congr 1
  ring
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem envelope_to_conjugate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] {K N : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (lam : ℝ) (hlam : 0≤lam) (s : Fin N → ℝ)
    (h : ∀ i, (⨆ ξ ∈ Ξ, maxLoss ℓ ξ-((lam*‖ξ-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal)) :
    ∃ z : Fin N → Fin K → StrongDual ℝ E,
      (∀ i k, conjOn Ξ (fun ξ => -ℓ k ξ) (z i k)-((z i k (ξhat i) : ℝ) : EReal) ≤ (s i : EReal)) ∧
      ∀ i k, ‖z i k‖≤lam := by
  classical
  choose z hz he using (fun (i : Fin N) (k : Fin K) => (minimax_dual_ball Ξ ℓ hA k (ξhat i) lam hlam).2)
  refine ⟨fun i k => -z i k, ?_, ?_⟩
  · intro i k
    rw [conjugate_neg_sign,he i k]
    apply iSup_le
    intro ξ
    apply iSup_le
    intro hξ
    have hp : ℓ k ξ ≤ maxLoss ℓ ξ := le_iSup (fun j => ℓ j ξ) k
    exact le_trans (EReal.sub_le_sub hp le_rfl)
      (le_trans (le_iSup₂_of_le ξ hξ le_rfl) (h i))
  · intro i k
    simpa only [norm_neg] using hz i k
 theorem conjugate_to_envelope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K N : ℕ} (hK : 0<K) (hN : 0<N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (ξhat : Fin N → E) (lam : ℝ) (s : Fin N → ℝ)
    (z : Fin N → Fin K → StrongDual ℝ E)
    (hc : ∀ i k, conjOn Ξ (fun ξ => -ℓ k ξ) (z i k)-((z i k (ξhat i) : ℝ) : EReal) ≤ (s i : EReal))
    (hn : ∀ i k, ‖z i k‖≤lam) :
    0≤lam ∧ ∀ i, (⨆ ξ ∈ Ξ, maxLoss ℓ ξ-((lam*‖ξ-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
  have hlam : 0≤lam := le_trans (norm_nonneg (z ⟨0,hN⟩ ⟨0,hK⟩)) (hn _ _)
  refine ⟨hlam, ?_⟩
  intro i
  apply iSup_le
  intro ξ
  apply iSup_le
  intro hξ
  rw [maxLoss,iSup_sub_real]
  apply iSup_le
  intro k
  have hb : ‖-z i k‖≤lam := by simpa only [norm_neg] using hn i k
  have hp := (pointwise_dual_ball (ξ-ξhat i) lam hlam (ℓ k ξ)).1
  rw [hp]
  apply le_trans (iInf_le_of_le (-z i k) (iInf_le_of_le hb le_rfl))
  have he := conjugate_neg_sign Ξ (ℓ k) (-z i k) (ξhat i)
  simp only [neg_neg] at he
  have hci := hc i k
  rw [he] at hci
  exact le_trans (le_iSup₂_of_le ξ hξ le_rfl) hci
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem worstCase_le_program12c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0<N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (ε : ℝ) (hε : 0≤ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)≤program12cValue ε Ξ ξhat (maxLoss ℓ) := by
  have hL : Measurable (maxLoss ℓ) := by
    unfold maxLoss
    exact Measurable.iSup hmeas
  unfold worstCaseExpectation program12cValue
  apply le_iInf
  intro lam
  apply le_iInf
  intro s
  apply le_iInf
  intro he
  apply le_iInf
  intro hlam
  apply iSup_le
  intro Q
  apply iSup_le
  intro hQ
  exact transport_epigraph_upper hN Ξ (maxLoss ℓ) hL ξhat ε lam hε hlam s he Q hQ.2.1 hQ.2.2
 theorem program12c_le_program12f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {K N : ℕ} (hK : 0<K) (hN : 0<N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (ξhat : Fin N → E) (ε : ℝ) :
    program12cValue ε Ξ ξhat (maxLoss ℓ)≤program12fValue ε Ξ ξhat ℓ := by
  unfold program12cValue program12fValue
  apply le_iInf
  intro lam
  apply le_iInf
  intro s
  apply le_iInf
  intro z
  apply le_iInf
  intro hc
  apply le_iInf
  intro hn
  obtain ⟨hlam,he⟩ := conjugate_to_envelope hK hN Ξ ℓ ξhat lam s z hc hn
  exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le he (iInf_le_of_le hlam le_rfl)))
 theorem approximate_reduction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0<K) (hN : 0<N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (ε : ℝ) (hε : 0≤ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)≤program12fValue ε Ξ ξhat ℓ :=
  le_trans (worstCase_le_program12c hN Ξ ℓ hmeas ξhat ε hε)
    (program12c_le_program12f hK hN Ξ ℓ ξhat ε)
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction

theorem exists_program12c_finite_upper {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) :
    ∃ r : ℝ, program12cValue ε Ξ ξhat (maxLoss ℓ) ≤ (r : EReal) := by
  let j : Fin N := ⟨0,hN⟩
  obtain ⟨C,A,hA0,hbound⟩ := maxLoss_linear_upper Ξ ℓ hA (ξhat j)
  let s : Fin N → ℝ := fun i => C+A*‖ξhat i-ξhat j‖
  have he : ∀ i, (⨆ x ∈ Ξ, maxLoss ℓ x-((A*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
    intro i
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    have hh := EReal.sub_le_sub (hbound x) (le_refl ((A*‖x-ξhat i‖ : ℝ) : EReal))
    rw [←EReal.coe_sub] at hh
    apply hh.trans
    apply EReal.coe_le_coe_iff.mpr
    have hd := norm_sub_le_norm_sub_add_norm_sub x (ξhat i) (ξhat j)
    dsimp [s]
    nlinarith [mul_le_mul_of_nonneg_left hd hA0]
  refine ⟨A*ε+(1/(N : ℝ))*∑ i, s i,?_⟩
  unfold program12cValue
  exact iInf_le_of_le A (iInf_le_of_le s (iInf_le_of_le he (iInf_le_of_le hA0 le_rfl)))

theorem program12c_ne_top {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) : program12cValue ε Ξ ξhat (maxLoss ℓ) ≠ ⊤ := by
  obtain ⟨r,hr⟩ := exists_program12c_finite_upper hN Ξ ℓ hA ξhat ε
  exact (lt_of_le_of_lt hr (EReal.coe_lt_top r)).ne

theorem worstCase_ne_top {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (hmeas : ∀ k, Measurable (ℓ k))
    (ξhat : Fin N → E) (ε : ℝ) (hε : 0 ≤ ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) ≠ ⊤ := by
  obtain ⟨r,hr⟩ := exists_program12c_finite_upper hN Ξ ℓ hA ξhat ε
  exact (lt_of_le_of_lt ((worstCase_le_program12c hN Ξ ℓ hmeas ξhat ε hε).trans hr)
    (EReal.coe_lt_top r)).ne
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality

/-- The strict-feasibility case of the original positive-radius equality.
The extra finite-coupling hypothesis is explicit and is not claimed to follow
from Assumption41 for every radius. -/
theorem worstCase_eq_program12c_of_strict_finite_coupling {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {K N : ℕ} (hK : 0 < K) (hN : 0 < N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hmeas : ∀ k, Measurable (ℓ k))
    (ξhat : Fin N → E) (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ)
    (v0 : ℝ×ℝ) (hv0 : v0∈finiteCouplingValues Ξ (empiricalDistribution ξhat) (maxLoss ℓ))
    (hstrict : v0.1 < ε) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)=program12cValue ε Ξ ξhat (maxLoss ℓ) := by
  have hL : Measurable (maxLoss ℓ) := Measurable.iSup hmeas
  have htop := worstCase_ne_top hN Ξ ℓ hA hmeas ξhat ε hε
  have hbot : worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)≠⊥ := by
    intro hh
    have hv := finiteCouplingValues_le_worstCase Ξ hA.closed.measurableSet (maxLoss ℓ)
      hL ξhat v0 hv0 ε hstrict.le
    rw [hh] at hv
    exact (EReal.coe_ne_bot _) (le_bot_iff.mp hv)
  have hreal := EReal.coe_toReal htop hbot
  let V : ℝ := (worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)).toReal
  have hupper : worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) ≤ (V : EReal) := hreal.symm.le
  obtain ⟨lam,hlam,hsupport⟩ := exists_multiplier_of_strict_finite_coupling Ξ
    hA.closed.measurableSet (maxLoss ℓ) hL ξhat ε V hupper v0 hv0 hstrict
  let k0 : Fin K := ⟨0,hK⟩
  obtain ⟨x0,hx0,hL0⟩ := hA.not_bot_on k0
  have hn0 : maxLoss ℓ x0≠⊥ := by
    intro hh
    have hl := le_iSup (fun k => ℓ k x0) k0
    change ℓ k0 x0 ≤ maxLoss ℓ x0 at hl
    rw [hh] at hl
    exact hL0 (le_bot_iff.mp hl)
  have hp := program12c_le_of_finite_multiplier hN Ξ (maxLoss ℓ) ξhat ε V lam hlam
    (fun x _ => iSup_ne_top (fun k => hA.ne_top k x)) ⟨x0,hx0,hn0⟩ hsupport
  exact le_antisymm (worstCase_le_program12c hN Ξ ℓ hmeas ξhat ε hε) (hp.trans hreal.le)
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction

theorem program12c_eq_bot_of_cost_gap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) (d : Fin N → ℝ)
    (hd : ∀ i x, x∈Ξ → maxLoss ℓ x≠⊥ → d i≤‖x-ξhat i‖)
    (hgap : ε < (1/(N : ℝ))*∑ i, d i) :
    program12cValue ε Ξ ξhat (maxLoss ℓ)=⊥ := by
  classical
  have hg : ∀ i, ∃ C A : ℝ, 0 ≤ A ∧
      ∀ x, maxLoss ℓ x ≤ ((C+A*‖x-ξhat i‖ : ℝ) : EReal) :=
    fun i => maxLoss_linear_upper Ξ ℓ hA (ξhat i)
  choose C A hA0 hupper using hg
  let a : ℝ := ∑ i, A i
  have ha : 0 ≤ a := Finset.sum_nonneg (fun i _ => hA0 i)
  have hai : ∀ i, A i≤a := fun i => Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_univ i)
  have hb (r : ℝ) : program12cValue ε Ξ ξhat (maxLoss ℓ) ≤ (r : EReal) := by
    let D : ℝ := (1/(N : ℝ))*∑ i, d i-ε
    have hD : 0 < D := sub_pos.mpr hgap
    let B : ℝ := a*ε+(1/(N : ℝ))*∑ i, C i
    let t : ℝ := max 0 ((B-r)/D)
    have ht : 0 ≤ t := le_max_left _ _
    have htr : B-r≤t*D := (div_le_iff₀ hD).mp (le_max_right _ _)
    let lam := a+t
    let s : Fin N → ℝ := fun i => C i-t*d i
    have he : ∀ i, (⨆ x∈Ξ, maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
      intro i
      apply iSup_le
      intro x
      apply iSup_le
      intro hx
      by_cases hbot : maxLoss ℓ x=⊥
      · simp [hbot]
      · have hh := EReal.sub_le_sub (hupper i x) (le_refl ((lam*‖x-ξhat i‖ : ℝ) : EReal))
        rw [←EReal.coe_sub] at hh
        apply hh.trans
        apply EReal.coe_le_coe_iff.mpr
        have hnorm := norm_nonneg (x-ξhat i)
        have hcost := mul_le_mul_of_nonneg_left (hd i x hx hbot) ht
        have hAi := mul_le_mul_of_nonneg_right (hai i) hnorm
        dsimp [lam,s]
        nlinarith
    have hobj : lam*ε+(1/(N : ℝ))*∑ i, s i ≤ r := by
      have hs : (∑ i, s i)=(∑ i, C i)-t*(∑ i, d i) := by
        dsimp [s]
        rw [Finset.sum_sub_distrib,Finset.mul_sum]
      rw [hs]
      have heq : lam*ε+(1/(N : ℝ))*((∑ i, C i)-t*(∑ i, d i)) = B-t*D := by
        dsimp [lam,B,D]
        ring
      rw [heq]
      nlinarith
    unfold program12cValue
    exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le he
      (iInf_le_of_le (add_nonneg ha ht) (EReal.coe_le_coe_iff.mpr hobj))))
  apply le_antisymm _ bot_le
  by_contra hh
  obtain ⟨r,_,hr⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
  exact (not_le_of_gt hr) (hb r)

theorem worstCase_and_program_eq_bot_of_cost_gap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) (hε : 0 ≤ ε) (d : Fin N → ℝ)
    (hd : ∀ i x, x∈Ξ → maxLoss ℓ x≠⊥ → d i≤‖x-ξhat i‖)
    (hgap : ε < (1/(N : ℝ))*∑ i, d i) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)=⊥ ∧ program12cValue ε Ξ ξhat (maxLoss ℓ)=⊥ := by
  have hp := program12c_eq_bot_of_cost_gap Ξ ℓ hA ξhat ε d hd hgap
  have hw := worstCase_le_program12c hN Ξ ℓ hmeas ξhat ε hε
  rw [hp] at hw
  exact ⟨le_bot_iff.mp hw,hp⟩
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality

def finiteLossDomain {E : Type*} (Ξ : Set E) (L : E → EReal) : Set E :=
  Ξ ∩ {x | L x≠⊥}

noncomputable def finiteDomainCost {E : Type*} [NormedAddCommGroup E] {N : ℕ}
    (Ξ : Set E) (L : E → EReal) (ξhat : Fin N → E) : ℝ :=
  (1/(N : ℝ))*∑ i, Metric.infDist (ξhat i) (finiteLossDomain Ξ L)

theorem finite_domain_distance_lower {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat x : E) (hx : x∈Ξ) (hLx : L x≠⊥) :
    Metric.infDist xhat (finiteLossDomain Ξ L) ≤ ‖x-xhat‖ := by
  have hh := Metric.infDist_le_dist_of_mem (x:=xhat) (show x∈finiteLossDomain Ξ L from ⟨hx,hLx⟩)
  rw [dist_comm,dist_eq_norm] at hh
  exact hh

theorem strict_finite_coupling_of_gt_domain_cost {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [MeasurableSingletonClass E] {N : ℕ} (hN : 0 < N)
    (Ξ : Set E) (L : E → EReal) (ξhat : Fin N → E) (ε : ℝ)
    (hne_top : ∀ x∈Ξ, L x≠⊤) (hfinite : (finiteLossDomain Ξ L).Nonempty)
    (hε : finiteDomainCost Ξ L ξhat < ε) :
    ∃ v∈finiteCouplingValues Ξ (empiricalDistribution ξhat) L, v.1 < ε := by
  classical
  let D := finiteDomainCost Ξ L ξhat
  let η : ℝ := (ε-D)/2
  have hη : 0 < η := by dsimp [η,D];linarith
  have hp : ∀ i, ∃ x∈finiteLossDomain Ξ L,
      ‖x-ξhat i‖ < Metric.infDist (ξhat i) (finiteLossDomain Ξ L)+η := by
    intro i
    obtain ⟨x,hx,hd⟩ := (Metric.infDist_lt_iff hfinite).mp
      (show Metric.infDist (ξhat i) (finiteLossDomain Ξ L) <
        Metric.infDist (ξhat i) (finiteLossDomain Ξ L)+η by linarith)
    refine ⟨x,hx,?_⟩
    simpa [dist_comm,dist_eq_norm] using hd
  choose x hx hdist using hp
  have hv := finite_empirical_coupling_mem hN Ξ L ξhat x
    (fun i => ⟨(hx i).1,hne_top (x i) (hx i).1,(hx i).2⟩)
  refine ⟨_,hv,?_⟩
  dsimp only
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hh : (1/(N : ℝ))*(∑ i, ‖x i-ξhat i‖) ≤
      (1/(N : ℝ))*(∑ i, (Metric.infDist (ξhat i) (finiteLossDomain Ξ L)+η)) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hdist i).le))
    (one_div_nonneg.mpr hn.le)
  have he : (1/(N : ℝ))*(∑ i, (Metric.infDist (ξhat i) (finiteLossDomain Ξ L)+η)) = D+η := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp [D,finiteDomainCost]
    field_simp
  rw [he] at hh
  exact lt_of_le_of_lt hh (by dsimp [η];dsimp [D] at hε ⊢;linarith)

theorem positive_reduction_except_domain_boundary {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ)
    (hne : ε≠finiteDomainCost Ξ (maxLoss ℓ) ξhat) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)=program12cValue ε Ξ ξhat (maxLoss ℓ) := by
  by_cases hlt : ε < finiteDomainCost Ξ (maxLoss ℓ) ξhat
  · have hh := worstCase_and_program_eq_bot_of_cost_gap hN Ξ ℓ hmeas hA ξhat ε hε
      (fun i => Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ)))
      (fun i x hx hn => finite_domain_distance_lower Ξ (maxLoss ℓ) (ξhat i) x hx hn) hlt
    rw [hh.1,hh.2]
  · have hgt : finiteDomainCost Ξ (maxLoss ℓ) ξhat < ε := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    let k0 : Fin K := ⟨0,hK⟩
    obtain ⟨x0,hx0,hL0⟩ := hA.not_bot_on k0
    have hn0 : maxLoss ℓ x0≠⊥ := by
      intro hh
      have hl := le_iSup (fun k => ℓ k x0) k0
      change ℓ k0 x0 ≤ maxLoss ℓ x0 at hl
      rw [hh] at hl
      exact hL0 (le_bot_iff.mp hl)
    obtain ⟨v,hv,hvε⟩ := strict_finite_coupling_of_gt_domain_cost hN Ξ (maxLoss ℓ) ξhat ε
      (fun x _ => iSup_ne_top (fun k => hA.ne_top k x)) ⟨x0,hx0,hn0⟩ hgt
    exact worstCase_eq_program12c_of_strict_finite_coupling hK hN Ξ ℓ hmeas ξhat ε hε hA v hv hvε
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem strict_finite_points {E : Type*} [NormedAddCommGroup E] {N : ℕ}
    (hN : 0 < N) (Ξ : Set E) (L : E → EReal) (ξhat : Fin N → E) (ε : ℝ)
    (hfinite : (WassReductionCodex.finiteLossDomain Ξ L).Nonempty)
    (hε : WassReductionCodex.finiteDomainCost Ξ L ξhat<ε) :
    ∃ x : Fin N → E, (∀ i, x i∈WassReductionCodex.finiteLossDomain Ξ L) ∧
      (1/(N : ℝ))*(∑ i, ‖x i-ξhat i‖)<ε := by
  classical
  let D := WassReductionCodex.finiteDomainCost Ξ L ξhat
  let η : ℝ := (ε-D)/2
  have hη : 0 < η := by dsimp [η,D];linarith
  have hp : ∀ i, ∃ x∈WassReductionCodex.finiteLossDomain Ξ L,
      ‖x-ξhat i‖<Metric.infDist (ξhat i) (WassReductionCodex.finiteLossDomain Ξ L)+η := by
    intro i
    obtain ⟨x,hx,hd⟩ := (Metric.infDist_lt_iff hfinite).mp
      (show Metric.infDist (ξhat i) (WassReductionCodex.finiteLossDomain Ξ L)<
        Metric.infDist (ξhat i) (WassReductionCodex.finiteLossDomain Ξ L)+η by linarith)
    refine ⟨x,hx,?_⟩
    simpa [dist_comm,dist_eq_norm] using hd
  choose x hx hdist using hp
  refine ⟨x,hx,?_⟩
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hh : (1/(N : ℝ))*(∑ i, ‖x i-ξhat i‖)≤
      (1/(N : ℝ))*(∑ i, (Metric.infDist (ξhat i) (WassReductionCodex.finiteLossDomain Ξ L)+η)) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hdist i).le))
      (one_div_nonneg.mpr hn.le)
  have he : (1/(N : ℝ))*(∑ i, (Metric.infDist (ξhat i) (WassReductionCodex.finiteLossDomain Ξ L)+η))=D+η := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp [D,WassReductionCodex.finiteDomainCost]
    field_simp
  rw [he] at hh
  exact lt_of_le_of_lt hh (by dsimp [η];dsimp [D] at hε ⊢;linarith)

theorem finite_loss_domain_nonempty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {K : ℕ}
    (hK : 0 < K) (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ) :
    (WassReductionCodex.finiteLossDomain Ξ (maxLoss ℓ)).Nonempty := by
  obtain ⟨x,hx,hb⟩ := hA.not_bot_on ⟨0,hK⟩
  refine ⟨x,hx,?_⟩
  intro h
  have hh : ℓ ⟨0,hK⟩ x ≤ maxLoss ℓ x := le_iSup (fun k => ℓ k x) ⟨0,hK⟩
  rw [h] at hh
  exact hb (le_bot_iff.mp hh)

theorem finitePerspectiveValues_strict_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (ξhat : Fin N → E) (ε : ℝ)
    (hε : WassReductionCodex.finiteDomainCost Ξ (maxLoss ℓ) ξhat<ε) :
    ∃ v∈finitePerspectiveValues Ξ ℓ ξhat, v.1<ε := by
  obtain ⟨x,hx,hcost⟩ := strict_finite_points hN Ξ (maxLoss ℓ) ξhat ε
    (finite_loss_domain_nonempty hK Ξ ℓ hA) hε
  have hm := finite_points_perspective_mem hK Ξ ℓ ξhat x (fun i => (hx i).1) hA.ne_top (fun i => (hx i).2)
  exact ⟨_,hm,hcost⟩
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

noncomputable def restrictedLoss {E : Type*} {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (k : Fin K) : E → EReal := by
  classical
  exact fun x => if x∈Ξ then -ℓ k x else ⊤

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {K : ℕ}

theorem restrictedLoss_ne_bot (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) (x : E) : restrictedLoss Ξ ℓ k x≠⊥ := by
  classical
  by_cases hx : x∈Ξ
  · simpa [restrictedLoss,hx] using hA.ne_top k x
  · simp [restrictedLoss,hx]

theorem restrictedLoss_proper (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) : ∃ x, restrictedLoss Ξ ℓ k x≠⊤ := by
  obtain ⟨x,hx,hb⟩ := hA.not_bot_on k
  refine ⟨x,?_⟩
  simpa [restrictedLoss,hx] using hb

theorem restrictedLoss_convex (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) : Convex ℝ {p : E×ℝ | restrictedLoss Ξ ℓ k p.1≤(p.2 : EReal)} := by
  have he : {p : E×ℝ | restrictedLoss Ξ ℓ k p.1≤(p.2 : EReal)} =
      {p : E×ℝ | p.1∈Ξ ∧ -ℓ k p.1≤(p.2 : EReal)} := by
    ext p
    by_cases hp : p.1∈Ξ <;> simp [restrictedLoss,hp,top_le_iff]
  rw [he]
  exact (hA.convex.linear_preimage (LinearMap.fst ℝ E ℝ)).inter (hA.convex_epigraph k)

theorem restrictedLoss_lsc (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (k : Fin K) : LowerSemicontinuous (restrictedLoss Ξ ℓ k) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro t
  by_cases ht : t=⊤
  · simp [ht]
  · have he : (restrictedLoss Ξ ℓ k) ⁻¹' Set.Iic t=Ξ∩(fun x => -ℓ k x) ⁻¹' Set.Iic t := by
      ext x
      by_cases hx : x∈Ξ <;> simp [restrictedLoss,hx,top_le_iff,ht]
    rw [he]
    exact hA.closed.inter ((hA.lsc k).isClosed_preimage t)

theorem restrictedLoss_conjugate (Ξ : Set E) (ℓ : Fin K → E → EReal) (k : Fin K)
    (z : StrongDual ℝ E) : conjOn Set.univ (restrictedLoss Ξ ℓ k) z=conjOn Ξ (fun x => -ℓ k x) z := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    by_cases h : x∈Ξ
    · simpa [restrictedLoss,h,conjOn] using (le_iSup₂_of_le x h le_rfl :
        ((z x : ℝ) : EReal)-(-ℓ k x)≤conjOn Ξ (fun x => -ℓ k x) z)
    · simp [restrictedLoss,h]
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    simpa [restrictedLoss,hx,conjOn] using (le_iSup₂_of_le x (Set.mem_univ x) le_rfl :
      ((z x : ℝ) : EReal)-restrictedLoss Ξ ℓ k x≤conjOn Set.univ (restrictedLoss Ξ ℓ k) z)
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex

theorem functional_product_decompose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : StrongDual ℝ (E×ℝ)) (x : E) (t : ℝ) :
    L (x,t)=L (x,0)+t*L (0,1) := by
  have hp : (x,t)=(x,0)+t • (0,1) := by ext <;> simp
  rw [hp,map_add,map_smul]
  rfl

theorem epigraph_separator_height_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (x0 : E) (a : ℝ) (ha : f x0=(a : EReal))
    (L : StrongDual ℝ (E×ℝ)) (u : ℝ)
    (hL : ∀ p : E×ℝ, f p.1≤(p.2 : EReal) → u<L p) :
    0 ≤ L (0,1) := by
  by_contra hb
  have hn : 0 < -L (0,1) := neg_pos.mpr (lt_of_not_ge hb)
  let t : ℝ := (|u-L (x0,a)|+1)/(-L (0,1))
  have ht : 0 < t := by dsimp [t]; positivity
  have hm : (-L (0,1))*t=|u-L (x0,a)|+1 := by
    dsimp [t]
    exact mul_div_cancel₀ _ hn.ne'
  have he : f (x0 : E)≤((a+t : ℝ) : EReal) := by
    rw [ha]
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  have hp := hL (x0,a+t) he
  rw [functional_product_decompose] at hp
  have hx := functional_product_decompose L x0 a
  nlinarith [le_abs_self (u-L (x0,a)),neg_le_abs (u-L (x0,a))]

theorem positive_height_separator_at_finite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (hc : Convex ℝ {p : E×ℝ | f p.1≤(p.2 : EReal)})
    (hl : LowerSemicontinuous f) (x0 : E) (a r : ℝ) (ha : f x0=(a : EReal)) (hr : r<a) :
    ∃ (L : StrongDual ℝ (E×ℝ)) (u : ℝ),
      0<L (0,1) ∧ L (x0,r)<u ∧ ∀ p : E×ℝ, f p.1≤(p.2 : EReal) → u<L p := by
  have hclosed : IsClosed {p : E×ℝ | f p.1≤(p.2 : EReal)} :=
    hl.isClosed_epigraph.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  have hout : (x0,r)∉{p : E×ℝ | f p.1≤(p.2 : EReal)} := by
    change ¬ f x0≤(r : EReal)
    rw [ha]
    exact not_le_of_gt (EReal.coe_lt_coe_iff.mpr hr)
  obtain ⟨L,u,hpoint,hbound⟩ := geometric_hahn_banach_point_closed hc hclosed hout
  refine ⟨L,u,?_,hpoint,hbound⟩
  have hf := hbound (x0,a) (by change f x0≤(a : EReal);rw [ha])
  rw [functional_product_decompose] at hf hpoint
  by_contra hb
  have hb0 : L (0,1)≤0 := le_of_not_gt hb
  nlinarith
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex

theorem positive_height_separator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (hbot : ∀ x, f x≠⊥) (hproper : ∃ x, f x≠⊤)
    (hc : Convex ℝ {p : E×ℝ | f p.1≤(p.2 : EReal)}) (hl : LowerSemicontinuous f)
    (q : E) (r : ℝ) (hr : (r : EReal)<f q) :
    ∃ (L : StrongDual ℝ (E×ℝ)) (u : ℝ),
      0<L (0,1) ∧ L (q,r)<u ∧ ∀ p : E×ℝ, f p.1≤(p.2 : EReal) → u<L p := by
  obtain ⟨x0,hx0⟩ := hproper
  let a : ℝ := (f x0).toReal
  have ha : f x0=(a : EReal) := (EReal.coe_toReal hx0 (hbot x0)).symm
  obtain ⟨L0,u0,hb0,hpoint0,hbound0⟩ := positive_height_separator_at_finite f hc hl x0 a (a-1) ha (by linarith)
  have hclosed : IsClosed {p : E×ℝ | f p.1≤(p.2 : EReal)} :=
    hl.isClosed_epigraph.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  obtain ⟨L,u,hpoint,hbound⟩ := geometric_hahn_banach_point_closed hc hclosed
    (show (q,r)∉{p : E×ℝ | f p.1≤(p.2 : EReal)} from not_le_of_gt hr)
  have hb := epigraph_separator_height_nonneg f x0 a ha L u hbound
  obtain ⟨δ,hδ,hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr hpoint) (|L0 (q,r)-u0|+1)
  have hmul : δ*(L0 (q,r)-u0) ≤ δ*(|L0 (q,r)-u0|+1) := by
    apply mul_le_mul_of_nonneg_left _ hδ.le
    linarith [le_abs_self (L0 (q,r)-u0)]
  refine ⟨L+δ • L0,u+δ*u0,?_,?_,?_⟩
  · change 0<L (0,1)+δ*L0 (0,1)
    positivity
  · change L (q,r)+δ*L0 (q,r)<u+δ*u0
    nlinarith
  · intro p hp
    change u+δ*u0<L p+δ*L0 p
    exact add_lt_add (hbound p hp) (mul_lt_mul_of_pos_left (hbound0 p hp) hδ)
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex

theorem affine_minorant_above {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (hbot : ∀ x, f x≠⊥) (hproper : ∃ x, f x≠⊤)
    (hc : Convex ℝ {p : E×ℝ | f p.1≤(p.2 : EReal)}) (hl : LowerSemicontinuous f)
    (q : E) (r : ℝ) (hr : (r : EReal)<f q) :
    ∃ (z : StrongDual ℝ E) (c : ℝ),
      (∀ x, ((z x+c : ℝ) : EReal)≤f x) ∧ r<z q+c := by
  obtain ⟨L,u,hb,hpoint,hbound⟩ := positive_height_separator f hbot hproper hc hl q r hr
  let b : ℝ := L (0,1)
  let z : StrongDual ℝ E := (-1/b) • (L.comp (ContinuousLinearMap.inl ℝ E ℝ))
  let c : ℝ := u/b
  have hval : ∀ x, z x+c=(u-L (x,0))/b := by
    intro x
    change (-1/b)*L (x,0)+u/b=(u-L (x,0))/b
    field_simp [ne_of_gt hb] <;> ring
  refine ⟨z,c,?_,?_⟩
  · intro x
    cases hx : f x using EReal.rec with
    | bot => exact False.elim (hbot x hx)
    | top => exact le_top
    | coe a =>
      apply EReal.coe_le_coe_iff.mpr
      rw [hval]
      apply (div_le_iff₀ hb).mpr
      have hh := hbound (x,a) (by change f x≤(a : EReal);rw [hx])
      rw [functional_product_decompose] at hh
      change u<L (x,0)+a*b at hh
      linarith
  · rw [hval]
    apply (lt_div_iff₀ hb).mpr
    rw [functional_product_decompose] at hpoint
    change L (q,0)+r*b<u at hpoint
    linarith
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem conjugate_le_of_affine_minorant {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → EReal) (z : StrongDual ℝ E) (c : ℝ)
    (h : ∀ x, ((z x+c : ℝ) : EReal)≤f x) : conjOn Set.univ f z≤((-c : ℝ) : EReal) := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  calc
    _ ≤ ((z x : ℝ) : EReal)-((z x+c : ℝ) : EReal) := EReal.sub_le_sub le_rfl (h x)
    _ = ((-c : ℝ) : EReal) := by
      rw [←EReal.coe_sub]
      congr 1
      ring

theorem biconjugate_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → EReal) (hbot : ∀ x, f x≠⊥) (hproper : ∃ x, f x≠⊤)
    (hc : Convex ℝ {p : E×ℝ | f p.1≤(p.2 : EReal)}) (hl : LowerSemicontinuous f)
    (q : E) : (⨆ z : StrongDual ℝ E, ((z q : ℝ) : EReal)-conjOn Set.univ f z)=f q := by
  apply le_antisymm
  · apply iSup_le
    intro z
    have hz : ((z q : ℝ) : EReal)-f q≤conjOn Set.univ f z := le_iSup₂_of_le q (Set.mem_univ q) le_rfl
    cases hq : f q using EReal.rec with
    | bot => exact False.elim (hbot q hq)
    | top => exact le_top
    | coe a =>
      rw [hq] at hz
      calc
        _ ≤ ((z q : ℝ) : EReal)-(((z q : ℝ) : EReal)-(a : EReal)) := EReal.sub_le_sub le_rfl hz
        _ = (a : EReal) := by
          rw [←EReal.coe_sub,←EReal.coe_sub]
          congr 1
          ring
  · by_contra h
    have hs : (⨆ z : StrongDual ℝ E, ((z q : ℝ) : EReal)-conjOn Set.univ f z)<f q := lt_of_not_ge h
    obtain ⟨r,hsr,hr⟩ := EReal.exists_between_coe_real hs
    obtain ⟨z,c,hm,hqr⟩ := affine_minorant_above f hbot hproper hc hl q r hr
    have hconj := conjugate_le_of_affine_minorant f z c hm
    have hz : ((z q+c : ℝ) : EReal)≤((z q : ℝ) : EReal)-conjOn Set.univ f z := by
      calc
        _ = ((z q : ℝ) : EReal)-((-c : ℝ) : EReal) := by
          rw [←EReal.coe_sub]
          congr 1
          ring
        _ ≤ _ := EReal.sub_le_sub le_rfl hconj
    have hh := hz.trans (le_iSup (fun z : StrongDual ℝ E => ((z q : ℝ) : EReal)-conjOn Set.univ f z) z)
    exact not_lt_of_ge hh (hsr.trans (EReal.coe_lt_coe_iff.mpr hqr))
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex

noncomputable def positiveScaleOrderIso (α : ℝ) (hα : 0 < α) : EReal ≃o EReal where
  toFun x := (α : EReal)*x
  invFun x := ((α⁻¹ : ℝ) : EReal)*x
  left_inv x := by
    change ((α⁻¹ : ℝ) : EReal)*((α : EReal)*x)=x
    rw [←mul_assoc,←EReal.coe_mul,inv_mul_cancel₀ hα.ne',EReal.coe_one,one_mul]
  right_inv x := by
    change (α : EReal)*(((α⁻¹ : ℝ) : EReal)*x)=x
    rw [←mul_assoc,←EReal.coe_mul,mul_inv_cancel₀ hα.ne',EReal.coe_one,one_mul]
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      change (α : EReal)*x≤(α : EReal)*y at h
      have hm := mul_le_mul_of_nonneg_left h
        (show (0 : EReal)≤((α⁻¹ : ℝ) : EReal) from by exact_mod_cast (inv_nonneg.mpr hα.le))
      simpa only [←mul_assoc,←EReal.coe_mul,inv_mul_cancel₀ hα.ne',EReal.coe_one,one_mul] using hm
    · intro h
      exact mul_le_mul_of_nonneg_left h (by exact_mod_cast hα.le)

theorem positive_scale_iInf {I : Sort*} (α : ℝ) (hα : 0 < α) (f : I → EReal) :
    (α : EReal)*(⨅ i, f i)=⨅ i, (α : EReal)*f i :=
  (positiveScaleOrderIso α hα).map_iInf f

theorem neg_iSup_ereal {I : Sort*} (f : I → EReal) : -(⨆ i, f i)=⨅ i, -f i :=
  EReal.negOrderIso.map_iSup f
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem positive_perspective_kernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → EReal) (sample q : E) (α : ℝ) (hα : 0 < α) (z : StrongDual ℝ E) :
    ((z (q-α • sample) : ℝ) : EReal)+(α : EReal)*conjOn Set.univ f z =
      (α : EReal)*(conjOn Set.univ f z-((z (sample-α⁻¹ • q) : ℝ) : EReal)) := by
  have hv : z (q-α • sample)=-(α*z (sample-α⁻¹ • q)) := by
    rw [map_sub,map_smul,map_sub,map_smul]
    simp only [smul_eq_mul]
    field_simp [hα.ne'] <;> ring
  rw [EReal.mul_sub_of_nonneg_of_ne_top (by exact_mod_cast hα.le) (EReal.coe_ne_top α),
    hv,EReal.coe_neg,EReal.coe_mul]
  exact add_comm _ _

theorem positive_perspective_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → EReal) (hbot : ∀ x, f x≠⊥) (hproper : ∃ x, f x≠⊤)
    (hc : Convex ℝ {p : E×ℝ | f p.1≤(p.2 : EReal)}) (hl : LowerSemicontinuous f)
    (sample q : E) (α : ℝ) (hα : 0 < α) :
    (⨅ z : StrongDual ℝ E, ((z (q-α • sample) : ℝ) : EReal)+(α : EReal)*conjOn Set.univ f z) =
      -((α : EReal)*f (sample-α⁻¹ • q)) := by
  simp_rw [positive_perspective_kernel f sample q α hα]
  rw [←positive_scale_iInf α hα]
  have hn (z : StrongDual ℝ E) : conjOn Set.univ f z-((z (sample-α⁻¹ • q) : ℝ) : EReal) =
      -(((z (sample-α⁻¹ • q) : ℝ) : EReal)-conjOn Set.univ f z) :=
    by
      simpa only [sub_eq_add_neg,add_comm] using
        (EReal.neg_sub (.inl (EReal.coe_ne_bot (z (sample-α⁻¹ • q))))
          (.inl (EReal.coe_ne_top (z (sample-α⁻¹ • q)))) (y := conjOn Set.univ f z)).symm
  simp_rw [hn]
  rw [←neg_iSup_ereal,biconjugate_eq f hbot hproper hc hl,mul_neg]
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem iInf_dual_eval_eq_bot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : E) (hq : q≠0) : (⨅ z : StrongDual ℝ E, ((z q : ℝ) : EReal))=⊥ := by
  by_contra h
  have hb : (⊥ : EReal)<(⨅ z : StrongDual ℝ E, ((z q : ℝ) : EReal)) :=
    lt_of_le_of_ne bot_le (Ne.symm h)
  obtain ⟨r,_,hr⟩ := EReal.exists_between_coe_real hb
  obtain ⟨g,hgn,hg⟩ := exists_dual_vector'' ℝ q
  have hgq : g q=‖q‖ := by simpa only [RCLike.ofReal_real_eq_id,id_eq] using hg
  have hn : 0<‖q‖ := norm_pos_iff.mpr hq
  let z : StrongDual ℝ E := (-(|r|+1)/‖q‖) • g
  have hz : z q=-(|r|+1) := by
    change (-(|r|+1)/‖q‖)*g q=-(|r|+1)
    rw [hgq,div_mul_cancel₀ _ hn.ne']
  have hzr : ((z q : ℝ) : EReal)<(r : EReal) := by
    rw [hz]
    apply EReal.coe_lt_coe_iff.mpr
    linarith [neg_le_abs r]
  exact not_lt_of_ge (iInf_le (fun z : StrongDual ℝ E => ((z q : ℝ) : EReal)) z) (hzr.trans hr)

theorem zero_perspective_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → EReal) (sample q : E) (α : ℝ) (hα : α=0) :
    (q=0 → (⨅ z : StrongDual ℝ E, ((z (q-α • sample) : ℝ) : EReal)+
      (α : EReal)*conjOn Set.univ f z)=0) ∧
    (q≠0 → (⨅ z : StrongDual ℝ E, ((z (q-α • sample) : ℝ) : EReal)+
      (α : EReal)*conjOn Set.univ f z)=⊥) := by
  constructor
  · intro hq
    simp [hα,hq]
  · intro hq
    simpa [hα] using iInf_dual_eval_eq_bot q hq
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem perspective_cell_constraints {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ) (k : Fin K)
    (sample q : E) (α t : ℝ) (hα : 0 ≤ α)
    (hbound : ∀ z : StrongDual ℝ E, (t : EReal)≤((z (q-α • sample) : ℝ) : EReal)+
      (α : EReal)*conjOn Ξ (fun x => -ℓ k x) z) :
    (α=0 → q=0) ∧ (α≠0 → atom13 sample α q∈Ξ) ∧
    (t : EReal)≤term13 (ℓ k) sample α q := by
  let F : EReal := ⨅ z : StrongDual ℝ E, ((z (q-α • sample) : ℝ) : EReal)+
    (α : EReal)*conjOn Ξ (fun x => -ℓ k x) z
  have hi : (t : EReal)≤F := le_iInf hbound
  have hp (hpos : 0 < α) : F= -((α : EReal)*restrictedLoss Ξ ℓ k (sample-α⁻¹ • q)) := by
    simpa only [restrictedLoss_conjugate] using
      positive_perspective_eq (restrictedLoss Ξ ℓ k) (restrictedLoss_ne_bot Ξ ℓ hA k)
        (restrictedLoss_proper Ξ ℓ hA k) (restrictedLoss_convex Ξ ℓ hA k)
        (restrictedLoss_lsc Ξ ℓ hA k) sample q α hpos
  have hz (hzero : α=0) : (q=0 → F=0) ∧ (q≠0 → F=⊥) := by
    simpa only [restrictedLoss_conjugate] using zero_perspective_eq (restrictedLoss Ξ ℓ k) sample q α hzero
  have hzero : α=0 → q=0 := by
    intro h0
    by_contra hq
    have hh := hi
    rw [(hz h0).2 hq] at hh
    exact not_le_of_gt (EReal.bot_lt_coe t) hh
  have hs : α≠0 → atom13 sample α q∈Ξ := by
    intro hne
    have hpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hne)
    by_contra hmem
    have hraw : sample-α⁻¹ • q∉Ξ := hmem
    have he : F=⊥ := by
      simpa [restrictedLoss,atom13,hraw,EReal.mul_top_of_pos
        (show (0 : EReal)<(α : EReal) from by exact_mod_cast hpos)] using hp hpos
    rw [he] at hi
    exact not_le_of_gt (EReal.bot_lt_coe t) hi
  refine ⟨hzero,hs,?_⟩
  by_cases h0 : α=0
  · have he := (hz h0).1 (hzero h0)
    rw [he] at hi
    simpa [term13,h0] using hi
  · have hpos : 0 < α := lt_of_le_of_ne hα (Ne.symm h0)
    have hraw : sample-α⁻¹ • q∈Ξ := hs h0
    have he : F=(α : EReal)*ℓ k (atom13 sample α q) := by
      simpa [restrictedLoss,atom13,hraw,mul_neg] using hp hpos
    rw [he] at hi
    simpa [term13,h0] using hi
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem coe_double_sum {N K : ℕ} (t : Fin N → Fin K → ℝ) :
    ((∑ i, ∑ k, t i k : ℝ) : EReal)=∑ i, ∑ k, (t i k : EReal) := by
  let toE : ℝ →+ EReal := ⟨⟨Real.toEReal,EReal.coe_zero⟩,EReal.coe_add⟩
  change toE (∑ i, ∑ k, t i k)=∑ i, ∑ k, toE (t i k)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_sum toE _ _)

theorem perspective_arrays_feasible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ) (ξhat : Fin N → E)
    (ε : ℝ) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) (t : Fin N → Fin K → ℝ)
    (hs : ∀ i, ∑ k, α i k=1) (hα : ∀ i k, 0≤α i k)
    (hcost : (1/(N : ℝ))*(∑ i, ∑ k, ‖q i k‖)≤ε)
    (hbound : ∀ i k (z : StrongDual ℝ E), (t i k : EReal)≤
      ((z (q i k-α i k • ξhat i) : ℝ) : EReal)+(α i k : EReal)*conjOn Ξ (fun x => -ℓ k x) z) :
    Feasible13 ε Ξ ξhat α q ∧
      (((1/(N : ℝ))*(∑ i, ∑ k, t i k) : ℝ) : EReal)≤objective13 ξhat ℓ α q := by
  have hc := fun i k => perspective_cell_constraints Ξ ℓ hA k (ξhat i) (q i k) (α i k) (t i k)
    (hα i k) (hbound i k)
  refine ⟨⟨hcost,hs,hα,fun i k => ⟨(hc i k).1,(hc i k).2.1⟩⟩,?_⟩
  unfold objective13
  rw [EReal.coe_mul,coe_double_sum]
  apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast (one_div_nonneg.mpr (Nat.cast_nonneg N)))
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ => (hc i k).2.2))

theorem finitePerspectiveValues_le_program13 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ) (ξhat : Fin N → E)
    (ε : ℝ) (v : ℝ×ℝ) (hv : v∈finitePerspectiveValues Ξ ℓ ξhat) (hε : v.1≤ε) :
    (v.2 : EReal)≤program13Value ε Ξ ξhat ℓ := by
  obtain ⟨α,q,t,hs,hα,hcost,hreward,hbound⟩ := hv
  obtain ⟨hfeasible,hobj⟩ := perspective_arrays_feasible Ξ ℓ hA ξhat ε α q t hs hα (hcost.trans hε) hbound
  calc
    _ ≤ (((1/(N : ℝ))*(∑ i, ∑ k, t i k) : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hreward
    _ ≤ objective13 ξhat ℓ α q := hobj
    _ ≤ program13Value ε Ξ ξhat ℓ :=
      le_iSup_of_le α (le_iSup_of_le q (le_iSup_of_le hfeasible le_rfl))
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem exists_perspective_multiplier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (ξhat : Fin N → E) (ε V : ℝ)
    (hε : WassReductionCodex.finiteDomainCost Ξ (maxLoss ℓ) ξhat<ε)
    (hupper : program13Value ε Ξ ξhat ℓ≤(V : EReal)) :
    ∃ lam : ℝ, 0≤lam ∧ ∀ v∈finitePerspectiveValues Ξ ℓ ξhat, v.2≤V+lam*(v.1-ε) := by
  obtain ⟨v0,hv0,hstrict⟩ := finitePerspectiveValues_strict_point hK hN Ξ ℓ hA ξhat ε hε
  apply WassReductionCodex.finite_supporting_multiplier _ (finitePerspectiveValues_convex Ξ ℓ ξhat)
    ε V v0.1 v0.2 hstrict
  · simpa using hv0
  · intro v hv hc
    exact EReal.coe_le_coe_iff.mp ((finitePerspectiveValues_le_program13 Ξ ℓ hA ξhat ε v hv hc.le).trans hupper)

theorem finite_tuple_bound_of_perspective_multiplier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (ξhat : Fin N → E) (ε V lam : ℝ)
    (hsupport : ∀ v∈finitePerspectiveValues Ξ ℓ ξhat, v.2≤V+lam*(v.1-ε))
    (x : Fin N → E) (hx : ∀ i, x i∈Ξ) (hbot : ∀ i, maxLoss ℓ (x i)≠⊥) :
    (∑ i, ((maxLoss ℓ (x i)).toReal-lam*‖x i-ξhat i‖))≤(N : ℝ)*(V-lam*ε) := by
  have hv := finite_points_perspective_mem hK Ξ ℓ ξhat x hx hA.ne_top hbot
  have hh := hsupport _ hv
  dsimp only at hh
  have hsum : (∑ i, ((maxLoss ℓ (x i)).toReal-lam*‖x i-ξhat i‖)) =
      (∑ i, (maxLoss ℓ (x i)).toReal)-lam*(∑ i, ‖x i-ξhat i‖) := by
    rw [Finset.sum_sub_distrib,Finset.mul_sum]
  rw [hsum]
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hc := mul_le_mul_of_nonneg_left hh hn.le
  have hcalc : (N : ℝ)*((1/(N : ℝ))*(∑ i, (maxLoss ℓ (x i)).toReal))=
      ∑ i, (maxLoss ℓ (x i)).toReal := by field_simp
  have hcalc2 : (N : ℝ)*(V+lam*((1/(N : ℝ))*(∑ i, ‖x i-ξhat i‖)-ε)) =
      (N : ℝ)*(V-lam*ε)+lam*(∑ i, ‖x i-ξhat i‖) := by
    field_simp
    ring
  rw [hcalc,hcalc2] at hc
  linarith
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem program12c_le_of_perspective_multiplier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (ξhat : Fin N → E) (ε V lam : ℝ) (hlam : 0 ≤ lam)
    (hsupport : ∀ v∈finitePerspectiveValues Ξ ℓ ξhat, v.2 ≤ V+lam*(v.1-ε)) :
    WassDDRO.Reduction.program12cValue ε Ξ ξhat (maxLoss ℓ) ≤ (V : EReal) := by
  classical
  let T : Fin N → Set ℝ := fun i =>
    {r | ∃ x∈Ξ, maxLoss ℓ x≠⊥ ∧ r=(maxLoss ℓ x).toReal-lam*‖x-ξhat i‖}
  obtain ⟨x0,hx0,hL0⟩ := finite_loss_domain_nonempty hK Ξ ℓ hA
  have hne : ∀ i, (T i).Nonempty := fun i => ⟨_,x0,hx0,hL0,rfl⟩
  have hb : ∀ r : Fin N → ℝ, (∀ i, r i∈T i) → (∑ i, r i) ≤ (N : ℝ)*(V-lam*ε) := by
    intro r hr
    choose x hx hbot hval using hr
    have hh := finite_tuple_bound_of_perspective_multiplier hK hN Ξ ℓ hA ξhat ε V lam hsupport x hx hbot
    simpa only [hval] using hh
  obtain ⟨s,hupper,hsum⟩ := WassReductionCodex.rectangular_scores_of_sum_bound hN T hne _ hb
  have he : ∀ i, (⨆ x∈Ξ, maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) := by
    intro i
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    by_cases hbot : maxLoss ℓ x=⊥
    · simp [hbot]
    · have hm : (maxLoss ℓ x).toReal-lam*‖x-ξhat i‖∈T i := ⟨x,hx,hbot,rfl⟩
      have hh := EReal.coe_le_coe_iff.mpr (hupper i _ hm)
      have htop : maxLoss ℓ x≠⊤ := iSup_ne_top (fun k => hA.ne_top k x)
      rw [EReal.coe_sub,EReal.coe_toReal htop hbot] at hh
      exact hh
  have hn : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hobj : lam*ε+(1/(N : ℝ))*(∑ i, s i) ≤ V := by
    have hh := mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hn.le)
    have hc : (1/(N : ℝ))*((N : ℝ)*(V-lam*ε))=V-lam*ε := by field_simp
    rw [hc] at hh
    linarith
  unfold WassDDRO.Reduction.program12cValue
  exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le he
    (iInf_le_of_le hlam (EReal.coe_le_coe_iff.mpr hobj))))

theorem program12c_le_of_upper_program13 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (ξhat : Fin N → E) (ε V : ℝ)
    (hε : WassReductionCodex.finiteDomainCost Ξ (maxLoss ℓ) ξhat < ε)
    (hupper : program13Value ε Ξ ξhat ℓ ≤ (V : EReal)) :
    WassDDRO.Reduction.program12cValue ε Ξ ξhat (maxLoss ℓ) ≤ (V : EReal) := by
  obtain ⟨lam,hlam,hsupport⟩ := exists_perspective_multiplier hK hN Ξ ℓ hA ξhat ε V hε hupper
  exact program12c_le_of_perspective_multiplier hK hN Ξ ℓ hA ξhat ε V lam hlam hsupport

theorem program12c_le_program13_of_gt_domain_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (ξhat : Fin N → E) (ε : ℝ)
    (hε : WassReductionCodex.finiteDomainCost Ξ (maxLoss ℓ) ξhat < ε) :
    WassDDRO.Reduction.program12cValue ε Ξ ξhat (maxLoss ℓ) ≤ program13Value ε Ξ ξhat ℓ := by
  cases hv : program13Value ε Ξ ξhat ℓ using EReal.rec with
  | bot =>
    obtain ⟨v,hvC,hstrict⟩ := finitePerspectiveValues_strict_point hK hN Ξ ℓ hA ξhat ε hε
    have hh := finitePerspectiveValues_le_program13 Ξ ℓ hA ξhat ε v hvC hstrict.le
    rw [hv] at hh
    exact False.elim (not_le_of_gt (EReal.bot_lt_coe v.2) hh)
  | top => exact le_top
  | coe V =>
    exact program12c_le_of_upper_program13 hK hN Ξ ℓ hA ξhat ε V hε hv.le
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {K N : ℕ}

def toReductionAssumption (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (h : WassDDRO.Extremal.Assumption41 Ξ ℓ) : WassDDRO.Reduction.Assumption41 Ξ ℓ :=
  ⟨h.convex, h.closed, h.ne_top, h.convex_epigraph, h.lsc, h.not_bot_on⟩

theorem maxLoss_eq (ℓ : Fin K → E → EReal) :
    WassDDRO.Extremal.maxLoss ℓ = WassDDRO.Reduction.maxLoss ℓ := rfl

theorem program12f_eq (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E) (ℓ : Fin K → E → EReal) :
    WassDDRO.Extremal.program12fValue ε Ξ ξhat ℓ = WassDDRO.Reduction.program12fValue ε Ξ ξhat ℓ := rfl

theorem worstCase_eq (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E) (L : E → EReal) :
    WassDDRO.Extremal.worstCaseExpectation ε Ξ ξhat L = WassDDRO.Reduction.worstCaseExpectation ε Ξ ξhat L := rfl
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex

/-- An upper semicontinuous loss attains its maximum on the compact nearest
face of the closure of its finite domain. The maximizing value may be bottom. -/
theorem nearest_finite_domain_max {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (Ξ : Set E) (hΞ : IsClosed Ξ) (L : E → EReal) (hL : UpperSemicontinuous L)
    (hne : (finiteLossDomain Ξ L).Nonempty) (xhat : E) :
    ∃ y∈Ξ, ‖y-xhat‖=Metric.infDist xhat (finiteLossDomain Ξ L) ∧
      y∈closure (finiteLossDomain Ξ L) ∧
      ∀ x∈closure (finiteLossDomain Ξ L),
        ‖x-xhat‖=Metric.infDist xhat (finiteLossDomain Ξ L) → L x≤L y := by
  let S := closure (finiteLossDomain Ξ L)
  let d := Metric.infDist xhat (finiteLossDomain Ξ L)
  let K := S ∩ Metric.sphere xhat d
  have hc : IsCompact K := (isCompact_sphere xhat d).inter_left isClosed_closure
  obtain ⟨z,hz,hdz⟩ := Metric.exists_mem_closure_infDist_eq_dist hne xhat
  have hnK : K.Nonempty := by
    refine ⟨z,hz,?_⟩
    change dist z xhat=d
    dsimp [d]
    rw [dist_comm]
    exact hdz.symm
  obtain ⟨y,hy,hmax⟩ := (hL.upperSemicontinuousOn K).exists_isMaxOn hnK hc
  have hSΞ : S⊆Ξ := closure_minimal (fun x hx => hx.1) hΞ
  refine ⟨y,hSΞ hy.1,?_,hy.1,?_⟩
  · have hs : dist y xhat=d := hy.2
    simpa only [dist_eq_norm] using hs
  · intro x hx hd
    apply hmax
    exact ⟨hx,by change dist x xhat=d;simpa only [dist_eq_norm] using hd⟩
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex

theorem critical_envelope_small {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (Ξ : Set E) (hΞ : IsClosed Ξ) (L : E → EReal) (hL : UpperSemicontinuous L)
    (xhat y : E) (C A : ℝ) (hA : 0 ≤ A)
    (hupper : ∀ x∈Ξ, L x≤((C+A*‖x-xhat‖ : ℝ) : EReal))
    (hmax : ∀ x∈closure (finiteLossDomain Ξ L),
      ‖x-xhat‖=Metric.infDist xhat (finiteLossDomain Ξ L) → L x≤L y)
    (r : ℝ) (hr : L y < (r : EReal)) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ lam' : ℝ, lam≤lam' →
      (⨆ x∈Ξ, L x-((lam'*‖x-xhat‖ : ℝ) : EReal)) ≤
        ((r-lam'*Metric.infDist xhat (finiteLossDomain Ξ L) : ℝ) : EReal) := by
  classical
  let d := Metric.infDist xhat (finiteLossDomain Ξ L)
  let T := Ξ ∩ {x | (r : EReal)≤L x}
  have hcost (x : E) (hx : x∈Ξ) (hb : L x≠⊥) : d≤‖x-xhat‖ :=
    finite_domain_distance_lower Ξ L xhat x hx hb
  have hlow (lam' : ℝ) (hlam : 0 ≤ lam') (x : E) (hx : x∈Ξ)
      (hb : L x≠⊥) (hl : L x≤(r : EReal)) :
      L x-((lam'*‖x-xhat‖ : ℝ) : EReal) ≤ ((r-lam'*d : ℝ) : EReal) := by
    have hh := EReal.sub_le_sub hl (EReal.coe_le_coe_iff.mpr
      (mul_le_mul_of_nonneg_left (hcost x hx hb) hlam))
    simpa only [←EReal.coe_sub] using hh
  by_cases hn : T.Nonempty
  · have hTc : IsClosed T := hΞ.inter (hL.isClosed_preimage (r : EReal))
    obtain ⟨z,hz,hzdist⟩ := hTc.exists_infDist_eq_dist hn xhat
    let q := Metric.infDist xhat T
    have hzbot : L z≠⊥ := by
      intro hh
      have hrz : (r : EReal)≤L z := hz.2
      rw [hh] at hrz
      exact (EReal.coe_ne_bot r) (le_bot_iff.mp hrz)
    have hzq : ‖z-xhat‖=q := by
      have hh := hzdist.symm
      rw [dist_comm,dist_eq_norm] at hh
      exact hh
    have hq : d<q := by
      have hdq : d≤q := by rw [←hzq];exact hcost z hz.1 hzbot
      by_contra hh
      have he : q=d := le_antisymm (le_of_not_gt hh) hdq
      have hzS : z∈closure (finiteLossDomain Ξ L) := subset_closure ⟨hz.1,hzbot⟩
      have hl := hmax z hzS (by rw [hzq,he])
      exact (not_le_of_gt hr) ((show (r : EReal)≤L z from hz.2).trans hl)
    let t : ℝ := max 0 ((C+A*d-r)/(q-d))
    have ht : 0 ≤ t := le_max_left _ _
    have htr : C+A*d-r≤t*(q-d) := (div_le_iff₀ (sub_pos.mpr hq)).mp (le_max_right _ _)
    refine ⟨A+t,add_nonneg hA ht,?_⟩
    intro lam' hlam
    have hlam0 : 0 ≤ lam' := le_trans (add_nonneg hA ht) hlam
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    by_cases hb : L x=⊥
    · simp [hb]
    · by_cases hl : L x≤(r : EReal)
      · exact hlow lam' hlam0 x hx hb hl
      · have hxT : x∈T := ⟨hx,(lt_of_not_ge hl).le⟩
        have hqx : q≤‖x-xhat‖ := by
          have hh := Metric.infDist_le_dist_of_mem (x:=xhat) hxT
          rw [dist_comm,dist_eq_norm] at hh
          exact hh
        have hg := le_trans hq.le hqx
        have htlam : t≤lam'-A := by linarith
        have hp1 := mul_le_mul_of_nonneg_left (sub_le_sub_right hqx d) ht
        have hp2 := mul_le_mul_of_nonneg_right htlam (sub_nonneg.mpr hg)
        have hh := EReal.sub_le_sub (hupper x hx) (le_refl ((lam'*‖x-xhat‖ : ℝ) : EReal))
        rw [←EReal.coe_sub] at hh
        apply hh.trans
        apply EReal.coe_le_coe_iff.mpr
        nlinarith
  · refine ⟨0,le_rfl,?_⟩
    intro lam' hlam
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    by_cases hb : L x=⊥
    · simp [hb]
    · have hl : L x≤(r : EReal) := by
        by_contra hh
        exact hn ⟨x,hx,(lt_of_not_ge hh).le⟩
      exact hlow lam' hlam x hx hb hl
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex
open WassDDRO.Reduction

lemma ereal_sum_ne_top {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊤) : (∑ i ∈ s, f i) ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact EReal.add_ne_top (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

lemma tendsto_ereal_finset_sum {α ι : Type*} (F : Filter α) (s : Finset ι)
    (f : ι → α → EReal) (a : ι → EReal)
    (ha : ∀ i ∈ s, a i ≠ ⊤) (hf : ∀ i ∈ s, Tendsto (f i) F (𝓝 (a i))) :
    Tendsto (fun x => ∑ i ∈ s, f i x) F (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0 : EReal)) F (𝓝 0))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have hs := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hc := EReal.continuousAt_add (p:=(a i, ∑ j ∈ s, a j)) (.inl (ha i (Finset.mem_insert_self _ _)))
      (.inr (ereal_sum_ne_top s a (fun j hj => ha j (Finset.mem_insert_of_mem hj))))
    exact hc.tendsto.comp ((hf i (Finset.mem_insert_self _ _)).prodMk_nhds hs)

theorem envelope_average_limit {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] {K N : ℕ}
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ) :
    Tendsto (fun lam : ℝ => ((1 / (N : ℝ) : ℝ) : EReal) *
      ∑ i, (⨆ x ∈ Ξ, maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal)))
      atTop (𝓝 (((1 / (N : ℝ) : ℝ) : EReal) * (∑ i, maxLoss ℓ (ξhat i)))) := by
  have ht := tendsto_ereal_finset_sum atTop Finset.univ
    (fun i (lam : ℝ) => ⨆ x ∈ Ξ, maxLoss ℓ x-((lam*‖x-ξhat i‖ : ℝ) : EReal))
    (fun i => maxLoss ℓ (ξhat i))
    (fun i _ => iSup_ne_top (fun k => hA.ne_top k (ξhat i)))
    (fun i _ => maxLoss_envelope_limit Ξ ℓ hA (ξhat i) (hξ i))
  exact EReal.Tendsto.const_mul ht (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))
end WassReductionCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace WassReductionCodex

theorem exists_real_scores_lt_average {N : ℕ} (a : Fin N → EReal)
    (hne_top : ∀ i, a i ≠ ⊤) (r : ℝ)
    (hr : ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, a i) < (r : EReal)) :
    ∃ s : Fin N → ℝ, (∀ i, a i < (s i : EReal)) ∧ (1/(N : ℝ))*∑ i, s i < r := by
  classical
  let s : Fin N → ℕ → ℝ := fun i n => if a i=⊥ then -(n : ℝ) else (a i).toReal+1/(n+1)
  have hscore : ∀ i n, a i < (s i n : EReal) := by
    intro i n
    by_cases hb : a i=⊥
    · simpa only [s,if_pos hb,hb] using EReal.bot_lt_coe (-(n : ℝ))
    · dsimp only [s]
      rw [if_neg hb,←EReal.coe_toReal (hne_top i) hb]
      apply EReal.coe_lt_coe_iff.mpr
      simpa using (Nat.one_div_pos_of_nat (n:=n) : (0 : ℝ)<1/(n+1))
  have ht : ∀ i, Tendsto (fun n => (s i n : EReal)) atTop (𝓝 (a i)) := by
    intro i
    by_cases hb : a i=⊥
    · simp only [s,hb,if_pos]
      exact EReal.tendsto_coe_nhds_bot_iff.mpr
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
    · simp only [s,if_neg hb]
      rw [←EReal.coe_toReal (hne_top i) hb]
      apply continuous_coe_real_ereal.continuousAt.tendsto.comp
      simpa using (tendsto_const_nhds (x:=(a i).toReal)).add
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hsum := tendsto_ereal_finset_sum atTop Finset.univ
    (fun i n => (s i n : EReal)) a (fun i _ => hne_top i) (fun i _ => ht i)
  have hav := EReal.Tendsto.const_mul (a:=((1/(N : ℝ) : ℝ) : EReal)) hsum
    (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))
  have hev : ∀ᶠ n : ℕ in atTop,
      ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, (s i n : EReal)) < (r : EReal) :=
    hav.eventually (isOpen_Iio.mem_nhds hr)
  obtain ⟨n,hn⟩ := hev.exists
  refine ⟨fun i => s i n,fun i => hscore i n,?_⟩
  have hs : (∑ i, (s i n : EReal)) = ((∑ i, s i n : ℝ) : EReal) :=
    (map_sum (⟨⟨Real.toEReal,EReal.coe_zero⟩,EReal.coe_add⟩ : ℝ →+ EReal) _ _).symm
  rw [hs,←EReal.coe_mul] at hn
  exact EReal.coe_lt_coe_iff.mp hn
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction

theorem critical_program_le_nearest_average {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    {K N : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat y : Fin N → E)
    (hmax : ∀ i, ∀ x∈closure (finiteLossDomain Ξ (maxLoss ℓ)),
      ‖x-ξhat i‖=Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ)) →
      maxLoss ℓ x ≤ maxLoss ℓ (y i)) :
    program12cValue (finiteDomainCost Ξ (maxLoss ℓ) ξhat) Ξ ξhat (maxLoss ℓ) ≤
      ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, maxLoss ℓ (y i)) := by
  classical
  by_contra hh
  obtain ⟨r,hr,hrp⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
  obtain ⟨R,hR,havg⟩ := exists_real_scores_lt_average (fun i => maxLoss ℓ (y i))
    (fun i => iSup_ne_top (fun k => hA.ne_top k (y i))) r hr
  have hp : ∀ i, ∃ lam : ℝ, 0 ≤ lam ∧ ∀ lam' : ℝ, lam≤lam' →
      (⨆ x∈Ξ, maxLoss ℓ x-((lam'*‖x-ξhat i‖ : ℝ) : EReal)) ≤
        ((R i-lam'*Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ)) : ℝ) : EReal) := by
    intro i
    obtain ⟨C,A,hA0,hupper⟩ := maxLoss_linear_upper Ξ ℓ hA (ξhat i)
    exact critical_envelope_small Ξ hA.closed (maxLoss ℓ)
      (maxLoss_upperSemicontinuous Ξ ℓ hA) (ξhat i) (y i) C A hA0
      (fun x _ => hupper x) (hmax i) (R i) (hR i)
  choose lam hnonneg hbound using hp
  let Λ : ℝ := ∑ i, lam i
  let s : Fin N → ℝ := fun i => R i-Λ*Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ))
  have hΛ : 0 ≤ Λ := Finset.sum_nonneg (fun i _ => hnonneg i)
  have he : ∀ i, (⨆ x∈Ξ, maxLoss ℓ x-((Λ*‖x-ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal) :=
    fun i => hbound i Λ (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i))
  have hobj : Λ*finiteDomainCost Ξ (maxLoss ℓ) ξhat+(1/(N : ℝ))*∑ i, s i =
      (1/(N : ℝ))*∑ i, R i := by
    dsimp [s,finiteDomainCost]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum]
    ring
  have hprog : program12cValue (finiteDomainCost Ξ (maxLoss ℓ) ξhat) Ξ ξhat (maxLoss ℓ) ≤
      (((1/(N : ℝ))*∑ i, R i : ℝ) : EReal) := by
    unfold program12cValue
    apply iInf_le_of_le Λ
    apply iInf_le_of_le s
    apply iInf_le_of_le he
    apply iInf_le_of_le hΛ
    rw [hobj]
  exact (not_le_of_gt hrp) (hprog.trans (EReal.coe_le_coe_iff.mpr havg.le))
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction WassersteinDRO.Duality DupacovaWets.Consistency

theorem empirical_law_budget {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (hN : 0 < N) (Ξ : Set E) (ξhat y : Fin N → E)
    (hy : ∀ i, y i∈Ξ) (ε : ℝ)
    (hc : (1/(N : ℝ))*∑ i, ‖y i-ξhat i‖ ≤ ε) :
    empiricalDistribution y∈ambiguitySet ε 1 Ξ (empiricalDistribution ξhat) := by
  have hQ := empirical_probability hN y
  letI := hQ
  have hs : (empiricalDistribution y) Ξᶜ=0 := by
    simp [empiricalDistribution,Measure.smul_apply,Measure.finsetSum_apply,hy]
  obtain ⟨_,hfst,hsnd⟩ := empirical_coupling hN y ξhat
  have hb : wassersteinDistance 1 (empiricalDistribution y) (empiricalDistribution ξhat) ≤ ENNReal.ofReal ε := by
    rw [wasserstein_one_eq]
    apply le_trans (iInf_le _ (empiricalDistribution (fun i => (y i,ξhat i))))
    apply le_trans (iInf_le _ ⟨hfst,hsnd⟩)
    rw [←ofReal_integral_eq_lintegral_ofReal (empirical_integrable hN _ _)
      (Filter.Eventually.of_forall fun w => norm_nonneg _),empirical_integral]
    apply ENNReal.ofReal_le_ofReal
    simpa only [one_div] using hc
  exact ⟨measure_univ,hs,hb⟩

theorem empirical_law_value_le_worstCase {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {N : ℕ} (hN : 0 < N) (Ξ : Set E) (L : E → EReal) (ξhat y : Fin N → E)
    (hy : ∀ i, y i∈Ξ) (hne_top : ∀ i, L (y i)≠⊤) (ε : ℝ)
    (hc : (1/(N : ℝ))*∑ i, ‖y i-ξhat i‖ ≤ ε) :
    ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, L (y i)) ≤ worstCaseExpectation ε Ξ ξhat L := by
  have hmem := empirical_law_budget hN Ξ ξhat y hy ε hc
  have he := empirical_expect_eq_of_ne_top_samples hN y L hne_top
  rw [←he]
  exact le_iSup₂_of_le (empiricalDistribution y) hmem le_rfl
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open WassDDRO.Reduction

theorem worstCase_eq_program12c_full {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)=program12cValue ε Ξ ξhat (maxLoss ℓ) := by
  classical
  by_cases hne : ε≠finiteDomainCost Ξ (maxLoss ℓ) ξhat
  · exact positive_reduction_except_domain_boundary hK hN Ξ ℓ hmeas ξhat ε hε hA hne
  · have he : ε=finiteDomainCost Ξ (maxLoss ℓ) ξhat := not_ne_iff.mp hne
    let k0 : Fin K := ⟨0,hK⟩
    obtain ⟨x0,hx0,hL0⟩ := hA.not_bot_on k0
    have hn0 : maxLoss ℓ x0≠⊥ := by
      intro hh
      have hl := le_iSup (fun k => ℓ k x0) k0
      change ℓ k0 x0 ≤ maxLoss ℓ x0 at hl
      rw [hh] at hl
      exact hL0 (le_bot_iff.mp hl)
    have hp : ∀ i, ∃ y∈Ξ, ‖y-ξhat i‖=Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ)) ∧
        y∈closure (finiteLossDomain Ξ (maxLoss ℓ)) ∧
        ∀ x∈closure (finiteLossDomain Ξ (maxLoss ℓ)),
          ‖x-ξhat i‖=Metric.infDist (ξhat i) (finiteLossDomain Ξ (maxLoss ℓ)) →
          maxLoss ℓ x ≤ maxLoss ℓ y := by
      intro i
      exact nearest_finite_domain_max Ξ hA.closed (maxLoss ℓ)
        (maxLoss_upperSemicontinuous Ξ ℓ hA) ⟨x0,hx0,hn0⟩ (ξhat i)
    choose y hy hdist hcl hmax using hp
    have hav := empirical_law_value_le_worstCase hN Ξ (maxLoss ℓ) ξhat y hy
      (fun i => iSup_ne_top (fun k => hA.ne_top k (y i))) ε (by
        rw [he]
        simp only [hdist,finiteDomainCost]
        exact le_rfl)
    have hprog := critical_program_le_nearest_average Ξ ℓ hA ξhat y hmax
    rw [←he] at hprog
    exact le_antisymm (worstCase_le_program12c hN Ξ ℓ hmeas ξhat ε hε) (hprog.trans hav)
end WassReductionCodex

end

section
set_option autoImplicit false
namespace WassReductionCodex
open WassDDRO.Reduction
 theorem program12c_eq_program12f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] {K N : ℕ} (hK : 0<K) (hN : 0<N)
    (Ξ : Set E) (ℓ : Fin K → E → EReal) (hA : Assumption41 Ξ ℓ)
    (ξhat : Fin N → E) (ε : ℝ) :
    program12cValue ε Ξ ξhat (maxLoss ℓ)=program12fValue ε Ξ ξhat ℓ := by
  unfold program12cValue program12fValue
  apply le_antisymm
  · apply le_iInf
    intro lam
    apply le_iInf
    intro s
    apply le_iInf
    intro z
    apply le_iInf
    intro hc
    apply le_iInf
    intro hn
    obtain ⟨hlam,he⟩ := conjugate_to_envelope hK hN Ξ ℓ ξhat lam s z hc hn
    exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le he (iInf_le_of_le hlam le_rfl)))
  · apply le_iInf
    intro lam
    apply le_iInf
    intro s
    apply le_iInf
    intro he
    apply le_iInf
    intro hlam
    obtain ⟨z,hc,hn⟩ := envelope_to_conjugate Ξ ℓ hA ξhat lam hlam s he
    exact iInf_le_of_le lam (iInf_le_of_le s (iInf_le_of_le z
      (iInf_le_of_le hc (iInf_le_of_le hn le_rfl))))
end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex

theorem weighted_rows_probability {Z : Type*} [MeasurableSpace Z] {N K : ℕ}
    (hN : 0 < N) (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z)
    (ha : ∀ i k, 0 ≤ a i k) (hs : ∀ i, ∑ k, a i k = 1) :
    IsProbabilityMeasure ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)) := by
  have hr : ∀ i, (∑ k, ENNReal.ofReal (a i k)) = 1 := by
    intro i
    rw [←ENNReal.ofReal_sum_of_nonneg (fun k _ => ha i k), hs i]
    simp
  constructor
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one, hr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

theorem weighted_rows_ae_support {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (S : Set Z)
    (hx : ∀ i k, a i k ≠ 0 → x i k ∈ S) :
    ∀ᵐ z ∂((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)), z∈S := by
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i hi
  rw [ae_finsetSum_measure_iff]
  intro k hk
  by_cases hz : a i k = 0
  · simp [hz]
  · apply Measure.ae_smul_measure
    rw [ae_dirac_eq]
    exact hx i k hz

theorem discreteQ_probability {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hN : 0 < N) (Ξ : Set E) (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : WassDDRO.Extremal.Feasible13 ε Ξ ξhat α q) :
    IsProbabilityMeasure (WassDDRO.Extremal.discreteQ ξhat α q) :=
  weighted_rows_probability hN α (fun i k => WassDDRO.Extremal.atom13 (ξhat i) (α i k) (q i k)) h.2.2.1 h.2.1

theorem discreteQ_ae_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (Ξ : Set E) (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : WassDDRO.Extremal.Feasible13 ε Ξ ξhat α q) :
    ∀ᵐ x ∂WassDDRO.Extremal.discreteQ ξhat α q, x∈Ξ :=
  weighted_rows_ae_support α (fun i k => WassDDRO.Extremal.atom13 (ξhat i) (α i k) (q i k)) Ξ
    (fun i k => (h.2.2.2 i k).2)
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex

theorem weighted_rows_map {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y] {N K : ℕ}
    (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (f : Z → Y) (hf : Measurable f) :
    ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)).map f =
      (N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (f (x i k)) := by
  simp only [Measure.map_smul, Measure.map_finset_sum' hf.aemeasurable, Measure.map_dirac' hf]

theorem weighted_rows_lintegral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (f : Z → ENNReal) :
    (∫⁻ z, f z ∂((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k))) =
      (N : ENNReal)⁻¹ * ∑ i, ∑ k, ENNReal.ofReal (a i k) * f (x i k) := by
  simp only [lintegral_smul_measure, lintegral_finsetSum_measure, lintegral_dirac, smul_eq_mul]

theorem atom13_weighted_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (sample q : E) (α : ℝ) (hα : 0 ≤ α) (hz : α = 0 → q = 0) :
    α * ‖WassDDRO.Extremal.atom13 sample α q-sample‖ = ‖q‖ := by
  by_cases h : α=0
  · simp [h,hz h]
  · have hp : 0 < α := lt_of_le_of_ne hα (Ne.symm h)
    have he : WassDDRO.Extremal.atom13 sample α q-sample = -(α⁻¹ • q) := by
      unfold WassDDRO.Extremal.atom13
      abel
    rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),←mul_assoc,mul_inv_cancel₀ h,one_mul]

noncomputable def coupling13 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) : Measure (E×E) :=
  (N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (α i k) •
    Measure.dirac (WassDDRO.Extremal.atom13 (ξhat i) (α i k) (q i k),ξhat i)

theorem coupling13_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) :
    (coupling13 ξhat α q).map Prod.fst = WassDDRO.Extremal.discreteQ ξhat α q :=
  weighted_rows_map α _ Prod.fst measurable_fst

theorem coupling13_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (hα : ∀ i k, 0 ≤ α i k) (hs : ∀ i, ∑ k, α i k=1) :
    (coupling13 ξhat α q).map Prod.snd = WassersteinDRO.Duality.empiricalDistribution ξhat := by
  rw [coupling13,weighted_rows_map α _ Prod.snd measurable_snd]
  have hr : ∀ i, (∑ k, ENNReal.ofReal (α i k))=1 := by
    intro i
    rw [←ENNReal.ofReal_sum_of_nonneg (fun k _ => hα i k),hs i]
    simp
  simp only [←Finset.sum_smul,hr,one_smul]
  rfl
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex
open WassDDRO.Extremal WassersteinDRO.Duality

theorem coupling13_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hN : 0 < N) (Ξ : Set E) (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : Feasible13 ε Ξ ξhat α q) :
    (∫⁻ w : E×E, ENNReal.ofReal ‖w.1-w.2‖ ∂coupling13 ξhat α q) =
      ENNReal.ofReal ((1/(N : ℝ)) * ∑ i, ∑ k, ‖q i k‖) := by
  rw [coupling13,weighted_rows_lintegral]
  have hc : ∀ i k, ENNReal.ofReal (α i k) *
      ENNReal.ofReal ‖atom13 (ξhat i) (α i k) (q i k)-ξhat i‖ = ENNReal.ofReal ‖q i k‖ := by
    intro i k
    rw [←ENNReal.ofReal_mul (h.2.2.1 i k),atom13_weighted_cost _ _ _ (h.2.2.1 i k) (h.2.2.2 i k).1]
  simp only [hc]
  have hi : (N : ENNReal)⁻¹=ENNReal.ofReal (1/(N : ℝ)) := by
    rw [one_div,ENNReal.ofReal_inv_of_pos (by exact_mod_cast hN)]
    simp
  have hs : ∀ i, (∑ k, ENNReal.ofReal ‖q i k‖)=ENNReal.ofReal (∑ k, ‖q i k‖) := by
    intro i
    exact (ENNReal.ofReal_sum_of_nonneg (fun k _ => norm_nonneg (q i k))).symm
  simp_rw [hs]
  rw [hi,←ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => norm_nonneg (q i k))),
    ←ENNReal.ofReal_mul (by positivity)]

theorem discreteQ_mem_ball_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hN : 0 < N) (Ξ : Set E) (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : Feasible13 ε Ξ ξhat α q) :
    discreteQ ξhat α q∈ambiguitySet ε 1 Ξ (empiricalDistribution ξhat) := by
  letI := discreteQ_probability hN Ξ ξhat ε α q h
  refine ⟨measure_univ,?_,?_⟩
  · have hs := discreteQ_ae_support Ξ ξhat ε α q h
    exact ae_iff.mp hs
  · have hm : (coupling13 ξhat α q).map Prod.fst=discreteQ ξhat α q ∧
        (coupling13 ξhat α q).map Prod.snd=empiricalDistribution ξhat :=
      ⟨coupling13_first ξhat α q,coupling13_second ξhat α q h.2.2.1 h.2.1⟩
    have hw : wassersteinDistance 1 (discreteQ ξhat α q) (empiricalDistribution ξhat) ≤
        ∫⁻ w : E×E, ENNReal.ofReal ‖w.1-w.2‖ ∂coupling13 ξhat α q := by
      simp only [wassersteinDistance,one_div_one,ENNReal.rpow_one,Real.rpow_one]
      exact iInf_le_of_le (coupling13 ξhat α q) (iInf_le_of_le hm le_rfl)
    rw [coupling13_cost hN Ξ ξhat ε α q h] at hw
    exact hw.trans (ENNReal.ofReal_le_ofReal h.1)
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex

theorem weighted_rows_integrable {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (hN : 0 < N) (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (f : Z → ℝ) :
    Integrable f ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)) := by
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i hi
    apply integrable_finsetSum_measure.mpr
    intro k hk
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne')

theorem weighted_rows_integral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (f : Z → ℝ)
    (ha : ∀ i k, 0 ≤ a i k) :
    (∫ z, f z ∂((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k))) =
      (1/(N : ℝ)) * ∑ i, ∑ k, a i k * f (x i k) := by
  have hint : ∀ i k, Integrable f (ENNReal.ofReal (a i k) • Measure.dirac (x i k)) :=
    fun i k => (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hr : ∀ i, (∫ z, f z ∂(∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k))) =
      ∑ k, a i k*f (x i k) := by
    intro i
    rw [integral_finsetSum_measure (fun k _ => hint i k)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (ha i k)]
    rfl
  rw [integral_smul_measure,integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun k _ => hint i k))]
  simp only [hr,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul,one_div]
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex
open DupacovaWets.Consistency

theorem weighted_rows_expect_of_finite {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (hN : 0 < N) (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z)
    (L : Z → EReal) (ha : ∀ i k, 0 ≤ a i k) (htop : ∀ i k, L (x i k)≠⊤)
    (hbot : ∀ i k, a i k≠0 → L (x i k)≠⊥) :
    expect ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)) L =
      ((1/(N : ℝ) : ℝ) : EReal) * ∑ i, ∑ k, (a i k : EReal)*L (x i k) := by
  let μ : Measure Z := (N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)
  let f : Z → ℝ := fun z => (L z).toReal
  have hae : L =ᵐ[μ] (fun z => (f z : EReal)) := by
    apply weighted_rows_ae_support a x {z | L z=(f z : EReal)}
    intro i k h
    exact (EReal.coe_toReal (htop i k) (hbot i k h)).symm
  have he : expect μ L=expect μ (fun z => (f z : EReal)) :=
    le_antisymm (WassReductionCodex.expect_mono _ _ _ (hae.mono fun z hz => hz.le))
      (WassReductionCodex.expect_mono _ _ _ (hae.mono fun z hz => hz.ge))
  rw [he,WassReductionCodex.expect_eq_integral μ f (weighted_rows_integrable hN a x f),
    weighted_rows_integral a x f ha]
  have hc : ∀ i k, (a i k : EReal)*L (x i k)=((a i k*f (x i k) : ℝ) : EReal) := by
    intro i k
    by_cases h : a i k=0
    · simp [h]
    · rw [←EReal.coe_toReal (htop i k) (hbot i k h),←EReal.coe_mul]
  simp_rw [hc]
  let toE : ℝ →+ EReal := ⟨⟨Real.toEReal,EReal.coe_zero⟩,EReal.coe_add⟩
  have hs : (∑ i, ∑ k, ((a i k*f (x i k) : ℝ) : EReal)) =
      ((∑ i, ∑ k, a i k*f (x i k) : ℝ) : EReal) := by
    calc
      _ = ∑ i, ((∑ k, a i k*f (x i k) : ℝ) : EReal) :=
        Finset.sum_congr rfl (fun i _ => (map_sum toE _ _).symm)
      _ = _ := (map_sum toE _ _).symm
  rw [hs,←EReal.coe_mul]

theorem weighted_rows_expect_of_ne_top {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (hN : 0 < N) (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z)
    (L : Z → EReal) (ha : ∀ i k, 0 ≤ a i k) (htop : ∀ i k, L (x i k)≠⊤) :
    expect ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)) L =
      ((1/(N : ℝ) : ℝ) : EReal) * ∑ i, ∑ k, (a i k : EReal)*L (x i k) := by
  by_cases hb : ∃ i k, a i k≠0 ∧ L (x i k)=⊥
  · obtain ⟨i,k,hak,hL⟩ := hb
    have hap : 0 < a i k := lt_of_le_of_ne (ha i k) (Ne.symm hak)
    have haz : ENNReal.ofReal (a i k)≠0 := (ENNReal.ofReal_pos.mpr hap).ne'
    have hpos : (∫⁻ z, (L z).toENNReal ∂((N : ENNReal)⁻¹ •
        ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)))≠⊤ := by
      rw [weighted_rows_lintegral]
      apply ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne'))
      apply ENNReal.sum_ne_top.mpr
      intro j hj
      apply ENNReal.sum_ne_top.mpr
      intro l hl
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (EReal.toENNReal_ne_top_iff.mpr (htop j l))
    have hneg : (∫⁻ z, (-L z).toENNReal ∂((N : ENNReal)⁻¹ •
        ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)))=⊤ := by
      rw [weighted_rows_lintegral]
      have hk : ENNReal.ofReal (a i k)*(-L (x i k)).toENNReal=⊤ := by
        simp [hL,haz]
      have hs : (∑ j, ∑ l, ENNReal.ofReal (a j l)*(-L (x j l)).toENNReal)=⊤ := by
        apply top_le_iff.mp
        rw [←hk]
        exact (Finset.single_le_sum (f := fun l : Fin K => ENNReal.ofReal (a i l)*(-L (x i l)).toENNReal)
          (fun l _ => bot_le) (Finset.mem_univ k)).trans
          (Finset.single_le_sum (f := fun j : Fin N => ∑ l, ENNReal.ofReal (a j l)*(-L (x j l)).toENNReal)
            (fun j _ => bot_le) (Finset.mem_univ i))
      rw [hs,ENNReal.mul_top]
      simp
    have hterm : (a i k : EReal)*L (x i k)=⊥ := by
      rw [hL]
      exact EReal.mul_bot_of_pos (by exact_mod_cast hap)
    have hs : (∑ j, ∑ l, (a j l : EReal)*L (x j l))=⊥ := by
      have hi : (∑ l, (a i l : EReal)*L (x i l))=⊥ := by
        rw [←Finset.add_sum_erase _ _ (Finset.mem_univ k),hterm,EReal.bot_add]
      rw [←Finset.add_sum_erase _ _ (Finset.mem_univ i),hi,EReal.bot_add]
    rw [expect,if_neg hpos,hneg,EReal.coe_ennreal_top,EReal.sub_top,hs]
    symm
    exact EReal.mul_bot_of_pos (by exact_mod_cast (one_div_pos.mpr (Nat.cast_pos.mpr hN)))
  · apply weighted_rows_expect_of_finite hN a x L ha htop
    intro i k hk hL
    exact hb ⟨i,k,hk,hL⟩
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex
open WassDDRO.Extremal DupacovaWets.Consistency

theorem term13_eq_weight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : E → EReal) (sample q : E) (α : ℝ) :
    term13 L sample α q=(α : EReal)*L (atom13 sample α q) := by
  by_cases h : α=0 <;> simp [term13,h]

theorem discreteQ_expect_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hN : 0 < N) (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (L : E → EReal) (ha : ∀ i k, 0 ≤ α i k) (htop : ∀ i k, L (atom13 (ξhat i) (α i k) (q i k))≠⊤) :
    expect (discreteQ ξhat α q) L =
      ((1/(N : ℝ) : ℝ) : EReal)*∑ i, ∑ k, term13 L (ξhat i) (α i k) (q i k) := by
  simp_rw [term13_eq_weight]
  exact weighted_rows_expect_of_ne_top hN α _ L ha htop

theorem objective13_le_expect_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal) (hne_top : ∀ k x, ℓ k x≠⊤)
    (ξhat : Fin N → E) (ε : ℝ) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : Feasible13 ε Ξ ξhat α q) :
    expect (discreteQ ξhat α q) (maxLoss ℓ) =
      ((1/(N : ℝ) : ℝ) : EReal)*∑ i, ∑ k, term13 (maxLoss ℓ) (ξhat i) (α i k) (q i k) ∧
    objective13 ξhat ℓ α q ≤ expect (discreteQ ξhat α q) (maxLoss ℓ) := by
  have he := discreteQ_expect_eq hN ξhat α q (maxLoss ℓ) h.2.2.1
    (fun i k => iSup_ne_top (fun l => hne_top l (atom13 (ξhat i) (α i k) (q i k))))
  refine ⟨he,?_⟩
  rw [he]
  unfold objective13
  apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast (one_div_nonneg.mpr (Nat.cast_nonneg N)))
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro k hk
  simp only [term13_eq_weight]
  exact mul_le_mul_of_nonneg_left (le_iSup (fun l => ℓ l (atom13 (ξhat i) (α i k) (q i k))) k)
    (by exact_mod_cast h.2.2.1 i k)
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem worstCase_eq_program12f_extremal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : Assumption41 Ξ ℓ) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ)=program12fValue ε Ξ ξhat ℓ := by
  change WassDDRO.Reduction.worstCaseExpectation ε Ξ ξhat (WassDDRO.Reduction.maxLoss ℓ)=
    WassDDRO.Reduction.program12fValue ε Ξ ξhat ℓ
  rw [←WassReductionCodex.program12c_eq_program12f hK hN Ξ ℓ (toReductionAssumption Ξ ℓ hA) ξhat ε]
  exact WassReductionCodex.worstCase_eq_program12c_full hK hN Ξ ℓ hmeas ξhat ε hε (toReductionAssumption Ξ ℓ hA)

theorem program13_le_program12f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : Assumption41 Ξ ℓ) : program13Value ε Ξ ξhat ℓ ≤ program12fValue ε Ξ ξhat ℓ := by
  rw [←worstCase_eq_program12f_extremal hK hN Ξ ℓ hmeas ξhat ε hε hA]
  apply iSup_le
  intro α
  apply iSup_le
  intro q
  apply iSup_le
  intro h
  have hm := discreteQ_mem_ball_full hN Ξ ξhat ε α q h
  have ho := (objective13_le_expect_full hN Ξ ℓ hA.ne_top ξhat ε α q h).2
  exact ho.trans (le_iSup₂_of_le (discreteQ ξhat α q) hm le_rfl)
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem oneHot_norm_sum {E : Type*} [NormedAddCommGroup E] {N K : ℕ}
    (sample x : Fin N → E) (j : Fin N → Fin K) (i : Fin N) :
    (∑ k, ‖oneHotDisplacements sample x j i k‖)=‖x i-sample i‖ := by
  simp [oneHotDisplacements,apply_ite,norm_sub_rev]

theorem oneHot_feasible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (Ξ : Set E) (sample x : Fin N → E) (j : Fin N → Fin K) (ε : ℝ)
    (hx : ∀ i, x i∈Ξ) (hcost : (1/(N : ℝ))*(∑ i, ‖x i-sample i‖) ≤ ε) :
    Feasible13 ε Ξ sample (oneHotWeights j) (oneHotDisplacements sample x j) := by
  refine ⟨?_,oneHot_row_sum j,oneHot_nonneg j,?_⟩
  · simp_rw [oneHot_norm_sum]
    exact hcost
  · intro i k
    by_cases hk : k=j i
    · subst k
      simp only [oneHotWeights,oneHotDisplacements,ite_true]
      have he : atom13 (sample i) 1 (sample i-x i)=x i := by
        unfold atom13
        simp only [inv_one,one_smul]
        abel
      constructor
      · intro h
        norm_num at h
      · intro h
        rw [he]
        exact hx i
    · simp [oneHotWeights,oneHotDisplacements,hk]

theorem oneHot_objective_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (ℓ : Fin K → E → EReal) (sample x : Fin N → E) (j : Fin N → Fin K) :
    objective13 sample ℓ (oneHotWeights j) (oneHotDisplacements sample x j)=
      ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, ℓ (j i) (x i)) := by
  have ht : ∀ i k, term13 (ℓ k) (sample i) (oneHotWeights j i k) (oneHotDisplacements sample x j i k)=
      if k=j i then ℓ (j i) (x i) else 0 := by
    intro i k
    by_cases hk : k=j i
    · subst k
      have he : atom13 (sample i) 1 (sample i-x i)=x i := by
        unfold atom13
        simp only [inv_one,one_smul]
        abel
      simp [oneHotWeights,oneHotDisplacements,term13,he]
    · simp [oneHotWeights,oneHotDisplacements,term13,hk]
  unfold objective13
  simp_rw [ht]
  simp

theorem maxLoss_points_value_le_program13 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (Ξ : Set E) (ℓ : Fin K → E → EReal) (sample x : Fin N → E) (ε : ℝ)
    (hx : ∀ i, x i∈Ξ) (hcost : (1/(N : ℝ))*(∑ i, ‖x i-sample i‖) ≤ ε) :
    ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, maxLoss ℓ (x i)) ≤ program13Value ε Ξ sample ℓ := by
  classical
  have hp : ∀ i, ∃ k, ℓ k (x i)=maxLoss ℓ (x i) := fun i => by
    letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
    exact exists_eq_ciSup_of_finite
  choose j hj using hp
  have hf := oneHot_feasible Ξ sample x j ε hx hcost
  have ho := oneHot_objective_eq ℓ sample x j
  simp_rw [hj] at ho
  rw [←ho]
  exact le_iSup_of_le (oneHotWeights j) (le_iSup_of_le (oneHotDisplacements sample x j)
    (le_iSup_of_le hf le_rfl))
end WassExtremalCodex

end

section
set_option autoImplicit false
namespace WassExtremalCodex
open WassDDRO.Extremal

theorem program12f_le_program13_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hA : Assumption41 Ξ ℓ) (ξhat : Fin N → E) (ε : ℝ) :
    program12fValue ε Ξ ξhat ℓ ≤ program13Value ε Ξ ξhat ℓ := by
  classical
  change WassDDRO.Reduction.program12fValue ε Ξ ξhat ℓ ≤ program13Value ε Ξ ξhat ℓ
  rw [←WassReductionCodex.program12c_eq_program12f hK hN Ξ ℓ (toReductionAssumption Ξ ℓ hA) ξhat ε]
  change WassDDRO.Reduction.program12cValue ε Ξ ξhat (maxLoss ℓ) ≤ program13Value ε Ξ ξhat ℓ
  by_cases hgt : WassReductionCodex.finiteDomainCost Ξ (maxLoss ℓ) ξhat < ε
  · exact program12c_le_program13_of_gt_domain_cost hK hN Ξ ℓ hA ξhat ε hgt
  · have hle : ε ≤ WassReductionCodex.finiteDomainCost Ξ (maxLoss ℓ) ξhat := le_of_not_gt hgt
    rcases lt_or_eq_of_le hle with hlt | heq
    · let d : Fin N → ℝ := fun i => Metric.infDist (ξhat i) (WassReductionCodex.finiteLossDomain Ξ (maxLoss ℓ))
      have hd : ∀ i x, x∈Ξ → maxLoss ℓ x≠⊥ → d i ≤ ‖x-ξhat i‖ :=
        fun i x hx hb => WassReductionCodex.finite_domain_distance_lower Ξ (maxLoss ℓ) (ξhat i) x hx hb
      have hbot := WassReductionCodex.program12c_eq_bot_of_cost_gap Ξ ℓ (toReductionAssumption Ξ ℓ hA)
        ξhat ε d hd hlt
      change WassDDRO.Reduction.program12cValue ε Ξ ξhat (maxLoss ℓ)=⊥ at hbot
      rw [hbot]
      exact bot_le
    · have husc : UpperSemicontinuous (maxLoss ℓ) :=
        WassReductionCodex.maxLoss_upperSemicontinuous Ξ ℓ (toReductionAssumption Ξ ℓ hA)
      have hp : ∀ i, ∃ y∈Ξ, ‖y-ξhat i‖=Metric.infDist (ξhat i) (WassReductionCodex.finiteLossDomain Ξ (maxLoss ℓ)) ∧
          y∈closure (WassReductionCodex.finiteLossDomain Ξ (maxLoss ℓ)) ∧
          ∀ x∈closure (WassReductionCodex.finiteLossDomain Ξ (maxLoss ℓ)),
            ‖x-ξhat i‖=Metric.infDist (ξhat i) (WassReductionCodex.finiteLossDomain Ξ (maxLoss ℓ)) →
            maxLoss ℓ x ≤ maxLoss ℓ y := fun i =>
        WassReductionCodex.nearest_finite_domain_max Ξ hA.closed (maxLoss ℓ) husc
          (finite_loss_domain_nonempty hK Ξ ℓ hA) (ξhat i)
      choose y hy hdist hcl hmax using hp
      have hprog := WassReductionCodex.critical_program_le_nearest_average Ξ ℓ
        (toReductionAssumption Ξ ℓ hA) ξhat y hmax
      change WassDDRO.Reduction.program12cValue
        (WassReductionCodex.finiteDomainCost Ξ (maxLoss ℓ) ξhat) Ξ ξhat (maxLoss ℓ) ≤
          ((1/(N : ℝ) : ℝ) : EReal)*(∑ i, maxLoss ℓ (y i)) at hprog
      rw [←heq] at hprog
      have hcost : (1/(N : ℝ))*(∑ i, ‖y i-ξhat i‖) ≤ ε := by
        rw [heq]
        simp only [hdist,WassReductionCodex.finiteDomainCost]
        exact le_rfl
      exact hprog.trans (maxLoss_points_value_le_program13 hK Ξ ℓ ξhat y ε hy hcost)

theorem program12f_eq_program13_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : Assumption41 Ξ ℓ) : program12fValue ε Ξ ξhat ℓ=program13Value ε Ξ ξhat ℓ :=
  le_antisymm (program12f_le_program13_full hK hN Ξ ℓ hA ξhat ε)
    (program13_le_program12f hK hN Ξ ℓ hmeas ξhat ε hε hA)
end WassExtremalCodex

end

set_option autoImplicit false
open WassDDRO.Extremal Filter Topology MeasureTheory
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ) :
    program12fValue ε Ξ ξhat ℓ = program13Value ε Ξ ξhat ℓ := by
  exact WassExtremalCodex.program12f_eq_program13_full hK hN Ξ ℓ hmeas ξhat ε hε hA



#print axioms solution
