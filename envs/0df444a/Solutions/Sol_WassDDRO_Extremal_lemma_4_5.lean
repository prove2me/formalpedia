-- Prove2me | solution 1 for WassDDRO.Extremal.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T11:03:50.393575+00:00
-- url     : https://prove2.me/submissions/37ea6230-7ed2-4e4f-bff7-e502fb5b0d59

import Definitions.Def_WassDDRO_Extremal_Setting
import Mathlib
set_option autoImplicit false
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

set_option autoImplicit false
open WassDDRO.Extremal
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (f : E → EReal) (hf_ne_bot : ∀ ξ, f ξ ≠ ⊥) (hf_ne_top : ∃ ξ, f ξ ≠ ⊤)
    (hf_convex : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)})
    (hf_lsc : LowerSemicontinuous f)
    (ξh q : E) (α : ℝ) (hα : 0 ≤ α) :
    (0 < α →
      (⨅ z : StrongDual ℝ E, ((z (q - α • ξh) : ℝ) : EReal) + (α : EReal) * conjOn Set.univ f z)
        = -((α : EReal) * f (ξh - α⁻¹ • q))) ∧
    (α = 0 →
      (q = 0 →
        (⨅ z : StrongDual ℝ E, ((z (q - α • ξh) : ℝ) : EReal) + (α : EReal) * conjOn Set.univ f z)
          = 0) ∧
      (q ≠ 0 →
        (⨅ z : StrongDual ℝ E, ((z (q - α • ξh) : ℝ) : EReal) + (α : EReal) * conjOn Set.univ f z)
          = ⊥)) := by
  exact ⟨(fun hp => WassExtremalCodex.positive_perspective_eq f hf_ne_bot hf_ne_top hf_convex hf_lsc ξh q α hp),
    (fun hz => WassExtremalCodex.zero_perspective_eq f ξh q α hz)⟩



#print axioms solution
