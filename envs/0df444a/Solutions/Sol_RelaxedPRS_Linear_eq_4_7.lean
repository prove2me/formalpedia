-- Prove2me | solution 1 for RelaxedPRS.Linear.eq_4_7
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T18:44:11.800099+00:00
-- url     : https://prove2.me/submissions/6a6c5908-54ab-48ad-9a1d-a57fabbe09c9

import Mathlib
import Definitions.Def_RelaxedPRS_Linear_Setting

set_option autoImplicit false
open scoped InnerProductSpace
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization RelaxedPRS.StrongCvx

theorem rpl_limit_aux (a b c e : ℝ) (he : 0 ≤ e)
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → a ≤ b + c + s * e) : a ≤ b + c := by
  by_contra hcon
  push_neg at hcon
  set δ := a - b - c with hδ
  have hδpos : 0 < δ := by linarith
  have hpos : 0 < δ / (2 * (e + 1)) := by positivity
  set s := min 1 (δ / (2 * (e + 1))) with hs
  have hs0 : 0 < s := lt_min one_pos hpos
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s ≤ δ / (2 * (e + 1)) := min_le_right _ _
  have := h s hs0 hs1
  have h3 : s * e ≤ δ / (2 * (e + 1)) * e := mul_le_mul_of_nonneg_right hs2 he
  have h4 : δ / (2 * (e + 1)) * e ≤ δ / 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

theorem rpl_prox_subgrad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : IsProperClosedConvex f) (γ : ℝ) (hγ : 0 < γ) (P : H → H)
    (hP : IsProx γ f P) (z : H) : γ⁻¹ • (z - P z) ∈ subgrad f (P z) := by
  obtain ⟨hbot, ⟨y0, hy0⟩, -, hconv⟩ := hf
  set p := P z with hp
  have hpbot := hbot p
  have hptop : f p ≠ ⊤ := by
    intro h
    have h1 := hP z y0
    rw [← hp, h] at h1
    obtain ⟨r, hr⟩ : ∃ r : ℝ, f y0 = r := ⟨(f y0).toReal, (EReal.coe_toReal hy0 (hbot y0)).symm⟩
    rw [hr, ← EReal.coe_add, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _), top_le_iff] at h1
    exact EReal.coe_ne_top _ h1
  refine ⟨hpbot, hptop, fun u => ?_⟩
  by_cases hu : f u = ⊤
  · rw [hu]; exact le_top
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f p = a := ⟨(f p).toReal, (EReal.coe_toReal hptop hpbot).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, f u = b := ⟨(f u).toReal, (EReal.coe_toReal hu (hbot u)).symm⟩
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      a ≤ b + γ⁻¹ * ⟪p - z, u - p⟫_ℝ + s * (‖u - p‖ ^ 2 / (2 * γ)) := by
    intro s hs0 hs1
    have hmem : ((1 - s) • p + s • u, (1 - s) * a + s * b) ∈
        {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} := by
      have := hconv (show (p, a) ∈ {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} by
          simp only [Set.mem_setOf_eq]; rw [ha])
        (show (u, b) ∈ {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} by
          simp only [Set.mem_setOf_eq]; rw [hb]) (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
      simpa using this
    simp only [Set.mem_setOf_eq] at hmem
    have h1 := hP z ((1 - s) • p + s • u)
    rw [← hp, ha] at h1
    have h2 : f ((1 - s) • p + s • u) + (((‖(1 - s) • p + s • u - z‖ ^ 2 / (2 * γ) : ℝ)) : EReal) ≤
        (((1 - s) * a + s * b : ℝ) : EReal) + (((‖(1 - s) • p + s • u - z‖ ^ 2 / (2 * γ) : ℝ)) : EReal) :=
      add_le_add hmem le_rfl
    have h3 := h1.trans h2
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    have hy : (1 - s) • p + s • u - z = (p - z) + s • (u - p) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [hy] at h3
    have hn : ‖(p - z) + s • (u - p)‖ ^ 2 =
        ‖p - z‖ ^ 2 + 2 * s * ⟪p - z, u - p⟫_ℝ + s ^ 2 * ‖u - p‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg hs0.le]
      ring
    rw [hn] at h3
    -- h3 : a + ‖p-z‖^2/(2γ) ≤ (1-s) a + s b + (…)/(2γ)
    have h4 : s * a ≤ s * (b + γ⁻¹ * ⟪p - z, u - p⟫_ℝ + s * (‖u - p‖ ^ 2 / (2 * γ))) := by
      have e1 : (‖p - z‖ ^ 2 + 2 * s * ⟪p - z, u - p⟫_ℝ + s ^ 2 * ‖u - p‖ ^ 2) / (2 * γ) =
          ‖p - z‖ ^ 2 / (2 * γ) + s * (γ⁻¹ * ⟪p - z, u - p⟫_ℝ) +
            s ^ 2 * (‖u - p‖ ^ 2 / (2 * γ)) := by
        field_simp
      rw [e1] at h3
      nlinarith
    exact le_of_mul_le_mul_left h4 hs0
  have := rpl_limit_aux a b (γ⁻¹ * ⟪p - z, u - p⟫_ℝ) (‖u - p‖ ^ 2 / (2 * γ)) (by positivity) key
  have e3 : ⟪u - p, γ⁻¹ • (z - p)⟫_ℝ = -(γ⁻¹ * ⟪p - z, u - p⟫_ℝ) := by
    rw [inner_smul_right]
    have : ⟪p - z, u - p⟫_ℝ = -⟪z - p, u - p⟫_ℝ := by rw [← inner_neg_left, neg_sub]
    rw [this, real_inner_comm]
    ring
  show a + ⟪u - p, γ⁻¹ • (z - P z)⟫_ℝ ≤ b
  rw [← hp, e3]
  linarith

theorem accepted_prs_identities {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg) (t : ℝ) (ht : 0 < t) (z : H) :
    RelaxedPRS.StrongCvx.gtG γ Pg z ∈ MoreauProx.Characterization.subgrad g (RelaxedPRS.StrongCvx.xg Pg z) ∧
    RelaxedPRS.StrongCvx.gtF γ Pf Pg z ∈ MoreauProx.Characterization.subgrad f (RelaxedPRS.StrongCvx.xf Pf Pg z) ∧
    RelaxedPRS.StrongCvx.xg Pg z = z - γ • RelaxedPRS.StrongCvx.gtG γ Pg z ∧
    RelaxedPRS.StrongCvx.xf Pf Pg z = RelaxedPRS.StrongCvx.xg Pg z - γ • RelaxedPRS.StrongCvx.gtG γ Pg z - γ • RelaxedPRS.StrongCvx.gtF γ Pf Pg z ∧
    RelaxedPRS.StrongCvx.Tlam Pf Pg t z - z = (2 * t) • (RelaxedPRS.StrongCvx.xf Pf Pg z - RelaxedPRS.StrongCvx.xg Pg z) ∧
    RelaxedPRS.StrongCvx.Tlam Pf Pg t z - z = -(2 * t * γ) • (RelaxedPRS.StrongCvx.gtG γ Pg z + RelaxedPRS.StrongCvx.gtF γ Pf Pg z) := by
  have hγ' : γ ≠ 0 := hγ.ne'
  have e1 : γ • (γ⁻¹ • (z - Pg z)) = z - Pg z := by rw [smul_smul, mul_inv_cancel₀ hγ', one_smul]
  have e2 : γ • (γ⁻¹ • (RelaxedPRS.StrongCvx.refl Pg z - Pf (RelaxedPRS.StrongCvx.refl Pg z))) = RelaxedPRS.StrongCvx.refl Pg z - Pf (RelaxedPRS.StrongCvx.refl Pg z) := by
    rw [smul_smul, mul_inv_cancel₀ hγ', one_smul]
  refine ⟨rpl_prox_subgrad g hg γ hγ Pg hPg z, rpl_prox_subgrad f hf γ hγ Pf hPf (RelaxedPRS.StrongCvx.refl Pg z), ?_, ?_, ?_, ?_⟩
  · simp only [gtG, xg, e1]; abel
  · simp only [gtG, gtF, xg, xf, RelaxedPRS.StrongCvx.refl]
    match_scalars <;> field_simp <;> ring
  · simp only [Tlam, TPRS, xf, xg, RelaxedPRS.StrongCvx.refl]; module
  · simp only [Tlam, TPRS, gtG, gtF, xf, xg, RelaxedPRS.StrongCvx.refl]
    match_scalars <;> field_simp <;> ring


open scoped InnerProductSpace
open ThreeOpSplitting.ConvexRates MoreauProx.Characterization RelaxedPRS.StrongCvx

namespace QueeliusPRS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem subgrad_gradient (h : H → ℝ) (hd : Differentiable ℝ h) (x u : H)
    (hu : u ∈ subgrad (fun y => (h y : EReal)) x) : u = gradient h x := by
  have hm : IsLocalMin (fun y => h y - ⟪u,y⟫_ℝ) x := by
    apply Filter.Eventually.of_forall
    intro y
    have hy := hu.2.2 y
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hy
    rw [real_inner_comm, inner_sub_right] at hy
    linarith
  have hd' := (hd x).hasGradientAt.hasFDerivAt.sub (innerSL ℝ u).hasFDerivAt
  have hz := congrArg (fun L : H →L[ℝ] ℝ => L (gradient h x-u))
    (hd'.fderiv.symm.trans hm.fderiv_eq_zero)
  simp only [ContinuousLinearMap.sub_apply, InnerProductSpace.toDual_apply_apply,
    innerSL_apply_apply, ContinuousLinearMap.zero_apply] at hz
  have hzero : gradient h x-u=0 := (inner_self_eq_zero (𝕜 := ℝ)).mp (by
    simpa only [inner_sub_left] using hz)
  exact (sub_eq_zero.mp hzero).symm

theorem prox_gradient (g : H → EReal) (hg : IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (P : H → H) (hP : IsProx γ g P)
    (h : H → ℝ) (hgh : ∀ x, g x = (h x : EReal))
    (hd : Differentiable ℝ h) (z : H) : z = P z + γ • gradient h (P z) := by
  have heq : g = fun x => (h x : EReal) := funext hgh
  have hs := rpl_prox_subgrad g hg γ hγ P hP z
  rw [heq] at hs
  have hh := subgrad_gradient h hd (P z) (γ⁻¹ • (z-P z)) hs
  rw [← hh,smul_smul,mul_inv_cancel₀ hγ.ne',one_smul]
  abel

theorem norm_three (a b c : H) :
    ‖a+b+c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have ht := (norm_add_le (a+b) c).trans (add_le_add (norm_add_le a b) (le_refl ‖c‖))
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖a‖+‖b‖+‖c‖)).2 ht
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖b‖-‖c‖)]

theorem strong_subgradient (f : H → EReal) (μ : ℝ) (hμ : 0 ≤ μ)
    (hsc : IsStrongCvxE μ f) (x y u : H)
    (hu : u ∈ subgrad f x) (hybot : f y ≠ ⊥) (hytop : f y ≠ ⊤) :
    (f x).toReal + ⟪y-x,u⟫_ℝ + μ/2*‖y-x‖^2 ≤ (f y).toReal := by
  let a := (f x).toReal
  let b := (f y).toReal
  have hx : f x = (a : EReal) := (EReal.coe_toReal hu.2.1 hu.1).symm
  have hy : f y = (b : EReal) := (EReal.coe_toReal hytop hybot).symm
  let q := μ/2*‖y-x‖^2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      a + ⟪y-x,u⟫_ℝ + q ≤ b + 0 + t*q := by
    intro t ht ht1
    have h1 := hsc y x t ht.le ht1
    have h2 := add_le_add (hu.2.2 (t • y + (1-t) • x))
      (le_refl (((μ/2*t*(1-t)*‖y-x‖^2 : ℝ)) : EReal))
    have h3 := h2.trans h1
    rw [hx,hy,← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add,
      ← EReal.coe_add,← EReal.coe_add,EReal.coe_le_coe_iff] at h3
    have hm : t • y+(1-t) • x-x = t • (y-x) := by module
    rw [hm,real_inner_smul_left] at h3
    have hscaled : t*(a+⟪y-x,u⟫_ℝ+q) ≤ t*(b+t*q) := by
      dsimp [q] at *
      nlinarith only [h3]
    simpa using le_of_mul_le_mul_left hscaled ht
  simpa only [add_zero] using rpl_limit_aux (a+⟪y-x,u⟫_ℝ+q) b 0 q hq key

end QueeliusPRS
/-- (4.7), proof of Theorem 4.3, p. 16: the fixed-point distance bound. -/
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hg : ThreeOpSplitting.ConvexRates.IsProperClosedConvex g)
    (γ : ℝ) (hγ : 0 < γ) (Pf Pg : H → H)
    (hPf : ThreeOpSplitting.ConvexRates.IsProx γ f Pf)
    (hPg : ThreeOpSplitting.ConvexRates.IsProx γ g Pg)
    (lam : ℕ → ℝ) (hlam : ∀ k, 0 < lam k ∧ lam k ≤ 1)
    (z : ℕ → H) (hz : RelaxedPRS.StrongCvx.IsPRSRun Pf Pg lam z)
    (zs : H) (hzs : RelaxedPRS.StrongCvx.TPRS Pf Pg zs = zs)
    (β : ℝ) (hβ : 0 < β)
    (h : H → ℝ) (hgh : ∀ x, g x = (h x : EReal))
    (hh : ThreeOpSplitting.ConvexRates.IsSmoothConvex β h) :
    ∀ k, ‖z k - zs‖ ^ 2 ≤ 3 *
      (‖RelaxedPRS.StrongCvx.xf Pf Pg (z k) - RelaxedPRS.StrongCvx.xg Pg zs‖ ^ 2 +
       ‖γ • gradient h (RelaxedPRS.StrongCvx.xg Pg (z k)) - γ • gradient h (RelaxedPRS.StrongCvx.xg Pg zs)‖ ^ 2 +
       ‖RelaxedPRS.StrongCvx.xg Pg (z k) - RelaxedPRS.StrongCvx.xf Pf Pg (z k)‖ ^ 2)  := by
  intro k
  have hk := QueeliusPRS.prox_gradient g hg γ hγ Pg hPg h hgh hh.2.1 (z k)
  have hs := QueeliusPRS.prox_gradient g hg γ hγ Pg hPg h hgh hh.2.1 zs
  have he : z k - zs =
      (xf Pf Pg (z k)-xg Pg zs) +
      (γ • gradient h (xg Pg (z k))-γ • gradient h (xg Pg zs)) +
      (xg Pg (z k)-xf Pf Pg (z k)) := by
    change z k-zs=(xf Pf Pg (z k)-Pg zs)+
      (γ • gradient h (Pg (z k))-γ • gradient h (Pg zs))+(Pg (z k)-xf Pf Pg (z k))
    calc
      z k-zs = (Pg (z k)+γ • gradient h (Pg (z k)))-
          (Pg zs+γ • gradient h (Pg zs)) := congrArg₂ (fun a b : H => a-b) hk hs
      _ = _ := by module
  rw [he]
  exact QueeliusPRS.norm_three _ _ _

