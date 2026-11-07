-- Prove2me | solution 1 for PenaltyLag.Asymptotic.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:57:04.089629+00:00
-- url     : https://prove2.me/submissions/6356a775-3e5d-43a3-9aec-6570da056ef1

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace PL41Sol

open PenaltyLag.Asymptotic

/-- Per-coordinate penalty bound: for `v ≥ a`, `(θ(b+2ra)² - b²)/(4r) ≤ v b + r v²`. -/
lemma pen_le (r a b v : ℝ) (hr : 0 < r) (hv : a ≤ v) :
    (1 / (4 * r)) * (theta (b + 2 * r * a) ^ 2 - b ^ 2) ≤ v * b + r * v ^ 2 := by
  have h4r : 0 < 4 * r := by positivity
  rw [one_div_mul_eq_div, div_le_iff₀ h4r]
  unfold theta
  rcases le_total 0 (b + 2 * r * a) with h | h
  · rw [max_eq_right h]
    nlinarith [mul_nonneg (sub_nonneg.2 hv) (by nlinarith : (0:ℝ) ≤ b + r * (v + a)), hr]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg (2 * r * v + b)]

/-- Per-coordinate penalty identity at the minimizer `max (-b/(2r)) a`. -/
lemma pen_eq (r a b : ℝ) (hr : 0 < r) :
    (1 / (4 * r)) * (theta (b + 2 * r * a) ^ 2 - b ^ 2)
      = max (-b / (2 * r)) a * b + r * (max (-b / (2 * r)) a) ^ 2 := by
  have hr' : r ≠ 0 := hr.ne'
  unfold theta
  rcases le_total 0 (b + 2 * r * a) with h | h
  · rw [max_eq_right h]
    have : -b / (2 * r) ≤ a := by
      rw [div_le_iff₀ (by positivity)]; linarith
    rw [max_eq_right this]
    field_simp
    ring
  · rw [max_eq_left h]
    have : a ≤ -b / (2 * r) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    rw [max_eq_left this]
    field_simp
    ring

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}

lemma Lr_le (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ) (hr : 0 < r) (x : E) (y : Mult m)
    (u : Fin m → ℝ) (hu : ∀ i, f i x ≤ u i) :
    Lr f₀ f r x y ≤ f₀ x + ∑ i, (u i * y i + r * u i ^ 2) := by
  unfold Lr
  rw [Finset.mul_sum]
  gcongr with i _
  exact pen_le r (f i x) (y i) (u i) hr (hu i)

lemma Lr_eq (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ) (hr : 0 < r) (x : E) (y : Mult m) :
    Lr f₀ f r x y = f₀ x + ∑ i, (max (-(y i) / (2 * r)) (f i x) * y i
      + r * (max (-(y i) / (2 * r)) (f i x)) ^ 2) := by
  unfold Lr
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact pen_eq r (f i x) (y i) hr

/-- Weak duality: `g_r(y) ≤ limsup f₀(x'ʲ)` along any asymptotically feasible sequence. -/
lemma weak (X : Set E) (f₀ : E → ℝ) (f : Fin m → E → ℝ) (r : ℝ) (hr : 0 < r) (y0 : Mult m)
    (x' : ℕ → E) (hx' : IsAsympFeasible X f x') :
    gr X f₀ f r y0 ≤ limsup (fun j => (f₀ (x' j) : EReal)) atTop := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  obtain ⟨b, hLb, hbc⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  refine le_trans ?_ hbc.le
  have hev0 : ∀ᶠ j in atTop, (f₀ (x' j) : EReal) < b := eventually_lt_of_limsup_lt hLb
  have key : ∀ ε : ℝ, 0 < ε →
      gr X f₀ f r y0 ≤ ((b + ∑ i, (ε * y0 i + r * ε ^ 2) : ℝ) : EReal) := by
    intro ε hε
    have hevi : ∀ᶠ j in atTop, ∀ i, (f i (x' j) : EReal) < (ε : EReal) :=
      eventually_all.2 fun i =>
        eventually_lt_of_limsup_lt (lt_of_le_of_lt (hx'.2 i) (by exact_mod_cast hε))
    obtain ⟨j, hj0, hji⟩ := (hev0.and hevi).exists
    have hj0' : f₀ (x' j) < b := by exact_mod_cast hj0
    have hji' : ∀ i, f i (x' j) ≤ ε := fun i => by
      have := hji i; exact le_of_lt (by exact_mod_cast this)
    have h1 : gr X f₀ f r y0 ≤ (Lr f₀ f r (x' j) y0 : EReal) := iInf₂_le (x' j) (hx'.1 j)
    have h2 := Lr_le f₀ f r hr (x' j) y0 (fun _ => ε) hji'
    refine h1.trans ?_
    exact_mod_cast (by linarith : Lr f₀ f r (x' j) y0 ≤ b + ∑ i, (ε * y0 i + r * ε ^ 2))
  have hne_top : gr X f₀ f r y0 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (key 1 one_pos)
  rcases eq_bot_or_bot_lt (gr X f₀ f r y0) with hb | hb
  · rw [hb]; exact bot_le
  · rw [← EReal.coe_toReal hne_top hb.ne']
    rw [EReal.coe_le_coe_iff]
    set g := (gr X f₀ f r y0).toReal with hg
    have hkey : ∀ ε : ℝ, 0 < ε → g ≤ b + ∑ i, (ε * y0 i + r * ε ^ 2) := by
      intro ε hε
      have := key ε hε
      rw [← EReal.coe_toReal hne_top hb.ne', EReal.coe_le_coe_iff] at this
      exact this
    have hcont : Tendsto (fun ε : ℝ => b + ∑ i, (ε * y0 i + r * ε ^ 2)) (𝓝[>] 0)
        (𝓝 (b + ∑ i : Fin m, ((0:ℝ) * y0 i + r * (0:ℝ) ^ 2))) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      apply Continuous.tendsto
      fun_prop
    simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero, Finset.sum_const_zero] at hcont
    exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun ε hε => hkey ε hε)

/-- The key estimate (merging Lemmas 4.2 and 4.3 of the paper). -/
lemma key_est (X : Set E) (hX : Convex ℝ X) (f₀ : E → ℝ) (f : Fin m → E → ℝ)
    (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i)) (r : ℝ) (hr : 0 < r)
    (y : Mult m) (xh : E) (hxh : xh ∈ X) (γ α : ℝ)
    (H1 : ∀ z ∈ X, γ ≤ Lr f₀ f r z y) (H2 : Lr f₀ f r xh y ≤ γ + α) (z : E) (hz : z ∈ X) :
    γ - 3 * α + (2 / 3) * r * ∑ i, (max (-(y i) / (2 * r)) (f i xh)) ^ 2
      ≤ Lr f₀ f r z (WithLp.toLp 2 (fun i => y i + 2 * r * max (-(y i) / (2 * r)) (f i xh))) := by
  set uh : Fin m → ℝ := fun i => max (-(y i) / (2 * r)) (f i xh) with huh
  set y' : Mult m := WithLp.toLp 2 (fun i => y i + 2 * r * uh i) with hy'
  set u : Fin m → ℝ := fun i => max (-(y' i) / (2 * r)) (f i z) with hu
  have hLz := Lr_eq f₀ f r hr z y'
  have hLh := Lr_eq f₀ f r hr xh y
  set xt : E := (3 / 4 : ℝ) • xh + (1 / 4 : ℝ) • z with hxt
  have hxtX : xt ∈ X := hX hxh hz (by norm_num) (by norm_num) (by norm_num)
  set ut : Fin m → ℝ := fun i => (3 / 4) * uh i + (1 / 4) * u i with hut
  have hfut : ∀ i, f i xt ≤ ut i := by
    intro i
    have h1 := (hf i).2 hxh hz (by norm_num : (0:ℝ) ≤ 3 / 4) (by norm_num : (0:ℝ) ≤ 1 / 4)
      (by norm_num)
    simp only [smul_eq_mul] at h1
    have h2 : f i xh ≤ uh i := le_max_right _ _
    have h3 : f i z ≤ u i := le_max_right _ _
    simp only [hut]
    linarith
  have hLt := Lr_le f₀ f r hr xt y ut hfut
  have hf0t := hf₀.2 hxh hz (by norm_num : (0:ℝ) ≤ 3 / 4) (by norm_num : (0:ℝ) ≤ 1 / 4)
      (by norm_num)
  simp only [smul_eq_mul] at hf0t
  have hH1 := H1 xt hxtX
  have hy'i : ∀ i, y' i = y i + 2 * r * uh i := fun i => rfl
  -- per-coordinate inequality
  have hpc : ∀ i : Fin m,
      (2 / 3) * r * uh i ^ 2 - 3 * (uh i * y i + r * uh i ^ 2) + 4 * (ut i * y i + r * ut i ^ 2)
        ≤ u i * y' i + r * u i ^ 2 := by
    intro i
    rw [hy'i]
    simp only [hut]
    nlinarith [mul_nonneg hr.le (sq_nonneg (u i + uh i / 3))]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpc i)
  have hid : ∑ i, ((2 / 3) * r * uh i ^ 2 - 3 * (uh i * y i + r * uh i ^ 2)
        + 4 * (ut i * y i + r * ut i ^ 2))
      = (2 / 3) * r * ∑ i, uh i ^ 2 - 3 * ∑ i, (uh i * y i + r * uh i ^ 2)
        + 4 * ∑ i, (ut i * y i + r * ut i ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
  rw [hid] at hsum
  have hLz' : Lr f₀ f r z y' = f₀ z + ∑ i, (u i * y' i + r * u i ^ 2) := hLz
  have hLh' : Lr f₀ f r xh y = f₀ xh + ∑ i, (uh i * y i + r * uh i ^ 2) := hLh
  rw [hLz']
  rw [hLh'] at H2
  linarith

end PL41Sol

open PenaltyLag.Asymptotic

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (hfin : asympValue X f₀ f ≠ ⊥ ∧ asympValue X f₀ f ≠ ⊤)
    (r : ℝ) (hr : 0 < r)
    (y : ℕ → Mult m) (hyb : Bornology.IsBounded (Set.range y)) (hymax : IsMaximizing X f₀ f r y)
    (x : ℕ → E) (hxX : ∀ k, x k ∈ X)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 0))
    (h47 : ∀ k, (Lr f₀ f r (x k) (y k) : EReal) ≤ gr X f₀ f r (y k) + (α k : EReal)) :
    IsAsympMinimizing X f₀ f x := by
  set G' : EReal := ⨆ y', gr X f₀ f r y' with hG'
  have hgr_le : ∀ k, gr X f₀ f r (y k) ≤ (Lr f₀ f r (x k) (y k) : EReal) :=
    fun k => iInf₂_le (x k) (hxX k)
  have hgr_ne_bot : ∀ k, gr X f₀ f r (y k) ≠ ⊥ := by
    intro k h
    have := h47 k
    rw [h, EReal.bot_add] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
  have hgr_ne_top : ∀ k, gr X f₀ f r (y k) ≠ ⊤ := fun k =>
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (hgr_le k)
  set γ : ℕ → ℝ := fun k => (gr X f₀ f r (y k)).toReal with hγdef
  have hγ : ∀ k, gr X f₀ f r (y k) = (γ k : EReal) := fun k =>
    (EReal.coe_toReal (hgr_ne_top k) (hgr_ne_bot k)).symm
  have hL : ∀ k, Lr f₀ f r (x k) (y k) ≤ γ k + α k := by
    intro k
    have := h47 k
    rw [hγ k, ← EReal.coe_add] at this
    exact_mod_cast this
  have hH1 : ∀ k, ∀ z ∈ X, γ k ≤ Lr f₀ f r z (y k) := by
    intro k z hz
    have : gr X f₀ f r (y k) ≤ (Lr f₀ f r z (y k) : EReal) := iInf₂_le z hz
    rw [hγ k] at this
    exact_mod_cast this
  have hG'le : G' ≤ asympValue X f₀ f :=
    iSup_le fun y0 => le_iInf₂ fun x' hx' => PL41Sol.weak X f₀ f r hr y0 x' hx'
  have hG'top : G' ≠ ⊤ := ne_top_of_le_ne_top hfin.2 hG'le
  have hG'bot : G' ≠ ⊥ := by
    intro h
    apply hgr_ne_bot 0
    have : gr X f₀ f r (y 0) ≤ G' := le_iSup (fun y' => gr X f₀ f r y') (y 0)
    rw [h] at this
    exact le_bot_iff.1 this
  set G : ℝ := G'.toReal with hGdef
  have hGG : G' = (G : EReal) := (EReal.coe_toReal hG'top hG'bot).symm
  have hγG : Tendsto γ atTop (𝓝 G) := (EReal.tendsto_toReal hG'top hG'bot).comp hymax
  set U : ℕ → Fin m → ℝ := fun k i => max (-(y k i) / (2 * r)) (f i (x k)) with hU
  have hkey : ∀ k, (2 / 3) * r * ∑ i, U k i ^ 2 ≤ G - γ k + 3 * α k := by
    intro k
    have hb : ((γ k - 3 * α k + (2 / 3) * r * ∑ i, U k i ^ 2 : ℝ) : EReal) ≤ G' := by
      refine le_trans ?_ (le_iSup (fun y' => gr X f₀ f r y')
        (WithLp.toLp 2 (fun i => y k i + 2 * r * max (-(y k i) / (2 * r)) (f i (x k)))))
      refine le_iInf₂ fun z hz => ?_
      exact_mod_cast PL41Sol.key_est X hX f₀ f hf₀ hf r hr (y k) (x k) (hxX k) (γ k) (α k)
        (hH1 k) (hL k) z hz
    rw [hGG, EReal.coe_le_coe_iff] at hb
    linarith
  have hSnn : ∀ k, 0 ≤ ∑ i, U k i ^ 2 := fun k =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS : Tendsto (fun k => ∑ i, U k i ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k => (3 / (2 * r)) * (G - γ k + 3 * α k)) atTop
        (𝓝 ((3 / (2 * r)) * (G - G + 3 * 0))) :=
      ((tendsto_const_nhds.sub hγG).add (hα.const_mul 3)).const_mul _
    simp only [sub_self, mul_zero, add_zero] at hlim
    refine squeeze_zero hSnn (fun k => ?_) hlim
    have := hkey k
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hUi : ∀ i, Tendsto (fun k => U k i) atTop (𝓝 0) := by
    intro i
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have hsq : Tendsto (fun k => Real.sqrt (∑ j, U k j ^ 2)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hS
      rw [Real.sqrt_zero] at this
      exact this
    refine squeeze_zero (fun k => abs_nonneg _) (fun k => ?_) hsq
    show |U k i| ≤ _
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (f := fun j => U k j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  -- feasibility
  have hfeas : IsAsympFeasible X f x := by
    refine ⟨hxX, fun i => ?_⟩
    have h1 : limsup (fun k => (f i (x k) : EReal)) atTop
        ≤ limsup (fun k => (U k i : EReal)) atTop :=
      limsup_le_limsup (Eventually.of_forall fun k => by
        show (f i (x k) : EReal) ≤ (U k i : EReal)
        exact_mod_cast (le_max_right _ _ : f i (x k) ≤ U k i))
    have h2 : limsup (fun k => (U k i : EReal)) atTop = ((0:ℝ) : EReal) :=
      ((continuous_coe_real_ereal.tendsto 0).comp (hUi i)).limsup_eq
    rw [h2] at h1
    exact_mod_cast h1
  -- bound on y
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hyb
  have hyM : ∀ k i, |y k i| ≤ M := fun k i => by
    have h1 := PiLp.norm_apply_le (y k) i
    have h2 := hM (y k) ⟨k, rfl⟩
    rw [Real.norm_eq_abs] at h1
    linarith
  have hf0b : ∀ k, f₀ (x k) ≤ γ k + α k + M * ∑ i, |U k i| := by
    intro k
    have h1 := PL41Sol.Lr_eq f₀ f r hr (x k) (y k)
    have h2 := hL k
    have h3 : ∀ i, -(M * |U k i|) ≤ U k i * y k i + r * U k i ^ 2 := by
      intro i
      have : |U k i * y k i| ≤ M * |U k i| := by
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hyM k i) (abs_nonneg _)
      have := neg_abs_le (U k i * y k i)
      nlinarith [mul_nonneg hr.le (sq_nonneg (U k i))]
    have h4 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h3 i)
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at h4
    have h1' : Lr f₀ f r (x k) (y k) = f₀ (x k) + ∑ i, (U k i * y k i + r * U k i ^ 2) := h1
    linarith
  have hw : Tendsto (fun k => γ k + α k + M * ∑ i, |U k i|) atTop (𝓝 (G + 0 + M * 0)) := by
    refine (hγG.add hα).add (Tendsto.const_mul M ?_)
    have : Tendsto (fun k => ∑ i, |U k i|) atTop (𝓝 (∑ i : Fin m, |(0:ℝ)|)) :=
      tendsto_finset_sum _ fun i _ => (hUi i).abs
    simpa using this
  simp only [add_zero, mul_zero] at hw
  have hls : limsup (fun k => (f₀ (x k) : EReal)) atTop ≤ G' := by
    have h1 : limsup (fun k => (f₀ (x k) : EReal)) atTop
        ≤ limsup (fun k => ((γ k + α k + M * ∑ i, |U k i| : ℝ) : EReal)) atTop :=
      limsup_le_limsup (Eventually.of_forall fun k => by
        show (f₀ (x k) : EReal) ≤ ((γ k + α k + M * ∑ i, |U k i| : ℝ) : EReal)
        exact_mod_cast hf0b k)
    have h2 : limsup (fun k => ((γ k + α k + M * ∑ i, |U k i| : ℝ) : EReal)) atTop = (G : EReal) :=
      ((continuous_coe_real_ereal.tendsto G).comp hw).limsup_eq
    rw [h2] at h1
    rw [hGG]; exact h1
  refine ⟨hfeas, le_antisymm (hls.trans hG'le) ?_⟩
  exact iInf₂_le x hfeas
