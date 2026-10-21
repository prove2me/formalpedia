-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P04.thermalCorrelator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:48:19.957+00:00
-- url     : https://prove2.me/submissions/e6396ea9-c05c-4a9b-9eff-6d7a312367d3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P04

open QAlgorithms.Papers.Independent.Next46.P04

noncomputable section

open Filter

lemma g62f_a_pos (p : AcousticModel) : 0 < a p := by
  unfold a; exact abs_pos.mpr p.V_neg.ne

lemma g62f_a_lt (p : AcousticModel) : a p < p.cin := p.cin_gt

lemma g62f_A_eq (p : AcousticModel) : A p = -(3 * p.kappa * (p.cin - a p) / (2 * a p)) := by
  unfold A; ring

lemma g62f_A_neg (p : AcousticModel) : A p < 0 := by
  have := g62f_a_pos p; have := g62f_a_lt p; have := p.kappa_pos
  rw [g62f_A_eq]; apply neg_neg_of_pos; apply div_pos <;> nlinarith

lemma g62f_B_pos (p : AcousticModel) : 0 < B p := by
  have := g62f_a_pos p; have := g62f_a_lt p; have := p.kappa_pos
  unfold B; apply div_pos <;> nlinarith

lemma g62f_exp_c : Real.exp (Real.artanh (1 / 3 : ℝ)) = Real.sqrt 2 := by
  rw [Real.exp_artanh (by norm_num)]; norm_num

lemma g62f_retIn (p : AcousticModel) (s r : ℝ) :
    retardedIn p s r = (s / A p) * Real.arsinh (Real.exp (-p.kappa * r)) := by
  unfold retardedIn Real.arsinh
  congr 2
  rw [add_comm]; congr 2
  rw [sq, ← Real.exp_add]; ring_nf

lemma g62f_cosh (w : ℝ) : Real.cosh (w + Real.artanh (1 / 3 : ℝ)) =
    (Real.sqrt 2 * Real.exp w + Real.exp (-w) / Real.sqrt 2) / 2 := by
  rw [Real.cosh_eq, Real.exp_add, neg_add, Real.exp_add, Real.exp_neg (Real.artanh _), g62f_exp_c]
  ring

lemma g62f_v0 (p : AcousticModel) (y : ℝ) :
    v p 0 y = (3 * z p y - Real.log (Real.cosh (z p y + Real.artanh (1 / 3 : ℝ)))) / (8 * p.kappa) := by
  unfold v z; ring_nf

lemma g62f_tanh_eq : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
  funext x; exact Real.tanh_eq_sinh_div_cosh x

lemma g62f_hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have e : (Real.sinh / Real.cosh : ℝ → ℝ) = Real.tanh := by
    funext y; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  rw [e] at h
  refine h.congr_deriv ?_
  rw [← Real.cosh_sq_sub_sinh_sq x]; ring

lemma g62f_tanh_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)

lemma g62f_tanh_neg {x : ℝ} (hx : x < 0) : Real.tanh x < 0 := by
  rw [Real.tanh_eq_sinh_div_cosh]; exact div_neg_of_neg_of_pos (Real.sinh_neg_iff.mpr hx) (Real.cosh_pos x)

lemma g62f_ss_sub (p : AcousticModel) (x : ℝ) :
    soundSpeed p x - a p = (2 * a p / 3) * (Real.sinh (3 * p.kappa / (2 * a p) * x) / Real.cosh (3 * p.kappa / (2 * a p) * x)) := by
  unfold soundSpeed z; rw [Real.tanh_eq_sinh_div_cosh] <;> ring_nf

lemma g62f_ss_add (p : AcousticModel) (x : ℝ) :
    soundSpeed p x + a p = (2 * a p / 3) * (3 + Real.sinh (3 * p.kappa / (2 * a p) * x) / Real.cosh (3 * p.kappa / (2 * a p) * x)) := by
  unfold soundSpeed z; rw [Real.tanh_eq_sinh_div_cosh] <;> ring_nf

lemma g62f_uval (p : AcousticModel) (x sx : ℝ) (hsx : (sx = 1 ∧ 0 < x) ∨ (sx = -1 ∧ x < 0)) :
    -(Real.cosh (3 * p.kappa / (2 * a p) * |x|) * (3 * p.kappa / (2 * a p) * sx) /
      Real.sinh (3 * p.kappa / (2 * a p) * |x|) / p.kappa) = -1 / (soundSpeed p x - a p) := by
  have ha := g62f_a_pos p
  have hk := p.kappa_pos
  have hk' : 0 < 3 * p.kappa / (2 * a p) := by positivity
  rw [g62f_ss_sub]
  have hc := Real.cosh_pos (3 * p.kappa / (2 * a p) * x)
  rcases hsx with ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · rw [abs_of_pos hx]
    have hs : 0 < Real.sinh (3 * p.kappa / (2 * a p) * x) := Real.sinh_pos_iff.mpr (mul_pos hk' hx)
    field_simp <;> ring
  · rw [abs_of_neg hx, show 3 * p.kappa / (2 * a p) * -x = -(3 * p.kappa / (2 * a p) * x) by ring,
      Real.sinh_neg, Real.cosh_neg]
    have hs : Real.sinh (3 * p.kappa / (2 * a p) * x) < 0 := Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg hk' hx)
    have hs' := hs.ne
    field_simp <;> ring

lemma g62f_u_deriv (p : AcousticModel) (t x sx : ℝ) (hsx : (sx = 1 ∧ 0 < x) ∨ (sx = -1 ∧ x < 0))
    (hd : HasDerivAt (fun y : ℝ => |y|) sx x) :
    HasDerivAt (u p t) (-1 / (soundSpeed p x - a p)) x := by
  have ha := g62f_a_pos p
  have hk := p.kappa_pos
  have hx : x ≠ 0 := by rcases hsx with ⟨_, h⟩ | ⟨_, h⟩ <;> [exact h.ne'; exact h.ne]
  have e : u p t = fun y => t - Real.log (Real.sinh (3 * p.kappa / (2 * a p) * |y|)) / p.kappa := by
    funext y; unfold u z; ring_nf
  have hg := hd.const_mul (3 * p.kappa / (2 * a p))
  have hs := (Real.hasDerivAt_sinh _).comp x hg
  have hne : Real.sinh (3 * p.kappa / (2 * a p) * |x|) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos (by positivity) (abs_pos.mpr hx))).ne'
  have hl := hs.log hne
  have h := (hl.div_const p.kappa).const_sub t
  rw [e]
  refine h.congr_deriv ?_
  rw [← g62f_uval p x sx hsx]; rfl

lemma g62f_v_eq (p : AcousticModel) (t : ℝ) : v p t = fun y => t + (9 * p.kappa / (2 * a p) * y -
    Real.log (Real.cosh (3 * p.kappa / (2 * a p) * y + Real.artanh (1 / 3 : ℝ)))) / (8 * p.kappa) := by
  funext y; unfold v z; ring_nf

lemma g62f_v_deriv (p : AcousticModel) (t x : ℝ) :
    HasDerivAt (v p t) (1 / (soundSpeed p x + a p)) x := by
  have ha := g62f_a_pos p
  have hk := p.kappa_pos
  set k := 3 * p.kappa / (2 * a p) with hkdef
  set c := Real.artanh (1 / 3 : ℝ) with hcdef
  have hlin : HasDerivAt (fun y => k * y + c) (k * 1) x := ((hasDerivAt_id' x).const_mul k).add_const c
  have hc := (Real.hasDerivAt_cosh _).comp x hlin
  have hl := hc.log (Real.cosh_pos _).ne'
  have h := ((((hasDerivAt_id' x).const_mul (9 * p.kappa / (2 * a p))).sub hl).div_const (8 * p.kappa)).const_add t
  rw [g62f_v_eq]
  refine h.congr_deriv ?_
  -- value
  have htc : Real.sinh c / Real.cosh c = 1 / 3 := by
    rw [← Real.tanh_eq_sinh_div_cosh, hcdef, Real.tanh_artanh (by norm_num)]
  have hcc := Real.cosh_pos c
  have hcs : Real.cosh c = 3 * Real.sinh c := by field_simp at htc; linarith
  have hsc : 0 < Real.sinh c := by nlinarith
  rw [g62f_ss_add, ← hkdef]
  simp only [Function.comp_apply, Function.comp, mul_one]
  rw [Real.sinh_add, Real.cosh_add, hcs]
  have hC := Real.cosh_pos (k * x)
  have hden : 0 < Real.cosh (k * x) * (3 * Real.sinh c) + Real.sinh (k * x) * Real.sinh c := by
    have : 0 < Real.cosh (k * x + c) := Real.cosh_pos _
    rw [Real.cosh_add, hcs] at this; exact this
  have hden2 : 0 < 3 * Real.cosh (k * x) + Real.sinh (k * x) := by
    have : (3 * Real.cosh (k * x) + Real.sinh (k * x)) * Real.sinh c = Real.cosh (k * x) * (3 * Real.sinh c) + Real.sinh (k * x) * Real.sinh c := by ring
    by_contra hh; push_neg at hh; nlinarith
  rw [hkdef]
  rw [hkdef] at hden hden2 hC
  generalize Real.sinh (3 * p.kappa / (2 * a p) * x) = S at *
  generalize Real.cosh (3 * p.kappa / (2 * a p) * x) = C at *
  have h1 := hden.ne'; have h2 := hden2.ne'; have h3 := hC.ne'; have h4 := ha.ne'; have h5 := hk.ne'
  have h6 : S + C * 3 ≠ 0 := by intro h; apply h2; linarith
  have h7 : C * 3 + S ≠ 0 := by intro h; apply h2; linarith
  have h8 : S + 3 * C ≠ 0 := by intro h; apply h2; linarith
  field_simp
  ring

lemma g62f_cosh2 (w : ℝ) : Real.cosh (w + Real.artanh (1 / 3 : ℝ)) =
    Real.sqrt 2 * (Real.exp w + (Real.exp w)⁻¹ / 2) / 2 := by
  rw [g62f_cosh, Real.exp_neg]
  have ht : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht0 : 0 < Real.sqrt 2 := by positivity
  have hX := Real.exp_pos w
  field_simp
  rw [ht]; ring

lemma g62f_mappedW0 (p : AcousticModel) (x : ℝ) : advancedIn p (v p 0 x) = x / (p.cin + a p) := by
  have ha := g62f_a_pos p
  have hac := g62f_a_lt p
  have hk := p.kappa_pos
  have hB := g62f_B_pos p
  have ht : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have ht0 : 0 < Real.sqrt 2 := by positivity
  have hwx : z p x = B p * (x / (p.cin + a p)) := by
    have : p.cin + a p ≠ 0 := by linarith
    unfold z B; field_simp
  unfold advancedIn advancedPrinted advancedOffset
  rw [g62f_v0]
  have hexp : Real.exp (-8 * p.kappa * ((3 * z p x - Real.log (Real.cosh (z p x + Real.artanh (1 / 3 : ℝ)))) / (8 * p.kappa)))
      = Real.cosh (z p x + Real.artanh (1 / 3 : ℝ)) * ((Real.exp (z p x)) ^ 3)⁻¹ := by
    rw [show -8 * p.kappa * ((3 * z p x - Real.log (Real.cosh (z p x + Real.artanh (1 / 3 : ℝ)))) / (8 * p.kappa))
      = Real.log (Real.cosh (z p x + Real.artanh (1 / 3 : ℝ))) + -((3:ℕ) * z p x) by field_simp; ring]
    rw [Real.exp_add, Real.exp_log (Real.cosh_pos _), Real.exp_neg, Real.exp_nat_mul]
  rw [hexp, g62f_cosh2]
  have hlogX : Real.log (Real.exp (z p x)) = z p x := Real.log_exp _
  have hX0 := Real.exp_pos (z p x)
  generalize Real.exp (z p x) = X at hlogX hX0 ⊢
  have hsq : 1 + 2 * Real.sqrt 2 * (Real.sqrt 2 * (X + X⁻¹ / 2) / 2 * (X ^ 3)⁻¹) = (1 + 1 / X ^ 2) ^ 2 := by
    rw [show 2 * Real.sqrt 2 * (Real.sqrt 2 * (X + X⁻¹ / 2) / 2 * (X ^ 3)⁻¹)
      = Real.sqrt 2 ^ 2 * ((X + X⁻¹ / 2) * (X ^ 3)⁻¹) by ring, ht]
    field_simp; ring
  rw [hsq, Real.sqrt_sq (by positivity)]
  have hY : 0 < X + X⁻¹ / 2 := by positivity
  have hl1 : Real.log (Real.sqrt 2 * (X + X⁻¹ / 2) / 2) = Real.log (Real.sqrt 2) + Real.log (X + X⁻¹ / 2) - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul ht0.ne' hY.ne']
  have hl2 : Real.log (1 + (1 + 1 / X ^ 2)) = Real.log (X + X⁻¹ / 2) + Real.log 2 - z p x := by
    rw [← hlogX, show 1 + (1 + 1 / X ^ 2) = (X + X⁻¹ / 2) * 2 / X by field_simp; ring,
      Real.log_div (by positivity) hX0.ne', Real.log_mul hY.ne' (by norm_num)]
  have hl3 : Real.log (2 * Real.sqrt 2) = Real.log 2 + Real.log (Real.sqrt 2) := Real.log_mul (by norm_num) ht0.ne'
  have hl4 : 2 * Real.log (Real.sqrt 2) = Real.log 2 := by
    have := Real.log_pow (Real.sqrt 2) 2; rw [ht] at this; push_cast at this; linarith
  rw [hl1, hl2, hl3, ← hl4, hwx]
  field_simp; ring


lemma g62f_flow (p : AcousticModel) (Φ₁ Φ₁' Φ₂ Φ₂' : ℝ → ℝ) (Φ₁'' Φ₂'' : ℝ) (q₁ q₂ : ℝ → ℝ → ℝ)
    (t x xp a1t a1x b1t b1x a2t a2x b2t b2x : ℝ)
    (h1t : HasDerivAt (fun s => q₁ s x) a1t t) (h1x : HasDerivAt (fun y => q₁ t y) a1x x)
    (h1t' : HasDerivAt (fun s => q₁ s xp) b1t t) (h1x' : HasDerivAt (fun y => q₁ t y) b1x xp)
    (h2t : HasDerivAt (fun s => q₂ s x) a2t t) (h2x : HasDerivAt (fun y => q₂ t y) a2x x)
    (h2t' : HasDerivAt (fun s => q₂ s xp) b2t t) (h2x' : HasDerivAt (fun y => q₂ t y) b2x xp)
    (S₁ S₂ : Set ℝ) (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂)
    (hm₁ : q₁ t x - q₁ t xp ∈ S₁) (hm₂ : q₂ t x - q₂ t xp ∈ S₂)
    (hΦ₁ : ∀ d ∈ S₁, HasDerivAt Φ₁ (Φ₁' d) d) (hΦ₂ : ∀ d ∈ S₂, HasDerivAt Φ₂ (Φ₂' d) d)
    (hΦ₁' : HasDerivAt Φ₁' Φ₁'' (q₁ t x - q₁ t xp)) (hΦ₂' : HasDerivAt Φ₂' Φ₂'' (q₂ t x - q₂ t xp)) :
    flowFirst p (flowSecond p (fun t x tp xp => Φ₁ (q₁ t x - q₁ tp xp) + Φ₂ (q₂ t x - q₂ tp xp))) t x t xp
      = -Φ₁'' * (a1t + p.V * a1x) * (b1t + p.V * b1x) - Φ₂'' * (a2t + p.V * a2x) * (b2t + p.V * b2x) := by
  set K : FieldKernel := fun t x tp xp => Φ₁ (q₁ t x - q₁ tp xp) + Φ₂ (q₂ t x - q₂ tp xp) with hK
  have hsec : ∀ s y, q₁ s y - q₁ t xp ∈ S₁ → q₂ s y - q₂ t xp ∈ S₂ →
      flowSecond p K s y t xp = -(Φ₁' (q₁ s y - q₁ t xp)) * (b1t + p.V * b1x)
        - Φ₂' (q₂ s y - q₂ t xp) * (b2t + p.V * b2x) := by
    intro s y m1 m2
    unfold flowSecond
    have d1 : HasDerivAt (fun σ => K s y σ xp)
        (Φ₁' (q₁ s y - q₁ t xp) * (-b1t) + Φ₂' (q₂ s y - q₂ t xp) * (-b2t)) t := by
      have := ((hΦ₁ _ m1).comp t (h1t'.const_sub (q₁ s y))).add ((hΦ₂ _ m2).comp t (h2t'.const_sub (q₂ s y)))
      exact this
    have d2 : HasDerivAt (fun w => K s y t w)
        (Φ₁' (q₁ s y - q₁ t xp) * (-b1x) + Φ₂' (q₂ s y - q₂ t xp) * (-b2x)) xp := by
      have := ((hΦ₁ _ m1).comp xp (h1x'.const_sub (q₁ s y))).add ((hΦ₂ _ m2).comp xp (h2x'.const_sub (q₂ s y)))
      exact this
    rw [d1.deriv, d2.deriv]; ring
  -- time direction
  have e1 : ∀ᶠ s in nhds t, q₁ s x - q₁ t xp ∈ S₁ :=
    (h1t.continuousAt.sub continuousAt_const).preimage_mem_nhds (hS₁.mem_nhds hm₁)
  have e2 : ∀ᶠ s in nhds t, q₂ s x - q₂ t xp ∈ S₂ :=
    (h2t.continuousAt.sub continuousAt_const).preimage_mem_nhds (hS₂.mem_nhds hm₂)
  have hF : HasDerivAt (fun s => -(Φ₁' (q₁ s x - q₁ t xp)) * (b1t + p.V * b1x)
        - Φ₂' (q₂ s x - q₂ t xp) * (b2t + p.V * b2x))
      (-(Φ₁'' * a1t) * (b1t + p.V * b1x) - Φ₂'' * a2t * (b2t + p.V * b2x)) t := by
    have := ((hΦ₁'.comp t (h1t.sub_const (q₁ t xp))).neg.mul_const (b1t + p.V * b1x)).sub
      ((hΦ₂'.comp t (h2t.sub_const (q₂ t xp))).mul_const (b2t + p.V * b2x))
    exact this
  have hev : (fun s => flowSecond p K s x t xp) =ᶠ[nhds t] (fun s => -(Φ₁' (q₁ s x - q₁ t xp)) * (b1t + p.V * b1x)
        - Φ₂' (q₂ s x - q₂ t xp) * (b2t + p.V * b2x)) := by
    filter_upwards [e1, e2] with s m1 m2; exact hsec s x m1 m2
  -- space direction
  have f1 : ∀ᶠ y in nhds x, q₁ t y - q₁ t xp ∈ S₁ :=
    (h1x.continuousAt.sub continuousAt_const).preimage_mem_nhds (hS₁.mem_nhds hm₁)
  have f2 : ∀ᶠ y in nhds x, q₂ t y - q₂ t xp ∈ S₂ :=
    (h2x.continuousAt.sub continuousAt_const).preimage_mem_nhds (hS₂.mem_nhds hm₂)
  have hG : HasDerivAt (fun y => -(Φ₁' (q₁ t y - q₁ t xp)) * (b1t + p.V * b1x)
        - Φ₂' (q₂ t y - q₂ t xp) * (b2t + p.V * b2x))
      (-(Φ₁'' * a1x) * (b1t + p.V * b1x) - Φ₂'' * a2x * (b2t + p.V * b2x)) x := by
    have := ((hΦ₁'.comp x (h1x.sub_const (q₁ t xp))).neg.mul_const (b1t + p.V * b1x)).sub
      ((hΦ₂'.comp x (h2x.sub_const (q₂ t xp))).mul_const (b2t + p.V * b2x))
    exact this
  have hev' : (fun y => flowSecond p K t y t xp) =ᶠ[nhds x] (fun y => -(Φ₁' (q₁ t y - q₁ t xp)) * (b1t + p.V * b1x)
        - Φ₂' (q₂ t y - q₂ t xp) * (b2t + p.V * b2x)) := by
    filter_upwards [f1, f2] with y m1 m2; exact hsec t y m1 m2
  unfold flowFirst
  rw [(hF.congr_of_eventuallyEq hev).deriv, (hG.congr_of_eventuallyEq hev').deriv]
  ring

lemma g62f_V (p : AcousticModel) : p.V = -a p := by
  unfold a; rw [abs_of_neg p.V_neg]; ring

lemma g62f_logabs (c : ℝ) : ∀ d ∈ ({0}ᶜ : Set ℝ), HasDerivAt (fun d => c * Real.log |d|) (c * d⁻¹) d := by
  intro d hd
  have e : (fun d : ℝ => c * Real.log |d|) = fun d => c * Real.log d := by funext d; rw [Real.log_abs]
  rw [e]; exact (Real.hasDerivAt_log hd).const_mul c

lemma g62f_inv (c d : ℝ) (hd : d ≠ 0) : HasDerivAt (fun d : ℝ => c * d⁻¹) (c * (-(d ^ 2)⁻¹)) d :=
  (hasDerivAt_inv hd).const_mul c

lemma g62f_vac_init (p : AcousticModel) :
    (∀ t x xp : ℝ, t < 0 → x ≠ xp →
      initialDensity p t x xp = -correlatorScale p / p.cin *
        (1 / ((p.cin - a p) ^ 2 * (initialU p t x - initialU p t xp) ^ 2) +
         1 / ((p.cin + a p) ^ 2 * (initialW p t x - initialW p t xp) ^ 2))) := by
  intro t x xp _ hxx
  have ha := g62f_a_pos p
  have hac := g62f_a_lt p
  have hc : 0 < p.cin := by linarith
  have hca : p.cin - a p ≠ 0 := by linarith
  have hca' : p.cin + a p ≠ 0 := by linarith
  have hsub : x - xp ≠ 0 := sub_ne_zero.mpr hxx
  have hU : initialU p t x - initialU p t xp ≠ 0 := by
    unfold initialU; rw [show t - x / (p.cin - a p) - (t - xp / (p.cin - a p)) = -((x - xp) / (p.cin - a p)) by ring]
    exact neg_ne_zero.mpr (div_ne_zero hsub hca)
  have hW : initialW p t x - initialW p t xp ≠ 0 := by
    unfold initialW; rw [show t + x / (p.cin + a p) - (t + xp / (p.cin + a p)) = (x - xp) / (p.cin + a p) by ring]
    exact div_ne_zero hsub hca'
  have dUt : ∀ y, HasDerivAt (fun s => initialU p s y) 1 t := fun y => (hasDerivAt_id' t).sub_const _
  have dWt : ∀ y, HasDerivAt (fun s => initialW p s y) 1 t := fun y => (hasDerivAt_id' t).add_const _
  have dUx : ∀ y, HasDerivAt (fun y => initialU p t y) (-(1 / (p.cin - a p))) y := fun y =>
    (((hasDerivAt_id' y).div_const (p.cin - a p)).const_sub t).congr_deriv (by ring)
  have dWx : ∀ y, HasDerivAt (fun y => initialW p t y) (1 / (p.cin + a p)) y := fun y =>
    (((hasDerivAt_id' y).div_const (p.cin + a p)).const_add t).congr_deriv (by ring)
  have hf := g62f_flow p (fun d => -p.hbar / (4 * Real.pi) * Real.log |d|) (fun d => -p.hbar / (4 * Real.pi) * d⁻¹)
    (fun d => -p.hbar / (4 * Real.pi) * Real.log |d|) (fun d => -p.hbar / (4 * Real.pi) * d⁻¹)
    _ _ (initialU p) (initialW p) t x xp _ _ _ _ _ _ _ _
    (dUt x) (dUx x) (dUt xp) (dUx xp) (dWt x) (dWx x) (dWt xp) (dWx xp)
    {0}ᶜ {0}ᶜ isOpen_compl_singleton isOpen_compl_singleton hU hW
    (g62f_logabs _) (g62f_logabs _) (g62f_inv _ _ hU) (g62f_inv _ _ hW)
  unfold initialDensity densityObservable
  have hK : (fun t x tp xp => vacuumSector p (initialU p) t x tp xp + vacuumSector p (initialW p) t x tp xp)
      = (fun t x tp xp => (fun d => -p.hbar / (4 * Real.pi) * Real.log |d|) (initialU p t x - initialU p tp xp)
          + (fun d => -p.hbar / (4 * Real.pi) * Real.log |d|) (initialW p t x - initialW p tp xp)) := rfl
  rw [hK, hf]
  have hsq : Real.sqrt (p.m ^ 2 * p.cin * p.cin / n1 p ^ 2) = p.m * p.cin / n1 p := by
    have hn : 0 < n1 p := by unfold n1; have := p.n_pos; have := p.lperp_pos; positivity
    rw [show p.m ^ 2 * p.cin * p.cin / n1 p ^ 2 = (p.m * p.cin / n1 p) ^ 2 by field_simp]
    exact Real.sqrt_sq (by have := p.m_pos; positivity)
  rw [hsq, g62f_V]
  have hn : 0 < n1 p := by unfold n1; have := p.n_pos; have := p.lperp_pos; positivity
  have hm := p.m_pos
  have hpi := Real.pi_pos
  unfold correlatorScale
  field_simp
  ring

lemma g62f_advShell (p : AcousticModel) (r : ℝ) : advancedShell p (advancedIn p r) = r := by
  have ha := g62f_a_pos p
  have hac := g62f_a_lt p
  have hk := p.kappa_pos
  have hB := g62f_B_pos p
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2p : 0 < Real.sqrt 2 := by positivity
  have hw : z p ((p.cin + a p) * advancedIn p r) = B p * advancedIn p r := by unfold z B; field_simp
  unfold advancedShell; rw [g62f_v0, hw]
  have h2w : 2 * (B p * advancedIn p r) = 8 * p.kappa * r +
      Real.log (1 + Real.sqrt (1 + 2 * Real.sqrt 2 * Real.exp (-8 * p.kappa * r))) - Real.log (2 * Real.sqrt 2) := by
    unfold advancedIn advancedPrinted advancedOffset; field_simp; ring
  generalize B p * advancedIn p r = w at h2w ⊢
  have hS0 : 0 ≤ Real.sqrt (1 + 2 * Real.sqrt 2 * Real.exp (-8 * p.kappa * r)) := Real.sqrt_nonneg _
  have hY : Real.exp w ^ 2 = Real.exp (8 * p.kappa * r) *
      (1 + Real.sqrt (1 + 2 * Real.sqrt 2 * Real.exp (-8 * p.kappa * r))) / (2 * Real.sqrt 2) := by
    rw [sq, ← Real.exp_add, show w + w = 2 * w by ring, h2w, Real.exp_sub, Real.exp_add,
      Real.exp_log (by positivity), Real.exp_log (by positivity)]
  have hc : Real.cosh (w + Real.artanh (1 / 3 : ℝ)) = Real.exp (3 * w - 8 * p.kappa * r) := by
    rw [g62f_cosh, show 3 * w - 8 * p.kappa * r = w + 2 * w + (-8 * p.kappa * r) by ring,
      Real.exp_add, Real.exp_add, Real.exp_neg w,
      show Real.exp (2 * w) = Real.exp w ^ 2 by rw [sq, ← Real.exp_add]; ring_nf, hY]
    have hE0 := Real.exp_pos (-8 * p.kappa * r)
    have hQE : Real.exp (8 * p.kappa * r) * Real.exp (-8 * p.kappa * r) = 1 := by
      rw [← Real.exp_add]; simp
    have hX0 := Real.exp_pos w
    generalize Real.exp w = X at hY hX0 ⊢
    generalize Real.exp (-8 * p.kappa * r) = E at hY hQE hE0 hS0 ⊢
    generalize Real.exp (8 * p.kappa * r) = Q at hY hQE ⊢
    have hS : Real.sqrt (1 + 2 * Real.sqrt 2 * E) ^ 2 = 1 + 2 * Real.sqrt 2 * E := Real.sq_sqrt (by positivity)
    generalize Real.sqrt (1 + 2 * Real.sqrt 2 * E) = S at hY hS hS0 ⊢
    generalize ht' : Real.sqrt 2 = t at hY hS hs2 hs2p ⊢
    have h1 : 2 * t * X ^ 2 * E = 1 + S := by
      calc 2 * t * X ^ 2 * E = (Q * E) * (1 + S) := by rw [hY]; field_simp
        _ = 1 + S := by rw [hQE, one_mul]
    have h2' : (S - 1) * X ^ 2 * (2 * t * E) = 1 * (2 * t * E) := by
      linear_combination (S - 1) * h1 + hS
    have h2 : (S - 1) * X ^ 2 = 1 := mul_right_cancel₀ (by positivity) h2'
    have hS' : S = 1 + 1 / X ^ 2 := by field_simp; linarith
    have hR : X * (Q * (1 + S) / (2 * t)) * E = X * (1 + S) * (Q * E) / (2 * t) := by ring
    rw [hR, hQE, mul_one]
    have hL : (t * X + X⁻¹ / t) / 2 = (t ^ 2 * X ^ 2 + 1) / (2 * t * X) := by
      field_simp
    rw [hL, hs2, hS']
    field_simp; ring
  rw [hc, Real.log_exp]; field_simp; ring

lemma g62f_retIn_fun (p : AcousticModel) (s : ℝ) :
    retardedIn p s = fun r => (s / A p) * Real.arsinh (Real.exp (-p.kappa * r)) := by
  funext r; exact g62f_retIn p s r

lemma g62f_retIn_hd (p : AcousticModel) (s r : ℝ) :
    HasDerivAt (retardedIn p s) (deriv (retardedIn p s) r) r := by
  apply hasDerivAt_deriv_iff.mpr
  rw [g62f_retIn_fun]
  exact (((Real.hasDerivAt_arsinh _).comp r (((hasDerivAt_id' r).const_mul (-p.kappa)).exp)).const_mul (s / A p)).differentiableAt

lemma g62f_advIn_hd (p : AcousticModel) (r : ℝ) :
    HasDerivAt (advancedIn p) (deriv (advancedIn p) r) r := by
  apply hasDerivAt_deriv_iff.mpr
  have e : advancedIn p = fun r => 4 * p.kappa * r / B p + Real.log (1 +
      Real.sqrt (1 + 2 * Real.sqrt 2 * Real.exp (-8 * p.kappa * r))) / (2 * B p) - advancedOffset p := by
    funext r; rfl
  rw [e]
  fun_prop (disch := positivity)

lemma g62f_side_ev (x : ℝ) (hx : x ≠ 0) : ∀ᶠ y in nhds x, side y = side x := by
  rcases hx.lt_or_gt with h | h
  · filter_upwards [Iio_mem_nhds h] with y hy
    unfold side; rw [if_neg (not_lt.mpr (le_of_lt hy)), if_neg (not_lt.mpr h.le)]
  · filter_upwards [Ioi_mem_nhds h] with y hy
    unfold side; rw [if_pos (show 0 < y from hy), if_pos h]

lemma g62f_mU (p : AcousticModel) (t x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun s => mappedU p s x) (deriv (retardedIn p (side x)) (u p t x) * 1) t ∧
    HasDerivAt (fun y => mappedU p t y)
      (deriv (retardedIn p (side x)) (u p t x) * (-1 / (soundSpeed p x - a p))) x := by
  have hR := g62f_retIn_hd p (side x) (u p t x)
  constructor
  · exact hR.comp t ((hasDerivAt_id' t).sub_const _)
  · have hu : HasDerivAt (u p t) (-1 / (soundSpeed p x - a p)) x := by
      rcases hx.lt_or_gt with h | h
      · exact g62f_u_deriv p t x (-1) (Or.inr ⟨rfl, h⟩) (hasDerivAt_abs_neg h)
      · exact g62f_u_deriv p t x 1 (Or.inl ⟨rfl, h⟩) (hasDerivAt_abs_pos h)
    have h1 := hR.comp x hu
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [g62f_side_ev x hx] with y hy
    simp only [mappedU, Function.comp, hy]

lemma g62f_mW (p : AcousticModel) (t x : ℝ) :
    HasDerivAt (fun s => mappedW p s x) (deriv (advancedIn p) (v p t x) * 1) t ∧
    HasDerivAt (fun y => mappedW p t y)
      (deriv (advancedIn p) (v p t x) * (1 / (soundSpeed p x + a p))) x := by
  have hR := g62f_advIn_hd p (v p t x)
  constructor
  · exact hR.comp t ((hasDerivAt_id' t).add_const _)
  · exact hR.comp x (g62f_v_deriv p t x)

lemma g62f_ss_add_pos (p : AcousticModel) (x : ℝ) : 0 < soundSpeed p x + a p := by
  have ha := g62f_a_pos p
  have := Real.neg_one_lt_tanh (z p x)
  unfold soundSpeed; nlinarith

lemma g62f_ss_pos (p : AcousticModel) (x : ℝ) : 0 < soundSpeed p x := by
  have ha := g62f_a_pos p
  have := Real.neg_one_lt_tanh (z p x)
  unfold soundSpeed; nlinarith

lemma g62f_ss_gt (p : AcousticModel) (x : ℝ) (hx : 0 < x) : a p < soundSpeed p x := by
  have ha := g62f_a_pos p
  have : 0 < z p x := by unfold z; have := p.kappa_pos; positivity
  have := g62f_tanh_pos this
  unfold soundSpeed; nlinarith

lemma g62f_ss_lt (p : AcousticModel) (x : ℝ) (hx : x < 0) : soundSpeed p x < a p := by
  have ha := g62f_a_pos p
  have : z p x < 0 := by
    unfold z; apply div_neg_of_neg_of_pos _ (by linarith); nlinarith [p.kappa_pos]
  have := g62f_tanh_neg this
  unfold soundSpeed; nlinarith

lemma g62f_v_mono (p : AcousticModel) (t : ℝ) : StrictMono (v p t) := by
  apply strictMono_of_deriv_pos
  intro y
  rw [(g62f_v_deriv p t y).deriv]
  exact one_div_pos.mpr (g62f_ss_add_pos p y)

lemma g62f_mU_sign (p : AcousticModel) (t x xp : ℝ) (hx : 0 < x) (hxp : xp < 0) :
    mappedU p t x < 0 ∧ 0 < mappedU p t xp := by
  have hA := g62f_A_neg p
  unfold mappedU side
  rw [if_pos hx, if_neg (not_lt.mpr hxp.le), g62f_retIn, g62f_retIn]
  constructor
  · exact mul_neg_of_neg_of_pos (div_neg_of_pos_of_neg one_pos hA) (Real.arsinh_pos_iff.mpr (Real.exp_pos _))
  · exact mul_pos (div_pos_of_neg_of_neg (by norm_num) hA) (Real.arsinh_pos_iff.mpr (Real.exp_pos _))

lemma g62f_mW_ne (p : AcousticModel) (t x xp : ℝ) (h : xp < x) : mappedW p t x - mappedW p t xp ≠ 0 := by
  intro h0
  have : advancedIn p (v p t x) = advancedIn p (v p t xp) := by unfold mappedW at h0; linarith
  have h2 := congrArg (advancedShell p) this
  rw [g62f_advShell, g62f_advShell] at h2
  exact (g62f_v_mono p t h).ne' h2

lemma g62f_sqrt_pref (p : AcousticModel) (c1 c2 : ℝ) (h1 : 0 < c1) (h2 : 0 < c2) :
    Real.sqrt (p.m ^ 2 * c1 * c2 / n1 p ^ 2) = p.m / n1 p * Real.sqrt (c1 * c2) := by
  have hn : 0 < n1 p := by unfold n1; have := p.n_pos; have := p.lperp_pos; positivity
  have hm := p.m_pos
  rw [show p.m ^ 2 * c1 * c2 / n1 p ^ 2 = (p.m / n1 p) ^ 2 * (c1 * c2) by field_simp,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

lemma g62f_vac_post (p : AcousticModel) :
    (∀ t x xp : ℝ, 0 < t → 0 < x → xp < 0 →
      vacuumDensity p t x xp = -correlatorScale p / Real.sqrt (soundSpeed p x * soundSpeed p xp) *
        (uFactor p t x xp / (mappedU p t x - mappedU p t xp) ^ 2 +
         vFactor p t x xp / (mappedW p t x - mappedW p t xp) ^ 2)) := by
  intro t x xp _ hx hxp
  have hU : mappedU p t x - mappedU p t xp ≠ 0 := by
    have := g62f_mU_sign p t x xp hx hxp; linarith
  have hW := g62f_mW_ne p t x xp (by linarith)
  have hf := g62f_flow p (fun d => -p.hbar / (4 * Real.pi) * Real.log |d|) (fun d => -p.hbar / (4 * Real.pi) * d⁻¹)
    (fun d => -p.hbar / (4 * Real.pi) * Real.log |d|) (fun d => -p.hbar / (4 * Real.pi) * d⁻¹)
    _ _ (mappedU p) (mappedW p) t x xp _ _ _ _ _ _ _ _
    (g62f_mU p t x hx.ne').1 (g62f_mU p t x hx.ne').2 (g62f_mU p t xp hxp.ne).1 (g62f_mU p t xp hxp.ne).2
    (g62f_mW p t x).1 (g62f_mW p t x).2 (g62f_mW p t xp).1 (g62f_mW p t xp).2
    {0}ᶜ {0}ᶜ isOpen_compl_singleton isOpen_compl_singleton hU hW
    (g62f_logabs _) (g62f_logabs _) (g62f_inv _ _ hU) (g62f_inv _ _ hW)
  unfold vacuumDensity densityObservable
  have hK : (fun t x tp xp => vacuumSector p (mappedU p) t x tp xp + vacuumSector p (mappedW p) t x tp xp)
      = (fun t x tp xp => (fun d => -p.hbar / (4 * Real.pi) * Real.log |d|) (mappedU p t x - mappedU p tp xp)
          + (fun d => -p.hbar / (4 * Real.pi) * Real.log |d|) (mappedW p t x - mappedW p tp xp)) := rfl
  rw [hK, hf]
  have c1 := g62f_ss_pos p x
  have c2 := g62f_ss_pos p xp
  have c3 := g62f_ss_add_pos p x
  have c4 := g62f_ss_add_pos p xp
  have c5 : soundSpeed p x - a p ≠ 0 := (sub_pos.mpr (g62f_ss_gt p x hx)).ne'
  have c6 : soundSpeed p xp - a p ≠ 0 := (sub_neg.mpr (g62f_ss_lt p xp hxp)).ne
  rw [g62f_sqrt_pref p _ _ c1 c2, g62f_V]
  have hP : 0 < Real.sqrt (soundSpeed p x * soundSpeed p xp) := Real.sqrt_pos.mpr (mul_pos c1 c2)
  have hPP := Real.mul_self_sqrt (mul_pos c1 c2).le
  have hinv : -correlatorScale p / Real.sqrt (soundSpeed p x * soundSpeed p xp) =
      -correlatorScale p * Real.sqrt (soundSpeed p x * soundSpeed p xp) / (soundSpeed p x * soundSpeed p xp) := by
    generalize Real.sqrt (soundSpeed p x * soundSpeed p xp) = P at hP hPP ⊢
    rw [← hPP]; field_simp
  rw [hinv]
  have hn : 0 < n1 p := by unfold n1; have := p.n_pos; have := p.lperp_pos; positivity
  have hm := p.m_pos
  have hpi := Real.pi_pos
  have c3' := c3.ne'
  have c4' := c4.ne'
  unfold correlatorScale uFactor vFactor
  field_simp
  ring

lemma g62f_thΦ (c0 A : ℝ) (hA : 0 < A) : ∀ d ∈ ({0}ᶜ : Set ℝ),
    HasDerivAt (fun d => c0 * Real.log |Real.sinh (A * d) / A|) (c0 * (A * Real.cosh (A * d) / Real.sinh (A * d))) d := by
  intro d hd
  have hd' : d ≠ 0 := hd
  have hs0 : Real.sinh (A * d) ≠ 0 := by
    intro h; rw [Real.sinh_eq_zero] at h; rcases mul_eq_zero.mp h with h | h
    · exact hA.ne' h
    · exact hd' h
  have e : (fun d : ℝ => c0 * Real.log |Real.sinh (A * d) / A|) = fun d => c0 * Real.log (Real.sinh (A * d) / A) := by
    funext d; rw [Real.log_abs]
  rw [e]
  have hs := ((Real.hasDerivAt_sinh _).comp d ((hasDerivAt_id' d).const_mul A)).div_const A
  have hl := (hs.log (div_ne_zero hs0 hA.ne')).const_mul c0
  refine hl.congr_deriv ?_
  simp only [Function.comp_apply]
  field_simp

lemma g62f_thΦ' (c0 A d : ℝ) (hA : 0 < A) (hd : d ≠ 0) :
    HasDerivAt (fun d => c0 * (A * Real.cosh (A * d) / Real.sinh (A * d)))
      (c0 * (-(A ^ 2) / Real.sinh (A * d) ^ 2)) d := by
  have hs0 : Real.sinh (A * d) ≠ 0 := by
    intro h; rw [Real.sinh_eq_zero] at h; rcases mul_eq_zero.mp h with h | h
    · exact hA.ne' h
    · exact hd h
  have hc := ((Real.hasDerivAt_cosh _).comp d ((hasDerivAt_id' d).const_mul A)).const_mul A
  have hs := (Real.hasDerivAt_sinh _).comp d ((hasDerivAt_id' d).const_mul A)
  have h := (hc.div hs hs0).const_mul c0
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  have key := Real.cosh_sq_sub_sinh_sq (A * d)
  field_simp
  linear_combination (-c0) * key

lemma g62f_Au_pos (p : AcousticModel) (T : ℝ) (hT : 0 < T) : 0 < Au p T := by
  have := g62f_a_lt p; have := p.kB_pos; have := p.hbar_pos; have := g62f_a_pos p
  unfold Au; apply div_pos
  · have : 0 < p.cin - a p := by linarith
    positivity
  · have : 0 < p.cin := by linarith
    positivity

lemma g62f_Av_pos (p : AcousticModel) (T : ℝ) (hT : 0 < T) : 0 < Av p T := by
  have := g62f_a_lt p; have := p.kB_pos; have := p.hbar_pos; have := g62f_a_pos p
  unfold Av; apply div_pos
  · have : 0 < p.cin + a p := by linarith
    positivity
  · have : 0 < p.cin := by linarith
    positivity

lemma g62f_sinh_ne (A d : ℝ) (hA : 0 < A) (hd : d ≠ 0) : Real.sinh (A * d) ≠ 0 := by
  intro h; rw [Real.sinh_eq_zero] at h; rcases mul_eq_zero.mp h with h | h
  · exact hA.ne' h
  · exact hd h


end

open Filter

theorem solution (p : AcousticModel) (T t x xp : ℝ)
    (hT : 0 < T) (ht : 0 < t) (hx : 0 < x) (hxp : xp < 0) :
    thermalDensityObservable p T t x xp =
      -correlatorScale p / Real.sqrt (soundSpeed p x * soundSpeed p xp) *
        (uFactor p t x xp * (Au p T) ^ 2 /
          (Real.sinh (Au p T * (mappedU p t x - mappedU p t xp))) ^ 2 +
         vFactor p t x xp * (Av p T) ^ 2 /
          (Real.sinh (Av p T * (mappedW p t x - mappedW p t xp))) ^ 2) := by
  have hU : mappedU p t x - mappedU p t xp ≠ 0 := by
    have := g62f_mU_sign p t x xp hx hxp; linarith
  have hW := g62f_mW_ne p t x xp (by linarith)
  have hAu := g62f_Au_pos p T hT
  have hAv := g62f_Av_pos p T hT
  have hf := g62f_flow p (fun d => -p.hbar / (4 * Real.pi) * Real.log |Real.sinh (Au p T * d) / Au p T|)
    (fun d => -p.hbar / (4 * Real.pi) * (Au p T * Real.cosh (Au p T * d) / Real.sinh (Au p T * d)))
    (fun d => -p.hbar / (4 * Real.pi) * Real.log |Real.sinh (Av p T * d) / Av p T|)
    (fun d => -p.hbar / (4 * Real.pi) * (Av p T * Real.cosh (Av p T * d) / Real.sinh (Av p T * d)))
    _ _ (mappedU p) (mappedW p) t x xp _ _ _ _ _ _ _ _
    (g62f_mU p t x hx.ne').1 (g62f_mU p t x hx.ne').2 (g62f_mU p t xp hxp.ne).1 (g62f_mU p t xp hxp.ne).2
    (g62f_mW p t x).1 (g62f_mW p t x).2 (g62f_mW p t xp).1 (g62f_mW p t xp).2
    {0}ᶜ {0}ᶜ isOpen_compl_singleton isOpen_compl_singleton hU hW
    (g62f_thΦ _ _ hAu) (g62f_thΦ _ _ hAv) (g62f_thΦ' _ _ _ hAu hU) (g62f_thΦ' _ _ _ hAv hW)
  unfold thermalDensityObservable densityObservable
  have hK : (fun t x tp xp => thermalSector p (Au p T) (mappedU p) t x tp xp + thermalSector p (Av p T) (mappedW p) t x tp xp)
      = (fun t x tp xp => (fun d => -p.hbar / (4 * Real.pi) * Real.log |Real.sinh (Au p T * d) / Au p T|) (mappedU p t x - mappedU p tp xp)
          + (fun d => -p.hbar / (4 * Real.pi) * Real.log |Real.sinh (Av p T * d) / Av p T|) (mappedW p t x - mappedW p tp xp)) := rfl
  rw [hK, hf]
  have c1 := g62f_ss_pos p x
  have c2 := g62f_ss_pos p xp
  have c3 := g62f_ss_add_pos p x
  have c4 := g62f_ss_add_pos p xp
  have c5 : soundSpeed p x - a p ≠ 0 := (sub_pos.mpr (g62f_ss_gt p x hx)).ne'
  have c6 : soundSpeed p xp - a p ≠ 0 := (sub_neg.mpr (g62f_ss_lt p xp hxp)).ne
  rw [g62f_sqrt_pref p _ _ c1 c2, g62f_V]
  have hP : 0 < Real.sqrt (soundSpeed p x * soundSpeed p xp) := Real.sqrt_pos.mpr (mul_pos c1 c2)
  have hPP := Real.mul_self_sqrt (mul_pos c1 c2).le
  have hinv : -correlatorScale p / Real.sqrt (soundSpeed p x * soundSpeed p xp) =
      -correlatorScale p * Real.sqrt (soundSpeed p x * soundSpeed p xp) / (soundSpeed p x * soundSpeed p xp) := by
    generalize Real.sqrt (soundSpeed p x * soundSpeed p xp) = P at hP hPP ⊢
    rw [← hPP]; field_simp
  rw [hinv]
  have hn : 0 < n1 p := by unfold n1; have := p.n_pos; have := p.lperp_pos; positivity
  have hm := p.m_pos
  have hpi := Real.pi_pos
  have c3' := c3.ne'
  have c4' := c4.ne'
  have s1 := g62f_sinh_ne _ _ hAu hU
  have s2 := g62f_sinh_ne _ _ hAv hW
  unfold correlatorScale uFactor vFactor
  field_simp
  ring
