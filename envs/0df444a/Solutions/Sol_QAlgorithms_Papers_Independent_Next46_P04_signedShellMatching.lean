-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P04.signedShellMatching
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T16:34:10.536001+00:00
-- url     : https://prove2.me/submissions/4f1d1472-bec8-4da5-89a6-190185e80932

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


end

open Filter

theorem solution (p : AcousticModel) :
    A p < 0 ∧ 0 < B p ∧
    (∀ s : ℝ, s = 1 ∨ s = -1 → ∀ r : ℝ,
      retardedShell p (retardedIn p s r) = r ∧
      -p.kappa * r = Real.log (Real.sinh |A p * retardedIn p s r|) ∧
      (s = 1 → retardedIn p s r < 0) ∧
      (s = -1 → 0 < retardedIn p s r)) ∧
    (∀ x : ℝ, x ≠ 0 → mappedU p 0 x = initialU p 0 x) ∧
    (∀ r : ℝ, advancedShell p (advancedIn p r) = r) ∧
    (∀ x : ℝ, mappedW p 0 x = initialW p 0 x ∧
      advancedPrinted p (v p 0 x) = initialW p 0 x + advancedOffset p) := by
  have ha := g62f_a_pos p
  have hac := g62f_a_lt p
  have hk := p.kappa_pos
  have hA := g62f_A_neg p
  have hB := g62f_B_pos p
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2p : 0 < Real.sqrt 2 := by positivity
  -- retarded
  have habs : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ r : ℝ,
      |A p * retardedIn p s r| = Real.arsinh (Real.exp (-p.kappa * r)) := by
    intro s hs r
    rw [g62f_retIn]
    have hpos : 0 < Real.arsinh (Real.exp (-p.kappa * r)) := Real.arsinh_pos_iff.mpr (Real.exp_pos _)
    have hA0 := hA.ne
    rcases hs with rfl | rfl
    · rw [show A p * (1 / A p * Real.arsinh (Real.exp (-p.kappa * r))) = Real.arsinh (Real.exp (-p.kappa * r)) by field_simp]
      exact abs_of_pos hpos
    · rw [show A p * (-1 / A p * Real.arsinh (Real.exp (-p.kappa * r))) = -Real.arsinh (Real.exp (-p.kappa * r)) by field_simp]
      rw [abs_neg]; exact abs_of_pos hpos
  have hlogs : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ r : ℝ,
      -p.kappa * r = Real.log (Real.sinh |A p * retardedIn p s r|) := by
    intro s hs r
    rw [habs s hs r, Real.sinh_arsinh, Real.log_exp]
  have hzabs : ∀ y : ℝ, z p |(-(p.cin - a p) * y)| = |A p * y| := by
    intro y
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < p.cin - a p), abs_of_neg hA, g62f_A_eq]
    unfold z; ring
  refine ⟨hA, hB, ?_, ?_, ?_, ?_⟩
  · intro s hs r
    refine ⟨?_, hlogs s hs r, ?_, ?_⟩
    · unfold retardedShell u
      rw [hzabs, ← hlogs s hs r]; field_simp; ring
    · rintro rfl; rw [g62f_retIn]
      exact mul_neg_of_neg_of_pos (div_neg_of_pos_of_neg one_pos hA) (Real.arsinh_pos_iff.mpr (Real.exp_pos _))
    · rintro rfl; rw [g62f_retIn]
      exact mul_pos (div_pos_of_neg_of_neg (by norm_num) hA) (Real.arsinh_pos_iff.mpr (Real.exp_pos _))
  · intro x hx
    unfold mappedU initialU
    rw [g62f_retIn]
    have hzx : 0 < z p |x| := by unfold z; have := abs_pos.mpr hx; positivity
    have hsh : 0 < Real.sinh (z p |x|) := Real.sinh_pos_iff.mpr hzx
    have : -p.kappa * u p 0 x = Real.log (Real.sinh (z p |x|)) := by
      unfold u; field_simp; ring
    rw [this, Real.exp_log hsh, Real.arsinh_sinh, g62f_A_eq]
    have hsd : side x * |x| = x := by
      unfold side; split_ifs with h
      · rw [abs_of_pos h]; ring
      · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h) hx)]; ring
    unfold z
    have h1 : p.cin - a p ≠ 0 := by linarith
    have hh : side x / -(3 * p.kappa * (p.cin - a p) / (2 * a p)) * (3 * p.kappa * |x| / (2 * a p))
        = -(side x * |x|) / (p.cin - a p) := by
      field_simp
    rw [hh, hsd]; ring
  · intro r
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
  · intro x
    have h := g62f_mappedW0 p x
    refine ⟨?_, ?_⟩
    · unfold mappedW initialW; rw [h]; ring
    · unfold initialW; unfold advancedIn at h; rw [zero_add, ← h]; ring
