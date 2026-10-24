-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P32.physical_degrading_map
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T14:13:48.938664+00:00
-- url     : https://prove2.me/submissions/c3922d80-3eda-4997-8388-f7d935902322

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32


noncomputable section
namespace X7PD
open QAlgorithms.Papers.Independent.Next46.P32

def amp (η : ℝ) (m l : ℕ) : ℝ :=
  Real.sqrt (Nat.choose (m + l) m) * Real.sqrt η ^ m * Real.sqrt (1 - η) ^ l

lemma sqrt_fact (m l : ℕ) :
    Real.sqrt (((Nat.factorial m : ℝ) * (Nat.factorial l : ℝ)) / (Nat.factorial (m + l) : ℝ)) *
      (Nat.choose (m + l) m : ℝ) = Real.sqrt (Nat.choose (m + l) m) := by
  have hC : (0 : ℝ) < Nat.choose (m + l) m := by exact_mod_cast Nat.choose_pos (by omega)
  have h : ((Nat.factorial (m + l)) : ℝ) = Nat.choose (m + l) m * (Nat.factorial m * Nat.factorial l) := by
    have := Nat.choose_mul_factorial_mul_factorial (show m ≤ m + l by omega)
    rw [show m + l - m = l by omega] at this
    exact_mod_cast (by rw [← this]; ring : (Nat.factorial (m+l)) = Nat.choose (m + l) m * (Nat.factorial m * Nat.factorial l))
  have hf : (0 : ℝ) < Nat.factorial m * Nat.factorial l := by positivity
  rw [h, div_mul_cancel_right₀ hf.ne', Real.sqrt_inv]
  have := Real.mul_self_sqrt hC.le
  have hs := Real.sqrt_pos.2 hC
  field_simp
  linarith

lemma beam_vac (η : ℝ) (m l p : ℕ) :
    beamCoefficient η m l p 0 = if m + l = p then amp η m l else 0 := by
  unfold beamCoefficient
  simp only [add_zero]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single m]
    · simp only [le_refl, Nat.sub_self, le_refl, and_self, if_true, Nat.choose_zero_right,
        Nat.cast_one, mul_one, pow_zero]
      rw [show m + l - m + 0 = l by omega, Nat.factorial_zero, Nat.cast_one, mul_one, amp,
        ← sqrt_fact m l]
      ring
    · intro u _ hu
      rw [if_neg]
      omega
    · intro hm; simp at hm
  · rfl

end X7PD


noncomputable section
namespace X7PD
open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (productCoeff)

def Amp {n : ℕ} (η : ℝ) (m l : NumberString n) : ℝ := ∏ i, amp η (m i) (l i)

lemma blockBeam_vac {n : ℕ} (η : ℝ) (u : NumberString n × NumberString n) (p : NumberString n) :
    blockBeam n η u (p, 0) = if u.1 + u.2 = p then ((Amp η u.1 u.2 : ℝ) : ℂ) else 0 := by
  unfold blockBeam Amp
  simp only [Pi.zero_apply, beam_vac]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, true_implies, funext_iff, Pi.add_apply]
  split_ifs <;> simp

lemma vac_apply {n : ℕ} (a b : NumberString n) :
    vacuum n a b = if a = 0 ∧ b = 0 then 1 else 0 := rfl

lemma broadcast_apply {n : ℕ} (η : ℝ) (X : FockKernel n) (u v : NumberString n × NumberString n) :
    broadcast n η X u v =
      ((Amp η u.1 u.2 * Amp η v.1 v.2 : ℝ) : ℂ) * X (u.1 + u.2) (v.1 + v.2) := by
  unfold broadcast jointMix
  have hin : ∀ a : NumberString n × NumberString n,
      (∑' b : NumberString n × NumberString n,
        blockBeam n η u a * productCoeff X (vacuum n) a b * star (blockBeam n η v b)) =
      blockBeam n η u a * productCoeff X (vacuum n) a (v.1 + v.2, 0) *
        star (blockBeam n η v (v.1 + v.2, 0)) := by
    intro a
    apply tsum_eq_single
    rintro ⟨b1, b2⟩ hb
    by_cases h2 : b2 = 0
    · subst h2
      rw [blockBeam_vac, if_neg]
      · simp
      · intro h; apply hb; rw [h]
    · simp [productCoeff, vac_apply, h2]
  simp_rw [hin]
  rw [tsum_eq_single (u.1 + u.2, (0 : NumberString n))]
  · rw [blockBeam_vac, blockBeam_vac, if_pos rfl, if_pos rfl]
    simp only [productCoeff, vac_apply, and_self, if_true, mul_one, Complex.star_def,
      Complex.conj_ofReal]
    push_cast; ring
  · rintro ⟨a1, a2⟩ ha
    by_cases h2 : a2 = 0
    · subst h2
      rw [blockBeam_vac, if_neg]
      · simp
      · intro h; apply ha; rw [h]
    · simp [productCoeff, vac_apply, h2]

lemma charlie_broadcast {n : ℕ} (η : ℝ) (X : FockKernel n) (a b : NumberString n) :
    charlieMarginal (broadcast n η X) a b =
      ∑' e, ((Amp η e a * Amp η e b : ℝ) : ℂ) * X (e + a) (e + b) := by
  simp only [charlieMarginal, broadcast_apply]

lemma bob_broadcast {n : ℕ} (η : ℝ) (X : FockKernel n) (a b : NumberString n) :
    bobMarginal (broadcast n η X) a b =
      ∑' e, ((Amp η a e * Amp η b e : ℝ) : ℂ) * X (a + e) (b + e) := by
  simp only [bobMarginal, broadcast_apply]

lemma pureLoss_apply {n : ℕ} (η : ℝ) (X : FockKernel n) (a b : NumberString n) :
    pureLoss n η X a b =
      ∑' e, ((Amp η a e * Amp η b e : ℝ) : ℂ) * X (a + e) (b + e) :=
  bob_broadcast η X a b

end X7PD


noncomputable section
namespace X7PD
open QAlgorithms.Papers.Independent.Next46.P32

lemma amp_nonneg (η : ℝ) (m l : ℕ) : 0 ≤ amp η m l := by unfold amp; positivity

lemma amp_sq (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) (m l : ℕ) :
    amp η m l ^ 2 = Nat.choose (m + l) m * η ^ m * (1 - η) ^ l := by
  unfold amp
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, ← pow_mul, mul_comm m 2, mul_comm l 2,
    pow_mul, pow_mul, Real.sq_sqrt h0, Real.sq_sqrt (by linarith)]

lemma amp_le_one (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) (m l : ℕ) : amp η m l ≤ 1 := by
  have hs : amp η m l ^ 2 ≤ 1 := by
    rw [amp_sq η h0 h1]
    have := add_pow η (1 - η) (m + l)
    rw [show η + (1 - η) = 1 by ring, one_pow] at this
    have hle := Finset.single_le_sum (s := Finset.range (m + l + 1))
      (f := fun j => η ^ j * (1 - η) ^ (m + l - j) * (Nat.choose (m + l) j : ℝ))
      (fun j _ => by have : 0 ≤ 1 - η := by linarith
                     positivity) (Finset.mem_range.2 (show m < m + l + 1 by omega))
    simp only [show m + l - m = l by omega] at hle
    linarith [show (Nat.choose (m + l) m : ℝ) * η ^ m * (1 - η) ^ l = η ^ m * (1 - η) ^ l * Nat.choose (m + l) m by ring]
  nlinarith [amp_nonneg η m l]

lemma fiber1 (η : ℝ) (h1 : 1 / 2 < η) (h2 : η ≤ 1) (a b k : ℕ) :
    ∑ f ∈ Finset.range (k + 1),
      amp ((1 - η) / η) a f * amp ((1 - η) / η) b f * amp η (a + f) (k - f) * amp η (b + f) (k - f) =
    amp η k a * amp η k b := by
  have hη : 0 < η := by linarith
  set x := Real.sqrt η with hx
  set y := Real.sqrt (1 - η) with hy
  set z := Real.sqrt (2 * η - 1) with hz
  have xpos : 0 < x := Real.sqrt_pos.2 hη
  have hx2 : x ^ 2 = η := Real.sq_sqrt hη.le
  have hy2 : y ^ 2 = 1 - η := Real.sq_sqrt (by linarith)
  have hz2 : z ^ 2 = 2 * η - 1 := Real.sq_sqrt (by linarith)
  have hc : Real.sqrt ((1 - η) / η) = y / x := by rw [Real.sqrt_div' _ hη.le]
  have hc' : Real.sqrt (1 - (1 - η) / η) = z / x := by
    rw [show 1 - (1 - η) / η = (2 * η - 1) / η by field_simp; ring, Real.sqrt_div' _ hη.le]
  have key : ∀ f ∈ Finset.range (k + 1),
      amp ((1 - η) / η) a f * amp ((1 - η) / η) b f * amp η (a + f) (k - f) * amp η (b + f) (k - f) =
      Real.sqrt (Nat.choose (a + k) a) * Real.sqrt (Nat.choose (b + k) b) * y ^ (a + b) *
        ((z ^ 2) ^ f * (y ^ 2) ^ (k - f) * Nat.choose k f) := by
    intro f hf
    have hfk : f ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hf)
    have hch : ∀ a : ℕ, Real.sqrt (Nat.choose (a + f) a) * Real.sqrt (Nat.choose (a + f + (k - f)) (a + f)) =
        Real.sqrt (Nat.choose (a + k) a) * Real.sqrt (Nat.choose k f) := by
      intro a
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
      congr 1
      have := Nat.choose_mul (n := a + k) (k := a + f) (s := a) (by omega)
      rw [show a + f + (k - f) = a + k by omega]
      rw [show a + k - a = k by omega, show a + f - a = f by omega] at this
      exact_mod_cast (by rw [mul_comm]; exact this)
    unfold amp
    rw [hc, hc', ← hx, ← hy]
    have e1 := hch a
    have e2 := hch b
    have hsk : Real.sqrt (Nat.choose k f) * Real.sqrt (Nat.choose k f) = Nat.choose k f :=
      Real.mul_self_sqrt (by positivity)
    have hxf : (z / x) ^ f * x ^ (a + f) = z ^ f * x ^ a := by
      rw [div_pow, pow_add]; field_simp
    have hyx : (y / x) ^ a * x ^ a = y ^ a := by rw [div_pow]; field_simp
    have hyx' : (y / x) ^ b * x ^ b = y ^ b := by rw [div_pow]; field_simp
    have hxf' : (z / x) ^ f * x ^ (b + f) = z ^ f * x ^ b := by
      rw [div_pow, pow_add]; field_simp
    calc _ = (Real.sqrt (Nat.choose (a + f) a) * Real.sqrt (Nat.choose (a + f + (k - f)) (a + f))) *
          (Real.sqrt (Nat.choose (b + f) b) * Real.sqrt (Nat.choose (b + f + (k - f)) (b + f))) *
          (((y / x) ^ a * x ^ a) * ((y / x) ^ b * x ^ b)) * ((z / x) ^ f * x ^ f) ^ 2 * (y ^ 2) ^ (k - f) := by ring
      _ = _ := by
        rw [e1, e2, hyx, hyx', show (z / x) ^ f * x ^ f = z ^ f by rw [div_pow]; field_simp]
        have hsq : Real.sqrt (Nat.choose k f) ^ 2 = Nat.choose k f := Real.sq_sqrt (by positivity)
        linear_combination (Real.sqrt (Nat.choose (a + k) a) * Real.sqrt (Nat.choose (b + k) b) * y ^ (a + b) *
          (z ^ 2) ^ f * (y ^ 2) ^ (k - f)) * hsq
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← add_pow, hz2, hy2,
    show 2 * η - 1 + (1 - η) = η by ring]
  unfold amp
  rw [← hx, ← hy, Nat.choose_symm_add, Nat.choose_symm_add, add_comm k a, add_comm k b, ← hx2]
  ring

end X7PD


noncomputable section
namespace X7PD
open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
attribute [local instance] Classical.propDecidable

lemma quad_pair {I : Type} (X : Matrix I I ℂ) {x y : I} (hxy : x ≠ y) (β : ℂ) :
    (∑ i ∈ ({x, y} : Finset I), ∑ j ∈ ({x, y} : Finset I),
      star ((fun i => if i = x then (1 : ℂ) else β) i) * X i j * (fun i => if i = x then (1 : ℂ) else β) j) =
    X x x + X x y * β + star β * X y x + star β * X y y * β := by
  rw [Finset.sum_pair hxy, Finset.sum_pair hxy, Finset.sum_pair hxy]
  simp only [if_pos rfl, if_neg hxy.symm, ↓reduceIte, star_one, one_mul, mul_one]
  ring

lemma diag_real {I : Type} {X : Matrix I I ℂ} (h : IsDensity X) (x : I) :
    (X x x).im = 0 ∧ 0 ≤ (X x x).re := by
  have := h.2.1 {x} (fun _ => 1)
  simpa using this

lemma entry_bound {I : Type} {X : Matrix I I ℂ} (h : IsDensity X) (x y : I) :
    ‖X x y‖ ≤ ((X x x).re + (X y y).re) / 2 := by
  by_cases hxy : x = y
  · subst hxy
    obtain ⟨h1, h2⟩ := diag_real h x
    have : X x x = ((X x x).re : ℂ) := Complex.ext (by simp) (by simp [h1])
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2]; simp
  have Q := fun β : ℂ => h.2.1 {x, y} (fun i => if i = x then (1 : ℂ) else β)
  simp only [quad_pair X hxy] at Q
  obtain ⟨dx1, dx2⟩ := diag_real h x
  obtain ⟨dy1, dy2⟩ := diag_real h y
  have q1 := (Q 1).1
  have q2 := (Q Complex.I).1
  simp [Complex.add_im, Complex.mul_im, dx1, dy1] at q1 q2
  have hq : X y x = star (X x y) := by
    apply Complex.ext <;> simp <;> linarith
  by_cases hp : X x y = 0
  · rw [hp, norm_zero]; linarith
  have hn : 0 < ‖X x y‖ := norm_pos_iff.2 hp
  set p := X x y
  have q3 := (Q (-(star p) / (‖p‖ : ℂ))).2
  rw [hq] at q3
  have e1 : p * (-(star p) / (‖p‖ : ℂ)) = -(‖p‖ : ℂ) := by
    have hn' : (‖p‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Complex.star_def, mul_div_assoc', mul_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [neg_div, sq, mul_div_assoc, div_self hn', mul_one]
  have e2 : star (-(star p) / (‖p‖ : ℂ)) * star p = -(‖p‖ : ℂ) := by
    rw [← star_mul', mul_comm, e1]; simp
  have e3 : star (-(star p) / (‖p‖ : ℂ)) * X y y * (-(star p) / (‖p‖ : ℂ)) =
      X y y * ((star (-(star p) / (‖p‖ : ℂ))) * (-(star p) / (‖p‖ : ℂ))) := by ring
  have e4 : (star (-(star p) / (‖p‖ : ℂ))) * (-(star p) / (‖p‖ : ℂ)) = 1 := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [norm_div, norm_neg, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn, div_self hn.ne']; simp
  rw [e1, e3, e4, mul_one] at q3
  rw [show X x x + -(‖p‖ : ℂ) + star (-(star p) / (‖p‖ : ℂ)) * star p + X y y =
    X x x + -(‖p‖ : ℂ) + -(‖p‖ : ℂ) + X y y by rw [e2]] at q3
  simp at q3
  linarith

lemma shift_summable {n : ℕ} {X : FockKernel n} (h : IsDensity X) (a b : NumberString n) :
    Summable (fun k : NumberString n => ‖X (k + a) (k + b)‖) := by
  have hd := h.2.2.1
  have ha : Summable (fun k : NumberString n => (X (k + a) (k + a)).re) :=
    hd.comp_injective (fun k k' hk => add_right_cancel hk)
  have hb : Summable (fun k : NumberString n => (X (k + b) (k + b)).re) :=
    hd.comp_injective (fun k k' hk => add_right_cancel hk)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => entry_bound h _ _) ?_
  exact (ha.add hb).div_const 2

def Fk {n : ℕ} (k : NumberString n) : Finset (NumberString n) :=
  Fintype.piFinset (fun i => Finset.range (k i + 1))

lemma mem_Fk {n : ℕ} (k f : NumberString n) : f ∈ Fk k ↔ f ≤ k := by
  simp [Fk, Fintype.mem_piFinset, Nat.lt_succ_iff, Pi.le_def]

lemma Amp_le_one {n : ℕ} (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) (m l : NumberString n) : Amp η m l ≤ 1 :=
  Finset.prod_le_one (fun i _ => amp_nonneg _ _ _) (fun i _ => amp_le_one η h0 h1 _ _)

lemma Amp_nonneg {n : ℕ} (η : ℝ) (m l : NumberString n) : 0 ≤ Amp η m l :=
  Finset.prod_nonneg (fun i _ => amp_nonneg _ _ _)

def kap {n : ℕ} (η : ℝ) (a b f e : NumberString n) : ℝ :=
  Amp ((1 - η) / η) a f * Amp ((1 - η) / η) b f * Amp η (a + f) e * Amp η (b + f) e

lemma kap_nonneg {n : ℕ} (η : ℝ) (a b f e : NumberString n) : 0 ≤ kap η a b f e := by
  unfold kap
  exact mul_nonneg (mul_nonneg (mul_nonneg (Amp_nonneg _ _ _) (Amp_nonneg _ _ _)) (Amp_nonneg _ _ _))
    (Amp_nonneg _ _ _)

lemma fiber {n : ℕ} (η : ℝ) (h1 : 1 / 2 < η) (h2 : η ≤ 1) (a b k : NumberString n) :
    ∑ f ∈ Fk k, kap η a b f (k - f) = Amp η k a * Amp η k b := by
  unfold kap Amp
  simp_rw [← Finset.prod_mul_distrib]
  set g : Fin n → ℕ → ℝ := fun i j => amp ((1 - η) / η) (a i) j * amp ((1 - η) / η) (b i) j *
    amp η (a i + j) (k i - j) * amp η (b i + j) (k i - j)
  calc _ = ∑ x ∈ Fintype.piFinset (fun i => Finset.range (k i + 1)), ∏ i, g i (x i) := rfl
    _ = ∏ i, ∑ j ∈ Finset.range (k i + 1), g i j := (Finset.prod_univ_sum _ _).symm
    _ = _ := Finset.prod_congr rfl (fun i _ => fiber1 η h1 h2 (a i) (b i) (k i))

end X7PD


noncomputable section
namespace X7PD
open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity State)

def sig (n : ℕ) : (Σ k : NumberString n, {f // f ∈ Fk k}) ≃ NumberString n × NumberString n where
  toFun s := (s.2.1, s.1 - s.2.1)
  invFun p := ⟨p.1 + p.2, ⟨p.1, (mem_Fk _ _).2 (fun i => by simp)⟩⟩
  left_inv := by
    rintro ⟨k, f, hf⟩
    have hf' := Pi.le_def.1 ((mem_Fk _ _).1 hf)
    apply Sigma.subtype_ext
    · funext i; have := hf' i; simp only [Pi.add_apply, Pi.sub_apply]; omega
    · rfl
  right_inv := by
    rintro ⟨f, e⟩
    ext i <;> simp

lemma main {n : ℕ} (η : ℝ) (h1 : 1 / 2 < η) (h2 : η ≤ 1) (X : FockKernel n) (hX : IsDensity X)
    (a b : NumberString n) :
    charlieMarginal (broadcast n η X) a b =
      pureLoss n ((1 - η) / η) (bobMarginal (broadcast n η X)) a b := by
  rw [charlie_broadcast, pureLoss_apply]
  simp_rw [bob_broadcast]
  set W : NumberString n → ℂ := fun k => X (k + a) (k + b) with hW
  set G : NumberString n × NumberString n → ℂ := fun p => (kap η a b p.1 p.2 : ℂ) * W (p.1 + p.2) with hG
  have hR : ∀ f : NumberString n,
      ((Amp ((1 - η) / η) a f * Amp ((1 - η) / η) b f : ℝ) : ℂ) *
        ∑' e, ((Amp η (a + f) e * Amp η (b + f) e : ℝ) : ℂ) * X (a + f + e) (b + f + e) =
      ∑' e, G (f, e) := by
    intro f
    rw [← tsum_mul_left]
    refine tsum_congr (fun e => ?_)
    simp only [hG, hW, kap]
    rw [show f + e + a = a + f + e by abel, show f + e + b = b + f + e by abel]
    push_cast; ring
  simp_rw [hR]
  have hGs : ∀ s, G (sig n s) = (kap η a b s.2.1 (s.1 - s.2.1) : ℂ) * W s.1 := by
    rintro ⟨k, f, hf⟩
    have hf' := Pi.le_def.1 ((mem_Fk _ _).1 hf)
    simp only [hG, sig, Equiv.coe_fn_mk]
    congr 2
    funext i; have := hf' i; simp only [Pi.add_apply, Pi.sub_apply]; omega
  have hsum : Summable (G ∘ sig n) := by
    refine Summable.of_norm ?_
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun k => Summable.of_finite, ?_⟩
    have : ∀ k, (∑' f : {f // f ∈ Fk k}, ‖(G ∘ sig n) ⟨k, f⟩‖) =
        Amp η k a * Amp η k b * ‖W k‖ := by
      intro k
      simp only [Function.comp, hGs, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [Finset.tsum_subtype (Fk k) (fun f => |kap η a b f (k - f)| * ‖W k‖), ← Finset.sum_mul]
      simp_rw [abs_of_nonneg (kap_nonneg _ _ _ _ _)]
      rw [fiber η h1 h2]
    simp_rw [this]
    refine Summable.of_nonneg_of_le (fun k => by
        have := Amp_nonneg η k a; have := Amp_nonneg η k b; positivity) (fun k => ?_)
      (shift_summable hX a b)
    have h0 : 0 ≤ η := by linarith
    have := Amp_le_one η h0 h2 k a; have := Amp_le_one η h0 h2 k b
    have := Amp_nonneg η k a; have := Amp_nonneg η k b
    have := norm_nonneg (W k)
    calc Amp η k a * Amp η k b * ‖W k‖ ≤ 1 * 1 * ‖W k‖ := by gcongr
      _ = ‖W k‖ := by ring
  have hGsum : Summable G := (sig n).summable_iff.1 hsum
  rw [← hGsum.tsum_prod, ← (sig n).tsum_eq,
    show (∑' c, G (sig n c)) = ∑' c, (G ∘ sig n) c from rfl, hsum.tsum_sigma]
  refine tsum_congr (fun k => ?_)
  simp only [Function.comp, hGs]
  rw [Finset.tsum_subtype (Fk k) (fun f => (kap η a b f (k - f) : ℂ) * W k), ← Finset.sum_mul,
    ← Complex.ofReal_sum, fiber η h1 h2]

end X7PD


open QAlgorithms.Papers.Independent.Next46.P32 QAlgorithms.Papers.Independent.Dependency50.P33 in
theorem solution (n : ℕ) (hn : 0 < n) (eta : ℝ)
    (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (rho : State (NumberString n)) :
    charlieMarginal (broadcast n eta rho.coefficients) =
      pureLoss n ((1 - eta) / eta)
        (bobMarginal (broadcast n eta rho.coefficients)) := by
  funext a b
  exact X7PD.main eta heta heta1 rho.coefficients rho.density a b
