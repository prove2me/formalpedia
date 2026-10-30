-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P05.weylRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:00:25.605757+00:00
-- url     : https://prove2.me/submissions/a9c143be-74ec-41c4-9eb1-21991a7933e6

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P05
noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P05

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P34 (cyclicPhase weyl dephasing)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Gap48.P36 (WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (nu superopTensor UniversalMultiplicative rowKraus indexedKrausDilation)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ} [NeZero d]

theorem s110w_cp (x : ZMod d) : cyclicPhase d x = ZMod.stdAddChar x := by
  unfold cyclicPhase
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]

theorem s110w_cp_add (x y : ZMod d) : cyclicPhase d (x + y) = cyclicPhase d x * cyclicPhase d y := by
  simp only [s110w_cp, AddChar.map_add_eq_mul]

theorem s110w_cp_zero : cyclicPhase d 0 = 1 := by
  simp only [s110w_cp, AddChar.map_zero_eq_one]

theorem s110w_cp_neg_mul (x : ZMod d) : cyclicPhase d (-x) * cyclicPhase d x = 1 := by
  rw [← s110w_cp_add, neg_add_cancel, s110w_cp_zero]

theorem s110w_cp_conj (x : ZMod d) : star (cyclicPhase d x) = cyclicPhase d (-x) := by
  have h1 : star (cyclicPhase d x) * cyclicPhase d x = 1 := by
    unfold cyclicPhase
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    convert Complex.exp_zero
    rw [map_div₀, map_mul, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast,
      map_natCast, map_ofNat]
    ring
  have h2 := s110w_cp_neg_mul x
  have hne : cyclicPhase d x ≠ 0 := by unfold cyclicPhase; exact Complex.exp_ne_zero _
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

theorem s110w_shift_pow (k : ℕ) (X Y : ZMod d) :
    ((Matrix.of fun a b : ZMod d => if a = b + 1 then (1:ℂ) else 0) ^ k) X Y =
      if X = Y + (k : ZMod d) then 1 else 0 := by
  induction k generalizing X Y with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [ih, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (Y + 1)]
    · simp only [if_true]; push_cast; congr 1; apply propext; constructor <;> intro h <;> rw [h] <;> ring
    · intro c _ hc; simp [hc]
    · simp

theorem s110w_cp_pow (y : ZMod d) (k : ℕ) : cyclicPhase d y ^ k = cyclicPhase d ((k : ZMod d) * y) := by
  simp only [s110w_cp, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

theorem s110w_W_apply (z : WeylLabel d) (x y : ZMod d) :
    W z x y = if x = y + z.1 then cyclicPhase d (z.2 * y) else 0 := by
  unfold W weyl
  simp only [Matrix.diagonal_pow, Matrix.mul_diagonal, s110w_shift_pow,
    ZMod.natCast_zmod_val, ite_mul, one_mul, zero_mul, Pi.pow_apply, s110w_cp_pow]

theorem s110w_tr (z : WeylLabel d) :
    (W z).trace = if z = 0 then (d : ℂ) else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, s110w_W_apply]
  by_cases h1 : z.1 = 0
  · simp only [h1, add_zero, if_true]
    have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod d) ℂ)) z.2
      (ZMod.isPrimitive_stdAddChar d)
    simp only [s110w_cp, mul_comm z.2]
    rw [this, ZMod.card]
    by_cases h2 : z.2 = 0
    · have : z = 0 := Prod.ext h1 h2
      simp [h2, this]
    · have : z ≠ 0 := fun h => h2 (by rw [h]; rfl)
      simp [h2, this]
  · have : z ≠ 0 := fun h => h1 (by rw [h]; rfl)
    rw [if_neg this]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    intro h
    apply h1
    have := congrArg (· - y) h
    simpa using this.symm


theorem s110w_mul (z v : WeylLabel d) : W z * W v = cyclicPhase d (z.2 * v.1) • W (z + v) := by
  ext x y
  rw [Matrix.mul_apply, Matrix.smul_apply, s110w_W_apply (z + v)]
  simp only [s110w_W_apply]
  rw [Finset.sum_eq_single (y + v.1)]
  · simp only [if_true, Prod.fst_add, Prod.snd_add]
    by_cases h : x = y + v.1 + z.1
    · rw [if_pos h, if_pos (by rw [h]; ring), smul_eq_mul, ← s110w_cp_add, ← s110w_cp_add]
      congr 1; ring
    · rw [if_neg h, if_neg (by rw [← add_assoc, add_right_comm]; exact h)]; simp
  · intro c _ hc; simp [hc]
  · simp

theorem s110w_star (z : WeylLabel d) : (W z)ᴴ = cyclicPhase d (z.2 * z.1) • W (-z) := by
  ext x y
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply, s110w_W_apply, s110w_W_apply]
  simp only [Prod.fst_neg, Prod.snd_neg]
  by_cases h : y = x + z.1
  · rw [if_pos h, if_pos (by rw [h]; ring), smul_eq_mul, s110w_cp_conj, ← s110w_cp_add, h]
    congr 1; ring
  · rw [if_neg h, if_neg (by intro h'; apply h; rw [h']; ring)]; simp

theorem s110w_tr_mul (z v : WeylLabel d) :
    (W z * (W v)ᴴ).trace = if z = v then (d : ℂ) else 0 := by
  rw [s110w_star, Matrix.mul_smul, s110w_mul, Matrix.trace_smul, Matrix.trace_smul, s110w_tr]
  by_cases h : z = v
  · subst h
    simp only [add_neg_cancel, if_true, smul_eq_mul, Prod.snd_neg]
    rw [← mul_assoc, ← s110w_cp_add]
    rw [Prod.fst_neg, show z.2 * z.1 + z.2 * -z.1 = 0 by ring, s110w_cp_zero, one_mul]
  · rw [if_neg (by rw [← sub_eq_add_neg]; exact sub_ne_zero.mpr h), if_neg h]; simp

theorem s110w_W0 : W (0 : WeylLabel d) = 1 := by
  ext x y
  rw [s110w_W_apply, Matrix.one_apply]
  simp [s110w_cp_zero]

theorem s110w_trXW (X : Op (ZMod d)) (z : WeylLabel d) :
    (X * (W z)ᴴ).trace = ∑ w, X (w + z.1) w * cyclicPhase d (-(z.2 * w)) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, s110w_W_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_eq_single (w + z.1)]
  · simp [s110w_cp_conj]
  · intro c _ hc; simp [hc]
  · simp

theorem s110w_charsum (c : ZMod d) : ∑ b : ZMod d, cyclicPhase d (b * c) = if c = 0 then (d : ℂ) else 0 := by
  simp only [s110w_cp]
  rw [AddChar.sum_mulShift c (ZMod.isPrimitive_stdAddChar d), ZMod.card]
  split_ifs <;> simp

theorem s110w_expand (X : Op (ZMod d)) : X = ∑ z, weylFourierCoefficient X z • W z := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  ext x y
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, weylFourierCoefficient, s110w_trXW, s110w_W_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp only
  rw [Finset.sum_eq_single (x - y)]
  · rw [show y + (x - y) = x by ring]
    simp only [if_true]
    simp only [div_mul_eq_mul_div, Finset.sum_mul]
    rw [← Finset.sum_div, Finset.sum_comm]
    simp only [mul_assoc, ← s110w_cp_add, ← Finset.mul_sum]
    have : ∀ w : ZMod d, ∑ b : ZMod d, cyclicPhase d (-(b * w) + b * y) =
        if y - w = 0 then (d : ℂ) else 0 := by
      intro w; rw [← s110w_charsum]; congr 1; funext b; congr 1; ring
    simp only [this, mul_ite, mul_zero]
    rw [Finset.sum_eq_single y]
    · simp only [sub_self, if_true]
      rw [show y + (x - y) = x by ring]; field_simp
    · intro w _ hw; rw [if_neg (sub_ne_zero.mpr (Ne.symm hw))]
    · simp
  · intro a _ ha
    apply Finset.sum_eq_zero; intro b _
    rw [if_neg (by intro h; apply ha; rw [h]; ring)]; simp
  · simp


theorem s110w_trstar (X : Op (ZMod d)) (z : WeylLabel d) :
    (Xᴴ * W z).trace = star ((X * (W z)ᴴ).trace) := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_mul_comm]

theorem s110w_parseval (X : Op (ZMod d)) :
    (Xᴴ * X).trace = (((d : ℝ) * ∑ z, ‖weylFourierCoefficient X z‖ ^ 2 : ℝ) : ℂ) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hX := s110w_expand X
  calc (Xᴴ * X).trace = (Xᴴ * ∑ z, weylFourierCoefficient X z • W z).trace := by rw [← hX]
    _ = _ := by
      rw [Matrix.mul_sum, Matrix.trace_sum]
      simp only [Matrix.mul_smul, Matrix.trace_smul, s110w_trstar, smul_eq_mul]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      have : (X * (W z)ᴴ).trace = (d : ℂ) * weylFourierCoefficient X z := by
        unfold weylFourierCoefficient; field_simp
      rw [this, star_mul', Complex.star_def, Complex.conj_natCast, ← Complex.mul_conj']
      ring

theorem s110w_conj (X : Op (ZMod d)) (z : WeylLabel d) :
    conj (weylFourierCoefficient X z) =
      cyclicPhase d (-(z.2 * z.1)) * weylFourierCoefficient Xᴴ (-z) := by
  unfold weylFourierCoefficient
  rw [s110w_star (-z), Matrix.mul_smul, Matrix.trace_smul, map_div₀, Complex.conj_natCast,
    ← Complex.star_def, ← s110w_trstar]
  simp only [Prod.fst_neg, Prod.snd_neg, neg_neg, smul_eq_mul]
  rw [← mul_div_assoc, ← mul_assoc, ← s110w_cp_add, show -(z.2 * z.1) + -z.2 * -z.1 = 0 by ring,
    s110w_cp_zero, one_mul]


theorem s110w_comm (z v : WeylLabel d) :
    W z * W v = cyclicPhase d (v.1 * z.2 - v.2 * z.1) • (W v * W z) := by
  rw [s110w_mul, s110w_mul, smul_smul, ← s110w_cp_add, add_comm v z]
  congr 2; ring

theorem s110w_unit (z : WeylLabel d) : W z * (W z)ᴴ = 1 := by
  rw [s110w_star, Matrix.mul_smul, s110w_mul, add_neg_cancel, s110w_W0, smul_smul, ← s110w_cp_add,
    Prod.fst_neg, show z.2 * z.1 + z.2 * -z.1 = 0 by ring, s110w_cp_zero, one_smul]

theorem s110w_conjW (a z : WeylLabel d) :
    W a * W z * (W a)ᴴ = cyclicPhase d (z.1 * a.2 - z.2 * a.1) • W z := by
  rw [s110w_comm a z, Matrix.smul_mul, Matrix.mul_assoc, s110w_unit, Matrix.mul_one]

theorem s110w_f_smul (c : ℂ) (X : Op (ZMod d)) (u : WeylLabel d) :
    weylFourierCoefficient (c • X) u = c * weylFourierCoefficient X u := by
  unfold weylFourierCoefficient
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_div_assoc]

theorem s110w_f_sum (s : Finset (WeylLabel d)) (c : WeylLabel d → ℂ) (u : WeylLabel d) :
    weylFourierCoefficient (∑ z ∈ s, c z • W z) u =
      ∑ z ∈ s, c z * weylFourierCoefficient (W z) u := by
  unfold weylFourierCoefficient
  rw [Finset.sum_mul, Matrix.trace_sum, Finset.sum_div]
  apply Finset.sum_congr rfl; intro z _
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_div_assoc]

theorem s110w_fW (z u : WeylLabel d) :
    weylFourierCoefficient (W z) u = if u = z then 1 else 0 := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  unfold weylFourierCoefficient
  rw [s110w_tr_mul]
  by_cases h : u = z
  · subst h; simp [hd]
  · rw [if_neg (Ne.symm h), if_neg h, zero_div]

theorem s110w_extract (c : WeylLabel d → ℂ) (u : WeylLabel d) :
    weylFourierCoefficient (∑ z, c z • W z) u = c u := by
  rw [s110w_f_sum]
  simp [s110w_fW]

theorem s110w_conjX (a : WeylLabel d) (X : Op (ZMod d)) :
    W a * X * (W a)ᴴ =
      ∑ w, (weylFourierCoefficient X w * cyclicPhase d (w.1 * a.2 - w.2 * a.1)) • W w := by
  conv_lhs => rw [s110w_expand X]
  rw [Matrix.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro w _
  rw [Matrix.mul_smul, Matrix.smul_mul, s110w_conjW, smul_smul]

theorem s110w_fconj (a : WeylLabel d) (X : Op (ZMod d)) (u : WeylLabel d) :
    weylFourierCoefficient (W a * X * (W a)ᴴ) u =
      weylFourierCoefficient X u * cyclicPhase d (u.1 * a.2 - u.2 * a.1) := by
  rw [s110w_conjX, s110w_extract]

theorem s110w_cp_inj {x y : ZMod d} (h : cyclicPhase d x = cyclicPhase d y) : x = y := by
  rw [s110w_cp, s110w_cp] at h
  exact ZMod.injective_stdAddChar h

theorem s110w_charsum2 (x : WeylLabel d) :
    ∑ g : WeylLabel d, cyclicPhase d (g.1 * x.1 + g.2 * x.2) =
      if x = 0 then (d : ℂ) ^ 2 else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [s110w_cp_add]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, s110w_charsum]
  by_cases h1 : x.1 = 0 <;> by_cases h2 : x.2 = 0 <;> simp [h1, h2, Prod.ext_iff, sq]

theorem s110w_inv (φ : WeylLabel d → ℂ) (z : WeylLabel d) :
    φ z = ∑ g, fourier φ g * duality g (-z) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  unfold fourier duality
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ w : WeylLabel d, ∑ g : WeylLabel d, (d : ℂ)⁻¹ ^ 2 * (φ w *
      cyclicPhase d (g.1 * w.1 + g.2 * w.2)) * cyclicPhase d (g.1 * (-z).1 + g.2 * (-z).2) =
      (d : ℂ)⁻¹ ^ 2 * φ w * ∑ g : WeylLabel d, cyclicPhase d (g.1 * (w - z).1 + g.2 * (w - z).2) := by
    intro w; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro g _
    have harg : g.1 * (w - z).1 + g.2 * (w - z).2 =
        (g.1 * w.1 + g.2 * w.2) + (g.1 * (-z).1 + g.2 * (-z).2) := by
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]; ring
    rw [harg, s110w_cp_add (g.1 * w.1 + g.2 * w.2)]
    ring
  simp only [this, s110w_charsum2, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  field_simp

theorem s110w_twirl (φ : WeylLabel d → ℂ) (X : Op (ZMod d)) :
    ∑ g, fourier φ g • (W (rotateWeylLabel g) * X * (W (rotateWeylLabel g))ᴴ) =
      multiplier φ X := by
  unfold multiplier
  simp only [s110w_conjX, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w _
  rw [← Finset.sum_smul]; congr 1
  rw [s110w_inv φ w, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro g _
  unfold duality rotateWeylLabel
  rw [show w.1 * (g.2, -g.1).2 - w.2 * (g.2, -g.1).1 = g.1 * (-w).1 + g.2 * (-w).2 by
    simp only [Prod.fst_neg, Prod.snd_neg]; ring]
  ring

theorem s110w_lin (Phi : Op (ZMod d) →ₗ[ℂ] Op (ZMod d))
    (hA : ∀ z, Phi (W z) = symbol Phi z • W z) (c : WeylLabel d → ℂ) :
    Phi (∑ z, c z • W z) = ∑ z, (c z * symbol Phi z) • W z := by
  rw [map_sum]
  apply Finset.sum_congr rfl; intro z _
  rw [map_smul, hA, smul_smul]

theorem s110w_diag (Phi : Op (ZMod d) →ₗ[ℂ] Op (ZMod d)) (hPhi : WeylCovariantMap Phi)
    (z : WeylLabel d) : Phi (W z) = symbol Phi z • W z := by
  set Y := Phi (W z) with hY
  have key : ∀ v u : WeylLabel d, cyclicPhase d (z.1 * v.2 - z.2 * v.1) * weylFourierCoefficient Y u =
      weylFourierCoefficient Y u * cyclicPhase d (u.1 * v.2 - u.2 * v.1) := by
    intro v u
    have h := hPhi v (W z)
    rw [s110w_conjW, map_smul] at h
    have := congrArg (fun M => weylFourierCoefficient M u) h
    simp only [s110w_f_smul, s110w_fconj] at this
    exact this
  have hzero : ∀ u, u ≠ z → weylFourierCoefficient Y u = 0 := by
    intro u hu
    by_contra hc
    by_cases h1 : u.1 = z.1
    · have h2 : u.2 ≠ z.2 := fun h2 => hu (Prod.ext h1 h2)
      have := key (1, 0) u
      simp only [mul_one, mul_zero, zero_sub] at this
      rw [mul_comm] at this
      have := s110w_cp_inj (mul_left_cancel₀ hc this)
      exact h2 (neg_inj.mp this).symm
    · have := key (0, 1) u
      simp only [mul_one, mul_zero, sub_zero] at this
      rw [mul_comm] at this
      exact h1 (s110w_cp_inj (mul_left_cancel₀ hc this)).symm
  calc Y = ∑ u, weylFourierCoefficient Y u • W u := s110w_expand Y
    _ = weylFourierCoefficient Y z • W z :=
        Finset.sum_eq_single z (fun u _ hu => by rw [hzero u hu, zero_smul]) (by simp)
    _ = symbol Phi z • W z := rfl

theorem s110w_comp (Phi Psi : Op (ZMod d) →ₗ[ℂ] Op (ZMod d))
    (hA : ∀ z, Phi (W z) = symbol Phi z • W z) (hB : ∀ z, Psi (W z) = symbol Psi z • W z)
    (X : Op (ZMod d)) :
    Phi (Psi X) = ∑ z, (weylFourierCoefficient X z * (symbol Phi z * symbol Psi z)) • W z := by
  conv_lhs => rw [s110w_expand X]
  rw [s110w_lin Psi hB, s110w_lin Phi hA]
  apply Finset.sum_congr rfl; intro z _
  congr 1; ring

theorem s110w_fconv (φ ψ : WeylLabel d → ℂ) (g : WeylLabel d) :
    fourier (fun z => φ z * ψ z) g = weylConvolution (fourier φ) (fourier ψ) g := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hterm : ∀ h z w : WeylLabel d, duality h z * duality (g - h) w =
      duality g w * cyclicPhase d (h.1 * (z - w).1 + h.2 * (z - w).2) := by
    intro h z w; unfold duality; rw [← s110w_cp_add, ← s110w_cp_add]; congr 1
    simp only [Prod.fst_sub, Prod.snd_sub]; ring
  unfold weylConvolution fourier
  have e1 : ∀ h : WeylLabel d, ((d : ℂ)⁻¹ ^ 2 * ∑ z, φ z * duality h z) *
      ((d : ℂ)⁻¹ ^ 2 * ∑ w, ψ w * duality (g - h) w) =
      ∑ z, ∑ w, ((d : ℂ)⁻¹ ^ 2 * (d : ℂ)⁻¹ ^ 2 * φ z * ψ w * duality g w) *
        cyclicPhase d (h.1 * (z - w).1 + h.2 * (z - w).2) := by
    intro h
    rw [mul_mul_mul_comm, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro z _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro w _
    rw [show φ z * duality h z * (ψ w * duality (g - h) w) =
      φ z * ψ w * (duality h z * duality (g - h) w) by ring, hterm]
    ring
  simp only [e1]
  rw [Finset.sum_comm]
  simp only [fun z => (Finset.sum_comm (s := (Finset.univ : Finset (WeylLabel d)))
    (t := (Finset.univ : Finset (WeylLabel d)))
    (f := fun h w => ((d : ℂ)⁻¹ ^ 2 * (d : ℂ)⁻¹ ^ 2 * φ z * ψ w * duality g w) *
        cyclicPhase d (h.1 * (z - w).1 + h.2 * (z - w).2)))]
  simp only [← Finset.mul_sum, s110w_charsum2, sub_eq_zero, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  field_simp

end QAlgorithms.Papers.Independent.Bridge50.P05

open QAlgorithms.Papers.Independent.Bridge50.P05
open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal
open QAlgorithms.Papers.Independent.Information100.P34 (cyclicPhase weyl dephasing)
open QAlgorithms.Papers.Independent.Gap48.P36 (WeylLabel)
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {d : ℕ} [NeZero d] (Phi Psi : Op (ZMod d) →ₗ[ℂ] Op (ZMod d))
    (hPhi : WeylCovariantMap Phi) (hPsi : WeylCovariantMap Psi) :
    (∀ z, Phi (W z) = symbol Phi z • W z) ∧
    (∀ X, Phi X = multiplier (symbol Phi) X) ∧
    (∀ z, symbol Phi z = ∑ g, fourier (symbol Phi) g * duality g (-z)) ∧
    (∀ X, Phi X = ∑ g, fourier (symbol Phi) g • (W (rotateWeylLabel g) * X * (W (rotateWeylLabel g))ᴴ)) ∧
    (∀ X, Phi (Psi X) = Psi (Phi X)) ∧
    (∀ z, symbol (fun X => Phi (Psi X)) z = symbol Phi z * symbol Psi z) ∧
    (∀ g, fourier (symbol (fun X => Phi (Psi X))) g =
      weylConvolution (fourier (symbol Phi)) (fourier (symbol Psi)) g) ∧
    (∀ X, Phi (Psi X) = ∑ g,
      weylConvolution (fourier (symbol Phi)) (fourier (symbol Psi)) g •
        (W (rotateWeylLabel g) * X * (W (rotateWeylLabel g))ᴴ)) ∧
    (∀ phi : WeylLabel d → ℂ,
      (∀ z, multiplier phi (W z) = phi z • W z) ∧
      (∀ z X, multiplier phi (W z * X * (W z)ᴴ) =
        W z * multiplier phi X * (W z)ᴴ)) := by
  have hA := s110w_diag Phi hPhi
  have hB := s110w_diag Psi hPsi
  have hmult : ∀ X, Phi X = multiplier (symbol Phi) X := fun X => by
    conv_lhs => rw [s110w_expand X]
    rw [s110w_lin Phi hA]; rfl
  have hsym : ∀ z, symbol (fun X => Phi (Psi X)) z = symbol Phi z * symbol Psi z := fun z => by
    show weylFourierCoefficient (Phi (Psi (W z))) z = _
    rw [hB z, map_smul, hA z, smul_smul, s110w_f_smul, s110w_fW, if_pos rfl, mul_one, mul_comm]
  have hconv : ∀ g, fourier (symbol (fun X => Phi (Psi X))) g =
      weylConvolution (fourier (symbol Phi)) (fourier (symbol Psi)) g := fun g => by
    rw [show symbol (fun X => Phi (Psi X)) = fun z => symbol Phi z * symbol Psi z from funext hsym]
    exact s110w_fconv _ _ g
  refine ⟨hA, hmult, fun z => s110w_inv _ z, fun X => by rw [s110w_twirl, hmult], fun X => ?_,
    hsym, hconv, fun X => ?_, fun phi => ⟨fun z => ?_, fun z X => ?_⟩⟩
  · rw [s110w_comp Phi Psi hA hB, s110w_comp Psi Phi hB hA]
    apply Finset.sum_congr rfl; intro z _
    congr 1; ring
  · simp only [← hconv]
    rw [s110w_twirl, s110w_comp Phi Psi hA hB]
    unfold multiplier
    simp only [hsym]
  · unfold multiplier
    simp [s110w_fW]
  · unfold multiplier
    simp only [s110w_fconj, Matrix.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
      s110w_conjW, smul_smul]
    apply Finset.sum_congr rfl; intro u _
    congr 1; ring
