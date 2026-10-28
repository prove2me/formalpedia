-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P06.thermalEntropy_matching
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T06:23:17.24016+00:00
-- url     : https://prove2.me/submissions/d9cdca10-635c-4682-ad4e-99c1e08ed900

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06
open MeasureTheory

namespace M30E
open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.RealRegisters (Hilbert)

lemma normsq_hasSum {I : Type} (v : Hilbert I) : HasSum (fun a => ‖v a‖ ^ 2) (‖v‖ ^ 2) := by
  have := lp.hasSum_norm (p := 2) (by norm_num) v
  simpa using this

lemma eigen {n : ℕ} (lam : NumberString n → ℝ) (D : FockKernel n)
    (hD : ∀ a b, D a b = if a = b then (lam a : ℂ) else 0) (d : SpectralResolution D)
    (j : ℕ) (hj : 0 < d.weight j) (a : NumberString n) :
    (lam a : ℂ) * d.vector j a = ((d.weight j : ℝ) : ℂ) * d.vector j a := by
  classical
  set v := d.vector with hv
  set w := d.weight with hw
  have h1 : ∑' b, D a b * v j b = lam a * v j a := by
    rw [tsum_eq_single a]
    · rw [hD, if_pos rfl]
    · intro b hb; rw [hD, if_neg (Ne.symm hb), zero_mul]
  let F : ℕ → NumberString n → ℂ := fun k b => ((w k : ℝ) : ℂ) * v k a * (star (v k b) * v j b)
  have h2 : ∀ b, D a b * v j b = ∑' k, F k b := by
    intro b; rw [d.coefficients a b, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    simp only [F]; ring
  have hnorm : ∀ k, 0 < w k → ‖v k‖ = 1 := d.norm_one
  have hsq : ∀ k, HasSum (fun b => ‖v k b‖ ^ 2) (‖v k‖ ^ 2) := fun k => normsq_hasSum (v k)
  let G : ℕ × NumberString n → ℝ := fun p => (w p.1 : ℝ) * ((‖v p.1 p.2‖ ^ 2 + ‖v j p.2‖ ^ 2) / 2)
  have hG0 : 0 ≤ G := fun p => by
    simp only [G, Pi.zero_apply]; positivity
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun k => ?_, ?_⟩
    · show Summable (fun b => (w k : ℝ) * ((‖v k b‖ ^ 2 + ‖v j b‖ ^ 2) / 2))
      exact (((hsq k).summable.add (hsq j).summable).div_const 2).mul_left _
    · have : ∀ k, ∑' b, G (k, b) = (w k : ℝ) := by
        intro k
        simp only [G]
        rw [tsum_mul_left, tsum_div_const, ((hsq k).add (hsq j)).tsum_eq]
        rcases eq_zero_or_pos (w k) with h | h
        · simp [h]
        · rw [hnorm k h, hnorm j hj]; ring
      simp only [this]
      exact d.summable
  have hFs : Summable (Function.uncurry F) := by
    refine Summable.of_norm_bounded hGs (fun p => ?_)
    obtain ⟨k, b⟩ := p
    simp only [Function.uncurry_apply_pair, F, G]
    simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
    rcases eq_zero_or_pos (w k) with h | h
    · simp [h]
    · have ha : ‖v k a‖ ≤ 1 := by
        rw [← hnorm k h]; exact lp.norm_apply_le_norm (by norm_num) _ _
      have hb : ‖v k b‖ * ‖v j b‖ ≤ (‖v k b‖ ^ 2 + ‖v j b‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖v k b‖ - ‖v j b‖)]
      have hw0 : (0 : ℝ) ≤ w k := (w k).2
      calc (w k : ℝ) * ‖v k a‖ * (‖v k b‖ * ‖v j b‖)
          ≤ (w k : ℝ) * 1 * (‖v k b‖ * ‖v j b‖) := by gcongr
        _ ≤ (w k : ℝ) * ((‖v k b‖ ^ 2 + ‖v j b‖ ^ 2) / 2) := by rw [mul_one]; gcongr
  have h3 : ∑' b, ∑' k, F k b = ∑' k, ∑' b, F k b := hFs.tsum_comm
  have h4 : ∀ k, ∑' b, F k b = ((w k : ℝ) : ℂ) * v k a * inner ℂ (v k) (v j) := by
    intro k
    simp only [F]
    rw [tsum_mul_left, lp.inner_eq_tsum]
    congr 1
    refine tsum_congr fun b => ?_
    simp [RCLike.inner_apply, mul_comm]
  have h5 : ∑' k, ((w k : ℝ) : ℂ) * v k a * inner ℂ (v k) (v j) = ((w j : ℝ) : ℂ) * v j a := by
    rw [tsum_eq_single j]
    · rw [inner_self_eq_norm_sq_to_K, hnorm j hj]; simp
    · intro k hk
      rcases eq_zero_or_pos (w k) with h | h
      · simp [h]
      · rw [d.orthogonal k j hk h hj, mul_zero]
  rw [← h1, tsum_congr h2, h3, tsum_congr h4, h5]


lemma lower {n : ℕ} (lam : NumberString n → ℝ) (hlam : ∀ a, 0 ≤ lam a) (D : FockKernel n)
    (hD : ∀ a b, D a b = if a = b then (lam a : ℂ) else 0) (d : SpectralResolution D) :
    ∑' a, ENNReal.ofReal (-(lam a) * Real.log (lam a)) ≤
      ∑' j, ENNReal.ofReal (-(d.weight j : ℝ) * Real.log (d.weight j : ℝ)) := by
  classical
  set v := d.vector with hv
  set w := d.weight with hw
  let c : ℕ → NumberString n → ENNReal := fun j a =>
    ENNReal.ofReal (if 0 < w j then ‖v j a‖ ^ 2 else 0)
  have hlamw : ∀ j, 0 < w j → ∀ a, v j a ≠ 0 → lam a = (w j : ℝ) := by
    intro j hj a ha
    have := eigen lam D hD d j hj a
    exact Complex.ofReal_injective (mul_right_cancel₀ ha this)
  have hi : ∀ j, ENNReal.ofReal (-(w j : ℝ) * Real.log (w j : ℝ)) =
      ∑' a, c j a * ENNReal.ofReal (-(lam a) * Real.log (lam a)) := by
    intro j
    rcases eq_zero_or_pos (w j) with h | h
    · simp [c, h]
    · have hpt : ∀ a, c j a * ENNReal.ofReal (-(lam a) * Real.log (lam a)) =
          ENNReal.ofReal (‖v j a‖ ^ 2) * ENNReal.ofReal (-(w j : ℝ) * Real.log (w j : ℝ)) := by
        intro a
        simp only [c, if_pos h]
        by_cases ha : v j a = 0
        · simp [ha]
        · rw [hlamw j h a ha]
      rw [tsum_congr hpt, ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
        (fun a => by positivity) (normsq_hasSum (v j)).summable, (normsq_hasSum (v j)).tsum_eq,
        d.norm_one j h]
      simp
  have hii : ∀ a, 0 < lam a → ∑' j, c j a = 1 := by
    intro a ha
    let f : ℕ → ℝ := fun k => if 0 < w k then ‖v k a‖ ^ 2 else 0
    have hD' : (lam a : ℂ) = ∑' k, (((w k : ℝ) * ‖v k a‖ ^ 2 : ℝ) : ℂ) := by
      have := d.coefficients a a
      rw [hD, if_pos rfl] at this
      rw [this]
      refine tsum_congr fun k => ?_
      rw [mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [← Complex.ofReal_tsum] at hD'
    have hD'' : lam a = ∑' k, (w k : ℝ) * ‖v k a‖ ^ 2 := by exact_mod_cast hD'
    have hpt : ∀ k, (w k : ℝ) * ‖v k a‖ ^ 2 = lam a * f k := by
      intro k
      simp only [f]
      rcases eq_zero_or_pos (w k) with h | h
      · simp [h]
      · rw [if_pos h]
        by_cases hk : v k a = 0
        · simp [hk]
        · rw [hlamw k h a hk]
    rw [tsum_congr hpt, tsum_mul_left] at hD''
    have hf1 : ∑' k, f k = 1 := by
      field_simp at hD''
      linarith
    have hfs : Summable f := by
      by_contra hns
      rw [tsum_eq_zero_of_not_summable hns] at hf1
      exact zero_ne_one hf1
    have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [f]; split_ifs <;> positivity
    show ∑' j, ENNReal.ofReal (f j) = 1
    rw [← ENNReal.ofReal_tsum_of_nonneg hf0 hfs, hf1, ENNReal.ofReal_one]
  calc ∑' a, ENNReal.ofReal (-(lam a) * Real.log (lam a))
      ≤ ∑' a, (∑' j, c j a) * ENNReal.ofReal (-(lam a) * Real.log (lam a)) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        rcases (hlam a).eq_or_lt with h | h
        · rw [← h]; simp
        · rw [hii a h, one_mul]
    _ = ∑' j, ∑' a, c j a * ENNReal.ofReal (-(lam a) * Real.log (lam a)) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun a => ?_
        rw [ENNReal.tsum_mul_right]
    _ = ∑' j, ENNReal.ofReal (-(w j : ℝ) * Real.log (w j : ℝ)) := by
        refine tsum_congr fun j => (hi j).symm


lemma spectral_diag {n : ℕ} (hn : 0 < n) (lam : NumberString n → ℝ) (hlam : ∀ a, 0 ≤ lam a)
    (hsum : HasSum lam 1) (D : FockKernel n)
    (hD : ∀ a b, D a b = if a = b then (lam a : ℂ) else 0) :
    spectralEntropyNats D = ∑' a, ENNReal.ofReal (-(lam a) * Real.log (lam a)) := by
  classical
  refine le_antisymm ?_ (le_iInf fun d => lower lam hlam D hD d)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Infinite (NumberString n) := inferInstance
  letI : Denumerable (NumberString n) := Denumerable.ofEncodableOfInfinite _
  let e : ℕ ≃ NumberString n := (Denumerable.eqv (NumberString n)).symm
  let res : SpectralResolution D :=
    { weight := fun j => ⟨lam (e j), hlam _⟩
      vector := fun j => lp.single 2 (e j) (1 : ℂ)
      summable := by
        show Summable (lam ∘ e)
        exact (Equiv.summable_iff e).mpr hsum.summable
      total := by
        show ∑' j, lam (e j) = 1
        rw [Equiv.tsum_eq e lam, hsum.tsum_eq]
      norm_one := fun j _ => by
        rw [lp.norm_single (by norm_num)]; simp
      orthogonal := fun i j hij _ _ => by
        rw [lp.inner_single_left]
        have : e i ≠ e j := e.injective.ne hij
        simp [lp.single_apply, Pi.single_apply, this.symm]
      coefficients := fun a b => by
        rw [hD, tsum_eq_single (e.symm a)]
        · simp only [Equiv.apply_symm_apply, lp.single_apply, Pi.single_eq_same]
          by_cases hab : a = b
          · subst hab; simp; rfl
          · rw [if_neg hab, Pi.single_eq_of_ne' hab]; simp
        · intro j hj
          have : e j ≠ a := by
            intro h; apply hj; rw [← h, Equiv.symm_apply_apply]
          simp [lp.single_apply, Pi.single_apply, this.symm] }
  refine iInf_le_of_le res ?_
  show ∑' j, ENNReal.ofReal (-(lam (e j)) * Real.log (lam (e j))) ≤ _
  rw [Equiv.tsum_eq e (fun a => ENNReal.ofReal (-(lam a) * Real.log (lam a)))]

end M30E

namespace M30T
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- η(x) = -x log x -/
noncomputable def eta (x : ℝ) : ℝ := -x * Real.log x

lemma eta_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ eta x := by
  unfold eta
  have := Real.log_nonpos h0 h1
  nlinarith

lemma eta_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : eta (x * y) = y * eta x + x * eta y := by
  unfold eta
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  rcases hy.eq_or_lt with h' | h'
  · subst h'; simp
  rw [Real.log_mul h.ne' h'.ne']; ring


lemma sum_cons (n : ℕ) (F : (Fin (n + 1) → ℕ) → ENNReal) :
    ∑' a, F a = ∑' m : ℕ, ∑' t : Fin n → ℕ, F (Fin.cons m t) := by
  rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ => ℕ)), ENNReal.tsum_prod']
  rfl

lemma prod_cons (p : ℕ → ℝ) (n : ℕ) (m : ℕ) (t : Fin n → ℕ) :
    ∏ i, p ((Fin.cons m t : Fin (n + 1) → ℕ) i) = p m * ∏ i, p (t i) := by
  rw [Fin.prod_univ_succ]; simp

lemma sumA (p : ℕ → ℝ) (hp0 : ∀ m, 0 ≤ p m) (hps : ∑' m, ENNReal.ofReal (p m) = 1) :
    ∀ n : ℕ, ∑' a : Fin n → ℕ, ENNReal.ofReal (∏ i, p (a i)) = 1
  | 0 => by
    rw [tsum_eq_single (fun i => i.elim0)]
    · simp
    · intro b hb; exact absurd (Subsingleton.elim b _) hb
  | n + 1 => by
    rw [sum_cons]
    simp only [prod_cons, ENNReal.ofReal_mul (hp0 _), ENNReal.tsum_mul_left, sumA p hp0 hps n,
      mul_one, hps]

lemma sumB (p : ℕ → ℝ) (hp0 : ∀ m, 0 ≤ p m) (hp1 : ∀ m, p m ≤ 1)
    (hps : ∑' m, ENNReal.ofReal (p m) = 1) :
    ∀ n : ℕ, ∑' a : Fin n → ℕ, ENNReal.ofReal (eta (∏ i, p (a i))) =
      n * ∑' m, ENNReal.ofReal (eta (p m))
  | 0 => by simp [eta]
  | n + 1 => by
    rw [sum_cons]
    have hQ0 : ∀ t : Fin n → ℕ, 0 ≤ ∏ i, p (t i) := fun t => Finset.prod_nonneg fun i _ => hp0 _
    have hQ1 : ∀ t : Fin n → ℕ, ∏ i, p (t i) ≤ 1 := fun t =>
      Finset.prod_le_one (fun i _ => hp0 _) (fun i _ => hp1 _)
    have hpt : ∀ m (t : Fin n → ℕ), ENNReal.ofReal (eta (∏ i, p ((Fin.cons m t : Fin (n + 1) → ℕ) i))) =
        ENNReal.ofReal (∏ i, p (t i)) * ENNReal.ofReal (eta (p m)) +
          ENNReal.ofReal (p m) * ENNReal.ofReal (eta (∏ i, p (t i))) := by
      intro m t
      rw [prod_cons, eta_mul (hp0 m) (hQ0 t), ENNReal.ofReal_add, ENNReal.ofReal_mul (hQ0 t),
        ENNReal.ofReal_mul (hp0 m)]
      · exact mul_nonneg (hQ0 t) (eta_nonneg (hp0 m) (hp1 m))
      · exact mul_nonneg (hp0 m) (eta_nonneg (hQ0 t) (hQ1 t))
    simp only [hpt]
    simp only [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, sumA p hp0 hps n,
      sumB p hp0 hp1 hps n, one_mul, hps]
    push_cast
    ring


/-- thermal photon-number probabilities -/
noncomputable def tp (K : ℝ) (m : ℕ) : ℝ := (K / (K + 1)) ^ m / (K + 1)

lemma tp_props (K : ℝ) (hK : 0 ≤ K) :
    (∀ m, 0 ≤ tp K m) ∧ (∀ m, tp K m ≤ 1) ∧ HasSum (tp K) 1 ∧
      HasSum (fun m : ℕ => (m : ℝ) * tp K m) K := by
  have hK1 : 0 < K + 1 := by linarith
  have hr0 : 0 ≤ K / (K + 1) := by positivity
  have hr1 : K / (K + 1) < 1 := by rw [div_lt_one hK1]; linarith
  refine ⟨fun m => by unfold tp; positivity, fun m => ?_, ?_, ?_⟩
  · unfold tp
    rw [div_le_one hK1]
    calc (K / (K + 1)) ^ m ≤ 1 := pow_le_one₀ hr0 hr1.le
      _ ≤ K + 1 := by linarith
  · have h := (hasSum_geometric_of_lt_one hr0 hr1).div_const (K + 1)
    have e0 : 1 - K / (K + 1) = 1 / (K + 1) := by field_simp; ring
    have e1 : (1 - K / (K + 1))⁻¹ / (K + 1) = 1 := by rw [e0]; field_simp
    rw [e1] at h
    exact h
  · have h := (hasSum_coe_mul_geometric_of_norm_lt_one
      (r := K / (K + 1)) (by rw [Real.norm_of_nonneg hr0]; exact hr1)).div_const (K + 1)
    have e0 : 1 - K / (K + 1) = 1 / (K + 1) := by field_simp; ring
    have e2 : K / (K + 1) / (1 - K / (K + 1)) ^ 2 / (K + 1) = K := by rw [e0]; field_simp
    rw [e2] at h
    have : (fun m : ℕ => (m : ℝ) * tp K m) = (fun i : ℕ => (i : ℝ) * (K / (K + 1)) ^ i / (K + 1)) := by
      funext m; unfold tp; ring
    rw [this]; exact h

lemma tp_entropy (K : ℝ) (hK : 0 ≤ K) :
    ∑' m, ENNReal.ofReal (eta (tp K m)) = ENNReal.ofReal (g K) := by
  obtain ⟨h0, h1, hs, hm⟩ := tp_props K hK
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => eta_nonneg (h0 m) (h1 m))]
  · congr 1
    rcases hK.eq_or_lt with hK0 | hKp
    · subst hK0
      have : ∀ m, eta (tp 0 m) = 0 := by
        intro m; unfold eta tp; rcases m with _ | m <;> simp
      simp [this, g]
    · have hK1 : 0 < K + 1 := by linarith
      have hpt : ∀ m, eta (tp K m) =
          tp K m * Real.log (K + 1) - (Real.log K - Real.log (K + 1)) * ((m : ℝ) * tp K m) := by
        intro m
        unfold eta tp
        rw [Real.log_div (by positivity) hK1.ne', Real.log_pow, Real.log_div hKp.ne' hK1.ne']
        ring
      have := (hs.mul_right (Real.log (K + 1))).sub (hm.mul_left (Real.log K - Real.log (K + 1)))
      rw [tsum_congr hpt, this.tsum_eq]
      unfold g; ring
  · obtain ⟨h0, h1, hs, hm⟩ := tp_props K hK
    rcases hK.eq_or_lt with hK0 | hKp
    · subst hK0
      have : ∀ m, eta (tp 0 m) = 0 := by
        intro m; unfold eta tp; rcases m with _ | m <;> simp
      simp only [this]; exact summable_zero
    · have hK1 : 0 < K + 1 := by linarith
      have hpt : ∀ m, eta (tp K m) =
          tp K m * Real.log (K + 1) - (Real.log K - Real.log (K + 1)) * ((m : ℝ) * tp K m) := by
        intro m
        unfold eta tp
        rw [Real.log_div (by positivity) hK1.ne', Real.log_pow, Real.log_div hKp.ne' hK1.ne']
        ring
      simp only [hpt]
      exact ((hs.mul_right (Real.log (K + 1))).sub
        (hm.mul_left (Real.log K - Real.log (K + 1)))).summable

end M30T

namespace M30T
open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

lemma thermal_entropy (n : ℕ) (hn : 0 < n) (K : ℝ) (hK : 0 ≤ K) :
    spectralEntropyNats (identicalThermalKernel n K) = ENNReal.ofReal ((n : ℝ) * g K) := by
  obtain ⟨h0, h1, hs, hm⟩ := tp_props K hK
  have hps : ∑' m, ENNReal.ofReal (tp K m) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg h0 hs.summable, hs.tsum_eq, ENNReal.ofReal_one]
  set lam : NumberString n → ℝ := fun a => ∏ i, tp K (a i) with hlam
  have hlam0 : ∀ a, 0 ≤ lam a := fun a => Finset.prod_nonneg fun i _ => h0 _
  have hA := sumA (tp K) h0 hps n
  have hlsum : HasSum lam 1 := by
    have hne : ∑' a, ENNReal.ofReal (lam a) ≠ ⊤ := by
      simp only [lam]; rw [hA]; exact ENNReal.one_ne_top
    have hsm := ENNReal.summable_toReal hne
    simp only [ENNReal.toReal_ofReal (hlam0 _)] at hsm
    have := ENNReal.tsum_toReal_eq (f := fun a => ENNReal.ofReal (lam a))
      (fun a => ENNReal.ofReal_ne_top)
    simp only [ENNReal.toReal_ofReal (hlam0 _)] at this
    have h1' : (∑' a, ENNReal.ofReal (lam a)) = 1 := hA
    rw [h1', ENNReal.toReal_one] at this
    rw [this]; exact hsm.hasSum
  rw [M30E.spectral_diag hn lam hlam0 hlsum]
  · have := sumB (tp K) h0 h1 hps n
    show ∑' a : NumberString n, ENNReal.ofReal (eta (∏ i, tp K (a i))) = _
    rw [this, tp_entropy K hK, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · intro a b
    simp only [identicalThermalKernel, lam, tp]

lemma g_cont : Continuous g := by
  have h1 : Continuous (fun x : ℝ => (x + 1) * Real.log (x + 1)) :=
    Real.continuous_mul_log.comp (continuous_id.add continuous_const)
  unfold g
  exact h1.sub Real.continuous_mul_log

lemma log_le_g (N : ℝ) (hN : 0 ≤ N) : Real.log (N + 1) ≤ g N := by
  unfold g
  rcases hN.eq_or_lt with h | h
  · subst h; simp
  · have : Real.log N ≤ Real.log (N + 1) := Real.log_le_log h (by linarith)
    nlinarith

lemma inv_spec (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ QAlgorithms.Papers.Independent.Claimed50.P11.thermalEntropyInverse s ∧
      g (QAlgorithms.Papers.Independent.Claimed50.P11.thermalEntropyInverse s) = s := by
  unfold QAlgorithms.Papers.Independent.Claimed50.P11.thermalEntropyInverse
  split_ifs with h
  · have : s = 0 := le_antisymm h hs
    subst this; simp [g]
  · push_neg at h
    have hTE : QAlgorithms.Papers.Independent.Information100.P49.thermalEntropy = g := by
      funext x; rfl
    rw [hTE]
    set T := {N : ℝ | 0 ≤ N ∧ s ≤ g N} with hT
    have hne : T.Nonempty := by
      refine ⟨Real.exp s - 1, ?_, ?_⟩
      · have := Real.add_one_le_exp s; linarith
      · have := log_le_g (Real.exp s - 1) (by have := Real.add_one_le_exp s; linarith)
        simpa using this
    have hbdd : BddBelow T := ⟨0, fun x hx => hx.1⟩
    have hcl : IsClosed T := by
      have : T = {N : ℝ | 0 ≤ N} ∩ {N | s ≤ g N} := by ext; simp [T]
      rw [this]
      exact (isClosed_le continuous_const continuous_id).inter (isClosed_le continuous_const g_cont)
    have hmem := hcl.csInf_mem hne hbdd
    refine ⟨hmem.1, ?_⟩
    obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc hmem.1 g_cont.continuousOn
      (show s ∈ Set.Icc (g 0) (g (sInf T)) from ⟨by simp [g]; exact hs, hmem.2⟩)
    have hcT : c ∈ T := ⟨hc.1, hgc.ge⟩
    have : sInf T ≤ c := csInf_le hbdd hcT
    have hceq : c = sInf T := le_antisymm hc.2 this
    rw [← hceq, hgc]

end M30T

noncomputable section

open QAlgorithms.Papers.Independent.Support50.P06

open MeasureTheory Filter

open scoped ENNReal BigOperators Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, (19)–(20): thermal entropy and the entropy-matched n-mode thermal
products for BOTH independent ports. Matching entropy never identifies an
arbitrary state's physical mean photons with its entropy photon number. -/
theorem solution (n : ℕ) (hn : 0 < n) :
    (∀ N : ℝ, 0 ≤ N → spectralEntropyNats (identicalThermalKernel 1 N) =
      ENNReal.ofReal (g N)) ∧
    (∀ rhoA rhoB : State (NumberString n),
      spectralEntropyNats rhoA.coefficients ≠ ⊤ →
      spectralEntropyNats rhoB.coefficients ≠ ⊤ →
      spectralEntropyNats (identicalThermalKernel n
        (entropyParameter n (spectralEntropyNats rhoA.coefficients))) =
          spectralEntropyNats rhoA.coefficients ∧
      spectralEntropyNats (identicalThermalKernel n
        (entropyParameter n (spectralEntropyNats rhoB.coefficients))) =
          spectralEntropyNats rhoB.coefficients) := by
  have key : ∀ S : ENNReal, S ≠ ⊤ →
      spectralEntropyNats (identicalThermalKernel n (entropyParameter n S)) = S := by
    intro S hS
    have hs : 0 ≤ S.toReal / (n : ℝ) := by positivity
    obtain ⟨hx0, hgx⟩ := M30T.inv_spec _ hs
    unfold entropyParameter
    rw [M30T.thermal_entropy n hn _ hx0, hgx]
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [mul_div_cancel₀ _ this, ENNReal.ofReal_toReal hS]
  refine ⟨fun N hN => ?_, fun rhoA rhoB hA hB => ⟨key _ hA, key _ hB⟩⟩
  rw [M30T.thermal_entropy 1 one_pos N hN]
  simp


end

