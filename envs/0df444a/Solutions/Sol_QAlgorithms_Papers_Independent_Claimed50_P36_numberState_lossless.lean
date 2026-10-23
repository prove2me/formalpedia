-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P36.numberState_lossless
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:03:10.324062+00:00
-- url     : https://prove2.me/submissions/d1f9910e-cf98-4d19-ae08-821e93cc84a9

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P36

noncomputable section

open Filter Topology

namespace X6P36

def symWord (L K : ℕ) (s : Sym (Fin (L+1)) K) : Fin L → ℕ :=
  fun i => (s : Multiset (Fin (L+1))).count i.succ

lemma sym_total (L K : ℕ) (s : Sym (Fin (L+1)) K) :
    (s : Multiset (Fin (L+1))).count 0 + ∑ i, symWord L K s i = K := by
  have h := Multiset.sum_count_eq_card (s := (Finset.univ : Finset (Fin (L+1))))
    (m := (s : Multiset (Fin (L+1)))) (by simp)
  rw [Fin.sum_univ_succ] at h
  simpa [symWord, s.2] using h

lemma symWord_sum (L K : ℕ) (s : Sym (Fin (L+1)) K) : ∑ i, symWord L K s i ≤ K := by
  have := sym_total L K s; omega

lemma symWord_inj (L K : ℕ) : Function.Injective (symWord L K) := by
  intro s t h
  apply Sym.coe_injective
  ext a
  have hs := sym_total L K s
  have ht := sym_total L K t
  rw [h] at hs
  refine Fin.cases ?_ (fun i => ?_) a
  · omega
  · exact congrFun h i

lemma card_words (L K : ℕ) :
    ((Finset.univ : Finset (Sym (Fin (L+1)) K)).image (symWord L K)).card = (L + K).choose K := by
  rw [Finset.card_image_of_injective _ (symWord_inj L K), Finset.card_univ,
    Sym.card_sym_eq_choose]
  simp

/-- generating-function bound on the number of words with bounded total. -/
lemma card_le_exp (L : ℕ) (m : ℝ) (hm : 0 < m) (T : Finset (Fin L → ℕ))
    (hT : ∀ w ∈ T, (∑ t, (w t : ℝ)) ≤ L * m) :
    (T.card : ℝ) ≤ Real.exp (L * (Real.log (1 + m) + m * Real.log ((1 + m) / m))) := by
  set x : ℝ := m / (1 + m) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hx, div_lt_one (by linarith)]; linarith
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ w ∈ T, ∀ t, w t < B := by
    refine ⟨(T.sup fun w => ∑ t, w t) + 1, fun w hw t => ?_⟩
    have h1 : w t ≤ ∑ t, w t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have h2 : ∑ t, w t ≤ T.sup fun w => ∑ t, w t := Finset.le_sup (f := fun w => ∑ t, w t) hw
    omega
  have hsub : T ⊆ Fintype.piFinset (fun _ : Fin L => Finset.range B) := by
    intro w hw; simp only [Fintype.mem_piFinset, Finset.mem_range]; exact hB w hw
  -- each word has weight ≥ x^(L m)
  have hw : ∀ w ∈ T, x ^ (L * m) ≤ ∏ t, x ^ (w t) := by
    intro w hw
    rw [Finset.prod_pow_eq_pow_sum, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le
    push_cast; exact hT w hw
  have hsum : ∑ w ∈ T, ∏ t, x ^ (w t) ≤ (1 + m) ^ L := by
    calc ∑ w ∈ T, ∏ t, x ^ (w t) ≤ ∑ w ∈ Fintype.piFinset (fun _ : Fin L => Finset.range B),
          ∏ t, x ^ (w t) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∏ _t : Fin L, ∑ j ∈ Finset.range B, x ^ j := (Finset.prod_univ_sum _ _).symm
      _ ≤ ∏ _t : Fin L, (1 + m) := by
          apply Finset.prod_le_prod (fun _ _ => by positivity)
          intro _ _
          have := geom_sum_Ico_le_of_lt_one (m := 0) (n := B) hx0.le hx1
          simp only [Finset.range_eq_Ico] at *
          refine this.trans (le_of_eq ?_)
          rw [hx]; field_simp; ring
      _ = (1 + m) ^ L := by simp
  have key : (T.card : ℝ) * x ^ (L * m) ≤ (1 + m) ^ L := by
    calc (T.card : ℝ) * x ^ (L * m) = ∑ w ∈ T, x ^ (L * m) := by simp
      _ ≤ _ := (Finset.sum_le_sum hw).trans hsum
  have hxp : 0 < x ^ (L * m) := Real.rpow_pos_of_pos hx0 _
  rw [← le_div_iff₀ hxp] at key
  refine key.trans (le_of_eq ?_)
  have h1 : (1 + m) ^ L = Real.exp (L * Real.log (1 + m)) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have h2 : x ^ ((L:ℝ) * m) = Real.exp (L * m * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]; ring_nf
  have h3 : Real.log x = - Real.log ((1 + m) / m) := by
    rw [hx, ← Real.log_inv, inv_div]
  rw [h1, h2, h3, ← Real.exp_sub]
  congr 1; ring

end X6P36

open Filter Topology Real

namespace X6P36

lemma log_fact_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial) ≤ n * Real.log n - n + 1 + Real.log n / 2 := by
  have hs : Stirling.stirlingSeq n ≤ Real.exp 1 / √2 := by
    rw [← Stirling.stirlingSeq_one]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  unfold Stirling.stirlingSeq at hs
  rw [div_le_iff₀ (by positivity)] at hs
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  calc Real.log (n.factorial) ≤ Real.log (Real.exp 1 / √2 * (√(2 * n) * (n / Real.exp 1) ^ n)) :=
        Real.log_le_log hf hs
    _ = n * Real.log n - n + 1 + Real.log n / 2 := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_div (by positivity)
          (by positivity), Real.log_exp, Real.log_sqrt (by positivity), Real.log_sqrt (by positivity),
          Real.log_mul (by positivity) (by positivity)]
        ring

lemma log_fact_ge (n : ℕ) : n * Real.log n - n ≤ Real.log (n.factorial) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have h1 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h2 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  linarith

lemma log_choose_ge (L K : ℕ) (hL : 1 ≤ L) (hK : 1 ≤ K) :
    (L + K : ℝ) * Real.log (L + K) - K * Real.log K - L * Real.log L - 2
      - (Real.log K + Real.log L) / 2 ≤ Real.log ((L + K).choose K) := by
  have hc := Nat.choose_mul_factorial_mul_factorial (n := L + K) (k := K) (by omega)
  have hpos : (0:ℝ) < (L + K).choose K := by exact_mod_cast Nat.choose_pos (by omega)
  have e : Real.log ((L + K).factorial) = Real.log ((L + K).choose K) + Real.log (K.factorial)
      + Real.log (L.factorial) := by
    rw [← Real.log_mul hpos.ne' (by positivity), ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    have : L + K - K = L := by omega
    rw [this] at hc; exact_mod_cast hc.symm
  have a1 := log_fact_ge (L + K)
  have a2 := log_fact_le K hK
  have a3 := log_fact_le L hL
  push_cast at a1
  linarith

end X6P36

open Filter Topology Real

namespace X6P36

def phi (t : ℝ) : ℝ := (1 + t) * Real.log (1 + t) - t * Real.log t

lemma phi_cont (m : ℝ) (hm : 0 < m) : ContinuousAt phi m := by
  unfold phi
  apply ContinuousAt.sub
  · exact (continuousAt_const.add continuousAt_id).mul
      ((continuousAt_const.add continuousAt_id).log (by simp; linarith))
  · exact continuousAt_id.mul (continuousAt_id.log hm.ne')

lemma eventually_rate (m r : ℝ) (hm : 0 < m) (hr : r < phi m) :
    ∀ᶠ L : ℕ in atTop, r < Real.log ((L + ⌊L * m⌋₊).choose ⌊L * m⌋₊) / L := by
  set K : ℕ → ℕ := fun L => ⌊(L:ℝ) * m⌋₊ with hK
  -- K/L → m
  have hKL : Tendsto (fun L : ℕ => (K L : ℝ) / L) atTop (𝓝 m) := by
    have up : ∀ᶠ L : ℕ in atTop, (K L : ℝ) / L ≤ m := by
      filter_upwards [eventually_gt_atTop 0] with L hL
      rw [div_le_iff₀ (by exact_mod_cast hL), mul_comm]
      exact Nat.floor_le (by positivity)
    have lo : ∀ᶠ L : ℕ in atTop, m - 1 / L ≤ (K L : ℝ) / L := by
      filter_upwards [eventually_gt_atTop 0] with L hL
      have hL' : (0:ℝ) < L := by exact_mod_cast hL
      have := Nat.lt_floor_add_one ((L:ℝ) * m)
      have e : ((L:ℝ) * m - 1) / L = m - 1 / L := by field_simp
      rw [← e]
      exact div_le_div_of_nonneg_right (by simp only [hK]; linarith) hL'.le
    have t1 : Tendsto (fun L : ℕ => m - 1 / (L:ℝ)) atTop (𝓝 m) := by
      simpa using (tendsto_const_nhds (x := m)).sub tendsto_one_div_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' t1 tendsto_const_nhds lo up
  have hphi : Tendsto (fun L : ℕ => phi ((K L : ℝ) / L)) atTop (𝓝 (phi m)) :=
    (phi_cont m hm).tendsto.comp hKL
  -- error term
  set err : ℕ → ℝ := fun L => (2 + (Real.log (K L) + Real.log L) / 2) / L with herr
  have hlog : Tendsto (fun L : ℕ => Real.log L / (L:ℝ)) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
    convert this using 1; ext L; simp
  have herr0 : Tendsto err atTop (𝓝 0) := by
    have up : Tendsto (fun L : ℕ => 2 * (1 / (L:ℝ)) + (Real.log m / 2) * (1 / (L:ℝ))
        + Real.log L / (L:ℝ)) atTop (𝓝 0) := by
      have := ((tendsto_one_div_atTop_nhds_zero_nat.const_mul 2).add
        (tendsto_one_div_atTop_nhds_zero_nat.const_mul (Real.log m / 2))).add hlog
      simpa using this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds up
    · filter_upwards [eventually_gt_atTop 0] with L hL
      simp only [herr]
      apply div_nonneg _ (by positivity)
      have : 0 ≤ Real.log (K L) := Real.log_natCast_nonneg _
      have : 0 ≤ Real.log L := Real.log_natCast_nonneg _
      linarith
    · filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop ⌈1/m⌉₊] with L hL hL2
      have hL' : (0:ℝ) < L := by exact_mod_cast hL
      have hK1 : 1 ≤ K L := by
        simp only [hK]; rw [Nat.one_le_floor_iff]
        have := Nat.ceil_le.mp hL2
        rw [div_le_iff₀ hm] at this; linarith
      have hKle : (K L : ℝ) ≤ L * m := Nat.floor_le (by positivity)
      have : Real.log (K L) ≤ Real.log L + Real.log m := by
        rw [← Real.log_mul hL'.ne' hm.ne']
        exact Real.log_le_log (by exact_mod_cast hK1) hKle
      simp only [herr]
      rw [div_le_iff₀ hL']
      field_simp
      nlinarith
  have hlim : Tendsto (fun L : ℕ => phi ((K L : ℝ) / L) - err L) atTop (𝓝 (phi m)) := by
    simpa using hphi.sub herr0
  filter_upwards [hlim.eventually_const_lt hr, eventually_gt_atTop 0,
    eventually_ge_atTop ⌈1/m⌉₊] with L h1 hL hL2
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  have hK1 : 1 ≤ K L := by
    simp only [hK]; rw [Nat.one_le_floor_iff]
    have := Nat.ceil_le.mp hL2
    rw [div_le_iff₀ hm] at this; linarith
  have hb := log_choose_ge L (K L) hL hK1
  have hK1' : (0:ℝ) < K L := by exact_mod_cast hK1
  -- rewrite phi(K/L)*L
  have hid : phi ((K L : ℝ) / L) * L = (L + K L : ℝ) * Real.log (L + K L) - K L * Real.log (K L)
      - L * Real.log L := by
    unfold phi
    have e1 : 1 + (K L : ℝ) / L = (L + K L) / L := by field_simp
    rw [e1, Real.log_div (by positivity) hL'.ne', Real.log_div hK1'.ne' hL'.ne']
    field_simp
    ring
  refine h1.trans_le ?_
  rw [le_div_iff₀ hL', sub_mul, hid]
  simp only [herr]
  rw [div_mul_cancel₀ _ hL'.ne']
  linarith

end X6P36

open Filter Topology
open scoped ENNReal

namespace X6P36
open QAlgorithms.Papers.Independent.Claimed50.P36
open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

lemma G_eq (m : ℝ) : Real.log 2 * bosonicEntropy m = phi m := by
  unfold bosonicEntropy phi
  have : Real.log 2 ≠ 0 := by positivity
  field_simp; ring_nf

lemma phi_alt (m : ℝ) (hm : 0 < m) :
    phi m = Real.log (1 + m) + m * Real.log ((1 + m) / m) := by
  unfold phi; rw [Real.log_div (by linarith) hm.ne']; ring

lemma phi_zero : phi 0 = 0 := by simp [phi]

lemma phi_nonneg (m : ℝ) (hm : 0 ≤ m) : 0 ≤ phi m := by
  rcases hm.eq_or_lt with rfl | hm
  · simp [phi_zero]
  rw [phi_alt m hm]
  have : 0 ≤ Real.log (1 + m) := Real.log_nonneg (by linarith)
  have : 0 ≤ Real.log ((1 + m) / m) := Real.log_nonneg (by rw [le_div_iff₀ hm]; linarith)
  positivity

lemma phi_pos (m : ℝ) (hm : 0 < m) : 0 < phi m := by
  rw [phi_alt m hm]
  have : 0 < Real.log (1 + m) := Real.log_pos (by linarith)
  have : 0 ≤ Real.log ((1 + m) / m) := Real.log_nonneg (by rw [le_div_iff₀ hm]; linarith)
  positivity

/-! thermal law -/

lemma one_sub_r (m : ℝ) (hm : 0 ≤ m) : 1 - m / (1 + m) = 1 / (1 + m) := by
  have : (1 + m) ≠ 0 := by linarith
  field_simp; ring

lemma thermal_hasSum (m : ℝ) (hm : 0 ≤ m) : HasSum (thermalLaw m) 1 := by
  have h0 : 0 ≤ m / (1 + m) := by positivity
  have h1 : m / (1 + m) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have := (hasSum_geometric_of_lt_one h0 h1).mul_left (1 / (1 + m))
  have hv : 1 / (1 + m) * (1 - m / (1 + m))⁻¹ = 1 := by
    rw [one_sub_r m hm]; have : (1 + m) ≠ 0 := by linarith
    field_simp
  rw [hv] at this
  exact this

lemma thermal_mean (m : ℝ) (hm : 0 ≤ m) :
    HasSum (fun n : ℕ => (n : ℝ) * thermalLaw m n) m := by
  have h0 : 0 ≤ m / (1 + m) := by positivity
  have h1 : ‖m / (1 + m)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg h0, div_lt_one (by linarith)]; linarith
  have := (hasSum_coe_mul_geometric_of_norm_lt_one h1).mul_left (1 / (1 + m))
  have hf : (fun n : ℕ => (n : ℝ) * thermalLaw m n) =
      fun i : ℕ => 1 / (1 + m) * ((i : ℝ) * (m / (1 + m)) ^ i) := by
    ext n; unfold thermalLaw; ring
  have hv : 1 / (1 + m) * (m / (1 + m) / (1 - m / (1 + m)) ^ 2) = m := by
    rw [one_sub_r m hm]; have : (1 + m) ≠ 0 := by linarith
    field_simp
  rw [hf]; rw [hv] at this; exact this

lemma thermal_nonneg (m : ℝ) (hm : 0 ≤ m) (n : ℕ) : 0 ≤ thermalLaw m n := by
  unfold thermalLaw; positivity

lemma thermal_log (m : ℝ) (hm : 0 < m) (n : ℕ) :
    Real.log (thermalLaw m n) = -(Real.log (1 + m) + n * Real.log ((1 + m) / m)) := by
  unfold thermalLaw
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, one_div, Real.log_inv,
    ← inv_div, Real.log_inv]
  ring

lemma thermal_numberLaw (m : ℝ) (hm : 0 ≤ m) : NumberLaw m (thermalLaw m) :=
  ⟨thermal_nonneg m hm, thermal_hasSum m hm, (thermal_mean m hm).summable,
    (thermal_mean m hm).tsum_eq.le⟩

/-- entropy as ofReal of a real sum -/
lemma entropy_of_hasSum (p : ℕ → ℝ) (s : ℝ) (hp : ∀ n, 0 ≤ -p n * Real.log (p n))
    (h : HasSum (fun n => -p n * Real.log (p n)) s) :
    numberEntropy p ≠ ⊤ ∧ (numberEntropy p).toReal = s := by
  unfold numberEntropy
  rw [← ENNReal.ofReal_tsum_of_nonneg hp h.summable, h.tsum_eq]
  refine ⟨ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ?_⟩
  exact h.nonneg hp

lemma neg_log_nonneg (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 ≤ -x * Real.log x := by
  have := Real.log_nonpos h0 h1
  nlinarith

lemma law_le_one (p : ℕ → ℝ) (h0 : ∀ n, 0 ≤ p n) (h : HasSum p 1) (n : ℕ) : p n ≤ 1 :=
  le_hasSum h n (fun j _ => h0 j)

lemma thermal_entropy (m : ℝ) (hm : 0 ≤ m) :
    numberEntropy (thermalLaw m) ≠ ⊤ ∧ (numberEntropy (thermalLaw m)).toReal = phi m := by
  have hnn : ∀ n, 0 ≤ -thermalLaw m n * Real.log (thermalLaw m n) := fun n =>
    neg_log_nonneg _ (thermal_nonneg m hm n)
      (law_le_one _ (thermal_nonneg m hm) (thermal_hasSum m hm) n)
  rcases hm.eq_or_lt with rfl | hm'
  · have hz : (fun n => -thermalLaw 0 n * Real.log (thermalLaw 0 n)) = fun _ => 0 := by
      ext n; cases n <;> simp [thermalLaw]
    apply entropy_of_hasSum _ _ hnn
    rw [hz, phi_zero]; exact hasSum_zero
  apply entropy_of_hasSum _ _ hnn
  have e : (fun n => -thermalLaw m n * Real.log (thermalLaw m n)) = fun n =>
      Real.log (1 + m) * thermalLaw m n + Real.log ((1 + m) / m) * ((n : ℝ) * thermalLaw m n) := by
    ext n; rw [thermal_log m hm' n]; ring
  rw [e, phi_alt m hm']
  have := ((thermal_hasSum m hm).mul_left (Real.log (1 + m))).add
    ((thermal_mean m hm).mul_left (Real.log ((1 + m) / m)))
  simpa [mul_comm] using this

lemma maxent (m : ℝ) (hm : 0 ≤ m) (p : ℕ → ℝ) (hp : NumberLaw m p) :
    numberEntropy p ≠ ⊤ ∧ (numberEntropy p).toReal ≤ phi m := by
  obtain ⟨h0, h1, hs, hmean⟩ := hp
  have hnn : ∀ n, 0 ≤ -p n * Real.log (p n) := fun n =>
    neg_log_nonneg _ (h0 n) (law_le_one _ h0 h1 n)
  rcases hm.eq_or_lt with rfl | hm'
  · -- all mass at 0
    have hz : ∀ n : ℕ, (n : ℝ) * p n = 0 := by
      have hsum0 : HasSum (fun n : ℕ => (n : ℝ) * p n) 0 := by
        have hle : ∑' n : ℕ, (n : ℝ) * p n = 0 :=
          le_antisymm hmean (tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg n) (h0 n))
        rw [← hle]; exact hs.hasSum
      have := (hasSum_zero_iff_of_nonneg (fun n => mul_nonneg (Nat.cast_nonneg n) (h0 n))).mp hsum0
      exact fun n => congrFun this n
    have hpn : ∀ n, n ≠ 0 → p n = 0 := by
      intro n hn
      have := hz n
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by exact_mod_cast h) hn
      · exact h
    have hp0 : p 0 = 1 := by
      have := h1.tsum_eq
      rw [tsum_eq_single 0 hpn] at this; exact this
    have hzz : (fun n => -p n * Real.log (p n)) = fun _ => 0 := by
      ext n; rcases eq_or_ne n 0 with rfl | hn
      · simp [hp0]
      · simp [hpn n hn]
    obtain ⟨a, b⟩ := entropy_of_hasSum p 0 hnn (by rw [hzz]; exact hasSum_zero)
    exact ⟨a, by rw [b, phi_zero]⟩
  set q := thermalLaw m
  set A := Real.log (1 + m)
  set B := Real.log ((1 + m) / m)
  have hB : 0 ≤ B := Real.log_nonneg (by rw [le_div_iff₀ hm']; linarith)
  set y : ℕ → ℝ := fun n => A * p n + B * ((n : ℝ) * p n) + (q n - p n)
  have hy : HasSum y (A * 1 + B * (∑' n : ℕ, (n : ℝ) * p n) + (1 - 1)) :=
    ((h1.mul_left A).add (hs.hasSum.mul_left B)).add ((thermal_hasSum m hm).sub h1)
  have hxy : ∀ n, -p n * Real.log (p n) ≤ y n := by
    intro n
    have hq : 0 < q n := by simp only [q, thermalLaw]; positivity
    have hlq : Real.log (q n) = -(A + n * B) := thermal_log m hm' n
    rcases (h0 n).eq_or_lt with hpz | hpp
    · rw [← hpz]; simp only [y, ← hpz]; simp; exact hq.le
    · have hl := Real.log_le_sub_one_of_pos (div_pos hq hpp)
      rw [Real.log_div hq.ne' hpp.ne', hlq] at hl
      have := mul_le_mul_of_nonneg_left hl hpp.le
      simp only [y]
      have e : p n * (q n / p n - 1) = q n - p n := by field_simp
      rw [e] at this
      nlinarith [this]
  have hxs : Summable (fun n => -p n * Real.log (p n)) :=
    Summable.of_nonneg_of_le hnn hxy hy.summable
  obtain ⟨a, b⟩ := entropy_of_hasSum p _ hnn hxs.hasSum
  refine ⟨a, ?_⟩
  rw [b, phi_alt m hm']
  calc ∑' n, -p n * Real.log (p n) ≤ ∑' n, y n := hxs.tsum_le_tsum hxy hy.summable
    _ = A * 1 + B * (∑' n : ℕ, (n : ℝ) * p n) + (1 - 1) := hy.tsum_eq
    _ ≤ A + m * B := by nlinarith

end X6P36

open Filter Topology
open scoped ENNReal

namespace X6P36
open QAlgorithms.Papers.Independent.Claimed50.P36

lemma loss_one (n y : ℕ) : lossTransition 1 n y = if y = n then 1 else 0 := by
  unfold lossTransition
  by_cases h : y = n
  · subst h; simp
  · by_cases h2 : y ≤ n
    · have : 0 < n - y := by omega
      simp [h, h2, zero_pow this.ne']
    · simp [h, h2]

lemma error_eq {budget : ℝ} {L M : ℕ} (code : NumberCode 1 budget L M) :
    numberError code = 1 - (∑ i, code.decode (code.letters i) i) / M := by
  unfold numberError
  congr 3
  ext i
  have : (fun y : Fin L → ℕ => (∏ t, lossTransition 1 (code.letters i t) (y t)) * code.decode y i)
      = fun y => if y = code.letters i then code.decode y i else 0 := by
    ext y
    simp only [loss_one]
    rw [Finset.prod_boole]
    by_cases h : y = code.letters i
    · simp [h]
    · have : ¬ ∀ t ∈ Finset.univ, y t = code.letters i t := by
        intro hh; exact h (funext fun t => hh t (Finset.mem_univ t))
      have : ¬ ∀ t, y t = code.letters i t := by
        intro hh; exact h (funext hh)
      simp [h, this]
  rw [this, tsum_ite_eq]

lemma success_le {budget : ℝ} {L M : ℕ} (code : NumberCode 1 budget L M) :
    ∑ i, code.decode (code.letters i) i ≤ ((Finset.univ.image code.letters).card : ℝ) := by
  set T := Finset.univ.image code.letters
  rw [← Finset.sum_fiberwise_of_maps_to (g := code.letters) (t := T)
    (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro w _
  calc ∑ i ∈ Finset.univ with code.letters i = w, code.decode (code.letters i) i
      = ∑ i ∈ Finset.univ with code.letters i = w, code.decode w i := by
        apply Finset.sum_congr rfl; intro i hi; rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ i, code.decode w i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => code.decode_nonneg w i)
    _ ≤ ((1:ℕ):ℝ) := by rw [code.decode_total]; simp

lemma words_card_le (m : ℝ) (hm : 0 ≤ m) (L : ℕ) (T : Finset (Fin L → ℕ))
    (hT : ∀ w ∈ T, (∑ t, (w t : ℝ)) ≤ L * m) : (T.card : ℝ) ≤ Real.exp (L * phi m) := by
  rcases hm.eq_or_lt with rfl | hm'
  · rw [phi_zero, mul_zero, Real.exp_zero]
    have : T ⊆ {0} := by
      intro w hw
      have h := hT w hw
      simp only [mul_zero] at h
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => (Nat.cast_nonneg (w t) : (0:ℝ) ≤ _))).mp
        (le_antisymm h (Finset.sum_nonneg fun t _ => Nat.cast_nonneg _))
      simp only [Finset.mem_singleton]
      funext t; exact_mod_cast h2 t (Finset.mem_univ t)
    exact_mod_cast (Finset.card_le_card this).trans (by simp)
  · rw [phi_alt m hm']; exact card_le_exp L m hm' T hT

lemma converse (m : ℝ) (hm : 0 ≤ m) (r : ℝ) (hr : r ∈ numberRates 1 m) : r ≤ phi m := by
  obtain ⟨_, hach⟩ := hr
  apply le_of_forall_pos_lt_add
  intro δ hδ
  set ε := min (δ / 2) (1 / 2) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hε2 : ε ≤ δ / 2 := min_le_left _ _
  obtain ⟨L0, hL0, hL⟩ := hach ε hε0
  set L := max L0 (⌈2 * Real.log 2 / δ⌉₊ + 1)
  obtain ⟨M, hM, code, herr, hrate⟩ := hL L (le_max_left _ _)
  have hLpos : (0:ℝ) < L := by
    have : 0 < L := lt_of_lt_of_le hL0 (le_max_left _ _); exact_mod_cast this
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  rw [error_eq] at herr
  have hS := success_le code
  have hT := words_card_le m hm L (Finset.univ.image code.letters) (by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact_mod_cast code.energy i)
  -- (1 - ε) M ≤ exp(L phi)
  have h1 : (1 - ε) * M ≤ Real.exp (L * phi m) := by
    have : (1 - ε) * M ≤ ∑ i, code.decode (code.letters i) i := by
      have := herr; rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hMpos] at this
      linarith
    linarith
  have h2 : Real.log M ≤ L * phi m + Real.log 2 := by
    have : (M:ℝ) ≤ Real.exp (L * phi m) * 2 := by nlinarith
    calc Real.log M ≤ Real.log (Real.exp (L * phi m) * 2) := Real.log_le_log hMpos this
      _ = L * phi m + Real.log 2 := by rw [Real.log_mul (by positivity) (by norm_num), Real.log_exp]
  have h3 : Real.log 2 / L < δ / 2 := by
    rw [div_lt_iff₀ hLpos]
    have hc : (⌈2 * Real.log 2 / δ⌉₊ : ℝ) + 1 ≤ L := by
      exact_mod_cast le_max_right L0 (⌈2 * Real.log 2 / δ⌉₊ + 1)
    have := Nat.le_ceil (2 * Real.log 2 / δ)
    rw [div_le_iff₀ hδ] at this
    nlinarith
  have h4 : Real.log M / L ≤ phi m + Real.log 2 / L := by
    rw [div_le_iff₀ hLpos, add_mul, div_mul_cancel₀ _ hLpos.ne']; linarith
  linarith

lemma zero_mem (m : ℝ) (hm : 0 ≤ m) : (0:ℝ) ∈ numberRates 1 m := by
  refine ⟨le_rfl, fun ε hε => ⟨1, one_pos, fun L _ => ⟨1, one_pos, ?_⟩⟩⟩
  let code : NumberCode 1 m L 1 :=
    { letters := fun _ _ => 0
      energy := fun _ => by simp; positivity
      decode := fun _ _ => 1
      decode_nonneg := fun _ _ => zero_le_one
      decode_total := fun _ => by simp }
  refine ⟨code, ?_, ?_⟩
  · rw [error_eq]; simp [code]; exact hε.le
  · simp; exact hε.le

lemma achievable (m : ℝ) (hm : 0 < m) (r : ℝ) (hr0 : 0 ≤ r) (hr : r < phi m) :
    r ∈ numberRates 1 m := by
  refine ⟨hr0, fun ε hε => ?_⟩
  obtain ⟨L1, hL1⟩ := eventually_atTop.mp (eventually_rate m r hm hr)
  refine ⟨max L1 1, by omega, fun L hL => ?_⟩
  have hLr := hL1 L (le_of_max_le_left hL)
  set K := ⌊(L:ℝ) * m⌋₊
  set T := (Finset.univ : Finset (Sym (Fin (L+1)) K)).image (symWord L K)
  have hTc : T.card = (L + K).choose K := card_words L K
  have hMpos : 0 < T.card := by rw [hTc]; exact Nat.choose_pos (by omega)
  let e := T.equivFin
  let letters : Fin T.card → Fin L → ℕ := fun i => (e.symm i).1
  have hinj : Function.Injective letters := by
    intro i j h; exact e.symm.injective (Subtype.ext h)
  let dec : (Fin L → ℕ) → Fin T.card := fun y =>
    if h : ∃ i, letters i = y then h.choose else ⟨0, hMpos⟩
  let code : NumberCode 1 m L T.card :=
    { letters := letters
      energy := fun i => by
        obtain ⟨w, hw⟩ := e.symm i
        have hwT : (e.symm i).1 ∈ T := (e.symm i).2
        obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hwT
        have h1 := symWord_sum L K s
        have h2 : (K : ℝ) ≤ L * m := Nat.floor_le (by positivity)
        show (∑ t, ((e.symm i).1 t : ℝ)) ≤ L * m
        rw [← hs]
        calc (∑ t, (symWord L K s t : ℝ)) = ((∑ t, symWord L K s t : ℕ) : ℝ) := by push_cast; rfl
          _ ≤ K := by exact_mod_cast h1
          _ ≤ L * m := h2
      decode := fun y i => if i = dec y then 1 else 0
      decode_nonneg := fun y i => by positivity
      decode_total := fun y => by simp }
  refine ⟨T.card, hMpos, code, ?_, ?_⟩
  · rw [error_eq]
    have : ∀ i, code.decode (code.letters i) i = 1 := by
      intro i
      show (if i = dec (letters i) then (1:ℝ) else 0) = 1
      have hex : ∃ j, letters j = letters i := ⟨i, rfl⟩
      have : dec (letters i) = i := by
        simp only [dec, dif_pos hex]; exact hinj hex.choose_spec
      simp [this]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [div_self (by exact_mod_cast hMpos.ne')]; linarith
  · rw [hTc]
    have := hLr
    linarith

end X6P36

open QAlgorithms.Papers.Independent.Claimed50.P36 in
open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy) in
open scoped ENNReal in
theorem solution (m : ℝ) (hm : 0 ≤ m) :
    NumberLaw m (thermalLaw m) ∧
    HasSum (fun n : ℕ => (n : ℝ) * thermalLaw m n) m ∧
    numberEntropy (thermalLaw m) ≠ ⊤ ∧
    (numberEntropy (thermalLaw m)).toReal = (Real.log 2 * bosonicEntropy m) ∧
    (∀ p : ℕ → ℝ, NumberLaw m p →
      numberEntropy p ≠ ⊤ ∧ (numberEntropy p).toReal ≤ (Real.log 2 * bosonicEntropy m)) ∧
    BddAbove (numberRates 1 m) ∧ numberCapacity 1 m = (Real.log 2 * bosonicEntropy m) ∧
    (0 < m → (Real.log 2 * bosonicEntropy m) = Real.log (1 + m) + m * Real.log (1 + 1 / m)) := by
  rw [X6P36.G_eq]
  refine ⟨X6P36.thermal_numberLaw m hm, X6P36.thermal_mean m hm, (X6P36.thermal_entropy m hm).1,
    (X6P36.thermal_entropy m hm).2, fun p hp => X6P36.maxent m hm p hp,
    ⟨X6P36.phi m, fun r hr => X6P36.converse m hm r hr⟩, ?_, ?_⟩
  · unfold numberCapacity
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨0, X6P36.zero_mem m hm⟩
      (fun r hr => X6P36.converse m hm r hr)
    intro w hw
    rcases lt_or_ge w 0 with h | h
    · exact ⟨0, X6P36.zero_mem m hm, h⟩
    · have hm' : 0 < m := by
        rcases hm.eq_or_lt with rfl | hm'
        · rw [X6P36.phi_zero] at hw; linarith
        · exact hm'
      refine ⟨(w + X6P36.phi m) / 2, X6P36.achievable m hm' _ (by linarith) (by linarith), by linarith⟩
  · intro hm'
    rw [X6P36.phi_alt m hm']
    congr 2; field_simp; ring_nf
