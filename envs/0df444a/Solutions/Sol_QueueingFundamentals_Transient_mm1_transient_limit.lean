-- Prove2me | solution 1 for QueueingFundamentals.Transient.mm1_transient_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:49:15.077458+00:00
-- url     : https://prove2.me/submissions/df69b348-1944-4baa-a376-e574e395f74c

import Mathlib
import Definitions.Def_QueueingFundamentals_Transient_mm1Transient



namespace QueueingFundamentals.Transient

open Filter Topology

lemma qlB_expsum (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x

noncomputable def qlBpois (m : ℝ) (j : ℕ) : ℝ := m ^ j / (j.factorial : ℝ) * Real.exp (-m)

lemma qlB_pois_nonneg {m : ℝ} (hm : 0 ≤ m) (j : ℕ) : 0 ≤ qlBpois m j := by
  unfold qlBpois; positivity

lemma qlB_pois_hasSum (m : ℝ) : HasSum (fun j => qlBpois m j) 1 := by
  have := (qlB_expsum m).mul_right (Real.exp (-m))
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
  exact this

lemma qlB_pois_le_one {m : ℝ} (hm : 0 ≤ m) (j : ℕ) : qlBpois m j ≤ 1 := by
  have := (qlB_pois_hasSum m)
  rw [← this.tsum_eq]
  exact this.summable.le_tsum j (fun k _ => qlB_pois_nonneg hm k)

lemma qlB_pois_stirling {m : ℝ} (hm : 0 ≤ m) {j : ℕ} (hj : j ≠ 0) :
    qlBpois m j ≤ 1 / Real.sqrt j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
  have hst := Stirling.sqrt_pi_le_stirlingSeq hj
  unfold Stirling.stirlingSeq at hst
  have hden : 0 < Real.sqrt (2 * j) * (j / Real.exp 1) ^ j := by positivity
  rw [le_div_iff₀ hden] at hst
  -- m^j e^{-m} ≤ (j/e)^j
  have hkey : m ^ j * Real.exp (-m) ≤ (j / Real.exp 1) ^ j := by
    have h1 : m / j ≤ Real.exp (m / j - 1) := by
      have := Real.add_one_le_exp (m / j - 1); linarith
    have h2 : (m / j) ^ j ≤ Real.exp (m / j - 1) ^ j :=
      pow_le_pow_left₀ (by positivity) h1 j
    rw [← Real.exp_nat_mul] at h2
    have h3 : (j : ℝ) * (m / j - 1) = m - j := by field_simp
    rw [h3, div_pow] at h2
    rw [div_pow, ← Real.exp_nat_mul, mul_one]
    rw [div_le_iff₀ (by positivity)] at h2
    rw [le_div_iff₀ (by positivity)]
    calc m ^ j * Real.exp (-m) * Real.exp (j : ℝ)
        = m ^ j * (Real.exp (-m) * Real.exp (j : ℝ)) := by ring
      _ ≤ Real.exp (m - j) * (j:ℝ) ^ j * (Real.exp (-m) * Real.exp (j : ℝ)) := by
          gcongr
      _ = (j : ℝ) ^ j := by
          have : Real.exp (m - j) * Real.exp (-m) * Real.exp j = 1 := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]; ring_nf
          linear_combination (j:ℝ)^j * this
  have hfac : (0 : ℝ) < j.factorial := by positivity
  unfold qlBpois
  have hsq : Real.sqrt (2 * j) = Real.sqrt 2 * Real.sqrt j := by
    rw [Real.sqrt_mul (by norm_num)]
  have hpi : 1 ≤ Real.sqrt Real.pi * Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  have hsj : 0 < Real.sqrt j := Real.sqrt_pos.2 hjpos
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hfac hsj, one_mul]
  calc m ^ j * Real.exp (-m) * Real.sqrt j ≤ (j / Real.exp 1) ^ j * Real.sqrt j := by gcongr
    _ ≤ (j / Real.exp 1) ^ j * Real.sqrt j * (Real.sqrt Real.pi * Real.sqrt 2) := by
        have : 0 ≤ (j / Real.exp 1) ^ j * Real.sqrt j := by positivity
        nlinarith
    _ = Real.sqrt Real.pi * (Real.sqrt (2 * j) * (j / Real.exp 1) ^ j) := by rw [hsq]; ring
    _ ≤ j.factorial := hst

lemma qlB_pois_unif (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m ≥ M, ∀ j : ℕ, qlBpois m j ≤ ε := by
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε ^ 2)
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; simp at hK; exact absurd hK (not_lt.2 (by positivity))
    · exact h
  have hev : ∀ᶠ m in atTop, ∀ j ∈ Finset.range K, qlBpois m j ≤ ε := by
    rw [Filter.eventually_all_finset]
    intro j _
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).div_const (j.factorial : ℝ)
    rw [zero_div] at ht
    have := ht.eventually (gt_mem_nhds hε)
    filter_upwards [this] with m hm
    unfold qlBpois; rw [div_mul_eq_mul_div]; exact hm.le
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  refine ⟨max M 0, fun m hm j => ?_⟩
  have hm0 : 0 ≤ m := le_trans (le_max_right _ _) hm
  by_cases hj : j < K
  · exact hM m (le_trans (le_max_left _ _) hm) j (Finset.mem_range.2 hj)
  · push_neg at hj
    have hj0 : j ≠ 0 := by omega
    refine le_trans (qlB_pois_stirling hm0 hj0) ?_
    have hjK : (K : ℝ) ≤ j := by exact_mod_cast hj
    have hKpos : (0:ℝ) < K := by exact_mod_cast hK1
    rw [div_le_iff₀ (Real.sqrt_pos.2 (by linarith))]
    have h1 : 1 / ε ^ 2 < j := lt_of_lt_of_le hK hjK
    have h2 : 1 < ε ^ 2 * j := by
      rw [div_lt_iff₀ (by positivity)] at h1; linarith
    have h3 : 1 < (ε * Real.sqrt j) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]; exact h2
    nlinarith [mul_nonneg hε.le (Real.sqrt_nonneg (j:ℝ))]

lemma qlB_bess_term (k j : ℕ) (y : ℝ) :
    (y / 2) ^ (k + 2 * j) / ((Nat.factorial j : ℝ) * (Nat.factorial (k + j) : ℝ))
      = Real.exp y * (qlBpois (y/2) j * qlBpois (y/2) (j + k)) := by
  have he : Real.exp (-(y/2)) * Real.exp (-(y/2)) * Real.exp y = 1 := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_zero]; ring_nf
  calc (y / 2) ^ (k + 2 * j) / ((Nat.factorial j : ℝ) * (Nat.factorial (k + j) : ℝ))
      = (y/2)^j / (j.factorial : ℝ) * ((y/2)^(j+k) / ((j+k).factorial : ℝ)) * 1 := by
        rw [add_comm k j]; ring
    _ = _ := by rw [← he]; unfold qlBpois; ring

lemma qlB_bess_hasSum (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    HasSum (fun j => qlBpois (y/2) j * qlBpois (y/2) (j + k)) (Real.exp (-y) * besselI k y) := by
  have hy2 : 0 ≤ y / 2 := by linarith
  have hs : Summable (fun j => qlBpois (y/2) j * qlBpois (y/2) (j + k)) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (qlB_pois_nonneg hy2 _) (qlB_pois_nonneg hy2 _))
      (fun j => mul_le_of_le_one_right (qlB_pois_nonneg hy2 _) (qlB_pois_le_one hy2 _))
      (qlB_pois_hasSum _).summable
  convert hs.hasSum using 1
  unfold besselI
  simp_rw [qlB_bess_term]
  rw [tsum_mul_left, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

lemma qlB_bess_nonneg (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ besselI k y := by
  have h := (qlB_bess_hasSum k hy).nonneg
    (fun j => mul_nonneg (qlB_pois_nonneg (by linarith) _) (qlB_pois_nonneg (by linarith) _))
  exact nonneg_of_mul_nonneg_right (by rwa [mul_comm] at h) (Real.exp_pos _)

lemma qlB_bess_le (k : ℕ) {y ε : ℝ} (hy : 0 ≤ y) (h : ∀ j, qlBpois (y/2) j ≤ ε) :
    Real.exp (-y) * besselI k y ≤ ε := by
  have h2 := (qlB_pois_hasSum (y/2)).mul_left ε
  rw [mul_one] at h2
  refine hasSum_le (fun j => ?_) (qlB_bess_hasSum k hy) h2
  rw [mul_comm ε]
  exact mul_le_mul_of_nonneg_left (h _) (qlB_pois_nonneg (by linarith) _)

lemma qlB_bess_le_one (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : Real.exp (-y) * besselI k y ≤ 1 :=
  qlB_bess_le k hy (fun j => qlB_pois_le_one (by linarith) j)

lemma qlB_two_sqrt_le (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) :
    2 * Real.sqrt (lam * mu) ≤ lam + mu := by
  have hs := Real.sq_sqrt (mul_pos hlam hmu).le
  nlinarith [Real.sqrt_nonneg (lam * mu), sq_nonneg (lam - mu), sq_nonneg (2 * Real.sqrt (lam * mu) - (lam + mu))]

lemma qlB_E_le (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    Real.exp (-(lam + mu) * t) * besselI k (2 * t * Real.sqrt (lam * mu))
      ≤ Real.exp (-(2 * t * Real.sqrt (lam * mu))) * besselI k (2 * t * Real.sqrt (lam * mu)) := by
  have hy : 0 ≤ 2 * t * Real.sqrt (lam * mu) := by positivity
  apply mul_le_mul_of_nonneg_right _ (qlB_bess_nonneg k hy)
  apply Real.exp_le_exp.2
  have := qlB_two_sqrt_le lam mu hlam hmu
  nlinarith

lemma qlB_E_nonneg (lam mu : ℝ) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    0 ≤ Real.exp (-(lam + mu) * t) * besselI k (2 * t * Real.sqrt (lam * mu)) :=
  mul_nonneg (Real.exp_pos _).le (qlB_bess_nonneg k (by positivity))

lemma qlB_E_le_one (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    Real.exp (-(lam + mu) * t) * besselI k (2 * t * Real.sqrt (lam * mu)) ≤ 1 :=
  le_trans (qlB_E_le lam mu hlam hmu ht k) (qlB_bess_le_one k (by positivity))

lemma qlB_unifT (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t ≥ T, ∀ k : ℕ,
      Real.exp (-(lam + mu) * t) * besselI k (2 * t * Real.sqrt (lam * mu)) ≤ ε := by
  obtain ⟨M, hM⟩ := qlB_pois_unif ε hε
  have hs : 0 < Real.sqrt (lam * mu) := Real.sqrt_pos.2 (mul_pos hlam hmu)
  refine ⟨max (M / Real.sqrt (lam * mu)) 0, le_max_right _ _, fun t ht k => ?_⟩
  have ht0 : 0 ≤ t := le_trans (le_max_right _ _) ht
  have htM : M / Real.sqrt (lam * mu) ≤ t := le_trans (le_max_left _ _) ht
  refine le_trans (qlB_E_le lam mu hlam hmu ht0 k) (qlB_bess_le k (by positivity) fun j => hM _ ?_ j)
  rw [div_le_iff₀ hs] at htM
  linarith

lemma qlB_lim_I (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (k : ℕ) :
    Tendsto (fun t => Real.exp (-(lam + mu) * t) * besselI k (2 * t * Real.sqrt (lam * mu)))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT0, hT⟩ := qlB_unifT lam mu hlam hmu (ε/2) (by linarith)
  refine ⟨T, fun t ht => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (qlB_E_nonneg lam mu (le_trans hT0 ht) k)]
  linarith [hT t ht k]

lemma qlB_tail_summable (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) {t : ℝ} (ht : 0 ≤ t)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (c : ℕ) :
    Summable (fun j : ℕ => x ^ (j + c) * besselI (j + c) (2 * t * Real.sqrt (lam * mu))) := by
  have hE := Real.exp_pos (-(lam + mu) * t)
  have h1 : Summable (fun j : ℕ => x ^ (j + c) *
      (Real.exp (-(lam + mu) * t) * besselI (j + c) (2 * t * Real.sqrt (lam * mu)))) := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (by positivity) (qlB_E_nonneg lam mu ht _))
      (fun j => mul_le_of_le_one_right (by positivity) (qlB_E_le_one lam mu hlam hmu ht _)) ?_
    simp_rw [pow_add]
    exact (summable_geometric_of_lt_one hx0 hx1).mul_right _
  have h2 := h1.mul_left (Real.exp (-(lam + mu) * t))⁻¹
  refine h2.congr (fun j => ?_)
  field_simp

lemma qlB_lim_tail (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (c : ℕ) :
    Tendsto (fun t => Real.exp (-(lam + mu) * t) *
      ∑' j : ℕ, x ^ (j + c) * besselI (j + c) (2 * t * Real.sqrt (lam * mu))) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1x : 0 < 1 - x := by linarith
  obtain ⟨T, hT0, hT⟩ := qlB_unifT lam mu hlam hmu (ε * (1 - x) / 2) (by positivity)
  refine ⟨T, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := le_trans hT0 ht
  have hS := qlB_tail_summable lam mu hlam hmu ht0 hx0 hx1 c
  rw [← tsum_mul_left]
  have hS' : Summable (fun j : ℕ => Real.exp (-(lam + mu) * t) *
      (x ^ (j + c) * besselI (j + c) (2 * t * Real.sqrt (lam * mu)))) := hS.mul_left _
  have hnn : ∀ j : ℕ, 0 ≤ Real.exp (-(lam + mu) * t) *
      (x ^ (j + c) * besselI (j + c) (2 * t * Real.sqrt (lam * mu))) := by
    intro j
    rw [mul_left_comm]
    exact mul_nonneg (by positivity) (qlB_E_nonneg lam mu ht0 _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg hnn)]
  have hgeo := (hasSum_geometric_of_lt_one hx0 hx1).mul_left (ε * (1 - x) / 2)
  have hle : ∑' j : ℕ, Real.exp (-(lam + mu) * t) *
      (x ^ (j + c) * besselI (j + c) (2 * t * Real.sqrt (lam * mu)))
      ≤ ε * (1 - x) / 2 * (1 - x)⁻¹ := by
    refine hasSum_le (fun j => ?_) hS'.hasSum hgeo
    rw [mul_left_comm]
    have hxj : x ^ (j + c) ≤ x ^ j := pow_le_pow_of_le_one hx0 hx1.le (by omega)
    calc x ^ (j + c) * (Real.exp (-(lam + mu) * t) * besselI (j + c) (2 * t * Real.sqrt (lam * mu)))
        ≤ x ^ j * (ε * (1 - x) / 2) :=
          mul_le_mul hxj (hT t ht _) (qlB_E_nonneg lam mu ht0 _) (by positivity)
      _ = _ := by ring
  have : ε * (1 - x) / 2 * (1 - x)⁻¹ = ε / 2 := by field_simp
  linarith

def qlBequiv : (ℕ × ℕ) ⊕ (ℕ × ℕ) ≃ ℕ × ℕ where
  toFun := Sum.elim (fun kj => (kj.2 + kj.1, kj.2)) (fun kj => (kj.2, kj.2 + kj.1 + 1))
  invFun := fun pq => if pq.2 ≤ pq.1 then Sum.inl (pq.1 - pq.2, pq.2)
    else Sum.inr (pq.2 - pq.1 - 1, pq.1)
  left_inv := by
    rintro (⟨k, j⟩ | ⟨k, j⟩)
    · simp
    · simp
      omega
  right_inv := by
    rintro ⟨p, q⟩
    by_cases h : q ≤ p
    · simp only [if_pos h, Sum.elim_inl]; ext <;> simp; omega
    · simp only [if_neg h, Sum.elim_inr]; ext <;> simp <;> omega

noncomputable def qlBf (a b : ℝ) (pq : ℕ × ℕ) : ℝ :=
  a ^ pq.1 / (pq.1.factorial : ℝ) * (b ^ pq.2 / (pq.2.factorial : ℝ))

lemma qlB_prod (a b : ℝ) : HasSum (qlBf a b) (Real.exp a * Real.exp b) := by
  have h1 : Summable (fun n : ℕ => ‖a ^ n / (n.factorial : ℝ)‖) := by
    simpa only [Real.norm_eq_abs] using (qlB_expsum a).summable.abs
  have h2 : Summable (fun n : ℕ => ‖b ^ n / (n.factorial : ℝ)‖) := by
    simpa only [Real.norm_eq_abs] using (qlB_expsum b).summable.abs
  have h3 := summable_mul_of_summable_norm h1 h2
  exact HasSum.mul (qlB_expsum a) (qlB_expsum b) h3

lemma qlB_gen (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) :
    ∃ A B : ℝ, HasSum (fun k : ℕ => x ^ k * besselI k y) A ∧
      HasSum (fun k : ℕ => (1 / x) ^ (k + 1) * besselI (k + 1) y) B ∧
      A + B = Real.exp (y * x / 2 + y / (2 * x)) := by
  have hf := qlB_prod (y * x / 2) (y / (2 * x))
  set f := qlBf (y * x / 2) (y / (2 * x)) with hfdef
  have hg : HasSum (f ∘ qlBequiv) (Real.exp (y * x / 2) * Real.exp (y / (2 * x))) :=
    (qlBequiv.hasSum_iff).2 hf
  have hinl : Summable (f ∘ qlBequiv ∘ Sum.inl) := hg.summable.comp_injective Sum.inl_injective
  have hinr : Summable (f ∘ qlBequiv ∘ Sum.inr) := hg.summable.comp_injective Sum.inr_injective
  have hA : ∀ k : ℕ, HasSum (fun j => (f ∘ qlBequiv ∘ Sum.inl) (k, j)) (x ^ k * besselI k y) := by
    intro k
    have hs : Summable (fun j => (f ∘ qlBequiv ∘ Sum.inl) (k, j)) :=
      hinl.comp_injective (Prod.mk_right_injective k)
    have heq : ∀ j : ℕ, (f ∘ qlBequiv ∘ Sum.inl) (k, j) =
        x ^ k * ((y / 2) ^ (k + 2 * j) / ((Nat.factorial j : ℝ) * (Nat.factorial (k + j) : ℝ))) := by
      intro j
      simp only [Function.comp, qlBequiv, Equiv.coe_fn_mk, Sum.elim_inl, hfdef, qlBf]
      rw [add_comm j k, show y / (2*x) = (y/2) * x⁻¹ by ring, show y*x/2 = (y/2)*x by ring,
        mul_pow, mul_pow, inv_pow]
      have hxj : x ^ (k + j) * (x ^ j)⁻¹ = x ^ k := by
        rw [pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx.ne'), mul_one]
      rw [show k + 2 * j = (k + j) + j by ring, pow_add (y/2) (k+j) j]
      calc (y / 2) ^ (k + j) * x ^ (k + j) / ((k + j).factorial : ℝ) *
            ((y / 2) ^ j * (x ^ j)⁻¹ / (j.factorial : ℝ))
          = (x ^ (k + j) * (x ^ j)⁻¹) * ((y / 2) ^ (k + j) * (y / 2) ^ j /
              ((j.factorial : ℝ) * ((k + j).factorial : ℝ))) := by ring
        _ = _ := by rw [hxj]
    simp_rw [heq] at hs ⊢
    convert hs.hasSum using 1
    unfold besselI
    rw [tsum_mul_left]
  have hB : ∀ k : ℕ, HasSum (fun j => (f ∘ qlBequiv ∘ Sum.inr) (k, j))
      ((1 / x) ^ (k + 1) * besselI (k + 1) y) := by
    intro k
    have hs : Summable (fun j => (f ∘ qlBequiv ∘ Sum.inr) (k, j)) :=
      hinr.comp_injective (Prod.mk_right_injective k)
    have heq : ∀ j : ℕ, (f ∘ qlBequiv ∘ Sum.inr) (k, j) =
        (1 / x) ^ (k + 1) * ((y / 2) ^ (k + 1 + 2 * j) /
          ((Nat.factorial j : ℝ) * (Nat.factorial (k + 1 + j) : ℝ))) := by
      intro j
      simp only [Function.comp, qlBequiv, Equiv.coe_fn_mk, Sum.elim_inr, hfdef, qlBf]
      rw [show j + k + 1 = k + 1 + j by omega, show y / (2*x) = (y/2) * x⁻¹ by ring,
        show y*x/2 = (y/2)*x by ring, mul_pow, mul_pow, inv_pow]
      have hxj : x ^ j * (x ^ (k + 1 + j))⁻¹ = (1 / x) ^ (k + 1) := by
        rw [one_div, inv_pow, pow_add, mul_comm (x ^ (k+1)), mul_inv, ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hx.ne'), one_mul]
      rw [show k + 1 + 2 * j = j + (k + 1 + j) by ring, pow_add (y/2) j (k + 1 + j)]
      calc (y / 2) ^ j * x ^ j / (j.factorial : ℝ) *
            ((y / 2) ^ (k + 1 + j) * (x ^ (k + 1 + j))⁻¹ / ((k + 1 + j).factorial : ℝ))
          = (x ^ j * (x ^ (k + 1 + j))⁻¹) * ((y / 2) ^ j * (y / 2) ^ (k + 1 + j) /
              ((j.factorial : ℝ) * ((k + 1 + j).factorial : ℝ))) := by ring
        _ = _ := by rw [hxj]
    simp_rw [heq] at hs ⊢
    convert hs.hasSum using 1
    unfold besselI
    rw [tsum_mul_left]
  have hAs := hinl.hasSum.prod_fiberwise hA
  have hBs := hinr.hasSum.prod_fiberwise hB
  refine ⟨_, _, hAs, hBs, ?_⟩
  have := HasSum.sum (f := f ∘ qlBequiv) hinl.hasSum hinr.hasSum
  rw [Real.exp_add]; exact this.unique hg

lemma qlB_hpow (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (N : ℕ) :
    (lam / mu) ^ (-((N : ℝ)) / 2) = (Real.sqrt (mu / lam)) ^ N := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← inv_div lam mu,
    Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  congr 1; ring

lemma qlB_expid (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (t : ℝ) :
    2 * t * Real.sqrt (lam * mu) * Real.sqrt (mu / lam) / 2 +
      2 * t * Real.sqrt (lam * mu) / (2 * Real.sqrt (mu / lam)) = (lam + mu) * t := by
  rw [Real.sqrt_mul hlam.le, Real.sqrt_div hmu.le]
  have ha := Real.sq_sqrt hlam.le
  have hb := Real.sq_sqrt hmu.le
  have ha0 : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hb0 : 0 < Real.sqrt mu := Real.sqrt_pos.2 hmu
  have e1 : 2 * t * (Real.sqrt lam * Real.sqrt mu) * (Real.sqrt mu / Real.sqrt lam) / 2
      = t * Real.sqrt mu ^ 2 := by field_simp
  have e2 : 2 * t * (Real.sqrt lam * Real.sqrt mu) / (2 * (Real.sqrt mu / Real.sqrt lam))
      = t * Real.sqrt lam ^ 2 := by field_simp
  rw [e1, e2, ha, hb]; ring

lemma qlB_lim_one (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hlt : lam < mu) (c : ℕ) :
    Tendsto (fun t => Real.exp (-(lam + mu) * t) *
      ∑' j : ℕ, (Real.sqrt (mu / lam)) ^ (j + c) *
        besselI (j + c) (2 * t * Real.sqrt (lam * mu))) atTop (𝓝 1) := by
  set x := Real.sqrt (mu / lam) with hxdef
  have hx1 : 1 < x := by
    rw [hxdef, Real.lt_sqrt (by norm_num), one_pow, one_lt_div hlam]; exact hlt
  have hx0 : 0 < x := by linarith
  have hix0 : 0 ≤ 1 / x := by positivity
  have hix1 : 1 / x < 1 := by rw [div_lt_one hx0]; exact hx1
  have hlimB := qlB_lim_tail lam mu hlam hmu hix0 hix1 1
  have hlimF : Tendsto (fun t => ∑ k ∈ Finset.range c,
      x ^ k * (Real.exp (-(lam + mu) * t) * besselI k (2 * t * Real.sqrt (lam * mu))))
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range c) (fun k _ => (qlB_lim_I lam mu hlam hmu k).const_mul (x ^ k))
    simpa using this
  have hlim := (tendsto_const_nhds (x := (1:ℝ))).sub (hlimB.add hlimF)
  rw [add_zero, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  have hy : 0 ≤ 2 * t * Real.sqrt (lam * mu) := by positivity
  obtain ⟨A, B, hA, hB, hAB⟩ := qlB_gen x (2 * t * Real.sqrt (lam * mu)) hx0 hy
  rw [hxdef, qlB_expid lam mu hlam hmu t] at hAB
  have hsplit := hA.summable.sum_add_tsum_nat_add c
  rw [hA.tsum_eq] at hsplit
  have hE : Real.exp (-(lam + mu) * t) * Real.exp ((lam + mu) * t) = 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]; ring_nf
  have hF : ∑ k ∈ Finset.range c, x ^ k * (Real.exp (-(lam + mu) * t) *
      besselI k (2 * t * Real.sqrt (lam * mu))) = Real.exp (-(lam + mu) * t) *
      ∑ k ∈ Finset.range c, x ^ k * besselI k (2 * t * Real.sqrt (lam * mu)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hF, hB.tsum_eq]
  linear_combination (-1 : ℝ) * hE - Real.exp (-(lam + mu) * t) * hAB
    - Real.exp (-(lam + mu) * t) * hsplit

theorem mm1_transient_limit_core (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) :
    (lam / mu < 1 →
        Tendsto (fun t : ℝ => mm1Transient lam mu i n t) atTop
          (𝓝 ((1 - lam / mu) * (lam / mu) ^ n))) ∧
      (1 ≤ lam / mu → Tendsto (fun t : ℝ => mm1Transient lam mu i n t) atTop (𝓝 0)) := by
  set x := Real.sqrt (mu / lam) with hxdef
  have hfun : (fun t : ℝ => mm1Transient lam mu i n t) = fun t =>
      (lam / mu) ^ (((n : ℝ) - (i : ℝ)) / 2) *
        (Real.exp (-(lam + mu) * t) * besselI ((n : ℤ) - (i : ℤ)).natAbs (2 * t * Real.sqrt (lam * mu)))
      + (lam / mu) ^ (((n : ℝ) - (i : ℝ) - 1) / 2) *
        (Real.exp (-(lam + mu) * t) * besselI (n + i + 1) (2 * t * Real.sqrt (lam * mu)))
      + (1 - lam / mu) * (lam / mu) ^ n * (Real.exp (-(lam + mu) * t) *
          ∑' j : ℕ, x ^ (j + (n + i + 2)) * besselI (j + (n + i + 2)) (2 * t * Real.sqrt (lam * mu))) := by
    funext t
    have htail : ∑' j : ℕ, (lam / mu) ^ (-(((j + n + i + 2 : ℕ) : ℝ)) / 2)
        * besselI (j + n + i + 2) (2 * t * Real.sqrt (lam * mu))
        = ∑' j : ℕ, x ^ (j + (n + i + 2)) * besselI (j + (n + i + 2)) (2 * t * Real.sqrt (lam * mu)) := by
      refine tsum_congr (fun j => ?_)
      rw [qlB_hpow lam mu hlam hmu, show j + n + i + 2 = j + (n + i + 2) by omega]
    simp only [mm1Transient, besselIZ]
    rw [htail]
    ring
  rw [hfun]
  have L1 := (qlB_lim_I lam mu hlam hmu ((n : ℤ) - (i : ℤ)).natAbs).const_mul
    ((lam / mu) ^ (((n : ℝ) - (i : ℝ)) / 2))
  have L2 := (qlB_lim_I lam mu hlam hmu (n + i + 1)).const_mul
    ((lam / mu) ^ (((n : ℝ) - (i : ℝ) - 1) / 2))
  rw [mul_zero] at L1 L2
  constructor
  · intro hρ
    have hlt : lam < mu := by rwa [div_lt_one hmu] at hρ
    have L3 := (qlB_lim_one lam mu hlam hmu hlt (n + i + 2)).const_mul ((1 - lam / mu) * (lam / mu) ^ n)
    rw [mul_one] at L3
    have := (L1.add L2).add L3
    rwa [zero_add, zero_add] at this
  · intro hρ
    have L3 : Tendsto (fun t => (1 - lam / mu) * (lam / mu) ^ n * (Real.exp (-(lam + mu) * t) *
          ∑' j : ℕ, x ^ (j + (n + i + 2)) * besselI (j + (n + i + 2)) (2 * t * Real.sqrt (lam * mu))))
        atTop (𝓝 0) := by
      rcases hρ.eq_or_lt with h | h
      · rw [← h, sub_self]; simp
      · have hgt : mu < lam := by rwa [one_lt_div hmu] at h
        have hx0 : 0 ≤ x := Real.sqrt_nonneg _
        have hx1 : x < 1 := by
          rw [hxdef, Real.sqrt_lt' (by norm_num), one_pow, div_lt_one hlam]; exact hgt
        have := (qlB_lim_tail lam mu hlam hmu hx0 hx1 (n + i + 2)).const_mul
          ((1 - lam / mu) * (lam / mu) ^ n)
        rwa [mul_zero] at this
    have := (L1.add L2).add L3
    rwa [zero_add, zero_add] at this

end QueueingFundamentals.Transient

open QueueingFundamentals.Transient
open Filter Topology

theorem solution (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (i n : ℕ) :
    (lam / mu < 1 →
        Tendsto (fun t : ℝ => mm1Transient lam mu i n t) atTop
          (𝓝 ((1 - lam / mu) * (lam / mu) ^ n))) ∧
      (1 ≤ lam / mu → Tendsto (fun t : ℝ => mm1Transient lam mu i n t) atTop (𝓝 0)) := by
  exact mm1_transient_limit_core lam mu hlam hmu i n
