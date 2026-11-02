-- Prove2me | solution 1 for OfflineCensoredPricing.Identifiability.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T04:09:40.118773+00:00
-- url     : https://prove2.me/submissions/cdb329ab-3507-44b1-aa01-b978fec004e9

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace DKWHelper

/-! ### Analytic part -/

noncomputable def J (t : ℝ) : ℝ :=
  t * Real.cosh t / Real.sinh t - (t / Real.sinh t) * (t / Real.sinh t) / 2 - 1 / 2
    - Real.log (Real.cosh t)

open Classical in
noncomputable def cnt {Ω ι : Type*} [Fintype ι] (B : Set Ω) (x : ι → Ω) : ℕ :=
  (Finset.univ.filter (fun j => x j ∈ B)).card

lemma tendsto_t_sinh : Tendsto (fun t : ℝ => t / Real.sinh t) (𝓝[>] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_sinh 0).tendsto_slope_zero_right
  simp only [zero_add, Real.sinh_zero, sub_zero, smul_eq_mul, Real.cosh_zero] at h
  have h2 := h.inv₀ one_ne_zero
  rw [inv_one] at h2
  refine h2.congr (fun t => ?_)
  show (t⁻¹ * Real.sinh t)⁻¹ = t / Real.sinh t
  rw [mul_inv, inv_inv, div_eq_mul_inv]

lemma tendsto_cosh0 : Tendsto Real.cosh (𝓝[>] 0) (𝓝 1) := by
  have := Real.continuous_cosh.continuousAt (x := 0)
  have h : Tendsto Real.cosh (𝓝 0) (𝓝 1) := by simpa [ContinuousAt] using this
  exact h.mono_left nhdsWithin_le_nhds

lemma tendsto_r : Tendsto (fun t : ℝ => t * Real.cosh t / Real.sinh t) (𝓝[>] 0) (𝓝 1) := by
  have := tendsto_t_sinh.mul tendsto_cosh0
  rw [one_mul] at this
  refine this.congr (fun t => ?_)
  ring

lemma J_tendsto : Tendsto J (𝓝[>] 0) (𝓝 0) := by
  have h1 := tendsto_r
  have h2 := (tendsto_t_sinh.mul tendsto_t_sinh).div_const 2
  have h3 : Tendsto (fun t => Real.log (Real.cosh t)) (𝓝[>] 0) (𝓝 (Real.log 1)) :=
    tendsto_cosh0.log one_ne_zero
  have := ((h1.sub h2).sub_const (1 / 2)).sub h3
  have e : (1 : ℝ) - 1 * 1 / 2 - 1 / 2 - Real.log 1 = 0 := by
    rw [Real.log_one]; norm_num
  rw [e] at this
  exact this

lemma J_hasDeriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt J ((Real.sinh t - t * Real.cosh t) ^ 2 / (Real.sinh t ^ 3 * Real.cosh t)) t := by
  have hS : Real.sinh t ≠ 0 := (Real.sinh_pos_iff.2 ht).ne'
  have hC : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  have h1 := ((hasDerivAt_id' t).mul (Real.hasDerivAt_cosh t)).div (Real.hasDerivAt_sinh t) hS
  have hd := (hasDerivAt_id' t).div (Real.hasDerivAt_sinh t) hS
  have h2 := hd.mul hd
  have h3 := (Real.hasDerivAt_cosh t).log hC
  have h := ((h1.sub (h2.div_const 2)).sub_const (1 / 2)).sub h3
  have e : Real.cosh t ^ 2 - Real.sinh t ^ 2 - 1 = 0 := by
    rw [Real.cosh_sq_sub_sinh_sq t]; norm_num
  refine (show HasDerivAt J _ t from h).congr_deriv ?_
  rw [← sub_eq_zero]
  calc _ = (Real.cosh t ^ 2 - Real.sinh t ^ 2 - 1) *
        (Real.sinh t ^ 2 - t * Real.sinh t * Real.cosh t) / (Real.sinh t ^ 3 * Real.cosh t) := by
        try simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply, id]
        field_simp
        ring
    _ = 0 := by rw [e]; simp

lemma J_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ J t := by
  have hmono : MonotoneOn J (Set.Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun x hx => (J_hasDeriv hx).continuousAt.continuousWithinAt) ?_ ?_
    · intro x hx
      rw [interior_Ioi] at hx
      exact (J_hasDeriv hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      rw [(J_hasDeriv hx).deriv]
      have hS : 0 < Real.sinh x := Real.sinh_pos_iff.2 hx
      have hC := Real.cosh_pos x
      positivity
  have h : ∀ᶠ s in 𝓝[>] (0 : ℝ), J s ≤ J t := by
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs
    exact hmono hs.1 ht hs.2.le
  exact le_of_tendsto J_tendsto h

lemma tangent {lam e : ℝ} (hl : 0 < lam)
    (h0 : (1 / 2) * (1 / 2 + lam) * (Real.log (1 / 2 + lam) - Real.log (1 / 2)) / lam
      - 1 / 2 - e = 0) {p : ℝ} (hp : 0 < p) :
    (1 / 2 + e) * (Real.log (1 / 2 + lam) - Real.log (1 / 2)) ≤
      (p + e) * (Real.log (p + lam) - Real.log p) := by
  set rho : ℝ → ℝ := fun p => p * (p + lam) * (Real.log (p + lam) - Real.log p) / lam - p - e
    with hrho
  set phi : ℝ → ℝ := fun p => (p + e) * (Real.log (p + lam) - Real.log p) with hphi
  have hL : ∀ {p : ℝ}, 0 < p →
      HasDerivAt (fun p => Real.log (p + lam) - Real.log p) (1 / (p + lam) - 1 / p) p := by
    intro p hp
    have h1 : HasDerivAt (fun p => Real.log (p + lam)) (1 / (p + lam)) p := by
      have := ((hasDerivAt_id' p).add_const lam).log (add_pos hp hl).ne'
      exact this
    exact h1.sub (Real.hasDerivAt_log hp.ne' |>.congr_deriv (by simp))
  have hphid : ∀ {p : ℝ}, 0 < p → HasDerivAt phi
      ((Real.log (p + lam) - Real.log p) + (p + e) * (1 / (p + lam) - 1 / p)) p := by
    intro p hp
    have := ((hasDerivAt_id' p).add_const e).mul (hL hp)
    refine (show HasDerivAt phi _ p from this).congr_deriv ?_
    ring
  have hrhod : ∀ {p : ℝ}, 0 < p → HasDerivAt rho
      ((2 * p + lam) * (Real.log (p + lam) - Real.log p) / lam - 2) p := by
    intro p hp
    have h1 : HasDerivAt (fun p : ℝ => p * (p + lam)) (1 * (p + lam) + p * 1) p :=
      (hasDerivAt_id' p).mul ((hasDerivAt_id' p).add_const lam)
    have := (((h1.mul (hL hp)).div_const lam).sub (hasDerivAt_id' p)).sub_const e
    refine (show HasDerivAt rho _ p from this).congr_deriv ?_
    have : p + lam ≠ 0 := (add_pos hp hl).ne'
    field_simp
    ring
  have hrhomono : MonotoneOn rho (Set.Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun x hx => (hrhod hx).continuousAt.continuousWithinAt) ?_ ?_
    · intro x hx
      rw [interior_Ioi] at hx
      exact (hrhod hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      have hx' : 0 < x := hx
      rw [(hrhod hx).deriv]
      have hlog := Real.le_log_one_add_of_nonneg (x := lam / x) (by positivity)
      have e1 : Real.log (x + lam) - Real.log x = Real.log (1 + lam / x) := by
        rw [← Real.log_div (by positivity) hx'.ne']
        congr 1
        field_simp
      rw [e1]
      have e2 : 2 * (lam / x) / (lam / x + 2) = 2 * lam / (2 * x + lam) := by
        field_simp
        ring
      rw [e2] at hlog
      have h3 : 2 * lam / (2 * x + lam) * (2 * x + lam) / lam = 2 := by
        field_simp
      have h4 : 2 * lam / (2 * x + lam) * (2 * x + lam) / lam ≤
          (2 * x + lam) * Real.log (1 + lam / x) / lam := by
        rw [mul_comm (2 * x + lam) (Real.log _)]
        gcongr
      linarith
  have hrho0 : rho (1 / 2) = 0 := h0
  have hphi' : ∀ {x : ℝ}, 0 < x →
      (Real.log (x + lam) - Real.log x) + (x + e) * (1 / (x + lam) - 1 / x) =
        rho x * (lam / (x * (x + lam))) := by
    intro x hx
    simp only [hrho]
    have : x + lam ≠ 0 := by positivity
    field_simp
    ring
  have hpos : ∀ {x : ℝ}, 0 < x → 0 < lam / (x * (x + lam)) := by
    intro x hx
    positivity
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hphi0 : phi (1 / 2) = (1 / 2 + e) * (Real.log (1 / 2 + lam) - Real.log (1 / 2)) := rfl
  change _ ≤ phi p
  rw [← hphi0]
  rcases le_total (1 / 2) p with hle | hle
  · have hm : MonotoneOn phi (Set.Ici (1 / 2)) := by
      have hx0 : ∀ x ∈ Set.Ici ((1 : ℝ) / 2), 0 < x := fun x hx =>
        lt_of_lt_of_le hhalf hx
      refine monotoneOn_of_deriv_nonneg (convex_Ici _)
        (fun x hx => (hphid (hx0 x hx)).continuousAt.continuousWithinAt) ?_ ?_
      · intro x hx
        rw [interior_Ici] at hx
        exact (hphid (hhalf.trans hx)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        have hx1 : (1 : ℝ) / 2 < x := hx
        have hx' : 0 < x := hhalf.trans hx1
        rw [(hphid hx').deriv, hphi' hx']
        have : 0 ≤ rho x := by
          rw [← hrho0]
          exact hrhomono hhalf hx' hx1.le
        exact mul_nonneg this (hpos hx').le
    exact hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hle) hle
  · have hm : AntitoneOn phi (Set.Ioc 0 (1 / 2)) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc _ _)
        (fun x hx => (hphid hx.1).continuousAt.continuousWithinAt) ?_ ?_
      · intro x hx
        rw [interior_Ioc] at hx
        exact (hphid hx.1).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ioc] at hx
        have hx' : 0 < x := hx.1
        rw [(hphid hx').deriv, hphi' hx']
        have : rho x ≤ 0 := by
          rw [← hrho0]
          exact hrhomono hx' hhalf hx.2.le
        exact mul_nonpos_of_nonpos_of_nonneg this (hpos hx').le
    exact hm ⟨hp, hle⟩ ⟨hhalf, le_rfl⟩ hle

lemma exists_t {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ (t * Real.cosh t / Real.sinh t + t - 1) / 2 = ε := by
  set eta : ℝ → ℝ := fun t => (t * Real.cosh t / Real.sinh t + t - 1) / 2 with heta
  have hlim : Tendsto eta (𝓝[>] 0) (𝓝 ((1 + 0 - 1) / 2)) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    exact ((tendsto_r.add hid).sub_const 1).div_const 2
  have e0 : ((1 : ℝ) + 0 - 1) / 2 = 0 := by norm_num
  rw [e0] at hlim
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), eta t < ε := hlim.eventually_lt_const hε
  have hb : (0 : ℝ) < 2 * ε + 1 := by positivity
  obtain ⟨t0, ht0, ht1⟩ := (hev.and (Ioo_mem_nhdsGT hb)).exists
  have hcont : ContinuousOn eta (Set.Icc t0 (2 * ε + 1)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ht1.1 hx.1
    have hS : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.2 hx0).ne'
    apply ContinuousAt.continuousWithinAt
    simp only [heta]
    fun_prop (disch := assumption)
  have hend : ε ≤ eta (2 * ε + 1) := by
    simp only [heta]
    have hS : 0 < Real.sinh (2 * ε + 1) := Real.sinh_pos_iff.2 hb
    have hC := Real.cosh_pos (2 * ε + 1)
    have : 0 ≤ (2 * ε + 1) * Real.cosh (2 * ε + 1) / Real.sinh (2 * ε + 1) := by positivity
    linarith
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc ht1.2.le hcont ⟨ht0.le, hend⟩
  exact ⟨t, lt_of_lt_of_le ht1.1 ht.1, hte⟩

lemma analytic {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ p : ℝ, 0 < p →
      Real.log (1 + lam) + 2 * ε ^ 2 ≤ (p + ε) * (Real.log (p + lam) - Real.log p) := by
  obtain ⟨t, ht, hte⟩ := exists_t hε
  have hS : 0 < Real.sinh t := Real.sinh_pos_iff.2 ht
  have hC : 0 < Real.cosh t := Real.cosh_pos t
  have hid : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq t
  have hSC : 0 < Real.cosh t + Real.sinh t := by positivity
  obtain ⟨S, hSdef⟩ : ∃ S, S = Real.sinh t := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = Real.cosh t := ⟨_, rfl⟩
  rw [← hSdef] at hS hte hid hSC
  rw [← hCdef] at hC hte hid hSC
  have hE : Real.exp (2 * t) = (C + S) ^ 2 := by
    rw [hCdef, hSdef, Real.cosh_add_sinh, ← Real.exp_nat_mul]
    norm_num
  have hEt : Real.exp t = C + S := by rw [hCdef, hSdef, Real.cosh_add_sinh]
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = S * (C + S) := ⟨_, rfl⟩
  have hlam : 0 < lam := by rw [hlamdef]; exact mul_pos hS hSC
  have hS' : S ≠ 0 := hS.ne'
  have hSC' : C + S ≠ 0 := hSC.ne'
  have hE2 : Real.exp (2 * t) = 1 + 2 * lam := by
    rw [hE, hlamdef]
    linear_combination hid
  have hL0 : Real.log (1 / 2 + lam) - Real.log (1 / 2) = 2 * t := by
    rw [← Real.log_div (by positivity) (by norm_num)]
    have : (1 / 2 + lam) / (1 / 2) = Real.exp (2 * t) := by rw [hE2]; ring
    rw [this, Real.log_exp]
  have hr : t * C / S = 2 * ε - t + 1 := by linarith
  have h0 : (1 / 2) * (1 / 2 + lam) * (Real.log (1 / 2 + lam) - Real.log (1 / 2)) / lam
      - 1 / 2 - ε = 0 := by
    rw [hL0]
    have h5 : (1 / 2 + lam) = (C + S) ^ 2 / 2 := by
      have := hE2; rw [hE] at this; linarith
    rw [h5, hlamdef]
    have h6 : (1 / 2) * ((C + S) ^ 2 / 2) * (2 * t) / (S * (C + S)) = (t * C / S + t) / 2 := by
      field_simp
      try ring
    rw [h6]
    linarith
  refine ⟨lam, hlam, fun p hp => le_trans ?_ (tangent hlam h0 hp)⟩
  rw [hL0]
  have h1lam : 1 + lam = C * Real.exp t := by
    rw [hEt, hlamdef]
    linear_combination (-1 : ℝ) * hid
  rw [h1lam, Real.log_mul hC.ne' (Real.exp_pos t).ne', Real.log_exp]
  have hJ := J_nonneg ht
  simp only [J] at hJ
  rw [← hCdef, ← hSdef] at hJ
  have hts : (t / S) * (t / S) = (t * C / S) ^ 2 - t ^ 2 := by
    have hz : C ^ 2 - S ^ 2 - 1 = 0 := by rw [hid]; norm_num
    rw [← sub_eq_zero]
    calc _ = - (t ^ 2 / S ^ 2) * (C ^ 2 - S ^ 2 - 1) := by
          field_simp
          ring
      _ = 0 := by rw [hz, mul_zero]
  rw [hts, hr] at hJ
  have e1 : (2 * ε - t + 1) - ((2 * ε - t + 1) ^ 2 - t ^ 2) / 2 - 1 / 2 - Real.log C =
      2 * ε * t - 2 * ε ^ 2 - Real.log C := by ring
  have e2 : (1 / 2 + ε) * (2 * t) = t + 2 * ε * t := by ring
  rw [e1] at hJ
  rw [e2]
  linarith

lemma real_key {lam p ε : ℝ} {n N : ℕ} (hlam : 0 < lam) (hp : 0 < p)
    (h : Real.log (1 + lam) + 2 * ε ^ 2 ≤ (p + ε) * (Real.log (p + lam) - Real.log p))
    (hN : (n : ℝ) * (p + ε) < N) :
    (1 + lam) ^ n * Real.exp (2 * n * ε ^ 2) * p ^ N ≤ (p + lam) ^ N := by
  have h1lam : 0 < 1 + lam := by positivity
  have hplam : 0 < p + lam := by positivity
  rw [← Real.log_le_log_iff (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_exp, Real.log_pow, Real.log_pow]
  have hd : 0 ≤ Real.log (p + lam) - Real.log p := by
    have := Real.log_le_log hp (by linarith : p ≤ p + lam)
    linarith
  have h1 := mul_le_mul_of_nonneg_right hN.le hd
  have h2 := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)
  nlinarith [h1, h2]

/-! ### Maximal inequality -/

lemma cnt_subtype {Ω ι : Type*} [Fintype ι] (p : ι → Prop) [Fintype {j // p j}] (B : Set Ω)
    (x : ι → Ω) (h : ∀ j, x j ∈ B → p j) :
    cnt B (fun j : {j // p j} => x j) = cnt B x := by
  classical
  unfold cnt
  refine Finset.card_bij (fun j _ => j.1) ?_ ?_ ?_
  · intro j hj
    simpa using hj
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ⟨⟨b, h b hb⟩, by simpa using hb, rfl⟩

theorem maximal {Ω : Type*} [MeasurableSpace Ω] (B : ℚ → Set Ω) (hB : ∀ q, MeasurableSet (B q))
    (hmono : Monotone B) (lam C : ℝ≥0∞) (s : Finset ℚ) :
    ∀ (ν : Measure Ω) [IsFiniteMeasure ν] (ι : Type) [Fintype ι],
      C * Measure.pi (fun _ : ι => ν)
        {x | ∃ q ∈ s, C * (ν (B q)) ^ cnt (B q) x ≤ (ν (B q) + lam) ^ cnt (B q) x} ≤
      (ν Set.univ + lam) ^ Fintype.card ι := by
  classical
  induction s using Finset.induction_on_max with
  | empty => intro ν _ ι _; simp
  | insert a s ha ih =>
    intro ν _ ι _
    set T := B a with hT
    set P := ν T with hP
    set Q := ν Tᶜ with hQ
    have hsub : ∀ q ∈ s, B q ⊆ T := fun q hq => hmono (ha q hq).le
    have huniv : ν Set.univ = P + Q := (measure_add_measure_compl (hB a)).symm
    set E : Set (ι → Ω) :=
      {x | ∃ q ∈ insert a s, C * (ν (B q)) ^ cnt (B q) x ≤ (ν (B q) + lam) ^ cnt (B q) x} with hE
    have cell : ∀ S : Finset ι, C * Measure.pi (fun _ : ι => ν)
        ({x | ∀ j, j ∈ S ↔ x j ∈ T} ∩ E)
        ≤ (P + lam) ^ S.card * Q ^ (Fintype.card ι - S.card) := by
      intro S
      let p : ι → Prop := (· ∈ S)
      have mp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => ν) p
      let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => Ω) p
      let ES : Set ({j // p j} → Ω) :=
        {y | ∃ q ∈ s, C * ((ν.restrict T) (B q)) ^ cnt (B q) y ≤
          ((ν.restrict T) (B q) + lam) ^ cnt (B q) y}
      let A : Set ({j // p j} → Ω) :=
        {y | (∀ j, y j ∈ T) ∧ ((C * P ^ S.card ≤ (P + lam) ^ S.card) ∨ y ∈ ES)}
      let A' : Set ({j // ¬ p j} → Ω) := Set.pi Set.univ fun _ => Tᶜ
      have hsubset : ({x | ∀ j, j ∈ S ↔ x j ∈ T} ∩ E) ⊆ e ⁻¹' (A ×ˢ A') := by
        rintro x ⟨hcell, q, hq, hx⟩
        refine ⟨⟨fun j => (hcell j.1).1 j.2, ?_⟩, ?_⟩
        · rcases Finset.mem_insert.1 hq with rfl | hqs
          · left
            have hc : cnt T x = S.card := by
              unfold cnt
              congr 1
              ext j
              simp [hcell j]
            rw [hc] at hx
            exact hx
          · right
            refine ⟨q, hqs, ?_⟩
            have h1 : (ν.restrict T) (B q) = ν (B q) := by
              rw [Measure.restrict_apply (hB q), Set.inter_eq_left.2 (hsub q hqs)]
            have h2 : cnt (B q) (fun j : {j // p j} => x j) = cnt (B q) x :=
              cnt_subtype p (B q) x (fun j hj => (hcell j).2 (hsub q hqs hj))
            rw [h1]
            change C * ν (B q) ^ cnt (B q) (fun j : {j // p j} => x j) ≤
              (ν (B q) + lam) ^ cnt (B q) (fun j : {j // p j} => x j)
            rw [h2]
            exact hx
        · intro j _
          exact fun hj => j.2 ((hcell j.1).2 hj)
      have hA' : Measure.pi (fun _ : {j // ¬ p j} => ν) A' =
          Q ^ (Fintype.card ι - S.card) := by
        rw [Measure.pi_pi]
        simp only [Finset.prod_const, Finset.card_univ]
        congr 1
        rw [Fintype.card_subtype_compl]
        simp [p]
      have hA : C * Measure.pi (fun _ : {j // p j} => ν) A ≤ (P + lam) ^ S.card := by
        have hmT : MeasurableSet (Set.pi Set.univ fun _ : {j // p j} => T) :=
          MeasurableSet.univ_pi (fun _ => hB a)
        have hcardS : Fintype.card {j // p j} = S.card := by simp [p]
        by_cases hc : C * P ^ S.card ≤ (P + lam) ^ S.card
        · have h1 : A ⊆ Set.pi Set.univ fun _ : {j // p j} => T := fun y hy j _ => hy.1 j
          have h2 : Measure.pi (fun _ : {j // p j} => ν) A ≤ P ^ S.card := by
            refine (measure_mono h1).trans ?_
            rw [Measure.pi_pi]
            simp [hcardS, hP]
          exact (mul_le_mul' le_rfl h2).trans hc
        · have h1 : A ⊆ ES ∩ Set.pi Set.univ fun _ : {j // p j} => T := by
            intro y hy
            refine ⟨?_, fun j _ => hy.1 j⟩
            exact hy.2.resolve_left hc
          have h2 : Measure.pi (fun _ : {j // p j} => ν) (ES ∩ Set.pi Set.univ fun _ => T) =
              Measure.pi (fun _ : {j // p j} => ν.restrict T) ES := by
            rw [← Measure.restrict_apply' hmT, Measure.restrict_pi_pi]
          have h3 := ih (ν.restrict T) {j // p j}
          rw [Measure.restrict_apply_univ, hcardS] at h3
          calc C * Measure.pi (fun _ : {j // p j} => ν) A
              ≤ C * Measure.pi (fun _ : {j // p j} => ν) (ES ∩ Set.pi Set.univ fun _ => T) := by
                gcongr
            _ = C * Measure.pi (fun _ : {j // p j} => ν.restrict T) ES := by rw [h2]
            _ ≤ _ := h3
      calc C * Measure.pi (fun _ : ι => ν) ({x | ∀ j, j ∈ S ↔ x j ∈ T} ∩ E)
          ≤ C * Measure.pi (fun _ : ι => ν) (e ⁻¹' (A ×ˢ A')) := by
            gcongr
        _ = C * (Measure.pi (fun _ : {j // p j} => ν) A *
              Measure.pi (fun _ : {j // ¬ p j} => ν) A') := by
            rw [mp.measure_preimage_equiv, Measure.prod_prod]
            first | rfl | congr! | convert rfl
        _ = (C * Measure.pi (fun _ : {j // p j} => ν) A) * Q ^ (Fintype.card ι - S.card) := by
            rw [hA', mul_assoc]
        _ ≤ _ := by gcongr
    have hcover : E ⊆ ⋃ S ∈ (Finset.univ : Finset (Finset ι)),
        ({x | ∀ j, j ∈ S ↔ x j ∈ T} ∩ E) := by
      intro x hx
      simp only [Set.mem_iUnion]
      refine ⟨Finset.univ.filter (fun j => x j ∈ T), Finset.mem_univ _, ?_, hx⟩
      intro j
      simp
    calc C * Measure.pi (fun _ : ι => ν) E
        ≤ C * ∑ S ∈ (Finset.univ : Finset (Finset ι)),
            Measure.pi (fun _ : ι => ν) ({x | ∀ j, j ∈ S ↔ x j ∈ T} ∩ E) := by
          gcongr
          exact (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
      _ = ∑ S ∈ (Finset.univ : Finset (Finset ι)),
            C * Measure.pi (fun _ : ι => ν) ({x | ∀ j, j ∈ S ↔ x j ∈ T} ∩ E) := Finset.mul_sum _ _ _
      _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset ι)),
            (P + lam) ^ S.card * Q ^ (Fintype.card ι - S.card) :=
          Finset.sum_le_sum (fun S _ => cell S)
      _ = (P + lam + Q) ^ Fintype.card ι := by
          have := Finset.sum_pow_mul_eq_add_pow (P + lam) Q (Finset.univ : Finset ι)
          rw [Finset.powerset_univ, Finset.card_univ] at this
          exact this
      _ = _ := by
          rw [huniv]
          congr 1
          ring

theorem one_sided {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (B : ℚ → Set Ω) (hB : ∀ q, MeasurableSet (B q)) (hmono : Monotone B) (n : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    Measure.pi (fun _ : Fin n => ν) {x | ∃ q, (n : ℝ) * ((ν (B q)).toReal + ε) < cnt (B q) x} ≤
      ENNReal.ofReal (Real.exp (-(2 * (n : ℝ) * ε ^ 2))) := by
  obtain ⟨lam, hlam, han⟩ := analytic hε
  set A : ℝ := (1 + lam) ^ n with hA
  have hApos : 0 < A := by positivity
  set X : ℝ := 2 * (n : ℝ) * ε ^ 2 with hX
  set C : ℝ≥0∞ := ENNReal.ofReal (A * Real.exp X) with hC
  have key : ∀ (q : ℚ) (x : Fin n → Ω), (n : ℝ) * ((ν (B q)).toReal + ε) < cnt (B q) x →
      C * ν (B q) ^ cnt (B q) x ≤ (ν (B q) + ENNReal.ofReal lam) ^ cnt (B q) x := by
    intro q x hx
    set N := cnt (B q) x
    have hPtop : ν (B q) ≠ ⊤ := measure_ne_top _ _
    have hp0 : 0 ≤ (ν (B q)).toReal := ENNReal.toReal_nonneg
    rcases hp0.eq_or_lt with hp | hp
    · have hP0 : ν (B q) = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).1 hp.symm with h | h
        · exact h
        · exact absurd h hPtop
      have hN : N ≠ 0 := by
        intro h
        rw [h, ← hp] at hx
        have : (0 : ℝ) < (n : ℝ) * (0 + ε) := by
          have : (0 : ℝ) < n := by exact_mod_cast hn
          positivity
        simp at hx
        linarith
      rw [hP0, zero_pow hN, mul_zero]
      exact zero_le ..
    · have hPeq : ν (B q) = ENNReal.ofReal (ν (B q)).toReal := (ENNReal.ofReal_toReal hPtop).symm
      rw [hPeq, ← ENNReal.ofReal_add hp.le hlam.le, ← ENNReal.ofReal_pow hp.le,
        ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (real_key hlam hp (han _ hp) hx)
  have hfin : ∀ s : Finset ℚ, Measure.pi (fun _ : Fin n => ν)
      {x | ∃ q ∈ s, C * (ν (B q)) ^ cnt (B q) x ≤ (ν (B q) + ENNReal.ofReal lam) ^ cnt (B q) x} ≤
      ENNReal.ofReal (Real.exp (-X)) := by
    intro s
    have h := maximal B hB hmono (ENNReal.ofReal lam) C s ν (Fin n)
    rw [measure_univ, Fintype.card_fin, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one hlam.le, ← ENNReal.ofReal_pow (by positivity), ← hA] at h
    have hC0 : C ≠ 0 := by
      rw [hC]
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
    have h2 := (ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl hCt)).2 ((mul_comm _ _).trans_le h)
    refine h2.trans (le_of_eq ?_)
    rw [hC, ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    rw [Real.exp_neg]
    field_simp
  have hsubset : {x : Fin n → Ω | ∃ q, (n : ℝ) * ((ν (B q)).toReal + ε) < cnt (B q) x} ⊆
      ⋃ s : Finset ℚ, {x | ∃ q ∈ s, C * (ν (B q)) ^ cnt (B q) x ≤
        (ν (B q) + ENNReal.ofReal lam) ^ cnt (B q) x} := by
    rintro x ⟨q, hq⟩
    simp only [Set.mem_iUnion]
    exact ⟨{q}, q, by simp, key q x hq⟩
  have hdir : Directed (· ⊆ ·) (fun s : Finset ℚ => {x : Fin n → Ω | ∃ q ∈ s,
      C * (ν (B q)) ^ cnt (B q) x ≤ (ν (B q) + ENNReal.ofReal lam) ^ cnt (B q) x}) := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · rintro x ⟨q, hq, h⟩
      exact ⟨q, Finset.mem_union_left _ hq, h⟩
    · rintro x ⟨q, hq, h⟩
      exact ⟨q, Finset.mem_union_right _ hq, h⟩
  calc _ ≤ Measure.pi (fun _ : Fin n => ν) (⋃ s : Finset ℚ, {x | ∃ q ∈ s,
        C * (ν (B q)) ^ cnt (B q) x ≤ (ν (B q) + ENNReal.ofReal lam) ^ cnt (B q) x}) :=
        measure_mono hsubset
    _ = _ := hdir.measure_iUnion
    _ ≤ _ := iSup_le hfin

lemma exists_rat_close (μ : Measure ℝ) [IsProbabilityMeasure μ] {n : ℕ} (ω : Fin n → ℝ)
    {x ε : ℝ}
    (h : ε < |((Finset.univ.filter (fun j => ω j ≤ x)).card : ℝ) / (n : ℝ) - cdf μ x|) :
    ∃ q : ℚ, ε <
      |((Finset.univ.filter (fun j => ω j ≤ (q : ℝ))).card : ℝ) / (n : ℝ) - cdf μ (q : ℝ)| := by
  set c : ℝ := ((Finset.univ.filter (fun j => ω j ≤ x)).card : ℝ) with hc
  have h1 : ∀ᶠ y in 𝓝[>] x, ∀ j, (ω j ≤ y ↔ ω j ≤ x) := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : ω j ≤ x
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact ⟨fun _ => hj, fun _ => hj.trans (le_of_lt hy)⟩
    · push_neg at hj
      filter_upwards [Ioo_mem_nhdsGT hj] with y hy
      exact ⟨fun h => absurd h (not_le.2 hy.2), fun h => absurd h (not_le.2 hj)⟩
  have h2 : ∀ᶠ y in 𝓝[>] x, ε < |c / (n : ℝ) - cdf μ y| := by
    have hc1 : ContinuousWithinAt (cdf μ) (Set.Ioi x) x :=
      ((cdf μ).right_continuous x).mono Set.Ioi_subset_Ici_self
    have hc2 : Tendsto (fun y => |c / (n : ℝ) - cdf μ y|) (𝓝[>] x)
        (𝓝 |c / (n : ℝ) - cdf μ x|) := (tendsto_const_nhds.sub hc1).abs
    exact hc2.eventually_const_lt h
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (h1.and h2)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (Set.mem_Ioi.1 hu)
  refine ⟨q, ?_⟩
  obtain ⟨h3, h4⟩ := hsub ⟨hq1, hq2⟩
  have e : Finset.univ.filter (fun j => ω j ≤ (q : ℝ)) = Finset.univ.filter (fun j => ω j ≤ x) :=
    Finset.filter_congr (fun j _ => h3 j)
  rw [e]
  exact h4

end DKWHelper

open DKWHelper in
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Measure.pi (fun _ : Fin n => μ)
        {ω | ∃ x : ℝ,
          ε < |((Finset.univ.filter (fun j => ω j ≤ x)).card : ℝ) / (n : ℝ) - cdf μ x|} ≤
      ENNReal.ofReal (2 * Real.exp (-(2 * (n : ℝ) * ε ^ 2))) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine prob_le_one.trans ?_
    simp only [Nat.cast_zero, mul_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hU := one_sided μ (fun q : ℚ => Set.Iic (q : ℝ)) (fun _ => measurableSet_Iic)
    (fun a b hab => Set.Iic_subset_Iic.2 (by exact_mod_cast hab)) n hn hε
  have hL := one_sided μ (fun q : ℚ => Set.Ioi (-(q : ℝ))) (fun _ => measurableSet_Ioi)
    (fun a b hab => Set.Ioi_subset_Ioi (neg_le_neg (by exact_mod_cast hab))) n hn hε
  have hsub : {ω : Fin n → ℝ | ∃ x : ℝ,
      ε < |((Finset.univ.filter (fun j => ω j ≤ x)).card : ℝ) / (n : ℝ) - cdf μ x|} ⊆
      {x | ∃ q : ℚ, (n : ℝ) * ((μ (Set.Iic (q : ℝ))).toReal + ε) < cnt (Set.Iic (q : ℝ)) x} ∪
      {x | ∃ q : ℚ, (n : ℝ) * ((μ (Set.Ioi (-(q : ℝ)))).toReal + ε) <
        cnt (Set.Ioi (-(q : ℝ))) x} := by
    rintro ω ⟨x, hx⟩
    obtain ⟨q, hq⟩ := exists_rat_close μ ω hx
    have hF : (μ (Set.Iic (q : ℝ))).toReal = cdf μ q := by
      rw [cdf_eq_real]
      try rfl
    have hcI : cnt (Set.Iic (q : ℝ)) ω =
        (Finset.univ.filter (fun j => ω j ≤ (q : ℝ))).card := by
      unfold cnt
      apply congrArg
      ext j
      simp
    rw [← hcI] at hq
    rcases lt_abs.1 hq with h | h
    · refine Or.inl ⟨q, ?_⟩
      show (n : ℝ) * ((μ (Set.Iic (q : ℝ))).toReal + ε) < (cnt (Set.Iic (q : ℝ)) ω : ℝ)
      rw [hF]
      have := (lt_sub_iff_add_lt.1 h)
      have h3 := (lt_div_iff₀ hnR).1 this
      linarith
    · refine Or.inr ⟨-q, ?_⟩
      show (n : ℝ) * ((μ (Set.Ioi (-(((-q : ℚ) : ℝ))))).toReal + ε) <
        (cnt (Set.Ioi (-(((-q : ℚ) : ℝ)))) ω : ℝ)
      have e1 : (-(((-q : ℚ) : ℝ))) = (q : ℝ) := by push_cast; ring
      rw [e1]
      have hF2 : (μ (Set.Ioi (q : ℝ))).toReal = 1 - cdf μ q := by
        rw [← hF, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
          ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
        simp
      have hcard : (cnt (Set.Iic (q : ℝ)) ω : ℝ) + (cnt (Set.Ioi (q : ℝ)) ω : ℝ) = n := by
        have e : ∀ (i1 : DecidablePred fun j => ω j ∈ Set.Ioi (q : ℝ))
            (i2 : DecidablePred fun j => ω j ∈ Set.Iic (q : ℝ)),
            @Finset.filter _ (fun j => ω j ∈ Set.Ioi (q : ℝ)) i1 Finset.univ =
              Finset.univ \ @Finset.filter _ (fun j => ω j ∈ Set.Iic (q : ℝ)) i2 Finset.univ := by
          intro i1 i2
          ext j
          simp
        have h7 : cnt (Set.Iic (q : ℝ)) ω + cnt (Set.Ioi (q : ℝ)) ω = n := by
          unfold cnt
          rw [e _ (fun _ => Classical.propDecidable _), add_comm,
            Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)]
          simp
        exact_mod_cast h7
      rw [hF2]
      have h3 : cnt (Set.Iic (q : ℝ)) ω / (n : ℝ) + ε < cdf μ q := by linarith
      have h4 : (cnt (Set.Iic (q : ℝ)) ω : ℝ) / (n : ℝ) * n = cnt (Set.Iic (q : ℝ)) ω :=
        div_mul_cancel₀ _ hnR.ne'
      have h5 := mul_lt_mul_of_pos_right h3 hnR
      rw [add_mul, h4] at h5
      have e2 : (n : ℝ) * (1 - cdf μ q + ε) = n - cdf μ q * n + ε * n := by ring
      rw [e2]
      linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans
    ((add_le_add hU hL).trans (le_of_eq ?_)))
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul (Real.exp _)]
