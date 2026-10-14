-- Prove2me | solution 1 for SennottDP.AvgASM.ac_limit_optimal_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:40:58.186973+00:00
-- url     : https://prove2.me/submissions/80818d56-f839-4249-8687-9b720b9f0dfc

import Mathlib
import Definitions.Def_SennottDP_AvgASM_Assumptions

open scoped ENNReal NNReal Topology
open Filter


namespace SennottDP.AvgASM

open Classical

set_option linter.unusedSectionVars false

variable {S : Type*} {Act : Type*} [Countable S]

theorem acl_tsum_cons {X : Type*} (F : List X → ℝ≥0∞) (t : ℕ) :
    (∑' h : List X, if h.length = t + 1 then F h else 0) =
      ∑' x : X, ∑' rest : List X, if rest.length = t then F (x :: rest) else 0 := by
  rw [← ENNReal.tsum_prod]
  have hinj : Function.Injective (fun p : X × List X => p.1 :: p.2) := by
    intro p q h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2
  rw [← hinj.tsum_eq]
  · apply tsum_congr
    intro p
    simp
  · intro h hh
    rcases h with _ | ⟨x, rest⟩
    · simp at hh
    · exact ⟨(x, rest), rfl⟩

theorem acl_tsum_len0 {X : Type*} (F : List X → ℝ≥0∞) :
    (∑' h : List X, if h.length = 0 then F h else 0) = F [] := by
  rw [tsum_eq_single []]
  · simp
  · intro b hb
    rw [if_neg]
    intro h
    exact hb (List.length_eq_zero_iff.mp h)

/-- distribution of the state at time t -/
noncomputable def acl_D {M : MDC S Act} (θ : Policy M) (i : S) (t : ℕ) (j : S) : ℝ≥0∞ :=
  ∑' rest : List (S × Act), if rest.length = t then histProb θ i rest * prevWeight M i rest j else 0

theorem acl_D_eq {M : MDC S Act} (e : StationaryPolicy M) (i : S) (t : ℕ) (j : S) :
    acl_D e.toPolicy i t j = nStep e.chain t i j := by
  induction t generalizing j with
  | zero =>
    unfold acl_D
    rw [acl_tsum_len0]
    simp [histProb, prevWeight, nStep, eq_comm]
  | succ t ih =>
    unfold acl_D
    rw [acl_tsum_cons]
    rw [ENNReal.tsum_prod']
    simp only [nStep]
    apply tsum_congr
    intro k
    rw [← ih k]
    unfold acl_D
    rw [tsum_eq_single (e.f k)]
    · rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro rest
      split_ifs
      · simp [histProb, prevWeight, StationaryPolicy.toPolicy, StationaryPolicy.chain]
      · simp
    · intro b hb
      apply ENNReal.tsum_eq_zero.mpr
      intro rest
      split_ifs
      · simp [histProb, StationaryPolicy.toPolicy, hb]
      · rfl

theorem acl_expCost_eq {M : MDC S Act} (e : StationaryPolicy M) (i : S) (t : ℕ) :
    expCost e.toPolicy i t = ∑' j, nStep e.chain t i j * e.cost j := by
  unfold expCost
  rw [acl_tsum_cons, ENNReal.tsum_prod']
  apply tsum_congr
  intro k
  rw [← acl_D_eq]
  unfold acl_D
  rw [tsum_eq_single (e.f k)]
  · rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro rest
    split_ifs
    · simp [histProb, lastCost, StationaryPolicy.toPolicy, StationaryPolicy.cost]
    · simp
  · intro b hb
    apply ENNReal.tsum_eq_zero.mpr
    intro rest
    split_ifs
    · simp [histProb, StationaryPolicy.toPolicy, hb]
    · rfl

theorem acl_horizon_eq {M : MDC S Act} (e : StationaryPolicy M) (n : ℕ) (i : S) :
    horizonCost e.toPolicy n i = ∑ t ∈ Finset.range n, ∑' j, nStep e.chain t i j * e.cost j := by
  unfold horizonCost
  simp only [acl_expCost_eq]

theorem acl_nStep_sum (P : S → S → ℝ≥0∞) (hP : ∀ i, ∑' j, P i j = 1) (t : ℕ) (i : S) :
    ∑' j, nStep P t i j = 1 := by
  induction t with
  | zero => simp [nStep]
  | succ t ih =>
    simp only [nStep]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, hP, mul_one, ih]

theorem acl_nStep_succ_apply (P : S → S → ℝ≥0∞) (t : ℕ) (i : S) (w : S → ℝ≥0∞) :
    ∑' k, nStep P (t + 1) i k * w k = ∑' j, nStep P t i j * ∑' k, P j k * w k := by
  simp only [nStep]
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr; intro j; apply tsum_congr; intro k; ring

theorem acl_iter (P : S → S → ℝ≥0∞) (hP : ∀ i, ∑' j, P i j = 1) (c w : S → ℝ≥0∞) (a : ℝ≥0∞)
    (h : ∀ i, c i + ∑' j, P i j * w j ≤ a + w i) (n : ℕ) (i : S) :
    (∑ t ∈ Finset.range n, ∑' j, nStep P t i j * c j) + ∑' j, nStep P n i j * w j
      ≤ n * a + w i := by
  induction n with
  | zero => simp [nStep]
  | succ n ih =>
    rw [Finset.sum_range_succ, acl_nStep_succ_apply, add_assoc, ← ENNReal.tsum_add]
    simp_rw [← mul_add]
    calc (∑ t ∈ Finset.range n, ∑' j, nStep P t i j * c j) +
          ∑' j, nStep P n i j * (c j + ∑' k, P j k * w k)
        ≤ (∑ t ∈ Finset.range n, ∑' j, nStep P t i j * c j) +
          ∑' j, nStep P n i j * (a + w j) := by
          exact add_le_add le_rfl (ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (h j))
      _ = (∑ t ∈ Finset.range n, ∑' j, nStep P t i j * c j) + ∑' j, nStep P n i j * w j + a := by
          simp_rw [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, acl_nStep_sum P hP]
          ring
      _ ≤ n * a + w i + a := by gcongr
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * a + w i := by push_cast; ring


theorem acl_liminf_add_le {u v : ℕ → ℝ≥0∞} {X : ℝ≥0∞} (hu : Tendsto u atTop (𝓝 X)) :
    liminf (fun r => u r + v r) atTop ≤ X + liminf v atTop := by
  by_cases hX : X = ⊤
  · simp [hX]
  have h1 : Tendsto (fun r => u r - X) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.sub hu (tendsto_const_nhds (x := X)) (Or.inr hX)
    simpa using this
  calc liminf (fun r => u r + v r) atTop
      ≤ liminf ((fun r => X + v r) + fun r => u r - X) atTop := by
        apply liminf_le_liminf (Eventually.of_forall fun r => ?_)
        simp only [Pi.add_apply]
        calc u r + v r ≤ (X + (u r - X)) + v r := by gcongr; exact le_add_tsub
          _ = _ := by ring
    _ = liminf (fun r => X + v r) atTop := ENNReal.liminf_add_of_right_tendsto_zero h1 _
    _ = X + liminf v atTop := liminf_const_add _ _ _ (by isBoundedDefault) (by isBoundedDefault)

theorem acl_fatou {T : Type*} [Countable T] (g : ℕ → T → ℝ≥0∞) :
    ∑' j, liminf (fun r => g r j) atTop ≤ liminf (fun r => ∑' j, g r j) atTop := by
  let _ : MeasurableSpace T := ⊤
  have := MeasureTheory.lintegral_liminf_le (μ := MeasureTheory.Measure.count) (f := g) (u := atTop)
    (fun n => measurable_from_top)
  rw [MeasureTheory.lintegral_count' measurable_from_top] at this
  simpa [MeasureTheory.lintegral_count' measurable_from_top] using this

theorem acl_ev_mem {M : MDC S Act} (AS : ApproxSeq M) (i : S) :
    ∀ᶠ N in atTop, AS.N₀ ≤ N ∧ i ∈ AS.SN N := by
  obtain ⟨N1, hN1, hi⟩ := AS.SN_cover i
  filter_upwards [eventually_ge_atTop N1] with N hN
  exact ⟨hN1.trans hN, AS.SN_mono N1 N hN1 hN hi⟩

theorem acl_PN_ne_top {M : MDC S Act} (AS : ApproxSeq M) {N : ℕ} (hN : AS.N₀ ≤ N) {i : S}
    (hi : i ∈ AS.SN N) {a : Act} (ha : a ∈ M.A i) (j : S) (hj : j ∈ AS.SN N) :
    AS.PN N i a j ≠ ⊤ := by
  have := AS.PN_sum N hN i hi a ha
  have h2 : AS.PN N i a j ≤ 1 := by
    rw [← this]; exact Finset.single_le_sum (f := fun j => AS.PN N i a j) (fun _ _ => zero_le) hj
  exact ne_top_of_le_ne_top ENNReal.one_ne_top h2

theorem acl_PN_toReal_sum {M : MDC S Act} (AS : ApproxSeq M) {N : ℕ} (hN : AS.N₀ ≤ N) {i : S}
    (hi : i ∈ AS.SN N) {a : Act} (ha : a ∈ M.A i) :
    ∑ j ∈ AS.SN N, (AS.PN N i a j).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun j hj => acl_PN_ne_top AS hN hi ha j hj), AS.PN_sum N hN i hi a ha]
  simp

theorem acl_stepA {M : MDC S Act} (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ)
    (e : ℕ → S → Act)
    (he : ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i))
    (hJ : ∀ N, AS.N₀ ≤ N → 0 ≤ JN N)
    (Q : S → ℝ≥0) (hQb : ∀ N, AS.N₀ ≤ N → ∀ j ∈ AS.SN N, -(Q j : ℝ) ≤ rN N j)
    (f : StationaryPolicy M)
    (hQf : ∀ i, Tendsto (fun N => ∑ j ∈ AS.SN N, AS.PN N i (f.f i) j * (Q j : ℝ≥0∞)) atTop
      (𝓝 (∑' j, M.P i (f.f i) j * (Q j : ℝ≥0∞))))
    (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) (hef : ∀ i, ∀ᶠ r in atTop, e (ψ r) i = f.f i)
    (L : ℝ≥0∞) (hL : Tendsto (fun r => ENNReal.ofReal (JN (ψ r))) atTop (𝓝 L)) (i : S) :
    (M.C i (f.f i) : ℝ≥0∞) +
        ∑' j, M.P i (f.f i) j * liminf (fun r => ENNReal.ofReal (rN (ψ r) j + Q j)) atTop + Q i
      ≤ L + ∑' j, M.P i (f.f i) j * Q j +
        liminf (fun r => ENNReal.ofReal (rN (ψ r) i + Q i)) atTop := by
  set w : S → ℝ≥0∞ := fun j => liminf (fun r => ENNReal.ofReal (rN (ψ r) j + Q j)) atTop with hw
  have hterm : ∀ (p : ℝ≥0∞) (x : ℝ), p ≠ ⊤ → ENNReal.ofReal (p.toReal * x) = p * ENNReal.ofReal x := by
    intro p x hp
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hp]
  let g : ℕ → S → ℝ≥0∞ := fun r j => if j ∈ AS.SN (ψ r) then
    AS.PN (ψ r) i (f.f i) j * ENNReal.ofReal (rN (ψ r) j + Q j) else 0
  have hev := (hψ.eventually (acl_ev_mem AS i)).and (hef i)
  -- the identity
  have hid : ∀ᶠ r in atTop,
      (ENNReal.ofReal (JN (ψ r)) + ∑ j ∈ AS.SN (ψ r), AS.PN (ψ r) i (f.f i) j * (Q j : ℝ≥0∞)) +
        ENNReal.ofReal (rN (ψ r) i + Q i)
      = ((M.C i (f.f i) : ℝ≥0∞) + Q i) + ∑' j, g r j := by
    filter_upwards [hev] with r hr
    obtain ⟨⟨hN, hi⟩, hfi⟩ := hr
    set N := ψ r
    have hreal := he N hN i hi
    rw [hfi] at hreal
    unfold ApproxSeq.acoeTerm at hreal
    have hsum1 := acl_PN_toReal_sum AS hN hi (f.mem i)
    have hgs : ∑' j, g r j = ∑ j ∈ AS.SN N,
        AS.PN N i (f.f i) j * ENNReal.ofReal (rN N j + Q j) :=
      (tsum_eq_sum (fun j hj => if_neg hj)).trans (Finset.sum_congr rfl fun j hj => if_pos hj)
    rw [hgs]
    have hnn : ∀ j ∈ AS.SN N, 0 ≤ rN N j + Q j := fun j hj => by
      have := hQb N hN j hj; linarith
    have e1 : ∑ j ∈ AS.SN N, AS.PN N i (f.f i) j * (Q j : ℝ≥0∞) =
        ENNReal.ofReal (∑ j ∈ AS.SN N, (AS.PN N i (f.f i) j).toReal * Q j) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg ENNReal.toReal_nonneg (by positivity))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hterm _ _ (acl_PN_ne_top AS hN hi (f.mem i) j hj)]
      simp
    have e2 : ∑ j ∈ AS.SN N, AS.PN N i (f.f i) j * ENNReal.ofReal (rN N j + Q j) =
        ENNReal.ofReal (∑ j ∈ AS.SN N, (AS.PN N i (f.f i) j).toReal * (rN N j + Q j)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => mul_nonneg ENNReal.toReal_nonneg (hnn j hj))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hterm _ _ (acl_PN_ne_top AS hN hi (f.mem i) j hj)]
    have hreal2 : JN N + ∑ j ∈ AS.SN N, (AS.PN N i (f.f i) j).toReal * Q j + (rN N i + Q i)
        = ((M.C i (f.f i) : ℝ) + Q i) +
          ∑ j ∈ AS.SN N, (AS.PN N i (f.f i) j).toReal * (rN N j + Q j) := by
      simp only [mul_add, Finset.sum_add_distrib]
      linarith
    have hJN := hJ N hN
    have hQs : 0 ≤ ∑ j ∈ AS.SN N, (AS.PN N i (f.f i) j).toReal * Q j :=
      Finset.sum_nonneg fun j _ => mul_nonneg ENNReal.toReal_nonneg (by positivity)
    have hS2 : 0 ≤ ∑ j ∈ AS.SN N, (AS.PN N i (f.f i) j).toReal * (rN N j + Q j) :=
      Finset.sum_nonneg fun j hj => mul_nonneg ENNReal.toReal_nonneg (hnn j hj)
    rw [e1, e2, ← ENNReal.ofReal_add hJN hQs, ← ENNReal.ofReal_add (by positivity) (hnn i hi),
      hreal2, ENNReal.ofReal_add (by positivity) hS2, ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  have hx : Tendsto (fun r => ENNReal.ofReal (JN (ψ r)) +
      ∑ j ∈ AS.SN (ψ r), AS.PN (ψ r) i (f.f i) j * (Q j : ℝ≥0∞)) atTop
      (𝓝 (L + ∑' j, M.P i (f.f i) j * Q j)) := hL.add ((hQf i).comp hψ)
  have hup := acl_liminf_add_le (v := fun r => ENNReal.ofReal (rN (ψ r) i + Q i)) hx
  rw [liminf_congr hid] at hup
  rw [liminf_const_add _ _ _ (by isBoundedDefault) (by isBoundedDefault)] at hup
  have hfat := acl_fatou g
  have hpt : ∀ j, M.P i (f.f i) j * w j ≤ liminf (fun r => g r j) atTop := by
    intro j
    have hgj : ∀ᶠ r in atTop, g r j = AS.PN (ψ r) i (f.f i) j * ENNReal.ofReal (rN (ψ r) j + Q j) := by
      filter_upwards [hψ.eventually (acl_ev_mem AS j)] with r hr
      simp [g, hr.2]
    rw [liminf_congr hgj]
    have hP := ((AS.PN_tendsto i (f.f i) (f.mem i) j).comp hψ).liminf_eq
    calc M.P i (f.f i) j * w j = liminf (fun r => AS.PN (ψ r) i (f.f i) j) atTop * w j := by
          rw [← hP]; rfl
      _ ≤ _ := ENNReal.le_liminf_mul
  have hsum : ∑' j, M.P i (f.f i) j * w j ≤ liminf (fun r => ∑' j, g r j) atTop :=
    (ENNReal.tsum_le_tsum hpt).trans hfat
  calc (M.C i (f.f i) : ℝ≥0∞) + ∑' j, M.P i (f.f i) j * w j + Q i
      = ((M.C i (f.f i) : ℝ≥0∞) + Q i) + ∑' j, M.P i (f.f i) j * w j := by ring
    _ ≤ ((M.C i (f.f i) : ℝ≥0∞) + Q i) + liminf (fun r => ∑' j, g r j) atTop := by gcongr
    _ ≤ _ := hup

theorem acl_avg_le {M : MDC S Act} (f : StationaryPolicy M) (w : S → ℝ≥0∞) (hw : ∀ i, w i < ⊤)
    (a : ℝ≥0∞) (h : ∀ i, f.cost i + ∑' j, f.chain i j * w j ≤ a + w i) (i : S) :
    avgCost f.toPolicy i ≤ a := by
  have hP : ∀ i, ∑' j, f.chain i j = 1 := fun i => M.P_sum i (f.f i) (f.mem i)
  have hb : ∀ n : ℕ, horizonCost f.toPolicy n i ≤ n * a + w i := by
    intro n
    rw [acl_horizon_eq]
    exact le_self_add.trans (acl_iter f.chain hP f.cost w a h n i)
  unfold avgCost
  have ht : Tendsto (fun n : ℕ => a + w i * (n : ℝ≥0∞)⁻¹) atTop (𝓝 a) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr (hw i).ne) (a := w i)
    simpa using tendsto_const_nhds.add this
  refine (limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)).trans_eq ht.limsup_eq
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  calc horizonCost f.toPolicy n i / n ≤ (n * a + w i) / n := by gcongr; exact hb n
    _ = a + w i * (n : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.add_div, mul_comm, ENNReal.mul_div_cancel_right hn0 (ENNReal.natCast_ne_top n),
        div_eq_mul_inv]


theorem acl_J_nonneg {M : MDC S Act} (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ)
    (hAC1 : AS.AC1 JN rN) : ∀ N, AS.N₀ ≤ N → 0 ≤ JN N := by
  intro N hN
  obtain ⟨i, hi, hmin⟩ := (AS.SN N).exists_min_image (rN N) (AS.SN_nonempty N hN)
  have h := hAC1 N hN i hi
  have h2 : rN N i ≤ (M.A i).inf' (M.A_nonempty i) (fun a => AS.acoeTerm rN N i a) := by
    apply Finset.le_inf'
    intro a ha
    unfold ApproxSeq.acoeTerm
    have h3 : ∑ j ∈ AS.SN N, (AS.PN N i a j).toReal * rN N i ≤
        ∑ j ∈ AS.SN N, (AS.PN N i a j).toReal * rN N j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hmin j hj) ENNReal.toReal_nonneg
    rw [← Finset.sum_mul, acl_PN_toReal_sum AS hN hi ha, one_mul] at h3
    have : (0 : ℝ) ≤ (M.C i a : ℝ) := NNReal.coe_nonneg _
    linarith
  linarith

theorem acl_L_le {M : MDC S Act} (AS : ApproxSeq M) (JN : ℕ → ℝ)
    (hJ : ∀ N, AS.N₀ ≤ N → 0 ≤ JN N) (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) (L : ℝ≥0∞)
    (hL : Tendsto (fun r => ENNReal.ofReal (JN (ψ r))) atTop (𝓝 L)) :
    (L : EReal) ≤ limsup (fun N => (JN N : EReal)) atTop := by
  have h1 : Tendsto (fun r => (JN (ψ r) : EReal)) atTop (𝓝 (L : EReal)) := by
    have := (continuous_coe_ennreal_ereal.tendsto L).comp hL
    refine this.congr' ?_
    filter_upwards [hψ.eventually (eventually_ge_atTop AS.N₀)] with r hr
    simp [EReal.coe_ennreal_ofReal, max_eq_left (hJ _ hr)]
  rw [← h1.limsup_eq]
  show limsup ((fun N => (JN N : EReal)) ∘ ψ) atTop ≤ _
  rw [limsup_comp]
  exact limsup_le_limsup_of_le hψ

theorem acl_subseq {M : MDC S Act} (x : ℕ → S → Act) (hx : ∀ N i, x N i ∈ M.A i)
    (y : ℕ → ℝ≥0∞) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (f : StationaryPolicy M) (L : ℝ≥0∞),
      Tendsto (fun r => y (φ r)) atTop (𝓝 L) ∧ ∀ i, ∀ᶠ r in atTop, x (φ r) i = f.f i := by
  let _ : ∀ i, TopologicalSpace (M.A i) := fun _ => ⊥
  have : ∀ i, DiscreteTopology (M.A i) := fun _ => ⟨rfl⟩
  let z : ℕ → (∀ i, M.A i) × ℝ≥0∞ := fun N => (fun i => ⟨x N i, hx N i⟩, y N)
  obtain ⟨⟨a, L⟩, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq z
  refine ⟨φ, hφ, ⟨fun i => (a i).1, fun i => (a i).2⟩, L, ?_, ?_⟩
  · exact (continuous_snd.tendsto _).comp hlim
  · intro i
    have h1 : Tendsto (fun r => (z (φ r)).1 i) atTop (𝓝 (a i)) :=
      ((continuous_apply i).tendsto a).comp ((continuous_fst.tendsto _).comp hlim)
    rw [nhds_discrete, tendsto_pure] at h1
    filter_upwards [h1] with r hr
    exact congrArg Subtype.val hr

theorem acl_w_lt_top {M : MDC S Act} (AS : ApproxSeq M) (rN : ℕ → S → ℝ) (hAC2 : AS.AC2 rN)
    (Q : S → ℝ≥0) (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop) (i : S) :
    liminf (fun r => ENNReal.ofReal (rN (ψ r) i + Q i)) atTop < ⊤ := by
  obtain ⟨B, hB1, -⟩ := EReal.lt_iff_exists_real_btwn.mp (hAC2 i)
  have hev : ∀ᶠ N in atTop, (rN N i : EReal) < B := eventually_lt_of_limsup_lt hB1
  calc liminf (fun r => ENNReal.ofReal (rN (ψ r) i + Q i)) atTop
      ≤ liminf (fun _ : ℕ => ENNReal.ofReal (B + Q i)) atTop := by
        refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
        filter_upwards [hψ.eventually hev] with r hr
        apply ENNReal.ofReal_le_ofReal
        have := EReal.coe_lt_coe_iff.mp hr
        linarith
    _ = ENNReal.ofReal (B + Q i) := liminf_const _
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem acl_final {M : MDC S Act} (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ)
    (hAC1 : AS.AC1 JN rN) (hAC4 : AS.AC4 JN)
    (hKEY : ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ (f : StationaryPolicy M) (ψ : ℕ → ℕ), Tendsto ψ atTop atTop →
      (∀ i, ∀ᶠ r in atTop, e (ψ r) i = f.f i) →
      ∀ L, Tendsto (fun r => ENNReal.ofReal (JN (ψ r))) atTop (𝓝 L) →
      ∀ i, avgCost f.toPolicy i ≤ L) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, ((avgValue M i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ f : StationaryPolicy M, AS.IsLimitPoint e f → IsAverageOptimal f.toPolicy := by
  have hJ := acl_J_nonneg AS JN rN hAC1
  have hcap : ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ (f : StationaryPolicy M) (ψ : ℕ → ℕ), Tendsto ψ atTop atTop →
      (∀ i, ∀ᶠ r in atTop, e (ψ r) i = f.f i) →
      ∀ L, Tendsto (fun r => ENNReal.ofReal (JN (ψ r))) atTop (𝓝 L) →
      ∀ i, avgCost f.toPolicy i = avgValue M i ∧ avgValue M i = L := by
    intro e he hmin f ψ hψ hef L hL i
    have h1 := hKEY e he hmin f ψ hψ hef L hL i
    have h2 : avgValue M i ≤ avgCost f.toPolicy i := iInf_le _ _
    have h3 : (L : EReal) ≤ avgValue M i := (acl_L_le AS JN hJ ψ hψ L hL).trans (hAC4.2 i)
    have h3' : L ≤ avgValue M i := EReal.coe_ennreal_le_coe_ennreal_iff.mp h3
    exact ⟨le_antisymm (h1.trans h3') h2, le_antisymm (h2.trans h1) h3'⟩
  have hex : ∀ N i, ∃ a ∈ M.A i, (AS.N₀ ≤ N ∧ i ∈ AS.SN N) →
      JN N + rN N i = AS.acoeTerm rN N i a := by
    intro N i
    by_cases h : AS.N₀ ≤ N ∧ i ∈ AS.SN N
    · obtain ⟨a, ha, hmin⟩ := (M.A i).exists_min_image (AS.acoeTerm rN N i) (M.A_nonempty i)
      refine ⟨a, ha, fun _ => ?_⟩
      rw [hAC1 N h.1 i h.2]
      exact le_antisymm (Finset.inf'_le _ ha) (Finset.le_inf' _ _ hmin)
    · obtain ⟨a, ha⟩ := M.A_nonempty i
      exact ⟨a, ha, fun h' => absurd h' h⟩
  choose e0 he0mem he0 using hex
  have he0s : AS.IsStationarySeq e0 := fun N _ i _ => he0mem N i
  have he0r : ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e0 N i) :=
    fun N hN i hi => he0 N i ⟨hN, hi⟩
  obtain ⟨i0, -⟩ := AS.SN_nonempty AS.N₀ le_rfl
  obtain ⟨φ, hφ, f, L, hL, hef⟩ := acl_subseq e0 he0mem (fun N => ENNReal.ofReal (JN N))
  have hcapL := hcap e0 he0s he0r f φ hφ.tendsto_atTop hef L hL
  have hconst : ∀ i, avgValue M i = avgValue M i0 := fun i =>
    (hcapL i).2.trans (hcapL i0).2.symm
  have hconv : Tendsto (fun N => ENNReal.ofReal (JN N)) atTop (𝓝 (avgValue M i0)) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨φ', hφ', f', L', hL', hef'⟩ := acl_subseq (fun N => e0 (ns N)) (fun N => he0mem (ns N))
      (fun N => ENNReal.ofReal (JN (ns N)))
    refine ⟨φ', ?_⟩
    have := (hcap e0 he0s he0r f' (fun r => ns (φ' r)) (hns.comp hφ'.tendsto_atTop) hef' L' hL' i0).2
    rw [this]
    exact hL'
  have hVtop : avgValue M i0 ≠ ⊤ := by
    have h3 := acl_L_le AS JN hJ φ hφ.tendsto_atTop L hL
    rw [← (hcapL i0).2] at h3
    intro htop
    rw [htop] at h3
    have := lt_of_le_of_lt h3 hAC4.1
    simp at this
  refine ⟨⟨(avgValue M i0).toReal, ?_, ?_⟩, ?_⟩
  · have := (ENNReal.tendsto_toReal hVtop).comp hconv
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop AS.N₀] with N hN
    simp [ENNReal.toReal_ofReal (hJ N hN)]
  · intro i
    rw [hconst i, EReal.coe_ennreal_toReal hVtop]
  · rintro e he hmin f ⟨φ, hφ, hef⟩ i
    obtain ⟨L, ms, hms, hL⟩ := CompactSpace.tendsto_subseq (fun N => ENNReal.ofReal (JN (φ N)))
    exact (hcap e he hmin f (fun n => φ (ms n)) (hφ.tendsto_atTop.comp hms.tendsto_atTop)
      (fun i => hms.tendsto_atTop.eventually (hef i)) L hL i).1

theorem acl_key_AC {M : MDC S Act} (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ)
    (hAC1 : AS.AC1 JN rN) (hAC2 : AS.AC2 rN) (q : ℝ) (hq : 0 ≤ q)
    (hb : ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, -q ≤ rN N i) :
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ (f : StationaryPolicy M) (ψ : ℕ → ℕ), Tendsto ψ atTop atTop →
      (∀ i, ∀ᶠ r in atTop, e (ψ r) i = f.f i) →
      ∀ L, Tendsto (fun r => ENNReal.ofReal (JN (ψ r))) atTop (𝓝 L) →
      ∀ i, avgCost f.toPolicy i ≤ L := by
  intro e _ hmin f ψ hψ hef L hL i
  have hJ := acl_J_nonneg AS JN rN hAC1
  let Q : S → ℝ≥0 := fun _ => q.toNNReal
  have hQq : ∀ j, (Q j : ℝ) = q := fun j => Real.coe_toNNReal _ hq
  have hQb : ∀ N, AS.N₀ ≤ N → ∀ j ∈ AS.SN N, -(Q j : ℝ) ≤ rN N j := by
    intro N hN j hj; rw [hQq j]; exact hb N hN j hj
  have hPQ : ∀ i, ∑' j, M.P i (f.f i) j * (Q i : ℝ≥0∞) = Q i := by
    intro i
    rw [ENNReal.tsum_mul_right, M.P_sum i (f.f i) (f.mem i), one_mul]
  have hQf : ∀ i, Tendsto (fun N => ∑ j ∈ AS.SN N, AS.PN N i (f.f i) j * (Q j : ℝ≥0∞)) atTop
      (𝓝 (∑' j, M.P i (f.f i) j * (Q j : ℝ≥0∞))) := by
    intro i
    have : ∑' j, M.P i (f.f i) j * (Q j : ℝ≥0∞) = Q i := hPQ i
    rw [this]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [acl_ev_mem AS i] with N hN
    show (Q i : ℝ≥0∞) = ∑ j ∈ AS.SN N, AS.PN N i (f.f i) j * (Q i : ℝ≥0∞)
    rw [← Finset.sum_mul, AS.PN_sum N hN.1 i hN.2 (f.f i) (f.mem i), one_mul]
  have hA := acl_stepA AS JN rN e hmin hJ Q hQb f hQf ψ hψ hef L hL
  refine acl_avg_le f _ (fun j => acl_w_lt_top AS rN hAC2 Q ψ hψ j) L ?_ i
  intro k
  have := hA k
  have hPQk : ∑' j, M.P k (f.f k) j * (Q j : ℝ≥0∞) = Q k := hPQ k
  rw [hPQk] at this
  have h2 : (M.C k (f.f k) : ℝ≥0∞) +
      ∑' j, M.P k (f.f k) j * liminf (fun r => ENNReal.ofReal (rN (ψ r) j + Q j)) atTop + Q k ≤
      (L + liminf (fun r => ENNReal.ofReal (rN (ψ r) k + Q k)) atTop) + Q k := by
    calc _ ≤ _ := this
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_right ENNReal.coe_ne_top).mp h2

theorem acl_core {M : MDC S Act}
    (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : AS.AC JN rN)
    (hQ : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, -Q ≤ rN N i) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, ((avgValue M i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ f : StationaryPolicy M, AS.IsLimitPoint e f → IsAverageOptimal f.toPolicy := by
  obtain ⟨q, hq, hb⟩ := hQ
  exact acl_final AS JN rN hAC.1 hAC.2.2.2 (acl_key_AC AS JN rN hAC.1 hAC.2.1 q hq hb)

end SennottDP.AvgASM

open SennottDP.AvgASM


theorem solution {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act}
    (AS : ApproxSeq M) (JN : ℕ → ℝ) (rN : ℕ → S → ℝ) (hAC : AS.AC JN rN)
    (hQ : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, -Q ≤ rN N i) :
    (∃ Jstar : ℝ, Tendsto JN atTop (𝓝 Jstar) ∧
        ∀ i, ((avgValue M i : ℝ≥0∞) : EReal) = (Jstar : EReal)) ∧
    ∀ e : ℕ → S → Act, AS.IsStationarySeq e →
      (∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, JN N + rN N i = AS.acoeTerm rN N i (e N i)) →
      ∀ f : StationaryPolicy M, AS.IsLimitPoint e f → IsAverageOptimal f.toPolicy := by
  exact acl_core AS JN rN hAC hQ
