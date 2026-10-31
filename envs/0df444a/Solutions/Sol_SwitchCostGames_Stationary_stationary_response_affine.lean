-- Prove2me | solution 1 for SwitchCostGames.Stationary.stationary_response_affine
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:29:59.2132+00:00
-- url     : https://prove2.me/submissions/4fccbec3-3e1b-4667-b344-6e54ad0d499e

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model

open SwitchCostGames.Stationary

namespace SCGResp

open Filter Topology Finset

theorem pow_apply_of_ker_range {V : Type*} [AddCommGroup V] [Module ℝ V] (L : V →ₗ[ℝ] V)
    (x w : V) (hx : L x = x) (hw : L w - w = x) :
    ∀ t : ℕ, (L ^ t) w = w + (t : ℝ) • x
  | 0 => by simp
  | t + 1 => by
    rw [pow_succ', Module.End.mul_apply, pow_apply_of_ker_range L x w hx hw t, map_add,
      map_smul, hx]
    have : L w = w + x := by rw [← hw]; abel
    rw [this]; push_cast; rw [add_smul, one_smul]; abel

/-- Cesàro averages of a power-bounded operator on a finite-dimensional space converge. -/
theorem cesaro_of_bounded {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : V →ₗ[ℝ] V) (hb : ∀ w : V, ∃ C, ∀ t : ℕ, ‖(L ^ t) w‖ ≤ C)
    (v : V) : ∃ π : V, Tendsto (fun T : ℕ => (T : ℝ)⁻¹ • ∑ t ∈ range T, (L ^ t) v)
      atTop (𝓝 π) := by
  set K := LinearMap.ker (L - 1)
  set R := LinearMap.range (L - 1)
  have hdisj : K ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxK, ⟨w, hw⟩⟩ := hx
    have hLx : L x = x := by
      have := LinearMap.mem_ker.1 hxK
      simp only [LinearMap.sub_apply, Module.End.one_apply] at this
      exact sub_eq_zero.1 this
    have hw' : L w - w = x := by simpa using hw
    have hpow := pow_apply_of_ker_range L x w hLx hw'
    obtain ⟨C, hC⟩ := hb w
    rw [Submodule.mem_bot]
    by_contra hne
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 hne
    obtain ⟨t, ht⟩ := exists_nat_gt ((C + ‖w‖) / ‖x‖)
    have h1 := hC t
    rw [hpow t] at h1
    have h2 : (t : ℝ) * ‖x‖ ≤ ‖w + (t : ℝ) • x‖ + ‖w‖ := by
      have := norm_sub_le (w + (t : ℝ) • x) w
      simp only [add_sub_cancel_left, norm_smul, Real.norm_natCast] at this
      linarith
    have h3 : C + ‖w‖ < t * ‖x‖ := by
      rwa [div_lt_iff₀ hpos] at ht
    linarith
  have hsup : K ⊔ R = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq K R
    have h2 : Module.finrank ℝ R + Module.finrank ℝ K = Module.finrank ℝ V :=
      LinearMap.finrank_range_add_finrank_ker (L - 1)
    rw [hdisj, finrank_bot] at h1
    omega
  have hv : v ∈ K ⊔ R := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨k, hk, r, ⟨w, rfl⟩, hkr⟩ := Submodule.mem_sup.1 hv
  have hLk : L k = k := by
    have := LinearMap.mem_ker.1 hk
    simp only [LinearMap.sub_apply, Module.End.one_apply] at this
    exact sub_eq_zero.1 this
  have hLk_pow : ∀ t : ℕ, (L ^ t) k = k := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', Module.End.mul_apply, ih, hLk]
  have hsum : ∀ T : ℕ, ∑ t ∈ range T, (L ^ t) v = (T : ℝ) • k + ((L ^ T) w - w) := by
    intro T
    rw [← hkr]
    simp only [map_add, Finset.sum_add_distrib, hLk_pow, Finset.sum_const, card_range,
      Nat.cast_smul_eq_nsmul]
    congr 1
    have : ∀ t : ℕ, (L ^ t) ((L - 1) w) = (L ^ (t + 1)) w - (L ^ t) w := by
      intro t
      simp only [map_sub, LinearMap.sub_apply, Module.End.one_apply, pow_succ,
        Module.End.mul_apply]
    simp only [this]
    rw [Finset.sum_range_sub (fun t => (L ^ t) w) T]
    simp
  refine ⟨k, ?_⟩
  obtain ⟨C, hC⟩ := hb w
  have hlim : Tendsto (fun T : ℕ => k + (T : ℝ)⁻¹ • ((L ^ T) w - w)) atTop (𝓝 k) := by
    have h0 : Tendsto (fun T : ℕ => (T : ℝ)⁻¹ • ((L ^ T) w - w)) atTop (𝓝 0) := by
      apply squeeze_zero_norm (a := fun T : ℕ => (C + ‖w‖) * (T : ℝ)⁻¹)
      · intro T
        rw [norm_smul, norm_inv, Real.norm_natCast, mul_comm]
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 (Nat.cast_nonneg _))
        exact (norm_sub_le _ _).trans (by linarith [hC T])
      · simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
          (C + ‖w‖)
    simpa using (tendsto_const_nhds (x := k)).add h0
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [hsum T, smul_add, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (by omega : T ≠ 0)),
    one_smul]

end SCGResp

namespace SCGAux

theorem take_snoc {m n T : ℕ} (h : History m n T) (x : Fin m × Fin n) (s : ℕ) (hs : s ≤ T) :
    History.take (Fin.snoc h x : History m n (T + 1)) s (hs.trans T.le_succ) =
      History.take h s hs := by
  funext r
  have hr : (r : ℕ) < T := lt_of_lt_of_le r.isLt hs
  simp [History.take, Fin.snoc, hr, Fin.castLT]
  rfl

theorem take_self {m n T : ℕ} (h : History m n T) : History.take h T le_rfl = h := by
  funext r
  simp [History.take]

theorem histProb_snoc {m n T : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n) (h : History m n T)
    (x : Fin m × Fin n) :
    histProb σ τ (Fin.snoc h x : History m n (T + 1)) =
      histProb σ τ h * (σ.act T h x.1 * τ.act T h x.2) := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun s _ => ?_)
    have e1 : (Fin.snoc h x : History m n (T + 1)) (Fin.castSucc s) = h s := Fin.snoc_castSucc ..
    have e2 := take_snoc h x s s.isLt.le
    simp only [Fin.val_castSucc]
    rw [e1, e2]
  · have e1 : (Fin.snoc h x : History m n (T + 1)) (Fin.last T) = x := Fin.snoc_last ..
    have e2 := take_snoc h x T le_rfl
    simp only [Fin.val_last]
    rw [e1, e2, take_self]

theorem histProb_nonneg {m n T : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n)
    (h : History m n T) : 0 ≤ histProb σ τ h := by
  unfold histProb
  exact Finset.prod_nonneg (fun s _ =>
    mul_nonneg ((σ.act_mem _ _).1 _) ((τ.act_mem _ _).1 _))

theorem sum_histProb {m n : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n) :
    ∀ T : ℕ, ∑ h : History m n T, histProb σ τ h = 1
  | 0 => by simp [histProb]
  | T + 1 => by
    rw [← (Fin.snocEquiv (fun _ : Fin (T + 1) => Fin m × Fin n)).sum_comp]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have key : ∀ h : History m n T,
        ∑ x : Fin m × Fin n, histProb σ τ (Fin.snoc h x : History m n (T + 1)) =
          histProb σ τ h := by
      intro h
      simp only [histProb_snoc]
      rw [← Finset.mul_sum, Fintype.sum_prod_type]
      have : ∑ i : Fin m, ∑ j : Fin n, σ.act T h i * τ.act T h j = 1 := by
        rw [← Finset.sum_mul_sum, (σ.act_mem _ _).2, (τ.act_mem _ _).2, one_mul]
      simp only at this ⊢
      rw [this, mul_one]
    calc ∑ h : History m n T, ∑ x : Fin m × Fin n,
          histProb σ τ (Fin.snoc h x : History m n (T + 1))
        = ∑ h : History m n T, histProb σ τ h := Finset.sum_congr rfl (fun h _ => key h)
      _ = 1 := sum_histProb σ τ T

theorem prevAction_of_const {m n : ℕ} [NeZero n] (j : Fin n) :
    ∀ {t : ℕ} (h : History m n t), (∀ r, (h r).2 = j) → t ≠ 0 → prevAction h = j
  | 0, _, _, ht => absurd rfl ht
  | t + 1, h, hj, _ => hj (Fin.last t)

end SCGAux

namespace SCGAux

open Finset

theorem sum_snoc_histProb {m n T : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n)
    (h : History m n T) :
    ∑ x : Fin m × Fin n, histProb σ τ h * (σ.act T h x.1 * τ.act T h x.2) = histProb σ τ h := by
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  have : ∑ i : Fin m, ∑ j : Fin n, σ.act T h i * τ.act T h j = 1 := by
    rw [← Finset.sum_mul_sum, (σ.act_mem _ _).2, (τ.act_mem _ _).2, one_mul]
  simp only at this ⊢
  rw [this, mul_one]

/-- Marginalization: summing a function of the first `s` stages against the law of histories of
length `T ≥ s` is the same as summing it against the law of histories of length `s`. -/
theorem snocEquiv_eq {m n t : ℕ} (x : Fin m × Fin n) (h : History m n t) :
    (Fin.snocEquiv (fun _ : Fin (t + 1) => Fin m × Fin n)) (x, h) =
      (Fin.snoc h x : History m n (t + 1)) := rfl

theorem marginal {m n : ℕ} (σ : Strategy1 m n) (τ : Strategy2 m n) :
    ∀ (T s : ℕ) (hs : s ≤ T) (F : History m n s → ℝ),
      ∑ h : History m n T, histProb σ τ h * F (h.take s hs) =
        ∑ h' : History m n s, histProb σ τ h' * F h'
  | 0, s, hs, F => by
    obtain rfl : s = 0 := by omega
    simp only [take_self]
  | T + 1, s, hs, F => by
    rcases eq_or_lt_of_le hs with rfl | hlt
    · simp only [take_self]
    · have hsT : s ≤ T := Nat.lt_succ_iff.1 hlt
      rw [← (Fin.snocEquiv (fun _ : Fin (T + 1) => Fin m × Fin n)).sum_comp,
        Fintype.sum_prod_type, Finset.sum_comm, ← marginal σ τ T s hsT F]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      have e : ∀ x : Fin m × Fin n,
          History.take (Fin.snoc h x : History m n (T + 1)) s hs = History.take h s hsT :=
        fun x => take_snoc h x s hsT
      simp only [snocEquiv_eq, e, histProb_snoc]
      rw [← Finset.sum_mul, sum_snoc_histProb]

end SCGAux

open SCGAux SCGResp Finset Filter Topology

/-- The stage-`t` reward, read off a history of length `t + 1`. -/
noncomputable def SCGstageR {m n : ℕ} [NeZero n] (G : Game m n) (c : ℝ) (t : ℕ)
    (h : History m n (t + 1)) : ℝ :=
  G.A (h (Fin.last t)).1 (h (Fin.last t)).2 +
    c * G.S (prevAction (h.take t (Nat.le_succ t))) (h (Fin.last t)).2

theorem SCG_expectedTotal_eq {m n : ℕ} [NeZero n] (G : Game m n) (c : ℝ) (σ : Strategy1 m n)
    (τ : Strategy2 m n) (T : ℕ) :
    expectedTotal G c σ τ T = ∑ t ∈ range T,
      ∑ h : History m n (t + 1), histProb σ τ h * SCGstageR G c t h := by
  unfold expectedTotal
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Fin.sum_univ_eq_sum_range (fun t => ∑ h : History m n (t + 1),
    histProb σ τ h * SCGstageR G c t h) T]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← marginal σ τ T (s + 1) s.isLt (SCGstageR G c s)]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  congr 1

theorem SCG_stage_formula {m n : ℕ} [NeZero n] (G : Game m n) (c : ℝ) (σ : Strategy1 m n)
    (τ : Strategy2 m n) (y : Fin n → Fin n → ℝ)
    (hy : ∀ t (h : History m n t), τ.act t h = y (prevAction h)) (t : ℕ) :
    ∑ h : History m n (t + 1), histProb σ τ h * SCGstageR G c t h =
      ∑ h : History m n t, histProb σ τ h * ∑ i, σ.act t h i *
        ∑ j, y (prevAction h) j * (G.A i j + c * G.S (prevAction h) j) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (t + 1) => Fin m × Fin n)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  have e1 : ∀ x : Fin m × Fin n, (Fin.snoc h x : History m n (t + 1)) (Fin.last t) = x :=
    fun x => Fin.snoc_last ..
  have e2 : ∀ x : Fin m × Fin n,
      History.take (Fin.snoc h x : History m n (t + 1)) t (Nat.le_succ t) = h := by
    intro x
    rw [take_snoc h x t le_rfl, take_self]
  simp only [snocEquiv_eq, histProb_snoc, SCGstageR, e1, e2, hy]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem SCG_occupation {m n : ℕ} [NeZero n] (σ : Strategy1 m n) (τ : Strategy2 m n)
    (y : Fin n → Fin n → ℝ) (hy : ∀ t (h : History m n t), τ.act t h = y (prevAction h))
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hL : ∀ μ j, L μ j = ∑ k, μ k * y k j) :
    ∀ (t : ℕ) (φ : Fin n → ℝ), ∑ h : History m n t, histProb σ τ h * φ (prevAction h) =
      ∑ k, (L ^ t) (fun k => if k = 0 then 1 else 0) k * φ k
  | 0, φ => by
    simp [histProb, prevAction]
  | t + 1, φ => by
    rw [← (Fin.snocEquiv (fun _ : Fin (t + 1) => Fin m × Fin n)).sum_comp,
      Fintype.sum_prod_type, Finset.sum_comm]
    have e1 : ∀ (h : History m n t) (x : Fin m × Fin n),
        prevAction (Fin.snoc h x : History m n (t + 1)) = x.2 := by
      intro h x
      show ((Fin.snoc h x : History m n (t + 1)) (Fin.last t)).2 = x.2
      rw [Fin.snoc_last]
    have inner : ∀ h : History m n t,
        ∑ x : Fin m × Fin n, histProb σ τ (Fin.snoc h x : History m n (t + 1)) *
          φ (prevAction (Fin.snoc h x : History m n (t + 1))) =
        histProb σ τ h * ∑ j, y (prevAction h) j * φ j := by
      intro h
      simp only [e1, histProb_snoc, hy]
      rw [Fintype.sum_prod_type]
      have hs : ∑ i : Fin m, σ.act t h i = 1 := (σ.act_mem _ _).2
      calc ∑ i : Fin m, ∑ j : Fin n, histProb σ τ h *
              (σ.act t h i * y (prevAction h) j) * φ j
          = ∑ i : Fin m, σ.act t h i * (histProb σ τ h * ∑ j, y (prevAction h) j * φ j) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            ring
        _ = histProb σ τ h * ∑ j, y (prevAction h) j * φ j := by
            rw [← Finset.sum_mul, hs, one_mul]
    simp only [snocEquiv_eq]
    rw [Finset.sum_congr rfl (fun h _ => inner h)]
    rw [SCG_occupation σ τ y hy L hL t (fun k => ∑ j, y k j * φ j)]
    rw [pow_succ', Module.End.mul_apply]
    simp only [hL, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring

theorem solution {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n)
    (τ : Strategy2 m n) (hτ : IsStationary2 τ) :
    ∃ α β : ℝ, ∃ σ : Strategy1 m n, IsStationary1 σ ∧ ∀ c : ℝ, 0 ≤ c →
      payoff G c σ τ = α + β * c ∧ ∀ σ' : Strategy1 m n, payoff G c σ' τ ≤ α + β * c := by
  classical
  obtain ⟨y, hy⟩ := hτ
  have hymix : ∀ k, BlottoLP.Flow.IsMixed (y k) := by
    intro k
    have h1 := τ.act_mem 1 (fun _ => ((0 : Fin m), k))
    rw [hy] at h1
    exact h1
  -- one-step payoffs
  let rowval : Fin n → Fin m → ℝ := fun k i => ∑ j, y k j * G.A i j
  let ρ : Fin n → ℝ := fun k => univ.sup' univ_nonempty (rowval k)
  have hf : ∀ k, ∃ i, rowval k i = ρ k := by
    intro k
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin m)) (rowval k)
    exact ⟨i, hi.symm⟩
  let f : Fin n → Fin m := fun k => Classical.choose (hf k)
  have hfk : ∀ k, rowval k (f k) = ρ k := fun k => Classical.choose_spec (hf k)
  let sk : Fin n → ℝ := fun k => ∑ j, y k j * G.S k j
  -- the state chain
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun μ j => ∑ k, μ k * y k j
      map_add' := by
        intro a b; funext j; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a; funext j; simp [Finset.mul_sum, mul_assoc] }
  have hL : ∀ μ j, L μ j = ∑ k, μ k * y k j := fun μ j => rfl
  have hLnorm : ∀ u : Fin n → ℝ, ∑ j, |L u j| ≤ ∑ k, |u k| := by
    intro u
    calc ∑ j, |L u j| ≤ ∑ j, ∑ k, |u k| * y k j := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          rw [hL]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [abs_mul, abs_of_nonneg ((hymix k).1 j)]
      _ = ∑ k, |u k| := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← Finset.mul_sum, (hymix k).2, mul_one]
  have hpow : ∀ (w : Fin n → ℝ) (t : ℕ), ∑ j, |(L ^ t) w j| ≤ ∑ k, |w k| := by
    intro w t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact (hLnorm _).trans ih
  have hbd : ∀ w : Fin n → ℝ, ∃ C, ∀ t : ℕ, ‖(L ^ t) w‖ ≤ C := by
    intro w
    refine ⟨∑ k, |w k|, fun t => ?_⟩
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun k _ => abs_nonneg _))).2
      (fun j => ?_)
    rw [Real.norm_eq_abs]
    exact (Finset.single_le_sum (f := fun j => |(L ^ t) w j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ j)).trans (hpow w t)
  let δ0 : Fin n → ℝ := fun k => if k = 0 then 1 else 0
  obtain ⟨π, hπ⟩ := cesaro_of_bounded L hbd δ0
  let μ : ℕ → Fin n → ℝ := fun t => (L ^ t) δ0
  refine ⟨∑ k, π k * ρ k, ∑ k, π k * sk k, ?_⟩
  -- the stationary best response
  let σ0 : Strategy1 m n :=
    { act := fun _ h => BlottoLP.Flow.pureMixed (f (prevAction h))
      act_mem := fun _ _ => by
        refine ⟨fun a => ?_, ?_⟩
        · unfold BlottoLP.Flow.pureMixed; split_ifs <;> norm_num
        · simp [BlottoLP.Flow.pureMixed] }
  refine ⟨σ0, ⟨fun k => BlottoLP.Flow.pureMixed (f k), fun t h => rfl⟩, ?_⟩
  intro c hc
  let r : Fin n → ℝ := fun k => ρ k + c * sk k
  -- inner one-step payoff
  have hinner : ∀ (k : Fin n) (p : Fin m → ℝ),
      ∑ i, p i * ∑ j, y k j * (G.A i j + c * G.S k j) = ∑ i, p i * (rowval k i + c * sk k) := by
    intro k p
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    simp only [rowval, sk, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- per-stage bound, and equality for σ0
  have hstage_le : ∀ (σ' : Strategy1 m n) (t : ℕ),
      ∑ h : History m n (t + 1), histProb σ' τ h * SCGstageR G c t h ≤ ∑ k, μ t k * r k := by
    intro σ' t
    rw [SCG_stage_formula G c σ' τ y hy t, ← SCG_occupation σ' τ y hy L hL t r]
    refine Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left ?_ (histProb_nonneg σ' τ h))
    rw [hinner]
    calc ∑ i, σ'.act t h i * (rowval (prevAction h) i + c * sk (prevAction h))
        ≤ ∑ i, σ'.act t h i * r (prevAction h) := by
          refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_
            ((σ'.act_mem _ _).1 i))
          have : rowval (prevAction h) i ≤ ρ (prevAction h) :=
            Finset.le_sup' (rowval (prevAction h)) (Finset.mem_univ i)
          simp only [r]; linarith
      _ = r (prevAction h) := by rw [← Finset.sum_mul, (σ'.act_mem _ _).2, one_mul]
  have hstage_eq : ∀ t : ℕ,
      ∑ h : History m n (t + 1), histProb σ0 τ h * SCGstageR G c t h = ∑ k, μ t k * r k := by
    intro t
    rw [SCG_stage_formula G c σ0 τ y hy t, ← SCG_occupation σ0 τ y hy L hL t r]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    congr 1
    rw [hinner]
    simp only [σ0, BlottoLP.Flow.pureMixed, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hfk]
  -- Cesàro averages of the bound
  let g : ℕ → ℝ := fun T => ∑ k, ((T : ℝ)⁻¹ • ∑ t ∈ range T, μ t) k * r k
  have hg : Tendsto g atTop (𝓝 (∑ k, π k * ρ k + (∑ k, π k * sk k) * c)) := by
    have : ∑ k, π k * ρ k + (∑ k, π k * sk k) * c = ∑ k, π k * r k := by
      simp only [r, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [this]
    refine tendsto_finsetSum _ (fun k _ => ?_)
    exact ((continuous_apply k).continuousAt.tendsto.comp hπ).mul_const _
  have hET : ∀ (σ' : Strategy1 m n) (T : ℕ), 1 ≤ T →
      expectedTotal G c σ' τ T / T ≤ g T := by
    intro σ' T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    rw [div_le_iff₀ hTpos, SCG_expectedTotal_eq]
    calc ∑ t ∈ range T, ∑ h : History m n (t + 1), histProb σ' τ h * SCGstageR G c t h
        ≤ ∑ t ∈ range T, ∑ k, μ t k * r k := Finset.sum_le_sum (fun t _ => hstage_le σ' t)
      _ = g T * T := by
          simp only [g, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
          rw [Finset.sum_comm, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← Finset.sum_mul]
          field_simp
  have hET0 : ∀ T : ℕ, 1 ≤ T → expectedTotal G c σ0 τ T / T = g T := by
    intro T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    rw [div_eq_iff hTpos.ne', SCG_expectedTotal_eq]
    calc ∑ t ∈ range T, ∑ h : History m n (t + 1), histProb σ0 τ h * SCGstageR G c t h
        = ∑ t ∈ range T, ∑ k, μ t k * r k := Finset.sum_congr rfl (fun t _ => hstage_eq t)
      _ = g T * T := by
          simp only [g, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
          rw [Finset.sum_comm, Finset.sum_mul]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← Finset.sum_mul]
          field_simp
  -- lower bound (boundedness below)
  set mA := Finset.univ.inf' Finset.univ_nonempty (fun p : Fin m × Fin n => G.A p.1 p.2)
  have hlo : ∀ (σ' : Strategy1 m n), ∀ᶠ T : ℕ in atTop, mA ≤ expectedTotal G c σ' τ T / T := by
    intro σ'
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    rw [le_div_iff₀ hTpos]
    unfold expectedTotal
    calc mA * T = ∑ h : History m n T, histProb σ' τ h * (T * mA) := by
          rw [← Finset.sum_mul, sum_histProb, one_mul, mul_comm]
      _ ≤ _ := by
        refine Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left ?_
          (histProb_nonneg σ' τ h))
        calc (T : ℝ) * mA = ∑ _s : Fin T, mA := by simp
          _ ≤ _ := by
            refine Finset.sum_le_sum (fun s _ => ?_)
            have : mA ≤ G.A (h s).1 (h s).2 :=
              Finset.inf'_le (fun p : Fin m × Fin n => G.A p.1 p.2) (Finset.mem_univ (h s))
            have : 0 ≤ c * G.S (prevAction (h.take s s.isLt.le)) (h s).2 :=
              mul_nonneg hc (G.S_nonneg _ _)
            linarith
  have hlim_eq : ∑ k, π k * ρ k + (∑ k, π k * sk k) * c =
      ∑ k, π k * ρ k + (∑ k, π k * sk k) * c := rfl
  refine ⟨?_, ?_⟩
  · unfold payoff
    have : Tendsto (fun T : ℕ => expectedTotal G c σ0 τ T / T) atTop
        (𝓝 (∑ k, π k * ρ k + (∑ k, π k * sk k) * c)) := by
      refine hg.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with T hT
      exact (hET0 T hT).symm
    rw [this.liminf_eq, mul_comm]
  · intro σ'
    unfold payoff
    calc Filter.liminf (fun T : ℕ => expectedTotal G c σ' τ T / T) atTop
        ≤ Filter.liminf g atTop :=
          Filter.liminf_le_liminf
            (by filter_upwards [eventually_ge_atTop 1] with T hT; exact hET σ' T hT)
            (Filter.isBoundedUnder_of_eventually_ge (hlo σ')) hg.isCoboundedUnder_ge
      _ = _ := by rw [hg.liminf_eq, mul_comm]
