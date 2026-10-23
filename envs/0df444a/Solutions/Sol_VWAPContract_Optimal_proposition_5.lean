-- Prove2me | solution 1 for VWAPContract.Optimal.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T02:34:42.462639+00:00
-- url     : https://prove2.me/submissions/ac3ecc11-3137-4fb4-9f75-c4feaf9c93d2

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model

set_option autoImplicit false

open MeasureTheory

/-- A strictly increasing concave function on ℝ has a nonnegative supergradient at 0. -/
lemma vwap_supergrad {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) (hmono : StrictMono u) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x, u x ≤ u 0 + c * x := by
  have hg : ConvexOn ℝ Set.univ (fun x => -u x) := hu.neg
  have hint : (0:ℝ) ∈ interior (Set.univ : Set ℝ) := by simp
  set c' := derivWithin (fun x => -u x) (Set.Ioi 0) 0 with hc'
  have hR : ∀ y : ℝ, 0 < y → c' ≤ (-u y - -u 0) / (y - 0) := by
    intro y hy
    have := hg.rightDeriv_le_slope (Set.mem_univ 0) (Set.mem_univ y) hy
      (hg.differentiableWithinAt_Ioi_of_mem_interior hint)
    rwa [slope_def_field] at this
  refine ⟨-c', ?_, ?_⟩
  · have h1 := hR 1 one_pos
    have := hmono (zero_lt_one' ℝ)
    norm_num at h1
    linarith
  · intro x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have h1 := hg.slope_le_leftDeriv (Set.mem_univ x) (Set.mem_univ 0) hx
        (hg.differentiableWithinAt_Iio_of_mem_interior hint)
      have h2 := hg.leftDeriv_le_rightDeriv_of_mem_interior hint
      rw [slope_def_field] at h1
      have h3 : (-u 0 - -u x) / (0 - x) ≤ c' := h1.trans h2
      rw [div_le_iff₀ (by linarith)] at h3
      nlinarith
    · subst hx; simp
    · have h3 := hR x hx
      rw [le_div_iff₀ (by linarith)] at h3
      nlinarith

/-- Weighted Chebyshev sum inequality for oppositely ordered sequences. -/
lemma vwap_cheb {T : ℕ} (y V h : Fin T → ℝ) (hy : ∀ t, 0 ≤ y t) (hs : ∑ t, y t = 1)
    (hpair : ∀ s t, 0 < y s → 0 < y t → (V t - V s) * (h t - h s) ≤ 0) :
    ∑ t, y t * V t * h t ≤ (∑ t, y t * V t) * ∑ t, y t * h t := by
  have e1 : ∑ t, ∑ s, y t * y s * V t * h t = ∑ t, y t * V t * h t := by
    refine Finset.sum_congr rfl fun t _ => ?_
    calc ∑ s, y t * y s * V t * h t = ∑ s, (y t * V t * h t) * y s :=
          Finset.sum_congr rfl fun s _ => by ring
      _ = _ := by rw [← Finset.mul_sum, hs, mul_one]
  have e2 : ∑ t, ∑ s, y t * y s * V t * h s = (∑ t, y t * V t) * ∑ t, y t * h t := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
  have key : ∑ t, y t * V t * h t - (∑ t, y t * V t) * ∑ t, y t * h t
      = ∑ t, ∑ s, y t * y s * V t * (h t - h s) := by
    rw [← e1, ← e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have sym : ∑ t, ∑ s, y t * y s * V t * (h t - h s)
      = ∑ t, ∑ s, y s * y t * V s * (h s - h t) := Finset.sum_comm
  have hneg : ∑ t, ∑ s, (y t * y s * V t * (h t - h s) + y s * y t * V s * (h s - h t)) ≤ 0 := by
    refine Finset.sum_nonpos fun t _ => Finset.sum_nonpos fun s _ => ?_
    have e : y t * y s * V t * (h t - h s) + y s * y t * V s * (h s - h t)
        = y t * y s * ((V t - V s) * (h t - h s)) := by ring
    rw [e]
    rcases (hy t).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    rcases (hy s).eq_or_lt with h1 | h1
    · rw [← h1]; simp
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hpair s t h1 h0)
  have split : ∑ t, ∑ s, (y t * y s * V t * (h t - h s) + y s * y t * V s * (h s - h t))
      = ∑ t, ∑ s, y t * y s * V t * (h t - h s) + ∑ t, ∑ s, y s * y t * V s * (h s - h t) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_add_distrib
  linarith

/-- Pointwise: the VWAP-weighted average impact never exceeds the schedule-weighted one. -/
lemma vwap_impact {T : ℕ} (hfun : ℝ → ℝ) (vol : ℝ → ℝ → ℝ) (V : ℝ → ℝ)
    (hh : StrictMonoOn hfun (Set.Ici 0))
    (hvolpos : ∀ x e, 0 ≤ x → 0 < e → 0 < vol x e)
    (hvolV : ∀ x e, 0 < x → 0 < e → vol x e = x * V (x / e))
    (hV : StrictAntiOn V (Set.Ioi 0))
    (e y : Fin T → ℝ) (he : ∀ t, 0 < e t) (hy : ∀ t, 0 ≤ y t) (hs : ∑ t, y t = 1) :
    ∑ t, vol (y t) (e t) * hfun (y t / e t)
      ≤ (∑ t, vol (y t) (e t)) * ∑ t, y t * hfun (y t / e t) := by
  set r : Fin T → ℝ := fun t => y t / e t with hr
  have hr0 : ∀ t, 0 ≤ r t := fun t => div_nonneg (hy t) (he t).le
  set H := ∑ t, y t * hfun (r t) with hH
  set z : Fin T → ℝ := fun t => if y t = 0 then vol (y t) (e t) else 0 with hz
  have hvz : ∀ t, vol (y t) (e t) = y t * V (r t) + z t := by
    intro t
    by_cases h0 : y t = 0
    · simp [hz, h0]
    · have hpos : 0 < y t := lt_of_le_of_ne (hy t) (Ne.symm h0)
      simp [hz, h0, hvolV _ _ hpos (he t), hr]
  have hz0 : ∀ t, 0 ≤ z t := by
    intro t; simp only [hz]; split_ifs
    · exact (hvolpos _ _ (hy t) (he t)).le
    · exact le_rfl
  have hh0 : hfun 0 ≤ H := by
    have : ∑ t, y t * hfun 0 ≤ H :=
      Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
        (hh.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (hr0 t)) (hr0 t)) (hy t)
    rwa [← Finset.sum_mul, hs, one_mul] at this
  have hcheb := vwap_cheb y (fun t => V (r t)) (fun t => hfun (r t)) hy hs (by
    intro s t hs' ht'
    have hrs : 0 < r s := div_pos hs' (he s)
    have hrt : 0 < r t := div_pos ht' (he t)
    rcases le_total (r s) (r t) with hle | hle
    · have h1 := hV.antitoneOn (Set.mem_Ioi.2 hrs) (Set.mem_Ioi.2 hrt) hle
      have h2 := hh.monotoneOn (Set.mem_Ici.2 hrs.le) (Set.mem_Ici.2 hrt.le) hle
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · have h1 := hV.antitoneOn (Set.mem_Ioi.2 hrt) (Set.mem_Ioi.2 hrs) hle
      have h2 := hh.monotoneOn (Set.mem_Ici.2 hrt.le) (Set.mem_Ici.2 hrs.le) hle
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
  have hzH : ∑ t, z t * hfun (r t) ≤ ∑ t, z t * H := by
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases h0 : y t = 0
    · have : r t = 0 := by simp [hr, h0]
      rw [this]; exact mul_le_mul_of_nonneg_left hh0 (hz0 t)
    · simp [hz, h0]
  have lhs : ∑ t, vol (y t) (e t) * hfun (r t)
      = ∑ t, y t * V (r t) * hfun (r t) + ∑ t, z t * hfun (r t) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by rw [hvz t]; ring
  have rhs : ∑ t, vol (y t) (e t) = ∑ t, y t * V (r t) + ∑ t, z t := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => hvz t
  show ∑ t, vol (y t) (e t) * hfun (r t) ≤ (∑ t, vol (y t) (e t)) * H
  have hzH' : ∑ t, z t * H = (∑ t, z t) * H := (Finset.sum_mul _ _ _).symm
  rw [lhs, rhs, add_mul]
  beta_reduce at hcheb
  linarith

open VWAPContract.Optimal in
/-- Conditional mean zero (mean `mu`) of the shocks against any bounded `eta`-measurable weight. -/
lemma vwap_noise {T : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model T Ω) (hM : M.Standing)
    (G : (Fin T → ℝ) → ℝ) (hG : Measurable G) (C : ℝ) (hC : ∀ ω, |G (M.eta ω)| ≤ C)
    (t : Fin T) :
    Integrable (fun ω => G (M.eta ω)) M.P ∧
    Integrable (fun ω => G (M.eta ω) * M.eps ω t) M.P ∧
    ∫ ω, G (M.eta ω) * M.eps ω t ∂M.P = M.mu * ∫ ω, G (M.eta ω) ∂M.P := by
  obtain ⟨hP, -, hη, -, -, hεi, hce, -⟩ := hM
  have hle : etaAlg M ≤ ‹MeasurableSpace Ω› := hη.comap_le
  have hGm : StronglyMeasurable[etaAlg M] (fun ω => G (M.eta ω)) :=
    (hG.comp (comap_measurable M.eta)).stronglyMeasurable
  have hGa : AEStronglyMeasurable (fun ω => G (M.eta ω)) M.P :=
    (hG.comp hη).aestronglyMeasurable
  have hGi : Integrable (fun ω => G (M.eta ω)) M.P :=
    Integrable.of_bound hGa C (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω)
  have hprod : Integrable (fun ω => G (M.eta ω) * M.eps ω t) M.P :=
    (hεi t).bdd_mul hGa (c := C) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω)
  refine ⟨hGi, hprod, ?_⟩
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := M.P) hGm hprod (hεi t)
  calc ∫ ω, G (M.eta ω) * M.eps ω t ∂M.P
      = ∫ ω, (M.P[(fun ω => G (M.eta ω)) * (fun ω => M.eps ω t) | etaAlg M]) ω ∂M.P := by
        rw [integral_condExp hle]; rfl
    _ = ∫ ω, G (M.eta ω) * M.mu ∂M.P := by
        refine integral_congr_ae ?_
        filter_upwards [hpull, hce t] with ω h1 h2
        rw [h1, Pi.mul_apply, h2]
    _ = M.mu * ∫ ω, G (M.eta ω) ∂M.P := by
        rw [integral_mul_const, mul_comm]

open VWAPContract.Optimal in
lemma vwap_cost_split {T : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model T Ω)
    (X : (Fin T → ℝ) → (Fin T → ℝ)) (ω : Ω) :
    cost M X ω = ∑ t, M.h (X (M.eta ω) t / M.eta ω t) * X (M.eta ω) t
      + ∑ t, X (M.eta ω) t * M.eps ω t := by
  unfold cost price
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

open VWAPContract.Optimal in
/-- Finite Jensen: the first-best impact cost is a pointwise lower bound. -/
lemma vwap_fb_lower {T : ℕ} (hfun : ℝ → ℝ)
    (hconv : StrictConvexOn ℝ (Set.Ici 0) (fun y => y * hfun y))
    (e x : Fin T → ℝ) (he : ∀ t, 0 < e t) (hx : ∀ t, 0 ≤ x t) (hs : ∑ t, x t = 1)
    (hS : 0 < ∑ t, e t) :
    hfun (1 / ∑ t, e t) ≤ ∑ t, hfun (x t / e t) * x t := by
  set S := ∑ t, e t with hSdef
  have hw0 : ∀ t ∈ Finset.univ, 0 ≤ e t / S := fun t _ => div_nonneg (he t).le hS.le
  have hw1 : ∑ t, e t / S = 1 := by rw [← Finset.sum_div, div_self hS.ne']
  have hmem : ∀ t ∈ Finset.univ, x t / e t ∈ Set.Ici (0:ℝ) :=
    fun t _ => Set.mem_Ici.2 (div_nonneg (hx t) (he t).le)
  have J := hconv.convexOn.map_sum_le hw0 hw1 hmem
  have hpt : ∑ t, (e t / S) • (x t / e t) = 1 / S := by
    simp only [smul_eq_mul]
    rw [show (1:ℝ) / S = (∑ t, x t) / S by rw [hs], Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by field_simp [(he t).ne']
  have hval : ∑ t, (e t / S) • ((x t / e t) * hfun (x t / e t))
      = (∑ t, hfun (x t / e t) * x t) / S := by
    simp only [smul_eq_mul]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by field_simp [(he t).ne']
  rw [hpt, hval] at J
  have := (le_div_iff₀ hS).1 J
  have e3 : 1 / S * hfun (1 / S) * S = hfun (1 / S) := by field_simp
  linarith

open VWAPContract.Optimal in
theorem solution {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : Model T Ω) (hM : M.Standing) :
    IsOptimal M tauVWAP := by
  have hM' := hM
  obtain ⟨hP, hT, hη, hε, hηpos, hεi, hce, hhm, hhmono, hconv, hvolm, hvolpos, hvolV, hVanti,
    humono, hucon, hhint⟩ := hM'
  haveI : Nonempty (Fin T) := ⟨⟨0, hT⟩⟩
  have hSpos : ∀ e : Fin T → ℝ, (∀ t, 0 < e t) → 0 < ∑ t, e t := fun e he =>
    Finset.sum_pos (fun t _ => he t) Finset.univ_nonempty
  -- the first-best policy
  have hpolFB : IsPolicy (xFB (T := T)) := by
    refine ⟨?_, fun e he => ⟨fun t => div_nonneg (he t).le (hSpos e he).le, ?_⟩⟩
    · unfold xFB; fun_prop
    · unfold xFB; rw [← Finset.sum_div, div_self (hSpos e he).ne']
  have hcontract : IsContract (tauVWAP (T := T)) := by
    unfold IsContract
    show Measurable (fun q : (Fin T → ℝ) × (Fin T → ℝ) => (∑ t, q.1 t * q.2 t) / ∑ s, q.2 s)
    fun_prop
  -- schedule facts for any policy along the path
  have hsched : ∀ X : (Fin T → ℝ) → (Fin T → ℝ), IsPolicy X → ∀ ω,
      (∀ t, 0 ≤ X (M.eta ω) t) ∧ ∑ t, X (M.eta ω) t = 1 := fun X hX ω =>
    hX.2 _ (hηpos ω)
  -- noise term of the cost of any policy has mean mu
  have hnoiseX : ∀ X : (Fin T → ℝ) → (Fin T → ℝ), IsPolicy X →
      Integrable (fun ω => ∑ t, X (M.eta ω) t * M.eps ω t) M.P ∧
      ∫ ω, ∑ t, X (M.eta ω) t * M.eps ω t ∂M.P = M.mu := by
    intro X hX
    have hXt : ∀ t, Measurable (fun e => X e t) := fun t =>
      (measurable_pi_apply t).comp hX.1
    have hb : ∀ t ω, |X (M.eta ω) t| ≤ 1 := by
      intro t ω
      obtain ⟨h0, h1⟩ := hsched X hX ω
      rw [abs_of_nonneg (h0 t), ← h1]
      exact Finset.single_le_sum (fun s _ => h0 s) (Finset.mem_univ t)
    have hN := fun t => vwap_noise M hM (fun e => X e t) (hXt t) 1 (hb t) t
    refine ⟨integrable_finsetSum _ fun t _ => (hN t).2.1, ?_⟩
    rw [integral_finsetSum _ fun t _ => (hN t).2.1]
    simp_rw [fun t => (hN t).2.2]
    rw [← Finset.mul_sum, ← integral_finsetSum _ fun t _ => (hN t).1]
    simp_rw [fun ω => (hsched X hX ω).2]
    simp
  -- first-best cost
  have hFBimp : ∀ ω, ∑ t, M.h (xFB (M.eta ω) t / M.eta ω t) * xFB (M.eta ω) t
      = M.h (1 / ∑ t, M.eta ω t) := by
    intro ω
    have hS := hSpos _ (hηpos ω)
    have : ∀ t, xFB (M.eta ω) t / M.eta ω t = 1 / ∑ t, M.eta ω t := by
      intro t; unfold xFB; field_simp [(hηpos ω t).ne']
    simp_rw [this]
    rw [← Finset.mul_sum, (hsched _ hpolFB ω).2, mul_one]
  have hcostFB : ∀ ω, cost M xFB ω
      = M.h (1 / ∑ t, M.eta ω t) + ∑ t, xFB (M.eta ω) t * M.eps ω t := by
    intro ω; rw [vwap_cost_split, hFBimp]
  have hcostFBi : Integrable (cost M xFB) M.P := by
    have := hhint.add (hnoiseX _ hpolFB).1
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]; rw [hcostFB]
  -- pay equals cost under VWAP with the first-best schedule
  have hpayFB : ∀ ω, pay M tauVWAP xFB ω = cost M xFB ω := by
    intro ω
    have hS := hSpos _ (hηpos ω)
    have hx : ∀ t, 0 < xFB (M.eta ω) t := fun t => div_pos (hηpos ω t) hS
    have hv : ∀ t, M.vol (xFB (M.eta ω) t) (M.eta ω t)
        = xFB (M.eta ω) t * M.V (1 / ∑ t, M.eta ω t) := by
      intro t
      rw [hvolV _ _ (hx t) (hηpos ω t)]
      congr 2; unfold xFB; field_simp [(hηpos ω t).ne']
    obtain ⟨t0⟩ := (inferInstance : Nonempty (Fin T))
    have hVpos : 0 < M.V (1 / ∑ t, M.eta ω t) := by
      have := hvolpos _ _ (hx t0).le (hηpos ω t0)
      rw [hv t0] at this
      exact pos_of_mul_pos_right this (hx t0).le
    unfold pay tauVWAP mktVol cost
    simp_rw [hv]
    rw [← Finset.sum_mul, (hsched _ hpolFB ω).2, one_mul]
    rw [div_eq_iff hVpos.ne']
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hutilFB : ∀ ω, dealerUtil M tauVWAP xFB ω = M.u 0 := by
    intro ω; unfold dealerUtil; rw [hpayFB, sub_self]
  have hEUFB : dealerEU M tauVWAP xFB = M.u 0 := by
    unfold dealerEU; simp_rw [hutilFB]; simp
  -- integrated cost comparison: first best is cheapest in expectation
  have hcost_le : ∀ X : (Fin T → ℝ) → (Fin T → ℝ), IsPolicy X → Integrable (cost M X) M.P →
      ∫ ω, cost M xFB ω ∂M.P ≤ ∫ ω, cost M X ω ∂M.P := by
    intro X hX hXi
    obtain ⟨hNi, hNe⟩ := hnoiseX X hX
    obtain ⟨hNFi, hNFe⟩ := hnoiseX _ hpolFB
    have hIi : Integrable (fun ω => cost M X ω - ∑ t, X (M.eta ω) t * M.eps ω t) M.P :=
      hXi.sub hNi
    have h1 : ∫ ω, cost M X ω ∂M.P
        = ∫ ω, (cost M X ω - ∑ t, X (M.eta ω) t * M.eps ω t) ∂M.P + M.mu := by
      rw [integral_sub hXi hNi, hNe]; ring
    have h2 : ∫ ω, cost M xFB ω ∂M.P = ∫ ω, M.h (1 / ∑ t, M.eta ω t) ∂M.P + M.mu := by
      simp_rw [hcostFB]
      rw [integral_add hhint hNFi, hNFe]
    rw [h1, h2]
    have : ∫ ω, M.h (1 / ∑ t, M.eta ω t) ∂M.P
        ≤ ∫ ω, (cost M X ω - ∑ t, X (M.eta ω) t * M.eps ω t) ∂M.P := by
      refine integral_mono hhint hIi fun ω => ?_
      simp only
      rw [vwap_cost_split, add_sub_cancel_right]
      obtain ⟨h0, h1⟩ := hsched X hX ω
      exact vwap_fb_lower M.h hconv _ _ (hηpos ω) h0 h1 (hSpos _ (hηpos ω))
    linarith
  refine ⟨xFB, ⟨hcontract, hpolFB, ?_, hcostFBi, ?_, ?_, ?_⟩, ?_⟩
  · exact hcostFBi.congr (Filter.Eventually.of_forall fun ω => (hpayFB ω).symm)
  · exact (integrable_const (M.u 0)).congr
      (Filter.Eventually.of_forall fun ω => (hutilFB ω).symm)
  · unfold IR; rw [hEUFB]
  · -- incentive compatibility
    intro Y hY hYi
    rw [hEUFB]
    obtain ⟨c, hc0, hc⟩ := vwap_supergrad hucon humono
    have hYt : ∀ t, Measurable (fun e => Y e t) := fun t =>
      (measurable_pi_apply t).comp hY.1
    set G : Fin T → (Fin T → ℝ) → ℝ := fun t e =>
      M.vol (Y e t) (e t) / (∑ s, M.vol (Y e s) (e s)) - Y e t with hGdef
    have hGm : ∀ t, Measurable (G t) := by
      intro t
      have hv : ∀ s, Measurable (fun e : Fin T → ℝ => M.vol (Y e s) (e s)) := fun s =>
        hvolm.comp ((hYt s).prodMk (measurable_pi_apply s))
      exact ((hv t).div (Finset.measurable_sum _ fun s _ => hv s)).sub (hYt t)
    have hvpos : ∀ ω t, 0 < M.vol (Y (M.eta ω) t) (M.eta ω t) := fun ω t =>
      hvolpos _ _ ((hsched Y hY ω).1 t) (hηpos ω t)
    have hVs : ∀ ω, 0 < ∑ s, M.vol (Y (M.eta ω) s) (M.eta ω s) := fun ω =>
      Finset.sum_pos (fun s _ => hvpos ω s) Finset.univ_nonempty
    have hGb : ∀ t ω, |G t (M.eta ω)| ≤ 2 := by
      intro t ω
      obtain ⟨h0, h1⟩ := hsched Y hY ω
      have hy1 : Y (M.eta ω) t ≤ 1 := by
        rw [← h1]; exact Finset.single_le_sum (fun s _ => h0 s) (Finset.mem_univ t)
      have hw0 : 0 ≤ M.vol (Y (M.eta ω) t) (M.eta ω t) / ∑ s, M.vol (Y (M.eta ω) s) (M.eta ω s) :=
        div_nonneg (hvpos ω t).le (hVs ω).le
      have hw1 : M.vol (Y (M.eta ω) t) (M.eta ω t) / ∑ s, M.vol (Y (M.eta ω) s) (M.eta ω s) ≤ 1 := by
        rw [div_le_one (hVs ω)]
        exact Finset.single_le_sum (fun s _ => (hvpos ω s).le) (Finset.mem_univ t)
      simp only [hGdef]
      rw [abs_le]; constructor <;> linarith [h0 t]
    have hN := fun t => vwap_noise M hM (G t) (hGm t) 2 (hGb t) t
    set N : Ω → ℝ := fun ω => ∑ t, G t (M.eta ω) * M.eps ω t with hNdef
    have hNi : Integrable N M.P := integrable_finsetSum _ fun t _ => (hN t).2.1
    have hNe : ∫ ω, N ω ∂M.P = 0 := by
      simp only [hNdef]
      rw [integral_finsetSum _ fun t _ => (hN t).2.1]
      simp_rw [fun t => (hN t).2.2]
      rw [← Finset.mul_sum, ← integral_finsetSum _ fun t _ => (hN t).1]
      have : ∀ ω, ∑ t, G t (M.eta ω) = 0 := by
        intro ω
        simp only [hGdef]
        rw [Finset.sum_sub_distrib, ← Finset.sum_div, div_self (hVs ω).ne',
          (hsched Y hY ω).2, sub_self]
      simp_rw [this]; simp
    -- pointwise: dealer surplus is at most the noise term
    have hDN : ∀ ω, pay M tauVWAP Y ω - cost M Y ω ≤ N ω := by
      intro ω
      obtain ⟨h0, h1⟩ := hsched Y hY ω
      have himp := vwap_impact M.h M.vol M.V hhmono hvolpos hvolV hVanti (M.eta ω)
        (Y (M.eta ω)) (hηpos ω) h0 h1
      have hVs' := hVs ω
      have hne := hVs'.ne'
      have hdecomp : pay M tauVWAP Y ω - cost M Y ω - N ω
          = (∑ t, M.vol (Y (M.eta ω) t) (M.eta ω t) * M.h (Y (M.eta ω) t / M.eta ω t))
            / ∑ s, M.vol (Y (M.eta ω) s) (M.eta ω s)
            - ∑ t, Y (M.eta ω) t * M.h (Y (M.eta ω) t / M.eta ω t) := by
        unfold pay tauVWAP mktVol cost price
        simp only [hNdef, hGdef]
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        field_simp
        ring
      have : (∑ t, M.vol (Y (M.eta ω) t) (M.eta ω t) * M.h (Y (M.eta ω) t / M.eta ω t))
            / ∑ s, M.vol (Y (M.eta ω) s) (M.eta ω s)
          ≤ ∑ t, Y (M.eta ω) t * M.h (Y (M.eta ω) t / M.eta ω t) := by
        rw [div_le_iff₀ hVs', mul_comm]; exact himp
      linarith
    have hbound : ∀ ω, dealerUtil M tauVWAP Y ω ≤ M.u 0 + c * N ω := by
      intro ω
      unfold dealerUtil
      have := hc (pay M tauVWAP Y ω - cost M Y ω)
      nlinarith [hDN ω]
    calc dealerEU M tauVWAP Y = ∫ ω, dealerUtil M tauVWAP Y ω ∂M.P := rfl
      _ ≤ ∫ ω, (M.u 0 + c * N ω) ∂M.P :=
          integral_mono hYi ((integrable_const _).add (hNi.const_mul c)) hbound
      _ = M.u 0 := by
          rw [integral_add (integrable_const _) (hNi.const_mul c), integral_const_mul, hNe]
          simp
  · -- optimality against every feasible pair
    intro τ' X' hF
    obtain ⟨-, hX', hpay', hcost', hutil', hIR', -⟩ := hF
    have hJ : ∫ ω, M.u ((fun ω => pay M τ' X' ω - cost M X' ω) ω) ∂M.P
        ≤ M.u (∫ ω, (pay M τ' X' ω - cost M X' ω) ∂M.P) :=
      hucon.le_map_integral (hucon.continuousOn isOpen_univ) isClosed_univ
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _) (hpay'.sub hcost') hutil'
    have hIR'' : M.u 0 ≤ M.u (∫ ω, (pay M τ' X' ω - cost M X' ω) ∂M.P) :=
      hIR'.trans hJ
    have h0 : 0 ≤ ∫ ω, (pay M τ' X' ω - cost M X' ω) ∂M.P := humono.le_iff_le.1 hIR''
    rw [integral_sub hpay' hcost'] at h0
    have := hcost_le X' hX' hcost'
    have hpe : ∫ ω, pay M tauVWAP xFB ω ∂M.P = ∫ ω, cost M xFB ω ∂M.P := by
      simp_rw [hpayFB]
    linarith
