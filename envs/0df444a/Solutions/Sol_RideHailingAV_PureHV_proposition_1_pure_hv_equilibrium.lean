-- Prove2me | solution 1 for RideHailingAV.PureHV.proposition_1_pure_hv_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T06:17:57.61746+00:00
-- url     : https://prove2.me/submissions/344a5a28-b28a-4ec9-b4cb-d3901f26c4e6

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_aTilde
import Definitions.Def_RideHailingAV_PureHV_util
import Definitions.Def_RideHailingAV_PureHV_IsLooseMarket

set_option autoImplicit false

namespace RideHailingAV.PureHV.Pff1
open RideHailingAV.PureHV

structure Hyp (M : Market) : Prop where
  ha : 0 < M.a
  hr0 : 0 ≤ M.r
  hr1 : M.r < 1
  ht2 : 0 < M.t2
  hV : 0 < M.V
  hw0 : 0 < M.w0
  hα : 0 ≤ M.α

noncomputable def N (M : Market) (d : ℝ) : ℝ :=
  aTilde M * d ^ (1 / (M.r + 1)) + M.t2 * d

noncomputable def F (M : Market) (m d : ℝ) : ℝ :=
  revenue M m d - wage M (N M d) * N M d

def P (M : Market) (m d : ℝ) : Prop :=
  0 ≤ d ∧ d ≤ m ∧ F M m d = 0 ∧ ∀ x, d < x → x ≤ m → F M m x < 0

variable {M : Market}

lemma theta_pos (h : Hyp M) : 0 < 1 / (M.r + 1) := div_pos one_pos (by linarith [h.hr0])

lemma aTilde_nonneg (h : Hyp M) : 0 ≤ aTilde M := by
  unfold aTilde
  exact add_nonneg (mul_nonneg (Real.rpow_nonneg h.hr0 _) (Real.rpow_nonneg h.ha.le _))
    (mul_nonneg (Real.rpow_nonneg h.hr0 _) (Real.rpow_nonneg h.ha.le _))

lemma aTilde_pos (h : Hyp M) (hr : 0 < M.r) : 0 < aTilde M := by
  unfold aTilde
  exact add_pos_of_pos_of_nonneg
    (mul_pos (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos h.ha _))
    (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg h.ha.le _))

lemma aTilde_eq (h : Hyp M) (hr : 0 < M.r) :
    aTilde M = (M.r * M.a) ^ (1 / (M.r + 1)) * (1 + 1 / M.r) := by
  unfold aTilde
  have hne : M.r + 1 ≠ 0 := by linarith
  have e : -M.r / (M.r + 1) = 1 / (M.r + 1) - 1 := by
    rw [div_sub_one hne]; congr 1; ring
  rw [e, Real.rpow_sub_one hr.ne', Real.mul_rpow hr.le h.ha.le]
  ring

lemma aTilde_r0 (hr : M.r = 0) : aTilde M = M.a := by
  unfold aTilde; rw [hr]; simp

lemma N_zero (h : Hyp M) : N M 0 = 0 := by
  unfold N; rw [Real.zero_rpow (theta_pos h).ne']; ring

lemma N_r0 (hr : M.r = 0) (d : ℝ) : N M d = (M.a + M.t2) * d := by
  unfold N
  have : d ^ (1 / ((0:ℝ) + 1)) = d := by norm_num
  rw [aTilde_r0 hr, hr, this]; ring

lemma N_nonneg (h : Hyp M) {d : ℝ} (hd : 0 ≤ d) : 0 ≤ N M d := by
  unfold N
  exact add_nonneg (mul_nonneg (aTilde_nonneg h) (Real.rpow_nonneg hd _)) (mul_nonneg h.ht2.le hd)

lemma N_pos (h : Hyp M) {d : ℝ} (hd : 0 < d) : 0 < N M d := by
  unfold N
  exact add_pos_of_nonneg_of_pos (mul_nonneg (aTilde_nonneg h) (Real.rpow_nonneg hd.le _))
    (mul_pos h.ht2 hd)

lemma N_lt (h : Hyp M) {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : N M x < N M y := by
  unfold N
  have h1 : aTilde M * x ^ (1 / (M.r + 1)) ≤ aTilde M * y ^ (1 / (M.r + 1)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy.le (theta_pos h).le) (aTilde_nonneg h)
  have h2 : M.t2 * x < M.t2 * y := mul_lt_mul_of_pos_left hxy h.ht2
  linarith

lemma N_cont (h : Hyp M) : Continuous (N M) := by
  have hc : Continuous fun d : ℝ => d ^ (1 / (M.r + 1)) :=
    Real.continuous_rpow_const (theta_pos h).le
  unfold N
  fun_prop

lemma F_cont (h : Hyp M) (m : ℝ) : Continuous (F M m) := by
  have hc := N_cont h
  unfold F revenue invDemand wage
  fun_prop

lemma N_eq_pos (h : Hyp M) (hr : 0 < M.r) {d : ℝ} (hd : 0 < d) :
    N M d = (M.r * M.a * d) ^ (1 / (M.r + 1)) * (1 + 1 / M.r) + M.t2 * d := by
  unfold N
  rw [aTilde_eq h hr, Real.mul_rpow (mul_pos hr h.ha).le hd.le]
  ring

lemma inf_aux (b c : ℝ) (hb : ∀ s : ℝ, 0 < s → b ≤ s + c) : b ≤ c := by
  by_contra hlt
  have hlt' : c < b := not_le.mp hlt
  have := hb ((b - c) / 2) (by linarith)
  linarith

lemma minSupply_eq (h : Hyp M) {d : ℝ} (hd : 0 ≤ d) : minSupply M d = N M d := by
  unfold minSupply
  have hne : ((fun s : ℝ => s + d * (M.a * s ^ (-M.r) + M.t2)) '' Set.Ioi 0).Nonempty :=
    ⟨_, 1, Set.mem_Ioi.mpr one_pos, rfl⟩
  apply IsGLB.csInf_eq _ hne
  rcases hd.eq_or_lt with hd0 | hdpos
  · subst hd0
    rw [N_zero h]
    constructor
    · rintro _ ⟨s, hs, rfl⟩
      dsimp only
      simp only [zero_mul, add_zero]
      exact (Set.mem_Ioi.mp hs).le
    · intro b hb
      exact inf_aux b 0 (fun s hs => by
        have := hb ⟨s, Set.mem_Ioi.mpr hs, rfl⟩
        simpa using this)
  rcases h.hr0.eq_or_lt with hr | hr
  · have hs1 : ∀ s : ℝ, s ^ (-M.r) = 1 := fun s => by rw [← hr, neg_zero, Real.rpow_zero]
    rw [N_r0 hr.symm]
    constructor
    · rintro _ ⟨s, hs, rfl⟩
      dsimp only
      rw [hs1, mul_one]
      have := Set.mem_Ioi.mp hs
      linarith
    · intro b hb
      exact inf_aux b ((M.a + M.t2) * d) (fun s hs => by
        have := hb ⟨s, Set.mem_Ioi.mpr hs, rfl⟩
        dsimp only at this
        rw [hs1, mul_one] at this
        linarith)
  -- main case: r > 0, d > 0
  obtain ⟨S, hS⟩ : ∃ S, S = (M.r * M.a * d) ^ (1 / (M.r + 1)) := ⟨_, rfl⟩
  have hprod : 0 < M.r * M.a * d := mul_pos (mul_pos hr h.ha) hdpos
  have hSpos : 0 < S := by rw [hS]; exact Real.rpow_pos_of_pos hprod _
  have hne1 : M.r + 1 ≠ 0 := by linarith
  have hSr : S * S ^ M.r = M.r * M.a * d := by
    have e1 : S ^ (1 + M.r) = S * S ^ M.r := by rw [Real.rpow_add hSpos, Real.rpow_one]
    have e2 : 1 / (M.r + 1) * (1 + M.r) = 1 := by
      rw [add_comm 1 M.r]; exact one_div_mul_cancel hne1
    rw [← e1, hS, ← Real.rpow_mul hprod.le, e2, Real.rpow_one]
  have hSrpos : 0 < S ^ M.r := Real.rpow_pos_of_pos hSpos _
  have hda : d * M.a * (S ^ M.r)⁻¹ = S / M.r := by
    rw [eq_div_iff hr.ne']
    field_simp
    linarith [hSr]
  have hNeq : N M d = S + S / M.r + M.t2 * d := by
    rw [N_eq_pos h hr hdpos, ← hS]; ring
  rw [hNeq]
  apply IsLeast.isGLB
  constructor
  · refine ⟨S, Set.mem_Ioi.mpr hSpos, ?_⟩
    dsimp only
    rw [Real.rpow_neg hSpos.le]
    linear_combination hda
  · rintro _ ⟨s, hs, rfl⟩
    dsimp only
    have hs0 : 0 < s := Set.mem_Ioi.mp hs
    obtain ⟨x, hx_def⟩ : ∃ x, x = s / S := ⟨_, rfl⟩
    have hsx : s = x * S := by rw [hx_def, div_mul_cancel₀ s hSpos.ne']
    have hxpos : 0 < x := by rw [hx_def]; exact div_pos hs0 hSpos
    have hsr : s ^ (-M.r) = (x ^ M.r)⁻¹ * (S ^ M.r)⁻¹ := by
      rw [hsx, Real.mul_rpow hxpos.le hSpos.le, Real.rpow_neg hxpos.le, Real.rpow_neg hSpos.le]
    have hq : 0 < x ^ M.r := Real.rpow_pos_of_pos hxpos _
    have hbern : x ^ M.r ≤ 1 + M.r * (x - 1) := by
      have := rpow_one_add_le_one_add_mul_self (s := x - 1) (by linarith) h.hr0 h.hr1.le
      rwa [show 1 + (x - 1) = x by ring] at this
    have hinv : 1 - M.r * (x - 1) ≤ (x ^ M.r)⁻¹ := by
      rcases le_or_gt (1 - M.r * (x - 1)) 0 with hneg | hpos
      · exact hneg.trans (inv_pos.mpr hq).le
      · rw [← one_div, le_div_iff₀ hq]
        nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hbern), sq_nonneg (M.r * (x - 1))]
    rw [hsr, hsx]
    have e3 : d * (M.a * ((x ^ M.r)⁻¹ * (S ^ M.r)⁻¹) + M.t2)
        = (x ^ M.r)⁻¹ * (S / M.r) + M.t2 * d := by
      rw [← hda]; ring
    rw [e3]
    have hSr' : 0 < S / M.r := div_pos hSpos hr
    have h4 := mul_le_mul_of_nonneg_right hinv hSr'.le
    have e2 : (1 - M.r * (x - 1)) * (S / M.r) = S / M.r - S * (x - 1) := by
      field_simp
    linarith

lemma lab_eq (h : Hyp M) (m : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    revenue M m x - laborCost M x = F M m x := by
  unfold F laborCost; rw [minSupply_eq h hx]

lemma eq_iff (h : Hyp M) {m d : ℝ} :
    IsHVEquilibrium M m d ↔ (0 ≤ d ∧ d ≤ m ∧ F M m d = 0) := by
  unfold IsHVEquilibrium
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, h1, ?_⟩
    have := lab_eq h m h0
    linarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h0, h1, ?_⟩
    have := lab_eq h m h0
    linarith

lemma F_zero (h : Hyp M) (m : ℝ) : F M m 0 = 0 := by
  unfold F revenue; rw [N_zero h]; ring

lemma F_m_neg (h : Hyp M) {m : ℝ} (hm : 0 < m) : F M m m < 0 := by
  have hn := N_pos h hm
  have h1 : revenue M m m = 0 := by
    unfold revenue invDemand; rw [div_self hm.ne']; ring
  have h2 : 0 < wage M (N M m) * N M m := by
    unfold wage
    exact mul_pos (add_pos_of_pos_of_nonneg h.hw0 (mul_nonneg h.hα hn.le)) hn
  unfold F; linarith

lemma exP (h : Hyp M) {m : ℝ} (hm : 0 < m) : ∃ d, P M m d := by
  have hfc := F_cont h m
  have hSc : IsCompact (Set.Icc 0 m ∩ (F M m) ⁻¹' {0}) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hfc)
  have hSne : (Set.Icc 0 m ∩ (F M m) ⁻¹' {0}).Nonempty :=
    ⟨0, ⟨le_refl 0, hm.le⟩, by
      rw [Set.mem_preimage, Set.mem_singleton_iff]; exact F_zero h m⟩
  obtain ⟨d0, hd0S, hmax⟩ := hSc.exists_isGreatest hSne
  have hd0z : F M m d0 = 0 := hd0S.2
  refine ⟨d0, hd0S.1.1, hd0S.1.2, hd0z, ?_⟩
  intro x hx hxm
  by_contra hneg
  have hpos : 0 ≤ F M m x := not_lt.mp hneg
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hxm hfc.continuousOn
    ⟨(F_m_neg h hm).le, hpos⟩
  have hzS : z ∈ Set.Icc 0 m ∩ (F M m) ⁻¹' {0} :=
    ⟨⟨by linarith [hz.1, hd0S.1.1], hz.2⟩, by
      rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hz0⟩
  have := hmax hzS
  linarith [hz.1]

lemma P_unique {m d d' : ℝ} (hP : P M m d) (hP' : P M m d') : d = d' := by
  rcases lt_trichotomy d d' with hlt | heq | hgt
  · have := hP.2.2.2 d' hlt hP'.2.1; linarith [hP'.2.2.1]
  · exact heq
  · have := hP'.2.2.2 d hgt hP.2.1; linarith [hP.2.2.1]

lemma P_lower {m d x0 : ℝ} (hP : P M m d) (hxm : x0 ≤ m) (hF : 0 ≤ F M m x0) : x0 ≤ d := by
  by_contra hc
  have := hP.2.2.2 x0 (not_le.mp hc) hxm
  linarith

lemma P_upper {m d y : ℝ} (hP : P M m d) (hy : ∀ x, y < x → x ≤ m → F M m x < 0) : d ≤ y := by
  by_contra hc
  have := hy d (not_le.mp hc) hP.2.1
  linarith [hP.2.2.1]

lemma P_max (h : Hyp M) {m d : ℝ} (hP : P M m d) : IsMaxStableHVEquilibrium M m d := by
  obtain ⟨h0, h1, h2, h3⟩ := hP
  refine ⟨⟨(eq_iff h).mpr ⟨h0, h1, h2⟩, ?_⟩, ?_⟩
  · rintro ⟨ε, hε, -, hle, -, hgt⟩
    have h4 := h3 (d + ε) (by linarith) hle
    have h5 := lab_eq h m (by linarith : 0 ≤ d + ε)
    linarith
  · intro d' hd'
    obtain ⟨a0, a1, a2⟩ := (eq_iff h).mp hd'.1
    by_contra hc
    have := h3 d' (not_le.mp hc) a1
    linarith

lemma P_iff (h : Hyp M) {m d : ℝ} (hm : 0 < m) : IsMaxStableHVEquilibrium M m d ↔ P M m d := by
  constructor
  · intro hd
    obtain ⟨d0, hP0⟩ := exP h hm
    have h1 : d0 ≤ d := hd.2 d0 (P_max h hP0).1
    have h2 : d ≤ d0 := (P_max h hP0).2 d hd.1
    have : d = d0 := le_antisymm h2 h1
    rw [this]; exact hP0
  · exact P_max h

lemma Rp_formula (h : Hyp M) {m p : ℝ} (hm : 0 < m) (hpV : p ≤ M.V) :
    revenue M m (demandAtPrice M m p) = m * M.t2 * (M.V / 4 - (p - M.V / 2) ^ 2 / M.V) := by
  have hmne := hm.ne'
  have hVne := h.hV.ne'
  unfold revenue demandAtPrice invDemand
  rw [min_eq_left ((div_le_one h.hV).mpr hpV)]
  field_simp
  ring

lemma Rp_big (h : Hyp M) {m p : ℝ} (hpV : M.V < p) :
    revenue M m (demandAtPrice M m p) = 0 := by
  unfold revenue demandAtPrice
  rw [min_eq_right ((one_le_div h.hV).mpr hpV.le)]
  ring

lemma Rp_half (h : Hyp M) {m : ℝ} (hm : 0 < m) :
    revenue M m (demandAtPrice M m (M.V / 2)) = m * M.t2 * (M.V / 4) := by
  rw [Rp_formula h hm (by linarith [h.hV])]; ring

lemma loose_iff (h : Hyp M) {m d : ℝ} (hm : 0 < m) (hP : P M m d) :
    IsLooseMarket M m ↔ m / 2 ≤ d := by
  have hV := h.hV
  have hmt := mul_pos hm h.ht2
  constructor
  · intro hl
    have hmax : IsMaxOn (fun p => revenue M m (demandAtPrice M m p)) (Set.Ici 0) (M.V / 2) := by
      rw [isMaxOn_iff]
      intro p hp
      rw [Rp_half h hm]
      rcases le_or_gt p M.V with hpV | hpV
      · rw [Rp_formula h hm hpV]
        have : 0 ≤ (p - M.V / 2) ^ 2 / M.V := div_nonneg (sq_nonneg _) hV.le
        nlinarith
      · rw [Rp_big h hpV]
        have := mul_pos hmt hV
        linarith
    have h1 := hl d (P_max h hP) (M.V / 2) (by linarith) hmax
    unfold invDemand at h1
    have h2 : M.V * (1 / 2) ≤ M.V * (d / m) := by linarith
    have h3 := le_of_mul_le_mul_left h2 hV
    rw [le_div_iff₀ hm] at h3
    linarith
  · intro hd d' hd' q hq0 hqmax
    have hdd : d' = d := P_unique ((P_iff h hm).mp hd') hP
    rw [hdd]
    have hq : M.V / 2 ≤ q := by
      by_contra hc
      have hlt : q < M.V / 2 := not_le.mp hc
      have h1 := (isMaxOn_iff.mp hqmax) (M.V / 2) (Set.mem_Ici.mpr (by linarith))
      rw [Rp_half h hm, Rp_formula h hm (by linarith)] at h1
      have hneg : q - M.V / 2 < 0 := by linarith
      have hsq : 0 < (q - M.V / 2) ^ 2 := by nlinarith
      have h5 : 0 < (q - M.V / 2) ^ 2 / M.V := div_pos hsq hV
      have := mul_pos hmt h5
      nlinarith
    unfold invDemand
    have h2 : 1 / 2 ≤ d / m := (le_div_iff₀ hm).mpr (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h2 hV.le]

lemma util_lt (h : Hyp M) (hr : 0 < M.r) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    x * M.t2 / N M x < y * M.t2 / N M y := by
  have hy : 0 < y := hx.trans hxy
  rw [div_lt_div_iff₀ (N_pos h hx) (N_pos h hy)]
  have hθ1 : 0 < 1 - 1 / (M.r + 1) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have e : 1 / (M.r + 1) + (1 - 1 / (M.r + 1)) = 1 := by ring
  have ex : x = x ^ (1 / (M.r + 1)) * x ^ (1 - 1 / (M.r + 1)) := by
    rw [← Real.rpow_add hx, e, Real.rpow_one]
  have ey : y = y ^ (1 / (M.r + 1)) * y ^ (1 - 1 / (M.r + 1)) := by
    rw [← Real.rpow_add hy, e, Real.rpow_one]
  have hA : 0 < x ^ (1 / (M.r + 1)) := Real.rpow_pos_of_pos hx _
  have hB : 0 < y ^ (1 / (M.r + 1)) := Real.rpow_pos_of_pos hy _
  have hXY : x ^ (1 - 1 / (M.r + 1)) < y ^ (1 - 1 / (M.r + 1)) :=
    Real.rpow_lt_rpow hx.le hxy hθ1
  have hk : x * y ^ (1 / (M.r + 1)) < y * x ^ (1 / (M.r + 1)) := by
    have h3 := mul_lt_mul_of_pos_left hXY (mul_pos hA hB)
    calc x * y ^ (1 / (M.r + 1))
        = x ^ (1 / (M.r + 1)) * y ^ (1 / (M.r + 1)) * x ^ (1 - 1 / (M.r + 1)) := by
          (conv_lhs => rw [ex]); ring
      _ < x ^ (1 / (M.r + 1)) * y ^ (1 / (M.r + 1)) * y ^ (1 - 1 / (M.r + 1)) := h3
      _ = y * x ^ (1 / (M.r + 1)) := by
          (conv_rhs => rw [ey]); ring
  have hpos := mul_pos h.ht2 (aTilde_pos h hr)
  have := mul_lt_mul_of_pos_left hk hpos
  unfold N
  nlinarith

lemma util_r0 (hr : M.r = 0) (h : Hyp M) {d : ℝ} (hd : 0 < d) :
    d * M.t2 / N M d = M.t2 / (M.a + M.t2) := by
  rw [N_r0 hr]
  have h1 : 0 < M.a + M.t2 := add_pos h.ha h.ht2
  rw [div_eq_div_iff (mul_pos h1 hd).ne' h1.ne']
  ring

theorem main_univ :
    (∀ (M : Market), 0 < M.a → 0 ≤ M.r → M.r < 1 → 0 < M.t2 → 0 < M.V → 0 < M.w0 → 0 ≤ M.α →
      ∀ {I : ℕ} (m : Fin I → ℝ), StrictMono m → (∀ i, 0 < m i) →
        (∀ i, IsLooseMarket M (m i)) →
        ∃ dstar : Fin I → ℝ,
          (∀ i, IsMaxStableHVEquilibrium M (m i) (dstar i) ∧
            ∀ d, IsMaxStableHVEquilibrium M (m i) d → d = dstar i) ∧
          (∀ i, revenue M (m i) (dstar i) =
              wage M (minSupply M (dstar i)) * minSupply M (dstar i) ∧
            minSupply M (dstar i) = aTilde M * dstar i ^ (1 / (M.r + 1)) + M.t2 * dstar i) ∧
          StrictMono dstar ∧
          (0 < M.r → StrictMono (fun i => util M (dstar i))) ∧
          (M.r = 0 → ∀ i j, util M (dstar i) = util M (dstar j)) ∧
          StrictMono (fun i => minSupply M (dstar i)) ∧
          (∀ i, invDemand M (m i) (dstar i) =
            wage M (minSupply M (dstar i)) / util M (dstar i))) := by
  intro M ha hr0 hr1 ht2 hV hw0 hα I m hm hmpos hloose
  have h : Hyp M := ⟨ha, hr0, hr1, ht2, hV, hw0, hα⟩
  have hex : ∀ i, ∃ d, P M (m i) d := fun i => exP h (hmpos i)
  choose dstar hdP using hex
  have hhalf : ∀ i, m i / 2 ≤ dstar i := fun i =>
    (loose_iff h (hmpos i) (hdP i)).mp (hloose i)
  have hdpos : ∀ i, 0 < dstar i := fun i => by linarith [hhalf i, hmpos i]
  have hmin : ∀ i, minSupply M (dstar i) = N M (dstar i) := fun i => minSupply_eq h (hdP i).1
  have hmono : StrictMono dstar := by
    intro i j hij
    have hmij := hm hij
    have hdiv : dstar i / m j < dstar i / m i := div_lt_div_of_pos_left (hdpos i) (hmpos i) hmij
    have key : F M (m j) (dstar i) - F M (m i) (dstar i)
        = dstar i * M.V * M.t2 * (dstar i / m i - dstar i / m j) := by
      unfold F revenue invDemand; ring
    have hpos := mul_pos (mul_pos (mul_pos (hdpos i) hV) ht2) (sub_pos.mpr hdiv)
    have hgt : 0 < F M (m j) (dstar i) := by linarith [(hdP i).2.2.1]
    have hle := P_lower (hdP j) (le_trans (hdP i).2.1 hmij.le) hgt.le
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso; rw [heq] at hgt; linarith [(hdP j).2.2.1]
  refine ⟨dstar, fun i => ⟨(P_iff h (hmpos i)).mpr (hdP i),
    fun d hd => P_unique ((P_iff h (hmpos i)).mp hd) (hdP i)⟩, fun i => ⟨?_, ?_⟩, hmono,
    ?_, ?_, ?_, ?_⟩
  · rw [hmin i]
    have := (hdP i).2.2.1
    unfold F at this
    linarith
  · rw [hmin i]; rfl
  · intro hr i j hij
    show util M (dstar i) < util M (dstar j)
    unfold util
    rw [hmin i, hmin j]
    exact util_lt h hr (hdpos i) (hmono hij)
  · intro hr i j
    unfold util
    rw [hmin i, hmin j, util_r0 hr h (hdpos i), util_r0 hr h (hdpos j)]
  · intro i j hij
    show minSupply M (dstar i) < minSupply M (dstar j)
    rw [hmin i, hmin j]
    exact N_lt h (hdP i).1 (hmono hij)
  · intro i
    unfold util
    rw [hmin i]
    have hF := (hdP i).2.2.1
    unfold F revenue at hF
    have hn := N_pos h (hdpos i)
    rw [div_div_eq_mul_div, eq_div_iff (mul_pos (hdpos i) ht2).ne']
    linarith

/-! ### The concrete market for the three examples -/

noncomputable def M0 : Market := ⟨2, 1 / 2, 1, 1, 1 / 20, 1 / 1000⟩

lemma M0_a : M0.a = 2 := rfl
lemma M0_r : M0.r = 1 / 2 := rfl
lemma M0_t2 : M0.t2 = 1 := rfl
lemma M0_V : M0.V = 1 := rfl
lemma M0_w0 : M0.w0 = 1 / 20 := rfl
lemma M0_α : M0.α = 1 / 1000 := rfl

lemma hyp0 : Hyp M0 :=
  ⟨by rw [M0_a]; norm_num, by rw [M0_r]; norm_num, by rw [M0_r]; norm_num,
    by rw [M0_t2]; norm_num, by rw [M0_V]; norm_num, by rw [M0_w0]; norm_num,
    by rw [M0_α]; norm_num⟩

lemma aT0 : aTilde M0 = 3 := by
  rw [aTilde_eq hyp0 (by rw [M0_r]; norm_num), M0_r, M0_a]
  norm_num

lemma N0 (x : ℝ) : N M0 x = 3 * x ^ ((2:ℝ) / 3) + x := by
  unfold N
  rw [aT0, M0_r, M0_t2]
  norm_num

lemma F0 (m x : ℝ) : F M0 m x = x * (1 - x / m) -
    (1 / 20 + 1 / 1000 * (3 * x ^ ((2:ℝ) / 3) + x)) * (3 * x ^ ((2:ℝ) / 3) + x) := by
  unfold F revenue invDemand wage
  rw [N0, M0_V, M0_t2, M0_w0, M0_α]
  ring

lemma u3 {x : ℝ} (hx : 0 ≤ x) : (x ^ ((2:ℝ) / 3)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast (x ^ ((2:ℝ) / 3)) 3, ← Real.rpow_mul hx]
  have : (2:ℝ) / 3 * ((3:ℕ):ℝ) = ((2:ℕ):ℝ) := by norm_num
  rw [this, Real.rpow_natCast]

lemma cost_mono {A B : ℝ} (h0 : 0 ≤ A) (h : A ≤ B) :
    (1 / 20 + 1 / 1000 * A) * A ≤ (1 / 20 + 1 / 1000 * B) * B := by
  nlinarith

lemma F0_lower {m x U : ℝ} (hx : 0 ≤ x) (hU : 0 ≤ U) (hU3 : x ^ 2 ≤ U ^ 3)
    (hval : (1 / 20 + 1 / 1000 * (3 * U + x)) * (3 * U + x) ≤ x * (1 - x / m)) :
    0 ≤ F M0 m x := by
  rw [F0]
  have hu0 : 0 ≤ x ^ ((2:ℝ) / 3) := Real.rpow_nonneg hx _
  have huU : x ^ ((2:ℝ) / 3) ≤ U := by
    by_contra hc
    have hlt : U < x ^ ((2:ℝ) / 3) := not_le.mp hc
    have := pow_lt_pow_left₀ hlt hU (by norm_num : (3:ℕ) ≠ 0)
    rw [u3 hx] at this
    linarith
  have := cost_mono (by linarith : 0 ≤ 3 * x ^ ((2:ℝ) / 3) + x)
    (by linarith : 3 * x ^ ((2:ℝ) / 3) + x ≤ 3 * U + x)
  linarith

lemma F0_upper {m y c : ℝ} (hc : 0 ≤ c) (hc3 : c ^ 3 * m ≤ 1) (hy : 0 ≤ y)
    (hneg : ∀ x, y < x → x ≤ m →
      x * (1 - x / m) < (1 / 20 + 1 / 1000 * ((1 + 3 * c) * x)) * ((1 + 3 * c) * x)) :
    ∀ x, y < x → x ≤ m → F M0 m x < 0 := by
  intro x hyx hxm
  have hx : 0 < x := by linarith
  rw [F0]
  have hu0 : 0 ≤ x ^ ((2:ℝ) / 3) := Real.rpow_nonneg hx.le _
  have hcu : c * x ≤ x ^ ((2:ℝ) / 3) := by
    by_contra hcon
    have hlt : x ^ ((2:ℝ) / 3) < c * x := not_le.mp hcon
    have h3 := pow_lt_pow_left₀ hlt hu0 (by norm_num : (3:ℕ) ≠ 0)
    rw [u3 hx.le] at h3
    have hx2 : 0 < x ^ 2 := by positivity
    have h1 : c ^ 3 * x ≤ c ^ 3 * m := mul_le_mul_of_nonneg_left hxm (pow_nonneg hc 3)
    have h2 : (c * x) ^ 3 = (c ^ 3 * x) * x ^ 2 := by ring
    nlinarith [mul_le_mul_of_nonneg_right h1 hx2.le, mul_le_mul_of_nonneg_right hc3 hx2.le]
  have hL0 : 0 ≤ (1 + 3 * c) * x := mul_nonneg (by linarith) hx.le
  have := cost_mono hL0 (by linarith : (1 + 3 * c) * x ≤ 3 * x ^ ((2:ℝ) / 3) + x)
  have := hneg x hyx hxm
  linarith

lemma b1 {d : ℝ} (hP : P M0 1 d) : 1 / 2 ≤ d ∧ d ≤ 79 / 100 :=
  ⟨P_lower hP (by norm_num) (F0_lower (U := 2 / 3) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)),
   P_upper hP (F0_upper (c := 1) (by norm_num) (by norm_num) (by norm_num) (fun x hx hxm => by
      nlinarith [mul_pos (by linarith : (0:ℝ) < x) (by linarith : (0:ℝ) < x - 79 / 100)]))⟩

lemma b8 {d : ℝ} (hP : P M0 8 d) : 32 / 5 ≤ d :=
  P_lower hP (by norm_num) (F0_lower (U := 69 / 20) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num))

lemma b256 {d : ℝ} (hP : P M0 256 d) : 128 ≤ d ∧ d ≤ 160 :=
  ⟨P_lower hP (by norm_num) (F0_lower (U := 127 / 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)),
   P_upper hP (F0_upper (c := 3 / 20) (by norm_num) (by norm_num) (by norm_num) (fun x hx hxm => by
      nlinarith [mul_pos (by linarith : (0:ℝ) < x) (by linarith : (0:ℝ) < x - 160)]))⟩

lemma price0 (m d : ℝ) : invDemand M0 m d = 1 - d / m := by
  unfold invDemand; rw [M0_V]; ring

theorem ex_all : ∃ d1 d8 d256 : ℝ,
    IsMaxStableHVEquilibrium M0 1 d1 ∧ IsMaxStableHVEquilibrium M0 8 d8 ∧
    IsMaxStableHVEquilibrium M0 256 d256 ∧
    IsLooseMarket M0 1 ∧ IsLooseMarket M0 8 ∧ IsLooseMarket M0 256 ∧
    invDemand M0 8 d8 < invDemand M0 1 d1 ∧ invDemand M0 8 d8 < invDemand M0 256 d256 := by
  obtain ⟨d1, h1⟩ := exP hyp0 (by norm_num : (0:ℝ) < 1)
  obtain ⟨d8, h8⟩ := exP hyp0 (by norm_num : (0:ℝ) < 8)
  obtain ⟨d256, h256⟩ := exP hyp0 (by norm_num : (0:ℝ) < 256)
  have c1 := b1 h1
  have c8 := b8 h8
  have c256 := b256 h256
  refine ⟨d1, d8, d256, P_max hyp0 h1, P_max hyp0 h8, P_max hyp0 h256,
    (loose_iff hyp0 (by norm_num) h1).mpr (by linarith),
    (loose_iff hyp0 (by norm_num) h8).mpr (by linarith),
    (loose_iff hyp0 (by norm_num) h256).mpr (by linarith), ?_, ?_⟩
  · rw [price0, price0]; linarith
  · rw [price0, price0]; linarith

end RideHailingAV.PureHV.Pff1

open RideHailingAV.PureHV in
theorem solution :
    (∀ (M : Market), 0 < M.a → 0 ≤ M.r → M.r < 1 → 0 < M.t2 → 0 < M.V → 0 < M.w0 → 0 ≤ M.α →
      ∀ {I : ℕ} (m : Fin I → ℝ), StrictMono m → (∀ i, 0 < m i) →
        (∀ i, IsLooseMarket M (m i)) →
        ∃ dstar : Fin I → ℝ,
          (∀ i, IsMaxStableHVEquilibrium M (m i) (dstar i) ∧
            ∀ d, IsMaxStableHVEquilibrium M (m i) d → d = dstar i) ∧
          (∀ i, revenue M (m i) (dstar i) =
              wage M (minSupply M (dstar i)) * minSupply M (dstar i) ∧
            minSupply M (dstar i) = aTilde M * dstar i ^ (1 / (M.r + 1)) + M.t2 * dstar i) ∧
          StrictMono dstar ∧
          (0 < M.r → StrictMono (fun i => util M (dstar i))) ∧
          (M.r = 0 → ∀ i j, util M (dstar i) = util M (dstar j)) ∧
          StrictMono (fun i => minSupply M (dstar i)) ∧
          (∀ i, invDemand M (m i) (dstar i) =
            wage M (minSupply M (dstar i)) / util M (dstar i))) ∧
    (∃ (M : Market) (I : ℕ) (m : Fin I → ℝ) (dstar : Fin I → ℝ),
        0 < M.a ∧ 0 ≤ M.r ∧ M.r < 1 ∧ 0 < M.t2 ∧ 0 < M.V ∧ 0 < M.w0 ∧ 0 ≤ M.α ∧
        2 ≤ I ∧ StrictMono m ∧ (∀ i, 0 < m i) ∧ (∀ i, IsLooseMarket M (m i)) ∧
        (∀ i, IsMaxStableHVEquilibrium M (m i) (dstar i)) ∧
        StrictMono (fun i => invDemand M (m i) (dstar i))) ∧
    (∃ (M : Market) (I : ℕ) (m : Fin I → ℝ) (dstar : Fin I → ℝ),
        0 < M.a ∧ 0 ≤ M.r ∧ M.r < 1 ∧ 0 < M.t2 ∧ 0 < M.V ∧ 0 < M.w0 ∧ 0 ≤ M.α ∧
        2 ≤ I ∧ StrictMono m ∧ (∀ i, 0 < m i) ∧ (∀ i, IsLooseMarket M (m i)) ∧
        (∀ i, IsMaxStableHVEquilibrium M (m i) (dstar i)) ∧
        StrictAnti (fun i => invDemand M (m i) (dstar i))) ∧
    (∃ (M : Market) (I : ℕ) (m : Fin I → ℝ) (dstar : Fin I → ℝ),
        0 < M.a ∧ 0 ≤ M.r ∧ M.r < 1 ∧ 0 < M.t2 ∧ 0 < M.V ∧ 0 < M.w0 ∧ 0 ≤ M.α ∧
        StrictMono m ∧ (∀ i, 0 < m i) ∧ (∀ i, IsLooseMarket M (m i)) ∧
        (∀ i, IsMaxStableHVEquilibrium M (m i) (dstar i)) ∧
        ¬ Monotone (fun i => invDemand M (m i) (dstar i)) ∧
        ¬ Antitone (fun i => invDemand M (m i) (dstar i))) := by
  obtain ⟨d1, d8, d256, e1, e8, e256, l1, l8, l256, p81, p8b⟩ := Pff1.ex_all
  have h0 := Pff1.hyp0
  refine ⟨Pff1.main_univ, ?_, ?_, ?_⟩
  · refine ⟨Pff1.M0, 2, ![8, 256], ![d8, d256], h0.ha, h0.hr0, h0.hr1, h0.ht2, h0.hV, h0.hw0,
      h0.hα, le_refl 2, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact p8b | exact p81 | norm_num
    · intro i; fin_cases i <;> norm_num
    · intro i; fin_cases i
      · exact l8
      · exact l256
    · intro i; fin_cases i
      · exact e8
      · exact e256
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact p8b | exact p81 | norm_num
  · refine ⟨Pff1.M0, 2, ![1, 8], ![d1, d8], h0.ha, h0.hr0, h0.hr1, h0.ht2, h0.hV, h0.hw0,
      h0.hα, le_refl 2, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact p8b | exact p81 | norm_num
    · intro i; fin_cases i <;> norm_num
    · intro i; fin_cases i
      · exact l1
      · exact l8
    · intro i; fin_cases i
      · exact e1
      · exact e8
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact p8b | exact p81 | norm_num
  · refine ⟨Pff1.M0, 3, ![1, 8, 256], ![d1, d8, d256], h0.ha, h0.hr0, h0.hr1, h0.ht2, h0.hV,
      h0.hw0, h0.hα, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | exact p8b | exact p81 | norm_num
    · intro i; fin_cases i <;> norm_num
    · intro i; fin_cases i
      · exact l1
      · exact l8
      · exact l256
    · intro i; fin_cases i
      · exact e1
      · exact e8
      · exact e256
    · intro hmono
      have := hmono (show (0 : Fin 3) ≤ 1 by decide)
      change invDemand Pff1.M0 1 d1 ≤ invDemand Pff1.M0 8 d8 at this
      linarith
    · intro hanti
      have := hanti (show (1 : Fin 3) ≤ 2 by decide)
      change invDemand Pff1.M0 256 d256 ≤ invDemand Pff1.M0 8 d8 at this
      linarith
