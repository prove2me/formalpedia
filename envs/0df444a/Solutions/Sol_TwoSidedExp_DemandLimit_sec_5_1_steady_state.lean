-- Prove2me | solution 1 for TwoSidedExp.DemandLimit.sec_5_1_steady_state
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T04:26:52.048006+00:00
-- url     : https://prove2.me/submissions/b90d5146-45c8-4086-ab96-5fb59da0245e

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

set_option linter.unusedSectionVars false
open Filter Topology MeasureTheory

namespace DLSolT
open TwoSidedExp.DemandLimit

variable {ι κ : Type} [Fintype ι] [Fintype κ]

structure Hyp (S : MFSystem ι κ) (lam tau : ℝ) : Prop where
  rho_nn : ∀ p, 0 ≤ S.ρ p
  phi_nn : ∀ q, 0 ≤ S.φ q
  av_nn : ∀ q p, 0 ≤ S.α q p * S.v q p
  eps_pos : ∀ q, 0 < S.eps q
  nu_pos : ∀ p, 0 < S.ν p
  lam_pos : 0 < lam
  tau_pos : 0 < tau

noncomputable def Den (S : MFSystem ι κ) (s : κ → ℝ) (q : ι) : ℝ :=
  S.eps q + ∑ p, S.α q p * S.v q p * s p

noncomputable def G (S : MFSystem ι κ) (lam tau : ℝ) (s : κ → ℝ) (p : κ) : ℝ :=
  tau * S.ν p + lam * ∑ q, S.φ q * (S.α q p * S.v q p) / Den S s q

noncomputable def T (S : MFSystem ι κ) (lam tau : ℝ) (s : κ → ℝ) : κ → ℝ :=
  fun p => S.ρ p * (tau * S.ν p) / G S lam tau s p

variable {S : MFSystem ι κ} {lam tau : ℝ}

lemma Den_pos (h : Hyp S lam tau) {s : κ → ℝ} (hs : 0 ≤ s) (q : ι) : 0 < Den S s q := by
  unfold Den
  have : 0 ≤ ∑ p, S.α q p * S.v q p * s p :=
    Finset.sum_nonneg fun p _ => mul_nonneg (h.av_nn q p) (hs p)
  linarith [h.eps_pos q]

lemma sum_nn (h : Hyp S lam tau) {s : κ → ℝ} (hs : 0 ≤ s) (p : κ) :
    0 ≤ ∑ q, S.φ q * (S.α q p * S.v q p) / Den S s q :=
  Finset.sum_nonneg fun q _ => div_nonneg (mul_nonneg (h.phi_nn q) (h.av_nn q p)) (Den_pos h hs q).le

lemma G_pos (h : Hyp S lam tau) {s : κ → ℝ} (hs : 0 ≤ s) (p : κ) : 0 < G S lam tau s p := by
  unfold G
  have := sum_nn h hs p
  have := mul_pos h.tau_pos (h.nu_pos p)
  have := h.lam_pos
  positivity

lemma tauν_le_G (h : Hyp S lam tau) {s : κ → ℝ} (hs : 0 ≤ s) (p : κ) :
    tau * S.ν p ≤ G S lam tau s p := by
  unfold G
  have := mul_nonneg h.lam_pos.le (sum_nn h hs p)
  linarith

lemma T_nn (h : Hyp S lam tau) {s : κ → ℝ} (hs : 0 ≤ s) : 0 ≤ T S lam tau s := by
  intro p
  have := mul_pos h.tau_pos (h.nu_pos p)
  exact div_nonneg (mul_nonneg (h.rho_nn p) this.le) (G_pos h hs p).le

lemma T_le_rho (h : Hyp S lam tau) {s : κ → ℝ} (hs : 0 ≤ s) : T S lam tau s ≤ S.ρ := by
  intro p
  have h1 := mul_pos h.tau_pos (h.nu_pos p)
  show S.ρ p * (tau * S.ν p) / G S lam tau s p ≤ S.ρ p
  rw [div_le_iff₀ (G_pos h hs p)]
  exact mul_le_mul_of_nonneg_left (tauν_le_G h hs p) (h.rho_nn p)

lemma T_mono (h : Hyp S lam tau) {s s' : κ → ℝ} (hs : 0 ≤ s) (hss : s ≤ s') :
    T S lam tau s ≤ T S lam tau s' := by
  have hs' : 0 ≤ s' := le_trans hs hss
  intro p
  have h1 := mul_pos h.tau_pos (h.nu_pos p)
  show S.ρ p * (tau * S.ν p) / G S lam tau s p ≤ S.ρ p * (tau * S.ν p) / G S lam tau s' p
  apply div_le_div_of_nonneg_left (mul_nonneg (h.rho_nn p) h1.le) (G_pos h hs' p)
  unfold G
  have : ∑ q, S.φ q * (S.α q p * S.v q p) / Den S s' q ≤ ∑ q, S.φ q * (S.α q p * S.v q p) / Den S s q := by
    apply Finset.sum_le_sum; intro q _
    apply div_le_div_of_nonneg_left (mul_nonneg (h.phi_nn q) (h.av_nn q p)) (Den_pos h hs q)
    unfold Den
    have : ∑ p, S.α q p * S.v q p * s p ≤ ∑ p, S.α q p * S.v q p * s' p :=
      Finset.sum_le_sum fun p' _ => mul_le_mul_of_nonneg_left (hss p') (h.av_nn q p')
    linarith
  nlinarith [h.lam_pos]

lemma T_subhom (h : Hyp S lam tau) {s : κ → ℝ} (hs : 0 ≤ s) {c : ℝ} (hc : 1 < c) (p : κ)
    (hρ : 0 < S.ρ p) : T S lam tau (c • s) p < c * T S lam tau s p := by
  have hcs : 0 ≤ c • s := fun p => mul_nonneg (by linarith) (hs p)
  have h1 := mul_pos h.tau_pos (h.nu_pos p)
  show S.ρ p * (tau * S.ν p) / G S lam tau (c • s) p < c * (S.ρ p * (tau * S.ν p) / G S lam tau s p)
  have g1 := G_pos h hcs p
  have g2 := G_pos h hs p
  rw [mul_div_assoc', div_lt_div_iff₀ g1 g2]
  have key : G S lam tau s p < c * G S lam tau (c • s) p := by
    unfold G
    have hsum : ∑ q, S.φ q * (S.α q p * S.v q p) / Den S s q ≤
        c * ∑ q, S.φ q * (S.α q p * S.v q p) / Den S (c • s) q := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro q _
      have d1 := Den_pos h hs q
      have d2 := Den_pos h hcs q
      have hn := mul_nonneg (h.phi_nn q) (h.av_nn q p)
      rw [mul_div_assoc', div_le_div_iff₀ d1 d2]
      have hDen : Den S (c • s) q ≤ c * Den S s q := by
        unfold Den
        simp only [Pi.smul_apply, smul_eq_mul]
        have : ∑ p, S.α q p * S.v q p * (c * s p) = c * ∑ p, S.α q p * S.v q p * s p := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
        rw [this]
        nlinarith [h.eps_pos q]
      calc S.φ q * (S.α q p * S.v q p) * Den S (c • s) q
          ≤ S.φ q * (S.α q p * S.v q p) * (c * Den S s q) := mul_le_mul_of_nonneg_left hDen hn
        _ = c * (S.φ q * (S.α q p * S.v q p)) * Den S s q := by ring
    have := h.lam_pos
    nlinarith
  have hr : 0 < S.ρ p * (tau * S.ν p) := mul_pos hρ h1
  nlinarith

lemma steady_iff (h : Hyp S lam tau) (s : κ → ℝ) :
    S.IsSteady lam tau s ↔ (0 ≤ s ∧ s = T S lam tau s) := by
  constructor
  · rintro ⟨hin, heq⟩
    have hs : 0 ≤ s := fun p => (hin p).1
    refine ⟨hs, funext fun p => ?_⟩
    have e := heq p
    have hrw : lam * ∑ q, S.φ q * S.choice q p s =
        s p * (lam * ∑ q, S.φ q * (S.α q p * S.v q p) / Den S s q) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _
      unfold MFSystem.choice Den
      ring
    rw [hrw] at e
    show s p = S.ρ p * (tau * S.ν p) / G S lam tau s p
    rw [eq_div_iff (G_pos h hs p).ne']
    unfold G; linarith
  · rintro ⟨hs, hT⟩
    refine ⟨fun p => ⟨hs p, ?_⟩, fun p => ?_⟩
    · rw [hT]; exact T_le_rho h hs p
    · have hrw : lam * ∑ q, S.φ q * S.choice q p s =
          s p * (lam * ∑ q, S.φ q * (S.α q p * S.v q p) / Den S s q) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro q _
        unfold MFSystem.choice Den
        ring
      rw [hrw]
      have e : s p = S.ρ p * (tau * S.ν p) / G S lam tau s p := congrFun hT p
      rw [eq_div_iff (G_pos h hs p).ne'] at e
      unfold G at e; linarith

lemma exists_fixed (h : Hyp S lam tau) : ∃ s, 0 ≤ s ∧ s = T S lam tau s := by
  have : Fact ((0 : κ → ℝ) ≤ S.ρ) := ⟨h.rho_nn⟩
  let f : Set.Icc (0 : κ → ℝ) S.ρ →o Set.Icc (0 : κ → ℝ) S.ρ :=
    { toFun := fun x => ⟨T S lam tau x.1, T_nn h x.2.1, T_le_rho h x.2.1⟩
      monotone' := fun x y hxy => T_mono h x.2.1 hxy }
  refine ⟨(OrderHom.lfp f).1, (OrderHom.lfp f).2.1, ?_⟩
  have := OrderHom.map_lfp f
  exact (congrArg Subtype.val this).symm

lemma fixed_pos (h : Hyp S lam tau) {s : κ → ℝ} (hs : 0 ≤ s) (hT : s = T S lam tau s) (p : κ)
    (hρ : 0 < S.ρ p) : 0 < s p := by
  rw [hT]
  exact div_pos (mul_pos hρ (mul_pos h.tau_pos (h.nu_pos p))) (G_pos h hs p)

lemma fixed_le (h : Hyp S lam tau) {s s' : κ → ℝ} (hs : 0 ≤ s) (hT : s = T S lam tau s)
    (hs' : 0 ≤ s') (hT' : s' = T S lam tau s') : s' ≤ s := by
  classical
  -- coordinates with ρ = 0 vanish
  have hz : ∀ {u : κ → ℝ}, 0 ≤ u → u = T S lam tau u → ∀ p, ¬ 0 < S.ρ p → u p = 0 := by
    intro u hu hTu p hp
    have h0 : S.ρ p = 0 := le_antisymm (not_lt.1 hp) (h.rho_nn p)
    have := T_le_rho h hu p
    rw [← hTu, h0] at this
    exact le_antisymm this (hu p)
  by_contra hcon
  have hex : ∃ p, s p < s' p := by
    by_contra hn; push Not at hn; exact hcon hn
  -- maximize the ratio over positive coordinates
  let P := Finset.univ.filter (fun p => 0 < S.ρ p)
  obtain ⟨p1, hp1⟩ := hex
  have hp1P : p1 ∈ P := by
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hn
    rw [hz hs hT p1 hn, hz hs' hT' p1 hn] at hp1
    exact lt_irrefl _ hp1
  obtain ⟨p0, hp0P, hmax⟩ := P.exists_max_image (fun p => s' p / s p) ⟨p1, hp1P⟩
  simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hp0P hmax hp1P
  set c := s' p0 / s p0 with hc
  have hspos : ∀ p, 0 < S.ρ p → 0 < s p := fun p hp => fixed_pos h hs hT p hp
  have hc1 : 1 < c := by
    have := hmax p1 hp1P
    have h1 : 1 < s' p1 / s p1 := by rw [one_lt_div (hspos p1 hp1P)]; exact hp1
    linarith
  have hle : s' ≤ c • s := by
    intro p
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hp : 0 < S.ρ p
    · have := hmax p hp
      rw [div_le_iff₀ (hspos p hp)] at this
      linarith
    · rw [hz hs' hT' p hp, hz hs hT p hp]; simp
  have h1 : s' p0 ≤ T S lam tau (c • s) p0 := by
    rw [hT']; exact T_mono h hs' hle p0
  have h2 := T_subhom h hs hc1 p0 hp0P
  rw [← hT] at h2
  have : c * s p0 = s' p0 := by
    rw [hc]; field_simp [(hspos p0 hp0P).ne']
  have h3 : s' p0 = T S lam tau s' p0 := congrFun hT' p0
  linarith

theorem exists_unique_steady (h : Hyp S lam tau) : ∃! s, S.IsSteady lam tau s := by
  obtain ⟨s, hs, hT⟩ := exists_fixed h
  refine ⟨s, (steady_iff h s).2 ⟨hs, hT⟩, fun s' hs' => ?_⟩
  obtain ⟨hs'0, hT'⟩ := (steady_iff h s').1 hs'
  exact le_antisymm (fixed_le h hs hT hs'0 hT') (fixed_le h hs'0 hT' hs hT)

end DLSolT

open TwoSidedExp.DemandLimit

theorem solution {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ)
    (hM : M.Standing) (aC aL : ℝ) (haC : aC ∈ Set.Icc (0 : ℝ) 1) (haL : aL ∈ Set.Icc (0 : ℝ) 1)
    (lam tau : ℝ) (hlam : 0 < lam) (htau : 0 < tau) :
    ∃! s : Θ × Fin 2 → ℝ, (M.expt aC aL).IsSteady lam tau s := by
  obtain ⟨h0, h1⟩ := haC
  obtain ⟨h0', h1'⟩ := haL
  apply DLSolT.exists_unique_steady
  exact
    { rho_nn := fun p => by
        show 0 ≤ M.rhoL aL p
        unfold Model.rhoL
        split_ifs
        · exact mul_nonneg h0' (hM.rho_pos _).le
        · exact mul_nonneg (by linarith) (hM.rho_pos _).le
      phi_nn := fun q => by
        unfold Model.expt; dsimp only
        split_ifs
        · exact mul_nonneg h0 (hM.phi_pos _).le
        · exact mul_nonneg (by linarith) (hM.phi_pos _).le
      av_nn := fun q p => by
        unfold Model.expt; dsimp only
        split_ifs
        · exact mul_nonneg (hM.alphat_pos _ _).le (hM.vt_pos _ _).le
        · exact mul_nonneg (hM.alpha_pos _ _).le (hM.v_pos _ _).le
      eps_pos := fun q => hM.eps_pos _
      nu_pos := fun p => hM.nu_pos _
      lam_pos := hlam
      tau_pos := htau }
