-- Prove2me | solution 1 for TwoSidedExp.DemandLimit.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T04:23:18.724097+00:00
-- url     : https://prove2.me/submissions/c4772d63-df17-4e51-a377-02827289cf3a

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

set_option linter.unusedSectionVars false
open Filter Topology MeasureTheory

namespace DLSol
open TwoSidedExp.DemandLimit

variable {ι κ : Type} [Fintype ι] [Fintype κ]

/-- Hypotheses on a mean-field system used in the demand-limit argument. -/
structure Good (S : MFSystem ι κ) : Prop where
  phi_nn : ∀ q, 0 ≤ S.φ q
  av_nn : ∀ q p, 0 ≤ S.α q p * S.v q p
  eps_pos : ∀ q, 0 < S.eps q
  nu_pos : ∀ p, 0 < S.ν p

lemma choice_nn_le_one (S : MFSystem ι κ) (hS : Good S) (s : κ → ℝ) (hs : ∀ p, 0 ≤ s p)
    (q : ι) (p : κ) : 0 ≤ S.choice q p s ∧ S.choice q p s ≤ 1 := by
  unfold MFSystem.choice
  have hterm : ∀ p', 0 ≤ S.α q p' * S.v q p' * s p' := fun p' => mul_nonneg (hS.av_nn q p') (hs p')
  have hle : S.α q p * S.v q p * s p ≤ ∑ p', S.α q p' * S.v q p' * s p' :=
    Finset.single_le_sum (f := fun p' => S.α q p' * S.v q p' * s p') (fun p' _ => hterm p')
      (Finset.mem_univ p)
  have hsum : 0 ≤ ∑ p', S.α q p' * S.v q p' * s p' := Finset.sum_nonneg (fun p' _ => hterm p')
  have hden : 0 < S.eps q + ∑ p', S.α q p' * S.v q p' * s p' := by linarith [hS.eps_pos q]
  refine ⟨div_nonneg (hterm p) hden.le, ?_⟩
  rw [div_le_one hden]; linarith [hS.eps_pos q]

lemma steady_tendsto (S : MFSystem ι κ) (hS : Good S) (lam tau : ℕ → ℝ) (hl : ∀ n, 0 < lam n)
    (ht : ∀ n, 0 < tau n) (hlim : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (s : ℕ → κ → ℝ) (hs : ∀ n, S.IsSteady (lam n) (tau n) (s n)) (p : κ) :
    Tendsto (fun n => s n p) atTop (𝓝 (S.ρ p)) := by
  set c : ℝ := (∑ q, S.φ q) / S.ν p
  have hbound : ∀ n, 0 ≤ S.ρ p - s n p ∧ S.ρ p - s n p ≤ lam n / tau n * c := by
    intro n
    obtain ⟨hin, heq⟩ := hs n
    have h0 : ∀ p', 0 ≤ s n p' := fun p' => (hin p').1
    refine ⟨by linarith [(hin p).2], ?_⟩
    have hsum : ∑ q, S.φ q * S.choice q p (s n) ≤ ∑ q, S.φ q := by
      apply Finset.sum_le_sum; intro q _
      have := (choice_nn_le_one S hS (s n) h0 q p).2
      nlinarith [hS.phi_nn q]
    have e := heq p
    have hν := hS.nu_pos p
    have htn := ht n
    have hln := hl n
    have key : (S.ρ p - s n p) * (tau n * S.ν p) ≤ lam n * ∑ q, S.φ q := by
      rw [e]; exact mul_le_mul_of_nonneg_left hsum hln.le
    have : lam n / tau n * c = (lam n * ∑ q, S.φ q) / (tau n * S.ν p) := by
      simp only [c]; field_simp
    rw [this, le_div_iff₀ (by positivity)]
    exact key
  have hup : Tendsto (fun n => lam n / tau n * c) atTop (𝓝 0) := by
    simpa using hlim.mul_const c
  have hd : Tendsto (fun n => S.ρ p - s n p) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (hbound n).1) (fun n => (hbound n).2)
  have : Tendsto (fun n => S.ρ p - (S.ρ p - s n p)) atTop (𝓝 (S.ρ p - 0)) :=
    tendsto_const_nhds.sub hd
  simpa using this

lemma choice_tendsto (S : MFSystem ι κ) (s : ℕ → κ → ℝ) (s0 : κ → ℝ)
    (h : ∀ p, Tendsto (fun n => s n p) atTop (𝓝 (s0 p))) (q : ι) (p : κ)
    (hden : S.eps q + ∑ p', S.α q p' * S.v q p' * s0 p' ≠ 0) :
    Tendsto (fun n => S.choice q p (s n)) atTop (𝓝 (S.choice q p s0)) := by
  unfold MFSystem.choice
  apply Tendsto.div _ _ hden
  · exact (h p).const_mul _
  · exact tendsto_const_nhds.add (tendsto_finsetSum _ (fun p' _ => (h p').const_mul _))

/-- The limit of `Σ_p Σ_q φ_q choice(q,p)` along steady states as `λ/τ → 0`. -/
lemma sum_choice_tendsto (S : MFSystem ι κ) (hS : Good S) (hρ : ∀ p, 0 ≤ S.ρ p)
    (lam tau : ℕ → ℝ) (hl : ∀ n, 0 < lam n)
    (ht : ∀ n, 0 < tau n) (hlim : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (s : ℕ → κ → ℝ) (hs : ∀ n, S.IsSteady (lam n) (tau n) (s n))
    {β γ' : Type} [Fintype β] [Fintype γ'] (P : β → κ) (Qf : γ' → ι) :
    Tendsto (fun n => ∑ b, ∑ g, S.φ (Qf g) * S.choice (Qf g) (P b) (s n)) atTop
      (𝓝 (∑ b, ∑ g, S.φ (Qf g) * S.choice (Qf g) (P b) S.ρ)) := by
  have hconv := steady_tendsto S hS lam tau hl ht hlim s hs
  apply tendsto_finsetSum _ (fun b _ => tendsto_finsetSum _ (fun g _ => ?_))
  apply Tendsto.const_mul
  apply choice_tendsto S s S.ρ hconv
  have : 0 ≤ ∑ p', S.α (Qf g) p' * S.v (Qf g) p' * S.ρ p' :=
    Finset.sum_nonneg (fun p' _ => mul_nonneg (hS.av_nn _ p') (hρ p'))
  have := hS.eps_pos (Qf g)
  positivity


namespace Model
variable {Γ Θ : Type} [Fintype Γ] [Fintype Θ]

lemma good_expt (M : Model Γ Θ) (hM : M.Standing) (aC aL : ℝ) (h0 : 0 ≤ aC) (h1 : aC ≤ 1) :
    Good (M.expt aC aL) where
  phi_nn q := by
    unfold Model.expt; dsimp only
    split_ifs
    · exact mul_nonneg h0 (hM.phi_pos _).le
    · exact mul_nonneg (by linarith) (hM.phi_pos _).le
  av_nn q p := by
    unfold Model.expt; dsimp only
    split_ifs
    · exact mul_nonneg (hM.alphat_pos _ _).le (hM.vt_pos _ _).le
    · exact mul_nonneg (hM.alpha_pos _ _).le (hM.v_pos _ _).le
  eps_pos q := hM.eps_pos _
  nu_pos p := hM.nu_pos _

lemma rho_nn (M : Model Γ Θ) (hM : M.Standing) (aC aL : ℝ) (h0 : 0 ≤ aL) (h1 : aL ≤ 1) :
    ∀ p, 0 ≤ (M.expt aC aL).ρ p := by
  intro p
  show 0 ≤ M.rhoL aL p
  unfold Model.rhoL
  split_ifs
  · exact mul_nonneg h0 (hM.rho_pos _).le
  · exact mul_nonneg (by linarith) (hM.rho_pos _).le

lemma Q_tendsto (M : Model Γ Θ) (hM : M.Standing) (aC aL : ℝ) (h0 : 0 ≤ aC) (h1 : aC ≤ 1)
    (h0' : 0 ≤ aL) (h1' : aL ≤ 1)
    (lam tau : ℕ → ℝ) (hl : ∀ n, 0 < lam n)
    (ht : ∀ n, 0 < tau n) (hlim : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (s : ℕ → Θ × Fin 2 → ℝ) (hs : ∀ n, (M.expt aC aL).IsSteady (lam n) (tau n) (s n))
    (i j : Fin 2) :
    Tendsto (fun n => M.Q (lam n) aC aL (s n) i j / lam n) atTop
      (𝓝 (∑ θ, ∑ γ, (M.expt aC aL).φ (γ, i) * M.pE (γ, i) (θ, j) (M.rhoL aL))) := by
  have := sum_choice_tendsto (M.expt aC aL) (good_expt M hM aC aL h0 h1)
    (rho_nn M hM aC aL h0' h1') lam tau hl ht hlim s hs (fun θ : Θ => (θ, j))
    (fun γ : Γ => (γ, i))
  refine this.congr' (Eventually.of_forall fun n => ?_)
  show _ = (lam n * _) / lam n
  rw [mul_div_cancel_left₀ _ (hl n).ne']

lemma control_identity (M : Model Γ Θ) (γ : Γ) (θ : Θ) :
    M.pE (γ, 0) (θ, 1) (M.rhoL 1) = M.pE (γ, 0) (θ, 0) (M.rhoL 0) := by
  simp [Model.pE, MFSystem.choice, Model.expt, Model.rhoL, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma cr_part (M : Model Γ Θ) (hM : M.Standing) (aC : ℝ) (h0 : 0 < aC) (h1 : aC < 1)
    (lam tau : ℕ → ℝ) (hl : ∀ n, 0 < lam n) (ht : ∀ n, 0 < tau n)
    (hlim : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (sCR sGT sGC : ℕ → Θ × Fin 2 → ℝ)
    (hCR : ∀ n, (M.expt aC 1).IsSteady (lam n) (tau n) (sCR n))
    (hGT : ∀ n, (M.expt 1 1).IsSteady (lam n) (tau n) (sGT n))
    (hGC : ∀ n, (M.expt 0 0).IsSteady (lam n) (tau n) (sGC n)) :
    Tendsto (fun n => M.crEst (lam n) aC (sCR n) / lam n
          - M.gte (lam n) (sGT n) (sGC n) / lam n) atTop (𝓝 0) := by
  have t11 := Q_tendsto M hM aC 1 h0.le h1.le zero_le_one le_rfl lam tau hl ht hlim sCR hCR 1 1
  have t01 := Q_tendsto M hM aC 1 h0.le h1.le zero_le_one le_rfl lam tau hl ht hlim sCR hCR 0 1
  have tGT := Q_tendsto M hM 1 1 zero_le_one le_rfl zero_le_one le_rfl lam tau hl ht hlim sGT hGT 1 1
  have tGC := Q_tendsto M hM 0 0 le_rfl zero_le_one le_rfl zero_le_one lam tau hl ht hlim sGC hGC 0 0
  have hT := ((t11.div_const aC).sub (t01.div_const (1 - aC))).sub (tGT.sub tGC)
  have hfun : (fun n => M.crEst (lam n) aC (sCR n) / lam n
          - M.gte (lam n) (sGT n) (sGC n) / lam n) =
      (fun n => (M.Q (lam n) aC 1 (sCR n) 1 1 / lam n / aC
          - M.Q (lam n) aC 1 (sCR n) 0 1 / lam n / (1 - aC))
          - (M.Q (lam n) 1 1 (sGT n) 1 1 / lam n - M.Q (lam n) 0 0 (sGC n) 0 0 / lam n)) := by
    funext n
    simp only [Model.crEst, Model.gte]
    ring
  rw [hfun]
  convert hT using 2
  have hc : (1 - aC) ≠ 0 := by linarith
  simp only [Model.expt, control_identity, if_true, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
    if_false, mul_assoc, ← Finset.mul_sum]
  field_simp
  ring

end Model
end DLSol

open TwoSidedExp.DemandLimit

theorem solution {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ)
    (hM : M.Standing) (aC aL : ℝ) (haC : aC ∈ Set.Icc (0 : ℝ) 1) (haL : aL ∈ Set.Icc (0 : ℝ) 1)
    (lam tau : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (htau : ∀ n, 0 < tau n)
    (hratio : Tendsto (fun n => lam n / tau n) atTop (𝓝 0))
    (s : ℕ → Θ × Fin 2 → ℝ) (hs : ∀ n, (M.expt aC aL).IsSteady (lam n) (tau n) (s n)) :
    ∀ i j : Fin 2, Tendsto (fun n => M.Q (lam n) aC aL (s n) i j / lam n) atTop
      (𝓝 (∑ θ, ∑ γ, (M.expt aC aL).φ (γ, i) *
        (M.expt aC aL).choice (γ, i) (θ, j) (M.expt aC aL).ρ)) := by
  intro i j
  exact DLSol.Model.Q_tendsto M hM aC aL haC.1 haC.2 haL.1 haL.2 lam tau hlam htau hratio s hs i j
